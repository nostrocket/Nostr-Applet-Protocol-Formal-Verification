// Validation probe for NIP5D-1's "Mitigations present" claim. The audit's spec
// (core/zz-audit-navigation.spec.ts) only checks that the session is revoked eventually. This one
// asks the sharper question: does a document the verified napplet navigates to get ANY NAP reply
// through the inherited WindowProxy before the second `load` revokes the session?
// Copy into hypergolic/runtime/tests/, run, then delete:
//   npx playwright test tests/zz-val-nav-race.spec.ts --reporter=line
import { test, expect, type Page } from '@playwright/test';
async function instrument(page: Page) {
  await page.addInitScript(() => {
    const state = window as any;
    if (window !== window.top) return;
    state.__received = [];
    window.addEventListener('message', event => { state.__received.push(event.data); }, true);
    state.__diagnostics = [];
    Object.defineProperty(window, 'localStorage', { get() { throw new DOMException('x', 'SecurityError'); } });
    Object.defineProperty(window, 'HypergolicHost', { value: { postMessage: (v: string) => state.__diagnostics.push(JSON.parse(v)) } });
  });
}
// The replacement document: unverified, sends NAP requests at once and reports any reply.
const html = `<script>
  addEventListener('message', e => { if (e.data && /\\.result$/.test(e.data.type || '')) parent.postMessage({type:'audit.got', reply:e.data}, '*'); });
  parent.postMessage({type:'audit.alive', csp: !!document.querySelector('meta[http-equiv]')}, '*');
  for (let i = 0; i < 5; i++) parent.postMessage({type:'theme.get', id:'nav-' + i}, '*');
</script>`;
const variants: Record<string, string> = {
  'data-href': `location.href = 'data:text/html,' + encodeURIComponent(H);`,
  'data-replace': `location.replace('data:text/html,' + encodeURIComponent(H));`,
  'blob-href': `location.href = URL.createObjectURL(new Blob([H], {type: 'text/html'}));`,
  'document-write': `document.open(); document.write(H); document.close();`,
};
for (const [name, code] of Object.entries(variants)) {
  test('VALIDATION nav race: ' + name, async ({ page }, info) => {
    await instrument(page);
    await page.goto('/assets/runtime/index.html?sessionId=navrace&fixture=ux-lab');
    const frame = await page.locator('#napplet').contentFrame();
    await expect(frame.getByTestId('lab')).toHaveAttribute('data-ready', 'true');
    await expect.poll(() => page.evaluate(() => (window as any).__diagnostics)).toEqual([{ type: 'ready', sessionId: 'navrace' }]);
    const guest = page.frames().find(f => f.parentFrame() === page.mainFrame())!;
    await guest.evaluate(([h, c]) => { (0, eval)('var H = ' + JSON.stringify(h) + ';' + c); }, [html, code]).catch(e => console.log('VALIDATION', name, 'evaluate error', String(e).slice(0, 120)));
    await page.waitForTimeout(1500);
    const diagnostics = await page.evaluate(() => (window as any).__diagnostics);
    const got = await page.evaluate(() => (window as any).__received.filter((m: any) => typeof m?.type === 'string' && (m.type.startsWith('audit.') || /^nav-/.test(m.id || ''))));
    const summary = { alive: got.filter((m: any) => m.type === 'audit.alive'), requestsSeenByShell: got.filter((m: any) => m.type === 'theme.get').length,
      repliesReachedNewDocument: got.filter((m: any) => m.type === 'audit.got').length, revoked: diagnostics.some((d: any) => d.code === 'frame-navigation') };
    console.log('VALIDATION', info.project.name, name, JSON.stringify(summary));
  });
}
