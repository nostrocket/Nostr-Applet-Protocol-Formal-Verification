import { test, expect, type Page } from '@playwright/test';
async function instrument(page: Page) {
  await page.addInitScript(() => {
    const state = window as any;
    if (window !== window.top) return;
    state.__received = [];
    window.addEventListener('message', event => { state.__received.push(event.data); });
    state.__diagnostics = [];
    Object.defineProperty(window, 'localStorage', { get() { throw new DOMException('x', 'SecurityError'); } });
    Object.defineProperty(window, 'HypergolicHost', { value: { postMessage: (v: string) => state.__diagnostics.push(JSON.parse(v)) } });
  });
}
test('AUDIT: a document the napplet navigates to inherits its NAP session before load revokes it', async ({ page }) => {
  await instrument(page);
  await page.goto('/assets/runtime/index.html?sessionId=navrace&fixture=ux-lab');
  const frameEl = page.locator('#napplet');
  const frame = await frameEl.contentFrame();
  await expect(frame.getByTestId('lab')).toHaveAttribute('data-ready', 'true');
  await expect.poll(() => page.evaluate(() => (window as any).__diagnostics)).toEqual([{ type: 'ready', sessionId: 'navrace' }]);
  const guest = page.frames().find(f => f.parentFrame() === page.mainFrame())!;
  // The new, unverified document has no CSP meta and no verified bytes. It sends a NAP request
  // and reports what it receives back to the shell window.
  const html = `<script>
    addEventListener('message', e => { if (e.data && e.data.type === 'theme.get.result') parent.postMessage({type:'audit.got', reply:e.data}, '*'); });
    parent.postMessage({type:'theme.get', id:'nav-1'}, '*');
  </script>`;
  await guest.evaluate(h => { location.href = 'data:text/html,' + encodeURIComponent(h); }, html);
  await expect.poll(() => page.evaluate(() => (window as any).__diagnostics)).toContainEqual({ type: 'error', sessionId: 'navrace', code: 'frame-navigation' });
  const got = await page.evaluate(() => (window as any).__received.filter((m: any) => m?.type === 'audit.got' || m?.type === 'theme.get'));
  console.log('AUDIT-RESULT', JSON.stringify(got));
});
