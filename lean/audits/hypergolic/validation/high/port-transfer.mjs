// Validation probe for NIP5D-1 ("not N/A mobile"): can a MessagePort cross the boundary of a
// sandbox="allow-scripts" srcdoc iframe in both directions? Runs in Playwright's Chromium (the
// engine of Android WebView) and WebKit (the engine of WKWebView). It is an engine check, not a
// device check. Run from the Hypergolic runtime directory:
//   node ../../lean/audits/hypergolic/validation/high/port-transfer.mjs
// Set PW_WEBKIT to a pw_run.sh path if Playwright's pinned WebKit build is not installed.
import { createRequire } from 'node:module';
const pw = createRequire(process.cwd() + '/package.json')('@playwright/test');
const guest = `<!doctype html><html><head><script>
  // NIP-5D direction: the napplet creates the channel and transfers one port to the shell.
  const ch = new MessageChannel();
  ch.port1.onmessage = e => ch.port1.postMessage({echo: e.data, origin: self.origin});
  parent.postMessage({type: 'napplet.hello'}, '*', [ch.port2]);
  // Reverse direction: the shell transfers a port into the iframe.
  addEventListener('message', e => { if (e.ports.length === 1) e.ports[0].postMessage({got: 'shell-port', ports: e.ports.length}); });
</script></head><body></body></html>`;
for (const name of ['chromium', 'webkit']) {
  const browser = await pw[name].launch(process.env.PW_WEBKIT && name === 'webkit' ? {executablePath: process.env.PW_WEBKIT} : {});
  const page = await browser.newPage();
  await page.goto('about:blank');
  const result = await page.evaluate(srcdoc => new Promise(resolve => {
    const out = {};
    const frame = document.createElement('iframe');
    frame.setAttribute('sandbox', 'allow-scripts'); frame.srcdoc = srcdoc;
    addEventListener('message', e => {
      if (e.source !== frame.contentWindow || e.data?.type !== 'napplet.hello') return;
      out.helloPorts = e.ports.length; out.helloOrigin = e.origin;
      const port = e.ports[0];
      port.onmessage = m => { out.overGuestPort = m.data;
        const ch = new MessageChannel();
        ch.port1.onmessage = r => { out.overShellPort = r.data; resolve(out); };
        frame.contentWindow.postMessage({type: 'port'}, '*', [ch.port2]); };
      port.postMessage('ping');
    });
    document.body.append(frame);
    setTimeout(() => resolve({...out, timeout: true}), 5000);
  }), guest);
  console.log(name, browser.version(), JSON.stringify(result));
  await browser.close();
}
