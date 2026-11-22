// Replays Hypergolic's published-napplet document builder (runtime/src/main.ts renderGuest,
// non-legacy published path) on the adversarial vectors of lean/Napplet/Srcdoc.lean.
import './win-stub.ts';
import { publishedCspParts } from '/Users/gareth/git/napplets/hypergolic/runtime/src/published-artifact.ts';
import { injectReviewedPresentation } from '/Users/gareth/git/napplets/hypergolic/runtime/src/reviewed-presentation.ts';
import { injectEmojiImages } from '/Users/gareth/git/napplets/hypergolic/runtime/src/reviewed-emoji-images.ts';
import { injectResourceMediaGate } from '/Users/gareth/git/napplets/hypergolic/runtime/src/resource-media.ts';
import { injectAndroidGuestHelpers } from '/Users/gareth/git/napplets/hypergolic/runtime/src/android-guest-helpers.ts';
import { injectCreatorUpload } from '/Users/gareth/git/napplets/hypergolic/runtime/src/reviewed-creator-upload.ts';
import { injectNappletNamespacePrelude } from '/Users/gareth/git/napplets/hypergolic/runtime/node_modules/@kehto/shell/dist/index.js';
// main.ts:93-99 (csp) with resource granted (media-src blob:) as for a resource-domain napplet
const csp = ["default-src 'none'", "script-src 'unsafe-inline' 'wasm-unsafe-eval'",
  "style-src 'unsafe-inline'", 'img-src data: blob:', 'font-src data:',
  "connect-src 'none'", "webrtc 'block'", "worker-src blob:", "child-src 'none'", "frame-src 'none'",
  "media-src 'none'", "object-src 'none'", "manifest-src 'none'", "base-uri 'none'",
  "form-action 'none'"].join('; ');
const artifact = { aggregateHash: '0'.repeat(64), appId: 'audit', title: 'audit', domains: ['storage'], published: true };
export function build(raw: string): string {
  const [prefix, withCsp] = publishedCspParts(raw, csp);
  const presentation = injectReviewedPresentation(injectEmojiImages(withCsp, artifact), artifact);
  const guest = injectAndroidGuestHelpers(injectResourceMediaGate(presentation, false));
  const injected = injectNappletNamespacePrelude(injectCreatorUpload(guest, artifact), { domains: ['storage'], requestTimeoutsMs: {} });
  return prefix + injected;
}
export { csp };
