// Validation probe for INTENT-1, INTENT-2 (and the shared "dropped without a reply" path).
// Drives Hypergolic's real WebView ingress decision (runtime/src/main.ts:331-332):
//   if (!validEnvelope(data)) { rejectEnvelope(event, source, domains); return; }
// with a recording `source`. Nothing is stubbed except the frame window that receives replies.
// Run from the Hypergolic root:
//   node --experimental-strip-types --import ../lean/audits/hypergolic/relay/register.mjs \
//     ../lean/audits/hypergolic/validation/high/ingress-drop.test.mts
const HG = process.cwd();
const { validEnvelope, rejectEnvelope } = await import(HG + '/runtime/src/guest-envelope.ts');
const domains = ['intent', 'inc', 'identity', 'relay', 'theme', 'config', 'notify', 'storage'];
const addr = '35129:' + 'a'.repeat(64) + ':chess';
const cases: [string, unknown][] = [
  ['intent.launch', { type: 'intent.launch', id: 'l1', target: { address: addr } }],
  ['intent.invoke +sender', { type: 'intent.invoke', id: 'i1', request: { archetype: 'profile', action: 'open', convention: 'napplet:profile/open', sender: 'x' } }],
  ['intent.invoke +handlerHint', { type: 'intent.invoke', id: 'i2', request: { archetype: 'profile', action: 'open', convention: 'napplet:profile/open', handlerHint: { address: addr } } }],
  ['intent.invoke no request', { type: 'intent.invoke', id: 'i3' }],
  ['intent.invoke plain (control)', { type: 'intent.invoke', id: 'i4', request: { archetype: 'profile', action: 'open', convention: 'napplet:profile/open' } }],
  ['identity.getPublicKey +extra', { type: 'identity.getPublicKey', id: 'p1', extra: 1 }],
];
for (const [label, data] of cases) {
  const replies: unknown[] = [];
  const valid = validEnvelope(data);
  if (!valid) rejectEnvelope({ data } as MessageEvent, { postMessage: (m: unknown) => replies.push(m) } as unknown as Window, domains);
  console.log(`${label}: validEnvelope=${valid} ${valid ? '(forwarded to Kehto)' : 'replies=' + JSON.stringify(replies)}`);
}
