// Validation probe: drives Hypergolic's real WebView ingress (guestMessageReceiver, validEnvelope,
// rejectEnvelope) wired exactly as runtime/src/main.ts:322-336 wires them. Only the frame window
// (postMessage sink) and the Kehto bridge (recorded as "FORWARDED") are stand-ins.
// Run from the Hypergolic root:
//   node --experimental-strip-types --import ../lean/audits/hypergolic/validation/storage/register.mjs \
//     --test ../lean/audits/hypergolic/validation/storage/ingress.test.ts
import test from 'node:test';
import { guestMessageReceiver } from '../../../../../hypergolic/runtime/src/guest-message-receiver.ts';
import { validEnvelope, rejectEnvelope } from '../../../../../hypergolic/runtime/src/guest-envelope.ts';
const domains = ['theme', 'identity', 'storage', 'config'];
function shell() {
  const replies: unknown[] = [], forwarded: unknown[] = [];
  const source = { postMessage(v: unknown) { replies.push(v); } } as unknown as Window;
  const frame = { contentWindow: source } as HTMLIFrameElement;
  const receive = guestMessageReceiver(frame, source, {
    domains, live: () => true, closed: () => false,
    routing: { connect: () => false } as any, keys: null, sendMedia: null,
    dispatch(event) { // main.ts:331-336
      if (!validEnvelope(event.data)) { rejectEnvelope(event, source, domains); return; }
      forwarded.push(event.data);
    },
  });
  const send = (data: unknown) => { const r = replies.length, f = forwarded.length;
    receive({ source, data, ports: [], isTrusted: true } as unknown as MessageEvent);
    return forwarded.length > f ? 'FORWARDED' : replies.length > r ? 'REPLY ' + JSON.stringify(replies.at(-1)) : 'DROPPED (no reply)'; };
  return { send };
}
test('malformed known requests at ingress', () => {
  const s = shell(); const o = (l: string, m: unknown) => console.log(l, '=>', s.send(m));
  o('THEME-1a theme.get ok', { type: 'theme.get', id: 't0' });
  o('THEME-1b theme.get extra member', { type: 'theme.get', id: 't1', x: 1 });
  o('THEME-1c theme.get id ""', { type: 'theme.get', id: '' });
  o('CONFIG-9a registerSchema no schema', { type: 'config.registerSchema', id: 'r' });
  o('CONFIG-9b registerSchema version -1', { type: 'config.registerSchema', id: 'r2', schema: { type: 'object', properties: {} }, version: -1 });
  o('CONFIG-9c config.get extra member', { type: 'config.get', id: 'g', x: 1 });
  o('CONFIG-9d config.subscribe with id', { type: 'config.subscribe', id: 's' });
  o('CONFIG-9e config.get ok', { type: 'config.get', id: 'g2' });
  o('IDENTITY-2 getList no listType', { type: 'identity.getList', id: 'l1' });
  o('IDENTITY-1 getPublicKey extra member', { type: 'identity.getPublicKey', id: 'p1', extra: 1 });
  o('STORAGE-3a storage.get extra member', { type: 'storage.get', id: 'x3', key: 'k', extra: 1 });
  o('STORAGE-3b storage.get id ""', { type: 'storage.get', id: '', key: 'k' });
  o('STORAGE-3c storage.get id 200 chars', { type: 'storage.get', id: 'i'.repeat(200), key: 'k' });
  o('STORAGE-3d storage.get id 128 chars', { type: 'storage.get', id: 'i'.repeat(128), key: 'k' });
});
test('rate limit: 65th message within one second', () => {
  for (const [label, msg] of [
    ['STORAGE-5 storage.get', { type: 'storage.get', id: 'q', key: 'k' }],
    ['IDENTITY-3 identity.getPublicKey', { type: 'identity.getPublicKey', id: 'q' }],
    ['IDENTITY-3b identity.getProfile', { type: 'identity.getProfile', id: 'q' }],
    ['THEME-2 theme.get', { type: 'theme.get', id: 'q' }],
    ['config.get', { type: 'config.get', id: 'q' }],
    ['config.subscribe (no id)', { type: 'config.subscribe' }],
  ] as const) {
    const s = shell(); let last = '';
    for (let i = 0; i < 64; i++) last = s.send({ type: 'storage.keys', id: 'n' + i });
    console.log(label, 'msg#64 =>', last, '| msg#65 =>', s.send(msg));
  }
});
