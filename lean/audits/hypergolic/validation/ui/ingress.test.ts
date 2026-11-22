// Validation probe: drives Hypergolic's real WebView ingress (guestMessageReceiver ->
// validEnvelope -> rejectEnvelope, keys side lane, media-wire projection).
// Only the 3-line `dispatch` glue is copied from runtime/src/main.ts:331-334; Kehto and the
// native client are replaced by recorders ("FORWARD" = handed to Kehto/native, no reply here).
// Run from the Hypergolic root:
//   node --experimental-strip-types --import ../lean/audits/hypergolic/validation/ui/register.mjs \
//     --test ../lean/audits/hypergolic/validation/ui/ingress.test.ts
import test from 'node:test';
import { guestMessageReceiver } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-message-receiver.ts';
import { validEnvelope, rejectEnvelope } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-envelope.ts';
import { createKeysSession } from '/Users/gareth/git/napplets/hypergolic/runtime/src/keys-adapter.ts';
const domains = ['intent', 'inc', 'notify', 'keys', 'media', 'link', 'theme', 'cvm'];
test('ingress', () => {
  const out: unknown[] = [];
  const source = { postMessage: (v: unknown) => out.push(v) } as unknown as Window;
  const frame = { contentWindow: source } as unknown as HTMLIFrameElement;
  const keys = createKeysSession(source, () => true);
  const receive = guestMessageReceiver(frame, source, {
    domains, routing: { connect: () => false } as never, keys,
    sendMedia: (request: unknown) => { out.push({ FORWARD_NATIVE_MEDIA: request }); return true; },
    cvm: (value: unknown) => { out.push({ FORWARD_CVM: value }); },
    closed: () => false, live: () => true,
    dispatch(event: MessageEvent) {
      if (!validEnvelope(event.data)) { rejectEnvelope(event, source, domains); return; }   // main.ts:331-334
      out.push('FORWARD_KEHTO');
    },
  });
  let n = 0;
  const show = (label: string, data: unknown) => {
    if (++n % 50 === 0) throw new Error('keep under the 64/s rate limit');
    out.length = 0; receive({ isTrusted: true, source, data, ports: [] } as unknown as MessageEvent);
    console.log(label, '=>', JSON.stringify(out));
  };
  show('INC-3 inc.subscribe no topic', { type: 'inc.subscribe', id: 's' });
  show('INC-3 inc.channel.open no target', { type: 'inc.channel.open', id: 'o' });
  show('INC-2 inc.subscribe napplet:foo', { type: 'inc.subscribe', id: 's2', topic: 'napplet:foo' });
  show('INC-2 inc.emit napplet:foo', { type: 'inc.emit', topic: 'napplet:foo', payload: 1 });
  show('INC-2 inc.emit empty topic', { type: 'inc.emit', topic: '', payload: 1 });
  show('INC-2 inc.emit query topic', { type: 'inc.emit', topic: 'napplet:note/open?a=1' });
  show('INTENT-3 invoke no action', { type: 'intent.invoke', id: 'i', request: { archetype: 'profile', convention: 'napplet:profile/open' } });
  show('INTENT-3 invoke query convention', { type: 'intent.invoke', id: 'i', request: { archetype: 'profile', action: 'open', convention: 'napplet:profile/open?pubkey=abc' } });
  show('NOTIFY-3 send missing title', { type: 'notify.send', id: 's4' });
  show('NOTIFY-3 send extra member', { type: 'notify.send', id: 's5', title: 't', tag: 'x' });
  show('NOTIFY-3 send empty title', { type: 'notify.send', id: 's6', title: '' });
  show('NOTIFY-3 permission extra member', { type: 'notify.permission.request', id: 'p1', foo: 1 });
  show('NOTIFY-2 send 4 actions', { type: 'notify.send', id: 's3', title: 'Hi', actions: ['a', 'b', 'c', 'd'].map(id => ({ id, label: id })) });
  show('NOTIFY ok send', { type: 'notify.send', id: 's1', title: 'Hi' });
  show('KEYS-2 register id with space', { type: 'keys.registerAction', id: 'req 5', action: { id: 'x', label: 'X' } });
  show('KEYS-2 register action extra member', { type: 'keys.registerAction', id: 'r6', action: { id: 'y', label: 'Y', extra: 1 } });
  show('KEYS-2 register Ctrl+Ctrl', { type: 'keys.registerAction', id: 'r4', action: { id: 'bad', label: 'Bad', defaultKey: 'Ctrl+Ctrl' } });
  show('KEYS-1 register a', { type: 'keys.registerAction', id: 'r1', action: { id: 'go', label: 'Go', defaultKey: 'a' } });
  show('KEYS-1 forward a', { type: 'keys.forward', key: 'a', code: 'KeyA', ctrl: false, alt: false, shift: false, meta: false });
  show('KEYS-3 register Space', { type: 'keys.registerAction', id: 'r2', action: { id: 'sp', label: 'Sp', defaultKey: 'Space' } });
  show('MEDIA-1 create owner napplet', { type: 'media.session.create', id: 'm1', owner: 'napplet' });
  show('MEDIA-1 create shell no source', { type: 'media.session.create', id: 'm2', owner: 'shell' });
  show('MEDIA-1 create no owner', { type: 'media.session.create', id: 'm3', source: { url: 'https://x.example/a.mp4' } });
  show('MEDIA create ok', { type: 'media.session.create', id: 'm4', owner: 'shell', source: { url: 'https://x.example/a.mp4' } });
  show('LINK-1 label number', { type: 'link.open', id: '1', url: 'https://example.com', options: { label: 5 } });
});
