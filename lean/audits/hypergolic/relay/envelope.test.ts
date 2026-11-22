import { validEnvelope, rejectEnvelope } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-envelope.ts';
const domains = ['relay','outbox'];
function run(label: string, data: any) {
  const posted: any[] = [];
  const valid = validEnvelope(data);
  if (!valid) rejectEnvelope({ data } as any, { postMessage: (m: any) => posted.push(m) } as any, domains);
  console.log(label, '| valid=', valid, '| replies=', JSON.stringify(posted));
}
const tpl = { kind: 1, content: 'hi', tags: [], created_at: 1 };
run('publishEncrypted valid', { type: 'relay.publishEncrypted', id: 'p1', event: tpl, recipient: 'a'.repeat(64) });
run('publishEncrypted nip04', { type: 'relay.publishEncrypted', id: 'p2', event: tpl, recipient: 'a'.repeat(64), encryption: 'nip04' });
run('publish w/ foreign pubkey', { type: 'relay.publish', id: 'p3', event: { ...tpl, pubkey: 'b'.repeat(64) } });
run('publish no event', { type: 'relay.publish', id: 'p4' });
run('publish nip04 ciphertext', { type: 'relay.publish', id: 'p5', event: { ...tpl, kind: 4, content: 'aGVsbG8=?iv=aGVsbG8=' } });
run('subscribe bad filters', { type: 'relay.subscribe', id: 's1', subId: 'x', filters: 'nope' });
run('subscribe bad id', { type: 'relay.subscribe', id: 5, subId: 'x', filters: [{}] });
run('subscribe filters [{}]', { type: 'relay.subscribe', id: 's2', subId: 'y', filters: [{}] });
run('subscribe scoped private', { type: 'relay.subscribe', id: 's3', subId: 'z', filters: [{kinds:[1]}], relay: 'wss://10.0.0.1' });
run('subscribe scoped localhost', { type: 'relay.subscribe', id: 's4', subId: 'w', filters: [{kinds:[1]}], relay: 'wss://localhost' });
run('subscribe kinds 4', { type: 'relay.subscribe', id: 's5', subId: 'v', filters: [{kinds:[4]}] });
run('close no id', { type: 'relay.close', subId: 'x' });
run('query bad filters', { type: 'relay.query', id: 'q1', filters: 'nope' });
run('unknown relay.foo', { type: 'relay.foo', id: 'u1' });
run('outbox.subscribe bad filters', { type: 'outbox.subscribe', id: 'o1', subId: 'os', filters: 'nope' });
run('outbox.close', { type: 'outbox.close', id: 'o2', subId: 'os' });
