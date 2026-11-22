// Validation probe (ingress) for RELAY-3, RELAY-6, RELAY-7, RELAY-8. Calls Hypergolic's real validEnvelope/rejectEnvelope
// (the pair main.ts:331-332 runs) and the broker's queryFailure. The only stub is the reply sink.
// Run from the Hypergolic root:
//   node --experimental-strip-types --import ../lean/audits/hypergolic/validation/relay/register.mjs ../lean/audits/hypergolic/validation/relay/envelope-val.test.ts
import { validEnvelope, rejectEnvelope } from '../../../../../hypergolic/runtime/src/guest-envelope.ts';
import { createRequire } from 'node:module';
const { finalizeEvent } = createRequire(new URL('../../../../../hypergolic/package.json', import.meta.url))('nostr-tools/pure');
import { createNativeRelayQuery } from '../../../../../hypergolic/src/network/native-relay-query.ts';
import { parseRelayQuery } from '../../../../../hypergolic/src/network/relay-query-contract.ts';
import { queryFailure } from '../../../../../hypergolic/src/runtime/capability-protocol.ts';
const env = (label: string, data: any, domains = ['relay', 'outbox']) => { const out: any[] = []; const valid = validEnvelope(data);
  if (!valid) rejectEnvelope({ data } as any, { postMessage: (m: any) => out.push(m) } as any, domains);
  console.log(`ENV ${label}: valid=${valid} replies=${JSON.stringify(out)}`); };
const tpl = { kind: 1, content: 'hi', tags: [], created_at: 1 };
env('publishEncrypted', { type: 'relay.publishEncrypted', id: 'p1', event: tpl, recipient: 'a'.repeat(64) });
env('publish 3-key template (no created_at)', { type: 'relay.publish', id: 't1', event: { kind: 1, content: 'hi', tags: [] } });
env('publish 5-key template (extra member)', { type: 'relay.publish', id: 't2', event: { ...tpl, extra: true } });
env('publish no event', { type: 'relay.publish', id: 't3' });
env('publish foreign pubkey', { type: 'relay.publish', id: 't4', event: { ...tpl, pubkey: 'b'.repeat(64) } });
env('subscribe filters:"nope"', { type: 'relay.subscribe', id: 's1', subId: 'x', filters: 'nope' });
env('subscribe id:5', { type: 'relay.subscribe', id: 5, subId: 'y', filters: [{}] });
env('subscribe relay wss://10.0.0.1', { type: 'relay.subscribe', id: 's3', subId: 'z', filters: [{ kinds: [1] }], relay: 'wss://10.0.0.1' });
env('subscribe relay ws://', { type: 'relay.subscribe', id: 's4', subId: 'w', filters: [{ kinds: [1] }], relay: 'ws://relay.example.com' });
env('query filters:"nope"', { type: 'relay.query', id: 'q1', filters: 'nope' });
console.log('BROKER invalid relay.query reply:', JSON.stringify(queryFailure({ type: 'relay.query', id: 'q1', filters: 'nope' }, 'invalid relay query')));
// RELAY-8: stub relay port returns one signed note; the real query service builds the rows.
let i = 0; const sk = new Uint8Array(32); sk[31] = 7;
const note = JSON.parse(JSON.stringify(finalizeEvent({ kind: 1, content: 'q', tags: [], created_at: 1_700_000_000 }, sk)));
const port = { newInstanceId: () => '00000000-0000-4000-8000-' + String(++i).padStart(12, '0'), cancelPublishedRelay() {},
  queryPublishedRelay: async (_a: string, _b: string, _c: string, s: string) => [JSON.stringify(['EVENT', s, note]), JSON.stringify(['EOSE', s])] };
const rows = await createNativeRelayQuery(port as any, () => ['wss://one.example.com'], 1000).query(parseRelayQuery({ type: 'relay.query', id: 'q', filters: [{ kinds: [1] }] }).filters, new AbortController().signal, () => {});
console.log('RELAY-8 relay.query row keys:', JSON.stringify(rows.map(r => Object.keys(r))));
