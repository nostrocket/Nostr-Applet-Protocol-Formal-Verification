// Validation probe for RELAY-3..8 and OUTBOX-2..5. Imports Hypergolic's real code only.
// Stubs: `window` timers, the native host bridge (records posts, lets the probe inject
// native stream frames), and the relay port for query. Nothing here decides a reply.
// Run: NODE_PATH=<hypergolic>/node_modules esbuild stream-val.test.mts --bundle --format=esm --platform=node --outfile=<tmp>.mjs && node <tmp>.mjs
(globalThis as any).window = { setTimeout, clearTimeout, addEventListener() {}, removeEventListener() {} };
import { finalizeEvent } from 'nostr-tools/pure';
import { createNativeClient } from '../../../../../hypergolic/runtime/src/native-client.ts';
import { outboxReadFailure } from '../../../../../hypergolic/src/outbox/query-contract.ts';
import { parseOutboxPublish } from '../../../../../hypergolic/src/outbox/publication-contract.ts';

const listeners: any[] = []; const posted: any[] = [];
const host = { postMessage: (m: string) => posted.push(JSON.parse(m)), addEventListener: (_: string, l: any) => listeners.push(l), removeEventListener() {} };
const client = createNativeClient(host as any, 'gen1');
const deliveries = new Map<number, number>();
const push = (seq: number, response: any) => { const d = (deliveries.get(seq) ?? 0) + 1; deliveries.set(seq, d);
  for (const l of listeners) l({ data: JSON.stringify({ type: 'capability.stream', sessionId: 'gen1', sequence: seq, delivery: d, response: JSON.stringify(response) }) }); };
const sk = new Uint8Array(32); sk[31] = 7;
const ev = (kind: number, content = 'x') => JSON.parse(JSON.stringify(finalizeEvent({ kind, content, tags: [], created_at: 1_700_000_000 }, sk)));
const pk = ev(1).pubkey;
const guest: any[] = [];
const sub = (m: any) => { try { client.subscribe(m, r => guest.push(r)); return 'started'; } catch (e) { return 'THROWS ' + (e as Error).message; } };
const seqOf = (type: string, subId: string) => posted.filter(p => p.type === 'relay-stream').find(p => { const m = JSON.parse(p.message); return m.subId === subId && m.type === type; })?.sequence;

for (const d of ['relay', 'outbox'] as const) {
  const filters = [{ authors: [pk], kinds: [1] }];
  console.log(`${d} A subscribe:`, sub({ type: `${d}.subscribe`, id: 'a1', subId: d + '-A', filters }));
  const seqA = seqOf(`${d}.subscribe`, d + '-A');
  let n = guest.length; client.close({ type: `${d}.close`, id: 'c1', subId: d + '-A' } as any);
  console.log(`${d}.close -> guest messages = ${guest.length - n}; native got`, JSON.stringify(posted.at(-1)?.message));
  // Refutation attempt: native answers the close with a terminal `closed` frame.
  n = guest.length; push(seqA, { type: `${d}.closed`, subId: d + '-A' });
  console.log(`${d}: native "${d}.closed" frame after close -> guest messages = ${guest.length - n}`);
  console.log(`${d} reuse CLOSED subId A:`, sub({ type: `${d}.subscribe`, id: 'a2', subId: d + '-A', filters }));
  console.log(`${d} B subscribe:`, sub({ type: `${d}.subscribe`, id: 'b1', subId: d + '-B', filters }));
  console.log(`${d} reuse LIVE subId B:`, sub({ type: `${d}.subscribe`, id: 'b2', subId: d + '-B', filters }));
  n = guest.length; push(seqOf(`${d}.subscribe`, d + '-B'), { type: `${d}.event`, subId: d + '-B', result: { event: ev(1, 'old-B') } });
  console.log(`${d} old B after refused reuse delivers:`, JSON.stringify(guest.slice(n).map(g => [g.type, g.subId, g.result?.event?.content])));
  client.close({ type: `${d}.close`, id: 'c2', subId: d + '-B' } as any);
}
// The claimed-subId history is shared by both domains (native-client.ts:262).
console.log('cross-domain: outbox.subscribe with a subId relay used:', sub({ type: 'outbox.subscribe', id: 'x1', subId: 'relay-A', filters: [{ authors: [pk], kinds: [1] }] }));

console.log('OUTBOX-4 resolveRelays failure:', JSON.stringify(outboxReadFailure({ type: 'outbox.resolveRelays', id: 'r1', target: 5 }, 'invalid filter')));
const tpl = { kind: 1, content: 'hi', tags: [], created_at: 1 };
const user = 'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5';
for (const [l, e] of [['3-key (trace outbox p2)', { kind: 1, content: 'hi', tags: [] }], ['4-key', tpl], ['5-key', { ...tpl, extra: 1 }]] as const) {
  try { parseOutboxPublish({ type: 'outbox.publish', id: 'p2', event: e, options: { toOutbox: false, relays: ['wss://relay.example.com'] } }, user); console.log(`outbox.publish ${l}: ACCEPTED`); }
  catch (x: any) { console.log(`outbox.publish ${l}: REJECTED ${x.message}`); }
}
process.exit(0);
