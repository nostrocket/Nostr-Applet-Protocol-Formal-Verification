(globalThis as any).window = { setTimeout, clearTimeout, addEventListener() {}, removeEventListener() {} };
import { finalizeEvent } from 'nostr-tools/pure';
const { createNativeClient } = await import('/Users/gareth/git/napplets/hypergolic/runtime/src/native-client.ts');
const { parseOutboxPublish } = await import('/Users/gareth/git/napplets/hypergolic/src/outbox/publication-contract.ts');
const listeners: any[] = []; const posted: any[] = [];
const host = { postMessage: (m: string) => posted.push(JSON.parse(m)), addEventListener: (_: string, l: any) => listeners.push(l), removeEventListener() {} };
const client = createNativeClient(host as any, 'gen1');
const deliveries = new Map<number, number>();
const push = (seq: number, response: any) => { const d = (deliveries.get(seq) ?? 0) + 1; deliveries.set(seq, d);
  for (const l of listeners) l({ data: JSON.stringify({ type: 'capability.stream', sessionId: 'gen1', sequence: seq, delivery: d, response: JSON.stringify(response) }) }); };
const sk = new Uint8Array(32); sk[31] = 7;
const ev = (kind: number, content = 'x') => JSON.parse(JSON.stringify(finalizeEvent({ kind, content, tags: [], created_at: 1_700_000_000 }, sk)));
const guest: any[] = [];
const sub = (m: any) => { try { client.subscribe(m, r => guest.push(r)); } catch (e) { guest.push({ THROWN: String(e), note: 'main.ts:126 catch sends relay.closed' }); } };
const seqOf = (subId: string) => posted.filter(p => p.type === 'relay-stream').find(p => JSON.parse(p.message).subId === subId)?.sequence;

// 1. relay.close: any reply?
sub({ type: 'relay.subscribe', id: 'a1', subId: 'A', filters: [{ authors: [ev(1).pubkey] }] });
const before = guest.length; client.close({ type: 'relay.close', id: 'c1', subId: 'A' } as any);
console.log('1 close: guest messages after close =', guest.slice(before).length, '(model: relay.closed {subId:A})');
// 2. subId reuse after close
sub({ type: 'relay.subscribe', id: 'a2', subId: 'A', filters: [{ kinds: [1] }] });
console.log('2 reuse closed subId:', JSON.stringify(guest.at(-1)));
// 3. reuse while live
sub({ type: 'relay.subscribe', id: 'b1', subId: 'B', filters: [{ kinds: [1, 4] .filter(k=>k!==4) }] });
const n3 = guest.length; sub({ type: 'relay.subscribe', id: 'b2', subId: 'B', filters: [{ kinds: [1] }] });
console.log('3 reuse live subId:', JSON.stringify(guest.slice(n3)));
push(seqOf('B'), { type: 'relay.event', subId: 'B', result: { event: ev(1, 'after') } });
console.log('3b old B still delivering after "closed":', JSON.stringify(guest.at(-1)?.type), guest.at(-1)?.result?.event?.content);
// 4. encrypted kind 4 event on author-filter subscription
client.close({ type: 'relay.close', id: 'cB', subId: 'B' } as any);
sub({ type: 'relay.subscribe', id: 'd1', subId: 'D', filters: [{ authors: [ev(1).pubkey] }] });
const n4 = guest.length;
push(seqOf('D'), { type: 'relay.event', subId: 'D', result: { event: ev(4, 'aGVsbG8=?iv=AAAAAAAAAAAAAAAAAAAAAA==') } });
push(seqOf('D'), { type: 'relay.event', subId: 'D', result: { event: ev(1, 'plain after') } });
console.log('4 kind4 event on authors sub ->', JSON.stringify(guest.slice(n4)));
// 5. outbox.publish parse
const user = 'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5';
for (const [l, v] of [['cipher', { type: 'outbox.publish', id: 'o1', event: { kind: 4, content: 'aGVsbG8=?iv=AAAAAAAAAAAAAAAAAAAAAA==', tags: [], created_at: 1 } }],
  ['foreign pk', { type: 'outbox.publish', id: 'o2', event: { kind: 1, content: 'x', tags: [], created_at: 1, pubkey: 'b'.repeat(64) } }],
  ['private relay', { type: 'outbox.publish', id: 'o3', event: { kind: 1, content: 'x', tags: [], created_at: 1 }, options: { relays: ['wss://192.168.0.1'] } }]] as const) {
  try { const r = parseOutboxPublish(v, user); console.log('5 outbox.publish', l, 'ACCEPTED content=', r.event.content); } catch (e: any) { console.log('5 outbox.publish', l, 'REJECTED', e.message); }
}
process.exit(0);
