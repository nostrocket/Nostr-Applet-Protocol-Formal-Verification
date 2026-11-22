(globalThis as any).window = { setTimeout, clearTimeout, addEventListener() {}, removeEventListener() {} };
const { createNativeClient } = await import('/Users/gareth/git/napplets/hypergolic/runtime/src/native-client.ts');
const { outboxReadFailure } = await import('/Users/gareth/git/napplets/hypergolic/src/outbox/query-contract.ts');
const { parseOutboxPublish } = await import('/Users/gareth/git/napplets/hypergolic/src/outbox/publication-contract.ts');
const listeners: any[] = []; const posted: any[] = [];
const client = createNativeClient({ postMessage: (m: string) => posted.push(JSON.parse(m)), addEventListener: (_: string, l: any) => listeners.push(l), removeEventListener() {} } as any, 'g');
const guest: any[] = [];
const sub = (m: any) => { try { client.subscribe(m, r => guest.push(r)); return 'started'; } catch (e) { return 'THROWN ' + e; } };
console.log('O1 subscribe', sub({ type: 'outbox.subscribe', id: 'i1', subId: 'S', filters: [{ kinds: [1] }] }));
const n = guest.length; client.close({ type: 'outbox.close', id: 'i2', subId: 'S' } as any);
console.log('O1 outbox.close guest replies =', guest.length - n, '(model: outbox.closed {subId:S})');
console.log('O2 subscribe T', sub({ type: 'outbox.subscribe', id: 'i3', subId: 'T', filters: [{ kinds: [1] }] }));
console.log('O2 reuse live T', sub({ type: 'outbox.subscribe', id: 'i4', subId: 'T', filters: [{ kinds: [1] }] }), '-> main.ts:126 sends outbox.closed{subId:T}');
console.log('O3 resolveRelays failure reply', JSON.stringify(outboxReadFailure({ type: 'outbox.resolveRelays', id: 'r1', target: 5 }, 'invalid filter')));
try { parseOutboxPublish({ type: 'outbox.publish', id: 'p2', event: { kind: 1, content: 'hi', tags: [] }, options: { toOutbox: false, relays: ['wss://relay.example.com'] } }, 'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5'); console.log('O4 trace p2 accepted'); } catch (e: any) { console.log('O4 trace p2 (outbox.in.ndjson) REJECTED', e.message); }
process.exit(0);
