import { finalizeEvent } from 'nostr-tools/pure';
import { createNativeRelayQuery } from '/Users/gareth/git/napplets/hypergolic/src/network/native-relay-query.ts';
import { parseRelayQuery } from '/Users/gareth/git/napplets/hypergolic/src/network/relay-query-contract.ts';
const sk = new Uint8Array(32); sk[31] = 1;
const ct = 'aGVsbG8gd29ybGQ=?iv=AAAAAAAAAAAAAAAAAAAAAA==';
const ev = JSON.parse(JSON.stringify(finalizeEvent({ kind: 4, content: ct, created_at: 100, tags: [['p', '22'.repeat(32)]] }, sk)));
let n = 0;
const port = { newInstanceId: () => '00000000-0000-4000-8000-' + String(++n).padStart(12, '0'), cancelPublishedRelay() {},
  queryPublishedRelay: async (_id: string, _u: string, _w: string, sub: string) => [JSON.stringify(['EVENT', sub, ev]), JSON.stringify(['EOSE', sub])] };
const req = parseRelayQuery({ type: 'relay.query', id: 'q', filters: [{ kinds: [4] }] });
const events = await createNativeRelayQuery(port as any, () => ['wss://one.example.com'], 1000).query(req.filters, new AbortController().signal, () => {});
console.log('relay.query kinds:[4] accepted; delivered', events.length, 'event(s); kind', events[0]?.event.kind, 'content=', events[0]?.event.content, 'sidecar=', JSON.stringify((events[0] as any)?.sidecar));
