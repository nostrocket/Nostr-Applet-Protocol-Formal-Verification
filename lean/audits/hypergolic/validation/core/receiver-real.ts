// Validation probe: replays every bound-port `message` input of lean/traces through Hypergolic's REAL
// guestMessageReceiver (runtime/src/guest-message-receiver.ts), not the audit adapter's copy of its
// side-lane routing. dispatch() mirrors main.ts: validEnvelope ? forward : rejectEnvelope.
import '../../core/win-stub.ts';
import { guestMessageReceiver } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-message-receiver.ts';
import { validEnvelope, rejectEnvelope } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-envelope.ts';
import { SUPPORTED_CAPABILITY_DOMAINS } from '/Users/gareth/git/napplets/hypergolic/src/runtime/capability-protocol.ts';
import { readFileSync, readdirSync } from 'node:fs';
const dir = process.argv[2];
const domains = [...SUPPORTED_CAPABILITY_DOMAINS];
const count: Record<string, number> = {};
let steps = 0, files = 0;
for (const f of readdirSync(dir).filter(f => f.endsWith('.in.ndjson')).sort()) {
  files++;
  const name = f.replace('.in.ndjson', '');
  const ins = readFileSync(`${dir}/${f}`, 'utf8').trim().split('\n').slice(1).map(l => JSON.parse(l));
  const outs = readFileSync(`${dir}/${name}.out.ndjson`, 'utf8').trim().split('\n').map(l => JSON.parse(l));
  const bound = new Set<number>();
  ins.forEach((inp, i) => {
    for (const o of outs[i].outputs) { if (o.t === 'bound') bound.add(o.port); if (o.t === 'closePort') bound.delete(o.port); }
    if (inp.t !== 'message' || !bound.has(inp.port)) return;
    steps++;
    const replies: any[] = []; let lane = 'none';
    const source: any = { postMessage: (m: any) => replies.push(m) };
    const frame: any = { contentWindow: source };
    const recv = guestMessageReceiver(frame, source, {
      domains, routing: { connect: () => false } as any,
      keys: { receive: () => { lane = 'keys'; } } as any,
      sendMedia: (() => { lane = 'media'; return true; }) as any,
      cvm: () => { lane = 'cvm'; },
      closed: () => false, live: () => true,
      dispatch: (event: MessageEvent) => {
        if (validEnvelope(event.data)) lane = 'forwarded'; else { lane = 'rejected'; rejectEnvelope(event, source, domains); }
      },
    });
    recv({ isTrusted: true, source, data: inp.msg, ports: [] } as any);
    if (lane === 'none') lane = 'media-dropped';
    count[lane] = (count[lane] ?? 0) + 1;
    console.log(`${name}#${i} ${inp.msg?.type} lane=${lane} reply=${replies.length ? JSON.stringify(replies[0]).slice(0, 140) : '-'}`);
  });
}
console.log(`files=${files} steps=${steps} lanes=${JSON.stringify(count)}`);
