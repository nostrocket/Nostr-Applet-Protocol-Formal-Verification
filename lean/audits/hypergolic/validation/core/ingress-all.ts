// Trace adapter: replays lean/traces/*.in.ndjson through Hypergolic's WebView ingress
// (runtime/src/guest-message-receiver.ts routing + guest-envelope.ts validEnvelope/rejectEnvelope,
// media-wire projection) and diffs each message step against *.out.ndjson.
import '../../core/win-stub.ts';
import { validEnvelope, rejectEnvelope } from '/Users/gareth/git/napplets/hypergolic/runtime/src/guest-envelope.ts';
import { projectMediaRequest, mediaRequestId } from '/Users/gareth/git/napplets/hypergolic/runtime/src/media-wire.ts';
import { SUPPORTED_CAPABILITY_DOMAINS } from '/Users/gareth/git/napplets/hypergolic/src/runtime/capability-protocol.ts';
import { readFileSync, readdirSync } from 'node:fs';
const dir = process.argv[2];
const domains = [...SUPPORTED_CAPABILITY_DOMAINS];
type Row = { trace: string; step: number; type: string; oracle: string; hyper: string; verdict: string };
const rows: Row[] = [];
const transport: Record<string, number> = {};
function ingress(msg: any): { lane: string; replies: any[] } {
  const replies: any[] = [];
  const source = { postMessage: (m: any) => replies.push(m) } as any;
  const type = msg?.type;
  if (typeof type === 'string' && type.startsWith('keys.')) return { lane: 'keys-lane', replies };
  if (typeof type === 'string' && type.startsWith('media.')) {
    const req = projectMediaRequest(msg);
    if (req) return { lane: 'media-lane', replies };
    if (type === 'media.session.create') { const id = mediaRequestId(msg.id); if (id) replies.push({ type: 'media.session.create.result', id, error: 'Unsupported media request.' }); }
    return { lane: 'media-dropped', replies };
  }
  if (typeof type === 'string' && type.startsWith('cvm.')) return { lane: 'cvm-lane', replies };
  if (validEnvelope(msg)) return { lane: 'forwarded', replies };
  rejectEnvelope({ data: msg } as any, source, domains);
  return { lane: 'rejected', replies };
}
for (const f of readdirSync(dir).filter(f => f.endsWith('.in.ndjson')).sort()) {
  const name = f.replace('.in.ndjson', '');
  const ins = readFileSync(`${dir}/${f}`, 'utf8').trim().split('\n').slice(1).map(l => JSON.parse(l));
  const outs = readFileSync(`${dir}/${name}.out.ndjson`, 'utf8').trim().split('\n').map(l => JSON.parse(l));
  const bound = new Set<number>();
  ins.forEach((inp, i) => {
    const out = outs[i].outputs as any[];
    for (const o of out) { if (o.t === 'bound') bound.add(o.port); if (o.t === 'closePort') bound.delete(o.port); }
    if (inp.t !== 'message') { if (['hello', 'windowMsg', 'portClosed'].includes(inp.t)) transport[inp.t] = (transport[inp.t] ?? 0) + 1; return; }
    if (!bound.has(inp.port)) return; // unbound-port traffic: Hypergolic analogue is unknown event.source, dropped
    const sends = out.filter(o => o.t === 'send' && o.port === inp.port).map(o => o.msg);
    const { lane, replies } = ingress(inp.msg);
    const o = sends.length ? JSON.stringify(sends[0]) : (out.length ? `(${out.map(x => x.t).join(',')})` : '(silent)');
    let verdict = 'same';
    if (lane === 'forwarded' || lane.endsWith('-lane')) verdict = 'forwarded';
    else if (!sends.length && replies.length) verdict = 'DIFF: Hypergolic replies where oracle is silent';
    else if (sends.length && !replies.length) verdict = out.some(x => x.t !== 'send') && !sends.length ? 'same' : 'DIFF: oracle replies, Hypergolic drops at ingress';
    else if (sends.length && replies.length) verdict = JSON.stringify(sends[0]) === JSON.stringify(replies[0]) ? 'same' : 'DIFF: reply differs';
    else if (!sends.length && !replies.length && out.length) verdict = 'DIFF: oracle acts (host call/effect), Hypergolic drops at ingress';
    rows.push({ trace: name, step: i, type: String(inp.msg?.type), oracle: o.slice(0, 160), hyper: lane + (replies.length ? ' ' + JSON.stringify(replies[0]).slice(0, 160) : ''), verdict });
  });
}
for (const r of rows) console.log(`ROW ${r.trace}#${r.step} ${r.type} => ${r.verdict} [${r.hyper}] oracle=${r.oracle}`);
const diffs = rows.filter(r => r.verdict.startsWith("DIFF"));
for (const r of diffs) console.log(`${r.trace}#${r.step} ${r.type}\n  oracle: ${r.oracle}\n  hyper:  ${r.hyper}\n  ${r.verdict}`);
const by = (k: string) => rows.filter(r => r.verdict === k).length;
console.log(`\nmessage steps on bound ports: ${rows.length}; forwarded to NAP handlers: ${by('forwarded')}; same at ingress: ${by('same')}; diffs: ${diffs.length}`);
console.log('transport inputs with no Hypergolic equivalent:', JSON.stringify(transport));
