import test from 'node:test';
import { randomUUID, createHash } from 'node:crypto';
import { gzipSync } from 'node:zlib';
import { npubEncode, noteEncode } from '/Users/gareth/git/napplets/hypergolic/node_modules/nostr-tools/lib/esm/nip19.js';
import { createResourceTransfers } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-transfers.ts';
import { createResourceBroker } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-broker.ts';
import { createResourceService } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-service.ts';
import { createResourceAdapter } from '/Users/gareth/git/napplets/hypergolic/runtime/src/resource-adapter.ts';
import { resourceInfo } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-contract.ts';

const registration: any = {sessionId:'s',generation:'g',epoch:0,user:'1'.repeat(64),publisher:'2'.repeat(64),appId:'a',version:'3'.repeat(64),instanceId:'i',fixture:'f',domains:['resource']};
const authority = {nativeToken:randomUUID(),assertActive() {}};
function harness(https: (u:string)=>Promise<Uint8Array>, query?: any) {
  const transfers = createResourceTransfers(randomUUID);
  const service = createResourceService({ https: https as any, servers:() => ['https://blossom.example.org'], sha256:async (b) => createHash('sha256').update(b).digest('hex'), query });
  const broker = createResourceBroker({service,transfers}, {registration,assertActive(){}} as any);
  const native = { async request(message: any) {
    const result = await broker.dispatch(message,authority);
    if (result === null) throw Error('denied');
    return JSON.parse(result);
  } };
  return createResourceAdapter(native as any, () => () => true);
}
async function run(adapter:any, message:any) { const out:any[]=[]; await adapter({message,send:(r:any)=>out.push(r)}); return out.map(r=>({...r, blob: r.blob? `Blob(${r.blob.size})`:undefined, items: r.items?.map((i:any)=>({url:i.url,ok:i.ok,error:i.error,mime:i.mime}))})); }
const show = (label:string, v:any) => console.log('RESULT', label, JSON.stringify(v));

test('resource wire probes', async () => {
  const enc = new TextEncoder();
  // 1 duplicate in-flight id
  let release!: () => void; const gate = new Promise<void>(r => release = r);
  const slow = harness(async () => { await gate; return enc.encode('hello'); });
  const p1 = run(slow, {type:'resource.bytes',id:'dup',url:'https://assets.public.org/a'});
  const p2 = run(slow, {type:'resource.bytes',id:'dup',url:'https://assets.public.org/a'});
  show('dup-second-while-inflight', await p2); release(); show('dup-first', await p1);
  // 2 reuse after completion
  const fast = harness(async () => enc.encode('hello'));
  show('reuse-1', await run(fast, {type:'resource.bytes',id:'r',url:'https://assets.public.org/a'}));
  show('reuse-2-after-complete', await run(fast, {type:'resource.bytes',id:'r',url:'https://assets.public.org/b'}));
  // 3 five concurrent distinct ids
  let rel2!: () => void; const gate2 = new Promise<void>(r => rel2 = r);
  const slow2 = harness(async () => { await gate2; return enc.encode('hi'); });
  const ps = [1,2,3,4,5].map(n => run(slow2, {type:'resource.bytes',id:'c'+n,url:'https://assets.public.org/'+n}));
  const fifth = await ps[4]; show('fifth-concurrent', fifth); rel2(); await Promise.all(ps.slice(0,4));
  // 4 nostr
  const npub = 'nostr:' + npubEncode('a'.repeat(64));
  const badnote = 'nostr:' + noteEncode('b'.repeat(64)).slice(0,-1) + 'q';
  const nsec = 'nostr:nsec1vl029mgpspedva04g90vltkh6fvh240zqtv9k0t9af8935ke9laqsnlfe5';
  const q = { async query() { return []; } };
  const ns = harness(async () => enc.encode('x'), q);
  show('nostr-items', await run(ns, {type:'resource.bytesMany',id:'n',urls:[npub,badnote,nsec]}));
  // 5 data urls and html
  const d = harness(async () => enc.encode('<html><body>x</body></html>'));
  show('data-items', await run(d, {type:'resource.bytesMany',id:'d',urls:['data:;base64,AA%3D%3D','data:nocomma','data:text/html,%3Chtml%3E','data:,%00%01','https://assets.public.org/page']}));
  // 6 blossom without extension
  const blob = enc.encode('hello'); const h = createHash('sha256').update(blob).digest('hex');
  const b = harness(async () => blob);
  show('blossom-noext', await run(b, {type:'resource.bytes',id:'b',url:'blossom:'+h}));
  // 7 extra field
  show('extra-opts-field', await run(fast, {type:'resource.bytes',id:'o',url:'https://assets.public.org/a',opts:{}}));
  // 8 empty url in bytesMany
  show('bytesMany-empty-item', await run(fast, {type:'resource.bytesMany',id:'e',urls:['https://assets.public.org/a','']}));
  // 9 long id
  show('long-id', await run(fast, {type:'resource.bytes',id:'x'.repeat(200),url:'https://assets.public.org/a'}));
  // 10 schemes
  show('schemes', await run(fast, {type:'resource.bytesMany',id:'s',urls:['http://assets.public.org/a','hashtree:nhash1qqqq','htree://'+'a'.repeat(64)+'/t','nhash1qqqq']}));
  show('info', resourceInfo());
  // 11 gzip / mime outside Lean allowlist
  const gz = harness(async () => new Uint8Array(gzipSync(enc.encode('x'.repeat(100)))));
  show('gzip', await run(gz, {type:'resource.bytes',id:'gz',url:'https://assets.public.org/a.gz'}));
});
