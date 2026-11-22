// Validation probe for RESOURCE-2..10. Run from the Hypergolic root:
//   node --experimental-strip-types --test ../lean/audits/hypergolic/validation/resource/resource-validation.test.ts
// Real code under test: resource-adapter (WebView), resource-broker, resource-service, resource-transfers,
// resource-contract, resource-mime. Stubs: the HTTPS resolver (returns fixed bytes), the native bridge
// (a direct call of the real broker.dispatch), the relay query (returns []), and the session authority.
import test from 'node:test';
import { randomUUID, createHash } from 'node:crypto';
import { gzipSync } from 'node:zlib';
import { createResourceTransfers } from '../../../../../hypergolic/src/resources/resource-transfers.ts';
import { createResourceBroker } from '../../../../../hypergolic/src/resources/resource-broker.ts';
import { createResourceService } from '../../../../../hypergolic/src/resources/resource-service.ts';
import { createResourceAdapter } from '../../../../../hypergolic/runtime/src/resource-adapter.ts';

const registration: any = {sessionId:'s',generation:'g',epoch:0,user:'1'.repeat(64),publisher:'2'.repeat(64),appId:'a',version:'3'.repeat(64),instanceId:'i',fixture:'f',domains:['resource']};
const authority = {nativeToken:randomUUID(),assertActive() {}};
function harness(https: (u:string)=>Promise<Uint8Array>) {
  const transfers = createResourceTransfers(randomUUID);
  const service = createResourceService({ https: https as any, servers:() => ['https://blossom.example.org'],
    sha256:async (b) => createHash('sha256').update(b).digest('hex'), query: { async query() { return []; } } as any });
  const broker = createResourceBroker({service,transfers}, {registration,assertActive(){}} as any);
  const native = { async request(message: any) {
    const result = await broker.dispatch(message,authority);
    if (result === null) throw Error('denied');
    return JSON.parse(result);
  } };
  return createResourceAdapter(native as any, () => () => true);
}
const brief = (r:any) => ({type:r.type,id:r.id.length>20?r.id.slice(0,8)+'…':r.id,error:r.error,mime:r.mime,blob:r.blob?`Blob(${r.blob.size})`:undefined,
  items:r.items?.map((i:any)=>({ok:i.ok,error:i.error,mime:i.mime}))});
async function run(adapter:any, message:any) { const out:any[]=[]; await adapter({message,send:(r:any)=>out.push(r)}); return out.map(brief); }
const show = (label:string, v:any) => console.log('VAL', label, JSON.stringify(v));
const enc = new TextEncoder();
const U = 'https://assets.public.org/';

test('resource validation', async () => {
  // RESOURCE-2: order of envelopes for one id while in flight
  { let release!: () => void; const gate = new Promise<void>(r => release = r);
    const a = harness(async () => { await gate; return enc.encode('hello'); });
    const seq:any[] = []; const send = (r:any) => seq.push(brief(r));
    const p1 = a({message:{type:'resource.bytes',id:'dup',url:U+'a'},send});
    const p2 = a({message:{type:'resource.bytes',id:'dup',url:U+'a'},send});
    await p2; release(); await p1; show('R2 envelopes-for-id-dup-in-order', seq); }
  // RESOURCE-3: legacy ids are capped at 1024 per session; SDK-format ids are not
  { const a = harness(async () => enc.encode('hello'));
    let firstFail = -1, err = '';
    for (let n = 1; n <= 1030 && firstFail < 0; n++) { const r = await run(a,{type:'resource.info',id:'legacy-'+n}); if (r[0].error) { firstFail = n; err = r[0].error; } }
    show('R3 first failing legacy id index', {firstFail, err});
    const b = harness(async () => enc.encode('hello')); let bad = 0;
    for (let n = 1; n <= 1100; n++) { const r = await run(b,{type:'resource.info',id:`hg-${n}-${randomUUID()}`}); if (r[0].error) bad++; }
    show('R3 failures among 1100 hg-<seq>-<uuid> ids', bad);
    show('R3 reuse of completed hg id', await run(b,{type:'resource.info',id:`hg-1100-${randomUUID()}`})); }
  // RESOURCE-4: fifth concurrent envelope; and URL-level waiting limits
  { let release!: () => void; const gate = new Promise<void>(r => release = r);
    const a = harness(async () => { await gate; return enc.encode('hi'); });
    const ps = [1,2,3,4,5].map(n => run(a,{type:'resource.bytes',id:'c'+n,url:U+n}));
    show('R4 fifth concurrent', await ps[4]); release(); show('R4 first four', (await Promise.all(ps.slice(0,4))).map(r=>r[0].type));
    let rel2!: () => void; const gate2 = new Promise<void>(r => rel2 = r);
    const b = harness(async () => { await gate2; return enc.encode('hi'); });
    const many = (id:string) => run(b,{type:'resource.bytesMany',id,urls:[1,2,3,4,5,6,7,8].map(n=>U+id+n)});
    const m = [many('m1'),many('m2'),many('m3'),many('m4')]; await new Promise(r=>setTimeout(r,50)); rel2();
    show('R4 four concurrent bytesMany x8', (await Promise.all(m)).map(r=>r[0].items?.map((i:any)=>i.ok?'ok':i.error).join(',') ?? r[0].error)); }
  // RESOURCE-8: sniff outcomes
  { const mk = (body:Uint8Array) => harness(async () => body);
    show('R8 html', await run(mk(enc.encode('<html><body>x</body></html>')),{type:'resource.bytes',id:'h',url:U+'h'}));
    show('R8 raw svg', await run(mk(enc.encode('<svg xmlns="http://www.w3.org/2000/svg"/>')),{type:'resource.bytes',id:'s',url:U+'s'}));
    show('R8 unknown binary', await run(mk(new Uint8Array([0,1,2,255])),{type:'resource.bytes',id:'b',url:U+'b'}));
    // RESOURCE-7 comparison: an SVG carried as base64 text is delivered as text/plain, like gzip
    show('R7 base64-of-svg as text', await run(mk(enc.encode(Buffer.from('<svg><script>alert(1)</script></svg>').toString('base64'))),{type:'resource.bytes',id:'t',url:U+'t'}));
    show('R7 gzip-of-svg', await run(mk(new Uint8Array(gzipSync(Buffer.from('<svg><script>alert(1)</script></svg>')))),{type:'resource.bytes',id:'z',url:U+'z'})); }
  // RESOURCE-9: one bad item discards the whole envelope
  { const a = harness(async () => enc.encode('hello'));
    show('R9 good + empty item', await run(a,{type:'resource.bytesMany',id:'e1',urls:[U+'a','']}));
    show('R9 good + 9000-byte https url', await run(a,{type:'resource.bytesMany',id:'e2',urls:[U+'a',U+'x'.repeat(9000)]}));
    show('R9 good + ftp item (per-item)', await run(a,{type:'resource.bytesMany',id:'e3',urls:[U+'a','ftp://x.org/a']}));
    show('R9 extra opts', await run(a,{type:'resource.bytes',id:'o',url:U+'a',opts:{}}));
    show('R9 id of 129 bytes', await run(a,{type:'resource.bytes',id:'x'.repeat(129),url:U+'a'}));
    show('R9 9 urls', await run(a,{type:'resource.bytesMany',id:'e4',urls:[1,2,3,4,5,6,7,8,9].map(n=>U+n)})); }
  // RESOURCE-6
  { const a = harness(async () => enc.encode('hello'));
    show('R6 data', await run(a,{type:'resource.bytesMany',id:'d',urls:['data:;base64,aGk%3D','data:;base64,aGk=','data:nocomma','data:,hi']})); }
});
