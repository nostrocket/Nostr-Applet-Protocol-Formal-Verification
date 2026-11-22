import test from 'node:test';
import { gunzipSync, gzipSync } from 'node:zlib';
import { randomUUID, createHash } from 'node:crypto';
import { createResourceTransfers } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-transfers.ts';
import { createResourceBroker } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-broker.ts';
import { createResourceService } from '/Users/gareth/git/napplets/hypergolic/src/resources/resource-service.ts';
import { createResourceAdapter } from '/Users/gareth/git/napplets/hypergolic/runtime/src/resource-adapter.ts';
const registration: any = {sessionId:'s',generation:'g',epoch:0,user:'1'.repeat(64),publisher:'2'.repeat(64),appId:'a',version:'3'.repeat(64),instanceId:'i',fixture:'f',domains:['resource']};
const authority = {nativeToken:randomUUID(),assertActive() {}};
function harness(https: any) {
  const transfers = createResourceTransfers(randomUUID);
  const service = createResourceService({ https, servers:() => [], sha256:async (b:any) => createHash('sha256').update(b).digest('hex') });
  const broker = createResourceBroker({service,transfers}, {registration,assertActive(){}} as any);
  return createResourceAdapter({ async request(m: any) { const r = await broker.dispatch(m,authority); if (r===null) throw Error('denied'); return JSON.parse(r); } } as any, () => () => true);
}
test('svgz + data', async () => {
  const svg = '<svg xmlns="http://www.w3.org/2000/svg"><script>alert(1)</script></svg>';
  const a = harness(async () => new Uint8Array(gzipSync(Buffer.from(svg))));
  const out: any[] = []; await a({message:{type:'resource.bytes',id:'z',url:'https://assets.public.org/x.svgz'},send:(r:any)=>out.push(r)});
  const r = out[0]; const bytes = r.blob ? Buffer.from(await r.blob.arrayBuffer()) : null;
  console.log('RESULT svgz', r.type, r.mime, bytes ? JSON.stringify(gunzipSync(bytes).toString()) : r.error);
  const out2: any[] = []; await a({message:{type:'resource.bytes',id:'d',url:'data:;base64,aGk%3D'},send:(r:any)=>out2.push(r)});
  console.log('RESULT data-pct-base64', JSON.stringify({type:out2[0].type, error:out2[0].error, mime:out2[0].mime}));
});
