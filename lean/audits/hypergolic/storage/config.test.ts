import test from 'node:test';
import {setup} from '/Users/gareth/git/napplets/hypergolic/tests/presentation/config-harness.ts';
import {captureConfigSchema} from '/Users/gareth/git/napplets/hypergolic/src/presentation/config-schema.ts';
import {parseConfigMessage} from '/Users/gareth/git/napplets/hypergolic/src/presentation/config-contract.ts';
const out=(l:string,v:unknown)=>console.log(l,JSON.stringify(v));
function cap(s:unknown){try{captureConfigSchema(s);return 'accepted';}catch(e:any){return 'rejected:'+e.code;}}
test('schema capture', ()=>{
  const P=(p:object,extra:object={})=>({type:'object',properties:p,...extra});
  out('S1 secret number+default', cap(P({n:{type:'number','x-napplet-secret':true,default:1}})));
  out('S2 secret boolean+default', cap(P({n:{type:'boolean','x-napplet-secret':true,default:true}})));
  out('S3 secret object+default', cap(P({n:{type:'object',properties:{},'x-napplet-secret':true,default:{}}})));
  out('S4 invalid default (enum)', cap(P({t:{type:'string',enum:['a'],default:'b'}})));
  out('S5 root without properties', cap({type:'object'}));
  out('S6 schema-valued additionalProperties', cap(P({},{additionalProperties:{type:'string'}})));
  out('S7 minimum on string', cap(P({s:{type:'string',minimum:1}})));
  out('S8 $version string', cap(P({},{'$version':'x'})));
  out('S9 $schema nested', cap(P({s:{type:'string','$schema':'http://json-schema.org/draft-07/schema#'}})));
  out('S10 x-foo keyword', cap(P({s:{type:'string','x-foo':1}})));
  out('S11 patternProperties', cap(P({},{patternProperties:{}})));
  out('S12 $dynamicRef', cap(P({},{'$dynamicRef':'#a'})));
  out('S13 duplicate required', cap(P({a:{type:'string'}},{required:['a','a']})));
  out('S14 minimum>maximum', cap(P({a:{type:'number',minimum:5,maximum:1}})));
  out('S15 $version nested', cap(P({s:{type:'string','$version':1}})));
});
test('wire', ()=>{
  try{parseConfigMessage({type:'config.registerSchema',id:'r',schema:{},version:-1});out('W1','ok');}catch(e:any){out('W1 version -1 throws',e.message);}
  try{parseConfigMessage({type:'config.get',id:'g',extra:1});out('W2','ok');}catch(e:any){out('W2 get+extra throws',e.message);}
  try{parseConfigMessage({type:'config.registerSchema',id:'r'});out('W3','ok');}catch(e:any){out('W3 no schema throws',e.message);}
});
test('broker', async t=>{
  const h=await setup(t);
  const A={type:'object',properties:{theme:{type:'string',enum:['dark','light'],default:'dark'}}};
  const B={type:'object',properties:{theme:{type:'string',enum:['dark','light'],default:'light'}}};
  await h.register(A,1); out('B1 after A', await h.get());
  await h.register(B,2); out('B2 after B (no user edit)', await h.get());
  out('B2b stored records', [...h.records.values()]);
  // persistence of schema across endpoints/reload
  const peer={...h.source,generation:'peer-gen',sessionId:'peer-view',instanceId:'peer-view'};
  const g=h.dispatch({type:'config.get',id:'peer-get'},peer); await g.promise; out('B3 peer same scope get reply', g.reply()); out('B3 sent', h.sent.at(-1));
  // version conflict across endpoints
  const r=h.dispatch({type:'config.registerSchema',id:'old',schema:A,version:1},peer); await r.promise; out('B4 peer registers v1 after v2', r.reply());
  // version vs $version mismatch
  const r2=h.dispatch({type:'config.registerSchema',id:'mm',schema:{...B,'$version':2},version:3}); await r2.promise; out('B5 version 3 with $version 2', r2.reply());
  // ancestor default fallback
  const N={type:'object',default:{a:{x:1}},properties:{a:{type:'object',default:{},properties:{x:{type:'integer'}}}}};
  await h.register(N,5); out('B6 nested ancestor default', await h.get());
  // order of schemaError vs result
  h.sent.length=0; const bad=h.dispatch({type:'config.registerSchema',id:'bad',schema:{type:'string'}}); await bad.promise; out('B7 bad reply', bad.reply()); out('B7 pushes', h.sent.map(s=>s.message));
});
