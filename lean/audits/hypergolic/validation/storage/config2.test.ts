// Validation probe for CONFIG-3..8 and CONFIG-10. Uses Hypergolic's real captureConfigSchema and
// ConfigBroker through Hypergolic's own tests/presentation/config-harness.ts (Map-backed store only).
// Run from the Hypergolic root:
//   node --experimental-strip-types --test ../lean/audits/hypergolic/validation/storage/config2.test.ts
import test from 'node:test';
import {setup} from '../../../../../hypergolic/tests/presentation/config-harness.ts';
import {captureConfigSchema} from '../../../../../hypergolic/src/presentation/config-schema.ts';
const out=(l:string,v:unknown)=>console.log(l,JSON.stringify(v));
function cap(s:unknown){try{captureConfigSchema(s);return 'accepted';}catch(e:any){return 'rejected:'+e.code;}}
const P=(p:object,extra:object={})=>({type:'object',properties:p,...extra});
test('schema capture', ()=>{
  out('C3a secret string+default', cap(P({n:{type:'string','x-napplet-secret':true,default:'x'}})));
  out('C3b secret integer+default', cap(P({n:{type:'integer','x-napplet-secret':true,default:1}})));
  out('C3c secret integer, no default', cap(P({n:{type:'integer','x-napplet-secret':true}})));
  out('C3d secret array+default', cap(P({a:{type:'array',items:{type:'string'},'x-napplet-secret':true,default:[]}})));
  out('C5a root no properties', cap({type:'object'}));
  out('C5b nested object no properties', cap(P({o:{type:'object'}})));
  out('C5c additionalProperties schema', cap(P({},{additionalProperties:{type:'string'}})));
  out('C5d minimum on string', cap(P({s:{type:'string',minimum:1}})));
  out('C5e minLength on number', cap(P({s:{type:'number',minLength:1}})));
  out('C5f minItems on string', cap(P({s:{type:'string',minItems:1}})));
  out('C6a x-napplet-future', cap(P({s:{type:'string','x-napplet-future':{}}})));
  out('C6b x-foo', cap(P({s:{type:'string','x-foo':1}})));
  out('C6c unknown keyword foo', cap(P({s:{type:'string',foo:1}})));
  out('C6d oneOf', cap(P({s:{type:'string',oneOf:[]}})));
  out('C6e pattern', cap(P({s:{type:'string',pattern:'a'}})));
  out('C6f $ref', cap(P({s:{'$ref':'#/x'}})));
  out('C6g $schema draft-04 at root', cap(P({},{'$schema':'http://json-schema.org/draft-04/schema#'})));
});
test('broker', async t=>{
  const h=await setup(t);
  const B={type:'object',properties:{theme:{type:'string',default:'light'}}};
  // CONFIG-7
  for (const [version,$version] of [[12,11],[11,11],[12,undefined],[undefined,13]] as const) {
    const r=h.dispatch({type:'config.registerSchema',id:'v'+version+'-'+$version,schema:{...B,...($version===undefined?{}:{'$version':$version})},...(version===undefined?{}:{version})}); await r.promise;
    out(`C7 version ${version} $version ${$version}`, r.reply());
  }
  // CONFIG-10: when the push is issued (native.send), has the correlated result already been
  // finished (capability.finish, which fills reply())?
  const order:string[]=[]; let current:{reply():unknown}|null=null; const push=h.sent.push.bind(h.sent);
  h.sent.push=(...items:any[])=>{for(const i of items)order.push('push '+i.message.type+' issued; result finished yet = '+(current?.reply()!==undefined));return push(...items);};
  const sub=h.dispatch({type:'config.subscribe'}); await sub.promise; order.length=0;
  const ok=h.dispatch({type:'config.registerSchema',id:'ok',schema:B,version:20}); current=ok; await ok.promise;
  order.push('result '+JSON.stringify(ok.reply())); out('C10 success order', order); order.length=0;
  const bad=h.dispatch({type:'config.registerSchema',id:'bad',schema:{type:'string'}}); current=bad; await bad.promise;
  order.push('result '+JSON.stringify(bad.reply())); out('C10 failure order', order);
});
