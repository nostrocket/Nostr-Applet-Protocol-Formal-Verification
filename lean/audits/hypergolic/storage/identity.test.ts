import test from 'node:test';
import { createCapabilityBroker } from '/Users/gareth/git/napplets/hypergolic/src/runtime/capability-broker.ts';
import { NativeLeases } from '/Users/gareth/git/napplets/hypergolic/tests/runtime/native-leases.ts';
import { hex, setup } from '/Users/gareth/git/napplets/hypergolic/tests/storage/harness.ts';
const config:any = { sessionId: 's-1', generation: 'g-1', epoch: 0, user: hex(1), publisher: hex(2), appId: 'my-napplet', version: hex(3), instanceId: 'i-1', fixture: 'state-lab', domains: ['theme','identity','storage'] };
test('identity', async t => {
  const { database } = await setup(t), native = new NativeLeases();
  const b = createCapabilityBroker(database, native, {registration: config, assertActive() {}});
  async function invoke(req: unknown) { const tok = native.add(config, req); await b.dispatch(tok); return native.results.get(tok); }
  const o=(l:string,v:unknown)=>console.log(l,JSON.stringify(v));
  o('I1 getList no listType', await invoke({type:'identity.getList', id:'l1'}));
  o('I2 getPublicKey extra member', await invoke({type:'identity.getPublicKey', id:'p1', extra:1}));
  o('I3 getPublicKey first', await invoke({type:'identity.getPublicKey', id:'p2'}));
  o('I3 getPublicKey same id again', await invoke({type:'identity.getPublicKey', id:'p2'}));
  o('I4 getList listType number', await invoke({type:'identity.getList', id:'l2', listType: 5}));
});
