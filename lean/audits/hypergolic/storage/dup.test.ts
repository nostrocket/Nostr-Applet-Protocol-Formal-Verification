import test from 'node:test';
import { createCapabilityBroker } from '/Users/gareth/git/napplets/hypergolic/src/runtime/capability-broker.ts';
import { NativeLeases } from '/Users/gareth/git/napplets/hypergolic/tests/runtime/native-leases.ts';
import { hex, setup } from '/Users/gareth/git/napplets/hypergolic/tests/storage/harness.ts';
const config:any = { sessionId: 's-1', generation: 'g-1', epoch: 0, user: hex(1), publisher: hex(2), appId: 'my-napplet', version: hex(3), instanceId: 'i-1', fixture: 'state-lab', domains: ['theme','identity','storage'] };
test('dup', async t => {
  const { database } = await setup(t), native = new NativeLeases();
  const b = createCapabilityBroker(database, native, {registration: config, assertActive() {}});
  async function invoke(req: unknown) { const tok = native.add(config, req); await b.dispatch(tok); return native.results.get(tok); }
  console.log('D1', JSON.stringify(await invoke({type:'storage.set', id:'a1', key:'k', value:'v'})));
  console.log('D2', JSON.stringify(await invoke({type:'storage.get', id:'a1', key:'k'})));
  for (let i=0;i<1030;i++) { const r:any = await invoke({type:'storage.get', id:'n'+i, key:'k'}); if (r?.error) { console.log('D4 first error at request', i, JSON.stringify(r)); break; } }
  console.log('D3', JSON.stringify(await invoke({type:'storage.get', id:'a1', key:'k'})));
});
