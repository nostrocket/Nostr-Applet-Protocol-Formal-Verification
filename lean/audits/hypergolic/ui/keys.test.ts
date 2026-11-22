import { test } from 'node:test';
import { createKeysSession } from '/Users/gareth/git/napplets/hypergolic/runtime/src/keys-adapter.ts';
test('keys', () => {
  const out: any[] = [];
  const s = createKeysSession({postMessage: (v: any) => out.push(v)} as any, () => true);
  const show = (label: string, m: any) => { out.length = 0; s.receive(m); console.log(label, JSON.stringify(out)); };
  show('register A:', {type:'keys.registerAction', id:'r1', action:{id:'go', label:'Go', defaultKey:'a'}});
  show('forward a:', {type:'keys.forward', key:'a', code:'KeyA', ctrl:false, alt:false, shift:false, meta:false});
  show('forward A:', {type:'keys.forward', key:'A', code:'KeyA', ctrl:false, alt:false, shift:false, meta:false});
  show('register Space:', {type:'keys.registerAction', id:'r2', action:{id:'sp', label:'Sp', defaultKey:'Space'}});
  show('register Ctrl+S:', {type:'keys.registerAction', id:'r3', action:{id:'save', label:'Save', defaultKey:'Ctrl+S'}});
  show('register bad combo:', {type:'keys.registerAction', id:'r4', action:{id:'bad', label:'Bad', defaultKey:'Ctrl+Ctrl'}});
  show('register id w/ space:', {type:'keys.registerAction', id:'req 5', action:{id:'x', label:'X'}});
  show('register action extra field:', {type:'keys.registerAction', id:'r6', action:{id:'y', label:'Y', extra:1}});
  show('register empty label:', {type:'keys.registerAction', id:'r7', action:{id:'z', label:''}});
  show('dup:', {type:'keys.registerAction', id:'r8', action:{id:'go', label:'Go'}});
  show('unknown type:', {type:'keys.foo'});
});
