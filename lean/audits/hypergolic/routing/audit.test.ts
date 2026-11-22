import test from 'node:test';
import assert from 'node:assert/strict';
import {setup, reviewReady, tick, user} from '/Users/gareth/git/napplets/hypergolic/tests/routing/harness.ts';
import {modernHandler} from '/Users/gareth/git/napplets/hypergolic/tests/routing/fixtures.ts';
import {parseRoutingMessage} from '/Users/gareth/git/napplets/hypergolic/src/routing/routing-contract.ts';
const tryParse = (m: unknown) => { try { return JSON.stringify(parseRoutingMessage(m)); } catch (e) { return 'THROWS ' + (e as Error).message; } };
test('P1 parse divergences', () => {
  console.log('missing action:', tryParse({type:'intent.invoke',id:'i',request:{archetype:'profile',convention:'napplet:profile/open'}}));
  console.log('missing convention:', tryParse({type:'intent.invoke',id:'i',request:{archetype:'profile',action:'open'}}));
  console.log('query convention:', tryParse({type:'intent.invoke',id:'i',request:{archetype:'profile',action:'open',convention:'napplet:profile/open?pubkey=abc'}}));
  console.log('extra sender member:', tryParse({type:'intent.invoke',id:'i',request:{archetype:'profile',action:'open',convention:'napplet:profile/open',sender:'x'}}));
  console.log('handlerHint:', tryParse({type:'intent.invoke',id:'i',request:{archetype:'profile',action:'open',convention:'napplet:profile/open',handlerHint:{address:'35129:'+'a'.repeat(64)+':x'}}}));
  console.log('intent.launch:', tryParse({type:'intent.launch',id:'l',target:{address:'35129:'+'a'.repeat(64)+':chess'}}));
  console.log('inc.subscribe no topic:', tryParse({type:'inc.subscribe',id:'s'}));
  console.log('inc.channel.open no target:', tryParse({type:'inc.channel.open',id:'o'}));
  console.log('inc.emit napplet:Note/open:', tryParse({type:'inc.emit',topic:'napplet:Note/open'}));
  console.log('inc.emit napplet:foo:', tryParse({type:'inc.emit',topic:'napplet:foo'}));
  console.log('inc.subscribe napplet:foo:', tryParse({type:'inc.subscribe',id:'s',topic:'napplet:foo'}));
  console.log('inc.emit query topic:', tryParse({type:'inc.emit',topic:'napplet:note/open?a=1'}));
  console.log('inc.emit empty topic:', tryParse({type:'inc.emit',topic:''}));
});
test('P2 INC sender/peer is the bare d tag, shared across publishers', async t => {
  const h = await setup(t); await h.register(h.target); await h.subscribeTarget('t1');
  const other = {...h.source, publisher: '05'.repeat(32), generation: 'other-source', sessionId: 'other-view', instanceId: 'other-view'};
  await h.register(h.source); await h.register(other);
  await h.dispatch(h.source, {type:'inc.emit', topic:'t1', payload:1}).promise;
  await h.dispatch(other, {type:'inc.emit', topic:'t1', payload:2}).promise;
  console.log('INC senders:', JSON.stringify(h.sent.map(s => s.message)));
  // channel open by d tag; two live views with same d -> refused
  const open = h.dispatch(h.target, {type:'inc.channel.open', id:'o', target:'caller'}); await open.promise;
  console.log('open to shared d:', JSON.stringify(open.reply()));
  const self = h.dispatch(h.source, {type:'inc.channel.open', id:'self', target:'caller'}); await self.promise;
  console.log('open (self+other share d):', JSON.stringify(self.reply()));
});
test('P3 channel limit and close reason', async t => {
  const h = await setup(t); await h.register(h.source); await h.register(h.target);
  let last: any;
  for (let i = 0; i < 9; i++) {
    const c = h.dispatch(h.source, {type:'inc.channel.open', id:'o'+i, target:h.target.appId});
    for (let k=0;k<20 && !h.reviews.getSnapshot();k++) await tick();
    const r = h.reviews.getSnapshot(); if (r) h.reviews.decide(r.id, {allow:true});
    await c.promise; last = c.reply();
  }
  console.log('9th open (limit 8):', JSON.stringify(last));
  const id = h.sent.find(s => s.message.type==='inc.channel.opened')!.message.channelId;
  const n = h.sent.length; await h.dispatch(h.source, {type:'inc.channel.close', channelId:id}).promise;
  console.log('close msgs:', JSON.stringify(h.sent.slice(n).map(s=>s.message)));
});
test('P4 inc.emit query topic transposed by runtime', async t => {
  const h = await setup(t); await h.register(h.target); await h.subscribeTarget('napplet:note/open');
  await h.dispatch(h.source, {type:'inc.emit', topic:'napplet:note/open?a=1'}).promise;
  console.log('query-topic delivery to exact subscriber of napplet:note/open:', JSON.stringify(h.sent.map(s=>s.message)));
});
test('P5 legacy archetype-tag handler is an intent target', async t => {
  const h = await setup(t);
  const av = h.dispatch(h.source, {type:'intent.available', id:'a', archetype:'note'}); await av.promise;
  console.log('legacy candidate:', JSON.stringify(av.reply().availability.candidates[0]));
});
test('P6 explicit unknown handler / explicit incompatible handler', async t => {
  const h = await setup(t, await modernHandler(), ['intent']);
  const unknown = h.dispatch(h.source, {type:'intent.invoke', id:'u', request:{archetype:'napptest', action:'open', convention:'napplet:napptest/open', handler:'35129:'+'f'.repeat(64)+':nope'}});
  await unknown.promise; console.log('explicit unknown:', JSON.stringify(unknown.reply()));
  const hid = '35129:'+h.a.manifest.pubkey+':modern-handler';
  const bad = h.dispatch(h.source, {type:'intent.invoke', id:'b', request:{archetype:'napptest', action:'edit', convention:'napplet:napptest/edit', handler:hid}});
  for (let k=0;k<20 && !h.reviews.getSnapshot();k++) await tick();
  console.log('prompted for incompatible explicit handler:', JSON.stringify(h.reviews.getSnapshot()?.request.kind ?? null));
  const r = h.reviews.getSnapshot(); if (r) h.reviews.decide(r.id, {allow:true});
  await bad.promise; console.log('explicit incompatible:', JSON.stringify(bad.reply()));
  const mism = h.dispatch(h.source, {type:'intent.invoke', id:'m', request:{archetype:'napptest', action:'open', convention:'napplet:napptest/edit'}});
  await mism.promise; console.log('convention/action mismatch:', JSON.stringify(mism.reply()));
  const none = h.dispatch(h.source, {type:'intent.invoke', id:'n', request:{archetype:'emoji-list', action:'open', convention:'napplet:emoji-list/open'}});
  await none.promise; console.log('no handler:', JSON.stringify(none.reply()));
});
