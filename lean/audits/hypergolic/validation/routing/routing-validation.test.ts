// Validation probe: self-target INC channel.open ("Not checked"), INC-2, INC-4, INTENT-3.
// Uses Hypergolic's real RoutingBroker through its own test harness (tests/routing/harness.ts:
// native port, capability port and target activation are the repo's stubs; broker, contract,
// channels, catalog and review service are real).
// Run from the Hypergolic root:
//   node --experimental-strip-types --test --test-timeout=20000 ../lean/audits/hypergolic/validation/routing/routing-validation.test.ts
import test from 'node:test';
import { setup, tick } from '/Users/gareth/git/napplets/hypergolic/tests/routing/harness.ts';
test('A: true self-target (only one live endpoint has d=caller)', async t => {
  const h = await setup(t); await h.register(h.source); await h.register(h.target);
  const self = h.dispatch(h.source, { type: 'inc.channel.open', id: 'self', target: 'caller' }); await self.promise;
  console.log('A self-open reply:', JSON.stringify(self.reply()), 'review pending:', h.reviews.getSnapshot() !== null);
  const missing = h.dispatch(h.source, { type: 'inc.channel.open', id: 'missing', target: 'nobody' }); await missing.promise;
  console.log('A missing-target reply:', JSON.stringify(missing.reply()));
});
test('B: audit P2 scenario - another publisher shares d=caller', async t => {
  const h = await setup(t);
  const other = { ...h.source, publisher: '05'.repeat(32), generation: 'other-source', sessionId: 'other-view', instanceId: 'other-view' };
  await h.register(h.source); await h.register(other);
  const self = h.dispatch(h.source, { type: 'inc.channel.open', id: 'self', target: 'caller' });
  for (let k = 0; k < 20 && !h.reviews.getSnapshot(); k++) await tick();
  const review = h.reviews.getSnapshot() as any;
  console.log('B review pending:', review?.request.kind, 'peer publisher:', review?.request.peer?.publisher?.slice(0, 4), 'own publisher:', h.source.publisher.slice(0, 4));
  h.reviews.decide(review.id, { allow: false }); await self.promise;
  console.log('B reply after deny:', JSON.stringify(self.reply()));
  const again = h.dispatch(h.source, { type: 'inc.channel.open', id: 'self2', target: 'caller' });
  for (let k = 0; k < 20 && !h.reviews.getSnapshot(); k++) await tick();
  h.reviews.decide((h.reviews.getSnapshot() as any).id, { allow: true }); await again.promise;
  console.log('B reply after allow:', JSON.stringify(again.reply()), 'pushed:', JSON.stringify(h.sent.map(s => [s.generation, s.message])));
});
test('C: INC-2 asymmetry - subscribe napplet:foo accepted, emit napplet:foo never routed', async t => {
  const h = await setup(t); await h.register(h.target); await h.subscribeTarget('napplet:foo'); await h.register(h.source);
  const emit = h.dispatch(h.source, { type: 'inc.emit', topic: 'napplet:foo', payload: 1 }); await emit.promise;
  console.log('C delivered after emit napplet:foo:', JSON.stringify(h.sent.map(s => s.message)));
  const ok = h.dispatch(h.source, { type: 'inc.emit', topic: 'plain-foo', payload: 1 }); await ok.promise;
  console.log('C (control) unsubscribed plain topic delivered:', h.sent.length);
});
test('D: INTENT-3 action/convention mismatch against a legacy (archetype-tag) handler', async t => {
  const h = await setup(t); await h.register(h.target); await h.subscribeTarget('napplet:note/edit');
  const r = h.dispatch(h.source, { type: 'intent.invoke', id: 'mm', request: { archetype: 'note', action: 'open', convention: 'napplet:note/edit' } });
  for (let k = 0; k < 20 && !h.reviews.getSnapshot(); k++) await tick();
  const review = h.reviews.getSnapshot() as any; console.log('D review pending:', review?.request.kind ?? null);
  if (review) h.reviews.decide(review.id, { allow: true }); await r.promise;
  console.log('D mismatch reply:', JSON.stringify(r.reply()), 'delivered:', JSON.stringify(h.sent.map(s => s.message)));
});
