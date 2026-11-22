import { test } from 'node:test';
import { setup } from '/Users/gareth/git/napplets/hypergolic/tests/presentation/harness.ts';
import { parseNotifyMessage, captureNotifyRejection } from '/Users/gareth/git/napplets/hypergolic/src/presentation/notify-contract.ts';
const adapter = (m: unknown) => { try { parseNotifyMessage(m); return 'accepted'; } catch { return JSON.stringify(captureNotifyRejection(m)); } };
test('notify', async t => {
  const h = await setup(t);
  await h.allow();
  const s = h.dispatch(h.source, {type:'notify.send', id:'s1', title:'Hi'}); await s.promise;
  const nid = s.reply().notificationId; console.log('send ->', JSON.stringify(s.reply()));
  // peer tries to dismiss
  const p = h.dispatch(h.peer, {type:'notify.dismiss', notificationId: nid}); await p.promise;
  console.log('after peer dismiss cards=', h.broker.getSnapshot().cards.length);
  h.sent.length = 0;
  const d = h.dispatch(h.source, {type:'notify.dismiss', notificationId: nid}); await d.promise;
  console.log('after own dismiss cards=', h.broker.getSnapshot().cards.length, 'pushed to napplet:', JSON.stringify(h.sent.map(x => x.message)));
  const c = h.dispatch(h.source, {type:'notify.send', id:'s2', title:'Hi', channel:'news'}); await c.promise;
  console.log('unregistered channel ->', JSON.stringify(c.reply()));
  const b = h.dispatch(h.source, {type:'notify.send', id:'s3', title:'Hi', actions:[{id:'a',label:'A'},{id:'b',label:'B'},{id:'c',label:'C'},{id:'d',label:'D'}]});
  await b.promise; console.log('4 actions via broker ->', JSON.stringify(b.reply()));
  console.log('adapter 4 actions ->', adapter({type:'notify.send', id:'s3', title:'Hi', actions:[{id:'a',label:'A'},{id:'b',label:'B'},{id:'c',label:'C'},{id:'d',label:'D'}]}));
  console.log('adapter missing title ->', adapter({type:'notify.send', id:'s4'}));
  console.log('adapter extra field ->', adapter({type:'notify.send', id:'s5', title:'t', tag:'x'}));
  console.log('adapter empty title ->', adapter({type:'notify.send', id:'s6', title:''}));
  console.log('adapter perm extra field ->', adapter({type:'notify.permission.request', id:'p1', foo:1}));
});
