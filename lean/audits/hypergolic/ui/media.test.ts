import { test } from 'node:test';
import { projectMediaRequest } from '/Users/gareth/git/napplets/hypergolic/runtime/src/media-wire.ts';
test('media', () => {
  const c = (m: any) => JSON.stringify(projectMediaRequest({type:'media.session.create', id:'r1', ...m}));
  console.log('no owner ->', c({source:{url:'https://x/a.mp4'}}));
  console.log('owner napplet ->', c({owner:'napplet'}));
  console.log('shell no source ->', c({owner:'shell'}));
  console.log('shell w/ hint ->', c({owner:'shell', sessionId:'mine', source:{url:'https://x/a.mp4'}}));
  console.log('update ->', JSON.stringify(projectMediaRequest({type:'media.session.update', sessionId:'media-00000000-0000-4000-8000-000000000000', metadata:{title:'t'}})));
});
