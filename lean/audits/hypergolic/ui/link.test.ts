import { test } from 'node:test';
import { parseLinkRequest, linkRequestId } from '/Users/gareth/git/napplets/hypergolic/src/links/link-contract.ts';
const run = (m: any) => { const id = linkRequestId(m); if (id === null) return 'dropped'; try { parseLinkRequest(m); return 'accepted'; } catch { return 'denied invalid-url'; } };
test('link', () => {
  console.log('label number ->', run({type:'link.open', id:'1', url:'https://example.com', options:{label:5}}));
  console.log('options string ->', run({type:'link.open', id:'2', url:'https://example.com', options:'x'}));
  console.log('extra top-level ->', run({type:'link.open', id:'3', url:'https://example.com', extra:true}));
  console.log('options extra ->', run({type:'link.open', id:'4', url:'https://example.com', options:{label:'a', target:'_blank'}}));
});
