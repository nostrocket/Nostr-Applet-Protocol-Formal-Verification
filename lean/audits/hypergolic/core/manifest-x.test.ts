// NIP-5D row 18: "a manifest that does not carry exactly one x tag MUST be rejected".
import test from 'node:test';
import assert from 'node:assert/strict';
import { finalizeEvent, generateSecretKey, getPublicKey } from '/Users/gareth/git/napplets/hypergolic/node_modules/nostr-tools/lib/esm/pure.js';
import { verifyManifest } from '/Users/gareth/git/napplets/hypergolic/src/napplets/verified-artifact.ts';
test('legacy-path manifest with zero x tags is accepted', async () => {
  const sk = generateSecretKey();
  const hash = 'ab'.repeat(32);
  const event = finalizeEvent({ kind: 35129, created_at: 1, content: '', tags: [['d', 'demo'], ['path', '/index.html', hash]] }, sk);
  const m = await verifyManifest({ kind: 35129, pubkey: getPublicKey(sk), identifier: 'demo', relayHints: [] } as any, { ...event });
  console.log('ACCEPTED format=', m.format, 'x tags=', m.tags.filter(t => t[0] === 'x').length, 'content=', JSON.stringify(m.content));
  assert.equal(m.tags.filter(t => t[0] === 'x').length, 0);
});
