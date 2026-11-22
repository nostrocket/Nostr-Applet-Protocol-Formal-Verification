// Validation probe for RELAY-1 and OUTBOX-1.
// Unlike relay/cipher.test.mts (which hands the template to ApprovalService through a stub lease
// port), this drives every JS stage Hypergolic really runs between the WebView and the signer:
//   1. runtime/src/guest-envelope.ts validEnvelope (WebView ingress)
//   2. src/runtime/approval-port.ts createNativeApprovalPort().take (decodes the native snapshot)
//   3. src/security/approval-service.ts enqueue -> approve (captureEventSnapshot, review, sign, publish)
//   4. for outbox: parseOutboxPublish + createOutboxPublicationPlanner + OutboxApprovalPreparation
// Only the native module (token store, lease flags), the signer and the relay socket are stubbed.
// Run from the Hypergolic root:
//   node --experimental-strip-types --import ../lean/audits/hypergolic/relay/register.mjs \
//     --test ../lean/audits/hypergolic/validation/high/cipher-e2e.test.mts
import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
const HG = process.cwd();
const req = createRequire(HG + '/package.json');
const { finalizeEvent, getPublicKey } = req('nostr-tools/pure');
const { validEnvelope } = await import(HG + '/runtime/src/guest-envelope.ts');
const { createNativeApprovalPort } = await import(HG + '/src/runtime/approval-port.ts');
const { ApprovalService } = await import(HG + '/src/security/approval-service.ts');
const { createOutboxPublicationPlanner } = await import(HG + '/src/outbox/publication-plan.ts');
const { parseOutboxRelayList } = await import(HG + '/src/outbox/relay-list.ts');

const secret = new Uint8Array(32).fill(37), user = getPublicKey(secret);
const now = Math.floor(Date.now() / 1000);
const NIP04 = 'aGVsbG8gd29ybGQ=?iv=AAAAAAAAAAAAAAAAAAAAAA==';
const NIP44 = 'Ag' + 'A'.repeat(130) + '==';
const registration = (domains: string[]) => ({ sessionId: 's1', generation: 'g1', epoch: 1, user, publisher: '22'.repeat(32),
  appId: 'approval-lab', version: '33'.repeat(32), instanceId: 'i1', fixture: 'approval-lab', domains });
const signFn = (event: any) => JSON.parse(JSON.stringify(finalizeEvent({ ...event, tags: event.tags.map((t: string[]) => [...t]) }, secret)));

function nativeModule(raw: string, sent: any[], responses: (string | null)[]) {
  let taken = false, approved = false, live = true, prepared = false;
  return {
    takeApproval: () => { if (taken) return null; taken = true; return raw; },
    prepareApprovalSigning: () => true,
    prepareOutboxApproval: () => { prepared = true; return true; },
    failOutboxApproval: (_t: string, error: string) => { live = false; responses.push(JSON.stringify({ ok: false, error })); },
    publishOutboxApproval: async (_t: string, group: string, event: string, relay: string) => {
      const e = JSON.parse(event); sent.push({ group, relay, content: e.content, kind: e.kind, sig: e.sig });
      return JSON.stringify({ relay, eventId: e.id, status: 'accepted', reason: '' }); },
    isApprovalLive: () => live, mayReviewApproval: () => live && !approved,
    approveApproval: () => { if (approved) return false; approved = true; return true; }, isApprovalApproved: () => approved,
    dismissApproval: () => { live = false; }, cancelApproval: () => { live = false; },
    finishApproval: (_t: string, r: string | null) => { live = false; responses.push(r); }, resumeApprovals: () => {},
    get prepared() { return prepared; },
  };
}

for (const [label, kind, content] of [['nip04', 4, NIP04], ['nip44', 1, NIP44]] as const) {
  test('relay.publish ' + label, async () => {
    const msg = { type: 'relay.publish', id: 'r-' + label, event: { kind, content, tags: [['p', '22'.repeat(32)]], created_at: now } };
    const ingress = validEnvelope(msg);
    const sent: any[] = [], responses: (string | null)[] = []; let signed: any = null;
    const mod = nativeModule(JSON.stringify({ registration: registration(['identity', 'relay', 'theme']), request: JSON.stringify(msg) }), sent, responses);
    const service = new ApprovalService(createNativeApprovalPort(mod as any), { assertActive() {} },
      { sign: async (s: any) => { signed = s.event; return signFn(s.event); },
        publishEvent: async (v: any, d: readonly string[]) => { for (const r of d) sent.push({ relay: r, content: v.content, kind: v.kind, sig: v.sig }); return d.map(r => ({ relay: r, eventId: v.id, status: 'accepted' as const, reason: '' })); } });
    const admitted = service.enqueue('tok', ['wss://relay.example.org']); service.focus('s1');
    const item = service.getSnapshot().current;
    const reviewText = item?.event.event.content;
    await service.approve(item!.id);
    const reply = JSON.parse(responses.at(-1)!);
    console.log(`relay.publish ${label}: ingress.valid=${ingress} enqueue=${admitted} reviewShowsRaw=${reviewText === content} SIGNED=${signed?.content === content} sentToRelay=${sent.length} reply=${reply.type} ok=${reply.ok}`);
    assert.equal(sent[0].content, content);
  });
  test('outbox.publish ' + label, async () => {
    const msg = { type: 'outbox.publish', id: 'o-' + label, event: { kind, content, tags: [], created_at: now }, options: { toOutbox: true } };
    const ingress = validEnvelope(msg);
    const own = parseOutboxRelayList(JSON.parse(JSON.stringify(finalizeEvent({ kind: 10002, created_at: 1, tags: [['r', 'wss://own.nostr.net', 'write']], content: '' }, secret))), user);
    const planner = createOutboxPublicationPlanner({ async resolve() { return { list: own, source: 'cache', incomplete: false }; } } as any,
      () => ({ networkRelays: ['wss://fallback.nostr.net'], lookupRelays: ['wss://lookup.nostr.net'] }), { ancillaryWhenOutboxSkipped: 'omit' });
    const sent: any[] = [], responses: (string | null)[] = []; let signed: any = null;
    const mod = nativeModule(JSON.stringify({ registration: registration(['identity', 'outbox', 'theme']), request: JSON.stringify(msg) }), sent, responses);
    const service = new ApprovalService(createNativeApprovalPort(mod as any), { assertActive() {} },
      { sign: async (s: any) => { signed = s.event; return signFn(s.event); }, publishEvent: async () => { throw Error('legacy publisher'); } }, planner);
    const admitted = service.enqueue('tok', []); service.focus('s1');
    for (let i = 0; i < 50 && !service.getSnapshot().current && service.getSnapshot().pending; i++) await new Promise(r => setTimeout(r, 2));
    const item = service.getSnapshot().current;
    if (!item) { console.log(`outbox.publish ${label}: ingress.valid=${ingress} enqueue=${admitted} NOT REVIEWABLE responses=${JSON.stringify(responses)}`); return; }
    await service.approve(item.id);
    const reply = JSON.parse(responses.at(-1)!);
    const primary = sent.filter(s => s.group === 'primary');
    console.log(`outbox.publish ${label}: ingress.valid=${ingress} enqueue=${admitted} reviewShowsRaw=${item.event.event.content === content} SIGNED=${signed?.content === content} sentToRelay=${primary.length} relay=${primary[0]?.relay} reply=${reply.type} ok=${reply.ok}`);
    assert.equal(primary[0].content, content);
  });
}
