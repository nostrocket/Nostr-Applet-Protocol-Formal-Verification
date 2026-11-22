import test from 'node:test';
import assert from 'node:assert/strict';
import { finalizeEvent } from 'nostr-tools/pure';
import { updateApprovalAppState } from '/Users/gareth/git/napplets/hypergolic/src/shell/approval-lifecycle.ts';
import { ApprovalService, PublicationUncertainError, type ApprovalEffects, type ApprovalOrigin, type NativeApprovalLease, type NativeApprovalLeasePort, type NativeTakenApproval } from '/Users/gareth/git/napplets/hypergolic/src/security/approval-service.ts';

const secret = new Uint8Array(32); secret[31] = 2;
const relay = 'wss://relay.example.org';
const event = (kind = 1) => ({ kind, content: 'approved', tags: [['t', 'approval']], created_at: 1_700_000_002 });
const origin = (sessionId: string, epoch = 1): ApprovalOrigin => Object.freeze({ sessionId, generation: `generation-${sessionId}`, epoch, user: 'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5', publisher: '11'.repeat(32), appId: 'approval-lab', version: '22'.repeat(32), instanceId: `instance-${sessionId}` });
const deferred = <T>() => { let resolve!: (value: T) => void; const promise = new Promise<T>(done => { resolve = done; }); return { promise, resolve }; };
type State = { live: boolean; approved: boolean };
class Native implements NativeApprovalLeasePort {
  sourceTokens = new WeakMap<NativeApprovalLease, string>();
  signingSource(lease: NativeApprovalLease) { const token = this.sourceTokens.get(lease); assert(token); return { kind: 'approval' as const, token }; }
  states = new Map<NativeApprovalLease, State>(); tokens = new Map<string, NativeTakenApproval>(); cancelled = 0; finished = 0; responses: (string | null)[] = [];
  issue(token: string, owner = origin(token), requestId = `wire-${token}`, request = event()) { const lease = {}; this.sourceTokens.set(lease, token); const taken = Object.freeze({ lease, origin: owner, requestId, event: request }); this.states.set(lease, { live: true, approved: false }); this.tokens.set(token, taken); return taken; }
  state(lease: NativeApprovalLease) { const value = this.states.get(lease); if (!value) throw new Error('unknown lease'); return value; }
  take(token: string) { const value = this.tokens.get(token) ?? null; this.tokens.delete(token); return value; }
  isLive(lease: NativeApprovalLease) { return this.state(lease).live; }
  mayReview(lease: NativeApprovalLease) { const state = this.state(lease); return state.live && !state.approved; }
  approveOnce(lease: NativeApprovalLease) { const state = this.state(lease); if (!state.live || state.approved) return false; state.approved = true; return true; }
  isApproved(lease: NativeApprovalLease) { const state = this.state(lease); return state.live && state.approved; }
  cancel(lease: NativeApprovalLease) { this.cancelled++; this.state(lease).live = false; }
  dismiss(lease: NativeApprovalLease) { this.cancel(lease); }
  resume() {}
  finish(lease: NativeApprovalLease, response: string | null = null) { this.finished++; this.responses.push(response); this.state(lease).live = false; }
}
function sign(snapshot: any) { return JSON.parse(JSON.stringify(finalizeEvent({ ...snapshot.event, tags: snapshot.event.tags.map((tag: string[]) => [...tag]) }, secret))); }
function make(native: Native, effects: Partial<ApprovalEffects> = {}, owner = { assertActive: (_: ApprovalOrigin) => undefined }) {
  return new ApprovalService(native, owner, { sign: async snapshot => sign(snapshot), publishEvent: async (verified, destinations) => Object.freeze(destinations.map(item => Object.freeze({ relay: item, eventId: verified.id, status: 'accepted' as const, reason: '' }))), ...effects });
for (const [label, tpl] of [
  ['nip04 kind4', { kind: 4, content: 'aGVsbG8gd29ybGQ=?iv=AAAAAAAAAAAAAAAAAAAAAA==', tags: [['p', '22'.repeat(32)]], created_at: 1_700_000_002 }],
  ['nip44 kind1', { kind: 1, content: 'Ag' + 'A'.repeat(130) + '==', tags: [], created_at: 1_700_000_002 }],
] as const) {
  test('ciphertext ' + label, async () => {
    const native = new Native(); native.issue('c', origin('c'), 'wire-c', tpl as any);
    let signed: any = null, published = 0;
    const service = make(native, { sign: async s => { signed = s.event; return sign(s); }, publishEvent: async (v, d) => { published++; return d.map(r => ({ relay: r, eventId: v.id, status: 'accepted' as const, reason: '' })); } });
    const id = current(service, 'c');
    await service.approve(id);
    const resp = JSON.parse(native.responses.at(-1)!);
    console.log(label, 'SIGNED content=', signed.content, 'published=', published, 'reply.ok=', resp.ok, 'reply.type=', resp.type);
  });
}
