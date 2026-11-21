# Napplets: specification digest and Lean 4 formal model

This repository covers napplets, the sandboxed Nostr web applets defined by
[NIP-5D](https://github.com/nostr-protocol/nips/pull/2303), and the capability
contracts (NAPs) defined in [napplet/naps](https://github.com/napplet/naps).

It is an independent, unofficial project. It is not affiliated with the NIP-5D or
NAP authors. Both specs are drafts and change often; everything here reflects the
upstream text as of November 2026.

## Contents

| Path | What it is |
|---|---|
| [`NAPPLETS-SPEC.md`](NAPPLETS-SPEC.md) | One-document digest of NIP-5D and all 21 NAPs. It covers the manifest, transport, identity, sandbox, every NAP's operations and wire messages, governance, tooling, and open review issues. It is a close paraphrase of the sources, not a verbatim copy. |
| [`lean/`](lean/README.md) | A mechanised formal model of the protocol in Lean 4, with 246 machine-checked theorems. It covers the NIP-5D core and every live NAP. |

## The Lean model

The model restates the protocol as Lean definitions and proves safety properties
about it. Some examples:

- NAP messages are processed only from a bound port.
- A dispatched message's sender identity always came from verified artifact bytes.
- Every revocation trigger closes the port and drops all grants.
- No resource fetch reaches a private address.
- Money moves only with consent or a covering allowance.
- A retired media session never comes back.

Several properties hold over every reachable shell state.

It verifies the **design**, not any implementation. No proof connects the model to
an actual shell or SDK. Browser guarantees (the iframe sandbox, CSP, an unforgeable
`MessageEvent.source`) and cryptography are assumptions, not proofs.

Building the model surfaced 28 points where the specs are silent or contradict
themselves. Each one, with the behaviour the model chose, is listed in
[`lean/README.md`](lean/README.md#modelling-decisions-where-the-spec-is-silent).

### Build

You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean/lean-toolchain`, and the model has no dependencies.

```bash
cd lean && lake build
```

```bash
cd lean && lake env lean Audit.lean
```

`lake build` checks every proof and runs the conformance vectors. `Audit.lean`
prints the axioms behind the headline theorems. Only `propext`, `Classical.choice`
and `Quot.sound` should appear. CI runs both, plus a `sorry` scan, on every push.

## Sources

- NIP-5D: [nostr-protocol/nips#2303](https://github.com/nostr-protocol/nips/pull/2303)
- NAP registry: [napplet/naps](https://github.com/napplet/naps)
- Napplet SDK: [napplet/web](https://github.com/napplet/web) and [napplet.run](https://napplet.run/)
- Runtime toolkit: [kehto/web](https://github.com/kehto/web)

## Licence

[Mozilla Public License 2.0](LICENSE).
