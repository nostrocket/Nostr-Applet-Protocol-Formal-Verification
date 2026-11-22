# Conformance of the Lean model to the upstream texts

One file per spec (NIP-5D and the 19 NAPs, at the commits in `../README.md`). Each row is
one normative statement (MUST, MUST NOT, SHOULD, SHOULD NOT, MAY, or a schema's
"required") and where the model meets it:

| Status | Meaning |
|---|---|
| OK | Implemented by the cited Lean definition, and by the cited theorem where one exists. |
| HOST | The host's or the shell UI's job, stated as a contract in `../Napplet/Host.lean` (or the component's "Host operations", collected there). |
| NAPPLET | Constrains the napplet or its binding; modelled in `../Napplet/Binding*.lean` where the web projection defines it. |
| OPTIONAL | A SHOULD or MAY the model does not do; listed under "Optional behaviours" in `../README.md`. |
| DECISION | Upstream is silent or contradictory; covered by a numbered modelling decision in `../README.md`. |
| RESOLVED (was MISMATCH) | The audit found the model contradicted or missed the statement; fixed in code, in a host contract, or by a decision (decisions 35–47 in `../README.md`). |

The tables were produced by reviewers reading the upstream text and the Lean source
independently of the authors of the components, with suspected mismatches checked by
evaluating the model. Every flagged item was then fixed; no statement is left in
contradiction with the model.
