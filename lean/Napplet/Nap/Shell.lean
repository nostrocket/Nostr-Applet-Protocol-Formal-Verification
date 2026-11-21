import Napplet.Shell

/-!
# NAP-SHELL (`shell`, optional)

`supports(domain)` is local. `shell.ready` → `shell.init` happens exactly once per
endpoint, and the environment describes only that napplet's own domains.
-/

namespace Napplet.NapShell

structure ShellEnvironment where
  capabilities : List Domain
  services : List String
  deriving DecidableEq, Repr

/-- `window.napplet.shell.supports(d)`: local, no wire message, works before init. -/
def supports (exposed : List Domain) (d : Domain) : Bool := decide (d ∈ exposed)

/-- The environment for a bound endpoint describes only its own exposure. -/
def environment (b : Binding) (services : List String) : ShellEnvironment :=
  { capabilities := b.exposed, services }

/-- Runtime reaction to one `shell.ready`, given whether `shell.init` was already sent
on this endpoint. Returns the new flag and the `shell.init` messages to send. -/
def onReady (sent : Bool) (env : ShellEnvironment) : Bool × List ShellEnvironment :=
  if sent then (true, []) else (true, [env])

/-- Feed `n` `shell.ready` messages to one endpoint. -/
def run (env : ShellEnvironment) : Bool → Nat → Bool × List ShellEnvironment
  | sent, 0 => (sent, [])
  | sent, n + 1 =>
    let r := onReady sent env
    let r' := run env r.1 n
    (r'.1, r.2 ++ r'.2)

theorem run_after_init (env : ShellEnvironment) (n : Nat) : (run env true n).2 = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, onReady, ih]

/-- The first `shell.ready` yields exactly one `shell.init`; duplicates yield none. -/
theorem init_exactly_once (env : ShellEnvironment) (n : Nat) :
    (run env false (n + 1)).2 = [env] := by
  simp [run, onReady, run_after_init]

theorem init_at_most_once (env : ShellEnvironment) (sent : Bool) (n : Nat) :
    (run env sent n).2.length ≤ 1 := by
  cases n with
  | zero => simp [run]
  | succ n =>
    cases sent with
    | false => simp [init_exactly_once]
    | true => simp [run, onReady, run_after_init]

/-- In a reachable shell, `shell.init` advertises exactly the policy exposure for the
bound identity: nothing a manifest declared, nothing another napplet has. -/
theorem init_capabilities {c : Crypto} {cfg : ShellConfig} {s : ShellState}
    (hr : Reachable c cfg s) {p : PortId} {b : Binding} (hb : s.bindings p = some b)
    (services : List String) :
    (environment b services).capabilities = exposedFor cfg b.identity := by
  obtain ⟨ld, hf⟩ := hr.inv.bind_frame p b hb
  exact (hr.inv.frame_verified _ _ _ _ _ hf).2

end Napplet.NapShell
