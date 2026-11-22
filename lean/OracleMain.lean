/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Oracle

/-!
# `napplet-oracle`

Reads a trace on standard input (a header line, then one `Runtime.Input` per line, as
JSON) and writes one JSON line per input with the outputs of `Refine.step'`. See
`Napplet/Oracle.lean` for the formats. Example:

```
lake exe napplet-oracle < traces/storage.in.ndjson
```
-/

open Napplet

def chomp (s : String) : String := String.ofList (s.toList.filter fun c => c ≠ '\n' && c ≠ '\r')

partial def loop (stdin stdout : IO.FS.Stream) (s : Oracle.Session) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := chomp line
  if l.all (· = ' ') then
    loop stdin stdout s
  else
    let (s', o) := Oracle.feed s l
    stdout.putStrLn o.render
    stdout.flush
    loop stdin stdout s'

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let h ← stdin.getLine
  match Json.parse (chomp h) with
  | none =>
    stdout.putStrLn (Json.mkObj [("error", some (.str "header is not JSON"))]).render
    return 1
  | some hj =>
    match Oracle.decHeader hj with
    | .error e =>
      stdout.putStrLn (Json.mkObj [("error", some (.str e))]).render
      return 1
    | .ok s =>
      loop stdin stdout s
      return 0
