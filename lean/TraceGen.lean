/-
This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
If a copy of the MPL was not distributed with this file, You can obtain one at
https://mozilla.org/MPL/2.0/.
-/

import Napplet.Test.Traces

/-!
# `napplet-tracegen`

Writes every trace of `Napplet.Test.Traces.all` to `<dir>/<name>.in.ndjson` and the
reference outputs (`Runtime.step`) to `<dir>/<name>.out.ndjson`, after checking that the
decoded header reproduces the end-to-end configuration's outputs exactly.

```
lake exe napplet-tracegen traces
```
-/

open Napplet Napplet.Test.Traces

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "traces"
  IO.FS.createDirAll dir
  let mut bad := 0
  for t in all ++ extra do
    match expected t with
    | .error e =>
      IO.eprintln s!"{t.name}: {e}"
      bad := bad + 1
    | .ok outs =>
      if let some c := t.e2eCfg then
        if outs != e2eLines t c then
          IO.eprintln s!"{t.name}: the decoded header does not reproduce the E2E configuration"
          bad := bad + 1
      IO.FS.writeFile s!"{dir}/{t.name}.in.ndjson" (String.intercalate "\n" (inLines t) ++ "\n")
      IO.FS.writeFile s!"{dir}/{t.name}.out.ndjson" (String.intercalate "\n" outs ++ "\n")
  IO.println s!"{(all ++ extra).length} traces written to {dir}"
  return (if bad = 0 then 0 else 1)
