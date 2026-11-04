import Lake
open Lake DSL

package CharacteristicSetWorkspace where
  version := v!"0.1.0"

require CharacteristicSet from "packages/computable"
require CharacteristicSetTheory from "packages/theory"
require CharacteristicSetBridge from "packages/bridge"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.35.0"

/-- Build every module of the three libraries, including executable examples. -/
@[default_target]
target all : Unit := do
  let jobs ← #[`CharacteristicSet, `CharacteristicSetTheory, `CharacteristicSetBridge].mapM fun name => do
    let some lib ← findLeanLib? name
      | error s!"library '{name}' not found"
    lib.fetch
  return Job.mixArray jobs
