import LonelyRunnerSpec.V1
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms

open Lean Elab Command Meta

namespace LonelyRunnerValidation

def permittedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def assertWhitelist (name : Name) : CommandElabM Unit := do
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless permittedAxioms.contains ax do
      throwError "AXIOM_REJECT: {name} uses {ax}"
  logInfo m!"AXIOMS_OK: {name}: {axioms}"

/-- A local preflight only. Official isolated Comparator remains a separate gate. -/
elab "#assert_frozen_target " name:ident : command => do
  let info ← getConstInfo name.getId
  unless info matches .thmInfo _ do
    throwError "TARGET_REJECT: target must be a theorem"
  liftTermElabM do
    unless ← isDefEq info.type (mkConst ``LonelyRunnerSpec.V1.Statement) do
      throwError "TARGET_REJECT: theorem does not have the frozen full statement"
  assertWhitelist name.getId
  logInfo m!"FROZEN_TARGET_OK: {name.getId}"

elab "#assert_axiom_whitelist " name:ident : command =>
  assertWhitelist name.getId

end LonelyRunnerValidation
