import Collatz
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Fails unless every declaration in the `Collatz` namespace depends only on `propext`,
`Classical.choice` and `Quot.sound`. This rules out `sorryAx`, `Lean.ofReduceBool`
(`native_decide`) and any user-declared axiom. Run: `lake env lean scripts/AxiomAudit.lean`.
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Collatz).isPrefixOf name && !name.isInternal then
      count := count + 1
      for ax in ← liftCoreM (collectAxioms name) do
        unless allowed.contains ax do bad := bad.push (name, ax)
  if count == 0 then throwError "no Collatz declarations found"
  unless bad.isEmpty do throwError m!"non-standard axioms: {bad.toList}"
  logInfo m!"audited {count} declarations: only propext, Classical.choice, Quot.sound"

#audit_axioms
