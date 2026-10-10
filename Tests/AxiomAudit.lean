import MeaningDimension

/-!
# Axiom audit

Collects the axioms used by every non-internal declaration in a `MeaningDimension.*` module and
fails if any axiom other than Lean's standard `propext`, `Classical.choice`, `Quot.sound` occurs
(in particular `sorryAx`, or any `axiom` declared by this project or by a dependency).
-/

open Lean Elab Command in
elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count := 0
  for i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless (`MeaningDimension).isPrefixOf mod do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      unless ci matches .thmInfo _ || ci matches .defnInfo _ do continue
      count := count + 1
      let axs ← liftCoreM <| Lean.collectAxioms n
      logInfo m!"{n} : {axs.toList}"
      for a in axs do
        unless allowed.contains a do bad := bad.push (n, a)
  if bad.isEmpty then
    logInfo m!"AXIOM AUDIT OK: {count} declarations, only [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"AXIOM AUDIT FAILED: {bad.toList}"

#audit_axioms
