import TournamentHamiltonian
import Lean.Util.CollectAxioms

/-! Audit every project theorem, including transitive dependencies. This
rejects placeholders, computation axioms, and arbitrary new axioms. The
standard foundational axioms below are used by Mathlib's real analysis. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "TournamentHamiltonian." then
      if let .thmInfo _ := info then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
        logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"Audited {count} project theorems. MainBound is still an unproved proposition."

#check TournamentHamiltonian.MainBound
