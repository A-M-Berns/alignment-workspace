/-
  dp-learner-nr audit round 3 (fidelity) — probe: `li_decided_crosser_no_lesion` is a squeeze.

  Claim checked: under `hcross` (every completed-theory world holds `cross n`), the theorem's
  conclusion "the lesion fails at `n`" is *equivalent* to its other hypothesis `hcon` (some
  completed-theory world refutes `incon n`). So the theorem is `hcross → (hcon → hcon)` up to
  that equivalence, which is what the ledger row and docstring say since repair round 2 (Kind
  "L (a squeeze …)"); STANDARDS §6 has the kind S for exactly this shape. Not imported by the
  library.
-/

import Cleanroom.Decision.DpLearnerNr.LeakLI

open LO
open LogicalInduction
open scoped LogicalInduction

namespace Cleanroom.Decision.DpLearnerNr.AuditR3

open Cleanroom.Decision.DpTrollBridge Cleanroom.Decision.DpLearnerNr

/-- The converse direction the package does not state: the failure of the lesion at `n` *yields*
`hcon` — and this direction needs no `hcross` at all (a world refuting `cross n 🡒 incon n` holds
`cross n` and refutes `incon n`). Together with `li_decided_crosser_no_lesion` this is an iff. -/
theorem no_lesion_imp_hcon (DP : DeductiveProcess) (cross incon : ℕ → Sentence) (n : ℕ)
    (hnl : ¬ ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n)) :
    ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n) := by
  by_contra h
  push Not at h
  apply hnl
  intro v hv
  exact (holds_imp v _ _).mpr (fun _ => h v hv)

/-- The squeeze, as an iff: under `hcross`, conclusion ↔ `hcon` (`hcross` is used only in the
backward direction, which is the package's theorem). -/
theorem decided_crosser_squeeze (DP : DeductiveProcess) (cross incon : ℕ → Sentence) (n : ℕ)
    (hcross : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n)) :
    (¬ ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds (cross n 🡒 incon n)) ↔
      (∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ¬ v.Holds (incon n)) :=
  ⟨no_lesion_imp_hcon DP cross incon n,
    fun hcon => li_decided_crosser_no_lesion DP cross incon n hcross hcon⟩

end Cleanroom.Decision.DpLearnerNr.AuditR3
