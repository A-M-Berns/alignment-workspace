import Cleanroom.Decision.DpReferentsCdt.ElhWitness

/-!
# `dp-referents-cdt` · audit r1 (adversarial) probe: the package's own reveal instance refutes
Everitt–Leike–Hutter's "one-step decisions (`m = t + 1`)" sentence as literally read

Not imported by the library.

The paper (line 419) says: "For one-step decisions (`m = t + 1`), SAEDT and SPEDT coincide."
Findings F13 reads this as an off-by-one and the package proves the coincidence at `m ≤ t`
(`spedtBelief_eq_saedtBelief_last`, `hlast : m ≤ h.length + 1` with `h.length = t − 1`), filing the
remark under *presentation*. But `reveal_saedt_ne_spedt` is stated at `m = 2` and `h = []`, i.e.
`t = 1` and `m = t + 1` — exactly the paper's case. So the witness is not merely "SAEDT ≠ SPEDT
can occur"; it is a counterexample to line 419 as written, inside the paper's own model (the
`s`-independent, history-dependent action likelihood is a special case of equation (2)). The
finding deserves a refutation row (plan §0.4 rule 3), not a presentation note.
-/

namespace Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial

open Cleanroom.Decision.DpReferentsCdt

/-- At `m = 2`, `h = []` (so `t = 1`, `m = t + 1`): SPEDT `2/3 ≠ 1/2` SAEDT. -/
theorem oneStep_literal_fails :
    spedtBelief revealEnv revealProc 2 revealPolicy [] .a 0 ≠
      saedtBelief revealEnv revealProc 2 [] .a 0 := by
  obtain ⟨h1, h2, -⟩ := reveal_saedt_ne_spedt
  rw [h1, h2]
  norm_num

/-- The paper's indexing: `h = []` has length `0 = t − 1`, and the lifetime is `2 = t + 1`; the
package's coincidence theorem needs `m ≤ h.length + 1 = 1`, which `m = 2` violates. -/
theorem oneStep_literal_outside_coincidence : ¬ ((2 : ℕ) ≤ ([] : Hist Act2 2).length + 1) := by
  simp

end Cleanroom.Decision.DpReferentsCdt.AuditR1Adversarial
