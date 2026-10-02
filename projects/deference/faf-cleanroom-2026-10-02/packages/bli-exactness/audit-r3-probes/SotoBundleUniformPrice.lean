import Cleanroom.Bli.BliExactness.Perturb

/-!
# Audit r3 (fidelity) probe — `sotoBundleHistory` gives every non-conjunction one price

Construction-facing (imports `Perturb` for the `ObjectLevel` discharges at `quoteAt T`). Not
imported by the library.

`sotoBundleHistory quoteAt cells w` takes **one** mass function `w : ℚ × ℚ → ℝ` for every quoted
sentence and every quoted day, where Soto's `n = 1` market has cell masses
`Q_k(Q_{k+1}(φ) ∈ cell_m)` that depend on `φ`. Consequence, machine-checked at FAF's `quoteAt 𝗜𝚺₁`:
every object-level sentence — every atom, `⊤`, and **every negation** `∼φ` whatever `φ` is (the
negation of a cell sentence included) — is priced at the same marginal `∑ mid I · w I`. So
`P_n(φ) = P_n(∼φ)` for every atom `φ`, a second incoherence of the construction unrelated to the
midpoint representative (F15's `⊤`-incoherence), and `P_n(∼χ_I) = ∑ mid·w` while `P_n(χ_I) = w I`.
None of this touches the package's grades (the object is already N−) or F15 (`sotoBundle_top_lt_one`
concerns `⊤`'s own cells and quantifies over `w`); it is a disclosure item for `sotoBundleHistory`'s
Fidelity line (audit r3 fidelity, non-blocking N1).
-/

namespace Cleanroom.Bli.BliExactness.AuditR3

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliExactness

/-- Every negation is object-level for `quoteAt T` (`isAnd (∼φ) = false`), so it is priced at the
marginal — the same value as `⊤`. -/
theorem sotoBundle_neg_eq_top (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ) (n : ℕ)
    (φ : Sentence) :
    sotoBundleHistory (quoteAt 𝗜𝚺₁) cells w n (∼φ) =
      sotoBundleHistory (quoteAt 𝗜𝚺₁) cells w n (⊤ : Sentence) := by
  rw [sotoBundle_obj w n (objectLevel_quoteAt_of_not_isAnd 𝗜𝚺₁ (isAnd_neg φ)),
    sotoBundle_obj w n (objectLevel_quoteAt_top 𝗜𝚺₁)]

/-- An atom and its negation share one price. -/
theorem sotoBundle_atom_eq_neg (cells : ℕ → Finset (ℚ × ℚ)) (w : ℚ × ℚ → ℝ) (n a : ℕ) :
    sotoBundleHistory (quoteAt 𝗜𝚺₁) cells w n (Formula.atom a) =
      sotoBundleHistory (quoteAt 𝗜𝚺₁) cells w n (∼(Formula.atom a : Sentence)) := by
  rw [sotoBundle_obj w n (objectLevel_quoteAt_atom 𝗜𝚺₁ a),
    sotoBundle_obj w n (objectLevel_quoteAt_of_not_isAnd 𝗜𝚺₁ (isAnd_neg _))]

/-- At X3's family and masses `½`: `P₁(φ₀) + P₁(∼φ₀) = 1` holds — by the coincidence
`∑ mid·½ = ½`, not by coherence (for `w ≡ ⅓` the sum would be `⅔`). -/
theorem sotoBundle_x3_atom_add_neg :
    sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ)) 1 x3Atom +
      sotoBundleHistory (quoteAt 𝗜𝚺₁) x3Cells (fun _ => (1 / 2 : ℝ)) 1 (∼x3Atom) = 1 := by
  rw [show x3Atom = Formula.atom 1 from rfl, sotoBundle_atom_eq_neg,
    sotoBundle_obj _ 1 (objectLevel_quoteAt_of_not_isAnd 𝗜𝚺₁ (isAnd_neg _))]
  have hne : ((0 : ℚ), (1 / 2 : ℚ)) ≠ (1 / 2, 1) := by norm_num
  show ∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)), ((mid I : ℚ) : ℝ) * (1 / 2 : ℝ) +
      ∑ I ∈ ({(0, 1 / 2), (1 / 2, 1)} : Finset (ℚ × ℚ)), ((mid I : ℚ) : ℝ) * (1 / 2 : ℝ) = 1
  rw [Finset.sum_pair hne]
  norm_num [mid]

end Cleanroom.Bli.BliExactness.AuditR3
