import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The two-option identity, finite-exact (T6a) and DDB's Lemma 7.1 on a finite frame (T6b)

Package `def-lattice`. Mathlib only — no FAF import. Over a finite world type `W`, novice
weights `π : W → ℝ` (arbitrary, no normalization), expert estimates `e : W → ℝ`, a bet
`X : W → ℝ` and a threshold `s`, the followed strategy of the two-option menu `{X, const s}`
is `Ŝ w = if s ≤ e w then X w else s` (ties toward `X`, the least-index rule of `Menu.argmax`),
and

`∑ π Ŝ − s ∑ π = ∑ π (X − s) 1[s ≤ e]`,  `∑ π Ŝ − ∑ π X = ∑ π (s − X) 1[e < s]`

exactly, by linearity alone (pointwise `Ŝ − s = (X − s)·1[s ≤ e]` and
`Ŝ − X = (s − X)·1[e < s]`). Hence Value against the constant ⟺ the above-threshold
inequality, Value against `X` ⟺ the below-threshold inequality, per `(X, s)`, and
quantified over all `(X, s)`. The indicator-as-factor spelling
`π w * (X w - s) * (if s ≤ e w then 1 else 0)` is `lit-ddb-frames`'s `TotalTrust` body with
`e w := ∑ v, P w v * X v` (`Cleanroom.Found.LitDdbFrames.TotalTrust`, which this file must not
import — both are roots; the identification is `corr-legit-general`'s).
-/

namespace Cleanroom.Found.DefLattice.TwoOptionFinite

open Finset

noncomputable section

variable {W : Type*} [Fintype W]

/-- The followed strategy of the two-option menu `{X, const s}` against expert estimates `e`:
take `X` where the expert's estimate is at least `s`, else the constant `s` (ties toward `X`).
Source: [[two-option-value-iff-total-trust]] §Statement
(`Ŝ_{X,s} = X·1[E*(X) ≥ s] + s·1[E*(X) < s]`); v6 §1.2
Kind: D
Fidelity: exact -/
def twoOptionStrategy (e X : W → ℝ) (s : ℝ) : W → ℝ :=
  fun w => if s ≤ e w then X w else s

/-- **The two-option identity, above-threshold form (T6a):**
`∑ π Ŝ − s ∑ π = ∑ π (X − s) 1[s ≤ e]`, exactly, for arbitrary `π`.
Source: [[two-option-value-iff-total-trust]] §Statement (the boxed identity); v6 §1.2;
lean-deference-007
Kind: L
Fidelity: exact -/
theorem twoOption_identity_above (π e X : W → ℝ) (s : ℝ) :
    (∑ w, π w * twoOptionStrategy e X s w) - s * (∑ w, π w) =
      ∑ w, π w * (X w - s) * (if s ≤ e w then 1 else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  unfold twoOptionStrategy
  by_cases h : s ≤ e w
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- **The two-option identity, below-threshold form (T6a, dual):**
`∑ π Ŝ − ∑ π X = ∑ π (s − X) 1[e < s]`, exactly.
Source: [[two-option-value-iff-total-trust]] §Statement ("Symmetrically"); v6 §1.2
Kind: L
Fidelity: exact -/
theorem twoOption_identity_below (π e X : W → ℝ) (s : ℝ) :
    (∑ w, π w * twoOptionStrategy e X s w) - (∑ w, π w * X w) =
      ∑ w, π w * (s - X w) * (if e w < s then 1 else 0) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  unfold twoOptionStrategy
  by_cases h : s ≤ e w
  · simp only [if_pos h, if_neg (not_lt.mpr h)]; ring
  · simp only [if_neg h, if_pos (not_le.mp h)]; ring

/-- **Value against the constant ⟺ the above-threshold inequality**, per `(X, s)`:
`s ∑ π ≤ ∑ π Ŝ` ⟺ `0 ≤ ∑ π (X − s) 1[s ≤ e]`.
Source: [[two-option-value-iff-total-trust]] §Statement; lean-deference-007
Kind: L
Fidelity: exact -/
theorem twoOption_value_iff_above (π e X : W → ℝ) (s : ℝ) :
    s * (∑ w, π w) ≤ ∑ w, π w * twoOptionStrategy e X s w ↔
      0 ≤ ∑ w, π w * (X w - s) * (if s ≤ e w then 1 else 0) := by
  rw [← sub_nonneg, twoOption_identity_above]

/-- **Value against the fixed option `X` ⟺ the below-threshold inequality**, per `(X, s)`:
`∑ π X ≤ ∑ π Ŝ` ⟺ `0 ≤ ∑ π (s − X) 1[e < s]`.
Source: [[two-option-value-iff-total-trust]] §Statement
Kind: L
Fidelity: exact -/
theorem twoOption_value_iff_below (π e X : W → ℝ) (s : ℝ) :
    (∑ w, π w * X w) ≤ ∑ w, π w * twoOptionStrategy e X s w ↔
      0 ≤ ∑ w, π w * (s - X w) * (if e w < s then 1 else 0) := by
  rw [← sub_nonneg, twoOption_identity_below]

/-- **Value on all two-option menus ⟺ both threshold inequalities at all `(X, s)`** — the
quantified form, both arrows, exact. Not the general-menu equivalence (that is
`def-argmax-value`'s, and false unconditionally); the name says `twoOption`.
Source: [[two-option-value-iff-total-trust]] §Statement (the last display); v6 §1.2
Kind: L
Fidelity: exact -/
theorem twoOption_value_all_iff (π e : W → ℝ) :
    (∀ (X : W → ℝ) (s : ℝ),
        s * (∑ w, π w) ≤ ∑ w, π w * twoOptionStrategy e X s w ∧
          (∑ w, π w * X w) ≤ ∑ w, π w * twoOptionStrategy e X s w) ↔
      (∀ (X : W → ℝ) (s : ℝ),
        0 ≤ ∑ w, π w * (X w - s) * (if s ≤ e w then 1 else 0) ∧
          0 ≤ ∑ w, π w * (s - X w) * (if e w < s then 1 else 0)) := by
  constructor
  · intro h X s
    exact ⟨(twoOption_value_iff_above π e X s).mp (h X s).1,
      (twoOption_value_iff_below π e X s).mp (h X s).2⟩
  · intro h X s
    exact ⟨(twoOption_value_iff_above π e X s).mpr (h X s).1,
      (twoOption_value_iff_below π e X s).mpr (h X s).2⟩

/-! ## T6b — DDB's Lemma 7.1 on a finite frame -/

/-- The expert's estimate of `X` on a finite frame `P : W → W → ℝ` (DDB's random variable
`E(X) : w ↦ ∑ v, P w v · X v`).
Source: [[Deference Done Better]] §1 (`E_w(X)`); [[deference-notions]] §Map to DDB's notions
Kind: D
Fidelity: exact -/
abbrev frameEstimate (P : W → W → ℝ) (X : W → ℝ) : W → ℝ :=
  fun w => ∑ v, P w v * X v

/-- **Two-option Value against the constant implies the above cut, at the frame's estimate
(T6b) — the one-strategy, one-direction instance that DDB's Lemma 7.1 uses.** On a finite
frame, if the two-option strategy "take `X` iff `s ≤ E_w(X)`" is weakly valued by `π` against
the constant `s`, then `0 ≤ ∑ π (X − s) 1[E(X) ≥ s]` — the product form of Total Trust at
`(X, s)` (`Cleanroom.Found.LitDdbFrames.TotalTrust`'s body, spelling for spelling). This is
*not* Lemma 7.1 itself (Weak Value ⟹ Total Trust at every `(X, t)`, quantified over all
recommended strategies, with the spectral-gap choice of `s ∈ (max(a, b), t)` that makes the
two-option strategy uniquely recommended — transcription App. B, ll. 480–496); it is the
per-`(X, s)` instance of T6a at `e := frameEstimate P X` with the tie-toward-`X` convention of
`Menu.argmax`'s least-index rule, which is what removes the need for the gap. Renamed from
`lemma71_twoOption` in repair round 1 so the name does not carry the lemma number. Quoted from
the transcription, which is not the PDF (fixpoint-lit-2-017).
Source: `references/deference-done-better/Deference Done Better.md` ll. 480–496 (Lemma 7.1)
Kind: L
Fidelity: weaker: one strategy, one direction (the instance of T6a at the frame's estimate)
Hyps: (a) -/
theorem twoOption_value_imp_above_frame (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ)
    (hV : s * (∑ w, π w) ≤ ∑ w, π w * twoOptionStrategy (frameEstimate P X) X s w) :
    0 ≤ ∑ w, π w * (X w - s) * (if s ≤ ∑ v, P w v * X v then 1 else 0) :=
  (twoOption_value_iff_above π (frameEstimate P X) X s).mp hV

/-- The frame form of the identity itself (both sides spelled with the frame's estimate), so
that a consumer holding a frame's `TotalTrust` sees the two-option value directly.
Source: [[Deference Done Better]] Lemma 7.1; v6 §1.2
Kind: L
Fidelity: exact -/
theorem frame_twoOption_value_iff (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    s * (∑ w, π w) ≤ ∑ w, π w * twoOptionStrategy (frameEstimate P X) X s w ↔
      0 ≤ ∑ w, π w * (X w - s) * (if s ≤ ∑ v, P w v * X v then 1 else 0) :=
  twoOption_value_iff_above π (frameEstimate P X) X s

end

end Cleanroom.Found.DefLattice.TwoOptionFinite
