import Cleanroom.Found.LitDdbFrames.Value
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# corr-value-change — Total Trust for a two-world source (T9(d), T12(i), T12(j), S1)

Source: [[value-change-as-epistemic-update]] §2.7 (the one-sided form, Total Trust), §6.6. Total
Trust is the run's definition of record `Cleanroom.Found.LitDdbFrames.TotalTrust` (DDB's
`E_π[X ∣ E_{P_w} X ≥ t] ≥ t` for all `X`, `t`, in product form), reused as is; the two-world
source `Q_1 = (a, 1−a)` in world 1, `Q_2 = (b, 1−b)` in world 2 is a `Frame Bool` (world 1 =
`true`). The characterization `Total Trust ↔ b ≤ p ≤ a` is proved, not gridded; the note's
example `(3/10, 7/10)`, `(9/10, 1/10)`, `(1/10, 9/10)` is an instance; the general "Total Trust ⇒
hull" is DDB Theorem 4.1 from `lit-ddb-frames` (S1, cited).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-- A two-point distribution `(x, 1 − x)` on `Bool` (`true` first).
Source: [[value-change-as-epistemic-update]] §6.6
Kind: D
Fidelity: exact -/
def twoPt (x : ℝ) : Bool → ℝ := fun v => if v then x else 1 - x

/-- `(x, 1−x)` is in the simplex for `x ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoPt_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : twoPt x ∈ stdSimplex ℝ Bool := by
  refine ⟨fun v => ?_, ?_⟩
  · cases v <;> simp [twoPt] <;> linarith
  · simp [twoPt, Fintype.sum_bool]

/-- **The two-world source**: the frame whose row at world 1 (`true`) is `Q_1 = (a, 1−a)` and at
world 2 is `Q_2 = (b, 1−b)`.
Source: [[value-change-as-epistemic-update]] §6.6 ("source opinion `Q_1 = (0.9, 0.1)` in world 1
and `Q_2 = (0.1, 0.9)` in world 2")
Kind: D
Fidelity: exact -/
def twoWorldFrame (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Frame Bool where
  P := fun w => if w then twoPt a else twoPt b
  P_mem := fun w => by cases w <;> simp [twoPt_mem ha0 ha1, twoPt_mem hb0 hb1]

/-- The expert's estimate of `X` in each world: `a X₁ + (1−a) X₂` and `b X₁ + (1−b) X₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoWorldFrame_E (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X : Bool → ℝ) (w : Bool) :
    E ((twoWorldFrame a b ha0 ha1 hb0 hb1).P w) X =
      (if w then a else b) * X true + (1 - (if w then a else b)) * X false := by
  cases w <;> simp [E, twoWorldFrame, twoPt, Fintype.sum_bool]

/-- **T9(d), Total Trust for the two-world source**: with `b < a` in `[0, 1]`, the prior
`π = (p, 1−p)` totally trusts the source (DDB's Total Trust, all bounded `X` and all thresholds)
**iff** `b ≤ p ≤ a` — iff `π` lies on the segment between the two opinions. Proved for all
`X, t`, not on a grid.
Source: [[value-change-as-epistemic-update]] §6.6 ("Total Trust holds (checked on a grid of payoff
vectors)"); mandate T9(d)
Kind: P
Fidelity: exact (and general in `a, b, p`)
Hyps: (a) `b < a`, `0 ≤ b`, `a ≤ 1` (the frame's own conditions; `p` unrestricted) -/
theorem total_trust_two_world (a b p : ℝ) (hab : b < a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) :
    TotalTrust (twoPt p) (twoWorldFrame a b (hb0.trans hab.le) ha1 hb0 (hab.le.trans ha1)) ↔
      b ≤ p ∧ p ≤ a := by
  have ha0 : 0 ≤ a := hb0.trans hab.le
  have hb1 : b ≤ 1 := hab.le.trans ha1
  constructor
  · intro h
    constructor
    · by_contra hc
      have hc' : p < b := not_le.1 hc
      have := h (fun v => if v then 1 else -1) (2 * b - 1)
      rw [Fintype.sum_bool, twoWorldFrame_E, twoWorldFrame_E] at this
      simp only [twoPt, if_true, Bool.false_eq_true, if_false] at this
      split_ifs at this <;> nlinarith
    · by_contra hc
      have hc' : a < p := not_le.1 hc
      have := h (fun v => if v then -1 else 1) (1 - 2 * a)
      rw [Fintype.sum_bool, twoWorldFrame_E, twoWorldFrame_E] at this
      simp only [twoPt, if_true, Bool.false_eq_true, if_false] at this
      split_ifs at this <;> nlinarith
  · rintro ⟨hbp, hpa⟩ X s
    rw [Fintype.sum_bool, twoWorldFrame_E, twoWorldFrame_E]
    simp only [twoPt, if_true, Bool.false_eq_true, if_false]
    have hp0 : 0 ≤ p := hb0.trans hbp
    have hp1 : p ≤ 1 := hpa.trans ha1
    split_ifs with h1 h2 h2
    · -- both estimates at least `s`: `π` is a convex combination of the two rows
      nlinarith [mul_nonneg (sub_nonneg.2 hbp) (sub_nonneg.2 h1),
        mul_nonneg (sub_nonneg.2 hpa) (sub_nonneg.2 h2)]
    · -- only world 1's estimate at least `s`: then `X₁ > X₂` and `X₁ ≥ s`
      have h2' := not_le.1 h2
      have hx : X false < X true := by
        by_contra hc; have hc' : X true ≤ X false := not_lt.1 hc
        nlinarith [mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 hc')]
      have hx1 : s ≤ X true := by
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hx.le)]
      nlinarith [mul_nonneg hp0 (sub_nonneg.2 hx1)]
    · -- only world 2's
      have h1' := not_le.1 h1
      have hx : X true < X false := by
        by_contra hc; have hc' : X false ≤ X true := not_lt.1 hc
        nlinarith [mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 hc')]
      have hx2 : s ≤ X false := by
        nlinarith [mul_nonneg hb0 (sub_nonneg.2 hx.le)]
      nlinarith [mul_nonneg (sub_nonneg.2 hp1) (sub_nonneg.2 hx2)]
    · simp

/-- **T12(j), Total Trust puts the prior in the hull of the two opinions**: under Total Trust,
`π = λ Q_1 + (1 − λ) Q_2` with `λ = (p − b)/(a − b) ∈ [0, 1]`, and `λ` is the only such weight.
Source: [[value-change-as-epistemic-update]] §6.6 ("the only mixing weights that recover `P_0`
from `{Q_1, Q_2}` are `(1/4, 3/4)`")
Kind: P
Fidelity: exact (two worlds)
Hyps: (a) `TotalTrust`, the frame's conditions -/
theorem TT_imp_hull_two_world (a b p : ℝ) (hab : b < a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (h : TotalTrust (twoPt p) (twoWorldFrame a b (hb0.trans hab.le) ha1 hb0 (hab.le.trans ha1))) :
    0 ≤ (p - b) / (a - b) ∧ (p - b) / (a - b) ≤ 1 ∧
      (∀ v, twoPt p v = (p - b) / (a - b) * twoPt a v + (1 - (p - b) / (a - b)) * twoPt b v) ∧
      ∀ μ : ℝ, (∀ v, twoPt p v = μ * twoPt a v + (1 - μ) * twoPt b v) → μ = (p - b) / (a - b) := by
  obtain ⟨hbp, hpa⟩ := (total_trust_two_world a b p hab ha1 hb0).1 h
  have hpos : 0 < a - b := by linarith
  refine ⟨div_nonneg (by linarith) hpos.le, ?_, fun v => ?_, fun μ hμ => ?_⟩
  · rw [div_le_one hpos]; linarith
  · cases v <;> simp [twoPt] <;> field_simp <;> ring
  · have := hμ true
    simp [twoPt] at this
    rw [eq_div_iff hpos.ne']
    linarith

/-- **S1, Total Trust ⇒ hull in general** (DDB Theorem 4.1, cited from `lit-ddb-frames`): a
deferrer in the simplex that totally trusts a finite frame lies in the convex hull of the frame's
candidates.
Source: [[value-change-as-epistemic-update]] §6.6; [[Deference Done Better]] Theorem 4.1
(`totalTrust_iff_hullAndModestlyInformed`)
Kind: C (cited (a))
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex`, `TotalTrust π F` -/
theorem TT_imp_hull_general {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) (h : TotalTrust π F) :
    π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ)) :=
  ((totalTrust_iff_hullAndModestlyInformed hπ F).1 h).1

/-- **T12(i), the note's example**: `P = (3/10, 7/10)`, `Q_1 = (9/10, 1/10)`, `Q_2 = (1/10, 9/10)`:
Total Trust holds (`1/10 ≤ 3/10 ≤ 9/10`); the prior expectation of the source's opinion of world 1,
`∑_w π_w Q_w(1)`, read off the frame, is `17/50 ≠ 3/10 = π_1`, so (M) fails; and the hull weight is
`1/4` and unique (`TT_imp_hull_two_world`), not the agent's `3/10`. Every clause is derived from
`twoPt`/`twoWorldFrame`, not checked on literals (audit r3 fidelity N3).
Source: [[value-change-as-epistemic-update]] §6.6 (computed); fixture `total_trust_example`
Kind: N+
Fidelity: exact -/
theorem total_trust_example :
    TotalTrust (twoPt (3 / 10)) (twoWorldFrame (9 / 10) (1 / 10) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) ∧
    ∑ w, twoPt (3 / 10) w *
      (twoWorldFrame (9 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).P w true
        = 17 / 50 ∧
    twoPt (3 / 10) true = 3 / 10 ∧ (17 / 50 : ℝ) ≠ 3 / 10 ∧
    (∀ v, twoPt (3 / 10) v = 1 / 4 * twoPt (9 / 10) v + (1 - 1 / 4) * twoPt (1 / 10) v) ∧
    ∀ μ : ℝ, (∀ v, twoPt (3 / 10) v = μ * twoPt (9 / 10) v + (1 - μ) * twoPt (1 / 10) v) →
      μ = 1 / 4 := by
  have hTT := (total_trust_two_world (9 / 10) (1 / 10) (3 / 10) (by norm_num) (by norm_num)
    (by norm_num)).2 ⟨by norm_num, by norm_num⟩
  have hhull := TT_imp_hull_two_world (9 / 10) (1 / 10) (3 / 10) (by norm_num) (by norm_num)
    (by norm_num) hTT
  have hw : ((3 : ℝ) / 10 - 1 / 10) / (9 / 10 - 1 / 10) = 1 / 4 := by norm_num
  refine ⟨hTT, ?_, by simp [twoPt], by norm_num, ?_, ?_⟩
  · simp [twoWorldFrame, twoPt, Fintype.sum_bool]; norm_num
  · intro v; have := hhull.2.2.1 v; rwa [hw] at this
  · intro μ hμ; have := hhull.2.2.2 μ hμ; rwa [hw] at this

/-! ## Total Trust implies the decision-theoretic verdict (the content behind §2.7's one-sided form) -/

/-- **Total Trust ⇒ acting on the source's opinion is worth it** (DDB Theorem 2.2, Total Trust ⇔
Value, cited): for every finite menu of payoff vectors `O ⊆ (W → ℝ)` and every strategy that
picks in each world an option the source's opinion there recommends, the prior's expected value
of following the strategy is at least that of any fixed option. This is the trust principle that
the one-sided form of §2.7 restates (F10); for the modest source it holds while (R) and (M) fail.
Source: [[value-change-as-epistemic-update]] §2.7 ("the theorem of Dorst et al. is that it is
equivalent to preferring to decide by the future state in every decision problem");
[[Deference Done Better]] Theorem 2.2 (`value_iff_totalTrust`)
Kind: C (cited (a))
Fidelity: exact
Hyps: (a) `π ∈ stdSimplex`, `TotalTrust π F` -/
theorem total_trust_imp_value {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) (h : TotalTrust π F) : Value π F :=
  (value_iff_totalTrust hπ F).2 h

end

end Cleanroom.Corrigibility.CorrValueChange
