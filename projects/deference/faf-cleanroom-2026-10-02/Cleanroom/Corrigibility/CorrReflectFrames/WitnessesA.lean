import Cleanroom.Corrigibility.CorrReflectFrames.Selection
import Cleanroom.Corrigibility.CorrReflectFrames.Accuracy
import Cleanroom.Corrigibility.CorrReflectFrames.Legit
import Cleanroom.Corrigibility.CorrReflectFrames.Support
import Mathlib.Data.Fin.VecNotation

/-!
# corr-reflect-frames — witnesses A (four worlds)

* `frame4`: the T1 collapse witness (N+) — an immodest two-branch refinement frame on `Fin 4`
  with non-degenerate conditionals, reflected by a non-uniform deferrer; every form of the
  collapse holds and the frame is neither flat nor single-candidate. (`flat` is the N−.)
* `s6`: the T5 separation (N+) — the informative-but-underconfident expert of radical `s6` (1):
  Brier `9/50 < 1/4`, log `(9/10) log(5/3) + (1/10) log(5/2) < log 2` (as
  `5¹⁰ < 2¹¹ · 3⁹` under `Real.log`), value-form reflection fails at `c = 3/5`, Total Trust fails
  at `X = 𝟙[¬φ ∧ h]`, `t = 3/10`; the frame is immodest.
* `ddb4`: ddb's I5 witness (N+) — Total Trust conditional on `L` holds, conditional on `¬L`
  fails, unconditionally fails (the converse of the partition lemma fails).
* `fig3` with `L = Ω`: the two "legitimizing" senses differ without introspection (T11(c)).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-- A nonnegative quadruple summing to one is a distribution on four worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem simplex4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 1) : (![a, b, c, d] : Fin 4 → ℝ) ∈ stdSimplex ℝ (Fin 4) :=
  ⟨fun x => by fin_cases x <;> simp [ha, hb, hc, hd], by simp [Fin.sum_univ_four, h]⟩

/-- Mass of an event under the value cell, as a filtered sum (for finite evaluation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_valCell {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (F : Frame W)
    (φ : Finset W) (c : ℝ) (A : Finset W) :
    mass π (A ∩ valCell F φ c) = ∑ w ∈ A, if mass (F.P w) φ = c then π w else 0 := by
  rw [mass, ← sum_filter]
  congr 1
  ext w; simp [mem_valCell]

/-- Mass of a value cell, as a full sum (for finite evaluation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_valCell {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (F : Frame W)
    (φ : Finset W) (c : ℝ) :
    mass π (valCell F φ c) = ∑ w, if mass (F.P w) φ = c then π w else 0 := by
  rw [← univ_inter (valCell F φ c), mass_inter_valCell]

/-- Mass of the misses of a value cell, as full sums (for finite evaluation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_valCell_sdiff {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (F : Frame W)
    (φ : Finset W) (c : ℝ) :
    mass π (valCell F φ c \ φ) =
      (∑ w, if mass (F.P w) φ = c then π w else 0) -
        ∑ w ∈ φ, if mass (F.P w) φ = c then π w else 0 := by
  have := mass_inter_add_mass_sdiff π (valCell F φ c) φ
  rw [inter_comm, mass_inter_valCell, mass_valCell] at this
  linarith

/-! ## T1 witness: a two-branch immodest refinement frame -/

/-- The deferrer `(1/3, 1/6, 1/8, 3/8)`: branch `A = {0, 1}` with conditional `(2/3, 1/3)`, branch
`B = {2, 3}` with conditional `(1/4, 3/4)`.
Source: [[radical]] `s6` (2)+(3) (branches with non-degenerate conditionals); mandate T1 witness
Kind: D
Fidelity: n/a -/
def π4 : Fin 4 → ℝ := ![1 / 3, 1 / 6, 1 / 8, 3 / 8]

/-- `π4` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π4_mem : π4 ∈ stdSimplex ℝ (Fin 4) :=
  simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The branch map: worlds `0, 1` in branch `A`, worlds `2, 3` in branch `B`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def branch : Fin 4 → Bool := ![true, true, false, false]

/-- **The T1 witness frame**: the Bayesian refinement of `π4` along the branch map — each row is
`π4`'s conditional on its own branch.
Source: mandate T1 (witness N+)
Kind: D
Fidelity: n/a -/
def frame4 : Frame (Fin 4) := refineFrame π4 π4_mem.1 branch

/-- The branch of world `0` has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_branch0 : mass π4 (fibre branch 0) = 1 / 2 := by
  rw [mass, fibre, sum_filter]
  simp [Fin.sum_univ_four, branch, π4] <;> norm_num

/-- The branch of world `2` has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_branch2 : mass π4 (fibre branch 2) = 1 / 2 := by
  rw [mass, fibre, sum_filter]
  simp [Fin.sum_univ_four, branch, π4] <;> norm_num

/-- The rows of `frame4`: `(2/3, 1/3, 0, 0)` on branch `A`, `(0, 0, 1/4, 3/4)` on branch `B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frame4_rows : frame4.P 0 = ![2 / 3, 1 / 3, 0, 0] ∧ frame4.P 2 = ![0, 0, 1 / 4, 3 / 4] := by
  have h0 : 0 < mass π4 (fibre branch 0) := by rw [mass_fibre_branch0]; norm_num
  have h2 : 0 < mass π4 (fibre branch 2) := by rw [mass_fibre_branch2]; norm_num
  constructor
  · funext v
    rw [frame4, refineFrame_P, condRow_apply_of_pos h0, mass_fibre_branch0]
    fin_cases v <;> simp [ind, fibre, branch, π4] <;> norm_num
  · funext v
    rw [frame4, refineFrame_P, condRow_apply_of_pos h2, mass_fibre_branch2]
    fin_cases v <;> simp [ind, fibre, branch, π4] <;> norm_num

/-- **T1 witness (N+).** `frame4` is reflected by `π4`, is immodest, has two distinct candidate
rows, and is not the flat frame — so the full hypothesis package of `collapse` is inhabited by a
frame with content: every one of the six forms holds.
Source: [[radical]] Theorem I4.1 (witness), `s6` (2)+(3); mandate T1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem frame4_witness :
    Reflects π4 frame4 ∧ frame4.Immodest ∧ CandsIntrospective π4 frame4 ∧
      frame4.P 0 ≠ frame4.P 2 ∧ frame4.P 0 ≠ π4 ∧ 0 < π4 0 ∧ 0 < π4 2 ∧
      List.TFAE [Reflects π4 frame4, ValueReflects π4 frame4, VarReflects π4 frame4,
        EstimateMatching π4 frame4, TotalTrust π4 frame4, Value π4 frame4] := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  have hI : frame4.Immodest := refineFrame_immodest _ _
  refine ⟨refineFrame_reflects _ _, hI, candsIntrospective_of_immodest hI π4, ?_, ?_,
    by rw [show π4 0 = 1 / 3 from rfl]; norm_num, by rw [show π4 2 = 1 / 8 from rfl]; norm_num,
    collapse π4_mem (candsIntrospective_of_immodest hI π4)⟩
  · rw [hr0, hr2]; intro h; have := congrFun h 0; simp at this
  · rw [hr0]; intro h; have := congrFun h 2; simp [π4] at this

/-! ## T5 witness: the informative-but-underconfident expert (`s6` (1)) -/

/-- The `s6` deferrer on `(φ,h), (¬φ,h), (φ,l), (¬φ,l)`: `(9/20, 1/20, 1/20, 9/20)`.
Source: [[radical]] Theorem I4.2(b) l. 135; `s6` (1)
Kind: D
Fidelity: exact -/
def π6 : Fin 4 → ℝ := ![9 / 20, 1 / 20, 1 / 20, 9 / 20]

/-- `π6` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π6_mem : π6 ∈ stdSimplex ℝ (Fin 4) :=
  simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The `s6` expert: on the `h`-worlds the row `(3/5, 2/5, 0, 0)` (announces `Q(φ) = 3/5`), on
the `l`-worlds `(0, 0, 2/5, 3/5)` (announces `2/5`); both rows live on their own branch, so the
frame is immodest.
Source: [[radical]] Theorem I4.2(b) l. 135; `s6` (1); mandate T5(b)
Kind: D
Fidelity: exact (rows chosen with the announced `φ`-masses and immodest) -/
def s6 : Frame (Fin 4) where
  P := fun w => if w.val < 2 then ![3 / 5, 2 / 5, 0, 0] else ![0, 0, 2 / 5, 3 / 5]
  P_mem := fun w => by
    split_ifs
    · exact simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The event `φ = {(φ,h), (φ,l)} = {0, 2}`.
Source: [[radical]] `s6` (1)
Kind: D
Fidelity: exact -/
abbrev φ6 : Finset (Fin 4) := {0, 2}

/-- The rows of `s6`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem s6_rows : s6.P 0 = ![3 / 5, 2 / 5, 0, 0] ∧ s6.P 1 = ![3 / 5, 2 / 5, 0, 0] ∧
    s6.P 2 = ![0, 0, 2 / 5, 3 / 5] ∧ s6.P 3 = ![0, 0, 2 / 5, 3 / 5] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The announced values: `3/5` on the `h`-worlds, `2/5` on the `l`-worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem s6_mass_φ : mass (s6.P 0) φ6 = 3 / 5 ∧ mass (s6.P 1) φ6 = 3 / 5 ∧
    mass (s6.P 2) φ6 = 2 / 5 ∧ mass (s6.P 3) φ6 = 2 / 5 := by
  obtain ⟨h0, h1, h2, h3⟩ := s6_rows
  simp [mass, φ6, sum_pair (show (0 : Fin 4) ≠ 2 by decide), h0, h1, h2, h3] <;> norm_num

/-- `π6(φ) = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π6_mass_φ : mass π6 φ6 = 1 / 2 := by
  simp [mass, φ6, sum_pair (show (0 : Fin 4) ≠ 2 by decide), π6] <;> norm_num

/-- **`s6` is immodest**: each row's cell contains its branch, on which it has mass one.
Source: [[radical]] `s6` (1) ("expert in `h` (INT)")
Kind: L
Fidelity: n/a -/
theorem s6_immodest : s6.Immodest := by
  intro w
  apply le_antisymm (mass_le_one (s6.P_mem w) _)
  fin_cases w
  · calc (1 : ℝ) = mass (s6.P 0) {0, 1} := by
          simp [mass, sum_pair (show (0 : Fin 4) ≠ 1 by decide), s6_rows.1] <;> norm_num
      _ ≤ _ := mass_mono (s6.P_nonneg 0) (by
          intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> simp [Frame.mem_cell, s6_rows.1, s6_rows.2.1])
  · calc (1 : ℝ) = mass (s6.P 1) {0, 1} := by
          simp [mass, sum_pair (show (0 : Fin 4) ≠ 1 by decide), s6_rows.2.1] <;> norm_num
      _ ≤ _ := mass_mono (s6.P_nonneg 1) (by
          intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> simp [Frame.mem_cell, s6_rows.1, s6_rows.2.1])
  · calc (1 : ℝ) = mass (s6.P 2) {2, 3} := by
          simp [mass, sum_pair (show (2 : Fin 4) ≠ 3 by decide), s6_rows.2.2.1] <;> norm_num
      _ ≤ _ := mass_mono (s6.P_nonneg 2) (by
          intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> simp [Frame.mem_cell, s6_rows.2.2.1, s6_rows.2.2.2])
  · calc (1 : ℝ) = mass (s6.P 3) {2, 3} := by
          simp [mass, sum_pair (show (2 : Fin 4) ≠ 3 by decide), s6_rows.2.2.2] <;> norm_num
      _ ≤ _ := mass_mono (s6.P_nonneg 3) (by
          intro v hv; simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> simp [Frame.mem_cell, s6_rows.2.2.1, s6_rows.2.2.2])

/-- **Brier: the underconfident expert beats the constant forecast**, `9/50 < 1/4`.
Source: [[radical]] Theorem I4.2(b) l. 135 ("under Brier (9/50 < 1/4)")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_brier : expLoss π6 s6 φ6 brier = 9 / 50 ∧ constLoss π6 φ6 brier = 1 / 4 := by
  obtain ⟨m0, m1, m2, m3⟩ := s6_mass_φ
  constructor
  · rw [expLoss, Fin.sum_univ_four, m0, m1, m2, m3]
    simp [brier, ind, π6] <;> norm_num
  · rw [constLoss, Fin.sum_univ_four, π6_mass_φ]
    simp [brier, ind, π6] <;> norm_num

/-- **Log loss: the underconfident expert beats the constant forecast.** The expert's expected
log loss is `(9/10) log(5/3) + (1/10) log(5/2)`, the constant's is `log 2`, and
`(9/10) log(5/3) + (1/10) log(5/2) < log 2 ⟺ 5¹⁰ < 2¹¹ · 3⁹` (`9765625 < 40310784`), proved
exactly under `Real.log`'s monotonicity — no decimal in the statement.
Source: [[radical]] Theorem I4.2(b) l. 135 ("under log (0.551 < 0.693)"); plan §0.4 rule 4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_log : expLoss π6 s6 φ6 logLoss < constLoss π6 φ6 logLoss := by
  obtain ⟨m0, m1, m2, m3⟩ := s6_mass_φ
  have hind : ind φ6 0 = 1 ∧ ind φ6 1 = 0 ∧ ind φ6 2 = 1 ∧ ind φ6 3 = 0 := by
    simp [ind, φ6]
  have q : π6 0 = 9 / 20 ∧ π6 1 = 1 / 20 ∧ π6 2 = 1 / 20 ∧ π6 3 = 9 / 20 := ⟨rfl, rfl, rfl, rfl⟩
  have l1 : logLoss (3 / 5) 1 = Real.log 5 - Real.log 3 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have l2 : logLoss (3 / 5) 0 = Real.log 5 - Real.log 2 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have l3 : logLoss (2 / 5) 1 = Real.log 5 - Real.log 2 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have l4 : logLoss (2 / 5) 0 = Real.log 5 - Real.log 3 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num)]; ring
  have l5 : logLoss (1 / 2) 1 = Real.log 2 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have l6 : logLoss (1 / 2) 0 = Real.log 2 := by
    unfold logLoss; norm_num; rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  have e1 : expLoss π6 s6 φ6 logLoss =
      (9 / 10) * (Real.log 5 - Real.log 3) + (1 / 10) * (Real.log 5 - Real.log 2) := by
    unfold expLoss
    rw [Fin.sum_univ_four, m0, m1, m2, m3, hind.1, hind.2.1, hind.2.2.1, hind.2.2.2, l1, l2, l3,
      l4, q.1, q.2.1, q.2.2.1, q.2.2.2]
    ring
  have e2 : constLoss π6 φ6 logLoss = Real.log 2 := by
    unfold constLoss
    rw [Fin.sum_univ_four, π6_mass_φ, hind.1, hind.2.1, hind.2.2.1, hind.2.2.2, l5, l6, q.1,
      q.2.1, q.2.2.1, q.2.2.2]
    ring
  rw [e1, e2]
  have key : 10 * Real.log 5 < 11 * Real.log 2 + 9 * Real.log 3 := by
    have h1 : Real.log ((5 : ℝ) ^ 10) = 10 * Real.log 5 := by rw [Real.log_pow]; push_cast; ring
    have h2 : Real.log ((2 : ℝ) ^ 11 * 3 ^ 9) = 11 * Real.log 2 + 9 * Real.log 3 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    rw [← h1, ← h2]
    exact Real.log_lt_log (by positivity) (by norm_num)
  linarith

/-- **Value-form reflection fails for `φ` on `s6`**: at `c = 3/5`, `π(φ ∩ C) = 9/20` while
`c · π(C) = 3/10`.
Source: [[radical]] Theorem I4.2(b) l. 135 ("reflection fails in both cells")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_not_valueReflectsOn : ¬ ValueReflectsOn π6 s6 φ6 := by
  intro h
  have := h (3 / 5)
  rw [mass_inter_valCell, mass_valCell] at this
  obtain ⟨m0, m1, m2, m3⟩ := s6_mass_φ
  rw [Fin.sum_univ_four, sum_pair (show (0 : Fin 4) ≠ 2 by decide), m0, m1, m2, m3] at this
  simp [π6] at this <;> norm_num at this

/-- **Total Trust fails on `s6`** at the self-referential bet `X = 𝟙[¬φ ∧ h] = 𝟙_{1}`,
`t = 3/10`: the above-threshold event is the `h`-branch and
`∑ π w (X w − 3/10) = 9/20 · (−3/10) + 1/20 · (7/10) = −1/10 < 0`. So the model separates
proposition-wise accuracy from Total Trust as well.
Source: [[radical]] Theorem I4.2(c) l. 136 (`E[X | E_Q X ≥ 0.3] = 0.1`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s6_not_totalTrust : ¬ TotalTrust π6 s6 := by
  intro h
  have := h (ind {1}) (3 / 10)
  obtain ⟨h0, h1, h2, h3⟩ := s6_rows
  simp [Fin.sum_univ_four, E, ind, h0, h1, h2, h3, π6] at this <;> norm_num at this

/-- **T5 separation, assembled.** The `s6` model is immodest, accuracy-increasing for `φ` under
Brier and log loss, and fails both value-form reflection for `φ` and Total Trust:
proposition-wise accuracy is strictly weaker than reflection.
Source: [[radical]] Theorem I4.2(b)(c) ll. 135–136; [[armstrong]] I4.2(ii) l. 121
Kind: N+
Fidelity: weaker: two scores (Brier and log; the source's (Acc_φ) is over every proper score)
Hyps: (a) none -/
theorem s6_separation :
    s6.Immodest ∧ expLoss π6 s6 φ6 brier < constLoss π6 φ6 brier ∧
      expLoss π6 s6 φ6 logLoss < constLoss π6 φ6 logLoss ∧
      ¬ ValueReflectsOn π6 s6 φ6 ∧ ¬ TotalTrust π6 s6 :=
  ⟨s6_immodest, by rw [s6_brier.1, s6_brier.2]; norm_num, s6_log, s6_not_valueReflectsOn,
    s6_not_totalTrust⟩

/-! ## T11(b): the converse of the partition lemma fails (ddb's I5 witness) -/

/-- ddb's deferrer on `(L,g), (L,b), (¬L,g), (¬L,b)`: `(4/10, 4/10, 1/10, 1/10)`.
Source: [[ddb]] I5 witness l. 132
Kind: D
Fidelity: exact -/
def πddb : Fin 4 → ℝ := ![4 / 10, 4 / 10, 1 / 10, 1 / 10]

/-- ddb's frame: on `L` the overseers track the world, `(9/10, 1/10, 0, 0)` and
`(1/10, 9/10, 0, 0)`; on `¬L` they are anti-experts, `(0, 0, 1/10, 9/10)` and `(0, 0, 9/10, 1/10)`.
Source: [[ddb]] I5 witness l. 132
Kind: D
Fidelity: exact -/
def ddb4 : Frame (Fin 4) where
  P := ![![9 / 10, 1 / 10, 0, 0], ![1 / 10, 9 / 10, 0, 0], ![0, 0, 1 / 10, 9 / 10],
    ![0, 0, 9 / 10, 1 / 10]]
  P_mem := fun w => by
    fin_cases w <;>
      exact simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The legitimacy event `L = {0, 1}`.
Source: [[ddb]] I5 witness l. 132
Kind: D
Fidelity: exact -/
abbrev Lddb : Finset (Fin 4) := {0, 1}

/-- **Total Trust conditional on `L` holds** on ddb's frame: on the restricted deferrer
`(2/5, 2/5, 0, 0)` the two above-threshold cases reduce to `X 0 + X 1 ≥ 2s` (both in) and
`X 0 > X 1` (one in), each linear.
Source: [[ddb]] I5 witness l. 132 ("Total Trust conditional on `L` holds")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ddb4_legitimizingTT : LegitimizingTT πddb ddb4 Lddb := by
  intro X s
  simp only [Fin.sum_univ_four, restrict_apply, Lddb, E, ddb4, πddb, Matrix.cons_val]
  simp only [mem_insert, mem_singleton, Fin.reduceEq, or_false, or_true, if_true, if_false,
    Fin.isValue, zero_mul, mul_zero, add_zero, zero_add]
  split_ifs <;> linarith

/-- **Total Trust conditional on `¬L` fails** (the anti-experts): at `X = 𝟙_{2}`, `s = 9/10`.
Source: [[ddb]] I5 witness l. 132 ("conditional on `¬L` fails")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ddb4_not_legitimizingTT_compl : ¬ LegitimizingTT πddb ddb4 (univ \ Lddb) := by
  intro h
  have := h (ind {2}) (9 / 10)
  simp [Fin.sum_univ_four, restrict_apply, Lddb, E, ind, ddb4, πddb] at this <;> norm_num at this

/-- **Total Trust fails unconditionally** on ddb's frame (same bet).
Source: [[ddb]] I5 witness l. 132 ("unconditionally fails")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ddb4_not_totalTrust : ¬ TotalTrust πddb ddb4 := by
  intro h
  have := h (ind {2}) (9 / 10)
  simp [Fin.sum_univ_four, E, ind, ddb4, πddb] at this <;> norm_num at this

/-! ## T11(c): the two senses differ without introspection -/

open Cleanroom.Found.LitDdbFrames.Examples in
/-- **Without introspection the two "legitimizing" senses differ**: `fig3` with `L = Ω` is
TT-legitimizing (Total Trust holds) but not value-form legitimizing for `φ = {0}` (`c = 9/10`:
`π(φ ∩ C) = 1/2 ≠ 9/20`).
Source: mandate T11(c); [[ddb]] fn 18 (Figure 3 modest)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_legitimizingTT_not_val :
    LegitimizingTT half fig3 univ ∧ ¬ (∀ φ, LegitimizingVal half fig3 φ univ) := by
  constructor
  · unfold LegitimizingTT; rw [restrict_univ]; exact fig3_totalTrust_value.1
  · intro h
    have := h {0} (9 / 10)
    rw [inter_univ, univ_inter, mass_inter_valCell, mass_valCell] at this
    simp [Fin.sum_univ_two, sum_singleton, mass_singleton, fig3_P0, fig3_P1, half] at this <;>
      norm_num at this

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
