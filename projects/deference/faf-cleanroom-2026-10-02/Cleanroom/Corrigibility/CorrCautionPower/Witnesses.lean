import Cleanroom.Corrigibility.CorrCautionPower.CautionRule

/-!
# `corr-caution-power` — witnesses and refutations for T1, T2, T3, T5

Concrete instances on `Fin 2` / `Fin 3` / `Fin (n+4)` with FAF's `Distr.uniform` and a two-point
posterior `twoPt p`:

* **T1(iv), S1's content** `s1_same_agent_two_targets`: one posterior, one base, two targets —
  conservatively calibrated against one, reckless against the other. `ρ` is not a function of `P`.
* **T1(v), 2-036(b)** `s1_estZero_trueHarm_pos`: `R̂ = 0 < R`; D8 gives `q = 0` (no
  quantilizer), D8′ gives `q = q_min`.
* **T2, Taylor's three-action example** (`taylor3_*`): `Q_q = δ_c` for `q ≤ 1/3`, `(0, 2/5, 3/5)`
  at `q = 5/9`, `γ` at `q = 1`, under the natural order, which is compatible with
  `U = (0.2, 0.5, 0.7)`.
* **T3, the withdrawn gloss refuted inside D1** `gloss_refuted`: `n + 4` uniform base actions,
  every value in `[0, 1]`, the harmful action proxy-top under the natural order, `R = R̂`,
  `H = η = (n+4) η · R`; the source's `n = 1000, η = 1/10` (`gloss_refuted_1000`). **Finding:**
  the mandate's construction (`P = δ_{ω*}` with the harmful action proxy-top) is inconsistent —
  at a point-mass posterior the proxy *is* the truth and a proxy-top action has zero commission
  harm; the witness here uses a two-hypothesis posterior with `R̂ = R` restored by two
  harmless-in-truth decoys the second hypothesis fears (audit r1 B1: the round-0 witness rated
  `a°` at `3`, outside D1's range; repaired here, with `InRange` and `Compatible` in the
  statement).
* **T3, the floored bound is tight under misspecification** `floored_tight_misspec`: `R̂ = 0 < R`
  and `H = R / q_min` exactly.
* **T5, S5(b) refuted for `δ > 0` inside realizability** (`witnessB_*`): the corrected predicate
  holds, both actions covered, and `R̂ < R`.
* **T5, the repaired S5(b) on a mixed witness** (`mixed_witness`): `∅` and `a` covered, `b`
  known-uncovered, both repaired bounds and the computable bound instantiated.
* **T5, S2 needs the null action covered** `s2_null_uncovered`: `a` covered, `∅` not,
  `|c(a) − (U(∅) − U(a))⁺| = 3/10 > 2δ = 1/10`; and the same state shows **the source's printed
  predicate does not give `COR_δ`** (`printed_predicate_no_CORδ`): `R − 2δ = 2/5 > 7/20 = R̂`.

Sources: `caution-final.md` S1 (l. 61), S3 (l. 65), S4(c) (l. 67), S5(b) (l. 69), proofs §3, §5;
`caution-adversary.md` A0.1–A0.2, A2.2, A3.2, A5.2; Taylor 2016 l. 60–75.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-! ## Helpers -/

/-- The two-point distribution on `Fin 2` with mass `p` on `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def twoPt (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distr (Fin 2) where
  mass := ![1 - p, p]
  nonneg := by
    intro s; fin_cases s
    · simp; linarith
    · simpa
  sum_eq_one := by simp [Fin.sum_univ_two]

/-- Masses of `twoPt`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma twoPt_mass (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (twoPt p h0 h1).mass = ![1 - p, p] := rfl

/-- Expectation on `Fin 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_fin2 (μ : Distr (Fin 2)) (X : Fin 2 → ℝ) :
    expect μ X = μ.mass 0 * X 0 + μ.mass 1 * X 1 := by
  simp [expect, Fin.sum_univ_two]

/-- Expectation on `Fin 3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_fin3 (μ : Distr (Fin 3)) (X : Fin 3 → ℝ) :
    expect μ X = μ.mass 0 * X 0 + μ.mass 1 * X 1 + μ.mass 2 * X 2 := by
  simp [expect, Fin.sum_univ_three]

/-- The uniform mass on `Fin n`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma uniform_mass_fin {n : ℕ} [NeZero n] (a : Fin n) :
    (Distr.uniform : Distr (Fin n)).mass a = (n : ℝ)⁻¹ := by
  simp [Distr.uniform]

/-- The last element of `Fin (n+1)` has nothing above it.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_last {n : ℕ} (γ : Distr (Fin (n + 1))) : above γ (Fin.last n) = 0 := by
  unfold above
  refine sum_eq_zero fun b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at hb
  exact absurd (Fin.le_last b) (not_le.mpr hb)

/-! ## T1(iv) — S1: the same agent, two targets -/

/-- The S1 state: `A = Fin 2` (`nul = 0`, `a = 1`), `Ω = Fin 2`, uniform posterior and base,
`V ω₁ = (1, 1)` (`a` harmless), `V ω₂ = (1, 0)` (`a` harmful), target `t`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md S1 (l. 61)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def s1State (t : Fin 2) : CautionState (Fin 2) (Fin 2) where
  V := ![![1, 1], ![1, 0]]
  nul := 0
  P := Distr.uniform
  target := t
  γ := Distr.uniform

/-- **S1(i)/(ii)/(v), the witness (N+):** with the same `V`, `nul`, `P` and `γ`, the agent with
target `ω₁` is conservatively calibrated (`R = 0 ≤ 1/4 = R̂`) and the agent with target `ω₂` is
reckless (`R̂ = 1/4 < 1/2 = R`): no functional of `P` can be `ρ`, and the two agents are one
object under introspection. Non-degenerate: two hypotheses with positive weight disagreeing
about harm, `R̂ ∉ {0, R}`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md S1 (l. 61); caution-adversary.md A0.2 (l. 19)
Kind: N+
Fidelity: exact (S1(i)/(ii)/(v) as a witness, not as a quantification over functionals)
Hyps: none -/
theorem s1_same_agent_two_targets :
    (s1State 0).ConservativelyCalibrated ∧ (s1State 1).Reckless ∧
      (s1State 0).P = (s1State 1).P ∧ (s1State 0).γ = (s1State 1).γ ∧
      (s1State 0).V = (s1State 1).V ∧ (s1State 0).estBaseHarm = 1 / 4 ∧
      (s1State 0).baseHarm = 0 ∧ (s1State 1).baseHarm = 1 / 2 := by
  have hest : ∀ t, (s1State t).estBaseHarm = 1 / 4 := by
    intro t
    simp only [CautionState.estBaseHarm, CautionState.estHarm, CautionState.harm, s1State,
      expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  have hb0 : (s1State 0).baseHarm = 0 := by
    simp only [CautionState.baseHarm, CautionState.trueHarm, CautionState.harm, s1State,
      expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  have hb1 : (s1State 1).baseHarm = 1 / 2 := by
    simp only [CautionState.baseHarm, CautionState.trueHarm, CautionState.harm, s1State,
      expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  refine ⟨?_, ?_, rfl, rfl, rfl, hest 0, hb0, hb1⟩
  · unfold CautionState.ConservativelyCalibrated; rw [hest, hb0]; norm_num
  · unfold CautionState.Reckless; rw [hest, hb1]; norm_num

/-! ## T1(v) — 2-036(b): `R̂ = 0 < R` -/

/-- The 2-036(b) state: point-mass posterior on `ω₁` (`V ω₁ = (1, 1)`, no harm) while the target
is `ω₂` (`V ω₂ = (1, 0)`, `a` harmful); uniform base.
Source: [[corr-wf14-2-inventory]] 2-036 / caution-adversary.md A0.2 (l. 19)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def estZeroState : CautionState (Fin 2) (Fin 2) where
  V := ![![1, 1], ![1, 0]]
  nul := 0
  P := twoPt 0 le_rfl zero_le_one
  target := 1
  γ := Distr.uniform

/-- **2-036(b) (N+):** `R̂ = 0 < 1/2 = R`; D8's slice is `q = 0` — not a quantilizer (Lean's
`OP 0 = log (1/0) = 0` is junk, the source's `+∞`); D8′'s slice is `q_min` for every
`q_min > 0` (`OP q_min = log (1/q_min)` is then definitional and not restated). The point-mass
posterior is the maximally overconfident agent of A0.1.
Source: [[corr-wf14-2-inventory]] 2-036 / caution-adversary.md A0.2 (l. 19); caution-final.md S4(b), S6(a) (l. 67, 71)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem s1_estZero_trueHarm_pos (η qmin : ℝ) :
    estZeroState.estBaseHarm = 0 ∧ estZeroState.baseHarm = 1 / 2 ∧
      qRule η estZeroState.estBaseHarm = 0 ∧
      (0 < qmin → qRuleFloored qmin η estZeroState.estBaseHarm = qmin) := by
  have hest : estZeroState.estBaseHarm = 0 := by
    simp only [CautionState.estBaseHarm, CautionState.estHarm, CautionState.harm, estZeroState,
      expect_fin2, harmOf, uniform_mass_fin, twoPt_mass]
    norm_num
  have hb : estZeroState.baseHarm = 1 / 2 := by
    simp only [CautionState.baseHarm, CautionState.trueHarm, CautionState.harm, estZeroState,
      expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  refine ⟨hest, hb, ?_, fun hqmin => ?_⟩
  · rw [hest]; simp [qRule]
  · rw [hest]; simp [qRuleFloored, hqmin.le]

/-! ## T2 — Taylor's three-action example -/

/-- Taylor's utilities `(0.2, 0.5, 0.7)` on `A = {a, b, c} = Fin 3`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 l. 66–70
Kind: D
Fidelity: exact -/
noncomputable def taylorU : Fin 3 → ℝ := ![1 / 5, 1 / 2, 7 / 10]

/-- The natural order on `Fin 3` is compatible with Taylor's utilities.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 l. 66–70
Kind: L
Fidelity: exact -/
theorem taylorU_compatible : Compatible taylorU := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [taylorU, Fin.lt_def] <;> norm_num

/-- `above` for the uniform base on `Fin 3`: `(2/3, 1/3, 0)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma above_uniform_fin3 :
    above (Distr.uniform : Distr (Fin 3)) 0 = 2 / 3 ∧
    above (Distr.uniform : Distr (Fin 3)) 1 = 1 / 3 ∧
    above (Distr.uniform : Distr (Fin 3)) 2 = 0 := by
  simp only [above, sum_filter, Fin.sum_univ_three, uniform_mass_fin, Fin.lt_def]
  norm_num

/-- **Taylor's example, `q ≤ 1/3`:** the quantilizer is the maximizer `δ_c`.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 l. 70 ("If `q ≤ 1/3`, it always returns `c`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem taylor3_maximizer {q : ℝ} (hq : 0 < q) (hq3 : q ≤ 1 / 3) :
    (quantilize (Distr.uniform : Distr (Fin 3)) q hq (by linarith)).mass 0 = 0 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) q hq (by linarith)).mass 1 = 0 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) q hq (by linarith)).mass 2 = 1 := by
  obtain ⟨h0, h1, h2⟩ := above_uniform_fin3
  have hq3' : q ≤ (3 : ℝ)⁻¹ := by rw [inv_eq_one_div]; exact hq3
  refine ⟨?_, ?_, ?_⟩
  · rw [quantilize_mass, qmass_of_le_above _ (by rw [h0]; linarith)]
  · rw [quantilize_mass, qmass_of_le_above _ (by rw [h1]; linarith)]
  · rw [quantilize_mass, qmass, aboveEq_eq, h2, uniform_mass_fin, zero_add, min_eq_right hq.le,
      sub_zero]
    push_cast
    rw [min_eq_left hq3', div_self hq.ne']

/-- **Taylor's example, `q = 5/9`:** the quantilizer is `(0, 2/5, 3/5)` (Figure 1).
Source: [[corr-refs-inventory]] 065 / Taylor 2016 Figure 1 (l. 66–70)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem taylor3_five_ninths :
    (quantilize (Distr.uniform : Distr (Fin 3)) (5 / 9) (by norm_num) (by norm_num)).mass 0 = 0 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) (5 / 9) (by norm_num) (by norm_num)).mass 1 = 2 / 5 ∧
    (quantilize (Distr.uniform : Distr (Fin 3)) (5 / 9) (by norm_num) (by norm_num)).mass 2 = 3 / 5 := by
  obtain ⟨h0, h1, h2⟩ := above_uniform_fin3
  refine ⟨?_, ?_, ?_⟩
  · rw [quantilize_mass, qmass_of_le_above _ (by rw [h0]; norm_num)]
  · rw [quantilize_mass, qmass, aboveEq_eq, h1, uniform_mass_fin]; norm_num
  · rw [quantilize_mass, qmass, aboveEq_eq, h2, uniform_mass_fin]; norm_num

/-- **Taylor's example, `q = 1`:** the quantilizer mimics the base.
Source: [[corr-refs-inventory]] 065 / Taylor 2016 l. 70 ("a 1-quantilizer just mimics `γ`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem taylor3_mimic :
    quantilize (Distr.uniform : Distr (Fin 3)) 1 one_pos le_rfl = Distr.uniform := by
  ext a
  rw [quantilize_mass, qmass_of_aboveEq_le _ (aboveEq_le_one _ _), div_one]

/-! ## T3 — the withdrawn gloss, refuted inside D1's range -/

section Gloss

variable (n : ℕ)

/-- The gloss state on `A = Fin (n+4)`, **inside D1's range `[0, 1]`** (audit r1 B1: the round-0
witness rated `a°` at `3`): decoys `b₁ = 0`, `b₂ = 1`, `nul = 2`, `n` further actions, the
harmful action `a° = last`; `Ω = Fin 2` with `P = (3/10, 7/10)`, target `ω* = 0`;
`V ω* = 1` except `V ω* a° = 0`; `V ω' = 0` on the decoys, `1/2` on `∅` and the rest, `1` on `a°`;
uniform base. Then the proxy is `3/10` on the decoys, `13/20` on `∅` and the rest, `7/10` on `a°`
(top; the natural order is compatible); `c(a°) = 1`, `c = 0` elsewhere; `ĉ(a°) = 3/10`,
`ĉ(bᵢ) = 7/20`, `ĉ = 0` elsewhere; so `R = R̂ = 1/(n+4)`. Two decoys are necessary: with one,
`R̂ = R` and `a°` proxy-top are incompatible inside `[0, 1]` (the decoy would need harm `1`
under `ω'`, forcing `V ω'(∅) = 1` and `U(∅) > U(a°)`).
Source: [[corr-wf14-inventory]] 096 / caution-final.md S3 gloss (l. 65), proof §3 (l. 121)
Kind: D
Fidelity: variant: two-hypothesis posterior (the source's `ρ = 1` realized without a point mass — see the module docstring); every value in `[0, 1]`
Hyps: n/a (witness) -/
noncomputable def glossState : CautionState (Fin (n + 4)) (Fin 2) where
  V := ![fun a => if a = Fin.last (n + 3) then 0 else 1,
         fun a => if a = Fin.last (n + 3) then 1 else if a = 0 then 0 else if a = 1 then 0 else 1 / 2]
  nul := 2
  P := twoPt (7 / 10) (by norm_num) (by norm_num)
  target := 0
  γ := Distr.uniform

/-- `0 ≠ last` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zero_ne_last : (0 : Fin (n + 4)) ≠ Fin.last (n + 3) := by
  rw [Ne, Fin.ext_iff]; simp

/-- `1 ≠ last` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma one_ne_last : (1 : Fin (n + 4)) ≠ Fin.last (n + 3) := by
  rw [Ne, Fin.ext_iff]; simp

/-- `2 ≠ last` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma two_ne_last : (2 : Fin (n + 4)) ≠ Fin.last (n + 3) := by
  intro h
  have h' := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega)] at h' <;> omega

/-- `0 ≠ 1` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma zero_ne_one' : (0 : Fin (n + 4)) ≠ 1 := by
  rw [Ne, Fin.ext_iff]; simp

/-- `2 ≠ 0` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma two_ne_zero' : (2 : Fin (n + 4)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega)] at h'

/-- `2 ≠ 1` in `Fin (n+4)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma two_ne_one' : (2 : Fin (n + 4)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega)] at h'

/-- The true harm in the gloss state is the indicator of `a°`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma glossState_trueHarm :
    (glossState n).trueHarm = fun a => if a = Fin.last (n + 3) then 1 else 0 := by
  funext a
  simp only [CautionState.trueHarm, CautionState.harm, harmOf, glossState, Matrix.cons_val_zero,
    two_ne_last, if_false]
  split_ifs <;> norm_num

/-- The estimated harm in the gloss state: `3/10` on `a°`, `7/20` on each decoy, `0` elsewhere.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma glossState_estHarm :
    (glossState n).estHarm = fun a => if a = Fin.last (n + 3) then 3 / 10
      else if a = 0 then 7 / 20 else if a = 1 then 7 / 20 else 0 := by
  funext a
  simp only [CautionState.estHarm, CautionState.harm, harmOf, glossState, expect_fin2, twoPt_mass,
    Matrix.cons_val_zero, Matrix.cons_val_one, two_ne_last, two_ne_zero', two_ne_one', if_false]
  by_cases ha : a = Fin.last (n + 3)
  · subst ha; simp <;> norm_num
  · by_cases h0 : a = 0
    · subst h0; simp [zero_ne_last, zero_ne_one'] <;> norm_num
    · by_cases h1 : a = 1
      · subst h1; simp [one_ne_last, (zero_ne_one' n).symm] <;> norm_num
      · simp [ha, h0, h1]

/-- `R = R̂ = 1/(n+4)` in the gloss state: conservatively calibrated with equality.
Source: [[corr-wf14-inventory]] 096 / caution-final.md proof §3 (l. 121, "`R_t = R̂_t = 10⁻³`")
Kind: L
Fidelity: exact -/
lemma glossState_baseHarm :
    (glossState n).baseHarm = ((n : ℝ) + 4)⁻¹ ∧ (glossState n).estBaseHarm = ((n : ℝ) + 4)⁻¹ := by
  have hγ : (glossState n).γ = Distr.uniform := rfl
  constructor
  · rw [CautionState.baseHarm, expect, glossState_trueHarm, hγ]
    simp only [uniform_mass_fin, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
    push_cast; ring
  · rw [CautionState.estBaseHarm, expect, glossState_estHarm, hγ]
    simp only [uniform_mass_fin]
    have key : ∀ (c : ℝ) (a : Fin (n + 4)), c *
        (if a = Fin.last (n + 3) then (3 / 10 : ℝ) else if a = 0 then 7 / 20
          else if a = 1 then 7 / 20 else 0)
        = (if a = Fin.last (n + 3) then 3 * c / 10 else 0) + (if a = 0 then 7 * c / 20 else 0)
          + (if a = 1 then 7 * c / 20 else 0) := by
      intro c a
      by_cases ha : a = Fin.last (n + 3)
      · subst ha; simp [(zero_ne_last n).symm, (one_ne_last n).symm]; ring
      · by_cases h0 : a = 0
        · subst h0; simp [zero_ne_last, zero_ne_one']; ring
        · by_cases h1 : a = 1
          · subst h1; simp [one_ne_last, (zero_ne_one' n).symm]; ring
          · simp [ha, h0, h1]
    simp only [key, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
    push_cast; ring

/-- The proxy of the gloss state: `7/10` on `a°` (top), `3/10` on the decoys, `13/20` elsewhere.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma glossState_proxy (x : Fin (n + 4)) : (glossState n).proxy x =
    if x = Fin.last (n + 3) then 7 / 10 else if x = 0 then 3 / 10
      else if x = 1 then 3 / 10 else 13 / 20 := by
  simp only [CautionState.proxy, glossState, expect_fin2, twoPt_mass, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  by_cases hx : x = Fin.last (n + 3)
  · subst hx; simp <;> norm_num
  · by_cases h0 : x = 0
    · subst h0; simp <;> norm_num
    · by_cases h1 : x = 1
      · subst h1; simp [one_ne_last, (zero_ne_one' n).symm] <;> norm_num
      · simp [hx, h0, h1] <;> norm_num

/-- The proxy of the gloss state ranks `a°` top and the decoys bottom: the natural order is
compatible.
Source: [[corr-wf14-inventory]] 096 / caution-final.md proof §3 (l. 121, "`a°` proxy-top")
Kind: L
Fidelity: exact -/
lemma glossState_proxy_compatible : Compatible (glossState n).proxy := by
  intro a b hab
  rw [glossState_proxy, glossState_proxy]
  have hane : a ≠ Fin.last (n + 3) := fun h => by
    subst h; exact absurd (Fin.le_last b) (not_le.mpr hab)
  have hbne : b ≠ 0 := fun h => by subst h; exact absurd (Fin.zero_le a) (not_le.mpr hab)
  by_cases hb1 : b = 1
  · have ha0 : a = 0 := by
      apply Fin.ext
      have h := Fin.lt_def.mp hab
      rw [hb1] at h
      simp at h
      omega
    subst hb1; subst ha0
    simp [one_ne_last]
  · simp only [hane, hbne, hb1, if_false]
    split_ifs <;> norm_num

/-- Every value of the gloss state lies in `[0, 1]` (D1).
Source: caution-final.md D1 (l. 25). Kind: L. Fidelity: exact -/
lemma glossState_inRange : (glossState n).InRange := by
  unfold CautionState.InRange
  rw [Fin.forall_fin_two]
  simp only [glossState, Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_Icc]
  refine ⟨fun a => ?_, fun a => ?_⟩ <;> split_ifs <;> norm_num

/-- **The withdrawn gloss, refuted inside D1's range (N+).** Quoted (`caution.md` S3, l. 71):
"if `ρ_t ≤ 1` then `H_t ≤ max{R_t, η}` — the agent never does worse than sampling the trusted
base distribution" (withdrawn in `caution-final.md` S3). Reading of the withdrawn clause:
`R ≤ R̂ → H ≤ R`. In the gloss state with `N = n + 4` base actions — every value in `[0, 1]`
(`InRange`), the proxy ranking `a°` top under the natural order (`Compatible`), `η ≤ 1`,
`1 < N η` — `R = R̂ = 1/N` (conservatively calibrated), the D8 slice is `q = 1/(Nη)`, the
quantilizer puts mass `η` on `a°`, and `H = η = Nη · R > R`. Surviving neighbour:
`realizedHarm_qRule_le_max` (`H ≤ max R η`), the formal clause of the quoted sentence, which
holds.
Source: [[corr-wf14-inventory]] 096 / caution.md S3 (l. 71); caution-final.md S3 (l. 65), proof §3 (l. 121); caution-adversary.md A3.2 (l. 35)
Kind: N+
Fidelity: exact (the witness is a D1 state: range, realizability, proxy-compatible order, all in the statement)
Hyps: none -/
theorem gloss_refuted {η : ℝ} (hη1 : η ≤ 1) (hNη : 1 < ((n : ℝ) + 4) * η) :
    (glossState n).InRange ∧ Compatible (glossState n).proxy ∧
    (glossState n).ConservativelyCalibrated ∧
    (glossState n).baseHarm = ((n : ℝ) + 4)⁻¹ ∧
    ∃ (hq : 0 < qRule η (glossState n).estBaseHarm) (hq1 : qRule η (glossState n).estBaseHarm ≤ 1),
      (glossState n).realizedHarm (quantilize (glossState n).γ (qRule η _) hq hq1) = η ∧
      (glossState n).baseHarm < (glossState n).realizedHarm (quantilize (glossState n).γ (qRule η _) hq hq1) := by
  obtain ⟨hR, hRh⟩ := glossState_baseHarm n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  have hη : 0 < η := by
    by_contra h; have h' := not_lt.mp h; nlinarith
  have hcal : (glossState n).ConservativelyCalibrated := by
    unfold CautionState.ConservativelyCalibrated; rw [hR, hRh]
  have hq : 0 < qRule η (glossState n).estBaseHarm := qRule_pos hη (by rw [hRh]; positivity)
  have hqval : qRule η (glossState n).estBaseHarm = (((n : ℝ) + 4) * η)⁻¹ := by
    have hle : ((n : ℝ) + 4)⁻¹ / η ≤ 1 := by
      rw [div_le_one hη, inv_le_iff_one_le_mul₀ hN]; nlinarith
    unfold qRule; rw [hRh, min_eq_right hle, div_eq_mul_inv, ← mul_inv]
  have hqle : qRule η (glossState n).estBaseHarm ≤ 1 := qRule_le_one _ _
  have hH : (glossState n).realizedHarm (quantilize (glossState n).γ (qRule η _) hq hqle) = η := by
    simp only [CautionState.realizedHarm, expect, glossState_trueHarm, mul_ite, mul_one,
      mul_zero, sum_ite_eq', mem_univ, if_true, quantilize_mass]
    have hg : (glossState n).γ.mass (Fin.last (n + 3)) = ((n : ℝ) + 4)⁻¹ := by
      show (Distr.uniform : Distr (Fin (n + 4))).mass _ = _
      rw [uniform_mass_fin]; push_cast; ring
    rw [(glossState n).qmass_top hq (above_last _), hg, hqval, min_eq_right]
    · field_simp
    · rw [inv_le_inv₀ hN (mul_pos hN hη)]
      exact mul_le_of_le_one_right hN.le hη1
  refine ⟨glossState_inRange n, glossState_proxy_compatible n, hcal, hR, hq, hqle, hH, ?_⟩
  rw [hH, hR, inv_lt_iff_one_lt_mul₀' hN]
  exact hNη

/-- **The source's numbers:** `n = 1000` uniform base actions (`Fin 1000 = Fin (996 + 4)`),
`η = 1/10`: `H = 1/10 = 100 R`, inside D1's range.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S3 (l. 65), proof §3 (l. 121)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem gloss_refuted_1000 :
    (glossState 996).InRange ∧ Compatible (glossState 996).proxy ∧
    (glossState 996).baseHarm = 1 / 1000 ∧
    ∃ (hq : 0 < qRule (1 / 10) (glossState 996).estBaseHarm)
      (hq1 : qRule (1 / 10) (glossState 996).estBaseHarm ≤ 1),
      (glossState 996).realizedHarm (quantilize (glossState 996).γ (qRule (1 / 10) _) hq hq1) = 1 / 10 ∧
      (glossState 996).realizedHarm (quantilize (glossState 996).γ (qRule (1 / 10) _) hq hq1)
        = 100 * (glossState 996).baseHarm := by
  obtain ⟨hrange, hcomp, -, hR, hq, hq1, hH, -⟩ :=
    gloss_refuted 996 (η := 1 / 10) (by norm_num) (by norm_num)
  refine ⟨hrange, hcomp, by rw [hR]; norm_num, hq, hq1, hH, ?_⟩
  rw [hH, hR]; norm_num

end Gloss

/-! ## T3 — the floored bound is tight under misspecification -/

/-- The misspecified state: `A = Fin 2` (`nul = 0`, `a° = 1`), `Ω = Fin 1` with `V ≡ 0` (the agent
sees no harm anywhere: `R̂ = 0`), uniform base. The true value function `trueV = (1, 0)` is
*outside* `Ω`: `harmOf 0 trueV = (0, 1)`.
Source: [[corr-wf14-2-inventory]] 2-046 / caution-final.md S4(c) (l. 67)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def misspecState : CautionState (Fin 2) (Fin 1) where
  V := fun _ _ => 0
  nul := 0
  P := Distr.uniform
  target := 0
  γ := Distr.uniform

/-- The true value function outside the algebra. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def misspecTrueV : Fin 2 → ℝ := ![1, 0]

/-- **S4(c)'s robust bound is tight under misspecification (N+):** `R̂ = 0`, so D8′ at
`q_min = 1/2`, `η = 1` gives `q = q_min`; the quantilizer (any order is compatible with the
constant proxy) is `δ_{a°}`; the true harm is `E_Q[c^true] = 1 = (1/2)/(1/2) = E_γ[c^true]/q_min`
exactly, while `R = 1/2 > 0 = R̂`.
Source: [[corr-wf14-2-inventory]] 2-046 / caution-final.md S4(c) (l. 67), proof §4 (l. 125)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem floored_tight_misspec :
    misspecState.estBaseHarm = 0 ∧
    expect misspecState.γ (harmOf misspecState.nul misspecTrueV) = 1 / 2 ∧
    qRuleFloored (1 / 2) 1 misspecState.estBaseHarm = 1 / 2 ∧
    expect (quantilize misspecState.γ (qRuleFloored (1 / 2) 1 misspecState.estBaseHarm)
        (qRuleFloored_pos (by norm_num) _ _) (qRuleFloored_le_one (by norm_num) _ _))
        (harmOf misspecState.nul misspecTrueV)
      = expect misspecState.γ (harmOf misspecState.nul misspecTrueV) / (1 / 2) ∧
    Compatible misspecState.proxy := by
  have hest : misspecState.estBaseHarm = 0 := by
    simp [CautionState.estBaseHarm, CautionState.estHarm, CautionState.harm, misspecState, expect,
      harmOf]
  have hbase : expect misspecState.γ (harmOf misspecState.nul misspecTrueV) = 1 / 2 := by
    simp [misspecState, expect_fin2, harmOf, misspecTrueV] <;> norm_num
  have hq : qRuleFloored (1 / 2) 1 misspecState.estBaseHarm = 1 / 2 := by
    rw [hest]; simp [qRuleFloored]
  refine ⟨hest, hbase, hq, ?_, fun a b _ => by simp [CautionState.proxy, misspecState]⟩
  rw [hbase]
  have h1 : above misspecState.γ 1 = 0 := above_last (n := 1) _
  have h0 : above misspecState.γ 0 = 1 / 2 := by
    show above (Distr.uniform : Distr (Fin 2)) 0 = 1 / 2
    simp only [above, sum_filter, Fin.sum_univ_two, uniform_mass_fin, Fin.lt_def]
    norm_num
  simp only [expect_fin2, quantilize_mass]
  rw [misspecState.qmass_top (qRuleFloored_pos (by norm_num) _ _) h1,
    qmass_of_le_above _ (by rw [h0, hq])]
  rw [hq]
  simp [harmOf, misspecTrueV, misspecState]

/-! ## T5 — S5(b) refuted for `δ > 0` inside realizability (Witness B) -/

/-- Witness B: `A = Fin 2` with `a = 0`, `nul = 1`; `Ω = Fin 2` with `ω₁ = 0`, `ω* = 1`;
`P(ω*) = 1/2`; `V ω₁ = (1/2, 1/2)`, `V ω* = (1/2 − δ, 1/2 + δ)` at `δ = 1/4`; uniform base.
The truth is *inside* `Ω` (realizability holds), unlike the source's witness.
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69); caution-adversary.md A5.2 (l. 49)
Kind: D
Fidelity: variant: the source's truth-outside-`Ω` witness moved inside the algebra (finding)
Hyps: n/a (witness) -/
noncomputable def witnessB : CautionState (Fin 2) (Fin 2) where
  V := ![![1 / 2, 1 / 2], ![1 / 4, 3 / 4]]
  nul := 1
  P := twoPt (1 / 2) (by norm_num) (by norm_num)
  target := 1
  γ := Distr.uniform

/-- **S5(b) refuted for `δ > 0` (N+, rule-3 row).** Quoted: "D10's pointwise form implies
`COR(T)`" (`caution.md` S5(b)). Reading: `CoveredOrKnownUncovered δ → R ≤ R̂`. In Witness B at
`δ = 1/4`: both actions are δ-covered (errors `±1/8`), so even the *corrected* predicate holds,
the range `[0, 1]` holds, and yet `R̂ = 1/8 < 1/4 = R` — reckless. Surviving neighbours:
`baseHarm_sub_le_estBaseHarm` (`R − 2δ ≤ R̂`: here `−1/4 ≤ 1/8`) and
`realizedHarm_le_known_cost`.
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69), proof §5 (l. 129); caution-adversary.md A5.2 (l. 49)
Kind: N+
Fidelity: exact (refutation of the unrelaxed claim; witness inside realizability)
Hyps: none -/
theorem witnessB_refutes_COR :
    witnessB.InRange ∧ witnessB.NullCoveredKnownUncovered (1 / 4) ∧
      witnessB.CoveredOrKnownUncovered (1 / 4) ∧ witnessB.Reckless ∧
      witnessB.baseHarm = 1 / 4 ∧ witnessB.estBaseHarm = 1 / 8 := by
  have hcov : ∀ a, witnessB.Covered (1 / 4) a := by
    intro a
    simp only [CautionState.Covered, CautionState.err, CautionState.proxy, witnessB, expect_fin2,
      twoPt_mass]
    fin_cases a <;> simp <;> norm_num [abs_le]
  have hb : witnessB.baseHarm = 1 / 4 := by
    simp only [CautionState.baseHarm, CautionState.trueHarm, CautionState.harm, witnessB,
      expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  have he : witnessB.estBaseHarm = 1 / 8 := by
    simp only [CautionState.estBaseHarm, CautionState.estHarm, CautionState.harm, witnessB,
      expect_fin2, harmOf, uniform_mass_fin, twoPt_mass]
    norm_num
  have hnull : witnessB.NullCoveredKnownUncovered (1 / 4) := ⟨hcov _, fun a _ => Or.inl (hcov a)⟩
  refine ⟨?_, hnull, witnessB.coveredOrKnownUncovered_of_nullCovered hnull, ?_, hb, he⟩
  · intro ω a; fin_cases ω <;> fin_cases a <;> simp [witnessB] <;> norm_num
  · unfold CautionState.Reckless; rw [hb, he]; norm_num

/-- **The refuted claim as a negation:** it is not the case that the pointwise predicate implies
`R ≤ R̂` for every state and tolerance.
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem not_pointwise_implies_COR :
    ¬ ∀ (S : CautionState (Fin 2) (Fin 2)) (δ : ℝ), S.CoveredOrKnownUncovered δ →
      S.baseHarm ≤ S.estBaseHarm := by
  intro h
  obtain ⟨-, -, hp, hr, -, -⟩ := witnessB_refutes_COR
  exact absurd (h witnessB _ hp) (not_le.mpr hr)

/-! ## T5 — S2 needs the null action covered; the printed predicate does not give `COR_δ` -/

/-- The null-uncovered state: `A = Fin 2` with `a = 0`, `nul = 1`; `Ω = Fin 2`, `P = (1/2, 1/2)`,
target `ω* = 0`; `V ω* = (0, 1)`, `V ω' = (0, 2/5)`; uniform base; `δ = 1/20`. Then `a` is
covered (`e(a) = 0`) and `∅` is not (`e(∅) = −3/10`).
Source: [[corr-wf14-2-inventory]] 2-037 / caution-adversary.md A2.2 (l. 31); caution-final.md D10 (l. 55)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def nullUncoveredState : CautionState (Fin 2) (Fin 2) where
  V := ![![0, 1], ![0, 2 / 5]]
  nul := 1
  P := twoPt (1 / 2) (by norm_num) (by norm_num)
  target := 0
  γ := Distr.uniform

/-- **S2 without `∅ ∈ C(δ)` is false (N+):** `a` is `1/20`-covered, `∅` is not, and
`|c(a) − (U(∅) − U(a))⁺| = |1 − 7/10| = 3/10 > 1/10 = 2δ`.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S2 (l. 63); caution-adversary.md A2.2 (l. 31)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem s2_null_uncovered :
    nullUncoveredState.Covered (1 / 20) 0 ∧ ¬ nullUncoveredState.Covered (1 / 20) 1 ∧
      |nullUncoveredState.trueHarm 0 - nullUncoveredState.proxyHarm 0| = 3 / 10 ∧
      ¬ |nullUncoveredState.trueHarm 0 - nullUncoveredState.proxyHarm 0| ≤ 2 * (1 / 20) := by
  have h3 : |nullUncoveredState.trueHarm 0 - nullUncoveredState.proxyHarm 0| = 3 / 10 := by
    simp only [CautionState.trueHarm, CautionState.harm, CautionState.proxyHarm,
      CautionState.proxy, nullUncoveredState, harmOf, expect_fin2, twoPt_mass]
    norm_num [abs_of_pos]
  refine ⟨?_, ?_, h3, by rw [h3]; norm_num⟩
  · simp only [CautionState.Covered, CautionState.err, CautionState.proxy, nullUncoveredState,
      expect_fin2, twoPt_mass]
    norm_num
  · simp only [CautionState.Covered, CautionState.err, CautionState.proxy, nullUncoveredState,
      expect_fin2, twoPt_mass]
    norm_num [abs_le]

/-- **The source's printed predicate does not give `COR_δ` (N+, finding).** In the null-uncovered
state at `δ = 1/20` the printed predicate `CoveredOrKnownUncovered` holds (`a` covered; at `∅` the
known-uncovered disjunct is `0 ≤ 0`), yet `R − 2δ = 2/5 > 7/20 = R̂`. So the source's S5(b) "ratio"
theorem is false as printed and needs `∅ ∈ C(δ)` as an explicit hypothesis
(`NullCoveredKnownUncovered`, under which `baseHarm_sub_le_estBaseHarm` holds).
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69), D10 (l. 55), proof §5 (l. 129)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem printed_predicate_no_CORδ :
    nullUncoveredState.CoveredOrKnownUncovered (1 / 20) ∧
      nullUncoveredState.baseHarm = 1 / 2 ∧ nullUncoveredState.estBaseHarm = 7 / 20 ∧
      nullUncoveredState.estBaseHarm < nullUncoveredState.baseHarm - 2 * (1 / 20) := by
  obtain ⟨hc, -, -, -⟩ := s2_null_uncovered
  have hb : nullUncoveredState.baseHarm = 1 / 2 := by
    simp only [CautionState.baseHarm, CautionState.trueHarm, CautionState.harm,
      nullUncoveredState, expect_fin2, harmOf, uniform_mass_fin]
    norm_num
  have he : nullUncoveredState.estBaseHarm = 7 / 20 := by
    simp only [CautionState.estBaseHarm, CautionState.estHarm, CautionState.harm,
      nullUncoveredState, expect_fin2, harmOf, uniform_mass_fin, twoPt_mass]
    norm_num
  refine ⟨?_, hb, he, by rw [hb, he]; norm_num⟩
  rw [nullUncoveredState.coveredOrKnownUncovered_iff]
  intro a _
  fin_cases a
  · exact Or.inl hc
  · right
    simp only [CautionState.trueHarm, CautionState.harm, CautionState.estHarm, harmOf,
      nullUncoveredState, expect_fin2, twoPt_mass]
    norm_num

/-- **The printed-predicate claim as a negation.**
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem not_printed_predicate_implies_CORδ :
    ¬ ∀ (S : CautionState (Fin 2) (Fin 2)) (δ : ℝ), S.CoveredOrKnownUncovered δ →
      S.baseHarm - 2 * δ ≤ S.estBaseHarm := by
  intro h
  obtain ⟨hp, -, -, hlt⟩ := printed_predicate_no_CORδ
  exact absurd (h nullUncoveredState _ hp) (not_le.mpr hlt)

/-! ## T5 — a mixed witness for the repaired S5(b): one covered, one known-uncovered base action -/

/-- The mixed state: `A = Fin 3` with `a = 0` (covered), `b = 1` (known-uncovered), `∅ = 2`;
`Ω = Fin 2`, `P = (1/2, 1/2)`, target `ω* = 0`; `V ω* = (1/2, 1, 1)`, `V ω′ = (1/2, 0, 1)`;
uniform base. Then `U = (1/2, 1/2, 1)` (natural order compatible), `e = (0, −1/2, 0)`: at
`δ = 1/4`, `a` and `∅` are covered, `b` is not, and `c(b) = 0 ≤ 1/2 = ĉ(b)` (known-uncovered);
`c = (1/2, 0, 0)`, `ĉ = (1/2, 1/2, 0)`, `(U(∅) − U)⁺ = (1/2, 1/2, 0)`, `R = 1/6`, `R̂ = 1/3`.
Source: caution-final.md S5(b) (l. 69), D10 (l. 55); mandate T5 ("a mixed witness"); audit r1 N6
Kind: D
Fidelity: n/a (witness) -/
noncomputable def mixedState : CautionState (Fin 3) (Fin 2) where
  V := ![![1 / 2, 1, 1], ![1 / 2, 0, 1]]
  nul := 2
  P := twoPt (1 / 2) (by norm_num) (by norm_num)
  target := 0
  γ := Distr.uniform

/-- The error, harms, proxy harm and proxy of the mixed state.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mixedState_vals :
    mixedState.err = ![0, -(1 / 2), 0] ∧ mixedState.trueHarm = ![1 / 2, 0, 0] ∧
    mixedState.estHarm = ![1 / 2, 1 / 2, 0] ∧ mixedState.proxyHarm = ![1 / 2, 1 / 2, 0] ∧
    mixedState.proxy = ![1 / 2, 1 / 2, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext a <;>
    simp only [CautionState.err, CautionState.proxy, CautionState.trueHarm, CautionState.estHarm,
      CautionState.harm, CautionState.proxyHarm, harmOf, mixedState, expect_fin2, twoPt_mass] <;>
    fin_cases a <;> simp <;> norm_num

/-- **The repaired S5(b) on a mixed witness (N+).** In `mixedState` at `δ = 1/4`: `∅` and `a` are
covered, `b` is uncovered but known-uncovered (`c(b) = 0 ≤ 1/2 = ĉ(b)`), so the corrected
predicate holds with *both* disjuncts in use; the ratio bound `R − 2δ ≤ R̂` reads
`1/6 − 1/2 ≤ 1/3`; at `η = 1/3` the D8 slice is `q = 1` (the base), `H = 1/6`, the knowingly
accepted cost is `k = 1/6`, and the harm bound `H ≤ k + 2δ + max{η, R̂}` reads
`1/6 ≤ 1/6 + 1/2 + 1/3`; the computable bound (`realizedHarm_le_known_cost_computable`) reads
`1/6 ≤ 1/3 + 1/2 + 1/3`. Every value is in `[0, 1]` and the natural order is proxy-compatible.
Source: caution-final.md S5(b) (l. 69), proof §5 (l. 129); mandate T5; audit r1 N6
Kind: N+
Fidelity: exact (an instance; at `q = 1` the quantilizer is the base, so Lemma 1's slice is not exercised here — `gloss_refuted` and `s12_refuted_d8` do that)
Hyps: none -/
theorem mixed_witness :
    mixedState.InRange ∧ Compatible mixedState.proxy ∧
    mixedState.Covered (1 / 4) 0 ∧ ¬ mixedState.Covered (1 / 4) 1 ∧
    mixedState.trueHarm 1 ≤ mixedState.estHarm 1 ∧
    mixedState.NullCoveredKnownUncovered (1 / 4) ∧
    mixedState.baseHarm = 1 / 6 ∧ mixedState.estBaseHarm = 1 / 3 ∧
    mixedState.baseHarm - 2 * (1 / 4) ≤ mixedState.estBaseHarm ∧
    ∃ (hq : 0 < qRule (1 / 3) mixedState.estBaseHarm) (hq1 : qRule (1 / 3) mixedState.estBaseHarm ≤ 1),
      qRule (1 / 3) mixedState.estBaseHarm = 1 ∧
      mixedState.realizedHarm (quantilize mixedState.γ (qRule (1 / 3) _) hq hq1) = 1 / 6 ∧
      (∑ a ∈ mixedState.coveredSet (1 / 4),
        (quantilize mixedState.γ (qRule (1 / 3) _) hq hq1).mass a * mixedState.proxyHarm a) = 1 / 6 ∧
      expect (quantilize mixedState.γ (qRule (1 / 3) _) hq hq1) mixedState.proxyHarm = 1 / 3 := by
  obtain ⟨herr, hc, hce, hph, hpr⟩ := mixedState_vals
  have hR : mixedState.baseHarm = 1 / 6 := by
    rw [CautionState.baseHarm, expect_fin3, hc]; simp [mixedState]; norm_num
  have hRh : mixedState.estBaseHarm = 1 / 3 := by
    rw [CautionState.estBaseHarm, expect_fin3, hce]; simp [mixedState]; norm_num
  have hqval : qRule (1 / 3) mixedState.estBaseHarm = 1 := by
    unfold qRule; rw [hRh]; norm_num
  have hq : 0 < qRule (1 / 3) mixedState.estBaseHarm := by rw [hqval]; norm_num
  have hq1 : qRule (1 / 3) mixedState.estBaseHarm ≤ 1 := qRule_le_one _ _
  have hQ : quantilize mixedState.γ (qRule (1 / 3) _) hq hq1 = Distr.uniform := by
    simp only [hqval]; exact taylor3_mimic
  have h0 : mixedState.Covered (1 / 4) 0 := by norm_num [CautionState.Covered, herr, abs_le]
  have hnul : mixedState.Covered (1 / 4) mixedState.nul := by
    show mixedState.Covered (1 / 4) 2
    norm_num [CautionState.Covered, herr, abs_le, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  have hb : ¬ mixedState.Covered (1 / 4) 1 := by norm_num [CautionState.Covered, herr, abs_le]
  have hkb : mixedState.trueHarm 1 ≤ mixedState.estHarm 1 := by rw [hc, hce]; norm_num
  refine ⟨?_, ?_, h0, hb, hkb, ⟨hnul, fun a _ => ?_⟩, hR, hRh, by rw [hR, hRh]; norm_num,
    hq, hq1, hqval, ?_, ?_, ?_⟩
  · intro ω a; fin_cases ω <;> fin_cases a <;> simp [mixedState] <;> norm_num
  · intro a b hab
    rw [hpr]
    fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def] <;> norm_num
  · fin_cases a
    · exact Or.inl h0
    · exact Or.inr hkb
    · exact Or.inl hnul
  · rw [CautionState.realizedHarm, expect_fin3, hQ, hc]; simp; norm_num
  · simp only [CautionState.coveredSet, sum_filter, Fin.sum_univ_three, hQ, herr, hph,
      uniform_mass_fin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    norm_num [abs_le]
  · rw [expect_fin3, hQ, hph]; simp; norm_num

end Cleanroom.Corrigibility.CorrCautionPower
