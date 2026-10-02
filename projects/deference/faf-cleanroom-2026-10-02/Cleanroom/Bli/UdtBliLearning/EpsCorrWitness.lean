import Cleanroom.Bli.UdtBliLearning.EpsCorr
import Cleanroom.Bli.UdtBliCore.WitnessTieFree

/-!
# `udt-bli-learning` · EpsCorrWitness: witnesses for the asymptotic ε-correlation headlines, and
the refutation of the exact clause (T9)

**Scope: core's two-table carrier** (`twoTables = {Ask, Rec}` as `T1`, `T2`; uniform base law
`tfMass` on `(state, pp·T1, pp·T2)`; independent fair points `tfPP`; realized tables `twoState`),
with a two-parameter utility. The single-coin model cannot carry these witnesses: on `scPrior p`
every cross branch `Ask_{k'}`, `k' ≠ j`, reads `Ask_j`'s point through the summed utility, so
`CorrBounded _ Ask_j ε` needs `ε ≥ c γ_j` at both states for `K ≥ 2` (report T9).

**The family** `vPrior g b` (`D`): `vU g b ω = [state = T1] · (if pp·T1 then 0 else g) +
[state = T2] · (if pp·T1 then b else 0)` — `T1`'s own branch prefers `refuse` by `g`, and `T2`'s
branch pays `b` when the *other* table's point is `pay`: a cross-branch correlation of size `b`.
Computed (`v_*`): branch probabilities all `1/2`; `condEU T2 T1 pay = b`, `refuse = 0`;
`condEU T1 T2 · = g/2`; `homeEU T1 = (0, g)`; `homeEU T2 · = b/2`; `EU T1 = (b/2, g/2)`. So
`CorrBounded (vPrior g b) T b` at both tables for `b ≥ 0`, the one-step choice at `T1` is `pay`
iff `g ≤ b`, and the updateful choice is uniquely `refuse` for `g > 0`.

* **N+ for `eventually_eps_updateful` / `eventually_updateful_of_gap`** (`wPrior n := vPrior 1
  (10/(n+1))`, `ε_n = 10/(n+1) → 0`, `|U| ≤ 10`, `ρ = 1/2`, gap `1`): the sequence is not constant,
  `ε_n ≠ 0`, and the asymptotics are exercised — at `T1` the one-step choice is `pay` for `n ≤ 9`
  against the updateful `refuse` (loss exactly `1`, inside the slack `δ(ε_n) = 1020/(n+1)` as it
  must be) and uniquely `refuse` for `n ≥ 10` (`w_oneStep_flips`); the conclusion of
  `eventually_eps_updateful` is false at `n = 0`, `η = 1/2` (`w_not_early`), so the `∃ N` is
  load-bearing. (Adopted from audit r2 adversarial probe `EpsCorrWitnessPlus`.)
* **N−** (`tfPrior`, constant, `ε ≡ 0`): core's tie-free prior has `CorrBounded tfPrior T 0` at
  both tables, so the constant sequence inhabits both packages (`tf_inhabits_*`). (Adopted from
  probe `EpsCorrWitnessTieFree`.)
* **Refutation of the exact clause** (`not_exactAsymptoticClause`): `xPrior n := vPrior
  (1/(2(n+1))) (1/(n+1))` — the home-value gap `g_n = 1/(2(n+1))` shrinks faster than the
  correlation `b_n = 1/(n+1) → 0`, so at *every* `n` the one-step choice `pay` at `T1` is not an
  updateful choice (`x_pay_oneStep_not_updateful`), while the full hypothesis package of
  `ExactAsymptoticClause witIndex 1 twoTables Bool 2` holds (`ε_n = 1/(n+1)`, `M = 1`,
  `ρ = 1/2`). The clause's conclusion (`∃ N, ∀ n ≥ N, one-step ⟹ updateful`) is therefore false.
  On the same family the *approximate* conclusion holds (`x_value_eventually_optimal`): the loss
  `g_n → 0`. So "performance … eventually optimal" (bli-soto-b-046) is true as **value** and false
  as **choice**, on one family — the two readings separate (F14).

Sources: bli-soto-b-046 (Notion ll. 360–368); mandate T9; audit r2 adversarial N2 (the two
probes), audit r2 fidelity N4/N9 (the `K = 1` route not taken; the counterexample family
"plausibly constructible on a two-table prior" — built here).
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.EpsCorrWitness

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.TieFree Finset

/-! ## The two-parameter family -/

/-- **The two-parameter utility**: `T1`'s branch prefers `refuse` by `g`; `T2`'s branch pays `b`
iff `T1`'s point is `pay`.
Source: none: infrastructure (audit r2 adversarial probe `EpsCorrWitnessPlus`, generalized)
Kind: D
Fidelity: n/a -/
def vU (g b : ℚ) : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2.1 then 0 else g) else (if ω.2.1 then b else 0)

/-- **The two-parameter prior**: `tfPrior`'s base law, state map and points with the utility
`vU g b`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def vPrior (g b : ℚ) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) tfMass (fun _ => by norm_num [tfMass])
    (by norm_num [tfMass, Finset.sum_const, Finset.card_univ])
    (fun ω => twoState ω.1) two_zeroOne tfPP (vU g b)

variable (g b : ℚ)

/-- The point masses of `vPrior g b` are `tfPrior`'s (same base law, state map and points).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_ppMass (T : ↥twoTables) (a : Bool) : (vPrior g b).ppMass T a = 1 / 2 :=
  ppMass_eq T a

/-- The joint masses of `vPrior g b` are `tfPrior`'s.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_jointMass (T' T : ↥twoTables) (a : Bool) : (vPrior g b).jointMass T' T a = 1 / 4 :=
  jointMass_eq T' T a

/-- Every branch probability of `vPrior g b` is `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_branchProb (T' T : ↥twoTables) (a : Bool) : (vPrior g b).branchProb T' T a = 1 / 2 := by
  unfold FiniteBLIPrior.branchProb
  rw [v_jointMass, v_ppMass]
  norm_num

/-- `T2`'s value given `T1`'s point: `b` for `pay`, `0` for `refuse`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_condEU_T2_T1 :
    (vPrior g b).condEU T2 T1 true = b ∧ (vPrior g b).condEU T2 T1 false = 0 := by
  constructor <;>
  · unfold FiniteBLIPrior.condEU vPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, vU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    all_goals ring

/-- `T1`'s value given `T2`'s point: `g/2` either way.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_condEU_T1_T2 (a : Bool) : (vPrior g b).condEU T1 T2 a = g / 2 := by
  cases a <;>
  · unfold FiniteBLIPrior.condEU vPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, vU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    all_goals ring

/-- Home values at `T1`: `pay ↦ 0`, `refuse ↦ g`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_homeEU_T1 : (vPrior g b).homeEU T1 true = 0 ∧ (vPrior g b).homeEU T1 false = g := by
  constructor <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU vPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, vU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    all_goals ring

/-- Home values at `T2`: `b/2` either way (a tie: `T2`'s branch does not read its own point).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_homeEU_T2 (a : Bool) : (vPrior g b).homeEU T2 a = b / 2 := by
  cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU vPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, vU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    all_goals ring

/-- One-step values at `T1`: `pay ↦ b/2`, `refuse ↦ g/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_EU_T1 : (vPrior g b).EU T1 true = b / 2 ∧ (vPrior g b).EU T1 false = g / 2 := by
  constructor <;>
  · unfold FiniteBLIPrior.EU vPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, vU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    all_goals ring

/-- **`CorrBounded (vPrior g b) T b` at both tables** for `b ≥ 0`: branch probabilities are
action-blind, the cross value at `T2` given `T1`'s point moves by exactly `b`, the cross value at
`T1` given `T2`'s point not at all.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_corrBounded (hb : 0 ≤ b) (T : ↥twoTables) : CorrBounded (vPrior g b) T b := by
  refine ⟨fun T' c d => ?_, fun T' c d hne _ _ => ?_⟩
  · rw [v_branchProb, v_branchProb]; simpa using hb
  · rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl
    · exact absurd rfl hne
    · obtain ⟨h1, h0⟩ := v_condEU_T2_T1 g b
      cases c <;> cases d <;> simp only [h1, h0]
      · simpa using hb
      · rw [zero_sub, abs_neg, abs_of_nonneg hb]
      · rw [sub_zero, abs_of_nonneg hb]
      · simpa using hb
    · rw [v_condEU_T1_T2, v_condEU_T1_T2]; simpa using hb
    · exact absurd rfl hne

/-- `|vU g b| ≤ M` when `|g| ≤ M` and `|b| ≤ M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_U_bound (M : ℚ) (hg : |g| ≤ M) (hb : |b| ≤ M) (ω : Fin 2 × Bool × Bool) :
    |(vPrior g b).U ω| ≤ M := by
  show |vU g b ω| ≤ M
  have h0 : |(0 : ℚ)| ≤ M := by rw [abs_zero]; exact (abs_nonneg g).trans hg
  unfold vU
  split_ifs <;> assumption

/-- The one-step choice at `T1` is `pay` iff `g ≤ b`; it is `refuse` iff `b ≤ g`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_oneStep_T1_iff :
    ((vPrior g b).IsOneStepChoice T1 true ↔ g ≤ b) ∧
      ((vPrior g b).IsOneStepChoice T1 false ↔ b ≤ g) := by
  obtain ⟨e1, e0⟩ := v_EU_T1 g b
  constructor
  · constructor
    · intro h; have := h false; rw [e0, e1] at this; linarith
    · intro h c; cases c
      · rw [e0, e1]; linarith
      · exact le_rfl
  · constructor
    · intro h; have := h true; rw [e0, e1] at this; linarith
    · intro h c; cases c
      · exact le_rfl
      · rw [e0, e1]; linarith

/-- The updateful choice at `T1`: `refuse` is one for `g ≥ 0`; `pay` is not one for `g > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_updateful_T1 :
    (0 ≤ g → (vPrior g b).IsUpdatefulChoice T1 false) ∧
      (0 < g → ¬ (vPrior g b).IsUpdatefulChoice T1 true) := by
  obtain ⟨h0, h1⟩ := v_homeEU_T1 g b
  constructor
  · intro hg c; cases c
    · exact le_rfl
    · rw [h0, h1]; exact hg
  · intro hg h; have := h false; rw [h0, h1] at this; linarith

/-- Home values at each table are equal or at least `g` apart.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma v_gap (hg : 0 ≤ g) (T : ↥twoTables) (a c : Bool) :
    (vPrior g b).homeEU T c = (vPrior g b).homeEU T a ∨
      g ≤ |(vPrior g b).homeEU T c - (vPrior g b).homeEU T a| := by
  rcases eq_T1_or_T2 T with rfl | rfl
  · obtain ⟨h0, h1⟩ := v_homeEU_T1 g b
    cases a <;> cases c <;> simp [h0, h1, abs_of_nonneg hg]
  · left; rw [v_homeEU_T2, v_homeEU_T2]

/-- `c/(n+1) → 0` (elementary convergence; the bound is one-sided, so no sign of `c` is needed).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lim_inv (c : ℚ) :
    ∀ η : ℚ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c / ((n : ℚ) + 1) ≤ η := by
  intro η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (c / η)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  have h : c / η < (n : ℚ) + 1 := by linarith
  rw [div_lt_iff₀ hη] at h
  linarith

/-! ## N+: a non-constant family on which the one-step verdict flips -/

/-- **The N+ family**: `vPrior 1 (10/(n+1))` — gap `1` at `T1`, cross-branch correlation
`10/(n+1) → 0`.
Source: mandate T9 (N+ for the asymptotic clause); audit r2 adversarial N2 (probe
`EpsCorrWitnessPlus`)
Kind: D
Fidelity: n/a -/
def wPrior (n : ℕ) : FiniteBLIPrior witIndex 1 twoTables Bool := vPrior 1 (10 / ((n : ℚ) + 1))

/-- **The content of the N+**: at `T1` the one-step choice is `pay` for `n ≤ 9` (tie at `n = 9`)
while the updateful choice is uniquely `refuse` (loss `1` by the home values); for `n ≥ 10` the
one-step choice is uniquely `refuse`, agreeing with the updateful one. The sequence is not
constant, `ε_n` is not `0`, and the asymptotic conclusion is false early and true late.
Source: mandate T9 (N+); audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w_oneStep_flips (n : ℕ) :
    (n ≤ 9 → (wPrior n).IsOneStepChoice T1 true ∧ ¬ (wPrior n).IsUpdatefulChoice T1 true ∧
      (wPrior n).homeEU T1 false - (wPrior n).homeEU T1 true = 1) ∧
    (10 ≤ n → (wPrior n).IsOneStepChoice T1 false ∧ ¬ (wPrior n).IsOneStepChoice T1 true ∧
      (wPrior n).IsUpdatefulChoice T1 false) := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  obtain ⟨h0, h1⟩ := v_homeEU_T1 1 (10 / ((n : ℚ) + 1))
  constructor
  · intro h9
    have hn9 : (n : ℚ) + 1 ≤ 10 := by
      have : (n : ℚ) ≤ 9 := by exact_mod_cast h9
      linarith
    have hge : (1 : ℚ) ≤ 10 / ((n : ℚ) + 1) := by
      rw [le_div_iff₀ hn]; linarith
    refine ⟨(v_oneStep_T1_iff _ _).1.mpr hge, (v_updateful_T1 _ _).2 one_pos, ?_⟩
    show (vPrior 1 _).homeEU T1 false - (vPrior 1 _).homeEU T1 true = 1
    rw [h0, h1]; norm_num
  · intro h10
    have hn10 : (10 : ℚ) ≤ (n : ℚ) := by exact_mod_cast h10
    have hlt : 10 / ((n : ℚ) + 1) < 1 := by
      rw [div_lt_iff₀ hn]; linarith
    exact ⟨(v_oneStep_T1_iff _ _).2.mpr hlt.le,
      fun h => absurd ((v_oneStep_T1_iff _ _).1.mp h) (not_le.mpr hlt),
      (v_updateful_T1 _ _).1 zero_le_one⟩

/-- **N+ for `eventually_eps_updateful`**: the package is inhabited by `wPrior`, `twoState`,
`ε_n = 10/(n+1)`, `M = 10`, `ρ = 1/2`, and the headline fires.
Source: mandate T9 (N+); audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w_inhabits_eventually_eps_updateful :
    ∀ η : ℚ, 0 < η → ∃ N, ∀ n, N ≤ n → ∀ (k : Fin 2) (a : Bool),
      (wPrior n).IsOneStepChoice (twoState k) a →
      ∀ c, (wPrior n).homeEU (twoState k) c - (wPrior n).homeEU (twoState k) a ≤ η :=
  eventually_eps_updateful wPrior twoState (fun n => 10 / ((n : ℚ) + 1)) 10 (1 / 2) (by norm_num)
    (by norm_num) (fun n => by positivity) (lim_inv 10)
    (fun n k c => by show 0 < (vPrior _ _).ppMass _ _; rw [v_ppMass]; norm_num)
    (fun n k => v_corrBounded _ _ (by positivity) _)
    (fun n ω => v_U_bound _ _ 10 (by norm_num) (by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]) ω)
    (fun n k a _ => by show (1 : ℚ) / 2 ≤ (vPrior _ _).branchProb _ _ _; rw [v_branchProb])

/-- **N+ for `eventually_updateful_of_gap`**: the same data with the gap `g = 1`; exact eventual
updateful optimality at both realized tables.
Source: mandate T9 (N+); audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w_inhabits_eventually_updateful_of_gap :
    ∃ N, ∀ n, N ≤ n → ∀ (k : Fin 2) (a : Bool),
      (wPrior n).IsOneStepChoice (twoState k) a → (wPrior n).IsUpdatefulChoice (twoState k) a :=
  eventually_updateful_of_gap wPrior twoState (fun n => 10 / ((n : ℚ) + 1)) 10 (1 / 2) 1
    (by norm_num) (by norm_num) (by norm_num) (fun n => by positivity) (lim_inv 10)
    (fun n k c => by show 0 < (vPrior _ _).ppMass _ _; rw [v_ppMass]; norm_num)
    (fun n k => v_corrBounded _ _ (by positivity) _)
    (fun n ω => v_U_bound _ _ 10 (by norm_num) (by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]) ω)
    (fun n k a _ => by show (1 : ℚ) / 2 ≤ (vPrior _ _).branchProb _ _ _; rw [v_branchProb])
    (fun n k a c => v_gap _ _ zero_le_one _ a c)

/-- **The conclusion of `eventually_eps_updateful` is false early**: at `n = 0`, `η = 1/2`, the
one-step choice `pay` at `T1` loses `1 > 1/2` by the home values — the `∃ N` is load-bearing.
Source: mandate T9 (N+); audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w_not_early :
    ¬ (∀ (a : Bool), (wPrior 0).IsOneStepChoice T1 a →
      ∀ c, (wPrior 0).homeEU T1 c - (wPrior 0).homeEU T1 a ≤ 1 / 2) := by
  intro h
  obtain ⟨hone, _, hgap⟩ := (w_oneStep_flips 0).1 (by norm_num)
  have := h true hone false
  linarith

/-! ## N−: core's tie-free prior, constant, `ε ≡ 0` -/

/-- Every branch probability of the tie-free prior is `1/2` (as in `reflective`).
Source: none: infrastructure (audit r2 adversarial probe `EpsCorrWitnessTieFree`)
Kind: L
Fidelity: n/a -/
lemma tf_branchProb (T' T : ↥twoTables) (a : Bool) : tfPrior.branchProb T' T a = 1 / 2 := by
  unfold FiniteBLIPrior.branchProb
  rw [jointMass_eq, ppMass_eq]
  norm_num

/-- `CorrBounded tfPrior T 0` at both tables: no belief in acausal correlations at all.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tf_corrBounded (T : ↥twoTables) : CorrBounded tfPrior T 0 := by
  refine ⟨fun T' c d => ?_, fun T' c d hne _ _ => ?_⟩
  · rw [tf_branchProb, tf_branchProb]; simp
  · rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl
    · exact absurd rfl hne
    · rw [(condEU_cross c).1, (condEU_cross d).1]; simp
    · rw [(condEU_cross c).2, (condEU_cross d).2]; simp
    · exact absurd rfl hne

/-- `|tfU| ≤ 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tf_U_bound (ω : Fin 2 × Bool × Bool) : |tfPrior.U ω| ≤ 4 := by
  show |tfU ω| ≤ 4
  unfold tfU
  split_ifs <;> norm_num

/-- Home values of the tie-free prior at each table are either equal or at least `1` apart.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tf_gap (T : ↥twoTables) (a c : Bool) :
    tfPrior.homeEU T c = tfPrior.homeEU T a ∨ 1 ≤ |tfPrior.homeEU T c - tfPrior.homeEU T a| := by
  rw [homeEU_eq, homeEU_eq]
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;> cases c <;>
    simp [Ne.symm mAsk_ne_mRec] <;> norm_num

/-- **N− for `eventually_eps_updateful`**: the constant sequence `tfPrior`, `ε ≡ 0`, `M = 4`,
`ρ = 1/2`, realized tables `twoState`, inhabits the package and the headline fires. Degenerate on
purpose (constant, `ε ≡ 0`): satisfiability only; the N+ is `w_inhabits_eventually_eps_updateful`.
Source: mandate T9; audit r2 adversarial N2 (probe `EpsCorrWitnessTieFree`)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem tf_inhabits_eventually_eps_updateful :
    ∀ η : ℚ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (k : Fin 2) (a : Bool),
      tfPrior.IsOneStepChoice (twoState k) a →
      ∀ c, tfPrior.homeEU (twoState k) c - tfPrior.homeEU (twoState k) a ≤ η :=
  eventually_eps_updateful (fun _ => tfPrior) twoState (fun _ => 0) 4 (1 / 2) (by norm_num)
    (by norm_num) (fun _ => le_refl (0 : ℚ)) (fun (η : ℚ) (hη : 0 < η) => ⟨0, fun _ _ => hη.le⟩)
    (fun _ k c => by rw [ppMass_eq]; norm_num)
    (fun _ k => tf_corrBounded _)
    (fun _ ω => tf_U_bound ω)
    (fun _ k a _ => by rw [tf_branchProb])

/-- **N− for `eventually_updateful_of_gap`**: the same data with the gap `g = 1`.
Source: mandate T9; audit r2 adversarial N2
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem tf_inhabits_eventually_updateful_of_gap :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (k : Fin 2) (a : Bool),
      tfPrior.IsOneStepChoice (twoState k) a → tfPrior.IsUpdatefulChoice (twoState k) a :=
  eventually_updateful_of_gap (fun _ => tfPrior) twoState (fun _ => 0) 4 (1 / 2) 1 (by norm_num)
    (by norm_num) (by norm_num) (fun _ => le_refl (0 : ℚ))
    (fun (η : ℚ) (hη : 0 < η) => ⟨0, fun _ _ => hη.le⟩)
    (fun _ k c => by rw [ppMass_eq]; norm_num)
    (fun _ k => tf_corrBounded _)
    (fun _ ω => tf_U_bound ω)
    (fun _ k a _ => by rw [tf_branchProb])
    (fun _ k a c => tf_gap _ a c)

/-! ## The exact clause is false: a gap shrinking faster than the correlation -/

/-- **The refuting family**: `vPrior (1/(2(n+1))) (1/(n+1))` — the home-value gap at `T1` is half
the cross-branch correlation at every `n`, and both tend to `0`.
Source: mandate T9 (the exact asymptotic clause); audit r2 fidelity N9 ("plausibly
constructible on a two-table prior")
Kind: D
Fidelity: n/a -/
def xPrior (n : ℕ) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  vPrior (1 / (2 * ((n : ℚ) + 1))) (1 / ((n : ℚ) + 1))

/-- **At every `n`, `pay` is a one-step choice at `T1` and not an updateful one**: the correlation
`1/(n+1)` outweighs the gap `1/(2(n+1))` in the one-step value (`EU T1 pay = 1/(2(n+1)) >
1/(4(n+1)) = EU T1 refuse`), while the home values prefer `refuse` by `1/(2(n+1)) > 0`.
Source: mandate T9; audit r2 fidelity N9
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem x_pay_oneStep_not_updateful (n : ℕ) :
    (xPrior n).IsOneStepChoice T1 true ∧ ¬ (xPrior n).IsUpdatefulChoice T1 true := by
  have hn : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  refine ⟨(v_oneStep_T1_iff _ _).1.mpr ?_, (v_updateful_T1 _ _).2 (by positivity)⟩
  rw [div_le_div_iff₀ (by positivity) hn]
  linarith

/-- **The hypothesis package of `ExactAsymptoticClause` holds on the refuting family**: `ε_n =
1/(n+1) → 0`, `M = 1`, `ρ = 1/2`, positive points, `CorrBounded` at both realized tables.
Source: mandate T9; audit r2 fidelity N9
Kind: L
Fidelity: n/a -/
theorem x_package :
    (∀ n : ℕ, (0 : ℚ) ≤ 1 / ((n : ℚ) + 1)) ∧
    (∀ η : ℚ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / ((n : ℚ) + 1) ≤ η) ∧
    (∀ n (k : Fin 2) c, 0 < (xPrior n).ppMass (twoState k) c) ∧
    (∀ n (k : Fin 2), CorrBounded (xPrior n) (twoState k) (1 / ((n : ℚ) + 1))) ∧
    (∀ n ω, |(xPrior n).U ω| ≤ 1) ∧
    (∀ n (k : Fin 2) a, (xPrior n).IsOneStepChoice (twoState k) a →
      (1 : ℚ) / 2 ≤ (xPrior n).branchProb (twoState k) (twoState k) a) := by
  refine ⟨fun n => by positivity, lim_inv 1, fun n k c => ?_, fun n k => ?_, fun n ω => ?_,
    fun n k a _ => ?_⟩
  · show 0 < (vPrior _ _).ppMass _ _; rw [v_ppMass]; norm_num
  · exact v_corrBounded _ _ (by positivity) _
  · have hn : (1 : ℚ) ≤ (n : ℚ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
    have hg0 : (0 : ℚ) ≤ 1 / (2 * ((n : ℚ) + 1)) := by positivity
    have hb0 : (0 : ℚ) ≤ 1 / ((n : ℚ) + 1) := by positivity
    have h2 : (0 : ℚ) < 2 * ((n : ℚ) + 1) := by positivity
    have h1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    refine v_U_bound (1 / (2 * ((n : ℚ) + 1))) (1 / ((n : ℚ) + 1)) 1 ?_ ?_ ω
    · rw [abs_of_nonneg hg0, div_le_one h2]; linarith
    · rw [abs_of_nonneg hb0, div_le_one h1]; exact hn
  · show (1 : ℚ) / 2 ≤ (vPrior _ _).branchProb _ _ _; rw [v_branchProb]

/-- **The exact asymptotic clause is false** (refutation of the former OPEN statement
`eventually_updateful_exact`): on core's two-table carrier with `K = 2` there is a belief-state
sequence satisfying every hypothesis of `ExactAsymptoticClause` — `ε_n = 1/(n+1) → 0`, `|U| ≤ 1`,
`ρ = 1/2`, positive points, `CorrBounded` at both realized tables — whose one-step choice `pay` at
the realized table `T1` is not an updateful choice at *any* `n`. The slack `δ(ε_n) → 0` bounds the
loss (here `1/(2(n+1))`), not the choice.
Source: bli-soto-b-046 ("the performance of UDT will eventually be optimal in that environment",
read as *choice*); mandate T9 (the asymptotic clause, exact form — the open list's one entry);
audit r2 fidelity N9
Kind: P (refutation)
Fidelity: exact (the open statement's own hypotheses and conclusion, at one carrier)
Hyps: (a) none -/
theorem not_exactAsymptoticClause : ¬ ExactAsymptoticClause witIndex 1 twoTables Bool 2 := by
  intro h
  obtain ⟨_, hlim, hpol, hcorr, hU, hρa⟩ := x_package
  obtain ⟨N, hN⟩ := h xPrior twoState (fun n => 1 / ((n : ℚ) + 1)) 1 (1 / 2) (by norm_num)
    (by norm_num) (fun n => by positivity) hlim hpol hcorr hU hρa
  obtain ⟨hone, hnot⟩ := x_pay_oneStep_not_updateful N
  exact hnot (hN N le_rfl 0 true hone)

/-- **On the refuting family the value reading holds**: for every `η > 0`, eventually every
one-step choice at every realized table is `η`-updateful-optimal (`eventually_eps_updateful`
fires), although the choice is never updateful-optimal at `T1` (`x_pay_oneStep_not_updateful`).
"Eventually optimal" is true as value and false as choice, on one family: the two readings of
bli-soto-b-046 separate.
Source: bli-soto-b-046; mandate T9; F14
Kind: C (`eventually_eps_updateful`, `x_package`, `x_pay_oneStep_not_updateful`)
Fidelity: exact
Hyps: (a) none -/
theorem x_value_eventually_optimal_choice_never :
    (∀ η : ℚ, 0 < η → ∃ N, ∀ n, N ≤ n → ∀ (k : Fin 2) (a : Bool),
      (xPrior n).IsOneStepChoice (twoState k) a →
      ∀ c, (xPrior n).homeEU (twoState k) c - (xPrior n).homeEU (twoState k) a ≤ η) ∧
    (∀ n, (xPrior n).IsOneStepChoice T1 true ∧ ¬ (xPrior n).IsUpdatefulChoice T1 true) := by
  obtain ⟨hε0, hlim, hpol, hcorr, hU, hρa⟩ := x_package
  exact ⟨eventually_eps_updateful xPrior twoState (fun n => 1 / ((n : ℚ) + 1)) 1 (1 / 2)
    (by norm_num) (by norm_num) hε0 hlim hpol hcorr hU hρa, x_pay_oneStep_not_updateful⟩

end Cleanroom.Bli.UdtBliLearning.EpsCorrWitness
