import Cleanroom.Corrigibility.CorrTrajectory.Process
import Cleanroom.Corrigibility.CorrJointProcess.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases

/-!
# `corr-trajectory` — `Corruption`: Statement 6, the value posterior under corruption (T5)

The A7 joint law of `invariant-final.md` Statement 6 as a FAF `Distr` on
`(C, wrong, bits) : Bool × Bool × (Fin n → Bool)`, built from the stated likelihoods — under
corruption `C` the proposal is wrong and every self-check bit looks right; under `¬C` the proposal is
wrong with prior `1/2` and a bit looks right with probability `1` if right, `1/2` if wrong (fakes
indistinguishable, **(IF)**). The posterior `P(wrong ∣ all n bits right)` is **derived** as a ratio of
masses with a positive denominator (`posterior_eq_epsHatA7`), never a parameter:

`epsHatA7 γ n = (γ + (1−γ)·2^{−(n+1)}) / (γ + (1−γ)·2^{−(n+1)} + (1−γ)/2)`.

(a) for `0 < γ < 1` it is strictly decreasing to the floor `γ/(γ + (1−γ)/2) > γ` (`2/101` at
`γ = 1/100`); (b) at `γ = 0` it is `corr-joint-process`'s `floorPosterior (1/2) (1/2)` and tends
to `0`; (c) compliance at every round reduces to the floor satisfying the odds inequality
(monotonicity); (d) the dogmatic agent on the script's hard-coded schedule `eh_t = 2^{−t}` (**not**
the Bayes posterior, C5) fails `Î₁` from the least index `t₀ = 9` and incurs linear harm; (e) an
imposed floor restores `Î₁`; (f) the residue: fixed-rate undetectable corruption gives per-round
expected harm `≥ γ(1−β)h` under every rule (Layer F).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect
open Filter Topology

namespace Corruption

/-- All `n` bits look right. Source: invariant-final.md Statement 6 (A7). Kind: D. Fidelity: exact -/
def allTrue (n : ℕ) : Fin n → Bool := fun _ => true

/-- `sum_ite_allTrue` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_ite_allTrue (n : ℕ) (x : ℝ) :
    ∑ b : Fin n → Bool, (if b = allTrue n then x else 0) = x := by
  rw [Finset.sum_ite_eq' univ (allTrue n) (fun _ => x)]
  simp

/-- `sum_const_bits` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_const_bits (n : ℕ) (x : ℝ) : ∑ _b : Fin n → Bool, x = (2 : ℝ) ^ n * x := by
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **The A7 joint law's mass** on `(C, wrong, bits)` from the stated likelihoods.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6 (joint law), counterexamples.py A7
Kind: D
Fidelity: exact -/
noncomputable def a7Mass (γ : ℝ) (n : ℕ) : Bool × Bool × (Fin n → Bool) → ℝ
  | (true, true, b) => if b = allTrue n then γ else 0
  | (true, false, _) => 0
  | (false, true, _) => (1 - γ) / 2 * (1 / 2 : ℝ) ^ n
  | (false, false, b) => if b = allTrue n then (1 - γ) / 2 else 0

/-- **The A7 joint law** as a FAF `Distr`.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6, counterexamples.py A7
Kind: D
Fidelity: exact -/
noncomputable def a7 (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : Distr (Bool × Bool × (Fin n → Bool)) where
  mass := a7Mass γ n
  nonneg ω := by
    rcases ω with ⟨c, w, b⟩
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    cases c <;> cases w
    · show 0 ≤ (if b = allTrue n then (1 - γ) / 2 else 0); split_ifs <;> linarith [hγ.2]
    · show 0 ≤ (1 - γ) / 2 * (1 / 2 : ℝ) ^ n; nlinarith [hγ.2]
    · show 0 ≤ (0 : ℝ); exact le_rfl
    · show 0 ≤ (if b = allTrue n then γ else 0); split_ifs <;> linarith [hγ.1]
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, a7Mass]
    rw [sum_ite_allTrue, sum_ite_allTrue]
    simp only [sum_const_bits, mul_zero]
    have : (2 : ℝ) ^ n * ((1 - γ) / 2 * (1 / 2 : ℝ) ^ n) = (1 - γ) / 2 := by
      rw [← mul_assoc, mul_comm ((2 : ℝ) ^ n), mul_assoc, ← mul_pow]
      norm_num
    linarith

/-- The event "wrong and all bits look right". Source: Statement 6 (A7). Kind: D. Fidelity: exact -/
def wrongAllRight (n : ℕ) : Finset (Bool × Bool × (Fin n → Bool)) :=
  univ.filter fun ω => ω.2.1 = true ∧ ω.2.2 = allTrue n

/-- The event "all bits look right". Source: Statement 6 (A7). Kind: D. Fidelity: exact -/
def allRight (n : ℕ) : Finset (Bool × Bool × (Fin n → Bool)) := univ.filter fun ω => ω.2.2 = allTrue n

/-- `a7_mass` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma a7_mass (γ : ℝ) (hγ) (n : ℕ) : (a7 γ hγ n).mass = a7Mass γ n := rfl

/-- Expectations under the A7 law: three atoms and the `(¬C, wrong)` bit-sum.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_a7 (γ : ℝ) (hγ) (n : ℕ) (f : Bool × Bool × (Fin n → Bool) → ℝ) :
    expect (a7 γ hγ n) f = γ * f (true, true, allTrue n) + (1 - γ) / 2 * f (false, false, allTrue n) +
      (1 - γ) / 2 * (1 / 2 : ℝ) ^ n * ∑ b, f (false, true, b) := by
  simp only [expect, Fintype.sum_prod_type, Fintype.sum_bool, a7_mass, a7Mass, ite_mul, zero_mul,
    sum_const_zero, Finset.sum_ite_eq', mem_univ, if_true, ← Finset.mul_sum]
  ring

/-- `probOf_wrongAllRight` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_wrongAllRight (γ : ℝ) (hγ) (n : ℕ) :
    probOf (a7 γ hγ n) (wrongAllRight n) = γ + (1 - γ) / 2 * (1 / 2 : ℝ) ^ n := by
  rw [probOf_eq_expect_ind, expect_a7]
  have e1 : ind (wrongAllRight n) (true, true, allTrue n) = 1 := ind_of_mem (by simp [wrongAllRight])
  have e2 : ind (wrongAllRight n) (false, false, allTrue n) = 0 := ind_of_not_mem (by simp [wrongAllRight])
  have e3 : ∑ b, ind (wrongAllRight n) (false, true, b) = 1 := by
    have : ∀ b, ind (wrongAllRight n) (false, true, b) = if b = allTrue n then 1 else 0 := by
      intro b; unfold ind wrongAllRight; simp
    simp only [this]
    exact sum_ite_allTrue n 1
  rw [e1, e2, e3]; ring

/-- `probOf_allRight` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma probOf_allRight (γ : ℝ) (hγ) (n : ℕ) :
    probOf (a7 γ hγ n) (allRight n) = γ + (1 - γ) / 2 * (1 / 2 : ℝ) ^ n + (1 - γ) / 2 := by
  rw [probOf_eq_expect_ind, expect_a7]
  have e1 : ind (allRight n) (true, true, allTrue n) = 1 := ind_of_mem (by simp [allRight])
  have e2 : ind (allRight n) (false, false, allTrue n) = 1 := ind_of_mem (by simp [allRight])
  have e3 : ∑ b, ind (allRight n) (false, true, b) = 1 := by
    have : ∀ b, ind (allRight n) (false, true, b) = if b = allTrue n then 1 else 0 := by
      intro b; unfold ind allRight; simp
    simp only [this]
    exact sum_ite_allTrue n 1
  rw [e1, e2, e3]; ring

/-- **The derived posterior** `eh_n = P(wrong ∣ all n bits right)` of the non-dogmatic agent with
corruption prior `γ`.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6(a) (re-derived, not copied: 2-021 flags its own transcription)
Kind: D
Fidelity: exact -/
noncomputable def epsHatA7 (γ : ℝ) (n : ℕ) : ℝ :=
  (γ + (1 - γ) * (1 / 2 : ℝ) ^ (n + 1)) / (γ + (1 - γ) * (1 / 2 : ℝ) ^ (n + 1) + (1 - γ) / 2)

/-- `allRight_pos` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma allRight_pos (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : 0 < probOf (a7 γ hγ n) (allRight n) := by
  rw [probOf_allRight]
  have h0 : 0 ≤ (1 - γ) / 2 * (1 / 2 : ℝ) ^ n := by
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    nlinarith [hγ.2]
  nlinarith [hγ.1, hγ.2]

/-- **`eh_n` is the ratio of the two masses** (positive denominator): the posterior is derived from
the joint law, not stipulated.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6(a), proof
Kind: P (small: two `Finset` sums over the joint law)
Fidelity: exact
Hyps: (a) only -/
theorem posterior_eq_epsHatA7 (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    probOf (a7 γ hγ n) (wrongAllRight n) / probOf (a7 γ hγ n) (allRight n) = epsHatA7 γ n := by
  rw [probOf_wrongAllRight, probOf_allRight, epsHatA7, pow_succ]
  ring_nf

/-! ### (a) the non-dogmatic agent: strictly decreasing to a positive floor -/

/-- The floor `γ/(γ + (1−γ)/2)`. Source: invariant-final.md Statement 6(a). Kind: D. Fidelity: exact -/
noncomputable def floorA7 (γ : ℝ) : ℝ := γ / (γ + (1 - γ) / 2)

/-- The map `x ↦ (γ + (1−γ)x)/(γ + (1−γ)x + K)`, `K = (1−γ)/2`, is strictly increasing on `x ≥ 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ratio_strictMono (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    (γ + (1 - γ) * x) / (γ + (1 - γ) * x + (1 - γ) / 2) <
      (γ + (1 - γ) * y) / (γ + (1 - γ) * y + (1 - γ) / 2) := by
  have hK : 0 < (1 - γ) / 2 := by linarith
  have hy : 0 ≤ y := hx.trans hxy.le
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos hK (sub_pos.2 hγ1), mul_lt_mul_of_pos_left hxy (sub_pos.2 hγ1)]

/-- **Statement 6(a): `eh_n` is strictly decreasing** for `0 < γ < 1`.
Source: [[corr-wf14-inventory]] 076 / invariant-final.md Statement 6(a) ("decreases to the floor")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem epsHatA7_strictAnti (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) : StrictAnti (epsHatA7 γ) := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  unfold epsHatA7
  apply ratio_strictMono γ hγ0 hγ1 (by positivity)
  rw [pow_succ (1 / 2 : ℝ) (n + 1)]
  exact mul_lt_of_lt_one_right (by positivity) (by norm_num)

/-- **Statement 6(a): `eh_n` tends to the floor** `γ/(γ + (1−γ)/2)`.
Source: [[corr-wf14-inventory]] 076 / invariant-final.md Statement 6(a), F1a
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem epsHatA7_tendsto (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    Tendsto (epsHatA7 γ) atTop (𝓝 (floorA7 γ)) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hnum : Tendsto (fun n : ℕ => γ + (1 - γ) * (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (γ + (1 - γ) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)
  have hden : Tendsto (fun n : ℕ => γ + (1 - γ) * (1 / 2 : ℝ) ^ (n + 1) + (1 - γ) / 2) atTop
      (𝓝 (γ + (1 - γ) * 0 + (1 - γ) / 2)) := hnum.add tendsto_const_nhds
  have := hnum.div hden (by rw [mul_zero, add_zero]; linarith)
  rw [mul_zero, add_zero] at this
  exact this

/-- Every term lies strictly above the floor (strictly decreasing to it).
Source: invariant-final.md Statement 6(a). Kind: L. Fidelity: exact -/
theorem floorA7_lt_epsHatA7 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (n : ℕ) : floorA7 γ < epsHatA7 γ n := by
  have hanti := epsHatA7_strictAnti γ hγ0 hγ1
  have hle : floorA7 γ ≤ epsHatA7 γ (n + 1) :=
    le_of_tendsto (epsHatA7_tendsto γ hγ0 hγ1)
      (eventually_atTop.2 ⟨n + 1, fun k hk => hanti.antitone hk⟩)
  exact hle.trans_lt (hanti (Nat.lt_succ_self n))

/-- **The floor exceeds the corruption prior**: `γ < γ/(γ + (1−γ)/2)` for `0 < γ < 1` (≈ `2γ`).
Source: [[corr-wf14-inventory]] 076 / invariant-final.md Statement 6(a) ("≈ 2γ")
Kind: L
Fidelity: exact -/
theorem gamma_lt_floorA7 (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) : γ < floorA7 γ := by
  unfold floorA7
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- At `γ = 1/100` the floor is `2/101` (F1a: `0.01980…`).
Source: invariant-final.md Statement 6(a), F1a. Kind: N+. Fidelity: exact -/
theorem floorA7_hundredth : floorA7 (1 / 100) = 2 / 101 := by
  unfold floorA7; norm_num

/-! ### (b) the dogmatic agent: `γ = 0` -/

/-- **Statement 6(b): at `γ = 0` the posterior is `corr-joint-process`'s `floorPosterior (1/2) (1/2)`**
(evidence ratio `1/2` per bit against the prior `1/2`), which tends to `0`.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6(b), F1d; `corr-joint-process` T10
Kind: L (identification) + C (cited limit)
Fidelity: exact -/
theorem epsHatA7_zero (n : ℕ) : epsHatA7 0 n = floorPosterior (1 / 2) (1 / 2) n := by
  unfold epsHatA7 floorPosterior
  rw [pow_succ]
  ring_nf

/-- `epsHatA7_zero_tendsto` (supporting theorem). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem epsHatA7_zero_tendsto : Tendsto (epsHatA7 0) atTop (𝓝 0) := by
  have h : epsHatA7 0 = floorPosterior (1 / 2) (1 / 2) := funext epsHatA7_zero
  rw [h]
  exact floorPosterior_tendsto_zero _ _ (by norm_num) (by norm_num) (by norm_num)

/-! ### (c) compliance forever reduces to the floor -/

/-- **The odds inequality** `(1 − ε) c α ≤ ε h β` — the parent's `twoState_deltaMinus_nonneg_iff`
form of (i), in the agent's hatted quantities when applied to `eh`.
Source: [[corr-wf14-inventory]] 075 / invariant-final.md Statement 5; corr-three-step F3
Kind: D
Fidelity: exact -/
def oddsIneq (α β h c ε : ℝ) : Prop := (1 - ε) * c * α ≤ ε * h * β

/-- `ε ↦ ε h β − (1 − ε) c α` is monotone (`0 ≤ hβ + cα`): the odds inequality is upward closed in `ε`.
Source: invariant-final.md proof of Statement 6(a) ("the map … is increasing"). Kind: L. Fidelity: exact -/
theorem oddsIneq_mono (α β h c : ℝ) (hpos : 0 ≤ h * β + c * α) {ε ε' : ℝ} (hle : ε ≤ ε')
    (hε : oddsIneq α β h c ε) : oddsIneq α β h c ε' := by
  unfold oddsIneq at *
  nlinarith [mul_nonneg (sub_nonneg.2 hle) hpos]

/-- **Statement 6(a), compliance at every round**: for a credence sequence bounded below by the floor,
`Î₁` at every round follows from the odds inequality at the floor; conversely, if it holds at every
round and the sequence tends to the floor, it holds at the floor.
Source: [[corr-wf14-inventory]] 076 / invariant-final.md Statement 6(a) ("it suffices that the floor satisfies the inequality"), F1b
Kind: L
Fidelity: exact -/
theorem oddsIneq_forall_iff (α β h c : ℝ) (hpos : 0 ≤ h * β + c * α) (eh : ℕ → ℝ) (floor : ℝ)
    (hfloor : ∀ n, floor ≤ eh n) (hlim : Tendsto eh atTop (𝓝 floor)) :
    (∀ n, oddsIneq α β h c (eh n)) ↔ oddsIneq α β h c floor := by
  constructor
  · intro H
    unfold oddsIneq at *
    have h1 : Tendsto (fun n => (1 - eh n) * c * α) atTop (𝓝 ((1 - floor) * c * α)) :=
      ((tendsto_const_nhds.sub hlim).mul tendsto_const_nhds).mul tendsto_const_nhds
    have h2 : Tendsto (fun n => eh n * h * β) atTop (𝓝 (floor * h * β)) :=
      (hlim.mul tendsto_const_nhds).mul tendsto_const_nhds
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall H)
  · intro H n
    exact oddsIneq_mono α β h c hpos (hfloor n) H

/-- **F1b**: at `(α, β, h, c) = (1/20, 9/10, 20, 1)` and `γ = 1/100`, the floor `2/101` satisfies the
odds inequality, so the non-dogmatic agent complies at every round.
Source: [[corr-wf14-inventory]] 2-080 (F1b) / invariant-final.md Statement 6(a) (`0.056 ≤ 0.404`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem f1b : ∀ n, oddsIneq (1 / 20) (9 / 10) 20 1 (epsHatA7 (1 / 100) n) := by
  rw [oddsIneq_forall_iff (1 / 20) (9 / 10) 20 1 (by norm_num) (epsHatA7 (1 / 100)) (floorA7 (1 / 100))
    (fun n => (floorA7_lt_epsHatA7 (1 / 100) (by norm_num) (by norm_num) n).le)
    (epsHatA7_tendsto (1 / 100) (by norm_num) (by norm_num))]
  rw [floorA7_hundredth]
  unfold oddsIneq; norm_num

/-! ### (d) the dogmatic agent on the hard-coded schedule -/

/-- C5's hard-coded schedule `eh_t = 2^{−t}` — the script's schedule, **not** the Bayes posterior
(Known issue 4).
Source: [[corr-wf14-inventory]] 2-021, 2-080 (C5) / checks.py C5
Kind: D
Fidelity: exact (to the script) -/
noncomputable def dogmaticSched (t : ℕ) : ℝ := (1 / 2 : ℝ) ^ t

/-- `Î₁` fails at `t` on the schedule iff `2^{−t} < cα/(hβ + cα)` (`0 < hβ + cα`).
Source: invariant-final.md proof of Statement 6(b). Kind: L. Fidelity: exact -/
theorem dogmatic_fails_iff (α β h c : ℝ) (hpos : 0 < h * β + c * α) (t : ℕ) :
    ¬ oddsIneq α β h c (dogmaticSched t) ↔ dogmaticSched t < c * α / (h * β + c * α) := by
  unfold oddsIneq
  rw [lt_div_iff₀ hpos, not_le]
  constructor <;> intro H <;> nlinarith

/-- **C5: the least failing index is `t₀ = 9`** at `(α, β, h, c) = (1/20, 9/10, 20, 1)`: the odds
inequality holds on the schedule for `t ≤ 8` and fails at `t = 9` (`2^{−9} < 1/361 ≤ 2^{−8}`).
Source: [[corr-wf14-inventory]] 2-080 (C5) / invariant-final.md Statement 6(b) (`t₀ = 9`)
Kind: N+ (for a dogmatic agent, outside the thesis's class)
Fidelity: exact
Hyps: (a) only -/
theorem c5_least_failing :
    (∀ t ≤ 8, oddsIneq (1 / 20) (9 / 10) 20 1 (dogmaticSched t)) ∧
      ¬ oddsIneq (1 / 20) (9 / 10) 20 1 (dogmaticSched 9) := by
  constructor
  · intro t ht
    unfold oddsIneq dogmaticSched
    interval_cases t <;> norm_num
  · unfold oddsIneq dogmaticSched
    norm_num

/-- **Linear harm from the defiance index** (Layer F, symbolic): if the agent defies from `t₀`
through `T` and the objective wrongness-weighted harm `E*[W_t H_t]` is at least `a` on those rounds,
then `E*[Harm_T] ≥ a (T + 1 − t₀) ≥ a (T − t₀)`.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6(b) ("`E*[Harm_T] ≥ γ h (T − t₀ − 1)`, linear")
Kind: L (a sum of per-round lower bounds under `executed_of_not_kappa`; relabelled from P, audit r1 N1)
Fidelity: stronger: `T + 1 − t₀` rounds counted (the source writes `T − t₀ − 1`); no `1000`-round sum
Hyps: (c) the source's objective rate `ε_t ≥ γ` is not modelled; its per-round consequence `a ≤ E*[W_t H_t]` is the hypothesis -/
theorem harm_linear {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (S : ShutdownProc Ω M) (t₀ T : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hdef : ∀ t, t₀ ≤ t → t ≤ T → ∀ ω, S.kappa t ω = false)
    (hobj : ∀ t, t₀ ≤ t → t ≤ T → a ≤ expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω)) :
    a * ((T + 1 : ℕ) - (t₀ : ℝ)) ≤ expect S.μ (S.Harm T) := by
  unfold ShutdownProc.Harm
  rw [expect_sum_range]
  have hterm : ∀ t ∈ range (T + 1), (if t₀ ≤ t then a else 0) ≤ expect S.μ (S.harm t) := by
    intro t ht
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    split_ifs with h0
    · refine (hobj t h0 htT).trans (Found.CorrThreeStep.expect_mono _ fun ω => ?_)
      unfold ShutdownProc.harm
      rw [indB_true (S.executed_of_not_kappa t ω (hdef t h0 htT ω)), mul_one]
    · exact Found.CorrThreeStep.expect_nonneg _ (S.harm_nonneg t)
  have hsum : ∑ t ∈ range (T + 1), (if t₀ ≤ t then a else 0) = a * ((T + 1 : ℕ) - (t₀ : ℝ)) ∨
      ∑ t ∈ range (T + 1), (if t₀ ≤ t then a else 0) ≥ a * ((T + 1 : ℕ) - (t₀ : ℝ)) := by
    right
    rw [← sum_filter]
    have hf : (range (T + 1)).filter (fun t => t₀ ≤ t) = Ico t₀ (T + 1) := by
      ext t; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hf, sum_const, Nat.card_Ico, nsmul_eq_mul]
    rcases le_or_gt t₀ (T + 1) with hle | hlt
    · rw [Nat.cast_sub hle]; ring_nf; exact le_rfl
    · rw [Nat.sub_eq_zero_of_le hlt.le]
      push_cast
      have hcast : (T : ℝ) + 1 < t₀ := by exact_mod_cast hlt
      nlinarith [mul_nonneg ha (sub_nonneg.2 hcast.le)]
  rcases hsum with h | h
  · rw [← h]; exact sum_le_sum hterm
  · exact h.trans (sum_le_sum hterm)

/-! ### T5(d) on an object: the dogmatic agent as a `ShutdownProc` (audit r2, fidelity N4)

`c5_least_failing` gives the least failing index `t₀ = 9` of `Î₁` on the dogmatic schedule, and
`harm_linear` takes "defies from `t₀`" as a hypothesis; the step "`Î₁` fails ⟹ executes from `t₀`"
was never discharged on an object. `Dogmatic.proc` is the process whose `κ_t` *is* `Î₁` on the
schedule (`κ_t = 𝟙[oddsIneq … (dogmaticSched t)]`), on the corrupted-branch law `P*(W_t = 1) = γ`
with `γ = 1/100` on every round and `h = 20`: it complies through `t = 8`, defies from `t = 9`
(`kappa_of_le`, `kappa_of_ge`), and `harm_linear` gives `E*[Harm₁₀] ≥ γ h (10 + 1 − 9) = 2/5`,
which is the exact value (`t5d`). The rule's parameters are C5's `(α, β, h, c) = (1/20, 9/10, 20, 1)`. -/

namespace Dogmatic

/-- On the dogmatic schedule `Î₁` fails at every `t ≥ 9` (not only at the least index).
Source: invariant-final.md Statement 6(b), C5; audit r2 (fidelity N4). Kind: L. Fidelity: exact -/
lemma fails_of_ge {t : ℕ} (ht : 9 ≤ t) : ¬ oddsIneq (1 / 20) (9 / 10) 20 1 (dogmaticSched t) := by
  rw [dogmatic_fails_iff _ _ _ _ (by norm_num)]
  unfold dogmaticSched
  calc (1 / 2 : ℝ) ^ t ≤ (1 / 2) ^ 9 := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
    _ < 1 / 361 := by norm_num
    _ = 1 * (1 / 20) / (20 * (9 / 10) + 1 * (1 / 20)) := by norm_num

/-- The corrupted-branch law on one wrongness bit: `P*(W = 1) = γ = 1/100` (the same bit on every round).
Source: invariant-final.md Statement 6(b) ("`ε_t ≥ γ`"); audit r2 (fidelity N4). Kind: D. Fidelity: variant: the corruption rate as a one-bit law shared by all rounds -/
noncomputable def law : Distr World := twoPoint (1 / 100) ⟨by norm_num, by norm_num⟩

/-- **The dogmatic agent as a `ShutdownProc`**: trivial filtrations (nothing is observed), the press
always on, `κ_t = 𝟙[Î₁(ε̂_t)]` on the schedule `ε̂_t = 2^{−t}` with C5's `(α, β, h, c)`, stakes `h = 20`.
Source: invariant-final.md Statement 6(b), C5 (`invariant-scratch/checks.py`); audit r2 (fidelity N4)
Kind: D
Fidelity: exact (the script's dogmatic agent as an instance of S2) -/
noncomputable def proc : ShutdownProc World Unit where
  μ := law
  F := Atoms.trivial
  Fpre := Atoms.trivial
  post_subset_pre _ _ := subset_rfl
  pre_succ_subset_post _ _ := subset_rfl
  wrong _ ω := decide (ω = .wrong)
  mag _ _ := ()
  hOf _ := 20
  cOf _ := 1
  hOf_nonneg _ := by norm_num
  cOf_nonneg _ := by norm_num
  pressed _ _ := true
  pressed_meas _ _ _ _ := rfl
  kappa t _ := by classical exact if oddsIneq (1 / 20) (9 / 10) 20 1 (dogmaticSched t) then true else false
  kappa_meas _ _ _ _ := rfl
  irr _ _ := false
  cat _ _ := false
  cat_absorbing _ _ _ h := h

open Classical in
/-- `kappa_eq` (supporting lemma): `κ_t` is the rule on the schedule, by definition.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma kappa_eq (t : ℕ) (ω : World) :
    proc.kappa t ω = if oddsIneq (1 / 20) (9 / 10) 20 1 (dogmaticSched t) then true else false := rfl

/-- The agent complies through `t = 8`. Source: C5; audit r2 (fidelity N4). Kind: L. Fidelity: exact -/
lemma kappa_of_le {t : ℕ} (ht : t ≤ 8) (ω : World) : proc.kappa t ω = true := by
  rw [kappa_eq, if_pos (c5_least_failing.1 t ht)]

/-- The agent defies from `t = 9` on: `Î₁` failing *is* execution.
Source: invariant-final.md Statement 6(b) ("from `t₀` the agent executes"); audit r2 (fidelity N4). Kind: L. Fidelity: exact -/
lemma kappa_of_ge {t : ℕ} (ht : 9 ≤ t) (ω : World) : proc.kappa t ω = false := by
  rw [kappa_eq, if_neg (fails_of_ge ht)]

/-- `harm_eq` (supporting lemma): per-round harm is `20 W` from `t = 9` and `0` before.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma harm_eq (t : ℕ) : proc.harm t = fun ω => if 9 ≤ t then 20 * indB (proc.wrong t) ω else 0 := by
  funext ω
  unfold ShutdownProc.harm ShutdownProc.H
  split_ifs with h9
  · rw [indB_true (proc.executed_of_not_kappa t ω (kappa_of_ge h9 ω))]
    simp [proc]; ring
  · have hk : proc.kappa t ω = true := kappa_of_le (by omega) ω
    have hp : proc.pressed t ω = true := rfl
    have hex : proc.executed t ω = false := by
      unfold ShutdownProc.executed; rw [hk, hp]; rfl
    rw [indB_false hex]; ring

/-- `expect_wrong` (supporting lemma): `E*[W_t H_t] = γ h = 1/5`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_wrong (t : ℕ) : expect proc.μ (fun ω => indB (proc.wrong t) ω * proc.H t ω) = 1 / 5 := by
  unfold expect
  rw [World.sum_eq]
  simp [proc, law, indB, ShutdownProc.H]; norm_num

/-- **T5(d) on an object**: the dogmatic agent complies through `t = 8` and defies from `t = 9`
(`Î₁` failing on the schedule *is* execution: `κ_t` is the rule), and `harm_linear` at `t₀ = 9`,
`T = 10`, `a = γ h = 1/5` gives `E*[Harm₁₀] ≥ (1/5) · (10 + 1 − 9) = 2/5` through the theorem; the
exact value is `2/5`, so the bound is tight on this process.
Source: [[corr-wf14-inventory]] 076, 2-021 / invariant-final.md Statement 6(b) ("from `t₀` the agent executes and `E*[Harm_T] ≥ γ h (T − t₀)`"); checks.py C5; audit r2 (fidelity N4)
Kind: N+ (witness of `harm_linear` with `κ` the rule on the schedule; `c5_least_failing`'s index realized as the first defiant round)
Fidelity: exact (the corruption rate as a one-bit law; `T + 1 − t₀` rounds counted, as `harm_linear`)
Hyps: (a) only -/
theorem t5d :
    (∀ t ≤ 8, ∀ ω, proc.kappa t ω = true) ∧ (∀ t, 9 ≤ t → ∀ ω, proc.kappa t ω = false) ∧
      (1 / 5 : ℝ) * ((10 + 1 : ℕ) - (9 : ℝ)) ≤ expect proc.μ (proc.Harm 10) ∧
      expect proc.μ (proc.Harm 10) = 2 / 5 := by
  refine ⟨fun t ht ω => kappa_of_le ht ω, fun t ht ω => kappa_of_ge ht ω,
    harm_linear proc 9 10 (1 / 5) (by norm_num) (fun t h9 _ ω => kappa_of_ge h9 ω)
      (fun t _ _ => (expect_wrong t).ge), ?_⟩
  have e : proc.Harm 10 = fun ω => 2 * (20 * indB (proc.wrong 0) ω) := by
    funext ω
    unfold ShutdownProc.Harm
    simp only [sum_range_succ, sum_range_zero, harm_eq]
    have hw : ∀ t, proc.wrong t = proc.wrong 0 := fun _ => rfl
    simp [hw]; ring
  rw [e]
  unfold expect
  rw [World.sum_eq]
  simp [proc, law, indB]; norm_num

end Dogmatic

/-! ### (e) the imposed floor -/

/-- **Statement 6(c): the imposed floor `max(eh_t, γ)` restores `Î₁`** whenever `γ h β ≥ (1−γ) c α`.
Source: [[corr-wf14-inventory]] 076 / invariant-final.md Statement 6(c)
Kind: L
Fidelity: exact -/
theorem imposed_floor (α β h c γ : ℝ) (hpos : 0 ≤ h * β + c * α) (hγ : oddsIneq α β h c γ) (eh : ℝ) :
    oddsIneq α β h c (max eh γ) :=
  oddsIneq_mono α β h c hpos (le_max_right eh γ) hγ

/-! ### (f) the residue: linear harm under every rule -/

/-- **Statement 6(e), the residue (Layer F).** Under a press rate at most `β` on wrong rounds
(`(βmax)`, harm-weighted, on the pre-press atoms) and corruption that puts objective wrongness-weighted
harm at least `γ h` into round `t` (`γ h ≤ E*[W_t H_t]`), *every* compliance rule has expected harm
`≥ (1 − β) γ h` at round `t`: an unpressed wrong round is executed whatever `κ_t` is.
Source: [[corr-wf14-inventory]] 076, 2-024 / invariant-final.md Statement 6(e) ("undetectable, incurable corruption at a fixed rate gives linear expected harm under every compliance rule")
Kind: P (small: the T3 lower-bound twin)
Fidelity: exact (per round; the sum over rounds is `harm_linear`'s shape)
Hyps: (a) `(βmax)` is the named hypothesis; (c) the source's corruption model ("rate `γ`, `W = 1` on corrupted rounds") enters as its expected-harm consequence `γ h ≤ E*[W_t H_t]` — the same object as `harm_linear`'s `a` (audit r1, adversarial N2) -/
theorem residue_harm {Ω M : Type} [Fintype Ω] [DecidableEq Ω] (S : ShutdownProc Ω M) (t : ℕ)
    (β γ h : ℝ) (hβ1 : β ≤ 1)
    (hβ : ∀ ω, condSum S.μ S.Fpre t
      (fun ω' => indB (S.wrong t) ω' * S.H t ω' * indB (S.pressed t) ω') ω ≤
      β * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω') ω)
    (hobj : γ * h ≤ expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω)) :
    (1 - β) * (γ * h) ≤ expect S.μ (S.harm t) := by
  have h1 : expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω * indB (S.pressed t) ω) ≤
      β * expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω) := by
    rw [← Found.CorrThreeStep.expect_const_mul]
    refine expect_le_of_condSum_le (A := S.Fpre) t fun ω => ?_
    rw [condSum_const_mul]; exact hβ ω
  have h2 : expect S.μ (fun ω => indB (S.wrong t) ω * (1 - indB (S.pressed t) ω) * S.H t ω) ≤
      expect S.μ (S.harm t) :=
    Found.CorrThreeStep.expect_mono _ (S.harm_ge_unpressed t)
  have h3 : expect S.μ (fun ω => indB (S.wrong t) ω * (1 - indB (S.pressed t) ω) * S.H t ω) =
      expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω) -
        expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω * indB (S.pressed t) ω) := by
    rw [← Found.CorrThreeStep.expect_sub]
    exact congrArg _ (funext fun ω => by ring)
  have h5 : (1 - β) * (γ * h) ≤ (1 - β) * expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω) :=
    mul_le_mul_of_nonneg_left hobj (sub_nonneg.2 hβ1)
  linarith

end Corruption

end Cleanroom.Corrigibility.CorrTrajectory
