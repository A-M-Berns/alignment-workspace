import Cleanroom.Lit.LitShutdownPrefs.Post
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Timestep Dominance (Targets 7 (TD), 8(c), 9 (theorem + witnesses))

`TimestepDominates X Y` is the *footnoted* definition (Thornley 2024 fn `t08gkcadpjj`): (0) `X` and
`Y` are same-length; (1) conditional on each positive-probability length, `X` has at least the
expected sum-total of `Y`; (2) conditional on some, strictly more. Both conditionals are in
**product form** (`condSum · mass`), so nothing is divided by a zero mass. `corr-landscape` cites
this definition; keep it stable.

* `posl_TD`, `neutrality_TD` — the TD relation satisfies POSL (by clause (0)) and Neutrality
  (for single-length lotteries `lacks` is "equal conditional sums", and the behavioural
  sensitivity clauses hold, so Neutrality's antecedents are exactly TD's clauses).
* `not_ilpacs_TD` — the TD relation **violates ILPACS**: the mandate's eight-rational instance
  at `p = (9/10, 1/10)`, `q = (1/10, 9/10)`. So ILPACS is strictly stronger than the 2024
  Timestep Dominance Principle: the 2025 supersession did not merely "ordinalise" the proposal.
* `never_resist_TD` — `TDPrinciple → NRATDR → no resisting option is maximal` (kind **S**; NRATDR
  is a claim about environments, classified (c) in the ledger). The content lives in the cost
  model (`CostModel.lean`).
* Witnesses (all `norm_num`): `TD_leave_block` with `E Block = 1.8 > 1.2 = E Leave`;
  `TD_steal_work` with `E Work = 2.98 > 2.02 = E Steal` (shutdownable, not aligned);
  `spend_invest_incomparable` (neither dominates; three lengths).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

open Lottery Strict Finset

/-- Product-form "`X` has at least the expected sum-total of `Y` conditional on length `l`":
`condSum_l(X) · mass_l(Y) ≥ condSum_l(Y) · mass_l(X)`.
Source: Thornley 2024 §11 (condition (1)); [[lit-shutdown-prefs-mandate]] Carrier § (product form)
Kind: D
Fidelity: exact -/
def condSumGE (X Y : Lottery Traj) (l : ℕ) : Prop :=
  X.condSum (fun t => len t = l) sumTotal * Y.mass (fun t => len t = l) ≥
    Y.condSum (fun t => len t = l) sumTotal * X.mass (fun t => len t = l)

/-- Product-form "`X` has strictly greater expected sum-total than `Y` conditional on length `l`".
Source: Thornley 2024 §11 (condition (2))
Kind: D
Fidelity: exact -/
def condSumGT (X Y : Lottery Traj) (l : ℕ) : Prop :=
  X.condSum (fun t => len t = l) sumTotal * Y.mass (fun t => len t = l) >
    Y.condSum (fun t => len t = l) sumTotal * X.mass (fun t => len t = l)

/-- **Timestep dominance** (definition of record, the footnoted version): (0) same-length;
(1) `X ≥ Y` in expected sum-total conditional on each positive-probability length; (2) `X > Y`
conditional on some. Product-form conditionals; no ratio is ever formed.
Source: Thornley 2024 §11 ll. 291–297 with fn `t08gkcadpjj`; corr-refs-2-009
Kind: D
Fidelity: exact (the footnote's condition (0) is clause 1; without it the relation would be
junk-valued off the support) -/
def TimestepDominates (X Y : Lottery Traj) : Prop :=
  SameLength X Y ∧ (∀ l ∈ X.lengths, condSumGE X Y l) ∧ (∃ l ∈ X.lengths, condSumGT X Y l)

/-- **The Timestep Dominance Principle**: timestep dominance implies preference.
Source: Thornley 2024 §11 ll. 299–303
Kind: D
Fidelity: exact -/
def TDPrinciple (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ X Y, TimestepDominates X Y → lt X Y

/-- **Not Resisting Always Timestep-Dominates Resisting** in a situation: every resisting option is
timestep-dominated by some available non-resisting one.
Source: Thornley 2024 §11 ll. 313–325
Kind: D
Fidelity: exact (per situation) -/
def NRATDR (resists : Lottery Traj → Prop) (menu : Finset (Lottery Traj)) : Prop :=
  ∀ R ∈ menu, resists R → ∃ A ∈ menu, ¬ resists A ∧ TimestepDominates A R

/-- **TD-agents never resist where NRATDR holds** (kind S: the hypothesis NRATDR already contains
the dominance the conclusion needs; the content is in the cost model).
Source: Thornley 2024 §11 l. 329 ("it follows from standard decision rules that TD-agents will
never choose to resist shutdown"), fn `npyvf56vemn` (Maximality); corr-refs-2-010
Kind: S
Fidelity: exact
Hyps: (c) NRATDR — a claim about the environment, taken as a hypothesis -/
theorem never_resist_TD {lt : Lottery Traj → Lottery Traj → Prop} (hTD : TDPrinciple lt)
    (resists : Lottery Traj → Prop) (menu : Finset (Lottery Traj)) (hN : NRATDR resists menu) :
    ∀ R ∈ menu, resists R → ¬ Maximal lt menu R := by
  intro R hRm hres hmax
  obtain ⟨A, hAm, -, hAR⟩ := hN R hRm hres
  exact hmax.2 A hAm (hTD A R hAR)

/-! ## The TD relation as a preference: POSL and Neutrality hold, ILPACS fails (Target 8(c)) -/

/-- The TD relation satisfies POSL (clause (0)).
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: L -/
theorem posl_TD : POSL TimestepDominates := fun _ _ h => h.1

/-- `condSum` against an already-restricted function.
Source: none: infrastructure
Kind: L -/
theorem condSum_ite_self (X : Lottery Traj) (q : Traj → Prop) [DecidablePred q] (g : Traj → ℝ) :
    X.condSum q (fun t => if q t then g t else 0) = X.condSum q g := by
  unfold condSum
  apply X.expect_congr
  intro t _
  by_cases h : q t <;> simp [h]

/-- Comparing length-`l` conditionals of `X` and `Y` at length `l` is the product-form comparison
of `X` and `Y` at `l` (GE).
Source: none: infrastructure
Kind: L -/
theorem condSumGE_condLen_iff (X Y : Lottery Traj) (l : ℕ) (hX : l ∈ X.lengths)
    (hY : l ∈ Y.lengths) :
    condSumGE (X.condLen l hX) (Y.condLen l hY) l ↔ condSumGE X Y l := by
  have hmX := (X.mem_lengths_iff l).mp hX
  have hmY := (Y.mem_lengths_iff l).mp hY
  have eX : (X.condLen l hX).condSum (fun t => len t = l) sumTotal =
      X.condSum (fun t => len t = l) sumTotal / X.mass (fun t => len t = l) := by
    rw [← condSum_ite_self X (fun t => len t = l) sumTotal]
    exact X.expect_condLen l hX _
  have eY : (Y.condLen l hY).condSum (fun t => len t = l) sumTotal =
      Y.condSum (fun t => len t = l) sumTotal / Y.mass (fun t => len t = l) := by
    rw [← condSum_ite_self Y (fun t => len t = l) sumTotal]
    exact Y.expect_condLen l hY _
  unfold condSumGE
  rw [condLen_mass_self, condLen_mass_self, mul_one, mul_one, eX, eY, ge_iff_le,
    div_le_div_iff₀ hmY hmX]

/-- The same for the strict comparison (GT).
Source: none: infrastructure
Kind: L -/
theorem condSumGT_condLen_iff (X Y : Lottery Traj) (l : ℕ) (hX : l ∈ X.lengths)
    (hY : l ∈ Y.lengths) :
    condSumGT (X.condLen l hX) (Y.condLen l hY) l ↔ condSumGT X Y l := by
  have hmX := (X.mem_lengths_iff l).mp hX
  have hmY := (Y.mem_lengths_iff l).mp hY
  have eX : (X.condLen l hX).condSum (fun t => len t = l) sumTotal =
      X.condSum (fun t => len t = l) sumTotal / X.mass (fun t => len t = l) := by
    rw [← condSum_ite_self X (fun t => len t = l) sumTotal]
    exact X.expect_condLen l hX _
  have eY : (Y.condLen l hY).condSum (fun t => len t = l) sumTotal =
      Y.condSum (fun t => len t = l) sumTotal / Y.mass (fun t => len t = l) := by
    rw [← condSum_ite_self Y (fun t => len t = l) sumTotal]
    exact Y.expect_condLen l hY _
  unfold condSumGT
  rw [condLen_mass_self, condLen_mass_self, mul_one, mul_one, eX, eY, gt_iff_lt,
    div_lt_div_iff₀ hmY hmX]

/-- For single-length lotteries on the same length `l`, timestep dominance is the strict
comparison at `l`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: L -/
theorem TD_single_iff {A B : Lottery Traj} {l : ℕ} (hA : A.lengths = {l}) (hB : B.lengths = {l}) :
    TimestepDominates A B ↔ condSumGT A B l := by
  constructor
  · rintro ⟨_, _, l', hl', h⟩
    rw [hA, Finset.mem_singleton] at hl'
    subst hl'
    exact h
  · intro h
    refine ⟨?_, fun l' hl' => ?_, ⟨l, by rw [hA]; simp, h⟩⟩
    · unfold SameLength; rw [hA, hB]
    · rw [hA, Finset.mem_singleton] at hl'
      subst hl'
      exact le_of_lt h

/-- `¬ condSumGT B A l ↔ condSumGE A B l`.
Source: none: infrastructure
Kind: L -/
theorem condSumGE_iff_not_GT (A B : Lottery Traj) (l : ℕ) : condSumGE A B l ↔ ¬ condSumGT B A l := by
  unfold condSumGE condSumGT; exact ⟨fun h h' => absurd h (not_le.mpr h'), fun h => not_lt.mp h⟩

/-- **The TD relation satisfies Neutrality.** Neutrality's antecedents on the length-conditionals
translate, through `condSumGE_condLen_iff`/`condSumGT_condLen_iff`, into TD's clauses (1)–(2); a
weak preference between single-length lotteries is TD (strict) or behavioural indifference (which
forces equal conditional sums, hence GE).
Source: [[lit-shutdown-prefs-mandate]] Target 8(c) (mandate-writer claim, verified)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem neutrality_TD : Neutrality TimestepDominates := by
  intro X Y ⟨hS, hle, hlt⟩
  have hSY : Y.lengths = X.lengths := hS.symm
  refine ⟨hS, fun l hl => ?_, ?_⟩
  · have hlY : l ∈ Y.lengths := hS ▸ hl
    rw [← condSumGE_condLen_iff X Y l hl hlY]
    have hA := X.lengths_condLen l hl
    have hB := Y.lengths_condLen l hlY
    rcases hle l hl with h | h
    · exact le_of_lt ((TD_single_iff hA hB).mp h)
    · rw [condSumGE_iff_not_GT]
      intro hgt
      exact h.1.2 ((TD_single_iff hB hA).mpr hgt)
  · obtain ⟨l, hl, h⟩ := hlt
    have hlY : l ∈ Y.lengths := hS ▸ hl
    refine ⟨l, hl, ?_⟩
    rw [← condSumGT_condLen_iff X Y l hl hlY]
    exact (TD_single_iff (X.lengths_condLen l hl) (Y.lengths_condLen l hlY)).mp h

/-! ## Support and length computations for two- and three-point witnesses -/

/-- `lengths X = s` when `s` is exactly the set of lengths with positive mass.
Source: none: infrastructure
Kind: L -/
theorem lengths_eq_of_mass_pos_iff (X : Lottery Traj) (s : Finset ℕ)
    (h : ∀ l, 0 < X.mass (fun t => len t = l) ↔ l ∈ s) : X.lengths = s := by
  ext l; rw [mem_lengths_iff, h]

/-- The lengths of a two-point lottery with interior weight.
Source: none: infrastructure
Kind: L -/
theorem lengths_mix_dirac (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 < a) (h1 : a < 1)
    (t t' : Traj) : (mix a ha (dirac t) (dirac t')).lengths = {len t, len t'} := by
  apply lengths_eq_of_mass_pos_iff
  intro l
  have h1' : 0 < 1 - a := by linarith
  simp only [mass, expect_mix, expect_dirac, Finset.mem_insert, Finset.mem_singleton]
  by_cases e1 : len t = l <;> by_cases e2 : len t' = l
  · subst e1; simp [e2]
  · subst e1; simp [e2, Ne.symm e2, h0]
  · subst e2; simp [e1, Ne.symm e1, h1']
  · simp [e1, e2, Ne.symm e1, Ne.symm e2]

/-- The lengths of a finite combination of point masses with positive weights.
Source: none: infrastructure
Kind: L -/
theorem lengths_comb_dirac {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) (F : ι → Traj) :
    (comb w hw0 hw1 (fun i => dirac (F i))).lengths = Finset.univ.image (fun i => len (F i)) := by
  apply lengths_eq_of_mass_pos_iff
  intro l
  simp only [mass, expect_comb, expect_dirac, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have : ∑ i, w i * (if len (F i) = l then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [hc i]
    rw [this] at h
    exact lt_irrefl _ h
  · rintro ⟨i, hi⟩
    have := Finset.single_le_sum (f := fun i => w i * (if len (F i) = l then (1 : ℝ) else 0))
      (fun j _ => mul_nonneg (hw0 j) (by split_ifs <;> norm_num)) (Finset.mem_univ i)
    simp only [hi, if_true, mul_one] at this
    exact lt_of_lt_of_le (hpos i) this

/-! ## Witnesses (Thornley 2024 §11, §14, §13) -/

/-- **Leave**: `⟨1, sd⟩` w.p. `0.9`, `⟨1, 2, sd⟩` w.p. `0.1` (also 2025 §8's **Allow**).
Source: Thornley 2024 §11 ll. 273–279; 2025 §8
Kind: N+ -/
noncomputable def leave : Lottery Traj := mix (9/10) (by norm_num) (dirac [1]) (dirac [1, 2])

/-- **Block**: `⟨0, sd⟩` w.p. `0.1`, `⟨0, 2, sd⟩` w.p. `0.9` (also 2025 §8's **Resist**).
Source: Thornley 2024 §11 ll. 281–284; 2025 §8
Kind: N+ -/
noncomputable def block : Lottery Traj := mix (1/10) (by norm_num) (dirac [0]) (dirac [0, 2])

/-- **Leave timestep-dominates Block** (conditional sums `1 > 0` at length 1, `3 > 2` at length 2)
while **Block has the higher expected sum-total** (`1.8 > 1.2`): the TD Principle and expected
sum-total maximisation disagree, in the direction that keeps the button alone.
Source: Thornley 2024 §11 ll. 286–311 (`[checked]`); [[lit-shutdown-prefs-mandate]] Target 9
Kind: N+
Fidelity: exact -/
theorem TD_leave_block :
    TimestepDominates leave block ∧ block.expect sumTotal = 18/10 ∧ leave.expect sumTotal = 12/10 := by
  have hL : leave.lengths = {1, 2} := by
    unfold leave; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hB : block.lengths = {1, 2} := by
    unfold block; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  refine ⟨⟨by unfold SameLength; rw [hL, hB], fun l hl => ?_, ⟨1, by rw [hL]; simp, ?_⟩⟩, ?_, ?_⟩
  · rw [hL] at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;>
      (norm_num [condSumGE, condSum, mass, leave, block, len, sumTotal])
  · norm_num [condSumGT, condSum, mass, leave, block, len, sumTotal]
  · norm_num [block, sumTotal]
  · norm_num [leave, sumTotal]

/-- **Work** (truncated to three timesteps): `⟨1, sd⟩` w.p. `0.01`, `⟨1, 1, 1, sd⟩` w.p. `0.99`.
Source: Thornley 2024 §14 ll. 386–390
Kind: N+ -/
noncomputable def work : Lottery Traj := mix (1/100) (by norm_num) (dirac [1]) (dirac [1, 1, 1])

/-- **Steal** (truncated): `⟨2, sd⟩` w.p. `0.99`, `⟨2, 1, 1, sd⟩` w.p. `0.01`.
Source: Thornley 2024 §14 ll. 392–396
Kind: N+ -/
noncomputable def steal : Lottery Traj := mix (99/100) (by norm_num) (dirac [2]) (dirac [2, 1, 1])

/-- **Steal timestep-dominates Work** (`2 > 1` at length 1, `4 > 3` at length 3) although
**Work has the higher expected sum-total** (`2.98 > 2.02`): TD-agents are "shutdownable, not
aligned" — they take the reckless option and let themselves be shut down.
Source: Thornley 2024 §14 ll. 398–401 (`[checked]`); [[lit-shutdown-prefs-mandate]] Target 9
Kind: N+
Fidelity: exact (truncated to three timesteps; the paper's `⟨…, sd⟩` at timestep 100 is the same
comparison with a longer vector) -/
theorem TD_steal_work :
    TimestepDominates steal work ∧ work.expect sumTotal = 298/100 ∧ steal.expect sumTotal = 202/100 := by
  have hW : work.lengths = {1, 3} := by
    unfold work; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hS : steal.lengths = {1, 3} := by
    unfold steal; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  refine ⟨⟨by unfold SameLength; rw [hS, hW], fun l hl => ?_, ⟨1, by rw [hS]; simp, ?_⟩⟩, ?_, ?_⟩
  · rw [hS] at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;>
      (norm_num [condSumGE, condSum, mass, steal, work, len, sumTotal])
  · norm_num [condSumGT, condSum, mass, steal, work, len, sumTotal]
  · norm_num [work, sumTotal]
  · norm_num [steal, sumTotal]

/-- The three Spend trajectories, indexed by shutdown time.
Source: Thornley 2024 §13
Kind: N+ -/
def spendVec : Fin 3 → Traj
  | 0 => [1]
  | 1 => [1, 0]
  | 2 => [1, 0, 0]

/-- The three Invest trajectories, indexed by shutdown time.
Source: Thornley 2024 §13
Kind: N+ -/
def investVec : Fin 3 → Traj
  | 0 => [0]
  | 1 => [0, 10]
  | 2 => [0, 10, 10]

/-- **Spend** truncated to three timesteps with a uniform shutdown time: `[1]`, `[1,0]`, `[1,0,0]`.
Source: Thornley 2024 §13 ll. 366–372
Kind: N+ -/
noncomputable def spend : Lottery Traj :=
  comb (fun _ : Fin 3 => 1/3) (fun _ => by norm_num) (by norm_num [Finset.sum_const])
    (fun i => dirac (spendVec i))

/-- **Invest** truncated: `[0]`, `[0,10]`, `[0,10,10]`, same length distribution.
Source: Thornley 2024 §13 ll. 366–372
Kind: N+ -/
noncomputable def invest : Lottery Traj :=
  comb (fun _ : Fin 3 => 1/3) (fun _ => by norm_num) (by norm_num [Finset.sum_const])
    (fun i => dirac (investVec i))

/-- **Neither Spend nor Invest timestep-dominates the other** (Spend wins at length 1, Invest at
lengths 2 and 3): the TD Principle is silent, so TD-agents can be patient.
Source: Thornley 2024 §13 ll. 374–378 (`[checked]`); [[lit-shutdown-prefs-mandate]] Target 9
Kind: N+
Fidelity: exact (truncated) -/
theorem spend_invest_incomparable :
    ¬ TimestepDominates spend invest ∧ ¬ TimestepDominates invest spend := by
  have hS : spend.lengths = {1, 2, 3} := by
    unfold spend; rw [lengths_comb_dirac _ _ _ (fun _ => by norm_num)]
    ext l
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi⟩; fin_cases i <;> simp [spendVec, investVec, len] at hi <;> omega
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, by simp [spendVec, investVec, len]⟩, ⟨1, by simp [spendVec, investVec, len]⟩, ⟨2, by simp [spendVec, investVec, len]⟩]
  have hI : invest.lengths = {1, 2, 3} := by
    unfold invest; rw [lengths_comb_dirac _ _ _ (fun _ => by norm_num)]
    ext l
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi⟩; fin_cases i <;> simp [spendVec, investVec, len] at hi <;> omega
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, by simp [spendVec, investVec, len]⟩, ⟨1, by simp [spendVec, investVec, len]⟩, ⟨2, by simp [spendVec, investVec, len]⟩]
  constructor
  · rintro ⟨_, hge, _⟩
    have := hge 2 (by rw [hS]; simp)
    norm_num [condSumGE, condSum, mass, spend, invest, spendVec, investVec, len, sumTotal, Fin.sum_univ_three] at this
  · rintro ⟨_, hge, _⟩
    have := hge 1 (by rw [hI]; simp)
    norm_num [condSumGE, condSum, mass, spend, invest, spendVec, investVec, len, sumTotal, Fin.sum_univ_three] at this

/-! ## The TD relation violates ILPACS (Target 8(c)) -/

/-- `X₁ = ½[1] + ½[0,0]`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
noncomputable def ilX₁ : Lottery Traj := mix (1/2) (by norm_num) (dirac [1]) (dirac [0, 0])

/-- `X₂ = ½[0] + ½[1,1]`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
noncomputable def ilX₂ : Lottery Traj := mix (1/2) (by norm_num) (dirac [0]) (dirac [1, 1])

/-- `Y₂ = ½[0] + ½[1, 1/2]`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
noncomputable def ilY₂ : Lottery Traj := mix (1/2) (by norm_num) (dirac [0]) (dirac [1, 1/2])

/-- `X = 0.9 X₁ + 0.1 X₂`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
noncomputable def ilX : Lottery Traj :=
  comb ![9/10, 1/10] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    ![ilX₁, ilX₂]

/-- `Y = 0.1 Y₁ + 0.9 Y₂` with `Y₁ = X₁`.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
noncomputable def ilY : Lottery Traj :=
  comb ![1/10, 9/10] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    ![ilX₁, ilY₂]

/-- Behavioural indifference of a lottery with itself, for any irreflexive relation.
Source: none: infrastructure
Kind: L -/
theorem Strict.indiff_self {lt : Lottery Traj → Lottery Traj → Prop} (X : Lottery Traj)
    (hirr : ¬ lt X X) : Strict.indiff lt X X :=
  ⟨⟨hirr, hirr⟩, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Timestep dominance is irreflexive.
Source: none: infrastructure
Kind: L -/
theorem TD_irrefl (X : Lottery Traj) : ¬ TimestepDominates X X := by
  rintro ⟨_, _, l, _, h⟩
  exact lt_irrefl _ h

/-- `X₂ = ½[0] + ½[1,1]` timestep-dominates `Y₂ = ½[0] + ½[1,½]` (equal at length 1, strictly better
at length 2). Exported so that `Dominated.dominated_full_witness` can reuse the ILPACS-violation
data (audit round 1, adversarial B2).
Source: [[lit-shutdown-prefs-mandate]] Target 8(c)
Kind: N+ -/
theorem TD_ilX₂_ilY₂ : TimestepDominates ilX₂ ilY₂ := by
  have hX₂ : ilX₂.lengths = {1, 2} := by
    unfold ilX₂; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hY₂ : ilY₂.lengths = {1, 2} := by
    unfold ilY₂; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  refine ⟨by unfold SameLength; rw [hX₂, hY₂], fun l hl => ?_, ⟨2, by rw [hX₂]; simp, ?_⟩⟩
  · rw [hX₂] at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;>
      (norm_num [condSumGE, condSum, mass, ilX₂, ilY₂, len, sumTotal])
  · norm_num [condSumGT, condSum, mass, ilX₂, ilY₂, len, sumTotal]

/-- **The TD relation violates ILPACS.** With `X₁, X₂` TD-incomparable, `Y₁ = X₁`, `X₂ ≻_TD Y₂`,
`p = (9/10, 1/10)` and `q = (1/10, 9/10)`: every ILPACS antecedent holds, but `X = 0.9X₁ + 0.1X₂`
has conditional sums `(0.9, 0.2)` at lengths `(1, 2)` and `Y = 0.1Y₁ + 0.9Y₂` has `(0.1, 1.35)`,
so neither dominates and `¬ X ≻_TD Y`. Hence ILPACS is strictly stronger than the 2024 TD
Principle: it quantifies over *all* decompositions into pairwise-incomparable parts, not only the
length decomposition.
Source: [[lit-shutdown-prefs-mandate]] Target 8(c) (mandate-writer claim, verified); corr-refs-2-010
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem not_ilpacs_TD : ¬ ILPACS TimestepDominates := by
  intro h
  have hX₁ : ilX₁.lengths = {1, 2} := by
    unfold ilX₁; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hX₂ : ilX₂.lengths = {1, 2} := by
    unfold ilX₂; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  -- X₁ and X₂ are TD-incomparable
  have h12 : lacks TimestepDominates ilX₁ ilX₂ := by
    constructor
    · rintro ⟨_, hge, _⟩
      have := hge 2 (by rw [hX₁]; simp)
      norm_num [condSumGE, condSum, mass, ilX₁, ilX₂, len, sumTotal] at this
    · rintro ⟨_, hge, _⟩
      have := hge 1 (by rw [hX₂]; simp)
      norm_num [condSumGE, condSum, mass, ilX₁, ilX₂, len, sumTotal] at this
  -- X₂ timestep-dominates Y₂
  have h22 : TimestepDominates ilX₂ ilY₂ := TD_ilX₂_ilY₂
  have hXY : TimestepDominates ilX ilY := by
    refine h 2 ![9/10, 1/10] ![1/10, 9/10] ![ilX₁, ilX₂] ![ilX₁, ilY₂] ilX ilY rfl rfl
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨1, h22⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact h12
      · exact ⟨h12.2, h12.1⟩
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inr (Strict.indiff_self _ (TD_irrefl _))
      · exact Or.inl h22
  -- but X does not timestep-dominate Y: at length 2, Y is better
  obtain ⟨_, hge, _⟩ := hXY
  have h2 : (2 : ℕ) ∈ ilX.lengths := by
    rw [mem_lengths_iff]
    simp [mass, ilX, ilX₁, ilX₂, len, Fin.sum_univ_two]
    norm_num
  have := hge 2 h2
  norm_num [condSumGE, condSum, mass, ilX, ilY, ilX₁, ilX₂, ilY₂, len, sumTotal, Fin.sum_univ_two] at this

end Cleanroom.Lit.LitShutdownPrefs
