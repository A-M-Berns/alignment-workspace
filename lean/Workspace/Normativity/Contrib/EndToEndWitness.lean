/-
# The end-to-end witness (item 35)

Round `projects/normativity/rounds/2026-10-21-rebuttal-and-end-to-end/`, Part C.  One run,
one fixture, every stage: the four-sentence fragment of the warrant-enforcement-semantics
round extended by a sentence `Z` and a second warrant `P(Z) ≥ 1/2`.

* **The fixture** (`Run`): strengths `4/5, 3/4, 2/3` on the first warrant, `1/2` on the
  second; `X` settles true at `n₁ = 3`, the first warrant's applicability port is defeated at
  `n₀ = 5`, `Y` is refuted at `n_E = 8`.  `seedC1` is the seed of C1 (the first warrant's
  three forms, the coherence row `X∧A ≤ X`, an empty constitutive layer), humble.
* **The rule produces the seed.**  `seedAt n` and the warrant list `W` are, at every date,
  the survivors of the grounds under the grounded rule (`seedAt_eq_survivors`): the strength
  occurrence leaves at the undercut together with the applicability it cites.
* **Intervals by elimination.**  `intervalAt n φ = forcedInterval (seedAt n) W quiet
  (settlementAt n) φ`.  The kernel cannot run the elimination over `ℚ` (`Rat` normalization
  does not reduce in `decide`), so each value is established through the elimination's own
  correctness theorem: valid bounds attained in the real region determine the computed pair
  (`forcedInterval_eq_of_bounds`).  The `#eval` lines run the elimination executably.
* **Licences.**  Certificates for the bound on `X∧A∧Y` (the first warrant's conclusion
  coordinate) and on `Z`, licensed at entry; after the undercut the certificate citing the
  applicability occurrence is not supported and a fresh certificate on `Z` is.
* **The bankroll.**  The force schedule is the survivors through `toForceRow` at the warrant
  round's fixed intensity; the
  enforcer's assessed net worth is at least `−3ρ(2 + ρ)` across the rebuttal
  (`liability_run`), and `conditional_normative_inductor` composes (`inductor_run`).
* **The record and the hull.**  `trace` is neither injective nor constant in the run and
  mediates the docket at every step; the hull mass over `{X∧A, X∧A∧Y, Z}` is a four-valued
  sequence with its one reopening, eventually constant.
* **`witness`**: the conjunction.

Names are provisional (`AGENTS.md` standard 6).  Nothing here is registered.
-/
import Workspace.Normativity.Contrib.WarrantEntitlement
import Workspace.Normativity.Contrib.ConvergenceMeasure

namespace Workspace.Normativity.Contrib.EndToEndWitness

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.ConvergenceMeasure
open Finset

variable {d : ℕ}

/-! ## Real satisfaction of the three forms -/

lemma cast_sum_ite (X : Fin d) (c : ℚ) (x : Fin d → ℝ) :
    ∑ i, (((if i = X then c else 0 : ℚ) : ℝ) * x i) = (c : ℝ) * x X := by
  rw [Finset.sum_eq_single X]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ X) h

theorem premise_satR_iff (X : Fin d) (c : ℚ) (x : Fin d → ℝ) :
    (Form.premise X c).row.SatR x ↔ (c : ℝ) ≤ x X := by
  simp only [Form.row, Row.SatR]
  rw [cast_sum_ite]
  push_cast
  constructor <;> intro h <;> linarith

theorem applicability_satR_iff (X XA : Fin d) (c : ℚ) (x : Fin d → ℝ) :
    (Form.applicability X XA c).row.SatR x ↔ (c : ℝ) * x X ≤ x XA := by
  simp only [Form.row, Row.SatR, Rat.cast_add, add_mul, Finset.sum_add_distrib, cast_sum_ite]
  push_cast
  constructor <;> intro h <;> linarith

theorem strength_satR_iff (XA XAY : Fin d) (c : ℚ) (x : Fin d → ℝ) :
    (Form.strength XA XAY c).row.SatR x ↔ (c : ℝ) * x XA ≤ x XAY := by
  simp only [Form.row, Row.SatR, Rat.cast_add, add_mul, Finset.sum_add_distrib, cast_sum_ite]
  push_cast
  constructor <;> intro h <;> linarith

/-! ## The computed interval is determined by valid attained bounds -/

/-- **The elimination's output, pinned by its specification.**  Bounds valid on the real
region and attained in it are the computed endpoints. -/
theorem forcedInterval_eq_of_bounds {m : ℕ} {A : Type*} (S : Seed (m + 1) A)
    (W : List (SubItem (m + 1))) (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
    (lo hi : ℚ)
    (hlo : ∀ x, forcedRegionR S W st F x → (lo : ℝ) ≤ x φ)
    (hhi : ∀ x, forcedRegionR S W st F x → x φ ≤ (hi : ℝ))
    (xlo : Fin (m + 1) → ℝ) (hxlo : forcedRegionR S W st F xlo) (hxloφ : xlo φ = lo)
    (xhi : Fin (m + 1) → ℝ) (hxhi : forcedRegionR S W st F xhi) (hxhiφ : xhi φ = hi) :
    forcedInterval S W st F φ = (lo, hi) := by
  obtain ⟨hb, ⟨y, hy, hyφ⟩, ⟨z, hz, hzφ⟩⟩ := forcedInterval_spec S W st F φ ⟨xlo, hxlo⟩
  have h1 : ((forcedInterval S W st F φ).1 : ℝ) ≤ lo := by rw [← hxloφ]; exact (hb xlo hxlo).1
  have h2 : (lo : ℝ) ≤ (forcedInterval S W st F φ).1 := by rw [← hyφ]; exact hlo y hy
  have h3 : (hi : ℝ) ≤ (forcedInterval S W st F φ).2 := by rw [← hxhiφ]; exact (hb xhi hxhi).2
  have h4 : ((forcedInterval S W st F φ).2 : ℝ) ≤ hi := by rw [← hzφ]; exact hhi z hz
  have e1 : (forcedInterval S W st F φ).1 = lo := by exact_mod_cast le_antisymm h1 h2
  have e2 : (forcedInterval S W st F φ).2 = hi := by exact_mod_cast le_antisymm h4 h3
  exact Prod.ext e1 e2

/-- A price in the settled region leaves the position on the settled bundle at zero. -/
theorem positionOf_eq_zero_of_region (G : Grounds d) (st : DocketState) (F : Settlement d)
    (β : ℚ) (p : Fin d → ℚ) (hp : G.settledRegion st F p) :
    positionOf (G.settledBundle st F) β p = 0 := by
  funext k
  unfold positionOf
  simp only [Pi.zero_apply]
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨c, hc, rfl⟩ := hy
  have hsat : c.row.Sat p := hp.2 c hc
  have hviol : TraderizedEnforcement.violation Finset.univ (fun j => -c.row.a j) (-c.row.b) p = 0 := by
    unfold TraderizedEnforcement.violation TraderizedEnforcement.pair
    unfold Row.Sat at hsat
    have : ∑ k, -c.row.a k * p k = -∑ k, c.row.a k * p k := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact max_eq_left (by linarith)
  rw [hviol]
  ring

/-- The record mediates the docket, on every audited class of runs. -/
theorem docket_mediated_any (D : Set (MarketRun d)) (β : ℚ) :
    Workspace.Deference.Contrib.ReasonMediatedAuthorship.ReasonMediated
      (fun (q : MarketRun d) (_ : Unit) => q) (fun q => trace q β) (fun q => q.docket) D () := by
  intro q _ q' _ h
  funext n
  have := congrArg (fun r : Record d => (r n).state.docket) h
  simpa [trace] using this

/-! ## The run -/

namespace Run

open Fixture2 (X XA XAY Y Z)

/-- The declared quantities. -/
def cP : ℚ := 4/5
def cA : ℚ := 3/4
def cS : ℚ := 2/3
def cZ : ℚ := 1/2
def n₁ : ℕ := 3
def n₀ : ℕ := 5
def nE : ℕ := 8

/-- The occurrences: the first warrant's three forms and the second warrant on `Z`. -/
def occP : Occurrence 5 := Fixture2.occP cP
def occA : Occurrence 5 := Fixture2.occA cA
def occS : Occurrence 5 := Fixture2.occS cS
def occZ : Occurrence 5 := Fixture2.occZ cZ
def grounds : Grounds 5 := [occP, occA, occS, occZ]

/-- The coherence row `X∧A ≤ X`, strength one. -/
def coh : StrItem 5 := ⟨⟨![-1, 1, 0, 0, 0], 0⟩, .coherence, 0⟩

lemma coh_satR_iff (x : Fin 5 → ℝ) : coh.row.SatR x ↔ x XA ≤ x X := by
  simp only [coh, Row.SatR, Fin.sum_univ_five]
  simp

/-- **C1.**  The seed: the first warrant's three forms as substantive items, the coherence
row as the one structural item, the constitutive layer empty. -/
def seedC1 : Seed 5 Unit := ⟨[occP.toSub, occA.toSub, occS.toSub], [coh], ⟨∅, ∅⟩⟩

theorem seedC1_humble : seedC1.HumbleItems := by
  unfold Seed.HumbleItems seedC1
  simp [Occurrence.toSub, occP, occA, occS, Fixture2.occP, Fixture2.occA, Fixture2.occS,
    Form.c, cP, cA, cS]
  norm_num

/-- The second warrant, as the warrant list `W` of the forced bundle. -/
def W : List (SubItem 5) := [occZ.toSub]

/-- The settlement at date `n`: `X` from `n₁`; from `nE` the refutation of `Y` and its closure. -/
def settlementAt (n : ℕ) : Settlement 5 :=
  ⟨![if n₁ ≤ n then some true else none, none, if nE ≤ n then some false else none,
     if nE ≤ n then some false else none, none]⟩

/-- The docket at date `n`: port `2` defeated from `n₀`. -/
def docketAt (n : ℕ) : DocketState := ⟨if n₀ ≤ n then {2} else ∅, ∅⟩

/-- The first warrant's surviving forms at date `n`: the premise always, the applicability
and the strength that cites it until the undercut at `n₀`. -/
def firstWarrantAt (n : ℕ) : List (SubItem 5) :=
  occP.toSub :: (if n < n₀ then [occA.toSub, occS.toSub] else [])

/-- The seed at date `n`. -/
def seedAt (n : ℕ) : Seed 5 Unit := ⟨firstWarrantAt n, [coh], ⟨∅, ∅⟩⟩

theorem seedAt_zero : seedAt 0 = seedC1 := by
  simp [seedAt, seedC1, firstWarrantAt, n₀, nE]

/-! ### The rule produces the seed -/

theorem outcome_occP (n : ℕ) : settleOutcome (settlementAt n) occP.form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occP, Fixture2.occP]

theorem outcome_occA (n : ℕ) : settleOutcome (settlementAt n) occA.form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occA, Fixture2.occA]

theorem outcome_occS (n : ℕ) :
    settleOutcome (settlementAt n) occS.form = (if nE ≤ n then .rebutted else .kept) := by
  simp [settleOutcome, pinsFalse, settlementAt, occS, Fixture2.occS]

theorem outcome_occZ (n : ℕ) : settleOutcome (settlementAt n) occZ.form = .kept := by
  simp [settleOutcome, pinsFalse, settlementAt, occZ, Fixture2.occZ]

@[simp] lemma occP_id : occP.id = 1 := rfl
@[simp] lemma occA_id : occA.id = 2 := rfl
@[simp] lemma occS_id : occS.id = 3 := rfl
@[simp] lemma occZ_id : occZ.id = 4 := rfl
@[simp] lemma occP_cites : occP.cites = .none := rfl
@[simp] lemma occA_cites : occA.cites = .occurrence 1 := rfl
@[simp] lemma occS_cites : occS.cites = .occurrence 2 := rfl
@[simp] lemma occZ_cites : occZ.cites = .none := rfl
@[simp] lemma occP_defeaters : occP.defeaters = ∅ := rfl
@[simp] lemma occA_defeaters : occA.defeaters = ∅ := rfl
@[simp] lemma occS_defeaters : occS.defeaters = {2} := rfl
@[simp] lemma occZ_defeaters : occZ.defeaters = ∅ := rfl

lemma mem_docketAt_iff (n j : ℕ) : j ∈ (docketAt n).defeated ↔ n₀ ≤ n ∧ j = 2 := by
  simp only [docketAt]
  split_ifs with h <;> simp [h]

/-- **The survivors, date by date**: the strength occurrence leaves at the undercut with the
applicability it cites, before `Y` is refuted. -/
theorem survivors_eq (n : ℕ) :
    grounds.survivors (docketAt n) (settlementAt n) =
      occP :: ((if n < n₀ then [occA, occS] else []) ++ [occZ]) := by
  have hP := outcome_occP n; have hA := outcome_occA n; have hS := outcome_occS n
  have hZ := outcome_occZ n
  unfold Grounds.survivors
  rw [activeIds_of_length _ _ _ 4 rfl, iterate_four]
  by_cases h0 : n < n₀
  · have hE : n < nE := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [activeStep, liveGiven, undercut, citesIn, grounds, hP, hA, hS, hZ, mem_docketAt_iff,
      h0, hE, show ¬ n₀ ≤ n from not_le.mpr h0, show ¬ nE ≤ n from not_le.mpr hE]
  · simp [activeStep, liveGiven, undercut, citesIn, grounds, hP, hA, hS, hZ, mem_docketAt_iff,
      h0, show n₀ ≤ n from not_lt.mp h0]

/-- **C2–C6, the rule produces the seed**: the seed's substantive items and the warrant list
are the survivors' items, at every date. -/
theorem seedAt_eq_survivors (n : ℕ) :
    (seedAt n).sub ++ W = (grounds.survivors (docketAt n) (settlementAt n)).map Occurrence.toSub := by
  rw [survivors_eq]
  simp only [seedAt, firstWarrantAt, W, List.map_append, List.map_cons, List.map_nil]
  by_cases h0 : n < n₀ <;> simp [h0]

/-! ### The real region, date by date -/

/-- The real forced region at date `n`, read as inequalities. -/
theorem regionRAt_iff (n : ℕ) (x : Fin 5 → ℝ) :
    forcedRegionR (seedAt n) W DocketState.quiet (settlementAt n) x ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) ∧
      (4/5 : ℝ) ≤ x X ∧ (n < n₀ → (3/4 : ℝ) * x X ≤ x XA) ∧
      (n < n₀ → (2/3 : ℝ) * x XA ≤ x XAY) ∧ x XA ≤ x X ∧ (1/2 : ℝ) ≤ x Z := by
  rw [forcedRegionR_iff]
  have hpin : (settlementAt n).PinnedR x ↔
      (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) := by
    unfold Settlement.PinnedR settlementAt
    constructor
    · intro h
      refine ⟨fun h₁ => ?_, fun hE => ⟨?_, ?_⟩⟩
      · simpa [truth, h₁] using h X true (by simp [h₁])
      · simpa [truth, hE] using h XAY false (by simp [hE])
      · simpa [truth, hE] using h Y false (by simp [hE])
    · rintro ⟨h₁, hE⟩ i b hi
      fin_cases i <;> simp_all [truth] <;> split_ifs at hi <;> simp_all
  have hsub : (∀ it ∈ (seedAt n).liveSub DocketState.quiet ++ W, it.form.row.SatR x) ↔
      ((4/5 : ℝ) ≤ x X ∧ (n < n₀ → (3/4 : ℝ) * x X ≤ x XA) ∧
        (n < n₀ → (2/3 : ℝ) * x XA ≤ x XAY) ∧ (1/2 : ℝ) ≤ x Z) := by
    simp only [seedAt, Seed.liveSub, firstWarrantAt, W, DocketState.quiet, Finset.notMem_empty,
      not_false_eq_true, decide_true, List.filter_cons_of_pos, List.filter_append,
      List.filter_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Occurrence.toSub, occP, occA, occS, occZ, Fixture2.occP, Fixture2.occA, Fixture2.occS,
      Fixture2.occZ]
    by_cases h0 : n < n₀ <;>
      simp [h0, premise_satR_iff, applicability_satR_iff, strength_satR_iff, cP, cA, cS, cZ,
        List.filter_cons, or_assoc, forall_eq_or_imp, forall_eq]
  have hstr : (∀ it ∈ (seedAt n).liveStr DocketState.quiet, it.row.SatR x) ↔ x XA ≤ x X := by
    simp [seedAt, Seed.liveStr, DocketState.quiet, coh_satR_iff]
  rw [hpin, hsub, hstr]
  tauto

/-- The point family `(1, 1, a, a, z)` with `a = 1` before the refutation and `0` after. -/
def ptZ (n : ℕ) (z : ℝ) : Fin 5 → ℝ := ![1, 1, if n < nE then 1 else 0, if n < nE then 1 else 0, z]

lemma ptZ_mem (n : ℕ) (z : ℝ) (hz0 : (1/2 : ℝ) ≤ z) (hz1 : z ≤ 1) :
    forcedRegionR (seedAt n) W DocketState.quiet (settlementAt n) (ptZ n z) := by
  rw [regionRAt_iff]
  refine ⟨fun i => ?_, fun _ => ?_, fun hn => ?_, ?_, fun _ => ?_, fun hlt => ?_, ?_, ?_⟩
  · fin_cases i <;> simp [ptZ] <;>
      first | (split_ifs <;> norm_num) | (constructor <;> linarith) | norm_num
  · simp [ptZ]
  · simp [ptZ, not_lt.mpr hn]
  · simp [ptZ] <;> norm_num
  · simp [ptZ] <;> norm_num
  · have hE : n < nE := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [ptZ, hE] <;> norm_num
  · simp [ptZ] <;> split_ifs <;> norm_num
  · simpa [ptZ] using hz0

/-- The interval computed at date `n` on coordinate `φ`. -/
def intervalAt (n : ℕ) (φ : Fin 5) : ℚ × ℚ :=
  forcedInterval (seedAt n) W DocketState.quiet (settlementAt n) φ

/-- **C3/C7: the interval on `Z` is `[1/2, 1]` at every date** — the second warrant is
untouched by everything that happens to the first. -/
theorem interval_Z (n : ℕ) : intervalAt n Z = (1/2, 1) := by
  unfold intervalAt
  refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ (ptZ n (1/2)) (ptZ_mem n _ le_rfl (by norm_num))
    (by simp [ptZ]) (ptZ n 1) (ptZ_mem n _ (by norm_num) le_rfl) (by simp [ptZ])
  · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact hx.2.2.2.2.2.2.2
  · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 Z).2

/-- **The interval on `X∧A∧Y`, by phase**: `[2/5, 1]` at entry, `[1/2, 1]` once `X` settles,
`[0, 1]` once the applicability port is defeated, `[0, 0]` once `Y` is refuted. -/
theorem interval_XAY (n : ℕ) :
    intervalAt n XAY =
      (if n < n₁ then ((2/5 : ℚ), (1 : ℚ)) else if n < n₀ then (1/2, 1)
        else if n < nE then (0, 1) else (0, 0)) := by
  unfold intervalAt
  by_cases h1 : n < n₁
  · have h0 : n < n₀ := by unfold n₁ n₀ at *; omega
    have hE : n < nE := by unfold n₁ nE at *; omega
    simp only [h1, if_true]
    refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![4/5, 3/5, 2/5, 1, 1/2] ?_ (by simp)
      ![1, 1, 1, 1, 1] ?_ (by simp)
    · intro x hx; rw [regionRAt_iff] at hx; push_cast
      obtain ⟨-, -, -, hP, hA, hS, -, -⟩ := hx
      have := hA h0; have := hS h0; linarith
    · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XAY).2
    · rw [regionRAt_iff]
      simp [Fin.forall_fin_succ, not_le.mpr h1, not_le.mpr hE, h0, hE] <;> norm_num
    · rw [regionRAt_iff]
      simp [Fin.forall_fin_succ, not_le.mpr hE, h0, hE] <;> norm_num
  · by_cases h0 : n < n₀
    · have hE : n < nE := by unfold n₀ nE at *; omega
      have hn₁ : n₁ ≤ n := not_lt.mp h1
      simp only [h1, h0, if_false, if_true]
      refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![1, 3/4, 1/2, 1, 1/2] ?_ (by simp)
        ![1, 1, 1, 1, 1] ?_ (by simp)
      · intro x hx; rw [regionRAt_iff] at hx; push_cast
        obtain ⟨-, hX, -, -, hA, hS, -, -⟩ := hx
        have := hX hn₁; have := hA h0; have := hS h0; linarith
      · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XAY).2
      · rw [regionRAt_iff]
        simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
      · rw [regionRAt_iff]
        simp [Fin.forall_fin_succ, not_le.mpr hE, h0, hE] <;> norm_num
    · by_cases hE : n < nE
      · have hn₁ : n₁ ≤ n := not_lt.mp h1
        simp only [h1, h0, hE, if_false, if_true]
        refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![1, 0, 0, 1, 1/2] ?_ (by simp)
          ![1, 1, 1, 1, 1] ?_ (by simp)
        · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XAY).1
        · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XAY).2
        · rw [regionRAt_iff]
          simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
        · rw [regionRAt_iff]
          simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
      · have hn₁ : n₁ ≤ n := not_lt.mp h1
        have hnE : nE ≤ n := not_lt.mp hE
        simp only [h1, h0, hE, if_false]
        refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![1, 0, 0, 0, 1/2] ?_ (by simp)
          ![1, 0, 0, 0, 1/2] ?_ (by simp)
        · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XAY).1
        · intro x hx; rw [regionRAt_iff] at hx; push_cast
          have := (hx.2.2.1 hnE).1; linarith
        · rw [regionRAt_iff]
          simp [Fin.forall_fin_succ, hn₁, hnE, h0, hE] <;> norm_num
        · rw [regionRAt_iff]
          simp [Fin.forall_fin_succ, hn₁, hnE, h0, hE] <;> norm_num

/-- **The interval on `X∧A`, by phase**: `[3/5, 1]`, `[3/4, 1]`, then `[0, 1]` from the
undercut on — and still `[0, 1]` after the rebuttal: the removed strength row had forced
nothing on `X∧A` at the pre-step settlement, so the reopening widens it by `0`, which is
exactly what A4(b) allows.  Under the port-only rule the same step pins `X∧A` to `0`. -/
theorem interval_XA (n : ℕ) :
    intervalAt n XA =
      (if n < n₁ then ((3/5 : ℚ), (1 : ℚ)) else if n < n₀ then (3/4, 1) else (0, 1)) := by
  unfold intervalAt
  by_cases h1 : n < n₁
  · have h0 : n < n₀ := by unfold n₁ n₀ at *; omega
    have hE : n < nE := by unfold n₁ nE at *; omega
    simp only [h1, if_true]
    refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![4/5, 3/5, 2/5, 1, 1/2] ?_ (by simp)
      ![1, 1, 1, 1, 1] ?_ (by simp)
    · intro x hx; rw [regionRAt_iff] at hx; push_cast
      obtain ⟨-, -, -, hP, hA, -, -, -⟩ := hx
      have := hA h0; linarith
    · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XA).2
    · rw [regionRAt_iff]
      simp [Fin.forall_fin_succ, not_le.mpr h1, not_le.mpr hE, h0, hE] <;> norm_num
    · rw [regionRAt_iff]
      simp [Fin.forall_fin_succ, not_le.mpr hE, h0, hE] <;> norm_num
  · by_cases h0 : n < n₀
    · have hE : n < nE := by unfold n₀ nE at *; omega
      have hn₁ : n₁ ≤ n := not_lt.mp h1
      simp only [h1, h0, if_false, if_true]
      refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_ ![1, 3/4, 1/2, 1, 1/2] ?_ (by simp)
        ![1, 1, 1, 1, 1] ?_ (by simp)
      · intro x hx; rw [regionRAt_iff] at hx; push_cast
        obtain ⟨-, hX, -, -, hA, -, -, -⟩ := hx
        have := hX hn₁; have := hA h0; linarith
      · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XA).2
      · rw [regionRAt_iff]
        simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
      · rw [regionRAt_iff]
        simp [Fin.forall_fin_succ, not_le.mpr hE, h0, hE] <;> norm_num
    · have hn₁ : n₁ ≤ n := not_lt.mp h1
      simp only [h1, h0, if_false]
      refine forcedInterval_eq_of_bounds _ _ _ _ _ _ _ ?_ ?_
        ![1, 0, 0, if n < nE then 1 else 0, 1/2] ?_ (by simp)
        ![1, 1, if n < nE then 1 else 0, if n < nE then 1 else 0, 1/2] ?_ (by simp)
      · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XA).1
      · intro x hx; rw [regionRAt_iff] at hx; push_cast; exact (hx.1 XA).2
      · rw [regionRAt_iff]
        by_cases hE : n < nE
        · simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
        · simp [Fin.forall_fin_succ, hn₁, not_lt.mp hE, h0, hE] <;> norm_num
      · rw [regionRAt_iff]
        by_cases hE : n < nE
        · simp [Fin.forall_fin_succ, hn₁, not_le.mpr hE, h0, hE] <;> norm_num
        · simp [Fin.forall_fin_succ, hn₁, not_lt.mp hE, h0, hE] <;> norm_num

/-- **C4, nested per A4(a)**: the settlement of `X` at `n₁` removes no row and shrinks every
interval: `[3/5, 1] → [3/4, 1]` on `X∧A`, `[2/5, 1] → [1/2, 1]` on `X∧A∧Y`, `Z` unchanged. -/
theorem settlement_nests :
    (intervalAt n₁ XA).1 ≥ (intervalAt 0 XA).1 ∧ (intervalAt n₁ XA).2 ≤ (intervalAt 0 XA).2 ∧
    (intervalAt n₁ XAY).1 ≥ (intervalAt 0 XAY).1 ∧ (intervalAt n₁ XAY).2 ≤ (intervalAt 0 XAY).2 ∧
    intervalAt n₁ Z = intervalAt 0 Z ∧
    grounds.survivors (docketAt n₁) (settlementAt n₁) =
      grounds.survivors (docketAt 0) (settlementAt 0) := by
  rw [interval_XA, interval_XA, interval_XAY, interval_XAY, interval_Z, interval_Z,
    survivors_eq, survivors_eq]
  simp [n₁, n₀, nE]
  norm_num

/-- **C5, the undercut widens** (`defeat_widens`): the defeat of port `2` at `n₀` moves
`X∧A` from `[3/4, 1]` to `[0, 1]`. -/
theorem undercut_widens : intervalAt n₀ XA = (0, 1) ∧ intervalAt (n₀ - 1) XA = (3/4, 1) := by
  rw [interval_XA, interval_XA]; simp [n₁, n₀]

/-- **C6, the rebuttal**: at `nE` the strength occurrence leaves by `settleForm`; `X∧A`'s
interval does not move (`[0, 1]` before and after — the reopening bound is attained with
widening `0`); `X∧A∧Y` is pinned; `Z` is unchanged. -/
theorem rebuttal_step :
    settleOutcome (settlementAt nE) occS.form = .rebutted ∧
    settleOutcome (settlementAt (nE - 1)) occS.form = .kept ∧
    intervalAt nE XA = intervalAt (nE - 1) XA ∧
    intervalAt nE XAY = (0, 0) ∧ intervalAt nE Z = intervalAt (nE - 1) Z := by
  rw [outcome_occS, outcome_occS, interval_XA, interval_XA, interval_XAY, interval_Z, interval_Z]
  simp [n₁, n₀, nE]

/-- **Under the port-only rule the same step pins `X∧A` to `0`** (the orphan pin): with the
strength row present and `X∧A∧Y` pinned to `0`, every region point has `X∧A = 0`. -/
theorem old_rule_pins :
    ∀ x, grounds.region (docketAt nE) (settlementAt nE) x → x XA = 0 := by
  intro x hx
  rw [Grounds.region_iff] at hx
  obtain ⟨hc, hpin, h⟩ := hx
  have hS := h occS (by simp [grounds]) (by simp [mem_docketAt_iff])
  simp only [occS, Fixture2.occS] at hS
  rw [Form.strength_sat_iff] at hS
  have h2 : x XAY = 0 := by simpa [truth] using hpin XAY false (by simp [settlementAt, nE])
  rw [h2] at hS
  have := (hc XA).1
  unfold cS at hS
  linarith

/-! ### Licences (C2, C5) -/

/-- The lower certificate for the bound on `X∧A∧Y` at entry: multipliers `c_S c_A, c_S, 1`
on the premise, applicability and strength rows. -/
def certXAY_lo : BoundCert 5 3 XAY (-1) where
  mult := ![cS * cA, cS, 1]
  row := ![specialize (settlementAt 0) occP.form.row, specialize (settlementAt 0) occA.form.row,
    specialize (settlementAt 0) occS.form.row]
  mult_nonneg := fun i => by fin_cases i <;> simp [cS, cA] <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;>
      simp [Fin.sum_univ_three, specialize, settlementAt, n₁, nE, occP, occA, occS, Fixture2.occP,
        Fixture2.occA, Fixture2.occS, Form.row, cS, cA, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num

/-- The upper certificate: the cube face. -/
def cert_hi (φ : Fin 5) : BoundCert 5 1 φ 1 where
  mult := fun _ => 1
  row := fun _ => cubeUpper φ
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by simp [cubeUpper]

/-- The verdict certificate on `X∧A∧Y` at entry, citing occurrences `1, 2, 3`. -/
def certXAY : VerdictCert 5 3 1 XAY where
  lo := certXAY_lo
  hi := cert_hi XAY
  loCite := ![Cite.sub 1, Cite.sub 2, Cite.sub 3]
  hiCite := fun _ => Cite.settled XAY
  loPoint := ![4/5, 3/5, 2/5, 1, 1/2]
  hiPoint := ![1, 1, 1, 1, 1]

/-- The lower certificate for the bound on `Z` at date `n`: multiplier `1` on the `Z` row. -/
def certZ_lo (n : ℕ) : BoundCert 5 1 Z (-1) where
  mult := fun _ => 1
  row := fun _ => specialize (settlementAt n) occZ.form.row
  mult_nonneg := fun _ => by norm_num
  coeff_sum := fun j => by
    fin_cases j <;> simp [specialize, settlementAt, occZ, Fixture2.occZ, Form.row, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      split_ifs <;> simp

/-- The verdict certificate on `Z` at date `n`, citing occurrence `4`. -/
def certZ (n : ℕ) : VerdictCert 5 1 1 Z where
  lo := certZ_lo n
  hi := cert_hi Z
  loCite := fun _ => Cite.sub 4
  hiCite := fun _ => Cite.settled Z
  loPoint := ![1, 1, if n < nE then 1 else 0, if n < nE then 1 else 0, 1/2]
  hiPoint := ![1, 1, if n < nE then 1 else 0, if n < nE then 1 else 0, 1]

/-- The record at date `n`, with event `7` authorized. -/
def recordAt (n : ℕ) : RecordState 5 := ⟨grounds, docketAt n, settlementAt n, {7}⟩

/-- The settled region at date `n`, read as inequalities on rational points. -/
theorem settledRegion_iff (n : ℕ) (x : Fin 5 → ℚ) :
    grounds.settledRegion (docketAt n) (settlementAt n) x ↔
      InCube x ∧ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) ∧
      cP ≤ x X ∧ (n < n₀ → cA * x X ≤ x XA) ∧ (n < n₀ → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z := by
  rw [Grounds.settledRegion_iff, survivors_eq]
  have hpin : (settlementAt n).Pinned x ↔ (n₁ ≤ n → x X = 1) ∧ (nE ≤ n → x XAY = 0 ∧ x Y = 0) := by
    unfold Settlement.Pinned settlementAt
    constructor
    · intro h
      refine ⟨fun h₁ => ?_, fun hE => ⟨?_, ?_⟩⟩
      · simpa [truth, h₁] using h X true (by simp [h₁])
      · simpa [truth, hE] using h XAY false (by simp [hE])
      · simpa [truth, hE] using h Y false (by simp [hE])
    · rintro ⟨h₁, hE⟩ i b hi
      fin_cases i <;> simp_all [truth] <;> split_ifs at hi <;> simp_all
  have hrows : (∀ o ∈ occP :: ((if n < n₀ then [occA, occS] else []) ++ [occZ]),
      o.form.row.Sat x) ↔
      (cP ≤ x X ∧ (n < n₀ → cA * x X ≤ x XA) ∧ (n < n₀ → cS * x XA ≤ x XAY) ∧ cZ ≤ x Z) := by
    by_cases h0 : n < n₀ <;>
      simp [h0, occP, occA, occS, occZ, Fixture2.occP, Fixture2.occA, Fixture2.occS,
        Fixture2.occZ, Form.premise_sat_iff, Form.applicability_sat_iff, Form.strength_sat_iff]
  unfold regionOn
  rw [hpin, hrows]
  tauto

lemma mem_settledBundle_sub (n : ℕ) (o : Occurrence 5)
    (ho : o ∈ grounds.survivors (docketAt n) (settlementAt n)) :
    (⟨Cite.sub o.id, specialize (settlementAt n) o.form.row⟩ : CitedRow (Cite 5) 5) ∈
      grounds.settledBundle (docketAt n) (settlementAt n) :=
  (mem_settledBundle_iff _ _ _ _).2 (Or.inl ⟨o, ho, rfl⟩)

/-- **C2: both certificates are licensed at entry.** -/
theorem licensed_at_entry :
    Licensed (recordAt 0) XAY (2/5) certXAY 7 ∧ Licensed (recordAt 0) Z (1/2) (certZ 0) 7 := by
  have hs : grounds.survivors (docketAt 0) (settlementAt 0) = [occP, occA, occS, occZ] := by
    rw [survivors_eq]; simp [n₀]
  refine ⟨⟨⟨⟨fun i _ => ?_, fun _ _ => Or.inr (Or.inl ⟨XAY, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
    by simp [recordAt]⟩, ⟨⟨⟨fun _ _ => ?_, fun _ _ => Or.inr (Or.inl ⟨Z, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩, by simp [recordAt]⟩⟩
  · -- the three cited rows are in the bundle
    fin_cases i
    · exact Or.inl (mem_settledBundle_sub 0 occP (by simp [hs]))
    · exact Or.inl (mem_settledBundle_sub 0 occA (by simp [hs]))
    · exact Or.inl (mem_settledBundle_sub 0 occS (by simp [hs]))
  · -- lower value
    simp [certXAY, certXAY_lo, BoundCert.value, Fin.sum_univ_three, specialize, settlementAt, n₁, nE,
      occP, occA, occS, Fixture2.occP, Fixture2.occA, Fixture2.occS, Form.row, settledTerm, cS, cA, cP, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
  · simp [certXAY, cert_hi, BoundCert.value, cubeUpper] <;> norm_num
  · show grounds.settledRegion (docketAt 0) (settlementAt 0) ![4/5, 3/5, 2/5, 1, 1/2]
    rw [settledRegion_iff]
    simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp [certXAY, certXAY_lo, BoundCert.value, Fin.sum_univ_three, specialize, settlementAt, n₁, nE,
      occP, occA, occS, Fixture2.occP, Fixture2.occA, Fixture2.occS, Form.row, settledTerm, cS, cA, cP, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
  · show grounds.settledRegion (docketAt 0) (settlementAt 0) ![1, 1, 1, 1, 1]
    rw [settledRegion_iff]
    simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp [certXAY, cert_hi, BoundCert.value, cubeUpper] <;> norm_num
  · exact Or.inl (mem_settledBundle_sub 0 occZ (by simp [hs]))
  · simp [certZ, certZ_lo, BoundCert.value, specialize, settlementAt, n₁, nE, occZ, Fixture2.occZ,
      Form.row, settledTerm, cZ, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
  · simp [certZ, cert_hi, BoundCert.value, cubeUpper] <;> norm_num
  · show grounds.settledRegion (docketAt 0) (settlementAt 0) ![1, 1, if 0 < nE then 1 else 0, if 0 < nE then 1 else 0, 1/2]
    rw [settledRegion_iff]
    simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp [certZ, certZ_lo, BoundCert.value, specialize, settlementAt, n₁, nE, occZ, Fixture2.occZ,
      Form.row, settledTerm, cZ, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
  · show grounds.settledRegion (docketAt 0) (settlementAt 0) ![1, 1, if 0 < nE then 1 else 0, if 0 < nE then 1 else 0, 1]
    rw [settledRegion_iff]
    simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
  · simp [certZ, cert_hi, BoundCert.value, cubeUpper] <;> norm_num

/-- **C2 through the record**: `decideLicensed` answers `true` at entry. -/
theorem decideLicensed_at_entry (β : ℚ) (run : MarketRun 5) (hrun : (trace run β 0).state = recordAt 0) :
    decideLicensed (trace run β) 0 XAY (2/5) certXAY 7 = true ∧
    decideLicensed (trace run β) 0 Z (1/2) (certZ 0) 7 = true := by
  rw [decideLicensed_iff, decideLicensed_iff, hrun]
  exact licensed_at_entry

/-- **C5: after the undercut, the certificate citing the applicability occurrence is not
supported** — its second positively weighted row is cited into a bundle that carries no row
under `Cite.sub 2`, and the row is no cube face — **while a fresh certificate on `Z` is.** -/
theorem undercut_licences :
    ¬ Supported grounds (docketAt n₀) (settlementAt n₀) XAY (1/2) certXAY ∧
    Licensed (recordAt n₀) Z (1/2) (certZ n₀) 7 := by
  have hs : grounds.survivors (docketAt n₀) (settlementAt n₀) = [occP, occZ] := by
    rw [survivors_eq]; simp
  constructor
  · rintro ⟨⟨hlo, -⟩, -⟩
    have h := hlo 1 (by simp [certXAY, certXAY_lo, cS] <;> norm_num)
    rcases h with h | ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [mem_settledBundle_iff, hs] at h
      rcases h with ⟨o, ho, heq⟩ | ⟨i, r, hr, heq⟩
      · have hc := congrArg CitedRow.cites heq
        simp only [certXAY] at hc
        simp at hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> simp at hc
      · have hc := congrArg CitedRow.cites heq
        simp [certXAY] at hc
    · have := congrArg (fun r : Row 5 => r.a X) hi
      simp [certXAY, certXAY_lo, cubeUpper, specialize, settlementAt, n₁, nE, occA, Fixture2.occA,
        Form.row, cA, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] at this
      split_ifs at this <;> norm_num at this
    · have := congrArg (fun r : Row 5 => r.a X) hi
      simp [certXAY, certXAY_lo, cubeLower, specialize, settlementAt, n₁, nE, occA, Fixture2.occA,
        Form.row, cA, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] at this
      split_ifs at this <;> norm_num at this
  · refine ⟨⟨⟨fun _ _ => ?_, fun _ _ => Or.inr (Or.inl ⟨Z, rfl⟩)⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩,
      by simp [recordAt]⟩
    · exact Or.inl (mem_settledBundle_sub n₀ occZ (by simp [hs]))
    · simp [certZ, certZ_lo, BoundCert.value, specialize, settlementAt, n₁, nE, n₀, occZ,
        Fixture2.occZ, Form.row, settledTerm, cZ, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
    · simp [certZ, cert_hi, BoundCert.value, cubeUpper] <;> norm_num
    · show grounds.settledRegion (docketAt n₀) (settlementAt n₀) _
      rw [settledRegion_iff]
      simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
    · simp [certZ, certZ_lo, BoundCert.value, specialize, settlementAt, n₁, nE, n₀, occZ,
        Fixture2.occZ, Form.row, settledTerm, cZ, Fin.sum_univ_five, Option.elim, truth, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;>
      norm_num
    · show grounds.settledRegion (docketAt n₀) (settlementAt n₀) _
      rw [settledRegion_iff]
      simp [certXAY, certZ, InCube, Fin.forall_fin_succ, n₁, n₀, nE, cP, cA, cS, cZ, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z] <;> norm_num
    · simp [certZ, cert_hi, BoundCert.value, cubeUpper] <;> norm_num

/-! ### The force schedule and the bankroll -/

section Force

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementPreservation
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement
open Fixture (X A Y XA XAY wAY allTrue_live_before holds_negY wAY_X wAY_A wAY_notY
  ratPayout_X ratPayout_XA ratPayout_XAY)

/-- The sentence `Z`. -/
def Zs : Sentence := .atom 3

@[simp] lemma Zs_ne_X : Zs ≠ Fixture.X := by simp [Zs, Fixture.X]
@[simp] lemma Zs_ne_XA : Zs ≠ Fixture.XA := by simp [Zs, Fixture.XA]
@[simp] lemma Zs_ne_XAY : Zs ≠ Fixture.XAY := by simp [Zs, Fixture.XAY, Fixture.XA]
@[simp] lemma Zs_ne_Y : Zs ≠ Fixture.Y := by simp [Zs, Fixture.Y]
@[simp] lemma X_ne_Zs : Fixture.X ≠ Zs := by simp [Zs, Fixture.X]
@[simp] lemma XA_ne_Zs : Fixture.XA ≠ Zs := by simp [Zs, Fixture.XA]
@[simp] lemma XAY_ne_Zs : Fixture.XAY ≠ Zs := by simp [Zs, Fixture.XAY, Fixture.XA]
@[simp] lemma Y_ne_Zs : Fixture.Y ≠ Zs := by simp [Zs, Fixture.Y]

/-- The five priced sentences. -/
def coordList5 : List Sentence := [Fixture.X, Fixture.XA, Fixture.XAY, Fixture.Y, Zs]

lemma coordList5_nodup : coordList5.Nodup := by simp [coordList5]

/-- The coordinate map of the five-coordinate seed into the fragment. -/
def ι5 : Fin 5 → Sentence := ![Fixture.X, Fixture.XA, Fixture.XAY, Fixture.Y, Zs]

def pres5 (rows : List Row) : Presentation := ⟨coordList5, coordList5_nodup, rows⟩

@[simp] lemma pres5_rows (rows : List Row) : (pres5 rows).rows = rows := rfl

lemma ι5_mem (j : Fin 5) : ι5 j ∈ (pres5 []).coords := by
  fin_cases j <;> simp [Presentation.coords, pres5, coordList5, ι5]

def β : ℚ := 10
lemma β_nonneg : 0 ≤ β := by norm_num [β]

def premiseRow5 : Row := Fixture.toForceRow ι5 β β_nonneg occP.form.row
def applRow5 : Row := Fixture.toForceRow ι5 β β_nonneg occA.form.row
def strengthRow5 : Row := Fixture.toForceRow ι5 β β_nonneg occS.form.row
def zRow5 : Row := Fixture.toForceRow ι5 β β_nonneg occZ.form.row

/-- The force rows at date `n`: the survivors through the bridge. -/
def rows5 (n : ℕ) : List Row :=
  (grounds.survivors (docketAt n) (settlementAt n)).map fun o =>
    Fixture.toForceRow ι5 β β_nonneg o.form.row

theorem rows5_eq (n : ℕ) :
    rows5 n = premiseRow5 :: ((if n < n₀ then [applRow5, strengthRow5] else []) ++ [zRow5]) := by
  unfold rows5
  rw [survivors_eq]
  by_cases h0 : n < n₀ <;> simp [h0, premiseRow5, applRow5, strengthRow5, zRow5]

/-- The force schedule of the run. -/
def sched5 : ℕ → Presentation := fun n => pres5 (rows5 n)

lemma gap_premise5 (v : PCWorld) :
    rowGap (pres5 []).coords premiseRow5 v = ratPayout v Fixture.X - cP := by
  rw [premiseRow5, Fixture.toForceRow_gap ι5 β β_nonneg _ _ ι5_mem]
  simp [occP, Fixture2.occP, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_appl5 (v : PCWorld) :
    rowGap (pres5 []).coords applRow5 v = ratPayout v Fixture.XA - cA * ratPayout v Fixture.X := by
  rw [applRow5, Fixture.toForceRow_gap ι5 β β_nonneg _ _ ι5_mem]
  simp [occA, Fixture2.occA, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_strength5 (v : PCWorld) :
    rowGap (pres5 []).coords strengthRow5 v =
      ratPayout v Fixture.XAY - cS * ratPayout v Fixture.XA := by
  rw [strengthRow5, Fixture.toForceRow_gap ι5 β β_nonneg _ _ ι5_mem]
  simp [occS, Fixture2.occS, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

lemma gap_z5 (v : PCWorld) : rowGap (pres5 []).coords zRow5 v = ratPayout v Zs - cZ := by
  rw [zRow5, Fixture.toForceRow_gap ι5 β β_nonneg _ _ ι5_mem]
  simp [occZ, Fixture2.occZ, Form.row, Fin.sum_univ_five, ι5, Fixture2.X, Fixture2.XA, Fixture2.XAY, Fixture2.Y, Fixture2.Z]
  ring

open Classical in
lemma ratPayout_Zs (v : PCWorld) : ratPayout v Zs = if v.Holds Zs then 1 else 0 := rfl

/-- The run's odds: `max(4, 3, 2, 1) = 4`. -/
def ρ : ℚ := 4

lemma allTrue_holds_Zs : allTrue.Holds Zs := trivial
lemma wAY_Zs : wAY.Holds Zs := by show (3 : ℕ) ≠ 2; decide

/-- Every row's deficit at every world is dominated at the odds by the all-true world. -/
theorem dominated_allTrue (r : Row) (hr : r ∈ [premiseRow5, applRow5, strengthRow5, zRow5])
    (w : PCWorld) :
    -(rowGap (pres5 []).coords r w) ≤ ρ * rowGap (pres5 []).coords r allTrue := by
  have hX : allTrue.Holds Fixture.X := trivial
  have hA : allTrue.Holds Fixture.A := trivial
  have hY : allTrue.Holds Fixture.Y := trivial
  have hZ := allTrue_holds_Zs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [gap_premise5, gap_premise5, ratPayout_X, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> simp [h, hX, cP, ρ] <;> norm_num
  · rw [gap_appl5, gap_appl5, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      simp [h, h', hX, hA, cA, ρ] <;> norm_num
  · rw [gap_strength5, gap_strength5, ratPayout_XAY, ratPayout_XA, ratPayout_XAY, ratPayout_XA]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      by_cases h'' : w.Holds Fixture.Y <;> simp [h, h', h'', hX, hA, hY, cS, ρ] <;> norm_num
  · rw [gap_z5, gap_z5, ratPayout_Zs, ratPayout_Zs]
    by_cases h : w.Holds Zs <;> simp [h, hZ, cZ, ρ] <;> norm_num

/-- After the rebuttal, the rows then live are dominated at the world `X, A, Z` true, `Y`
false. -/
theorem dominated_wAY (r : Row) (hr : r ∈ [premiseRow5, applRow5, zRow5]) (w : PCWorld) :
    -(rowGap (pres5 []).coords r w) ≤ ρ * rowGap (pres5 []).coords r wAY := by
  have hX := wAY_X; have hA := wAY_A; have hZ := wAY_Zs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [gap_premise5, gap_premise5, ratPayout_X, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> simp [h, hX, cP, ρ] <;> norm_num
  · rw [gap_appl5, gap_appl5, ratPayout_XA, ratPayout_X, ratPayout_XA, ratPayout_X]
    by_cases h : w.Holds Fixture.X <;> by_cases h' : w.Holds Fixture.A <;>
      simp [h, h', hX, hA, cA, ρ] <;> norm_num
  · rw [gap_z5, gap_z5, ratPayout_Zs, ratPayout_Zs]
    by_cases h : w.Holds Zs <;> simp [h, hZ, cZ, ρ] <;> norm_num

lemma mem_rows5 {n : ℕ} {r : Row} (h : r ∈ rows5 n) :
    r ∈ [premiseRow5, applRow5, strengthRow5, zRow5] ∧
      (nE ≤ n → r ∈ [premiseRow5, applRow5, zRow5]) := by
  rw [rows5_eq] at h
  by_cases h0 : n < n₀
  · simp [h0] at h
    refine ⟨?_, fun hn => absurd hn (by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega)⟩
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · simp [h0] at h
    rcases h with rfl | rfl <;> simp

/-- The run's assessment process: the warrant round's, with `Y` refuted at `nE`. -/
def L5 : Assessment := Fixture.L n₁ nE false

lemma wAY_live5 (n : ℕ) : L5.Live n wAY := Fixture.wAY_live n₁ nE n

/-- **The bankroll of the run**: `−3ρ(2 + ρ) = −72` at every live world at every date. -/
theorem liability_run :
    ∀ n (v : PCWorld), L5.Live n v →
      -(3 * (ρ : ℝ) * (2 + ρ)) ≤
        (realizedEnforcer L5 (warrantEnforcer sched5)).netWorth (history L5 (warrantEnforcer sched5)) v n := by
  intro n v hv
  have hρ : (0 : ℚ) ≤ ρ := by norm_num [ρ]
  have hpre : ∀ (w : PCWorld) t, t < nE → ∀ r ∈ (sched5 t).rows,
      -(rowGap (sched5 t).coords r w) ≤ ρ * rowGap (sched5 t).coords r allTrue :=
    fun w t _ r hr => dominated_allTrue r (mem_rows5 hr).1 w
  have hpost : ∀ (w : PCWorld) t, nE ≤ t → ∀ r ∈ (sched5 t).rows,
      -(rowGap (sched5 t).coords r w) ≤ ρ * rowGap (sched5 t).coords r wAY :=
    fun w t ht r hr => dominated_wAY r ((mem_rows5 hr).2 ht) w
  by_cases hn : n < nE
  · have h3 := netWorth_ge_neg_odds L5 sched5 ρ hρ n allTrue (allTrue_live_before n₁ nE false n hn) v
      (fun t ht r hr => hpre v t (by omega) r hr)
    have : -(3 * (ρ : ℝ) * (2 + ρ)) ≤ -(3 * (ρ : ℝ)) := by norm_num [ρ]
    linarith
  · exact netWorth_ge_neg_odds_reopened L5 sched5 ρ hρ (by norm_num [nE]) (not_lt.mp hn) allTrue
      (allTrue_live_before n₁ nE false (nE - 1) (by norm_num [nE])) wAY (wAY_live5 n) v
      (fun t ht r hr => hpre v t ht r hr) (fun t ht r hr => hpre wAY t ht r hr)
      (fun t ht _ r hr => hpost v t ht r hr)

open Workspace.Normativity.Contrib.NormativeInductionInterface in
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol) in
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState) in
/-- **The run's Normative Inductor**: `conditional_normative_inductor` at the run's force
schedule, `liability` discharged by `liability_run`; the computable-market and uptake
hypotheses stay the theorem's own. -/
theorem inductor_run {Occ Req Service : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
    {O : ObligationState S anchor} (E : Evaluation O Service)
    (computableMarket : ComputableMarket (history L5 (warrantEnforcer sched5)))
    (cert : E.PracticalUptake (history L5 (warrantEnforcer sched5))) :
    L5.IsLogicalInductor (history L5 (warrantEnforcer sched5)) ∧
    (0 ≤ E.residual ∧ E.residual ≤ 1) ∧
    E.progress (history L5 (warrantEnforcer sched5)) ≤ E.modulus + E.error + E.D * E.residual :=
  E.conditional_normative_inductor L5 (warrantEnforcer sched5) (3 * (ρ : ℝ) * (2 + ρ))
    liability_run computableMarket cert

end Force

/-! ### The record of the run (C7) -/

/-- The market run with price schedule `p`: grounds, docket and settlement as above, the two
certificates at entry (`7` selected) and a fresh `Z` certificate at `n₀` (`8`), events `7`
and `8` authorized. -/
def run (p : ℕ → Fin 5 → ℚ) : MarketRun 5 where
  grounds _ := grounds
  docket := docketAt
  settlement := settlementAt
  certs n := if n = 0 then [(7, true), (7, true)] else if n = n₀ then [(8, true)] else []
  authorized _ := {7, 8}
  prices := p

/-- A clearing price schedule: `(1, a, a, a, z)` with `a = 1` before the refutation and `0`
after, which lies in the settled region at every date.  It is a stipulated price path, not
the market's output. -/
def clearing (z : ℚ) : ℕ → Fin 5 → ℚ := fun n =>
  ![1, if n < nE then 1 else 0, if n < nE then 1 else 0, if n < nE then 1 else 0, z]

lemma clearing_mem (z : ℚ) (hz0 : cZ ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    grounds.settledRegion (docketAt n) (settlementAt n) (clearing z n) := by
  have hz0' : (1/2 : ℚ) ≤ z := hz0
  rw [settledRegion_iff]
  refine ⟨fun i => ?_, fun _ => ?_, fun hn => ?_, ?_, fun h0 => ?_, fun h0 => ?_, ?_⟩
  · fin_cases i <;> simp [clearing, InCube] <;>
      first | (split_ifs <;> norm_num) | (constructor <;> linarith) | norm_num
  · simp [clearing]
  · simp [clearing, not_lt.mpr hn]
  · simp [clearing, cP] <;> norm_num
  · have hE : n < nE := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [clearing, hE, cA] <;> norm_num
  · have hE : n < nE := by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega
    simp [clearing, hE, cS] <;> norm_num
  · simpa [clearing, cZ] using hz0'

/-- **The record is not injective in the run**: two clearing schedules, one record. -/
theorem trace_not_injective (β : ℚ) :
    run (clearing (1/2)) ≠ run (clearing 1) ∧ trace (run (clearing (1/2))) β = trace (run (clearing 1)) β := by
  constructor
  · intro h
    have := congrArg (fun r : MarketRun 5 => r.prices 0 Z) h
    norm_num [run, clearing] at this
  · funext n
    simp only [trace, run]
    rw [positionOf_eq_zero_of_region _ _ _ _ _ (clearing_mem (1/2) le_rfl (by norm_num [cZ]) n),
      positionOf_eq_zero_of_region _ _ _ _ _ (clearing_mem 1 (by norm_num [cZ]) le_rfl n)]

/-- A run with no undercut. -/
def runNoDefeat (p : ℕ → Fin 5 → ℚ) : MarketRun 5 :=
  { run p with docket := fun _ => DocketState.quiet }

/-- **The record is not constant in the run**: the undercut shows. -/
theorem trace_not_const (β : ℚ) : trace (run (clearing 1)) β ≠ trace (runNoDefeat (clearing 1)) β := by
  intro h
  have := congrArg (fun r : Record 5 => (2 : ℕ) ∈ (r n₀).state.docket.defeated) h
  simp [trace, run, runNoDefeat, docketAt, DocketState.quiet] at this

/-- **The record mediates the docket at every step** of every audited class of runs. -/
theorem docket_mediated (D : Set (MarketRun 5)) (β : ℚ) :
    Workspace.Deference.Contrib.ReasonMediatedAuthorship.ReasonMediated
      (fun (q : MarketRun 5) (_ : Unit) => q) (fun q => trace q β) (fun q => q.docket) D () :=
  docket_mediated_any D β

/-! ### The hull mass of the run (C7) -/

/-- The run's interval data: one reasoner, the computed intervals. -/
def I (n : ℕ) : IntervalData Unit 5 := fun _ φ => intervalAt n φ

/-- The declared fragment and weights: `X∧A`, `X∧A∧Y`, `Z` at `1/3` each. -/
def Φ : Finset (Fin 5) := {XA, XAY, Z}
def w : Fin 5 → ℚ := fun _ => 1/3

lemma hullLo_unit (J : IntervalData Unit 5) (φ : Fin 5) : hullLo J φ = (J () φ).1 := by
  simp [hullLo, Finset.univ_unique]

lemma hullHi_unit (J : IntervalData Unit 5) (φ : Fin 5) : hullHi J φ = (J () φ).2 := by
  simp [hullHi, Finset.univ_unique]

/-- **The hull mass sequence**: `1/2` at entry, `5/12` after `X` settles, `5/6` after the
undercut (the one rise), `1/2` after the rebuttal — and constant from there. -/
theorem hullMass_run (n : ℕ) :
    hullMass (I n) Φ w =
      (if n < n₁ then (1/2 : ℚ) else if n < n₀ then 5/12 else if n < nE then 5/6 else 1/2) := by
  unfold hullMass Φ w hullWidth
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [hullLo_unit, hullHi_unit, I, interval_XA, interval_XAY, interval_Z]
  by_cases h1 : n < n₁ <;> by_cases h0 : n < n₀ <;> by_cases hE : n < nE <;>
    simp [h1, h0, hE] <;> norm_num <;> omega

/-- **C7, eventually constant**: nothing settles after `nE`, and the interval data is the
same at every later date (the finite docket of `eventually_const_of_finite`). -/
theorem eventually_const : ∀ n, nE ≤ n → I n = I nE := by
  intro n hn
  have hs : settlementAt n = settlementAt nE := by
    simp [settlementAt, show n₁ ≤ n by unfold n₁ nE at *; omega, hn, show n₁ ≤ nE by decide]
  have hd : docketAt n = docketAt nE := by
    simp [docketAt, show n₀ ≤ n by unfold n₀ nE at *; omega, show n₀ ≤ nE by decide]
  have hseed : seedAt n = seedAt nE := by
    simp [seedAt, firstWarrantAt, show ¬ n < n₀ by have h5 : n₀ = 5 := rfl; have h8 : nE = 8 := rfl; omega,
      show ¬ nE < n₀ by decide]
  funext u φ
  simp [I, intervalAt, hs, hseed]

/-- The docket's defeated set and the settlement's pinned set grow monotonically: the
hypotheses of `eventually_const_of_finite`. -/
theorem docket_monotone : Monotone fun n => (docketAt n).defeated := by
  intro a b hab j hj
  rw [mem_docketAt_iff] at hj ⊢
  exact ⟨le_trans hj.1 hab, hj.2⟩

/-- The pinned coordinates at date `n`. -/
def pinnedAt (n : ℕ) : Finset (Fin 5) := Finset.univ.filter fun i => ((settlementAt n).val i).isSome

theorem pinned_monotone : Monotone pinnedAt := by
  intro a b hab i hi
  simp only [pinnedAt, Finset.mem_filter, Finset.mem_univ, true_and, settlementAt] at hi ⊢
  fin_cases i <;> simp at hi ⊢ <;> omega

/-! ### C8 — the witness statement -/

open Workspace.Normativity.Contrib.NormativeInductionInterface in
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol) in
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState) in
open LogicalInduction in
open Workspace.Normativity.Contrib.EnforcementPreservation in
/-- **The end-to-end witness** (item 35).  On the fixture's declared quantities: the seed is
humble; both entries are licensed; the augmented market is a logical inductor under the
odds bankroll, with the computable-market and uptake hypotheses exactly as
`conditional_normative_inductor` takes them; the interval on `Z` after `nE` is the value the
elimination computes; and the run's record is neither injective nor constant. -/
theorem witness {Occ Req Service : Type*} {S : Protocol Occ Req} {anchor : Occ → Req}
    {O : ObligationState S anchor} (E : Evaluation O Service) (β : ℚ)
    (computableMarket : ComputableMarket (history L5 (warrantEnforcer sched5)))
    (cert : E.PracticalUptake (history L5 (warrantEnforcer sched5))) :
    seedC1.HumbleItems ∧
    (Licensed (recordAt 0) XAY (2/5) certXAY 7 ∧ Licensed (recordAt 0) Z (1/2) (certZ 0) 7) ∧
    L5.IsLogicalInductor (history L5 (warrantEnforcer sched5)) ∧
    (∀ n, nE ≤ n → intervalAt n Z = (1/2, 1)) ∧
    (run (clearing (1/2)) ≠ run (clearing 1) ∧
      trace (run (clearing (1/2))) β = trace (run (clearing 1)) β) ∧
    trace (run (clearing 1)) β ≠ trace (runNoDefeat (clearing 1)) β :=
  ⟨seedC1_humble, licensed_at_entry, (inductor_run E computableMarket cert).1,
    fun n _ => interval_Z n, trace_not_injective β, trace_not_const β⟩

/-! ### The elimination, run -/

#eval intervalAt 0 XAY
#eval intervalAt 0 Z
#eval intervalAt n₁ XAY
#eval intervalAt n₀ XA
#eval intervalAt nE XA
#eval intervalAt nE XAY
#eval intervalAt nE Z
#eval (grounds.survivors (docketAt nE) (settlementAt nE)).map Occurrence.id
#eval decideLicensed (trace (run (clearing 1)) 1) 0 XAY (2/5) certXAY 7
#eval decideLicensed (trace (run (clearing 1)) 1) 0 Z (1/2) (certZ 0) 7

end Run

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.EndToEndWitness.cast_sum_ite
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.premise_satR_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.applicability_satR_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.strength_satR_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.forcedInterval_eq_of_bounds
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.positionOf_eq_zero_of_region
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.docket_mediated_any
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.cP
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.cA
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.cS
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.cZ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.n₁
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.n₀
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.nE
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occP
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occA
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occS
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occZ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.grounds
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.coh
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.coh_satR_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.seedC1
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.seedC1_humble
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.W
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.settlementAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.docketAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.firstWarrantAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.seedAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.seedAt_zero
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.outcome_occP
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.outcome_occA
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.outcome_occS
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.outcome_occZ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occP_id
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occA_id
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occS_id
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occZ_id
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occP_cites
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occA_cites
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occS_cites
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occZ_cites
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occP_defeaters
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occA_defeaters
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occS_defeaters
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.occZ_defeaters
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.mem_docketAt_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.survivors_eq
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.seedAt_eq_survivors
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.regionRAt_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ptZ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ptZ_mem
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.intervalAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.interval_Z
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.interval_XAY
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.interval_XA
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.settlement_nests
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.undercut_widens
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.rebuttal_step
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.old_rule_pins
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.certXAY_lo
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.cert_hi
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.certXAY
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.certZ_lo
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.certZ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.recordAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.settledRegion_iff
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.mem_settledBundle_sub
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.licensed_at_entry
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.decideLicensed_at_entry
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.undercut_licences
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Zs_ne_X
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Zs_ne_XA
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Zs_ne_XAY
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Zs_ne_Y
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.X_ne_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.XA_ne_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.XAY_ne_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Y_ne_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.coordList5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.coordList5_nodup
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ι5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.pres5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.pres5_rows
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ι5_mem
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.β
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.β_nonneg
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.premiseRow5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.applRow5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.strengthRow5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.zRow5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.rows5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.rows5_eq
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.sched5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.gap_premise5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.gap_appl5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.gap_strength5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.gap_z5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ratPayout_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.ρ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.allTrue_holds_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.wAY_Zs
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.dominated_allTrue
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.dominated_wAY
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.mem_rows5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.L5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.wAY_live5
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.liability_run
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.inductor_run
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.run
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.clearing
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.clearing_mem
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.trace_not_injective
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.runNoDefeat
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.trace_not_const
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.docket_mediated
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.I
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.Φ
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.w
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.hullLo_unit
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.hullHi_unit
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.hullMass_run
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.eventually_const
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.docket_monotone
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.pinnedAt
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.pinned_monotone
#print axioms Workspace.Normativity.Contrib.EndToEndWitness.Run.witness

end Workspace.Normativity.Contrib.EndToEndWitness