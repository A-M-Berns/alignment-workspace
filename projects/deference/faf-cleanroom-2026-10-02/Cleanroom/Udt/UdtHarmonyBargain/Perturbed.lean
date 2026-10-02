import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# `udt-harmony-bargain` — the perturbed game and trembling-hand equilibrium (T3)

Over an arbitrary finite `StrategicGame N ℝ` with EconCSLib's mixed strategies:

* `Floor ε p`: every pure strategy of every player carries weight `≥ ε`.
* `IsPerturbedNash ε p`: `p` has the floor and no player improves by a deviation *within the
  constrained simplex* (EconCSLib's `IsMixedNashEq` checks pure deviations, which are infeasible
  under a floor, so it is not reused for the perturbed game).
* `THPE p*` (SC Def. 10.4, verbatim): an ε-sequence `→ 0`, `ε k > 0`, perturbed equilibria
  `p k` of the uniformly ε k-perturbed game, converging (in the weight vectors) to `p*`.
* `THPESelten`: Selten's general definition with a floor vector `η k i s > 0`; `THPE → THPESelten`.

Theorems: `expectedPayoff_update_eq_sum` (affinity in one player's strategy),
`constrainedBR_iff` (weight above the floor only on pure best responses), `THPE.isMixedNashEq`
(a limit of perturbed equilibria is a mixed Nash equilibrium), `thpe_pure_isNash`,
`thpe_of_unifPert` (the Selten step for the uniform perturbation `s*` with `1 − (K−1)ε` on `s*ᵢ`
and `ε` elsewhere), `thpe_of_dominant`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset StrategicGame Filter Topology

variable {N : Type} [Fintype N] [DecidableEq N]
variable {G : StrategicGame N ℝ} [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]

/-! ### Weights and the expected payoff as a polynomial -/

/-- The weight vectors of a mixed profile, as a point of `∀ i, G.strategy i → ℝ` (the space in
which convergence is taken).
Source: none: infrastructure
Kind: D -/
def profileVal (p : MixedProfile G) : ∀ i, G.strategy i → ℝ := fun i => (p i).val

/-- The expected payoff as a function of the weight vectors: `∑_σ (∏ᵢ xᵢ(σᵢ)) · uᵢ(σ)`.
Source: none: infrastructure (EconCSLib's `expectedPayoff` composed with `profileVal`)
Kind: D -/
def euFun (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)]
    (x : ∀ i, G.strategy i → ℝ) (who : N) : ℝ :=
  ∑ σ : G.Profile, (∏ i, x i (σ i)) * G.payoff σ who

theorem expectedPayoff_eq_euFun (p : MixedProfile G) (who : N) :
    expectedPayoff G p who = euFun G (profileVal p) who := rfl

/-- `euFun` is continuous in the weight vectors (a polynomial).
Source: none: infrastructure
Kind: P -/
theorem continuous_euFun (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)] (who : N) :
    Continuous (fun x : ∀ i, G.strategy i → ℝ => euFun G x who) := by
  unfold euFun
  refine continuous_finset_sum _ fun σ _ => ?_
  refine Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun i _ => (continuous_apply (σ i)).comp (continuous_apply i)

/-- The weight of a pure profile under a mixed profile.
Source: none: infrastructure
Kind: D -/
def profWeight (p : MixedProfile G) (σ : G.Profile) : ℝ := ∏ i, (p i).val (σ i)

/-- The weight the *other* players put on `σ`.
Source: none: infrastructure
Kind: D -/
def oppWeight (p : MixedProfile G) (i : N) (σ : G.Profile) : ℝ :=
  ∏ j ∈ univ.erase i, (p j).val (σ j)

theorem profWeight_nonneg (p : MixedProfile G) (σ : G.Profile) : 0 ≤ profWeight p σ :=
  prod_nonneg fun i _ => (p i).2.1 (σ i)

theorem oppWeight_nonneg (p : MixedProfile G) (i : N) (σ : G.Profile) : 0 ≤ oppWeight p i σ :=
  prod_nonneg fun j _ => (p j).2.1 (σ j)

theorem profWeight_eq (p : MixedProfile G) (i : N) (σ : G.Profile) :
    profWeight p σ = (p i).val (σ i) * oppWeight p i σ :=
  (mul_prod_erase univ (fun j => (p j).val (σ j)) (mem_univ i)).symm

theorem oppWeight_update_left (p : MixedProfile G) (i : N) (q : MixedStrategy G i)
    (σ : G.Profile) : oppWeight (Function.update p i q) i σ = oppWeight p i σ :=
  prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

theorem oppWeight_update_right (p : MixedProfile G) (i : N) (s : G.strategy i)
    (σ : G.Profile) : oppWeight p i (Function.update σ i s) = oppWeight p i σ :=
  prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

theorem profWeight_update (p : MixedProfile G) (i : N) (q : MixedStrategy G i) (σ : G.Profile) :
    profWeight (Function.update p i q) σ = q.val (σ i) * oppWeight p i σ := by
  rw [profWeight_eq _ i, oppWeight_update_left, Function.update_self]

/-- Under a positive floor every pure profile has positive weight.
Source: none: infrastructure
Kind: L -/
theorem profWeight_pos {p : MixedProfile G} {ε : ℝ} (hε : 0 < ε)
    (hfl : ∀ i s, ε ≤ (p i).val s) (σ : G.Profile) : 0 < profWeight p σ :=
  prod_pos fun i _ => lt_of_lt_of_le hε (hfl i (σ i))

/-- The payoff of the pure deviation `s` at `i` against the mixed profile `p` (which players other
than `i` play), written as a full-profile sum: `∑_σ w_p(σ) · uᵢ(σ[i ↦ s])`.
Source: none: infrastructure
Kind: D -/
def pureDev (p : MixedProfile G) (i : N) (s : G.strategy i) : ℝ :=
  ∑ σ : G.Profile, profWeight p σ * G.payoff (Function.update σ i s) i

/-- The fibration identity behind `pureDev`: for a weight `w` summing to one and an `R`
insensitive to coordinate `i`, `∑_σ w(σᵢ) R(σ) F(σ[i ↦ x]) = ∑_{σ : σᵢ = x} R(σ) F(σ)`.
Source: none: infrastructure
Kind: P -/
theorem sum_update_fiber (i : N) (x : G.strategy i) (w : G.strategy i → ℝ) (hw : ∑ y, w y = 1)
    (R F : G.Profile → ℝ) (hR : ∀ σ y, R (Function.update σ i y) = R σ) :
    ∑ σ : G.Profile, w (σ i) * R σ * F (Function.update σ i x) =
      ∑ σ : G.Profile, (if σ i = x then 1 else 0) * R σ * F σ := by
  have hrhs : ∑ σ : G.Profile, (if σ i = x then 1 else 0) * R σ * F σ =
      ∑ σ ∈ univ.filter (fun σ : G.Profile => σ i = x), R σ * F σ := by
    rw [sum_filter]
    refine sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  rw [hrhs]
  have hexp : ∑ σ ∈ univ.filter (fun σ : G.Profile => σ i = x), R σ * F σ =
      ∑ σ ∈ univ.filter (fun σ : G.Profile => σ i = x), ∑ y, w y * (R σ * F σ) := by
    refine sum_congr rfl fun σ _ => ?_
    rw [← sum_mul, hw, one_mul]
  rw [hexp, ← sum_product']
  refine sum_nbij' (fun σ => (Function.update σ i x, σ i)) (fun q => Function.update q.1 i q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro σ _
    simp
  · intro q _
    exact mem_univ _
  · intro σ _
    simp
  · intro q hq
    obtain ⟨h1, -⟩ := mem_product.mp hq
    have h1' : q.1 i = x := (mem_filter.mp h1).2
    refine Prod.ext ?_ ?_
    · simp only [Function.update_idem]
      conv_rhs => rw [← Function.update_eq_self i q.1]
      rw [h1']
    · simp
  · intro σ _
    simp only [hR]
    ring

/-- `pureDev` in the pinned form `∑_{σ : σᵢ = s} oppWeight(σ) uᵢ(σ)`.
Source: none: infrastructure
Kind: L -/
theorem pureDev_eq_ite (p : MixedProfile G) (i : N) (s : G.strategy i) :
    pureDev p i s = ∑ σ : G.Profile, (if σ i = s then 1 else 0) * oppWeight p i σ * G.payoff σ i := by
  unfold pureDev
  rw [← sum_update_fiber i s (p i).val (p i).2.2 (oppWeight p i) (fun σ => G.payoff σ i)
    (fun σ y => oppWeight_update_right p i y σ)]
  refine sum_congr rfl fun σ _ => ?_
  rw [profWeight_eq p i]

/-- A pure deviation's expected payoff is `pureDev`.
Source: none: infrastructure
Kind: L -/
theorem expectedPayoff_update_pure (p : MixedProfile G) (i : N) (s : G.strategy i) :
    expectedPayoff G (Function.update p i (pureToMixed s)) i = pureDev p i s := by
  rw [pureDev_eq_ite]
  unfold expectedPayoff
  refine sum_congr rfl fun σ _ => ?_
  rw [show (∏ j, (Function.update p i (pureToMixed s) j).val (σ j)) =
      profWeight (Function.update p i (pureToMixed s)) σ from rfl, profWeight_update]
  rfl

/-- **Affinity in one player's strategy**: `EU(p[i ↦ q]) = ∑_s q(s) · pureDev p i s`.
Source: mandate T3(i) (`expectedPayoff_update_eq_sum`)
Kind: P
Fidelity: exact -/
theorem expectedPayoff_update_eq_sum (p : MixedProfile G) (i : N) (q : MixedStrategy G i) :
    expectedPayoff G (Function.update p i q) i = ∑ s, q.val s * pureDev p i s := by
  simp_rw [pureDev_eq_ite, mul_sum]
  rw [sum_comm]
  unfold expectedPayoff
  refine sum_congr rfl fun σ _ => ?_
  rw [show (∏ j, (Function.update p i q j).val (σ j)) = profWeight (Function.update p i q) σ from
    rfl, profWeight_update]
  simp [mul_ite, mul_assoc]

/-- `EU(p) = ∑_s pᵢ(s) · pureDev p i s`.
Source: none: infrastructure
Kind: L -/
theorem expectedPayoff_eq_sum (p : MixedProfile G) (i : N) :
    expectedPayoff G p i = ∑ s, (p i).val s * pureDev p i s := by
  conv_lhs => rw [← Function.update_eq_self i p]
  exact expectedPayoff_update_eq_sum p i (p i)

/-! ### The perturbed game and trembling-hand equilibrium -/

/-- Every pure strategy carries weight at least `ε`.
Source: [[superconditioning-mismatched-ontologies]] §10.4 Def. 10.4 ("every strategy is played with
probability at least `ε`")
Kind: D -/
def Floor (ε : ℝ) (p : MixedProfile G) : Prop := ∀ i s, ε ≤ (p i).val s

/-- **Nash equilibrium of the uniformly `ε`-perturbed game `𝒢^ε`**: the floor holds and no player
improves by deviating to a mixed strategy that also respects the floor.
Source: [[superconditioning-mismatched-ontologies]] §10.4 Def. 10.4
Kind: D
Fidelity: exact (deviations range over the constrained simplex, not over pure strategies) -/
def IsPerturbedNash (ε : ℝ) (p : MixedProfile G) : Prop :=
  Floor ε p ∧ ∀ i (q : MixedStrategy G i), (∀ s, ε ≤ q.val s) →
    expectedPayoff G (Function.update p i q) i ≤ expectedPayoff G p i

/-- **Trembling-hand equilibrium (SC Def. 10.4, verbatim)**: there are `ε k > 0` with `ε k → 0`
and Nash equilibria `p k` of `𝒢^{ε k}` whose weight vectors converge to those of `p*`.
Source: [[superconditioning-mismatched-ontologies]] §10.4 Def. 10.4
Kind: D
Fidelity: exact (existential over the ε-sequence; uniform floor; convergence of `profileVal` in the
product topology) -/
def THPE (pStar : MixedProfile G) : Prop :=
  ∃ (ε : ℕ → ℝ) (p : ℕ → MixedProfile G), (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
    (∀ k, IsPerturbedNash (ε k) (p k)) ∧
    Tendsto (fun k => profileVal (p k)) atTop (𝓝 (profileVal pStar))

/-- Selten's general trembling-hand perfection: a floor *vector* `η k i s > 0` with `η k → 0`.
Nothing in this package is refuted against this form.
Source: Selten 1975 (as recalled by [[superconditioning-mismatched-ontologies]] §10.4 and the harmony
ledger; not read)
Kind: D -/
def THPESelten (pStar : MixedProfile G) : Prop :=
  ∃ (η : ℕ → ∀ i, G.strategy i → ℝ) (p : ℕ → MixedProfile G), (∀ k i s, 0 < η k i s) ∧
    Tendsto η atTop (𝓝 0) ∧
    (∀ k, (∀ i s, η k i s ≤ (p k i).val s) ∧ ∀ i (q : MixedStrategy G i),
      (∀ s, η k i s ≤ q.val s) →
        expectedPayoff G (Function.update (p k) i q) i ≤ expectedPayoff G (p k) i) ∧
    Tendsto (fun k => profileVal (p k)) atTop (𝓝 (profileVal pStar))

/-- SC's uniform-floor equilibria are Selten trembling-hand perfect.
Source: [[superconditioning-mismatched-ontologies]] §10.4 (Def. 10.4 as a special case of Selten)
Kind: L -/
theorem THPE.selten {pStar : MixedProfile G} (h : THPE pStar) : THPESelten pStar := by
  obtain ⟨ε, p, hpos, hε, hnash, hconv⟩ := h
  refine ⟨fun k _ _ => ε k, p, fun k _ _ => hpos k, ?_, fun k => ⟨(hnash k).1, (hnash k).2⟩, hconv⟩
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro s
  simpa using hε

/-! ### The constrained best-response characterisation -/

/-- **Constrained best responses** (T3(i)): under a floor `ε ≥ 0`, player `i`'s mixed strategy is a
best response within the constrained simplex iff every pure strategy carrying weight strictly
above the floor is a pure best response to the others.
Source: mandate T3(i) (`constrainedBR_iff`); Selten 1975's characterisation of perturbed equilibria
Kind: P
Fidelity: stronger (needs only `0 ≤ ε` and the floor at `i`, not `ε · card < 1`) -/
theorem constrainedBR_iff (p : MixedProfile G) (i : N) {ε : ℝ} (hε : 0 ≤ ε)
    (hfloor : ∀ s, ε ≤ (p i).val s) :
    (∀ q : MixedStrategy G i, (∀ s, ε ≤ q.val s) →
        expectedPayoff G (Function.update p i q) i ≤ expectedPayoff G p i) ↔
      ∀ s, ε < (p i).val s → ∀ s', pureDev p i s' ≤ pureDev p i s := by
  set f := pureDev p i with hf
  constructor
  · intro h s hs s'
    by_contra hlt
    push_neg at hlt
    have hne : s ≠ s' := fun heq => by rw [heq] at hlt; exact lt_irrefl _ hlt
    set δ := (p i).val s - ε with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    let qv : G.strategy i → ℝ := fun t =>
      (p i).val t - (if t = s then δ else 0) + (if t = s' then δ else 0)
    have hq : qv ∈ stdSimplex ℝ (G.strategy i) := by
      refine ⟨fun t => ?_, ?_⟩
      · simp only [qv]
        have := (p i).2.1 t
        have := hfloor t
        split_ifs <;> subst_vars <;> linarith
      · simp only [qv, sum_add_distrib, sum_sub_distrib, sum_ite_eq', mem_univ, if_true]
        rw [(p i).2.2]; ring
    have hqfl : ∀ t, ε ≤ (⟨qv, hq⟩ : MixedStrategy G i).val t := by
      intro t
      simp only [qv]
      have := hfloor t
      split_ifs <;> subst_vars <;> linarith
    have h1 := h ⟨qv, hq⟩ hqfl
    rw [expectedPayoff_update_eq_sum, expectedPayoff_eq_sum] at h1
    simp only [qv, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_univ, if_true] at h1
    rw [← hf] at h1
    nlinarith
  · intro h q hqfl
    rw [expectedPayoff_update_eq_sum, expectedPayoff_eq_sum, ← hf]
    have hsum : ∑ t, (q.val t - (p i).val t) = 0 := by
      rw [sum_sub_distrib, q.2.2, (p i).2.2]; ring
    by_cases hex : ∃ t₀, ε < (p i).val t₀
    · obtain ⟨t₀, ht₀⟩ := hex
      have hM : ∀ t, f t ≤ f t₀ := h t₀ ht₀
      have key : ∑ t, (q.val t - (p i).val t) * (f t - f t₀) =
          ∑ t, q.val t * f t - ∑ t, (p i).val t * f t := by
        have e1 : ∑ t, (q.val t - (p i).val t) * (f t - f t₀) =
            ∑ t, (q.val t * f t - (p i).val t * f t) - (∑ t, (q.val t - (p i).val t)) * f t₀ := by
          rw [sum_mul, ← sum_sub_distrib]
          refine sum_congr rfl fun t _ => ?_
          ring
        rw [e1, hsum, zero_mul, sub_zero, sum_sub_distrib]
      have hle : ∑ t, (q.val t - (p i).val t) * (f t - f t₀) ≤ 0 := by
        refine sum_nonpos fun t _ => ?_
        by_cases ht : ε < (p i).val t
        · have : f t = f t₀ := le_antisymm (hM t) (h t ht t₀)
          rw [this, sub_self, mul_zero]
        · have h1 : (p i).val t = ε := le_antisymm (not_lt.mp ht) (hfloor t)
          have h2 : 0 ≤ q.val t - (p i).val t := by rw [h1]; linarith [hqfl t]
          exact mul_nonpos_of_nonneg_of_nonpos h2 (by linarith [hM t])
      linarith
    · push_neg at hex
      have hall : ∀ t, q.val t - (p i).val t = 0 := by
        have h0 : ∀ t ∈ (univ : Finset (G.strategy i)), 0 ≤ q.val t - (p i).val t := by
          intro t _
          have : (p i).val t = ε := le_antisymm (hex t) (hfloor t)
          rw [this]; linarith [hqfl t]
        intro t
        exact (sum_eq_zero_iff_of_nonneg h0).mp hsum t (mem_univ t)
      have : ∀ t, q.val t = (p i).val t := fun t => by linarith [hall t]
      simp only [this]
      exact le_refl _

/-! ### A limit of perturbed equilibria is a Nash equilibrium -/

/-- The tremble of a pure strategy: `ε` everywhere and the rest on `s'`.
Source: none: infrastructure
Kind: D -/
def trembleVal (ε : ℝ) {i : N} (s' : G.strategy i) (s : G.strategy i) : ℝ :=
  ε + (1 - Fintype.card (G.strategy i) * ε) * (if s = s' then 1 else 0)

theorem sum_ite_eq_one {i : N} (s' : G.strategy i) :
    ∑ s : G.strategy i, (if s = s' then (1 : ℝ) else 0) = 1 := by
  simp

theorem trembleVal_mem {ε : ℝ} (hε : 0 ≤ ε) {i : N}
    (hK : (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) (s' : G.strategy i) :
    trembleVal ε s' ∈ stdSimplex ℝ (G.strategy i) := by
  refine ⟨fun s => ?_, ?_⟩
  · unfold trembleVal
    split_ifs <;> nlinarith
  · unfold trembleVal
    rw [sum_add_distrib, ← mul_sum, sum_ite_eq_one, sum_const, card_univ, nsmul_eq_mul]
    ring

/-- The floor of a mixed strategy forces `card · ε ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem card_mul_le_one_of_floor {ε : ℝ} {i : N} (q : MixedStrategy G i)
    (hfl : ∀ s, ε ≤ q.val s) : (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1 := by
  have := sum_le_sum (fun s (_ : s ∈ (univ : Finset (G.strategy i))) => hfl s)
  rw [q.2.2, sum_const, card_univ, nsmul_eq_mul] at this
  exact this

/-- **A trembling-hand equilibrium is a mixed Nash equilibrium** (T3(ii)): pass to the limit in
the constrained inequality along the tremble of each pure deviation.
Source: mandate T3(ii) (`thpe_isMixedNash`); Selten 1975
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem THPE.isMixedNashEq {pStar : MixedProfile G} (h : THPE pStar) : IsMixedNashEq G pStar := by
  obtain ⟨ε, p, hpos, hε, hnash, hconv⟩ := h
  intro who s'
  -- the tremble of `s'` at level `ε k`
  have hK : ∀ k, (Fintype.card (G.strategy who) : ℝ) * ε k ≤ 1 := fun k =>
    card_mul_le_one_of_floor (p k who) fun s => (hnash k).1 who s
  let q : ℕ → MixedStrategy G who := fun k => ⟨trembleVal (ε k) s', trembleVal_mem (hpos k).le (hK k) s'⟩
  have hqfl : ∀ k s, ε k ≤ (q k).val s := by
    intro k s
    show ε k ≤ trembleVal (ε k) s' s
    unfold trembleVal
    have := hK k
    split_ifs <;> nlinarith
  have hineq : ∀ k, expectedPayoff G (Function.update (p k) who (q k)) who ≤
      expectedPayoff G (p k) who := fun k => (hnash k).2 who (q k) (hqfl k)
  -- convergence of the deviated profiles
  have hconv' : Tendsto (fun k => profileVal (Function.update (p k) who (q k))) atTop
      (𝓝 (profileVal (deviateMixed G pStar who s'))) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro s
    by_cases hi : i = who
    · subst hi
      simp only [profileVal, deviateMixed, Function.update_self]
      show Tendsto (fun k => trembleVal (ε k) s' s) atTop (𝓝 ((pureToMixed s').val s))
      unfold trembleVal pureToMixed
      simp only
      have h1 : Tendsto (fun k => ε k + (1 - Fintype.card (G.strategy i) * ε k) *
          (if s = s' then (1 : ℝ) else 0)) atTop
          (𝓝 (0 + (1 - Fintype.card (G.strategy i) * 0) * (if s = s' then (1 : ℝ) else 0))) := by
        refine hε.add (Tendsto.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul hε))
          tendsto_const_nhds)
      simpa using h1
    · simp only [profileVal, deviateMixed, Function.update_of_ne hi]
      have := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hconv i) s
      exact this
  have hl : Tendsto (fun k => expectedPayoff G (Function.update (p k) who (q k)) who) atTop
      (𝓝 (expectedPayoff G (deviateMixed G pStar who s') who)) := by
    simp only [expectedPayoff_eq_euFun]
    exact ((continuous_euFun G who).tendsto _).comp hconv'
  have hr : Tendsto (fun k => expectedPayoff G (p k) who) atTop (𝓝 (expectedPayoff G pStar who)) := by
    simp only [expectedPayoff_eq_euFun]
    exact ((continuous_euFun G who).tendsto _).comp hconv
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hineq)

/-- The weight of a pure profile under a pure profile is the indicator of equality.
Source: none: infrastructure
Kind: L -/
theorem profWeight_pureProfileToMixed (σ σ' : G.Profile) :
    profWeight (pureProfileToMixed σ) σ' = if σ' = σ then 1 else 0 := by
  unfold profWeight pureProfileToMixed pureToMixed
  simp only
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- The expected payoff of a pure profile is its payoff.
Source: none: infrastructure
Kind: L -/
theorem expectedPayoff_pureProfileToMixed (σ : G.Profile) (who : N) :
    expectedPayoff G (pureProfileToMixed σ) who = G.payoff σ who := by
  unfold expectedPayoff
  simp_rw [show ∀ σ', (∏ i, (pureProfileToMixed σ i).val (σ' i)) = profWeight (pureProfileToMixed σ) σ'
    from fun _ => rfl, profWeight_pureProfileToMixed]
  simp

theorem deviateMixed_pureProfileToMixed (σ : G.Profile) (i : N) (s : G.strategy i) :
    deviateMixed G (pureProfileToMixed σ) i s = pureProfileToMixed (Function.update σ i s) := by
  funext j
  unfold deviateMixed pureProfileToMixed
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- **A pure trembling-hand equilibrium is a pure Nash equilibrium** (EconCSLib's
`IsNashEquilibrium`).
Source: mandate T3(ii) (`thpe_pure_isNash`)
Kind: C
Fidelity: exact -/
theorem thpe_pure_isNash {σ : G.Profile} (h : THPE (pureProfileToMixed σ)) :
    IsNashEquilibrium G σ := by
  have hm := h.isMixedNashEq
  intro i s'
  have := hm i s'
  rw [deviateMixed_pureProfileToMixed, expectedPayoff_pureProfileToMixed,
    expectedPayoff_pureProfileToMixed] at this
  exact this

/-! ### The uniform perturbation of a pure profile -/

/-- The uniform perturbation of the pure profile `s*`: weight `1 − (Kᵢ − 1)ε` on `s*ᵢ` and `ε` on
every other pure strategy (raw weight vectors).
Source: mandate T3(iii) (`σ^ε`)
Kind: D -/
def unifPertVal (ε : ℝ) (sStar : G.Profile) (i : N) (s : G.strategy i) : ℝ :=
  if s = sStar i then 1 - (Fintype.card (G.strategy i) - 1) * ε else ε

theorem unifPertVal_nonneg {ε : ℝ} (hε : 0 ≤ ε) (sStar : G.Profile) (i : N)
    (hK : (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) (s : G.strategy i) :
    0 ≤ unifPertVal ε sStar i s := by
  unfold unifPertVal
  split_ifs <;> nlinarith

theorem unifPertVal_floor {ε : ℝ} (hε : 0 ≤ ε) (sStar : G.Profile) (i : N)
    (hK : (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) (s : G.strategy i) :
    ε ≤ unifPertVal ε sStar i s := by
  unfold unifPertVal
  split_ifs <;> nlinarith

theorem unifPertVal_mem {ε : ℝ} (hε : 0 ≤ ε) (sStar : G.Profile) (i : N)
    (hK : (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) :
    unifPertVal ε sStar i ∈ stdSimplex ℝ (G.strategy i) := by
  refine ⟨unifPertVal_nonneg hε sStar i hK, ?_⟩
  unfold unifPertVal
  have : ∀ s : G.strategy i, (if s = sStar i then 1 - (Fintype.card (G.strategy i) - 1) * ε else ε)
      = ε + (if s = sStar i then 1 - Fintype.card (G.strategy i) * ε else 0) := by
    intro s; split_ifs <;> ring
  simp_rw [this]
  rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ _), sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The uniform perturbation as a mixed profile.
Source: mandate T3(iii)
Kind: D -/
def unifPert {ε : ℝ} (hε : 0 ≤ ε) (sStar : G.Profile)
    (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) : MixedProfile G :=
  fun i => ⟨unifPertVal ε sStar i, unifPertVal_mem hε sStar i (hK i)⟩

theorem profileVal_unifPert {ε : ℝ} (hε : 0 ≤ ε) (sStar : G.Profile)
    (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1) :
    profileVal (unifPert hε sStar hK) = unifPertVal ε sStar := rfl

/-- The pure-deviation payoff as a function of raw weight vectors.
Source: none: infrastructure
Kind: D -/
def pureDevFun (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)]
    (x : ∀ i, G.strategy i → ℝ) (i : N) (s : G.strategy i) : ℝ :=
  ∑ σ : G.Profile, (∏ j, x j (σ j)) * G.payoff (Function.update σ i s) i

theorem pureDev_eq_pureDevFun (p : MixedProfile G) (i : N) (s : G.strategy i) :
    pureDev p i s = pureDevFun G (profileVal p) i s := rfl

/-- **The Selten step for the uniform perturbation**: if for all small `ε > 0` every player's
`s*ᵢ` is a pure best response to `σ^ε_{-i}`, then `s*` is a trembling-hand equilibrium.
Source: mandate T3(iii) (the step dp-cf-003 left as prose)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem thpe_of_unifPert (sStar : G.Profile) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε₀ ≤ 1)
    (h : ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ i (s : G.strategy i),
      pureDevFun G (unifPertVal ε sStar) i s ≤ pureDevFun G (unifPertVal ε sStar) i (sStar i)) :
    THPE (pureProfileToMixed sStar) := by
  let ε : ℕ → ℝ := fun k => ε₀ / (k + 2)
  have hpos : ∀ k, 0 < ε k := fun k => by positivity
  have hle : ∀ k, ε k ≤ ε₀ := fun k => by
    show ε₀ / (k + 2) ≤ ε₀
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hKk : ∀ k i, (Fintype.card (G.strategy i) : ℝ) * ε k ≤ 1 := fun k i =>
    le_trans (mul_le_mul_of_nonneg_left (hle k) (Nat.cast_nonneg _)) (hK i)
  refine ⟨ε, fun k => unifPert (hpos k).le sStar (hKk k), hpos, ?_, ?_, ?_⟩
  · -- ε k → 0
    have : Tendsto (fun k : ℕ => ε₀ / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat ε₀).comp (tendsto_add_atTop_nat 2)
    refine this.congr fun k => ?_
    simp [ε]
  · intro k
    refine ⟨fun i s => unifPertVal_floor (hpos k).le sStar i (hKk k i) s, ?_⟩
    intro i
    dsimp only
    rw [constrainedBR_iff _ i (hpos k).le (fun s => unifPertVal_floor (hpos k).le sStar i (hKk k i) s)]
    intro s hs s'
    have hs' : s = sStar i := by
      by_contra hne
      have : (unifPert (hpos k).le sStar (hKk k) i).val s = ε k := by
        show unifPertVal (ε k) sStar i s = ε k
        unfold unifPertVal; rw [if_neg hne]
      rw [this] at hs; exact lt_irrefl _ hs
    rw [hs', pureDev_eq_pureDevFun, pureDev_eq_pureDevFun, profileVal_unifPert]
    exact h (ε k) (hpos k) (hle k) i s'
  · rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro s
    show Tendsto (fun k => unifPertVal (ε k) sStar i s) atTop (𝓝 ((pureToMixed (sStar i)).val s))
    unfold unifPertVal pureToMixed
    simp only
    have hε : Tendsto ε atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => ε₀ / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat ε₀).comp (tendsto_add_atTop_nat 2)
      refine this.congr fun k => ?_
      simp [ε]
    split_ifs
    · have := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := ((Fintype.card (G.strategy i) : ℝ) - 1))).mul hε)
      simpa using this
    · exact hε

/-- **Dominant strategies are trembling-hand perfect** (T3(iv)): if each `s*ᵢ` is a best response
to *every* pure profile of the others, `s*` is a trembling-hand equilibrium.
Source: mandate T3(iv) (`thpe_of_dominant`)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem thpe_of_dominant (sStar : G.Profile)
    (h : ∀ i (s : G.strategy i) (σ : G.Profile),
      G.payoff (Function.update σ i s) i ≤ G.payoff (Function.update σ i (sStar i)) i) :
    THPE (pureProfileToMixed sStar) := by
  let Kmax : ℕ := univ.sup fun i => Fintype.card (G.strategy i)
  have hKmax : ∀ i, Fintype.card (G.strategy i) ≤ Kmax := fun i =>
    Finset.le_sup (f := fun i => Fintype.card (G.strategy i)) (mem_univ i)
  refine thpe_of_unifPert sStar (ε₀ := 1 / (Kmax + 1)) (by positivity) ?_ ?_
  · intro i
    have h1 : (Fintype.card (G.strategy i) : ℝ) ≤ Kmax := by exact_mod_cast hKmax i
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  · intro ε hε hεle i s
    unfold pureDevFun
    refine sum_le_sum fun σ _ => ?_
    refine mul_le_mul_of_nonneg_left (h i s σ) ?_
    refine prod_nonneg fun j _ => unifPertVal_nonneg hε.le sStar j ?_ (σ j)
    have h1 : (Fintype.card (G.strategy j) : ℝ) ≤ Kmax := by exact_mod_cast hKmax j
    calc (Fintype.card (G.strategy j) : ℝ) * ε ≤ Kmax * (1 / (Kmax + 1)) :=
          mul_le_mul h1 hεle hε.le (Nat.cast_nonneg _)
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith

end Cleanroom.Udt.UdtHarmonyBargain
