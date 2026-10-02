import Cleanroom.Udt.UdtHarmonyBargain.Perturbed
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `udt-harmony-bargain` — the support of a trembling-hand equilibrium

General facts about `THPE` over an arbitrary finite `StrategicGame N ℝ`, used by Proposition S:

* `sum_profWeight`: the profile weights of a mixed profile sum to one;
* `pureDev_le_of_pointwise` / `pureDev_lt_of_pointwise`: pointwise dominance of one pure
  deviation over another transfers to the expected payoffs against any mixed profile, strictly
  under a positive floor;
* `THPE.support_isBestResponse`: every pure strategy in the support of a trembling-hand
  equilibrium is a pure best response to it (the classical support characterisation);
* `IsPerturbedNash.val_le_of_dominated`: in a perturbed equilibrium a pure strategy that is
  pointwise weakly dominated and somewhere strictly dominated carries only the floor weight.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset StrategicGame Filter Topology

variable {N : Type} [Fintype N] [DecidableEq N]
variable {G : StrategicGame N ℝ} [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]

/-- The profile weights sum to one.
Source: none: infrastructure
Kind: L -/
theorem sum_profWeight (p : MixedProfile G) : ∑ σ : G.Profile, profWeight p σ = 1 := by
  unfold profWeight
  have := Finset.prod_univ_sum (fun i : N => (univ : Finset (G.strategy i)))
    (fun i s => (p i).val s)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp only [(fun i => (p i).2.2)]
  simp

/-- `pureDevFun` is continuous in the weight vectors.
Source: none: infrastructure
Kind: P -/
theorem continuous_pureDevFun (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)]
    [∀ i, DecidableEq (G.strategy i)] (i : N) (s : G.strategy i) :
    Continuous (fun x : ∀ j, G.strategy j → ℝ => pureDevFun G x i s) := by
  unfold pureDevFun
  refine continuous_finset_sum _ fun σ _ => ?_
  refine Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun j _ => (continuous_apply (σ j)).comp (continuous_apply j)

/-- Pointwise weak dominance transfers to `pureDev` against every mixed profile.
Source: none: infrastructure
Kind: P -/
theorem pureDev_le_of_pointwise (p : MixedProfile G) (i : N) {s s' : G.strategy i}
    (h : ∀ σ : G.Profile, G.payoff (Function.update σ i s) i ≤
      G.payoff (Function.update σ i s') i) :
    pureDev p i s ≤ pureDev p i s' :=
  sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (h σ) (profWeight_nonneg p σ)

/-- Pointwise weak dominance with one strict instance transfers strictly under a positive floor.
Source: none: infrastructure
Kind: P -/
theorem pureDev_lt_of_pointwise (p : MixedProfile G) (i : N) {ε : ℝ} (hε : 0 < ε)
    (hfl : ∀ j t, ε ≤ (p j).val t) {s s' : G.strategy i}
    (h : ∀ σ : G.Profile, G.payoff (Function.update σ i s) i ≤
      G.payoff (Function.update σ i s') i)
    (hstrict : ∃ σ : G.Profile, G.payoff (Function.update σ i s) i <
      G.payoff (Function.update σ i s') i) :
    pureDev p i s < pureDev p i s' := by
  obtain ⟨σ₀, hσ₀⟩ := hstrict
  unfold pureDev
  refine sum_lt_sum (fun σ _ => mul_le_mul_of_nonneg_left (h σ) (profWeight_nonneg p σ))
    ⟨σ₀, mem_univ _, ?_⟩
  exact mul_lt_mul_of_pos_left hσ₀ (profWeight_pos hε hfl σ₀)

/-- In a perturbed equilibrium, a pure strategy that is pointwise weakly dominated by another,
strictly against some pure profile, carries only the floor weight `ε`.
Source: HA-5′ (Lemma B's mechanism)
Kind: P -/
theorem IsPerturbedNash.val_le_of_dominated {ε : ℝ} (hε : 0 < ε) {p : MixedProfile G}
    (hp : IsPerturbedNash ε p) (i : N) {s s' : G.strategy i}
    (h : ∀ σ : G.Profile, G.payoff (Function.update σ i s) i ≤
      G.payoff (Function.update σ i s') i)
    (hstrict : ∃ σ : G.Profile, G.payoff (Function.update σ i s) i <
      G.payoff (Function.update σ i s') i) :
    (p i).val s ≤ ε := by
  by_contra hlt
  push_neg at hlt
  have hbr := (constrainedBR_iff p i hε.le (fun t => hp.1 i t)).mp (hp.2 i) s hlt s'
  exact absurd hbr (not_le.mpr (pureDev_lt_of_pointwise p i hε hp.1 h hstrict))

/-- A pure strategy with positive weight in a trembling-hand equilibrium is a pure best response
to it.
Source: Selten 1975 (support characterisation), mandate T3
Kind: P
Fidelity: exact -/
theorem THPE.support_isBestResponse {pStar : MixedProfile G} (h : THPE pStar) (i : N)
    (s : G.strategy i) (hs : 0 < (pStar i).val s) :
    ∀ s', pureDev pStar i s' ≤ pureDev pStar i s := by
  obtain ⟨ε, p, hpos, hε, hnash, hconv⟩ := h
  intro s'
  have hval : Tendsto (fun k => (p k i).val s) atTop (𝓝 ((pStar i).val s)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hconv i) s
  have hev : ∀ᶠ k in atTop, ε k < (p k i).val s := hε.eventually_lt hval hs
  have hineq : ∀ᶠ k in atTop, pureDev (p k) i s' ≤ pureDev (p k) i s := by
    filter_upwards [hev] with k hk
    exact (constrainedBR_iff (p k) i (hpos k).le (fun t => (hnash k).1 i t)).mp
      ((hnash k).2 i) s hk s'
  have hl : Tendsto (fun k => pureDev (p k) i s') atTop (𝓝 (pureDev pStar i s')) := by
    simp only [pureDev_eq_pureDevFun]
    exact ((continuous_pureDevFun G i s').tendsto _).comp hconv
  have hr : Tendsto (fun k => pureDev (p k) i s) atTop (𝓝 (pureDev pStar i s)) := by
    simp only [pureDev_eq_pureDevFun]
    exact ((continuous_pureDevFun G i s).tendsto _).comp hconv
  exact le_of_tendsto_of_tendsto hl hr hineq

/-- A pure strategy that carries only the floor weight in every perturbed equilibrium of a
trembling-hand sequence has weight `0` in the limit.
Source: HA-5′ (Lemma B, the limit step)
Kind: P -/
theorem THPE.val_eq_zero_of_forall_le {pStar : MixedProfile G} (i : N) (s : G.strategy i)
    (ε : ℕ → ℝ) (p : ℕ → MixedProfile G) (hε : Tendsto ε atTop (𝓝 0))
    (hconv : Tendsto (fun k => profileVal (p k)) atTop (𝓝 (profileVal pStar)))
    (hle : ∀ k, (p k i).val s ≤ ε k) : (pStar i).val s = 0 := by
  have hval : Tendsto (fun k => (p k i).val s) atTop (𝓝 ((pStar i).val s)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hconv i) s
  have h1 : (pStar i).val s ≤ 0 := le_of_tendsto_of_tendsto' hval hε hle
  exact le_antisymm h1 ((pStar i).2.1 s)

/-- The profile weight is positive iff every coordinate has positive weight.
Source: mandate §3 ("outcomes of the profiles in the limit's support")
Kind: L -/
theorem profWeight_pos_iff (p : MixedProfile G) (σ : G.Profile) :
    0 < profWeight p σ ↔ ∀ i, 0 < (p i).val (σ i) := by
  unfold profWeight
  constructor
  · intro h i
    by_contra hi
    push_neg at hi
    have h0 : (p i).val (σ i) = 0 := le_antisymm hi ((p i).2.1 _)
    have : ∏ j, (p j).val (σ j) = 0 := prod_eq_zero (mem_univ i) h0
    rw [this] at h
    exact lt_irrefl _ h
  · intro h
    exact prod_pos fun i _ => h i

/-- Expected payoff as a `profWeight`-weighted sum of payoffs.
Source: none: infrastructure
Kind: L -/
theorem expectedPayoff_eq_sum_profWeight (p : MixedProfile G) (who : N) :
    expectedPayoff G p who = ∑ σ : G.Profile, profWeight p σ * G.payoff σ who := rfl

/-- The mixed-Nash inequality for a pure deviation, in `pureDev` form.
Source: none: infrastructure
Kind: L -/
theorem IsMixedNashEq.pureDev_le {p : MixedProfile G} (h : IsMixedNashEq G p) (i : N)
    (s : G.strategy i) : pureDev p i s ≤ expectedPayoff G p i := by
  have := h i s
  unfold deviateMixed at this
  rwa [expectedPayoff_update_pure] at this

end Cleanroom.Udt.UdtHarmonyBargain
