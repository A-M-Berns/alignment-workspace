import Cleanroom.Decision.DpLearnerNr.Defs

/-!
# `dp-learner-nr` D4 and targets 4(b), 5(a)(b), 7(b): the policy-level marginal-formula learner, static

**D4.** `PolicyLearner Π W R K`: a *state* — the pooled marginal `P : FinDistr K W` over exogenous
configurations, the response table `E : Π → W → K` (the per-cell histogram collapsed to its mean
payoff; disclosed), and the observed per-round law `law : Π → FinDistr K (W × R)` per policy (the
exogenous and responsive observables), for the partition test. No dynamics in the definition:
rounds are the hypotheses of the theorems that mention them.

* `cfPol π := ∑_w P(w) E(π, w)` (D2 at the policy level); `evPol π := ∑_w P(w ∣ π) E(π, w)` with
  `P(· ∣ π)` the `W`-marginal of `law π` (policy-level EDT); `IsGreedy`.
* `ExogenousCoord L visited f`: the pushforward of the round law along a coordinate `f` is the same
  for every visited policy; `Exogenous := ExogenousCoord … Prod.fst`.
* **Target 5(a), the FDT property by construction**: when the pooled marginal agrees with the
  per-policy exogenous marginals on the visited set (`Pooled`, which `Exogenous` gives once `P`
  is any visited policy's marginal), `cfPol = evPol` there (`cfPol_eq_evPol_of_pooled`). Kind L/C
  — the content of [[policy-level-fdt-learner]] §1.3.
* **Target 5(b), the non-responsiveness clause**: `cfPol` depends on the state only through
  `(P, E)` (`cfPol_congr`): a composite sentence `π_t = π → φ(w)` constrains `P(w ∣ π)`, which has
  no slot here.
* **Target 7(b), identifiability's static half**: a policy-fair environment `Env` (`Pstar`,
  `F : Π → W → FinDistr K Y`, `u`) determines the learner at the truth (`Env.learner`): its `E` is
  `𝔼_{F π w}[u]` by definition and its exogenous marginal is `Pstar` for every policy
  (`Env.learner_exogenous`, `Env.learner_pooled`) — definitional, said so.
* **Target 4(b), 𝔅 as the one-point learner**: `Π := Act2`, `W := Bool`, `P := Bern θ`, `E` the
  troll's table: `cfPol = cfMarginal` definitionally and `greedy = cross ↔ θ < ½`.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **D4 — the policy-level marginal-formula learner, static.** `P` the pooled marginal over the
exogenous configurations `W`; `E` the per-cell mean payoff (the histogram of
[[policy-level-fdt-learner]] §1.2(v) collapsed to its expectation — disclosed); `law` the observed
per-round law per policy over the exogenous and responsive observables `W × R`, for the partition
test. The learner is a state; rounds are hypotheses of the theorems that mention them.
Source: [[policy-level-fdt-learner]] §1.2 (state), §1.3 (decision rule), §1.5 (the partition
test); [[marginal-formula-learner]] "The policy-level lift"; [[dp-core-2-inventory]] 028;
[[dp-learner-nr-mandate]] D4
Kind: D
Fidelity: variant: `E` is a mean, not a histogram; the partition is rendered at the type level
(`W` exogenous, `R` responsive) with the per-variable test as `ExogenousCoord` along a
coordinate map -/
structure PolicyLearner (Pol W R : Type) [Fintype Pol] [Fintype W] [Fintype R] (K : Type) [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The pooled marginal over exogenous configurations. -/
  P : FinDistr K W
  /-- The response table: mean payoff per `(policy, exogenous configuration)` cell. -/
  E : Pol → W → K
  /-- The observed per-round law per policy, over exogenous and responsive observables. -/
  law : Pol → FinDistr K (W × R)

namespace PolicyLearner

variable {Pol W R : Type} [Fintype Pol] [Fintype W] [Fintype R] [DecidableEq W]

/-- `cf(U ∣ do π) := ∑_w P(w) · E(π, w)` — D2 at the policy level.
Source: [[policy-level-fdt-learner]] §1.3; [[dp-learner-nr-mandate]] D4
Kind: D -/
def cfPol (L : PolicyLearner Pol W R K) (π : Pol) : K := cfMarginal L.P L.E π

/-- The exogenous marginal of the observed round law under policy `π`: `P(· ∣ π)` on `W`.
Source: [[policy-level-fdt-learner]] §1.3 ("`P(w ∣ π)`"); [[dp-learner-nr-mandate]] D4
Kind: D -/
def lawW (L : PolicyLearner Pol W R K) (π : Pol) : FinDistr K W := pushDistr (L.law π) Prod.fst

/-- Policy-level EDT: `cf_EDT(π) := E[U ∣ π_t = π] = ∑_w P(w ∣ π) E(π, w)`.
Source: [[policy-level-fdt-learner]] §4.2 ("`cf_EDT(π) := E[U | π_t = π] = Σ_w P(w | π) E(π, w)`");
[[dp-learner-nr-mandate]] D4
Kind: D -/
def evPol (L : PolicyLearner Pol W R K) (π : Pol) : K := ∑ w, (L.lawW π).w w * L.E π w

/-- `π` is greedy: it maximizes `cfPol`. Source: [[policy-level-fdt-learner]] §1.3. Kind: D -/
def IsGreedy (L : PolicyLearner Pol W R K) (π : Pol) : Prop := ∀ π', L.cfPol π' ≤ L.cfPol π

/-- **The partition test for a coordinate `f` of the observables** on a visited set: the
pushforward of the round law along `f` is the same for every visited policy.
Source: [[policy-level-fdt-learner]] §1.5(c), §3 ("the invariance of `P(v | π)` across the
*visited* policy set"); [[dp-learner-nr-mandate]] D4 (`Exogenous`)
Kind: D -/
def ExogenousCoord {X : Type} [Fintype X] [DecidableEq X] (L : PolicyLearner Pol W R K)
    (visited : Finset Pol) (f : W × R → X) : Prop :=
  ∀ π ∈ visited, ∀ π' ∈ visited, pushDistr (L.law π) f = pushDistr (L.law π') f

/-- The designated exogenous configuration is exogenous on the visited set.
Source: [[dp-learner-nr-mandate]] D4
Kind: D -/
def Exogenous (L : PolicyLearner Pol W R K) (visited : Finset Pol) : Prop :=
  ExogenousCoord L visited Prod.fst

/-- The pooled marginal agrees with every visited policy's exogenous marginal.
Source: [[policy-level-fdt-learner]] §1.5(a) ("`P(w)` is never indexed by `π`");
[[dp-learner-nr-mandate]] target 5(a)
Kind: D -/
def Pooled (L : PolicyLearner Pol W R K) (visited : Finset Pol) : Prop :=
  ∀ π ∈ visited, L.lawW π = L.P

/-- Exogeneity on the visited set plus `P` equal to one visited policy's marginal gives `Pooled`.
Source: none: infrastructure
Kind: L -/
theorem pooled_of_exogenous (L : PolicyLearner Pol W R K) (visited : Finset Pol)
    (hex : L.Exogenous visited) (π₀ : Pol) (h₀ : π₀ ∈ visited) (hP : L.lawW π₀ = L.P) :
    L.Pooled visited := by
  intro π hπ
  rw [← hP]
  exact hex π hπ π₀ h₀

/-- **The FDT property by construction** (target 5(a)): on the visited set, when the exogenous
coordinates' law does not vary with `π` and `P` is that common marginal, the marginal formula
*is* the policy-conditional expectation: `cfPol π = evPol π`. The formula differs from policy-level
EDT only at unvisited policies, at latent `W`, and wherever something asserts `P(w ∣ π) ≠ P(w)`
for a `w ∈ W` — the whole of Troll Bridge.
Source: [[policy-level-fdt-learner]] §1.3 ("On visited policies with a correct partition this
equals `E[U | π_t = π]` … so the FDT property … holds *by construction* on the visited set");
[[dp-core-2-inventory]] 028; [[dp-learner-nr-mandate]] target 5(a)
Kind: L
Fidelity: exact (an unfolding; do not oversell)
Hyps: (a) `Pooled` on the visited set -/
theorem cfPol_eq_evPol_of_pooled (L : PolicyLearner Pol W R K) (visited : Finset Pol)
    (hpool : L.Pooled visited) (π : Pol) (hπ : π ∈ visited) : L.cfPol π = L.evPol π := by
  unfold cfPol evPol cfMarginal
  rw [hpool π hπ]

/-- **The non-responsiveness clause** (target 5(b)): `cfPol` depends on the state only through
`(P, E)`. A composite sentence `π_t = π → φ(w)` constrains `P(w ∣ π)` — the `law` field — which has
no slot in `cfPol`; it is inert for the decision whatever its provenance.
Source: [[policy-level-fdt-learner]] §1.6 ("constrains `P(w | π)`, a quantity the formula of 1.3
never forms; it is therefore inert for the decision, whatever its provenance");
[[dp-core-2-inventory]] 028; [[dp-learner-nr-mandate]] target 5(b)
Kind: L
Fidelity: exact (a `congr` lemma; the clause's content is the absence of a slot) -/
theorem cfPol_congr (L L' : PolicyLearner Pol W R K) (hP : L.P = L'.P) (hE : L.E = L'.E) :
    L.cfPol = L'.cfPol := by
  funext π
  unfold cfPol cfMarginal
  rw [hP, hE]

/-- Two learners with the same `(P, E)` and *different* observed laws have the same `cfPol`:
the law field — where a composite theorem would land — never reaches the decision.
Source: [[policy-level-fdt-learner]] §1.6; [[dp-learner-nr-mandate]] target 5(b)
Kind: L -/
theorem cfPol_eq_of_law_ne (L : PolicyLearner Pol W R K) (law' : Pol → FinDistr K (W × R)) :
    L.cfPol = (PolicyLearner.mk L.P L.E law').cfPol :=
  cfPol_congr L _ rfl rfl

end PolicyLearner

/-! ## Target 7(b): a policy-fair environment determines the learner at the truth -/

/-- **A policy-fair environment**: i.i.d. exogenous law `Pstar`, a round law `F π w` of the
outcome `y` that is a function of `(π, w)` alone (policy-fairness), and a payoff `u`.
Source: [[policy-level-fdt-learner]] §6 ("round law `F(π_t, w_t)` with `w_t` i.i.d. … *Policy-
fairness*: `F` depends on the agent only through `π_t`"); [[dp-learner-nr-mandate]] D4
Kind: D -/
structure Env (Pol W Y : Type) [Fintype Pol] [Fintype W] [Fintype Y] (K : Type) [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The i.i.d. exogenous law. -/
  Pstar : FinDistr K W
  /-- The round law of the outcome given the policy and the exogenous configuration. -/
  F : Pol → W → FinDistr K Y
  /-- The payoff of an outcome. -/
  u : Y → K

namespace Env

variable {Pol W Y : Type} [Fintype Pol] [Fintype W] [Fintype Y] [DecidableEq W]

/-- The cell mean `E(π, w) := 𝔼_{F π w}[u]`.
Source: [[policy-level-fdt-learner]] §3 ("`E` on `Π′ × W` are determined by `F|_{Π′}`");
[[dp-learner-nr-mandate]] target 7(b)
Kind: D -/
def E (e : Env Pol W Y K) (π : Pol) (w : W) : K := ∑ y, (e.F π w).w y * e.u y

/-- The joint round law `(w, y)` under policy `π`: `w ∼ Pstar`, `y ∼ F π w`.
Source: none: infrastructure
Kind: D -/
def law (e : Env Pol W Y K) (π : Pol) : FinDistr K (W × Y) where
  w p := e.Pstar.w p.1 * (e.F π p.1).w p.2
  nonneg p := mul_nonneg (e.Pstar.nonneg _) ((e.F π p.1).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FinDistr.sum_one, mul_one]

/-- **The learner at the truth**: `P := Pstar`, `E := 𝔼_{F π w}[u]`, `law := the joint`.
Source: [[policy-level-fdt-learner]] §3 ("Identifiability, theorem-shaped … the partition
restricted to `Π′` and `E` on `Π′ × W` are identifiable"); [[dp-learner-nr-mandate]] target 7(b)
Kind: D -/
def learner (e : Env Pol W Y K) : PolicyLearner Pol W Y K := ⟨e.Pstar, e.E, e.law⟩

/-- The exogenous marginal of the joint under any policy is `Pstar`.
Source: none: infrastructure
Kind: L -/
theorem lawW_eq (e : Env Pol W Y K) (π : Pol) : (e.learner).lawW π = e.Pstar := by
  apply FinDistr.ext'
  intro w
  show ∑ p ∈ univ.filter (fun p : W × Y => p.1 = w), e.Pstar.w p.1 * (e.F π p.1).w p.2 = _
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single w]
  · simp [← Finset.mul_sum, FinDistr.sum_one]
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ w) h

/-- **Identifiability, the static half** (target 7(b)): in a policy-fair environment the
designated exogenous configuration is exogenous on every visited set — the test
`∀ π π' ∈ Π′, marginal_W (F π) = marginal_W (F π')` holds by definition — and the learner's `E` is
`𝔼_{F π w}[u]` by definition. Definitional; said so.
Source: [[policy-level-fdt-learner]] §3 ("if the round law is `F(π_t, w_t)` with `w_t` i.i.d. and
`F` fixed, then … the partition restricted to `Π′` and `E` on `Π′ × W` are identifiable");
[[dp-core-2-inventory]] 033; [[dp-learner-nr-mandate]] target 7(b)
Kind: L
Fidelity: exact (of the static half; the estimator half is target 14, `cell_mean_converges`,
proved at repair round 1) -/
theorem learner_exogenous (e : Env Pol W Y K) (visited : Finset Pol) :
    (e.learner).Exogenous visited ∧ (e.learner).Pooled visited ∧
    ∀ π w, (e.learner).E π w = ∑ y, (e.F π w).w y * e.u y := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro π _ π' _
    show (e.learner).lawW π = (e.learner).lawW π'
    rw [lawW_eq, lawW_eq]
  · intro π _
    rw [lawW_eq]; rfl

/-- In a policy-fair environment the learner at the truth has `cfPol = evPol` everywhere (the FDT
property, instantiated).
Source: [[policy-level-fdt-learner]] §6 Conjecture F (iv) (the static form); [[dp-learner-nr-mandate]] target 5(a)
Kind: L (an instance of the unfolding `cfPol_eq_evPol_of_pooled`; relabelled from C at audit r1) -/
theorem learner_cfPol_eq_evPol (e : Env Pol W Y K) (π : Pol) :
    (e.learner).cfPol π = (e.learner).evPol π :=
  PolicyLearner.cfPol_eq_evPol_of_pooled _ Finset.univ (learner_exogenous e Finset.univ).2.1 π
    (Finset.mem_univ π)

end Env

/-! ## Target 4(b): 𝔅 as the one-point learner -/

/-- **𝔅 as the one-point instance of (D)**: `Π := Act2`, `W := Bool` (`incon`), `P := Bern θ`, `E`
the troll's stated table, no responsive observable.
Source: [[policy-level-fdt-learner]] §1.7 ("𝔅 … **is the act-level, one-shot, zero-data,
latent-W instance of this learner**: `W = {□⊥}`, `P = P₀`, `E` supplied entirely by the troll's
stated rule, `Π = {cross, stay}`"); [[dp-core-2-inventory]] 028; [[dp-learner-nr-mandate]] target 4(b)
Kind: D -/
def onePointLearner (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : PolicyLearner Act2 Bool Unit ℚ :=
  ⟨boolDistr θ h0 h1, trollE, fun _ => pushDistr (boolDistr θ h0 h1) fun b => (b, ())⟩

/-- `cfPol = cfMarginal` definitionally on the one-point learner, and the greedy policy is `cross`
iff `θ < ½` (strictly: `cross` is the unique maximizer iff `θ < ½`; `IsGreedy cross ↔ θ ≤ ½`).
Source: [[policy-level-fdt-learner]] §1.7; [[dp-learner-nr-mandate]] target 4(b)
Kind: L
Fidelity: exact -/
theorem onePointLearner_facts (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (onePointLearner θ h0 h1).cfPol = cfMarginal (boolDistr θ h0 h1) trollE ∧
    ((onePointLearner θ h0 h1).IsGreedy Act2.a ↔ θ ≤ 1 / 2) ∧
    ((onePointLearner θ h0 h1).cfPol Act2.b < (onePointLearner θ h0 h1).cfPol Act2.a ↔ θ < 1 / 2) := by
  have ha : (onePointLearner θ h0 h1).cfPol Act2.a = 10 - 20 * θ := by
    show cfMarginal (boolDistr θ h0 h1) trollE Act2.a = _
    rw [cfMarginal_trollE_cross]; simp
  have hb : (onePointLearner θ h0 h1).cfPol Act2.b = 0 := by
    show cfMarginal (boolDistr θ h0 h1) trollE Act2.b = _
    exact cfMarginal_trollE_stay _
  refine ⟨rfl, ?_, ?_⟩
  · constructor
    · intro h
      have := h Act2.b
      rw [ha, hb] at this
      linarith
    · intro h π'
      cases π' with
      | a => exact le_rfl
      | b => rw [ha, hb]; linarith
  · rw [ha, hb]; constructor <;> intro h <;> linarith

end Cleanroom.Decision.DpLearnerNr
