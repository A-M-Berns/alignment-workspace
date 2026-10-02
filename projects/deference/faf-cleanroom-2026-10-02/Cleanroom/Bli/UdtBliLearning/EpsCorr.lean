import Cleanroom.Bli.UdtBliLearning.Calibration

/-!
# `udt-bli-learning` · EpsCorr: ε-bounded belief in acausal correlations gives ε-updateful
behaviour — the finite form as a corollary of core's `eps_updateful`, the asymptotic clause in
its honest approximate form, and the exact form stated as a proposition (refuted in
`EpsCorrWitness`) (T9)

**Scope: any `FiniteBLIPrior` (finite, one level); over a belief-state sequence with realized
tables for the asymptotic clause.**

Abram's Notion note states the target: "for each environment, there is some epsilon such that if
the agent's belief in acausal correlations is below epsilon, and the environment doesn't
systematically introduce such correlations, then the performance of UDT will eventually be optimal
in that environment"; the Sep 8 email splits "correlations" into the two kinds — "between actions
and the probability of branches" and "between actions and the *utility* of other branches".

* `CorrBounded P T ε` (D): exactly those two `ε`-invariances at `T` — the hypotheses
  `udt-bli-core`'s `eps_updateful` takes (branch-probability spread and cross-branch value spread
  over `T' ≠ T`). A predicate, not a number: "belief in acausal correlations below `ε`".
* `eps_corr_implies_eps_updateful` (**C**): `CorrBounded P T ε → |U| ≤ M → … → every one-step
  choice at `T` is `δ(ε)`-updateful-optimal`, `δ(ε) = ε (1 + (2|𝒟| + 1) M)/ρ` — a corollary of
  `eps_updateful`, nothing new proved; its value is the *statement* in the source's vocabulary.
* **Not a squeeze** (`corrBounded_zero_not_necessary`, N−): on `scPrior p` with `gain < 0` the
  conclusion at `ε = 0` holds at `Ask_j` (one-step and updateful both refuse) while
  `CorrBounded (scPrior p) Ask_j 0` fails (the cross-branch spread at `Rec_j` is `V γ_j > 0`):
  the hypothesis is strictly stronger than the conclusion.
* **The asymptotic clause, approximate form** (`eventually_eps_updateful`, **C**): if the
  correlation bounds `ε_n → 0` (elementary convergence) with uniform `M`, `ρ`, then for every
  `η > 0`, eventually every one-step choice of `Q_n` at every realized table is `η`-updateful-
  optimal — an honest round-by-round corollary (not a squeeze: the hypothesis is about
  correlations, the conclusion about home values), but **approximate**. With a uniform home-value
  gap `g > 0` (`eventually_updateful_of_gap`, **C**) the conclusion is exact.
* **The exact clause without a gap condition is false** (`ExactAsymptoticClause`, D, the
  proposition; `EpsCorrWitness.not_exactAsymptoticClause`, its refutation on core's two-table
  carrier). Diagnosis confirmed by construction: `δ(ε_n) → 0` bounds the loss, not the choice; a
  family whose home-value gap `1/(2(n+1))` shrinks faster than its cross-branch correlation
  `1/(n+1)` keeps the one-step choice on the wrong side at *every* `n` while the loss tends to `0`.
  Until repair round 2 this was the package's one OPEN statement (`eventually_updateful_exact`,
  "stated, not believed"); the open list is now empty. The asymptotic headlines' witnesses (N− and
  N+) live in `EpsCorrWitness.lean` too.

`pointCorr` (sist's policy-point correlation) is a second candidate for "belief in correlations";
`eps_updateful` needs the two invariances above, not `pointCorr` (recorded in the findings).

Sources: bli-soto-b-046 (Notion ll. 360–368), bli-soto-a-068 (ii), bli-soto-a-070 (the two kinds
of correlation); [[bli-program]] §3.9 U3; mandate T9.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

section Generic

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- **Belief in acausal correlations at `T` bounded by `ε`**: the two `ε`-invariances — the
branch probabilities move by at most `ε` with the action at `T`, and the values of the other
branches `T' ≠ T` (where both cells are positive) move by at most `ε`.
Source: bli-soto-a-070 (the two kinds of correlation); bli-soto-b-046 ("belief in acausal
correlations is below epsilon"); mandate T9
Kind: D
Fidelity: variant: a predicate ("below `ε`") in place of a number; exactly `eps_updateful`'s
hypotheses -/
def CorrBounded (T : ↥𝒟) (ε : ℚ) : Prop :=
  (∀ T' c d, |P.branchProb T' T c - P.branchProb T' T d| ≤ ε) ∧
  (∀ T' c d, T' ≠ T → 0 < P.jointMass T' T c → 0 < P.jointMass T' T d →
    |P.condEU T' T c - P.condEU T' T d| ≤ ε)

/-- **The updateful slack** `δ(ε) := ε (1 + (2|𝒟| + 1) M)/ρ` of `eps_updateful`.
Source: [[bli-program]] §3.9 U3; `udt-bli-core` T5 (the explicit constant)
Kind: D
Fidelity: exact -/
def updatefulSlack (𝒟 : Finset (Table 𝒮 m)) (ε M ρ : ℚ) : ℚ :=
  ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) / ρ

/-- **ε-bounded correlations give ε-updateful behaviour** (finite form): under `CorrBounded P T ε`,
positive points at `T`, `|U| ≤ M`, and home branch probability `≥ ρ` under the chosen action,
every one-step choice `a*` at `T` is `δ(ε)`-updateful-optimal.
Source: bli-soto-b-046; bli-soto-a-068 (ii); mandate T9 (`eps_corr_implies_eps_updateful`)
Kind: L (one application of core's `eps_updateful` with `CorrBounded` unpacked; its value is the
statement in the source's vocabulary)
Fidelity: exact (finite; the asymptotic clause is `eventually_eps_updateful`)
Hyps: (a) `CorrBounded`, `NDPOL` at `T`, `|U| ≤ M`, `ρ ≤ branchProb T T a*` -/
theorem eps_corr_implies_eps_updateful (T : ↥𝒟) (ε M ρ : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hρ : 0 < ρ) (hpol : ∀ c, 0 < P.ppMass T c) (hcorr : CorrBounded P T ε)
    (hU : ∀ ω, |P.U ω| ≤ M) (astar : A) (hstar : P.IsOneStepChoice T astar)
    (hρa : ρ ≤ P.branchProb T T astar) (b : A) :
    P.homeEU T b - P.homeEU T astar ≤ updatefulSlack 𝒟 ε M ρ :=
  P.eps_updateful T ε M ρ hε hM hρ hpol hcorr.1 hcorr.2 hU astar hstar hρa b

variable {K : ℕ}

/-- **The asymptotic clause, approximate form**: over a belief-state sequence `Q` with realized
tables `real`, if the correlation bounds `ε_n` tend to `0` (elementary convergence), with uniform
`M`, `ρ`, positive points and `CorrBounded (Q n) (real k) (ε n)` at every realized table, then for
every `η > 0`, from some `n` on every one-step choice of `Q_n` at every realized table is
`η`-updateful-optimal. An honest round-by-round corollary of `eps_updateful`; approximate, not
exact (see `eventually_updateful_of_gap` and the open statement).
Source: bli-soto-b-046 ("the performance of UDT will eventually be optimal in that environment");
mandate T9 (the asymptotic clause)
Kind: C
Fidelity: weaker: `η`-optimal for every `η`, not exact optimality; finite horizon. Two further
readings (audit r1 N1): the source's "optimal **in that environment**" is rendered as "optimal by
`Q_n`'s own home values" (by the agent's lights, not by an external criterion); and the source's
quantifier is a *threshold* ("for each environment there is some epsilon such that if the belief …
is below epsilon"), which the finite form `eps_corr_implies_eps_updateful` carries (`δ(ε) ≤ η` for
small `ε`) and this `ε_n → 0` form reshapes
Hyps: (a) convergence of `ε_n`, uniform `M`, `ρ`, `NDPOL`, `CorrBounded` at every realized table.
Witness: `EpsCorrWitness.w_inhabits_eventually_eps_updateful` (N+: a non-constant family on
core's two-table carrier with `ε_n = 10/(n+1) → 0` on which the one-step verdict flips from
updateful-suboptimal to updateful-optimal at `n = 10`, `w_oneStep_flips`; the conclusion is false
early, `w_not_early`) and `EpsCorrWitness.tf_inhabits_eventually_eps_updateful` (N−: core's
`tfPrior`, constant, `ε ≡ 0`). The witnesses live outside the single-coin model because on it
`CorrBounded _ Ask_j 0` fails for both states for `K ≥ 2` — the cross branches `Ask_k'`, `k' ≠ j`,
read `Ask_j`'s point through the summed utility (see the report, T9) -/
theorem eventually_eps_updateful (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟)
    (ε : ℕ → ℚ) (M ρ : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) (hε0 : ∀ n, 0 ≤ ε n)
    (hlim : ∀ η, 0 < η → ∃ N, ∀ n, N ≤ n → ε n ≤ η)
    (hpol : ∀ n (k : Fin K) c, 0 < (Q n).ppMass (real k) c)
    (hcorr : ∀ n (k : Fin K), CorrBounded (Q n) (real k) (ε n))
    (hU : ∀ n ω, |(Q n).U ω| ≤ M)
    (hρa : ∀ n (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      ρ ≤ (Q n).branchProb (real k) (real k) a) :
    ∀ η, 0 < η → ∃ N, ∀ n, N ≤ n → ∀ (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      ∀ b, (Q n).homeEU (real k) b - (Q n).homeEU (real k) a ≤ η := by
  intro η hη
  set C : ℚ := 1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M with hC
  have hCpos : 0 < C := by
    have : 0 ≤ (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M := mul_nonneg (by positivity) hM
    linarith
  obtain ⟨N, hN⟩ := hlim (η * ρ / C) (by positivity)
  refine ⟨N, fun n hn k a ha b => ?_⟩
  have h := eps_corr_implies_eps_updateful (Q n) (real k) (ε n) M ρ (hε0 n) hM hρ (hpol n k)
    (hcorr n k) (hU n) a ha (hρa n k a ha) b
  unfold updatefulSlack at h
  have hεn := hN n hn
  have hslack : ε n * C / ρ ≤ η := by
    rw [div_le_iff₀ hρ]
    have : ε n * C ≤ η * ρ / C * C := mul_le_mul_of_nonneg_right hεn hCpos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hCpos)] at this
  exact h.trans hslack

/-- **The asymptotic clause, exact under a uniform home-value gap**: if moreover at every realized
table two actions' home values are either equal or at least `g > 0` apart, then from some `n` on
every one-step choice of `Q_n` at every realized table is an updateful choice.
Source: bli-soto-b-046; mandate T9
Kind: C (`eventually_eps_updateful`)
Fidelity: weaker: needs the gap `g`; finite horizon. The gap is not removable:
`ExactAsymptoticClause` (the same statement without it) is refuted
Hyps: (a) as `eventually_eps_updateful` plus the uniform gap
Witness: `EpsCorrWitness.w_inhabits_eventually_updateful_of_gap` (N+, gap `g = 1`),
`EpsCorrWitness.tf_inhabits_eventually_updateful_of_gap` (N−) -/
theorem eventually_updateful_of_gap (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟)
    (ε : ℕ → ℚ) (M ρ g : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) (hg : 0 < g) (hε0 : ∀ n, 0 ≤ ε n)
    (hlim : ∀ η, 0 < η → ∃ N, ∀ n, N ≤ n → ε n ≤ η)
    (hpol : ∀ n (k : Fin K) c, 0 < (Q n).ppMass (real k) c)
    (hcorr : ∀ n (k : Fin K), CorrBounded (Q n) (real k) (ε n))
    (hU : ∀ n ω, |(Q n).U ω| ≤ M)
    (hρa : ∀ n (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      ρ ≤ (Q n).branchProb (real k) (real k) a)
    (hgap : ∀ n (k : Fin K) a b, (Q n).homeEU (real k) b = (Q n).homeEU (real k) a ∨
      g ≤ |(Q n).homeEU (real k) b - (Q n).homeEU (real k) a|) :
    ∃ N, ∀ n, N ≤ n → ∀ (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      (Q n).IsUpdatefulChoice (real k) a := by
  obtain ⟨N, hN⟩ := eventually_eps_updateful Q real ε M ρ hM hρ hε0 hlim hpol hcorr hU hρa (g / 2)
    (by positivity)
  refine ⟨N, fun n hn k a ha b => ?_⟩
  have hle := hN n hn k a ha b
  rcases hgap n k a b with heq | hge
  · exact le_of_eq heq
  · by_contra hlt
    have hpos : 0 < (Q n).homeEU (real k) b - (Q n).homeEU (real k) a := by
      linarith [not_le.mp hlt]
    rw [abs_of_pos hpos] at hge
    linarith

end Generic

/-- **The asymptotic clause, exact, without a gap condition — as a proposition** over a carrier
`(𝒮, m, 𝒟, A)` and horizon `K`: for every belief-state sequence `Q`, realized tables `real`,
correlation bounds `ε_n → 0`, uniform `M`, `ρ`, with positive points and `CorrBounded (Q n)
(real k) (ε n)` at every realized table, from some `n` on every one-step choice of `Q_n` at every
realized table is an updateful choice. Exactly the hypotheses of `eventually_eps_updateful` with
the *exact* conclusion. **Refuted** (`EpsCorrWitness.not_exactAsymptoticClause`, on core's
two-table carrier with `K = 2`): the slack `δ(ε_n) → 0` bounds the loss, not the choice, and a
home-value gap shrinking faster than the cross-branch correlation keeps the one-step choice on the
wrong side at every `n`. Until repair round 2 this was the package's one OPEN statement
(`eventually_updateful_exact`, stated with `sorry`, "not believed"); it is now a definition of
record whose negation is proved.
Source: bli-soto-b-046 ("eventually be optimal in that environment", read as *choice*); mandate T9
(the asymptotic clause "goes to `udt-bli-learning-open.txt`" — closed by refutation instead)
Kind: D
Fidelity: exact (the source's clause in the choice reading, finite horizon; the value reading is
`eventually_eps_updateful`) -/
def ExactAsymptoticClause (𝒮 : SmallIndex) (m : ℕ) (𝒟 : Finset (Table 𝒮 m)) (A : Type)
    [DecidableEq A] (K : ℕ) : Prop :=
  ∀ (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (ε : ℕ → ℚ) (M ρ : ℚ),
    0 ≤ M → 0 < ρ → (∀ n, 0 ≤ ε n) → (∀ η, 0 < η → ∃ N, ∀ n, N ≤ n → ε n ≤ η) →
    (∀ n (k : Fin K) c, 0 < (Q n).ppMass (real k) c) →
    (∀ n (k : Fin K), CorrBounded (Q n) (real k) (ε n)) →
    (∀ n ω, |(Q n).U ω| ≤ M) →
    (∀ n (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      ρ ≤ (Q n).branchProb (real k) (real k) a) →
    ∃ N, ∀ n, N ≤ n → ∀ (k : Fin K) a, (Q n).IsOneStepChoice (real k) a →
      (Q n).IsUpdatefulChoice (real k) a

/-! ## Not a squeeze: the conclusion at `ε = 0` without the hypothesis -/

variable {K : ℕ} (p : Params K)

/-- The joint mass of `Rec_j` under the point `Ask_j = a` is `(1 − q) w_j / 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_rec_askT (j : Fin K) (a : Bool) :
    (scPrior p).jointMass (recT K j) (askT K j) a = (1 - p.q) * p.w j * (1 / 2) := by
  unfold FiniteBLIPrior.jointMass scPrior
  have e := (scData p).massOf_rect (fun ω₀ : Base K => baseState ω₀ = recT K j)
    (fun π' => π' (askT K j) = a)
  change massOf (scData p).μ (fun ω => baseState ω.1 = recT K j ∧ ω.2 (askT K j) = a) = _
  rw [e, SingleCoin.massOf_point]
  change massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ = recT K j) * (1 / 2) = _
  rw [massOf_congr _ (fun ω₀ => baseState_eq_st_iff ω₀ false j)]
  unfold massOf
  rw [sum_base_single (baseMass p) false j]
  unfold baseMass
  simp

/-- **The cross-branch spread at `Rec_j` is `V γ_j`**: `condEU Rec_j Ask_j pay − condEU Rec_j Ask_j
refuse = V γ_j` (for `(1 − q) w_j > 0`) — the correlation the frozen prior believes in.
Source: bli-soto-a-070 ("correlations between actions and the *utility* of other branches");
mandate T9 (trap: squeeze check)
Kind: C (`condEU_base_askT_eq`)
Fidelity: exact
Hyps: (a) `q < 1`, `0 < w_j`; does not use faith -/
theorem condEU_rec_diff (j : Fin K) (hq1 : p.q < 1) (hw : 0 < p.w j) :
    (scPrior p).condEU (recT K j) (askT K j) true - (scPrior p).condEU (recT K j) (askT K j) false =
      p.V * p.γ j := by
  have hpos : 0 < baseMass p (false, j) := by
    unfold baseMass; simp only [Bool.false_eq_true, ↓reduceIte]; exact mul_pos (by linarith) hw
  rw [condEU_base_askT_eq p false j true hpos, condEU_base_askT_eq p false j false hpos]
  simp only [payoff, Bool.false_eq_true, ↓reduceIte, ind_true, ind_false]
  ring

/-- **`CorrBounded … 0` is not necessary for the conclusion (N−, the squeeze check)**: on `scPrior
p` with `gain < 0`, `0 < q < 1`, `0 < c`, `0 < V`, `0 < w_j`, `γ_j > 0`, at `Ask_j` every one-step
choice is an updateful choice (both uniquely `refuse`), yet `CorrBounded (scPrior p) Ask_j 0`
fails — the cross-branch spread at `Rec_j` is `V γ_j > 0`. The hypothesis of
`eps_corr_implies_eps_updateful` is strictly stronger than its conclusion.
Source: mandate T9 ("Trap: `corrBelief = 0` iff the conclusion (squeeze)")
Kind: N−
Fidelity: exact
Hyps: (a) positivity, `gain < 0`; does not use faith -/
theorem corrBounded_zero_not_necessary (j : Fin K) (hq : 0 < p.q) (hq1 : p.q < 1) (hc : 0 < p.c)
    (hV : 0 < p.V) (hw : 0 < p.w j) (hγ : 0 < p.γ j) (hg : gain p < 0) :
    (∀ a, (scPrior p).IsOneStepChoice (askT K j) a → (scPrior p).IsUpdatefulChoice (askT K j) a) ∧
      ¬ CorrBounded (scPrior p) (askT K j) 0 := by
  constructor
  · intro a ha
    have hd := EU_diff p j
    have hneg : p.γ j * gain p < 0 := mul_neg_of_pos_of_neg hγ hg
    have ha' : a = false := by
      cases a
      · rfl
      · exfalso; have := ha false; linarith
    subst ha'
    exact (isUpdatefulChoice_refuse p j hq hw hc hγ).1
  · rintro ⟨_, hcross⟩
    have hjm : ∀ a, 0 < (scPrior p).jointMass (recT K j) (askT K j) a := by
      intro a; rw [jointMass_rec_askT]; have := mul_pos (by linarith : 0 < 1 - p.q) hw; linarith
    have h := hcross (recT K j) true false (SingleCoin.askT_ne_recT j j).symm (hjm true) (hjm false)
    rw [condEU_rec_diff p j hq1 hw, abs_of_pos (mul_pos hV hγ)] at h
    exact absurd (mul_pos hV hγ) (not_lt.mpr h)

end Cleanroom.Bli.UdtBliLearning
