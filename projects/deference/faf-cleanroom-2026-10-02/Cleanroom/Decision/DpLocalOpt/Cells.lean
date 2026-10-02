import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Ssa

/-!
# `dp-local-opt`: the anthropic 2×2 (T12), and conditioning on one's own draw (T13(a))

The four own-draw evaluators of SE-11 are defined at the (run, instance) level: on each leaf `ℓ`
the evaluator of `a` at `d` weights `r(ℓ)` by the run law (`μ_C` under Definition 6, `μ'_C` under
6′), an instance weight (`1` per occurrence — SIA; `1/#_d(ℓ)` per run — SSA) and the number
`nInst_a(ℓ) = countDraw d a B ℓ` of `d`-instances on `ℓ` that drew `a`, then normalises. Two cells
are identified with the two theorems of §8:

* **(Definition 6, per-occurrence) = Theorem 1 normalised** (`ownDraw6Occ_eq`): the evaluator is
  `Φ_d(C, a) / 𝔼[#_d]`, because `∑_ℓ μ_C(ℓ) nInst_a(ℓ) r(ℓ) = C(d)(a) Φ_d(C, a)` and
  `∑_ℓ μ_C(ℓ) nInst_a(ℓ) = C(d)(a) 𝔼[#_d]` (`sum_leafLaw_countDraw_mul_payoff`,
  `sum_leafLaw_countDraw`); with full support at `d` its argmax is `Thm1At`'s
  (`thm1At_iff_ownDraw6Occ`).
* **(Definition 6′, per-run) = Theorem 2′** (`ownDraw6'Run_eq`): under the shared seed all
  `d`-instances of a run draw alike (`seed_pure_draws`), so `nInst_a(ℓ)/#_d(ℓ) ∈ {0, 1}` and the
  evaluator is `∑_{ℓ ∈ occ(d)} μ'_{C[d↦a]}(ℓ) r(ℓ) / μ'_C(occ(d))`, whose argmax is
  `argmax_a V'_B(C[d ↦ a])` (`ownDraw6'Run_le_iff`).
* **SE-21, the fork closes under 6′** (`thm1'At_iff_coherent'At`,
  `coherent'At_iff_coherentPure'At`): `V'_B` is affine in `C(d)`, so Theorem 1's marginal
  condition, Theorem 2′'s total condition and Definition 22 (pure = mixed) coincide on every tree.
* **T13(a)** (`condDraw_eq_forced`): under Definition 6, `𝔼_C[r · 1(edge_q = a)] = C(d_q)(a) ·
  forcedBelow(q, a)` and `μ_C(edge_q = a) = C(d_q)(a) R_q` (`mass_edge`): conditioning on one's
  own draw at a node is single-instance forcing there — Appendix B's conjecture in the
  full-support case.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-! ### `countDraw` node equations -/

section countDraw

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem countDraw_leaf (d : ι) (a : acts d) (ω : Ω) (r : K)
    (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) : countDraw d a (leaf ω r) ℓ = 0 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem countDraw_chance (d : ι) (a : acts d) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    countDraw d a (chance n β child) ⟨i, ℓ⟩ = countDraw d a (child i) ℓ := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem countDraw_decision (d : ι) (a : acts d) (d' : ι) (child : acts d' → Tree Ω ι acts K)
    (c : acts d') (ℓ : (child c).Leaves) :
    countDraw d a (decision d' child) ⟨c, ℓ⟩ =
      countDraw d a (child c) ℓ + if (⟨d', c⟩ : Σ e, acts e) = ⟨d, a⟩ then 1 else 0 := by
  simp only [countDraw, draws_decision, List.count_cons, beq_iff_eq]

/-- At a `d`-node the indicator is `[c = a]`.
Source: none: infrastructure
Kind: L -/
theorem countDraw_decision_self (d : ι) (a : acts d) (child : acts d → Tree Ω ι acts K)
    (c : acts d) (ℓ : (child c).Leaves) :
    countDraw d a (decision d child) ⟨c, ℓ⟩ = countDraw d a (child c) ℓ + if c = a then 1 else 0 := by
  rw [countDraw_decision]
  simp

/-- At a node carrying another point the indicator is `0`.
Source: none: infrastructure
Kind: L -/
theorem countDraw_decision_ne (d : ι) (a : acts d) {d' : ι} (h : d' ≠ d)
    (child : acts d' → Tree Ω ι acts K) (c : acts d') (ℓ : (child c).Leaves) :
    countDraw d a (decision d' child) ⟨c, ℓ⟩ = countDraw d a (child c) ℓ := by
  rw [countDraw_decision]
  simp [h]

end countDraw

/-! ### (Definition 6, per-occurrence) = Theorem 1 normalised -/

section cell6occ

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The (Definition 6, per-occurrence) own-draw evaluator** of `a` at `d`: each `d`-instance on
each leaf that drew `a` weighted by the run law `μ_C`, payoff-averaged and normalised.
Source: `repair/seeds.md` SE-11 (the "(Definition 6, SIA)" cell); [[fable-slop-notes]] Claim 4.1
Kind: D
Fidelity: exact (`r := payoff B`; `nInst_a(ℓ) := countDraw d a B ℓ`, the number of `d`-nodes on
the path that took the `a`-edge) -/
def ownDraw6Occ (a : acts d) : K :=
  (∑ ℓ, leafLaw C B ℓ * (countDraw d a B ℓ : K) * payoff B ℓ) /
    (∑ ℓ, leafLaw C B ℓ * (countDraw d a B ℓ : K))

/-- `𝔼[#_d]` at a chance node.
Source: none: infrastructure
Kind: L -/
theorem expCount_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    expCount C (chance n β child) d = ∑ i, β.w i * expCount C (child i) d := by
  unfold expCount
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by simp only [leafLaw_chance, count_chance]; ring

/-- `𝔼[#_d]` at a node carrying another point.
Source: none: infrastructure
Kind: L -/
theorem expCount_decision_ne {d' : ι} (h : d' ≠ d) (child : acts d' → Tree Ω ι acts K) :
    expCount C (decision d' child) d = ∑ c, (C d').w c * expCount C (child c) d := by
  unfold expCount
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by
    simp only [leafLaw_decision, count_decision, if_neg h, zero_add]; ring

/-- `𝔼[#_d]` at a `d`-node: one plus the `C(d)`-average of the children's.
Source: none: infrastructure
Kind: L -/
theorem expCount_decision_self (child : acts d → Tree Ω ι acts K) :
    expCount C (decision d child) d = 1 + ∑ c, (C d).w c * expCount C (child c) d := by
  unfold expCount
  rw [sum_leaves_decision]
  have hc : ∀ c, ∑ ℓ, leafLaw C (decision d child) ⟨c, ℓ⟩ *
      (count d (decision d child) ⟨c, ℓ⟩ : K) =
      (C d).w c * (1 + ∑ ℓ, leafLaw C (child c) ℓ * (count d (child c) ℓ : K)) := by
    intro c
    have h1 : (C d).w c = ∑ ℓ, (C d).w c * leafLaw C (child c) ℓ := by
      rw [← Finset.mul_sum, sum_leafLaw, mul_one]
    symm
    calc (C d).w c * (1 + ∑ ℓ, leafLaw C (child c) ℓ * (count d (child c) ℓ : K))
        = ∑ ℓ, ((C d).w c * leafLaw C (child c) ℓ +
            (C d).w c * (leafLaw C (child c) ℓ * (count d (child c) ℓ : K))) := by
          rw [Finset.sum_add_distrib, ← h1, ← Finset.mul_sum]; ring
      _ = _ := by
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          simp only [leafLaw_decision, count_decision, if_true]
          push_cast; ring
  simp only [hc, mul_add, mul_one, Finset.sum_add_distrib, (C d).sum_one]

/-- `∑_ℓ μ_C(ℓ) nInst_a(ℓ) r(ℓ) = C(d)(a) Φ_d(C, a)`: the `a`-instances' payoff mass is the draw
weight times Theorem 1's functional (conditioning on the draw at a node is forcing there).
Source: [[fable-slop-notes]] Claim 4.1 ("conditioning on it equals forcing it"); mandate T12(a)
Kind: P
Fidelity: exact -/
theorem sum_leafLaw_countDraw_mul_payoff (a : acts d) :
    (B : Tree Ω ι acts K) →
      ∑ ℓ, leafLaw C B ℓ * (countDraw d a B ℓ : K) * payoff B ℓ = (C d).w a * siaSum C B d a
  | leaf _ _ => by simp
  | chance _ β child => by
      rw [sum_leaves_chance, siaSum_chance, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ih := sum_leafLaw_countDraw_mul_payoff a (child i)
      simp only [leafLaw_chance, countDraw_chance, payoff_chance]
      have e : (C d).w a * (β.w i * siaSum C (child i) d a) =
          β.w i * ((C d).w a * siaSum C (child i) d a) := by ring
      rw [e, ← ih, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  | decision d' child => by
      have ih : ∀ c, ∑ ℓ, leafLaw C (child c) ℓ * (countDraw d a (child c) ℓ : K) *
          payoff (child c) ℓ = (C d).w a * siaSum C (child c) d a :=
        fun c => sum_leafLaw_countDraw_mul_payoff a (child c)
      rw [sum_leaves_decision]
      by_cases hd : d' = d
      · subst hd
        rw [siaSum_decision_self]
        have hterm : ∀ c, ∑ ℓ, leafLaw C (decision d' child) ⟨c, ℓ⟩ *
            (countDraw d' a (decision d' child) ⟨c, ℓ⟩ : K) * payoff (decision d' child) ⟨c, ℓ⟩ =
            (C d').w c * ((C d').w a * siaSum C (child c) d' a) +
              if c = a then (C d').w c * value C (child c) else 0 := by
          intro c
          simp only [leafLaw_decision, countDraw_decision_self, payoff_decision]
          rw [← ih c, value, Finset.mul_sum, Finset.mul_sum]
          by_cases hc : c = a
          · subst hc
            simp only [if_true, eq_self_iff_true, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            push_cast; ring
          · simp only [hc, if_false, add_zero]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            ring
        simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by ring
      · rw [siaSum_decision_ne C hd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [leafLaw_decision, countDraw_decision_ne d a hd, payoff_decision]
        have e : (C d).w a * ((C d').w c * siaSum C (child c) d a) =
            (C d').w c * ((C d).w a * siaSum C (child c) d a) := by ring
        rw [e, ← ih c, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- `∑_ℓ μ_C(ℓ) nInst_a(ℓ) = C(d)(a) 𝔼[#_d]`: the `a`-instances' mass is the draw weight times
the expected occurrence count (`= C(d)(a) ∑_{q : d_q = d} R_q`, by `sum_reach_fiber_eq_expCount`).
Source: mandate T12(a) ("`∑_ℓ λ ℓ · nInst_a ℓ = C(d)(a) · ∑_q R_q`")
Kind: P
Fidelity: exact -/
theorem sum_leafLaw_countDraw (a : acts d) :
    (B : Tree Ω ι acts K) →
      ∑ ℓ, leafLaw C B ℓ * (countDraw d a B ℓ : K) = (C d).w a * expCount C B d
  | leaf _ _ => by simp [expCount]
  | chance _ β child => by
      rw [sum_leaves_chance, expCount_chance, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ih := sum_leafLaw_countDraw a (child i)
      simp only [leafLaw_chance, countDraw_chance]
      have e : (C d).w a * (β.w i * expCount C (child i) d) =
          β.w i * ((C d).w a * expCount C (child i) d) := by ring
      rw [e, ← ih, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => by ring
  | decision d' child => by
      have ih : ∀ c, ∑ ℓ, leafLaw C (child c) ℓ * (countDraw d a (child c) ℓ : K) =
          (C d).w a * expCount C (child c) d := fun c => sum_leafLaw_countDraw a (child c)
      rw [sum_leaves_decision]
      by_cases hd : d' = d
      · subst hd
        rw [expCount_decision_self]
        have hterm : ∀ c, ∑ ℓ, leafLaw C (decision d' child) ⟨c, ℓ⟩ *
            (countDraw d' a (decision d' child) ⟨c, ℓ⟩ : K) =
            (C d').w c * ((C d').w a * expCount C (child c) d') +
              if c = a then (C d').w c else 0 := by
          intro c
          simp only [leafLaw_decision, countDraw_decision_self]
          rw [← ih c, Finset.mul_sum]
          by_cases hc : c = a
          · subst hc
            simp only [if_true, eq_self_iff_true]
            have h1 : ∑ ℓ, (C d').w c * leafLaw C (child c) ℓ = (C d').w c := by
              rw [← Finset.mul_sum, sum_leafLaw, mul_one]
            calc ∑ x, (C d').w c * leafLaw C (child c) x *
                  ((countDraw d' c (child c) x + 1 : ℕ) : K)
                = ∑ x, ((C d').w c * (leafLaw C (child c) x * (countDraw d' c (child c) x : K)) +
                    (C d').w c * leafLaw C (child c) x) := by
                  refine Finset.sum_congr rfl fun ℓ _ => ?_
                  push_cast; ring
              _ = _ := by rw [Finset.sum_add_distrib, h1]
          · simp only [hc, if_false, add_zero]
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            ring
        simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_add, mul_one, Finset.mul_sum, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun c _ => by ring
      · rw [expCount_decision_ne C d hd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [leafLaw_decision, countDraw_decision_ne d a hd]
        have e : (C d).w a * ((C d').w c * expCount C (child c) d) =
            (C d').w c * ((C d).w a * expCount C (child c) d) := by ring
        rw [e, ← ih c, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- **(Definition 6, per-occurrence) = Theorem 1 normalised**: for `C(d)(a) > 0`,
`ownDraw6Occ(a) = Φ_d(C, a) / 𝔼[#_d]` — v2's SIA-weighted single-instance-causal value
`∑_q (R_q / 𝔼[#_d]) G_q(C, a)`.
Source: `repair/seeds.md` SE-11, SE-21 ("per-occurrence weights are Theorem 1's");
[[fable-slop-notes]] Claim 4.1 ("Averaging over which instance I am with per-occurrence (SIA)
weights `R_q / 𝔼_μ[#_d]` gives exactly Theorem 1's condition") | dp-core-066 | dp-cf-057
Kind: P
Fidelity: exact (`r := payoff B`)
Hyps: (a) `0 < C(d)(a)` (SE-11's full-support hypothesis, per action) -/
theorem ownDraw6Occ_eq {a : acts d} (ha : 0 < (C d).w a) :
    ownDraw6Occ C B d a = siaSum C B d a / expCount C B d := by
  unfold ownDraw6Occ
  rw [sum_leafLaw_countDraw_mul_payoff, sum_leafLaw_countDraw, mul_div_mul_left _ _ ha.ne']

/-- **With full support at `d` and `d` reached, the (Definition 6, per-occurrence) cell's argmax
condition is Theorem 1's.** Under full support both sides are the *tie* condition (every action's
`Φ_d(C, ·)`, resp. every cell value, equal): Theorem 1's `supp C(d) ⊆ argmax` with full support
says `Φ_d(C, ·)` is constant. The identification of the cell with Theorem 1's functional for
*every* `C` (argmax sets coincide over the actions of positive weight) is `ownDraw6Occ_eq`
(`= Φ_d(C,a)/𝔼[#_d]`); this iff is its full-support corollary. Evaluated on the AMD in
`NestedWitness.lean` (`amd_ownDraw6Occ`, `amd_cells_differ_at_third`).
Source: `repair/seeds.md` SE-11; mandate T12(a); audit r1 adversarial N3
Kind: C
Fidelity: exact
Hyps: (a) full support at `d` and `0 < 𝔼[#_d]` (SE-11's hypotheses) -/
theorem thm1At_iff_ownDraw6Occ (hfs : ∀ b, 0 < (C d).w b) (hE : 0 < expCount C B d) :
    Thm1At C B d ↔ ∀ a b, ownDraw6Occ C B d b ≤ ownDraw6Occ C B d a := by
  unfold Thm1At
  simp only [ownDraw6Occ_eq C B d (hfs _), div_le_div_iff_of_pos_right hE]
  exact ⟨fun h a b => h a (hfs a) b, fun h a _ b => h a b⟩

end cell6occ

/-! ### The shared seed: all instances on a run draw alike -/

section seed

variable (C : Proc ι acts K) (d : ι)

/-- **Under the shared seed, a procedure pure at `d` has every `d`-instance of a positive run draw
`b`**: if `leafLawSeed C' env B ℓ ≠ 0` with `C'(d) = δ_b` and the seed for `d` either undrawn or
`b`, then `nInst_x(ℓ) = [x = b] · #_d(ℓ)`.
Source: `repair/seeds.md` Definition 6′ ("one seed per queried point per run, reused at every node
carrying it"); mandate T12(b)
Kind: P -/
theorem seed_pure_draws (C' : Proc ι acts K) (b : acts d) (hC' : C' d = FinDistr.pure b) :
    (B : Tree Ω ι acts K) → ∀ (env : (e : ι) → Option (acts e)) (ℓ : B.Leaves),
      (env d = none ∨ env d = some b) → leafLawSeed C' env B ℓ ≠ 0 →
      ∀ x, countDraw d x B ℓ = if x = b then count d B ℓ else 0
  | leaf _ _, _, _, _, _, x => by simp
  | chance _ β child, env, ⟨i, ℓ⟩, henv, hne, x => by
      rw [leafLawSeed_chance] at hne
      have := seed_pure_draws C' b hC' (child i) env ℓ henv (right_ne_zero_of_mul hne) x
      simpa using this
  | decision d' child, env, ⟨c, ℓ⟩, henv, hne, x => by
      have ih : ∀ (env' : (e : ι) → Option (acts e)), (env' d = none ∨ env' d = some b) →
          leafLawSeed C' env' (child c) ℓ ≠ 0 →
          countDraw d x (child c) ℓ = if x = b then count d (child c) ℓ else 0 :=
        fun env' henv' hne' => seed_pure_draws C' b hC' (child c) env' ℓ henv' hne' x
      by_cases hd : d' = d
      · subst hd
        rcases henv with h0 | hs
        · rw [leafLawSeed_decision_of_none C' h0] at hne
          have hc : c = b := by
            have := left_ne_zero_of_mul hne
            rw [hC', FinDistr.pure_w] at this
            by_contra hcb; exact this (if_neg hcb)
          subst hc
          rw [countDraw_decision_self, ih (Function.update env d' (some c)) (Or.inr (by simp))
            (right_ne_zero_of_mul hne), count_decision, if_pos rfl]
          by_cases hx : x = c
          · subst hx; simp; omega
          · simp [hx, Ne.symm hx]
        · rw [leafLawSeed_decision_of_some C' hs] at hne
          have hc : b = c := by by_contra h; rw [if_neg h] at hne; exact hne rfl
          subst hc
          rw [countDraw_decision_self, ih env (Or.inr hs) (by rwa [if_pos rfl] at hne),
            count_decision, if_pos rfl]
          by_cases hx : x = b
          · subst hx; simp; omega
          · simp [hx, Ne.symm hx]
      · have hne' : d ≠ d' := fun h => hd h.symm
        rcases h' : env d' with _ | a'
        · rw [leafLawSeed_decision_of_none C' h'] at hne
          rw [countDraw_decision_ne d x hd, ih (Function.update env d' (some c))
            (by rwa [Function.update_of_ne hne']) (right_ne_zero_of_mul hne), count_decision,
            if_neg hd, zero_add]
        · rw [leafLawSeed_decision_of_some C' h'] at hne
          have hc : a' = c := by by_contra h; rw [if_neg h] at hne; exact hne rfl
          subst hc
          rw [countDraw_decision_ne d x hd, ih env henv (by rwa [if_pos rfl] at hne),
            count_decision, if_neg hd, zero_add]

/-- Under the shared seed, procedures agreeing off `d` give the same seeded mass to every leaf
whose path meets no `d`-node.
Source: `repair/seeds.md` SE-1(c) (Lemma 1 under 6′); mandate T12(b)
Kind: P -/
theorem leafLawSeed_congr_off_of_count_zero {C' : Proc ι acts K} (h : ∀ e, e ≠ d → C' e = C e) :
    (B : Tree Ω ι acts K) → ∀ (env : (e : ι) → Option (acts e)) (ℓ : B.Leaves),
      count d B ℓ = 0 → leafLawSeed C' env B ℓ = leafLawSeed C env B ℓ
  | leaf _ _, _, _, _ => rfl
  | chance _ β child, env, ⟨i, ℓ⟩, hc => by
      rw [leafLawSeed_chance, leafLawSeed_chance,
        leafLawSeed_congr_off_of_count_zero h (child i) env ℓ (by simpa using hc)]
  | decision d' child, env, ⟨c, ℓ⟩, hc => by
      have hd : d' ≠ d := by
        intro e; subst e; simp at hc
      have hc' : count d (child c) ℓ = 0 := by simpa [count_decision, hd] using hc
      rcases h' : env d' with _ | a'
      · rw [leafLawSeed_decision_of_none C' h', leafLawSeed_decision_of_none C h', h d' hd,
          leafLawSeed_congr_off_of_count_zero h (child c) _ ℓ hc']
      · rw [leafLawSeed_decision_of_some C' h', leafLawSeed_decision_of_some C h',
          leafLawSeed_congr_off_of_count_zero h (child c) _ ℓ hc']

/-- Off `occ(d)`, the shared-seed law of `C[d ↦ m]` is that of `C`.
Source: `repair/seeds.md` SE-1(c)
Kind: L -/
theorem leafLaw'_deviate_of_not_occ (B : Tree Ω ι acts K) (m : FinDistr K (acts d)) {ℓ : B.Leaves}
    (hℓ : ℓ ∉ occ d B) : leafLaw' (C.deviate d m) B ℓ = leafLaw' C B ℓ :=
  leafLawSeed_congr_off_of_count_zero C d (fun e he => Proc.deviate_ne C m he) B _ ℓ
    (by simpa [occ] using hℓ)

/-- For a procedure pure at `d`, `μ'(ℓ) · nInst_a(ℓ) = [a = b] · μ'(ℓ) · #_d(ℓ)`.
Source: mandate T12(b) ("`nInst_a ℓ ∈ {0, #_d(ℓ)}`")
Kind: L -/
theorem leafLaw'_deviatePure_mul_countDraw (B : Tree Ω ι acts K) (b a : acts d) (ℓ : B.Leaves) :
    leafLaw' (C.deviatePure d b) B ℓ * (countDraw d a B ℓ : K) =
      if a = b then leafLaw' (C.deviatePure d b) B ℓ * (count d B ℓ : K) else 0 := by
  by_cases h : leafLaw' (C.deviatePure d b) B ℓ = 0
  · simp [h]
  · rw [seed_pure_draws d (C.deviatePure d b) b (Proc.deviate_same C d (FinDistr.pure b)) B
      (fun _ => none) ℓ (Or.inl rfl) h a]
    split_ifs <;> simp

/-- `μ'_C(ℓ) · nInst_a(ℓ)/#_d(ℓ) = [ℓ ∈ occ(d)] · C(d)(a) · μ'_{C[d↦a]}(ℓ)`: under the shared seed
the per-run instance weight of `a` on a leaf is the probability that the run's seed for `d` is
`a`.
Source: mandate T12(b) ("the `1/#_d` cancels")
Kind: P -/
theorem leafLaw'_mul_ratio (B : Tree Ω ι acts K) (a : acts d) (ℓ : B.Leaves) :
    leafLaw' C B ℓ * ((countDraw d a B ℓ : K) / (count d B ℓ : K)) =
      if 0 < count d B ℓ then (C d).w a * leafLaw' (C.deviatePure d a) B ℓ else 0 := by
  rw [leafLaw'_deviate_sum C B d ℓ, Finset.sum_mul]
  have hterm : ∀ b, (C d).w b * leafLaw' (C.deviatePure d b) B ℓ *
      ((countDraw d a B ℓ : K) / (count d B ℓ : K)) =
      if b = a then (C d).w a * (leafLaw' (C.deviatePure d a) B ℓ *
        ((count d B ℓ : K) / (count d B ℓ : K))) else 0 := by
    intro b
    have key := leafLaw'_deviatePure_mul_countDraw C d B b a ℓ
    by_cases hab : b = a
    · subst hab
      rw [if_pos rfl]
      calc (C d).w b * leafLaw' (C.deviatePure d b) B ℓ *
            ((countDraw d b B ℓ : K) / (count d B ℓ : K))
          = (C d).w b * ((leafLaw' (C.deviatePure d b) B ℓ * (countDraw d b B ℓ : K)) /
              (count d B ℓ : K)) := by ring
        _ = _ := by rw [key, if_pos rfl]; ring
    · rw [if_neg hab]
      calc (C d).w b * leafLaw' (C.deviatePure d b) B ℓ *
            ((countDraw d a B ℓ : K) / (count d B ℓ : K))
          = (C d).w b * ((leafLaw' (C.deviatePure d b) B ℓ * (countDraw d a B ℓ : K)) /
              (count d B ℓ : K)) := by ring
        _ = 0 := by rw [key, if_neg (Ne.symm hab)]; simp
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with hc
  · have : (count d B ℓ : K) ≠ 0 := by exact_mod_cast hc.ne'
    rw [div_self this, mul_one]
  · have : count d B ℓ = 0 := Nat.eq_zero_of_not_pos hc
    simp [this]

end seed

/-! ### (Definition 6′, per-run) = Theorem 2′ -/

section cell6run

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The (Definition 6′, per-run) own-draw evaluator** of `a` at `d`: each `d`-instance on each
leaf that drew `a`, weighted by the shared-seed law `μ'_C` and by `1/#_d(ℓ)` (SSA), payoff-averaged
and normalised. Lean's `x / 0 = 0` applies off `occ(d)` (where `#_d = 0`), harmlessly: those
leaves carry no instance.
Source: `repair/seeds.md` SE-11 (the "(shared, SSA)" cell); [[fable-slop-notes]] Claim 4.2
Kind: D
Fidelity: exact (`r := payoff B`) -/
def ownDraw6'Run (a : acts d) : K :=
  (∑ ℓ, leafLaw' C B ℓ * ((countDraw d a B ℓ : K) / (count d B ℓ : K)) * payoff B ℓ) /
    (∑ ℓ, leafLaw' C B ℓ * ((countDraw d a B ℓ : K) / (count d B ℓ : K)))

/-- The on-occurrence shared-seed payoff mass of `C[d ↦ a]`.
Source: `repair/seeds.md` SE-12′(i) (Theorem 2′)
Kind: D -/
def ssaNum' (a : acts d) : K := ∑ ℓ ∈ occ d B, leafLaw' (C.deviatePure d a) B ℓ * payoff B ℓ

/-- The off-occurrence shared-seed payoff mass of `C`.
Source: `repair/seeds.md` SE-12′(i)
Kind: D -/
def offOcc' : K := ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ occ d B), leafLaw' C B ℓ * payoff B ℓ

/-- `V'_B(C[d ↦ a]) = ssaNum'(a) + offOcc'`, the off-occurrence part free of `a`.
Source: `repair/seeds.md` SE-12′(i)
Kind: P -/
theorem value'_deviatePure_eq (a : acts d) :
    value' (C.deviatePure d a) B = ssaNum' C B d a + offOcc' C B d := by
  unfold value' ssaNum' offOcc'
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ => ℓ ∈ occ d B)]
  congr 1
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Finset.mem_filter] at hℓ
    rw [Proc.deviatePure, leafLaw'_deviate_of_not_occ C d B _ hℓ.2]

/-- **(Definition 6′, per-run) = Theorem 2′**: for `C(d)(a) > 0`,
`ownDraw6'Run(a) = ssaNum'(a) / μ'_C(occ(d))` — the shared-seed EDT+SSA evaluator is the
occurrence-conditioned value of the all-instance deviation.
Source: `repair/seeds.md` SE-12′(i) ("The (shared, SSA) evaluator equals Theorem 2′ … on
**every** tree"); [[fable-slop-notes]] Claim 4.2 | dp-core-066 | dp-cf-057 | dp-cf-061
Kind: P
Fidelity: exact (`r := payoff B`)
Hyps: (a) `0 < C(d)(a)` (SE-12′'s full-support hypothesis, per action) -/
theorem ownDraw6'Run_eq {a : acts d} (ha : 0 < (C d).w a) :
    ownDraw6'Run C B d a = ssaNum' C B d a / ∑ ℓ ∈ occ d B, leafLaw' C B ℓ := by
  unfold ownDraw6'Run ssaNum'
  have hnum : ∑ ℓ, leafLaw' C B ℓ * ((countDraw d a B ℓ : K) / (count d B ℓ : K)) * payoff B ℓ =
      (C d).w a * ∑ ℓ ∈ occ d B, leafLaw' (C.deviatePure d a) B ℓ * payoff B ℓ := by
    rw [occ, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [leafLaw'_mul_ratio C d B a ℓ]
    split_ifs <;> ring
  have hden : ∑ ℓ, leafLaw' C B ℓ * ((countDraw d a B ℓ : K) / (count d B ℓ : K)) =
      (C d).w a * ∑ ℓ ∈ occ d B, leafLaw' C B ℓ := by
    rw [← occurrence_constancy' C B d (FinDistr.pure a), occ, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [leafLaw'_mul_ratio C d B a ℓ]
    split_ifs <;> simp [Proc.deviatePure]
  rw [hnum, hden, mul_div_mul_left _ _ ha.ne']

/-- **Theorem 2′, argmax form**: with `0 < μ'_C(occ(d))` and full support at `a`, `b`,
`ownDraw6'Run(b) ≤ ownDraw6'Run(a) ↔ V'_B(C[d ↦ b]) ≤ V'_B(C[d ↦ a])`.
Source: `repair/seeds.md` SE-12′(i) ("whose argmax is `argmax_a V'_B(C[d↦a])`")
Kind: C
Fidelity: exact
Hyps: (a) `0 < μ'_C(occ(d))`, `0 < C(d)(a)`, `0 < C(d)(b)` -/
theorem ownDraw6'Run_le_iff (hpos : 0 < ∑ ℓ ∈ occ d B, leafLaw' C B ℓ) {a b : acts d}
    (ha : 0 < (C d).w a) (hb : 0 < (C d).w b) :
    ownDraw6'Run C B d b ≤ ownDraw6'Run C B d a ↔
      value' (C.deviatePure d b) B ≤ value' (C.deviatePure d a) B := by
  rw [ownDraw6'Run_eq C B d ha, ownDraw6'Run_eq C B d hb, div_le_div_iff_of_pos_right hpos,
    value'_deviatePure_eq, value'_deviatePure_eq, add_le_add_iff_right]

end cell6run

/-! ### SE-21: the fork closes under 6′ -/

section se21

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- Theorem 1's condition under 6′ (first-order for `V'`, which is affine in `C(d)`, so the
"gradient" toward `δ_b` is `V'_B(C[d ↦ b])`): `supp C(d) ⊆ argmax_a V'_B(C[d ↦ a])`.
Source: `repair/seeds.md` SE-21 ("first-order optimality over `Δ(A_d)` reads
`supp C(d) ⊆ argmax_a V'_B(C[d↦a])`")
Kind: D -/
def Thm1'At : Prop :=
  ∀ a, 0 < (C d).w a → ∀ b, value' (C.deviatePure d b) B ≤ value' (C.deviatePure d a) B

/-- Mixed Definition 22 under 6′.
Source: `repair/seeds.md` SE-21
Kind: D -/
def Coherent'At : Prop := ∀ m : FinDistr K (acts d), value' (C.deviate d m) B ≤ value' C B

/-- Pure Definition 22 under 6′.
Source: `repair/seeds.md` SE-21
Kind: D -/
def CoherentPure'At : Prop := ∀ a, value' (C.deviatePure d a) B ≤ value' C B

/-- Deviating twice at `d` is deviating once.
Source: none: infrastructure
Kind: L -/
theorem Proc.deviate_deviate' (m m' : FinDistr K (acts d)) :
    (C.deviate d m).deviate d m' = C.deviate d m' := by
  unfold Proc.deviate; simp

/-- `V'_B(C[d ↦ m]) = ∑_a m(a) V'_B(C[d ↦ a])` on every tree.
Source: `repair/seeds.md` SE-1(b) (`value'_deviate_sum`)
Kind: L -/
theorem value'_deviate_eq_sum (m : FinDistr K (acts d)) :
    value' (C.deviate d m) B = ∑ a, m.w a * value' (C.deviatePure d a) B := by
  rw [value'_deviate_sum _ B d]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Proc.deviate_same, Proc.deviatePure, Proc.deviate_deviate']

/-- `V'_B(C) = ∑_a C(d)(a) V'_B(C[d ↦ a])`.
Source: `repair/seeds.md` SE-1(b)
Kind: L -/
theorem value'_eq_sum_deviatePure :
    value' C B = ∑ a, (C d).w a * value' (C.deviatePure d a) B :=
  value'_deviate_sum C B d

/-- **The finite-difference form of `Thm1'At`**: under 6′, moving `C(d)` by `ε` toward `δ_b`
changes `V'` by exactly `ε (V'(C[d ↦ b]) − V'(C))` — the "gradient toward `δ_b`" that `Thm1'At`
compares is the derivative of the affine `V'` in `C(d)`, so SE-21's argmax form *is* first-order
optimality, not a definition.
Source: `repair/seeds.md` SE-21 ("first-order optimality over `Δ(A_d)` reads
`supp C(d) ⊆ argmax_a V'_B(C[d↦a])`"); audit r1 fidelity non-blocking 7 / adversarial N4
Kind: P
Fidelity: exact -/
theorem value'_lerp_deviatePure (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (b : acts d) :
    value' (C.deviate d (FinDistr.lerp ε h0 h1 (C d) (FinDistr.pure b))) B =
      value' C B + ε * (value' (C.deviatePure d b) B - value' C B) := by
  have hS := value'_eq_sum_deviatePure C B d
  rw [value'_deviate_eq_sum]
  have : ∀ a, (FinDistr.lerp ε h0 h1 (C d) (FinDistr.pure b)).w a =
      (1 - ε) * (C d).w a + ε * (if a = b then 1 else 0) := fun a => by
    rw [FinDistr.lerp_w, FinDistr.pure_w]
  simp only [this, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hS]
  ring

/-- **SE-21 (i): under 6′ Theorem 1's condition and mixed Definition 22 coincide on every tree.**
Source: `repair/seeds.md` SE-21 ("Theorem 1's marginal condition, Theorem 2′'s total condition
and Definition 22 (pure = mixed deviations) coincide on every tree") | dp-core-066 | dp-cf-061
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem thm1'At_iff_coherent'At : Thm1'At C B d ↔ Coherent'At C B d := by
  constructor
  · intro h m
    rw [value'_deviate_eq_sum, value'_eq_sum_deviatePure C B d]
    have hmax : ∀ b, value' (C.deviatePure d b) B ≤ ∑ a, (C d).w a * value' (C.deviatePure d a) B := by
      intro b
      have hle : ∀ a, 0 < (C d).w a →
          value' (C.deviatePure d b) B ≤ value' (C.deviatePure d a) B := fun a ha => h a ha b
      calc value' (C.deviatePure d b) B = ∑ a, (C d).w a * value' (C.deviatePure d b) B := by
            rw [← Finset.sum_mul, (C d).sum_one, one_mul]
        _ ≤ ∑ a, (C d).w a * value' (C.deviatePure d a) B := by
            apply Finset.sum_le_sum
            intro a _
            rcases ((C d).nonneg a).lt_or_eq with ha | ha
            · exact mul_le_mul_of_nonneg_left (hle a ha) ha.le
            · rw [← ha]; simp
    calc ∑ a, m.w a * value' (C.deviatePure d a) B
        ≤ ∑ a, m.w a * ∑ a', (C d).w a' * value' (C.deviatePure d a') B :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmax a) (m.nonneg a)
      _ = _ := by rw [← Finset.sum_mul, m.sum_one, one_mul]
  · intro h a ha b
    -- first-order necessity toward `δ_b`, exact since `V'` is affine
    have hle : ∀ b', value' (C.deviatePure d b') B ≤ ∑ a', (C d).w a' * value' (C.deviatePure d a') B := by
      intro b'
      have := h (FinDistr.pure b')
      rw [value'_deviate_eq_sum, value'_eq_sum_deviatePure C B d] at this
      simpa [FinDistr.pure_w, Finset.sum_ite_eq'] using this
    have hge : ∑ a', (C d).w a' * value' (C.deviatePure d a') B ≤ value' (C.deviatePure d a) B := by
      by_contra hlt
      replace hlt := not_le.mp hlt
      have : ∑ a', (C d).w a' * value' (C.deviatePure d a') B <
          ∑ a', (C d).w a' * ∑ a'', (C d).w a'' * value' (C.deviatePure d a'') B := by
        apply Finset.sum_lt_sum
        · intro a' _; exact mul_le_mul_of_nonneg_left (hle a') ((C d).nonneg a')
        · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left hlt ha⟩
      rw [← Finset.sum_mul, (C d).sum_one, one_mul] at this
      exact lt_irrefl _ this
    exact (hle b).trans hge

/-- **SE-21 (ii): under 6′ the pure and mixed forms of Definition 22 coincide on every tree.**
Source: `repair/seeds.md` SE-21 ("P1:synthesis item 25's pure/mixed seam does not exist under
6′") | A30
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem coherent'At_iff_coherentPure'At : Coherent'At C B d ↔ CoherentPure'At C B d := by
  constructor
  · intro h a; exact h (FinDistr.pure a)
  · intro h m
    rw [value'_deviate_eq_sum]
    calc ∑ a, m.w a * value' (C.deviatePure d a) B ≤ ∑ a, m.w a * value' C B :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (m.nonneg a)
      _ = value' C B := by rw [← Finset.sum_mul, m.sum_one, one_mul]

end se21

/-! ### T13(a): conditioning on one's own draw is forcing, under Definition 6 -/

section condDraw

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Conditioning on one's own draw at a node is single-instance forcing there** (Definition 6):
`∑_ℓ 1(edge_q(ℓ) = a) μ_C(ℓ) r(ℓ) = C(d_q)(a) · forcedBelow(q, a)`; with `mass_edge`
(`μ_C(edge_q = a) = C(d_q)(a) R_q`) the conditional expectation of `r` given "I drew `a` at `q`" is
`G_q(C, a)`. Averaging over the fiber with per-occurrence weights is `ownDraw6Occ_eq`.
Source: [[decision-problems-v2]] Appendix B (line 347, "procedure-side tremble-conditioning …
delivers single-instance information, so a tremble-EDT evaluator should recover Theorem 1's
forcing counterfactual `G_q`"); [[fable-slop-notes]] Claim 4.1 | dp-core-038
Kind: C (one application of `leafLawNode_update_of_edge` + `mass_edge`; regraded from P in repair
round 1, docstring aligned in round 2)
Fidelity: exact (the full-support case, no tremble: the draw at `q` is independent of the path)
Hyps: (a) all -/
theorem condDraw_eq_forced (q : B.DecNode) (a : acts (pt B q)) :
    (∑ ℓ, if edgeOf B q ℓ = some a then leafLaw C B ℓ * payoff B ℓ else 0) =
      (C (pt B q)).w a * forcedBelow B (NodePolicy.ofProc C B) q a := by
  unfold forcedBelow leavesBelow
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : edgeOf B q ℓ = some a
  · have hs : (edgeOf B q ℓ).isSome := by rw [h]; rfl
    rw [if_pos h, if_pos hs, ← leafLawNode_ofProc]
    have key := leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ
      (NodePolicy.ofProc C B q) a h
    rw [NodePolicy.update_eq_self] at key
    rw [key]
    simp only [NodePolicy.ofProc]
    ring
  · rw [if_neg h]
    by_cases hs : (edgeOf B q ℓ).isSome
    · rw [if_pos hs]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
      have hba : b ≠ a := fun e => h (e ▸ hb)
      rw [leafLawNode_update_of_edge B (NodePolicy.ofProc C B) q ℓ (FinDistr.pure a) b hb]
      simp [FinDistr.pure_w, hba]
    · rw [if_neg hs]; simp

end condDraw

end Cleanroom.Decision.DpLocalOpt
