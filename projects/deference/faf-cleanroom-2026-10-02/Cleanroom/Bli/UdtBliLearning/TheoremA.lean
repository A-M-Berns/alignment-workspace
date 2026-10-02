import Cleanroom.Bli.UdtBliLearning.Defs

/-!
# `udt-bli-learning` · TheoremA: strong learning at the decided state and prior-optimality are
incompatible on the single-coin iterated mugging (T2)

**Scope: single coin, additive stakes, finite horizon `K`, the prior pays (`gain > 0`), the coin
true, the decided state `Q_N` in force from round `f N < K`.**

Over `udt-bli-tiling`'s `SingleCoin.scPrior p` and `Defs.lean`'s derived belief sequence
`beliefState p true N`:

* (i) `strongLearner_refuses`: a policy that strongly learns at `N` refuses at `Ask_{f N}`;
* (ii) `theoremA`: no policy both strongly learns at `N` and is prior-optimal (equivalently: and
  has no strict preference for precommitment) — **the dilemma is the pair**;
* (iii) `strongLearner_loss`: a strong learner loses at least `gain · ∑_{k ≥ f N} γ_k` against
  `payAll` under the frozen prior;
* (iv) `not_strongLearnsAt_of_priorOptimal`: a prior-optimal policy does not strongly learn at `N`.

Every hypothesis is positivity (`0 < q`, `0 < c`, `0 < γ_k`, `0 < gain`, `f N < K`); the
decided state's choice (`conditionOn_EU_eq_twoStepEU`, `isTwoStepChoice_refuse`), the frozen
prior's optimum (`priorOptimal_payAll`, `noStrictPrecommit_iff_payOnAsk`) and positivity of every
policy (`structure_facts`) are **derived** from `udt-bli-tiling`; nothing about value, learning or
optimality is assumed beyond the two predicates shown incompatible. `IsPriorOptimal` is used
inside `NDPOLICY` (every policy positive), so it is the junk-free predicate here.

**Each half is inhabited** (`dilemma_halves`, general; `inst_dilemma_halves`, the numeric
instance `(c, V) = (10, 100)`, `q = 1/2`, `K = 3`, `N = 1`, `f ≡ 1`): `payAll` is prior-optimal
and does not learn; `refrozen (f N)` learns and is not prior-optimal, with the gap `gain ·
tailSum γ (f N)` (`90` on the instance). The artifact check is `Defs.lean`'s
`refuseAll_learns_and_optimal_of_gain_neg`: for `gain < 0` one policy has both.

Not stated: the all-`n` strong hypothesis (self-inconsistent, `strongLearns_inconsistent`); a
theorem assuming it would be vacuous.

Sources: [[bli-program-desiderata]] I10 Theorem A; [[bli-program]] §3.9 U10; bli-soto-a-084
(`soto-email-thread-2023.md` ll. 262–290: "some priors force a choice between learning vs
selecting actions in a way which is optimal according to that prior", ll. 11–60); bli-soto-b-038;
mandate T2.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

variable {K : ℕ} (p : Params K) {N : ℕ}
  (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true)) (f : ℕ → ℕ)

/-! ## The two sides -/

/-- **(i) A strong learner at `N` refuses at `Ask_{f N}`** (and at every later round).
Source: [[bli-program-desiderata]] I10 Theorem A ("refuses at all rounds after `f(N)` when `c` is
true"); mandate T2 (i)
Kind: C (`strongLearnsAt_decided_iff`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `f N < K`; does not use faith -/
theorem strongLearner_refuses (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hf : f N < K)
    (π : Policy (iterTables K) Bool)
    (h : StrongLearnsAt (beliefState p true N hb) (realized true) f π N) :
    π (askT K ⟨f N, hf⟩) = false :=
  (strongLearnsAt_decided_iff p hb f hq hc hγ π).mp h ⟨f N, hf⟩ le_rfl

/-- **A prior-optimal policy pays at every round** (`gain > 0`, `γ > 0`), derived from
`udt-bli-tiling`'s characterization of no-strict-preference-for-precommitment.
Source: bli-soto-a-084 ("the prior-optimal policy pays forever iff …"); mandate T2
Kind: C (`noStrictPrecommit_of_priorOptimal`, `noStrictPrecommit_iff_payOnAsk`)
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ`; does not use faith -/
theorem priorOptimal_pays (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) (π : Policy (iterTables K) Bool)
    (h : (scPrior p).IsPriorOptimal π) : ∀ k, π (askT K k) = true :=
  (noStrictPrecommit_iff_payOnAsk p hg hγ π).mp
    (noStrictPrecommit_of_priorOptimal (structure_facts p).1 h)

/-- A policy refusing from round `t` on has `roundSum ≤ roundSum (refrozen t)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_le_refrozen (hγ : ∀ k, 0 ≤ p.γ k) (t : ℕ) (π : Policy (iterTables K) Bool)
    (h : ∀ k : Fin K, t ≤ k.val → π (askT K k) = false) :
    roundSum p.γ π ≤ roundSum p.γ (refrozen t) := by
  unfold roundSum
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : t ≤ k.val
  · rw [h k hk, refrozen_askT_of_le t k hk]
  · rw [refrozen_askT_of_lt t k (not_le.mp hk), ind_true, mul_one]
    exact mul_le_of_le_one_right (hγ k) (ind_le_one _)

/-- **(iii) The quantitative gap**: a strong learner at `N` loses at least `gain · ∑_{k ≥ f N} γ_k`
against `payAll` under the frozen prior.
Source: [[bli-program-desiderata]] I10 ("explicit numbers"); mandate T2 (iii)
Kind: C (`exAnteValue_eq`, `roundSum_le_refrozen`, `roundSum_payAll_sub_refrozen`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 ≤ gain`; does not use faith -/
theorem strongLearner_loss (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hg : 0 ≤ gain p)
    (π : Policy (iterTables K) Bool)
    (h : StrongLearnsAt (beliefState p true N hb) (realized true) f π N) :
    gain p * tailSum p.γ (f N) ≤ (scPrior p).exAnteValue payAll - (scPrior p).exAnteValue π := by
  have hr := roundSum_le_refrozen p (fun k => (hγ k).le) (f N) π
    ((strongLearnsAt_decided_iff p hb f hq hc hγ π).mp h)
  have hs := roundSum_payAll_sub_refrozen p (f N)
  rw [exAnteValue_eq, exAnteValue_eq]
  nlinarith

/-! ## Theorem A -/

/-- **Theorem A (the learning dilemma, single coin)**: for `0 < q`, `0 < c`, `γ > 0`, `gain =
V(1−q) − cq > 0` and `f N < K`, on the coin-true realization **no policy both strongly learns at
the decided state `N` and is prior-optimal for the frozen prior** — and the same with "has no
strict preference for precommitment" in place of prior-optimality. The two sides: a strong learner
refuses at `Ask_{f N}` (the decided state's unique one-step choice); a prior-optimal policy pays
there (the frozen prior's unique optimum). Each side separately is inhabited (`dilemma_halves`).
Source: [[bli-program-desiderata]] I10 Theorem A ("for `q < 10/11` and `c` true no prior-optimal
policy has strong learning"); [[bli-program]] §3.9 U10; bli-soto-a-084 (Sep 8: "some priors force
a choice between learning vs selecting actions in a way which is optimal according to that
prior"); bli-soto-b-038; mandate T2 (ii)
Kind: C
Fidelity: exact (finite horizon; strong learning at the one decided state, the weakest hypothesis
with content — the all-`n` form is self-inconsistent, `strongLearns_inconsistent`)
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `0 < gain`, `f N < K`; does not use faith -/
theorem theoremA (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hg : 0 < gain p)
    (hf : f N < K) (π : Policy (iterTables K) Bool) :
    ¬ (StrongLearnsAt (beliefState p true N hb) (realized true) f π N ∧
        (scPrior p).IsPriorOptimal π) ∧
    ¬ (StrongLearnsAt (beliefState p true N hb) (realized true) f π N ∧
        NoStrictPrecommit (scPrior p) π) := by
  constructor
  · rintro ⟨hl, ho⟩
    have h1 := strongLearner_refuses p hb f hq hc hγ hf π hl
    have h2 := priorOptimal_pays p hg hγ π ho ⟨f N, hf⟩
    rw [h1] at h2
    exact Bool.noConfusion h2
  · rintro ⟨hl, ho⟩
    have h1 := strongLearner_refuses p hb f hq hc hγ hf π hl
    have h2 := (noStrictPrecommit_iff_payOnAsk p hg hγ π).mp ho ⟨f N, hf⟩
    rw [h1] at h2
    exact Bool.noConfusion h2

/-- **(iv) A prior-optimal policy does not strongly learn at `N`.**
Source: [[bli-program-desiderata]] I10 Theorem A; mandate T2 (iv)
Kind: C (`theoremA`)
Fidelity: exact
Hyps: (a) as `theoremA`; does not use faith -/
theorem not_strongLearnsAt_of_priorOptimal (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (hf : f N < K) (π : Policy (iterTables K) Bool)
    (ho : (scPrior p).IsPriorOptimal π) :
    ¬ StrongLearnsAt (beliefState p true N hb) (realized true) f π N :=
  fun hl => (theoremA p hb f hq hc hγ hg hf π).1 ⟨hl, ho⟩

/-! ## Each half inhabited -/

/-- **The dilemma is the pair, each half inhabited** (general, grade (a)): `payAll` is
prior-optimal and does not strongly learn at `N`; `refrozen (f N)` strongly learns at `N`, has
positive mass, and is not prior-optimal — it loses exactly `gain · ∑_{k ≥ f N} γ_k > 0` against
`payAll` (`udt-bli-tiling`'s `frozen_gap`).
Source: [[bli-program-desiderata]] I10 ("the impossibility is about the *pair* (learning,
optimality), each of which has a witness"); mandate T2 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `0 < gain`, `f N < K`; does not use faith -/
theorem dilemma_halves (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hg : 0 < gain p)
    (hf : f N < K) :
    ((scPrior p).IsPriorOptimal payAll ∧
      ¬ StrongLearnsAt (beliefState p true N hb) (realized true) f payAll N) ∧
    (StrongLearnsAt (beliefState p true N hb) (realized true) f (refrozen (f N)) N ∧
      0 < (scPrior p).policyMass (refrozen (f N)) ∧
      ¬ (scPrior p).IsPriorOptimal (refrozen (f N)) ∧
      (scPrior p).exAnteValue payAll - (scPrior p).exAnteValue (refrozen (f N)) =
        gain p * tailSum p.γ (f N) ∧
      0 < gain p * tailSum p.γ (f N)) := by
  obtain ⟨hl, hm, _, _⟩ := strongLearnsAt_refrozen p hb f hq hc hγ hf
  refine ⟨⟨priorOptimal_payAll p hg.le (fun k => (hγ k).le),
    not_strongLearnsAt_payAll p hb f hq hc hγ hf⟩, hl, hm, ?_, frozen_gap p (f N),
    mul_pos hg (tailSum_pos p hγ (f N) hf)⟩
  intro ho
  have := ho payAll
  have := frozen_prefers_payAll p (f N) hf hg hγ
  linarith

/-- `0 < c` on the instance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inst_hc : 0 < inst.c := by norm_num [inst]

/-- `0 < γ_k` on the instance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inst_hγ : ∀ k, 0 < inst.γ k := fun _ => by norm_num [inst]

/-- `0 < gain` on the instance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inst_hg : 0 < gain inst := by rw [inst_gain.1]; norm_num

/-- **Theorem A on the numeric instance** (`(c, V) = (10, 100)`, `q = 1/2`, `K = 3`, `γ ≡ 1`,
decision day `N = 1`, `f ≡ 1`): `payAll` is prior-optimal and does not strongly learn at `1`;
`refrozen 1` strongly learns at `1` and is not prior-optimal, losing exactly `90` against
`payAll` (`udt-bli-tiling`'s `inst_dilemma`).
Source: mandate T2 (N+: "`inst`, `N = 1`, `f ≡ 1`: `payAll` optimal-not-learning, `refrozen 1`
learning-not-optimal, gap `90`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inst_dilemma_halves :
    ((scPrior inst).IsPriorOptimal payAll ∧
      ¬ StrongLearnsAt (beliefState inst true 1 (coinClass_pos inst inst_hq)) (realized true)
        (fun _ => 1) payAll 1) ∧
    (StrongLearnsAt (beliefState inst true 1 (coinClass_pos inst inst_hq)) (realized true)
        (fun _ => 1) (refrozen 1) 1 ∧
      ¬ (scPrior inst).IsPriorOptimal (refrozen 1) ∧
      (scPrior inst).exAnteValue payAll - (scPrior inst).exAnteValue (refrozen 1) = 90) := by
  obtain ⟨⟨h1, h2⟩, h3, _, h5, _, _⟩ := dilemma_halves inst (coinClass_pos inst inst_hq)
    (fun _ => 1) inst_hq inst_hc inst_hγ inst_hg (by norm_num)
  exact ⟨⟨h1, h2⟩, h3, h5, inst_dilemma.1.1⟩

end Cleanroom.Bli.UdtBliLearning
