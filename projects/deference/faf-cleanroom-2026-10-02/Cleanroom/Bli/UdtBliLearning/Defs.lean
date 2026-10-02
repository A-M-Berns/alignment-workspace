import Cleanroom.Bli.UdtBliTiling.Refreeze

/-!
# `udt-bli-learning` · Defs: learning predicates over a belief-state sequence, and the single-coin
belief sequence derived by conditioning (T1)

**Scope: finite horizon `K` (days = rounds), one carrier `𝒟` for every belief state, the
contingent reading** (Notion ll. 671–679: the property of an (agent, tree) pair, not of the prior
across all trees).

A **belief-state sequence** is `Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A` with a **realized-table
sequence** `real : Fin K → ↥𝒟` (the table actually faced at round `k`). "`π` acts as if using
`Q_n` at round `k`" (`ActsAs`) means the action `π (real k)` at the table actually faced is a
one-step choice of `Q_n` there (UDT over a state = the one-step rule of record, core U1).
`IsOneStepChoice` compares the junk `0` at a null point, so `NDPOL`-type positivity is carried as
an explicit hypothesis of each theorem (every state here is `scPrior` or its `conditionOn`,
where every point is positive).

* `StrongLearnsAt Q real f π n`: from round `f n` on, `π` acts as `Q_n` (bli-soto-a-073's strong
  reading, at one `n`); `StrongLearns` is the all-`n` form (shown self-inconsistent on the model
  in `strongLearns_inconsistent`, mandate §3.3 (ii)).
* `WeakLearns Q real f π`: for every `n`, from round `f n` on every action is explained by *some*
  `Q_x`, `x ≥ n` (bli-soto-a-073's weak reading).
* `FUpdateful Q real g π`: at round `k` the policy acts as `Q_{g k}` (bli-soto-a-068 (i),
  "behaving as if we use `Q_{f(n)}` at time `n`"); plumbing to `WeakLearns` for monotone `g`.
* **Horizon.** "Eventually" is "for `k` with `f n ≤ k < K`"; an empty tail is vacuous
  (`strongLearnsAt_of_horizon`), so every theorem of substance carries `f n < K`. The predicates
  do not enforce `n ≤ f n` ("you cannot act by `Q_n` before day `n`" under days = rounds): a rate
  with `f n < n` is allowed, which only makes the learning demands stronger, so Theorem A is the
  stronger for it; `TheoremB`'s `Schedule` gets `n ≤ schedF s n` from `le_schedF`.

**The single-coin belief sequence is derived, not stipulated** (mandate §3.2): on
`udt-bli-tiling`'s `SingleCoin.scPrior p`, `beliefState p b N hb n := if n < N then scPrior p else
conditionOn (scPrior p) (coinClassOf K b) hb` — the state `Q_n` for `n ≥ N` is the frozen prior
re-frozen on the class of tables that decide the coin as `b` (mass `q` or `1 − q`); faith is
inherited from `conditionOn`. The realized tables are `Ask_k` when the coin is true and `Rec_k`
when false (`realized`). On the coin-false realization every action is utility-irrelevant at the
realized tables, so every policy acts as every state: the content is the coin-true realization,
and that is what Theorem A is about ([[bli-program-desiderata]] I10: "when `c` is true").

The one fact everything turns on (`actsAs_true_of_lt`, `actsAs_true_of_le`): on the coin-true
realization with `gain > 0`, `0 < q`, `0 < c`, `γ > 0`, acting as an early state (`n < N`) at
`Ask_k` *is* paying there, acting as a decided state (`n ≥ N`) *is* refusing there — both from
`udt-bli-tiling`'s unique one-step verdicts (`isOneStepChoice_pay`, `conditionOn_EU_eq_twoStepEU`
with `isTwoStepChoice_refuse`), never from a definition of learning that mentions paying.

Sources: bli-soto-a-070 (`soto-email-thread-2023.md` ll. 11–60), bli-soto-a-073 (ll. 231–262),
bli-soto-b-013 (PDF 15 pp. 1–2), bli-soto-a-068 (i) (Notion ll. 360–368), bli-soto-a-018
(Notion ll. 148–177), Notion ll. 671–679 (universal vs contingent); mandate §3.1–3.3, T1.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

/-! ## The learning predicates over a belief-state sequence -/

section Generic

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] {K : ℕ}

/-- **"Acts as if using `Q_n` at round `k`"**: the action `π (real k)` at the table actually faced
at round `k` is a one-step choice of the belief state `Q_n` at that table. Junk: `IsOneStepChoice`
compares against `0` at a null point; theorems carry the positivity they need.
Source: bli-soto-a-070 ("actions can eventually be explained in terms of a later state");
bli-soto-a-073 ("interpreted as being chosen by `Q_x`"); mandate §3.1
Kind: D
Fidelity: variant: UDT over a state = its one-step rule (core U1); days = rounds; finite
horizon; the contingent reading (Notion ll. 671–679) -/
def ActsAs (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (π : Policy 𝒟 A) (n : ℕ)
    (k : Fin K) : Prop :=
  (Q n).IsOneStepChoice (real k) (π (real k))

/-- **Strong learning at `n`**: from round `f n` on (within the horizon), every action is a
one-step choice of `Q_n` itself.
Source: bli-soto-a-073 ("Strong interpretation: for every `n`, there is a time `m`, beyond which
all actions can be interpreted as being chosen by `Q_n`"), at one `n`; mandate §3.1
Kind: D
Fidelity: variant: the time `m` is `f n`; finite horizon (empty tail vacuous) -/
def StrongLearnsAt (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (f : ℕ → ℕ)
    (π : Policy 𝒟 A) (n : ℕ) : Prop :=
  ∀ k : Fin K, f n ≤ k.val → ActsAs Q real π n k

/-- **Strong learning (all `n`)**: `StrongLearnsAt` at every `n`. On the single-coin model this
is self-inconsistent whenever two states are both "eventually" in force (`strongLearns_inconsistent`).
Source: bli-soto-a-073 (strong interpretation); mandate §3.1, §3.3 (ii)
Kind: D
Fidelity: variant: as `StrongLearnsAt` -/
def StrongLearns (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (f : ℕ → ℕ)
    (π : Policy 𝒟 A) : Prop :=
  ∀ n, StrongLearnsAt Q real f π n

/-- **Weak learning**: for every `n`, from round `f n` on every action is a one-step choice of
*some* later-or-equal state `Q_x`, `x ≥ n`. **Quantifier order**: `∀ n k, f n ≤ k → ∃ x ≥ n, …` —
the state index `x` may depend on the round `k` (per-round explanation), not one `x` for the whole
tail. This is the reading under which bli-soto-a-2-017 (i) is "by inspection" and the Sep 12
email's "allows future actions to move on from `Q_n`" makes sense; it is load-bearing for
`weakLearns_iff` (every policy weakly learns at every early `n`: `x = n` where it pays, `x = N`
where it refuses) and for `refrozen_weakLearns` at `n = 0`.
Source: bli-soto-a-073 ("Weak interpretation: … chosen by `Q_x` for `x` greater than or equal to
`n`"); mandate §3.1
Kind: D
Fidelity: variant: finite horizon; per-round `x` -/
def WeakLearns (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (f : ℕ → ℕ)
    (π : Policy 𝒟 A) : Prop :=
  ∀ n (k : Fin K), f n ≤ k.val → ∃ x, n ≤ x ∧ ActsAs Q real π x k

/-- **`g`-updatefulness**: at every round `k` the policy acts as `Q_{g k}` — a per-round
predicate (the state index is a function of the round, the reverse direction of `f` above).
Source: bli-soto-a-068 (i) ("`f`-updatefulness: behaving as if we use `Q_{f(n)}` at time `n`")
Kind: D
Fidelity: exact (finite horizon) -/
def FUpdateful (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (real : Fin K → ↥𝒟) (g : ℕ → ℕ)
    (π : Policy 𝒟 A) : Prop :=
  ∀ k : Fin K, ActsAs Q real π (g k.val) k

variable {Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A} {real : Fin K → ↥𝒟} {f g : ℕ → ℕ} {π : Policy 𝒟 A}
  {n : ℕ}

/-- Strong learning implies weak learning (witness `x = n`).
Source: bli-soto-a-073; mandate §3.1
Kind: L
Fidelity: n/a -/
theorem WeakLearns.of_strongLearns (h : StrongLearns Q real f π) : WeakLearns Q real f π :=
  fun n k hk => ⟨n, le_rfl, h n k hk⟩

/-- **Plumbing `g`-updatefulness → weak learning**: if `g` is monotone and `f` is a right bound
for it (`n ≤ g (f n)`), then acting as `Q_{g k}` at every `k` gives weak `f`-learning (witness
`x = g k ≥ g (f n) ≥ n`). The exact gap to the converse: weak learning yields *some* state index
per round but no monotone `g`.
Source: bli-soto-a-068 (i) vs bli-soto-a-073; mandate §3.1 ("prove the plumbing … or record
the exact gap")
Kind: L
Fidelity: n/a -/
theorem WeakLearns.of_fUpdateful (hg : Monotone g) (hfg : ∀ n, n ≤ g (f n))
    (h : FUpdateful Q real g π) : WeakLearns Q real f π :=
  fun n k hk => ⟨g k.val, (hfg n).trans (hg hk), h k⟩

/-- **The horizon clause is load-bearing**: with `K ≤ f n` the tail is empty and every policy
strongly learns at `n`, vacuously (T1 guard (c)).
Source: mandate §3.1 ("an empty tail is vacuous"), T1 (c)
Kind: N−
Fidelity: n/a -/
theorem strongLearnsAt_of_horizon (hK : K ≤ f n) : StrongLearnsAt Q real f π n :=
  fun k hk => absurd (lt_of_lt_of_le k.isLt hK) (not_lt.mpr hk)

end Generic

/-! ## The single-coin belief sequence, derived by conditioning -/

variable {K : ℕ} (p : Params K)

/-- The class of tables deciding the coin as `b`: `coinClass K` (mass `q`) for `true`, its
complement (mass `1 − q`) for `false`.
Source: mandate §3.2
Kind: D
Fidelity: exact -/
def coinClassOf (K : ℕ) : Bool → Finset ↥(iterTables K)
  | true => coinClass K
  | false => univ \ coinClass K

/-- `coinClassOf K true = coinClass K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma coinClassOf_true : coinClassOf K true = coinClass K := rfl

/-- `coinClassOf K false = univ \ coinClass K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma coinClassOf_false : coinClassOf K false = univ \ coinClass K := rfl

/-- The mass of the coin-false class is `1 − q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateClassMass_coinClassOf_false :
    stateClassMass (scPrior p) (coinClassOf K false) = 1 - p.q := by
  rw [coinClassOf_false]
  unfold scPrior
  rw [IndepCalc.stateClassMass_toPrior]
  change massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ ∈ univ \ coinClass K) = _
  have e : ∀ ω₀ : Base K, (baseState ω₀ ∈ univ \ coinClass K) ↔ ω₀.1 = false := by
    intro ω₀
    rw [Finset.mem_sdiff, baseState_mem_coinClass_iff]
    cases ω₀.1 <;> simp
  rw [massOf_congr _ e]
  unfold massOf
  have := sum_baseMass_mul p (fun b => if b = false then 1 else 0)
  simp only [Bool.true_eq_false, ↓reduceIte, mul_zero, mul_one, zero_add] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/-- Both coin classes are positive when `0 < q < 1`.
Source: mandate §3.2 ("prove positivity")
Kind: L
Fidelity: n/a -/
lemma coinClassOf_pos (hq0 : 0 < p.q) (hq1 : p.q < 1) (b : Bool) :
    0 < stateClassMass (scPrior p) (coinClassOf K b) := by
  cases b
  · rw [stateClassMass_coinClassOf_false]; linarith
  · rw [coinClassOf_true, stateClassMass_coinClass]; exact hq0

/-- **The single-coin belief-state sequence**: the frozen prior `scPrior p` before day `N`, and
from day `N` on the prior re-frozen on the class of tables that decide the coin as `b`
(`conditionOn`, faith preserved). "`Q_n` decides the coin by day `N`" is this and nothing more.
Source: [[bli-program-desiderata]] I10 ("base states `Q_n` decide `c` by day `N`"); bli-soto-a-084;
mandate §3.2
Kind: D
Fidelity: variant: the decided state is the conditional of the frozen prior on the deciding
class (finite shadow; `udt-bli-tiling`'s `conditionOn`) -/
def beliefState (b : Bool) (N : ℕ) (hb : 0 < stateClassMass (scPrior p) (coinClassOf K b))
    (n : ℕ) : FiniteBLIPrior (iterIndex K) 1 (iterTables K) Bool :=
  if n < N then scPrior p else conditionOn (scPrior p) (coinClassOf K b) hb

/-- **The realized tables**: `Ask_k` at round `k` when the coin is true, `Rec_k` when false.
Source: bli-soto-a-084 (the tree); mandate §3.2
Kind: D
Fidelity: exact -/
def realized (b : Bool) : Fin K → ↥(iterTables K) := fun k => if b then askT K k else recT K k

variable {p}

/-- Before `N` the belief state is the frozen prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma beliefState_of_lt {b : Bool} {N : ℕ} {hb : 0 < stateClassMass (scPrior p) (coinClassOf K b)}
    {n : ℕ} (h : n < N) : beliefState p b N hb n = scPrior p := if_pos h

/-- From `N` on the belief state is the re-frozen prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma beliefState_of_le {b : Bool} {N : ℕ} {hb : 0 < stateClassMass (scPrior p) (coinClassOf K b)}
    {n : ℕ} (h : N ≤ n) :
    beliefState p b N hb n = conditionOn (scPrior p) (coinClassOf K b) hb :=
  if_neg (not_lt.mpr h)

/-- The realized table on the coin-true branch is `Ask_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma realized_true (k : Fin K) : realized true k = askT K k := rfl

/-- The realized table on the coin-false branch is `Rec_k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma realized_false (k : Fin K) : realized false k = recT K k := rfl

/-! ## Acting as a state, on the coin-true realization -/

variable (p)

/-- **Acting as an early state is paying**: for `n < N`, `gain > 0`, `γ_k > 0`, on the coin-true
realization `π` acts as `Q_n` at round `k` iff `π` pays at `Ask_k` (the frozen prior's one-step
choice is uniquely `pay`, `udt-bli-tiling`'s `isOneStepChoice_pay`).
Source: [[bli-program-desiderata]] I10 Theorem A; mandate §3.3
Kind: C (`isOneStepChoice_pay`)
Fidelity: exact
Hyps: (a) `0 < gain`, `0 < γ_k`, `n < N`; does not use faith -/
theorem actsAs_true_of_lt (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) {N : ℕ}
    (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true)) {n : ℕ} (hn : n < N)
    (π : Policy (iterTables K) Bool) (k : Fin K) :
    ActsAs (beliefState p true N hb) (realized true) π n k ↔ π (askT K k) = true := by
  unfold ActsAs
  rw [beliefState_of_lt hn, realized_true]
  obtain ⟨h1, h2⟩ := isOneStepChoice_pay p k (hγ k) hg
  cases h : π (askT K k)
  · simp only [Bool.false_eq_true, iff_false]; exact h2
  · simp only [iff_true]; exact h1

/-- **Acting as a decided state is refusing**: for `n ≥ N`, `0 < q`, `0 < c`, `γ_k > 0`, on the
coin-true realization `π` acts as `Q_n` at round `k` iff `π` refuses at `Ask_k` (the re-frozen
prior's one-step choice is the two-step choice at `{coin}`, uniquely `refuse`:
`conditionOn_EU_eq_twoStepEU`, `isTwoStepChoice_refuse`).
Source: [[bli-program-desiderata]] I10 Theorem A ("refuses at all rounds after `f(N)` when `c`
is true"); mandate §3.3
Kind: C (`conditionOn_EU_eq_twoStepEU`, `isTwoStepChoice_refuse`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ_k`, `N ≤ n`; does not use faith -/
theorem actsAs_true_of_le (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) {N : ℕ}
    (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true)) {n : ℕ} (hn : N ≤ n)
    (π : Policy (iterTables K) Bool) (k : Fin K) :
    ActsAs (beliefState p true N hb) (realized true) π n k ↔ π (askT K k) = false := by
  unfold ActsAs
  rw [beliefState_of_le hn, realized_true]
  have hEU : ∀ a, (conditionOn (scPrior p) (coinClassOf K true) hb).EU (askT K k) a =
      twoStepEU (scPrior p) {coin1 K} (askT K k) a := fun a =>
    conditionOn_EU_eq_twoStepEU p hb k a
  obtain ⟨h1, h2⟩ := isTwoStepChoice_refuse p k hq hc (hγ k)
  unfold FiniteBLIPrior.IsOneStepChoice
  simp only [hEU]
  cases h : π (askT K k)
  · simp only [iff_true]; exact h1
  · simp only [Bool.true_eq_false, iff_false]; exact h2

/-- **On the coin-false realization every policy acts as every state** (the realized tables are
`Rec_k`, where no round reads the action): both the frozen and the re-frozen prior are
action-blind at `Rec_k`. This is why Theorem A is about the coin-true realization.
Source: mandate §3.2 ("for `b = false` … every policy acts as every state")
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem actsAs_false (N : ℕ) (hb : 0 < stateClassMass (scPrior p) (coinClassOf K false))
    (π : Policy (iterTables K) Bool) (n : ℕ) (k : Fin K) :
    ActsAs (beliefState p false N hb) (realized false) π n k := by
  unfold ActsAs
  rw [realized_false]
  intro b
  by_cases hn : n < N
  · rw [beliefState_of_lt hn]
    -- the frozen prior is action-blind at `Rec_k`: no round reads the point there
    have : ∀ a a', (scPrior p).EU (recT K k) a = (scPrior p).EU (recT K k) a' := by
      intro a a'
      unfold scPrior
      rw [IndepCalc.EU_toPrior, IndepCalc.EU_toPrior, SingleCoin.massOf_point,
        SingleCoin.massOf_point]
      simp only [inner_sum, SingleCoin.askT_ne_recT, if_false]
    exact le_of_eq (this b _)
  · rw [beliefState_of_le (not_lt.mp hn)]
    refine le_of_eq ?_
    unfold scPrior
    rw [IndepCalc.conditionOn_EU_toPrior, IndepCalc.conditionOn_EU_toPrior]
    simp only [inner_sum, SingleCoin.askT_ne_recT, if_false, SingleCoin.massOf_point]

/-! ## The refusing policy -/

/-- **Refuse at every table.**
Source: mandate T1 (e), T5 (the updateful policy of record on the model)
Kind: D
Fidelity: exact -/
def refuseAll : Policy (iterTables K) Bool := fun _ => false

/-- `roundSum refuseAll = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_refuseAll : roundSum p.γ (refuseAll (K := K)) = 0 := by
  unfold roundSum refuseAll; simp [ind]

/-- `0 ≤ roundSum γ π` for nonnegative weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma roundSum_nonneg (hγ : ∀ k, 0 ≤ p.γ k) (π : Policy (iterTables K) Bool) :
    0 ≤ roundSum p.γ π := by
  unfold roundSum
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hγ k) (ind_nonneg _))

/-- **Refusing everywhere is prior-optimal when `gain ≤ 0`** (and `γ ≥ 0`).
Source: bli-soto-a-084 (the "iff" of "pays forever iff …"); mandate T1 (e)
Kind: C (`exAnteValue_eq`)
Fidelity: exact
Hyps: (a) `gain ≤ 0`, `0 ≤ γ`; does not use faith -/
theorem priorOptimal_refuseAll (hg : gain p ≤ 0) (hγ : ∀ k, 0 ≤ p.γ k) :
    (scPrior p).IsPriorOptimal refuseAll := by
  intro π
  rw [exAnteValue_eq, exAnteValue_eq, roundSum_refuseAll]
  have := roundSum_nonneg p hγ π
  nlinarith

/-! ## T1 guards over the coin-true belief sequence -/

section Guards

variable {N : ℕ} (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true)) (f : ℕ → ℕ)

/-- **Strong learning at `N` is refusing on the tail** (`0 < q`, `0 < c`, `γ > 0`):
`StrongLearnsAt N π ↔ ∀ k ≥ f N, π Ask_k = refuse`.
Source: [[bli-program-desiderata]] I10 Theorem A; mandate §3.3
Kind: C (`actsAs_true_of_le`)
Fidelity: exact
Hyps: (a) positivity; does not use faith -/
theorem strongLearnsAt_decided_iff (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (π : Policy (iterTables K) Bool) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f π N ↔
      ∀ k : Fin K, f N ≤ k.val → π (askT K k) = false := by
  unfold StrongLearnsAt
  simp only [actsAs_true_of_le p hq hc hγ hb le_rfl]

/-- **Strong learning at an early state `n < N` is paying on the tail** (`gain > 0`, `γ > 0`):
`StrongLearnsAt n π ↔ ∀ k ≥ f n, π Ask_k = pay`.
Source: mandate §3.3
Kind: C (`actsAs_true_of_lt`)
Fidelity: exact
Hyps: (a) positivity, `n < N`; does not use faith -/
theorem strongLearnsAt_early_iff (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k) {n : ℕ} (hn : n < N)
    (π : Policy (iterTables K) Bool) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f π n ↔
      ∀ k : Fin K, f n ≤ k.val → π (askT K k) = true := by
  unfold StrongLearnsAt
  simp only [actsAs_true_of_lt p hg hγ hb hn]

/-- **Guard (a): the predicate is not universal** — `payAll` does not strongly learn at `N` when
the tail is nonempty (`f N < K`).
Source: mandate T1 (a)
Kind: N−
Fidelity: exact
Hyps: (a) positivity, `f N < K`; does not use faith -/
theorem not_strongLearnsAt_payAll (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hf : f N < K) :
    ¬ StrongLearnsAt (beliefState p true N hb) (realized true) f payAll N := by
  rw [strongLearnsAt_decided_iff p hb f hq hc hγ]
  intro h
  have := h ⟨f N, hf⟩ le_rfl
  simp [payAll] at this

/-- **Guard (b): the predicate is not vacuous** — the re-frozen policy `refrozen (f N)` strongly
learns at `N`, has positive mass under the frozen prior, and — for `f N < K`, the horizon clause
that makes the tail nonempty — refuses at `Ask_{f N}` where the frozen prior's `payAll` pays: it
learns by *doing something*, not through an empty tail. Without `f N < K` every policy strongly
learns at `N` (`strongLearnsAt_of_horizon_sc`) and `refrozen (f N)` is `payAll` on every `Ask`, so
the N+ reading needs the clause (audit r2 adversarial N4; the clause was missing until repair
round 2).
Source: mandate T1 (b); audit r2 adversarial N4
Kind: N+
Fidelity: exact
Hyps: (a) positivity, `f N < K`; does not use faith -/
theorem strongLearnsAt_refrozen (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hf : f N < K) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f (refrozen (f N)) N ∧
      0 < (scPrior p).policyMass (refrozen (f N)) ∧
      refrozen (f N) (askT K ⟨f N, hf⟩) = false ∧ payAll (askT K ⟨f N, hf⟩) = true := by
  refine ⟨?_, (structure_facts p).1 _, refrozen_askT_of_le (f N) ⟨f N, hf⟩ le_rfl, rfl⟩
  rw [strongLearnsAt_decided_iff p hb f hq hc hγ]
  intro k hk
  exact refrozen_askT_of_le (f N) k hk

/-- **Guard (c) on the model**: with `K ≤ f N` every policy strongly learns at `N` — the horizon
clause carries the content.
Source: mandate T1 (c)
Kind: N−
Fidelity: exact
Hyps: (a) `K ≤ f N` -/
theorem strongLearnsAt_of_horizon_sc (hK : K ≤ f N) (π : Policy (iterTables K) Bool) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f π N :=
  strongLearnsAt_of_horizon hK

/-- **§3.3 (i): weak learning for all `n` is strong learning at every decided state.** For
`n < N` the witness `x` may be `n` (if `π` pays at `Ask_k`) or `N` (if it refuses), so every policy
weakly learns at every early `n`; for `n ≥ N` the two readings coincide.
Source: bli-soto-a-073 (the two readings); mandate §3.3 (i)
Kind: P
Fidelity: exact
Hyps: (a) positivity; does not use faith -/
theorem weakLearns_iff (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (π : Policy (iterTables K) Bool) :
    WeakLearns (beliefState p true N hb) (realized true) f π ↔
      ∀ n, N ≤ n → StrongLearnsAt (beliefState p true N hb) (realized true) f π n := by
  constructor
  · intro h n hn k hk
    obtain ⟨x, hx, hact⟩ := h n k hk
    rw [actsAs_true_of_le p hq hc hγ hb (hn.trans hx)] at hact
    rw [actsAs_true_of_le p hq hc hγ hb hn]
    exact hact
  · intro h n k hk
    by_cases hn : N ≤ n
    · exact ⟨n, le_rfl, h n hn k hk⟩
    · have hn' : n < N := not_le.mp hn
      cases hπ : π (askT K k)
      · exact ⟨N, hn'.le, (actsAs_true_of_le p hq hc hγ hb le_rfl π k).mpr hπ⟩
      · exact ⟨n, le_rfl, (actsAs_true_of_lt p hg hγ hb hn' π k).mpr hπ⟩

/-- **§3.3 (i), monotone schedule: weak learning collapses to strong learning at `N`.**
Source: bli-soto-a-073; mandate §3.3 (i) ("weak learning for all `n` collapses to strong
learning at `N`")
Kind: C (`weakLearns_iff`)
Fidelity: exact
Hyps: (a) positivity, `Monotone f`; does not use faith -/
theorem weakLearns_iff_strongLearnsAt (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (hf : Monotone f) (π : Policy (iterTables K) Bool) :
    WeakLearns (beliefState p true N hb) (realized true) f π ↔
      StrongLearnsAt (beliefState p true N hb) (realized true) f π N := by
  rw [weakLearns_iff p hb f hq hc hg hγ]
  constructor
  · intro h; exact h N le_rfl
  · intro h n hn k hk
    rw [actsAs_true_of_le p hq hc hγ hb hn]
    exact (strongLearnsAt_decided_iff p hb f hq hc hγ π).mp h k ((hf hn).trans hk)

/-- **§3.3 (ii): strong learning for all `n` is self-inconsistent** whenever `0 < N` and some
round `k < K` is in both tails (`f 0 ≤ k`, `f N ≤ k`): at `k` the policy must pay (as `Q_0 = P`)
and refuse (as `Q_N`). The all-`n` strong reading is the exact form of "later actions may be more
updateful than `Q_n` only if `Q_n` endorses it" — `Q_0` does not (ATTRIBUTION-UNVETTED on what
the source meant). Theorem A is therefore stated with `StrongLearnsAt N`.
Source: bli-soto-a-073 (strong interpretation and its endorsement clause); mandate §3.3 (ii)
Kind: P
Fidelity: exact
Hyps: (a) positivity, `0 < N`, a common tail round; does not use faith -/
theorem strongLearns_inconsistent (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p)
    (hγ : ∀ k, 0 < p.γ k) (hN : 0 < N) (k : Fin K) (h0 : f 0 ≤ k.val) (hNk : f N ≤ k.val) :
    ¬ ∃ π : Policy (iterTables K) Bool,
      StrongLearns (beliefState p true N hb) (realized true) f π := by
  rintro ⟨π, h⟩
  have hpay := (strongLearnsAt_early_iff p hb f hg hγ hN π).mp (h 0) k h0
  have href := (strongLearnsAt_decided_iff p hb f hq hc hγ π).mp (h N) k hNk
  rw [hpay] at href
  exact Bool.noConfusion href

/-- **Guard (e), the artifact check: for `gain < 0` the dilemma disappears** — `refuseAll` both
strongly learns at `N` and is prior-optimal. The incompatibility of Theorem A is in the stakes
(`gain > 0`), not in the predicate.
Source: [[bli-program-desiderata]] I10 ("artifact check"); mandate T1 (e)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `gain < 0`; does not use faith -/
theorem refuseAll_learns_and_optimal_of_gain_neg (hq : 0 < p.q) (hc : 0 < p.c)
    (hγ : ∀ k, 0 < p.γ k) (hg' : gain p < 0) :
    StrongLearnsAt (beliefState p true N hb) (realized true) f refuseAll N ∧
      (scPrior p).IsPriorOptimal refuseAll := by
  refine ⟨?_, priorOptimal_refuseAll p hg'.le (fun k => (hγ k).le)⟩
  rw [strongLearnsAt_decided_iff p hb f hq hc hγ]
  intro k _
  rfl

/-- **`g`-updatefulness on the model**: `π` acts as `Q_{g k}` at every round iff it pays at the
rounds whose state is early (`g k < N`) and refuses at the rounds whose state is decided
(`N ≤ g k`) — the `g`-updateful policy is determined.
Source: bli-soto-a-068 (i); mandate §3.1
Kind: C (`actsAs_true_of_lt`, `actsAs_true_of_le`)
Fidelity: exact
Hyps: (a) positivity; does not use faith -/
theorem fUpdateful_iff (hq : 0 < p.q) (hc : 0 < p.c) (hg : 0 < gain p) (hγ : ∀ k, 0 < p.γ k)
    (g : ℕ → ℕ) (π : Policy (iterTables K) Bool) :
    FUpdateful (beliefState p true N hb) (realized true) g π ↔
      ∀ k : Fin K, (g k.val < N → π (askT K k) = true) ∧ (N ≤ g k.val → π (askT K k) = false) := by
  unfold FUpdateful
  constructor
  · intro h k
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · exact (actsAs_true_of_lt p hg hγ hb hk π k).mp (h k)
    · exact (actsAs_true_of_le p hq hc hγ hb hk π k).mp (h k)
  · intro h k
    by_cases hk : g k.val < N
    · exact (actsAs_true_of_lt p hg hγ hb hk π k).mpr ((h k).1 hk)
    · exact (actsAs_true_of_le p hq hc hγ hb (not_lt.mp hk) π k).mpr ((h k).2 (not_lt.mp hk))

end Guards

end Cleanroom.Bli.UdtBliLearning
