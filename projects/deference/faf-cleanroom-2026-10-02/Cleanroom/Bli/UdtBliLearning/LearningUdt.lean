import Cleanroom.Bli.UdtBliLearning.TheoremA
import Cleanroom.Bli.UdtBliCore.Good

/-!
# `udt-bli-learning` · LearningUdt: "Learning UDT" in two readings — the prefix reading is
uninhabitable on the model, the current-state reading is inhabited (T6)

**Scope: a belief-state sequence `Q` and a policy sequence `π : ℕ → Policy 𝒟 A` (the agent's policy
at time `m`); optimality is `IsPriorOptimalOnSupport` (junk-free).** The 2025 note defines
"Learning UDT" as "for some definition of 'updateful' which implies a sequence of updated belief
states `P₀, P₁, P₂, …`, the agent is eventually UDT-optimal for any particular `P_n`", adding "Note
that this requires UDT-optimality for all earlier `P_{<n}`. We could also consider a version which
does not require this, but, that's less interesting." Two readings, written with their quantifier
orders:

* **R1 (the prefix reading, `LearningUdtR1`)**: `∀ n, ∃ M, ∀ m ≥ M, ∀ n' ≤ n, (Q n').IsPriorOptimalOnSupport
  (π m)` — from some time on the policy is optimal for every state up to `n`.
* **R2 (the current-state reading, `LearningUdtR2`)**: `∃ M, ∀ m ≥ M, (Q m).IsPriorOptimalOnSupport
  (π m)` — from some time on the policy is optimal for the *current* state.

Plumbing: R1 implies per-state eventual optimality (`EventuallyOptimalFor`), and — because the
prefix `n' ≤ n` is finite — **is equivalent to it** (`learningUdtR1_iff_eventually`, by induction
with `max`): the quantifier order inside R1 carries no content; the content is R1 versus R2.

On the single-coin model (`beliefState p true N`, `gain > 0`, `0 < N`, `0 < K`): **no policy
sequence is R1** (`not_learningUdtR1`): the prefix `n = N` demands, at one time `m`, a policy
prior-optimal for `Q_0 = P` (pays at every `Ask_k`) and for `Q_N` (refuses at every `Ask_k`) —
mandate §3.3 (iii), the Learning-UDT shape of the all-`n` strong reading. The switch policy
`switchPolicy N m := if m < N then payAll else refuseAll` is R2 (`learningUdtR2_switch`, N+), and
indeed optimal for the current state at *every* time (`switchPolicy_optimal`).

Finding (ATTRIBUTION-UNVETTED on the reading): the note calls the prefix version "the interesting"
one; on any model where two states in the prefix disagree about the optimal policy it has no
inhabitant (here they disagree at every round; the proof uses round `0`). R2 is also met by the
constant `refuseAll` from `M = N` (`learningUdtR2_const_refuseAll`, N−): R2 does not need the
policy to change.

Sources: bli-paper-2-010 (`udt-tiling-working-notes-2025-06-30` b.300–308); bli-soto-b-051
(journal 2023-09-27 ll. 7–65); mandate T6.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

/-! ## The two readings -/

section Generic

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]

/-- **Learning UDT, prefix reading (R1)**: for every `n`, from some time `M` on, the policy is
prior-optimal (on the support) for every state `Q_{n'}` with `n' ≤ n`.
Source: bli-paper-2-010 b.300–301 ("eventually UDT-optimal for any particular `P_n`"; "this
requires UDT-optimality for all earlier `P_{<n}`"); mandate T6
Kind: D
Fidelity: variant: "UDT-optimal for `P_n`" = `IsPriorOptimalOnSupport` of `Q_n`, asked of the
*whole* policy `π m` at each time (including its actions at rounds already past), with no tail
restriction. Why (audit r2 fidelity N3): under a tail-only reading ("from time `m` on the actions
are `Q_{n'}`-optimal") the finite horizon makes R1 vacuously inhabited by any `M ≥ K`, so the
whole-policy reading is the one with content here; and the results below are unchanged under a
tail reading with a nonempty tail, because on the single-coin model the two states disagree at
*every* round (`not_learningUdtR1` reads round `0`; any round works) -/
def LearningUdtR1 (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (π : ℕ → Policy 𝒟 A) : Prop :=
  ∀ n, ∃ M, ∀ m', M ≤ m' → ∀ n', n' ≤ n → (Q n').IsPriorOptimalOnSupport (π m')

/-- **Learning UDT, current-state reading (R2)**: from some time `M` on, the policy at time `m`
is prior-optimal (on the support) for the current state `Q_m`.
Source: bli-paper-2-010 b.302 ("a version which does not require this"); mandate T6
Kind: D
Fidelity: variant: as R1 (whole-policy optimality at each time; see R1's Fidelity for why) -/
def LearningUdtR2 (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (π : ℕ → Policy 𝒟 A) : Prop :=
  ∃ M, ∀ m', M ≤ m' → (Q m').IsPriorOptimalOnSupport (π m')

/-- **Per-state eventual optimality**: from some time on, the policy is prior-optimal (on the
support) for the one state `Q_n`.
Source: bli-paper-2-010 b.300; mandate T6
Kind: D
Fidelity: exact -/
def EventuallyOptimalFor (Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A) (π : ℕ → Policy 𝒟 A) (n : ℕ) : Prop :=
  ∃ M, ∀ m', M ≤ m' → (Q n).IsPriorOptimalOnSupport (π m')

variable {Q : ℕ → FiniteBLIPrior 𝒮 m 𝒟 A} {π : ℕ → Policy 𝒟 A}

/-- R1 implies per-state eventual optimality.
Source: mandate T6 ("prove R1 ⟹ per-state eventual optimality")
Kind: L
Fidelity: n/a -/
theorem LearningUdtR1.eventuallyOptimalFor (h : LearningUdtR1 Q π) (n : ℕ) :
    EventuallyOptimalFor Q π n :=
  let ⟨M, hM⟩ := h n
  ⟨M, fun m' hm' => hM m' hm' n le_rfl⟩

/-- **The two quantifier orders are equivalent**: R1 (one time for the whole prefix) holds iff
per-state eventual optimality holds for every state — the prefix is finite, so the times can be
maximized. The content of "Learning UDT" is therefore R1 versus R2, not the order inside R1.
Source: bli-paper-2-010 b.300–301; mandate T6 ("Quantifier order is the content — write both
orders, prove the implication")
Kind: L (finite-prefix `max` plumbing)
Fidelity: exact
Hyps: (a) none -/
theorem learningUdtR1_iff_eventually :
    LearningUdtR1 Q π ↔ ∀ n, EventuallyOptimalFor Q π n := by
  constructor
  · exact fun h n => h.eventuallyOptimalFor n
  · intro h n
    induction n with
    | zero =>
      obtain ⟨M, hM⟩ := h 0
      exact ⟨M, fun m' hm' n' hn' => by
        have : n' = 0 := Nat.le_zero.mp hn'
        subst this; exact hM m' hm'⟩
    | succ n ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨M', hM'⟩ := h (n + 1)
      refine ⟨max M M', fun m' hm' n' hn' => ?_⟩
      rcases Nat.lt_or_ge n' (n + 1) with hlt | hge
      · exact hM m' (le_of_max_le_left hm') n' (Nat.lt_succ_iff.mp hlt)
      · have : n' = n + 1 := le_antisymm hn' hge
        subst this; exact hM' m' (le_of_max_le_right hm')

end Generic

/-! ## On the single-coin model -/

variable {K : ℕ} (p : Params K) {N : ℕ} (hb : 0 < stateClassMass (scPrior p) (coinClassOf K true))

/-- Every policy has positive mass under the re-frozen prior (the policy law is independent of the
base, and the class is positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionOn_policyMass_pos (π : Policy (iterTables K) Bool) :
    0 < (conditionOn (scPrior p) (coinClassOf K true) hb).policyMass π := by
  rw [conditionOn_policyMass]
  apply div_pos _ hb
  have hb' := hb
  unfold scPrior at hb' ⊢
  rw [IndepCalc.stateClassMass_toPrior] at hb'
  have e := (scData p).massOf_rect (fun ω₀ => (scData p).state₀ ω₀ ∈ coinClassOf K true)
    (fun π' => π' = π)
  change 0 < massOf (scData p).μ (fun ω => (scData p).state₀ ω.1 ∈ coinClassOf K true ∧ ω.2 = π)
  rw [e]
  apply mul_pos hb'
  have : massOf (scData p).ν (fun π' => π' = π) = (scData p).ν π := by
    unfold massOf; simp
  rw [this]; exact ν_pos p π

/-- The ex-ante value under the re-frozen prior, stated at the class `coinClassOf K true`
(`udt-bli-tiling`'s `conditionOn_exAnteValue_eq` at `coinClass K`, the same class by `rfl`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionOn_true_exAnteValue_eq (hq : 0 < p.q) (π : Policy (iterTables K) Bool) :
    (conditionOn (scPrior p) (coinClassOf K true) hb).exAnteValue π =
      -p.c * roundSum p.γ π + p.r₀ true :=
  conditionOn_exAnteValue_eq p hb hq π

/-- A policy with `roundSum ≤ 0` refuses at every `Ask_k` (positive weights).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refuses_of_roundSum_nonpos (hγ : ∀ k, 0 < p.γ k) (π : Policy (iterTables K) Bool)
    (h : roundSum p.γ π ≤ 0) (k : Fin K) : π (askT K k) = false := by
  have hle : p.γ k * ind (π (askT K k)) ≤ roundSum p.γ π :=
    Finset.single_le_sum (f := fun k => p.γ k * ind (π (askT K k)))
      (fun k _ => mul_nonneg (hγ k).le (ind_nonneg _)) (Finset.mem_univ k)
  cases hk : π (askT K k)
  · rfl
  · rw [hk, ind_true, mul_one] at hle
    exact absurd (hγ k) (not_lt.mpr (hle.trans h))

/-- **A policy prior-optimal (on the support) for the decided state refuses at every `Ask_k`**
(`0 < q`, `0 < c`, `γ > 0`).
Source: mandate T6 ("derive the decided optimum from `conditionOn_exAnteValue` + `twoStep_diff`")
Kind: C (`conditionOn_exAnteValue_eq`, `conditionOn_policyMass_pos`)
Fidelity: exact
Hyps: (a) positivity; does not use faith -/
theorem decided_optimal_refuses (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (π : Policy (iterTables K) Bool)
    (h : (conditionOn (scPrior p) (coinClassOf K true) hb).IsPriorOptimalOnSupport π) (k : Fin K) :
    π (askT K k) = false := by
  have := h refuseAll (conditionOn_policyMass_pos p hb refuseAll)
  rw [conditionOn_true_exAnteValue_eq p hb hq, conditionOn_true_exAnteValue_eq p hb hq,
    roundSum_refuseAll] at this
  apply refuses_of_roundSum_nonpos p hγ π _ k
  nlinarith

/-- **`refuseAll` is prior-optimal (on the support) for the decided state.**
Source: mandate T6 (the R2 witness)
Kind: C (`conditionOn_exAnteValue_eq`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 ≤ γ`; does not use faith -/
theorem decided_optimal_refuseAll (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 ≤ p.γ k) :
    (conditionOn (scPrior p) (coinClassOf K true) hb).IsPriorOptimalOnSupport refuseAll := by
  intro π _
  rw [conditionOn_true_exAnteValue_eq p hb hq, conditionOn_true_exAnteValue_eq p hb hq,
    roundSum_refuseAll]
  have := roundSum_nonneg p hγ π
  nlinarith

/-- **No policy sequence is Learning UDT in the prefix reading (R1) on the model**: at the prefix
`n = N`, one time `m` would need a policy prior-optimal for `Q_0 = P` (pays at every `Ask_k`) and
for `Q_N` (refuses at every `Ask_k`). The proof reads the contradiction off round `0` — a choice;
on this model the two states disagree at every round, early or late.
Source: bli-paper-2-010 b.300–301; mandate §3.3 (iii), T6 ("no sequence is R1")
Kind: C (`priorOptimal_pays`, `decided_optimal_refuses`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `0 < N`, `0 < K`; does not use faith -/
theorem not_learningUdtR1 (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) (hg : 0 < gain p)
    (hN : 0 < N) (hK : 0 < K) (π : ℕ → Policy (iterTables K) Bool) :
    ¬ LearningUdtR1 (beliefState p true N hb) π := by
  intro h
  obtain ⟨M, hM⟩ := h N
  have h0 := hM M le_rfl 0 (Nat.zero_le _)
  have hNN := hM M le_rfl N le_rfl
  rw [beliefState_of_lt hN] at h0
  rw [beliefState_of_le le_rfl] at hNN
  have hpay := priorOptimal_pays p hg hγ (π M)
    ((FiniteBLIPrior.isPriorOptimalOnSupport_iff _ (structure_facts p).1 _).mp h0) ⟨0, hK⟩
  have href := decided_optimal_refuses p hb hq hc hγ (π M) hNN ⟨0, hK⟩
  rw [hpay] at href
  exact Bool.noConfusion href

/-- **The switch policy**: `payAll` before the decision day, `refuseAll` from it on — the policy
sequence that is optimal for the current state at every time.
Source: mandate T6 (the R2 witness)
Kind: D
Fidelity: exact -/
def switchPolicy (N m : ℕ) : Policy (iterTables K) Bool := if m < N then payAll else refuseAll

/-- **The switch policy is prior-optimal for the current state at every time.**
Source: mandate T6
Kind: C (`priorOptimal_payAll`, `decided_optimal_refuseAll`)
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`; does not use faith -/
theorem switchPolicy_optimal (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (m' : ℕ) :
    (beliefState p true N hb m').IsPriorOptimalOnSupport (switchPolicy N m') := by
  unfold switchPolicy
  by_cases hm : m' < N
  · rw [beliefState_of_lt hm, if_pos hm]
    exact FiniteBLIPrior.isPriorOptimalOnSupport_of_isPriorOptimal _
      (priorOptimal_payAll p hg.le (fun k => (hγ k).le))
  · rw [beliefState_of_le (not_lt.mp hm), if_neg hm]
    exact decided_optimal_refuseAll p hb hq hc (fun k => (hγ k).le)

/-- **Learning UDT in the current-state reading (R2) is inhabited on the model** by the switch
policy, with `M = 0` (N+: the states disagree and every value compared is a positive-mass
policy's; that this witness *changes* with the state is a property of the witness — it is optimal
at every time — not something R2 demands, see `learningUdtR2_const_refuseAll`).
Source: bli-paper-2-010 b.302; mandate T6 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`; does not use faith -/
theorem learningUdtR2_switch (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) :
    LearningUdtR2 (beliefState p true N hb) (switchPolicy N) :=
  ⟨0, fun m' _ => switchPolicy_optimal p hb hq hc hγ hg m'⟩

/-- **N−: the constant `refuseAll` is R2 too** (from `M = N`): R2 does not require the policy to
change with the state; its `∃ M` absorbs the early disagreement. On this model the `∃ M` is idle
for the switch policy (`M = 0`) and load-bearing for the constant one.
Source: mandate T6; audit r1 adversarial N3 (probe `WeakIsTail`)
Kind: N−
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`; does not use faith -/
theorem learningUdtR2_const_refuseAll (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k) :
    LearningUdtR2 (beliefState p true N hb) (fun _ => refuseAll) :=
  ⟨N, fun m' hm' => by
    show (beliefState p true N hb m').IsPriorOptimalOnSupport refuseAll
    rw [beliefState_of_le hm']
    exact decided_optimal_refuseAll p hb hq hc (fun k => (hγ k).le)⟩

/-- **The two readings separate on the model**: R2 is inhabited and R1 is not.
Source: bli-paper-2-010 b.300–302; mandate T6
Kind: C
Fidelity: exact
Hyps: (a) `0 < q`, `0 < c`, `0 < γ`, `0 < gain`, `0 < N`, `0 < K`; does not use faith -/
theorem learningUdt_readings_separate (hq : 0 < p.q) (hc : 0 < p.c) (hγ : ∀ k, 0 < p.γ k)
    (hg : 0 < gain p) (hN : 0 < N) (hK : 0 < K) :
    LearningUdtR2 (beliefState p true N hb) (switchPolicy N) ∧
      ∀ π : ℕ → Policy (iterTables K) Bool, ¬ LearningUdtR1 (beliefState p true N hb) π :=
  ⟨learningUdtR2_switch p hb hq hc hγ hg, fun π => not_learningUdtR1 p hb hq hc hγ hg hN hK π⟩

end Cleanroom.Bli.UdtBliLearning
