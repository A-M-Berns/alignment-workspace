import Cleanroom.Decision.DpReferentsCdt.Elh

/-!
# Everitt–Leike–Hutter: the two-round tree in closed form and the SAEDT ≠ SPEDT witness

Mandate T8's numeric witness: a two-step instance (`m = 2`) at which SAEDT and SPEDT disagree at
the first decision (`t = 1`). On the `Elh.lean` rendering the hidden state draws no action
(findings F13), so the disagreement must come from the *future policy event* weighting the percepts
differently — which happens exactly when the continuation procedure `C(æ_1)` puts different weight
on the policy's next action for different first percepts. The instance here (`revealEnv`,
`revealProc`): two hidden states drawn fairly, a percept that reveals the state, and a procedure that
follows `π ≡ one` surely after percept `0` and only half the time after percept `1`. Then at the
root: SAEDT's belief in percept `0` is `1/2`, SPEDT's is `2/3`, and SCDT's (Proposition 7: the
one-point deviation) is `1/2`.

**Closed forms** (`P`, every environment, procedure and policy): on the `m = 2` tree the first-step
prefix masses factor through the root draw and the first percept, with the second-round percept
summing to one (`massPrefix_two_first`, `spedt_two_num`, `spedt_two_den`); SAEDT, SPEDT and SCDT at
the root follow (`saedtBelief_two_root`, `spedtBelief_two_root`, `scdtBelief_two_root`), the first
two under the guard `C([])(a) ≠ 0` that cancels the root draw.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

section twoRound

variable {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {ns ne : ℕ}
variable (E : ElhEnv A ns ne) (C : Proc (Hist A ne) (fun _ => A) ℚ)

/-- The two-round subtree after state `s`, written out: decision at `[]`, percept, decision at
`[(a, e)]`, percept, leaf. Definitionally `elhSub E s 2 []`.
Source: none: infrastructure (mandate T8's two-step instance)
Kind: D -/
def elhTwo (s : Fin ns) : Tree (ElhW A ns ne) (Hist A ne) (fun _ => A) ℚ :=
  .decision [] fun a => .chance ne (E.μ s [] a) fun e =>
    .decision [(a, e)] fun a' => .chance ne (E.μ s [(a, e)] a') fun e' =>
      .leaf (s, [(a, e), (a', e')]) (histUtil E.u [(a, e), (a', e')])

/-- `elhSub E s 2 [] = elhTwo E s`. Source: none: infrastructure. Kind: L -/
theorem elhSub_two (s : Fin ns) : elhSub E s 2 [] = elhTwo E s := rfl

/-- A leaf of the two-round tree, typed as such (the anonymous constructor elaborates at the sigma
type, which defeats instance-level rewriting). Source: none: infrastructure. Kind: D -/
def elh2Leaf (s : Fin ns) (a1 : A) (e1 : Fin ne) (a2 : A) (e2 : Fin ne) : (elhTree E 2).Leaves :=
  ⟨s, a1, e1, a2, e2, ()⟩

/-- Sums over the leaves of the two-round tree: `∑ s a₁ e₁ a₂ e₂`.
Source: none: infrastructure
Kind: L -/
theorem elh2_sum (f : (elhTree E 2).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ s, ∑ a1, ∑ e1, ∑ a2, ∑ e2, f (elh2Leaf E s a1 e1 a2 e2) := by
  unfold elhTree
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (∑ ℓ : (elhTwo E s).Leaves, f ⟨s, ℓ⟩) = _
  unfold elhTwo
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun e1 _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun e2 _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The world of a two-round leaf. Source: none: infrastructure. Kind: L -/
theorem elh2_world (s : Fin ns) (a1 a2 : A) (e1 e2 : Fin ne) :
    world (elhTree E 2) (elh2Leaf E s a1 e1 a2 e2) = (s, [(a1, e1), (a2, e2)]) := rfl

/-- The run law of a two-round leaf, grouped with the last percept as the outer factor.
Source: EL&H equation (2) on the two-round tree
Kind: L -/
theorem elh2_leafLaw (s : Fin ns) (a1 a2 : A) (e1 e2 : Fin ne) :
    leafLaw C (elhTree E 2) (elh2Leaf E s a1 e1 a2 e2) =
      (E.ρ.w s * (C []).w a1 * (E.μ s [] a1).w e1 * (C [(a1, e1)]).w a2) *
        (E.μ s [(a1, e1)] a2).w e2 := by
  show E.ρ.w s * ((C []).w a1 * ((E.μ s [] a1).w e1 * ((C [(a1, e1)]).w a2 *
    ((E.μ s [(a1, e1)] a2).w e2 * 1)))) = _
  ring

/-- `Follows π 1` on a two-element trajectory says the second action is the policy's.
Source: EL&H equation (4) on the two-round tree
Kind: L -/
theorem follows_one_two (π : Hist A ne → A) (a1 a2 : A) (e1 e2 : Fin ne) :
    Follows π 1 [(a1, e1), (a2, e2)] ↔ a2 = π [(a1, e1)] := by
  unfold Follows
  constructor
  · intro h; exact h 1 (by simp) le_rfl
  · intro h i hi hk
    have : i = 1 := by simp at hi; omega
    subst this; exact h

/-- The prefix `[(a, e)]` on a two-element trajectory. Source: none: infrastructure. Kind: L -/
theorem prefix_one_two (a a1 a2 : A) (e e1 e2 : Fin ne) :
    [(a, e)] <+: [(a1, e1), (a2, e2)] ↔ e1 = e ∧ a1 = a := by
  simp only [List.cons_prefix_cons, List.nil_prefix, and_true, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1.symm⟩
  · rintro ⟨h2, h1⟩; exact ⟨h1.symm, h2.symm⟩

/-- A sum of a term gated by a condition free of the summation variable.
Source: none: infrastructure
Kind: L -/
theorem sum_ite_const_cond {α M : Type} [AddCommMonoid M] (s : Finset α) (P : Prop) [Decidable P]
    (f : α → M) : (∑ x ∈ s, if P then f x else 0) = if P then ∑ x ∈ s, f x else 0 := by
  split_ifs <;> simp

/-- **First-step prefix mass on the two-round tree**: `μ{æ_1 = (a, e)} = C([])(a) · ∑_s ρ(s) μ(e ∣ s, a)`.
Source: EL&H equation (2) (`μ(æ_{<t} a_t)`); mandate T8
Kind: P -/
theorem massPrefix_two_first (a : A) (e : Fin ne) :
    massPrefix C (elhTree E 2) [(a, e)] = (C []).w a * ∑ s, E.ρ.w s * (E.μ s [] a).w e := by
  rw [massPrefix_eq_sum, elh2_sum]
  simp only [elh2_world, prefix_one_two, elh2_leafLaw, sum_ite_const_cond, ← Finset.mul_sum,
    FinDistr.sum_one, mul_one, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- Membership in SPEDT's numerator event at the root. Source: none: infrastructure. Kind: L -/
theorem elh2_mem_spedt_num (π : Hist A ne → A) (a : A) (e : Fin ne) (s : Fin ns) (a1 a2 : A)
    (e1 e2 : Fin ne) :
    elh2Leaf E s a1 e1 a2 e2 ∈ prefixEv (elhTree E 2) [(a, e)] ∩ followsEv π 1 (elhTree E 2) ↔
      a2 = π [(a1, e1)] ∧ (e1 = e ∧ a1 = a) := by
  rw [Finset.mem_inter]
  unfold prefixEv followsEv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, elh2_world, follows_one_two,
    prefix_one_two]
  tauto

/-- Membership in SPEDT's denominator event at the root. Source: none: infrastructure. Kind: L -/
theorem elh2_mem_spedt_den (π : Hist A ne → A) (a : A) (s : Fin ns) (a1 a2 : A)
    (e1 e2 : Fin ne) :
    elh2Leaf E s a1 e1 a2 e2 ∈
        (Finset.univ.biUnion fun e' => prefixEv (elhTree E 2) [(a, e')]) ∩
          followsEv π 1 (elhTree E 2) ↔
      a2 = π [(a1, e1)] ∧ a1 = a := by
  rw [Finset.mem_inter, Finset.mem_biUnion]
  unfold prefixEv followsEv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, elh2_world, follows_one_two,
    prefix_one_two, exists_eq_left']
  tauto

/-- **SPEDT's numerator at the root**: `μ{æ_1 = (a, e), a_2 = π(æ_1)} = C([])(a) · ∑_s ρ(s) μ(e ∣ s, a) C((a,e))(π(a,e))`.
Source: EL&H Definition 4 (SPEDT), equation (4); mandate T8
Kind: P -/
theorem spedt_two_num (π : Hist A ne → A) (a : A) (e : Fin ne) :
    mass C (elhTree E 2) (prefixEv (elhTree E 2) [(a, e)] ∩ followsEv π 1 (elhTree E 2)) =
      (C []).w a * ∑ s, E.ρ.w s * ((E.μ s [] a).w e * (C [(a, e)]).w (π [(a, e)])) := by
  have hset : prefixEv (elhTree E 2) [(a, e)] ∩ followsEv π 1 (elhTree E 2) =
      Finset.univ.filter fun ℓ => ℓ ∈ prefixEv (elhTree E 2) [(a, e)] ∩ followsEv π 1 (elhTree E 2) := by
    ext ℓ; simp
  rw [hset, mass_filter, elh2_sum]
  simp only [elh2_mem_spedt_num, elh2_leafLaw, sum_ite_const_cond, ← Finset.mul_sum,
    FinDistr.sum_one, mul_one, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **SPEDT's denominator at the root**: `μ{a_1 = a, a_2 = π(æ_1)} = C([])(a) · ∑_s ρ(s) ∑_{e'} μ(e' ∣ s, a) C((a,e'))(π(a,e'))`.
Source: EL&H Definition 4 (SPEDT), equation (4); mandate T8
Kind: P -/
theorem spedt_two_den (π : Hist A ne → A) (a : A) :
    mass C (elhTree E 2) ((Finset.univ.biUnion fun e' => prefixEv (elhTree E 2) [(a, e')]) ∩
        followsEv π 1 (elhTree E 2)) =
      (C []).w a * ∑ s, E.ρ.w s * ∑ e', (E.μ s [] a).w e' * (C [(a, e')]).w (π [(a, e')]) := by
  have hset : (Finset.univ.biUnion fun e' => prefixEv (elhTree E 2) [(a, e')]) ∩
      followsEv π 1 (elhTree E 2) =
      Finset.univ.filter fun ℓ => ℓ ∈ (Finset.univ.biUnion fun e' => prefixEv (elhTree E 2) [(a, e')]) ∩
        followsEv π 1 (elhTree E 2) := by
    ext ℓ; simp
  rw [hset, mass_filter, elh2_sum]
  simp only [elh2_mem_spedt_den, elh2_leafLaw, sum_ite_const_cond, ← Finset.mul_sum,
    FinDistr.sum_one, mul_one, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e1 _ => ?_
  ring

/-- **SAEDT at the root of the two-round tree**: `μ(e_1 ∣ a_1) = ∑_s ρ(s) μ(e_1 ∣ s, a_1)` whenever
`C([])(a_1) ≠ 0` — the prior average of the percept law, policy-free.
Source: EL&H Definition 3 (SAEDT); mandate T8
Kind: P
Fidelity: variant (finite-tree rendering)
Hyps: (a) `C([])(a) ≠ 0` -/
theorem saedtBelief_two_root (a : A) (e : Fin ne) (ha : (C []).w a ≠ 0) :
    saedtBelief E C 2 [] a e = ∑ s, E.ρ.w s * (E.μ s [] a).w e := by
  unfold saedtBelief
  simp only [List.nil_append, massPrefix_two_first, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ ha]
  have : (∑ e', ∑ s, E.ρ.w s * (E.μ s [] a).w e') = 1 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FinDistr.sum_one, mul_one]
  rw [this, div_one]

/-- **SPEDT at the root of the two-round tree**: `μ(e_1 ∣ a_1, π_{2:2}) =
(∑_s ρ(s) μ(e_1 ∣ s, a_1) C((a_1,e_1))(π(a_1,e_1))) / (∑_s ρ(s) ∑_{e'} μ(e' ∣ s, a_1) C((a_1,e'))(π(a_1,e')))`
whenever `C([])(a_1) ≠ 0` — the percepts are reweighted by how surely the procedure will follow `π`
after each.
Source: EL&H Definition 4 (SPEDT); mandate T8
Kind: P
Fidelity: variant (finite-tree rendering)
Hyps: (a) `C([])(a) ≠ 0` -/
theorem spedtBelief_two_root (π : Hist A ne → A) (a : A) (e : Fin ne) (ha : (C []).w a ≠ 0) :
    spedtBelief E C 2 π [] a e =
      (∑ s, E.ρ.w s * ((E.μ s [] a).w e * (C [(a, e)]).w (π [(a, e)]))) /
        (∑ s, E.ρ.w s * ∑ e', (E.μ s [] a).w e' * (C [(a, e')]).w (π [(a, e')])) := by
  unfold spedtBelief
  simp only [List.nil_append, List.length_nil, zero_add]
  rw [spedt_two_num, spedt_two_den, mul_div_mul_left _ _ ha]

/-- **SCDT at the root of the two-round tree**: `μ(e_1 ∣ do(π_{1:2})) = ∑_s ρ(s) μ(e_1 ∣ s, π([]))` —
by Proposition 7 the whole-future intervention is the one-point deviation at the root, whose draw is
the sure `π([])`; no guard is needed.
Source: EL&H Definition 6, Proposition 7; mandate T8
Kind: C
Fidelity: variant (finite-tree rendering) -/
theorem scdtBelief_two_root (π : Hist A ne → A) (e : Fin ne) :
    scdtBelief E C 2 π [] e = ∑ s, E.ρ.w s * (E.μ s [] (π [])).w e := by
  rw [scdtBelief_eq_scdt1Belief]
  unfold scdt1Belief
  simp only [List.nil_append]
  rw [massPrefix_two_first, massPrefix_elhTree]
  have hden : (∑ s, E.ρ.w s * massPrefix (C.deviatePure [] (π [])) (elhSub E s 2 []) []) = 1 := by
    have h1 : ∀ s, massPrefix (C.deviatePure [] (π [])) (elhSub E s 2 []) [] = 1 := fun s =>
      massPrefix_elhSub_of_prefix E s _ 2 [] [] List.nil_prefix
    simp only [h1, mul_one]
    exact E.ρ.sum_one
  rw [hden, div_one]
  have hroot : ((C.deviatePure [] (π [])) []).w (π []) = 1 := by
    simp [Proc.deviatePure, Proc.deviate_same]
  rw [hroot, one_mul]

end twoRound

/-! ## The reveal instance: SAEDT ≠ SPEDT at `t = 1`, `m = 2` -/

section reveal

/-- **The reveal environment**: two hidden states drawn fairly; every percept reveals the state
(`μ(e ∣ s, ·) = δ_s`); utility `0` (the beliefs are the point, not the values).
Source: EL&H §3.1 (hidden state `s`, percept law); mandate T8 ("a hidden state that the first
percept reveals")
Kind: D -/
def revealEnv : ElhEnv Act2 2 2 where
  ρ := FinDistr.fair
  μ := fun s _ _ => FinDistr.pure s
  u := fun _ => 0

/-- **The reveal procedure**: a fair root draw; after a first percept `0` the second draw is surely
`one`, after `1` it is fair. The hidden state influences the second action *through the percept* —
the only route a Definition-6 tree offers (findings F13).
Source: mandate T8 (history-dependent mixed `C`); EL&H's toxoplasmosis mechanism rendered through
the observation
Kind: D -/
def revealProc : Proc (Hist Act2 2) (fun _ => Act2) ℚ
  | [] => FinDistr.act2 (1/2) (by norm_num) (by norm_num)
  | (_, e) :: _ => if e = 0 then FinDistr.pure .a else FinDistr.act2 (1/2) (by norm_num) (by norm_num)

/-- The policy `π ≡ one`. Source: mandate T8. Kind: D -/
def revealPolicy : Hist Act2 2 → Act2 := fun _ => .a

/-- `revealProc` after percept `0` is `δ_one`. Source: none: infrastructure. Kind: L -/
theorem revealProc_zero (x : Act2) : revealProc [(x, 0)] = FinDistr.pure .a := rfl

/-- `revealProc` after percept `1` is fair. Source: none: infrastructure. Kind: L -/
theorem revealProc_one (x : Act2) :
    revealProc [(x, 1)] = FinDistr.act2 (1/2) (by norm_num) (by norm_num) := by
  rfl

/-- **SAEDT ≠ SPEDT ≠ SCDT at the root of the reveal instance** (`t = 1`, `m = 2`): SAEDT's belief in
percept `0` after `one` is `1/2` (the prior), SPEDT's is `2/3` (percept `0` makes the procedure follow
`π` surely, percept `1` only half the time), SCDT's is `1/2` (Proposition 7). The mandate's two-step
witness; the gap is produced by the history-dependent procedure, not by a state-dependent action
likelihood (findings F13).
Source: EL&H Definitions 3, 4, 6, §3.4 ("the three decision theories differ"); mandate T8
Kind: N+ -/
theorem reveal_saedt_ne_spedt :
    saedtBelief revealEnv revealProc 2 [] .a 0 = 1/2 ∧
    spedtBelief revealEnv revealProc 2 revealPolicy [] .a 0 = 2/3 ∧
    scdtBelief revealEnv revealProc 2 revealPolicy [] 0 = 1/2 := by
  have ha : (revealProc []).w .a ≠ 0 := by simp [revealProc]
  refine ⟨?_, ?_, ?_⟩
  · rw [saedtBelief_two_root _ _ _ _ ha]
    simp [revealEnv, FinDistr.fair, FinDistr.coin]
  · rw [spedtBelief_two_root _ _ _ _ _ ha]
    simp [revealEnv, revealPolicy, FinDistr.fair, FinDistr.coin, Fin.sum_univ_two, revealProc_zero,
      revealProc_one]
    norm_num
  · rw [scdtBelief_two_root]
    simp [revealEnv, revealPolicy, FinDistr.fair, FinDistr.coin]

end reveal

end Cleanroom.Decision.DpReferentsCdt
