import Cleanroom.Udt.UdtHarmonyBargain.Harmony

/-!
# `udt-harmony-bargain` — the surviving neighbour of Theorem 11.1 (T5)

For any singleton-faithful selector (`sel {O} = O`; every welfare rule is one) and any **pure
Nash** profile `σ*` of the bargaining game (a fortiori any pure harmonious profile): if an outcome
`O*` is accepted by every player other than `j`, then `j` values the realised outcome at least as
much as `O*` (`no_all_but_one_improvement`). Hence **no outcome that a player strictly prefers is
accepted by all the others**, in particular no all-but-one-accepted subjective Pareto improvement
is left on the table (`paretoDom_not_accepted_by_others`). The deviation is `(bⱼ, {O*})`, which
realises exactly `O*` — the one case the proof of Theorem 11.1 gets right (at order `ε⁰`).

**Finding F2, reversed.** The mandate (T5, after udt-rep-072) expected the neighbour to use the
welfare rule's Pareto-consistency and asked for a witness: a singleton-faithful non-welfare `sel`
and a pure Nash profile with an all-but-one-accepted improvement left on the table. No such witness
exists: the neighbour holds for every singleton-faithful `sel`, exactly as Remark 11.2 says
("the proof only uses that `sel({O*}) = O*`"). The mandate's stated form of the neighbour
("if `U_j(O*) > U_j(outcome)` then a deal exists and `W O* ≤ W(outcome)`") has an unsatisfiable
hypothesis package under any welfare rule and is not shipped as a headline; the theorem
`mandate_form_vacuous` records that its antecedent is contradictory.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame

variable {N : Type} [Fintype N] [DecidableEq N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- A selector is singleton-faithful if it returns the unique element of a singleton.
Source: [[superconditioning-mismatched-ontologies]] §11 Remark 11.2
Kind: D -/
def SingletonFaithful (sel : Finset (Outcome A) → Outcome A) : Prop := ∀ O, sel {O} = O

/-- Every welfare selection rule is singleton-faithful.
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3(2)
Kind: L -/
theorem IsWelfareSel.singletonFaithful {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    {W : Outcome A → ℝ} (hW : IsWelfareSel Γ sel W) : SingletonFaithful sel := by
  intro O
  have := (hW.2 {O} (singleton_nonempty O)).1
  rwa [mem_singleton] at this

/-- Proposing `(b, {O*})` when everyone else accepts `O*` makes the intersection exactly `{O*}`.
Source: [[superconditioning-mismatched-ontologies]] §11 (the proof's event `E_ε`)
Kind: L -/
theorem inter_update_singleton (σ : ∀ i, Proposal A i) (j : N) (b : A j) {Os : Outcome A}
    (hacc : ∀ i, i ≠ j → Os ∈ (σ i).2) :
    inter (Function.update σ j (b, {Os})) = {Os} := by
  ext O
  simp only [mem_inter, mem_singleton]
  constructor
  · intro h
    have hj := h j
    rw [Function.update_self] at hj
    exact mem_singleton.mp hj
  · rintro rfl
    intro i
    rcases eq_or_ne i j with rfl | hi
    · rw [Function.update_self]; exact mem_singleton_self _
    · rw [Function.update_of_ne hi]; exact hacc i hi

/-- Inserting `O*` into `j`'s acceptable set when everyone else accepts `O*`: the intersection
becomes `insert O* (inter σ)` (the deviation Theorem 11.1's proof uses).
Source: [[superconditioning-mismatched-ontologies]] §11 (proof of Thm 11.1)
Kind: L -/
theorem inter_update_insert (σ : ∀ i, Proposal A i) (j : N) {Os : Outcome A}
    (hacc : ∀ i, i ≠ j → Os ∈ (σ i).2) :
    inter (Function.update σ j ((σ j).1, insert Os (σ j).2)) = insert Os (inter σ) := by
  ext O
  simp only [mem_inter, mem_insert]
  constructor
  · intro h
    have hj := h j
    rw [Function.update_self] at hj
    rcases mem_insert.mp hj with rfl | hmem
    · exact Or.inl rfl
    · right
      intro i
      rcases eq_or_ne i j with rfl | hi
      · exact hmem
      · have := h i
        rwa [Function.update_of_ne hi] at this
  · rintro (rfl | h)
    · intro i
      rcases eq_or_ne i j with rfl | hi
      · rw [Function.update_self]; exact mem_insert_self _ _
      · rw [Function.update_of_ne hi]; exact hacc i hi
    · intro i
      rcases eq_or_ne i j with rfl | hi
      · rw [Function.update_self]; exact mem_insert_of_mem (h i)
      · rw [Function.update_of_ne hi]; exact h i

/-- **The surviving neighbour of Theorem 11.1**: for any singleton-faithful selector and any pure
Nash profile of the bargaining game, an outcome accepted by every player but `j` is worth no more
to `j` than the realised outcome (else `j` grabs it with `(bⱼ, {O*})`).
Source: [[superconditioning-mismatched-ontologies]] §11 (the proof's order-1 deviation), Remark 11.2;
mandate T5
Kind: P
Fidelity: stronger (any singleton-faithful `sel`, not only welfare rules; conclusion in `j`'s own
utility)
Hyps: (a) all -/
theorem no_all_but_one_improvement {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    (hsel : SingletonFaithful sel) {σ : ∀ i, Proposal A i} (hσ : BargainNash Γ sel σ) (j : N)
    {Os : Outcome A} (hacc : ∀ i, i ≠ j → Os ∈ (σ i).2) :
    Γ.u Os j ≤ Γ.u (outcome sel σ) j := by
  have hdev := hσ j ((σ j).1, {Os})
  have hinter := inter_update_singleton σ j (σ j).1 hacc
  rw [outcome_of_nonempty sel (by rw [hinter]; exact singleton_nonempty _), hinter, hsel] at hdev
  exact hdev

/-- **No all-but-one-accepted Pareto improvement is left on the table**: if `O*` subjectively
Pareto-dominates the outcome of a pure Nash profile, it is not accepted by all the other players
of any player who strictly prefers it.
Source: [[superconditioning-mismatched-ontologies]] §11 Thm 11.1 (the surviving neighbour); mandate T5
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem paretoDom_not_accepted_by_others {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    (hsel : SingletonFaithful sel) {σ : ∀ i, Proposal A i} (hσ : BargainNash Γ sel σ)
    {Os : Outcome A} (j : N) (hlt : Γ.u (outcome sel σ) j < Γ.u Os j) :
    ¬ ∀ i, i ≠ j → Os ∈ (σ i).2 := fun hacc =>
  absurd (no_all_but_one_improvement hsel hσ j hacc) (not_le.mpr hlt)

/-- The neighbour for pure harmonious profiles under a welfare rule (via `thpe_pure_isNash`).
Source: mandate T5
Kind: C -/
theorem harmoniousPure_no_all_but_one_improvement {Γ : Game N A}
    {sel : Finset (Outcome A) → Outcome A} {W : Outcome A → ℝ} (hW : IsWelfareSel Γ sel W)
    {σ : ∀ i, Proposal A i} (h : HarmoniousPure Γ sel σ) (j : N) {Os : Outcome A}
    (hacc : ∀ i, i ≠ j → Os ∈ (σ i).2) : Γ.u Os j ≤ Γ.u (outcome sel σ) j :=
  no_all_but_one_improvement hW.singletonFaithful h.bargainNash j hacc

/-- **The mandate's form of the neighbour is vacuous** (finding F2, reversed): under any welfare
rule, no pure Nash profile has an outcome `O*` accepted by all players but `j` that `j` strictly
prefers — so "if `U_j(O*) > U_j(outcome)` then a deal exists and `W O* ≤ W(outcome)`" has an
unsatisfiable antecedent, and the harmony ledger's suggested witness (a singleton-faithful
non-welfare `sel` with such a profile) cannot exist either: singleton-faithfulness alone forbids it.
Source: mandate T5 (Remark 11.2 / finding F2); [[superconditioning-mismatched-ontologies]] §11
Remark 11.2 (vindicated for the neighbour)
Kind: N- (the antecedent is uninhabited)
Fidelity: n/a
Hyps: (a) all -/
theorem mandate_form_vacuous {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    (hsel : SingletonFaithful sel) :
    ¬ ∃ (σ : ∀ i, Proposal A i) (j : N) (Os : Outcome A), BargainNash Γ sel σ ∧
      (∀ i, i ≠ j → Os ∈ (σ i).2) ∧ Γ.u (outcome sel σ) j < Γ.u Os j := by
  rintro ⟨σ, j, Os, hσ, hacc, hlt⟩
  exact paretoDom_not_accepted_by_others hsel hσ j hlt hacc

end Cleanroom.Udt.UdtHarmonyBargain
