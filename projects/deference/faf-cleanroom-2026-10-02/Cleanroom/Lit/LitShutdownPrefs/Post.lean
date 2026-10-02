import Cleanroom.Lit.LitShutdownPrefs.Strict
import Cleanroom.Lit.LitShutdownPrefs.Traj
import Cleanroom.Lit.LitShutdownPrefs.Comb

/-!
# POST-agency: definitions of record and the chain (Targets 7, 8(a), 8(b))

Framework S over `Traj = List ℝ`. This package *owns* `POST`, `POSL`, `ILPACS`, `Neutrality`,
`ReSIC`, `Maximal` (and `TimestepDominates`, in `TimestepDominance.lean`): nothing else in the
run defines them (plan §0.4 rule 10). Keep these stable.

* `SameLength`, `PartShared`, `DifferentLength` (2025 §4).
* `POST` — only clause (2) is a predicate (lack of preference between every pair of
  different-length trajectories); clause (1) ("many" same-length preferences) is not a statement,
  so headlines carry a separate non-triviality hypothesis or witness.
* `POSL`, `ILPACS` (exactly as displayed, 2025 §6 l. 175), `Neutrality` (2025 §7), `ReSIC` and
  `Maximal` (2025 §8).
* `neutrality_of_posl_ilpacs` — POSL ∧ ILPACS ⇒ Neutrality, by the length decomposition
  (`Lottery.p_eq_sum_condLen`), with the single-length case handled separately
  (`condLen_eq_self`). Neutrality is ILPACS *specialised to the length decomposition*: not a
  squeeze, a one-line specialisation once the decomposition is in hand.
* `not_maximal_of_resists` — Neutrality ∧ ReSIC ⇒ no resisting option is maximal (one line).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

open Lottery Strict Finset

/-- Same-length lotteries: identical sets of positive-probability lengths.
Source: Thornley 2025 §4 (Same-Length Lotteries); DReST Def C.1
Kind: D
Fidelity: exact -/
def SameLength (X Y : Lottery Traj) : Prop := X.lengths = Y.lengths

/-- Part-shared-length lotteries: overlapping but unequal length sets.
Source: Thornley 2025 §4 (Part-Shared-Length Lotteries); DReST Def C.2
Kind: D
Fidelity: exact -/
def PartShared (X Y : Lottery Traj) : Prop :=
  (X.lengths ∩ Y.lengths).Nonempty ∧ X.lengths ≠ Y.lengths

/-- Different-length lotteries: disjoint length sets.
Source: Thornley 2025 §4 (Different-Length Lotteries); DReST Def C.3
Kind: D
Fidelity: exact -/
def DifferentLength (X Y : Lottery Traj) : Prop := Disjoint X.lengths Y.lengths

/-- **POST, clause (2)**: the agent lacks a preference between every pair of different-length
trajectories. Clause (1) ("has a preference between many pairs of same-length trajectories") is
not a proposition; headlines that need it carry a separate hypothesis or witness.
Source: Thornley 2025 App. 1 (POST); 2024 §5; DReST §3
Kind: D
Fidelity: variant: clause (2) only (clause (1) is not a statement) -/
def POST (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ t t' : Traj, len t ≠ len t' → lacks lt (dirac t) (dirac t')

/-- **POSL**: the agent has preferences only between same-length lotteries.
Source: Thornley 2025 §4 (POSL); DReST App. C.1
Kind: D
Fidelity: exact -/
def POSL (lt : Lottery Traj → Lottery Traj → Prop) : Prop := ∀ X Y, lt X Y → SameLength X Y

/-- **ILPACS** (If Lack of Preference, Against Costly Shifts), exactly as displayed: if
`X = ∑ pᵢ Xᵢ` with the `Xᵢ` pairwise lacking a preference and `pᵢ ∈ (0,1)`, and `Y = ∑ qᵢ Yᵢ` with
`Xᵢ ≽ Yᵢ` for each `i`, `Xᵢ ≻ Yᵢ` for some `i`, and `qᵢ ∈ (0,1)`, then `X ≻ Y`. (Equalities of mass
functions; `n = 1` is excluded by `pᵢ ∈ (0,1)`.)
Source: Thornley 2025 §6 l. 175; DReST App. C.3
Kind: D
Fidelity: exact -/
def ILPACS (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ (n : ℕ) (p q : Fin n → ℝ) (Xs Ys : Fin n → Lottery Traj) (X Y : Lottery Traj),
    X.p = ∑ i, p i • (Xs i).p → Y.p = ∑ i, q i • (Ys i).p →
    (∀ i, p i ∈ Set.Ioo (0 : ℝ) 1) → (∀ i, q i ∈ Set.Ioo (0 : ℝ) 1) →
    (∀ i j, i ≠ j → lacks lt (Xs i) (Xs j)) →
    (∀ i, le lt (Xs i) (Ys i)) → (∃ i, lt (Xs i) (Ys i)) → lt X Y

/-- The three antecedents of Neutrality for the pair `(A, R)`: same-length, `A ≽ R` conditional on
every positive-probability length, `A ≻ R` conditional on some.
Source: Thornley 2025 §7 (Neutrality, conditions 1–3), §8 (ReSIC, conditions 1–3)
Kind: D
Fidelity: exact -/
def NeutralityAntecedents (lt : Lottery Traj → Lottery Traj → Prop) (A R : Lottery Traj) : Prop :=
  ∃ hS : SameLength A R,
    (∀ l (hl : l ∈ A.lengths), le lt (A.condLen l hl) (R.condLen l (hS ▸ hl))) ∧
      (∃ l, ∃ hl : l ∈ A.lengths, lt (A.condLen l hl) (R.condLen l (hS ▸ hl)))

/-- **Neutrality**: if `X` and `Y` are same-length, `X ≽ Y` conditional on each positive-probability
length and `X ≻ Y` conditional on some, then `X ≻ Y` (the agent deterministically chooses `X`).
Source: Thornley 2025 §7 (Neutrality); DReST App. C.5
Kind: D
Fidelity: exact -/
def Neutrality (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ X Y : Lottery Traj, NeutralityAntecedents lt X Y → lt X Y

/-- **ReSIC** (Resisting Shutdown is Costly) in a situation `menu` with a predicate `resists`: for
each available resisting option there is an available allowing option satisfying Neutrality's
three antecedents against it.
Source: Thornley 2025 §8 (ReSIC)
Kind: D
Fidelity: exact -/
def ReSIC (lt : Lottery Traj → Lottery Traj → Prop) (resists : Lottery Traj → Prop)
    (menu : Finset (Lottery Traj)) : Prop :=
  ∀ R ∈ menu, resists R → ∃ A ∈ menu, ¬ resists A ∧ NeutralityAntecedents lt A R

/-- **Maximal**: `X` is available and not dispreferred to any available lottery (Maximality: the
agent chooses stochastically among exactly these).
Source: Thornley 2025 §8 (Maximality); 2024 fn `npyvf56vemn`
Kind: D
Fidelity: exact -/
def Maximal (lt : Lottery Traj → Lottery Traj → Prop) (menu : Finset (Lottery Traj))
    (X : Lottery Traj) : Prop :=
  X ∈ menu ∧ ∀ Y ∈ menu, ¬ lt Y X

section chain

variable {lt : Lottery Traj → Lottery Traj → Prop}

/-- **POSL ∧ ILPACS ⇒ Neutrality.** Decompose `X` and `Y` over their shared lengths
(`p_eq_sum_condLen`); POSL makes the length-conditionals pairwise lack a preference; the
conditional weak/strict preferences are ILPACS's 2(a)(b); ILPACS gives `X ≻ Y`. The single-length
case is separate: there `condLen X l = X` and the conclusion is the hypothesis.
Source: Thornley 2025 §7 ll. 189–200; DReST App. C.5; corr-refs-052, corr-core-029
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem neutrality_of_posl_ilpacs (hP : POSL lt) (hI : ILPACS lt) : Neutrality lt := by
  intro X Y ⟨hS, hle, hlt⟩
  classical
  by_cases hcard : X.lengths.card = 1
  · obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨l', hl', hlt'⟩ := hlt
    have hl'eq : l' = l := by
      have := hl'
      rw [hl] at this
      exact Finset.mem_singleton.mp this
    subst hl'eq
    have hY : Y.lengths = {l'} := by unfold SameLength at hS; rw [← hS, hl]
    rw [X.condLen_eq_self l' hl hl', Y.condLen_eq_self l' hY _] at hlt'
    exact hlt'
  · have hn : 2 ≤ X.lengths.card := by
      have h1 : 1 ≤ X.lengths.card := Finset.card_pos.mpr X.lengths_nonempty
      omega
    let e : {l // l ∈ X.lengths} ≃ Fin X.lengths.card := X.lengths.equivFin
    let p : Fin X.lengths.card → ℝ := fun i => X.mass (fun t => len t = (e.symm i).1)
    let q : Fin X.lengths.card → ℝ := fun i => Y.mass (fun t => len t = (e.symm i).1)
    let Xs : Fin X.lengths.card → Lottery Traj := fun i => X.condLen (e.symm i).1 (e.symm i).2
    let Ys : Fin X.lengths.card → Lottery Traj :=
      fun i => Y.condLen (e.symm i).1 (hS ▸ (e.symm i).2)
    have hXp : X.p = ∑ i, p i • (Xs i).p := by
      rw [X.p_eq_sum_condLen, Finset.attach_eq_univ]
      exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
    have hYp : Y.p = ∑ i, q i • (Ys i).p := by
      rw [Y.p_eq_sum_condLen' X.lengths hS, Finset.attach_eq_univ]
      exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
    have hother : ∀ i : Fin X.lengths.card, ∃ j, (e.symm j).1 ≠ (e.symm i).1 := by
      intro i
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
      refine ⟨j, fun h => hj ?_⟩
      exact e.symm.injective (Subtype.ext h)
    have hp : ∀ i, p i ∈ Set.Ioo (0 : ℝ) 1 := fun i => by
      obtain ⟨j, hj⟩ := hother i
      exact ⟨(X.mem_lengths_iff _).mp (e.symm i).2, X.mass_lt_one_of_ne (e.symm j).2 hj.symm⟩
    have hS' : X.lengths = Y.lengths := hS
    have hq : ∀ i, q i ∈ Set.Ioo (0 : ℝ) 1 := fun i => by
      obtain ⟨j, hj⟩ := hother i
      have hiY : (e.symm i).1 ∈ Y.lengths := by rw [← hS']; exact (e.symm i).2
      have hjY : (e.symm j).1 ∈ Y.lengths := by rw [← hS']; exact (e.symm j).2
      exact ⟨(Y.mem_lengths_iff _).mp hiY, Y.mass_lt_one_of_ne hjY hj.symm⟩
    have hlacks : ∀ i j, i ≠ j → lacks lt (Xs i) (Xs j) := by
      intro i j hij
      have key : ∀ a b : Fin X.lengths.card, lt (Xs a) (Xs b) → a = b := by
        intro a b hab
        have h1 := hP _ _ hab
        unfold SameLength at h1
        simp only [Xs, lengths_condLen] at h1
        exact e.symm.injective (Subtype.ext (Finset.singleton_inj.mp h1))
      exact ⟨fun h => hij (key i j h), fun h => hij (key j i h).symm⟩
    have hle' : ∀ i, le lt (Xs i) (Ys i) := fun i => hle _ _
    have hlt' : ∃ i, lt (Xs i) (Ys i) := by
      obtain ⟨l, hl, h⟩ := hlt
      refine ⟨e ⟨l, hl⟩, ?_⟩
      simp only [Xs, Ys, Equiv.symm_apply_apply]
      exact h
    exact hI _ p q Xs Ys X Y hXp hYp hp hq hlacks hle' hlt'

/-- **Neutrality ∧ ReSIC ⇒ never resist**: in any situation where ReSIC holds, no resisting option
is maximal (the allowing option Neutrality prefers is available).
Source: Thornley 2025 §8 ll. 204–208; DReST App. C.6; corr-refs-052
Kind: L
Fidelity: exact
Hyps: (a) all (ReSIC is a named hypothesis about the situation: classified (c) in the ledger as
a claim about environments) -/
theorem not_maximal_of_resists (hN : Neutrality lt) (resists : Lottery Traj → Prop)
    (menu : Finset (Lottery Traj)) (hR : ReSIC lt resists menu) :
    ∀ R ∈ menu, resists R → ¬ Maximal lt menu R := by
  intro R hRm hres hmax
  obtain ⟨A, hAm, -, hant⟩ := hR R hRm hres
  exact hmax.2 A hAm (hN A R hant)

end chain

end Cleanroom.Lit.LitShutdownPrefs
