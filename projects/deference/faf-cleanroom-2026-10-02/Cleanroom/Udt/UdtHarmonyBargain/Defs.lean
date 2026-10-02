import SafeParetoImprovements.Game
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import Cleanroom.Found.DpCoreTree.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

/-!
# `udt-harmony-bargain` — definitions of record (T1, T2)

Part II of [[superconditioning-mismatched-ontologies]] (§9–§10): decision-points with their own
finite world-models, the derived utility game over FAF's `SafeParetoImprovements.Game`, subjective
Pareto dominance as Mathlib's `Pi.lt` (FAF's own strict Pareto improvement), the bargaining game
`𝒢` (Def. 10.2) and welfare selection rules (Def. 10.3).

Representation choices (mandate §3):
* Players `N` finite, nonempty; actions `A i` finite, nonempty; outcomes `∀ i, A i`.
* Every headline is stated over `utilGame U : Game N A` for an arbitrary `U : N → (∀ i, A i) → ℝ`,
  so nothing depends on the finite world-model of `DecisionPoint` (a `variant` disclosed once,
  here).
* Proposals `Proposal A i := A i × Finset (∀ j, A j)` (batna, acceptable set); the intersection
  `inter σ` is the filter `{O | ∀ i, O ∈ (σ i).2}` (extensionally the `Finset` intersection);
  `outcome sel σ` consults `sel` only on the nonempty intersection.
* `sel : Finset O → O` is a parameter (Def. 10.3's "consistently" made explicit); its value on `∅`
  is never consulted by `outcome`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements
open Cleanroom.Found.DpCoreTree (FinDistr)

variable {N : Type} [Fintype N] [DecidableEq N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- Joint outcomes `A = ∏ⱼ Aⱼ` (SC Def. 9.1's joint action space).
Source: [[superconditioning-mismatched-ontologies]] §9.2 Def. 9.1
Kind: D
Fidelity: exact -/
abbrev Outcome (A : N → Type) : Type := ∀ i, A i

/-- A decision-point `dᵢ = (X̂ᵢ, Aᵢ, uᵢ)`: a finite world-model `X` with a probability `μ` on it
and a utility `u : Outcome × X → ℝ`. The action set `A i` is carried by the ambient family.
Source: [[superconditioning-mismatched-ontologies]] §9.2 Def. 9.1
Kind: D
Fidelity: variant: finite world-models (`FinDistr ℝ X` on a `Fintype X`) in place of a general
probability space; no headline depends on this — every headline is stated over `utilGame U` for an
arbitrary `U`. -/
structure DecisionPoint (A : N → Type) where
  /-- The world-model's sample space. -/
  X : Type
  /-- Finiteness of the world-model. -/
  [fintypeX : Fintype X]
  /-- The world-model's probability. -/
  μ : FinDistr ℝ X
  /-- The utility of a joint outcome in a world. -/
  u : Outcome A → X → ℝ

attribute [instance] DecisionPoint.fintypeX

/-- The expected utility `Uᵢ(O) = 𝔼_{Xᵢ}[uᵢ(O, ·)]` of a decision-point.
Source: [[superconditioning-mismatched-ontologies]] §9.2 (after Def. 9.1)
Kind: D
Fidelity: exact (finite expectation) -/
def U (dp : DecisionPoint A) (O : Outcome A) : ℝ := ∑ x, dp.μ.w x * dp.u O x

/-- **The derived utility game**: FAF's `Game N A` with every action available and payoff
`u O i := U i O`. Every headline of this package is stated over this object for an arbitrary
`U : N → Outcome A → ℝ`.
Source: [[superconditioning-mismatched-ontologies]] §9.2 (the collection `{dᵢ}` as an `n`-player game)
Kind: D
Fidelity: exact -/
def utilGame (U : N → Outcome A → ℝ) : Game N A where
  S _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  u O i := U i O

@[simp] theorem utilGame_u (U : N → Outcome A → ℝ) (O : Outcome A) (i : N) :
    (utilGame U).u O i = U i O := rfl

@[simp] theorem utilGame_S (U : N → Outcome A → ℝ) (i : N) : (utilGame U).S i = Finset.univ := rfl

/-- The game of a collection of decision-points.
Source: [[superconditioning-mismatched-ontologies]] §9.2
Kind: D -/
def collectionGame (dp : N → DecisionPoint A) : Game N A := utilGame (fun i => U (dp i))

/-- A common-payoff game: every player's utility is `V`.
Source: [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1 ("the same utility function")
Kind: D -/
def commonGame (V : Outcome A → ℝ) : Game N A := utilGame (fun _ => V)

@[simp] theorem commonGame_u (V : Outcome A → ℝ) (O : Outcome A) (i : N) :
    (commonGame V).u O i = V O := rfl

/-- **Subjective Pareto dominance** (Def. 9.2): `O'` dominates `O` iff the payoff vectors satisfy
Mathlib's strict pointwise order `Pi.lt` — the same relation FAF's `Game.ParetoOptimalIn` names as
its strict Pareto improvement.
Source: [[superconditioning-mismatched-ontologies]] §9.2 Def. 9.2
Kind: D
Fidelity: exact -/
def ParetoDom (Γ : Game N A) (O O' : Outcome A) : Prop :=
  (fun i => Γ.u O i) < (fun i => Γ.u O' i)

/-- Unfolding `ParetoDom` to Def. 9.2's words: `≥` everywhere and `>` somewhere.
Source: [[superconditioning-mismatched-ontologies]] §9.2 Def. 9.2
Kind: L
Fidelity: exact -/
theorem paretoDom_iff (Γ : Game N A) (O O' : Outcome A) :
    ParetoDom Γ O O' ↔ (∀ i, Γ.u O i ≤ Γ.u O' i) ∧ ∃ i, Γ.u O i < Γ.u O' i := by
  unfold ParetoDom
  rw [Pi.lt_def]
  constructor
  · rintro ⟨hle, i, hi⟩
    exact ⟨hle, i, hi⟩
  · rintro ⟨hle, i, hi⟩
    exact ⟨hle, i, hi⟩

/-- "Not subjectively Pareto-dominated" is FAF's `ParetoOptimalIn` of the payoff vector relative
to the image of all outcomes.
Source: [[superconditioning-mismatched-ontologies]] §11 Thm 11.1 (the conclusion's vocabulary)
Kind: L
Fidelity: exact -/
theorem paretoOptimalIn_iff (Γ : Game N A) (O : Outcome A) :
    Game.ParetoOptimalIn (Γ.u O) (Γ.u '' Set.univ) ↔ ∀ O', ¬ ParetoDom Γ O O' := by
  unfold Game.ParetoOptimalIn ParetoDom
  constructor
  · intro h O' hlt
    exact h ⟨Γ.u O', ⟨O', Set.mem_univ _, rfl⟩, hlt⟩
  · rintro h ⟨y, ⟨O', -, rfl⟩, hlt⟩
    exact h O' hlt

/-- With an empty player set nothing is ever dominated (the strict clause has no witness), so
`Nonempty N` is a genuine hypothesis wherever a strict inequality is produced (finding F5).
Source: mandate T1 (trap)
Kind: L -/
theorem not_paretoDom_of_isEmpty [IsEmpty N] (Γ : Game N A) (O O' : Outcome A) :
    ¬ ParetoDom Γ O O' := by
  rw [paretoDom_iff]
  rintro ⟨-, i, -⟩
  exact IsEmpty.false i

/-- In a common-payoff game with at least one player, `O'` dominates `O` iff `V O < V O'`
(Thm 13.1(1)).
Source: [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1(1)
Kind: P
Fidelity: exact
Hyps: (a) `Nonempty N` (needed: finding F5) -/
theorem paretoDom_commonGame_iff [Nonempty N] (V : Outcome A → ℝ) (O O' : Outcome A) :
    ParetoDom (commonGame V) O O' ↔ V O < V O' := by
  rw [paretoDom_iff]
  simp only [commonGame_u]
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · intro h
    exact ⟨fun _ => h.le, Classical.arbitrary N, h⟩

/-! ### The bargaining game (Def. 10.2) -/

/-- A proposal `(bᵢ, 𝒜ᵢ)`: a batna and a finite set of acceptable outcomes.
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2 (strategies)
Kind: D
Fidelity: exact (`𝒜ᵢ ⊆ A` finite is automatic: `A` is finite) -/
abbrev Proposal (A : N → Type) (i : N) : Type := A i × Finset (Outcome A)

/-- The batna profile `b = (b₁, …, bₙ)` of a proposal profile.
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2
Kind: D -/
def batna (σ : ∀ i, Proposal A i) : Outcome A := fun i => (σ i).1

/-- The intersection `⋂ᵢ 𝒜ᵢ` of the acceptable sets, as the filter of outcomes accepted by every
player (extensionally the `Finset` intersection; `inter_two` below is the two-player form).
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2
Kind: D -/
def inter (σ : ∀ i, Proposal A i) : Finset (Outcome A) :=
  Finset.univ.filter fun O => ∀ i, O ∈ (σ i).2

@[simp] theorem mem_inter (σ : ∀ i, Proposal A i) (O : Outcome A) :
    O ∈ inter σ ↔ ∀ i, O ∈ (σ i).2 := by
  simp [inter]

/-- **The outcome rule**: `sel(⋂ᵢ 𝒜ᵢ)` if the intersection is nonempty, else the batna profile.
`sel`'s value on `∅` is never consulted (junk-value disclosure).
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2 (outcome rule)
Kind: D
Fidelity: exact -/
def outcome (sel : Finset (Outcome A) → Outcome A) (σ : ∀ i, Proposal A i) : Outcome A :=
  if (inter σ).Nonempty then sel (inter σ) else batna σ

/-- The outcome is a selected deal or the batna profile.
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2
Kind: L -/
theorem outcome_eq_sel_or_batna (sel : Finset (Outcome A) → Outcome A) (σ : ∀ i, Proposal A i) :
    ((inter σ).Nonempty ∧ outcome sel σ = sel (inter σ)) ∨
      (inter σ = ∅ ∧ outcome sel σ = batna σ) := by
  unfold outcome
  by_cases h : (inter σ).Nonempty
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨Finset.not_nonempty_iff_eq_empty.mp h, if_neg h⟩

theorem outcome_of_nonempty (sel : Finset (Outcome A) → Outcome A) {σ : ∀ i, Proposal A i}
    (h : (inter σ).Nonempty) : outcome sel σ = sel (inter σ) := if_pos h

theorem outcome_of_empty (sel : Finset (Outcome A) → Outcome A) {σ : ∀ i, Proposal A i}
    (h : ¬ (inter σ).Nonempty) : outcome sel σ = batna σ := if_neg h

/-- **The bargaining game `𝒢`** as FAF's `Game N (Proposal A)`: every proposal available, payoff
the collection's utility of the realised outcome.
Source: [[superconditioning-mismatched-ontologies]] §10.2 Def. 10.2
Kind: D
Fidelity: exact -/
def bargain (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A) : Game N (Proposal A) where
  S _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  u σ i := Γ.u (outcome sel σ) i

@[simp] theorem bargain_u (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) (i : N) : (bargain Γ sel).u σ i = Γ.u (outcome sel σ) i := rfl

/-- A universe proposal profile as a profile of `(bargain Γ sel).toStrategic` (every `S i = univ`).
Source: none: infrastructure
Kind: D -/
def toStrat (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A) (σ : ∀ i, Proposal A i) :
    (bargain Γ sel).toStrategic.Profile :=
  fun i => ⟨σ i, Finset.mem_univ _⟩

@[simp] theorem toStrat_apply (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) (i : N) : ((toStrat Γ sel σ i : Proposal A i)) = σ i := rfl

@[simp] theorem ofStrategicProfile_toStrat (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) : (bargain Γ sel).ofStrategicProfile (toStrat Γ sel σ) = σ := rfl

/-- Pure Nash equilibrium of the bargaining game in universe-profile form: no player can improve
their utility of the realised outcome by changing their own proposal.
Source: [[superconditioning-mismatched-ontologies]] §10.4 (Nash equilibria of `𝒢`)
Kind: D -/
def BargainNash (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) : Prop :=
  ∀ i (s' : Proposal A i), Γ.u (outcome sel (Function.update σ i s')) i ≤ Γ.u (outcome sel σ) i

/-- EconCSLib's `IsNashEquilibrium` of `(bargain Γ sel).toStrategic` at a universe profile is
`BargainNash` (every `S i = univ`, so the subtype strategies are all proposals).
Source: mandate §3 (the `L` lemma)
Kind: L
Fidelity: exact -/
theorem isNashEquilibrium_toStrat_iff (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) :
    _root_.IsNashEquilibrium (bargain Γ sel).toStrategic (toStrat Γ sel σ) ↔
      BargainNash Γ sel σ := by
  unfold _root_.IsNashEquilibrium _root_.IsBestResponse BargainNash
  constructor
  · intro h i s'
    have := h i ⟨s', Finset.mem_univ _⟩
    rw [Game.toStrategic_payoff, Game.toStrategic_payoff, Game.ofStrategicProfile_deviate] at this
    simpa using this
  · intro h i s'
    rw [Game.toStrategic_payoff, Game.toStrategic_payoff, Game.ofStrategicProfile_deviate]
    simpa using h i (s' : Proposal A i)

/-- Every strategic profile of the bargaining game is `toStrat` of its universe profile.
Source: none: infrastructure
Kind: L -/
theorem toStrat_ofStrategicProfile (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A)
    (τ : (bargain Γ sel).toStrategic.Profile) :
    toStrat Γ sel ((bargain Γ sel).ofStrategicProfile τ) = τ := by
  funext i; rfl

/-! ### Welfare selection (Def. 10.3) -/

/-- Pareto-consistency of a welfare function: subjective Pareto dominance is strictly respected.
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3(1)
Kind: D
Fidelity: exact -/
def ParetoConsistent (Γ : Game N A) (W : Outcome A → ℝ) : Prop :=
  ∀ O O', ParetoDom Γ O O' → W O < W O'

/-- **Welfare selection rule** (Def. 10.3): `sel` picks a `W`-maximiser of every nonempty set, for
a Pareto-consistent `W`. The tie-break is whatever `sel` does; "consistently" is by construction.
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3
Kind: D
Fidelity: exact -/
def IsWelfareSel (Γ : Game N A) (sel : Finset (Outcome A) → Outcome A) (W : Outcome A → ℝ) :
    Prop :=
  ParetoConsistent Γ W ∧ ∀ S : Finset (Outcome A), S.Nonempty → sel S ∈ S ∧ ∀ O ∈ S, W O ≤ W (sel S)

/-- The realised outcome of a nonempty intersection is `W`-maximal in it, under a welfare rule.
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3(2)
Kind: L -/
theorem IsWelfareSel.outcome_mem {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    {W : Outcome A → ℝ} (h : IsWelfareSel Γ sel W) {σ : ∀ i, Proposal A i}
    (hne : (inter σ).Nonempty) : outcome sel σ ∈ inter σ := by
  rw [outcome_of_nonempty sel hne]; exact (h.2 _ hne).1

theorem IsWelfareSel.outcome_max {Γ : Game N A} {sel : Finset (Outcome A) → Outcome A}
    {W : Outcome A → ℝ} (h : IsWelfareSel Γ sel W) {σ : ∀ i, Proposal A i}
    (hne : (inter σ).Nonempty) {O : Outcome A} (hO : O ∈ inter σ) :
    W O ≤ W (outcome sel σ) := by
  rw [outcome_of_nonempty sel hne]; exact (h.2 _ hne).2 O hO

/-- The utilitarian sum `W_sum(O) = ∑ᵢ Uᵢ(O)` (no normalisation; finding F3).
Source: [[superconditioning-mismatched-ontologies]] §10.3 ("one natural choice"), without the
`[0,1]`-normalisation that divides by zero on a constant `Uᵢ`
Kind: D -/
def wSum (Γ : Game N A) (O : Outcome A) : ℝ := ∑ i, Γ.u O i

/-- **`W_sum` is Pareto-consistent** — the "standard argument" Def. 10.3 omits: a weak improvement
everywhere with a strict one somewhere strictly raises the sum.
Source: [[superconditioning-mismatched-ontologies]] §10.3 ("the existence of a Pareto-consistent
`W` follows from a standard argument")
Kind: P
Fidelity: exact
Hyps: (a) none (a dominated pair already supplies a player) -/
theorem wSum_paretoConsistent (Γ : Game N A) : ParetoConsistent Γ (wSum Γ) := by
  intro O O' h
  rw [paretoDom_iff] at h
  obtain ⟨hle, i, hi⟩ := h
  unfold wSum
  exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hi⟩

/-- A `W`-argmax selector (ties broken by `Classical.choice`, consistently since it is a function;
its value on `∅` is arbitrary and never consulted by `outcome`).
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3(2)
Kind: D -/
noncomputable def argmaxSel (W : Outcome A → ℝ) (S : Finset (Outcome A)) : Outcome A :=
  if h : S.Nonempty then (Finset.exists_max_image S W h).choose
  else Classical.arbitrary (Outcome A)

theorem argmaxSel_spec (W : Outcome A → ℝ) {S : Finset (Outcome A)} (h : S.Nonempty) :
    argmaxSel W S ∈ S ∧ ∀ O ∈ S, W O ≤ W (argmaxSel W S) := by
  unfold argmaxSel
  rw [dif_pos h]
  exact (Finset.exists_max_image S W h).choose_spec

/-- `argmaxSel W` is a welfare selection rule for every Pareto-consistent `W`.
Source: [[superconditioning-mismatched-ontologies]] §10.3 Def. 10.3
Kind: C -/
theorem isWelfareSel_argmaxSel {Γ : Game N A} {W : Outcome A → ℝ} (hW : ParetoConsistent Γ W) :
    IsWelfareSel Γ (argmaxSel W) W :=
  ⟨hW, fun _ h => argmaxSel_spec W h⟩

/-- **Existence of a welfare selection rule** for every derived utility game (T2).
Source: [[superconditioning-mismatched-ontologies]] §10.3 (existence claim)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem exists_welfareSel (Γ : Game N A) :
    ∃ (sel : Finset (Outcome A) → Outcome A) (W : Outcome A → ℝ), IsWelfareSel Γ sel W :=
  ⟨argmaxSel (wSum Γ), wSum Γ, isWelfareSel_argmaxSel (wSum_paretoConsistent Γ)⟩

/-! ### Two-player forms -/

/-- For two players the intersection is the `Finset` intersection of the two acceptable sets.
Source: none: infrastructure
Kind: L -/
theorem inter_two {A : Fin 2 → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)]
    (σ : ∀ i, Proposal A i) : inter σ = (σ 0).2 ∩ (σ 1).2 := by
  ext O
  simp [Fin.forall_fin_two]

end Cleanroom.Udt.UdtHarmonyBargain
