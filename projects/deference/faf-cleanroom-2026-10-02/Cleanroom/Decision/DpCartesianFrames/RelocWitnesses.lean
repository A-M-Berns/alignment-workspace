import Cleanroom.Decision.DpCartesianFrames.Reloc
import Cleanroom.Decision.DpCartesianFrames.Straddle
import Cleanroom.Decision.DpCartesianFrames.MapWorld
import Mathlib.Tactic.FinCases

/-!
# The relocated mugging: the seeding is load-bearing

Package `dp-cartesian-frames`, file 9 (T5(b) ⟹, T8(b)). The relocation output
`Rel_{{d}}(B₁)` of the catalogue's mugging, over `dp-fairness-reloc`'s `relocRoot`.

* `relocMug_stronglyFair`: the coarsened output is strongly fair (`dp-fairness-reloc`'s
  `Closed.stronglyFair_output`, `{()}` being closed for a one-point tree).
* **T5(b) ⟹, dp-core-063's forward direction refuted lazily**: the coin partition is not
  column-determined in the lazy frame of the relocated mugging (`relocMug_not_columnDetermined_lazy`,
  stamped worlds; `relocMug_coarsened_not_columnDetermined_lazy`, coarsened worlds through
  `fr_mapWorld_biextEquiv`) — by Lemma A's corollary: the relocated tree's root is a decision
  node with two actions, so a column-determined partition would be trivial, while the diagonal
  columns realize both a tails and a heads world.
* **CFF-15, the identified re-reading of open problem 1 is false**: in the identified frame
  `FrIdent {()} (mug1 x y)` the coin partition **is** column-determined
  (`relocMug_columnDetermined_ident`) and **not** observable (`relocMug_not_observable_ident`) —
  a strongly fair, root-veridical tree with a chance-determined unobservable partition. The two
  seedings give opposite column-determinedness verdicts on one tree.

Seeding: `Fr (relocRoot …)` lazy (stamped worlds), `FrIdent` identified.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-- The relocated set `{d}` of the one-point mugging.
Source: none: infrastructure
Kind: D -/
abbrev U1 : Finset Unit := {()}

/-- `{()}` is closed for any one-point tree (no point lies outside it).
Source: `dp-fairness-reloc` `Closed` (definition of record)
Kind: L -/
theorem closed_U1 (B : Tree MugW Unit (fun _ => Act2) ℚ) : Closed B U1 :=
  ⟨fun _ he => absurd (Finset.mem_singleton.mpr rfl) he,
    fun _ he => absurd (Finset.mem_singleton.mpr rfl) he⟩

/-- **The coarsened relocated mugging is strongly fair** (`dp-fairness-reloc`'s T5).
Source: cf-correspondence CF-14(c) (line 69: "the relocated mugging … is strongly fair
(singleton fiber)"); `Closed.stronglyFair_output`
Kind: C
Fidelity: exact
Hyps: none -/
theorem relocMug_stronglyFair (x y : ℚ) :
    StronglyFair (mapWorld Prod.fst (relocRoot U1 (mug1 x y))) :=
  (closed_U1 (mug1 x y)).stronglyFair_output

/-- **The stamped relocated mugging itself is strongly fair** (not only its coarsening, which
`relocMug_stronglyFair` states): the root fiber is the singleton `d̂`, and no `inl` node survives
— every point of the one-point tree is relocated, so the fibers inside the resolved branches are
empty. This is the tree whose identified frame `FrIdent U1 (mug1 x y)` CFF-15's two facts are
about.
Source: `dp-fairness-reloc` T5 (`Closed.stronglyFair_output`), re-proved on the stamped tree;
cf-correspondence CF-14(c) (line 69: "strongly fair (singleton fiber)"); audit r2 (N2)
Kind: P
Fidelity: exact
Hyps: none -/
theorem relocMug_stamped_stronglyFair (x y : ℚ) : StronglyFair (relocRoot U1 (mug1 x y)) := by
  show StronglyFair (.decision (.inr ()) fun σ => resolveW U1 (fun ω => (ω, σ)) σ (mug1 x y))
  intro p q hq q' hq'
  rw [mem_fiber] at hq hq'
  have hroot : pt (.decision (.inr ()) fun σ => resolveW U1 (fun ω => (ω, σ)) σ (mug1 x y))
      none = Sum.inr () := rfl
  rcases q with _ | ⟨σ, r⟩ <;> rcases q' with _ | ⟨σ', r'⟩
  · exact LabIso.refl _
  · exfalso
    have h2 := pt_resolveW U1 (fun ω => (ω, σ')) σ' (mug1 x y) r'
    change pt (resolveW U1 (fun ω => (ω, σ')) σ' (mug1 x y)) r' = p at hq'
    rw [hroot] at hq; rw [h2] at hq'
    exact absurd (hq.trans hq'.symm) Sum.inr_ne_inl
  · exfalso
    have h2 := pt_resolveW U1 (fun ω => (ω, σ)) σ (mug1 x y) r
    change pt (resolveW U1 (fun ω => (ω, σ)) σ (mug1 x y)) r = p at hq
    rw [hroot] at hq'; rw [h2] at hq
    exact absurd (hq.trans hq'.symm) Sum.inl_ne_inr
  · exfalso
    exact nodeMapW_not_mem U1 (fun ω => (ω, σ)) σ (mug1 x y) r
      (Finset.mem_singleton.mpr (Subsingleton.elim _ _))

theorem mugWorld1_zero_mem (act : Act2) : mugWorld1 0 act ∈ mugObs () := by
  cases act <;> decide

theorem mugWorld1_one_not_mem (act : Act2) : mugWorld1 1 act ∉ mugObs () := by
  cases act <;> decide

/-- The tails and heads profiles of the mugging.
Source: none: infrastructure
Kind: D -/
def mugεT (x y : ℚ) : ChanceProfile (mug1 x y) := (0, fun _ _ => ())

def mugεH (x y : ℚ) : ChanceProfile (mug1 x y) := (1, fun _ _ => ())

/-- The relocated tree's root has two actions.
Source: none: infrastructure
Kind: L -/
theorem two_le_card_actsR_root : 2 ≤ Fintype.card (actsR (fun _ : Unit => Act2) U1 (Sum.inr ())) := by
  show 2 ≤ Fintype.card ((d : ↥U1) → Act2)
  rw [Fintype.card_pi]
  simp
  decide

/-- **T5(b) ⟹ (dp-core-063's forward direction, lazy relocated frame): the coin partition is
not column-determined in `Fr (Rel_{{d}} B₁)`** (stamped worlds). The relocated tree's root is a
decision node with two actions, so by `cell_eq_of_two_le` a column-determined partition would
put every outcome on one side; the diagonal tails and heads columns realize a tails world and a
heads world.
Source: cf-correspondence CF-14(c) (line 69: "the coin partition is not observable: … column
`(T, H)` sends pay to a `T`-world and refuse to an `H`-world — membership is not
column-determined"); cf-frontier CFF-14 (line 84: "`Rel_d(B₁)` has no nontrivial
chance-determined partition lazily"); mandate T5(b)
Kind: N+
Fidelity: exact (the mechanism is the decision root, Lemma A's corollary) -/
theorem relocMug_not_columnDetermined_lazy (x y : ℚ) :
    ¬ ColumnDetermined (Fr (relocRoot U1 (mug1 x y))) (SOR U1 mugObs ()) := by
  intro hcd
  have h := cell_eq_of_two_le (d := Sum.inr ()) (child := fun σ => resolve U1 σ (mug1 x y))
    hcd two_le_card_actsR_root (liftFun U1 fun _ => Act2.a) (liftFun U1 fun _ => Act2.a)
    (diag U1 (mug1 x y) (mugεT x y)) (diag U1 (mug1 x y) (mugεH x y))
  have eT := fr_relocRoot_outcome_diag U1 (mug1 x y) (liftFun U1 fun _ => Act2.a) (mugεT x y)
  have eH := fr_relocRoot_outcome_diag U1 (mug1 x y) (liftFun U1 fun _ => Act2.a) (mugεH x y)
  change (Fr (relocRoot U1 (mug1 x y))).outcome _ _ ∈ SOR U1 mugObs () ↔
    (Fr (relocRoot U1 (mug1 x y))).outcome _ _ ∈ SOR U1 mugObs () at h
  rw [eT, eH] at h
  have hT : mugWorld1 0 (toPolicy U1 ((liftFun U1 fun _ => Act2.a) (Sum.inr ()))
      (liftFun U1 fun _ => Act2.a) ()) ∈ mugObs () := mugWorld1_zero_mem _
  have hH : mugWorld1 1 (toPolicy U1 ((liftFun U1 fun _ => Act2.a) (Sum.inr ()))
      (liftFun U1 fun _ => Act2.a) ()) ∉ mugObs () := mugWorld1_one_not_mem _
  exact hH (h.mp hT)

/-- **T5(b) ⟹ on the coarsened output** (the tree `dp-fairness-reloc` proves strongly fair):
the coin partition `{w | w.1 ∈ O_T}` is not column-determined in the lazy frame of
`mapWorld Prod.fst (Rel_{{d}} B₁)` — transported from the stamped frame along
`fr_mapWorld_biextEquiv`.
Source: cf-correspondence CF-14(c) (line 69); mandate T5(b)
Kind: N+
Fidelity: exact -/
theorem relocMug_coarsened_not_columnDetermined_lazy (x y : ℚ) :
    ¬ ColumnDetermined (Fr (mapWorld Prod.fst (relocRoot U1 (mug1 x y)))) (SO mugObs ()) := by
  intro hcd
  rw [columnDetermined_iff_of_biextEquiv (fr_mapWorld_biextEquiv Prod.fst _),
    columnDetermined_mapWorlds_iff] at hcd
  exact relocMug_not_columnDetermined_lazy x y hcd

/-- **CFF-15, first half: under identification the coin partition is column-determined** in
`FrIdent {()} (mug1 x y)` — every policy reads the one identified coin.
Source: cf-frontier CFF-15 (line 86: "Under identification post-decision copies are read by
every policy, so a post-decision coin is chance-determined"); mandate T8(b)
Kind: N+
Fidelity: exact -/
theorem relocMug_columnDetermined_ident (x y : ℚ) :
    ColumnDetermined (FrIdent U1 (mug1 x y)) (SOR U1 mugObs ()) := by
  rintro ⟨ε', ε, hε⟩ ρ₀ ρ₁
  subst hε
  change (Fr (relocRoot U1 (mug1 x y))).outcome ρ₀ (diag U1 (mug1 x y) ε) ∈ SOR U1 mugObs () ↔
    (Fr (relocRoot U1 (mug1 x y))).outcome ρ₁ (diag U1 (mug1 x y) ε) ∈ SOR U1 mugObs ()
  rw [fr_relocRoot_outcome_diag, fr_relocRoot_outcome_diag]
  obtain ⟨i, f⟩ := ε
  fin_cases i
  · exact iff_of_true (mugWorld1_zero_mem _) (mugWorld1_zero_mem _)
  · exact iff_of_false (mugWorld1_one_not_mem _) (mugWorld1_one_not_mem _)

/-- **CFF-15, second half: under identification the coin partition is not observable** in
`FrIdent {()} (mug1 x y)`: "pay on tails, refuse on heads" needs a row whose tails world is
`(T, pay, 0)` and whose heads world is `(H, ⊥, 0)`, but one root answer fixes both.
Together with `relocMug_stronglyFair` and `relocMug_columnDetermined_ident`: a strongly fair
tree carrying a chance-determined unobservable partition — the identified re-reading of
open problem 1 is false, while the lazy statement `observable2_fr_of_stronglyFair` is true.
Source: cf-frontier CFF-15 (line 86: "three strongly fair, root-veridical, covered trees carry a
chance-determined unobservable partition: `Rel_d(B₁)` …"); CFF-16 (line 88); mandate T8(b)
Kind: N+
Fidelity: exact (the "root-veridical and covered" clauses are `dp-core-tree` facts about the
output not restated here; the refutation needs only strong fairness) -/
theorem relocMug_not_observable_ident (x y : ℚ) :
    ¬ Observable2 (FrIdent U1 (mug1 x y)) (SOR U1 mugObs ()) := by
  intro h
  obtain ⟨ρ, hρ⟩ := h (liftFun U1 fun _ => Act2.a) (liftFun U1 fun _ => Act2.b)
  have hT := hρ ⟨diag U1 (mug1 x y) (mugεT x y), ⟨mugεT x y, rfl⟩⟩
  have hH := hρ ⟨diag U1 (mug1 x y) (mugεH x y), ⟨mugεH x y, rfl⟩⟩
  change ((Fr (relocRoot U1 (mug1 x y))).outcome ρ (diag U1 (mug1 x y) (mugεT x y)) ∈
      SOR U1 mugObs () → (Fr (relocRoot U1 (mug1 x y))).outcome ρ (diag U1 (mug1 x y) (mugεT x y)) =
      (Fr (relocRoot U1 (mug1 x y))).outcome (liftFun U1 fun _ => Act2.a)
        (diag U1 (mug1 x y) (mugεT x y))) ∧ _ at hT
  change _ ∧ ((Fr (relocRoot U1 (mug1 x y))).outcome ρ (diag U1 (mug1 x y) (mugεH x y)) ∉
      SOR U1 mugObs () → (Fr (relocRoot U1 (mug1 x y))).outcome ρ (diag U1 (mug1 x y) (mugεH x y)) =
      (Fr (relocRoot U1 (mug1 x y))).outcome (liftFun U1 fun _ => Act2.b)
        (diag U1 (mug1 x y) (mugεH x y))) at hH
  rw [fr_relocRoot_outcome_diag, fr_relocRoot_outcome_diag] at hT hH
  have h1 := congrArg (fun w => w.1.1) (hT.1 (mugWorld1_zero_mem _))
  have h2 := congrArg (fun w => w.1.1) (hH.2 (mugWorld1_one_not_mem _))
  change mugWorld1 0 (toPolicy U1 (ρ (Sum.inr ())) ρ ()) = mugWorld1 0
    (toPolicy U1 ((liftFun U1 fun _ => Act2.a) (Sum.inr ())) (liftFun U1 fun _ => Act2.a) ()) at h1
  change mugWorld1 1 (toPolicy U1 (ρ (Sum.inr ())) ρ ()) = mugWorld1 1
    (toPolicy U1 ((liftFun U1 fun _ => Act2.b) (Sum.inr ())) (liftFun U1 fun _ => Act2.b) ()) at h2
  generalize toPolicy U1 (ρ (Sum.inr ())) ρ () = act at h1 h2
  cases act
  · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)

end Cleanroom.Decision.DpCartesianFrames
