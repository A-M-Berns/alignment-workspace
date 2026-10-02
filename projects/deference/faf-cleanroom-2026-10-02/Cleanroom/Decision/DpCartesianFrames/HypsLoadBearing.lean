import Cleanroom.Decision.DpCartesianFrames.Witnesses
import Cleanroom.Decision.DpCartesianFrames.OneRound

/-!
# The hypotheses of headline 3 and of CF-12 are load-bearing

Package `dp-cartesian-frames`, file 19 (repair round 2; audit r2 adversarial N5, N7, promoted
from its probe `HypsLoadBearing.lean`). Lazy seeding.

By headline 3 itself no strongly fair tree can show "fairness blocks straddling" positively; the
negative instance that shows `StronglyFair` and the straddle mechanism are load-bearing is the
catalogue's mugging `mug1 x y`, for every `x`, `y`: it is **not** strongly fair
(`mug1_not_stronglyFair`), its point **straddles** the coin partition (`mug1_straddles`), the
partition is column-determined in the global frame `Fr` (`mug1_columnDetermined_fr`) and **not**
observable there (`mug1_not_observable_fr`). So `StronglyFair` in `observable2_fr_of_stronglyFair`
cannot be dropped, and straddling is the mechanism the theorem rules out. The `Fr` statements
are also T11(a)'s locus as CF-15 and slop Claim 2.1 state it (`Fr(B₁) = Loc_d(B₁)`; the package's
`mug1_columnDetermined_not_observable` is at `Loc ()`).

Likewise the mugging is one-round (`mug1_oneRound`), with trivially disjoint observations, fails
subtree-veridicality at the heads node (`mug1_not_veridical_all`), and its observation system is
**not** observable in `Fr` (`mug1_obsSystem_not_observable`) — so `hV` in
`observable_fr_obsSystem_of_oneRound` cannot be dropped.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

variable (x y : ℚ)

/-- **The mugging is not strongly fair**: its two `d`-nodes carry leaves with different worlds.
Source: cf-correspondence CF-15 (line 75); audit r2 (N7)
Kind: N+
Fidelity: exact -/
theorem mug1_not_stronglyFair : ¬ StronglyFair (mug1 x y) := by
  intro h
  have hiso := h () ⟨0, none⟩ ((mem_fiber _ _ _).mpr rfl) ⟨1, none⟩ ((mem_fiber _ _ _).mpr rfl)
  change LabIso
    (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
      Tree.leaf (mugWorld1 0 act) (mugPay x y (mugWorld1 0 act)))
    (Tree.decision (acts := fun _ : Unit => Act2) () fun act =>
      Tree.leaf (mugWorld1 1 act) (mugPay x y (mugWorld1 1 act)))
    at hiso
  cases hiso with
  | decision _ _ _ hchild =>
    have h2 := hchild .a
    change LabIso (Tree.leaf MugW.tPay (mugPay x y MugW.tPay))
      (Tree.leaf MugW.hOne (mugPay x y MugW.hOne)) at h2
    cases h2

/-- The mugging's point is consulted on every run.
Source: none: infrastructure
Kind: L -/
theorem mug1_count_pos (π : Unit → Act2) (ε : ChanceProfile (mug1 x y)) :
    0 < count () (mug1 x y) (runLeaf π (mug1 x y) ε) := by
  obtain ⟨i, _⟩ := ε
  show 0 < (if () = () then 1 else 0) + 0
  simp

/-- **The mugging's point straddles the coin partition** (tails runs land in `S_T`, heads runs
outside): the mechanism `observable2_fr_of_not_straddles` rules out, present.
Source: cf-frontier CFF-B′ (line 50: consulted straddle); CFF-12 (line 80); audit r2 (N7)
Kind: N+
Fidelity: exact -/
theorem mug1_straddles : Straddles (mug1 x y) (SO mugObs ()) () := by
  refine ⟨⟨fun _ => .a, (0, fun _ _ => ()), mug1_count_pos x y _ _, ?_⟩,
    ⟨fun _ => .a, (1, fun _ _ => ()), mug1_count_pos x y _ _, ?_⟩⟩
  · exact mugφ_zero_mem x y .a
  · exact mugφ_one_not_mem x y .a

/-- **The coin partition is column-determined in the global frame `Fr (mug1 x y)`** (CF-15's
locus: `Fr(B₁) = Loc_d(B₁)` for a one-point tree).
Source: cf-correspondence CF-15 (line 75: "`S_T` … column-determined"); fable-slop-notes Claim
2.1 (line 39); audit r2 (N5)
Kind: N+
Fidelity: exact (every `x`, `y`) -/
theorem mug1_columnDetermined_fr : ColumnDetermined (Fr (mug1 x y)) (SO mugObs ()) := by
  rintro ⟨i, _⟩ π π'
  fin_cases i
  · exact iff_of_true (mugφ_zero_mem x y (π ())) (mugφ_zero_mem x y (π' ()))
  · exact iff_of_false (mugφ_one_not_mem x y (π ())) (mugφ_one_not_mem x y (π' ()))

/-- **… and not observable in `Fr (mug1 x y)`**: the hypothesis `StronglyFair` of headline 3 is
load-bearing — column-determinedness alone does not give observability.
Source: cf-correspondence CF-15 (line 75: "not observable"); fable-slop-notes Claim 2.1
(line 39); audit r2 (N5, N7)
Kind: N+
Fidelity: exact for CF-15 (its worlds record the choice); stronger than Claim 2.1's
`(coin, payoff)` frame, which needs `x ≠ 0`, `y ≠ 0` (findings F7) -/
theorem mug1_not_observable_fr : ¬ Observable2 (Fr (mug1 x y)) (SO mugObs ()) := by
  intro h
  obtain ⟨π, hπ⟩ := h (fun _ => .a) (fun _ => .b)
  have hT := (hπ (0, fun _ _ => ())).1 (mugφ_zero_mem x y (π ()))
  have hH := (hπ (1, fun _ _ => ())).2 (mugφ_one_not_mem x y (π ()))
  have e1 : mugWorld1 0 (π ()) = mugWorld1 0 Act2.a := congrArg Prod.fst hT
  have e2 : mugWorld1 1 (π ()) = mugWorld1 1 Act2.b := congrArg Prod.fst hH
  generalize π () = act at e1 e2
  cases act
  · exact absurd e2 (by decide)
  · exact absurd e1 (by decide)

/-- The mugging is one-round.
Source: cf-correspondence CF-12 (line 51: one-round); audit r2 (N7)
Kind: L -/
theorem mug1_oneRound : OneRound (mug1 x y) := by
  intro i
  fin_cases i <;> intro act <;> trivial

/-- **The mugging fails CF-12's veridicality hypothesis** (at the heads node).
Source: cf-correspondence CF-15 (line 75: the heads node is not subtree-veridical); audit r2 (N7)
Kind: N+
Fidelity: exact -/
theorem mug1_not_veridical_all :
    ¬ (∀ d, ∀ q ∈ fiber (mug1 x y) d, SubtreeVeridical mugObs (mug1 x y) q) :=
  fun h => (mug1_not_powerless_heads_not_veridical x y).2.1
    (h () ⟨1, none⟩ ((mem_fiber _ _ _).mpr rfl))

/-- **… and its observation system is not observable in `Fr`**: the hypothesis `hV` of CF-12
(`observable_fr_obsSystem_of_oneRound`) is load-bearing.
Source: cf-correspondence CF-12 (line 51); CF-15 (line 75); audit r2 (N7)
Kind: N+
Fidelity: exact -/
theorem mug1_obsSystem_not_observable : ¬ Observable (Fr (mug1 x y)) (obsSystem mugObs) := by
  intro h
  let f : Option Unit → (Unit → Act2) := fun c => match c with
    | some _ => fun _ => Act2.a
    | none => fun _ => Act2.b
  obtain ⟨π, hπ⟩ := h f
  have hdisj : ∀ d d' : Unit, d ≠ d' → ∀ ℓ : (mug1 x y).Leaves,
      ¬ (world (mug1 x y) ℓ ∈ mugObs d ∧ world (mug1 x y) ℓ ∈ mugObs d') :=
    fun _ _ hne _ _ => hne (Subsingleton.elim _ _)
  have e0 : obsSystem mugObs ((Fr (mug1 x y)).outcome π (0, fun _ _ => ())) = some () :=
    obsSystem_readout_eq_some mugObs (mug1 x y) hdisj _ () (mugφ_zero_mem x y (π ()))
  have e1 : obsSystem mugObs ((Fr (mug1 x y)).outcome π (1, fun _ _ => ())) = none := by
    unfold obsSystem
    rw [dif_neg]
    rintro ⟨d, hd⟩
    cases d
    exact mugφ_one_not_mem x y (π ()) hd
  have hT : (Fr (mug1 x y)).outcome (fun _ => Act2.a) (0, fun _ _ => ()) =
      (Fr (mug1 x y)).outcome π (0, fun _ _ => ()) := by
    have := hπ (0, fun _ _ => ())
    rw [e0] at this
    exact this
  have hH : (Fr (mug1 x y)).outcome (fun _ => Act2.b) (1, fun _ _ => ()) =
      (Fr (mug1 x y)).outcome π (1, fun _ _ => ()) := by
    have := hπ (1, fun _ _ => ())
    rw [e1] at this
    exact this
  have w0 : mugWorld1 0 Act2.a = mugWorld1 0 (π ()) := congrArg Prod.fst hT
  have w1 : mugWorld1 1 Act2.b = mugWorld1 1 (π ()) := congrArg Prod.fst hH
  generalize π () = act at w0 w1
  cases act
  · exact absurd w1 (by decide)
  · exact absurd w0 (by decide)

end Cleanroom.Decision.DpCartesianFrames
