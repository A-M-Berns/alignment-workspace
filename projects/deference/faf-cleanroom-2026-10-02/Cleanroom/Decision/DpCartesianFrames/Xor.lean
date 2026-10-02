import Cleanroom.Decision.DpCartesianFrames.Witnesses

/-!
# ZO-14: the XOR tree — globally observable, not locally observable

Package `dp-cartesian-frames`, file 15 (repair round 1; mandate T11(c)). Lazy seeding.

The XOR tree: a fair coin; on index `0` the point `d` then the point `e`, landing in a world
`(true, d XOR e)`; on index `1` the point `d` alone, landing in `(false, d)`; `O_d = O_e =
{coin = 0}`. In `Fr B` the coin partition is observable — `e` compensates `d` on the coin-`0`
column — while at `Loc d B` it is not: the splice "`a`-row on the coin-`0` columns, `b`-row on
the coin-`1` column" is no row. Global observability does not descend to the deciding
component; the pseudo-observation test runs at `Loc d` (the converse direction of CF-13's
look-decide).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-- The bit of an action: `a ↦ true`, `b ↦ false`.
Source: none: infrastructure
Kind: D -/
def bit : Act2 → Bool
  | .a => true
  | .b => false

/-- The two branches of the XOR tree: index `0` → point `true` (`d`) then point `false` (`e`)
→ world `(true, bit d != bit e)`; index `1` → point `true` → world `(false, bit d)`.
Source: zoo ZO-14 (line 117)
Kind: D -/
def xorBranch : Fin 2 → Tree (Bool × Bool) Bool (fun _ => Act2) ℚ :=
  ![.decision true fun x => .decision false fun y => .leaf (true, bit x != bit y) 0,
    .decision true fun x => .leaf (false, bit x) 0]

/-- **The XOR tree**: a fair coin over `xorBranch`. Payoffs `0`.
Source: zoo ZO-14 (line 117: "coin `c`; `c=1`: `d` then `e` XOR into `w₁/w₂`; `c=2`: `d →
w₃/w₄`")
Kind: D
Fidelity: exact (`w₁ = (true, true)`, `w₂ = (true, false)`, `w₃ = (false, true)`,
`w₄ = (false, false)`) -/
def xorTree : Tree (Bool × Bool) Bool (fun _ => Act2) ℚ := .chance 2 FinDistr.fair xorBranch

/-- `O_d = O_e = {coin = 0}`: the worlds whose first coordinate is `true`.
Source: zoo ZO-14 (line 117: "`O_d = O_e = {c=1}`")
Kind: D -/
def xorObs : Bool → Finset (Bool × Bool) := fun _ => Finset.univ.filter fun w => w.1 = true

/-- Membership in `O_d`: the first coordinate is `true`.
Source: none: infrastructure
Kind: L -/
theorem mem_xorObs (p : Bool) (w : Bool × Bool) : w ∈ xorObs p ↔ w.1 = true := by
  simp [xorObs]

/-- The outcome of `Fr xorTree`: on a coin-`0` column `(true, d XOR e)`, on the coin-`1`
column `(false, d)`.
Source: none: infrastructure
Kind: L -/
theorem xor_fr_outcome (π : Bool → Act2) (ε : ChanceProfile xorTree) :
    (Fr xorTree).outcome π ε =
      if ε.1 = 0 then ((true, bit (π true) != bit (π false)), 0) else ((false, bit (π true)), 0) := by
  obtain ⟨i, f⟩ := ε
  fin_cases i <;> rfl

/-- **ZO-14, global half**: the coin partition is observable in `Fr xorTree` — for the
conditional policy `(π₀ on S, π₁ off S)` the row `d ↦ π₁ d`, `e ↦` whatever makes
`d XOR e` agree with `π₀` works: `e` compensates `d` on the coin-`0` column.
Source: zoo ZO-14 (line 117: "the coin partition is observable (`e` compensates `d`)")
Kind: N+
Fidelity: exact -/
theorem xorTree_observable2_fr : Observable2 (Fr xorTree) (SO xorObs true) := by
  intro π₀ π₁
  refine ⟨fun p => if p then π₁ true else
    (if (bit (π₁ true) != (bit (π₀ true) != bit (π₀ false))) then Act2.a else Act2.b), ?_⟩
  intro ε
  simp only [xor_fr_outcome]
  by_cases hi : ε.1 = 0
  · rw [if_pos hi, if_pos hi, if_pos hi]
    refine ⟨fun _ => ?_, fun h => absurd ((mem_xorObs true _).mpr rfl) h⟩
    cases π₀ true <;> cases π₀ false <;> cases π₁ true <;> rfl
  · rw [if_neg hi, if_neg hi, if_neg hi]
    exact ⟨fun h => absurd ((mem_xorObs true _).mp h) Bool.false_ne_true, fun _ => rfl⟩

/-- The outcome of `Loc true xorTree`: on a coin-`0` column `(true, x XOR e)` with `e` read
from the environment, on the coin-`1` column `(false, x)`.
Source: none: infrastructure
Kind: L -/
theorem xor_loc_outcome (x : Act2) (p : (e : {e : Bool // e ≠ true}) → Act2)
    (ε : ChanceProfile xorTree) :
    (Loc true xorTree).outcome x (p, ε) =
      if ε.1 = 0 then ((true, bit x != bit (p ⟨false, Bool.false_ne_true⟩)), 0)
      else ((false, bit x), 0) := by
  obtain ⟨i, f⟩ := ε
  fin_cases i
  · show readout xorTree ⟨0, ⟨extend (acts := fun _ : Bool => Act2) true x p true,
      ⟨extend (acts := fun _ : Bool => Act2) true x p false, ()⟩⟩⟩ = _
    rw [extend_self, extend_ne (acts := fun _ : Bool => Act2) true x p Bool.false_ne_true]
    rfl
  · show readout xorTree ⟨1, ⟨extend (acts := fun _ : Bool => Act2) true x p true, ()⟩⟩ = _
    rw [extend_self]
    rfl

/-- **ZO-14, local half**: the coin partition is *not* observable at `Loc d xorTree` — the
conditional policy "`a` on the coin-`0` columns, `b` on the coin-`1` column" would need a row
agreeing with `a` wherever the world is `(true, _)` and with `b` on the `(false, _)` column; the
former forces `x = a`, the latter `x = b`.
Source: zoo ZO-14 (line 117: "in `Loc_d` … the splice `(w₁,w₂ | w₄,w₄)` is absent, not
observable")
Kind: N+
Fidelity: exact -/
theorem xorTree_not_observable2_loc : ¬ Observable2 (Loc true xorTree) (SO xorObs true) := by
  intro h
  obtain ⟨x, hx⟩ := h Act2.a Act2.b
  let p : (e : {e : Bool // e ≠ true}) → Act2 := fun _ => Act2.a
  let εT : ChanceProfile xorTree := (0, fun _ => Classical.arbitrary _)
  let εH : ChanceProfile xorTree := (1, fun _ => Classical.arbitrary _)
  have h0 := (hx (p, εT)).1
  have h1 := (hx (p, εH)).2
  simp only [xor_loc_outcome] at h0 h1
  have hT : εT.1 = 0 := rfl
  have hH : ¬ (εH.1 = 0) := by decide
  simp only [hT, hH, if_true, if_false] at h0 h1
  have hin : (((true, bit x != bit (p ⟨false, Bool.false_ne_true⟩)), (0 : ℚ)) :
      (Bool × Bool) × ℚ) ∈ SO xorObs true := (mem_xorObs true _).mpr rfl
  have hout : ¬ ((((false, bit x), (0 : ℚ)) : (Bool × Bool) × ℚ) ∈ SO xorObs true) :=
    fun h => absurd ((mem_xorObs true _).mp h) Bool.false_ne_true
  have e0 := h0 hin
  have e1 := h1 hout
  cases x
  · exact absurd (congrArg (fun w => w.1.2) e1) (by decide)
  · exact absurd (congrArg (fun w => w.1.2) e0) (by decide)

/-- **ZO-14**: global observability does not descend to the deciding component — the XOR tree's
coin partition is observable in `Fr` and not at `Loc d` (the converse of CF-13's look-decide,
where the global frame fails and the local one succeeds).
Source: zoo ZO-14 (line 116–117); mandate T11(c)
Kind: N+
Fidelity: exact -/
theorem xorTree_observable_fr_not_loc :
    Observable2 (Fr xorTree) (SO xorObs true) ∧ ¬ Observable2 (Loc true xorTree) (SO xorObs true) :=
  ⟨xorTree_observable2_fr, xorTree_not_observable2_loc⟩

end Cleanroom.Decision.DpCartesianFrames
