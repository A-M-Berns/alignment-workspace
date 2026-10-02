import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpCalibration.Mugging

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T12: the coupling-uncertainty refuser (`fable-slop-notes` §6)

Thin, and said so: (b) a payer's value separates the coupled mugging `B₁(x, y)` from the inert
`B₁(x, 0)` by `q y / 2`, a refuser's does not (`= 0` iff `q = 0`); a mixture weight `π` on the
coupled tree makes paying worthwhile iff `π > x/y`. (a) The root-decision tree with
`r = ½ y·𝟙[pay] − ½ x·𝟙[pay]` has the payer's value `(y − x)/2 = V_{B₁}(pay)`. The learning
claim ("a refuser never learns") is not in the type and is recorded only; the "three readings of
`½`" is prose.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

section coupling

variable (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- **The coupling gap**: `V_{B₁(x,y)}(q) − V_{B₁(x,0)}(q) = q y / 2` — a payer's value separates
the coupled tree from the inert one, a refuser's (`q = 0`) does not.
Source: [[fable-slop-notes]] §6 ("Decay as coupling-uncertainty … a refuser sees no transfers
under either hypothesis"); dp-core-070
Kind: T
Fidelity: exact -/
theorem mug1_coupling_gap :
    value (procQ q h0 h1) (mug1 x y) - value (procQ q h0 h1) (mug1 x 0) = q * y / 2 := by
  rw [mug1_value, mug1_value]; simp [procQ]; ring

/-- The gap vanishes iff the agent refuses (for `y ≠ 0`).
Source: [[fable-slop-notes]] §6 ("refusing is *self-confirming*")
Kind: T -/
theorem mug1_coupling_gap_zero_iff (hy : y ≠ 0) :
    value (procQ q h0 h1) (mug1 x y) - value (procQ q h0 h1) (mug1 x 0) = 0 ↔ q = 0 := by
  rw [mug1_coupling_gap]
  constructor
  · intro h
    have : q * y = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hy
  · rintro rfl; ring

/-- **The mixture criterion**: with credence `π` on the coupled tree, paying is worthwhile —
`π V_{B₁(x,y)}(pay) + (1−π) V_{B₁(x,0)}(pay) > 0` — iff `π > x/y` (for `0 < y`).
Source: [[fable-slop-notes]] §6 ("pays iff `π(couple) > x/y`"); Appendix B's mixture
calibration
Kind: T
Fidelity: exact -/
theorem mug1_mixture_pays_iff (hy : 0 < y) (π : ℚ) :
    0 < π * value (procQ 1 zero_le_one le_rfl) (mug1 x y) +
        (1 - π) * value (procQ 1 zero_le_one le_rfl) (mug1 x 0) ↔ x / y < π := by
  rw [mug1_value, mug1_value]
  simp only [procQ, FinDistr.act2_a]
  rw [div_lt_iff₀ hy]
  constructor <;> intro h <;> nlinarith

end coupling

/-- **The root-decision tree** with `r = ½ y·𝟙[pay] − ½ x·𝟙[pay]`: the coin absorbed into the
payoff as a weight (reality (3), the caring measure; the same tree read as a self-location
credence or as the description's chance).
Source: [[fable-slop-notes]] §6 Claim 6.1 ("a root decision node whose leaf carries
`r = ½ y 𝟙[pay] − ½ x 𝟙[pay]`")
Kind: D -/
def rootMug (x y : ℚ) : Tree Unit Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf () (y / 2 - x / 2)
    | .b => .leaf () 0

/-- The root-decision tree's payer value is `(y − x)/2 = V_{B₁}(δ_pay)`: the three readings of
`½` are one tree.
Source: [[fable-slop-notes]] §6 Claim 6.1 ("The tree formalism cannot distinguish them")
Kind: T
Fidelity: exact -/
theorem rootMug_value (x y : ℚ) :
    value (procQ 1 zero_le_one le_rfl) (rootMug x y) = (y - x) / 2 ∧
    value (procQ 1 zero_le_one le_rfl) (rootMug x y) =
      value (procQ 1 zero_le_one le_rfl) (mug1 x y) := by
  have h : value (procQ 1 zero_le_one le_rfl) (rootMug x y) = (y - x) / 2 := by
    simp [rootMug, value_decision, Act2.sum_univ, procQ]; ring
  refine ⟨h, ?_⟩
  rw [h, mug1_value]; simp [procQ]

end Cleanroom.Decision.DpDevicesCatalog
