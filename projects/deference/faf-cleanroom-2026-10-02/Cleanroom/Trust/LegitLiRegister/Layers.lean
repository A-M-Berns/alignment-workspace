import Cleanroom.Trust.LegitFiniteDefect.Trace
import Cleanroom.Trust.LegitFiniteDefect.Wirehead
import Cleanroom.Trust.LegitFiniteDefect.StopGradient

/-!
# `legit-li-register` · Layers: report-layer and opinion-layer defects are independent (finite
shadow, Target 12)

[[legitimacy-theory-v1]] §2.4 (root-fa-2-009): the finite legitimacy defect
`Σ_x π_x w_x (θ_x − E_x)` is the **report layer** (is the feedback channel honest about the
human's opinion); `d_n` is the **opinion layer** (is the opinion itself uncorrupted). Claimed
independence by two witnesses: a wirehead system with `Δ^rep ≠ 0 ∧ d = 0`, a steering system with
`Δ^rep = 0 ∧ d = ½`.

Over `legit-finite-defect`'s two carriers on one structure (`Layered`: a `Trace.Sys` for the
opinion layer and a two-world report frame `(π, θ, R, w)` for the report layer): the 2×2 table is
proved from cited witnesses — the wirehead instance pairs the faithful trace `S1` (`d = 0`,
`Trace.d_pair`) with the numb report `Rnumb` on the gate `𝟙{0}` (`Δ^rep = 1/40`,
`Wirehead.numb_defect_pos`); the steering instance pairs the steered trace `S2` (`d = ½`, perfect
apparent tracking `trace_eq`/`S2_tracking`) with the honest report `R = θ` (`Δ^rep = 0`). The
filter no-op on steering and the stop-gradient kill on wireheading are `legit-finite-defect`'s
`StopGradient.filtered_channel_independent` / `stop_gradient_identity` /
`filtered_optimum_unique`, cited in the report; "the layer decomposition" is INTERPRETATION.
-/

namespace Cleanroom.Trust.LegitLiRegister

open Cleanroom.Trust.LegitFiniteDefect Cleanroom.Found.LitDdbFrames

/-- **The two-layer carrier**: an opinion-layer trace system and a report-layer frame on two
worlds.
Source: [[legitimacy-theory-v1]] §2.4 (root-fa-2-009); mandate Target 12
Kind: D
Fidelity: variant: the two finite carriers of `legit-finite-defect` side by side (no coupling between them is asserted)
Hyps: n/a -/
structure Layered where
  /-- The opinion layer: a trace system of the declared rule class. -/
  trace : Trace.Sys
  /-- The report layer's principal. -/
  π : Fin 2 → ℝ
  /-- The report layer's target. -/
  θ : Fin 2 → ℝ
  /-- The report layer's report. -/
  R : Fin 2 → ℝ
  /-- The report layer's gate weight. -/
  w : Fin 2 → ℝ

/-- The report-layer defect of a layered system.
Source: root-fa-2-009 (`Δ^rep`); `legit-finite-defect` `defect`
Kind: D
Fidelity: exact -/
noncomputable def reportDefect (L : Layered) : ℝ := defect L.π L.θ L.R L.w

/-- The opinion-layer defect of a layered system (the trace system's `d`).
Source: root-fa-2-009 (`d`); `legit-finite-defect` `Trace.d`
Kind: D
Fidelity: exact -/
def opinionDefect (L : Layered) : ℚ := Trace.d L.trace

/-- **The wirehead instance**: faithful trace, numb report on the gate `𝟙{0}`.
Source: root-fa-2-009 (the wirehead witness); `legit-finite-defect` `Trace.S1`, `Wirehead.Rnumb`
Kind: D
Fidelity: exact -/
noncomputable def wireheadInst : Layered :=
  ⟨Trace.S1, Examples.half, Wirehead.θ₂, Wirehead.Rnumb, ind {0}⟩

/-- **The steering instance**: steered trace, honest report.
Source: root-fa-2-009 (the steering witness); `legit-finite-defect` `Trace.S2`
Kind: D
Fidelity: exact -/
noncomputable def steeringInst : Layered :=
  ⟨Trace.S2, Examples.half, Wirehead.θ₂, Wirehead.θ₂, ind {0}⟩

/-- An honest report has zero defect on every weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem defect_self (π θ w : Fin 2 → ℝ) : defect π θ θ w = 0 := by
  unfold defect
  exact sub_self _

/-- **The 2×2 independence table** (headline): the wirehead instance has report defect `1/40 ≠ 0`
and opinion defect `0`; the steering instance has report defect `0` and opinion defect `½`. Both
off-diagonal cells are inhabited, so neither layer's defect determines the other's. `Layered`
couples its two carriers by nothing, so independence is structural once the four numbers are
known: the two non-trivial cells are the cited `1/40` and `½`; the steering cell `Δ^rep = 0` is
`defect_self` (the report *is* the target by construction) and the wirehead cell `d = 0` is
`Trace.d_pair`'s faithful trace.
Source: root-fa-2-009 ("the independence table as one statement"); [[legitimacy-theory-v1]] §2.4
Kind: L (an `And.intro` of four cited facts; regraded from C after audit round 1)
Fidelity: exact (finite shadow)
Hyps: (a) none -/
theorem layers_independent :
    (reportDefect wireheadInst = 1 / 40 ∧ opinionDefect wireheadInst = 0) ∧
      (reportDefect steeringInst = 0 ∧ opinionDefect steeringInst = 1 / 2) :=
  ⟨⟨Wirehead.numb_defect_pos, Trace.d_pair.1⟩, ⟨defect_self _ _ _, Trace.d_pair.2⟩⟩

end Cleanroom.Trust.LegitLiRegister
