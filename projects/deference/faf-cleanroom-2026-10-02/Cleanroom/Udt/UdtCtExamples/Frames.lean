import CartesianFrames.Basic
import Mathlib.Data.Real.Basic

/-!
# `Cleanroom.Udt.UdtCtExamples.Frames`: "Cartesian frames' `W = A × E` implies something like
DD" has no statement (T6)

Work package `udt-ct-examples`, target T6 (udt-rep-088; [[notation]] §5.4). Source:
[[topics/decision-determination]] line 92: "**Cartesian Frames**: In Garrabrant's framework,
`W = A × E` imposes a product structure that implies something like DD. The I/B/E decomposition
refines this by distinguishing internal and external aspects of the agent."

FAF's `CartesianFrames.Frame W` (`CartesianFrames/Basic.lean`, Definition 1) is a pair of types
`Agent`, `Env` with `outcome : Agent → Env → W`. It has no observation, no policy, no
probability and no utility; `Ensure`/`Ctrl`/observables are not in FAF (the word "observation"
occurs in FAF's `CartesianFrames/` only in prose comments of `Operations.lean`). The only reading
of "utility depends on the agent only through its agent element" that can be stated is that a
utility on worlds, composed with `outcome`, is a function of the agent element and the
environment element — which is what composition *is*. Shipped as the `T` row it is; the analogy
rows of [[notation]] §5.4 ("ensurable ~ `Π̈`-controllable", "biextensional ~ condensation") and
bli-paper-095 are recorded in the findings (F-11) as analogies without statements.
`CartesianFrames.Basic` built in 2 s wall time on 2026-09-30 (its oleans were already produced by
FAF's own build; the run's cache had 0 of 9 before).
-/

namespace Cleanroom.Udt.UdtCtExamples

open CartesianFrames

/-- **The trivial reading of "`W = A × E` implies something like DD"**: for a frame `C` and a
utility `u` on worlds, `u (C.outcome a e)` is a function of `(a, e)` — by `rfl`. Nothing about
decision-determination (a statement about conditional independence of an environment from an
agent's dynamics given its external policy, under a probability measure) is expressible on FAF's
frames, which carry no observation, policy, measure or utility. Status `recorded (vacuous)`.
Source: [[topics/decision-determination]] line 92 (udt-rep-088); [[notation]] §5.4; mandate T6
Kind: T
Fidelity: n/a (the analogy has no object)
Hyps: none -/
theorem frame_utility_through_agent_trivial {W : Type} (C : Frame W) (u : W → ℝ) :
    ∀ a e, u (C.outcome a e) = (fun a e => u (C.outcome a e)) a e := fun _ _ => rfl

end Cleanroom.Udt.UdtCtExamples
