import Cleanroom.Decision.DpCausalConsist.Defs

/-!
# `dp-causal-consist`: why the mixture reads each component on its support (finding F9's
counterexample; repair round 1, audit r1 N2/N5)

`mixState`'s desirability reads each component on that component's support. This file ships the
two-point counterexample the module docstring of `Defs.lean` describes: two point-mass states on
`Bool`, one carrying junk `V` on a null-extended event (legal: the averaging axiom binds only
disjoint *positive* pairs), mixed fairly. The naive Definition-25 formula
`V(X) = ∑ π_i P_i(X) V_i(X) / P(X)` violates the averaging axiom on `{true}, {false}`
(`mixState_naive_fails`), while the package's `mixState` gives `V(⊤) = 0` (`mixState_junk_V_univ`),
and its axiom is `mixState_avg`. Ported from the round-1 adversarial probe `MixJunk.lean`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

/-- The point mass at `b`. Source: none: infrastructure. Kind: D -/
def dirac (b : Bool) : FinDistr ℚ Bool where
  w x := if x = b then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by cases b <;> simp

/-- `probOf` of a point mass. Source: none: infrastructure. Kind: L -/
theorem probOf_dirac (b : Bool) (X : Finset Bool) :
    probOf (dirac b) X = if b ∈ X then 1 else 0 := by
  unfold probOf dirac
  simp only
  rw [Finset.sum_ite_eq' X b]

/-- A state with law `δ_b` and an arbitrary desirability: the averaging axiom is vacuous (two
disjoint events cannot both be positive under a point mass), so `V` may be junk on every event
other than the ones a mixture reads.
Source: [[decision-problems-v2]] Definition 2 (`V` defined on non-null events only); finding F9
Kind: D -/
def junkState (b : Bool) (V : Finset Bool → ℚ) : State Bool ℚ where
  P := dirac b
  V := V
  avg X Y hXY hX hY := by
    exfalso
    rw [probOf_dirac] at hX hY
    split_ifs at hX hY with h1 h2
    · exact Finset.disjoint_left.mp hXY h1 h2
    all_goals norm_num at *

/-- The fair mixing weights on `Bool`. Source: none: infrastructure. Kind: D -/
def fairBool : FinDistr ℚ Bool where
  w _ := 1/2
  nonneg _ := by norm_num
  sum_one := by simp

/-- Component `true`: law `δ_true`, `V(⊤) = 100` (junk: `⊤ ⊋ {true}` differs from `{true}` by a
null point), `V = 0` elsewhere. Component `false`: law `δ_false`, `V ≡ 0`.
Source: finding F9
Kind: D -/
def junkComps : Bool → State Bool ℚ := fun i =>
  if i then junkState true (fun X => if true ∈ X ∧ false ∈ X then 100 else 0)
  else junkState false (fun _ => 0)

/-- The naive mixture desirability of Definition 25 read literally (components read on `X`, not
on `X ∩ supp`). Source: [[defining-cdt-in-the-learning-setting]] Definition 25. Kind: D -/
def naiveMixV (X : Finset Bool) : ℚ :=
  (∑ i, fairBool.w i * (junkComps i).pr X * (junkComps i).V X)
    / ∑ i, fairBool.w i * (junkComps i).pr X

/-- The mixed law. Source: none: infrastructure. Kind: D -/
def junkMixP (X : Finset Bool) : ℚ := ∑ i, fairBool.w i * (junkComps i).pr X

/-- **The naive formula violates the averaging axiom**: `V(⊤)·P(⊤) = 50` while
`P{true}·V{true} + P{false}·V{false} = 0`.
Source: finding F9 (Definition 25's formula on a Lean `State` with junk off the support)
Kind: N+ -/
theorem mixState_naive_fails :
    naiveMixV Finset.univ * junkMixP Finset.univ
      ≠ junkMixP {true} * naiveMixV {true} + junkMixP {false} * naiveMixV {false} := by
  simp [naiveMixV, junkMixP, junkComps, junkState, fairBool, State.pr, probOf_dirac]

/-- **The package's `mixState` does not**: reading each component on its support, `V(⊤) = 0` (the
axiom is `mixState_avg`, proved in the package).
Source: finding F9
Kind: N+ -/
theorem mixState_junk_V_univ : (mixState fairBool junkComps).V Finset.univ = 0 := by
  rw [mixState_V]
  simp [junkComps, junkState, fairBool, State.pr, supp, dirac]

end Cleanroom.Decision.DpCausalConsist
