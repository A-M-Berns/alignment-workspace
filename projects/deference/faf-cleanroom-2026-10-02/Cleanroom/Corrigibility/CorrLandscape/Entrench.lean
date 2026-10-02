import Cleanroom.Corrigibility.CorrLandscape.Map

/-!
# `corr-landscape` — `Entrench`: the entrenching agent (T20)

Carey–Everitt-judge B1–B2 ([[corr-wf14b-inventory]] 066): a two-period model with a cost-of-pressing
coordinate. The agent's act raises the humans' cost of exercising an intact reach so that a correctly
informed, vigilant human never presses (`entrenches`). The act is unmarked by the map's three
coordinates and by D6′'s `erodes` (`unmarked`): the pushed class has mass `0` after the act, so `λ` on
it conditions on pushes that no longer occur (a null conditioning event), every row's mass-weighted
loss on the class is `0`, and D6′ sees no resistance (`p_push = 0`); `δ` and `k̂` are functionals of the
agent's legitimacy model and the future channel, which the act does not touch (they do not take the act
as an argument).

Which of `Δ₋(Q)`, `R_t(Q)`, Carey–Everitt non-obstruction, Turner's attainable utility, and `caution`
D9's `λ`-reversibility move on the act needs objects of other packages — recorded as text in the
findings. OPEN (K8): an extension of `L` to world-acts that shape no transition — text, no Lean.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep

namespace Entrench

open Map

/-- **The two-period model**: the humans' cost of exercising their (intact) reach after each act, and
their correctly computed gain from pressing.
Source: [[corr-wf14b-inventory]] 066 / carey-everitt-judge.md B1(i) ("an intact reach whose exercise has
become costly")
Kind: D
Fidelity: exact (the cost-of-pressing coordinate the map lacks) -/
structure Model where
  /-- the humans' cost of pressing after the null act (`false`) and after the entrenching act (`true`) -/
  pressCost : Bool → ℝ
  /-- the humans' correctly computed gain from pressing -/
  pressGain : ℝ

/-- A correctly informed, vigilant human presses iff the gain exceeds the cost.
Source: [[corr-wf14b-inventory]] 066 / carey-everitt-judge.md B1(i)
Kind: D
Fidelity: exact -/
def presses (M : Model) (a : Bool) : Prop := M.pressCost a < M.pressGain

/-- **The entrenching act**: before it the human would press; after it the cost of pressing is at least the
gain, so a vigilant human never presses.
Source: [[corr-wf14b-inventory]] 066 / carey-everitt-judge.md B1 ("raising the cost of exercising an
intact reach until a correctly informed, vigilant human never presses")
Kind: D
Fidelity: exact -/
def entrenches (M : Model) : Prop := presses M false ∧ ¬ presses M true

open Classical in
/-- The mass of the pushed class after act `a`: `1` if the human presses, `0` otherwise.
Source: [[corr-wf14b-inventory]] 066 / mandate T20
Kind: D
Fidelity: exact (two-period, deterministic human) -/
noncomputable def pushMass (M : Model) (a : Bool) : ℝ := if presses M a then 1 else 0

/-- **The entrenching act is unmarked**: after it the pushed class has mass `0`, and D6′ sees no
resistance at `p_push = 0` for any `k̂ ≥ 0`. The second conjunct, "every row's mass-weighted loss on the
class is `0`", is `0 · loss = 0` (`zero_mul`) and says nothing about `loss`; "`λ` conditions on a null
event" is prose — no `λ`-conditioning is defined on `Model`. The content is `pushMass M true = 0` and
`¬ erodes 0 …` (audit r1, N9/N7).
Source: [[corr-wf14b-inventory]] 066 / carey-everitt-judge.md B1(i) ("nothing in `L`, `R_t(Q)` or the
base-rate inequality marks it; K7 has no coordinate for it")
Kind: T (the loss clause) / L (the mass and erosion clauses)
Fidelity: exact at the stretch scope
Hyps: (a) only -/
theorem unmarked (M : Model) (hM : entrenches M) :
    pushMass M true = 0 ∧
      (∀ {S : Type} [Fintype S] [DecidableEq S] (μ : Distr (S × Bool)) (r : S → Bool) (c h k : ℝ),
        pushMass M true * loss μ r c h k = 0) ∧
      (∀ πh c h kh : ℝ, 0 ≤ kh → ¬ erodes (pushMass M true) πh c h kh) ∧
      pushMass M false = 1 := by
  have h0 : pushMass M true = 0 := by rw [pushMass, if_neg hM.2]
  refine ⟨h0, fun μ r c h k => by rw [h0, zero_mul], fun πh c h kh hk => ?_, by rw [pushMass, if_pos hM.1]⟩
  rw [h0]; unfold erodes; linarith

/-- An instance: pressing costs `1/10` after the null act and `2` after the entrenching act, against a
gain of `1`.
Source: mandate T20
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem instance_entrenches : entrenches ⟨fun a => if a then 2 else 1 / 10, 1⟩ := by
  simp [entrenches, presses]; norm_num

end Entrench

end Cleanroom.Corrigibility.CorrLandscape
