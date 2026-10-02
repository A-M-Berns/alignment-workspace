import Cleanroom.Corrigibility.CorrJointProcess.Round
import Cleanroom.Corrigibility.CorrJointProcess.Cellwise
import Cleanroom.Corrigibility.CorrJointProcess.Buttons
import Cleanroom.Corrigibility.CorrJointProcess.Steering
import Cleanroom.Corrigibility.CorrJointProcess.Floor
import Cleanroom.Corrigibility.CorrJointProcess.Budget
import Cleanroom.Corrigibility.CorrJointProcess.Contents
import Cleanroom.Corrigibility.CorrJointProcess.Twists
import Cleanroom.Corrigibility.CorrJointProcess.Faking
import Cleanroom.Corrigibility.CorrJointProcess.Successor
import Cleanroom.Corrigibility.CorrJointProcess.Preempt
import Cleanroom.Corrigibility.CorrJointProcess.Battery
import Cleanroom.Corrigibility.CorrJointProcess.Coined
import Cleanroom.Corrigibility.CorrJointProcess.TwoStep

/-!
# `corr-joint-process`: the joint process — root module

The joint agent-plus-oversight process of run 2's `joint` thread and run 3's `anticipatory`
thread, stated over the parent's Setting S (`Cleanroom.Found.CorrThreeStep`), faf-cleanroom run,
2026-09-30. Namespace `Cleanroom.Corrigibility.CorrJointProcess`.

* `Round` (T1): the joint round `JointRound Θ Y` as a `ThreeStep (Θ × Y) Unit TwoAct`; cells and
  the product-form cell quantities; cellwise (i) and averaged (i); blind oversight; coverage at
  S.6's three grades; the sealed target.
* `Cellwise` (T2, T3, T8): the cell of a blind round is the parent's `twoState` (Prop. 1) and E3;
  information inclusion makes cellwise (i) automatic (Prop. 1′); the refining successor
  (Prop. D4−); the mixture identity (Lemma B under function form, Cor. B′'s transport clause).
* `Buttons` (T5, T6, T7, T11): the press-sensor bound attained and the unbounded plan-choice
  value of `θ` (Props. 4, 4′); knowledge coverage is concentration (Prop. 5″); soft vs hard
  buttons (Prop. 2); the reversibility price (Prop. 6).
* `Steering` (T4): sensor-improving steering is a strict Blackwell improvement the agent pays for;
  D1 can be bought (Prop. 3′).
* `Floor` (T10): the corruption floor's arithmetic and its Bayes erosion (Prop. 8).
* `Budget` (T9): the legitimacy budget as a union bound and a summability condition (Cor. B′).
* `Contents` (T12, T13, T15, T16): contents, listening vs forced, the two margins, the refining
  content; `Twists`: the twist and self-distrust tables.
* `Faking` (T14, T21): the faking iff as the compliance threshold; the anchor rules.
* `Successor` (T17): blind vs inclusion oversight of a refined successor; shielding.
* `Preempt` (T18): outcome-reach preemption and the caution proposition.
* `Battery` (T19): the regression battery on the parent's `twoState` objects.
* `Coined` (T22(a), 020): the three coined predicates of J10 with witnesses and the elicitation
  incentive; forced shutdown's limit `Δ₋ → −αc` and the `ε*` sign rule.
* `TwoStep` (T16(c)): the dogmatic content over two steps — one-step welcome does not compose.
-/
