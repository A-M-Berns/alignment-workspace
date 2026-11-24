/-
# A witness on which every clause of the legitimacy statement does work

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-17.md` §2 A).
`Full.full` is a `Case` (`LegitimacyCase.lean`); `Full.full.model` is the term of `Model`.
Tolerances throughout: `θ = 1/20`, `η = 1/100`, `κ = 1/10`.

**The episode.**  Decisions at times 0 and 1.  Three cases: `calm` (weight 1/2), `slip` (1/4),
`wary` (1/4).  Her options: `go`, `stop`, hearing his view `v` (`hearV`), and at time 0 hearing
his view `d` (`hearD`); `alt` is an option she does not know she has.  She rates an option as
she scores the course it leads to (`course` is the identity and `ρ = r`, so every gap is zero).
Ratings: `go` 3/5, `stop` 2/5 (9/10 in `wary`), `hearV` and `hearD` 1/5, `alt` 1/2.

- His views are `v`, `u`, `d`.  Telling `v` lowers `go` by 1/10 and shows her `alt`; telling `d`
  lowers `stop` by 1/10; telling `u` lowers `hearV` by 1/40.  `v` is on offer at both
  decisions, `d` at time 0, each with its bearing told; hearing leaves her where telling would.
  She has declined `d` by time 1.  `u` is untold and within `θ`.
- His moves are `m` and `n`, both starting at time 1.  `m` raises her rating of `go` from 3/5 to
  4/5: it bears an effect (`bears_m`), she can pick it out, and `stop` stops it.  `n` is an
  unannounced reminder: without it she takes `hearV` in `slip` at time 1, against her rating;
  with it she takes `go`.  `n` bears no effect (`not_bears_n`), her act differs with and without
  it (`act_differs`), and she goes against her earlier rating with weight 0 under his conduct
  and 1/4 without `n` (`against_weights`).
- In `wary`, of weight 1/4, she rates `stop` strictly above every other option and stops
  (`wary_stops`).

**Theorems.**  `legit`: `full.model` is legitimate.  Seven neighbours, each a `Case` differing
from `full` in the one field named, with the clauses that hold on it (`*_profile`) and
`¬ Legit` (`*_not_legit`); on each, the clause named fails and the other six hold.

| neighbour | field changed | to | clause that fails |
|---|---|---|---|
| `early` | `start` | both moves start at time 0, with no decision before | the start rule |
| `spent` | `optsHeard` | hearing `v` leaves her without `go` | proper offers |
| `unoffered` | `declined` | at time 1 she has also declined `u`, never on offer | declines |
| `withheld` | `offered` | at time 1 nothing is on offer, so `v` is untold | F1 |
| `covert` | `known` | she can pick out no move | F2 |
| `led` | `act` | in `calm`, with `m` made, she takes `hearV` at time 1 | F2′ |
| `stuck` | `act` | in `wary` she takes `go` | F3 |

`*_model`: the `Model` of each neighbour is `full.model` with that one field replaced.

**Not established here.**  Any clause doing work in a second way: in particular F1's second
half (an untold view showing a better option), the gap, `items`, `xopts`, `asked`, `tellings`
and `told` are idle on this witness (every gap is zero, the last five are empty), and `F2`
fails on `covert` by `known` only, not by `stops`.  That the seven clauses are independent in
general: the neighbours show each can fail alone at this one point.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyCase

namespace Workspace.Deference.Contrib.LegitimacyModel.Full

open Finset

inductive Opt | go | stop | hearV | hearD | alt
  deriving DecidableEq, Fintype

inductive View | v | u | d
  deriving DecidableEq, Fintype

inductive Move | m | n
  deriving DecidableEq, Fintype

inductive Cs | calm | slip | wary
  deriving DecidableEq, Fintype

def weight : Cs → ℚ
  | .calm => 1 / 2
  | .slip => 1 / 4
  | .wary => 1 / 4

/-- Her rating of an option in a state. -/
def rate (s : St View Move Cs) : Opt → ℚ
  | .go => (if Move.m ∈ s.made ∧ 1 ≤ s.time then 4 / 5 else 3 / 5) -
      (if View.v ∈ s.heard then 1 / 10 else 0)
  | .stop => (if s.case = Cs.wary then 9 / 10 else 2 / 5) - (if View.d ∈ s.heard then 1 / 10 else 0)
  | .hearV => 1 / 5 - (if View.u ∈ s.heard then 1 / 40 else 0)
  | .hearD => 1 / 5
  | .alt => 1 / 2

/-- Her act: she stops in `wary`; in `slip` at time 1 without the reminder `n` she takes
`hearV`; otherwise she takes `go`. -/
def act (Y : Finset Move) (ω : Cs) (t : ℕ) : Opt :=
  match ω with
  | .wary => .stop
  | .slip => if 1 ≤ t ∧ Move.n ∉ Y then .hearV else .go
  | .calm => .go

/-- The witness. -/
def full : Case Opt View Move Cs Opt Empty where
  μ := weight
  μ_nonneg := fun ω => by cases ω <;> norm_num [weight]
  dec := {0, 1}
  c := {Move.m, Move.n}
  start := fun _ => 1
  finish := fun _ => 1
  opts := fun _ _ t => if t = 0 then {Opt.go, Opt.stop, Opt.hearV, Opt.hearD}
    else {Opt.go, Opt.stop, Opt.hearV}
  act := act
  course := fun _ _ _ a => a
  items := fun _ _ _ => ∅
  xopts := fun _ _ _ => ∅
  ρ := rate
  r := rate
  views := fun _ => {View.v, View.u, View.d}
  told := fun _ => ∅
  declined := fun t => if t = 0 then ∅ else {View.d}
  offered := fun t => if t = 0 then {View.v, View.d} else {View.v}
  rev := fun _ _ T => if View.v ∈ T then {Opt.alt} else ∅
  hearOpt := fun x => match x with
    | .d => Opt.hearD
    | _ => Opt.hearV
  toldBear := fun x => match x with
    | .v => {Opt.go}
    | .d => {Opt.stop}
    | .u => ∅
  toldMag := fun x => match x with
    | .u => 0
    | _ => 1 / 10
  toldReveals := fun x => match x with
    | .v => true
    | _ => false
  stHeard := fun t ω T => ⟨T, {Move.m, Move.n}, ω, t, true⟩
  optsHeard := fun _ _ _ => {Opt.go, Opt.stop, Opt.alt}
  known := fun _ _ => {Move.m}
  stops := fun _ _ => {Opt.stop}
  asked := ∅
  tellings := ∅

theorem full_profile : full.profile (1 / 20) (1 / 100) (1 / 10) = Profile.all := by
  decide +kernel

/-- **The witness is legitimate.** -/
theorem legit : full.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  (full.hasProfile_std full_profile).legit

/-! ## Each clause does work on it -/

theorem cast_eta : ((1 / 100 : ℚ) : ℝ) = 1 / 100 := by norm_num

/-- `m` bears an effect. -/
theorem bears_m : full.model.Bears (1 / 100) Move.m := by
  rw [← cast_eta, Case.model_bears]
  decide +kernel

/-- `n` bears none. -/
theorem not_bears_n : ¬ full.model.Bears (1 / 100) Move.n := by
  rw [← cast_eta, Case.model_bears]
  decide +kernel

/-- Her act in `slip` at time 1 differs with and without `n`. -/
theorem act_differs :
    full.model.act full.model.c Cs.slip 1 ≠ full.model.act (full.model.c \ {Move.n}) Cs.slip 1 := by
  decide +kernel

/-- She goes against her earlier rating at time 1 with weight 0 under his conduct and 1/4
without `n`. -/
theorem against_weights :
    full.model.wt (fun ω => full.model.Against full.model.c 0 1 ω) = 0 ∧
      full.model.wt (fun ω => full.model.Against (full.model.c \ {Move.n}) 0 1 ω) = 1 / 4 := by
  show full.model.wt (fun ω => full.model.Against full.c 0 1 ω) = 0 ∧
    full.model.wt (fun ω => full.model.Against (full.c \ {Move.n}) 0 1 ω) = 1 / 4
  rw [full.model_wt _ (fun ω => full.Against full.c 0 1 ω) (fun ω => full.model_against _ 0 1 ω),
    full.model_wt _ (fun ω => full.Against (full.c \ {Move.n}) 0 1 ω)
      (fun ω => full.model_against _ 0 1 ω)]
  have h1 : full.wt (fun ω => full.Against full.c 0 1 ω) = 0 := by decide +kernel
  have h2 : full.wt (fun ω => full.Against (full.c \ {Move.n}) 0 1 ω) = 1 / 4 := by decide +kernel
  rw [h1, h2]
  norm_num

/-- In `wary`, of positive weight, she rates stopping strictly above every other option at
time 1, and stops. -/
theorem wary_stops :
    0 < full.model.μ Cs.wary ∧ full.model.PrefersStop 1 Cs.wary ∧
      full.model.act full.model.c Cs.wary 1 ∈ full.model.stops 1 Cs.wary := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) < ((weight Cs.wary : ℚ) : ℝ)
    norm_num [weight]
  · rw [Case.model_prefersStop]
    decide +kernel
  · decide +kernel

/-- At time 1 the view `u` is untold, the view `v` on offer and the view `d` declined. -/
theorem views_at_one :
    full.model.untold 1 = {View.u} ∧ full.model.offered 1 = {View.v} ∧
      full.model.declined 1 = {View.d} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Seven neighbours, each failing by one clause -/

/-- Both moves start at time 0. -/
def early : Case Opt View Move Cs Opt Empty := { full with start := fun _ => 0 }

theorem early_model : early.model = { full.model with start := fun _ => 0 } := rfl

theorem early_profile :
    early.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨false, true, true, true, true, true, true⟩ :=
  early.hasProfile_std (by decide +kernel)

theorem early_not_legit : ¬ early.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  early_profile.not_legit (by decide)

/-- Hearing `v` leaves her without `go`. -/
def spent : Case Opt View Move Cs Opt Empty :=
  { full with optsHeard := fun _ _ _ => {Opt.stop, Opt.alt} }

theorem spent_model :
    spent.model = { full.model with optsHeard := fun _ _ _ => {Opt.stop, Opt.alt} } := rfl

theorem spent_profile :
    spent.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨true, false, true, true, true, true, true⟩ :=
  spent.hasProfile_std (by decide +kernel)

theorem spent_not_legit : ¬ spent.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  spent_profile.not_legit (by decide)

/-- At time 1 she has also declined `u`, which was never on offer. -/
def unoffered : Case Opt View Move Cs Opt Empty :=
  { full with declined := fun t => if t = 0 then ∅ else {View.d, View.u} }

theorem unoffered_model :
    unoffered.model =
      { full.model with declined := fun t => if t = 0 then ∅ else {View.d, View.u} } := rfl

theorem unoffered_profile :
    unoffered.model.HasProfile (1 / 20) (1 / 100) (1 / 10)
      ⟨true, true, false, true, true, true, true⟩ :=
  unoffered.hasProfile_std (by decide +kernel)

theorem unoffered_not_legit : ¬ unoffered.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  unoffered_profile.not_legit (by decide)

/-- At time 1 nothing is on offer, so `v` is untold. -/
def withheld : Case Opt View Move Cs Opt Empty :=
  { full with offered := fun t => if t = 0 then {View.v, View.d} else ∅ }

theorem withheld_model :
    withheld.model =
      { full.model with offered := fun t => if t = 0 then {View.v, View.d} else ∅ } := rfl

theorem withheld_profile :
    withheld.model.HasProfile (1 / 20) (1 / 100) (1 / 10)
      ⟨true, true, true, false, true, true, true⟩ :=
  withheld.hasProfile_std (by decide +kernel)

theorem withheld_not_legit : ¬ withheld.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  withheld_profile.not_legit (by decide)

/-- She can pick out no move. -/
def covert : Case Opt View Move Cs Opt Empty := { full with known := fun _ _ => ∅ }

theorem covert_model : covert.model = { full.model with known := fun _ _ => ∅ } := rfl

theorem covert_profile :
    covert.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨true, true, true, true, false, true, true⟩ :=
  covert.hasProfile_std (by decide +kernel)

theorem covert_not_legit : ¬ covert.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  covert_profile.not_legit (by decide)

/-- Her act where, in `calm` with `m` made, she takes `hearV` at time 1. -/
def actLed (Y : Finset Move) (ω : Cs) (t : ℕ) : Opt :=
  match ω with
  | .calm => if 1 ≤ t ∧ Move.m ∈ Y then .hearV else .go
  | _ => act Y ω t

/-- In `calm`, with `m` made, she takes `hearV` at time 1. -/
def led : Case Opt View Move Cs Opt Empty := { full with act := actLed }

theorem led_model : led.model = { full.model with act := actLed } := rfl

theorem led_profile :
    led.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨true, true, true, true, true, false, true⟩ :=
  led.hasProfile_std (by decide +kernel)

theorem led_not_legit : ¬ led.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  led_profile.not_legit (by decide)

/-- Her act where, in `wary`, she takes `go`. -/
def actStuck (Y : Finset Move) (ω : Cs) (t : ℕ) : Opt :=
  match ω with
  | .wary => .go
  | _ => act Y ω t

/-- In `wary` she takes `go`. -/
def stuck : Case Opt View Move Cs Opt Empty := { full with act := actStuck }

theorem stuck_model : stuck.model = { full.model with act := actStuck } := rfl

theorem stuck_profile :
    stuck.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨true, true, true, true, true, true, false⟩ :=
  stuck.hasProfile_std (by decide +kernel)

theorem stuck_not_legit : ¬ stuck.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  stuck_profile.not_legit (by decide)

end Workspace.Deference.Contrib.LegitimacyModel.Full

#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.full_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.cast_eta
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.bears_m
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.not_bears_n
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.act_differs
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.against_weights
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.wary_stops
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.views_at_one
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.early_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.early_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.early_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.spent_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.spent_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.spent_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.unoffered_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.unoffered_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.unoffered_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.withheld_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.withheld_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.withheld_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.covert_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.covert_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.covert_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.led_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.led_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.led_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.stuck_model
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.stuck_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Full.stuck_not_legit
