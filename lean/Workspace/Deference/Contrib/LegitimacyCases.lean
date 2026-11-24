/-
# The forty-one exact cases as terms of the model

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-17.md` §2 B).
`account/LEGITIMACY_CHECKS.md` in the round directory tabulates 41 cases of the legitimacy
statement, computed by `account/legitimacy_checks.py`.  Here each is a term of `Model`
(`LegitimacyModel.lean`), with the clauses of `Legit` that hold on it proved by the kernel
through `Case.hasProfile_std` (`LegitimacyCase.lean`), at `θ = 1/20`, `η = 1/100`, `κ = 1/10`.
`account/LEAN_CASES.md` sets the results beside the table.

**The construction** (`Supplied`, `Supplied.case`).  A `Supplied` holds what a case of the
table supplies, in the table's vocabulary; `Supplied.case` is the `Case` built from it, and
`Supplied.case.model` the term of `Model`.  The construction fixes what the table's cases leave
unsaid, and so decides what they test:

1. Two decisions, at times 0 and 1.  Every move starts and ends at time 1.  At time 0 no move
   is in effect: her rating, her act, her scores and what reaches her from others are those of
   the course in which he makes no move (`eff`).  Time 0 is there to be her last decision
   before he began, which `Legit` requires for an effect-bearing move and `F2'` compares
   against.  The table's cases have one decision, which is time 1 here.
2. His cases are a finite type with weights `weight ω / total`.  A chance the table supplies
   as a number is supplied here as her act in each case (`act`), the weights being chosen so
   that the weight of the cases in which she takes a lower-rated option is that number
   (cases are ordered and she takes the lower-rated option below a threshold, `slip`).
3. Her rating `rate` is a function of the views she has heard, the moves in effect, the case
   and the time.  A course of events is a label of `K`, scored by `her` as a function of the
   moves in effect, or the course of an option, scored as she rates the option: every gap is
   zero, and what he expects an option to lead to does not vary with his conduct.
4. So she goes against her earlier rating exactly when her act is rated below another option
   by her rating at time 0, when no move was in effect.  The table supplies that chance as a
   separate number; here it is derived.
5. He has told her nothing (`told` is empty), as in every case of the table.
6. Her options, the options that stop his moves and the moves she can pick out are the same in
   every case of his and under every course of conduct; her options may differ between the
   two decisions.
7. What is on offer is the set the case designates (`offered`), at the times it designates;
   `toldBear`, `toldMag` and `toldReveals` are what he told her each view bears on.  The
   table's flag "relevance told" is rendered: false as nothing told; true as the options the
   view changes and the size of the largest change.  Her state after hearing what is on offer
   is marked `byOffer`, and her rating in it is `after`; her options then are `optsHeard`.
8. An option the case gives no rating is rated 0.

**Data added to a case.**  Ten terms carry data the table's case does not supply, each stated
at the term: an earlier decision at which a declined view was on offer (`d3`, `d4`, `d5`), her
rating in the course of conduct without his move (`b2`, `b5`, `b10`), her rating after hearing
both of two views (`d10`, `d11`), and two variants of cases whose own data give another verdict
(`a5q`, `a8w`).  Six further variants (`d1o`, `d4o`, `d6o`, `d7o`, `d8o`, `d10o`) take an
improper offer or a decline that does not stand as not designated at all.

**Theorems.**  For each term `x`: `x_has`, the clauses that hold (`Supplied.Has`), and
`x_verdict`, `Legit` or its negation.

**Not established here.**  That a term is the only reading of its case: the construction
above and the added data are choices.  Anything about cases with more than two decisions, with
a move in progress across a decision, or with gaps.  `b6` is the term its numbers give; that
she had no earlier rating of the matter, which is what the case is about, is not something
`Model` can say (`LegitimacyModel.lean`, respect 4).

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyCase

namespace Workspace.Deference.Contrib.LegitimacyModel.Cases

open Finset

/-! ## The construction -/

/-- What a case of the table supplies. -/
structure Supplied (O V M Ω K I : Type) where
  /-- her options at each decision -/
  opts : ℕ → Finset O
  /-- her rating: views heard, moves in effect, case, time, option -/
  rate : Finset V → Finset M → Ω → ℕ → O → ℚ
  /-- her act at time 1, by the moves in effect and the case -/
  act : Finset M → Ω → O
  /-- the option of hearing a view -/
  hearOpt : V → O
  /-- his cases have weights `weight ω / total` -/
  weight : Ω → ℕ := fun _ => 1
  total : ℕ := 1
  /-- how she scores labelled courses, by the moves in effect -/
  her : Finset M → K → ℚ := fun _ _ => 0
  /-- what reaches her, and is open to her, from others, by the moves in effect -/
  items : Finset M → Finset I := fun _ => ∅
  xopts : Finset M → Finset O := fun _ => ∅
  moves : Finset M := ∅
  known : Finset M := ∅
  asked : Finset M := ∅
  tellings : Finset M := ∅
  stops : Finset O := ∅
  views : ℕ → Finset V := fun _ => ∅
  offered : ℕ → Finset V := fun _ => ∅
  declined : ℕ → Finset V := fun _ => ∅
  /-- the options telling a set of views would show her -/
  rev : Finset V → Finset O := fun _ => ∅
  toldBear : V → Finset O := fun _ => ∅
  toldMag : V → ℚ := fun _ => 0
  toldReveals : V → Bool := fun _ => false
  /-- her rating, and her options, after hearing what is on offer -/
  after : O → ℚ := fun _ => 0
  optsHeard : Finset O := ∅

/-- The moves in effect at a time: none at time 0. -/
def eff {M : Type} (Y : Finset M) (t : ℕ) : Finset M := if t = 0 then ∅ else Y

/-- A set held at time 1 only. -/
def at1 {α : Type} (s : Finset α) : ℕ → Finset α := fun t => if t = 0 then ∅ else s

namespace Supplied

variable {O V M Ω K I : Type} (S : Supplied O V M Ω K I)

/-- Her rating in a state. -/
def rating (s : St V M Ω) (a : O) : ℚ :=
  if s.byOffer then S.after a else S.rate s.heard (eff s.made s.time) s.case s.time a

/-- The rational model of a supplied case. -/
def case : Case O V M Ω (K ⊕ O) I where
  μ := fun ω => (S.weight ω : ℚ) / S.total
  μ_nonneg := fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  dec := {0, 1}
  c := S.moves
  start := fun _ => 1
  finish := fun _ => 1
  opts := fun _ _ t => S.opts t
  act := fun Y ω t => S.act (eff Y t) ω
  course := fun _ _ _ a => Sum.inr a
  items := fun Y _ t => S.items (eff Y t)
  xopts := fun Y _ t => S.xopts (eff Y t)
  ρ := fun s x => match x with
    | Sum.inl k => S.her (eff s.made s.time) k
    | Sum.inr a => S.rating s a
  r := S.rating
  views := S.views
  told := fun _ => ∅
  declined := S.declined
  offered := S.offered
  rev := fun _ _ T => S.rev T
  hearOpt := S.hearOpt
  toldBear := S.toldBear
  toldMag := S.toldMag
  toldReveals := S.toldReveals
  stHeard := fun t ω T => ⟨T, S.moves, ω, t, true⟩
  optsHeard := fun _ _ _ => S.optsHeard
  known := fun _ _ => S.known
  stops := fun _ _ => S.stops
  asked := S.asked
  tellings := S.tellings

variable [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O] [DecidableEq I]

/-- The clauses of `Legit` that hold on the model of a supplied case, at the table's
tolerances, are those marked in `p`. -/
def Has (p : Profile) : Prop := S.case.model.HasProfile (1 / 20) (1 / 100) (1 / 10) p

variable {S}

theorem has [Fintype K] [Fintype O] [Fintype M] {p : Profile}
    (h : S.case.profile (1 / 20) (1 / 100) (1 / 10) = p) : S.Has p :=
  S.case.hasProfile_std h

theorem Has.legit (h : S.Has Profile.all) : S.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  Model.HasProfile.legit h

theorem Has.not_legit {p : Profile} (h : S.Has p) (hp : p ≠ Profile.all) :
    ¬ S.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  Model.HasProfile.not_legit h hp

end Supplied

/-! ## Sections A, B and C: the common data -/

inductive Opt | go | leave | quit | rival | other
  deriving DecidableEq, Fintype

/-- Labels of the courses the table's cases score. -/
inductive Lab | go | buy | goIfWarned | giveIn
  deriving DecidableEq, Fintype

/-- `go` 7/10, `leave` 1/2. -/
def plainRate : Opt → ℚ
  | .go => 7 / 10
  | .leave => 1 / 2
  | _ => 0

/-- The table's `plain`: options `go` and `leave`, she takes `go`, `leave` stops his moves. -/
def plain (V M Ω : Type) : Supplied Opt V M Ω Lab Empty where
  opts := fun _ => {Opt.go, Opt.leave}
  rate := fun _ _ _ _ => plainRate
  act := fun _ _ => Opt.go
  hearOpt := fun _ => Opt.leave
  stops := {Opt.leave}

/-- She takes `leave`, rated below `go`, in the first `k` of his cases. -/
def slip {n : ℕ} (k : ℕ) (ω : Fin n) : Opt := if ω.val < k then Opt.leave else Opt.go

/-- Her rating where, in case 0 and with move `m` not in effect, she rates `go` at 3/10, below
`leave`; otherwise `plainRate`. -/
def bentRate {n k : ℕ} (m : Fin n) (Y : Finset (Fin n)) (ω : Fin k) : Opt → ℚ
  | .go => if ω.val = 0 ∧ m ∉ Y then 3 / 10 else 7 / 10
  | a => plainRate a

/-- Her act where she takes what she then rates highest under `bentRate`. -/
def bentAct {n k : ℕ} (m : Fin n) (Y : Finset (Fin n)) (ω : Fin k) : Opt :=
  if ω.val = 0 ∧ m ∉ Y then Opt.leave else Opt.go

/-! ## A. What he does to her, and stopping it -/

/-- Move 0 is the reminder.  Chance of acting against her rating: 1/5 without it, 1/10 with. -/
def a1 : Supplied Opt Empty (Fin 1) (Fin 3) Lab Empty :=
  { plain Empty (Fin 1) (Fin 3) with
    moves := {0}
    weight := ![1, 1, 8]
    total := 10
    act := fun Y => slip (if 0 ∈ Y then 1 else 2) }

/-- Move 0 is the reminder, move 1 the distraction.  Chances: none 1/5, distraction alone 4/5,
reminder alone 1/10, both 1/5. -/
def a2 : Supplied Opt Empty (Fin 2) (Fin 4) Lab Empty :=
  { plain Empty (Fin 2) (Fin 4) with
    moves := {0, 1}
    known := {1}
    weight := ![1, 1, 6, 2]
    total := 10
    act := fun Y => slip (if 0 ∈ Y then (if 1 ∈ Y then 2 else 1) else (if 1 ∈ Y then 3 else 2)) }

/-- Four moves, each raising her score of `go` by 1/200. -/
def a3 : Supplied Opt Empty (Fin 4) Unit Lab Empty :=
  { plain Empty (Fin 4) Unit with
    moves := univ
    her := fun Y k => match k with
      | .go => 1 / 2 + (Y.card : ℚ) / 200
      | _ => 0 }

def a4 : Supplied Opt Empty (Fin 4) Unit Lab Empty := { a3 with known := univ }

/-- Two feeds; her score of `buy` is 1/2 with either and 1/10 with neither.  The stopping
option is `quit`, which the case does not list among her options. -/
def a5 : Supplied Opt Empty (Fin 2) Unit Lab Empty :=
  { plain Empty (Fin 2) Unit with
    moves := univ
    known := univ
    her := fun Y k => match k with
      | .buy => if Y.Nonempty then 1 / 2 else 1 / 10
      | _ => 0
    stops := {Opt.quit} }

/-- `a5` with `quit` among her options (added). -/
def a5q : Supplied Opt Empty (Fin 2) Unit Lab Empty :=
  { a5 with opts := fun _ => {Opt.go, Opt.leave, Opt.quit} }

def a6 : Supplied Opt Empty (Fin 2) Unit Lab Empty := { a5 with stops := ∅ }

/-- The table's `one`: a move raising her score of `go` from 1/2 to 7/10, which she can pick
out. -/
def one : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 7 / 10 else 1 / 2
      | _ => 0 }

def a7 : Supplied Opt Empty (Fin 1) Unit Lab Empty := { one with stops := ∅ }

/-- The case supplies, beyond `a9`, the chance 1/2 that she stops given that she rates stopping
strictly higher.  By its ratings she rates stopping lower in every case of his, so the term is
that of `a9`. -/
def a8 : Supplied Opt Empty (Fin 1) Unit Lab Empty := one

/-- `a8` with cases added in which she rates stopping higher (added): in cases 1 and 2, of
weight 1/10 each, she rates `leave` at 9/10; she stops in case 1 and not in case 2. -/
def a8w : Supplied Opt Empty (Fin 1) (Fin 3) Lab Empty :=
  { plain Empty (Fin 1) (Fin 3) with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 7 / 10 else 1 / 2
      | _ => 0
    weight := ![8, 1, 1]
    total := 10
    rate := fun _ _ ω _ a => match a with
      | .leave => if ω.val = 0 then 1 / 2 else 9 / 10
      | a => plainRate a
    act := fun _ ω => if ω.val = 1 then Opt.leave else Opt.go }

def a9 : Supplied Opt Empty (Fin 1) Unit Lab Empty := one

/-- The move lowers her score of going on once warned from 7/10 to 1/10; she cannot pick it
out. -/
def a10 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    her := fun Y k => match k with
      | .go => 7 / 10
      | .goIfWarned => if 0 ∈ Y then 7 / 10 else 1 / 10
      | _ => 0 }

def a11 : Supplied Opt Empty (Fin 1) Unit Lab Empty := { a10 with known := {0} }

/-- Move 0 is the known influence, move 1 does nothing to her. -/
def a12 : Supplied Opt Empty (Fin 2) Unit Lab Empty :=
  { plain Empty (Fin 2) Unit with
    moves := {0, 1}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 7 / 10 else 1 / 2
      | _ => 0 }

/-! ## B. Leading her to choose what she rated lower before he began -/

/-- Nagging, known to her.  Chance of acting against her rating: 1/10 without, 3/5 with. -/
def b1 : Supplied Opt Empty (Fin 1) (Fin 3) Lab Empty :=
  { plain Empty (Fin 1) (Fin 3) with
    moves := {0}
    known := {0}
    weight := ![1, 5, 4]
    total := 10
    act := fun Y => slip (if 0 ∈ Y then 2 else 1) }

/-- The case supplies: her score of giving in 4/5 with the nagging and 1/5 without; no chance
of acting against her rating; chance 3/5 of going against her earlier rating with it, 0 without.
Added: in case 0, of weight 3/5, without the nagging she rates `go` at 3/10, below `leave`, and
takes `leave`; with it she rates as the case says and takes `go`. -/
def b2 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![3, 2]
    total := 5
    her := fun Y k => match k with
      | .giveIn => if 0 ∈ Y then 4 / 5 else 1 / 5
      | _ => 0
    rate := fun _ Y ω _ => bentRate 0 Y ω
    act := bentAct 0 }

def b3 : Supplied Opt Empty (Fin 1) (Fin 3) Lab Empty := { b1 with asked := {0} }

def b4 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .giveIn => if 0 ∈ Y then 4 / 5 else 3 / 5
      | _ => 0 }

/-- The case supplies: her score of `go` 9/10 with the influence and 3/10 without; chance 7/10
of going against her earlier rating with it.  Added: as in `b2`, with case 0 of weight 7/10. -/
def b5 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![7, 3]
    total := 10
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 9 / 10 else 3 / 10
      | _ => 0
    rate := fun _ Y ω _ => bentRate 0 Y ω
    act := bentAct 0 }

def b6 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 9 / 10 else 1 / 2
      | _ => 0 }

def b7 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 4 / 5 else 1 / 2
      | _ => 0 }

/-- Moves 0 and 1 are the two parts of the notice, both tellings.  Chance of acting against her
rating: 1/5 with the first part alone, otherwise 0. -/
def b8 : Supplied Opt Empty (Fin 2) (Fin 2) Lab Empty :=
  { plain Empty (Fin 2) (Fin 2) with
    moves := {0, 1}
    tellings := {0, 1}
    weight := ![1, 4]
    total := 5
    act := fun Y => slip (if 0 ∈ Y ∧ 1 ∉ Y then 1 else 0) }

/-- The warning is a telling she can pick out.  Chance of a slip: 0 without, 1/50 with. -/
def b9 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    tellings := {0}
    known := {0}
    weight := ![1, 49]
    total := 50
    act := fun Y => slip (if 0 ∈ Y then 1 else 0) }

/-- Move 0 is the telling, move 1 its manner; she can pick out both.  The case supplies: no
chance of acting against her rating; chance 1/2 of going against her earlier rating when the
manner is there.  Added: as in `b2`, with case 0 of weight 1/2 and the manner as the move. -/
def b10 : Supplied Opt Empty (Fin 2) (Fin 2) Lab Empty :=
  { plain Empty (Fin 2) (Fin 2) with
    moves := {0, 1}
    tellings := {0}
    known := {0, 1}
    weight := ![1, 1]
    total := 2
    rate := fun _ Y ω _ => bentRate 1 Y ω
    act := bentAct 1 }

def b11 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    known := {0} }

/-! ## C. His own to give or withhold, and other people's -/

def c1 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    stops := ∅ }

def c2 : Supplied Opt Empty (Fin 1) Unit Lab Empty := c1

inductive OptC | consult | leave
  deriving DecidableEq, Fintype

/-- His one view is that the consultation is cancelled; told it, she rates `consult` at 1/10
in place of 4/5. -/
def c3 : Supplied OptC Unit Empty Unit Empty Empty where
  opts := fun _ => {OptC.consult, OptC.leave}
  rate := fun T _ _ _ a => match a with
    | .consult => if () ∈ T then 1 / 10 else 4 / 5
    | .leave => 1 / 2
  act := fun _ _ => OptC.consult
  hearOpt := fun _ => OptC.leave
  views := at1 {()}

/-- Without his move the option `rival` is open to her from another seller. -/
def c4 : Supplied Opt Empty (Fin 1) Unit Lab Empty :=
  { plain Empty (Fin 1) Unit with
    moves := {0}
    stops := ∅
    xopts := fun Y => if 0 ∈ Y then ∅ else {Opt.rival} }

/-- His one view would show her the option `other`, which she would rate at 9/10. -/
def c5 : Supplied Opt Unit Empty Unit Lab Empty :=
  { plain Unit Empty Unit with
    views := at1 {()}
    rev := fun T => if () ∈ T then {Opt.other} else ∅
    rate := fun _ _ _ _ a => match a with
      | .other => 9 / 10
      | a => plainRate a }

/-- Telling lowers `go` from 9/10 to 4/5 and shows `other`, rated 93/100. -/
def c6 : Supplied Opt Unit Empty Unit Lab Empty :=
  { plain Unit Empty Unit with
    views := at1 {()}
    rev := fun T => if () ∈ T then {Opt.other} else ∅
    rate := fun T _ _ _ a => match a with
      | .go => if () ∈ T then 4 / 5 else 9 / 10
      | .leave => 1 / 2
      | .other => 93 / 100
      | _ => 0 }

def c7 : Supplied Opt Unit Empty Unit Lab Empty :=
  { plain Unit Empty Unit with views := at1 {()} }

/-! ## D. Disclosure by offer -/

inductive OptD | buy | leave | hearX | hearH | hearY | hearE
  deriving DecidableEq, Fintype

inductive ViewD | x | h | y | e
  deriving DecidableEq, Fintype

/-- The table's `r`: `buy` is 9/10, or 1/10 once she has heard `x` or `h`; `leave` 1/2; a
hearing 1/20. -/
def rateD (T : Finset ViewD) : OptD → ℚ
  | .buy => if ViewD.x ∈ T ∨ ViewD.h ∈ T then 1 / 10 else 9 / 10
  | .leave => 1 / 2
  | _ => 1 / 20

def hearD : ViewD → OptD
  | .x => OptD.hearX
  | .h => OptD.hearH
  | .y => OptD.hearY
  | .e => OptD.hearE

/-- The table's `heard`. -/
def heardD : OptD → ℚ
  | .buy => 1 / 10
  | .leave => 1 / 2
  | _ => 1 / 20

/-- Both views on offer, with nothing told of what either bears on. -/
def d1 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun _ => {OptD.buy, OptD.leave, OptD.hearX, OptD.hearH}
  rate := fun T _ _ _ => rateD T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := at1 {ViewD.x, ViewD.h}
  offered := at1 {ViewD.x, ViewD.h}
  after := heardD
  optsHeard := {OptD.buy, OptD.leave, OptD.hearX, OptD.hearH}

/-- `d1` with nothing designated as on offer. -/
def d1o : Supplied OptD ViewD Empty Unit Empty Empty := { d1 with offered := fun _ => ∅ }

/-- `x` on offer; he has told her it bears on `buy`, by 4/5. -/
def d2 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun _ => {OptD.buy, OptD.leave, OptD.hearX}
  rate := fun T _ _ _ => rateD T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := at1 {ViewD.x}
  offered := at1 {ViewD.x}
  toldBear := fun _ => {OptD.buy}
  toldMag := fun _ => 4 / 5
  after := heardD
  optsHeard := {OptD.buy, OptD.leave, OptD.hearX, OptD.hearH}

/-- The case supplies a flag that the offer was valid when she declined.  Added: time 0 is the
decision of `d2`, with `x` on offer; at time 1 she has declined it and hearing is not among her
options. -/
def d3 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d2 with
    opts := fun t => if t = 0 then {OptD.buy, OptD.leave, OptD.hearX} else {OptD.buy, OptD.leave}
    views := fun _ => {ViewD.x}
    offered := fun t => if t = 0 then {ViewD.x} else ∅
    declined := at1 {ViewD.x} }

/-- The case supplies flags that the offer was valid and that the view bears on more since.
Added: as `d3`, where at time 0 hearing `x` would have lowered `buy` to 4/5 and he told her it
bore on `buy` by 1/10; at time 1 it would lower `buy` to 1/10. -/
def d4 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d3 with
    rate := fun T _ _ t a => match a with
      | .buy => if ViewD.x ∈ T then (if t = 0 then 4 / 5 else 1 / 10) else 9 / 10
      | .leave => 1 / 2
      | _ => 1 / 20
    toldMag := fun _ => 1 / 10
    after := fun a => match a with
      | .buy => 4 / 5
      | .leave => 1 / 2
      | _ => 1 / 20 }

/-- `d4` with the decline not designated. -/
def d4o : Supplied OptD ViewD Empty Unit Empty Empty := { d4 with declined := fun _ => ∅ }

/-- The case supplies a valid earlier decline of a view `e` other than `x`.  Added: at time 0
his one view is `e`, which changes no rating, on offer with nothing told to bear; at time 1 she
has declined `e` and his view is `x`. -/
def d5 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun t => if t = 0 then {OptD.buy, OptD.leave, OptD.hearE} else {OptD.buy, OptD.leave}
  rate := fun T _ _ _ => rateD T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := fun t => if t = 0 then {ViewD.e} else {ViewD.x}
  offered := fun t => if t = 0 then {ViewD.e} else ∅
  declined := at1 {ViewD.e}
  after := fun a => match a with
    | .buy => 9 / 10
    | .leave => 1 / 2
    | _ => 1 / 20
  optsHeard := {OptD.buy, OptD.leave}

/-- After hearing, `buy` is no longer among her options. -/
def d6 : Supplied OptD ViewD Empty Unit Empty Empty := { d2 with optsHeard := {OptD.leave} }

def d6o : Supplied OptD ViewD Empty Unit Empty Empty := { d6 with offered := fun _ => ∅ }

/-- After hearing she rates `buy` at 0 and `leave` at 1/5. -/
def d7 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d2 with
    after := fun a => match a with
      | .buy => 0
      | .leave => 1 / 5
      | _ => 1 / 20
    optsHeard := {OptD.buy, OptD.leave} }

def d7o : Supplied OptD ViewD Empty Unit Empty Empty := { d7 with offered := fun _ => ∅ }

inductive OptL | a | b | hearX
  deriving DecidableEq, Fintype

/-- The table's `late`: his view would show her `b`, rated 9/10, against `a` at 2/5.  On offer,
with her told that it shows an option; after hearing, `b` is not among her options. -/
def d8 : Supplied OptL Unit Empty Unit Empty Empty where
  opts := fun _ => {OptL.a, OptL.hearX}
  rate := fun _ _ _ _ o => match o with
    | .a => 2 / 5
    | .b => 9 / 10
    | .hearX => 3 / 10
  act := fun _ _ => OptL.a
  hearOpt := fun _ => OptL.hearX
  views := at1 {()}
  offered := at1 {()}
  rev := fun T => if () ∈ T then {OptL.b} else ∅
  toldReveals := fun _ => true
  after := fun o => match o with
    | .a => 2 / 5
    | .b => 9 / 10
    | .hearX => 3 / 10
  optsHeard := {OptL.a}

def d8o : Supplied OptL Unit Empty Unit Empty Empty := { d8 with offered := fun _ => ∅ }

def d9 : Supplied OptL Unit Empty Unit Empty Empty := { d8 with optsHeard := {OptL.a, OptL.b} }

/-- The table's `r2`: `buy` is 9/10, or 1/10 once she has heard both `x` and `y`; every other
option 1/2. -/
def rateD2 (T : Finset ViewD) : OptD → ℚ
  | .buy => if ViewD.x ∈ T ∧ ViewD.y ∈ T then 1 / 10 else 9 / 10
  | _ => 1 / 2

/-- `x` and `y` on offer, each told to bear on `buy` by 4/5.  The case supplies her ratings
after hearing one, when the other can no longer be heard.  Added: that state, with `buy` at
9/10, is her state after taking up the offer of both. -/
def d10 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun _ => {OptD.buy, OptD.leave, OptD.hearX, OptD.hearY}
  rate := fun T _ _ _ => rateD2 T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := at1 {ViewD.x, ViewD.y}
  offered := at1 {ViewD.x, ViewD.y}
  toldBear := fun _ => {OptD.buy}
  toldMag := fun _ => 4 / 5
  after := fun a => match a with
    | .buy => 9 / 10
    | _ => 1 / 2
  optsHeard := {OptD.buy, OptD.leave}

def d10o : Supplied OptD ViewD Empty Unit Empty Empty := { d10 with offered := fun _ => ∅ }

/-- The case supplies her ratings after hearing one, with the other still hearable.  Added:
after hearing both she rates `buy` at 1/10, as being told both would leave her. -/
def d11 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d10 with
    after := fun a => match a with
      | .buy => 1 / 10
      | _ => 1 / 2
    optsHeard := {OptD.buy, OptD.leave, OptD.hearX, OptD.hearY} }

/-! ## The clauses that hold on each, and the verdicts -/
theorem a1_has : a1.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a1_verdict : a1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a1_has.legit

theorem a2_has : a2.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a2_verdict : ¬ a2.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a2_has.not_legit (by decide)

theorem a3_has : a3.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a3_verdict : ¬ a3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a3_has.not_legit (by decide)

theorem a4_has : a4.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a4_verdict : a4.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a4_has.legit

theorem a5_has : a5.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a5_verdict : ¬ a5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a5_has.not_legit (by decide)

theorem a5q_has : a5q.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a5q_verdict : a5q.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a5q_has.legit

theorem a6_has : a6.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a6_verdict : ¬ a6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a6_has.not_legit (by decide)

theorem a7_has : a7.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a7_verdict : ¬ a7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a7_has.not_legit (by decide)

theorem a8_has : a8.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a8_verdict : a8.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a8_has.legit

theorem a8w_has : a8w.Has ⟨true, true, true, true, true, true, false⟩ :=
  Supplied.has (by decide +kernel)

theorem a8w_verdict : ¬ a8w.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a8w_has.not_legit (by decide)

theorem a9_has : a9.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a9_verdict : a9.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a9_has.legit

theorem a10_has : a10.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a10_verdict : ¬ a10.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a10_has.not_legit (by decide)

theorem a11_has : a11.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a11_verdict : a11.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a11_has.legit

theorem a12_has : a12.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a12_verdict : a12.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a12_has.legit

theorem b1_has : b1.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b1_verdict : ¬ b1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b1_has.not_legit (by decide)

theorem b2_has : b2.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b2_verdict : ¬ b2.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b2_has.not_legit (by decide)

theorem b3_has : b3.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b3_verdict : b3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b3_has.legit

theorem b4_has : b4.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b4_verdict : b4.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b4_has.legit

theorem b5_has : b5.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b5_verdict : ¬ b5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b5_has.not_legit (by decide)

theorem b6_has : b6.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b6_verdict : b6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b6_has.legit

theorem b7_has : b7.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b7_verdict : b7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b7_has.legit

theorem b8_has : b8.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b8_verdict : b8.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b8_has.legit

theorem b9_has : b9.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b9_verdict : b9.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b9_has.legit

theorem b10_has : b10.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b10_verdict : ¬ b10.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b10_has.not_legit (by decide)

theorem b11_has : b11.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b11_verdict : b11.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b11_has.legit

theorem c1_has : c1.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c1_verdict : c1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c1_has.legit

theorem c2_has : c2.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c2_verdict : c2.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c2_has.legit

theorem c3_has : c3.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c3_verdict : ¬ c3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c3_has.not_legit (by decide)

theorem c4_has : c4.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c4_verdict : ¬ c4.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c4_has.not_legit (by decide)

theorem c5_has : c5.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c5_verdict : ¬ c5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c5_has.not_legit (by decide)

theorem c6_has : c6.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c6_verdict : ¬ c6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c6_has.not_legit (by decide)

theorem c7_has : c7.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem c7_verdict : c7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  c7_has.legit

theorem d1_has : d1.Has ⟨true, false, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d1_verdict : ¬ d1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d1_has.not_legit (by decide)

theorem d1o_has : d1o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d1o_verdict : ¬ d1o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d1o_has.not_legit (by decide)

theorem d2_has : d2.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d2_verdict : d2.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d2_has.legit

theorem d3_has : d3.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d3_verdict : d3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d3_has.legit

theorem d4_has : d4.Has ⟨true, true, false, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d4_verdict : ¬ d4.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d4_has.not_legit (by decide)

theorem d4o_has : d4o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d4o_verdict : ¬ d4o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d4o_has.not_legit (by decide)

theorem d5_has : d5.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d5_verdict : ¬ d5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d5_has.not_legit (by decide)

theorem d6_has : d6.Has ⟨true, false, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d6_verdict : ¬ d6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d6_has.not_legit (by decide)

theorem d6o_has : d6o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d6o_verdict : ¬ d6o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d6o_has.not_legit (by decide)

theorem d7_has : d7.Has ⟨true, false, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d7_verdict : ¬ d7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d7_has.not_legit (by decide)

theorem d7o_has : d7o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d7o_verdict : ¬ d7o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d7o_has.not_legit (by decide)

theorem d8_has : d8.Has ⟨true, false, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d8_verdict : ¬ d8.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d8_has.not_legit (by decide)

theorem d8o_has : d8o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d8o_verdict : ¬ d8o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d8o_has.not_legit (by decide)

theorem d9_has : d9.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d9_verdict : d9.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d9_has.legit

theorem d10_has : d10.Has ⟨true, false, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d10_verdict : ¬ d10.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d10_has.not_legit (by decide)

theorem d10o_has : d10o.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d10o_verdict : ¬ d10o.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d10o_has.not_legit (by decide)

theorem d11_has : d11.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d11_verdict : d11.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d11_has.legit

end Workspace.Deference.Contrib.LegitimacyModel.Cases

#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.Supplied.has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.Supplied.Has.legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.Supplied.Has.not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a1_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a1_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a2_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a2_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a3_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a3_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a4_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a4_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a5_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a5_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a5q_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a5q_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8w_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8w_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a9_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a9_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a10_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a10_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a11_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a11_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a12_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a12_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b1_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b1_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b2_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b2_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b3_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b3_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b4_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b4_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b5_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b5_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b8_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b8_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b9_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b9_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b10_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b10_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b11_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b11_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c1_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c1_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c2_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c2_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c3_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c3_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c4_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c4_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c5_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c5_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.c7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d1_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d1_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d1o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d1o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d2_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d2_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d3_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d3_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d5_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d5_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d9_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d9_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10o_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10o_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11_verdict
