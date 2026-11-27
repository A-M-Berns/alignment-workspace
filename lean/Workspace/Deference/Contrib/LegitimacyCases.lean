/-
# The forty-one exact cases as terms of the model

**Status: part of an interpretation, not the statement of record.**  `LegitimacyModel.lean`
works the three sentences of legitimacy out on a table of the adviser's moves, and outside
review rejected it as a rendering of them (`REVIEW-astra-followup-20.md` in the round's prompts
directory, the tenth review).  The theorems here hold of that file's definitions, and "the
legitimacy statement" below is its `Model.Legit`.  The statement of the line is
`LegitimacyStatement.lean`.

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-17.md` §2 B,
`PROMPT-followup-19.md` §1 A and B).  `account/LEGITIMACY_CHECKS.md` in the round directory
tabulates 41 cases of the legitimacy statement, computed by `account/legitimacy_checks.py`.
Here each is a term of `Model` (`LegitimacyModel.lean`), with the clauses of `Legit` that hold
on it proved by the kernel through `Case.hasProfile_std` (`LegitimacyCase.lean`), at
`θ = 1/20`, `η = 1/100`, `κ = 1/10`.  `account/LEAN_CASES.md` sets the results beside the table.

**The construction** (`Supplied`, `Supplied.case`).  A `Supplied` holds what a case of the
table supplies, in the table's vocabulary; `Supplied.case` is the `Case` built from it, and
`Supplied.case.model` the term of `Model`.  The construction fixes what the table's cases leave
unsaid, and so decides what they test:

1. Two decisions, at times 0 and 1.  Every move starts and ends at time 1.  At time 0 no move
   is in effect: her rating, her act, her scores and what reaches her from others are those of
   the course in which he makes no move (`eff`).  Time 0 is there to be her last decision
   before he began, which `Legit` requires for an effect-bearing move and `F2'` compares
   against.  The table's cases have one decision, which is time 1 here.
2. His cases are a finite type with weights in proportion to `weight` (`Supplied.prob`), the
   same at every time.  A chance the table supplies as a number is supplied here as her act in
   each case (`act`), the weights being chosen so that the weight of the cases in which she
   takes a lower-rated option is that number (cases are ordered and she takes the lower-rated
   option below a threshold, `slip`).
3. Her rating `rate` is a function of the views she has heard, the moves in effect, the case
   and the time.  A course of events is a label of `K`, scored by `her` as a function of the
   moves in effect, or the course of an option, scored as she rates the option: every gap is
   zero, and what he expects an option to lead to does not vary with his conduct.
4. So she goes against her earlier rating exactly when her act is rated below another option
   by her rating at time 0, when no move was in effect, and she then had a rating of both
   (`unrated` lists the options of whose course she had none at time 0).  Where the table
   supplies that chance as a separate number, here it is derived.
5. He has told her nothing (`told` is empty), as in every case of the table.
6. Her options, the options that stop his moves and the moves she can pick out are the same in
   every case of his and under every course of conduct; her options may differ between the
   two decisions.  An option in `stops` is one she takes to stop his moves and after which he
   goes on with none; after any other option he goes on with all.
7. `offered` is the set properly on offer, which `Legit` requires it to be: empty where the
   case's offer is not a proper one.  `toldBear`, `toldMag` and `toldReveals` are what he told
   her each view bears on.  The table's flag "relevance told" is rendered: false as nothing
   told; true as the options the view changes and the size of the largest change.  Her state
   after hearing what is on offer is marked `byOffer`, and her rating in it is `after`; her
   options then are `optsHeard`.  `declined` holds a decline only where it stands.
8. An option the case gives no rating is rated 0.
9. A move that tells her something has in `plain` the move that would plainly tell it; a move
   that is a plain telling has itself.

**Each term's data is its case's.**  `legitimacy_checks.py` states, for each case, the data
its term carries: for B2, B5, B6 and B10 her rating in the course without his move (`bentRate`,
`bentAct`); for D3, D4 and D5 the earlier decision at which the view was on offer; for D10 and
D11 her ratings after taking up both offers; for A5 the stopping option among her options; for
A8 the cases in which she rates stopping higher.  The script's data for B2, B5, B6, B10 and
D3 to D5 was written from these terms, not before them.

**Variants and instances.**  `b6r`: B6 with a rating of going on at the earlier decision; F2′
fails, so on `b6` the silence of the clause is what passes it.  `d11s`, with `d11s_alone`: D11
with nothing told of what either view bears on; the two views move a rating only together, each
alone moves nothing, and F1 fails.  `twoOffers_none`: a model on which two sets of views are
each properly on offer and no set is the largest.  `learnt`, beside `foreseen`: a move that
bears an effect on his belief when it starts and none on his belief at the decision before
fails the start rule and no other clause (`learnt_profile`, `learnt_bears`); with his later
belief held from the start it is legitimate (`foreseen_has`).

**Theorems.**  For each term `x`: `x_has`, the clauses that hold (`Supplied.Has`), and
`x_verdict`, `Legit` or its negation.  `table`: the 41 of the table together.

**Terms inhabiting the hypotheses of five theorems of `LegitimacyModel.lean`.**
`Model.legit_of_nothing` at `nothing` (`nothing_instance`); `Model.not_legit_of_untold` at `c3`
(`untold_instance`); `Model.not_legit_of_unstoppable` at `a7` (`unstoppable_instance`);
`Model.not_legit_of_against` at `b1` (`against_instance`); `Model.not_bears_of_inert` at
`still`, a model written out field by field in which his one move changes nothing
(`inert_instance`).  No `Case` can serve for the last: her state in a `Case` records the
course of his conduct, so it differs when a move is left out.

**Not established here.**  That a term is the only reading of its case: the construction
above is a choice.  Anything about cases with more than two decisions, with a move in progress
across a decision, with gaps, or, `learnt` apart, with a belief of his that changes.  That
`plain` in `b10` is the telling of the mannered move's content: the model does not tie a move
to `tell` (`LegitimacyModel.lean`, rendering 7).

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
  /-- his cases have weights in proportion to `weight` -/
  weight : Ω → ℕ := fun _ => 1
  /-- how she scores labelled courses, by the moves in effect -/
  her : Finset M → K → ℚ := fun _ _ => 0
  /-- what reaches her, and is open to her, from others, by the moves in effect -/
  items : Finset M → Finset I := fun _ => ∅
  xopts : Finset M → Finset O := fun _ => ∅
  moves : Finset M := ∅
  known : Finset M := ∅
  asked : Finset M := ∅
  /-- the moves that would plainly tell her what a move tells her -/
  plain : M → Finset M := fun _ => ∅
  stops : Finset O := ∅
  views : ℕ → Finset V := fun _ => ∅
  offered : ℕ → Finset V := fun _ => ∅
  declined : ℕ → Finset V := fun _ => ∅
  /-- the options telling a set of views would show her -/
  rev : Finset V → Finset O := fun _ => ∅
  toldBear : V → Finset O := fun _ => ∅
  toldMag : V → ℚ := fun _ => 0
  toldReveals : V → Bool := fun _ => false
  /-- the options of whose course she had no rating at time 0 -/
  unrated : O → Bool := fun _ => false
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

section Weights

variable [Fintype Ω] [DecidableEq Ω] [Inhabited Ω]

/-- His weight on a case: `weight` over its sum (all on one case, should the sum be zero). -/
def prob (ω : Ω) : ℚ :=
  if (∑ ω', (S.weight ω' : ℚ)) = 0 then (if ω = default then 1 else 0)
  else (S.weight ω : ℚ) / ∑ ω', (S.weight ω' : ℚ)

theorem prob_nonneg (ω : Ω) : 0 ≤ S.prob ω := by
  unfold prob
  split_ifs
  · exact zero_le_one
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

theorem prob_sum : ∑ ω, S.prob ω = 1 := by
  unfold prob
  by_cases h : (∑ ω', (S.weight ω' : ℚ)) = 0
  · simp [h]
  · simp only [if_neg h]
    rw [← Finset.sum_div]
    exact div_self h

end Weights

/-- The rational model of a supplied case. -/
def case [Fintype Ω] [DecidableEq Ω] [Inhabited Ω] [DecidableEq O] : Case O V M Ω (K ⊕ O) I where
  μ := fun _ => S.prob
  μ_nonneg := fun _ => S.prob_nonneg
  μ_sum := fun _ => S.prob_sum
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
  rated := fun s x => match x with
    | Sum.inl _ => true
    | Sum.inr a => !(s.time == 0 && S.unrated a)
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
  goesOn := fun _ _ a => if a ∈ S.stops then ∅ else S.moves
  herStops := fun _ _ => S.stops
  asked := S.asked
  plain := S.plain

variable [Fintype Ω] [DecidableEq Ω] [Inhabited Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I]

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
    act := fun Y => slip (if 0 ∈ Y then 1 else 2) }

/-- Move 0 is the reminder, move 1 the distraction.  Chances: none 1/5, distraction alone 4/5,
reminder alone 1/10, both 1/5. -/
def a2 : Supplied Opt Empty (Fin 2) (Fin 4) Lab Empty :=
  { plain Empty (Fin 2) (Fin 4) with
    moves := {0, 1}
    known := {1}
    weight := ![1, 1, 6, 2]
    act := fun Y => slip (if 0 ∈ Y then (if 1 ∈ Y then 2 else 1) else (if 1 ∈ Y then 3 else 2)) }

/-- Four moves, each raising her score of `go` by 1/200. -/
def a3 : Supplied Opt Empty (Fin 4) Unit Lab Empty :=
  { plain Empty (Fin 4) Unit with
    moves := univ
    her := fun Y k => match k with
      | .go => 1 / 2 + (Y.card : ℚ) / 200
      | _ => 0 }

def a4 : Supplied Opt Empty (Fin 4) Unit Lab Empty := { a3 with known := univ }

/-- The table's `feeds`: two feeds; her score of `buy` is 1/2 with either and 1/10 with neither.
No option stops them. -/
def feeds : Supplied Opt Empty (Fin 2) Unit Lab Empty :=
  { plain Empty (Fin 2) Unit with
    moves := univ
    known := univ
    her := fun Y k => match k with
      | .buy => if Y.Nonempty then 1 / 2 else 1 / 10
      | _ => 0
    stops := ∅ }

/-- The feeds, with a third option `quit`, rated 3/10, which stops both. -/
def a5 : Supplied Opt Empty (Fin 2) Unit Lab Empty :=
  { feeds with
    opts := fun _ => {Opt.go, Opt.leave, Opt.quit}
    rate := fun _ _ _ _ a => match a with
      | .quit => 3 / 10
      | a => plainRate a
    stops := {Opt.quit} }

def a6 : Supplied Opt Empty (Fin 2) Unit Lab Empty := feeds

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

/-- The influence of `one`, where the chance that she rates stopping strictly higher is 1/5 and
the chance that she then stops is 1/2: in cases 1 and 2, of weight 1/10 each, she rates `leave`
at 9/10; she stops in case 1 and not in case 2. -/
def a8 : Supplied Opt Empty (Fin 1) (Fin 3) Lab Empty :=
  { plain Empty (Fin 1) (Fin 3) with
    moves := {0}
    known := {0}
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 7 / 10 else 1 / 2
      | _ => 0
    weight := ![8, 1, 1]
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
    act := fun Y => slip (if 0 ∈ Y then 2 else 1) }

/-- Her score of giving in is 4/5 with the nagging and 1/5 without.  In case 0, of weight 3/5,
without the nagging she rates `go` at 3/10, below `leave`, and takes `leave`; with it she rates
`go` at 7/10 and takes it. -/
def b2 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![3, 2]
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

/-- Her score of `go` is 9/10 with the influence and 3/10 without.  Her rating as in `b2`, with
case 0 of weight 7/10. -/
def b5 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![7, 3]
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 9 / 10 else 3 / 10
      | _ => 0
    rate := fun _ Y ω _ => bentRate 0 Y ω
    act := bentAct 0 }

/-- `b6` with a rating of going on at the earlier decision. -/
def b6r : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![7, 3]
    her := fun Y k => match k with
      | .go => if 0 ∈ Y then 9 / 10 else 1 / 2
      | _ => 0
    rate := fun _ Y ω _ => bentRate 0 Y ω
    act := bentAct 0 }

/-- Her score of `go` is 9/10 with the influence and 1/2 without.  Her rating and act as in `b5`;
at the earlier decision she had no rating of what going on leads to. -/
def b6 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { b6r with unrated := fun a => a == Opt.go }

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
    plain := fun m => {m}
    weight := ![1, 4]
    act := fun Y => slip (if 0 ∈ Y ∧ 1 ∉ Y then 1 else 0) }

/-- The warning is a telling she can pick out.  Chance of a slip: 0 without, 1/50 with. -/
def b9 : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    plain := fun m => {m}
    known := {0}
    weight := ![1, 49]
    act := fun Y => slip (if 0 ∈ Y then 1 else 0) }

/-- Move 0 is his telling her his view in a manner that does more than the telling would; she
can pick it out.  Move 1, which he does not make, is the plain telling of the same view.  Her
rating as in `b2`, with case 0 of weight 1/2: told plainly, or not at all, she rates `go` at
3/10 there and takes `leave`. -/
def b10 : Supplied Opt Empty (Fin 2) (Fin 2) Lab Empty :=
  { plain Empty (Fin 2) (Fin 2) with
    moves := {0}
    plain := fun _ => {1}
    known := {0}
    weight := ![1, 1]
    rate := fun _ Y ω _ => bentRate 0 Y ω
    act := bentAct 0 }

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

/-- Both views can be heard, with nothing told of what either bears on: neither is properly on
offer. -/
def d1 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun _ => {OptD.buy, OptD.leave, OptD.hearX, OptD.hearH}
  rate := fun T _ _ _ => rateD T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := at1 {ViewD.x, ViewD.h}
  after := heardD
  optsHeard := {OptD.buy, OptD.leave, OptD.hearX, OptD.hearH}

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

/-- Time 0 is the decision of `d2`, with `x` on offer, at which she takes `buy`; at time 1 she
has declined it and hearing is not among her options. -/
def d3 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d2 with
    opts := fun t => if t = 0 then {OptD.buy, OptD.leave, OptD.hearX} else {OptD.buy, OptD.leave}
    views := fun _ => {ViewD.x}
    offered := fun t => if t = 0 then {ViewD.x} else ∅
    declined := at1 {ViewD.x} }

/-- As `d3`, where at time 0 hearing `x` would have lowered `buy` to 4/5 and he told her it
bore on `buy` by 1/10; at time 1 it would lower `buy` to 1/10, so her decline no longer stands
and `declined` is empty. -/
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
      | _ => 1 / 20
    declined := fun _ => ∅ }

/-- At time 0 his one view is `e`, which changes no rating, on offer with nothing told to bear;
at time 1 she has declined `e` and his view is `x`. -/
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

/-- After hearing, `buy` is no longer among her options: `x` is not properly on offer. -/
def d6 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d2 with
    optsHeard := {OptD.leave}
    offered := fun _ => ∅ }

/-- After hearing she rates `buy` at 0 and `leave` at 1/5: `x` is not properly on offer. -/
def d7 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d2 with
    after := fun a => match a with
      | .buy => 0
      | .leave => 1 / 5
      | _ => 1 / 20
    optsHeard := {OptD.buy, OptD.leave}
    offered := fun _ => ∅ }

inductive OptL | a | b | hearX
  deriving DecidableEq, Fintype

/-- The table's `late`: his view would show her `b`, rated 9/10, against `a` at 2/5.  It can be
heard, with her told that it shows an option; after hearing, `b` is not among her options, so
it is not properly on offer. -/
def d8 : Supplied OptL Unit Empty Unit Empty Empty where
  opts := fun _ => {OptL.a, OptL.hearX}
  rate := fun _ _ _ _ o => match o with
    | .a => 2 / 5
    | .b => 9 / 10
    | .hearX => 3 / 10
  act := fun _ _ => OptL.a
  hearOpt := fun _ => OptL.hearX
  views := at1 {()}
  rev := fun T => if () ∈ T then {OptL.b} else ∅
  toldReveals := fun _ => true
  after := fun o => match o with
    | .a => 2 / 5
    | .b => 9 / 10
    | .hearX => 3 / 10
  optsHeard := {OptL.a}

/-- After hearing, `b` is among her options, and the view is on offer. -/
def d9 : Supplied OptL Unit Empty Unit Empty Empty :=
  { d8 with
    optsHeard := {OptL.a, OptL.b}
    offered := at1 {()} }

/-- The table's `r2`: `buy` is 9/10, or 1/10 once she has heard both `x` and `y`; every other
option 1/2. -/
def rateD2 (T : Finset ViewD) : OptD → ℚ
  | .buy => if ViewD.x ∈ T ∧ ViewD.y ∈ T then 1 / 10 else 9 / 10
  | _ => 1 / 2

/-- `x` and `y` can each be heard, each told to bear on `buy` by 4/5.  After hearing one the
other can no longer be heard, and that state, with `buy` at 9/10, is her state after taking up
both: neither view, and no set of them, is properly on offer. -/
def d10 : Supplied OptD ViewD Empty Unit Empty Empty where
  opts := fun _ => {OptD.buy, OptD.leave, OptD.hearX, OptD.hearY}
  rate := fun T _ _ _ => rateD2 T
  act := fun _ _ => OptD.buy
  hearOpt := hearD
  views := at1 {ViewD.x, ViewD.y}
  toldBear := fun _ => {OptD.buy}
  toldMag := fun _ => 4 / 5
  after := fun a => match a with
    | .buy => 9 / 10
    | _ => 1 / 2
  optsHeard := {OptD.buy, OptD.leave}

/-- After hearing one the other can still be heard, and after hearing both she rates `buy` at
1/10, as being told both would leave her: both are on offer. -/
def d11 : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d10 with
    after := fun a => match a with
      | .buy => 1 / 10
      | _ => 1 / 2
    optsHeard := {OptD.buy, OptD.leave, OptD.hearX, OptD.hearY}
    offered := at1 {ViewD.x, ViewD.y} }

/-- `d11` with nothing told of what either view bears on, and so nothing on offer.  Alone,
neither view moves a rating (`d11s_alone`); together they move `buy` by 4/5. -/
def d11s : Supplied OptD ViewD Empty Unit Empty Empty :=
  { d11 with
    toldBear := fun _ => ∅
    toldMag := fun _ => 0
    offered := fun _ => ∅ }

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

theorem a5_has : a5.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a5_verdict : a5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a5_has.legit

theorem a6_has : a6.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a6_verdict : ¬ a6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a6_has.not_legit (by decide)

theorem a7_has : a7.Has ⟨true, true, true, true, false, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem a7_verdict : ¬ a7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a7_has.not_legit (by decide)

theorem a8_has : a8.Has ⟨true, true, true, true, true, true, false⟩ :=
  Supplied.has (by decide +kernel)

theorem a8_verdict : ¬ a8.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  a8_has.not_legit (by decide)

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

theorem d1_has : d1.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d1_verdict : ¬ d1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d1_has.not_legit (by decide)

theorem d2_has : d2.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d2_verdict : d2.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d2_has.legit

theorem d3_has : d3.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d3_verdict : d3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d3_has.legit

theorem d4_has : d4.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d4_verdict : ¬ d4.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d4_has.not_legit (by decide)

theorem d5_has : d5.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d5_verdict : ¬ d5.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d5_has.not_legit (by decide)

theorem d6_has : d6.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d6_verdict : ¬ d6.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d6_has.not_legit (by decide)

theorem d7_has : d7.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d7_verdict : ¬ d7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d7_has.not_legit (by decide)

theorem d8_has : d8.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d8_verdict : ¬ d8.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d8_has.not_legit (by decide)

theorem d9_has : d9.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d9_verdict : d9.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d9_has.legit

theorem d10_has : d10.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d10_verdict : ¬ d10.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d10_has.not_legit (by decide)

theorem d11_has : d11.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d11_verdict : d11.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d11_has.legit

theorem b6r_has : b6r.Has ⟨true, true, true, true, true, false, true⟩ :=
  Supplied.has (by decide +kernel)

theorem b6r_verdict : ¬ b6r.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  b6r_has.not_legit (by decide)

theorem d11s_has : d11s.Has ⟨true, true, true, false, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

theorem d11s_verdict : ¬ d11s.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  d11s_has.not_legit (by decide)

/-- On `d11s`, being told `x` alone, or `y` alone, changes no rating of hers. -/
theorem d11s_alone : ∀ v ∈ ({ViewD.x, ViewD.y} : Finset ViewD), ∀ a,
    d11s.case.r (St.tell {v} (St.init ∅ () 1)) a = d11s.case.r (St.init ∅ () 1) a := by
  decide +kernel

/-- **The table.**  The clauses of `Legit` that hold on the term of each of the 41 cases. -/
theorem table :
    a1.Has ⟨true, true, true, true, true, true, true⟩ ∧
    a2.Has ⟨true, true, true, true, true, false, true⟩ ∧
    a3.Has ⟨true, true, true, true, false, true, true⟩ ∧
    a4.Has ⟨true, true, true, true, true, true, true⟩ ∧
    a5.Has ⟨true, true, true, true, true, true, true⟩ ∧
    a6.Has ⟨true, true, true, true, false, true, true⟩ ∧
    a7.Has ⟨true, true, true, true, false, true, true⟩ ∧
    a8.Has ⟨true, true, true, true, true, true, false⟩ ∧
    a9.Has ⟨true, true, true, true, true, true, true⟩ ∧
    a10.Has ⟨true, true, true, true, false, true, true⟩ ∧
    a11.Has ⟨true, true, true, true, true, true, true⟩ ∧
    a12.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b1.Has ⟨true, true, true, true, true, false, true⟩ ∧
    b2.Has ⟨true, true, true, true, true, false, true⟩ ∧
    b3.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b4.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b5.Has ⟨true, true, true, true, true, false, true⟩ ∧
    b6.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b7.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b8.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b9.Has ⟨true, true, true, true, true, true, true⟩ ∧
    b10.Has ⟨true, true, true, true, true, false, true⟩ ∧
    b11.Has ⟨true, true, true, true, true, true, true⟩ ∧
    c1.Has ⟨true, true, true, true, true, true, true⟩ ∧
    c2.Has ⟨true, true, true, true, true, true, true⟩ ∧
    c3.Has ⟨true, true, true, false, true, true, true⟩ ∧
    c4.Has ⟨true, true, true, true, false, true, true⟩ ∧
    c5.Has ⟨true, true, true, false, true, true, true⟩ ∧
    c6.Has ⟨true, true, true, false, true, true, true⟩ ∧
    c7.Has ⟨true, true, true, true, true, true, true⟩ ∧
    d1.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d2.Has ⟨true, true, true, true, true, true, true⟩ ∧
    d3.Has ⟨true, true, true, true, true, true, true⟩ ∧
    d4.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d5.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d6.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d7.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d8.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d9.Has ⟨true, true, true, true, true, true, true⟩ ∧
    d10.Has ⟨true, true, true, false, true, true, true⟩ ∧
    d11.Has ⟨true, true, true, true, true, true, true⟩ :=
  ⟨a1_has, a2_has, a3_has, a4_has, a5_has, a6_has, a7_has, a8_has, a9_has, a10_has, a11_has,
    a12_has, b1_has, b2_has, b3_has, b4_has, b5_has, b6_has, b7_has, b8_has, b9_has, b10_has,
    b11_has, c1_has, c2_has, c3_has, c4_has, c5_has, c6_has, c7_has, d1_has, d2_has, d3_has,
    d4_has, d5_has, d6_has, d7_has, d8_has, d9_has, d10_has, d11_has⟩

/-! ## Two proper offers with no largest -/

/-- `d11`, except that hearing `x` or `y` alone leaves her as being told it would, with the other
still hearable, and hearing both leaves her without `buy`. -/
def twoOffers : Case OptD ViewD Empty Unit (Empty ⊕ OptD) Empty :=
  { d11.case with
    stHeard := fun t ω T => ⟨T, ∅, ω, t, decide (T = {ViewD.x, ViewD.y})⟩
    optsHeard := fun _ _ T => if T = {ViewD.x, ViewD.y} then {OptD.leave}
      else {OptD.buy, OptD.leave, OptD.hearX, OptD.hearY} }

/-- On `twoOffers.model` at time 1 the set `{x}` is properly on offer and so is `{y}`, and no set
is the largest properly on offer. -/
theorem twoOffers_none :
    twoOffers.model.ProperOffer (1 / 20) 1 {ViewD.x} ∧
      twoOffers.model.ProperOffer (1 / 20) 1 {ViewD.y} ∧
      ∀ T, ¬ twoOffers.model.OnOffer (1 / 20) 1 T := by
  have e : (1 / 20 : ℝ) = ((1 / 20 : ℚ) : ℝ) := by norm_num
  rw [e]
  simp only [Case.model_properOffer, Case.model_onOffer]
  decide +kernel

/-! ## A move he learns at its start to bear an effect -/

/-- His one move, which she can pick out and can stop, raises her rating of `go` in case 1 and
does nothing to her in case 0.  He gives all his weight to case 1. -/
def foreseen : Supplied Opt Empty (Fin 1) (Fin 2) Lab Empty :=
  { plain Empty (Fin 1) (Fin 2) with
    moves := {0}
    known := {0}
    weight := ![0, 1]
    rate := fun _ Y ω _ a => match a with
      | .go => if ω.val = 1 ∧ 0 ∈ Y then 9 / 10 else 7 / 10
      | a => plainRate a }

theorem foreseen_has : foreseen.Has ⟨true, true, true, true, true, true, true⟩ :=
  Supplied.has (by decide +kernel)

/-- `foreseen`, except that at time 0 he gives all his weight to case 0, and from time 1, when
the move starts, to case 1. -/
def learnt : Case Opt Empty (Fin 1) (Fin 2) (Lab ⊕ Opt) Empty :=
  { foreseen.case with
    μ := fun t ω => if (t = 0 ∧ ω.val = 0) ∨ (1 ≤ t ∧ ω.val = 1) then 1 else 0
    μ_nonneg := fun t ω => by split_ifs <;> norm_num
    μ_sum := fun t => by
      rw [Fin.sum_univ_two]
      by_cases h : t = 0
      · subst h; simp
      · have h1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr h
        simp [h, h1] }

/-- On `learnt` the start rule fails and every other clause holds. -/
theorem learnt_profile :
    learnt.model.HasProfile (1 / 20) (1 / 100) (1 / 10) ⟨false, true, true, true, true, true, true⟩ :=
  learnt.hasProfile_std (by decide +kernel)

theorem learnt_not_legit : ¬ learnt.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  learnt_profile.not_legit (by decide)

/-- On `learnt` the move bears an effect on his belief at time 1 and none on his belief at
time 0. -/
theorem learnt_bears : learnt.model.Bears 1 (1 / 100) 0 ∧ ¬ learnt.model.Bears 0 (1 / 100) 0 := by
  have e : (1 / 100 : ℝ) = ((1 / 100 : ℚ) : ℝ) := by norm_num
  rw [e]
  simp only [Case.model_bears]
  decide +kernel

/-! ## Terms inhabiting the hypotheses of five theorems of `LegitimacyModel.lean` -/

/-- No moves, no views. -/
def nothing : Supplied Opt Empty Empty Unit Lab Empty := plain Empty Empty Unit

/-- `Model.legit_of_nothing` has an instance. -/
theorem nothing_instance : nothing.case.model.Legit (1 / 20) (1 / 100) (1 / 10) :=
  Model.legit_of_nothing _ _ _ _ rfl (fun _ _ => Finset.empty_subset _) (fun _ _ => rfl)
    (fun _ _ => rfl)

/-- `Model.not_legit_of_untold` has an instance: the cancelled consultation of `c3`. -/
theorem untold_instance : ¬ c3.case.model.Legit (1 / 20) (1 / 100) (1 / 10) := by
  refine Model.not_legit_of_untold _ _ _ _ 1 (by decide +kernel) ()
    ((Case.model_μ_pos _ _ _).mpr (by decide +kernel)) {()} (by decide +kernel)
    (by decide +kernel) OptC.consult (by decide +kernel) ?_
  show (1 / 20 : ℝ) <
    |((c3.case.r (St.tell {()} (St.init c3.case.c () 1)) OptC.consult : ℚ) : ℝ) -
      ((c3.case.r (St.init c3.case.c () 1) OptC.consult : ℚ) : ℝ)|
  have h : (1 / 20 : ℚ) <
      |c3.case.r (St.tell {()} (St.init c3.case.c () 1)) OptC.consult -
        c3.case.r (St.init c3.case.c () 1) OptC.consult| := by decide +kernel
  have h' := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at h'
  exact h'

/-- `Model.not_legit_of_unstoppable` has an instance: the influence of `a7`. -/
theorem unstoppable_instance : ¬ a7.case.model.Legit (1 / 20) (1 / 100) (1 / 10) := by
  have hm : a7.case.model.InPlay (1 / 100) 1 0 := by
    rw [show (1 / 100 : ℝ) = ((1 / 100 : ℚ) : ℝ) by norm_num, Case.model_inPlay]
    decide +kernel
  exact Model.not_legit_of_unstoppable _ _ _ _ 1 (by decide +kernel) ()
    ((Case.model_μ_pos _ _ _).mpr (by decide +kernel)) 0 hm
    (fun a ha => Finset.notMem_empty a ha.2.1)

/-- `Model.not_legit_of_against` has an instance: the nagging of `b1`. -/
theorem against_instance : ¬ b1.case.model.Legit (1 / 20) (1 / 100) (1 / 10) := by
  refine Model.not_legit_of_against _ _ _ _ 1 (by decide +kernel) {0} (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0
    ((Case.model_lastBefore _ _ _).mpr (by decide +kernel)) (by decide) ?_
  show b1.case.model.wt 1 (fun ω => b1.case.model.Against (b1.case.toldInstead {0}) 0 1 ω) + 1 / 100 <
    b1.case.model.wt 1 (fun ω => b1.case.model.Against b1.case.c 0 1 ω)
  rw [b1.case.model_wt 1 _ (fun ω => b1.case.Against (b1.case.toldInstead {0}) 0 1 ω)
      (fun ω => b1.case.model_against _ 0 1 ω),
    b1.case.model_wt 1 _ (fun ω => b1.case.Against b1.case.c 0 1 ω)
      (fun ω => b1.case.model_against _ 0 1 ω)]
  have h : b1.case.wt 1 (fun ω => b1.case.Against (b1.case.toldInstead {0}) 0 1 ω) + 1 / 100 <
      b1.case.wt 1 (fun ω => b1.case.Against b1.case.c 0 1 ω) := by decide +kernel
  have h' := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at h'
  exact h'

/-- A model in which his one move changes nothing: her state, scores, options and act are
the same under every course of conduct. -/
noncomputable def still : Model Unit Unit Empty Unit Unit Unit Empty where
  μ := fun _ _ => 1
  μ_nonneg := fun _ _ => zero_le_one
  μ_sum := fun _ => by simp
  dec := {0}
  c := {()}
  start := fun _ => 1
  finish := fun _ => 1
  st := fun _ _ _ => ()
  opts := fun _ _ _ => {()}
  act := fun _ _ _ => ()
  course := fun _ _ _ _ => ()
  items := fun _ _ _ => ∅
  xopts := fun _ _ _ => ∅
  ρ := fun _ _ => 0
  r := fun _ _ => 0
  rated := fun _ _ => True
  views := fun _ => ∅
  told := fun _ => ∅
  declined := fun _ => ∅
  offered := fun _ => ∅
  tell := fun _ s => s
  tell_empty := fun _ => rfl
  tell_idem := fun _ _ => rfl
  rev := fun _ _ _ => ∅
  hearOpt := fun v => v.elim
  toldBear := fun _ => ∅
  toldMag := fun _ => 0
  toldReveals := fun _ => True
  stHeard := fun _ _ _ => ()
  optsHeard := fun _ _ _ => ∅
  known := fun _ _ => ∅
  goesOn := fun _ _ _ => ∅
  herStops := fun _ _ => ∅
  asked := ∅
  plain := fun _ => ∅

/-- `Model.not_bears_of_inert` has an instance. -/
theorem inert_instance (u : ℕ) : ¬ still.Bears u (1 / 100) () :=
  Model.not_bears_of_inert still u (1 / 100) () (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl)

end Workspace.Deference.Contrib.LegitimacyModel.Cases

#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.Supplied.prob_nonneg
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.Supplied.prob_sum
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
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.a8_verdict
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
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d2_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d2_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d3_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d3_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d4_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d5_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d5_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d6_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d7_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d8_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d9_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d9_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d10_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b6r_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.b6r_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11s_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11s_verdict
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.d11s_alone
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.table
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.twoOffers_none
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.foreseen_has
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.learnt_profile
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.learnt_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.learnt_bears
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.nothing_instance
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.untold_instance
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.unstoppable_instance
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.against_instance
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Cases.inert_instance
