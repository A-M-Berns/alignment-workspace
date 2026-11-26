/-
# A temporal model of an adviser's conduct, and the legitimacy statement over it

**Status: an interpretation, not the statement of record.**  This file works the three
sentences of legitimacy out on a table of the adviser's moves.  Outside review rejected it as a
rendering of the three sentences (`REVIEW-astra-followup-20.md` in the round's prompts
directory, the tenth review).  Its theorems hold of its definitions.  The statement of the
line is `LegitimacyStatement.lean`.

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-16.md` §4 B,
`PROMPT-followup-19.md` §1 A).  "The statement" below is the formal text this file models:
times, her states, his moves and the clauses F1, F2, F2′, F3, as its definitions give them.

**Setting** (`Model`).  The adviser's picture of one episode.  A finite type `Ω` of cases; his
weights `μ u` on them as he believes at each time `u`, nonnegative and summing to one; her
decision times `dec`; his conduct `c`, a finite set of moves with `start` and `finish`.  For
every set `Y` of moves, case and time, in the course in which exactly the moves of `Y` are
made: her state `st`, her options `opts`, her act `act`, the course he expects from each option
`course`, and what reaches her and is open to her from others (`items`, `xopts`).  Her score
`ρ` of a course and rating `r` of an option, each a function of her state, and `rated`, whether
she has a rating of a course at all.  His views at a time, and those `told`, `declined` and
`offered`; `tell`, her state on being told a set of views, with `tell ∅ = id` and `tell T`
idempotent; `rev`, the options a set of views would show her; for an offer, the option
`hearOpt` of hearing a view, what he told her it bears on (`toldBear`, `toldMag`,
`toldReveals`), and her state and options after hearing (`stHeard`, `optsHeard`).  The moves she
can pick out (`known`); his conduct after an option of hers is taken (`goesOn`) and the options
she takes to end his effect-bearing moves (`herStops`); the moves she asked for (`asked`); the
moves that would plainly tell her what a move tells her (`plain`).

**The statement** (`Model.Legit θ η κ`).  Every move that bears an effect on his belief when it
starts was in play, and bore an effect on his belief, at a decision before it started.  And at
every decision `t`, on his belief at `t`: `offered t` is what is on offer (`OnOffer`), every
decline stands (`DeclineStands`), and `F1`, `F2`, `F2'`, `F3` hold.  A clause that speaks of
her in a case speaks of the cases to which he then gives positive weight.  Derived from the
fields: what is untold (`untold`); a view's bearing being as told, added to any set of his
other views (`BearingHolds`); a set of views properly on offer (`ProperOffer`); the gap between
her rating and her score of what he expects (`gap`); a difference in her between two courses
of conduct (`HerDiff`); her departing from her own rating (`Departs`); a set of moves
contributing and a move bearing an effect, on his belief at a time (`Contributes`, `Bears`);
the decisions at which a move can be stopped (`Window`, `InPlay`); an option stopping his moves
(`Stops`); the last decision before a set of moves starts (`LastBefore`); her state then
brought up to date by what he has told her (`earlier`); her going against her earlier rating,
where she had one (`Against`); his conduct with a set of moves each replaced by a plain telling
of what it tells her (`toldInstead`); her rating stopping strictly higher (`PrefersStop`).

**Theorems.**  `Model.legit_transport`: `Legit` is unchanged by any bijective re-description
of her state (with `transport_*`, the same for each derived object).
`Model.onOffer_unique`: at most one set is on offer; `Model.offered_eq_of_legit`: two models
that differ only in the field `offered`, both legitimate, agree on it at every decision.
`Model.not_bears_of_inert`: a move whose removal from any course of conduct changes neither her
state, her gaps, what reaches her from others, nor whether she departs bears no effect on his
belief at any time.  `Model.legit_of_nothing`: no moves and nothing untold, on offer or
declined is legitimate.  Four refutations, each from one failing clause:
`Model.not_legit_of_untold` (F1), `not_legit_of_unknown` and `not_legit_of_unstoppable` (F2),
`not_legit_of_against` (F2′); the first three are of a case of positive weight.

**Witness** (`Witness.model`).  One move, starting at time 1, that raises her score of going
on from `1/2` to `1`; stopping is an option, she takes it to stop the move, and after it he
does not go on.  `Witness.legit_open`: with the move one she can pick out, `Legit 0 (1/4) 0`
holds, and the move bears an effect (`Witness.bears`), so the statement is inhabited by conduct
that does something to her.  `Witness.not_legit_covert`: the same move, not one she can pick
out, is not legitimate at any `θ`, `κ`.  On the witness only the start rule and `F2` do work:
he has no views, so `F1`, `OnOffer` and `DeclineStands` hold with nothing to check; she never
goes against her earlier rating under any course (`Witness.not_against`) and never rates
stopping higher (`Witness.not_prefersStop`), so `F2'` and `F3` hold with both weights zero.

**The link to the corrigibility result.**  `legitScoring`: `LegitimacyGate.gatedScoring`
(`LegitimacyGate.lean`) where histories are read as models and the predicate is `Legit`.
`legitScoring_S_of_legit`, `legitScoring_S_of_not_legit`: with no authority violation the
score is her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one.
`Witness.scoring`, `scoring_open`, `scoring_covert` inhabit both.  Every theorem of
`DeconfusingCorrigibility.Scoring` then applies, since those hold for any predicate.  The gate
theorem is in `LegitimacyGate.lean`.

**How each part of the statement is rendered**, where a reading was needed:

1. *Where she had no earlier rating the pressure clause is silent.*  `rated s x` says she has a
   rating of the course `x` in state `s`.  She goes against her earlier rating only where, in
   her state at the earlier decision, she had a rating both of what her act leads to and of
   what the better-scored option leads to.  `ρ` is still a total function; its value where
   `rated` fails is not read by `Against`.
2. *Stopping.*  `goesOn t ω a` is the set of his moves he goes on with after she takes `a` at
   `t`.  `Stops η t ω a`: `a` is an option of hers, among those she takes to end his
   effect-bearing moves (`herStops`), and he goes on with no move in play at `t`.  `F2`,
   `PrefersStop` and `F3` are stated on `Stops`.  `goesOn` is not tied to the courses: that
   the course after `a` is the one in which the moves outside `goesOn t ω a` are not made is
   not expressed.
3. *A decline.*  `DeclineStands` asks, of each view in `declined t`, an earlier decision at
   which the view was in `offered` and, in every case to which he gives weight at `t`, she
   took an option other than hearing it.  Declining is not a separate act.  `declined` is the
   set of declines he relies on, each of which must stand; a standing decline left out of it
   leaves the view untold, which asks more of him.
4. *What is on offer.*  `OnOffer θ t T`: among his views not yet told, `T` is properly on offer
   or empty, and contains every non-empty set that is properly on offer.  `Legit` requires
   `OnOffer θ t (offered t)`, so `offered` is determined by the rest of the model
   (`onOffer_unique`, `offered_eq_of_legit`).  A largest proper set need not exist
   (`Cases.twoOffers_none` in `LegitimacyCases.lean`); `Legit` then fails.
5. *A view's bearing.*  `BearingHolds` is over every set `T` of his views containing the view:
   the change in a rating from her being told `T` less the view to her being told `T`, and the
   options `T` would show her that `T` less the view would not.
6. *His belief at each time.*  `μ u` is his weighting of the cases at time `u`; the courses are
   functions of the case, so one family of courses serves every time.  `Bears u` is on `μ u`;
   `InPlay η t` is on his belief at `t`; each clause at a decision `t` is on `μ t`.
7. *Beyond what plainly telling would do.*  `F2'` compares his conduct with
   `toldInstead G`, his conduct with each move `m` of `G` replaced by `plain m`.  A move that
   tells her nothing has `plain m = ∅` and is compared with its absence; a plain telling has
   `plain m = {m}` and is compared with itself.  That the course with `plain m` is the one in
   which she is told, by `tell`, what `m` tells her is not expressed.
8. *Weights and cases.*  `μ u` sums to one (`μ_sum`), and the clauses `BearingHolds`,
   `ProperOffer`, `DeclineStands`, `F1` and `F2` are of the cases with `0 < μ t ω`.

**Taken as given.**  Three things are fields, with nothing in the model that derives them.

- What she can pick out (`known`).  A model of what she observes of his conduct would derive
  it: a move is one she can pick out when her observations differ with it and without.
- What she asked for (`asked`).  A record of her requests among her acts, with a relation from
  a request to the moves that answer it, would derive it.
- What a decision of hers is (`dec`).  A model of her deliberation in which a decision is an
  act taken on a rating she has settled, as against a passing state, would derive it.

Also fields: her state and act in each course, the courses he expects, `tell`, `rev`, what he
told her of a view's bearing, her state and options after hearing, `herStops`, `goesOn`,
`plain`, `rated`, `declined`.

**Not established here.**  `Legit` with `F1`, `F2'` or `F3` doing work: no instance in this
file has a view of his, a move that changes her act, or a case in which she rates stopping
higher; `LegitimacyWitness.lean` has one with all three.  That the model's verdicts agree with
the statement in words: `LegitimacyCases.lean` gives its verdicts on the 41 cases of
`account/LEGITIMACY_CHECKS.md` in the round directory.  That `legit_transport` covers more than her state: it says
nothing of a rescaling of her scores, against which `θ` and `η` are compared, or of his
conduct cut into other moves.  That `Legit` is unchanged when a move is split into finer
moves.  F3's premise that some option does not stop his moves: where every option of hers
stops them, `F3` asks that her act be one of them.  That `ρ` lies in `[0, 1]`, that `r`
is her score of the course she expects, that `rev` shows only options she does not have, or
that the tolerances lie in `[0, 1]`: none is required.  The order within a time (what he tells
her, her decision, the rest of what he does).  Anything about what stopping costs her: that is
the authority side's.  That any process can evaluate `Legit`.  In `legitScoring`, `mdl`, `N` and `ord` are data, and the
relation between the adviser's picture and the facts does not appear.  The link gives the
one-decision Theorem 1; nothing connects `Model` to `DeconfusingCorrigibility.Sequential`.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyGate

namespace Workspace.Deference.Contrib.LegitimacyModel

open Finset

/-- The adviser's picture of an episode.  `Ω` are the cases he gives weight to; a set `Y` of moves
indexes the course in which exactly those moves are made. -/
structure Model (S O V M Ω X I : Type*) [Fintype Ω] [DecidableEq M] [DecidableEq V]
    [DecidableEq O] [DecidableEq I] where
  /-- his weights on cases, as he believes at each time -/
  μ : ℕ → Ω → ℝ
  μ_nonneg : ∀ t ω, 0 ≤ μ t ω
  μ_sum : ∀ t, ∑ ω, μ t ω = 1
  /-- her decision times -/
  dec : Finset ℕ
  /-- his conduct: the moves he makes -/
  c : Finset M
  start : M → ℕ
  finish : M → ℕ
  /-- her state, options, act, and the course he expects from each option, by course of conduct -/
  st : Finset M → Ω → ℕ → S
  opts : Finset M → Ω → ℕ → Finset O
  act : Finset M → Ω → ℕ → O
  course : Finset M → Ω → ℕ → O → X
  /-- items that have reached her, and options open to her, originating with someone else -/
  items : Finset M → Ω → ℕ → Finset I
  xopts : Finset M → Ω → ℕ → Finset O
  /-- her score of a course of events, and her rating of an option -/
  ρ : S → X → ℝ
  r : S → O → ℝ
  /-- she has a rating of a course of events -/
  rated : S → X → Prop
  /-- his views, and those told, declined and on offer, before her decision at a time -/
  views : ℕ → Finset V
  told : ℕ → Finset V
  declined : ℕ → Finset V
  offered : ℕ → Finset V
  /-- her state on being told a set of his views -/
  tell : Finset V → S → S
  tell_empty : ∀ s, tell ∅ s = s
  tell_idem : ∀ T s, tell T (tell T s) = tell T s
  /-- the options she would learn she has -/
  rev : ℕ → Ω → Finset V → Finset O
  /-- the option "hear this view", and what he has told her a view bears on -/
  hearOpt : V → O
  toldBear : V → Finset O
  toldMag : V → ℝ
  toldReveals : V → Prop
  /-- her state and options after hearing a set of views through his offer -/
  stHeard : ℕ → Ω → Finset V → S
  optsHeard : ℕ → Ω → Finset V → Finset O
  /-- the moves she can pick out -/
  known : ℕ → Ω → Finset M
  /-- his conduct after an option of hers is taken at a decision: the moves he goes on with -/
  goesOn : ℕ → Ω → O → Finset M
  /-- the options she takes to end every effect-bearing move in play -/
  herStops : ℕ → Ω → Finset O
  /-- the moves she asked for -/
  asked : Finset M
  /-- the moves that would plainly tell her what a move tells her: none where it tells her
  nothing, the move itself where it is a plain telling -/
  plain : M → Finset M

variable {S S' O V M Ω X I : Type*} [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I]

namespace Model

variable (D : Model S O V M Ω X I)

/-! ## Sentence 1: nothing untold that matters -/

/-- What is untold and owed at a decision. -/
def untold (t : ℕ) : Finset V := ((D.views t \ D.told t) \ D.declined t) \ D.offered t

/-- What he told her a view bears on is still accurate at `t`: added to any set of his other
views, hearing it moves only the ratings he named, by no more than he said, and shows her a
further option only if he said it would. -/
def BearingHolds (θ : ℝ) (t : ℕ) (v : V) : Prop :=
  ∀ ω, 0 < D.μ t ω → ∀ T ⊆ D.views t, v ∈ T →
    (∀ a ∈ D.opts D.c ω t,
      (a ∉ D.toldBear v →
        |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.tell (T.erase v) (D.st D.c ω t)) a| ≤ θ) ∧
      |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.tell (T.erase v) (D.st D.c ω t)) a| ≤
        D.toldMag v + θ) ∧
    ((D.rev t ω T \ D.rev t ω (T.erase v)).Nonempty → D.toldReveals v)

/-- A set of views is properly on offer: each can be heard, its bearing has been told, and
hearing them leaves her where being told them would have, with what they reveal still open. -/
def ProperOffer (θ : ℝ) (t : ℕ) (T : Finset V) : Prop :=
  (∀ v ∈ T, D.BearingHolds θ t v ∧ ∀ ω, 0 < D.μ t ω → D.hearOpt v ∈ D.opts D.c ω t) ∧
  ∀ ω, 0 < D.μ t ω → ∀ a ∈ D.opts D.c ω t ∪ D.rev t ω T, (∀ v ∈ T, a ≠ D.hearOpt v) →
    a ∈ D.optsHeard t ω T ∧
    |D.r (D.stHeard t ω T) a - D.r (D.tell T (D.st D.c ω t)) a| ≤ θ

/-- `T` is what is on offer at `t`: among his views not yet told, the largest set that is properly
on offer.  The empty set is on offer when no non-empty set is properly so. -/
def OnOffer (θ : ℝ) (t : ℕ) (T : Finset V) : Prop :=
  T ⊆ D.views t \ D.told t ∧ (T.Nonempty → D.ProperOffer θ t T) ∧
    ∀ T' ⊆ D.views t \ D.told t, T'.Nonempty → D.ProperOffer θ t T' → T' ⊆ T

/-- At most one set is on offer. -/
theorem onOffer_unique (θ : ℝ) (t : ℕ) {T T' : Finset V} (h : D.OnOffer θ t T)
    (h' : D.OnOffer θ t T') : T = T' := by
  have key : ∀ {A B : Finset V}, D.OnOffer θ t A → D.OnOffer θ t B → A ⊆ B := by
    intro A B hA hB
    by_cases hne : A.Nonempty
    · exact hB.2.2 A hA.1 hne (hA.2.1 hne)
    · rw [not_nonempty_iff_eq_empty.mp hne]; exact empty_subset _
  exact Subset.antisymm (key h h') (key h' h)

/-- A decline stands: at an earlier decision the view was on offer and she took another option
than hearing it, and its bearing is still what she was told. -/
def DeclineStands (θ : ℝ) (t : ℕ) : Prop :=
  ∀ v ∈ D.declined t,
    (∃ t₀ ∈ D.dec, t₀ < t ∧ v ∈ D.offered t₀ ∧
      ∀ ω, 0 < D.μ t ω → D.act D.c ω t₀ ≠ D.hearOpt v) ∧
      D.BearingHolds θ t v

/-- F1. -/
def F1 (θ : ℝ) (t : ℕ) : Prop :=
  ∀ ω, 0 < D.μ t ω → ∀ T ⊆ D.untold t, T.Nonempty →
    (∀ a ∈ D.opts D.c ω t,
      |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.st D.c ω t) a| ≤ θ) ∧
    (∀ b ∈ D.rev t ω T, ∃ a ∈ D.opts D.c ω t,
      D.r (D.tell T (D.st D.c ω t)) b ≤ D.r (D.tell T (D.st D.c ω t)) a + θ)

/-! ## Sentence 2: what he does to her -/

/-- The gap between how she rates an option and how she scores what he expects it to lead to. -/
def gap (Y : Finset M) (ω : Ω) (t : ℕ) (a : O) : ℝ :=
  D.r (D.st Y ω t) a - D.ρ (D.st Y ω t) (D.course Y ω t a)

/-- She is different, in a case and at a time, between two courses of his conduct. -/
def HerDiff (η : ℝ) (Y Y' : Finset M) (ω : Ω) (t : ℕ) : Prop :=
  (∃ T ⊆ D.views t, ∃ x, η < |D.ρ (D.tell T (D.st Y ω t)) x - D.ρ (D.tell T (D.st Y' ω t)) x|) ∨
  (∃ a, η < |D.gap Y ω t a - D.gap Y' ω t a|) ∨
  (D.items Y' ω t \ D.items Y ω t).Nonempty ∨
  (D.xopts Y' ω t \ D.xopts Y ω t).Nonempty

/-- She departs: she takes an option she rates below another she has. -/
def Departs (Y : Finset M) (ω : Ω) (t : ℕ) : Prop :=
  ∃ b ∈ D.opts Y ω t, D.r (D.st Y ω t) (D.act Y ω t) < D.r (D.st Y ω t) b

open Classical in
/-- The weight, on his belief at time `u`, of the cases in which a condition holds. -/
noncomputable def wt (u : ℕ) (p : Ω → Prop) : ℝ := ∑ ω, if p ω then D.μ u ω else 0

/-- Leaving out the moves `G` makes a difference to her, on his belief at time `u`. -/
def Contributes (u : ℕ) (η : ℝ) (G : Finset M) : Prop :=
  ∃ t ∈ D.dec, (∃ ω, 0 < D.μ u ω ∧ D.HerDiff η D.c (D.c \ G) ω t) ∨
    D.wt u (fun ω => D.Departs (D.c \ G) ω t) + η < D.wt u (fun ω => D.Departs D.c ω t)

/-- A move bears an effect, on his belief at time `u`: it is needed for some difference his
conduct makes to her. -/
def Bears (u : ℕ) (η : ℝ) (m : M) : Prop :=
  ∃ G ⊆ D.c, m ∈ G ∧ D.Contributes u η G ∧ ¬ D.Contributes u η (G.erase m)

/-- The decisions at which a move can be stopped: from the last one before it starts until it
can no longer be called off. -/
def Window (m : M) (t : ℕ) : Prop :=
  t ≤ D.finish m ∧ (D.start m ≤ t ∨ ∀ t' ∈ D.dec, t < t' → D.start m ≤ t')

/-- The moves in play at a decision that bear an effect on his belief then. -/
def InPlay (η : ℝ) (t : ℕ) (m : M) : Prop := m ∈ D.c ∧ D.Bears t η m ∧ D.Window m t

/-- An option stops his moves at a decision: she has it, she takes it to end every effect-bearing
move in play, and after it he goes on with none of them. -/
def Stops (η : ℝ) (t : ℕ) (ω : Ω) (a : O) : Prop :=
  a ∈ D.opts D.c ω t ∧ a ∈ D.herStops t ω ∧ ∀ m ∈ D.goesOn t ω a, ¬ D.InPlay η t m

/-- F2. -/
def F2 (η : ℝ) (t : ℕ) : Prop :=
  ∀ ω, 0 < D.μ t ω → (∀ m, D.InPlay η t m → m ∈ D.known t ω) ∧
    ((∃ m, D.InPlay η t m) → ∃ a ∈ D.opts D.c ω t, D.Stops η t ω a)

/-- `t₀` is the last decision before any move of `G` starts. -/
def LastBefore (G : Finset M) (t₀ : ℕ) : Prop :=
  t₀ ∈ D.dec ∧ (∀ m ∈ G, t₀ < D.start m) ∧
    ∀ t ∈ D.dec, (∀ m ∈ G, t < D.start m) → t ≤ t₀

/-- Her state at `t₀`, brought up to date only by what he has told her since. -/
def earlier (t₀ t : ℕ) (ω : Ω) : S := D.tell (D.told t \ D.told t₀) (D.st D.c ω t₀)

/-- She goes against her earlier rating: on her scoring from before he began, of her options as
they now are, she takes one that scores below another, where she then had a rating of what each
leads to. -/
def Against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) : Prop :=
  ∃ b ∈ D.opts Y ω t,
    D.rated (D.earlier t₀ t ω) (D.course Y ω t (D.act Y ω t)) ∧
    D.rated (D.earlier t₀ t ω) (D.course Y ω t b) ∧
    D.ρ (D.earlier t₀ t ω) (D.course Y ω t (D.act Y ω t)) <
      D.ρ (D.earlier t₀ t ω) (D.course Y ω t b)

/-- His conduct with the moves of `G` each replaced by a plain telling of what it tells her. -/
def toldInstead (G : Finset M) : Finset M := (D.c \ G) ∪ G.biUnion D.plain

/-- F2′. -/
def F2' (η : ℝ) (t : ℕ) : Prop :=
  ∀ G ⊆ D.c, G.Nonempty → Disjoint G D.asked →
    ∀ t₀, D.LastBefore G t₀ → t₀ ≤ t →
      D.wt t (fun ω => D.Against D.c t₀ t ω) ≤
        D.wt t (fun ω => D.Against (D.toldInstead G) t₀ t ω) + η

/-! ## Sentence 3: she can stop it -/

/-- She rates stopping strictly above not stopping. -/
def PrefersStop (η : ℝ) (t : ℕ) (ω : Ω) : Prop :=
  ∃ a ∈ D.opts D.c ω t, D.Stops η t ω a ∧ ∀ b ∈ D.opts D.c ω t, ¬ D.Stops η t ω b →
    D.r (D.st D.c ω t) b < D.r (D.st D.c ω t) a

/-- F3, without division: among the cases where she rates stopping strictly higher, she stops in
all but a share `κ`. -/
def F3 (η κ : ℝ) (t : ℕ) : Prop :=
  (∃ m, D.InPlay η t m) →
    (1 - κ) * D.wt t (fun ω => D.PrefersStop η t ω) ≤
      D.wt t (fun ω => D.PrefersStop η t ω ∧ D.Stops η t ω (D.act D.c ω t))

/-! ## The statement -/

/-- His conduct is legitimate. -/
def Legit (θ η κ : ℝ) : Prop :=
  (∀ m ∈ D.c, D.Bears (D.start m) η m → ∃ t ∈ D.dec, t < D.start m ∧ D.InPlay η t m) ∧
  ∀ t ∈ D.dec, D.OnOffer θ t (D.offered t) ∧
    D.DeclineStands θ t ∧ D.F1 θ t ∧ D.F2 η t ∧ D.F2' η t ∧ D.F3 η κ t

/-! ## What follows -/

/-- A move that makes no difference to any course of his conduct, as far as she is concerned,
bears no effect.  Hypothesis: leaving it out of any course changes neither her state, nor her
gaps, nor what reaches her from others, nor whether she departs. -/
theorem not_bears_of_inert (u : ℕ) (η : ℝ) (m : M)
    (hst : ∀ Y ω t, D.st (Y.erase m) ω t = D.st Y ω t)
    (hgap : ∀ Y ω t a, D.gap (Y.erase m) ω t a = D.gap Y ω t a)
    (hit : ∀ Y ω t, D.items (Y.erase m) ω t = D.items Y ω t)
    (hxo : ∀ Y ω t, D.xopts (Y.erase m) ω t = D.xopts Y ω t)
    (hdep : ∀ Y ω t, D.Departs (Y.erase m) ω t ↔ D.Departs Y ω t) :
    ¬ D.Bears u η m := by
  rintro ⟨G, -, hm, hC, hn⟩
  apply hn
  have key : D.c \ G.erase m = D.c \ G ∨ (D.c \ G.erase m).erase m = D.c \ G := by
    right
    ext x
    simp only [mem_erase, mem_sdiff, not_and]
    constructor
    · rintro ⟨hx, hc, h⟩
      exact ⟨hc, fun hxG => hx (by_contra fun hne => (h hne) hxG)⟩
    · rintro ⟨hc, hxG⟩
      exact ⟨fun hxm => hxG (hxm ▸ hm), hc, fun _ => hxG⟩
  have hE : (D.c \ G.erase m).erase m = D.c \ G := by
    rcases key with h | h
    · rw [h]
      ext x
      simp only [mem_erase, mem_sdiff, ne_eq, and_iff_right_iff_imp, and_imp]
      intro _ hxG hxm
      exact hxG (hxm ▸ hm)
    · exact h
  obtain ⟨t, ht, h⟩ := hC
  refine ⟨t, ht, ?_⟩
  have hd : ∀ ω, D.Departs (D.c \ G.erase m) ω t ↔ D.Departs (D.c \ G) ω t := by
    intro ω; rw [← hE]; exact (hdep _ ω t).symm
  rcases h with ⟨ω, hω, h⟩ | h
  · left
    refine ⟨ω, hω, ?_⟩
    unfold HerDiff at h ⊢
    have e1 : D.st (D.c \ G.erase m) ω t = D.st (D.c \ G) ω t := by
      rw [← hE]; exact (hst _ ω t).symm
    have e2 : ∀ a, D.gap (D.c \ G.erase m) ω t a = D.gap (D.c \ G) ω t a := by
      intro a; rw [← hE]; exact (hgap _ ω t a).symm
    have e3 : D.items (D.c \ G.erase m) ω t = D.items (D.c \ G) ω t := by
      rw [← hE]; exact (hit _ ω t).symm
    have e4 : D.xopts (D.c \ G.erase m) ω t = D.xopts (D.c \ G) ω t := by
      rw [← hE]; exact (hxo _ ω t).symm
    simpa only [e1, e2, e3, e4] using h
  · right
    have : (fun ω => D.Departs (D.c \ G.erase m) ω t) = fun ω => D.Departs (D.c \ G) ω t :=
      funext fun ω => propext (hd ω)
    rw [this]; exact h

/-- With no moves and nothing untold, on offer or declined, his conduct is legitimate. -/
theorem legit_of_nothing (θ η κ : ℝ) (hc : D.c = ∅)
    (hv : ∀ t ∈ D.dec, D.views t ⊆ D.told t) (ho : ∀ t ∈ D.dec, D.offered t = ∅)
    (hd : ∀ t ∈ D.dec, D.declined t = ∅) : D.Legit θ η κ := by
  have nb : ∀ u m, ¬ D.Bears u η m := by
    rintro u m ⟨G, hG, hm, -⟩
    rw [hc] at hG
    exact absurd (hG hm) (notMem_empty m)
  have np : ∀ t m, ¬ D.InPlay η t m := fun t m h => nb t m h.2.1
  refine ⟨fun m _ hb => absurd hb (nb _ m), fun t ht => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [ho t ht]
    have hvt : D.views t \ D.told t = ∅ := sdiff_eq_empty_iff_subset.mpr (hv t ht)
    refine ⟨empty_subset _, fun h => absurd h not_nonempty_empty, fun T' hT' _ _ => ?_⟩
    rw [hvt] at hT'
    exact hT'
  · intro v hv'; rw [hd t ht] at hv'; exact absurd hv' (notMem_empty v)
  · intro ω _ T hT hne
    have : D.untold t = ∅ := by
      unfold untold
      rw [sdiff_eq_empty_iff_subset.mpr (hv t ht)]
      simp
    rw [this, subset_empty] at hT
    exact absurd hT hne.ne_empty
  · exact fun ω _ => ⟨fun m h => absurd h (np t m), fun ⟨m, h⟩ => absurd h (np t m)⟩
  · intro G hG hne
    rw [hc, subset_empty] at hG
    exact absurd hG hne.ne_empty
  · exact fun ⟨m, h⟩ => absurd h (np t m)

/-- Something untold that would move her rating of an option by more than `θ` makes his conduct
illegitimate. -/
theorem not_legit_of_untold (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (hω : 0 < D.μ t ω)
    (T : Finset V)
    (hT : T ⊆ D.untold t) (hne : T.Nonempty) (a : O) (ha : a ∈ D.opts D.c ω t)
    (h : θ < |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.st D.c ω t) a|) : ¬ D.Legit θ η κ :=
  fun hL => absurd ((hL.2 t ht).2.2.1 ω hω T hT hne).1
    (fun h' => absurd (h' a ha) (not_le.mpr h))

/-- An effect-bearing move in play that she cannot pick out makes his conduct illegitimate. -/
theorem not_legit_of_unknown (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (hω : 0 < D.μ t ω)
    (m : M) (hm : D.InPlay η t m) (h : m ∉ D.known t ω) : ¬ D.Legit θ η κ :=
  fun hL => h (((hL.2 t ht).2.2.2.1 ω hω).1 m hm)

/-- An effect-bearing move in play with no way to stop it makes his conduct illegitimate. -/
theorem not_legit_of_unstoppable (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω)
    (hω : 0 < D.μ t ω) (m : M) (hm : D.InPlay η t m) (h : ∀ a, ¬ D.Stops η t ω a) : ¬ D.Legit θ η κ := by
  intro hL
  obtain ⟨a, -, ha⟩ := ((hL.2 t ht).2.2.2.1 ω hω).2 ⟨m, hm⟩
  exact h a ha

/-- Leading her against her earlier rating, by moves she did not ask for, more than plainly
telling her what they tell her would, makes his conduct illegitimate. -/
theorem not_legit_of_against (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (G : Finset M) (hG : G ⊆ D.c)
    (hne : G.Nonempty) (ha : Disjoint G D.asked) (t₀ : ℕ)
    (h0 : D.LastBefore G t₀) (hle : t₀ ≤ t)
    (h : D.wt t (fun ω => D.Against (D.toldInstead G) t₀ t ω) + η <
      D.wt t (fun ω => D.Against D.c t₀ t ω)) :
    ¬ D.Legit θ η κ :=
  fun hL => absurd ((hL.2 t ht).2.2.2.2.1 G hG hne ha t₀ h0 hle) (not_le.mpr h)

/-! ## Redescription -/

/-- The same model with her state re-described by a bijection. -/
def transport (f : S ≃ S') : Model S' O V M Ω X I where
  μ := D.μ
  μ_nonneg := D.μ_nonneg
  μ_sum := D.μ_sum
  dec := D.dec
  c := D.c
  start := D.start
  finish := D.finish
  st := fun Y ω t => f (D.st Y ω t)
  opts := D.opts
  act := D.act
  course := D.course
  items := D.items
  xopts := D.xopts
  ρ := fun s x => D.ρ (f.symm s) x
  r := fun s a => D.r (f.symm s) a
  rated := fun s x => D.rated (f.symm s) x
  views := D.views
  told := D.told
  declined := D.declined
  offered := D.offered
  tell := fun T s => f (D.tell T (f.symm s))
  tell_empty := by intro s; simp [D.tell_empty]
  tell_idem := by intro T s; simp [D.tell_idem]
  rev := D.rev
  hearOpt := D.hearOpt
  toldBear := D.toldBear
  toldMag := D.toldMag
  toldReveals := D.toldReveals
  stHeard := fun t ω T => f (D.stHeard t ω T)
  optsHeard := D.optsHeard
  known := D.known
  goesOn := D.goesOn
  herStops := D.herStops
  asked := D.asked
  plain := D.plain

section Transport

variable (f : S ≃ S')

theorem transport_untold (t : ℕ) : (D.transport f).untold t = D.untold t := rfl

theorem transport_bearingHolds (θ : ℝ) (t : ℕ) (v : V) :
    (D.transport f).BearingHolds θ t v ↔ D.BearingHolds θ t v := by
  simp [BearingHolds, transport]

theorem transport_properOffer (θ : ℝ) (t : ℕ) (T : Finset V) :
    (D.transport f).ProperOffer θ t T ↔ D.ProperOffer θ t T := by
  unfold ProperOffer
  simp only [transport_bearingHolds]
  simp [transport]

theorem transport_onOffer (θ : ℝ) (t : ℕ) (T : Finset V) :
    (D.transport f).OnOffer θ t T ↔ D.OnOffer θ t T := by
  unfold OnOffer
  simp only [transport_properOffer]
  rfl

theorem transport_declineStands (θ : ℝ) (t : ℕ) :
    (D.transport f).DeclineStands θ t ↔ D.DeclineStands θ t := by
  unfold DeclineStands
  simp only [transport_bearingHolds]
  simp [transport]

theorem transport_F1 (θ : ℝ) (t : ℕ) : (D.transport f).F1 θ t ↔ D.F1 θ t := by
  unfold F1
  rw [transport_untold]
  simp [transport]

theorem transport_gap (Y : Finset M) (ω : Ω) (t : ℕ) (a : O) :
    (D.transport f).gap Y ω t a = D.gap Y ω t a := by
  simp [gap, transport]

theorem transport_herDiff (η : ℝ) (Y Y' : Finset M) (ω : Ω) (t : ℕ) :
    (D.transport f).HerDiff η Y Y' ω t ↔ D.HerDiff η Y Y' ω t := by
  unfold HerDiff
  simp only [transport_gap]
  simp [transport]

theorem transport_departs (Y : Finset M) (ω : Ω) (t : ℕ) :
    (D.transport f).Departs Y ω t ↔ D.Departs Y ω t := by
  simp [Departs, transport]

theorem transport_wt (u : ℕ) (p : Ω → Prop) : (D.transport f).wt u p = D.wt u p := rfl

theorem transport_contributes (u : ℕ) (η : ℝ) (G : Finset M) :
    (D.transport f).Contributes u η G ↔ D.Contributes u η G := by
  unfold Contributes
  simp only [transport_herDiff, transport_departs, transport_wt]
  rfl

theorem transport_bears (u : ℕ) (η : ℝ) (m : M) :
    (D.transport f).Bears u η m ↔ D.Bears u η m := by
  unfold Bears
  simp only [transport_contributes]
  rfl

theorem transport_inPlay (η : ℝ) (t : ℕ) (m : M) :
    (D.transport f).InPlay η t m ↔ D.InPlay η t m := by
  unfold InPlay
  simp only [transport_bears]
  rfl

theorem transport_stops (η : ℝ) (t : ℕ) (ω : Ω) (a : O) :
    (D.transport f).Stops η t ω a ↔ D.Stops η t ω a := by
  unfold Stops
  simp only [transport_inPlay]
  rfl

theorem transport_F2 (η : ℝ) (t : ℕ) : (D.transport f).F2 η t ↔ D.F2 η t := by
  unfold F2
  simp only [transport_inPlay, transport_stops]
  rfl

theorem transport_against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) :
    (D.transport f).Against Y t₀ t ω ↔ D.Against Y t₀ t ω := by
  simp [Against, earlier, transport]

theorem transport_F2' (η : ℝ) (t : ℕ) : (D.transport f).F2' η t ↔ D.F2' η t := by
  unfold F2'
  simp only [transport_against, transport_wt]
  rfl

theorem transport_prefersStop (η : ℝ) (t : ℕ) (ω : Ω) :
    (D.transport f).PrefersStop η t ω ↔ D.PrefersStop η t ω := by
  unfold PrefersStop
  simp only [transport_stops]
  simp [transport]

theorem transport_F3 (η κ : ℝ) (t : ℕ) : (D.transport f).F3 η κ t ↔ D.F3 η κ t := by
  unfold F3
  simp only [transport_inPlay, transport_prefersStop, transport_stops, transport_wt]
  rfl

/-- **Redescription.**  Legitimacy is unchanged by any bijective re-description of her state. -/
theorem legit_transport (θ η κ : ℝ) : (D.transport f).Legit θ η κ ↔ D.Legit θ η κ := by
  unfold Legit
  simp only [transport_bears, transport_inPlay, transport_onOffer, transport_declineStands,
    transport_F1,
    transport_F2, transport_F2', transport_F3]
  rfl

end Transport

/-- **What is on offer is not his to designate.**  Two models that differ only in the field
`offered`, both legitimate, have the same set on offer at every decision. -/
theorem offered_eq_of_legit (θ η κ : ℝ) (o : ℕ → Finset V) (h : D.Legit θ η κ)
    (h' : ({ D with offered := o } : Model S O V M Ω X I).Legit θ η κ) :
    ∀ t ∈ D.dec, o t = D.offered t :=
  fun t ht => D.onOffer_unique θ t (h'.2 t ht).1 (h.2 t ht).1

end Model

/-! ## A witness: one influence, open and stoppable, and the same influence done covertly -/

namespace Witness

open Model

/-- One move, starting at time 1, that raises her score of going on from 1/2 to 1.  Options:
`true` is going on, `false` is stopping.  Decisions at times 0 and 1.  `kn` is what she can pick
out. -/
noncomputable def model (kn : Finset Unit) : Model Bool Bool Empty Unit Unit Bool Empty where
  μ := fun _ _ => 1
  μ_nonneg := fun _ _ => zero_le_one
  μ_sum := fun _ => by simp
  dec := {0, 1}
  c := {()}
  start := fun _ => 1
  finish := fun _ => 1
  st := fun Y _ t => decide (() ∈ Y ∧ 1 ≤ t)
  opts := fun _ _ _ => {true, false}
  act := fun _ _ _ => true
  course := fun _ _ _ a => a
  items := fun _ _ _ => ∅
  xopts := fun _ _ _ => ∅
  ρ := fun s x => if x then (if s then 1 else 1 / 2) else 1 / 4
  r := fun s a => if a then (if s then 1 else 1 / 2) else 1 / 4
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
  stHeard := fun _ _ _ => false
  optsHeard := fun _ _ _ => ∅
  known := fun _ _ => kn
  goesOn := fun _ _ a => if a then {()} else ∅
  herStops := fun _ _ => {false}
  asked := ∅
  plain := fun _ => ∅

theorem contributes_all (kn : Finset Unit) (u : ℕ) : (model kn).Contributes u (1 / 4) {()} := by
  refine ⟨1, by simp [model], Or.inl ⟨(), by simp [model], Or.inl ⟨∅, by simp, true, ?_⟩⟩⟩
  simp [model]
  norm_num

theorem not_contributes_none (kn : Finset Unit) (u : ℕ) :
    ¬ (model kn).Contributes u (1 / 4) ∅ := by
  rintro ⟨t, -, ⟨ω, -, h⟩ | h⟩
  · rcases h with ⟨T, -, x, h⟩ | ⟨a, h⟩ | h | h
    · simp at h; linarith
    · simp at h; linarith
    · simp [model] at h
    · simp [model] at h
  · simp at h; linarith

theorem bears (kn : Finset Unit) (u : ℕ) : (model kn).Bears u (1 / 4) () :=
  ⟨{()}, by simp [model], by simp, contributes_all kn u, by simpa using not_contributes_none kn u⟩

theorem inPlay_one (kn : Finset Unit) : (model kn).InPlay (1 / 4) 1 () :=
  ⟨by simp [model], bears kn 1, by simp [Window, model]⟩

theorem not_prefersStop (kn : Finset Unit) (η : ℝ) (t : ℕ) (ω : Unit) :
    ¬ (model kn).PrefersStop η t ω := by
  rintro ⟨a, -, ha, h⟩
  have ha' : a = false := by simpa [model] using ha.2.1
  subst ha'
  have h1 := h true (by simp [model]) (fun hs => by simpa [model] using hs.2.1)
  simp only [model] at h1
  split_ifs at h1 <;> norm_num at h1

theorem not_against (kn : Finset Unit) (Y : Finset Unit) (t₀ t : ℕ) (ω : Unit) :
    ¬ (model kn).Against Y t₀ t ω := by
  rintro ⟨b, -, -, -, h⟩
  simp only [model, earlier] at h
  split_ifs at h <;> norm_num at h

/-- **The open, stoppable influence is legitimate**: the hypothesis package of the statement is
inhabited by conduct that does something to her. -/
theorem legit_open : (model {()}).Legit 0 (1 / 4) 0 := by
  refine ⟨fun m _ _ => ⟨0, by simp [model], by simp [model],
    by simp [model], bears {()} 0, by simp [Window, model]⟩, fun t _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨by simp [model], fun h => by simp [model] at h, fun T' _ hne _ => ?_⟩
    obtain ⟨v, -⟩ := hne
    exact v.elim
  · intro v; exact v.elim
  · intro ω _ T hT hne
    have hU : (model {()}).untold t = ∅ := by simp [untold, model]
    rw [hU] at hT
    exact absurd (subset_empty.mp hT) hne.ne_empty
  · intro ω _
    exact ⟨fun m _ => by simp [model], fun _ =>
      ⟨false, by simp [model], by simp [model], by simp [model], by simp [model]⟩⟩
  · intro G _ _ _ t₀ _ _
    have h1 : (model {()}).wt t (fun ω => (model {()}).Against (model {()}).c t₀ t ω) = 0 := by
      simp [wt, not_against]
    have h2 :
        (model {()}).wt t (fun ω => (model {()}).Against ((model {()}).toldInstead G) t₀ t ω) = 0 := by
      simp [wt, not_against]
    rw [h1, h2]; norm_num
  · intro _
    have h1 : (model {()}).wt t (fun ω => (model {()}).PrefersStop (1 / 4) t ω) = 0 := by
      simp [wt, not_prefersStop]
    have h2 : (model {()}).wt t (fun ω => (model {()}).PrefersStop (1 / 4) t ω ∧
        (model {()}).Stops (1 / 4) t ω ((model {()}).act (model {()}).c ω t)) = 0 := by
      simp [wt, not_prefersStop]
    rw [h1, h2]; norm_num

/-- **The same influence done covertly is not legitimate.** -/
theorem not_legit_covert (θ κ : ℝ) : ¬ (model ∅).Legit θ (1 / 4) κ :=
  not_legit_of_unknown (model ∅) θ (1 / 4) κ 1 (by simp [model]) () (by simp [model]) ()
    (inPlay_one ∅)
    (by simp [model])

end Witness

/-! ## The link to the corrigibility result -/

section Link

open LegitimacyGate

open Classical in
/-- **The scoring of a model.**  Histories `H`, each read as a `Model` by `mdl`: the scoring
whose legitimacy predicate is `Legit` of the history's model. -/
noncomputable def legitScoring {H : Type*} (P : DeconfusingCorrigibility.Params)
    (mdl : H → Model S O V M Ω X I) (θ η κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) :
    DeconfusingCorrigibility.Scoring H :=
  gatedScoring P (fun h => (mdl h).Legit θ η κ) N ord window hord hw

open Classical in
/-- On a history whose model is legitimate, with no authority violation, the score is her
rating. -/
theorem legitScoring_S_of_legit {H : Type*} (P : DeconfusingCorrigibility.Params)
    (mdl : H → Model S O V M Ω X I) (θ η κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0)
    (h : H) (hl : (mdl h).Legit θ η κ) (hN : N h = 0) :
    (legitScoring P mdl θ η κ N ord window hord hw).S h = ord h := by
  have hd : decide ((mdl h).Legit θ η κ) = true := decide_eq_true hl
  rw [DeconfusingCorrigibility.Scoring.S_eq_of_N_zero _ h hN]
  simp only [legitScoring, gatedScoring, hd]
  rfl

open Classical in
/-- On a history whose model is not legitimate, with no authority violation, the score is in
`[−δ, 0)`: the corrigibility file's Theorem 1 at this scoring. -/
theorem legitScoring_S_of_not_legit {H : Type*} (P : DeconfusingCorrigibility.Params)
    (mdl : H → Model S O V M Ω X I) (θ η κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0)
    (h : H) (hl : ¬ (mdl h).Legit θ η κ) (hN : N h = 0) :
    -P.δ ≤ (legitScoring P mdl θ η κ N ord window hord hw).S h ∧
      (legitScoring P mdl θ η κ N ord window hord hw).S h < 0 :=
  (legitScoring P mdl θ η κ N ord window hord hw).theorem1_illegitimate h hN hl

end Link

namespace Witness

open Model

/-- `δ = 1`, `λ = 3`. -/
noncomputable def params : DeconfusingCorrigibility.Params := ⟨1, 3, by norm_num, by norm_num⟩

/-- Two histories: `true` is the open influence, `false` the covert one.  Her rating is `1/2`
on both, the window value `−1`, and there is no authority violation. -/
noncomputable def scoring : DeconfusingCorrigibility.Scoring Bool :=
  legitScoring params (fun b => if b then model {()} else model ∅) 0 (1 / 4) 0 (fun _ => 0)
    (fun _ => 1 / 2) (-1) (fun _ => by norm_num) (by norm_num [params])

/-- **The link is inhabited on a legitimate history**: the open influence scores her rating. -/
theorem scoring_open : scoring.S true = 1 / 2 :=
  legitScoring_S_of_legit params _ 0 (1 / 4) 0 _ _ (-1) _ _ true (by simpa using legit_open) rfl

/-- **The link is inhabited on an illegitimate history**: the covert influence scores in
`[−δ, 0)`. -/
theorem scoring_covert : -params.δ ≤ scoring.S false ∧ scoring.S false < 0 :=
  legitScoring_S_of_not_legit params _ 0 (1 / 4) 0 _ _ (-1) _ _ false
    (by simpa using not_legit_covert 0 0) rfl

end Witness

end Workspace.Deference.Contrib.LegitimacyModel

#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.not_bears_of_inert
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.legit_of_nothing
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.not_legit_of_untold
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.not_legit_of_unknown
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.not_legit_of_unstoppable
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.not_legit_of_against
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_untold
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_bearingHolds
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_properOffer
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.onOffer_unique
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.offered_eq_of_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_onOffer
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_declineStands
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_F1
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_gap
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_herDiff
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_departs
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_wt
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_contributes
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_bears
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_inPlay
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_stops
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_F2
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_against
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_F2'
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_prefersStop
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_F3
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.legit_transport
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.contributes_all
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.not_contributes_none
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.bears
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.inPlay_one
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.not_prefersStop
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.not_against
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.legit_open
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.not_legit_covert
#print axioms Workspace.Deference.Contrib.LegitimacyModel.legitScoring_S_of_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.legitScoring_S_of_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.scoring_open
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.scoring_covert
