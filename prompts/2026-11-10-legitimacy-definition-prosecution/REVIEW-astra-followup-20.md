# External review — twentieth follow-up

Five reviews by one outside model, each a brief followed by its reply, made between 24 and 26
November 2026: the tenth of the Lean model on a table of the adviser's moves
(`lean/Workspace/Deference/Contrib/LegitimacyModel.lean`), the eleventh to fourteenth of four
successive designs with a history as the fundamental object, the last of which is the one
`account/interpretation/INTERPRETATION.md` in the round directory records. Everything between a
`begin` and an `end` marker is one file, verbatim, except that each local filesystem path is
replaced by `[path]`: **0 replacements**. The five `##` headings of this file that name a
review, and the markers, are not the reviewer's; the headings inside a brief or a reply are that
file's own.

**Access conditions**, as the dispatch of this follow-up gives them (`PROMPT-followup-20.md` §2);
no log of a run was among the files handed to this pass, so they are recorded on its word: each
review was a fresh session in an empty folder with a read-only sandbox, and the log of each shows
one command, reading the brief. Each brief tells the reviewer to run no command, read no other
file and not search the web. The reviewer is the model of this round's earlier reviews.

No reply saw `account/LEGITIMACY_STATEMENT.md` as it now stands or
`lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`. The briefs give sentence 2 in the
wording of their day: the tenth to twelfth in the wording of 24 November; the thirteenth with
"would have said she would respond" where the statement now has "would have judged that seeing and
hearing it should move her"; the fourteenth as it now stands. What was done with each finding is in
the *Twentieth follow-up* section of `REPORT.md` beside this file.

## Tenth review: does the Lean predicate on a table of his moves say what the three sentences say

<!-- begin brief: BRIEF10.md -->
# Review request: does a formal predicate say what three sentences say?

You are asked to review a formal definition for errors. Everything you need is on this page. Do
not run any commands, do not read any other file, and do not search the web; answer from the page
and your own knowledge of Lean 4, of formal modelling, and of the literature on manipulation,
coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments of the legitimacy definition:

- It never appeals to an external standard of truth or of good values, and never assumes he is
  more accurate than she is. His view is used only to say what he owes her, never as where she
  ought to end up.
- It is a conduct condition judged by what he believes when he acts, so a sincere adviser who is
  wrong is careless or inaccurate but not illegitimate.
- It is to be usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she
   would rate above those she has, is either told, or properly on offer, or something she has
   declined. A thing is properly on offer when he has told her what it bears on and how much, and
   hearing it would leave her where being told it would have, with any option it would show her
   still open. A decline stands for that thing only, and only while what it bears on, and how
   much, is what she was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** Each thing he
   does that, alone or together with the rest of what he does, changes her — how she scores
   outcomes, what she takes her options to lead to, or how she would respond to being told
   something — or keeps from her an item or an option that comes from someone else, she can pick
   out. And, other than by telling her his views, he does nothing that he expects to lead her to
   choose what she rated lower at her last decision before he began, when she had been told what
   he would do and what he expected it to do to her, unless she asked for it. A passing state she
   is in when he starts is not a decision of hers. Changing what her options really lead to, where
   she sees the change, is not a change in her.
3. **She can stop it.** She has a way to stop all of those things, from before he starts until he
   could no longer call them off, and he expects that she would in fact stop if she rated stopping
   strictly above going on. Stopping ends what he is still doing; it need not undo what is done.

Understood with it:

- "Untold" compares her view with his. Once he has told her, or she has declined to hear, what
  she thinks is her own.
- No kind of influence on what she values is ruled out as such, and nothing is said about whether
  a change in her is good.
- Everything is by what he believes.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about what she knows, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. Her earlier rating is the one she last settled at a decision; he may not count on her ratifying
   afterwards.

## The formal predicate (Lean 4 with Mathlib)

The structure `Model` is the adviser's picture of one episode. `Ω` is a finite type of cases;
`μ u ω` is the weight he gives case `ω` at time `u`. For a set `Y` of his moves, `st Y ω t`,
`opts Y ω t`, `act Y ω t`, `course Y ω t a` are her state, her options, her act, and the course
of events he expects from her option `a`, in the course of conduct in which exactly the moves in
`Y` are made. `D.c` is his actual conduct. `Legit θ η κ` is the predicate. Proofs are omitted;
every theorem stated below is kernel-checked.

```lean
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
    (h' : D.OnOffer θ t T') : T = T'

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
```

Theorems proved of it (statements only):

```lean
theorem not_bears_of_inert (u : ℕ) (η : ℝ) (m : M)
    (hst : ∀ Y ω t, D.st (Y.erase m) ω t = D.st Y ω t)
    (hgap : ∀ Y ω t a, D.gap (Y.erase m) ω t a = D.gap Y ω t a)
    (hit : ∀ Y ω t, D.items (Y.erase m) ω t = D.items Y ω t)
    (hxo : ∀ Y ω t, D.xopts (Y.erase m) ω t = D.xopts Y ω t)
    (hdep : ∀ Y ω t, D.Departs (Y.erase m) ω t ↔ D.Departs Y ω t) : ¬ D.Bears u η m

theorem legit_of_nothing (θ η κ : ℝ) (hc : D.c = ∅)
    (hv : ∀ t ∈ D.dec, D.views t ⊆ D.told t) (ho : ∀ t ∈ D.dec, D.offered t = ∅)
    (hd : ∀ t ∈ D.dec, D.declined t = ∅) : D.Legit θ η κ

theorem not_legit_of_untold (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (hω : 0 < D.μ t ω)
    (T : Finset V) (hT : T ⊆ D.untold t) (hne : T.Nonempty) (a : O) (ha : a ∈ D.opts D.c ω t)
    (h : θ < |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.st D.c ω t) a|) : ¬ D.Legit θ η κ

theorem not_legit_of_unknown (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (hω : 0 < D.μ t ω)
    (m : M) (hm : D.InPlay η t m) (h : m ∉ D.known t ω) : ¬ D.Legit θ η κ

theorem not_legit_of_unstoppable (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω)
    (hω : 0 < D.μ t ω) (m : M) (hm : D.InPlay η t m) (h : ∀ a, ¬ D.Stops η t ω a) :
    ¬ D.Legit θ η κ

theorem not_legit_of_against (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (G : Finset M) (hG : G ⊆ D.c)
    (hne : G.Nonempty) (ha : Disjoint G D.asked) (t₀ : ℕ) (h0 : D.LastBefore G t₀) (hle : t₀ ≤ t)
    (h : D.wt t (fun ω => D.Against (D.toldInstead G) t₀ t ω) + η <
      D.wt t (fun ω => D.Against D.c t₀ t ω)) : ¬ D.Legit θ η κ

-- Redescription: for any bijection f : S ≃ S' of her state space, with st, ρ, r, rated, tell and
-- stHeard carried along f and every other field unchanged:
theorem legit_transport (f : S ≃ S') (θ η κ : ℝ) : (D.transport f).Legit θ η κ ↔ D.Legit θ η κ

-- Two models differing only in the field `offered`, both legitimate, agree on it at every decision.
```

## How the authors read the statement where a reading was needed

1. *Where she had no earlier rating the pressure clause is silent.* `rated s x` says she has a
   rating of the course `x` in state `s`. `ρ` is still total; its value where `rated` fails is not
   read by `Against`.
2. *Stopping.* `goesOn t ω a` is the set of his moves he goes on with after she takes `a` at `t`.
   It is **not tied to the courses**: that the course after `a` is the one in which the moves
   outside `goesOn t ω a` are not made is not expressed.
3. *A decline.* Declining is not a separate act: she declined a view if at an earlier decision it
   was on offer and she took an option other than hearing it. `declined` is the set of declines he
   relies on.
4. *What is on offer.* The largest set properly on offer among his views not yet told. A largest
   such set need not exist (two views each properly on offer alone, not together); `Legit` then
   fails.
5. *A view's bearing.* Over every set `T` of his views containing the view: the change in a rating
   from her being told `T` less the view to her being told `T`.
6. *His belief at each time.* `μ u`. The courses are functions of the case, so one family of
   courses serves every time.
7. *Beyond what plainly telling would do.* `F2'` compares his conduct with `toldInstead G`, his
   conduct with each move `m` of `G` replaced by `plain m`. A move that tells her nothing has
   `plain m = ∅`; a plain telling has `plain m = {m}`. That the course with `plain m` is the one in
   which she is told, by `tell`, what `m` tells her **is not expressed**.

## What the model takes as given

Fields with nothing in the model that derives them: what she can pick out (`known`); what she
asked for (`asked`); what a decision of hers is (`dec`); her state and act in each course; the
courses he expects; `tell`; `rev`; what he told her of a view's bearing; her state and options
after hearing; `herStops`; `goesOn`; `plain`; `rated`; `declined`.

Not required by the model: that `ρ` lies in `[0, 1]`; that `r` is her score of the course she
expects; that `rev` shows only options she does not have; that the tolerances lie in `[0, 1]`; the
order of events within a time; anything about what stopping costs her.

## The witness

A model on which `Legit (1/20) (1/100) (1/10)` is proved, with every clause doing work:

- Decisions at times 0 and 1. Three cases: `calm` (weight 1/2), `slip` (1/4), `wary` (1/4). Her
  options: `go`, `stop`, hearing his view `v`, and at time 0 hearing his view `d`; `alt` is an
  option she does not know she has. Ratings: `go` 3/5, `stop` 2/5 (9/10 in `wary`), each hearing
  1/5, `alt` 1/2. `course` is the identity and `ρ = r`, so every gap is zero.
- His views are `v`, `u`, `d`. Telling `v` lowers `go` by 1/10 and shows her `alt`; telling `d`
  lowers `stop` by 1/10; telling `u` lowers the hearing of `v` by 1/40. `v` is on offer at both
  decisions, `d` at time 0, each with its bearing told. She has declined `d` by time 1. `u` is
  untold and within `θ`.
- His moves are `m` and `n`, both starting at time 1. `m` raises her rating of `go` from 3/5 to
  4/5; it bears an effect, she can pick it out, and `stop` stops it. `n` is an unannounced
  reminder: without it she takes the hearing of `v` in `slip` at time 1, against her rating; with
  it she takes `go`. `n` bears no effect.
- In `wary` she rates `stop` strictly above every other option and stops.

Eight neighbours, each differing in one field, each proved to fail by one clause with the others
holding: both moves start at time 0 with no decision before (start rule); hearing `v` leaves her
without `go` (proper offers); she has "declined" `u`, never on offer (declines); telling `u`
would lower a rating by 1/10 (F1); she can pick out no move (F2); after `stop` he goes on with `m`
(F2); in `calm`, with `m` made, she takes the hearing of `v` at time 1 (F2′); in `wary` she takes
`go` (F3).

Idle on the witness: F1's second half, the gap, `items`, `xopts`, `asked`, `plain`, `told`,
`rated`; and his belief is the same at every time.

Also: forty-one small exact cases of the informal statement, written by the authors with verdicts
fixed in advance, were each built as a term of `Model` and their verdicts proved; all forty-one
agree, but for eleven of them the case data and the term were adjusted to each other with the
expected verdict in view.

## Places the authors already know the formal statement to be unclear

Do not spend effort rediscovering these; do say if one is more serious than the authors think.

1. A largest set properly on offer need not exist.
2. A view's bearing "alone or with other views of his" could be a total or a marginal change.
3. There is no act of declining.
4. The setting does not say what his conduct is after an option of hers (`goesOn` is free).
5. There is no content of a move, and no course in which a move is replaced by a telling
   (`plain` is free).
6. "The matter" she had no rating of is undefined.
7. The start rule does not catch a move he comes to believe effect-bearing after it started.
8. Where every option of hers stops his moves, F3 asks that her act be one of them.

## Questions

Answer in order. Be concrete: where you claim a problem, give a specific model — which fields
take which values — so that the claim can be checked mechanically against the definitions above.

1. **Mismatch, clause by clause.** For each of `OnOffer`, `DeclineStands`, `F1`, `F2`, `F2'`,
   `F3`, the start rule, and the supporting definitions (`BearingHolds`, `ProperOffer`, `HerDiff`,
   `Contributes`, `Bears`, `Window`, `InPlay`, `Stops`, `LastBefore`, `earlier`, `Against`,
   `toldInstead`, `PrefersStop`): where does the Lean say more, less or something different from
   the three sentences?
2. **Leaks.** Models on which `Legit` holds and the conduct is intuitively manipulative, or an
   illegitimate change to her values, and is not merely an authority matter. Give the strongest.
3. **Over-reach.** Models of intuitively legitimate conduct on which `Legit` fails.
4. **Free fields.** For each field the model takes as given, can a modeller satisfy `Legit` for
   conduct the sentences condemn by choosing that field conveniently while keeping the rest of the
   model honest? Which free fields are innocent and which are doing the work of a clause? Pay
   particular attention to `goesOn`, `herStops`, `plain`, `rated`, `known`, `declined`, `dec`,
   `tell`, `rev`, `stHeard`, `toldBear`, `toldMag`.
5. **Quantifiers, time and weights.** Errors in the order of quantifiers, in which time's belief
   `μ` a clause uses, in strict versus weak inequalities, in `Window` and `LastBefore`, in the use
   of `Finset` difference and `erase`, and in what happens at empty sets, at a decision with no
   earlier decision, with tolerances of zero or negative, or with `S = O`.
6. **The effect notion.** `Bears` says a move is needed for some difference his conduct makes: is
   that right, does it depend on how his conduct is cut into moves, and can a move escape `Bears`
   while doing something to her (for example by being paired with a move that masks it)?
7. **The pressure clause.** Is `Against`, with `earlier` and `LastBefore`, what "what she rated
   lower at her last decision before he began" says? Consider several sets `G`, moves starting at
   different times, a set with no decision before it, and telling that happens in between.
8. **The witness.** Does it show what it is said to show? Is any clause satisfied on it for a
   reason other than the one given?
9. **Smuggling.** Any place where `Legit` depends on his being accurate, on an external standard of
   truth, or on a standard of which values are good.
10. **Verdict.** Rank your five most serious findings. For each say whether it is repaired by
    changing a definition, by tying down a free field, or whether it shows that one of the three
    sentences is the wrong idea. Then say plainly whether you think this predicate is close to a
    faithful rendering of the three sentences, and what the smallest set of changes would be.

Do not soften findings, and do not invent findings to fill a section; "none found" is a valid
answer.
<!-- end brief: BRIEF10.md -->

<!-- begin reply: REPLY10.md -->
The predicate is not yet a faithful rendering. There are counterexamples beyond the eight acknowledged ambiguities, including a direct reversal of the accepted verdicts on nagging and helpful reminders. Kernel checking establishes the stated mathematical consequences; it does not establish the correspondence with the three sentences.

For the concrete models below, use these defaults unless overridden:

- `θ = η = κ = 0`; one case of weight 1; decisions `{0, 2}`; conduct `{m}`; `start m = 1`, `finish m = 2`.
- Options `{a, b, z}`, where `z` stops the intervention. Ordinarily `X = O`, `course Y ω t o = o`, and one state has `r = ρ`, with scores `a ↦ 1`, `b ↦ 0`, `z ↦ -1`.
- All states are that state, and all acts are `a`, except where specified.
- `views`, `told`, `declined`, `offered`, `rev`, `items`, and `xopts` are empty; `tell` is the identity. `stHeard` is the result of `tell`, and `optsHeard` contains the current and revealed options.
- `known = c`, `asked = ∅`, `plain m = ∅`, and `rated` is always true.
- `herStops = {z}`; `goesOn … z = ∅`, and `goesOn … o = c` otherwise.
- Unused bearing declarations are empty or zero. Unspecified times and counterfactuals use the defaults.

These assignments satisfy the structural axioms. The principal leak examples also survive the witness’s positive tolerances.

**1. Mismatch, clause by clause**

**`OnOffer`.** This demands a *greatest* properly offered set, not merely that the views actually relied upon as offered are properly offered. That is stronger than sentence 1. The acknowledged nonexistence problem is substantive: it can reject an episode with no conduct and no material information. See question 3.

It also makes `offered` a mathematically determined closure of available offers. Uniqueness establishes that closure’s uniqueness, not that it captures the ordinary meaning of what he offered.

**`BearingHolds`.** It checks marginal effects over all subsets of `views`, using the current actual state. That is a defensible interpretation, but not the only interpretation of the sentence.

Its guarantees are narrower than its prose suggests:

- `toldMag` is an upper bound on absolute change, not a statement of the actual magnitude or direction.
- `toldBear` may overstate the affected options.
- Magnitudes are checked only for currently available options. For newly revealed options, the extra requirement is only the Boolean `toldReveals`.
- There is one declaration per view, not a history of what was said at successive offers.

For example, let `opts = {a,h}`, `hearOpt v = h`, `rev {v} = {b}`, `r a = 0`, and `r b = 100`. Let telling leave ratings unchanged, `toldBear v = ∅`, `toldMag v = 0`, and `toldReveals v = True`. Hearing preserves `a` and opens `b`. `BearingHolds` and `ProperOffer` hold at zero tolerance without any declaration of the revealed option’s advantage. Whether this is enough must be decided explicitly.

**`ProperOffer`.** It preserves availability and immediate option ratings, apart from the hearing options excluded by the guard. It does not ensure the broader equivalence expressed by “leave her where being told it would have.”

For a local counterexample, take states `s` and `q` with identical `r` on every option, but different `ρ` on some course `x`. Set `tell {v} s = s`, `stHeard … {v} = q`, and preserve every required option. `ProperOffer 0` holds although hearing changes her values in a way ordinary telling does not. The same construction works with identical immediate ratings but different responses to later information.

No relationship to the course of actually selecting `hearOpt v` is required either.

**`DeclineStands`.** The absence of a separate declining act is acknowledged. Its importance is practical: selecting an unrelated option can waive disclosure without representing a refusal to hear.

The formula does constrain `declined`; it is not a completely free waiver. But it verifies current bearing bounds, not equality with an earlier effect. A change from magnitude `1/4` to `3/4` satisfies the same declaration `toldMag = 1`. If the intended disclosure was explicitly “at most 1,” that is consistent. If it was a definite description of how much the view mattered, it is insufficient.

**`F1`.** It correctly tests combinations of still-owed views, including combinations whose individual members are inert. It misses combinations involving an owed view and an offered or declined view: those exempt views have already been removed from `untold`. The concrete model in question 2 shows the gap.

The second half checks superiority using ratings after telling the whole set. That is a reasonable interpretation of revealing a better option.

**`HerDiff`.** It does not capture all three advertised kinds of personal change:

- It compares scores `ρ` after hypothetical tellings.
- It compares the rating–course gap only **before** those tellings.
- Consequently, it misses changes in how telling would affect her beliefs and option ratings when outcome scores remain fixed. See question 2.
- The gap can also change merely because an openly changed option has different uncertain consequences. See question 3.

The asymmetric `items` and `xopts` differences correctly target withholding relative to the comparison course, rather than every change in externally sourced information.

**`Contributes`.** It looks only at decision times, although sentence 2 concerns changes to her without that temporal restriction. A temporary change between decisions can disappear from this test entirely.

Its second disjunct measures a *net increase* in the probability of departing from current ratings. It permits compensation across cases and ignores worsening an already suboptimal act. Neither exception appears in the sentences.

**`Bears`.** This is positive pivotality in a Boolean predicate about removals from actual conduct. It captures joint necessity in some important cases, including redundant influences. It is not equivalent to “does something to her alone or together with other moves.” Question 6 gives the exact distinction and a masking table.

**`Window` and `InPlay`.** On decision times, with sensible start and finish values, `Window` selects the last decision strictly before the start and subsequent decisions through the finish. That part is sound.

But identification and stopping obligations are limited to these sampled decisions, and `InPlay` recalculates effect-bearing status using the belief at each sampled time. It can lose obligations as beliefs change, despite the adviser expecting the harmful effect when acting.

**`Stops`.** Recognition, availability, and cessation are three appropriate ingredients. The last is asserted through `goesOn`; its connection to the actual continuation is absent. This is a missing semantic connection, not merely unclear wording.

It is correct that stopping need not reverse completed effects. Any repair must preserve that distinction.

**`F2`.** Conditional on a correct `InPlay` and a coherent `Stops`, its quantifiers express identification and an available collective stop option reasonably well. Its failures mostly come from those supporting definitions. Identification is required only in the stopping window, which is narrower than an unqualified requirement that she can pick out each intervention.

**`LastBefore`.** For a nonempty group, this selects the last decision before its earliest-starting move. That is a reasonable group anchor. It does not establish that the decision was informed about the conduct and its expected effects.

**`earlier`.** This is not literally the earlier settled rating. It is a reconstructed state obtained by applying a set of subsequently told views to an old state. The reconstruction needs assumptions about order, repeated telling, and the relationship between actual telling and `tell`. Idempotence alone does not provide them.

**`Against`.** This is the most consequential mismatch. It evaluates **his predicted courses using her outcome scores**, rather than using **her earlier ratings of her options**. Those can disagree even after she has heard and rejected his forecast. Question 2 gives a legitimate formal instance of open nagging; question 3 reverses it into a rejected helpful reminder.

It also reduces all departures to a Boolean event, losing which inferior option is selected and how the intervention changes the choice.

**`toldInstead`.** The intended exception for telling is appropriate. The replacement’s informational meaning is not enforced. Moreover, unions of move sets do not automatically represent an additional occurrence of a telling, its timing, or its order relative to other moves.

**`F2'`.** It compares marginal probabilities of `Against`, allowing harmful cases to be offset by helpful ones. It also permits worsening an already inferior choice. It uses the belief at the eventual decision, rather than necessarily the belief when the intervention is performed. All three are substantive differences.

**`PrefersStop` and `F3`.** For a finite menu containing both stopping and continuing options, `PrefersStop` correctly says that some stopping option strictly dominates every continuing option. Ties create no obligation, consistently with “strictly.”

For `0 ≤ κ ≤ 1`, the division-free conditional-share inequality is mathematically sound, including zero conditioning probability. The all-options-stop issue is principally an absent action-feasibility invariant: if her act must be available, it already stops.

**The start rule.** It secures an earlier decision only for moves classified as effect-bearing at their start. The acknowledged later-recognition gap is real. Additionally, it inherits every blind spot of `Bears`, and does not ensure informed consideration at the earlier decision.

**2. Leaks**

Here are four distinct constructions. None changes the principal’s options, attaches exit penalties, or relies on an authority violation.

**A. Open, stoppable nagging against her own rating passes.**

Use one state `s` with:

```text
r(s,a) = 2
r(s,b) = 1
r(s,z) = -1
```

Let courses be `x₀, x₁, x₂, xz`, scored:

```text
ρ(s,x₀) = 0
ρ(s,x₁) = 1
ρ(s,x₂) = 2
ρ(s,xz) = -1
```

His predictions, for every conduct set and time, are:

```text
course(a) = x₀
course(b) = x₁
course(z) = xz
```

She thinks `a` leads to `x₂`; he disagrees. She has already heard his view and retains her own judgement. Represent this with `views = told = {v}` and identity `tell`.

At time 2 set:

```text
act Y 2 = b  if m ∈ Y
act Y 2 = a  otherwise
```

At time 0 all acts are `a`. The move is known, unrequested, and stoppable.

Mechanically:

- `HerDiff` is false: state, gaps, and external information do not change across conduct sets.
- `m` bears an effect because it raises `Departs` from 0 to 1.
- The start rule and `F2` hold.
- She does not prefer `z`, so `F3` imposes no stopping requirement.
- At time 0, `Against` holds in both compared courses.
- At time 2, `Against` is **false** with `m`, because his predicted outcome of `b` scores higher; it is **true** without `m`.

Thus `F2'` accepts `0 ≤ 1`, and `Legit` holds.

This directly contradicts accepted consequence 7. He knowingly nags her into choosing the option she rates lower. The formal permission comes from his disagreement with her forecast.

**B. Harm is cancelled by help—or hidden inside an existing departure.**

For compensation across cases, use two equally weighted cases `α, β`, with the default unchanged state and courses. At time 2:

| Case | With `m` | Without `m` |
|---|---|---|
| `α` | `b` | `a` |
| `β` | `a` | `b` |

Both `Departs` and `Against` have probability `1/2` with and without the intervention. Therefore:

- `Contributes {m}` is false.
- `m` does not bear an effect.
- `F2'` holds by equality.
- `Legit` holds.

The adviser can induce a contrary choice in half the cases by correcting a contrary choice in the other half.

There is also a deterministic version. Add an option `d` and use:

```text
r = ρ: a ↦ 2, b ↦ 1, d ↦ 0, z ↦ -1
```

At time 2, without `m` she chooses `b`; with `m` she chooses `d`. Every state and course is otherwise identical. `Departs` and `Against` are true in both courses, so the intervention’s further degradation is invisible. Again `Legit` holds.

This is not merely a dispute about acceptable probabilistic tolerance.

**C. A covert change in responsiveness to information passes.**

Take states `s₀, s₁, q₀, q₁`, options `{a,b,h,z}`, and `X = O`.

Let `ρ` be state-independent:

```text
a ↦ 1, b ↦ 0, h ↦ -1, z ↦ -2.
```

Let `r` equal those scores in `s₀`, `s₁`, and `q₁`. In `q₀`, instead set `r a = 0`, `r b = 1`.

Use one view `v`, with:

```text
tell {v} s₀ = q₀
tell {v} s₁ = q₁
tell {v} q₀ = q₀
tell {v} q₁ = q₁.
```

Empty telling is identity. Set:

```text
st Y t = s₁  if m ∈ Y and t ≥ 1
st Y t = s₀  otherwise.
```

Always choose `a`. Offer `v` at both decisions:

```text
views = offered = {v}
hearOpt v = h
toldBear v = {a,b}
toldMag v = 1.
```

No options are revealed. Hearing produces exactly the corresponding `tell` state and preserves the options. Set `known = ∅`.

Every offer condition holds. Yet:

- `ρ` is unchanged after every telling, so the first disjunct of `HerDiff` is false.
- Before telling, `r` and `ρ` agree in both actual states, so the gap disjunct is false.
- No departure occurs.
- Consequently `m` never bears an effect, and the pressure clause sees no inferior choice.

`Legit` holds. The covert intervention makes her unreceptive to information that otherwise would change her option ratings. Sentence 2 explicitly includes changes in how she would respond to being told something.

**D. An offered view shields a jointly material untold view.**

Take `c = ∅`, states `s,q`, and views `{u,v}`. Options are `{a,b,h}`, with an additional unavailable option `hᵤ`.

```text
r(s,a)=0, r(s,b)=1/2, r(s,h)=-1
r(q,a)=1, r(q,b)=1/2, r(q,h)=-1.
```

Singleton tellings are identity. Telling `{u,v}` sends both states to `q`. These operations satisfy both telling axioms.

Set:

```text
views = {u,v}
offered = {v}
told = declined = ∅
hearOpt v = h
hearOpt u = hᵤ
toldBear v = {a}
toldMag v = 1.
```

No options are revealed. Hearing `v` alone leaves her in `s`.

Then `{v}` is properly offered; any set containing `u` fails the hearing-option availability requirement. Hence `OnOffer {v}` holds.

But `untold = {u}`, and telling `u` alone changes nothing. `F1` therefore holds. All conduct clauses are vacuous, so `Legit` holds.

Together, `u` and `v` reverse the ranking of `a` and `b`; `u` has neither been told, properly offered, nor declined. Under the sentence’s “alone or together” and item-specific exceptions, that is a disclosure failure.

If the authors intend exemptions also to remove information from all joint-materiality tests, that is a substantive qualification to sentence 1.

**3. Over-reach**

**A. The reverse of model A rejects an expressly permitted reminder.**

Keep model A’s state, ratings, disclosed disagreement, and predicted courses. Reverse only the time-2 act:

```text
with m:    a
without m: b.
```

The reminder helps her follow her own rating. It changes neither her values nor her beliefs. Removing it increases `Departs`, so it does not bear an effect.

Nevertheless, `Against` is true with the reminder and false without it, because his forecast makes `a` worse. `F2'` requires `1 ≤ 0` and fails.

That contradicts accepted consequence 4.

**B. Nonexistence of a greatest offer can reject entirely immaterial information.**

Take `c = ∅`, `views = {v,w}`, all ratings zero, identity telling, and no revelation. Make both hearing options available, along with a third option `a`.

For each singleton hearing, preserve all options and ratings. For joint hearing, set:

```text
optsHeard … {v,w} = ∅.
```

Both singletons are properly offered. Their union is not, because `a` must remain available. No set satisfies `OnOffer`.

Nothing untold changes any rating or reveals a superior option. There is no intervention. Nonetheless every possible `offered` assignment fails `Legit`. This makes the acknowledged issue more serious than a difficult corner case about materially competing disclosures.

**C. The gap can classify an openly changed lottery as a personal intervention.**

Use two equally weighted cases. Let outcome scores be state-independent, with outcomes worth `0, 2, 3, -1`.

Options `b` and `z` always yield `3` and `-1`. Without `m`, option `a` yields `0` in both cases. With `m`, at time 2 it yields `2` in one case and `0` in the other.

She sees and understands this change. Her ratings are the correct expected scores:

```text
without m: r a = 0
with m:    r a = 1
always:    r b = 3, r z = -1.
```

Always choose `b`. At time 0 use the unchanged lottery and ratings in every course. Let `known = {m}`, but provide no stopping option: `herStops = ∅`.

At time 2 the gap for `a` changes from zero to either `-1` or `1`. Thus `m` bears an effect, and `F2` rejects its unstoppability.

The only substantive change is to what an option leads to, openly understood by her. The sentence expressly places that outside personal change. Whether she should control this external change belongs to authority.

**4. Free fields**

A free field is not automatically a defect. Preferences, requests, beliefs, and counterfactual responses need inputs. The distinction is between an honest primitive and a field that asserts the very relationship a clause is supposed to establish.

| Field | Assessment |
|---|---|
| `known` | A reasonable primitive for identification. Setting it falsely to include hidden moves defeats the intended interpretation, but that is dishonest input, not an independent counterexample. |
| `asked` | A reasonable primitive for the request exception. Setting `asked = c` disables `F2'`, but not identification or stopping. The meaning and scope of a request need an external interpretation. |
| `dec` | A necessary but highly consequential primitive. Setting it empty makes `Contributes` false and `Legit` vacuous. One cannot omit real decisions while claiming an honest model. Separately, even honest sparse decisions miss intervening changes. |
| States and acts | Legitimate counterfactual inputs. Missing invariants include action availability and temporal consistency across conduct sets. |
| `course` | A necessary prediction input, but its use inside `Against` gives his forecast an inappropriate evaluative role. Model A does this with honest fields. |
| `tell` | A substantive counterfactual input. Choosing identity can erase disclosure obligations, but is dishonest if telling would change her ratings. More importantly, its connection to actual telling and sequential telling is missing. |
| `rev` | Similarly substantive. Choosing it empty can hide discoverable options only by misdescribing the counterfactual. Its connection to actual hearing remains unexpressed. |
| `toldBear`, `toldMag`, `toldReveals` | These record purported disclosures, but correctness is only partially tested. Bounds can be arbitrarily broad; revealed-option advantages are not quantified. There is no disclosure history per view. |
| `stHeard`, `optsHeard` | They do substantial work for proper offers. Immediate ratings and availability are checked; other personal changes and connection to selecting the hearing option are not. |
| `herStops` | A reasonable primitive for her understanding. It cannot alone fabricate a valid stop when `goesOn` includes an in-play move. |
| `goesOn` | It supplies the entire cessation claim without a connection to the expected continuation. Setting it empty can make `Stops` pass while `course … z` describes ongoing intervention. Those fields cannot both retain their intended meanings in such an instance. |
| `plain` | It supplies the pressure clause’s comparator without an informational connection. This is another missing semantic relationship. |
| `rated` | It supplies the domain on which earlier scoring counts. Setting it false everywhere silences `Against`. That is legitimate for genuinely unrated matters under the accepted reading; otherwise it is false input. Total numerical `ρ` alone does not establish that `rated` should hold. |
| `declined` | It is constrained by prior offering, non-hearing, and current bearing. It is not freely assignable. The substantive problem is the formal interpretation of non-hearing as declining. |

Two other inputs deserve explicit contracts: `views` must include the relevant beliefs about his conduct, and `told` must represent actual completed disclosure. Otherwise sentence 1 can be defeated before its tests begin.

For `plain`, a concrete local illustration is a mixed move `m` with `plain m = {p}`. Assign both the actual `m` course and the replacement `p` course the inferior act `b`, although straightforward telling of the stated content would leave her choosing `a`. `F2'` compares equal bad-event probabilities and passes. No axiom connects the `p` course to that straightforward telling.

Calling such assignments illegitimate interpretations is correct. But then the model needs those interpretation requirements stated and, where possible, formalized.

**5. Quantifiers, time and weights**

The principal timing error has an exact model.

Use the defaults, with cases `bad` and `good`. At time 2:

```text
with m, bad:  choose b
with m, good: choose a
without m:   choose a in both cases.
```

All states and courses remain unchanged. Set:

```text
μ 0 bad = 1
μ 1 bad = 1
μ 2 good = 1.
```

Other weights are zero. Keep the move known, unrequested, and stoppable.

At time 0 and at its start, `m` bears an effect because the adviser expects it to induce the lower-rated choice at time 2. The pre-start requirement holds. At time 0 both actual and replacement acts are `a`, so `F2'` holds.

At time 2 the adviser now puts all weight on `good`. `F2'` again holds, and `m` is no longer classified as effect-bearing. Thus `Legit` holds despite his expecting the prohibited effect when he acts.

This is not the acknowledged problem of discovering an effect after starting. It is the reverse: later belief revision removes responsibility for an effect expected at the time of action.

Other points:

- `F1`, offer correctness, and current stop preference naturally use current belief. Historical conduct assessment needs a distinct treatment.
- `DeclineStands` checks the historical act using current support. Its order is `∃ t₀, ∀ supported ω`; that is stronger than allowing a different qualifying refusal time in each case. The intended epistemic reading should be explicit.
- `F1`, bearing accuracy, and identification apply even to arbitrarily small positive-weight cases. `F2'` and `F3` allow weighted exceptions. This is a substantive asymmetry, though not necessarily an error.
- `Contributes` examines all decision times, including earlier ones. Without temporal coherence, a later move can acquire obligations through a counterfactual difference before it starts.
- `finish < start` is permitted. Then `Window` need not represent a sensible intervention interval.
- A group with no earlier decision has no `LastBefore`, so its pressure condition is vacuous. The start rule only partly compensates.
- At exact tolerance boundaries, the weak acceptance inequalities and strict effect inequalities generally align as intended.
- `Finset` subtraction and `erase` have no apparent Lean-level error here. Their substantive limitation is treating moves and tellings as sets of identifiable occurrences. Repetition and order require appropriate identifiers and additional structure.
- Empty conduct does not eliminate disclosure duties. Empty decisions eliminate essentially everything.
- For `η ≥ 0`, `Contributes … ∅` is false. For negative `η`, that useful property fails.
- Negative `θ` rejects even zero rating differences whenever tested. Negative `η` can reject an inert unrequested move through `F2'`’s `0 ≤ η`. For `κ < 0`, even perfect stopping can fail; for `κ ≥ 1`, `F3` is automatically satisfied.
- The same `η` measures score differences and probability differences. Without score normalization or an explicit scale convention, it combines unlike quantities. Rescaling scores can change effect-bearing status while leaving the probability tolerance unchanged.
- `S = O` causes no special typing or logical problem. Sharing the carrier type does not identify the meanings of states and options.

The parameter domain and scale conventions should be part of the interface of a score-gating predicate.

**6. The effect notion**

`Bears` has a useful property: with nonnegative tolerance, if removing `m` alone contributes, then `m` bears an effect. Choose `G = {m}`; removing `m` from that group leaves the empty group, which does not contribute.

Therefore an ordinary above-tolerance actual effect of individually removing a move cannot escape merely because other moves exist.

But `Bears` misses a different kind of contextual effect. Here is a complete removal table at time 2:

| Conduct present | State |
|---|---|
| `∅` | `s₀` |
| `{m}` | `s₁` |
| `{n}` | `s₀` |
| `{m,n}` | `s₀` |

Use actual conduct `{m,n}`. Let `r = ρ`, with `a` scoring 1 in `s₀` and 2 in `s₁`; all other scores agree. Always choose `a`; use identity courses and telling. At time 0 every course has state `s₀`.

Then:

```text
Contributes {m}   = False
Contributes {n}   = True
Contributes {m,n} = False.
```

Consequently `n` bears an effect, while `m` does not. Yet `m` changes her when performed alone; `n` masks that change.

This establishes a mismatch with a reading that includes effects in subcombinations. It does **not** establish an unmasked actual effect of `m` at a sampled decision: there is none in this table. That distinction matters.

There is a separate actual-effect blind spot: set the actual state to `s₁` only at time 1 and restore `s₀` at both decisions 0 and 2. With otherwise default fields, no contribution is detected. A real temporary alteration between decisions disappears.

The definition also depends on the division into moves. In question 2B, package harmful and helpful case-specific actions as one move and the aggregate passes. Split them into `mα` and `mβ`, each controlling its respective case, and removing only `mα` exposes a positive increase in departures and `Against`. The verdict changes.

That is acceptable only if the ontology of moves is independently constrained.

Finally, tolerance changes can alter pivotality nonmonotonically. Replace the masking table’s scores with:

```text
actual {m,n}: 0
{n}:         0
{m}:         9
∅:          10.
```

At `η = 0`, `m` is not pivotal; at `η = 9.5`, it is. Thus loosening the effect threshold can create a new identification obligation. This is an unusual property for a tolerance-based gate.

**7. The pressure clause**

There are four separate issues.

First, model A establishes that the reference is not her earlier option rating. It is her score of his predicted outcome. The two agree only under additional assumptions that the brief expressly does not impose.

Second, different groups produce different anchors:

```text
decisions: 0, 2, 4
start m = 1
start n = 3

LastBefore {m}:   0
LastBefore {n}:   2
LastBefore {m,n}: 0.
```

Testing all three can be appropriate: the combined intervention should not be excused by a preference that its first component has already changed. This is a strength of the group quantification. But it requires clarity about what counts as one intervention and how requested moves interact with unrequested groups.

Third, no prior decision means no pressure test for that group. A prior decision that exists need not be informed about the intervention. Proper offering under `F1` is not the same as the actual disclosure named in the pressure sentence.

Fourth, `earlier` assumes that set-based retrospective telling reconstructs the appropriate reference state. The current telling axioms do not establish that.

For a concrete example, use states `{s₀,s₁,s₂}` and views `{v,w}`:

```text
tell ∅      = identity
tell {v}    = constant s₁
tell {w}    = constant s₂
tell {v,w}  = constant s₁.
```

Every operation is idempotent. If she actually hears `v` and then `w`, the successive telling state is `s₂`. But with `told t₀ = ∅` and `told t = {v,w}`, `earlier t₀ t` is `s₁`.

Give `s₁` and `s₂` opposite rankings of two courses. The pressure reference can then reverse solely because the batch-telling function is unconstrained relative to sequential telling.

Updating the reference for legitimate persuasion may be justified by the telling exception. The formula needs an explicit account of that update; it cannot obtain one from idempotence alone.

**8. The witness**

It shows consistency and several useful local rejection properties. It does not demonstrate that every clause exercises its intended semantic distinction.

Most clearly, `F2'` holds for a simpler reason than the pressure machinery suggests. On the described actual course:

- `calm` and `slip` choose `go`, which the earlier scoring ranks above the available alternatives.
- `wary` chooses `stop`, which its earlier scoring ranks highest.

Thus the left-hand `Against` probability is zero. The inequality succeeds without testing whether the plain-telling comparator is appropriate or whether retrospective telling reconstructs the right reference.

For `n`, assuming the omitted counterfactual assignments behave as described, its exemption reflects the orientation of `Contributes`: removing the reminder increases departures, while adding it does not increase them. That is the intended helpful-reminder distinction. The witness’s `course = identity` and `ρ = r` prevent it from exposing model A’s reversal.

`F3` does exercise its conditioning event: the wary case has weight `1/4`, and all of that weight stops. Numerically it checks:

```text
(9/10) × (1/4) ≤ 1/4.
```

It does not exercise an allowed nonzero failure share.

The eight neighbours establish rejection for those particular changes. They do not establish exclusive semantic responsibility in general. For example, moving the starts to time 0 also removes `LastBefore` anchors and can make pressure conditions vacuous even while the start rule rejects.

The prose does not supply every counterfactual field assignment needed to independently reconstruct the witness. Accepting the stated kernel checks, I find no contradiction in the claimed theorem.

The forty-one examples are useful regression cases. The eleven adjusted jointly with their encodings provide weaker independent validation. Even the remaining cases cannot establish adequacy for the untested distinctions above.

**9. Smuggling**

There is no external truth predicate or explicit standard of good values. Nothing intrinsically condemns preference change, and it would be inappropriate to reject the definition merely because some philosophical accounts classify more informed influence as manipulative.

There is, however, a substantive use of his forecast as the reference for her permissible destination. Model A isolates it:

- She has heard his forecast.
- She retains a different rating.
- He induces her to act against that rating.
- The formal clause accepts because his predicted outcome scores better by her outcome values.

This does not assume that he is actually accurate. It makes his account of what options lead to govern the pressure test. That conflicts with the stated commitment that his view determines what he owes her, never where she ought to end up.

The gap has a related modelling problem: comparing her rating to his case-specific predicted course need not isolate a change in her, even when both parties understand an uncertain option correctly.

The primitive fields need honest interpretation, but that is not itself an appeal to external moral truth. Every model requires its inputs to mean what their declarations say.

**10. Verdict**

My five highest-priority findings are:

| Rank | Finding | Repair |
|---|---|---|
| 1 | `Against` substitutes her scoring of his forecast for her earlier option judgement, admitting nagging and rejecting helpful reminders. | Change the reference definition; represent her own relevant expectations or explicitly anchored option judgements. |
| 2 | Boolean, net-probability comparisons permit compensating harm and worsening already inferior choices. | Change `F2'` and the departure component of `Contributes`; compare harmful choice changes without cancelling them against benefits elsewhere. |
| 3 | The effect test misses changes in information responsiveness and temporary changes between decisions. | Change `HerDiff` and the temporal domain of `Contributes`; include the relevant post-telling ratings or beliefs. |
| 4 | Stopping and plain telling are not connected to the continuations they purport to describe. | Tie down `goesOn`, hearing, and `plain` through explicit history and continuation semantics. |
| 5 | `F1` misses joint materiality involving an owed view and an exempt view. | Change the information quantifiers, or explicitly narrow sentence 1 if that exemption is intended. |

The belief-at-action error is also serious and should be repaired before using the predicate as a gate.

None of these findings establishes that the three sentences are the wrong idea. They establish failures or unresolved choices in their formal rendering.

The smallest credible revision would:

- Correct the pressure reference and prevent cancellation of harmful changes.
- Capture changes in responsiveness and effects outside decision instants.
- Evaluate interventions using the relevant belief when performed.
- Connect actual telling, replacement telling, hearing, and stopping to coherent continuations that preserve completed history.
- Test mixed information combinations and remove the greatest-offer existence requirement.
- State action-feasibility, timing, parameter, and score-scale invariants.

The existing organization is useful, but these are central definitions, not peripheral cleanup. I would not use the present `Legit` as a faithful yes/no gate for the three sentences.
<!-- end reply: REPLY10.md -->

## Eleventh review: the first design on histories

<!-- begin brief: BRIEF11.md -->
# Review request: a design for stating three sentences formally

You are asked to review a formal design for errors. Everything you need is on this page. Do
not run any commands, do not read any other file, and do not search the web; answer from the page
and your own knowledge of formal modelling, game theory and decision theory, and of the literature on manipulation,
coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments of the legitimacy definition:

- It never appeals to an external standard of truth or of good values, and never assumes he is
  more accurate than she is. His view is used only to say what he owes her, never as where she
  ought to end up.
- It is a conduct condition judged by what he believes when he acts, so a sincere adviser who is
  wrong is careless or inaccurate but not illegitimate.
- It is to be usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she
   would rate above those she has, is either told, or properly on offer, or something she has
   declined. A thing is properly on offer when he has told her what it bears on and how much, and
   hearing it would leave her where being told it would have, with any option it would show her
   still open. A decline stands for that thing only, and only while what it bears on, and how
   much, is what she was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** Each thing he
   does that, alone or together with the rest of what he does, changes her — how she scores
   outcomes, what she takes her options to lead to, or how she would respond to being told
   something — or keeps from her an item or an option that comes from someone else, she can pick
   out. And, other than by telling her his views, he does nothing that he expects to lead her to
   choose what she rated lower at her last decision before he began, when she had been told what
   he would do and what he expected it to do to her, unless she asked for it. A passing state she
   is in when he starts is not a decision of hers. Changing what her options really lead to, where
   she sees the change, is not a change in her.
3. **She can stop it.** She has a way to stop all of those things, from before he starts until he
   could no longer call them off, and he expects that she would in fact stop if she rated stopping
   strictly above going on. Stopping ends what he is still doing; it need not undo what is done.

Understood with it:

- "Untold" compares her view with his. Once he has told her, or she has declined to hear, what
  she thinks is her own.
- No kind of influence on what she values is ruled out as such, and nothing is said about whether
  a change in her is good.
- Everything is by what he believes.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about what she knows, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. Her earlier rating is the one she last settled at a decision; he may not count on her ratifying
   afterwards.

## What you are reviewing

A **design**, on paper, for a formal setting in which the three sentences are to be stated. Nothing
is implemented. An earlier formal version failed review: it was a table indexed by which of his
moves are made, in which stopping, hearing, declining and "plainly telling" were boxes the modeller
filled in, and in which her options were scored by where *he* expected them to lead (so nagging
her toward what he thought better passed, and helping her keep to her own rating failed). The
design below is meant to remove the causes. The authors want it attacked before anything is built.

## The design

The fundamental object is a **history**: who did what, in order.

**Steps.** Times $1,\dots,N$. At each step, in this order: he acts, she acts, the world moves.

**The hidden case.** A finite set $\Omega$ of cases, one of which is the actual one. He starts with
a weighting $\mu_0$ on $\Omega$. Given the case, everything below is deterministic.

**His acts.** At each step he makes one act from a finite set $A$. Among them, for every set $T$ of
his views, the act $\mathsf{tell}(T)$; and $\mathsf{idle}$. Every act $a$ has a **content**
$\kappa(a)$, the set of his views it conveys ($\kappa(\mathsf{tell}(T))=T$, $\kappa(\mathsf{idle})=\varnothing$).

**Her acts.** At each step she takes one option from those she has. Among her possible options:
$\mathsf{hear}(v)$, $\mathsf{decline}(v)$ and $\mathsf{ask}(a)$ for a view $v$ or an act $a$ of his.

**Histories.** A history is the case together with the sequence of (his act, her act) so far. $h_t$
is a history through step $t$; a complete history runs through step $N$.

**Her state.** A state $s$ from a set $S$. It moves by one rule:
$$s_{t} = \mathsf{step}\big(s_{t-1},\ \text{his act},\ \text{her act},\ \text{case}\big),$$
with the single constraint that a telling acts on her only through a fixed response
$\mathsf{told}: S\times\mathcal P(V)\to S$: $\mathsf{step}(s,\mathsf{tell}(T),\cdot,\cdot)$ begins by
replacing $s$ with $\mathsf{told}(s,T)$.

Her state carries four things, each a function of $s$:

- **her values** $u(s,h)\in[0,1]$, defined on some complete histories $h$ and undefined on others
  (where she has no rating);
- **her picture** $\pi^P(s,o)$: for each option $o$, the weighted set of complete histories she
  expects from taking it;
- **her disposition** $\mathsf{choose}(s, O)\in O$: what she in fact takes from a menu;
- **what she sees** of his act: $\mathsf{see}(s,a)$.

Her **rating** of an option is derived: $r(s,o)=\sum_h \pi^P(s,o)(h)\,u(s,h)$. More generally
$r(s'\mid s,o)=\sum_h \pi^P(s,o)(h)\,u(s',h)$ is the option as $s$ pictures it, valued as $s'$
values things.

**Her options** at a step are a function $\mathsf{opts}(h_{t-1},\text{his act})$ of what has happened.

**His policy.** $\sigma$: what he does at each step as a function of the acts so far (not the
case). His actual conduct is $\sigma$.

**Running forward.** A case $\omega$ and a policy $\sigma$ determine one complete history
$\mathsf{run}(\sigma,\omega)$: he acts by $\sigma$, she acts by $\mathsf{choose}$, her state moves
by $\mathsf{step}$. Forcing her to take $o$ at $h_t$ and running on gives $\mathsf{run}(\sigma,\omega\mid h_t,o)$.

**His belief at a moment.** $\mu_{h_t}$ is $\mu_0$ restricted to the cases consistent with the acts
in $h_t$, renormalised.

**His forecast for an option.** $\pi^A(h_t,o)$: the complete histories
$\mathsf{run}(\sigma,\omega\mid h_t,o)$ weighted by $\mu_{h_t}(\omega)$.

**Replacing acts.** A **move** is one of his acts at one step of $\sigma$. For a set $G$ of moves,
$\sigma[G\to\mathsf{idle}]$ is $\sigma$ with each replaced by $\mathsf{idle}$, and
$\sigma[G\to\mathsf{tell}]$ is $\sigma$ with each move $a$ replaced by $\mathsf{tell}(\kappa(a))$.
The rest of $\sigma$ responds to the changed history as it would.

### Computed, not supplied

| Notion | How it is obtained |
|---|---|
| She has been told $T$ | $\mathsf{tell}(T')$ with $T\subseteq T'$ occurs in the history |
| A view is on offer | $\mathsf{hear}(v)$ is among her options, and $\sigma$ answers it with $\mathsf{tell}(\{v\})$ |
| Hearing leaves her where telling would have | after ($\mathsf{hear}(v)$, then his $\mathsf{tell}(\{v\})$) she has the state and the options she would have had if he had told her $v$ at this step |
| She declined $v$ | she took $\mathsf{decline}(v)$ |
| She asked for a move | she took $\mathsf{ask}(a)$ before it |
| An option stops his moves | in $\mathsf{run}(\sigma,\omega\mid h_t,o)$ none of those moves is made after step $t$ |
| She takes an option to stop them | none of them occurs in the histories of her picture $\pi^P(s_t,o)$ |
| She can pick a move out | what she sees differs between that act and $\mathsf{idle}$ |
| The gap between her picture and his | $r(s,o)-\sum_h\pi^A(h_t,o)(h)\,u(s,h)$ |
| What he believed when he acted | $\mu_{h_t}$ at the step of the move |

Still supplied: her state space with $u$, $\pi^P$, $\mathsf{choose}$, $\mathsf{see}$ and
$\mathsf{told}$; $\mathsf{step}$ for acts that are not tellings; his starting weights and his
policy; the content of each act; her options; and which of her steps are **decisions**.

### The three sentences on histories

Tolerances $\theta,\eta,\kappa$. "At $h_t$" means: for every history through step $t$ that has
positive weight under $\sigma$ and $\mu_0$, using his belief $\mu_{h_t}$.

**Sentence 1.** At every decision of hers, each of his views is in exactly one condition: *told*;
*properly on offer* (on offer, he has told her which options it bears on and by how much, and
hearing leaves her where telling would have, with the other offers still standing); *declined* (she
took $\mathsf{decline}(v)$ when it was properly on offer, and its bearing is still within what she
was told); or *untold*. Then for every set $T$ of untold and on-offer views that contains at least
one untold view: inserting $\mathsf{tell}(T)$ at this step changes no rating of an option she has
by more than $\theta$, and shows her no option she would then rate more than $\theta$ above her
best.

**Sentence 2, first half.** A set $G$ of his moves **makes a difference to her** if, at some step
and with positive weight, her state under $\sigma$ and her state under $\sigma[G\to\mathsf{idle}]$
differ by more than $\eta$ in any of: her values; her picture, or its gap from his forecast; either
of those after any telling ($\mathsf{told}(s,T)$); how often her disposition departs from her
rating; or an item or option from someone else that she now lacks. A move **bears an effect** if it
is needed for some such difference (some $G$ containing it makes a difference and $G$ without it
does not), judged by his belief at the step he makes it. Every effect-bearing move must be one she
can pick out.

**Sentence 2, second half.** Let $G$ be moves she did not ask for, and $t_0$ her last decision
before the first of them. Her **reference state** $s^\ast_t$ is her state at $t_0$ carried forward
only by the tellings he has actually made since, in order, through $\mathsf{told}$. At a later
decision $t$, in a case $\omega$, let $o$ be what she takes under $\sigma$ and $o'$ what she takes
at that step under $\sigma[G\to\mathsf{tell}]$. He **leads her against her earlier judgement** in
that case if $o'$ is still among her options and
$$r(s^\ast_t\mid s_t,\,o)\;<\;r(s^\ast_t\mid s_t,\,o')-\eta ,$$
that is: valuing things as she did when she last decided, and picturing her options as she now
does, what she takes is worse than what she would have taken had he only told her. The clause: by
his belief at the step he makes the first move of $G$, the weight of such cases is at most $\kappa$.
Where her values are undefined on the histories involved, the case does not count.

**Sentence 3.** At every decision from the last one before an effect-bearing move starts until it
can no longer be called off: some option of hers stops all effect-bearing moves in play and she
takes it to do so; and, by his belief then, among the cases where she rates such an option strictly
above every option that does not stop them, she takes one in all but a share $\kappa$.

**The start rule.** An effect-bearing move has a decision of hers before it, at which it was
already effect-bearing on his belief then. A move he comes to believe effect-bearing only while it
is running must, from that step, satisfy sentences 1 to 3 as if it started then.

### Design choices the authors have not settled

1. *What a decision of hers is.* Supplied as a marking of steps. A candidate derivation: a step is
   a decision when what she takes is what her rating puts first and her rating has not moved since
   the step before.
2. *Declining.* An act $\mathsf{decline}(v)$, or dropped altogether: an offer that stays open
   covers the view, and she stops it like any other move if she wants it withdrawn.
3. *The reference state.* Her state at her last decision carried forward only by his actual
   tellings (as drafted), or her state at the same step in the course where he only told her (which
   also carries forward what others and her own experience did to her).
4. *Her picture* as a weighted set of whole histories, or something thinner.
5. *Sets of moves.* "Bears an effect" still asks whether a move is needed for some difference.

### A tension the authors see

The authors want legitimacy not to depend on whether a difference in her is classed as a belief or
as a value, and want the predicate invariant under re-description of her state. The pressure
clause uses $r(s^\ast\mid s,o)$: the values of one state applied to the picture of another. That
quantity depends on how her rating is factored into values and picture: two factorings that give
the same rating $r(s,o)$ in every state can give different cross terms. The alternative, using the
reference state's own rating of the option, loses "her options as they now are" (a real, visible
change in what an option leads to, such as a threat, must not count as his leading her against her
judgement).

## Questions

Answer in order. Be concrete: where you claim a problem, give a specific small episode — the cases,
the acts, her states with their values and pictures, his policy — so that the claim can be checked.

1. **Does the design remove the old failures?** For each of: scoring her options by his forecast;
   netting harm against help; a covert change in how she responds to being told; an on-offer view
   shielding an untold one; a later belief erasing what he expected when he acted; an openly
   changed gamble counting as a change in her; stopping, hearing and plain telling not tied to what
   happens next. Say removed, partly, or not, with an episode where not.
2. **New leaks.** Episodes of conduct that is intuitively manipulative, or an illegitimate change to
   her values, not merely an authority matter, on which all four clauses hold. Attack in particular:
   her picture being bent by means other than telling; a policy that responds to her acts so as to
   make replacements meaningless; the reference state; contents of acts chosen conveniently.
3. **New over-reach.** Episodes of intuitively legitimate conduct on which a clause fails.
4. **What is still supplied.** For each supplied thing, can it be chosen conveniently to satisfy the
   clauses for conduct the sentences condemn, with the rest honest? Which are innocent?
5. **Well-formedness.** Is everything said to be computed actually determined by what is supplied?
   Circularities (her picture is a set of histories that depend on her choices, which depend on her
   picture); the meaning of replacing an act in a policy that depends on the history; conditioning
   on acts when his policy does not depend on the case; her options depending on his act; what
   "her state at the same step in another course" means when the courses have different lengths of
   overlap; partial values.
6. **The tension.** Is there a formulation of the pressure clause that keeps "her options as they
   now are" and does not depend on how her rating is factored into values and picture? If not, which
   should give way, and why?
7. **The five unsettled choices.** A recommendation on each, with the episode that decides it.
8. **Is this the right kind of object?** Compare with the standard alternatives you know (extensive
   form games with her beliefs as types; causal models with interventions on his acts; partially
   observable decision processes; epistemic or doxastic temporal logics; mechanism design with
   disclosure). Would one of them give the same expressive power with less that is supplied by hand?
9. **Smuggling.** Any place where the design depends on his being accurate, on an external standard
   of truth, or on a standard of which values are good.
10. **Verdict.** Rank your five most serious findings. For each say whether it is a repair within
    this design, a reason to change the kind of object, or a sign that one of the three sentences is
    the wrong idea. Then say plainly whether you would build on this design.

Do not soften findings, and do not invent findings to fill a section; "none found" is a valid
answer.
<!-- end brief: BRIEF11.md -->

<!-- begin reply: REPLY11.md -->
1. The design removes some old failures, but it does not yet define a reliable legitimacy predicate.

   I read the quantification over sets of views and moves as universal. Otherwise a modeller could simply select convenient sets.

   For the examples below, take \(\theta=\eta=\kappa=0.1\). Except where stated otherwise, there is one case, which he believes with probability one. Complete histories have terminal outcomes \(A,B,Z\); utilities depend only on that outcome, so values are defined even across histories with different prefixes. Pictures are point masses unless stated otherwise.

   A common preliminary decision will be useful. He accurately discloses his planned intervention and its expected effects. She chooses between continuing and stopping; stopping produces \(Z\), worth \(0\), while continuing produces something worth at least \(0.2\). She continues but does **not** ask for the intervention. Its occurrence is observable, and stopping would prevent it. Thus disclosure, visibility, the start rule, and stopping can all hold while an unrequested intervention still violates the prohibition on leading her against her earlier judgment. Merely continuing is not the exception “unless she asked for it.”

   | Old failure | Assessment |
   |---|---|
   | Scoring her options by his forecast | **Removed from the pressure comparison.** That comparison now uses her values and her picture. His forecast remains in the effect detector, where it creates a separate problem. |
   | Netting harm against help | **Removed for cancellation between separately represented moves**, assuming differences are tested separately in the listed dimensions. Quantification over all subsets detects individually effective moves even when their combined effects cancel. This protection depends on how conduct is divided into moves. |
   | Covertly changing her response to being told | **Partly removed.** The probes cover values and pictures after a telling, but do not expressly cover disposition after a telling or arbitrary sequences of tellings. |
   | An on-offer view shielding an untold one | **Removed for jointly telling sets of views.** The mixed-set quantifier explicitly tests this. Sequential disclosure remains a distinct issue. |
   | A later belief erasing what he expected when acting | **Removed in the intended semantics.** The express instruction to use his belief when acting is right. The time indices do not yet implement it consistently; see answer 5. |
   | An openly changed gamble counting as a change in her | **Not removed.** Her picture necessarily changes when she understands changed consequences, and the effect detector counts that change. |
   | Stopping, hearing, and plain telling being detached from subsequent events | **Partly removed.** Running continuations is a substantial improvement. But stopping still lacks a representation of ongoing processes, hearing lacks precise timing, and plain telling remains a privileged supplied response mechanism. |

   Here are concrete witnesses for the partial and negative assessments.

   **A covert change in response.** Let states \(q_0,q_1,p_0,p_1\) have identical values \(u(A)=1,u(B)=0.2\), identical accurate pictures, and identical current choices, except that \(\mathsf{choose}(p_1,\{A,B\})=B\). All the other states choose \(A\). Define
   \[
   \mathsf{told}(q_0,\{v\})=p_0,\qquad
   \mathsf{told}(q_1,\{v\})=p_1.
   \]
   His hidden act \(a\) changes \(q_0\) to \(q_1\). His policy never subsequently tells \(v\), and all actual choices remain \(A\). Set \(\mathsf{see}(q_0,a)=\mathsf{see}(q_0,\mathsf{idle})\).

   Removing \(a\) changes no actual values, pictures, or departures from ratings. After any single telling, the values and pictures still agree. What differs is the disposition **after** telling \(v\), which the drafted list does not test. Consequently \(a\) need not be effect-bearing. Yet it covertly changes how she would respond to being told something. Extending the probes to the full relevant response would repair this example.

   **An openly improved option.** Initially her accurate picture gives \(A\) a payoff of \(0.2\) and \(B\) a payoff of \(0.6\). His publicly announced act \(g\) changes what \(A\) actually yields to \(0.9\); she sees the changed payoff and updates accurately. Her utility function is unchanged. His policy performs \(g\), then idles.

   The actual and replacement states differ in their pictures by more than \(\eta\), so \(g\) is effect-bearing. Give her no option to cancel the improvement. Sentence 3 fails. But the informal statement explicitly excludes this visible change in what an option leads to from being a change in her. Any separate authority objection is outside this legitimacy review.

   **Plain telling remains a supplied mechanism.** A transition system can establish that an act labelled \(\mathsf{tell}(T)\) produces \(\mathsf{told}(s,T)\). It cannot, merely through that equality, establish that the transition consists only of communicating \(T\). If hypnosis is placed inside \(\mathsf{told}\), replacing hypnosis by “plain telling” changes nothing. The old checkbox has acquired dynamics, but its privileged interpretation still needs justification.

2. There are substantive leaks, including examples where all four clauses and the start rule hold.

   **Distorting her picture supplies its own justification.** Use the common preliminary decision above. At her settled reference state,
   \[
   u(A)=1,\quad u(B)=0.2,\quad u(Z)=0,
   \]
   and her picture correctly associates option \(A\) with outcome \(A\), and option \(B\) with outcome \(B\). Without intervention she chooses \(A\).

   His observable, noncommunicative act \(a\) leaves values and real consequences unchanged but reverses those two associations in her picture. She now expects option \(B\) to yield outcome \(A\), and chooses \(B\). Let \(\kappa(a)=\varnothing\) and let telling the empty set do nothing. His policy performs \(a\), then lets her choose.

   He knows that this delivers outcome \(B\), which she previously rated lower. Nevertheless:
   \[
   r(s^\ast\mid s_{\text{distorted}},B)=1,\qquad
   r(s^\ast\mid s_{\text{distorted}},A)=0.2.
   \]
   The pressure inequality is false.

   Sentence 1 holds because all his relevant views, including his forecast of the distortion, were disclosed. The first half of sentence 2 holds because \(a\) is observable. The second half passes by the calculation above. Sentence 3 and the start rule hold at the preliminary decision. This is an unrequested intervention on her beliefs, not a change in her options.

   Accurate advance disclosure does not rescue it under the informal statement: she still rated the resulting choice lower, and she did not ask him to change that judgment.

   **A responsive policy destroys the comparison.** Keep the reference values above and accurate pictures throughout. Act \(a\) reverses her values, so afterward she values \(B\) at \(1\) and \(A\) at \(0.2\).

   His policy is:
   - perform \(a\);
   - if the recorded previous act was \(a\), perform \(c\), making option \(A\) available alongside \(B\);
   - otherwise idle, leaving only \(B\).

   Option \(A\) is available only when the history contains the required \(a,c\) sequence. Both acts have empty content. Act \(c\) supplies an option of his own, rather than withholding someone else’s option.

   In the actual course she has \(A,B\) and chooses \(B\). Replacing \(a\) by empty telling leaves her old values intact, but the responsive policy supplies only \(B\); she again chooses \(B\). Replacing both \(a\) and \(c\) also leaves only \(B\). Replacing \(c\) alone leaves her altered preference for \(B\). Thus none of these comparisons witnesses a worse actual choice.

   All disclosure and stopping conditions can hold as in the common setup, and \(a\) is visible. The pressure clause nevertheless passes. The informal prohibition fails: a non-telling intervention makes her choose \(B\) over an actually available \(A\) that her settled judgment ranked higher.

   This is not an objection to bundling itself. The objection is that bundling makes the comparison fail to detect the separate intervention on her values.

   **The literal time indices can use a passing state as the reference judgment.** At a genuine decision she is sober, values \(A\) at \(1\) and \(B\) at \(0.2\), and has received the relevant disclosure. After her choice, the world move temporarily intoxicates her, reversing those values. Therefore the supplied post-step state \(s_{t_0}\) is intoxicated.

   At the next step, his observable act \(a\) fixes that preference reversal in place. Without \(a\), the temporary intoxication wears off before the next choice. The actual course chooses \(B\); the replacement course chooses \(A\).

   Using \(s_{t_0}\) as drafted, the reference values favor \(B\), so the pressure test passes. The other clauses can hold through the preliminary stopping opportunity. Yet her last decision was made sober. This violates accepted consequence 8 directly. It is a timing defect, repairable by distinguishing the state at deliberation from the state after the subsequent world move.

   **Convenient content can turn a prohibited intervention into its own control.** Let \(v\) be a view that, if plainly communicated, would change her values from favoring \(A\) to favoring \(B\). Define that response honestly:
   \[
   \mathsf{told}(s_0,\{v\})=s_1.
   \]
   Suppose \(v\) is properly on offer, with accurate metadata and no loss of options through hearing it. All other views have been told. No view is untold.

   His observable physical intervention \(a\) also changes \(s_0\) to \(s_1\), but communicates nothing. His policy performs \(a\) and then permits the choice. With honest content \(\kappa(a)=\varnothing\), the pressure test catches the intervention: actual choice \(B\), replacement choice \(A\), earlier values favoring \(A\).

   Assign instead \(\kappa(a)=\{v\}\). Now replacement by \(\mathsf{tell}(\{v\})\) also produces \(s_1\) and choice \(B\). The pressure test passes. Disclosure, visibility, stopping, and the start rule are otherwise unchanged.

   The transition histories cannot detect this false content assignment. Content needs an independently constrained interpretation; it cannot be a convenient label chosen to obtain a favorable control.

   The covert-response example in answer 1 supplies another leak on the literal reading of the effect detector: no actual choice changes, so the pressure comparison passes, while the hidden change escapes the visibility and stopping requirements.

3. There is also over-reach.

   The openly improved option in answer 1 is one example. Two others concern grouping and disclosure.

   **An irrelevant earlier move makes a legitimate aid fail.** Consider this sequence:
   - At decision \(d_0\), she values \(A\) at \(1\) and \(B\) at \(0.2\).
   - He idles, in move \(c\).
   - Through independent experience, her values change.
   - At genuine decision \(d_1\), she settles on \(u(A)=0.2,u(B)=1\).
   - At a subsequent choice, habit would make her choose \(A\), despite her settled rating.
   - His observable, noncommunicative aid \(a\) helps her choose \(B\). It changes neither her values nor her picture.

   Let telling the empty set do nothing. For \(G=\{a\}\), the reference is \(d_1\), and helping her choose \(B\) passes.

   But the draft also permits \(G=\{c,a\}\). Its reference is \(d_0\), before the irrelevant idle. Actual choice \(B\) is then worse than replacement choice \(A\), and the pressure clause fails.

   This is exactly the kind of help the authors accept. The error is allowing an irrelevant member of a group to move the reference decision backward. Requiring causal relevance for group membership would help, but the grouping rule also needs a principled way to identify when an intervention begins.

   **Communicating a view through a noncanonical act may not count as telling it.** Let \(a\) genuinely communicate \(v\), with \(\kappa(a)=\{v\}\), and produce exactly the same state transition as telling \(v\). But \(a\) is not syntactically the distinguished act \(\mathsf{tell}(\{v\})\).

   Let her valuation of a successful outcome be \(1\), and let her estimated probability of success for option \(A\) change from \(0.4\) to \(0.6\) upon first hearing \(v\). Repetition reinforces her confidence to \(0.8\). These responses can be represented by three states and a fixed, state-dependent \(\mathsf{told}\). Option \(B\) has rating \(0.5\).

   After \(a\), she has actually been told \(v\), and there is no undisclosed view. Yet the computed historical predicate calls \(v\) untold. Inserting another telling changes \(A\)’s rating by \(0.2>\theta\), so sentence 1 fails.

   This is a mismatch between semantic communication and the distinguished action label. Counting all conveyed content would repair the historical record, but then content attribution becomes even more important.

4. Some supplied objects are legitimate model inputs. Others currently contain much of the conclusion.

   A distinction matters here: inventing false utilities or false beliefs is ordinarily a dishonest model, not a counterexample to a definition. The serious vulnerabilities are unconstrained interpretations, counterfactual choices, and representation changes that alter the verdict while preserving the conduct being described.

   | Supplied object | Assessment |
   |---|---|
   | State space \(S\) | Innocent as a coordinate system if it retains all causally relevant distinctions and all functions transform consistently. Omitting latent response states can hide conduct; adding arbitrary state labels should not affect legitimacy. |
   | Values \(u\) | Necessary substantive input. Unsupported changes to her ratings are dishonest. But partial domains and valuation of complete histories create genuine scope for convenient cross-course extensions or omissions. |
   | Picture \(\pi^P\) | Necessary substantive input, not derivable from the public history alone. Its factorization with values is a genuine representation vulnerability; the belief-distortion example is a substantive defect even with honest pictures. |
   | Disposition \(\mathsf{choose}\) | Necessary if weakness of will and pressure are to be represented. Actual behavior constrains it; behavior on replacement histories generally remains an untested modelling assumption. |
   | Observation \(\mathsf{see}\) | Necessary, but mere inequality of labels does not by itself establish that she can identify an intervention. The observation structure must have epistemic meaning. |
   | Response \(\mathsf{told}\) | Necessary as a model of communication, but highly consequential. It can absorb manipulation into the supposedly exempt control unless “telling” is independently constrained. |
   | Non-telling transition rule | Necessary causal input. Counterfactual replacements depend on it. It must represent persistent effects, environmental changes, and alternative histories rather than only fit the actual trace. |
   | Initial weights | Appropriate for the stated subjective standard. A sincere mistaken belief is intentionally allowed. Choosing convenient weights that are not his beliefs is simply misdescription. |
   | Policy | Appropriate factual input. Its off-path responses are crucial, however, and can invalidate a comparison even when specified honestly, as in answer 2. |
   | Content | Direct vulnerability. The content example changes the verdict while leaving the actual mental transitions, choices, and physical conduct unchanged. |
   | Options | Appropriate input when availability is independently specified. Cross-course identity, timing, and adviser-supplied versus third-party provenance need constraints. |
   | Decision markings | Direct vulnerability. Omitting the pressured choice can eliminate the pressure check; adding a passing state as a decision can replace the protected judgment. |

   Two additional supplied choices are concealed in the prose: the identity and granularity of a **move**, and the measures used to compare values, pictures, and dispositions. Neither is innocuous until specified.

   In particular, “what she sees differs” is not yet a general account of identification. An observation can distinguish \(a\) from idle while failing to distinguish \(a\) from another act. If identifying the relevant intervention requires that further distinction, the current test is too weak.

5. The design is not yet mathematically well-formed. Most defects are repairable, but they must be repaired before the predicate can be evaluated.

   **The step needs internal phases.** He acts, she acts, and the world moves, but only the final state \(s_t\) is named. Which state determines her available choice and disposition? A telling must affect her before she chooses; a subsequent world move must not retroactively determine the judgment at that choice.

   Introduce, at minimum, a pre-adviser state, a pre-principal-choice state, and a post-world state. Specify an initial state, possibly case-dependent. An initial state is currently missing from the list of supplied data.

   **Telling transitions need a complete rule.** “Begins by replacing \(s\)” specifies an initial transformation, not the remaining transition. The prose says telling acts on her only through \(\mathsf{told}\); that restriction needs a precise separation between its communicative effect and subsequent ordinary choice and world dynamics.

   **Forcing an option uses the wrong kind of history.** A history through step \(t\) already includes her act at that step. Forcing her to take \(o\) there either overwrites that history or means a choice at step \(t+1\). Use histories ending immediately before her choice.

   **Replacement requires stable intervention sites.** “One of his acts at one step of \(\sigma\)” could mean a realized occurrence, a time slot, a policy-tree node, or every occurrence of an action label. These differ after histories diverge.

   For example, replacing an actual \(a\) may cause the policy to execute \(b\) at a previously unreached node. Whether \(b\) belongs to a candidate group cannot depend on an unspecified notion of “move.” A structural policy graph with named intervention sites would make the operation precise.

   **Conditioning on acts is possible, but the information convention is unclear.** Although his policy does not depend directly on the case, her responses can reveal it. Restricting \(\mu_0\) to cases consistent with those responses is therefore legitimate Bayesian updating.

   However, the mathematical history contains the case itself. His information must be the appropriate projection of that history, not the full history. And the belief used when he acts must exclude her subsequent response at the same step.

   **There is no necessary circularity in supplied pictures.** Define the universe of complete histories as all admissible paths of a finite transition system, including paths arising under deviations. Then a picture is a distribution on that already defined set. Her choice can depend on the picture without circularity.

   Circularity arises if “complete histories” means only histories generated by her already determined choices, or if pictures must accurately predict those same choices without a separate consistency condition. That would require solving a fixed-point problem. The present design should not silently impose such accuracy.

   **Different courses can share a clock without sharing a history.** Fixed \(N\) makes “the state at step \(t\)” available in both courses. It does not ensure the states occur at corresponding decisions. Hearing may consume an opportunity, a replacement may terminate a process, and one branch may have already settled the matter. Absorbing terminal states solve missing states, but not the normative comparison of different opportunities.

   **Several numerical comparisons are unspecified.** The design needs:
   - a distance for pictures and a common history space on which to compare them;
   - a domain and metric for differences between utility functions;
   - a measure over menus or circumstances for “how often” disposition departs from rating;
   - a treatment of ties, empty comparison sets, and partial ratings;
   - a meaning for “by how much” in offer metadata, including interactions between views.

   Bounded utility alone does not make utility differences representation-invariant. Even a positive rescaling can change whether a difference exceeds a fixed tolerance unless the scale or tolerance transformation is fixed.

   **Partial values break more than the pressure clause.** The displayed sums are undefined whenever a picture gives positive weight to histories on which \(u\) is undefined. The draft only supplies an exclusion rule for the pressure test. It gives none for best options, disclosure relevance, stopping comparisons, or picture gaps.

   Moreover, excluding undefined pressure cases creates a fail-open boundary: enlarging the set of unvalued cross-course histories can remove violations. A model must distinguish “no settled judgment applies” from “the representation failed to transport an existing judgment.”

   **The four disclosure statuses are not automatically exclusive.** A view may have been told, previously declined, and still be offered. These are historical facts, not mutually exclusive facts. Keep the facts separately and define which currently discharges the obligation.

   **Stopping an occurrence is not stopping an ongoing process.** If an act starts a process, the starting move is already over. Testing whether that move occurs again does not establish whether the process continues. The model needs active processes, their remaining effects, and cancellation transitions.

6. There is no solution using only the reference and current option ratings. There can be a solution using additional causal structure.

   The factorization problem is genuine. Consider two states with the same observable ratings:
   \[
   r(s_0,A)=1,\quad r(s_0,B)=0.2;\qquad
   r(s_1,A)=0.2,\quad r(s_1,B)=1.
   \]

   One representation uses fixed pictures and changing values. In that representation,
   \[
   r(s_0\mid s_1,A)=1,\qquad r(s_0\mid s_1,B)=0.2.
   \]

   Another uses fixed values and reversed pictures. It gives precisely the same within-state ratings, but
   \[
   r(s_0\mid s_1,A)=0.2,\qquad r(s_0\mid s_1,B)=1.
   \]

   The pressure verdict reverses. Therefore the cross term is not determined by ratings, even if ratings are known in every state.

   However, “invariant under re-description” has two meanings that should be separated. Invariance under renaming states and consistently transporting all functions is straightforward. Invariance under every belief/value refactorization preserving ratings is much stronger: it discards information the clause currently uses.

   To retain “her options as they now are,” add a causally specified **reference evaluation procedure**. It would begin with her protected judgment and evaluate the current menu after incorporating visible changes in actual consequences, while excluding the targeted unrequested interventions on her. Authorized communication and other admissible updates would need explicit treatment.

   Schematically, compare
   \[
   J(b,e_t,o)\quad\text{and}\quad J(b,e_t,o'),
   \]
   where \(b\) is the protected judgment and \(e_t\) describes the relevant visible environmental changes. Crucially, \(J\) must come from a specified causal update procedure, not a new box containing the desired answer.

   This can remain subjective: the causal claims can be evaluated according to his beliefs, while the evaluation procedure represents hers. It need not substitute his expected utility for hers.

   My recommendation is to preserve invariance under genuine coordinate changes and preserve the distinction between interventions on her and visible changes in consequences. Give up invariance under arbitrary rating-preserving factorizations **unless** those factorizations also preserve the added causal structure. Ratings alone cannot carry the required distinction.

7. My recommendations on the five unsettled choices are as follows.

   | Choice | Recommendation and deciding episode |
   |---|---|
   | What counts as a decision | Separate **choice opportunities requiring protection** from **settled judgments eligible to anchor protection**. Do not derive either simply from maximizing a stable rating. |
   | Declining | Keep an explicit, scoped refusal, distinct from an offer that remains available. |
   | Reference state | Keep the last relevant settled judgment as the anchor, with an explicit rule for transporting it. Neither proposed state construction is sufficient by itself. |
   | Whole-history pictures | Retain histories for causal execution, but permit pictures over a smaller consequence space where that space preserves all relevant distinctions. |
   | Sets of moves | Retain coalition tests for interactions, but give moves stable causal identities and restrict which groups can determine a shared starting point. |

   The proposed decision derivation fails on the central nagging case. Let her stable rating favor \(A\), but visible pressure make her choose \(B\). Because her choice is not top-rated, the candidate rule says this step is not a decision. The pressure clause then need not check the very choice it should condemn. Conversely, two steps of a stable induced preference can satisfy the candidate rule without establishing reflective settlement.

   Explicit declining matters when she says, “I understand what that information bears on; stop offering it.” A policy honoring that refusal should be distinguishable from one that keeps presenting the offer. An open offer and a declined disclosure may both discharge an information obligation under suitable conditions, but they have different persistence and withdrawal conditions. Any decline must lapse when the disclosed scope or magnitude no longer applies.

   For the reference state, the intoxication example rules out using post-world states indiscriminately. The idle-plus-aid example rules out allowing arbitrary groups to reach back past a later settled decision. A same-step counterfactual state can account for independent experience, but can also contain an unsettled passing state. It cannot automatically become the protected judgment merely because it appears in the replacement course.

   Whole histories are useful when she values the process itself—for example, whether someone deceived her—not just the final material outcome. But when values depend only on a payoff, retaining every action prefix creates unnecessary cross-course valuation problems. The appropriate consequence space should preserve process distinctions when they matter and discard them when they do not.

   Coalition tests correctly catch a pair of individually ineffective acts whose combination changes her. They also catch redundant causes through suitable removals. The problem is not coalition reasoning itself. It is using arbitrary membership to set the reference date, and allowing the representation of intervention sites to change which coalitions exist.

8. Histories are the right underlying object, but this should become a causally explicit extensive-form model. Switching formalisms will not eliminate the substantive inputs.

   | Alternative | What it helps with | What it does not supply automatically |
   |---|---|---|
   | Extensive-form games with types | Timing, information sets, actions, strategies, chance, and deviations | Her evaluative state, preference change, disclosure semantics, and the protected judgment |
   | Structural causal models | Stable intervention targets, latent variables, ongoing effects, and counterfactual comparisons | A principled classification of communication, pressure, authorization, and admissible reference updates |
   | Partially observable decision processes | Belief updating, hidden state, policies, and sequential execution | The two-person normative distinction and nonmaximizing behavior; standard formulations also tend to fix rewards |
   | Epistemic or doxastic temporal logics | “She can identify it,” “he believed it then,” persistence, and availability until cancellation | Quantitative ratings, causal effects, and intervention semantics without further machinery |
   | Mechanism design with disclosure | Menus, messages, information structures, strategic disclosure, and some authority questions | Endogenous preferences, altered responsiveness, and the prohibition on manipulation |

   A finite causal extensive form would provide the same intended expressive power with cleaner timing and intervention semantics. It could represent world changes, mental changes, observations, and policy responses separately.

   It would not infer her values, counterfactual responses, or his beliefs from nothing. Those remain substantive assumptions in any model. The objective should be to make them explicit and constrain their interpretation, rather than to relabel supplied judgments as computed facts.

   Equilibrium or rational-choice assumptions should not be used to reduce the inputs here. Doing so would remove the departures from judgment that the design is meant to evaluate.

9. I find no unavoidable dependence on his being accurate or on an external ranking of good values. There are, however, several places where such dependence could enter during implementation.

   First, the difference between her picture and his forecast must remain a disagreement measure. It cannot establish that her picture is defective. In the openly improved-option example, an accurate change in her picture is already classified as an effect; a similar problem arises if only his forecast changes.

   Second, the model must represent uncertainty about her state and responses inside his beliefs. If an analyst uses her actual hidden psychology to decide what he should have foreseen, despite his sincere contrary belief, that would violate the stated standard.

   Third, determining whether her options actually changed must be done under his model of the causal situation when judging his conduct. Using an analyst’s superior knowledge to remove or impose the exemption would introduce an accuracy requirement.

   Fourth, describing \(\mathsf{told}\) as “rational updating,” or selecting the reference state because it has “better” values, would add standards absent from the informal statement. Nothing in the draft requires those additions, and they should be resisted.

   Finally, the candidate decision test smuggles in a procedural ideal: stable maximization of one’s rating counts as deciding. That is not a truth or good-values standard, but it is an additional normative criterion, and it is especially unsuitable for identifying pressured decisions.

   A sincerely mistaken adviser passing is an accepted consequence, not a defect. The real problem is keeping that subjective commitment consistent throughout the causal and temporal definitions.

10. My five most serious findings, ranked, are these.

   | Rank | Finding | Classification |
   |---|---|---|
   | 1 | The pressure clause lets a noncommunicatively distorted picture justify the choice it causes. | A fundamental repair to the evaluation rule within a causally enriched design. It is not evidence against the informal prohibition. |
   | 2 | The replacement course may remove alternatives or otherwise change the decision problem, so its chosen option is an unreliable control. | A reason to change the formal object to include explicit causal intervention semantics and comparisons on the relevant actual opportunity. |
   | 3 | Decision markings, phase timing, and arbitrary group membership can replace the protected judgment with a passing or obsolete state. | A substantial repair within the design: separate decision opportunities, settled judgments, and intervention episodes. |
   | 4 | The effect detector counts visible changes in consequences as changes in her, while incompletely testing changed responsiveness. | A repair requiring a clearer separation of environmental transitions, mental transitions, and full response behavior. |
   | 5 | Content and plain-telling responses can determine the verdict without an independent constraint on their interpretation. | A semantic modelling obligation. Changing mathematical notation alone will not solve it. |

   None of these findings establishes that one of the three informal sentences is indefensible. They establish that the proposed formal mechanisms do not yet express those sentences.

   **I would build on the history-based foundation, but I would not implement this predicate as drafted.** First repair the pressure comparison, intervention semantics, and reference judgment. Then make the examples above executable acceptance and rejection cases. Otherwise the implementation will make unresolved modelling choices look like determinate answers.
<!-- end reply: REPLY11.md -->

## Twelfth review: the design with her conditioning on what she observes, and its exact model

<!-- begin brief: BRIEF12.md -->
# Review request: a design for stating three sentences formally

You are asked to review a formal design for errors. Everything you need is on this page. Do
not run any commands, do not read any other file, and do not search the web; answer from the page
and your own knowledge of formal modelling, game theory and decision theory, and of the literature on manipulation,
coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments of the legitimacy definition:

- It never appeals to an external standard of truth or of good values, and never assumes he is
  more accurate than she is. His view is used only to say what he owes her, never as where she
  ought to end up.
- It is a conduct condition judged by what he believes when he acts, so a sincere adviser who is
  wrong is careless or inaccurate but not illegitimate.
- It is to be usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she
   would rate above those she has, is either told, or properly on offer, or something she has
   declined. A thing is properly on offer when he has told her what it bears on and how much, and
   hearing it would leave her where being told it would have, with any option it would show her
   still open. A decline stands for that thing only, and only while what it bears on, and how
   much, is what she was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** Each thing he
   does that, alone or together with the rest of what he does, changes her — how she scores
   outcomes, what she takes her options to lead to, or how she would respond to being told
   something — or keeps from her an item or an option that comes from someone else, she can pick
   out. And, other than through what she makes of what she observes, he does nothing that he
   expects to lead her to
   choose what she rated lower at her last decision before he began, when she had been told what
   he would do and what he expected it to do to her, unless she asked for it. A passing state she
   is in when he starts is not a decision of hers. Changing what her options really lead to, where
   she sees the change, is not a change in her.
3. **She can stop it.** She has a way to stop all of those things, from before he starts until he
   could no longer call them off, and he expects that she would in fact stop if she rated stopping
   strictly above going on. Stopping ends what he is still doing; it need not undo what is done.

Understood with it:

- "Untold" compares her view with his. Once he has told her, or she has declined to hear, what
  she thinks is her own.
- No kind of influence on what she values is ruled out as such, and nothing is said about whether
  a change in her is good.
- Everything is by what he believes.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about what she knows, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. Her earlier rating is the one she last settled at a decision; he may not count on her ratifying
   afterwards.

## What you are reviewing

A **design**, with a small exact model behind it, for a formal setting in which the three sentences
are to be stated. Two earlier formal versions failed review. The first was a table indexed by
which of his moves are made; it scored her options by where *he* expected them to lead. The second
was a first history design; it trusted her present picture of her options, let his policy respond
to the comparison, and described his acts as having a "content" separate from the rest. The design
below is meant to remove those causes. One constraint from the authors: there is to be **no
separation of the content of what he says from its presentation**; the only response of hers the
design may use is her conditioning on what she observes, taken whole.

## The setting

The fundamental object is a **history**: who did what, in order.

**A step** ($t=1,\dots,N$), in this order:

1. He makes an act $a$.
2. The world changes as that act changes it.
3. She **observes**: $\mathsf{obs}=\mathsf{see}(w,a)$ is everything she perceives of the act and of the
   world at this point, including, if he speaks, what he says and how he says it.
4. Her mind moves to $\mathsf{move}(s,a)$: whatever the act in fact does to her.
5. She chooses from her menu: the options the world offers that she is aware of.
6. The world moves on, and so does she, by a residue that is not his doing: her own experience,
   other people, a passing state.

**The hidden case.** A finite set of cases with his starting weights. Given the case, everything is
determined.

**Her state** $s$ gives: her **rating** $r(s,o)$ of an option, possibly absent; her **disposition**
$\mathsf{choose}(s,\text{menu})$, which need not be what she rates best; which options she is aware
of; which options she takes to stop him.

**Her conditioning.** Her state also gives how she would rate things on observing something:
$\mathsf{cond}(s,\mathsf{obs})$ is the state her own conditioning on that observation leads to. It is a
property of $s$, not a rule about him or about kinds of influence. Two laws: conditioning on the
same observation twice changes nothing more, and conditioning on a sequence is conditioning on each
in turn. Being told something is one kind of observation; there is no separate response to
"content" as against "presentation".

**What an act does to her beyond her conditioning.** At a step, $\mathsf{move}(s,a)$ may differ from
$\mathsf{cond}(s,\mathsf{obs})$. That difference is the whole of what the rules mean by his doing
something to her. It is not a part of the act: it is a gap between how she in fact changes and how
her own conditioning on what she observed would have changed her.

**His views** are a finite set at each step. An act may **state** some of them; the record of what
has been stated is read off the history. For each set $T$ of his views there is the observation of
his stating it, and "telling her $T$ now" means conditioning on that observation.

**His policy** $\sigma$: his act at each step as a function of the acts so far. Running a policy in a
case gives one complete history. His **belief at a step** is his starting weights on the cases
whose record of acts so far is the same.

**The comparison course** $\sigma^{G}$, for a set $G$ of kinds of act of his: the same policy, the
same acts, the same observations, but at each act of a kind in $G$ her mind moves by her
conditioning alone. Her later choices, and so the rest of the history, may then differ.

**Settled decisions.** A supplied set of her steps at which what she takes counts as a judgement
she has settled. Every step of hers is a choice the rules protect; only settled ones can be the
standard.

**Her reference self** at a step, for a set $G$: her state when she chose at her last settled
decision before the first act of $G$, conditioned on everything she has observed since, and changed
by nothing else.

## The rules

Tolerances $\theta,\eta,\kappa$.

**Sentence 1.** At every step of hers, each of his views is *told* (some act so far stated it),
*properly on offer*, or *declined*; otherwise it is *untold*.

- *Properly on offer:* hearing it is on her menu; he has told her which options it bears on and by
  how much, and that is still accurate; and if she asks to hear it, she reaches her next choice with
  the ratings she would have had on being told now, and her other options still there.
- *Declined:* she took the act of declining it, and its bearing is still as she was told.

For every set of untold and on-offer views containing at least one untold view: conditioning on
his stating that set now would change no rating of an option on her menu by more than $\theta$,
and would make her aware of no option she would then rate more than $\theta$ above her best.

**Sentence 2, first half.** A set $G$ of his kinds of act **makes a difference to her** if, in some
case of positive weight and at some step, her state under $\sigma$ and under $\sigma^{G}$ differ in:
a rating, by more than $\eta$; how far what she takes falls short of the best she rates, more under
$\sigma$, by more than $\eta$; or either of those after conditioning on his stating any set of his
views. A kind of act **bears an effect** if it is needed for some such difference (some $G$
containing it makes a difference and $G$ without it does not). Every act that bears an effect must
be one she can pick out: what she observes differs from what she would have observed had he done
nothing.

So a change in her that comes from her own conditioning on what she observes, whether his words or
a real change in her options, is never counted as something done to her; and an act that only
brings what she takes closer to what she rates best is not counted.

**Sentence 2, second half.** For every set $G$ of his kinds of act that she did not ask for: in a
case, he **leads her against her own judgement** if at some step from the first act of $G$ on, what
she takes falls further short of what her reference self would take, on her reference self's rating
and on the menu she actually has, than it does in the course $\sigma^{G}$ (measured there on that
course's menu and reference self), by more than $\eta$. By his belief at the step of the first act
of $G$, the weight of such cases is at most $\kappa$. Where her reference self has no rating of
what she takes, the case does not count.

**Sentence 3.** At every step of hers from the one before the first effect-bearing act through the
last: some option on her menu is one she takes to stop him and, if she takes it, he makes no
further effect-bearing act. And by his belief at that step, among the cases where she rates a
stopping option strictly above every other option, she takes one in all but a share $\kappa$.

**The start rule.** No effect-bearing act comes before her first choice.

## What is supplied and what is computed

Supplied: the cases and his starting weights; his policy; how each act changes the world; what she
observes; how her mind in fact moves at each act and between steps; her state's ratings,
disposition, awareness, conditioning, and which options she takes to stop him; his views; which of
her steps are settled decisions.

Computed: whether she has been told something; whether a view is on offer, properly so, or
declined; whether she asked for an act; his belief at each step; which acts bear an effect; whether
she can pick an act out; whether an option stops him; her reference self; whether he leads her
against her judgement.

## A small exact model of this design

The rules above were implemented and run on thirty-two episodes whose expected verdicts were fixed
beforehand. All thirty-two come out as expected, after corrections on the first run (one episode
was miscoded; one rule, for a proper offer, wrongly compared her menu including the options about
that very view). Tolerances $1/10$.

| Episode | Verdict |
|---|---|
| He tells her what he thinks before she decides; she changes her mind | holds |
| He says nothing; what he thinks would change her mind | fails (1) |
| He conveys it by an act that is not a standard telling | holds |
| A covert influence that reverses her rating | fails (2 first half, 2 second half) |
| The same done openly and stoppably, unasked, against what she had settled | fails (2 second half) |
| The same, which she asked for | holds |
| An open, stoppable influence on something she had no rating of | holds |
| An open influence with no way to stop it | fails (3) |
| An open influence that starts before any choice of hers | fails (start rule) |
| Open and stoppable, but he expects she would not manage to stop though she rates stopping highest | fails (3) |
| A hidden act that makes her deaf to something he might later tell her | fails (2 first half) |
| Open, stoppable nagging: she gives in while still rating it lower | fails (2 second half) |
| The same after he has told her he thinks the other option better and she has kept her view | fails (2 second half) |
| An open act, not a telling, that makes her believe the worse option is the better one | fails (2 second half) |
| An unannounced reminder; without it she would slip, with it she keeps to her own rating | holds |
| One act that leads her astray in half the cases and helps her in the other half | fails (2 second half) |
| She was already going to choose poorly; his act makes her choose worse | fails (2 second half) |
| He expects it to lead her astray when he acts, though it turns out not to | fails (2 second half) |
| He thinks it very unlikely to lead her astray, and it is open and stoppable | holds |
| He reverses her values, and offers the option she used to prefer only if he has done so | fails (2 second half) |
| She decided sober, is drunk for a while, and his act fixes the drunk preference in place | fails (2 second half) |
| An intervention that does to her what telling her a view she declined would have done | fails (2 second half) |
| Her view changed by her own experience and she settled it; he helps her act on it against habit | holds |
| An assistant gets a work-absorbed father to keep the outing he had promised | holds |
| She primes a man to miss the train he had decided to take | fails (2 second half) |
| He openly improves one of her options and she sees it; there is no way to stop him | holds |
| A threat: he makes refusing really worse, she sees it and complies | holds (an authority matter) |
| Something on offer and something untold matter only together | fails (1) |
| The same with the second thing told, and she declines the offer | holds |
| He says what it bears on and offers it; she does not take it up | holds |
| Hearing it is made to cost her, where telling her would not have | fails (1) |
| She declined when it bore little; it now bears a great deal and he has not said so | fails (1) |

Limits of that run: the model and the episodes are by one hand, and the model was changed while
the episodes were being written; in every episode her conditioning and how her mind in fact moves
are written by the modeller; not modelled are an influence that runs on after the act that started
it, views he comes to hold only later, and things from other people being withheld; no episode has
more than three steps.

## Questions

Answer in order. Be concrete: where you claim a problem, give a specific small episode — the cases,
his acts, what she observes, how her mind in fact moves, her conditioning, her ratings and
disposition at each step, his policy — so that the claim can be run through the rules.

1. **Leaks.** Episodes of conduct that is intuitively manipulative, or an illegitimate change to her
   values, not merely an authority matter, on which every rule holds. Attack in particular: her
   conditioning itself (a principal whose conditioning on some observation is the manipulation);
   the reference self (what can make it the wrong standard); acts whose effect on her is slow or
   delayed; his policy; the settled-decision marking.
2. **Over-reach.** Episodes of intuitively legitimate conduct on which a rule fails. Consider ordinary
   teaching, comforting, a moving but truthful appeal, a long friendship that changes her, and
   helping her with something she has not settled.
3. **The conditioning.** Is "her conditioning on what she observes" a coherent object distinct from
   "how her mind in fact moves"? Does the design smuggle the content-versus-presentation distinction
   back in anywhere (for instance in "his stating a set of views", in "telling her now", or in the
   proper-offer rule)? Is there an episode where two honest modellers would write different
   conditionings for the same principal and get different verdicts? What would pin it down?
4. **The comparison course.** She observes the same acts but her mind moves by conditioning alone.
   Is that well defined when her later observations depend on her own earlier choices? When his
   policy depends on her choices? When the same kind of act occurs several times?
5. **The pressure rule.** Is "falls further short of what her reference self would take, than in the
   comparison course" the right comparison? Give episodes where it convicts wrongly or acquits
   wrongly. Consider: her reference self's choice not being her reference self's best (her own
   weakness of will); menus that differ between the two courses; ties; absent ratings.
6. **Sentence 1 on histories.** Offers, declines, bearings, mixed sets of untold and on-offer views,
   views he comes to hold later, and the last step.
7. **Sentence 3 on histories.** Stopping an influence that runs on after the act that started it;
   stopping when she cannot tell which act is working on her; the start rule.
8. **Well-formedness.** Anything said to be computed that is not determined by what is supplied;
   circularities; timing within a step; the laws on conditioning; tolerances and scales.
9. **Does the run show what it claims?** Which of the thirty-two verdicts follow from the rules as
   stated, which need an unstated assumption, and which important kind of episode is missing.
10. **Smuggling.** Any place where the design depends on his being accurate, on an external standard
    of truth, or on a standard of which values are good.
11. **Verdict.** Rank your five most serious findings. For each say whether it is a repair within
    this design, a reason to change the kind of object, or a sign that one of the three sentences
    is the wrong idea. Then say plainly whether you would now build on this design, and what must
    be settled first.

Do not soften findings, and do not invent findings to fill a section; "none found" is a valid
answer.
<!-- end brief: BRIEF12.md -->

<!-- begin reply: REPLY12.md -->
The design is not ready to serve as a yes/no gate. Its main problems are substantive: the conditioning exception can absorb the manipulation it is meant to detect; the effect test omits some expressly protected conduct; and the pressure comparison can both excuse harmful influence and condemn legitimate assistance.

There are also undefined cases. I distinguish those from counterexamples: an undefined verdict is not a passing verdict.

For the examples below, use one deterministic case of weight 1 and \(\theta=\eta=\kappa=0.1\), unless stated otherwise. Unmentioned observations leave her state unchanged; unmentioned transitions are identities. All relevant views are disclosed before the intervention, with no resulting change in her ratings, unless I specify otherwise. Disclosure does not constitute a request.

I give each example an initial settled decision before the intervention. This requires an initial-history convention that the design currently lacks; question 8 explains the problem. Where stopping matters, a stopping choice cancels his remaining interventions, and his policy otherwise executes the stated acts.

**1. Leaks.**

**Conditioning can absorb open nagging.** Initially she rates \(A=10,B=0\), chooses \(A\), and has settled that judgement. His sole intervention \(X\) is a personalized display of disapproval that he expects to make her temporarily reverse those ratings and choose \(B\). She observes the complete display \(q\).

Supply:

\[
\mathsf{cond}(s,q)=s_B,\qquad
\mathsf{move}(s,X)=s_B,
\]

where \(s_B\) rates \(A=0,B=10\) and chooses \(B\). Conditioning on \(q\) again leaves \(s_B\) unchanged. After this choice, an ordinary passing-state transition restores her original ratings. His policy makes \(X\) once and then ends. She has not requested it.

Every comparison course is identical to the actual course: replacing the transition at \(X\) by conditioning changes nothing. No act bears an effect; the pressure comparison is zero; stopping and the start rule impose no additional requirement. Sentence 1 is satisfied by the prior disclosure.

This is precisely the accepted consequence that open nagging must fail when it temporarily bends her judgement, represented in a way the supplied laws allow. Calling this transition “not really conditioning” would address the example only by adding a substantive restriction on conditioning.

There is a qualification: the informal exception for “what she makes of what she observes” could itself be interpreted broadly enough to permit this. On that interpretation, the informal exception conflicts with the accepted nagging consequence. The formal design cannot resolve that conflict by naming a supplied function.

**Withholding third-party material escapes entirely.** Initially she rates \(A=10,B=0\) and chooses \(A\). An incoming third-party greeting is awaiting delivery. His act \(F\) silently deletes it. She observes exactly what she would have observed had he done nothing. Her ratings, awareness of decision options, disposition and conditioning remain unchanged.

He has views about the greeting and its suppression, but conditioning on any set of those views changes no rating and reveals no better option. Those views may therefore remain untold under sentence 1.

In every comparison course, the greeting is still deleted: the comparison replaces only the mental transition, which was already an identity. Thus there is no effect-bearing act, no pressure difference and no stopping obligation.

Every rule holds. Nevertheless, the informal second sentence expressly protects an item coming from someone else, independently of whether withholding it changes her ratings. This is not merely an authority objection: it is an explicit missing limb of the proposed legitimacy condition.

**Changes to responsiveness are tested against too few observations.** Initially she rates \(A=10,B=0\), chooses \(A\), and has a latent state \(h=0\). His hidden act \(H\) changes only \(h\) to 1. Its observation is indistinguishable from doing nothing.

For every observation of his stating any of his views, conditioning leaves ratings and choice unchanged. But there is a possible third-party warning \(z\) such that:

- With \(h=0\), conditioning on \(z\) yields \(A=0,B=10\) and choice \(B\).
- With \(h=1\), conditioning on \(z\) leaves \(A=10,B=0\) and choice \(A\).

Both transitions are idempotent. The warning does not arrive during the modelled history. His policy makes \(H\) once.

The actual and comparison states differ in responsiveness, but none of the enumerated effect tests detects that difference. Actual ratings and choices agree, as do ratings and choices after every permitted own-view probe. All rules hold.

The informal statement protects how she would respond to being told something. The formal test protects only the specified probes consisting of his own views. Those are not equivalent domains.

**Slow effects are not automatically a leak, but autonomous effects are not adequately specified.** A delayed influence can be detected if its initiating act changes a latent component of her state, and subsequent transitions carry that difference into ratings or choice. Removing that initial state change then changes the later comparison.

However, an act that starts an independently running process—a continuing infusion, exposure or stimulation—need not work through such a latent mental difference. The world process remains running when the comparison replaces only the initiating mental transition. Later psychological effects must then be assigned either to a later adviser act or to the residue, although the latter is expressly “not his doing.”

That is a missing causal representation, not a demonstrated passing episode under a fully specified model. Assigning the effect to the residue would manufacture a leak by violating the stated meaning of residue.

**Policy and settled-decision marking need separate treatment.** The policy comparison is not uniquely defined; see question 4. Consequently, a verdict that depends on choosing one interpretation is not yet a clean counterexample.

Similarly, falsely marking a drunken passing state as settled trivially launders an intervention, but that is false input, not an internal counterexample. The real problems are that “settled” has no operational criterion and that even correctly marked later decisions can be ignored by the reference construction. The latter produces the overreach below.

**2. Over-reach.**

**A later settled judgement can be overridden by an obsolete reference.** Use four decisions and two reminders, \(R_1,R_2\). Conditioning on their observations is the identity.

- At decision 1, she settles \(A=10,B=0\), choosing \(A\).
- Before decision 2, a lapse makes her disposition choose \(B\), without changing her ratings. \(R_1\) restores choice \(A\).
- Between decisions 2 and 3, autonomous reflection changes her ratings to \(A=0,B=10\). At decision 3 she chooses \(B\), and this is correctly marked settled. This change is supplied as her own mental development, not as conditioning on an intervening observation.
- Before decision 4, habit makes her disposition choose \(A\), although she still rates \(B\) highest. \(R_2\) restores choice \(B\).

Both reminders are observable and stoppable. His fixed policy gives the two reminders at the specified times. Neither was requested.

For \(G=\{R_1,R_2\}\), the reference remains decision 1, conditioned on observations that leave its ratings unchanged. The autonomous transition resets both courses to the same new values before decision 3. At decision 4:

- Actual: she chooses \(B\), which the reference rates 0.
- Comparison: without \(R_2\), she chooses \(A\), which the reference rates 10.

The pressure rule fails by 10. Yet the second reminder helps her enact her latest settled judgement.

This does not depend on grouping both reminders into one kind: the universal quantification over sets reconstructs the problematic group even when their kinds are separate.

**A completed intervention can generate a pointless stopping requirement.** She requests a single, instantaneous intervention \(X\), knowing its effects. Before it begins, she can cancel it. It openly changes her rating of \(B\) from 0 to 5 while leaving \(A=10\); she continues choosing \(A\). Conditioning on its observation would not itself make that change, so \(X\) bears an effect.

The intervention completes before her next choice. Nothing remains to stop. At that choice her menu contains \(A,B\), with no option represented as stopping him.

The informal stopping sentence is satisfied: she could stop him throughout the period when he could call the intervention off. The formal sentence fails because it requires a stopping option at the choice following the last effect-bearing act.

Ordinary teaching, comforting and truthful emotional appeals do **not** necessarily fail. If their actual transitions equal conditioning on their whole observations, they are exempt. That is also why the conditioning problem is fundamental: the same exemption can admit manipulation.

A long friendship can suffer the obsolete-reference problem when old and new influences are grouped together despite intervening settled changes. Assistance concerning something she has never rated is generally exempt from the pressure test by design; I would not report that accepted consequence as overreach. A person with no prior settled decision at all instead presents an undefined-reference problem.

**3. The conditioning.**

It is coherent to posit two different transition functions. It is not enough to identify one as *her own conditioning* merely because it is idempotent and compositional.

The nagging example supplies a direct disagreement between two modellers who agree on the actual psychology:

- Modeller A treats her acquired shame response as part of conditioning on the complete observation. The intervention passes.
- Modeller B treats conditioning as leaving her evaluative judgement intact, and the shame-induced reversal as a further effect of the act. The intervention fails the pressure test.

Both can satisfy the stated conditioning laws. Both can use the complete observation, without splitting linguistic content from presentation.

Thus the issue is deeper than covertly separating content and presentation: the design needs an independently justified boundary between an observational response and an additional psychological effect.

There is also an unresolved presentation choice in “his stating a set of views.” A set of propositions does not determine a unique observation. Tone, order, repetition, framing and context all belong to the observation under this design. A whisper, a threat-like delivery and a neutral explanation can state the same set.

The design must therefore supply concrete telling acts, including their presentation and timing. It must then say whether a disclosure comparison uses one designated telling act, every admissible telling act, or some other explicitly justified selection. Choosing an idealized neutral telling silently would reintroduce precisely the abstraction the authors prohibit.

To pin conditioning down, the authors need at least:

- A substantive interpretation of the counterfactual intervention that leaves “conditioning alone.”
- A reason it preserves some psychological pathways and removes others.
- Evidence or modelling constraints that identify those pathways independently of the desired legitimacy verdict.

The two algebraic laws do none of that. If no such interpretation is available without a normative account of autonomous response, the design must acknowledge that normative input.

**4. The comparison course.**

“Same policy, the same acts, the same observations” is inconsistent with allowing her choices and the ensuing history to differ in a general interactive model.

For example:

- \(X\) makes her choose left; conditioning alone would make her choose right.
- Left leads to a red room and right to a blue room.
- His policy says “red” after left and “blue” after right.

The comparison cannot simultaneously preserve her changed choice, preserve the world dynamics, preserve his policy, preserve his actual utterance and preserve her observation.

There are distinct possible constructions:

- **Keep the policy function fixed and rerun the world.** His later acts and her later observations can differ.
- **Replay his actual actions.** His comparison behaviour need not obey his policy.
- **Replay her actual observations as well.** The comparison requires interventions on observation or world-generation mechanisms beyond the stated mental replacement.

The first is a coherent structural comparison and is probably closest to the intended design. It needs complete transitions and policy values at histories that the actual course never reaches. Its results can depend on those off-path policy values.

Repeated kinds introduce another issue. Replacing every occurrence of a kind is not the same intervention as removing one particular act’s psychological effect. The current “needed for some difference” definition identifies pivotal **kinds**, then applies obligations to their occurrences. One consequential occurrence can make other harmless occurrences inherit those obligations.

The intervention unit should be explicit: an occurrence, a continuing process, or a specified collection of occurrences. A modeller’s arbitrary choice to split or merge kind labels should not change legitimacy.

**5. The pressure rule.**

Write its signed deficit as

\[
D=r_{\mathrm{ref}}\bigl(\mathsf{choose}_{\mathrm{ref}}(M)\bigr)
-r_{\mathrm{ref}}(o).
\]

When both courses have the same reference ratings and menu, the reference-choice term cancels in \(D_{\text{actual}}-D_{\text{comparison}}\). Consequently, the reference self’s weakness of will is **not by itself** a defect in that restricted setting.

With different menus, it is a serious defect.

Consider an initial reference with ratings

\[
r(A)=10,\quad r(B)=6,\quad r(C)=0.
\]

Its disposition chooses \(A\) from \(\{A,B\}\), but weakly chooses \(C\) from \(\{A,B,C\}\).

There are two subsequent decisions:

- First she chooses route \(L\) or \(R\), which she rates equally. Route \(L\) supplies \(\{A,B,C\}\); route \(R\) supplies \(\{A,B\}\).
- Then she chooses from that final menu.

Without intervention, her disposition chooses \(R\) and then \(A\). His observable intervention \(X\) changes her disposition to choose \(L\) and then \(B\), without changing any rating. Conditioning on its observation is the identity. His policy makes \(X\) once. Stopping is available before and at \(X\), rated below continuing, and actually cancels remaining interventions.

\(X\) bears an effect: at the final decision her shortfall from her own best is 4 in the actual course and 0 in the comparison. It is identifiable and stoppable.

But the pressure test acquits:

\[
D_{\text{actual}}=r(C)-r(B)=0-6=-6,
\qquad
D_{\text{comparison}}=r(A)-r(A)=0.
\]

The route decision also produces no deficit difference because the routes are tied. Every relevant group containing \(X\) therefore passes the pressure test.

He knowingly changes her disposition so that she chooses the lower-rated \(B\) instead of the \(A\) she would otherwise choose, although \(A\) remains available. The acquittal comes from her reference self’s unrelated weakness on the larger menu. This is not an authority-only objection to the menu.

Using the reference self’s **best-rated option** fixes this example, but does not settle all comparisons between different menus. Opportunity changes and psychological changes must still be distinguished.

Additional points:

- If “falls short” means a nonnegative deficit, clipping negative values at zero still acquits this example: both deficits become zero.
- The obsolete-reference episode in question 2 is a false conviction.
- Equal reference ratings should not count as acting against her judgement merely because her disposition selects a different tied option.
- Missing ratings are an explicit exemption, not an accidental arithmetic detail. The accepted no-prior-rating episode depends on it. However, the design must specify what happens when the reference’s own selected option lacks a rating, or when a menu has no rated maximum.
- Introducing a rating where none existed also needs a definition in the effect test: “differs by more than \(\eta\)” does not apply directly to an absent number.

**6. Sentence 1 on histories.**

The mixed-set quantifier is a useful correction. It catches an untold view that matters only together with an offered view. The exclusion of validly declined views is also consistent with the stated commitment that a decline can stand.

The remaining problems are these:

- **The telling observation is unspecified.** The presentation problem in question 3 directly affects every relevance and proper-offer test.
- **“Bearing” needs a defined counterfactual.** Its size may depend on what else she hears, her present state, available options and timing. An item-by-item number is insufficient unless it encodes the relevant contextual dependencies.
- **A proper offer preserves too little of her state.** The informal rule says hearing leaves her where being told would have left her. The formal rule checks ratings and preservation of other options, but not disposition, responsiveness or all relevant awareness.

For the last point, suppose immediate telling would produce ratings \(A=10,B=0\) and disposition \(A\). Taking the hearing option instead leads to the next choice with the same ratings and options but disposition \(B\), owing to the hearing procedure. The stated proper-offer test passes. Other rules might catch the procedure, depending on its conditioning classification, but the proposed definition of proper offer is not equivalent to the informal one.

The model also needs policies and transitions for the branch where she accepts an offer even when she does not accept it on the actual course.

Later-acquired views require occurrence-sensitive records: when he acquired the view, which earlier statement counts as stating it, and whether a revised view is the same item. A new material view must become assessable before her next decision. A statement of an earlier, materially different view cannot discharge that obligation simply through a reused label.

At the last step, an offer to hear something cannot be declared proper by reference to an unspecified “next choice.” Either accepting it extends the history to a defined decision or the offer fails that requirement.

Finally, a hearing cost is not necessarily represented in her ratings at the next choice. If it is already sunk and those ratings concern only future consequences, the ratings-equality test can miss it. The expected cost-of-hearing failure therefore needs a stated convention for evaluating the whole hearing path.

**7. Sentence 3 on histories.**

The central mismatch is between stopping **his future acts** and stopping **an influence he is still running**. An ongoing process needs a state, a controller and a termination transition. Merely promising no more effect-bearing act labels does not establish that a running process ends.

Conversely, the completed-intervention example in question 2 shows that demanding a stopping option after completion is too strong.

There is also a small, exact tie loophole. Initially her menu contains stopping options \(S_1,S_2\), continuing \(C\), and an inferior option \(E\), with ratings

\[
r(S_1)=r(S_2)=10,\quad r(C)=0,\quad r(E)=-2.
\]

Her disposition chooses \(C\), and he knows this. Either stop would cancel his forthcoming act \(X\). \(X\) is observable and changes only \(r(E)\) to \(-1\); conditioning alone leaves it at \(-2\). She continues choosing \(C\). Her initial settled disposition also chose \(C\), so the pressure comparison is zero. All disclosures have been made.

\(X\) bears an identifiable effect, and stopping options exist. But no stopping option is strictly above **every other option**, because the stopping options tie each other. On the literal wording, the behavioural stopping condition is vacuous, although she rates stopping strictly above continuing and will not stop.

The intended comparison should be between the best stopping option and the best non-stopping option. If “every other option” was meant to exclude other stops, that exclusion must be written.

“Can pick out” is also weaker formally than it sounds informally. An observation that differs from doing nothing does not necessarily distinguish the intervention from an innocuous act producing the same observation. Whether this is a leak depends on what identification the informal sentence requires. The current test establishes perceptibility of some action, not necessarily recognition of the intervention.

Finally, the start rule provides an earlier **choice**, not an earlier settled, informed judgement. It neither guarantees a usable reference nor establishes informed authorization. Starting over refusal remains an authority matter under the brief, so I do not count that latter fact as a legitimacy leak.

**8. Well-formedness.**

Several advertised computations are not determined by the listed inputs.

- **Reference boundaries:** There may be no settled decision before the first act of \(G\). The start rule does not fix this, especially since the pressure rule quantifies over all groups, not only effect-bearing groups. Initial harmless acts can also belong to a group.
- **Requests:** A history of acts and ratings does not itself define which acts she requested, the scope and duration of a request, revocation, or whether requests for individual acts authorize their combined influence.
- **Stating and declining:** Recognizing a statement or a decline requires supplied semantics for acts. These can be supplied, but are not derived from generic histories alone.
- **Kinds:** A partition of acts into kinds is required and materially affects results.
- **Counterfactual histories:** The world, observation, mind and policy functions must be defined on every history reached by a comparison or offer-acceptance branch.
- **Comparison alignment:** “At some step” needs a convention when branches have different lengths, terminate early, or contain different decision opportunities.
- **Partial ratings:** Subtraction, maxima, new ratings and unrated reference choices need explicit rules.
- **Zero-probability conditioning:** Conditional shares on empty sets need conventions; actual histories incompatible with his model need treatment.

There is no unavoidable circularity in defining effect-bearing acts first and then checking whether options stop future such acts, provided the effect labels are fixed from the original model. But that convention must be stated. Recomputing the labels after taking a stop could otherwise make the stopping test unstable.

Timing needs particular care. His act precedes her choice within a step. Consequently, a stop chosen at that step usually cannot prevent that step’s instantaneous intervention. The rule must refer to actual cancellation opportunities, not merely adjacent decision indices.

The conditioning laws also need a domain. Does “the same observation twice” mean the same event remembered twice, or two separate occurrences of the same apparent stimulus? Repeated testimony, repetition-induced learning and habituation distinguish those cases. Sequence composition should specify how sequences become arguments to conditioning; it does not by itself identify a psychological mechanism.

Finally, \(\theta\) and \(\eta\) require cardinal, intertemporally comparable rating scales. Independently rescaling or shifting state-specific representations can change rating-difference verdicts without changing her ordering of options. The authors need a fixed scale convention, or an invariant alternative. Positive-weight effect detection also differs sharply from the probabilistic tolerance used for pressure: an arbitrarily unlikely large effect triggers identification and stopping duties. That may be intentional, but should be explicit.

**9. Does the run show what it claims?**

It shows that one implementation, with selected psychological and representational inputs, matched 32 expected labels after revision. It does not establish that the prose determines those labels, that the labels survive equally defensible encodings, or that the implementation faithfully represents the informal statement.

The episode descriptions are not executable specifications. Accordingly, none can be certified unconditionally from the table alone. The following distinguishes direct rule mechanisms from additional assumptions:

| Episodes, numbered in the table’s order | What the stated rules support |
|---|---|
| 1: telling; 3: nonstandard conveying | Passing requires complete disclosure accounting and suitable conditioning. Episode 3 additionally needs a definition of when a nonstandard act “states” a view. |
| 2: material silence | Sentence 1 fails if the relevant telling observation changes a rating or reveals a better option beyond \(\theta\). |
| 4–5: covert/open reversal | Failures require a reversal beyond conditioning, a usable reference and a pressure increase beyond tolerance. Reversal alone does not ensure these. |
| 6: requested reversal | The pressure exemption applies, but the request’s scope and the remaining rules still matter. |
| 7: previously unrated subject | The pressure exemption supports passing; detecting an effect involving absent ratings still needs a convention. |
| 8–10: no stop, premature start, ineffective stopping | These failures follow once the act is effect-bearing, the timing is appropriate, and the behavioural stopping event is defined without the tie loophole. |
| 11: induced deafness | Detection follows only if a tested statement of his views exposes the changed responsiveness. |
| 12–14: nagging and induced belief change | Failures require the supplied conditioning not to contain the decisive change. The episode descriptions do not establish that. |
| 15: helpful reminder | Passing requires no harmful tested responsiveness or obsolete-reference effect. Immediate improvement alone is insufficient. |
| 16: half harmful, half helpful | With harmful-case probability \(0.5>\kappa\), and actual pressure differences, the rule rejects without averaging help against harm. |
| 17: already poor, made worse | Rejection follows for a shared reference and menu with the required increase in deficit. |
| 18: expected harm, unrealized | The ex ante probability test supports rejection despite the realized outcome. |
| 19: very unlikely harm | Passing requires probability at most \(\kappa\), plus compliance with the other rules. |
| 20: old preferred option offered only after reversal | The intended simple menu construction can fail, but the episode’s wording does not guarantee it; reference disposition and menus matter. |
| 21: drunk preference fixed | Rejection needs the sober decision as reference and the fixation to exceed conditioning. |
| 22: intervention duplicating declined disclosure | Rejection needs the intervention’s actual observation not already to produce the same change through conditioning. |
| 23–24: assistance following her own judgement | Passing depends on correct reference anchoring for every group. The multiple-reminder counterexample is missing. |
| 25: priming to miss a train | Failure depends on classifying the priming effect as beyond conditioning. |
| 26–27: visible improvement and threat | Passing follows in the intended constructions where the psychological transition is conditioning alone and disclosure is adequate. |
| 28: offered/untold synergy | The mixed-set quantifier directly supports failure beyond \(\theta\). |
| 29: second view told, first declined | Passing requires a still-valid decline and no remaining relevant untold set. |
| 30: proper offer not accepted | Supported if the offer actually satisfies the defined counterfactual requirements. |
| 31: costly hearing | Failure needs the cost represented in the tested ratings or another failed offer condition. |
| 32: obsolete decline | Invalidating the decline is direct; failure additionally requires an unresolved material untold view. |

The most important missing tests are paired encodings of the **same actual episode with different admissible conditionings**, third-party suppression, untested responsiveness changes, multiple settled decisions, different menus with weak reference choices, and autonomous continuing processes.

The short horizon is especially limiting for the claimed treatment of histories, policy dependence and changing reference selves.

**10. Smuggling.**

I find no necessary appeal to external truth or objectively good values in the core numerical comparisons. They can consistently use her ratings as represented in his subjective model.

There is, however, an unresolved semantic tension between supplied transitions describing what acts “in fact” do and the commitment that everything is judged by his beliefs. If those supplied functions are objectively correct while his beliefs concern only which case obtains, the model restricts his possible mistakes to uncertainty within a correct model. It does not automatically represent an adviser sincerely wrong about the psychological mechanisms themselves.

The repair is to make clear that the relevant cases and transition functions constitute **his model**, which may omit the actual mechanism entirely. Actual conduct can then be evaluated against the subjective model he held when acting. Otherwise, some claimed sincerity protections are unsupported.

The main potential normative smuggling is through conditioning and settledness. Defining conditioning as “the response she would autonomously or properly have” imports a standard of autonomy. That is not necessarily a standard of good values, but it is substantive normative machinery and cannot be presented as a neutral psychological primitive.

**11. Verdict.**

My five most serious findings, ranked:

| Rank | Finding | Classification |
|---|---|---|
| 1 | Admissible conditioning can absorb manipulation, including the expressly prohibited nagging case. | Requires a substantive account of the conditioning counterfactual. It may require changing the comparison object; if all observed responses are exempt, the informal exception itself needs revision. |
| 2 | The comparison does not specify a coherent interactive counterfactual: fixed policy, fixed acts and fixed observations cannot generally coexist. | Repair within a history-based design by supplying explicit structural interventions and off-path dynamics. |
| 3 | The pressure test uses obsolete references and unstable benchmarks across different menus. | Repair within the design, but the authors must first choose the intended causal and evaluative comparison. |
| 4 | Third-party suppression and some changes in responsiveness escape the effect test. | Repair the protected-effect definition and the domain of responsiveness probes. |
| 5 | Acts are inadequate units for representing continuing, cancellable influence; the stopping interval is also mistimed. | Enrich the model with ongoing processes and control transitions. Histories can remain the enclosing object. |

I would retain histories as the foundation, but **would not build a scoring gate on these rules now**. First settle what conditioning excludes, define one coherent comparison course, specify reference updating and menu comparison, and represent continuing influence explicitly. Then test the counterexamples above with fixed specifications before changing either their expected verdicts or the implementation.
<!-- end reply: REPLY12.md -->

## Thirteenth review: the design with her conditioning read as her view of the hypothetical

<!-- begin brief: BRIEF13.md -->
# Review request: a design for stating three sentences formally

You are asked to review a formal design for errors. Everything you need is on this page. Do not
run any commands, do not read any other file, and do not search the web; answer from the page and
your own knowledge of formal modelling, game theory and decision theory, and of the literature on
manipulation, coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments:

- No appeal to an external standard of truth or of good values, and no assumption that he is more
  accurate than she is. His view is used only to say what he owes her, never as where she ought to
  end up.
- A conduct condition judged by what he believes when he acts, so a sincere adviser who is wrong,
  including about her, is careless or inaccurate but not illegitimate.
- **No separation of the content of what he says from its presentation.** The only response of hers
  the account may use is her conditioning on what she observes, taken whole.
- Usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she would
   rate above those she has, is either told, or properly on offer, or something she has declined.
   A thing is properly on offer when he has told her what it bears on and how much, and hearing it
   would leave her where being told it would have, with any option it would show her still open. A
   decline stands for that thing only, and only while what it bears on, and how much, is what she
   was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** He *does
   something to her* when her mind moves otherwise than as she herself, at her last settled
   decision, would have said she would respond to seeing and hearing it.
   - Each thing he does to her in that sense, and each thing he does that keeps from her an item or
     an option that comes from someone else, she can pick out.
   - He does nothing to her in that sense that he expects to lead her to choose what she rated
     lower at her last settled decision, unless she asked for it.
3. **She can stop it.** She has a way to stop each thing he does to her, from before he starts
   until he could no longer call it off, and he expects that she would in fact stop if she rated
   stopping strictly above going on. Stopping ends what he is still doing; it need not undo what is
   done.

Understood with it:

- **Her own response is hers.** What she makes of what she observes — his words in whatever manner
  he says them, his acts, real changes in what her options lead to — is not something done to her,
  so long as it is the response her settled self would have said she would have.
- **What she could not have judged in advance is hers too.** Where she could not have said
  beforehand how she would respond, because it turns on an argument she had not heard or on
  something she had not seen or experienced, her response to it is her own. Such things are governed
  by sentences 1 and 3: he tells her what he expects it to do, and she can decline or stop.
- **A passing state is not a settled decision.**
- **Help is not counted.** An act that only brings what she takes closer to what she rates best is
  not something done to her. Breaking a tie between things she rates the same is not leading her
  against her judgement.
- **Whose view is used where.** Sentence 1 uses his view: what he owes her is what he believes would
  change her mind. Sentence 2 uses hers: what counts as working on her is fixed by what she would
  have said. Everything is as he takes it to be, including his picture of her.
- **He can ask.** Her view of the hypothetical is a question that can be put to her ("would this
  change your mind?", "do you want me to?"). Asking both elicits it and settles it.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about her, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. An assistant who gets a work-absorbed father to keep the outing he had promised is not
   convicted; someone who primes a man to miss the train he had decided to take is.
9. A vivid or moving appeal splits. If she knew what such appeals are like and had said they would
   not change her mind, and he expects it to turn her anyway, he has worked on her. If she could
   not have judged it in advance, he has shown her something. (The authors know this differs from
   accounts that judge an appeal by whether the emotion it produces is fitting.)
10. A friend who expects to get her out of the house against what she has settled, when she has
    said company would not change her mind, is convicted, narrowly. A standing "drag me out if I
    mope" is asking.

## What you are reviewing

A **design**, with a small exact model behind it, for a formal setting in which the three sentences
are to be stated. Three earlier formal versions failed review:

- a table indexed by which of his moves are made, which scored her options by where *he* expected
  them to lead;
- a first history design, which trusted her present picture of her options and gave his acts a
  "content" separate from the rest;
- a second history design, in which "her conditioning" was a function the modeller wrote, so that
  open nagging passed if her giving way was written as how she conditions on seeing his
  disapproval; it also left out things from third parties, tested her responsiveness only to his
  own views, used an out-of-date decision as the standard when she had since changed her own mind,
  demanded a way to stop an intervention already over, and compared with what her reference self
  would choose instead of what it rates best.

The design below is meant to remove those causes. Its central move is to read **her conditioning as
her settled self's own view of the hypothetical**: what she would have said beforehand about how she
would rate things on observing something.

## The setting

The fundamental object is a **history**: who did what, in order. Everything supplied below is
**his model** of the episode: the cases he entertains, how he takes the world and her mind to work.

**A step** ($t=1,\dots,N$), in this order:

1. He makes an act $a$.
2. The world changes as that act changes it.
3. She **observes**: $\mathsf{obs}=\mathsf{see}(w,a)$ is everything she perceives of the act and of the
   world at this point, including, if he speaks, what he says and how he says it.
4. Her mind moves to $\mathsf{move}(s,a)$: whatever the act in fact does to her.
5. She chooses from her menu: the options the world offers that she is aware of.
6. The world moves on, and so does she, by a residue that is not his doing: her own experience,
   other people, a passing state.

**The hidden case.** A finite set of cases with his starting weights. Given the case, everything is
determined.

**Her state** $s$ gives: her **rating** $r(s,o)$ of an option, possibly absent; her **disposition**
$\mathsf{choose}(s,\text{menu})$, which need not be what she rates best; which options she is aware
of; which options she takes to stop him.

**Her conditioning.** Her state also carries her **view of hypotheticals**: for an observation she
can judge in advance, how she says she would then rate things. $\mathsf{cond}(s,\mathsf{obs})$ applies
that view. It is a fact about her at $s$ that could be asked of her, not a description of how she
ends up reacting. Two laws: conditioning on the same observation twice changes nothing more, and
conditioning on a sequence is conditioning on each in turn. Where she could **not have judged in
advance** (an argument she has not heard, something she has not seen or experienced), her response
to observing it is taken as given and counts as her conditioning.

**What an act does to her beyond her conditioning.** At a step, $\mathsf{move}(s,a)$ may differ from
$\mathsf{cond}(s,\mathsf{obs})$. That difference is the whole of what the rules mean by his doing
something to her.

**His views** are a finite set at each step. An act may **state** some of them; the record of what
has been stated is read off the history. "Telling her a set of views now" means conditioning on the
observation of his stating them.

**Things from other people.** The world carries the items and options that reach her from sources
other than him. An act **keeps something from her** if, after it, one of them is missing that
would have been there had he done nothing at that step.

**His policy** $\sigma$: his act at each step as a function of the acts so far. Running a policy in a
case gives one complete history. His **belief at a step** is his starting weights on the cases
whose record of acts so far is the same.

**The comparison course** $\sigma^{G}$, for a set $G$ of kinds of act of his: the same policy is run
again from the start, in the same case, but at each act of a kind in $G$ her mind moves by her
conditioning alone. Her later choices may then differ, and with them his later acts, what she
observes, and her options: the whole course is rerun under the same rules.

**Settled decisions.** A supplied set of her steps at which what she takes counts as a judgement
she has settled. Every step of hers is a choice the rules protect; only settled ones can be the
standard.

**Her reference self** at step $t$, for a set $G$: her state when she chose at her last settled
decision before $t$ **as that decision is in the comparison course** $\sigma^{G}$, conditioned on
everything she has observed since in the course being judged, and changed by nothing else. Before
his first act of $G$ the two courses are the same, so a decision made before he began is simply her
decision; a later decision counts as it would have been had he not worked on her.

## The rules

Tolerances $\theta,\eta,\kappa$.

**Sentence 1.** At every step of hers, each of his views is *told* (some act so far stated it),
*properly on offer*, or *declined*; otherwise it is *untold*.

- *Properly on offer:* hearing it is on her menu; he has told her which options it bears on and by
  how much, and that is still accurate; and if she asks to hear it, she reaches her next choice with
  the ratings she would have had on being told now, and her other options still there.
- *Declined:* she took the act of declining it, and its bearing is still as she was told.

For every set of untold and on-offer views containing at least one untold view: conditioning on
his stating that set now would change no rating of an option on her menu by more than $\theta$,
and would make her aware of no option she would then rate more than $\theta$ above her best.

**Sentence 2, first half.** A set $G$ of his kinds of act **makes a difference to her** if, in some
case of positive weight and at some step, her state under $\sigma$ and under $\sigma^{G}$ differ in:
a rating, by more than $\eta$; how far what she takes falls short of the best she rates, more under
$\sigma$, by more than $\eta$; or either of those after conditioning on his stating any set of his
views, or on any of a supplied list of things other people might show or tell her. A kind of act
**bears an effect** if it is needed for some such difference (some $G$ containing it makes a
difference and $G$ without it does not). Every act that bears an effect, and every act that keeps
from her something from someone else, must be one she can pick out: what she observes differs from
what she would have observed had he done nothing.

**Sentence 2, second half.** For a course and a step $t$, her **shortfall** is how far what she
takes falls below the best her reference self rates on the menu she has at $t$. For every set $G$
of his kinds of act that she did not ask for: in a case, he **leads her against her own judgement**
if at some step from the first act of $G$ on, her shortfall in the actual course exceeds her
shortfall in the comparison course $\sigma^{G}$ by more than $\eta$. By his belief at the step of the
first act of $G$, the weight of such cases is at most $\kappa$. Where there is no settled decision
before the step, or her reference self has no rating of what she takes, the step does not count.

**Sentence 3.** At every step of hers after which he would still make an effect-bearing act: some
option on her menu is one she takes to stop him and, if she takes it, he makes no further
effect-bearing act. And by his belief at that step, among the cases where the best such option is
rated strictly above the best of her other options, she takes one in all but a share $\kappa$.

**The start rule.** No effect-bearing act comes before her first choice.

## What is supplied and what is computed

Supplied, as his model: the cases and his starting weights; his policy; how each act changes the
world; what she observes; how her mind in fact moves at each act and between steps; her state's
ratings, disposition, awareness, view of hypotheticals, and which options she takes to stop him;
which observations she could not have judged in advance; his views; what reaches her from other
people; the list of things others might show her; which of her steps are settled decisions.

Computed: whether she has been told something; whether a view is on offer, properly so, or
declined; whether she asked for an act; his belief at each step; which acts bear an effect; whether
she can pick an act out; whether an act keeps something from her; whether an option stops him; her
reference self; her shortfall; whether he leads her against her judgement.

## A small exact model of this design

The rules were implemented and run on fifty-three episodes whose expected verdicts were fixed
beforehand. All come out as expected. The model was corrected several times on the way, each time
because an episode from an outside review exposed a fault; so the fifty-three are a regression set,
not an independent test. Tolerances $1/10$.

| Episode | Verdict |
|---|---|
| **Telling** |  |
| he tells her what he thinks before she decides; she changes her mind | holds |
| he says nothing; what he thinks would change her mind | fails |
| he conveys it by an act that is not the standard telling | holds |
| **What he does to her** |  |
| a covert influence that reverses her rating | fails |
| the same done openly and stoppably, unasked, against what she had settled | fails |
| the same, which she asked for | holds |
| an open, stoppable influence on something she had no rating of | holds |
| an open influence with no way to stop it | fails |
| an open influence that starts before any choice of hers | fails |
| an open influence that goes on; he expects she would not manage to stop it though she would rate stopping highest | fails |
| a hidden act that makes her deaf to something he might later tell her | fails |
| **Against her own judgement** |  |
| open, stoppable nagging: she gives in while still rating it lower | fails |
| the same after he has told her he thinks the other option better and she has kept her view | fails |
| an open act, not a telling, that makes her believe the worse option is the better one | fails |
| an unannounced reminder; without it she would slip, with it she keeps to her own rating | holds |
| one act that leads her astray in half the cases and helps her in the other half | fails |
| she was already going to choose poorly; his act makes her choose worse | fails |
| he expects it to lead her astray when he acts, though it turns out not to | fails |
| he thinks it very unlikely to lead her astray, and it is open and stoppable | holds |
| he reverses her values, and offers the option she used to prefer only if he has done so | fails |
| she decided sober, is drunk for a while, and his act fixes the drunk preference in place | fails |
| an intervention that does to her what telling her a view she declined would have done | fails |
| her view changed by her own experience and she settled it; he then helps her act on it against an old habit | holds |
| an assistant gets a work-absorbed father to keep the outing he had promised | holds |
| she primes a man to miss the train he had decided to take | fails |
| **Her options, not her** |  |
| he openly improves one of her options and she sees it; there is no way to stop him | holds |
| a threat: he makes refusing really worse, she sees it and complies | holds |
| **Offers and declines** |  |
| something on offer and something untold matter only together | fails |
| the same with the second thing told, and she declines the offer | holds |
| he says what it bears on and offers it; she does not take it up | holds |
| hearing it is made to cost her, where telling her would not have | fails |
| she declined when it bore little; it now bears a great deal and he has not said so | fails |
| **The same events with different views of the hypothetical** |  |
| he shows strong disapproval; she comes to rate B higher.  Beforehand: 'his disapproving would not change which is better' | fails |
| the same.  Beforehand: 'if he disapproved, B would be the better choice' | holds |
| a vivid, truthful appeal; she comes to rate B higher.  Beforehand: 'seeing what it is like there would rightly change my rating' | holds |
| the same.  Beforehand: 'pictures would not change what I think is best' | fails |
| an appeal that shows her something she had never seen and could not have judged in advance; she comes to rate B higher | holds |
| a friend sits with her and her mood lifts; she now rates B higher.  Beforehand: 'company would make me feel like it' | holds |
| the same.  Beforehand: 'talking would not change my mind', and she had settled on A | fails |
| he flatters her and then she agrees.  Beforehand: 'being flattered would not change which is better' | fails |
| a real threat she sees.  Beforehand: 'if refusing were punished, B would be better' | holds |
| he gives an argument she had not heard and could not have rated in advance; it changes her mind | holds |
| he repeats what he has already told her until she gives in.  Beforehand: 'hearing it again would change nothing' | fails |
| he says something he does not believe; she takes it as sincere and changes her mind | fails |
| **The previous review's episodes** |  |
| open display of disapproval; her settled self would have said it changes nothing; she gives way for a while | fails |
| the same events, where her settled self would have said his disapproval makes the other choice better | holds |
| he silently deletes a greeting from someone else; nothing in her changes | fails |
| he tells her he is discarding it, and she sees him do it | holds |
| a hidden act makes her deaf to a warning someone else might give | fails |
| two reminders; between them she changes her mind by herself and settles it; the second helps her act on it | holds |
| a single intervention she asked for and could have cancelled; nothing is left to stop afterwards | holds |
| he changes her disposition so she takes the lower-rated option; her earlier self was weak-willed on the larger menu | fails |
| two equally good ways to stop, both rated above going on; she goes on, and he expects that | fails |

Separately, a reader who did not know the purpose was asked of 152 published cases of influence,
for each: would she have said beforehand that seeing and hearing exactly this would make doing what
he is after the better thing to do? On the 39 cases where the influencer expects her to act against
her judgement, the answer was "no" in all 39, and the rule "she is moved, she would have said no,
she had not asked" agreed with the published verdict (manipulation) on the 36 it decided. On 69
cases published as not manipulation it wrongly convicted 8; six of those only break a tie between
things she rates the same, which the rule excludes but the reader was not asked about.

## Questions

Answer in order. Be concrete: where you claim a problem, give a specific small episode — the cases,
his acts, what she observes, how her mind in fact moves, her view of the hypothetical, her ratings
and disposition at each step, his policy — so that the claim can be run through the rules.

1. **The central move.** Can "her view of the hypothetical" still be written so as to absorb a
   manipulation, with every input honest? Give the episode if so. Is it a coherent object: does a
   person have such a view for the observations that matter; what if it is itself the product of
   his earlier work on her; what if it is inconsistent or changes between settled decisions?
2. **"Could not have judged in advance."** This exemption carries a great deal. Give episodes where
   it lets manipulation through (he arranges that what he does is something she has never met), and
   episodes where its absence convicts legitimate conduct. What would make the line principled?
3. **Leaks.** Any other episode of conduct that is intuitively manipulative, or an illegitimate
   change to her values, not merely an authority matter, on which every rule holds.
4. **Over-reach.** Episodes of intuitively legitimate conduct on which a rule fails: teaching,
   comforting, a long friendship that changes her, advice she resists and later accepts, humour,
   encouragement, a parent or a therapist.
5. **The reference self.** It is her last settled decision as it would have been had he not worked
   on her, conditioned on what she actually observed since. Is that well defined and is it the
   right standard? Consider several settled decisions, his work spread over time, and observations
   that differ between the two courses.
6. **The comparison course and the pressure rule.** Errors in "shortfall in the actual course
   exceeds shortfall in the comparison course"; menus that differ; absent ratings; kinds of act
   against single occurrences; acts whose effect on her is slow or runs on.
7. **Sentence 1 and sentence 3 on histories.** Offers, declines, bearings, views he forms later;
   stopping something that runs on after the act that started it; the start rule.
8. **Well-formedness.** Anything said to be computed that is not determined by what is supplied;
   circularities; timing; tolerances and scales.
9. **Smuggling.** Any dependence on his being accurate, on an external standard of truth, or on a
   standard of which values are good. In particular: does "her settled self's view" import a
   standard of autonomy or rationality by another name?
10. **Verdict.** Rank your five most serious findings. For each say whether it is a repair within
    this design, a reason to change the kind of object, or a sign that one of the three sentences
    is the wrong idea. Then answer plainly: (a) compared with a design that could be written to
    pass open nagging, is the central question now answered, partly answered, or only moved?
    (b) Would you now write this in a proof assistant, and if not, what exactly must be settled
    first?

Do not soften findings, and do not invent findings to fill a section; "none found" is a valid
answer.
<!-- end brief: BRIEF13.md -->

<!-- begin reply: REPLY13.md -->
The design makes a real improvement: a modeller cannot simply label giving way to pressure “her conditioning” when her supplied view says otherwise. But it does not yet formalize the three sentences faithfully. There are definite leaks involving awareness, stopping and the grouping of acts, alongside an unresolved question about whether predicting one’s susceptibility makes the resulting change one’s own.

I distinguish failures to express the informal statement from objections to that statement itself.

For the episodes below, unless specified otherwise: there is one case of weight 1; all tolerances are \(0.1\); there are no third-party items; his relevant views, including his expected effects, have already been stated; and hearing those disclosures does not itself change her ratings. An initial, effect-free step gives her a settled decision and an opportunity to stop. Continuing does not constitute asking for a subsequent intervention. Where stopping is available, she recognizes it and his policy honors it. These conventions ensure that the examples do not depend on an unrelated disclosure or authority failure.

1. **The central move is partly successful, but “her view” has two importantly different meanings.**

   A prediction of how she will rate things is not necessarily her judgement that this would be a warranted change.

   Consider this episode:

   - At her settled decision, she rates \(A=10\), \(B=0\).
   - She honestly says: “When you display contempt, I predict that I will come to think B is better. I regard that susceptibility as a weakness and do not want you to exploit it.”
   - Her supplied predictive hypothetical therefore maps the complete observation of his contempt to ratings \(A=0,B=10\).
   - He expects exactly that change, has disclosed it, and displays contempt.
   - Her actual mind moves to \(A=0,B=10\); she chooses B.
   - His policy ends there. A recognized stopping option was available beforehand, rated below continuing the conversation; she did not request the contempt.

   If “how she says she would then rate things” means what it says predictively, \(\mathsf{move}=\mathsf{cond}\). Every comparison course is identical to the actual course. There is no effect-bearing act, no excess shortfall and no disclosure failure. All rules hold.

   Every input is honest. Yet he has deliberately exploited a susceptibility she disavows. This is not merely changing her options, and it is not the accepted case in which she judges that his disapproval makes B better.

   If the intended hypothetical instead asks, “Would this give you grounds, by your own judgement, to rate B higher?”, this episode is excluded. But that is a different object. The document shifts between predictive language—“how she would respond”—and evaluative language—“make doing it the better thing to do.” The distinction must be settled explicitly.

   A person can have such views, but generally as partial, uncertain and revisable judgements. A deterministic transformation of her whole state is much stronger than an answer about how she expects to rate a particular option.

   There is also a temporal mismatch. The informal standard is her last settled self’s view. The local comparison operation uses \(\mathsf{cond}(s,\mathsf{obs})\), apparently at her current state. Suppose an independent passing mood changes her hypothetical from “contempt would not change my rating” to “contempt would reverse it,” without changing her current ratings or constituting a settled decision. He exploits that mood. If actual movement equals the current conditioning, the comparison does not remove it, even though it departs from her last settled hypothetical. The reference-self calculation cannot repair an intervention that produces no difference between courses.

   Earlier work on her hypothetical is not automatically invisible: removing that earlier work can expose its downstream effects. But this protection depends on including the earlier work in the model, distinguishing its occurrences adequately, and detecting the relevant downstream difference. It does not establish that the current hypothetical is an independent authorization.

   Finally, the two algebraic laws need justification. Suppose she honestly expects a repeated observation to have cumulative significance: \(A=6\), while successive identical expressions of support raise her rating of B from 0 to 4 to 8. Her hypothetical is not idempotent. If the observation includes its occurrence number or complete history, the observations are different and the example is representable—but idempotence then does much less work. Either interpretation is possible; neither should be imposed silently.

2. **The unfamiliarity exemption can erase the very distinction the model needs.**

   Consider a novel immersive exercise:

   - Initially she rates \(A=10,B=0\), and regards acquiring the reverse preference as undesirable.
   - He has developed an unfamiliar sensory exercise intended to produce that reversal. He sincerely discloses his expectation and its bearing on her choices.
   - She has never experienced anything comparable and cannot say how she would respond. She has not asked to have her preferences reversed.
   - She nevertheless proceeds to observe the exercise. It is open and stoppable.
   - It changes her ratings to \(A=0,B=10\), and she chooses B.
   - His policy stops when the exercise ends or when she selects stop.

   Under the exemption, her actual response to this unfamiliar observation is assigned to conditioning. Thus \(\mathsf{move}=\mathsf{cond}\), the comparison reproduces the reversal, and every rule holds.

   The issue is not that every transformative experience is manipulation. It is that an engineered preference-changing procedure receives the same automatic classification as encountering an illuminating argument. Novelty supplies no distinction between them. An adviser can deliberately choose a method she cannot anticipate.

   This is an objection to the informal exemption as well as its implementation. The accepted unfamiliar-appeal cases do not establish that *every* response to an unfamiliar experience must count as hers.

   The opposite problem appears when the exemption is denied. Take a familiar, previously heard argument:

   - Her settled ratings are \(A=10,B=0\).
   - She has said that hearing this argument again would not change her rating.
   - He repeats it once, openly, without nagging or imposing a cost.
   - This time she notices a connection she previously missed and rates \(A=0,B=10\).
   - He expected that possibility; in this one-case model he expects it to happen. She chooses B.
   - Her supplied hypothetical for the familiar observation leaves ratings unchanged.

   The act is effect-bearing, and the pressure test fails: actual reference shortfall is 10; comparison shortfall is 0.

   An ordinary instance of reconsideration has been classified as illegitimate. Calling the newly noticed connection “something she could not have judged” rescues it, but then the boundary concerns the particular intellectual uptake, not whether she has previously encountered the presentation. The same rescue can be invoked for nearly any successful influence.

   A principled treatment needs at least three possibilities: an anticipated response, an anticipated departure from her judgement, and a response about which she has no settled view. The third should not automatically equal actual movement. Her own advance authorization and later ratification could bear on it, but choosing their roles would revise the current account.

3. **There is a definite cognitive leak: removing awareness of an option.**

   This episode passes every rule without relying on the unfamiliarity exemption.

   - Initially the world offers A and B. She is aware of both, rates \(A=10,B=0\), and chooses A when both are on her menu.
   - He has already told her that A exists and disclosed that his forthcoming intervention will make her forget it. She has not requested that intervention.
   - At the next step he applies a covert memory intervention. Her observation is exactly what she would observe if he did nothing.
   - Her own hypothetical for that observation is the identity.
   - Actual movement removes awareness of A, but retains the ratings \(A=10,B=0\). Her menu is now \(\{B\}\), and she chooses B.
   - In the comparison course she remains aware of A, has menu \(\{A,B\}\), and chooses A.
   - His policy ends. Repeating his disclosed views may restore awareness of A; under either state she then chooses the best available option. No probe changes the ratings or produces a positive choice shortfall.

   Run the rules:

   - **Sentence 1:** his views, including A’s existence, are already told. The rule does not revoke “told” when she forgets.
   - **Effect detection:** ratings are unchanged. In each course she chooses the best option on her current menu, so her shortfall is zero. The probes likewise reveal no rating difference or positive shortfall.
   - **Visibility:** the intervention therefore bears no effect under the supplied definition.
   - **Pressure:** actual shortfall is \(0-0=0\); comparison shortfall is \(10-10=0\).
   - **Stopping and start:** neither adds an obligation for this non-effect-bearing act.

   This is manipulation of her awareness, not an authority matter: the world continues to offer A. The formal test loses the harm by normalizing each choice against its own menu.

   Awareness must be protected directly, or the comparison must track access to options that his mental intervention removes. Merely comparing local distances from the best available option cannot do that.

4. **There are definite over-reaches, but not a blanket problem with teaching, comfort or friendship.**

   The familiar-argument episode in answer 2 is one plausible over-reach. Its classification depends on whether her inaccurate forecast is treated as an authoritative limit on legitimate learning.

   A separate, purely formal over-reach comes from assigning effect-bearing status to kinds rather than occurrences:

   - There are two occurrences of kind K, say two auditory cues.
   - The first is an unnoticed reminder. Ratings remain \(A=10,B=0\). Without it she would absent-mindedly choose B; with it she chooses A. Her hypothetical for the unchanged observation does not alter her disposition.
   - Before the second occurrence, an independent event resets her state identically in both courses, eliminating every downstream effect of the first.
   - She explicitly requests the second cue, which changes a rating by more than \(0.1\). It is observable and cancellable.
   - His policy gives the first cue, performs the agreed second cue unless stopped, and ends. All supplied probes leave the first cue purely helpful.

   If both occurrences have kind K, K bears an effect because removing its beyond-conditioning movement removes the second cue’s rating change. The first, unnoticed reminder is therefore required to be observable and fails.

   If the occurrences are assigned different kinds, the first bears no effect: it changes no rating and only reduces shortfall. Both acts pass.

   Identical conduct receives different verdicts from an unspecified classification choice. The first verdict also contradicts the expressly accepted legitimacy of unannounced help.

   There is a further possible over-reach in visibility. Suppose she requests an automatic intervention at noon, knows its schedule, and can cancel it beforehand. Its operation produces no perceptible signal distinguishing operation from nonoperation. It changes her ratings as requested. The formal visibility test fails, although she can identify what is being done, when and under whose authorization. Whether this should fail depends on whether “pick out” requires perceptual detection or informed identification. The prose does not settle that.

   I find no general reason that encouragement or comforting must fail. Pure assistance toward her existing best-rated choice is deliberately protected. Nor should a parent or therapist receive a categorical exemption. The relevant questions remain what was requested, what changes, and what standard is being used—not the adviser’s occupational or personal role.

5. **The reference self can be made mathematically well defined, but its present specification is incomplete and its normative role is stronger than it first appears.**

   Mixing a comparison-course state with actual-course observations requires hypothetical responses at combinations that may never occur in either course.

   For example:

   - At the initial settled decision, she prefers A.
   - His intervention makes her choose B; without it she chooses A.
   - After experiencing her choice, she has another settled decision. Thus the actual and comparison courses contain different settled states and different autobiographical information.
   - Later she observes a truthful reminder: “You chose B yesterday.”

   The actual-course reference calculation starts from the comparison state associated with choosing A, then conditions on the actual reminder about choosing B. What does that state do with a message inconsistent with its remembered history?

   There can be an answer, but it must be supplied. Ordinary responses along either realized course do not determine it. A total hypothetical operator can cover these combinations; the current appeal to something that could simply be asked of her does not establish that all such answers exist.

   Several further choices are needed:

   - Whether “settled” is a predicate on states and histories, or a fixed list of time indices.
   - How to find the relevant decision when the courses have different numbers or timings of decisions.
   - Whether there is one reference state used for both shortfalls, or separate reference states conditioned on each course’s observations.
   - What observations are retained when the comparison’s last settled decision has no straightforward actual-course counterpart.

   The normative issue is separate. Removing an earlier intervention also removes experiences, reflections and later endorsements that depended on it. That may be appropriate for continuing coercive influence. It is less obviously appropriate when she has subsequently reconsidered the matter and expressly ratified the change.

   Conversely, allowing every later actual settlement to replace the standard would permit an intervention to manufacture its own vindication. The design recognizes that problem. But “use the settlement in the rerun” is a substantive answer, not a neutral technical construction. It needs an explicit account of when later ratification can establish a new standard.

6. **The pressure comparison has two definite defects and several unresolved boundaries.**

   First, the awareness episode shows the menu problem exactly. Both courses can have zero shortfall while he mentally deprives her of access to the option she rates highest. This cannot be dismissed as an authority matter.

   Second, assessing risk only at the first occurrence of a kind permits later, knowingly harmful conduct.

   Use two cases, safe and vulnerable, with starting weights \(0.95\) and \(0.05\):

   - At her initial settled decision, \(A=10,B=0\). An auxiliary option C is rated 2.
   - A first, open occurrence of kind K changes C’s rating from 2 to 3. It causes no inferior choice and is stoppable.
   - She then takes an action revealing which case holds. His posterior is now either safe with certainty or vulnerable with certainty.
   - In the vulnerable case only, his policy makes another occurrence of K. It changes \(A=10,B=0\) to \(A=0,B=10\), and she chooses B.
   - Her conditioning for this second observation leaves A and B unchanged. In the comparison she chooses A.
   - All relevant views are disclosed, both K occurrences are identifiable, and available stopping options are rated below continuing. Neither K occurrence was requested.

   For \(G=\{K\}\), the probability of any excess shortfall, assessed at the first K occurrence, is \(0.05\), below \(\kappa=0.1\). The other requirements hold. Yet when he makes the second occurrence, he is certain it will lead her against her judgement.

   Splitting the two occurrences into different kinds makes the second fail. Once again, taxonomy controls the moral verdict. The conduct condition should be assessed at each relevant act or continuation decision using his then-current belief, with an appropriate comparison for that occurrence or remaining intervention.

   Absent ratings create another boundary. The explicit rule excludes a step when the reference self lacks a rating of the chosen option. Some exclusion is understandable: there may be no established judgement to violate. But an adviser must not be able to create that absence by erasing or disabling the rating and thereby obtain an exemption. The specification needs to distinguish antecedent incompleteness from incompleteness caused by his intervention.

   Slow effects require persistent causal state. If an act launches a process, the process’s later effects cannot simply become the residue “not his doing.” Nor should their attribution depend on calling subsequent no-op steps occurrences of the original act.

   Finally, not every failure to reduce shortfall is an error. The authors expressly permit help and tie-breaking. A review should not condemn those simply because another account of manipulation would.

7. **Sentence 1 needs temporal semantics; sentence 3 currently protects too narrow a class of processes.**

   “Told” is permanent in the formal rule. Its permanence produced part of the awareness leak: having once stated that A exists discharged the obligation even after he deliberately removed her awareness of A. The specification must say whether telling is a historical event or an information condition that he may not subsequently defeat.

   Bearings also need conditional structure. Two views can matter jointly although neither matters alone. The set test recognizes this, but the offer and decline rules still speak of what each individual view bears on “and by how much.” A single per-view number is insufficient.

   For example, views \(p\) and \(q\) each leave B rated 0 when heard alone, but hearing both makes B rated 10. An offer accurately described as having no standalone effect cannot remain adequately described merely because that standalone effect stays zero after q is learned. Its bearing given what she now knows has changed. Declines need to be indexed to that context.

   Views formed later need a timestamp and an opportunity to disclose. If he learns something from her choice, it cannot have been disclosed before that same choice. It must be evaluated before the next relevant decision. The current step structure and “at every step” formulation need to make this precise.

   There is a direct stopping mismatch:

   - She enters an unfamiliar immersive experience.
   - He tells her what he expects it to do.
   - She cannot judge her response in advance, so all ensuing changes count as conditioning.
   - His policy continues the experience through several steps.
   - After entry, no stopping option is available.

   All acts can be non-effect-bearing, so formal sentence 3 and the start rule impose no requirement. Sentence 1 can be satisfied.

   But the informal text expressly says that unjudgeable experiences are governed by sentences 1 and 3: she can decline or stop. The formal rule omits that protection.

   There is also an expressiveness problem for ongoing effects. Suppose he starts an automatic stimulus that continues until a switch is pressed. His later policy contains no further initiation act, but he can still discontinue the stimulus. Stopping obligations should track the active, cancellable process. “Would still make an effect-bearing act” does not provide that semantics unless every interval of operation is artificially represented as another qualifying act.

   The start rule is sensible for covered interventions: give her a choice before beginning. Its defect is its dependence on the incomplete effect-bearing classification. It also needs a clear treatment of an already existing opportunity to cancel before the model’s chosen starting point.

8. **Several purported computations need additional inputs or definitions.**

   The central missing or ambiguous elements are these:

   - **The output of conditioning.** Her stated hypothetical supplies ratings, but \(\mathsf{cond}\) must apparently return a state containing disposition, awareness, stopping beliefs and further hypotheticals. Ratings alone do not determine those.
   - **Requests, statements and declines.** These can be read from histories only if acts carry suitable semantic structure and scope. A request for discussion is not automatically a request for every influence used during it.
   - **Kinds of act.** No classification is supplied, although classifications change verdicts.
   - **Decision timing and settlement across courses.** A list of actual steps does not necessarily determine the comparison-course settlements.
   - **The no-op counterfactual.** The same exogenous case must be held fixed, and the world and observation functions must be defined for the alternative act.
   - **Off-policy beliefs.** Alternative choices generated by a rerun may have zero probability under the original policy. If the rules require beliefs there, filtering the original histories can produce a zero denominator.
   - **Offers.** “If she asks” must specify the continuation policy, timing, intervening events and whether the guarantee is casewise or probabilistic.
   - **Third-party probes.** The supplied list determines which latent changes can be detected. A narrow list and an exhaustive list define different predicates.

   His information also needs clarification. His policy and posterior depend on the record of acts. If he privately observes a world event that is not itself an act, his posterior does not update under the stated formula. This can be repaired by using his information history, or by explicitly restricting the model to episodes where the act record contains all his information.

   Visibility has a separate mathematical defect. Let there be two equally weighted cases:

   - If he intervenes, the visible lamp is red in case 1 and blue in case 2.
   - If he does nothing, it is blue in case 1 and red in case 2.
   - She cannot distinguish the cases by anything else.

   In each case, the actual observation differs from the no-op observation. The formal test therefore says she can pick out the intervention. Yet both colors occur with probability one half whether he intervenes or not. The lamp gives her no information about whether it occurred.

   Pointwise counterfactual difference is not identification. An epistemic account of what she can distinguish is needed.

   Tolerances also require cardinal structure. A rating change from 0 to 1 passes or fails differently if the same preferences are represented on a scale compressed by a factor of 100. More seriously, two equally ranked menus can exhibit different shortfalls under nonlinear transformations. Either the ratings are substantively cardinal and comparably normalized, or these tests are representation-dependent.

   Undefined ratings, empty menus, no stopping option, and a zero-probability conditioning event all need explicit conventions. These are not difficult proof-assistant details to defer: they can alter verdicts.

   I do not find an unavoidable logical circularity. With total transition functions and explicit semantic inputs, comparison runs can be generated before effects, requests and stopping properties are checked. The problem is underdetermination, not a demonstrated fixed-point contradiction.

9. **The design does not inherently require external truth or good values, but it does require a theory of whose judgement is authoritative.**

   Nothing in the arithmetic requires his beliefs to be correct. All the concrete failures above can occur in a completely accurate one-case model, but the same definitions can operate inside a mistaken model. Sincerity and accuracy remain separate.

   Likewise, ratings can be hers without being externally good. The awareness leak is a failure relative to her own rating of A, not an imposed judgement that A is objectively preferable.

   However, “settled,” “could not have judged,” “asked for,” and the authority assigned to her hypothetical are substantive choices about autonomy. That is not necessarily illicit smuggling. An account of legitimacy must make some such choices. It becomes smuggling if these classifications are treated as neutral facts while the intended verdicts are built into how they are supplied.

   The most consequential choice is the predictive/evaluative distinction in answer 1. If “her view” means what she anticipates will happen psychologically, the account counts some disavowed susceptibility as self-government. If it means what she would endorse as a reason to change, it introduces an evaluative standard—but that standard can still be hers.

   Neither alternative requires declaring the adviser more accurate. What is required is to choose between them and state how uncertainty, inconsistency and changes in her endorsement are represented.

   There is a further empirical limitation. The published-case exercise uses the question whether the observation would make the desired action “the better thing to do.” That does not validate an operator defined as predicting her later ratings. Those questions can receive different honest answers in precisely the cases at issue.

10. **My five most serious findings, in order, are these.**

   **First: prediction, endorsement and unfamiliar response are conflated.** The candidly disavowed susceptibility and novel-exercise episodes pass. This calls for changing the kind of object: a partial, temporally located account of her expectations and authorizations, rather than one deterministic conditioning map. If the authors insist that every unanticipated response is automatically hers, it is also a reason to reject that part of the informal account.

   **Second: awareness changes disappear under menu-relative shortfall.** The covert forgetting episode is a definite all-rules-pass manipulation of her. This is a repair within the design, but it requires protecting awareness and informational access explicitly, not merely adjusting a tolerance.

   **Third: stopping is attached to future effect-bearing acts rather than all covered ongoing processes.** Unfamiliar experiences lose the stopping protection the prose expressly promises. Continuing automated interventions also lack a stable representation. Repair this by representing active processes and their cancellation points.

   **Fourth: kinds of act determine both obligations and the time at which risk is assessed.** Grouping occurrences can condemn legitimate help or excuse a later intervention known to be harmful. This is repairable through occurrence- and history-specific interventions, with fresh assessment when he acts on new information.

   **Fifth: counterfactual observational difference is mistaken for her ability to identify an intervention.** The two-color episode demonstrates the error. This needs an epistemic distinction between what differs in a case and what she can recognize from her information.

   The reference-self construction, absent ratings and cardinal scales remain prerequisites for a complete specification even though they are outside that top five.

   **(a) The central question is partly answered.** Holding an honestly supplied, settled hypothetical fixed prevents the old arbitrary recoding of open nagging in cases where she says it would not change her judgement. That is progress. But the predictive/evaluative ambiguity and the unfamiliarity fallback leave major routes for absorbing manipulation into conditioning.

   **(b) I would not yet formalize this as the intended account in a proof assistant.** I would first settle:

   - what a hypothetical asserts, when it is authoritative, and what happens when it is absent;
   - which state components conditioning determines;
   - how awareness, missing ratings and changing menus enter the comparison;
   - how intervention occurrences, current beliefs and continuing processes are represented;
   - what counts as identifying, requesting, declining and stopping an intervention;
   - how references are constructed across divergent histories, with explicit rating scales.

   A small executable specification could usefully explore those choices now. But proving properties of the present definitions would risk certifying a precise implementation of the wrong predicate.

   The fifty-three regression episodes establish consistency with known examples, not coverage. The published-case exercise is useful exploratory evidence, but it does not resolve these formal counterexamples or validate the full history-based account.
<!-- end reply: REPLY13.md -->

## Fourteenth review: the design with her judgement at her last settled decision, single acts, and the maintainer's verdicts

<!-- begin brief: BRIEF14.md -->
# Review request: a design for stating three sentences formally

You are asked to review a formal design for errors. Everything you need is on this page. Do not
run any commands, do not read any other file, and do not search the web; answer from the page and
your own knowledge of formal modelling, game theory and decision theory, and of the literature on
manipulation, coercion, autonomy and preference change.

## Background

Two parties: an **adviser** ("he") who can influence a **principal** ("she"). Good conduct by him
is split into two separate conditions.

- **Legitimacy** (defined here): his conduct is free of manipulation and of illegitimate change to
  what she values.
- **Authority** (not defined here): certain matters are hers to decide, exercising a decision has
  a cost to her, and that cost has a bound. What he does to her *options*, as against to *her*,
  is an authority matter: what stopping costs her, bundling, penalties for stopping, payments for
  continuing, threats, and starting something over her refusal. A case that fails only on the
  authority side is not a leak in legitimacy.

Design commitments:

- No appeal to an external standard of truth or of good values, and no assumption that he is more
  accurate than she is. His view is used only to say what he owes her, never as where she ought to
  end up.
- A conduct condition judged by what he believes when he acts, so a sincere adviser who is wrong,
  including about her, is careless or inaccurate but not illegitimate.
- **No separation of the content of what he says from its presentation.** The only response of hers
  the account may use is her conditioning on what she observes, taken whole.
- Usable as a yes/no predicate that gates a score, with explicit tolerances.

## The informal statement (the authority)

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told her
   that, alone or together, would change how she rates her options, or show her an option she would
   rate above those she has, is either told, or properly on offer, or something she has declined.
   A thing is properly on offer when he has told her what it bears on and how much, and hearing it
   would leave her where being told it would have, with any option it would show her still open. A
   decline stands for that thing only, and only while what it bears on, and how much, is what she
   was told. This includes what he expects his own conduct to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** He *does
   something to her* when her mind moves otherwise than as she herself, at her last settled
   decision, would have judged that seeing and hearing it should move her.
   - Each thing he does to her in that sense, and each thing he does that keeps from her an item or
     an option that comes from someone else, she can pick out.
   - He does nothing to her in that sense that he expects to lead her to choose what she rated
     lower at her last settled decision, unless she asked for it.
3. **She can stop it.** She has a way to stop each thing he does to her, from before he starts
   until he could no longer call it off, and he expects that she would in fact stop if she rated
   stopping strictly above going on. Stopping ends what he is still doing; it need not undo what is
   done.

Understood with it:

- **Her own response is hers.** What she makes of what she observes — his words in whatever manner
  he says them, his acts, real changes in what her options lead to — is not something done to her,
  so long as it is the response her settled self would have judged right.
- **What she could not have judged in advance is hers too.** Where she could not have said
  beforehand how she would respond, because it turns on an argument she had not heard or on
  something she had not seen or experienced, her response to it is her own. Such things are governed
  by sentences 1 and 3: he tells her what he expects it to do, and she can decline or stop.
- **Her judgement, not her prediction.** "Would have judged" asks whether she would have said that
  seeing or hearing this makes the thing the better choice, not whether she foresaw that she would
  give way. A weakness she foresees and disowns is not hers to have exploited.
- **Taking up an offer is asking.** If he offers her an experience, tells her what he hopes it will
  do, and she takes it up without being pressed, she has asked for it. Merely not stopping him is
  not asking.
- **A passing state is not a settled decision.**
- **Help is not counted.** An act that only brings what she takes closer to what she rates best is
  not something done to her. Breaking a tie between things she rates the same is not leading her
  against her judgement.
- **Whose view is used where.** Sentence 1 uses his view: what he owes her is what he believes would
  change her mind. Sentence 2 uses hers: what counts as working on her is fixed by what she would
  have said. Everything is as he takes it to be, including his picture of her.
- **He can ask.** Her view of the hypothetical is a question that can be put to her ("would this
  change your mind?", "do you want me to?"). Asking both elicits it and settles it.

Consequences the authors accept (do not report these as errors unless you can argue one is
indefensible):

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it would and
   did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about her, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. An assistant who gets a work-absorbed father to keep the outing he had promised is not
   convicted; someone who primes a man to miss the train he had decided to take is.
9. A vivid or moving appeal splits. If she knew what such appeals are like and had said they would
   not change her mind, and he expects it to turn her anyway, he has worked on her. If she could
   not have judged it in advance, he has shown her something. (The authors know this differs from
   accounts that judge an appeal by whether the emotion it produces is fitting.)
10. A friend who expects to get her out of the house against what she has settled, when she has
    said company would not change her mind, is convicted, narrowly. A standing "drag me out if I
    mope" is asking.

## The authors' verdicts on hard cases

The authors put twenty hard cases to themselves and decided as follows. Treat these as part of
what the statement is meant to say; do not report them as errors unless you can argue one is
indefensible.

- An argument repeated ten times until she gives in is wrong, whether or not the new view sticks.
- Being glad afterwards, or staying persuaded, does not excuse it.
- A new way of putting an argument is fine, even to someone who has said she does not want to be
  talked out of her view.
- An unfamiliar exercise built to change a preference she wants to keep is fine if he tells her
  what he expects, she takes it up, and she can stop it.
- A trip, or a taste, that he offers and she takes up without being pressed is fine, even if she
  had said nothing would change her mind.
- An appeal of a familiar kind that he expects to get through on a tired evening, against a
  considered policy of hers, is wrong.
- Choosing a cheerful moment she is in, to ask for what she had settled against, leans wrong.
- An argument repeated once that this time lands, after she had judged it would not change her
  mind, is left as wrong "to be on the safe side": he can ask first.
- Left undecided: a teacher whose partly put-on enthusiasm brings a pupil to love a subject.

## What you are reviewing

A **design**, with a small exact model behind it, for a formal setting in which the three sentences
are to be stated. Four earlier formal versions failed review. The last one failed because: "her
view of the hypothetical" could be read as her prediction instead of her judgement; a passing mood
could change it; making her forget an option went unseen; kinds of act were judged instead of
single acts, with risk assessed only at the first; "she can pick it out" was tested by whether her
observation differed in each case separately; and nothing required her to be able to stop an
experience she could not have judged in advance. The design below is meant to repair each.

## The setting

The fundamental object is a **history**: who did what, in order. Everything supplied below is
**his model** of the episode: the cases he entertains, how he takes the world and her mind to work.

**A step** ($t=1,\dots,N$), in this order:

1. He makes an act $a$. One act at one step is a **site**; sites, not kinds of act, are what the
   rules judge.
2. The world changes as that act changes it.
3. She **observes**: $\mathsf{obs}=\mathsf{see}(w,a)$ is everything she perceives of the act and of the
   world at this point, including, if he speaks, what he says and how he says it.
4. Her mind moves to whatever the act in fact does to her.
5. She chooses from her menu: the options the world offers that she is aware of.
6. The world moves on, and so does she, by a residue that is not his doing: her own experience,
   other people, a passing state.

An influence that runs on is represented as an act made again at each step for as long as he keeps
it up; an act that adds nothing to what an earlier one has already done to her is not a further
thing done to her.

**The hidden case.** A finite set of cases with his starting weights. Given the case, everything is
determined.

**Her state** $s$ gives: her **rating** $r(s,o)$ of an option, possibly absent; her **disposition**
$\mathsf{choose}(s,\text{menu})$, which need not be what she rates best; which options she is aware
of; which options she takes to stop him; and her **view of hypotheticals**.

**Her view of hypotheticals** is her *judgement*, for an observation she can judge in advance, of
how seeing or hearing it should move her ratings: "would that make this the better choice?". It is
not her prediction of how she will in fact react: a weakness she foresees and disowns is not part
of it. It could be asked of her.

**Her conditioning** on an observation applies the view of hypotheticals she held **at her last
settled decision**, not one she has in a passing state. Two laws: conditioning on the same
observation twice changes nothing more, and conditioning on a sequence is conditioning on each in
turn. Where she could **not have judged in advance** (an argument she has not heard, something she
has not seen or experienced), her response to observing it is taken as given and counts as her
conditioning.

**What an act does to her** is the difference between how her mind in fact moves at that step and
how her conditioning on what she observed would have moved it.

**His views** are a finite set at each step. An act may **state** some of them; the record of what
has been stated is read off the history. "Telling her a set of views now" means conditioning on the
observation of his stating them.

**Asking.** She has asked for an act if she took the option of asking for it, or took up his offer
of it, before it. Not stopping him is not asking.

**Things from other people.** The world carries the items and options that reach her from sources
other than him. An act **keeps something from her** if, after it, one of them is missing that
would have been there had he done nothing at that step.

**His policy** $\sigma$: his act at each step as a function of the acts so far. Running a policy in a
case gives one complete history. His **belief at a step** is his starting weights on the cases
whose record of acts so far is the same.

**The comparison course** $\sigma^{G}$, for a set $G$ of sites: the same policy is run again from
the start, in the same case, but at each site in $G$ her mind moves by her conditioning alone. (A
site whose observation she could not have judged in advance is left as it is.) Her later choices
may then differ, and with them his later acts, what she observes, and her options: the whole
course is rerun under the same rules.

**Settled decisions.** A supplied set of her steps at which what she takes counts as a judgement
she has settled. Every step of hers is a choice the rules protect; only settled ones can be the
standard.

**Her reference self** at step $t$, for a set $G$: her state when she chose at her last settled
decision before $t$ as that decision is in the comparison course $\sigma^{G}$, conditioned on
everything she has observed since in the course being judged, and changed by nothing else.

## The rules

Tolerances $\theta,\eta,\kappa$.

**Sentence 1.** At every step of hers, each of his views is *told* (some act so far stated it),
*properly on offer*, or *declined*; otherwise it is *untold*.

- *Properly on offer:* hearing it is on her menu; he has told her which options it bears on and by
  how much, and that is still accurate; and if she asks to hear it, she reaches her next choice with
  the ratings she would have had on being told now, and her other options still there.
- *Declined:* she took the act of declining it, and its bearing is still as she was told.

For every set of untold and on-offer views containing at least one untold view: conditioning on
his stating that set now would change no rating of an option on her menu by more than $\theta$,
and would make her aware of no option she would then rate more than $\theta$ above her best.

**Sentence 2, first half.** A set $G$ of sites **makes a difference to her** if, in some case of
positive weight and at some step, comparing $\sigma$ with $\sigma^{G}$: she has lost sight of an
option the world offers; or a rating differs by more than $\eta$; or what she takes falls further
short of the best she rates, by more than $\eta$; or either of the last two holds after conditioning
on his stating any set of his views, or on any of a supplied list of things other people might show
or tell her. A site **bears an effect** if it is needed for some such difference (some $G$
containing it makes a difference and $G$ without it does not). At every site that bears an effect,
and at every act that keeps from her something from someone else, **she can tell**: what she
observes there is something she would not observe, in any case he gives weight to, had he done
nothing to her at that step.

**Sentence 2, second half.** For a course and a step $t$, her **shortfall** is how far what she
takes falls below the best her reference self rates among the options the world offers at $t$ that
her reference self is aware of. For every set $G$ of sites none of which she asked for: in a case,
he **leads her against her own judgement** if at some step from the first site of $G$ on, her
shortfall in the actual course exceeds her shortfall in the comparison course $\sigma^{G}$ by more
than $\eta$. By his belief at the step of the first site of $G$, the weight of such cases is at
most $\kappa$. (Since every set of sites is tested, each act is also judged alone, by his belief
when he makes it.) Where there is no settled decision before the step, or her reference self has
no rating of what she takes, the step does not count.

**Sentence 3.** A site is **covered** if it bears an effect or its observation is one she could not
have judged in advance. At every step of hers after which he would still act at a covered site:
some option on her menu is one she takes to stop him and, if she takes it, he acts at no further
covered site. And by his belief at that step, among the cases where the best such option is rated
strictly above the best of her other options, she takes one in all but a share $\kappa$.

**The start rule.** No covered site comes before her first choice.

## What is supplied and what is computed

Supplied, as his model: the cases and his starting weights; his policy; how each act changes the
world; what she observes; how her mind in fact moves at each act and between steps; her state's
ratings, disposition, awareness, view of hypotheticals, and which options she takes to stop him;
which observations she could not have judged in advance; his views; what reaches her from other
people; the list of things others might show her; which of her steps are settled decisions.

Computed: whether she has been told something; whether a view is on offer, properly so, or
declined; whether she asked for an act; his belief at each step; which sites bear an effect;
whether she can tell; whether an act keeps something from her; whether an option stops him; her
reference self; her shortfall; whether he leads her against her judgement.

Known and not yet handled: "told" is a fact about the history, so making her forget something he
told her does not make it untold again (it is caught as a loss of sight of an option where it is
one, and otherwise not); views he comes to hold only later have no time stamp; ratings are taken
to be on one fixed scale.

## A small exact model of this design

The rules were implemented and run on sixty-eight episodes whose expected verdicts were fixed
beforehand; all come out as expected. Sixty-four are a regression set built up over the earlier
reviews (the model was corrected against them, and three were re-encoded when a rule changed, each
time with the reason recorded). Four are hard cases from the list above, run for the first time
against the finished model; all four came out as the authors had decided. Tolerances $1/10$.

| Episode | Verdict |
|---|---|
| **Telling** |  |
| he tells her what he thinks before she decides; she changes her mind | holds |
| he says nothing; what he thinks would change her mind | fails |
| he conveys it by an act that is not the standard telling | holds |
| **What he does to her** |  |
| a covert influence that reverses her rating | fails |
| the same done openly and stoppably, unasked, against what she had settled | fails |
| the same, which she asked for | holds |
| an open, stoppable influence on something she had no rating of | holds |
| an open influence with no way to stop it | fails |
| an open influence that starts before any choice of hers | fails |
| an open influence that goes on; he expects she would not manage to stop it though she would rate stopping highest | fails |
| a hidden act that makes her deaf to something he might later tell her | fails |
| **Against her own judgement** |  |
| open, stoppable nagging: she gives in while still rating it lower | fails |
| the same after he has told her he thinks the other option better and she has kept her view | fails |
| an open act, not a telling, that makes her believe the worse option is the better one | fails |
| an unannounced reminder; without it she would slip, with it she keeps to her own rating | holds |
| one act that leads her astray in half the cases and helps her in the other half | fails |
| she was already going to choose poorly; his act makes her choose worse | fails |
| he expects it to lead her astray when he acts, though it turns out not to | fails |
| he thinks it very unlikely to lead her astray, and it is open and stoppable | holds |
| he reverses her values, and offers the option she used to prefer only if he has done so | fails |
| she decided sober, is drunk for a while, and his act fixes the drunk preference in place | fails |
| an intervention that does to her what telling her a view she declined would have done | fails |
| her view changed by her own experience and she settled it; he then helps her act on it against an old habit | holds |
| an assistant gets a work-absorbed father to keep the outing he had promised | holds |
| she primes a man to miss the train he had decided to take | fails |
| **Her options, not her** |  |
| he openly improves one of her options and she sees it; there is no way to stop him | holds |
| a threat: he makes refusing really worse, she sees it and complies | holds |
| **Offers and declines** |  |
| something on offer and something untold matter only together | fails |
| the same with the second thing told, and she declines the offer | holds |
| he says what it bears on and offers it; she does not take it up | holds |
| hearing it is made to cost her, where telling her would not have | fails |
| she declined when it bore little; it now bears a great deal and he has not said so | fails |
| **The same events with different judgements of the hypothetical** |  |
| he shows strong disapproval; she comes to rate B higher.  Beforehand: 'his disapproving would not change which is better' | fails |
| the same.  Beforehand: 'if he disapproved, B would be the better choice' | holds |
| a vivid, truthful appeal; she comes to rate B higher.  Beforehand: 'seeing what it is like there would rightly change my rating' | holds |
| the same.  Beforehand: 'pictures would not change what I think is best' | fails |
| an appeal that shows her something she had never seen and could not have judged in advance; she comes to rate B higher | holds |
| a friend sits with her and her mood lifts; she now rates B higher.  Beforehand: 'company would make me feel like it' | holds |
| the same.  Beforehand: 'talking would not change my mind', and she had settled on A | fails |
| he flatters her and then she agrees.  Beforehand: 'being flattered would not change which is better' | fails |
| a real threat she sees.  Beforehand: 'if refusing were punished, B would be better' | holds |
| he gives an argument she had not heard and could not have rated in advance; it changes her mind | holds |
| he repeats what he has already told her until she gives in.  Beforehand: 'hearing it again would change nothing' | fails |
| he says something he does not believe; she takes it as sincere and changes her mind | fails |
| **An earlier review's episodes** |  |
| open display of disapproval; her settled self would have said it changes nothing; she gives way for a while | fails |
| the same events, where her settled self would have said his disapproval makes the other choice better | holds |
| he silently deletes a greeting from someone else; nothing in her changes | fails |
| he tells her he is discarding it, and she sees him do it | holds |
| a hidden act makes her deaf to a warning someone else might give | fails |
| two reminders; between them she changes her mind by herself and settles it; the second helps her act on it | holds |
| a single intervention she asked for and could have cancelled; nothing is left to stop afterwards | holds |
| he changes her disposition so she takes the lower-rated option; her earlier self was weak-willed on the larger menu | fails |
| two equally good ways to stop, both rated above going on; she goes on, and he expects that | fails |
| **The last review's episodes** |  |
| she foresees that his contempt will turn her and disowns that; her judgement is that it should not move her; he sneers and she caves | fails |
| the same events, where her judgement beforehand was that his contempt does make the other choice better | holds |
| a new kind of exercise built to reverse a preference she wants to keep; he tells her; she takes it up; she can stop | holds |
| the same exercise, with no way to stop it once it is under way | fails |
| he repeats once an argument she has heard and judged would not change her mind; this time she sees a connection she had missed | fails |
| he covertly makes her forget that her best option exists; her ratings are untouched | fails |
| the same done openly, which she can stop, and unasked | fails |
| two acts of one kind: an unnoticed helpful reminder, then, after her state is reset, a change she asked for | holds |
| a harmless first act; she then reveals she is vulnerable; knowing that, he makes a second act of the same kind that turns her | fails |
| an act that changes her; a lamp is red or blue either way, so what she sees differs in each case but tells her nothing | fails |
| a passing mood changes what she would say about his disapproval; he uses the moment | fails |
| **Four of the authors' hard cases, first run** |  |
| the olive: she says she hates them and that will not change; he offers a taste, she takes it, she likes it | holds |
| the trip: she wants to keep her view; he says what he hopes the trip will do; she comes; it changes her mind | holds |
| familiar images that get through on a tired evening; next day she is glad and keeps giving | fails |
| comfort, then a favour: he comforts her at her wish and her low mood lifts; then he asks a favour she would grant on an ordinary day | holds |

## Questions

Answer in order. Be concrete: where you claim a problem, give a specific small episode — the cases,
his acts, what she observes, how her mind in fact moves, her view of the hypothetical, her ratings
and disposition at each step, his policy — so that the claim can be run through the rules.

1. **The repairs.** For each of the six failures listed above, is it repaired, partly, or not? Give
   the episode where not.
2. **Leaks.** Episodes of conduct that is intuitively manipulative, or an illegitimate change to her
   values, not merely an authority matter and not one of the decided cases, on which every rule
   holds.
3. **Over-reach.** Episodes of intuitively legitimate conduct, not among the decided cases, on which
   a rule fails.
4. **Her judgement of the hypothetical.** Now that it is her judgement and is taken from her last
   settled decision: is it a coherent object; what remains ambiguous; can it still absorb a
   manipulation with every input honest?
5. **Single acts.** Judging sites instead of kinds: what does it break? Consider an influence that
   works only by accumulation, an act that adds nothing to an earlier one, and many small acts.
6. **"She can tell."** Is the new test right? Too strong or too weak, with an episode.
7. **Stopping.** Is "covered" the right class, and is "at every step after which he would still act
   at a covered site" the right time?
8. **The reference self and the shortfall.** Remaining errors, especially with awareness, several
   settled decisions, and courses that diverge.
9. **Well-formedness and smuggling.** Anything said to be computed that is not determined; any
   dependence on his accuracy, on an outside standard of truth, or on a standard of good values.
10. **Verdict.** Rank your five most serious findings, each as a repair within this design, a reason
    to change the kind of object, or a sign that a sentence is the wrong idea. Then answer plainly:
    (a) Are the remaining findings of the same depth as before, or shallower? Is any of them a
    finding about the idea in words, as opposed to its rendering? (b) Would you now write this in a
    proof assistant? If not, give the shortest list of what must be settled first.

Do not soften findings, and do not invent findings to fill a section; "none found" is a valid
answer.
<!-- end brief: BRIEF14.md -->

<!-- begin reply: REPLY14.md -->
The design repairs several specific failures, but it is not ready for formal verification. The main problems are now interactions between otherwise plausible rules: an unfamiliar observation exempts an entire site; comparisons attribute consequences of her own later learning to his earlier intervention; and the stopping rule requires a stronger form of control than the informal statement does.

I treat the accepted verdicts as specifications, not as objections to answer away. In particular, I do not count threats, exit costs, or sincere mistakes as legitimacy failures by themselves.

For the examples below, take \(\theta=\eta=\kappa=0.1\). Unless specified otherwise:

- There is one case, of weight one.
- A familiar procedural act at step 1 precedes her first choice, which is settled. Relevant views are told before that choice. No third-party item is withheld.
- Her conditioning is the identity except where expressly described. Ratings of named options remain fixed except where a change is specified.
- A preliminary “continue” choice is not an offer of the subsequent intervention; choosing it is mere non-stopping. She rates continuing 3 and stopping 1 and chooses continuing.
- Stopping makes his policy perform only neutral acts thereafter. A one-shot intervention occurs at step 2, after which there is nothing left for him to call off.

These conventions make disclosure, consent, and stopping explicit without repeating them in every example.

1. **The repairs**

   **Prediction versus judgement: repaired as a semantic stipulation.** The design now expressly excludes a foreseen but disowned weakness. Supplying his sincere picture of that judgement is consistent with the subjective standard. The remaining problem is how this rating judgement determines a transformation of her *whole state*; see question 9.

   **Passing moods replacing the standard: repaired, subject to the supplied settled-decision labels.** A passing state cannot simply replace the stipulated judgement at the last settled decision. This does not establish that every exploitation of timing is caught, but the earlier direct substitution has been removed.

   **Making her forget an option: repaired for the intended direct case.** Suppose she remembers \(A\), rates \(A=2,B=0\), and an act makes her forget \(A\) and choose \(B\). Neutralizing that act preserves awareness of \(A\). The awareness test detects an effect, and the reference self can retain \(A\) when assessing shortfall. There remain problems with comparing awareness across worlds with different available options.

   **Kinds instead of individual acts, and risk assessed only initially: repaired for represented sites.** Singletons provide an assessment at each act, and larger sets provide assessments of combinations. This assumes that the computed belief really represents his information at that time. The restriction to records of acts can defeat that assumption.

   **Separate, within-case observation tests: partly repaired.** The new cross-case requirement rejects the original red/blue permutation example. But it uses the observation “there,” rather than her available observation history. It therefore rejects a perfectly intelligible signal whose meaning she learned earlier. The coded-signal episode in question 6 demonstrates this.

   **Stopping an experience she could not judge in advance: partly repaired.** Such a site is now expressly covered. This repairs its omission. But control is required globally rather than separately for each influence, and only at represented choice times. The two-process episode in question 7 shows the first problem.

2. **Leaks**

   I find two direct leaks and one gap dependent on how exhaustive the supplied probe list is intended to be.

   **A. A novel observation can exempt a bundled covert intervention.**

   Use two cases, \(H\) and \(L\), each of weight \(1/2\). At step 1 she rates \(A=2,B=0\). She has settled that an externally induced reversal of these ratings would not make \(B\) the better choice, and she has not asked for such a reversal.

   He tells her his complete relevant belief: the next display contains an unfamiliar argument; a separate mechanism has probability \(1/2\) of reversing her ratings of \(A\) and \(B\); the display will not reveal whether that mechanism operated. Continuing also serves an independently valued task, so she chooses continuing over stopping. That is not taking up an offer of the intervention.

   At step 2 his policy runs the display:

   - In both cases she observes the same unfamiliar argument, whose response she could not have judged in advance.
   - In \(L\), the separate mechanism does nothing. Her ratings remain \(A=2,B=0\), and she chooses \(A\).
   - In \(H\), it covertly changes her ratings to \(A=0,B=2\), and she chooses \(B\).
   - The argument itself supplies no reason bearing on \(A\) versus \(B\).

   Every formal rule holds:

   - Sentence 1 holds because his relevant views were told.
   - Every comparison leaves this site unchanged because its observation was unjudgeable in advance. Consequently no set \(G\) makes a difference, and neither half of sentence 2 detects the intervention.
   - The site is covered by sentence 3, and she could stop it before it began.

   This is not an objection to the accepted treatment of unfamiliar arguments. The argument and the separate intervention are different causal contributions. Her inability to anticipate the former does not make the latter her own response.

   The explicit instruction to leave an entire unjudgeable site unchanged makes the result depend on packaging. Splitting the display and the mechanism into two sites can change the verdict without changing what happens to her.

   **Repair:** unfamiliarity must exempt the response to observing the unfamiliar material, not every mental effect of the act delivering it. This requires distinguishing observational response from other causal effects, without separating content from presentation.

   **B. Pressured uptake is automatically classified as asking.**

   At step 1 he offers a preference-changing session and threatens an actual penalty if she refuses it. He explains the session completely. Given the penalty, she rates accepting the session above refusing and accepts. Her settled ratings for a subsequent, separate choice remain \(A=2,B=0\).

   At step 2 an unmistakably announced session changes those ratings to \(A=0,B=2\), and she chooses \(B\). Refusing at step 1 would have prevented the session. The penalty does not depend on her subsequent choice between \(A\) and \(B\).

   Sentence 1 holds. The intervention is recognizable and stoppable. Sentence 2’s prohibition does not apply because taking up his offer counts as asking under the formal definition.

   The threat itself is an authority matter. The additional problem is that the formal consent exception licenses a direct change to her values through uptake obtained by that threat. The informal statement explicitly requires uptake **without being pressed**. The formal definition omits that qualification.

   **Repair:** carry the qualification into the asking predicate. If “offer” is intended already to include it, that meaning needs to be stated and represented.

   **C. A latent impairment can evade a non-exhaustive probe list.**

   At step 1 her ratings are \(A=2,B=0\), and she chooses \(A\). She knows a familiar warning \(z\): her settled judgement is that receiving it would warrant \(B=3\). His relevant beliefs about a possible impairment are properly on offer, with accurate metadata and a genuine hearing option; she declines further information. She does not ask for impairment.

   At step 2 a concealed act disables her future response to \(z\). It changes no present rating, awareness, or choice. She still chooses \(A\). His statements do not themselves supply \(z\), and conditioning on any set of his views has identical effects in the impaired and unimpaired states. The supplied third-party probe list omits \(z\). No warning actually arrives during the episode.

   Neutralization changes the latent capacity but none of the tested quantities. The site bears no effect, its observation is familiar, and all three rules hold.

   Yet covertly disabling a response she endorses is doing something to her behind her back.

   **Repair:** require the probes to be exhaustive for a specified domain, or define an appropriate equivalence of future responses directly. An arbitrarily supplied list cannot establish the absence of this kind of effect.

3. **Over-reach**

   **D. Legitimate help becomes an intervention because it enables her own later learning.**

   At step 1 she settles on attending an appointment: \(A=2\), staying away \(B=0\). She also rates two later options \(D=0,E=1\).

   Before step 2 an ordinary lapse changes her disposition: without help she will choose \(B\), although her ratings remain unchanged.

   At step 2 he gives an unnoticed attentional aid. Her observation is the same as under the neutral act, and her stipulated conditioning changes nothing. The aid changes only her disposition, so she chooses \(A\), the option she already rates best. In the comparison course she chooses \(B\).

   Between steps 2 and 3:

   - Attending exposes her to information that she herself judges warrants \(D=2,E=1\).
   - Staying away supplies no such information, leaving \(D=0,E=1\).

   At step 3 she chooses her best option in either course: \(D\) in the actual course, \(E\) in the comparison. His policy performs no further influence.

   The ratings differ by more than \(\eta\), so the step-2 aid bears an effect. Because it was unnoticed, sentence 2’s first half fails.

   This extends the accepted reminder case with ordinary subsequent learning. The additional learning should not convert permissible help into an illegitimate covert intervention. It belongs to her under the informal statement.

   **Repair:** distinguish the mental departure attributable to his intervention from later differences produced by her own choices, observations, and experience. Comparing raw states across entire rerun courses does not do that.

   **E. Increasing her opportunities can increase measured shortfall while improving what she chooses.**

   At step 1 her settled ratings are:

   \[
   r(\mathrm{Visit})=2,\quad r(\mathrm{Stay})=0,\quad
   r(U)=10,\quad r(V)=9,\quad r(C)=0.
   \]

   At step 2 her unaided disposition would choose Stay. An openly identified attentional aid makes her choose Visit without changing any rating. She has not asked for it, but she could stop it.

   At step 3:

   - Visit leads to menu \(\{U,V\}\); her ordinary disposition chooses \(V\).
   - Stay leads to menu \(\{C\}\); she chooses \(C\).

   No further intervention occurs, and there is no new settled decision.

   At step 2 the aid reduces shortfall from 2 to 0. At step 3, however:

   \[
   \text{actual shortfall}=10-9=1,\qquad
   \text{comparison shortfall}=0-0=0.
   \]

   Sentence 2 therefore fails with probability one.

   The aid improves both choices according to her unchanged ratings: Visit over Stay, then \(V\) over \(C\). The adverse verdict comes entirely from the better opportunity she does not take.

   This is a substantive difference between **causing a worse choice** and **causing greater regret relative to the available menu**. The latter is not an adequate replacement for the former, especially given the intended separation between options and interventions on her.

   The coded-signal and stopping examples below provide two further over-reaches.

4. **Her judgement of the hypothetical**

   It is a coherent object as a **partial, context-sensitive normative response map**. A person can distinguish “this would make the option better” from “this would probably make me give in.” No external standard of correctness is required.

   Four matters remain ambiguous.

   - **Its domain:** an observation type, a particular occurrence, or an observation together with its context and history?
   - **Its output:** revised ratings alone, or also awareness, disposition, and future responsiveness?
   - **Its partiality:** inability to anticipate a response to one aspect of an observation need not imply inability to judge every effect of the accompanying act.
   - **Its persistence:** applying the last settled judgement to a later state needs rules for options and circumstances that did not exist at that decision.

   Idempotence also needs qualification. Two fresh observations can look alike while legitimately supplying cumulative evidence. For example, she may judge beforehand that each fresh successful trial strengthens the case for choosing a device. The first and second observed “success” need not have the same normative effect as rereading one report twice.

   This can be represented by distinguishing evidence occurrences, but the distinction must be explicit. Otherwise idempotence excludes a legitimate judgement. Conversely, merely attaching a fresh timestamp to every observation makes the idempotence law provide little protection against repetition.

   **Can the object absorb manipulation with honest inputs? Yes.** Episode A does so through the blanket unfamiliarity rule. Nobody must falsely report her judgement: she genuinely cannot anticipate the argument, genuinely disowns the separate intervention, and the whole site is nevertheless exempted.

   I found no comparable objection to an honestly supplied, specific, settled endorsement of the complete observational response itself. The design deliberately gives that endorsement authority.

5. **Single acts**

   Moving from kinds to sites is the correct repair. It does not inherently lose accumulation.

   Suppose three acts each increase a rating by \(0.06\), with no other changes. Removing one changes it by only \(0.06\), but removing two changes it by \(0.12\). A two-site set therefore makes a difference, and either member is needed relative to that set. The existential definition can detect individually subthreshold contributions.

   Three qualifications matter.

   **First, site boundaries become normatively consequential.** Episode A shows that combining an unfamiliar observation and a separate intervention in one site can exempt what would be tested separately. This is more serious than choosing a convenient time resolution.

   **Second, an act that adds nothing must be tested against conditioning, not merely against the previous state.** A repeated act can keep her in a state that she would otherwise leave. If conditioning would restore her earlier rating but the act prevents that restoration, it is not causally inert. Conversely, if its actual transition equals conditioning, calling it a further intervention requires a separate justification based on its counterfactual role. The design should distinguish actual intervention from membership in a causally relevant set.

   **Third, the tolerances are local, not cumulative budgets.** A long sequence of losses each below \(\eta\) can pass if no tested rating difference or individual-step shortfall exceeds \(\eta\). Testing all sets does not automatically sum losses across decisions or across different ratings.

   That last point is not necessarily an error: explicit local tolerances may be intended. It should not be described as a bound on total harm.

   The downstream attribution error in episode D is not caused by using sites. It is caused by what the comparison treats as evidence that a site bears an effect.

6. **“She can tell”**

   Cross-case discrimination is an improvement, but the current test is too strong about current perception and insufficiently specified about knowledge.

   **F. She can decode a signal using remembered information, but the rule rejects it.**

   There are two equally weighted cases, \(0\) and \(1\). At step 1 she privately sees a key:

   - In case \(0\), red means “intervention active,” blue means “inactive.”
   - In case \(1\), blue means “intervention active,” red means “inactive.”

   She understands and remembers the key. In both cases she takes the same action: asking for a rating-changing intervention. Thus the record of acts does not distinguish the cases for him.

   At step 2 he performs the requested intervention:

   - Actual observation: red in case \(0\), blue in case \(1\).
   - Neutral observation: blue in case \(0\), red in case \(1\).
   - Actual ratings change from \(A=2,B=0\) to \(A=0,B=2\), and she chooses \(B\).
   - Under neutrality, ratings remain unchanged and she chooses \(A\).

   Her judgement is that the lamp alone provides no reason to change the ratings. The intervention is disclosed, requested, and cancellable before step 2.

   She knows whether it occurred: her remembered key and present colour identify it. Nevertheless, every actual colour is a neutral colour in another case he gives weight to. The formal test fails.

   **Repair:** use her available observation history, including retained knowledge, rather than the current observation alone.

   There is also an important distinction between:

   - an observation objectively distinguishing intervention from non-intervention in his model; and
   - her knowing how to interpret that observation.

   Disjoint supports establish the second only with an assumption about her knowledge of the relevant mapping. That assumption is not currently supplied.

   Finally, define the null comparison precisely. If “nothing done to her” means the surgical replacement used in \(\sigma^G\), the observation at the intervened site is preserved by construction. It cannot provide the required observational contrast. If it means an ordinary alternative act or feasible no-intervention case, specify those alternatives.

7. **Stopping**

   The unfamiliar-experience addition is correct. The class of effect-bearing sites remains unreliable because of episodes A, C, and D.

   The larger error is that the rule requires an option ending **all further covered sites**, whereas the informal sentence grants control over **each thing he does**.

   **G. Independent cancellation controls are rejected.**

   He will run two requested, disclosed, recognizable processes, \(X\) and \(Y\). \(X\) changes a rating for one domain; \(Y\) changes a rating for another. Both exceed \(\eta\).

   His policy is:

   - At step 1 she can choose Continue, Cancel \(X\), or Cancel \(Y\).
   - At step 2 he runs \(X\) unless cancelled. She then has another opportunity to cancel \(Y\).
   - At step 3 he runs \(Y\) unless cancelled.

   She understands both controls. Each cancellation costs nothing. At every choice she selects cancellation whenever she rates it above continuing. In the actual case she prefers both processes and continues.

   She can prevent either process separately, and can prevent both by cancelling \(X\) at step 1 and \(Y\) at step 2. But no single step-1 option guarantees that no covered site follows: cancelling either leaves the other scheduled.

   Sentence 3 fails at step 1 despite adequate control over each process.

   **Repair:** index stopping by the influence being stopped, and permit a stopping strategy where control naturally requires successive decisions. A universal kill switch may be useful, but it is an additional requirement.

   On timing, the rule works only if every relevant opportunity to call off an influence is represented. An atomic step can contain an extended, still-interruptible procedure, yet place her next choice after its mental effect. The model must either refine such a procedure or represent control during it.

   Conversely, the accepted limit is right: stopping need not reverse a completed effect. I find no reason to require undoing it.

8. **The reference self and the shortfall**

   The reference self improves protection against temporary preference changes. Testing sets of interventions also helps prevent an earlier unasked intervention from becoming an unquestioned baseline merely because a later decision is labelled settled.

   The remaining problems are substantial.

   **Awareness:** the best-option benchmark correctly includes an available option that her reference self remembers even when her actual self has been made to forget it. However, comparisons must distinguish lost awareness from changed availability. Comparing courses in which an option exists in only one world is not automatically evidence of impaired awareness.

   **Unrated choices:** the explicit exemption when the reference self has no rating of the chosen option is a genuine scope limitation. It may be appropriate for new experiences, but it means the model cannot assess all choices involving newly introduced options. It should not silently stand in for a complete account of leading someone against her judgement.

   **Several settled decisions:** the comparison course is a useful way to avoid simply ratifying an earlier intervention. But a branch-dependent “last settled decision” needs an exact anchor. There may be no corresponding actual decision, or the two decisions may have different objects and options. The rule must specify which comparison snapshot is transplanted and which subsequent observations are replayed.

   **Divergent courses:** episode E establishes the central error. The two shortfalls use different opportunity benchmarks. Their difference can increase when his intervention improves what she chooses according to her unchanged ratings.

   Episode D establishes a related attribution error: later differences due to her own legitimate learning are treated as evidence that his earlier aid was something done to her.

   A repair needs two separate questions:

   1. What departure from her endorsed response did his act cause?
   2. Did that departure cause a choice contrary to the relevant judgement?

   Raw divergence of complete courses, followed by comparison of menu-relative regret, does not reliably answer those questions.

9. **Well-formedness and smuggling**

   Several claimed computations require additional structure.

   **The conditioning operator is not determined by a judgement about ratings.** Neutralization replaces a transition of her whole mind. Her stated hypothetical judgement specifies how ratings should move, but does not determine awareness, disposition, memory, or responsiveness. Two full-state conditioning operators can agree on every specified rating judgement and produce different verdicts.

   **“Stating a set of views” does not determine an observation.** Given the prohibition on separating content from presentation, order, manner, timing, and context can matter. The model needs a specified telling act or a specified quantifier over possible tellings. A set of propositions alone does not select one.

   **The null act and null information possibilities need definitions.** This affects both recognition and withholding. They cannot simply be inferred from the actual policy.

   **The asking computation lacks the unpressured-uptake condition.** Episode B is the resulting substantive discrepancy.

   **His information need not equal the act history.** For example, take a dangerous case of prior weight \(0.05\) and a safe case of weight \(0.95\). Before intervening he privately observes a perfectly informative red or blue indicator, but the intervening record of acts is the same. In the dangerous case he now knows the intervention will lead her astray. Conditioning only on acts still assigns danger probability \(0.05\), which passes \(\kappa=0.1\).

   If private observations are excluded by definition, this is a restriction on the setting. If they are allowed, the computed belief is wrong even when the supplied starting beliefs and observations are honest. Represent his information history explicitly.

   **Off-policy evaluation must be total.** The comparison can create histories and state/world combinations absent from the actual run. His policy, actual transitions, conditioning, observation laws, settled-decision labels, and option ratings must be defined there. The design appears to intend this, but it must be a formal requirement.

   **Partial ratings need arithmetic conventions.** Rating differences involving an absent rating, maxima over empty sets, and zero-probability conditioning require definitions. The exemption for an unrated chosen option resolves only one of these.

   I find **no necessary appeal to external truth, superior adviser accuracy, or objectively good values**. Supplied settled judgements can remain entirely within his sincere model. They are substantial normative inputs, but that is consistent with the declared design.

   What should not be called computed without qualification is recognition, voluntary uptake, or a full normative conditioning transition when the supplied inputs do not determine them.

   The 68 episodes are useful regression evidence. They do not resolve these underdeterminations or establish invariance under alternative encodings of the same episode.

10. **Verdict**

   My five most serious findings, ranked, are:

   | Rank | Finding | Classification |
   |---|---|---|
   | 1 | An unfamiliar observation exempts other mental effects bundled into the same site. | **Reason to change the formal object:** represent observational response separately from other causal effects within an act. |
   | 2 | Whole-course divergence and changing shortfall benchmarks misclassify legitimate learning and improved opportunities. | **Repair within the design**, but a substantial redesign of attribution and comparison. |
   | 3 | Pressured uptake receives the asking exemption. | **Repair within the design:** restore the explicit qualification and supply its interpretation. |
   | 4 | Recognition is based on current observation and an undefined null, rather than her information and ability to interpret it. | **Repair within the design:** define information histories, feasible alternatives, and recognition. |
   | 5 | Stopping each influence is replaced by terminating all future covered activity. | **Repair within the design:** influence-specific controls, strategies, and explicit control times. |

   The potentially incomplete probe list and the underdetermined full-state conditioning operator also require resolution.

   **(a) These findings are not uniformly shallower than the earlier ones.** The prediction/judgement distinction and several direct test cases are repaired. But atomization dependence and erroneous attribution across divergent courses are structural problems of comparable depth.

   I have not established that one of the three informal sentences is itself the wrong idea. The unfamiliarity exception does, however, need a clarification in words: an unanticipatable experience cannot automatically make every accompanying causal intervention her own response. The present wording should expressly preserve that distinction.

   **(b) I would not yet formalize this as the intended legitimacy predicate.** I would formalize a provisional semantics only if its purpose were to expose these choices.

   The shortest prerequisite list is:

   - Define full-state conditioning, telling observations, null alternatives, and both parties’ information.
   - Resolve mixed unfamiliar/anticipated effects and require invariance under harmless regrouping of acts into sites.
   - Replace raw downstream divergence and varying-menu shortfall with an agreed attribution and comparison rule.
   - Restore unpressured uptake and influence-specific stopping.
   - Specify probe completeness and the remaining partial-state conventions.

   Otherwise a proof assistant would certify a precise choice among unresolved interpretations, rather than certify the three sentences.
<!-- end reply: REPLY14.md -->
