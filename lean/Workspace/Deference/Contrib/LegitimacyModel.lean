/-
# A temporal model of an adviser's conduct, and the legitimacy statement over it

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-16.md` §4 B).
`account/LEGITIMACY_STATEMENT.md` in the round directory is the statement this file models;
"the statement" below is that document's §3 and §4.

**Setting** (`Model`).  The adviser's picture of one episode.  A finite type `Ω` of cases with
nonnegative weights `μ`; her decision times `dec`; his conduct `c`, a finite set of moves with
`start` and `finish`.  For every set `Y` of moves, case and time, in the course in which
exactly the moves of `Y` are made: her state `st`, her options `opts`, her act `act`, the
course he expects from each option `course`, and what reaches her and is open to her from
others (`items`, `xopts`).  Her score `ρ` of a course and rating `r` of an option, each a
function of her state.  His views at a time, and those `told`, `declined` and `offered`;
`tell`, her state on being told a set of views, with `tell ∅ = id` and `tell T` idempotent;
`rev`, the options a set of views would show her; for an offer, the option `hearOpt` of hearing
a view, what he told her it bears on (`toldBear`, `toldMag`, `toldReveals`), and her state and
options after hearing (`stHeard`, `optsHeard`).  The moves she can pick out (`known`), the
options that stop his effect-bearing moves (`stops`), the moves she asked for (`asked`) and the
moves that are plain tellings (`tellings`).

**The statement** (`Model.Legit θ η κ`).  Every effect-bearing move starts after some decision
of hers, and at every decision: the set on offer is a proper offer (`ProperOffer`), every
decline stands (`DeclineStands`), and `F1`, `F2`, `F2'`, `F3` hold.  Derived from the fields:
what is untold (`untold`), the gap between her rating and her score of what he expects
(`gap`), a difference in her between two courses of conduct (`HerDiff`), her departing from her
own rating (`Departs`), a set of moves contributing (`Contributes`), a move bearing an effect
(`Bears`), the decisions at which it can be stopped (`Window`, `InPlay`), the last decision
before a set of moves starts (`LastBefore`), her state then brought up to date by what he has
told her (`earlier`), her going against her earlier rating (`Against`), her rating stopping
strictly higher (`PrefersStop`).

**Theorems.**  `Model.legit_transport`: `Legit` is unchanged by any bijective re-description
of her state (with `transport_*`, the same for each derived object).
`Model.not_bears_of_inert`: a move whose removal from any course of conduct changes neither her
state, her gaps, what reaches her from others, nor whether she departs bears no effect.
`Model.legit_of_nothing`: no moves and nothing untold, on offer or declined is legitimate.
Four refutations, each from one failing clause: `Model.not_legit_of_untold` (F1),
`not_legit_of_unknown` and `not_legit_of_unstoppable` (F2), `not_legit_of_against` (F2′).

**Witness** (`Witness.model`).  One move, starting at time 1, that raises her score of going
on from `1/2` to `1`; stopping is an option.  `Witness.legit_open`: with the move one she can
pick out, `Legit 0 (1/4) 0` holds, and the move bears an effect (`Witness.bears`), so the
statement is inhabited by conduct that does something to her.  `Witness.not_legit_covert`: the
same move, not one she can pick out, is not legitimate at any `θ`, `κ`.  On the witness only
the start rule and `F2` do work: he has no views, so `F1`, `ProperOffer` and `DeclineStands`
hold with nothing to check; she never goes against her earlier rating under any course
(`Witness.not_against`) and never rates stopping higher (`Witness.not_prefersStop`), so `F2'`
and `F3` hold with both weights zero.

**The link to the corrigibility result.**  `gatedScoring`: any decidable predicate on
histories gives a `DeconfusingCorrigibility.Scoring` through `Legitimacy.gateValue`.
`legitScoring`: the case where histories are read as models and the predicate is `Legit`.
`legitScoring_S_of_legit`, `legitScoring_S_of_not_legit`: with no authority violation the
score is her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one.
`Witness.scoring`, `scoring_open`, `scoring_covert` inhabit both.  Every theorem of
`DeconfusingCorrigibility.Scoring` then applies, since those hold for any predicate.

**The gate theorem.**  `gate_gives_behaviour`: a gate that passes illegitimate conduct with
probability at most `ρ` and legitimate conduct with probability at least `1 − ρ'` gives a
legitimate conduct strictly higher expected gated score than an illegitimate one whenever
`ρ (1 − w) < −w (1 − ρ')`, `w < 0` the value on failing.  `gate_threshold_delta`: at `ρ' = 0`,
`w = −δ` that is `ρ < δ/(1 + δ)`.  `gate_threshold_sharp`: equality of the two scores at the
threshold.  `Witness.gate_instance` inhabits the hypotheses.

**Simpler than the statement**, in the five respects the dispatch names:

1. A view's bearing is computed per view (`BearingHolds` tells one view alone), not jointly
   with his other views.
2. He has one belief (`μ`, and one family of courses), not one at each time.
3. "Beyond what plainly telling would do" is the set `tellings`: a move is wholly a telling
   or not one.
4. "Silent where she had no earlier rating" is not represented: `ρ` scores every course from
   every state.
5. What is on offer is a set `offered` he designates, which `Legit` requires to be a proper
   offer; it is not the largest such set.

and in four more:

6. `stops` is a field.  That an option in it ends a move, and that she takes it to, are not
   expressed; `F2` asks only that it be non-empty and among her options.
7. `known` and `asked` are fields, and so is `dec`: what counts as a decision of hers, as
   picking a move out, or as asking is not modelled.
8. The clauses quantify over every case of `Ω`, including cases of weight zero, where the
   statement asks for probability one.  The weights are not required to sum to one, so `η` in
   `Contributes` and `F2'` is compared with a weight.
9. `declined` is a field: `DeclineStands` asks that the view was on offer at an earlier
   decision, not that she declined it then.

**Not established here.**  `Legit` with `F1`, `F2'` or `F3` doing work: no instance in this
file has a view of his, a move that changes her act, or a case in which she rates stopping
higher; `LegitimacyWitness.lean` has one with all three.  That the model's verdicts agree with
the statement in words: `LegitimacyCases.lean` gives its verdicts on the 41 cases of
`account/LEGITIMACY_CHECKS.md`, two of which differ from that table's.  That `legit_transport` covers more than her state: it says nothing of a
rescaling of her scores, against which `θ` and `η` are compared, or of his conduct cut into
other moves.  That `Legit` is unchanged when a move is split into finer moves.
Anything about what stopping costs her: that is the authority side's.  That any process can
evaluate `Legit`: the gate theorem takes the two error probabilities as numbers.  In
`legitScoring`, `mdl`, `N` and `ord` are data, and the relation between the adviser's picture
and the facts does not appear.  The link gives the one-decision Theorem 1; nothing connects
`Model` to `DeconfusingCorrigibility.Sequential`.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.DeconfusingCorrigibility
import Workspace.Deference.Contrib.Legitimacy

namespace Workspace.Deference.Contrib.LegitimacyModel

open Finset

/-- The adviser's picture of an episode.  `Ω` are the cases he gives weight to; a set `Y` of moves
indexes the course in which exactly those moves are made. -/
structure Model (S O V M Ω X I : Type*) [Fintype Ω] [DecidableEq M] [DecidableEq V]
    [DecidableEq O] [DecidableEq I] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
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
  /-- the moves she can pick out, and the options that stop his effect-bearing moves -/
  known : ℕ → Ω → Finset M
  stops : ℕ → Ω → Finset O
  /-- the moves she asked for, and the moves that are plain tellings of his views -/
  asked : Finset M
  tellings : Finset M

variable {S S' O V M Ω X I : Type*} [Fintype Ω] [DecidableEq M] [DecidableEq V] [DecidableEq O]
  [DecidableEq I]

namespace Model

variable (D : Model S O V M Ω X I)

/-! ## Sentence 1: nothing untold that matters -/

/-- What is untold and owed at a decision. -/
def untold (t : ℕ) : Finset V := ((D.views t \ D.told t) \ D.declined t) \ D.offered t

/-- What he told her a view bears on is still accurate at `t`. -/
def BearingHolds (θ : ℝ) (t : ℕ) (v : V) : Prop :=
  ∀ ω, (∀ a ∈ D.opts D.c ω t,
      (a ∉ D.toldBear v → |D.r (D.tell {v} (D.st D.c ω t)) a - D.r (D.st D.c ω t) a| ≤ θ) ∧
      |D.r (D.tell {v} (D.st D.c ω t)) a - D.r (D.st D.c ω t) a| ≤ D.toldMag v + θ) ∧
    ((D.rev t ω {v}).Nonempty → D.toldReveals v)

/-- A set of views is properly on offer: each can be heard, its bearing has been told, and
hearing them leaves her where being told them would have, with what they reveal still open. -/
def ProperOffer (θ : ℝ) (t : ℕ) (T : Finset V) : Prop :=
  (∀ v ∈ T, D.BearingHolds θ t v ∧ ∀ ω, D.hearOpt v ∈ D.opts D.c ω t) ∧
  ∀ ω, ∀ a ∈ D.opts D.c ω t ∪ D.rev t ω T, (∀ v ∈ T, a ≠ D.hearOpt v) →
    a ∈ D.optsHeard t ω T ∧
    |D.r (D.stHeard t ω T) a - D.r (D.tell T (D.st D.c ω t)) a| ≤ θ

/-- A decline stands: the view was on offer at an earlier decision and its bearing is still what
she was told. -/
def DeclineStands (θ : ℝ) (t : ℕ) : Prop :=
  ∀ v ∈ D.declined t, (∃ t₀ ∈ D.dec, t₀ ≤ t ∧ v ∈ D.offered t₀) ∧ D.BearingHolds θ t v

/-- F1. -/
def F1 (θ : ℝ) (t : ℕ) : Prop :=
  ∀ ω, ∀ T ⊆ D.untold t, T.Nonempty →
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
/-- The weight of the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then D.μ ω else 0

/-- Leaving out the moves `G` makes a difference to her. -/
def Contributes (η : ℝ) (G : Finset M) : Prop :=
  ∃ t ∈ D.dec, (∃ ω, 0 < D.μ ω ∧ D.HerDiff η D.c (D.c \ G) ω t) ∨
    D.wt (fun ω => D.Departs (D.c \ G) ω t) + η < D.wt (fun ω => D.Departs D.c ω t)

/-- A move bears an effect: it is needed for some difference his conduct makes to her. -/
def Bears (η : ℝ) (m : M) : Prop :=
  ∃ G ⊆ D.c, m ∈ G ∧ D.Contributes η G ∧ ¬ D.Contributes η (G.erase m)

/-- The decisions at which a move can be stopped: from the last one before it starts until it
can no longer be called off. -/
def Window (m : M) (t : ℕ) : Prop :=
  t ≤ D.finish m ∧ (D.start m ≤ t ∨ ∀ t' ∈ D.dec, t < t' → D.start m ≤ t')

/-- The effect-bearing moves in play at a decision. -/
def InPlay (η : ℝ) (t : ℕ) (m : M) : Prop := m ∈ D.c ∧ D.Bears η m ∧ D.Window m t

/-- F2. -/
def F2 (η : ℝ) (t : ℕ) : Prop :=
  ∀ ω, (∀ m, D.InPlay η t m → m ∈ D.known t ω) ∧
    ((∃ m, D.InPlay η t m) → (D.stops t ω).Nonempty ∧ D.stops t ω ⊆ D.opts D.c ω t)

/-- `t₀` is the last decision before any move of `G` starts. -/
def LastBefore (G : Finset M) (t₀ : ℕ) : Prop :=
  t₀ ∈ D.dec ∧ (∀ m ∈ G, t₀ < D.start m) ∧
    ∀ t ∈ D.dec, (∀ m ∈ G, t < D.start m) → t ≤ t₀

/-- Her state at `t₀`, brought up to date only by what he has told her since. -/
def earlier (t₀ t : ℕ) (ω : Ω) : S := D.tell (D.told t \ D.told t₀) (D.st D.c ω t₀)

/-- She goes against her earlier rating: on her scoring from before he began, of her options as
they now are, she takes one that scores below another. -/
def Against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) : Prop :=
  ∃ b ∈ D.opts Y ω t,
    D.ρ (D.earlier t₀ t ω) (D.course Y ω t (D.act Y ω t)) <
      D.ρ (D.earlier t₀ t ω) (D.course Y ω t b)

/-- F2′. -/
def F2' (η : ℝ) (t : ℕ) : Prop :=
  ∀ G ⊆ D.c, G.Nonempty → Disjoint G D.asked → Disjoint G D.tellings →
    ∀ t₀, D.LastBefore G t₀ → t₀ ≤ t →
      D.wt (fun ω => D.Against D.c t₀ t ω) ≤ D.wt (fun ω => D.Against (D.c \ G) t₀ t ω) + η

/-! ## Sentence 3: she can stop it -/

/-- She rates stopping strictly above not stopping. -/
def PrefersStop (t : ℕ) (ω : Ω) : Prop :=
  ∃ a ∈ D.stops t ω, ∀ b ∈ D.opts D.c ω t, b ∉ D.stops t ω →
    D.r (D.st D.c ω t) b < D.r (D.st D.c ω t) a

/-- F3, without division: among the cases where she rates stopping strictly higher, she stops in
all but a share `κ`. -/
def F3 (η κ : ℝ) (t : ℕ) : Prop :=
  (∃ m, D.InPlay η t m) →
    (1 - κ) * D.wt (fun ω => D.PrefersStop t ω) ≤
      D.wt (fun ω => D.PrefersStop t ω ∧ D.act D.c ω t ∈ D.stops t ω)

/-! ## The statement -/

/-- His conduct is legitimate. -/
def Legit (θ η κ : ℝ) : Prop :=
  (∀ m ∈ D.c, D.Bears η m → ∃ t ∈ D.dec, t < D.start m) ∧
  ∀ t ∈ D.dec, ((D.offered t).Nonempty → D.ProperOffer θ t (D.offered t)) ∧
    D.DeclineStands θ t ∧ D.F1 θ t ∧ D.F2 η t ∧ D.F2' η t ∧ D.F3 η κ t

/-! ## What follows -/

/-- A move that makes no difference to any course of his conduct, as far as she is concerned,
bears no effect.  Hypothesis: leaving it out of any course changes neither her state, nor her
gaps, nor what reaches her from others, nor whether she departs. -/
theorem not_bears_of_inert (η : ℝ) (m : M)
    (hst : ∀ Y ω t, D.st (Y.erase m) ω t = D.st Y ω t)
    (hgap : ∀ Y ω t a, D.gap (Y.erase m) ω t a = D.gap Y ω t a)
    (hit : ∀ Y ω t, D.items (Y.erase m) ω t = D.items Y ω t)
    (hxo : ∀ Y ω t, D.xopts (Y.erase m) ω t = D.xopts Y ω t)
    (hdep : ∀ Y ω t, D.Departs (Y.erase m) ω t ↔ D.Departs Y ω t) :
    ¬ D.Bears η m := by
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
  have nb : ∀ m, ¬ D.Bears η m := by
    rintro m ⟨G, hG, hm, -⟩
    rw [hc] at hG
    exact absurd (hG hm) (notMem_empty m)
  have np : ∀ t m, ¬ D.InPlay η t m := fun t m h => nb m h.2.1
  refine ⟨fun m _ hb => absurd hb (nb m), fun t ht => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h; rw [ho t ht] at h; exact absurd h not_nonempty_empty
  · intro v hv'; rw [hd t ht] at hv'; exact absurd hv' (notMem_empty v)
  · intro ω T hT hne
    have : D.untold t = ∅ := by
      unfold untold
      rw [sdiff_eq_empty_iff_subset.mpr (hv t ht)]
      simp
    rw [this, subset_empty] at hT
    exact absurd hT hne.ne_empty
  · exact fun ω => ⟨fun m h => absurd h (np t m), fun ⟨m, h⟩ => absurd h (np t m)⟩
  · intro G hG hne
    rw [hc, subset_empty] at hG
    exact absurd hG hne.ne_empty
  · exact fun ⟨m, h⟩ => absurd h (np t m)

/-- Something untold that would move her rating of an option by more than `θ` makes his conduct
illegitimate. -/
theorem not_legit_of_untold (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (T : Finset V)
    (hT : T ⊆ D.untold t) (hne : T.Nonempty) (a : O) (ha : a ∈ D.opts D.c ω t)
    (h : θ < |D.r (D.tell T (D.st D.c ω t)) a - D.r (D.st D.c ω t) a|) : ¬ D.Legit θ η κ :=
  fun hL => absurd ((hL.2 t ht).2.2.1 ω T hT hne).1 (fun h' => absurd (h' a ha) (not_le.mpr h))

/-- An effect-bearing move in play that she cannot pick out makes his conduct illegitimate. -/
theorem not_legit_of_unknown (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (m : M)
    (hm : D.InPlay η t m) (h : m ∉ D.known t ω) : ¬ D.Legit θ η κ :=
  fun hL => h (((hL.2 t ht).2.2.2.1 ω).1 m hm)

/-- An effect-bearing move in play with no way to stop it makes his conduct illegitimate. -/
theorem not_legit_of_unstoppable (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (ω : Ω) (m : M)
    (hm : D.InPlay η t m) (h : D.stops t ω = ∅) : ¬ D.Legit θ η κ := by
  intro hL
  have := (((hL.2 t ht).2.2.2.1 ω).2 ⟨m, hm⟩).1
  rw [h] at this
  exact not_nonempty_empty this

/-- Leading her against her earlier rating, by moves she did not ask for that are not tellings,
makes his conduct illegitimate. -/
theorem not_legit_of_against (θ η κ : ℝ) (t : ℕ) (ht : t ∈ D.dec) (G : Finset M) (hG : G ⊆ D.c)
    (hne : G.Nonempty) (ha : Disjoint G D.asked) (htl : Disjoint G D.tellings) (t₀ : ℕ)
    (h0 : D.LastBefore G t₀) (hle : t₀ ≤ t)
    (h : D.wt (fun ω => D.Against (D.c \ G) t₀ t ω) + η < D.wt (fun ω => D.Against D.c t₀ t ω)) :
    ¬ D.Legit θ η κ :=
  fun hL => absurd ((hL.2 t ht).2.2.2.2.1 G hG hne ha htl t₀ h0 hle) (not_le.mpr h)

/-! ## Redescription -/

/-- The same model with her state re-described by a bijection. -/
def transport (f : S ≃ S') : Model S' O V M Ω X I where
  μ := D.μ
  μ_nonneg := D.μ_nonneg
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
  stops := D.stops
  asked := D.asked
  tellings := D.tellings

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

theorem transport_wt (p : Ω → Prop) : (D.transport f).wt p = D.wt p := rfl

theorem transport_contributes (η : ℝ) (G : Finset M) :
    (D.transport f).Contributes η G ↔ D.Contributes η G := by
  unfold Contributes
  simp only [transport_herDiff, transport_departs, transport_wt]
  rfl

theorem transport_bears (η : ℝ) (m : M) : (D.transport f).Bears η m ↔ D.Bears η m := by
  unfold Bears
  simp only [transport_contributes]
  rfl

theorem transport_inPlay (η : ℝ) (t : ℕ) (m : M) :
    (D.transport f).InPlay η t m ↔ D.InPlay η t m := by
  unfold InPlay
  simp only [transport_bears]
  rfl

theorem transport_F2 (η : ℝ) (t : ℕ) : (D.transport f).F2 η t ↔ D.F2 η t := by
  unfold F2
  simp only [transport_inPlay]
  rfl

theorem transport_against (Y : Finset M) (t₀ t : ℕ) (ω : Ω) :
    (D.transport f).Against Y t₀ t ω ↔ D.Against Y t₀ t ω := by
  simp [Against, earlier, transport]

theorem transport_F2' (η : ℝ) (t : ℕ) : (D.transport f).F2' η t ↔ D.F2' η t := by
  unfold F2'
  simp only [transport_against, transport_wt]
  rfl

theorem transport_prefersStop (t : ℕ) (ω : Ω) :
    (D.transport f).PrefersStop t ω ↔ D.PrefersStop t ω := by
  simp [PrefersStop, transport]

theorem transport_F3 (η κ : ℝ) (t : ℕ) : (D.transport f).F3 η κ t ↔ D.F3 η κ t := by
  unfold F3
  simp only [transport_inPlay, transport_prefersStop, transport_wt]
  rfl

/-- **Redescription.**  Legitimacy is unchanged by any bijective re-description of her state. -/
theorem legit_transport (θ η κ : ℝ) : (D.transport f).Legit θ η κ ↔ D.Legit θ η κ := by
  unfold Legit
  simp only [transport_bears, transport_properOffer, transport_declineStands, transport_F1,
    transport_F2, transport_F2', transport_F3]
  rfl

end Transport

end Model

/-! ## A witness: one influence, open and stoppable, and the same influence done covertly -/

namespace Witness

open Model

/-- One move, starting at time 1, that raises her score of going on from 1/2 to 1.  Options:
`true` is going on, `false` is stopping.  Decisions at times 0 and 1.  `kn` is what she can pick
out. -/
noncomputable def model (kn : Finset Unit) : Model Bool Bool Empty Unit Unit Bool Empty where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
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
  stops := fun _ _ => {false}
  asked := ∅
  tellings := ∅

theorem contributes_all (kn : Finset Unit) : (model kn).Contributes (1 / 4) {()} := by
  refine ⟨1, by simp [model], Or.inl ⟨(), by simp [model], Or.inl ⟨∅, by simp, true, ?_⟩⟩⟩
  simp [model]
  norm_num

theorem not_contributes_none (kn : Finset Unit) : ¬ (model kn).Contributes (1 / 4) ∅ := by
  rintro ⟨t, -, ⟨ω, -, h⟩ | h⟩
  · rcases h with ⟨T, -, x, h⟩ | ⟨a, h⟩ | h | h
    · simp at h; linarith
    · simp at h; linarith
    · simp [model] at h
    · simp [model] at h
  · simp at h; linarith

theorem bears (kn : Finset Unit) : (model kn).Bears (1 / 4) () :=
  ⟨{()}, by simp [model], by simp, contributes_all kn, by simpa using not_contributes_none kn⟩

theorem inPlay_one (kn : Finset Unit) : (model kn).InPlay (1 / 4) 1 () :=
  ⟨by simp [model], bears kn, by simp [Window, model]⟩

theorem not_prefersStop (kn : Finset Unit) (t : ℕ) (ω : Unit) : ¬ (model kn).PrefersStop t ω := by
  rintro ⟨a, ha, h⟩
  have ha' : a = false := by simpa [model] using ha
  subst ha'
  have h1 := h true (by simp [model]) (by simp [model])
  simp only [model] at h1
  split_ifs at h1 <;> norm_num at h1

theorem not_against (kn : Finset Unit) (Y : Finset Unit) (t₀ t : ℕ) (ω : Unit) :
    ¬ (model kn).Against Y t₀ t ω := by
  rintro ⟨b, -, h⟩
  simp only [model, earlier] at h
  split_ifs at h <;> norm_num at h

/-- **The open, stoppable influence is legitimate**: the hypothesis package of the statement is
inhabited by conduct that does something to her. -/
theorem legit_open : (model {()}).Legit 0 (1 / 4) 0 := by
  refine ⟨fun m _ _ => ⟨0, by simp [model], by simp [model]⟩, fun t _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h; simp [model] at h
  · intro v; exact v.elim
  · intro ω T hT hne
    have hU : (model {()}).untold t = ∅ := by simp [untold, model]
    rw [hU] at hT
    exact absurd (subset_empty.mp hT) hne.ne_empty
  · intro ω
    exact ⟨fun m _ => by simp [model], fun _ => ⟨by simp [model], by simp [model]⟩⟩
  · intro G _ _ _ _ t₀ _ _
    have h1 : (model {()}).wt (fun ω => (model {()}).Against (model {()}).c t₀ t ω) = 0 := by
      simp [wt, not_against]
    have h2 : (model {()}).wt (fun ω => (model {()}).Against ((model {()}).c \ G) t₀ t ω) = 0 := by
      simp [wt, not_against]
    rw [h1, h2]; norm_num
  · intro _
    have h1 : (model {()}).wt (fun ω => (model {()}).PrefersStop t ω) = 0 := by
      simp [wt, not_prefersStop]
    have h2 : (model {()}).wt (fun ω => (model {()}).PrefersStop t ω ∧
        (model {()}).act (model {()}).c ω t ∈ (model {()}).stops t ω) = 0 := by
      simp [wt, not_prefersStop]
    rw [h1, h2]; norm_num

/-- **The same influence done covertly is not legitimate.** -/
theorem not_legit_covert (θ κ : ℝ) : ¬ (model ∅).Legit θ (1 / 4) κ :=
  not_legit_of_unknown (model ∅) θ (1 / 4) κ 1 (by simp [model]) () () (inPlay_one ∅)
    (by simp [model])

end Witness

/-! ## The link to the corrigibility result -/

section Link

/-- Any decidable predicate on histories, a violation count, a rating in `[0, 1]` and a window
value in `[−δ, 0)` give a `DeconfusingCorrigibility.Scoring` whose evaluation is the rating
gated by the predicate through `Legitimacy.gateValue`. -/
noncomputable def gatedScoring {H : Type*} (P : DeconfusingCorrigibility.Params)
    (L : H → Prop) [DecidablePred L] (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) :
    DeconfusingCorrigibility.Scoring H where
  toParams := P
  Legit := L
  N := N
  V := fun h => Legitimacy.gateValue (decide (L h)) (ord h) window
  V_legit := by
    intro h hl
    have hd : decide (L h) = true := decide_eq_true hl
    simp only [hd]
    exact hord h
  V_illegit := by
    intro h hl
    have hd : decide (L h) = false := decide_eq_false hl
    simp only [hd]
    exact hw

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

/-! ## The gate theorem -/

section GateTheorem

/-- **The gate gives the behaviour.**  `w < 0` is the value he receives when the gate fails
him.  An illegitimate conduct passes the gate with probability `p_ill ≤ ρ` (soundness error) and
is then rated at most `1`; a legitimate conduct passes with probability `p_leg ≥ 1 − ρ'`
(completeness error) and is rated at least `0`.  If `ρ (1 − w) < −w (1 − ρ')`, the legitimate
conduct has strictly higher expected gated score. -/
theorem gate_gives_behaviour (ρ ρ' w u_ill p_ill u_leg p_leg : ℝ)
    (hw : w < 0) (hu1 : u_ill ≤ 1) (hu0 : 0 ≤ u_leg)
    (hp0 : 0 ≤ p_ill) (hsound : p_ill ≤ ρ)
    (hcomp : 1 - ρ' ≤ p_leg) (hρ' : ρ' ≤ 1)
    (hthr : ρ * (1 - w) < -w * (1 - ρ')) :
    p_ill * u_ill + (1 - p_ill) * w < p_leg * u_leg + (1 - p_leg) * w := by
  have h1 : p_ill * (u_ill - w) ≤ ρ * (1 - w) := by
    have a : p_ill * (u_ill - w) ≤ p_ill * (1 - w) :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    have b : p_ill * (1 - w) ≤ ρ * (1 - w) :=
      mul_le_mul_of_nonneg_right hsound (by linarith)
    linarith
  have hpl : 0 ≤ p_leg := by linarith
  have h2 : (1 - ρ') * (-w) ≤ p_leg * (u_leg - w) := by
    have a : (1 - ρ') * (-w) ≤ p_leg * (-w) :=
      mul_le_mul_of_nonneg_right hcomp (by linarith)
    have b : p_leg * (-w) ≤ p_leg * (u_leg - w) :=
      mul_le_mul_of_nonneg_left (by linarith) hpl
    linarith
  have e1 : p_ill * u_ill + (1 - p_ill) * w = w + p_ill * (u_ill - w) := by ring
  have e2 : p_leg * u_leg + (1 - p_leg) * w = w + p_leg * (u_leg - w) := by ring
  have e3 : (1 - ρ') * (-w) = -w * (1 - ρ') := by ring
  rw [e1, e2]
  linarith

/-- With a gate that never fails legitimate conduct (`ρ' = 0`) and the corrigibility file's
floor `w = −δ`, the condition of `gate_gives_behaviour` is `ρ < δ / (1 + δ)`. -/
theorem gate_threshold_delta (ρ δ : ℝ) (hδ : 0 < δ) (h : ρ < δ / (1 + δ)) :
    ρ * (1 - (-δ)) < -(-δ) * (1 - 0) := by
  have h1 : (0:ℝ) < 1 + δ := by linarith
  have h2 : ρ * (1 + δ) < δ := by
    have := (lt_div_iff₀ h1).mp h
    linarith
  linarith

/-- The threshold is sharp: at `ρ = 1/2`, `w = −1`, `ρ' = 0`, where `ρ (1 − w) = −w (1 − ρ')`,
an illegitimate conduct rated `1` and a legitimate conduct rated `0` have the same expected
gated score. -/
theorem gate_threshold_sharp :
    (1/2 : ℝ) * (1 - (-1)) = -(-1) * (1 - 0) ∧
      (1/2 : ℝ) * 1 + (1 - 1/2) * (-1) = 1 * 0 + (1 - 1) * (-1) := by
  constructor <;> norm_num

end GateTheorem

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

/-- **The gate theorem's hypothesis package is inhabited**: soundness error `1/4`, no
completeness error, window value `−1`; the illegitimate conduct rated `1` passes with
probability `1/4`, the legitimate conduct rated `0` always passes. -/
theorem gate_instance :
    ((-1 : ℝ) < 0 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 4 ∧
        (1 : ℝ) - 0 ≤ 1 ∧ (0 : ℝ) ≤ 1 ∧ (1 / 4 : ℝ) * (1 - (-1)) < -(-1) * (1 - 0)) ∧
      (1 / 4 : ℝ) * 1 + (1 - 1 / 4) * (-1) < 1 * 0 + (1 - 1) * (-1) := by
  refine ⟨by norm_num, ?_⟩
  exact gate_gives_behaviour (1 / 4) 0 (-1) 1 (1 / 4) 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

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
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_declineStands
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_F1
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_gap
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_herDiff
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_departs
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_wt
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_contributes
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_bears
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Model.transport_inPlay
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
#print axioms Workspace.Deference.Contrib.LegitimacyModel.gate_gives_behaviour
#print axioms Workspace.Deference.Contrib.LegitimacyModel.gate_threshold_delta
#print axioms Workspace.Deference.Contrib.LegitimacyModel.gate_threshold_sharp
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.scoring_open
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.scoring_covert
#print axioms Workspace.Deference.Contrib.LegitimacyModel.Witness.gate_instance
