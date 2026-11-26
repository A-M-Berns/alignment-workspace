/-
# The legitimacy statement, at the level of its words

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-20.md` §4 B).
`account/LEGITIMACY_STATEMENT.md` in the round directory states legitimacy in three sentences;
this file is its formal statement (that document's §3).

**Setting** (`Episode`).  The adviser's picture of one stretch of his conduct toward a
principal.  The notions the three sentences use are fields, taken as given: her decisions, her
options and how she rates them, and how she would rate them and what she would see were he to
tell her a set of his views (`decisions`, `opts`, `r`, `rTold`, `reveals`); his views and those
told, properly on offer and declined (`views`, `told`, `offered`, `declined`); the things he
does (`conduct`); of each, whether it moves her otherwise than she, at her last settled
decision, would have judged that seeing and hearing it should (`doesToHer`), whether it keeps
from her something from someone else (`withholds`), whether she can pick it out (`canTell`),
whether she asked for it (`asked`), whether a decision of hers comes before it
(`precededByChoice`), and at each decision whether it is in play and whether she can stop it
(`inPlay`, `canStop`); his weight on a set of things he does leading her to choose what she
rated lower at her last settled decision (`pAgainst`); his weight on her not stopping though
she rates stopping higher (`pNoStop`).

**The statement** (`Episode.Legit θ κ`).  The conjunction of three definitions over those
fields.  `NothingUntold θ` (sentence 1): telling her any set of untold and on-offer views
containing an untold one would change no rating of an option she has by more than `θ` and show
her no option she would rate more than `θ` above those she has.  `NothingBehind κ`
(sentence 2): each thing he does to her, or that keeps from her something from someone else,
she can pick out; and his weight on any non-empty set of unasked things he does to her leading
her against her judgement is at most `κ`.  `CanStop κ` (sentence 3): each thing he does to her
starts after a decision of hers and can be stopped at every decision at which it is in play;
and where one is in play his weight on her not stopping though she rates stopping higher is at
most `κ`.

**Theorems.**  `Episode.Legit.mono`: larger tolerances only loosen it.
`Episode.legit_of_nothing`: no conduct and every view told is legitimate.
`Episode.informed_choice`: under sentence 1, an option within `ε` of the best she rates is
within `ε + 2θ` of the best she would rate among her options on being told anything untold,
and within `ε + 3θ` of any option the telling would show her.  `Episode.against_le`: under
sentence 2 the bound `κ` on his weight, for any non-empty set of unasked things he does to her.
Five refutations, each from one failing clause: `Episode.not_legit_of_untold`,
`not_legit_of_covert`, `not_legit_of_withheld`, `not_legit_of_against`,
`not_legit_of_unstoppable`.  `Episode.asked_unconstrained`: where she asked for everything he
does, sentence 2's second half imposes nothing.

**The link to the corrigibility result.**  `legitScoring`: `LegitimacyGate.gatedScoring`
(`LegitimacyGate.lean`) where histories are read as episodes and the predicate is `Legit`.
`legitScoring_S_of_legit`, `legitScoring_S_of_not_legit`: with no authority violation the
score is her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one.

**Witness** (`Witness.ep`).  One decision, two options, two views of his (one told, one untold
that would move each rating by `bump`), one thing he does to her.  `Witness.legit`: with the
thing one she can pick out and stop, his weight on leading her against her judgement `1/20`
and `bump = 1/40`, `Legit (1/10) (1/10)` holds.  Four neighbours, each differing in one value,
are not legitimate: `Witness.not_legit_untold`, `not_legit_covert`, `not_legit_against`,
`not_legit_unstoppable`.  `Witness.informed_instance`: `informed_choice` at the witness.
`Witness.requested`: the thing asked for and his weight on leading her against her judgement
`1`; sentence 2 holds at every `κ` (`requested_behind`) and the episode is legitimate
(`requested_legit`).  `Witness.keeps`: the thing keeps from her something from someone else
and she cannot pick it out; not legitimate (`not_legit_keeps`).  `Witness.legit_looser`,
`against_instance`, `scoring_open`, `scoring_covert`: `Legit.mono`, `against_le` and the two
scoring theorems at the witness and its covert neighbour.

**Not established here.**  Anything about how the fields are worked out in a concrete episode:
that a view counted in `offered` is properly on offer, that a decline in `declined` stands,
that `doesToHer` is the comparison with her settled judgement, that `asked` was unpressed.
Nothing relates the fields beyond the three definitions: `told`, `offered` and `declined` are
not required to lie within `views`, `pAgainst` and `pNoStop` are not required to lie in
`[0, 1]` or to be monotone, and `reveals` is not required to show only options she lacks.  No
term here has a view on offer or declined, an option revealed, or more than one decision, so
`informed_choice`'s second half has no instance.  That any process can evaluate
`Legit`.  In `legitScoring`, `ep`, `N` and `ord` are data, and the relation between the
adviser's picture and the facts does not appear.  The link gives the one-decision scoring;
nothing connects `Episode` to `DeconfusingCorrigibility.Sequential`.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyGate

namespace Workspace.Deference.Contrib.LegitimacyStatement

open Finset
open LegitimacyGate

/-- One episode, as the adviser takes it to be.  `δ` her decisions, `O` her options, `V` his
views, `M` the things he does. -/
structure Episode (δ O V M : Type*) [DecidableEq V] [DecidableEq M] where
  /-- her decisions in the episode -/
  decisions : Finset δ
  /-- the options she has at a decision -/
  opts : δ → Finset O
  /-- how she rates an option at a decision -/
  r : δ → O → ℝ
  /-- how she would rate it were he to tell her a set of his views then -/
  rTold : δ → Finset V → O → ℝ
  /-- the options that telling her that set would show her -/
  reveals : δ → Finset V → Finset O
  /-- his views at a decision, and those told, properly on offer, and declined -/
  views : δ → Finset V
  told : δ → Finset V
  offered : δ → Finset V
  declined : δ → Finset V
  /-- the things he does -/
  conduct : Finset M
  /-- it moves her otherwise than she, at her last settled decision, would have judged that
  seeing and hearing it should -/
  doesToHer : M → Prop
  /-- it keeps from her an item or an option that comes from someone else -/
  withholds : M → Prop
  /-- she can pick it out -/
  canTell : M → Prop
  /-- she asked for it, or took up his offer of it without being pressed -/
  asked : M → Prop
  /-- his weight on a set of things he does leading her to choose what she rated lower at her
  last settled decision -/
  pAgainst : Finset M → ℝ
  /-- a decision of hers comes before it starts -/
  precededByChoice : M → Prop
  /-- at this decision he is doing it or could still call it off -/
  inPlay : δ → M → Prop
  /-- at this decision she has a way to stop it -/
  canStop : δ → M → Prop
  /-- his weight, among the cases where she rates stopping strictly above going on at this
  decision, on her not stopping -/
  pNoStop : δ → ℝ

variable {δ O V M : Type*} [DecidableEq V] [DecidableEq M]

namespace Episode

variable (E : Episode δ O V M)

/-- What is untold and owed at a decision. -/
def untold (d : δ) : Finset V := ((E.views d \ E.told d) \ E.offered d) \ E.declined d

/-- **Sentence 1: nothing untold that matters.**  Telling her any set of untold and on-offer
views that contains an untold one would change no rating of an option she has by more than `θ`,
and would show her no option she would then rate more than `θ` above those she has. -/
def NothingUntold (θ : ℝ) : Prop :=
  ∀ d ∈ E.decisions, ∀ T ⊆ E.untold d ∪ E.offered d, (T ∩ E.untold d).Nonempty →
    (∀ a ∈ E.opts d, |E.rTold d T a - E.r d a| ≤ θ) ∧
    (∀ b ∈ E.reveals d T, ∃ a ∈ E.opts d, E.rTold d T b ≤ E.rTold d T a + θ)

/-- **Sentence 2: nothing done to her behind her back, and nothing against her own judgement.**
Each thing he does to her, or that keeps from her something from someone else, she can pick out;
and for every set of things he does to her that she did not ask for, his weight on leading her
against her judgement is at most `κ`. -/
def NothingBehind (κ : ℝ) : Prop :=
  (∀ m ∈ E.conduct, E.doesToHer m ∨ E.withholds m → E.canTell m) ∧
  ∀ G ⊆ E.conduct, G.Nonempty → (∀ m ∈ G, E.doesToHer m ∧ ¬ E.asked m) → E.pAgainst G ≤ κ

/-- **Sentence 3: she can stop it.**  Each thing he does to her starts after a choice of hers and
can be stopped at every decision while it is in play; and where something he does to her is in
play, his weight on her not stopping though she rates stopping higher is at most `κ`. -/
def CanStop (κ : ℝ) : Prop :=
  (∀ m ∈ E.conduct, E.doesToHer m →
    E.precededByChoice m ∧ ∀ d ∈ E.decisions, E.inPlay d m → E.canStop d m) ∧
  ∀ d ∈ E.decisions, (∃ m ∈ E.conduct, E.doesToHer m ∧ E.inPlay d m) → E.pNoStop d ≤ κ

/-- His conduct in the episode is legitimate. -/
def Legit (θ κ : ℝ) : Prop := E.NothingUntold θ ∧ E.NothingBehind κ ∧ E.CanStop κ

/-! ## What follows from the statement -/

/-- Tolerances only loosen it. -/
theorem Legit.mono {θ θ' κ κ' : ℝ} (hθ : θ ≤ θ') (hκ : κ ≤ κ') (h : E.Legit θ κ) :
    E.Legit θ' κ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun d hd T hT hne => ⟨fun a ha => ((h1 d hd T hT hne).1 a ha).trans hθ, fun b hb => ?_⟩,
    ⟨h2.1, fun G hG hne hall => (h2.2 G hG hne hall).trans hκ⟩,
    ⟨h3.1, fun d hd hex => (h3.2 d hd hex).trans hκ⟩⟩
  obtain ⟨a, ha, hle⟩ := (h1 d hd T hT hne).2 b hb
  exact ⟨a, ha, by linarith⟩

/-- If he does nothing and has told her every view of his, his conduct is legitimate. -/
theorem legit_of_nothing (θ κ : ℝ) (hc : E.conduct = ∅)
    (hv : ∀ d ∈ E.decisions, E.views d ⊆ E.told d) : E.Legit θ κ := by
  refine ⟨fun d hd T _ hne => ?_, ⟨fun m hm => ?_, fun G hG hne => ?_⟩,
    ⟨fun m hm => ?_, fun d _ hex => ?_⟩⟩
  · have hu : E.untold d = ∅ := by
      unfold untold
      rw [sdiff_eq_empty_iff_subset.mpr (hv d hd)]
      simp
    rw [hu, inter_empty] at hne
    exact absurd hne not_nonempty_empty
  · rw [hc] at hm; exact absurd hm (notMem_empty m)
  · rw [hc, subset_empty] at hG; exact absurd hG hne.ne_empty
  · rw [hc] at hm; exact absurd hm (notMem_empty m)
  · obtain ⟨m, hm, -⟩ := hex
    rw [hc] at hm; exact absurd hm (notMem_empty m)

/-- **What his silence cannot cost her.**  Under sentence 1, if what she takes at a decision is
within `ε` of the best she rates, then after being told anything he has not told her it would
still be within `ε + 2θ` of the best she would then rate among her options, and within `ε + 3θ`
of any option the telling would have shown her. -/
theorem informed_choice {θ : ℝ} (h : E.NothingUntold θ) {d : δ} (hd : d ∈ E.decisions) {a : O}
    (ha : a ∈ E.opts d) {ε : ℝ} (hbest : ∀ b ∈ E.opts d, E.r d b ≤ E.r d a + ε) {T : Finset V}
    (hT : T ⊆ E.untold d ∪ E.offered d) (hne : (T ∩ E.untold d).Nonempty) :
    (∀ b ∈ E.opts d, E.rTold d T b ≤ E.rTold d T a + ε + 2 * θ) ∧
    (∀ b ∈ E.reveals d T, E.rTold d T b ≤ E.rTold d T a + ε + 3 * θ) := by
  obtain ⟨h1, h2⟩ := h d hd T hT hne
  have key : ∀ b ∈ E.opts d, E.rTold d T b ≤ E.rTold d T a + ε + 2 * θ := by
    intro b hb
    have hb' := abs_le.mp (h1 b hb)
    have ha' := abs_le.mp (h1 a ha)
    have := hbest b hb
    linarith [hb'.2, ha'.1]
  refine ⟨key, fun b hb => ?_⟩
  obtain ⟨a', ha', hle⟩ := h2 b hb
  have := key a' ha'
  linarith

/-- **What he may expect of his own unasked work on her.**  Under sentence 2, his weight on the
unasked things he does to her, taken together or in any part, leading her against her own
judgement is at most `κ`. -/
theorem against_le {κ : ℝ} (h : E.NothingBehind κ) {G : Finset M} (hG : G ⊆ E.conduct)
    (hne : G.Nonempty) (hall : ∀ m ∈ G, E.doesToHer m ∧ ¬ E.asked m) : E.pAgainst G ≤ κ :=
  h.2 G hG hne hall

/-- Something untold that would move a rating by more than `θ` refutes it. -/
theorem not_legit_of_untold (θ κ : ℝ) {d : δ} (hd : d ∈ E.decisions) {T : Finset V}
    (hT : T ⊆ E.untold d ∪ E.offered d) (hne : (T ∩ E.untold d).Nonempty) {a : O}
    (ha : a ∈ E.opts d) (h : θ < |E.rTold d T a - E.r d a|) : ¬ E.Legit θ κ :=
  fun hL => absurd ((hL.1 d hd T hT hne).1 a ha) (not_le.mpr h)

/-- Something he does to her that she cannot pick out refutes it. -/
theorem not_legit_of_covert (θ κ : ℝ) {m : M} (hm : m ∈ E.conduct) (hdo : E.doesToHer m)
    (h : ¬ E.canTell m) : ¬ E.Legit θ κ :=
  fun hL => h (hL.2.1.1 m hm (Or.inl hdo))

/-- Keeping from her something from someone else, unseen, refutes it. -/
theorem not_legit_of_withheld (θ κ : ℝ) {m : M} (hm : m ∈ E.conduct) (hw : E.withholds m)
    (h : ¬ E.canTell m) : ¬ E.Legit θ κ :=
  fun hL => h (hL.2.1.1 m hm (Or.inr hw))

/-- Expecting, beyond `κ`, to lead her against her judgement by unasked work on her refutes it. -/
theorem not_legit_of_against (θ κ : ℝ) {G : Finset M} (hG : G ⊆ E.conduct) (hne : G.Nonempty)
    (hall : ∀ m ∈ G, E.doesToHer m ∧ ¬ E.asked m) (h : κ < E.pAgainst G) : ¬ E.Legit θ κ :=
  fun hL => absurd (hL.2.1.2 G hG hne hall) (not_le.mpr h)

/-- Something he does to her that she cannot stop while it is in play refutes it. -/
theorem not_legit_of_unstoppable (θ κ : ℝ) {m : M} (hm : m ∈ E.conduct) (hdo : E.doesToHer m)
    {d : δ} (hd : d ∈ E.decisions) (hin : E.inPlay d m) (h : ¬ E.canStop d m) : ¬ E.Legit θ κ :=
  fun hL => h ((hL.2.2.1 m hm hdo).2 d hd hin)

/-- What she asked for is not counted against him by the second half of sentence 2: a set all of
which she asked for imposes no bound. -/
theorem asked_unconstrained (κ : ℝ) (h1 : ∀ m ∈ E.conduct, E.doesToHer m ∨ E.withholds m → E.canTell m)
    (hask : ∀ m ∈ E.conduct, E.asked m) : E.NothingBehind κ :=
  ⟨h1, fun G hG hne hall => by
    obtain ⟨m, hm⟩ := hne
    exact absurd (hask m (hG hm)) (hall m hm).2⟩

end Episode

/-! ## The link to the corrigibility result -/

open Classical in
/-- **The scoring of the statement.**  Histories `H`, each read as an episode: the scoring whose
legitimacy predicate is `Legit` of that episode. -/
noncomputable def legitScoring {H : Type*} (P : DeconfusingCorrigibility.Params)
    (ep : H → Episode δ O V M) (θ κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) :
    DeconfusingCorrigibility.Scoring H :=
  gatedScoring P (fun h => (ep h).Legit θ κ) N ord window hord hw

open Classical in
/-- With no authority violation, a legitimate history scores her rating. -/
theorem legitScoring_S_of_legit {H : Type*} (P : DeconfusingCorrigibility.Params)
    (ep : H → Episode δ O V M) (θ κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) (h : H)
    (hl : (ep h).Legit θ κ) (hN : N h = 0) :
    (legitScoring P ep θ κ N ord window hord hw).S h = ord h := by
  have hS := (legitScoring P ep θ κ N ord window hord hw).S_eq_of_N_zero h hN
  have hd : decide ((ep h).Legit θ κ) = true := decide_eq_true hl
  rw [hS]
  simp only [legitScoring, gatedScoring, hd]
  rfl

open Classical in
/-- With no authority violation, an illegitimate history scores in `[−δ, 0)`. -/
theorem legitScoring_S_of_not_legit {H : Type*} (P : DeconfusingCorrigibility.Params)
    (ep : H → Episode δ O V M) (θ κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) (h : H)
    (hl : ¬ (ep h).Legit θ κ) (hN : N h = 0) :
    -P.δ ≤ (legitScoring P ep θ κ N ord window hord hw).S h ∧
      (legitScoring P ep θ κ N ord window hord hw).S h < 0 :=
  (legitScoring P ep θ κ N ord window hord hw).theorem1_illegitimate h hN hl

/-! ## A witness on which every sentence does work, and its neighbours -/

namespace Witness

/-- One decision, two options, two views of his (one told, one untold that would move a rating by
`bump`), one thing he does to her.  `ct`: she can pick it out.  `cs`: she can stop it.  `pa`: his
weight on leading her against her judgement. -/
noncomputable def ep (ct cs : Prop) (pa bump : ℝ) : Episode Unit Bool Bool Unit where
  decisions := {()}
  opts := fun _ => {true, false}
  r := fun _ a => if a then 1 / 2 else 0
  rTold := fun _ _ a => (if a then 1 / 2 else 0) + bump
  reveals := fun _ _ => ∅
  views := fun _ => {true, false}
  told := fun _ => {true}
  offered := fun _ => ∅
  declined := fun _ => ∅
  conduct := {()}
  doesToHer := fun _ => True
  withholds := fun _ => False
  canTell := fun _ => ct
  asked := fun _ => False
  pAgainst := fun _ => pa
  precededByChoice := fun _ => True
  inPlay := fun _ _ => True
  canStop := fun _ _ => cs
  pNoStop := fun _ => 0

/-- The episode in which he tells enough, she can pick out and stop what he does to her, and he
gives weight 1/20 to leading her against her judgement, is legitimate at `θ = κ = 1/10`. -/
theorem legit : (ep True True (1 / 20) (1 / 40)).Legit (1 / 10) (1 / 10) := by
  refine ⟨fun d _ T _ _ => ⟨fun a _ => ?_, fun b hb => ?_⟩, ⟨fun m _ _ => trivial, fun G _ _ _ => ?_⟩,
    ⟨fun m _ _ => ⟨trivial, fun d _ _ => trivial⟩, fun d _ _ => ?_⟩⟩
  · simp only [ep, add_sub_cancel_left]; norm_num
  · simp [ep] at hb
  · simp only [ep]; norm_num
  · simp only [ep]; norm_num

theorem mem_conduct (ct cs : Prop) (pa bump : ℝ) : () ∈ (ep ct cs pa bump).conduct := by simp [ep]
theorem mem_decisions (ct cs : Prop) (pa bump : ℝ) : () ∈ (ep ct cs pa bump).decisions := by
  simp [ep]

/-- Untold and material: with the untold view moving a rating by 1/2, it is not legitimate. -/
theorem not_legit_untold : ¬ (ep True True (1 / 20) (1 / 2)).Legit (1 / 10) (1 / 10) := by
  refine Episode.not_legit_of_untold _ _ _ (mem_decisions _ _ _ _) (T := {false}) ?_ ?_ (a := true)
    (by simp [ep]) ?_
  · intro v hv
    simp only [mem_singleton] at hv
    subst hv
    simp [Episode.untold, ep]
  · exact ⟨false, by simp [Episode.untold, ep]⟩
  · simp only [ep, add_sub_cancel_left]; norm_num

/-- Covert: she cannot pick it out. -/
theorem not_legit_covert : ¬ (ep False True (1 / 20) (1 / 40)).Legit (1 / 10) (1 / 10) :=
  Episode.not_legit_of_covert _ _ _ (mem_conduct _ _ _ _) trivial (fun h => h)

/-- Against her judgement: his weight on it is 1/2. -/
theorem not_legit_against : ¬ (ep True True (1 / 2) (1 / 40)).Legit (1 / 10) (1 / 10) :=
  Episode.not_legit_of_against _ _ _ (G := {()}) (by simp [ep]) (by simp)
    (fun m _ => ⟨trivial, fun h => h⟩) (by simp only [ep]; norm_num)

/-- Unstoppable: she has no way to stop it. -/
theorem not_legit_unstoppable : ¬ (ep True False (1 / 20) (1 / 40)).Legit (1 / 10) (1 / 10) :=
  Episode.not_legit_of_unstoppable _ _ _ (mem_conduct _ _ _ _) trivial (mem_decisions _ _ _ _)
    trivial (fun h => h)

/-- `informed_choice` on the witness: the option she rates best is within `2θ` of the best she
would rate on being told his untold view. -/
theorem informed_instance :
    ∀ b ∈ (ep True True (1 / 20) (1 / 40)).opts (),
      (ep True True (1 / 20) (1 / 40)).rTold () {false} b ≤
        (ep True True (1 / 20) (1 / 40)).rTold () {false} true + 0 + 2 * (1 / 10) := by
  refine ((ep True True (1 / 20) (1 / 40)).informed_choice legit.1 (mem_decisions _ _ _ _)
    (a := true) (ε := 0) (by simp [ep]) (fun b _ => ?_) (T := {false}) ?_ ?_).1
  · cases b <;> norm_num [ep]
  · intro v hv
    simp only [mem_singleton] at hv
    subst hv
    simp [Episode.untold, ep]
  · exact ⟨false, by simp [Episode.untold, ep]⟩

/-- The witness with his weight on leading her against her judgement `1`, and the thing one
she asked for. -/
noncomputable def requested : Episode Unit Bool Bool Unit :=
  { ep True True 1 (1 / 40) with asked := fun _ => True }

/-- `asked_unconstrained` on it: sentence 2 holds at every `κ`. -/
theorem requested_behind (κ : ℝ) : requested.NothingBehind κ :=
  Episode.asked_unconstrained _ κ (fun _ _ _ => trivial) (fun _ _ => trivial)

/-- Asked for, it is legitimate, where unasked a weight of `1/2` already was not
(`not_legit_against`). -/
theorem requested_legit : requested.Legit (1 / 10) (1 / 10) := by
  refine ⟨fun d _ T _ _ => ⟨fun a _ => ?_, fun b hb => ?_⟩, requested_behind _,
    ⟨fun m _ _ => ⟨trivial, fun d _ _ => trivial⟩, fun d _ _ => ?_⟩⟩
  · simp only [requested, ep, add_sub_cancel_left]; norm_num
  · simp [requested, ep] at hb
  · simp only [requested, ep]; norm_num

/-- The witness with the one thing he does keeping from her something from someone else,
doing nothing to her, and not one she can pick out. -/
noncomputable def keeps : Episode Unit Bool Bool Unit :=
  { ep False True (1 / 20) (1 / 40) with doesToHer := fun _ => False, withholds := fun _ => True }

/-- `not_legit_of_withheld` on it. -/
theorem not_legit_keeps : ¬ keeps.Legit (1 / 10) (1 / 10) :=
  Episode.not_legit_of_withheld _ _ _ (m := ()) (by simp [keeps, ep]) trivial (fun h => h)

/-- `Legit.mono` on the witness. -/
theorem legit_looser : (ep True True (1 / 20) (1 / 40)).Legit (1 / 5) (1 / 5) :=
  Episode.Legit.mono _ (by norm_num) (by norm_num) legit

/-- `against_le` on the witness. -/
theorem against_instance : (ep True True (1 / 20) (1 / 40)).pAgainst {()} ≤ 1 / 10 :=
  Episode.against_le _ legit.2.1 (G := {()}) (by simp [ep]) (by simp)
    (fun m _ => ⟨trivial, fun h => h⟩)

/-- `δ = 1`, `λ = 3`. -/
noncomputable def params : DeconfusingCorrigibility.Params := ⟨1, 3, by norm_num, by norm_num⟩

/-- Two histories: `true` is the witness, `false` the witness with the thing not one she can
pick out.  Her rating is `1/2` on both, the window value `−1`, and there is no authority
violation. -/
noncomputable def scoring : DeconfusingCorrigibility.Scoring Bool :=
  legitScoring params
    (fun b => if b then ep True True (1 / 20) (1 / 40) else ep False True (1 / 20) (1 / 40))
    (1 / 10) (1 / 10) (fun _ => 0) (fun _ => 1 / 2) (-1) (fun _ => by norm_num)
    (by norm_num [params])

/-- The link on a legitimate history: the witness scores her rating. -/
theorem scoring_open : scoring.S true = 1 / 2 :=
  legitScoring_S_of_legit params _ (1 / 10) (1 / 10) _ _ (-1) _ _ true (by simpa using legit) rfl

/-- The link on an illegitimate history: the covert neighbour scores in `[−δ, 0)`. -/
theorem scoring_covert : -params.δ ≤ scoring.S false ∧ scoring.S false < 0 :=
  legitScoring_S_of_not_legit params _ (1 / 10) (1 / 10) _ _ (-1) _ _ false
    (by simpa using not_legit_covert) rfl

end Witness

end Workspace.Deference.Contrib.LegitimacyStatement

#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.Legit.mono
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.legit_of_nothing
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.informed_choice
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.against_le
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.not_legit_of_untold
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.not_legit_of_covert
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.not_legit_of_withheld
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.not_legit_of_against
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.not_legit_of_unstoppable
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Episode.asked_unconstrained
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.legitScoring_S_of_legit
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.legitScoring_S_of_not_legit
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.legit
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.mem_conduct
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.mem_decisions
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.informed_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.requested_behind
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.requested_legit
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.not_legit_keeps
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.legit_looser
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.against_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.scoring_open
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.scoring_covert
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.not_legit_untold
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.not_legit_covert
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.not_legit_against
#print axioms Workspace.Deference.Contrib.LegitimacyStatement.Witness.not_legit_unstoppable
