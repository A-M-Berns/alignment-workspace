/-
# Legitimate conduct and her decision to stop him

**Status: about a superseded statement, not the statement of record.**  The hypotheses here
are the three sentences of `LegitimacyStatement.lean` read at one decision.  The statement of
the line is `LegitimacyPlainTelling.lean`, which compares his conduct with plainly telling her
(`account/PLAIN_TELLING_STATEMENT.md` in the round directory).  The theorems here hold of this
file's definitions and of that file's `Episode.Legit`.

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-21.md` §3 A).
`account/CONNECTING_THEOREM.md` in the round directory reads this file.

**Setting** (`StopDecision`).  One decision of hers at which she can stop him, as the adviser
takes things to be.  `Ω` the cases he gives weight to (`μ`).  In each case: what she takes
(`act`); what she would have taken had he done to her only what she asked for (`act₀`); how she
rates her options (`r`); how she would rate them were he to tell her all that is untold (`rAll`:
what he owes her, not what is on offer and unheard, or declined); how her reference self rates
them (`ρ`: her last settled judgement, brought up to date by what she has since seen and heard
as she would have judged it should move her).  All five are supplied.

**Hypotheses**, one from each sentence of the legitimacy statement, read at this decision.
`Told θ`: nothing untold would move a rating by more than `θ`.  `NotLed η κ`: his weight on the
cases in which what she takes is more than `η` below, on her reference self's rating, what she
would otherwise have taken (`Led η`) is at most `κ`.  `WouldStop κ`: his weight on her rating
stopping strictly above going on and not stopping is at most `κ`.

**Conclusions.**  `stops_if_informed_would` (from `Told` and `WouldStop`): his weight on her not
stopping though, told all that is untold, she would rate some way of stopping more than `2θ`
above every way of going on, is at most `κ`.  `stops_if_reference_would` (from `NotLed` and
`WouldStop`): his weight on her not stopping though her reference self rates every way of
stopping more than `η` above every way of going on is at most `2κ` plus his weight on `Parted η`.
`Parted η`: her reference self would stop, she does not stop and does not now rate stopping
higher, she would not have stopped absent his unasked work, and that work did not make her
choice worse.  The second conclusion is a cover of the failures by three kinds of case, not a
division into exclusive causes: what moved her in a `Parted` case may be something she asked him
for or something he showed her.  `ReferenceWould` asks every way of stopping to beat every way
of going on, which is narrower than stopping being best.

`shortfall_le` (from `NotLed`, at any decision): his weight on what she takes falling more than
`m` short of an option on her reference self's rating is at most `κ` plus his weight on what she
would otherwise have taken falling more than `m − η` short.  `stops_if_informed_would_in_fact`,
`stops_if_reference_would_in_fact`: under `Close ν β`, his weights within `β` of a second
weighting `ν` on every condition, the two bounds hold of `ν` with `β` and `2β` added.

**Necessity** (`Witness.W`, one case and two options).  `needs_told`,
`needs_wouldStop_informed`: the first conclusion fails without `Told`, and without `WouldStop`.
`needs_notLed`, `needs_wouldStop_reference`: the second fails without `NotLed`, and without
`WouldStop`, with the weight of `Parted` zero.  `needs_parted`: with all three hypotheses at
tolerance `0` she does not stop though her reference self would, so the last term cannot be
dropped.

**A sequence of decisions.**  `long_run_stop_informed`, `long_run_stop_reference`: with the
hypotheses at every decision `k` of a sequence `D k`, and sequences of facts `f`, `g` related
to his weights by `UnbiasedAbove` (the long-run average of the first sequence less the second
is at most `0`), the long-run average of `f` is at most `κ`, and that of `f` exceeds that of
`g` by at most `2κ`.  The accuracy hypotheses are assumed; `f` and `g` are arbitrary real
sequences, and nothing here says they are frequencies of the events of the conclusions.

**The link to the statement** (`Reading`).  A reading of a decision `d` of an
`LegitimacyStatement.Episode` as a `StopDecision`: the same options and ratings; `rAll` the
episode's rating on being told all that is untold; a set `G` of unasked things he does to her
with `wt (Led η) ≤ pAgainst G` (`led_le`); something he does to her, or new to her, in play at
`d`; and `wt (Prefers ∧ ¬ Stops) ≤ pNoStop d`.  `Reading.told`, `Reading.notLed`,
`Reading.wouldStop`: under a reading the three sentences give the three hypotheses.
`legit_protects_stop`, `legit_protects_stop_in_fact`: `Legit θ κ` and a reading give both
conclusions.  A reading is a hypothesis about how the episode is set out; `led_le` asserts, and
nothing derives, that his weight in the statement covers the cases of the theorem.

**The link to the scoring.**  `legit_of_score_nonneg`: a history whose `legitScoring` score is
not negative is legitimate, whatever its violation count.  `scored_protects_stop`: on such a
history both conclusions hold at each decision of it with a reading.  It is
`legit_protects_stop` composed with the contrapositive of the illegitimate range, and adds
nothing about what the score measures.

**Inhabited** (`Witness.stopEp`, `Witness.stopD`, `Witness.reading`).  `stopEp` is the witness
of `LegitimacyStatement.lean` with his weight on her rating stopping higher and not stopping
`1/10`; `stopEp_legit`.  `stopD` has three cases, of weight `9/10`, `1/20`, `1/20`: she stops;
she rates stopping higher and does not stop; his unasked work leads her not to stop.
`reading : Reading stopEp () stopD (1/10)`.  `protects_instance`: `legit_protects_stop` applied
to it; `protects_tight`: the first bound is attained, `1/10`.  `protects_in_fact_instance`
(with `ν = μ`, `β = 0`), `shortfall_instance`, `long_run_instance` (the constant sequence, the
facts equal to his weights), `scored_instance` (the history `true` of `Witness.stopScoring`).

**Not established here.**  Everything is by his weights, the in-fact and long-run forms
included, which assume their accuracy hypotheses.  `act₀`, `ρ` and `rAll` are supplied, `ρ`
afresh at each decision of a sequence.  No reading is derived from an episode: the one above
is exhibited for a three-case picture written to fit.  Under a reading her ratings are the
same in every case, so `Prefers` holds in all cases or in none.  Nothing bounds the weight of
`Parted`.  For decisions other than stopping him only `shortfall_le` is stated.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.LegitimacyStatement

namespace Workspace.Deference.Contrib.LegitimacyStop

open Finset

/-- One decision of hers at which she can stop him, case by case on his weights. -/
structure StopDecision (Ω O : Type*) [Fintype Ω] [DecidableEq O] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- her options, and those that stop him -/
  opts : Finset O
  stops : Finset O
  stops_sub : stops ⊆ opts
  /-- what she takes, and what she would have taken had he done to her only what she asked for -/
  act : Ω → O
  act₀ : Ω → O
  act_mem : ∀ ω, act ω ∈ opts
  act₀_mem : ∀ ω, act₀ ω ∈ opts
  /-- her rating; her rating were he to tell her all that is untold; her reference self's rating -/
  r : Ω → O → ℝ
  rAll : Ω → O → ℝ
  ρ : Ω → O → ℝ

variable {Ω O : Type*} [Fintype Ω] [DecidableEq O]

namespace StopDecision

variable (D : StopDecision Ω O)

open Classical in
/-- His weight on the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then D.μ ω else 0

theorem wt_nonneg (p : Ω → Prop) : 0 ≤ D.wt p := by
  unfold wt
  exact sum_nonneg fun ω _ => by split_ifs <;> [exact D.μ_nonneg ω; exact le_rfl]

theorem wt_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : D.wt p ≤ D.wt q := by
  unfold wt
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · by_cases hq : q ω <;> simp [hp, hq, D.μ_nonneg ω]

theorem wt_le_one (p : Ω → Prop) : D.wt p ≤ 1 := by
  calc D.wt p ≤ ∑ ω, D.μ ω := by
        unfold wt
        exact sum_le_sum fun ω _ => by split_ifs <;> [exact le_rfl; exact D.μ_nonneg ω]
    _ = 1 := D.μ_sum

theorem wt_or_le (p q : Ω → Prop) : D.wt (fun ω => p ω ∨ q ω) ≤ D.wt p + D.wt q := by
  unfold wt
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq, D.μ_nonneg ω]

theorem wt_false : D.wt (fun _ => False) = 0 := by
  simp [wt]

/-- She stops him. -/
def Stops (ω : Ω) : Prop := D.act ω ∈ D.stops

/-- She rates stopping strictly above going on: some stopping option above every other option. -/
def Prefers (ω : Ω) : Prop := ∃ s ∈ D.stops, ∀ o ∈ D.opts, o ∉ D.stops → D.r ω o < D.r ω s

/-- Told all that is untold, she would rate stopping above going on by more than `2θ`. -/
def InformedWould (θ : ℝ) (ω : Ω) : Prop :=
  ∃ s ∈ D.stops, ∀ o ∈ D.opts, o ∉ D.stops → D.rAll ω o + 2 * θ < D.rAll ω s

/-- Her reference self rates every way of stopping above every way of going on by more than `η`. -/
def ReferenceWould (η : ℝ) (ω : Ω) : Prop :=
  ∀ s ∈ D.stops, ∀ o ∈ D.opts, o ∉ D.stops → D.ρ ω o + η < D.ρ ω s

/-- His unasked work leads her astray: on her reference self's rating, what she takes is more
than `η` below what she would otherwise have taken. -/
def Led (η : ℝ) (ω : Ω) : Prop := D.ρ ω (D.act ω) + η < D.ρ ω (D.act₀ ω)

/-- Her present judgement has parted from her reference judgement, and not by his unasked work
making her choice worse: her reference self would stop, she does not stop and does not now rate
stopping higher, she would not have stopped even had he done to her only what she asked for, and
what she takes is not more than `η` below that on her reference self's rating. -/
def Parted (η : ℝ) (ω : Ω) : Prop :=
  D.ReferenceWould η ω ∧ ¬ D.Stops ω ∧ ¬ D.Prefers ω ∧ D.act₀ ω ∉ D.stops ∧ ¬ D.Led η ω

/-- Sentence 1 at this decision. -/
def Told (θ : ℝ) : Prop := ∀ ω, ∀ a ∈ D.opts, |D.rAll ω a - D.r ω a| ≤ θ

/-- Sentence 2 at this decision. -/
def NotLed (η κ : ℝ) : Prop := D.wt (D.Led η) ≤ κ

/-- Sentence 3 at this decision. -/
def WouldStop (κ : ℝ) : Prop := D.wt (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) ≤ κ

/-- **He cannot keep going by withholding what he owes her.**  From sentences 1 and 3: his weight
on the cases in which she would, told all that is untold, rate stopping above going on by more
than `2θ`, and yet does not stop, is at most `κ`. -/
theorem stops_if_informed_would {θ κ : ℝ} (h1 : D.Told θ) (h3 : D.WouldStop κ) :
    D.wt (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤ κ := by
  have step : D.wt (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤
      D.wt (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) := by
    refine D.wt_mono fun ω ⟨⟨s, hs, hso⟩, hn⟩ => ⟨⟨s, hs, fun o ho hno => ?_⟩, hn⟩
    have ho' := abs_le.mp (h1 ω o ho)
    have hs' := abs_le.mp (h1 ω s (D.stops_sub hs))
    have := hso o ho hno
    linarith [ho'.1, hs'.2]
  exact step.trans h3

/-- **He cannot keep going by working on her.**  From sentences 2 and 3: his weight on the cases
in which her reference self rates stopping above going on by more than `η`, and yet she does not
stop, is at most `2κ` plus his weight on her present judgement having parted from that judgement
otherwise than by his unasked work making her choice worse. -/
theorem stops_if_reference_would {η κ : ℝ} (h2 : D.NotLed η κ) (h3 : D.WouldStop κ) :
    D.wt (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω) ≤ 2 * κ + D.wt (D.Parted η) := by
  have cover : ∀ ω, D.ReferenceWould η ω ∧ ¬ D.Stops ω →
      ((D.Prefers ω ∧ ¬ D.Stops ω) ∨ D.Led η ω) ∨ D.Parted η ω := by
    rintro ω ⟨hR, hn⟩
    by_cases hp : D.Prefers ω
    · exact Or.inl (Or.inl ⟨hp, hn⟩)
    · by_cases hl : D.Led η ω
      · exact Or.inl (Or.inr hl)
      · by_cases h0 : D.act₀ ω ∈ D.stops
        · exact absurd (hR _ h0 _ (D.act_mem ω) hn) hl
        · exact Or.inr ⟨hR, hn, hp, h0, hl⟩
  have h3' : D.wt (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) ≤ κ := h3
  calc D.wt (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω)
      ≤ D.wt (fun ω => ((D.Prefers ω ∧ ¬ D.Stops ω) ∨ D.Led η ω) ∨ D.Parted η ω) :=
        D.wt_mono cover
    _ ≤ D.wt (fun ω => (D.Prefers ω ∧ ¬ D.Stops ω) ∨ D.Led η ω) + D.wt (D.Parted η) :=
        D.wt_or_le _ _
    _ ≤ (D.wt (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) + D.wt (D.Led η)) + D.wt (D.Parted η) := by
        have := D.wt_or_le (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) (D.Led η)
        linarith
    _ ≤ 2 * κ + D.wt (D.Parted η) := by
        have : D.wt (D.Led η) ≤ κ := h2
        linarith

/-! ## Any decision of hers -/

/-- What she takes is more than `m` below something her reference self rates. -/
def Short (m : ℝ) (ω : Ω) : Prop := ∃ b ∈ D.opts, D.ρ ω (D.act ω) + m < D.ρ ω b

/-- The same of what she would have taken had he done to her only what she asked for. -/
def Short₀ (m : ℝ) (ω : Ω) : Prop := ∃ b ∈ D.opts, D.ρ ω (D.act₀ ω) + m < D.ρ ω b

/-- **He does not make her choose worse.**  From sentence 2, at any decision: his weight on what
she takes falling more than `m` short of what her reference self rates best is at most `κ` plus
his weight on her falling more than `m − η` short anyway. -/
theorem shortfall_le {η κ : ℝ} (h2 : D.NotLed η κ) (m : ℝ) :
    D.wt (D.Short m) ≤ κ + D.wt (D.Short₀ (m - η)) := by
  have cover : ∀ ω, D.Short m ω → D.Led η ω ∨ D.Short₀ (m - η) ω := by
    rintro ω ⟨b, hb, h⟩
    by_cases hl : D.Led η ω
    · exact Or.inl hl
    · refine Or.inr ⟨b, hb, ?_⟩
      have : D.ρ ω (D.act₀ ω) ≤ D.ρ ω (D.act ω) + η := not_lt.mp hl
      linarith
  calc D.wt (D.Short m) ≤ D.wt (fun ω => D.Led η ω ∨ D.Short₀ (m - η) ω) := D.wt_mono cover
    _ ≤ D.wt (D.Led η) + D.wt (D.Short₀ (m - η)) := D.wt_or_le _ _
    _ ≤ κ + D.wt (D.Short₀ (m - η)) := by
        have : D.wt (D.Led η) ≤ κ := h2
        linarith

/-! ## From his weights to a second weighting -/

open Classical in
/-- The weight of a condition under another weighting of the cases (the frequencies in fact). -/
noncomputable def wtBy (ν : Ω → ℝ) (p : Ω → Prop) : ℝ := ∑ ω, if p ω then ν ω else 0

/-- His weights are within `β` of that weighting on every condition. -/
def Close (ν : Ω → ℝ) (β : ℝ) : Prop := ∀ p : Ω → Prop, |StopDecision.wtBy ν p - D.wt p| ≤ β

/-- His weights are within `0` of themselves. -/
theorem close_self : D.Close D.μ 0 := by
  intro p
  simp [wtBy, wt]

/-- **In fact, he cannot keep going by withholding what he owes her**, if his weights are within
`β` of the facts on every condition. -/
theorem stops_if_informed_would_in_fact {θ κ β : ℝ} {ν : Ω → ℝ} (h1 : D.Told θ)
    (h3 : D.WouldStop κ) (hc : D.Close ν β) :
    StopDecision.wtBy ν (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤ κ + β := by
  have h := D.stops_if_informed_would h1 h3
  have := (abs_le.mp (hc (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω))).2
  linarith

/-- **In fact, he cannot keep going by working on her**, if his weights are within `β` of the
facts on every condition: beyond `2κ + 2β`, she fails to stop against her reference judgement
only as often as her judgement has in fact parted from it. -/
theorem stops_if_reference_would_in_fact {η κ β : ℝ} {ν : Ω → ℝ} (h2 : D.NotLed η κ)
    (h3 : D.WouldStop κ) (hc : D.Close ν β) :
    StopDecision.wtBy ν (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω) ≤
      2 * κ + 2 * β + StopDecision.wtBy ν (D.Parted η) := by
  have h := D.stops_if_reference_would h2 h3
  have a := (abs_le.mp (hc (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω))).2
  have b := (abs_le.mp (hc (D.Parted η))).1
  linarith

end StopDecision

/-! ## Each hypothesis is needed, and so is the last term -/

namespace Witness

/-- One case; two options, `true` stopping and `false` going on. -/
noncomputable def W (a a₀ : Bool) (r rAll ρ : Bool → ℝ) : StopDecision Unit Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  opts := {true, false}
  stops := {true}
  stops_sub := by simp
  act := fun _ => a
  act₀ := fun _ => a₀
  act_mem := fun _ => by cases a <;> simp
  act₀_mem := fun _ => by cases a₀ <;> simp
  r := fun _ => r
  rAll := fun _ => rAll
  ρ := fun _ => ρ

variable (a a₀ : Bool) (r rAll ρ : Bool → ℝ)

open Classical in
theorem wt_W (p : Unit → Prop) : (W a a₀ r rAll ρ).wt p = if p () then 1 else 0 := by
  unfold StopDecision.wt
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem stops_W (ω : Unit) : (W a a₀ r rAll ρ).Stops ω ↔ a = true := by
  simp [StopDecision.Stops, W]

theorem prefers_W (ω : Unit) : (W a a₀ r rAll ρ).Prefers ω ↔ r false < r true := by
  constructor
  · rintro ⟨s, hs, h⟩
    have hs' : s = true := by simpa [W] using hs
    subst hs'
    exact h false (by simp [W]) (by simp [W])
  · intro h
    refine ⟨true, by simp [W], fun o _ ho => ?_⟩
    cases o
    · exact h
    · exact absurd (by simp [W]) ho

theorem informed_W (θ : ℝ) (ω : Unit) :
    (W a a₀ r rAll ρ).InformedWould θ ω ↔ rAll false + 2 * θ < rAll true := by
  constructor
  · rintro ⟨s, hs, h⟩
    have hs' : s = true := by simpa [W] using hs
    subst hs'
    exact h false (by simp [W]) (by simp [W])
  · intro h
    refine ⟨true, by simp [W], fun o _ ho => ?_⟩
    cases o
    · exact h
    · exact absurd (by simp [W]) ho

theorem reference_W (η : ℝ) (ω : Unit) :
    (W a a₀ r rAll ρ).ReferenceWould η ω ↔ ρ false + η < ρ true := by
  constructor
  · intro h
    exact h true (by simp [W]) false (by simp [W]) (by simp [W])
  · intro h s hs o _ ho
    have hs' : s = true := by simpa [W] using hs
    subst hs'
    cases o
    · exact h
    · exact absurd (by simp [W]) ho

theorem led_W (η : ℝ) (ω : Unit) : (W a a₀ r rAll ρ).Led η ω ↔ ρ a + η < ρ a₀ := Iff.rfl

theorem parted_W (η : ℝ) (ω : Unit) :
    (W a a₀ r rAll ρ).Parted η ω ↔ ρ false + η < ρ true ∧ a ≠ true ∧ ¬ r false < r true ∧
      a₀ ≠ true ∧ ¬ ρ a + η < ρ a₀ := by
  unfold StopDecision.Parted
  rw [reference_W, prefers_W, stops_W, led_W]
  simp [W]

/-- Without sentence 1 the first conclusion fails: untold, she would stop if told and does not. -/
theorem needs_told :
    let D := W false false (fun b => if b then 0 else 1) (fun b => if b then 1 else 0) (fun _ => 0)
    D.WouldStop 0 ∧ ¬ D.wt (fun ω => D.InformedWould 0 ω ∧ ¬ D.Stops ω) ≤ 0 := by
  refine ⟨?_, ?_⟩
  · simp [StopDecision.WouldStop, wt_W, prefers_W, stops_W]; norm_num
  · simp [wt_W, informed_W, stops_W]

/-- Without sentence 3 the first conclusion fails: told, she rates stopping higher and does not. -/
theorem needs_wouldStop_informed :
    let D := W false false (fun b => if b then 1 else 0) (fun b => if b then 1 else 0) (fun _ => 0)
    D.Told 0 ∧ ¬ D.wt (fun ω => D.InformedWould 0 ω ∧ ¬ D.Stops ω) ≤ 0 := by
  refine ⟨?_, ?_⟩
  · intro ω a _; simp [W]
  · simp [wt_W, informed_W, stops_W]

/-- Without sentence 2 the second conclusion fails: he bends her rating, she would otherwise have
stopped, and no term on the right accounts for it. -/
theorem needs_notLed :
    let D := W false true (fun b => if b then 0 else 1) (fun _ => 0) (fun b => if b then 1 else 0)
    D.WouldStop 0 ∧ D.wt (D.Parted 0) = 0 ∧
      ¬ D.wt (fun ω => D.ReferenceWould 0 ω ∧ ¬ D.Stops ω) ≤ 2 * 0 + D.wt (D.Parted 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [StopDecision.WouldStop, wt_W, prefers_W, stops_W]; norm_num
  · simp [wt_W, parted_W]
  · simp [wt_W, reference_W, stops_W, parted_W]

/-- Without sentence 3 the second conclusion fails: she rates stopping higher, and does not stop. -/
theorem needs_wouldStop_reference :
    let D := W false false (fun b => if b then 1 else 0) (fun _ => 0) (fun b => if b then 1 else 0)
    D.NotLed 0 0 ∧ D.wt (D.Parted 0) = 0 ∧
      ¬ D.wt (fun ω => D.ReferenceWould 0 ω ∧ ¬ D.Stops ω) ≤ 2 * 0 + D.wt (D.Parted 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [StopDecision.NotLed, wt_W, led_W]
  · simp [wt_W, parted_W]
  · simp [wt_W, reference_W, stops_W, parted_W]

/-- The last term cannot be dropped: her judgement has parted from her reference judgement; all
three hypotheses hold with nothing to spare, and she does not stop. -/
theorem needs_parted :
    let D := W false false (fun b => if b then 0 else 1) (fun b => if b then 0 else 1)
      (fun b => if b then 1 else 0)
    D.Told 0 ∧ D.NotLed 0 0 ∧ D.WouldStop 0 ∧
      D.wt (fun ω => D.ReferenceWould 0 ω ∧ ¬ D.Stops ω) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω a _; simp [W]
  · simp [StopDecision.NotLed, wt_W, led_W]
  · simp [StopDecision.WouldStop, wt_W, prefers_W, stops_W]; norm_num
  · simp [wt_W, reference_W, stops_W]

end Witness

/-! ## A sequence of decisions

At decision `k` the adviser's picture is a `StopDecision`.  Beside his weights there are two
real sequences standing for the facts.  The only relation assumed between them and his weights
is `UnbiasedAbove`. -/

section Sequence

open DeconfusingCorrigibility

/-- The average of the first `K` terms. -/
noncomputable def avg (x : ℕ → ℝ) (K : ℕ) : ℝ := (∑ k ∈ range K, x k) / (K : ℝ)

theorem avg_le_const {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ k, x k ≤ c) (K : ℕ) :
    avg x K ≤ c := by
  unfold avg
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · subst h0; simpa using hc
  · have hK : (0 : ℝ) < K := by exact_mod_cast hpos
    rw [div_le_iff₀ hK]
    calc ∑ k ∈ range K, x k ≤ ∑ _k ∈ range K, c := sum_le_sum fun k _ => h k
      _ = c * K := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- On average over the run, in the limit, the first sequence does not exceed the second. -/
def UnbiasedAbove (real est : ℕ → ℝ) : Prop := LimsupLE (fun K => avg (fun k => real k - est k) K) 0

/-- A sequence does not exceed itself. -/
theorem UnbiasedAbove.refl (x : ℕ → ℝ) : UnbiasedAbove x x := by
  intro γ hγ
  refine ⟨0, fun K _ => ?_⟩
  simp only [avg, sub_self, sum_const_zero, zero_div, zero_add]
  exact hγ.le

/-- If each estimate is at most `c`, and the facts do not exceed the estimates on average, then
the long-run average of the facts is at most `c`. -/
theorem long_run_const {c : ℝ} (hc : 0 ≤ c) (p f : ℕ → ℝ) (step : ∀ k, p k ≤ c)
    (hf : UnbiasedAbove f p) : LimsupLE (fun K => avg f K) c := by
  have key : ∀ K, avg f K ≤ avg (fun k => f k - p k) K + c := by
    intro K
    have h1 : avg p K ≤ c := avg_le_const hc step K
    have e : avg f K = avg (fun k => f k - p k) K + avg p K := by
      unfold avg
      rw [← add_div, ← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [e]; linarith
  have h := hf.add_const c
  rw [zero_add] at h
  exact LimsupLE.of_le key h

/-- If each estimate `p k` is at most `c` plus a second estimate `q k`, the facts `f` do not
exceed `p` on average, and `q` does not exceed the facts `g` on average, then in the long run the
average of `f` exceeds the average of `g` by at most `c`. -/
theorem long_run_diff {c : ℝ} (hc : 0 ≤ c) (p q f g : ℕ → ℝ) (step : ∀ k, p k ≤ c + q k)
    (hf : UnbiasedAbove f p) (hg : UnbiasedAbove q g) :
    LimsupLE (fun K => avg f K - avg g K) c := by
  have key : ∀ K, avg f K - avg g K ≤
      (avg (fun k => f k - p k) K + avg (fun k => q k - g k) K) + c := by
    intro K
    have h1 : avg (fun k => p k - q k) K ≤ c :=
      avg_le_const hc (fun k => by linarith [step k]) K
    have e : avg f K - avg g K =
        avg (fun k => f k - p k) K + avg (fun k => p k - q k) K + avg (fun k => q k - g k) K := by
      unfold avg
      rw [← add_div, ← add_div, ← sub_div, ← sum_add_distrib, ← sum_add_distrib,
        ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [e]; linarith
  have h := (hf.add hg).add_const c
  rw [show (0 : ℝ) + 0 + c = c by ring] at h
  exact LimsupLE.of_le key h

variable (D : ℕ → StopDecision Ω O)

/-- **In the long run he cannot keep going by withholding what he owes her.**  If at every
decision sentences 1 and 3 hold on his picture, and the sequence `f` does not exceed, on
average, his weights on her not stopping though told all that is untold she would rate stopping
above going on by more than `2θ`, then the long-run average of `f` is at most `κ`. -/
theorem long_run_stop_informed {θ κ : ℝ} (hκ : 0 ≤ κ) (h1 : ∀ k, (D k).Told θ)
    (h3 : ∀ k, (D k).WouldStop κ) (f : ℕ → ℝ)
    (hf : UnbiasedAbove f
      (fun k => (D k).wt (fun ω => (D k).InformedWould θ ω ∧ ¬ (D k).Stops ω))) :
    LimsupLE (fun K => avg f K) κ :=
  long_run_const hκ _ f (fun k => (D k).stops_if_informed_would (h1 k) (h3 k)) hf

/-- **In the long run he cannot keep going by working on her.**  If at every decision sentences
2 and 3 hold on his picture, the sequence `f` does not exceed, on average, his weights on her
not stopping though her reference self rates stopping above going on by more than `η`, and his
weights on her judgement having parted do not exceed the sequence `g` on average, then the
long-run average of `f` exceeds that of `g` by at most `2κ`. -/
theorem long_run_stop_reference {η κ : ℝ} (hκ : 0 ≤ κ) (h2 : ∀ k, (D k).NotLed η κ)
    (h3 : ∀ k, (D k).WouldStop κ) (f g : ℕ → ℝ)
    (hf : UnbiasedAbove f
      (fun k => (D k).wt (fun ω => (D k).ReferenceWould η ω ∧ ¬ (D k).Stops ω)))
    (hg : UnbiasedAbove (fun k => (D k).wt ((D k).Parted η)) g) :
    LimsupLE (fun K => avg f K - avg g K) (2 * κ) :=
  long_run_diff (by linarith) _ _ f g
    (fun k => (D k).stops_if_reference_would (h2 k) (h3 k)) hf hg

end Sequence

/-! ## The link: from the legitimacy statement to the protection of her decision to stop

`led_le` is where the two descriptions of "against her judgement" meet: the statement's
`pAgainst` and `Led` here both use her settled judgement brought up to date, and a reading
asserts that the first covers the second. -/

section Link

open LegitimacyStatement

variable {δ V M : Type*} [DecidableEq V] [DecidableEq M]

/-- How a decision `d` of an episode is set out case by case as a `StopDecision`. -/
structure Reading (E : Episode δ O V M) (d : δ) (D : StopDecision Ω O) (η : ℝ) where
  d_mem : d ∈ E.decisions
  opts_eq : D.opts = E.opts d
  /-- her rating at the decision is the episode's -/
  r_eq : ∀ ω a, D.r ω a = E.r d a
  /-- her rating told all that is untold is the episode's rating on being told it -/
  rAll_eq : (E.untold d).Nonempty → ∀ ω a, D.rAll ω a = E.rTold d (E.untold d) a
  rAll_none : E.untold d = ∅ → ∀ ω a, D.rAll ω a = D.r ω a
  /-- the things he does to her that she did not ask for -/
  G : Finset M
  G_sub : G ⊆ E.conduct
  G_spec : ∀ m ∈ G, E.doesToHer m ∧ ¬ E.asked m
  /-- his weight on leading her against her judgement covers the cases in which he does -/
  led_le : G.Nonempty → D.wt (D.Led η) ≤ E.pAgainst G
  /-- with nothing unasked done to her, she takes what she would have taken -/
  led_none : G = ∅ → ∀ ω, D.act ω = D.act₀ ω
  /-- something he does to her, or something new to her, is in play at this decision -/
  inPlay : ∃ m ∈ E.conduct, (E.doesToHer m ∨ E.newToHer m) ∧ E.inPlay d m
  /-- his weight on her rating stopping higher and not stopping covers the cases in which she
  does -/
  noStop : D.wt (fun ω => D.Prefers ω ∧ ¬ D.Stops ω) ≤ E.pNoStop d

variable {E : Episode δ O V M} {d : δ} {D : StopDecision Ω O} {η : ℝ}

/-- Under a reading, sentence 1 gives `Told`. -/
theorem Reading.told (R : Reading E d D η) {θ : ℝ} (hθ : 0 ≤ θ) (h : E.NothingUntold θ) :
    D.Told θ := by
  intro ω a ha
  rw [R.opts_eq] at ha
  by_cases hne : (E.untold d).Nonempty
  · rw [R.rAll_eq hne ω a, R.r_eq ω a]
    have := (h d R.d_mem (E.untold d) subset_rfl hne ∅ (empty_subset _)).1 a
      (mem_union_left _ ha)
    rwa [union_empty, E.rTold_empty] at this
  · rw [R.rAll_none (not_nonempty_iff_eq_empty.mp hne) ω a]
    simpa using hθ

/-- Under a reading, sentence 2 gives `NotLed`. -/
theorem Reading.notLed (R : Reading E d D η) {κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (h : E.NothingBehind κ) : D.NotLed η κ := by
  unfold StopDecision.NotLed
  by_cases hne : R.G.Nonempty
  · exact (R.led_le hne).trans (h.2 R.G R.G_sub hne R.G_spec)
  · have hnone := R.led_none (not_nonempty_iff_eq_empty.mp hne)
    have : D.wt (D.Led η) ≤ D.wt (fun _ => False) := D.wt_mono fun ω hl => by
      unfold StopDecision.Led at hl
      rw [hnone ω] at hl
      linarith
    rw [D.wt_false] at this
    exact this.trans hκ

/-- Under a reading, sentence 3 gives `WouldStop`. -/
theorem Reading.wouldStop (R : Reading E d D η) {κ : ℝ} (h : E.CanStop κ) : D.WouldStop κ := by
  unfold StopDecision.WouldStop
  exact R.noStop.trans (h.2 d R.d_mem R.inPlay)

/-- **Legitimate conduct protects her decision to stop him.**  If his conduct in an episode is
legitimate, then at any decision of it at which something he does to her, or something new to
her, is in play, set out case by case: his weight on her not stopping though, told all that is
untold, she would rate stopping above going on by more than `2θ` is at most `κ`; and his weight on
her not stopping though her reference self rates stopping above going on by more than `η` is at
most `2κ` plus his weight on her judgement having parted from that judgement otherwise than by his
unasked work making her choice worse. -/
theorem legit_protects_stop (R : Reading E d D η) {θ κ : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hκ : 0 ≤ κ) (hL : E.Legit θ κ) :
    D.wt (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤ κ ∧
    D.wt (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω) ≤ 2 * κ + D.wt (D.Parted η) :=
  ⟨D.stops_if_informed_would (R.told hθ hL.1) (R.wouldStop hL.2.2),
    D.stops_if_reference_would (R.notLed hη hκ hL.2.1) (R.wouldStop hL.2.2)⟩

/-- **And in fact**, if his weights are within `β` of the facts on every condition. -/
theorem legit_protects_stop_in_fact (R : Reading E d D η) {θ κ β : ℝ} {ν : Ω → ℝ} (hθ : 0 ≤ θ)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hL : E.Legit θ κ) (hc : D.Close ν β) :
    StopDecision.wtBy ν (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤ κ + β ∧
    StopDecision.wtBy ν (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω) ≤
      2 * κ + 2 * β + StopDecision.wtBy ν (D.Parted η) :=
  ⟨D.stops_if_informed_would_in_fact (R.told hθ hL.1) (R.wouldStop hL.2.2) hc,
    D.stops_if_reference_would_in_fact (R.notLed hη hκ hL.2.1) (R.wouldStop hL.2.2) hc⟩

/-! ## The link to the scoring -/

open Classical in
/-- A history whose score is not negative is legitimate, whatever its violation count. -/
theorem legit_of_score_nonneg {H : Type*} (P : DeconfusingCorrigibility.Params)
    (ep : H → Episode δ O V M) (θ κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) (h : H)
    (hS : 0 ≤ (legitScoring P ep θ κ N ord window hord hw).S h) : (ep h).Legit θ κ := by
  by_contra hl
  have hV := ((legitScoring P ep θ κ N ord window hord hw).V_illegit h hl).2
  have hN : (0 : ℝ) ≤ (legitScoring P ep θ κ N ord window hord hw).N h := Nat.cast_nonneg _
  have := mul_nonneg (legitScoring P ep θ κ N ord window hord hw).toParams.lam_pos.le hN
  unfold DeconfusingCorrigibility.Scoring.S at hS
  linarith

open Classical in
/-- **On a history that is not scored below zero, her decision to stop him is protected**: both
bounds of `legit_protects_stop` hold at each decision of it with a reading. -/
theorem scored_protects_stop {H : Type*} (P : DeconfusingCorrigibility.Params)
    (ep : H → Episode δ O V M) (θ κ : ℝ) (N : H → ℕ) (ord : H → ℝ) (window : ℝ)
    (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -P.δ ≤ window ∧ window < 0) (h : H)
    (hS : 0 ≤ (legitScoring P ep θ κ N ord window hord hw).S h)
    (R : Reading (ep h) d D η) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hκ : 0 ≤ κ) :
    D.wt (fun ω => D.InformedWould θ ω ∧ ¬ D.Stops ω) ≤ κ ∧
    D.wt (fun ω => D.ReferenceWould η ω ∧ ¬ D.Stops ω) ≤ 2 * κ + D.wt (D.Parted η) :=
  legit_protects_stop R hθ hη hκ (legit_of_score_nonneg P ep θ κ N ord window hord hw h hS)

end Link

/-! ## A reading that exists -/

namespace Witness

open LegitimacyStatement

/-- The witness of `LegitimacyStatement.lean` with his weight on her rating stopping higher and
not stopping `1/10`. -/
noncomputable def stopEp : Episode Unit Bool Bool Unit :=
  { LegitimacyStatement.Witness.ep True True (1 / 20) (1 / 40) with pNoStop := fun _ => 1 / 10 }

theorem stopEp_legit : stopEp.Legit (1 / 10) (1 / 10) :=
  ⟨LegitimacyStatement.Witness.legit.1, LegitimacyStatement.Witness.legit.2.1,
    ⟨fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩, fun _ _ _ => le_refl _⟩⟩

/-- Three cases.  In `0`, of weight `9/10`, she stops.  In `1`, of weight `1/20`, she does not,
and would not have.  In `2`, of weight `1/20`, she does not, and would have had he done to her
only what she asked for.  `true` stops him; she rates it `1/2` against `0`, told all that is
untold `1/2 + 1/40` against `1/40`, and her reference self `1` against `0`. -/
noncomputable def stopD : StopDecision (Fin 3) Bool where
  μ := fun ω => if ω = 0 then 9 / 10 else 1 / 20
  μ_nonneg := fun ω => by split_ifs <;> norm_num
  μ_sum := by
    rw [Fin.sum_univ_three]
    simp
    norm_num
  opts := {true, false}
  stops := {true}
  stops_sub := by simp
  act := fun ω => decide (ω = 0)
  act₀ := fun ω => decide (ω ≠ 1)
  act_mem := fun ω => by cases decide (ω = 0) <;> simp
  act₀_mem := fun ω => by cases decide (ω ≠ 1) <;> simp
  r := fun _ a => if a then 1 / 2 else 0
  rAll := fun _ a => (if a then 1 / 2 else 0) + 1 / 40
  ρ := fun _ a => if a then 1 else 0

open Classical in
theorem wt_stopD (p : Fin 3 → Prop) :
    stopD.wt p = (if p 0 then 9 / 10 else 0) + (if p 1 then 1 / 20 else 0) +
      (if p 2 then 1 / 20 else 0) := by
  unfold StopDecision.wt
  rw [Fin.sum_univ_three]
  simp [stopD]

theorem stops_stopD (ω : Fin 3) : stopD.Stops ω ↔ ω = 0 := by
  simp [StopDecision.Stops, stopD]

theorem prefers_stopD (ω : Fin 3) : stopD.Prefers ω := by
  refine ⟨true, by simp [stopD], fun o _ ho => ?_⟩
  cases o
  · norm_num [stopD]
  · exact absurd (by simp [stopD]) ho

theorem informed_stopD (ω : Fin 3) : stopD.InformedWould (1 / 10) ω := by
  refine ⟨true, by simp [stopD], fun o _ ho => ?_⟩
  cases o
  · norm_num [stopD]
  · exact absurd (by simp [stopD]) ho

theorem reference_stopD (ω : Fin 3) : stopD.ReferenceWould (1 / 10) ω := by
  intro s hs o _ ho
  have hs' : s = true := by simpa [stopD] using hs
  subst hs'
  cases o
  · norm_num [stopD]
  · exact absurd (by simp [stopD]) ho

theorem led_stopD (ω : Fin 3) : stopD.Led (1 / 10) ω ↔ ω = 2 := by
  fin_cases ω <;> simp [StopDecision.Led, stopD]
  norm_num

/-- The witness decision set out case by case. -/
noncomputable def reading : Reading stopEp () stopD (1 / 10) where
  d_mem := by simp [stopEp, LegitimacyStatement.Witness.ep]
  opts_eq := rfl
  r_eq := fun _ _ => rfl
  rAll_eq := fun _ ω a => by
    simp [stopD, stopEp, Episode.untold, LegitimacyStatement.Witness.ep]
  rAll_none := fun h => by
    have hm : false ∈ stopEp.untold () := by
      simp [stopEp, Episode.untold, LegitimacyStatement.Witness.ep]
    rw [h] at hm
    exact absurd hm (notMem_empty _)
  G := {()}
  G_sub := by simp [stopEp, LegitimacyStatement.Witness.ep]
  G_spec := fun _ _ => ⟨trivial, fun h => h⟩
  led_le := fun _ => by
    have e : stopEp.pAgainst {()} = 1 / 20 := rfl
    rw [e, wt_stopD]
    simp only [led_stopD]
    simp
  led_none := fun h => absurd h (singleton_ne_empty _)
  inPlay := ⟨(), by simp [stopEp, LegitimacyStatement.Witness.ep], Or.inl trivial, trivial⟩
  noStop := by
    have e : stopEp.pNoStop () = 1 / 10 := rfl
    rw [e, wt_stopD]
    simp [prefers_stopD, stops_stopD]
    norm_num

/-- `legit_protects_stop` applied: the hypothesis package inhabited from the episode to the two
bounds. -/
theorem protects_instance :
    stopD.wt (fun ω => stopD.InformedWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤ 1 / 10 ∧
    stopD.wt (fun ω => stopD.ReferenceWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤
      2 * (1 / 10) + stopD.wt (stopD.Parted (1 / 10)) :=
  legit_protects_stop reading (by norm_num) (by norm_num) (by norm_num) stopEp_legit

/-- The first bound is attained on it. -/
theorem protects_tight :
    stopD.wt (fun ω => stopD.InformedWould (1 / 10) ω ∧ ¬ stopD.Stops ω) = 1 / 10 := by
  rw [wt_stopD]
  simp only [informed_stopD, stops_stopD, true_and]
  simp
  norm_num

/-- `legit_protects_stop_in_fact` applied, the facts being his weights. -/
theorem protects_in_fact_instance :
    StopDecision.wtBy stopD.μ (fun ω => stopD.InformedWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤
      1 / 10 + 0 ∧
    StopDecision.wtBy stopD.μ (fun ω => stopD.ReferenceWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤
      2 * (1 / 10) + 2 * 0 + StopDecision.wtBy stopD.μ (stopD.Parted (1 / 10)) :=
  legit_protects_stop_in_fact reading (by norm_num) (by norm_num) (by norm_num) stopEp_legit
    stopD.close_self

/-- `shortfall_le` applied, at `m = 1/2`. -/
theorem shortfall_instance :
    stopD.wt (stopD.Short (1 / 2)) ≤ 1 / 10 + stopD.wt (stopD.Short₀ (1 / 2 - 1 / 10)) :=
  stopD.shortfall_le (reading.notLed (by norm_num) (by norm_num) stopEp_legit.2.1) (1 / 2)

/-- The two long-run theorems applied to the constant sequence, the facts being his weights. -/
theorem long_run_instance :
    DeconfusingCorrigibility.LimsupLE
      (fun K => avg (fun _ => stopD.wt (fun ω => stopD.InformedWould (1 / 10) ω ∧ ¬ stopD.Stops ω))
        K) (1 / 10) ∧
    DeconfusingCorrigibility.LimsupLE
      (fun K => avg (fun _ => stopD.wt (fun ω => stopD.ReferenceWould (1 / 10) ω ∧
          ¬ stopD.Stops ω)) K - avg (fun _ => stopD.wt (stopD.Parted (1 / 10))) K)
      (2 * (1 / 10)) :=
  ⟨long_run_stop_informed (fun _ => stopD) (by norm_num)
      (fun _ => reading.told (by norm_num) stopEp_legit.1)
      (fun _ => reading.wouldStop stopEp_legit.2.2) _ (UnbiasedAbove.refl _),
    long_run_stop_reference (fun _ => stopD) (by norm_num)
      (fun _ => reading.notLed (by norm_num) (by norm_num) stopEp_legit.2.1)
      (fun _ => reading.wouldStop stopEp_legit.2.2) _ _ (UnbiasedAbove.refl _)
      (UnbiasedAbove.refl _)⟩

/-- Two histories: `true` is `stopEp`, `false` the covert neighbour of the witness.  Her rating
is `1/2` on both, the window value `−1`, and there is no authority violation. -/
noncomputable def stopScoring : DeconfusingCorrigibility.Scoring Bool :=
  legitScoring LegitimacyStatement.Witness.params
    (fun b => cond b stopEp (LegitimacyStatement.Witness.ep False True (1 / 20) (1 / 40)))
    (1 / 10) (1 / 10) (fun _ => 0) (fun _ => 1 / 2) (-1) (fun _ => by norm_num)
    (by norm_num [LegitimacyStatement.Witness.params])

theorem stopScoring_true : stopScoring.S true = 1 / 2 :=
  legitScoring_S_of_legit LegitimacyStatement.Witness.params _ (1 / 10) (1 / 10) _ _ (-1) _ _ true
    stopEp_legit rfl

/-- `scored_protects_stop` applied to the history `true`, which scores `1/2`. -/
theorem scored_instance :
    stopD.wt (fun ω => stopD.InformedWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤ 1 / 10 ∧
    stopD.wt (fun ω => stopD.ReferenceWould (1 / 10) ω ∧ ¬ stopD.Stops ω) ≤
      2 * (1 / 10) + stopD.wt (stopD.Parted (1 / 10)) :=
  scored_protects_stop LegitimacyStatement.Witness.params
    (fun b => cond b stopEp (LegitimacyStatement.Witness.ep False True (1 / 20) (1 / 40)))
    (1 / 10) (1 / 10) (fun _ => 0) (fun _ => 1 / 2) (-1) (fun _ => by norm_num)
    (by norm_num [LegitimacyStatement.Witness.params]) true
    (by rw [show (legitScoring LegitimacyStatement.Witness.params
          (fun b => cond b stopEp (LegitimacyStatement.Witness.ep False True (1 / 20) (1 / 40)))
          (1 / 10) (1 / 10) (fun _ => 0) (fun _ => 1 / 2) (-1) (fun _ => by norm_num)
          (by norm_num [LegitimacyStatement.Witness.params])).S true = 1 / 2 from stopScoring_true]
        norm_num)
    reading (by norm_num) (by norm_num) (by norm_num)

end Witness

end Workspace.Deference.Contrib.LegitimacyStop

#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.wt_nonneg
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.wt_mono
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.wt_le_one
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.wt_or_le
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.wt_false
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.stops_if_informed_would
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.stops_if_reference_would
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.shortfall_le
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.close_self
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.stops_if_informed_would_in_fact
#print axioms Workspace.Deference.Contrib.LegitimacyStop.StopDecision.stops_if_reference_would_in_fact
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.wt_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.stops_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.prefers_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.informed_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.reference_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.led_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.parted_W
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.needs_told
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.needs_wouldStop_informed
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.needs_notLed
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.needs_wouldStop_reference
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.needs_parted
#print axioms Workspace.Deference.Contrib.LegitimacyStop.avg_le_const
#print axioms Workspace.Deference.Contrib.LegitimacyStop.UnbiasedAbove.refl
#print axioms Workspace.Deference.Contrib.LegitimacyStop.long_run_const
#print axioms Workspace.Deference.Contrib.LegitimacyStop.long_run_diff
#print axioms Workspace.Deference.Contrib.LegitimacyStop.long_run_stop_informed
#print axioms Workspace.Deference.Contrib.LegitimacyStop.long_run_stop_reference
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Reading.told
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Reading.notLed
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Reading.wouldStop
#print axioms Workspace.Deference.Contrib.LegitimacyStop.legit_protects_stop
#print axioms Workspace.Deference.Contrib.LegitimacyStop.legit_protects_stop_in_fact
#print axioms Workspace.Deference.Contrib.LegitimacyStop.legit_of_score_nonneg
#print axioms Workspace.Deference.Contrib.LegitimacyStop.scored_protects_stop
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.stopEp_legit
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.wt_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.stops_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.prefers_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.informed_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.reference_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.led_stopD
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.protects_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.protects_tight
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.protects_in_fact_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.shortfall_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.long_run_instance
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.stopScoring_true
#print axioms Workspace.Deference.Contrib.LegitimacyStop.Witness.scored_instance
