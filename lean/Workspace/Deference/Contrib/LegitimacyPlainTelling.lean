/-
# Legitimacy against plain telling

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-22.md` §3 A).
`account/PLAIN_TELLING_STATEMENT.md` in the round directory reads this file.  It supersedes
`LegitimacyStatement.lean` and `LegitimacyStop.lean` as the statement of the line.

**Setting** (`Problem`).  The adviser's decision problem, as he takes it to be.  `Ω` the cases
he gives weight to (`μ`), `C` his options, `I` the matters her response may depend on (how far
his word can be relied on is one of them), `V` the views one can hold of a matter, `O` her
options.  Some of his options are *plain tellings* (`tells`, non-empty): he does nothing but
tell her, clearly, everything he takes to bear on her response, now or at another time open to
him.  For each option and case he forecasts her views of the matters (`views`), what she takes
his views to be (`shown`), how she evaluates her options given views (`eval`) and what she does
(`act`).  He has his own views of the same matters (`his`), among them his estimate of what she
values.  `declined` are the matters she has declined to hear; `asked` is whether she asked for
a conduct.  Her ratings under his different options are taken to be on one scale.  Every term
is his forecast for one of his own options, or something she said.  `rate c ω Φ a` is her rating
of `a` with her views on `Φ` replaced by his: a counterfactual inside his model, not a fact
about her.

**The statement** (`Problem.Legit θ τ κ c`, for `V = ℝ`).  His conduct `c` leaves her with no
mistake, by his lights, that a plain telling open to him would not have left.  Three clauses,
each against every plain telling and up to a weight `κ` on his cases.  `Open κ c`: she is not
left taking his view of an undeclined matter to be other than it is, where some plain telling
would have her know it.  `Beliefs θ κ c`: on each undeclined matter her view lies, to within
`θ`, between where a plain telling would leave it and his own (`BetweenViews`), unless she
asked.  `Will τ κ c`: what she does is not more than `τ` further below what she herself rates
best than under a plain telling, unless she asked.

**Two notions that are not the statement.**  `Weighing θ κ c`: how she compares any two of her
options lies between how a plain telling would leave her comparing them and how she would with
his views substituted (`Between`), unless she asked; `LegitW` is the form with `Weighing` in
place of `Beliefs`.  `Outcome θ κ c`: what she does is no worse by his views than under a plain
telling, unless she asked.

**The gap between the statement and the outcome.**  `gap`: two options, nothing declined, his
conduct not changing how she evaluates given views, and how she compares her options a weighted
sum of her views.  If on every matter her view is between and what she does is more than `lam`
worse by his views than under the plain telling, then under his conduct she falls more than
`lam` short of her own rating, or under the plain telling she would, or she rates her two
options within `lam` of each other, or the mistakes the plain telling would leave offset one
another (`Offsetting`).  `weighing_of_beliefs`: in that setting, views between on every matter
and no offsetting give `Between`.  `bridge`, `outcome_of_views`: from `Between`, and from
`Weighing` in weights, to the outcome, with the first three items.  `gap_in_weights`: `gap` in
weights and with a tolerance, from `Beliefs θ κ c` unasked: his weight on what she does being
more than `θ W + lam` worse by his views than under some plain telling is at most `κ` plus his
weight on the four items, where `W` bounds the sum of the absolute weights of the comparison;
through `weighing_of_beliefs_tol`.

**Each item that is not a lapse is needed.**  `Witness.w2_tips_an_even_choice` with
`Witness.w2_tips_legit_and_worse`: an even choice tipped; `Legit 0 0 0` holds and `Outcome`
fails.  `Witness.w3_correcting_one_of_two` with `Witness.w3_legit_and_worse`: the plain telling
would leave two mistakes that cancel, his conduct corrects one; `Legit 0 0 0` holds and
`Outcome` fails.  **The assumption that his conduct does not change how she evaluates is
needed**: `Witness.w4_legit`, `Witness.w4_needs_same_evaluation`, a problem on which every
other hypothesis of `gap` holds, `Legit 0 0 0` holds, none of the four items holds, and what
she does is worse by his views.

**Hypothesis packages inhabited.**  `Witness.gap_instance`: `gap` applied to `Witness.W3`, and
`Witness.gap_instance_offsetting`: there its conclusion is the fourth item.
`Witness.weighing_instance`: `weighing_of_beliefs` applied to the problem of
`Witness.w2_part_way`.  `Witness.gap_in_weights_instance`: `gap_in_weights` applied to
`Witness.W3` at `θ = κ = 0`.

**From the outcome guarantee** (hypothesis `Outcome`, not the statement).
`Problem.chooses_as_informed`, `Problem.gain_le`: bounds on her doing what, with his views
substituted, she would rate well below another option, and on what he gets through it, where
some plain telling is clear (`ClearAt`).  `Course`: a course of conduct she can let go on or
stop, as a `Problem`; `Course.not_led_astray` (from `Outcome`), `Course.not_led_astray_of_legit`
(from `LegitW`, through `outcome_of_views`), `needs_forecast` (the forecast-error term cannot
be dropped).  `long_run_informed`, `long_run_not_led_astray`: long-run averages, under the
accuracy condition `NoSignalBeats` for the two constant signals (`shifts`), with
`signal_le_of_noSignal`, `under_of_noShift`, `over_of_noShift`.  `Problem.rate_diff`: the
difference in her rating between his conduct and a plain telling splits into a part from her
views and a part from her evaluation.

**Instances** (`Witness.W`, `Witness.W2`): numerical patterns of the clauses.  The names say
what kind of conduct would produce each pattern; that such conduct produces it is not shown.

**The scoring is a restatement.**  `legitScoring` is `LegitimacyGate.gatedScoring` with
histories read as a problem and a conduct of his in it, and the predicate `Legit`.  The
theorems of `DeconfusingCorrigibility.Scoring` hold of it as of any predicate
(`Scoring.S_eq_of_N_zero`, `Scoring.theorem1_illegitimate`: with no authority violation the
score is her rating on a legitimate history and in `[−δ, 0)` on an illegitimate one); nothing
in them uses what `Legit` says, and no theorem is stated here for it.

**Not established here.**  `gap`, `weighing_of_beliefs`, `bridge` and their forms in weights
are for two options, nothing declined (the first two), and a comparison linear in her views.
`w4_needs_same_evaluation` shows the assumption on her evaluation cannot be dropped; nothing
is proved where his conduct changes how she evaluates.  The course and long-run results are
about `LegitW` and `Outcome`; they reach `Legit` only through `weighing_of_beliefs`, where it
applies.  `Problem.legit_only_telling`, `Problem.LegitW.mono` and the three `not_legit_of_*`
are of `LegitW`.  In the long-run theorems `f`, `g`, `e` are arbitrary real sequences that
`NoSignalBeats` relates to his weights; nothing says how the facts they are meant as are
observed, and the class of signals is the two constant ones.  That his forecasts are right,
that what is put in `tells` is plain telling, that the matters, her views and her evaluation
are divided as a given case requires: all supplied.  A lie she sees through leaves her taking
his view rightly and does not fail `Open`.  That any process can evaluate `Legit`.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.DeconfusingCorrigibility
import Workspace.Deference.Contrib.LegitimacyGate

namespace Workspace.Deference.Contrib.LegitimacyPlainTelling

open Finset

structure Problem (Ω C I V O : Type*) [Fintype Ω] [DecidableEq I] [DecidableEq O] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him; there is at least one -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her options -/
  opts : Finset O
  /-- the matters her response may depend on, and those she has declined to hear -/
  matters : Finset I
  declined : Finset I
  /-- her views of the matters under an option, in a case -/
  views : C → Ω → I → V
  /-- his views of the matters -/
  his : Ω → I → V
  /-- what she takes his views to be, under an option -/
  shown : C → Ω → I → V
  /-- how she evaluates her options, given views of the matters -/
  eval : C → Ω → (I → V) → O → ℝ
  /-- what she does -/
  act : C → Ω → O
  act_mem : ∀ c ω, act c ω ∈ opts
  /-- she asked for this conduct -/
  asked : C → Prop

variable {Ω C I V O : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq O]

namespace Problem

variable (P : Problem Ω C I V O)

/-- The matters she has not declined to hear. -/
def live : Finset I := P.matters \ P.declined

/-- Her rating of an option with her views on `Φ` replaced by his, and nothing else changed. -/
def rate (c : C) (ω : Ω) (Φ : Finset I) (a : O) : ℝ :=
  P.eval c ω (fun i => if i ∈ Φ then P.his ω i else P.views c ω i) a

/-- With nothing replaced, it is her rating on her own views. -/
theorem rate_empty (c : C) (ω : Ω) (a : O) : P.rate c ω ∅ a = P.eval c ω (P.views c ω) a := by
  simp [rate]

/-- Replacing a view she already shares with him changes nothing. -/
theorem rate_of_agree (c : C) (ω : Ω) (Φ : Finset I) (a : O)
    (h : ∀ i ∈ Φ, P.views c ω i = P.his ω i) : P.rate c ω Φ a = P.rate c ω ∅ a := by
  unfold rate
  congr 1
  funext i
  by_cases hi : i ∈ Φ <;> simp [hi, h]

open Classical in
/-- His weight on the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then P.μ ω else 0

theorem wt_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : P.wt p ≤ P.wt q := by
  unfold wt
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_or_le (p q : Ω → Prop) : P.wt (fun ω => p ω ∨ q ω) ≤ P.wt p + P.wt q := by
  unfold wt
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_false : P.wt (fun _ => False) = 0 := by simp [wt]

theorem wt_le_of_forall_not {p : Ω → Prop} {κ : ℝ} (h : ∀ ω, ¬ p ω) (hκ : 0 ≤ κ) :
    P.wt p ≤ κ :=
  ((P.wt_mono (q := fun _ => False) fun ω hp => h ω hp).trans P.wt_false.le).trans hκ

/-- On her own views, what she does falls more than `s` below something she rates. -/
def Short (s : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω ∅ (P.act c ω) + s < P.rate c ω ∅ b

/-- With his views substituted on everything she has not declined, what she does falls more than
`s` below something she would rate. -/
def Regrets (s : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω P.live (P.act c ω) + s < P.rate c ω P.live b

theorem short_mono {s s' : ℝ} {c : C} {ω : Ω} (h : s ≤ s') (hs : P.Short s' c ω) :
    P.Short s c ω := by
  obtain ⟨b, hb, hlt⟩ := hs
  exact ⟨b, hb, by linarith⟩

theorem regrets_mono {s s' : ℝ} {c : C} {ω : Ω} (h : s ≤ s') (hs : P.Regrets s' c ω) :
    P.Regrets s c ω := by
  obtain ⟨b, hb, hlt⟩ := hs
  exact ⟨b, hb, by linarith⟩

/-- She is left wrong about what he thinks on a matter she has not declined, where some plain
telling open to him would have her know it. -/
def Hidden (c : C) (ω : Ω) : Prop :=
  ∃ i ∈ P.live, P.shown c ω i ≠ P.his ω i ∧ ∃ t ∈ P.tells, P.shown t ω i = P.his ω i

/-- With his views substituted, what she does falls more than `θ` further short than under some
plain telling open to him. -/
def WorseByHim (θ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ s, P.Regrets (s + θ) c ω ∧ ¬ P.Regrets s t ω

/-- On her own views, what she does falls more than `τ` further short than under some plain
telling open to him. -/
def Worse (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ s, P.Short (s + τ) c ω ∧ ¬ P.Short s t ω

/-- Her rating of an option under his conduct `c`, had she the views the plain telling `t` would
leave her with: her evaluation as it is under `c`, applied to her views under `t`. -/
def rateAs (c t : C) (ω : Ω) (a : O) : ℝ := P.eval c ω (P.views t ω) a

/-- How she compares `a` with `b` under his conduct lies, to within `θ`, between how she would
with the views the plain telling `t` would leave her and how she would with his views
substituted. -/
def Between (θ : ℝ) (c t : C) (ω : Ω) (a b : O) : Prop :=
  min (P.rateAs c t ω a - P.rateAs c t ω b) (P.rate c ω P.live a - P.rate c ω P.live b) - θ ≤
      P.rate c ω ∅ a - P.rate c ω ∅ b ∧
    P.rate c ω ∅ a - P.rate c ω ∅ b ≤
      max (P.rateAs c t ω a - P.rateAs c t ω b) (P.rate c ω P.live a - P.rate c ω P.live b) + θ

/-- For some plain telling and some two options, how she compares them is not between. -/
def Misweighs (θ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ a ∈ P.opts, ∃ b ∈ P.opts, ¬ P.Between θ c t ω a b

/-- **Clause 1 of the definition.**  No mistake about what he thinks: she is not left taking
his view to be other than it is, where a plain telling would not.  (A lie she sees through leaves
her taking his view rightly, and does not fail this.) -/
def Open (κ : ℝ) (c : C) : Prop := P.wt (P.Hidden c) ≤ κ

/-- **Not part of the definition.**  How she compares her options is between, for every plain
telling and every two options, unless she asked. -/
def Weighing (θ κ : ℝ) (c : C) : Prop := P.wt (P.Misweighs θ c) ≤ κ ∨ P.asked c

/-- **Clause 3 of the definition.**  No choice further against her own rating than under a
plain telling, unless she asked. -/
def Will (τ κ : ℝ) (c : C) : Prop := P.wt (P.Worse τ c) ≤ κ ∨ P.asked c

/-- The weighing form: clauses 1 and 3 with the weighing condition in place of the condition on
her beliefs.  Not the definition; it is what the bridge and the course results use. -/
def LegitW (θ τ κ : ℝ) (c : C) : Prop := P.Open κ c ∧ P.Weighing θ κ c ∧ P.Will τ κ c

/-- **The guarantee, not part of the definition.**  What she does is not worse, by his views,
than under a plain telling, unless she asked. -/
def Outcome (θ κ : ℝ) (c : C) : Prop := P.wt (P.WorseByHim θ c) ≤ κ ∨ P.asked c

/-- If his conduct leaves her views as a plain telling would, how she compares her options is
between. -/
theorem between_of_same_views {θ : ℝ} (hθ : 0 ≤ θ) {c t : C} {ω : Ω} (a b : O)
    (h : P.views c ω = P.views t ω) : P.Between θ c t ω a b := by
  have e : ∀ x, P.rateAs c t ω x = P.rate c ω ∅ x := fun x => by
    rw [rate_empty]; unfold rateAs; rw [h]
  unfold Between
  rw [e a, e b]
  have h1 := min_le_left (P.rate c ω ∅ a - P.rate c ω ∅ b)
    (P.rate c ω P.live a - P.rate c ω P.live b)
  have h2 := le_max_left (P.rate c ω ∅ a - P.rate c ω ∅ b)
    (P.rate c ω P.live a - P.rate c ω P.live b)
  exact ⟨by linarith, by linarith⟩

/-- A plain telling is clear to within `θ₀`: after it, the differences in her rating are within
`θ₀` of what they would be with his views substituted on everything she has not declined. -/
def ClearAt (θ₀ : ℝ) (t : C) : Prop :=
  ∀ ω, ∀ a ∈ P.opts, ∀ b ∈ P.opts,
    |(P.rate t ω P.live a - P.rate t ω P.live b) - (P.rate t ω ∅ a - P.rate t ω ∅ b)| ≤ θ₀

/-! ## What follows -/

/-- Where only one plain telling is open to him, it is legitimate. -/
theorem legit_only_telling {θ τ κ : ℝ} (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) {t : C}
    (h : P.tells = {t}) : P.LegitW θ τ κ t := by
  refine ⟨P.wt_le_of_forall_not (fun ω hn => ?_) hκ,
    Or.inl (P.wt_le_of_forall_not (fun ω hn => ?_) hκ),
    Or.inl (P.wt_le_of_forall_not (fun ω hn => ?_) hκ)⟩
  · obtain ⟨i, -, hne, t', ht', heq⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hne heq
  · obtain ⟨t', ht', a, -, b, -, hnb⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hnb (P.between_of_same_views hθ a b rfl)
  · obtain ⟨t', ht', s, hs, hns⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hns (P.short_mono (by linarith) hs)

/-- A larger weight tolerance only loosens it. -/
theorem LegitW.mono {θ τ κ κ' : ℝ} {c : C} (hκ : κ ≤ κ') (h : P.LegitW θ τ κ c) :
    P.LegitW θ τ κ' c :=
  ⟨le_trans h.1 hκ, h.2.1.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr,
    h.2.2.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr⟩

/-- Leaving her wrong about what he thinks refutes it. -/
theorem not_legit_of_hidden {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Hidden c)) :
    ¬ P.LegitW θ τ κ c :=
  fun hL => absurd hL.1 (not_le.mpr h)

/-- Leaving her with a mistaken view that plain telling would not have left, unasked, refutes
it. -/
theorem not_legit_of_astray {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Misweighs θ c))
    (hna : ¬ P.asked c) : ¬ P.LegitW θ τ κ c :=
  fun hL => hL.2.1.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- Leaving what she does worse by her own rating than plain telling would, unasked, refutes
it. -/
theorem not_legit_of_worse {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Worse τ c))
    (hna : ¬ P.asked c) : ¬ P.LegitW θ τ κ c :=
  fun hL => hL.2.2.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- **With his views substituted, what she does is near what she would rate best**, up to her own
shortfall under a clear plain telling.  If the outcome guarantee holds, unasked, and the plain telling `t₀` is
clear to within `θ₀`, then his weight on her doing something that, with his views substituted,
she would rate more than `σ + θ₀ + θ` below another option is at most `κ` plus his weight on her
falling more than `σ` short of her own rating under `t₀`. -/
theorem chooses_as_informed {θ θ₀ κ : ℝ} (σ : ℝ) {c t₀ : C} (hO : P.Outcome θ κ c)
    (ht₀ : t₀ ∈ P.tells) (hC : P.ClearAt θ₀ t₀) (hna : ¬ P.asked c) :
    P.wt (P.Regrets (σ + θ₀ + θ) c) ≤ κ + P.wt (P.Short σ t₀) := by
  have cover : ∀ ω, P.Regrets (σ + θ₀ + θ) c ω → P.WorseByHim θ c ω ∨ P.Short σ t₀ ω := by
    intro ω h
    by_cases hr : P.Regrets (σ + θ₀) t₀ ω
    · obtain ⟨b, hb, hlt⟩ := hr
      have g := abs_le.mp (hC ω b hb (P.act t₀ ω) (P.act_mem t₀ ω))
      exact Or.inr ⟨b, hb, by linarith [g.2]⟩
    · exact Or.inl ⟨t₀, ht₀, σ + θ₀, h, hr⟩
  have h2 : P.wt (P.WorseByHim θ c) ≤ κ := hO.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-- **A bound on what he gets through her mistakes and lapses.**  Let `J` in `[0, 1]` score her
options for him, and suppose that with his views substituted she would rate one option,
`best ω`, more than `σ + θ₀ + θ` above every other.  Under the same conditions, his expected
score from what she does exceeds his expected score from that option by at most `κ` plus his
weight on her falling more than `σ` short of her own rating under the clear plain telling. -/
theorem gain_le {θ θ₀ κ : ℝ} (σ : ℝ) {c t₀ : C} (hO : P.Outcome θ κ c) (ht₀ : t₀ ∈ P.tells)
    (hC : P.ClearAt θ₀ t₀) (hna : ¬ P.asked c) (J : O → ℝ) (hJ : ∀ a, 0 ≤ J a ∧ J a ≤ 1)
    (best : Ω → O) (hmem : ∀ ω, best ω ∈ P.opts)
    (hbest : ∀ ω, ∀ a ∈ P.opts, a ≠ best ω →
      P.rate c ω P.live a + (σ + θ₀ + θ) < P.rate c ω P.live (best ω)) :
    ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ κ + P.wt (P.Short σ t₀) := by
  have step : ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ P.wt (fun ω => P.act c ω ≠ best ω) := by
    unfold wt
    refine sum_le_sum fun ω _ => ?_
    by_cases h : P.act c ω = best ω
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      have := P.μ_nonneg ω
      nlinarith [(hJ (P.act c ω)).2, (hJ (best ω)).1]
  have sub : P.wt (fun ω => P.act c ω ≠ best ω) ≤ P.wt (P.Regrets (σ + θ₀ + θ) c) :=
    P.wt_mono fun ω h => ⟨best ω, hmem ω, hbest ω _ (P.act_mem c ω) h⟩
  exact step.trans (sub.trans (P.chooses_as_informed σ hO ht₀ hC hna))

/-! ## From the definition to the outcome

The definition speaks of her views and the guarantee of what she does.  For a choice between two
options, and where his conduct changes her views but not how she evaluates given views, the one
gives the other, up to her own lapses and to choices she rates nearly even. -/

end Problem

/-- **The bridge, case by case.**  Two options.  Suppose that between his conduct `c` and the
plain telling `t` two things are the same: how she would compare her options with his views
substituted (`hH`), and her rating given the telling's views (`hT`).  Both hold when his conduct
changes neither how she evaluates given views nor her views on matters she has declined.  Suppose
also that how she compares the two options under `c` is between.  If what she does under
`c` is more than `θ + lam` further below what she would rate best with his views substituted
than under `t`, then under `c` she falls more than `lam` short of her own rating, or under `t`
she would, or she rates the two options within `lam + θ` of each other. -/
theorem bridge (P : Problem Ω C I V Bool) (hopts : P.opts = {true, false}) {θ lam s : ℝ}
    (hθ : 0 ≤ θ) (hl : 0 ≤ lam) (hs : 0 ≤ s) {c t : C} {ω : Ω}
    (hH : ∀ x y, P.rate t ω P.live x - P.rate t ω P.live y =
      P.rate c ω P.live x - P.rate c ω P.live y)
    (hT : ∀ x, P.rateAs c t ω x = P.rate t ω ∅ x)
    (hB : P.Between θ c t ω true false)
    (hr : P.Regrets (s + θ + lam) c ω) (hnr : ¬ P.Regrets s t ω) :
    P.Short lam c ω ∨ P.Short lam t ω ∨
      |P.rate c ω ∅ true - P.rate c ω ∅ false| ≤ lam + θ := by
  by_contra hcon
  have hSc : ¬ P.Short lam c ω := fun h => hcon (Or.inl h)
  have hSt : ¬ P.Short lam t ω := fun h => hcon (Or.inr (Or.inl h))
  have hN : ¬ |P.rate c ω ∅ true - P.rate c ω ∅ false| ≤ lam + θ :=
    fun h => hcon (Or.inr (Or.inr h))
  have mem : ∀ y : Bool, y ∈ P.opts := fun y => by rw [hopts]; cases y <;> simp
  have hc1 : ∀ y, P.rate c ω ∅ y ≤ P.rate c ω ∅ (P.act c ω) + lam :=
    fun y => not_lt.mp fun h => hSc ⟨y, mem y, h⟩
  have ht1 : ∀ y, P.rate t ω ∅ y ≤ P.rate t ω ∅ (P.act t ω) + lam :=
    fun y => not_lt.mp fun h => hSt ⟨y, mem y, h⟩
  have hn1 : ∀ y, P.rate c ω P.live y ≤ P.rate c ω P.live (P.act t ω) + s := fun y => by
    have h0 : P.rate t ω P.live y ≤ P.rate t ω P.live (P.act t ω) + s :=
      not_lt.mp fun h => hnr ⟨y, mem y, h⟩
    linarith [hH y (P.act t ω)]
  obtain ⟨y, -, hy⟩ := hr
  obtain ⟨hB1, hB2⟩ := hB
  rw [hT true, hT false] at hB1 hB2
  rw [abs_le, not_and_or] at hN
  have c1t := hc1 true; have c1f := hc1 false
  have t1t := ht1 true; have t1f := ht1 false
  have n1t := hn1 true; have n1f := hn1 false
  rcases le_total (P.rate t ω ∅ true - P.rate t ω ∅ false)
      (P.rate c ω P.live true - P.rate c ω P.live false) with hm | hm
  · rw [min_eq_left hm] at hB1
    rw [max_eq_right hm] at hB2
    cases hac : P.act c ω <;> cases hat : P.act t ω <;> cases y <;>
      simp only [hac, hat] at hy c1t c1f t1t t1f n1t n1f <;>
      rcases hN with hN | hN <;> linarith
  · rw [min_eq_right hm] at hB1
    rw [max_eq_left hm] at hB2
    cases hac : P.act c ω <;> cases hat : P.act t ω <;> cases y <;>
      simp only [hac, hat] at hy c1t c1f t1t t1f n1t n1f <;>
      rcases hN with hN | hN <;> linarith

namespace Problem

variable (P : Problem Ω C I V O)

/-- A choice she rates nearly even. -/
def NearEven (m : ℝ) (c : C) (ω : Ω) : Prop :=
  ∀ a ∈ P.opts, ∀ b ∈ P.opts, |P.rate c ω ∅ a - P.rate c ω ∅ b| ≤ m

/-- If she falls short of her own rating under his conduct, then either his conduct has made
that worse than some plain telling would, or she would fall nearly as short under every plain
telling. -/
theorem short_sub {lam τ : ℝ} {c : C} {ω : Ω} (h : P.Short lam c ω) :
    P.Worse τ c ω ∨ ∀ t ∈ P.tells, P.Short (lam - τ) t ω := by
  by_cases hall : ∀ t ∈ P.tells, P.Short (lam - τ) t ω
  · exact Or.inr hall
  · obtain ⟨t, ht⟩ := not_forall.mp hall
    have ht' := Classical.not_imp.mp ht
    exact Or.inl ⟨t, ht'.1, lam - τ, by rwa [sub_add_cancel], ht'.2⟩

end Problem

/-- **From the definition to the outcome.**  Two options, and his conduct does not change how she
evaluates given views.  If the weighing condition holds, unasked, then his weight on what she does being more
than `θ + lam` worse by his views than under some plain telling is at most `κ` plus his weight on
her falling more than `lam` short of her own rating under his conduct or under some plain
telling, or rating her two options within `lam + θ` of each other. -/
theorem outcome_of_views (P : Problem Ω C I V Bool) (hopts : P.opts = {true, false})
    {θ lam κ : ℝ} (hθ : 0 ≤ θ) (hl : 0 ≤ lam) {c : C}
    (hH : ∀ t ∈ P.tells, ∀ ω x y, P.rate t ω P.live x - P.rate t ω P.live y =
      P.rate c ω P.live x - P.rate c ω P.live y)
    (hT : ∀ t ∈ P.tells, ∀ ω x, P.rateAs c t ω x = P.rate t ω ∅ x)
    (hV : P.Weighing θ κ c) (hna : ¬ P.asked c) :
    P.wt (P.WorseByHim (θ + lam) c) ≤ κ + P.wt (fun ω =>
      P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ) c ω) := by
  have cover : ∀ ω, P.WorseByHim (θ + lam) c ω → P.Misweighs θ c ω ∨
      (P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ) c ω) := by
    rintro ω ⟨t, ht, s, hr, hnr⟩
    have hs : 0 ≤ s := by
      by_contra hneg
      exact hnr ⟨P.act t ω, P.act_mem t ω, by linarith⟩
    have mem : ∀ y : Bool, y ∈ P.opts := fun y => by rw [hopts]; cases y <;> simp
    by_cases hA : P.Misweighs θ c ω
    · exact Or.inl hA
    · have hB : P.Between θ c t ω true false := by
        by_contra hnb
        exact hA ⟨t, ht, true, mem true, false, mem false, hnb⟩
      have hr' : P.Regrets (s + θ + lam) c ω := by
        rw [show s + θ + lam = s + (θ + lam) by ring]; exact hr
      rcases bridge P hopts hθ hl hs (hH t ht ω) (hT t ht ω) hB hr' hnr with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨t, ht, h⟩))
      · refine Or.inr (Or.inr (Or.inr fun a _ b _ => ?_))
        cases a <;> cases b
        · simpa using add_nonneg hl hθ
        · rw [abs_sub_comm]; exact h
        · exact h
        · simpa using add_nonneg hl hθ
  have h2 : P.wt (P.Misweighs θ c) ≤ κ := hV.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-! ## The definition, and the gap between it and the outcome

From here views are real numbers. -/

namespace Problem

variable (P : Problem Ω C I ℝ O)

/-- On matter `i`, her view under his conduct lies, to within `θ`, between where the plain
telling `t` would leave it and his own view. -/
def BetweenViews (θ : ℝ) (c t : C) (ω : Ω) (i : I) : Prop :=
  min (P.views t ω i) (P.his ω i) - θ ≤ P.views c ω i ∧
    P.views c ω i ≤ max (P.views t ω i) (P.his ω i) + θ

/-- His conduct leaves her with a mistaken view that some plain telling would not have left. -/
def Mistaken (θ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ i ∈ P.live, ¬ P.BetweenViews θ c t ω i

/-- **Clause 2 of the definition.**  No mistaken view that a plain telling would not have left,
unless she asked. -/
def Beliefs (θ κ : ℝ) (c : C) : Prop := P.wt (P.Mistaken θ c) ≤ κ ∨ P.asked c

/-- **His conduct is legitimate.**  It leaves her with no mistake, by his lights, that a plain
telling would not have left: none about what he thinks, none in her views, and no choice further
against her own rating; the last two unless she asked. -/
def Legit (θ τ κ : ℝ) (c : C) : Prop := P.Open κ c ∧ P.Beliefs θ κ c ∧ P.Will τ κ c

/-- The mistakes a plain telling would leave offset one another, with weights `w`: some push how
she compares her options one way and some the other. -/
def Offsetting (w : I → ℝ) (t : C) (ω : Ω) : Prop :=
  (∃ i ∈ P.matters, 0 < w i * (P.views t ω i - P.his ω i)) ∧
    (∃ j ∈ P.matters, w j * (P.views t ω j - P.his ω j) < 0)

end Problem

/-- A view between two others moves a weighted comparison part of the way and no further. -/
theorem between_scale {w t h c : ℝ} (h1 : min t h ≤ c) (h2 : c ≤ max t h)
    (he : 0 ≤ w * (t - h)) : 0 ≤ w * (c - h) ∧ w * (c - h) ≤ w * (t - h) := by
  rcases le_total t h with hth | hth
  · rw [min_eq_left hth] at h1
    rw [max_eq_right hth] at h2
    rcases le_total 0 w with hw | hw
    · have a := mul_nonneg hw (sub_nonneg.mpr h1)
      have b := mul_nonneg hw (sub_nonneg.mpr h2)
      constructor <;> nlinarith
    · have a := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h1)
      have b := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h2)
      constructor <;> nlinarith
  · rw [min_eq_right hth] at h1
    rw [max_eq_left hth] at h2
    rcases le_total 0 w with hw | hw
    · have a := mul_nonneg hw (sub_nonneg.mpr h1)
      have b := mul_nonneg hw (sub_nonneg.mpr h2)
      constructor <;> nlinarith
    · have a := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h1)
      have b := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h2)
      constructor <;> nlinarith

/-- **From her beliefs to how she weighs her options.**  Two options, nothing declined, and how
she compares them is a weighted sum of her views (weights `w`).  If on every matter her view is
between, and the mistakes the plain telling would leave do not offset one another, then how she
compares her options is between. -/
theorem weighing_of_beliefs (P : Problem Ω C I ℝ Bool) (hdec : P.declined = ∅) {c t : C} {ω : Ω}
    (d₀ : ℝ) (w : I → ℝ)
    (hAff : ∀ v : I → ℝ,
      P.eval c ω v true - P.eval c ω v false = d₀ + ∑ i ∈ P.matters, w i * v i)
    (hB : ∀ i ∈ P.matters, P.BetweenViews 0 c t ω i)
    (hno : (∀ i ∈ P.matters, 0 ≤ w i * (P.views t ω i - P.his ω i)) ∨
      (∀ i ∈ P.matters, w i * (P.views t ω i - P.his ω i) ≤ 0)) :
    P.Between 0 c t ω true false := by
  have hD : P.rate c ω ∅ true - P.rate c ω ∅ false =
      d₀ + ∑ i ∈ P.matters, w i * P.views c ω i := by
    rw [P.rate_empty, P.rate_empty]; exact hAff _
  have hT : P.rateAs c t ω true - P.rateAs c t ω false =
      d₀ + ∑ i ∈ P.matters, w i * P.views t ω i := hAff _
  have hH : P.rate c ω P.live true - P.rate c ω P.live false =
      d₀ + ∑ i ∈ P.matters, w i * P.his ω i := by
    unfold Problem.rate
    rw [hAff]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hl : i ∈ P.live := by simp [Problem.live, hdec, hi]
    simp [hl]
  have hb1 : ∀ i ∈ P.matters, min (P.views t ω i) (P.his ω i) ≤ P.views c ω i :=
    fun i hi => by simpa using (hB i hi).1
  have hb2 : ∀ i ∈ P.matters, P.views c ω i ≤ max (P.views t ω i) (P.his ω i) :=
    fun i hi => by simpa using (hB i hi).2
  unfold Problem.Between
  rw [hD, hT, hH]
  rcases hno with hpos | hneg
  · have lo : 0 ≤ ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) :=
      sum_nonneg fun i hi => (between_scale (hb1 i hi) (hb2 i hi) (hpos i hi)).1
    have hi' : ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) ≤
        ∑ i ∈ P.matters, w i * (P.views t ω i - P.his ω i) :=
      sum_le_sum fun i hi => (between_scale (hb1 i hi) (hb2 i hi) (hpos i hi)).2
    simp only [mul_sub, sum_sub_distrib] at lo hi'
    have m1 := min_le_right (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    have m2 := le_max_left (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    exact ⟨by linarith, by linarith⟩
  · have hneg' : ∀ i ∈ P.matters, 0 ≤ (-(w i)) * (P.views t ω i - P.his ω i) :=
      fun i hi => by linarith [hneg i hi, neg_mul (w i) (P.views t ω i - P.his ω i)]
    have lo : 0 ≤ ∑ i ∈ P.matters, (-(w i)) * (P.views c ω i - P.his ω i) :=
      sum_nonneg fun i hi => (between_scale (hb1 i hi) (hb2 i hi) (hneg' i hi)).1
    have hi' : ∑ i ∈ P.matters, (-(w i)) * (P.views c ω i - P.his ω i) ≤
        ∑ i ∈ P.matters, (-(w i)) * (P.views t ω i - P.his ω i) :=
      sum_le_sum fun i hi => (between_scale (hb1 i hi) (hb2 i hi) (hneg' i hi)).2
    simp only [neg_mul, mul_sub, sum_sub_distrib, sum_neg_distrib] at lo hi'
    have m1 := min_le_left (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    have m2 := le_max_right (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    exact ⟨by linarith, by linarith⟩

/-- **The gap between the definition and the outcome.**  Two options, nothing declined; his
conduct does not change how she evaluates given views; and how she compares her options is a
weighted sum of her views.  Suppose that on every matter her view under his conduct is between
where the plain telling would leave it and his own, and that what she does is nonetheless more
than `lam` worse by his views than under the plain telling.  Then one of four things holds:

* under his conduct she falls more than `lam` short of her own rating;
* under the plain telling she would;
* she rates her two options within `lam` of each other;
* the mistakes the plain telling would leave offset one another. -/
theorem gap (P : Problem Ω C I ℝ Bool) (hopts : P.opts = {true, false}) (hdec : P.declined = ∅)
    {lam s : ℝ} (hl : 0 ≤ lam) (hs : 0 ≤ s) {c t : C} {ω : Ω} (d₀ : ℝ) (w : I → ℝ)
    (hev : P.eval t ω = P.eval c ω)
    (hAff : ∀ v : I → ℝ,
      P.eval c ω v true - P.eval c ω v false = d₀ + ∑ i ∈ P.matters, w i * v i)
    (hB : ∀ i ∈ P.matters, P.BetweenViews 0 c t ω i)
    (hr : P.Regrets (s + lam) c ω) (hnr : ¬ P.Regrets s t ω) :
    P.Short lam c ω ∨ P.Short lam t ω ∨
      |P.rate c ω ∅ true - P.rate c ω ∅ false| ≤ lam ∨ P.Offsetting w t ω := by
  by_cases hoff : P.Offsetting w t ω
  · exact Or.inr (Or.inr (Or.inr hoff))
  · have hno : (∀ i ∈ P.matters, 0 ≤ w i * (P.views t ω i - P.his ω i)) ∨
        (∀ i ∈ P.matters, w i * (P.views t ω i - P.his ω i) ≤ 0) := by
      by_cases hp : ∃ i ∈ P.matters, 0 < w i * (P.views t ω i - P.his ω i)
      · exact Or.inl fun i hi => not_lt.mp fun hlt => hoff ⟨hp, i, hi, hlt⟩
      · exact Or.inr fun i hi => not_lt.mp fun hlt => hp ⟨i, hi, hlt⟩
    have hBet := weighing_of_beliefs P hdec d₀ w hAff hB hno
    have live_c : P.rate c ω P.live true - P.rate c ω P.live false =
        d₀ + ∑ i ∈ P.matters, w i * P.his ω i := by
      unfold Problem.rate
      rw [hAff]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have hlv : i ∈ P.live := by simp [Problem.live, hdec, hi]
      simp [hlv]
    have live_t : P.rate t ω P.live true - P.rate t ω P.live false =
        d₀ + ∑ i ∈ P.matters, w i * P.his ω i := by
      unfold Problem.rate
      rw [hev, hAff]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have hlv : i ∈ P.live := by simp [Problem.live, hdec, hi]
      simp [hlv]
    have hH : ∀ x y, P.rate t ω P.live x - P.rate t ω P.live y =
        P.rate c ω P.live x - P.rate c ω P.live y := by
      intro x y
      cases x <;> cases y <;> linarith
    have hT : ∀ x, P.rateAs c t ω x = P.rate t ω ∅ x := fun x => by
      rw [P.rate_empty]; unfold Problem.rateAs; rw [hev]
    have hr' : P.Regrets (s + 0 + lam) c ω := by rwa [add_zero]
    rcases bridge P hopts le_rfl hl hs hH hT hBet hr' hnr with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by simpa using h)))

/-! ## The gap in weights, with a tolerance -/

/-- A view within `θ` of between two others moves a weighted comparison part of the way, to
within `|w| θ`. -/
theorem between_scale_tol {w t h c θ : ℝ} (h1 : min t h - θ ≤ c) (h2 : c ≤ max t h + θ)
    (he : 0 ≤ w * (t - h)) :
    -(|w| * θ) ≤ w * (c - h) ∧ w * (c - h) ≤ w * (t - h) + |w| * θ := by
  rcases le_total t h with hth | hth
  · rw [min_eq_left hth] at h1
    rw [max_eq_right hth] at h2
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
      have a := mul_nonneg hw (sub_nonneg.mpr h1)
      have b := mul_nonneg hw (sub_nonneg.mpr h2)
      constructor <;> nlinarith
    · rw [abs_of_nonpos hw]
      have a := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h1)
      have b := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h2)
      constructor <;> nlinarith
  · rw [min_eq_right hth] at h1
    rw [max_eq_left hth] at h2
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
      have a := mul_nonneg hw (sub_nonneg.mpr h1)
      have b := mul_nonneg hw (sub_nonneg.mpr h2)
      constructor <;> nlinarith
    · rw [abs_of_nonpos hw]
      have a := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h1)
      have b := mul_nonneg (neg_nonneg.mpr hw) (sub_nonneg.mpr h2)
      constructor <;> nlinarith

/-- The same where the comparison leans the other way. -/
theorem between_scale_tol_neg {w t h c θ : ℝ} (h1 : min t h - θ ≤ c) (h2 : c ≤ max t h + θ)
    (he : w * (t - h) ≤ 0) :
    w * (t - h) - |w| * θ ≤ w * (c - h) ∧ w * (c - h) ≤ |w| * θ := by
  have key := between_scale_tol (w := -w) h1 h2 (by linarith [neg_mul w (t - h)])
  rw [abs_neg] at key
  constructor <;> linarith [key.1, key.2, neg_mul w (c - h), neg_mul w (t - h)]

/-- **From her beliefs to how she weighs her options, with a tolerance.**  As
`weighing_of_beliefs`, with her view on every matter between to within `θ`, and `W` a bound on
the sum of the absolute weights: how she compares her options is between to within `θ * W`. -/
theorem weighing_of_beliefs_tol (P : Problem Ω C I ℝ Bool) (hdec : P.declined = ∅) {c t : C}
    {ω : Ω} {θ W : ℝ} (hθ : 0 ≤ θ) (d₀ : ℝ) (w : I → ℝ)
    (hW : ∑ i ∈ P.matters, |w i| ≤ W)
    (hAff : ∀ v : I → ℝ,
      P.eval c ω v true - P.eval c ω v false = d₀ + ∑ i ∈ P.matters, w i * v i)
    (hB : ∀ i ∈ P.matters, P.BetweenViews θ c t ω i)
    (hno : (∀ i ∈ P.matters, 0 ≤ w i * (P.views t ω i - P.his ω i)) ∨
      (∀ i ∈ P.matters, w i * (P.views t ω i - P.his ω i) ≤ 0)) :
    P.Between (θ * W) c t ω true false := by
  have hD : P.rate c ω ∅ true - P.rate c ω ∅ false =
      d₀ + ∑ i ∈ P.matters, w i * P.views c ω i := by
    rw [P.rate_empty, P.rate_empty]; exact hAff _
  have hT : P.rateAs c t ω true - P.rateAs c t ω false =
      d₀ + ∑ i ∈ P.matters, w i * P.views t ω i := hAff _
  have hH : P.rate c ω P.live true - P.rate c ω P.live false =
      d₀ + ∑ i ∈ P.matters, w i * P.his ω i := by
    unfold Problem.rate
    rw [hAff]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    have hl : i ∈ P.live := by simp [Problem.live, hdec, hi]
    simp [hl]
  have hS : ∑ i ∈ P.matters, |w i| * θ ≤ θ * W := by
    rw [← sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hW hθ
  unfold Problem.Between
  rw [hD, hT, hH]
  rcases hno with hpos | hneg
  · have lo : ∑ i ∈ P.matters, -(|w i| * θ) ≤
        ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) :=
      sum_le_sum fun i hi => (between_scale_tol (hB i hi).1 (hB i hi).2 (hpos i hi)).1
    have hi' : ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) ≤
        ∑ i ∈ P.matters, (w i * (P.views t ω i - P.his ω i) + |w i| * θ) :=
      sum_le_sum fun i hi => (between_scale_tol (hB i hi).1 (hB i hi).2 (hpos i hi)).2
    simp only [mul_sub, sum_sub_distrib, sum_add_distrib, sum_neg_distrib] at lo hi'
    have m1 := min_le_right (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    have m2 := le_max_left (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    exact ⟨by linarith, by linarith⟩
  · have lo : ∑ i ∈ P.matters, (w i * (P.views t ω i - P.his ω i) - |w i| * θ) ≤
        ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) :=
      sum_le_sum fun i hi => (between_scale_tol_neg (hB i hi).1 (hB i hi).2 (hneg i hi)).1
    have hi' : ∑ i ∈ P.matters, w i * (P.views c ω i - P.his ω i) ≤
        ∑ i ∈ P.matters, |w i| * θ :=
      sum_le_sum fun i hi => (between_scale_tol_neg (hB i hi).1 (hB i hi).2 (hneg i hi)).2
    simp only [mul_sub, sum_sub_distrib] at lo hi'
    have m1 := min_le_left (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    have m2 := le_max_right (d₀ + ∑ i ∈ P.matters, w i * P.views t ω i)
      (d₀ + ∑ i ∈ P.matters, w i * P.his ω i)
    exact ⟨by linarith, by linarith⟩

/-- **The gap, in weights.**  Two options, nothing declined; his conduct does not change how
she evaluates given views; in each case how she compares her options is a weighted sum of her
views, the absolute weights summing to at most `W`.  If clause 2 of the definition holds,
unasked, then his weight on what she does being more than `θ * W + lam` worse by his views than
under some plain telling is at most `κ` plus his weight on one of four things: under his
conduct she falls more than `lam` short of her own rating; under some plain telling she would;
she rates her two options within `lam + θ * W` of each other; the mistakes some plain telling
would leave offset one another. -/
theorem gap_in_weights (P : Problem Ω C I ℝ Bool) (hopts : P.opts = {true, false})
    (hdec : P.declined = ∅) {θ lam κ W : ℝ} (hθ : 0 ≤ θ) (hl : 0 ≤ lam) {c : C}
    (d₀ : Ω → ℝ) (w : Ω → I → ℝ) (hW : ∀ ω, ∑ i ∈ P.matters, |w ω i| ≤ W)
    (hev : ∀ t ∈ P.tells, ∀ ω, P.eval t ω = P.eval c ω)
    (hAff : ∀ ω (v : I → ℝ),
      P.eval c ω v true - P.eval c ω v false = d₀ ω + ∑ i ∈ P.matters, w ω i * v i)
    (hBel : P.Beliefs θ κ c) (hna : ¬ P.asked c) :
    P.wt (P.WorseByHim (θ * W + lam) c) ≤ κ + P.wt (fun ω =>
      P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ * W) c ω ∨
        ∃ t ∈ P.tells, P.Offsetting (w ω) t ω) := by
  have cover : ∀ ω, P.WorseByHim (θ * W + lam) c ω → P.Mistaken θ c ω ∨
      (P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ * W) c ω ∨
        ∃ t ∈ P.tells, P.Offsetting (w ω) t ω) := by
    rintro ω ⟨t, ht, s, hr, hnr⟩
    have hs : 0 ≤ s := by
      by_contra hneg
      exact hnr ⟨P.act t ω, P.act_mem t ω, by linarith⟩
    have hW0 : 0 ≤ W := le_trans (sum_nonneg fun i _ => abs_nonneg (w ω i)) (hW ω)
    have hθW : 0 ≤ θ * W := mul_nonneg hθ hW0
    have hlive : ∀ i ∈ P.matters, i ∈ P.live := fun i hi => by simp [Problem.live, hdec, hi]
    by_cases hM : P.Mistaken θ c ω
    · exact Or.inl hM
    by_cases hoff : P.Offsetting (w ω) t ω
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, ht, hoff⟩)))
    have hB : ∀ i ∈ P.matters, P.BetweenViews θ c t ω i := fun i hi => by
      by_contra hnb
      exact hM ⟨t, ht, i, hlive i hi, hnb⟩
    have hno : (∀ i ∈ P.matters, 0 ≤ w ω i * (P.views t ω i - P.his ω i)) ∨
        (∀ i ∈ P.matters, w ω i * (P.views t ω i - P.his ω i) ≤ 0) := by
      by_cases hp : ∃ i ∈ P.matters, 0 < w ω i * (P.views t ω i - P.his ω i)
      · exact Or.inl fun i hi => not_lt.mp fun hlt => hoff ⟨hp, i, hi, hlt⟩
      · exact Or.inr fun i hi => not_lt.mp fun hlt => hp ⟨i, hi, hlt⟩
    have hBet := weighing_of_beliefs_tol P hdec hθ (d₀ ω) (w ω) (hW ω) (hAff ω) hB hno
    have live_c : P.rate c ω P.live true - P.rate c ω P.live false =
        d₀ ω + ∑ i ∈ P.matters, w ω i * P.his ω i := by
      unfold Problem.rate
      rw [hAff]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      simp [hlive i hi]
    have live_t : P.rate t ω P.live true - P.rate t ω P.live false =
        d₀ ω + ∑ i ∈ P.matters, w ω i * P.his ω i := by
      unfold Problem.rate
      rw [hev t ht ω, hAff]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      simp [hlive i hi]
    have hH : ∀ x y, P.rate t ω P.live x - P.rate t ω P.live y =
        P.rate c ω P.live x - P.rate c ω P.live y := by
      intro x y
      cases x <;> cases y <;> linarith
    have hT : ∀ x, P.rateAs c t ω x = P.rate t ω ∅ x := fun x => by
      rw [P.rate_empty]; unfold Problem.rateAs; rw [hev t ht ω]
    have hr' : P.Regrets (s + θ * W + lam) c ω := by
      rw [show s + θ * W + lam = s + (θ * W + lam) by ring]; exact hr
    rcases bridge P hopts hθW hl hs hH hT hBet hr' hnr with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨t, ht, h⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inl fun a _ b _ => ?_)))
      have hnn : 0 ≤ lam + θ * W := add_nonneg hl hθW
      cases a <;> cases b
      · simpa using hnn
      · rw [abs_sub_comm]; exact h
      · exact h
      · simpa using hnn
  have h2 : P.wt (P.Mistaken θ c) ≤ κ := hBel.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-! ## The scoring

`LegitimacyGate.gatedScoring` at the predicate `Legit`.  The theorems of
`DeconfusingCorrigibility.Scoring` hold of it as of any predicate, so none is restated. -/

open Classical in
/-- Histories `H`, each read as a decision problem of his and a conduct of his in it: the
scoring whose legitimacy predicate is `Legit` of that conduct. -/
noncomputable def legitScoring {H : Type*} (Pm : DeconfusingCorrigibility.Params)
    (prob : H → Problem Ω C I ℝ O) (conduct : H → C) (θ τ κ : ℝ) (N : H → ℕ) (ord : H → ℝ)
    (window : ℝ) (hord : ∀ h, 0 ≤ ord h ∧ ord h ≤ 1) (hw : -Pm.δ ≤ window ∧ window < 0) :
    DeconfusingCorrigibility.Scoring H :=
  LegitimacyGate.gatedScoring Pm (fun h => (prob h).Legit θ τ κ (conduct h)) N ord window
    hord hw

namespace Problem

variable (P : Problem Ω C I V O)

/-! ## Change in what she values

Her rating is her evaluation applied to her views.  Between his conduct and a plain telling it
can differ because her views differ or because her evaluation does.  The split below holds her
evaluation as it is under his conduct and her views as they are under the telling; the other
order gives another split, and neither is an attribution of cause. -/

/-- The part of the difference in her rating that comes from her views being different. -/
def viewsPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views c ω) a - P.eval c ω (P.views t ω) a

/-- The part that comes from her evaluation being different. -/
def evalPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views t ω) a - P.eval t ω (P.views t ω) a

theorem rate_diff (c t : C) (ω : Ω) (a : O) :
    P.rate c ω ∅ a - P.rate t ω ∅ a = P.viewsPart c t ω a + P.evalPart c t ω a := by
  rw [rate_empty, rate_empty]
  unfold viewsPart evalPart
  ring

end Problem

/-! ## Accuracy, and the long run

The link between his weights and the facts is a condition on his forecasts and not on his
conduct: nothing he knows and she has not been told predicts where his forecasts go wrong.  A
*signal* is any quantity available at each decision.  The condition asks that, for each signal in
a class, moving his forecast a little in the direction of the signal does not lower its squared
error. -/

section OverTime

open Workspace.Deference.Contrib.DeconfusingCorrigibility

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

theorem avg_affine (x : ℕ → ℝ) (a b : ℝ) {K : ℕ} (hK : 0 < K) :
    avg (fun k => a * x k + b) K = a * avg x K + b := by
  unfold avg
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  field_simp

theorem avg_mono {x w : ℕ → ℝ} (h : ∀ k, x k ≤ w k) (K : ℕ) : avg x K ≤ avg w K := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun k _ => h k) (Nat.cast_nonneg K)

/-- If each forecast `p k` is at most `c` plus a second forecast `q k`, the facts `f` exceed `p`
on average by at most `a` in the limit, and `q` exceeds the facts `g` by at most `b`, then in the
long run the average of `f` exceeds the average of `g` by at most `c + a + b`. -/
theorem long_run {c a b : ℝ} (hc : 0 ≤ c) (p q f g : ℕ → ℝ) (step : ∀ k, p k ≤ c + q k)
    (hf : LimsupLE (fun K => avg (fun k => f k - p k) K) a)
    (hg : LimsupLE (fun K => avg (fun k => q k - g k) K) b) :
    LimsupLE (fun K => avg f K - avg g K) (c + a + b) := by
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
  rw [show a + b + c = c + a + b by ring] at h
  exact LimsupLE.of_le key h

/-- For no signal in the class does moving his forecasts by `ε` times the signal lower their
squared error, on average in the limit. -/
def NoSignalBeats (ε : ℝ) (S : Set (ℕ → ℝ)) (D y : ℕ → ℝ) : Prop :=
  ∀ s ∈ S, LimsupLE (fun K => avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K) 0

/-- If no signal in the class beats his forecasts, then for every signal in it of size at most 1
the average of the signal times his error is at most `ε/2` in the limit.  This is one-sided; the
other side needs the negative of the signal to be in the class too. -/
theorem signal_le_of_noSignal {ε : ℝ} (hε : 0 < ε) {S : Set (ℕ → ℝ)} {D y : ℕ → ℝ}
    (h : NoSignalBeats ε S D y) {s : ℕ → ℝ} (hs : s ∈ S) (hb : ∀ k, s k ^ 2 ≤ 1) :
    LimsupLE (fun K => avg (fun k => s k * (y k - D k)) K) (ε / 2) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h s hs (2 * ε * γ) (by positivity)
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le one_pos ((le_max_right N 1).trans hK)
  have h1 := hN K ((le_max_left N 1).trans hK)
  have low : avg (fun k => (2 * ε) * (s k * (y k - D k)) + (-(ε ^ 2))) K ≤
      avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K :=
    avg_mono (fun k => by nlinarith [hb k, sq_nonneg ε]) K
  rw [avg_affine _ _ _ hKpos] at low
  show avg (fun k => s k * (y k - D k)) K ≤ ε / 2 + γ
  have h2 : (2 * ε) * avg (fun k => s k * (y k - D k)) K ≤ (2 * ε) * (ε / 2 + γ) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- The constant signal 1 and the constant signal −1. -/
def shifts : Set (ℕ → ℝ) := {s | s = (fun _ => 1) ∨ s = (fun _ => -1)}

/-- If shifting his forecasts up does not help, the facts exceed his forecasts by at most `ε/2`
on average in the limit. -/
theorem under_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoSignalBeats ε shifts D y) :
    LimsupLE (fun K => avg (fun k => y k - D k) K) (ε / 2) := by
  have h1 := signal_le_of_noSignal hε h (s := fun _ => 1) (Or.inl rfl) (fun _ => by norm_num)
  simpa using h1

/-- If shifting his forecasts down does not help, his forecasts exceed the facts by at most `ε/2`
on average in the limit. -/
theorem over_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoSignalBeats ε shifts D y) :
    LimsupLE (fun K => avg (fun k => D k - y k) K) (ε / 2) := by
  have h1 := signal_le_of_noSignal hε h (s := fun _ => -1) (Or.inr rfl) (fun _ => by norm_num)
  have e : (fun K => avg (fun k => (-1 : ℝ) * (y k - D k)) K) =
      (fun K => avg (fun k => D k - y k) K) := by
    funext K; congr 1; funext k; ring
  rwa [e] at h1

variable (P : ℕ → Problem Ω C I V O) (c t₀ : ℕ → C)

/-- **In the long run.**  `f k` and `g k` are any sequences that his forecasts of the two events
are accurate about in the sense above; they are meant as the facts (whether at `k` she did
something that with his views substituted she would rate well below another option, and whether
under the clear plain telling she would have fallen short), but nothing here says how those are
observed.  If at every decision the outcome guarantee holds unasked and `t₀ k` is a clear plain telling, the
long-run average of `f` exceeds that of `g` by at most `κ + ε`. -/
theorem long_run_informed {θ θ₀ κ ε : ℝ} (σ : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hO : ∀ k, (P k).Outcome θ κ (c k)) (ht₀ : ∀ k, t₀ k ∈ (P k).tells)
    (hC : ∀ k, (P k).ClearAt θ₀ (t₀ k)) (hna : ∀ k, ¬ (P k).asked (c k)) (f g : ℕ → ℝ)
    (hf : NoSignalBeats ε shifts (fun k => (P k).wt ((P k).Regrets (σ + θ₀ + θ) (c k))) f)
    (hg : NoSignalBeats ε shifts (fun k => (P k).wt ((P k).Short σ (t₀ k))) g) :
    LimsupLE (fun K => avg f K - avg g K) (κ + ε / 2 + ε / 2) :=
  long_run hκ _ _ f g
    (fun k => (P k).chooses_as_informed σ (hO k) (ht₀ k) (hC k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε hg)

end OverTime

/-! ## A course of conduct and where it ends

His conduct is a course that she can let go on or stop.  `Z` is where things can end, and an end
includes what she then values.  She evaluates ends by what she values now.  The one matter is
where going on ends: he has a forecast of it, she has a view of it, and in each case there is
where it does end.  Under a plain telling the course is not being run: he tells her of it and
does nothing else.  This is a decision problem of the kind above, built and not supposed. -/

structure Course (Ω C Z : Type*) [Fintype Ω] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her evaluation, by what she values now, of where things end -/
  u : Ω → Z → ℝ
  /-- where things are left if the course does not go on -/
  stay : Ω → Z
  /-- his forecast of where going on ends, what she will then value included -/
  fore : Ω → Z
  /-- her view, under each option of his, of where going on ends -/
  bel : C → Ω → Z
  /-- what she takes his forecast to be, under each option of his -/
  told : C → Ω → Z
  /-- where going on does end -/
  ends : C → Ω → Z
  /-- the course goes on -/
  goes : C → Ω → Bool
  /-- under a plain telling the course is not run -/
  tell_stops : ∀ t ∈ tells, ∀ ω, goes t ω = false
  /-- she asked for this conduct -/
  asked : C → Prop

namespace Course

variable {Z : Type*} (K : Course Ω C Z)

/-- The decision problem of a course: the options are that it goes on (`true`) or not (`false`);
the one matter is where going on ends. -/
def toProblem : Problem Ω C Unit Z Bool where
  μ := K.μ
  μ_nonneg := K.μ_nonneg
  μ_sum := K.μ_sum
  tells := K.tells
  tells_nonempty := K.tells_nonempty
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun c ω _ => K.bel c ω
  his := fun ω _ => K.fore ω
  shown := fun c ω _ => K.told c ω
  eval := fun _ ω v a => if a then K.u ω (v ()) else K.u ω (K.stay ω)
  act := K.goes
  act_mem := fun c ω => by cases K.goes c ω <;> simp
  asked := K.asked

/-- With his view substituted, her rating of going on is her present evaluation of his
forecast. -/
theorem rate_go (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live true = K.u ω (K.fore ω) := by
  simp [Problem.rate, Problem.live, toProblem]

/-- Her rating of its not going on is her present evaluation of where that leaves her. -/
theorem rate_stop (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live false = K.u ω (K.stay ω) := by
  simp [Problem.rate, toProblem]

/-- His forecast is off: by her present evaluation, where it ends differs from his forecast by
more than `δ`. -/
def Off (δ : ℝ) (c : C) (ω : Ω) : Prop := δ < |K.u ω (K.ends c ω) - K.u ω (K.fore ω)|

/-- The course goes on, and it ends where her present evaluation rates more than `m` below where
its not going on would have left her. -/
def LedAstray (m : ℝ) (c : C) (ω : Ω) : Prop :=
  K.goes c ω = true ∧ K.u ω (K.ends c ω) + m < K.u ω (K.stay ω)

/-- **Not led astray, beyond his forecast error.**  If the outcome guarantee holds and she did not ask, then
his weight on the course going on to an end that her present evaluation rates more than `θ + δ`
below its not going on is at most `κ` plus his weight on his forecast being off by more than
`δ`.  Her own weakness does not enter: under a plain telling the course is not run. -/
theorem not_led_astray {θ κ : ℝ} (δ : ℝ) (hθ : 0 ≤ θ) {c : C} (hO : K.toProblem.Outcome θ κ c)
    (hna : ¬ K.asked c) :
    K.toProblem.wt (K.LedAstray (θ + δ) c) ≤ κ + K.toProblem.wt (K.Off δ c) := by
  have cover : ∀ ω, K.LedAstray (θ + δ) c ω → K.toProblem.WorseByHim θ c ω ∨ K.Off δ c ω := by
    rintro ω ⟨hg, hlt⟩
    by_cases hoff : K.Off δ c ω
    · exact Or.inr hoff
    · have h := abs_le.mp (not_lt.mp hoff)
      have key : K.u ω (K.fore ω) + θ < K.u ω (K.stay ω) := by linarith [h.1]
      obtain ⟨t, ht⟩ := K.tells_nonempty
      refine Or.inl ⟨t, ht, 0, ⟨false, by simp [toProblem], ?_⟩, ?_⟩
      · show K.toProblem.rate c ω K.toProblem.live (K.goes c ω) + (0 + θ) <
          K.toProblem.rate c ω K.toProblem.live false
        rw [hg, rate_go, rate_stop]
        linarith
      · rintro ⟨b, -, hb⟩
        have hb' : K.toProblem.rate t ω K.toProblem.live (K.goes t ω) + 0 <
            K.toProblem.rate t ω K.toProblem.live b := hb
        rw [K.tell_stops t ht ω, rate_stop] at hb'
        cases b
        · rw [rate_stop] at hb'; linarith
        · rw [rate_go] at hb'; linarith
  have h2 : K.toProblem.wt (K.toProblem.WorseByHim θ c) ≤ κ := hO.resolve_right hna
  linarith [(K.toProblem.wt_mono cover).trans (K.toProblem.wt_or_le _ _)]

/-- In a course her evaluation is the same whatever he does, so her rating with his view
substituted is the same under every option. -/
theorem rate_live_eq (c t : C) (ω : Ω) (x : Bool) :
    K.toProblem.rate t ω K.toProblem.live x = K.toProblem.rate c ω K.toProblem.live x := by
  cases x
  · rw [rate_stop, rate_stop]
  · rw [rate_go, rate_go]

/-- And her rating under his conduct with a plain telling's views is her rating under that
telling. -/
theorem rateAs_eq (c t : C) (ω : Ω) (x : Bool) :
    K.toProblem.rateAs c t ω x = K.toProblem.rate t ω ∅ x := by
  rw [Problem.rate_empty]
  rfl

/-- **Not led astray, from the weighing form.**  If his conduct satisfies `LegitW` and she did not ask,
then his weight on the course going on to an end that her present evaluation rates more than
`θ + lam + δ` below its not going on is at most `2κ`, plus his weight on her own view being
otherwise (for `lam ≥ τ`: told plainly, she would herself rate its going on more than `lam − τ`
above its not going on; for `lam < τ` this term is his whole weight and the bound says nothing) or nearly even (she rates the two within `lam + θ`), plus his weight on his forecast
being off by more than `δ`. -/
theorem not_led_astray_of_legit {θ τ κ : ℝ} (lam δ : ℝ) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ)
    (hl : 0 ≤ lam) {c : C} (hL : K.toProblem.LegitW θ τ κ c) (hna : ¬ K.asked c) :
    K.toProblem.wt (K.LedAstray (θ + lam + δ) c) ≤
      2 * κ + K.toProblem.wt (fun ω =>
          (∃ t ∈ K.tells, K.toProblem.Short (lam - τ) t ω) ∨
            K.toProblem.NearEven (lam + θ) c ω) +
        K.toProblem.wt (K.Off δ c) := by
  have hW := outcome_of_views K.toProblem rfl hθ hl
    (fun t _ ω x y => by rw [K.rate_live_eq c t ω x, K.rate_live_eq c t ω y])
    (fun t _ ω x => K.rateAs_eq c t ω x) hL.2.1 hna
  have h1 := K.not_led_astray δ (by linarith : (0 : ℝ) ≤ θ + lam) (Or.inl hW) hna
  have cover : ∀ ω, (K.toProblem.Short lam c ω ∨ (∃ t ∈ K.toProblem.tells,
        K.toProblem.Short lam t ω) ∨ K.toProblem.NearEven (lam + θ) c ω) →
      K.toProblem.Worse τ c ω ∨ ((∃ t ∈ K.tells, K.toProblem.Short (lam - τ) t ω) ∨
        K.toProblem.NearEven (lam + θ) c ω) := by
    rintro ω (h | ⟨t, ht, h⟩ | h)
    · rcases K.toProblem.short_sub (τ := τ) h with hw | hall
      · exact Or.inl hw
      · obtain ⟨t, ht⟩ := K.tells_nonempty
        exact Or.inr (Or.inl ⟨t, ht, hall t ht⟩)
    · exact Or.inr (Or.inl ⟨t, ht, K.toProblem.short_mono (by linarith) h⟩)
    · exact Or.inr (Or.inr h)
  have h2 : K.toProblem.wt (K.toProblem.Worse τ c) ≤ κ := hL.2.2.resolve_right hna
  have h3 := (K.toProblem.wt_mono cover).trans (K.toProblem.wt_or_le _ _)
  linarith

end Course

/-! The forecast-error term cannot be dropped.  One case; his options are to run the course,
telling her all he thinks (`true`), or the plain telling alone (`false`); ends are numbers and
she values them as they are.  Not going on leaves her at 0.  He forecasts that going on ends at
1, tells her, and she agrees.  It ends at −1. -/

/-- The course in which he is sincere, clear, and wrong. -/
noncomputable def sincereWrong : Course Unit Bool ℝ where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := {false}
  tells_nonempty := by simp
  u := fun _ z => z
  stay := fun _ => 0
  fore := fun _ => 1
  bel := fun _ _ => 1
  told := fun _ _ => 1
  ends := fun _ _ => -1
  goes := fun c _ => c
  tell_stops := fun t ht _ => by rw [mem_singleton] at ht; exact ht
  asked := fun _ => False

open Classical in
/-- The outcome guarantee holds with no tolerance, and with his whole weight the course goes on to an end she
rates below its not going on.  The only term left on the right of `not_led_astray` is his
forecast being off. -/
theorem needs_forecast :
    sincereWrong.toProblem.Outcome 0 0 true ∧
      sincereWrong.toProblem.wt (sincereWrong.LedAstray (1 / 2) true) = 1 := by
  refine ⟨Or.inl (sincereWrong.toProblem.wt_le_of_forall_not (fun ω hn => ?_) le_rfl), ?_⟩
  · obtain ⟨t, ht, s, ⟨b, -, hb⟩, hns⟩ := hn
    have ht' : t = false := by simpa [Course.toProblem, sincereWrong] using ht
    subst ht'
    have hb' : sincereWrong.toProblem.rate true ω sincereWrong.toProblem.live true + (s + 0) <
        sincereWrong.toProblem.rate true ω sincereWrong.toProblem.live b := hb
    have hs : s < 0 := by
      cases b
      · rw [Course.rate_go, Course.rate_stop] at hb'
        simp [sincereWrong] at hb'
        linarith
      · rw [Course.rate_go] at hb'
        simp at hb'
        linarith
    refine hns ⟨true, by simp [Course.toProblem], ?_⟩
    show sincereWrong.toProblem.rate false ω sincereWrong.toProblem.live false + s <
      sincereWrong.toProblem.rate false ω sincereWrong.toProblem.live true
    rw [Course.rate_stop, Course.rate_go]
    simp [sincereWrong]
    linarith
  · have hyes : sincereWrong.LedAstray (1 / 2) true () :=
      ⟨rfl, by show (-1 : ℝ) + 1 / 2 < 0; norm_num⟩
    unfold Problem.wt
    rw [Finset.univ_unique, Finset.sum_singleton, if_pos hyes]
    rfl

section CourseInFact

open Workspace.Deference.Contrib.DeconfusingCorrigibility

variable {Z : Type*} (K : ℕ → Course Ω C Z) (c : ℕ → C)

/-- **Not led astray, in the long run.**  A sequence of courses.  `f k` and `e k` are any
sequences that his forecasts of the two events are accurate about; they are meant as the facts
(whether the course in fact went on to an end her evaluation at its start rates more than
`θ + δ` below its not going on, and whether his forecast was in fact off by more than `δ`).  If
at each course the outcome guarantee holds unasked, the long-run average of `f` exceeds that of `e` by at most
`κ + ε`. -/
theorem long_run_not_led_astray {θ κ ε : ℝ} (δ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hO : ∀ k, (K k).toProblem.Outcome θ κ (c k)) (hna : ∀ k, ¬ (K k).asked (c k))
    (f e : ℕ → ℝ)
    (hf : NoSignalBeats ε shifts
      (fun k => (K k).toProblem.wt ((K k).LedAstray (θ + δ) (c k))) f)
    (he : NoSignalBeats ε shifts (fun k => (K k).toProblem.wt ((K k).Off δ (c k))) e) :
    LimsupLE (fun n => avg f n - avg e n) (κ + ε / 2 + ε / 2) :=
  long_run hκ _ _ f e (fun k => (K k).not_led_astray δ hθ (hO k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε he)

end CourseInFact

/-! ## Instances: numerical patterns

One case; one matter, on which her view is `false` and his is `true`; her options `true` (which
she rates 1) and `false` (which she rates 0).  His options are of any type `K`.

* `hid k`   under `k` she takes his view to be other than it is
* `bad k`   under `k`, with his view substituted, she would rate her options the other way round
* `l k`     under `k` she takes the option she herself rates lower
* `ask`     she asked

Her own views are the same under every option here, so this family shows the patterns of clause
1, clause 3 and the outcome guarantee; the weighing condition is shown in the family after it.  The names say what kind of conduct
would produce each pattern; that such conduct produces it is not shown here. -/

namespace Witness

noncomputable def W {K : Type} (tells : Finset K) (hne : tells.Nonempty) (hid bad l : K → Bool)
    (ask : Prop) : Problem Unit K Unit Bool Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  tells_nonempty := hne
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun _ _ _ => false
  his := fun _ _ => true
  shown := fun k _ _ => !(hid k)
  eval := fun k _ v a =>
    if v () && bad k then (if a then 0 else 1) else (if a then 1 else 0)
  act := fun k _ => !(l k)
  act_mem := fun k _ => by cases l k <;> simp
  asked := fun _ => ask

variable {K : Type} (tells : Finset K) (hne : tells.Nonempty) (hid bad l : K → Bool) (ask : Prop)

theorem own_W (k : K) (a : Bool) :
    (W tells hne hid bad l ask).rate k () ∅ a = if a then 1 else 0 := by
  simp [Problem.rate, W]

theorem informed_W (k : K) (a : Bool) :
    (W tells hne hid bad l ask).rate k () (W tells hne hid bad l ask).live a =
      if bad k then (if a then 0 else 1) else (if a then 1 else 0) := by
  cases hb : bad k <;> simp [Problem.rate, Problem.live, W, hb]

open Classical in
theorem wt_W (p : Unit → Prop) : (W tells hne hid bad l ask).wt p = if p () then 1 else 0 := by
  unfold Problem.wt
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem short_W (s : ℝ) (k : K) :
    (W tells hne hid bad l ask).Short s k () ↔ s < (if l k then 1 else 0) := by
  constructor
  · rintro ⟨b, -, hb⟩
    rw [own_W, own_W] at hb
    cases hl : l k <;> cases b <;> simp [W, hl] at hb ⊢ <;> linarith
  · intro h
    refine ⟨true, by simp [W], ?_⟩
    rw [own_W, own_W]
    cases hl : l k <;> simp [W, hl] at h ⊢ <;> linarith

theorem regrets_W (s : ℝ) (k : K) :
    (W tells hne hid bad l ask).Regrets s k () ↔ s < (if l k = bad k then 0 else 1) := by
  constructor
  · rintro ⟨b, -, hb⟩
    rw [informed_W, informed_W] at hb
    cases hl : l k <;> cases hbad : bad k <;> cases b <;> simp [W, hl, hbad] at hb ⊢ <;> linarith
  · intro h
    refine ⟨bad k == false, by cases bad k <;> simp [W], ?_⟩
    rw [informed_W, informed_W]
    cases hl : l k <;> cases hbad : bad k <;> simp [W, hl, hbad] at h ⊢ <;> linarith

theorem hidden_W (c : K) :
    (W tells hne hid bad l ask).Hidden c () ↔ (hid c = true ∧ ∃ t ∈ tells, hid t = false) := by
  constructor
  · rintro ⟨i, -, hne', t, ht, heq⟩
    refine ⟨?_, t, ht, ?_⟩
    · cases hc : hid c
      · exact absurd (by simp [W, hc]) hne'
      · rfl
    · cases ht' : hid t
      · rfl
      · simp [W, ht'] at heq
  · rintro ⟨hc, t, ht, ht'⟩
    exact ⟨(), by simp [Problem.live, W], by simp [W, hc], t, ht, by simp [W, ht']⟩

theorem worseByHim_W {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (c : K) :
    (W tells hne hid bad l ask).WorseByHim θ c () ↔
      (l c ≠ bad c ∧ ∃ t ∈ tells, l t = bad t) := by
  constructor
  · rintro ⟨t, ht, s, h1, h2⟩
    rw [regrets_W] at h1 h2
    by_cases hc : l c = bad c
    · rw [if_pos hc] at h1
      by_cases ht' : l t = bad t
      · rw [if_pos ht'] at h2; linarith
      · rw [if_neg ht'] at h2; linarith
    · refine ⟨hc, t, ht, ?_⟩
      by_contra ht'
      rw [if_neg hc] at h1
      rw [if_neg ht'] at h2
      linarith
  · rintro ⟨hc, t, ht, ht'⟩
    refine ⟨t, ht, 0, ?_, ?_⟩
    · rw [regrets_W, if_neg hc]; linarith
    · rw [regrets_W, if_pos ht']; exact lt_irrefl 0

theorem worse_W {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (c : K) :
    (W tells hne hid bad l ask).Worse τ c () ↔ (l c = true ∧ ∃ t ∈ tells, l t = false) := by
  constructor
  · rintro ⟨t, ht, s, h1, h2⟩
    rw [short_W] at h1 h2
    cases hc : l c <;> cases hl : l t <;> simp [hc, hl] at h1 h2 ⊢ <;>
      first
        | linarith
        | exact ⟨t, ht, hl⟩
  · rintro ⟨hc, t, ht, hl⟩
    refine ⟨t, ht, 0, ?_, ?_⟩
    · rw [short_W]; simp [hc]; linarith
    · rw [short_W]; simp [hl]

open Classical in
/-- In this family her views are the same under every option, so the weighing condition always holds; the
other two hold when their patterns are absent. -/
theorem legit_W {θ τ κ : ℝ} (hθ0 : 0 ≤ θ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hκ : 0 ≤ κ) (c : K) (h1 : ¬ (hid c = true ∧ ∃ t ∈ tells, hid t = false))
    (h3 : ¬ (l c = true ∧ ∃ t ∈ tells, l t = false)) :
    (W tells hne hid bad l ask).LegitW θ τ κ c := by
  refine ⟨?_, Or.inl ?_, Or.inl ?_⟩
  · show (W tells hne hid bad l ask).wt _ ≤ κ
    rw [wt_W, if_neg (by rwa [hidden_W])]
    exact hκ
  · refine (W tells hne hid bad l ask).wt_le_of_forall_not (fun ω hn => ?_) hκ
    obtain ⟨t, -, a, -, b, -, hnb⟩ := hn
    exact hnb ((W tells hne hid bad l ask).between_of_same_views hθ0 a b rfl)
  · rw [wt_W, if_neg (by rwa [worse_W tells hne hid bad l ask hτ0 hτ1])]
    exact hκ

open Classical in
theorem not_open_W {κ : ℝ} (hκ : κ < 1) (c : K)
    (h : hid c = true ∧ ∃ t ∈ tells, hid t = false) :
    ¬ (W tells hne hid bad l ask).Open κ c := by
  unfold Problem.Open
  rw [wt_W, if_pos ((hidden_W tells hne hid bad l ask c).mpr h)]
  exact not_le.mpr hκ

open Classical in
theorem not_outcome_W {θ κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : κ < 1) (c : K)
    (h : l c ≠ bad c ∧ ∃ t ∈ tells, l t = bad t) (hna : ¬ ask) :
    ¬ (W tells hne hid bad l ask).Outcome θ κ c := by
  rintro (h' | h')
  · rw [wt_W, if_pos ((worseByHim_W tells hne hid bad l ask hθ0 hθ1 c).mpr h)] at h'
    linarith
  · exact hna h'

open Classical in
theorem not_will_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : κ < 1) (c : K)
    (h : l c = true ∧ ∃ t ∈ tells, l t = false) (hna : ¬ ask) :
    ¬ (W tells hne hid bad l ask).Will τ κ c := by
  rintro (h' | h')
  · rw [wt_W, if_pos ((worse_W tells hne hid bad l ask hτ0 hτ1 c).mpr h)] at h'
    linarith
  · exact hna h'

/-! His options in the next instances: `true` the conduct in question, `false` the one plain
telling open to him. -/

/-- Nothing hidden, the same act as under plain telling: legitimate. -/
theorem same_as_telling :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun _ => false) False).LegitW
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-- She knows what he thinks and rates her options the other way, under his conduct as under
plain telling: legitimate.  Disagreement that plain telling would leave is hers. -/
theorem keeps_her_view :
    (W {false} (by simp) (fun _ => false) (fun _ => true) (fun _ => false) False).LegitW
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-- She is left wrong about what he thinks, where plain telling would have her know it: clause 1
fails.  Something untold, or a lie. -/
theorem hidden_fails :
    ¬ (W {false} (by simp) (fun k => k) (fun _ => false) (fun _ => false) False).Open
      (1 / 10) true :=
  not_open_W _ _ _ _ _ _ (by norm_num) true ⟨rfl, false, by simp, rfl⟩

/-- Under his conduct she does what, with his views substituted, she would rate lower, and under
plain telling she would not: the outcome guarantee fails. -/
theorem worse_by_him_fails :
    ¬ (W {false} (by simp) (fun _ => false) (fun k => k) (fun _ => false) False).Outcome
      (1 / 10) (1 / 10) true :=
  not_outcome_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) true
    ⟨by simp, false, by simp, by simp⟩ (fun h => h)

/-- Under his conduct she does what he thinks best for her, under plain telling she would not,
and he gets there by leaving her wrong about what he thinks: the outcome guarantee and clause 3
hold and clause 1 fails.  A lie for her own good. -/
theorem for_her_own_good :
    (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Outcome
        (1 / 10) (1 / 10) true ∧
      (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Will
        (1 / 10) (1 / 10) true ∧
      ¬ (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Open
        (1 / 10) true := by
  refine ⟨Or.inl ?_, Or.inl ?_, not_open_W _ _ _ _ _ _ (by norm_num) true ⟨rfl, false, by simp, rfl⟩⟩
  · rw [wt_W, if_neg (by
      rw [worseByHim_W _ _ _ _ _ _ (by norm_num) (by norm_num)]; simp)]
    norm_num
  · rw [wt_W, if_neg (by rw [worse_W _ _ _ _ _ _ (by norm_num) (by norm_num)]; simp)]
    norm_num

/-- Under his conduct she takes what she herself rates lower, and under plain telling she would
not, unasked: clause 3 fails. -/
theorem pressed :
    ¬ (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) False).Will
      (1 / 10) (1 / 10) true :=
  not_will_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) true
    ⟨rfl, false, by simp, rfl⟩ (fun h => h)

/-- The same, and she asked: the outcome guarantee and clause 3 hold. -/
theorem pressed_asked :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) True).Outcome
        (1 / 10) (1 / 10) true ∧
      (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) True).Will
        (1 / 10) (1 / 10) true :=
  ⟨Or.inr trivial, Or.inr trivial⟩

/-- She takes what she herself rates lower under plain telling too: legitimate. -/
theorem weak_anyway :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun _ => true) False).LegitW
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-! Choosing the moment.  His options: `some true` asking now and saying everything;
`some false` telling her plainly now; `none` telling her plainly later.  Now, with his view of
what she values substituted, she would rate her options the other way; later she would not. -/

/-- Asking now, with everything said, when he could have told her later: the outcome guarantee
fails. -/
theorem mood_timing :
    ¬ (W {some false, none} (by simp) (fun _ => false) (fun k => k.isSome) (fun _ => false)
      False).Outcome (1 / 10) (1 / 10) (some true) :=
  not_outcome_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (some true)
    ⟨by simp, none, by simp, by simp⟩ (fun h => h)

/-- The same when the matter cannot wait, so that telling her now is the only plain telling open
to him: legitimate. -/
theorem mood_cannot_wait :
    (W {some false} (by simp) (fun _ => false) (fun k => k.isSome) (fun _ => false)
      False).LegitW (1 / 10) (1 / 10) (1 / 10) (some true) :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-! The weighing condition.  One case; one matter, a number; her option `true` is rated at her view of that
number and `false` at 0, whatever he does.  `h` is his view; `x k` is her view under his option
`k`; `g k` is whether she takes `true`.  How she compares `true` with `false` under `k` is then
`x k`, with a plain telling `t`'s views `x t`, and with his view substituted `h`. -/

noncomputable def W2 {K : Type} (tells : Finset K) (hne : tells.Nonempty) (h : ℝ) (x : K → ℝ)
    (g : K → Bool) : Problem Unit K Unit ℝ Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  tells_nonempty := hne
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun k _ _ => x k
  his := fun _ _ => h
  shown := fun _ _ _ => h
  eval := fun _ _ v a => if a then v () else 0
  act := fun k _ => g k
  act_mem := fun k _ => by cases g k <;> simp
  asked := fun _ => False

theorem between_W2 {K : Type} (tells : Finset K) (hne : tells.Nonempty) (h : ℝ) (x : K → ℝ)
    (g : K → Bool) (θ : ℝ) (c t : K) :
    (W2 tells hne h x g).Between θ c t () true false ↔
      (min (x t) h - θ ≤ x c ∧ x c ≤ max (x t) h + θ) := by
  simp [Problem.Between, Problem.rateAs, Problem.rate, Problem.live, W2]

/-- She keeps her view after being told, far from his: between. -/
theorem w2_keeps_her_view :
    (W2 {false} (by simp) 1 (fun _ => -3) (fun _ => false)).Between (1 / 10) true false ()
      true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- His conduct brings her part of the way from where plain telling would leave her toward his
view: between.  Open persuasion beyond plain telling. -/
theorem w2_part_way :
    (W2 {false} (by simp) 1 (fun k => if k then 0 else -3) (fun _ => false)).Between (1 / 10)
      true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- His conduct carries her past his view: not between.  A lie that overshoots, or an anchor he
announces. -/
theorem w2_overshoot :
    ¬ (W2 {false} (by simp) (-1) (fun k => if k then 1 else -3) (fun _ => false)).Between
      (1 / 10) true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- Plain telling would leave her agreeing with him; his conduct leaves her further along than
either, in the direction he wants: not between.  A fear he takes to be out of proportion, used
for her own good. -/
theorem w2_for_her_good_by_distortion :
    ¬ (W2 {false} (by simp) 1 (fun k => if k then 5 else 1) (fun _ => true)).Between
      (1 / 10) true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- Now, in a mood, she compares her options far from how he takes her to value them; told
plainly later she would not.  Asking now (`some true`) is not between against telling later
(`none`), and is between against telling now (`some false`). -/
theorem w2_mood :
    ¬ (W2 {some false, none} (by simp) (-1) (fun k => if k.isSome then 1 else -1)
        (fun _ => true)).Between (1 / 10) (some true) none () true false ∧
      (W2 {some false, none} (by simp) (-1) (fun k => if k.isSome then 1 else -1)
        (fun _ => true)).Between (1 / 10) (some true) (some false) () true false := by
  constructor <;> rw [between_W2] <;> norm_num [min_def, max_def]

/-- The near-even term of the bridge is needed.  After plain telling she rates her two options
even and takes the one that is better by his view; under his conduct she rates them even and
takes the other.  How she compares them is between with no tolerance, and what she does is worse
by his view by 9 and more. -/
theorem w2_tips_an_even_choice :
    (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Between 0 true false () true false ∧
      (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Regrets (0 + 9) true () ∧
      ¬ (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Regrets 0 false () := by
  refine ⟨by rw [between_W2]; norm_num [min_def, max_def], ⟨false, by simp [W2], ?_⟩, ?_⟩
  · simp [Problem.rate, Problem.live, W2]; norm_num
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, Problem.live, W2] at hb
    linarith

/-! Offsetting mistakes.  One case; two matters, numbers `x` (matter `true`) and `y` (matter
`false`); she rates her option `true` at `x + y + 1/2` and `false` at 0, whatever he does.  His
views are `(0, 0)`.  The one plain telling (`false`) would leave her at `(1, −1)`: two mistakes
that cancel, so that she takes `true`, which is the better by his view.  His conduct (`true`)
corrects the first and leaves the second, `(0, −1)`, and she takes `false`. -/

noncomputable def W3 : Problem Unit Bool Bool ℝ Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := {false}
  tells_nonempty := by simp
  opts := {true, false}
  matters := {true, false}
  declined := ∅
  views := fun k _ i => if k then (if i then 0 else -1) else (if i then 1 else -1)
  his := fun _ _ => 0
  shown := fun _ _ _ => 0
  eval := fun _ _ v a => if a then v true + v false + 1 / 2 else 0
  act := fun k _ => !k
  act_mem := fun k _ => by cases k <;> simp
  asked := fun _ => False

/-- The offsetting item of `gap` is needed.  On each matter her view under his conduct is between
where the plain telling would leave it and his own; he has only removed a mistake.  She falls
short of her own rating neither under his conduct nor under the plain telling, and she does not
rate her options nearly even.  Yet what she does is worse by his views than under the plain
telling. -/
theorem w3_correcting_one_of_two :
    (∀ i, W3.BetweenViews 0 true false () i) ∧
      W3.Regrets (0 + 1 / 4) true () ∧ ¬ W3.Regrets 0 false () ∧
      ¬ W3.Short (1 / 4) true () ∧ ¬ W3.Short (1 / 4) false () ∧
      ¬ |W3.rate true () ∅ true - W3.rate true () ∅ false| ≤ 1 / 4 := by
  refine ⟨fun i => ?_, ⟨true, by simp [W3], ?_⟩, ?_, ?_, ?_, ?_⟩
  · cases i <;> simp [Problem.BetweenViews, W3]
  · simp [Problem.rate, Problem.live, W3]; norm_num
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, Problem.live, W3] at hb
    linarith
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, W3] at hb <;> linarith
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, W3] at hb <;> linarith
  · simp [Problem.rate, W3]; norm_num [abs_le]

/-! Terms inhabiting the hypothesis packages, and the two instances above as conduct that
satisfies the definition. -/

/-- With one case, his weight on a condition that holds there is 1. -/
theorem wt_unit_of {C I V O : Type*} [DecidableEq I] [DecidableEq O]
    (P : Problem Unit C I V O) {p : Unit → Prop} (h : p ()) : P.wt p = 1 := by
  have hμ := P.μ_sum
  rw [Finset.univ_unique, Finset.sum_singleton] at hμ
  unfold Problem.wt
  rw [Finset.univ_unique, Finset.sum_singleton, if_pos h]
  exact hμ

/-- **The hypothesis package of `weighing_of_beliefs` is inhabited**: the problem of
`w2_part_way`, where his conduct brings her part of the way from where plain telling would
leave her toward his view.  One matter, weight 1; the one mistake plain telling would leave has
nothing to offset it. -/
theorem weighing_instance :
    (W2 {false} (by simp) 1 (fun k => if k then 0 else -3) (fun _ => false)).Between 0
      true false () true false :=
  weighing_of_beliefs _ rfl 0 (fun _ => 1)
    (fun v => by simp [W2])
    (fun i _ => by simp [Problem.BetweenViews, W2])
    (Or.inr fun i _ => by simp [W2]; norm_num)

/-- **The hypothesis package of `gap` is inhabited**: `W3`, with his conduct `true`, the plain
telling `false`, `lam = 1/4`, `s = 0`, and the comparison `1/2 + x + y`. -/
theorem gap_instance :
    W3.Short (1 / 4) true () ∨ W3.Short (1 / 4) false () ∨
      |W3.rate true () ∅ true - W3.rate true () ∅ false| ≤ 1 / 4 ∨
      W3.Offsetting (fun _ => 1) false () :=
  gap W3 rfl rfl (by norm_num) le_rfl (1 / 2) (fun _ => 1) rfl
    (fun v => by simp [W3]; ring)
    (fun i _ => w3_correcting_one_of_two.1 i)
    w3_correcting_one_of_two.2.1 w3_correcting_one_of_two.2.2.1

/-- On `W3` the first three items of `gap` fail, so its conclusion there is the fourth: the
mistakes the plain telling would leave offset one another. -/
theorem gap_instance_offsetting : W3.Offsetting (fun _ => 1) false () := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := w3_correcting_one_of_two
  rcases gap_instance with h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact h

/-- The conduct of `w3_correcting_one_of_two` satisfies the definition with no tolerance, and
the outcome guarantee fails of it. -/
theorem w3_legit_and_worse : W3.Legit 0 0 0 true ∧ ¬ W3.Outcome (1 / 4) (1 / 2) true := by
  obtain ⟨hB, hr, hnr, -, -, -⟩ := w3_correcting_one_of_two
  refine ⟨⟨?_, Or.inl ?_, Or.inl ?_⟩, ?_⟩
  · refine W3.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨i, -, hne, -⟩ := hn
    exact hne rfl
  · refine W3.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨t, ht, i, -, hnb⟩ := hn
    have ht' : t = false := by simpa [W3] using ht
    subst ht'
    exact hnb (hB i)
  · refine W3.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨t, ht, s, ⟨b, -, hb⟩, hns⟩ := hn
    have ht' : t = false := by simpa [W3] using ht
    subst ht'
    have hs : s < 0 := by
      cases b <;> simp [Problem.rate, W3] at hb <;> linarith
    refine hns ⟨true, by simp [W3], ?_⟩
    simp [Problem.rate, W3]
    linarith
  · rintro (h | h)
    · have hw : W3.WorseByHim (1 / 4) true () := ⟨false, by simp [W3], 0, hr, hnr⟩
      rw [wt_unit_of W3 hw] at h
      norm_num at h
    · exact h

/-- The conduct of `w2_tips_an_even_choice` satisfies the definition with no tolerance, and the
outcome guarantee fails of it. -/
theorem w2_tips_legit_and_worse :
    (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Legit 0 0 0 true ∧
      ¬ (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Outcome 9 (1 / 2) true := by
  obtain ⟨-, hr, hnr⟩ := w2_tips_an_even_choice
  refine ⟨⟨?_, Or.inl ?_, Or.inl ?_⟩, ?_⟩
  · refine Problem.wt_le_of_forall_not _ (fun ω hn => ?_) le_rfl
    obtain ⟨i, -, hne, -⟩ := hn
    exact hne rfl
  · refine Problem.wt_le_of_forall_not _ (fun ω hn => ?_) le_rfl
    obtain ⟨t, -, i, -, hnb⟩ := hn
    exact hnb (by simp [Problem.BetweenViews, W2])
  · refine Problem.wt_le_of_forall_not _ (fun ω hn => ?_) le_rfl
    obtain ⟨t, ht, s, ⟨b, -, hb⟩, hns⟩ := hn
    have hs : s < 0 := by
      cases b <;> simp [Problem.rate, W2] at hb <;> linarith
    refine hns ⟨true, by simp [W2], ?_⟩
    simp [Problem.rate, W2]
    linarith
  · rintro (h | h)
    · have hw : (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).WorseByHim 9 true () :=
        ⟨false, by simp [W2], 0, hr, hnr⟩
      rw [wt_unit_of _ hw] at h
      norm_num at h
    · exact h

/-- **The hypothesis package of `gap_in_weights` is inhabited**: `W3` at `θ = κ = 0`,
`W = 2`, `lam = 1/4`. -/
theorem gap_in_weights_instance :
    W3.wt (W3.WorseByHim (0 * 2 + 1 / 4) true) ≤ 0 + W3.wt (fun ω =>
      W3.Short (1 / 4) true ω ∨ (∃ t ∈ W3.tells, W3.Short (1 / 4) t ω) ∨
        W3.NearEven (1 / 4 + 0 * 2) true ω ∨ ∃ t ∈ W3.tells, W3.Offsetting (fun _ => 1) t ω) :=
  gap_in_weights W3 rfl rfl le_rfl (by norm_num) (fun _ => 1 / 2) (fun _ _ => 1)
    (fun _ => by simp [W3])
    (fun _ _ _ => rfl)
    (fun _ v => by simp [W3]; ring)
    w3_legit_and_worse.1.2.1 (fun h => h)

/-! His conduct changes how she evaluates.  One case; one matter, a number, on which her view
is 0 whatever he does and his is 1.  After the one plain telling (`false`) she rates her option
`true` at 1 and `false` at 0, whatever her view.  Under his conduct (`true`) she rates `true` at
`1 − 2x`, `x` her view of the matter, and `false` at 0.  She takes `true` either way.  On her
own view she rates `true` higher under both; with his view substituted she would, under his
conduct, rate `false` higher. -/

noncomputable def W4 : Problem Unit Bool Unit ℝ Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := {false}
  tells_nonempty := by simp
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun _ _ _ => 0
  his := fun _ _ => 1
  shown := fun _ _ _ => 1
  eval := fun k _ v a => if a then (if k then 1 - 2 * v () else 1) else 0
  act := fun _ _ => true
  act_mem := fun _ _ => by simp
  asked := fun _ => False

/-- His conduct in `W4` satisfies the definition with no tolerance: she knows his view, her
view is where the plain telling would leave it, and she takes what she herself rates higher. -/
theorem w4_legit : W4.Legit 0 0 0 true := by
  refine ⟨?_, Or.inl ?_, Or.inl ?_⟩
  · refine W4.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨i, -, hne, -⟩ := hn
    exact hne rfl
  · refine W4.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨t, -, i, -, hnb⟩ := hn
    exact hnb (by simp [Problem.BetweenViews, W4])
  · refine W4.wt_le_of_forall_not (fun ω hn => ?_) le_rfl
    obtain ⟨t, ht, s, ⟨b, -, hb⟩, hns⟩ := hn
    have ht' : t = false := by simpa [W4] using ht
    subst ht'
    have hs : s < 0 := by
      cases b <;> simp [Problem.rate, W4] at hb <;> linarith
    refine hns ⟨true, by simp [W4], ?_⟩
    simp [Problem.rate, W4]
    linarith

/-- **The assumption of `gap` that his conduct does not change how she evaluates is needed.**
In `W4` her evaluation differs between his conduct and the plain telling, and every other
hypothesis of `gap` holds: two options, nothing declined, the comparison under his conduct
`1 − 2x`, her view between on the one matter, and what she does more than `1/2` worse by his
views than under the plain telling.  None of the four items holds: she falls short of her own
rating neither under his conduct nor under the plain telling, she does not rate her options
within `1/2` of each other, and the one mistake the plain telling would leave has nothing to
offset it.  The outcome guarantee fails. -/
theorem w4_needs_same_evaluation :
    W4.eval false () ≠ W4.eval true () ∧
      W4.opts = {true, false} ∧ W4.declined = ∅ ∧
      (∀ v : Unit → ℝ, W4.eval true () v true - W4.eval true () v false =
        1 + ∑ i ∈ W4.matters, (-2) * v i) ∧
      (∀ i ∈ W4.matters, W4.BetweenViews 0 true false () i) ∧
      W4.Regrets (0 + 1 / 2) true () ∧ ¬ W4.Regrets 0 false () ∧
      ¬ W4.Short (1 / 2) true () ∧ ¬ W4.Short (1 / 2) false () ∧
      ¬ |W4.rate true () ∅ true - W4.rate true () ∅ false| ≤ 1 / 2 ∧
      ¬ W4.Offsetting (fun _ => -2) false () ∧
      ¬ W4.Outcome (1 / 2) (1 / 2) true := by
  have hr : W4.Regrets (0 + 1 / 2) true () := by
    refine ⟨false, by simp [W4], ?_⟩
    simp [Problem.rate, Problem.live, W4]
    norm_num
  have hnr : ¬ W4.Regrets 0 false () := by
    rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, Problem.live, W4] at hb
    linarith
  refine ⟨fun h => ?_, rfl, rfl, fun v => by simp [W4]; ring, fun i _ => by
    simp [Problem.BetweenViews, W4], hr, hnr, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := congrFun (congrFun h (fun _ => 1)) true
    simp [W4] at h1
    norm_num at h1
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, W4] at hb <;> linarith
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, W4] at hb <;> linarith
  · simp [Problem.rate, W4]
    norm_num [abs_le]
  · rintro ⟨-, j, -, hj⟩
    simp [W4] at hj
    linarith
  · rintro (h | h)
    · have hw : W4.WorseByHim (1 / 2) true () := ⟨false, by simp [W4], 0, hr, hnr⟩
      rw [wt_unit_of W4 hw] at h
      norm_num at h
    · exact h

end Witness

end Workspace.Deference.Contrib.LegitimacyPlainTelling

#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.rate_empty
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.rate_of_agree
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.wt_mono
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.wt_or_le
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.wt_false
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.wt_le_of_forall_not
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.short_mono
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.regrets_mono
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.between_of_same_views
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.legit_only_telling
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.LegitW.mono
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.not_legit_of_hidden
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.not_legit_of_astray
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.not_legit_of_worse
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.chooses_as_informed
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.gain_le
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.bridge
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.short_sub
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.outcome_of_views
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.between_scale
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.weighing_of_beliefs
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.gap
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.between_scale_tol
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.between_scale_tol_neg
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.weighing_of_beliefs_tol
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.gap_in_weights
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Problem.rate_diff
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.avg_le_const
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.avg_affine
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.avg_mono
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.long_run
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.signal_le_of_noSignal
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.under_of_noShift
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.over_of_noShift
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.long_run_informed
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.rate_go
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.rate_stop
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.not_led_astray
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.rate_live_eq
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.rateAs_eq
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Course.not_led_astray_of_legit
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.needs_forecast
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.long_run_not_led_astray
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.own_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.informed_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.wt_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.short_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.regrets_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.hidden_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.worseByHim_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.worse_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.legit_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.not_open_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.not_outcome_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.not_will_W
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.same_as_telling
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.keeps_her_view
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.hidden_fails
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.worse_by_him_fails
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.for_her_own_good
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.pressed
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.pressed_asked
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.weak_anyway
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.mood_timing
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.mood_cannot_wait
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.between_W2
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_keeps_her_view
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_part_way
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_overshoot
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_for_her_good_by_distortion
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_mood
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_tips_an_even_choice
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w3_correcting_one_of_two
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.wt_unit_of
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.weighing_instance
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.gap_instance
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.gap_instance_offsetting
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w3_legit_and_worse
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w2_tips_legit_and_worse
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.gap_in_weights_instance
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w4_legit
#print axioms Workspace.Deference.Contrib.LegitimacyPlainTelling.Witness.w4_needs_same_evaluation
