import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# `udt-bli-learning` · Omu: open-minded updatelessness on a finite awareness-growth model of
Chicken — EA-OMU, awareness-growth exploitability, UE-OMU, and the b.333 check (T7)

**Scope: a finite awareness-growth model with one growth point.** Adversary types `Θ = {bestResponder,
unconditional}`; awareness chain `H₀ = {bestResponder} ⊆ H₁ = Θ`; a *given* prior `μ₁` on `H₁` with
`μ₁(unconditional) = u` (the post does not derive it; neither do we). Chicken with `straight = true`,
`swerve = false` and payoffs `crash < lose < tie < win` (`Payoffs`). Bob moves first *and predicts
Alice perfectly*: his type is a function of Alice's **policy** (M2, `bobMove`: the best responder
picks the move maximizing his payoff against her response, swerving on a tie — disclosed; the
unconditional type goes straight). Alice has one decision node, *after* observing Bob's move; the
growth point is that observation: "if Alice sees Bob coming on straight, then Alice conceives of a
new possibility". Since she has not acted before the growth point, every policy is *available*
(the post's "consistent with the actions the agent actually did so far").

Definitions as the post (b.309–333): `EU0` (the time-0 value under `H₀`), `EU1 u` (the value under
the open-minded prior on `H₁`), `EAOMU_acceptable u σ` (optimal among available policies judged
from the hypothetical time-0 state with the new prior), `Exploitable u` (the best responder's
optimal move against an EA-OMU Alice triggers growth, and every post-growth optimal policy does
strictly worse against the best responder than every pre-growth optimal one, both evaluated in the
new state), `UEOMU_acceptable u σ` (EA-OMU unless exploitable, then pre-growth acceptable).

* **The threshold** `thr = (win − lose)/(win − crash) ∈ (0, 1)`: `eaomu_swerves_of_gt` — for
  `u > thr` every EA-OMU-acceptable policy swerves on seeing Bob straight; `eaomu_straight_of_lt` —
  for `u < thr` the unique EA-OMU-acceptable policy is "always straight"; ties at `u = thr`
  (`eaomu_acceptable_swerveOnStraight`, `eaomu_acceptable_alwaysStraight`, both at `thr`).
* **Exploitability** (`exploitable_of_gt`, **P**, the Chicken witness N+): for `u > thr` rational
  Bob's best response to the EA-OMU Alice is straight (the growth trigger), Alice's post-growth
  value against him is `lose < win`, and Bob gains `win > lose` by "behaving like crazy Bob"; for
  `u < thr` not exploitable (`not_exploitable_of_lt`). Growth is possible (`growth_possible`).
* **UE-OMU** (`ueomu_of_gt`): above the threshold UE-OMU goes straight (the pre-growth policy);
  below it UE-OMU and EA-OMU agree (`ueomu_of_lt`).
* **The b.333 check.** (M1) `bobMoveAct`: Bob's type sees Alice's *action*, and her policy is a
  plain move chosen *without observing Bob* — so **M1 has no awareness-growth point** ("Alice sees
  Bob coming on straight" is not an observation she acts on), `Exploitable` and `posteriorUnc` are
  not defined for it, and `eaomuAct_swerve_iff` is the ex-ante threshold of a one-shot game: EA-OMU
  swerves iff `u > thr`, the same threshold as M2 (`eaomu_models_agree` is agreement on the
  threshold only). The b.333 scenario itself is posed in M2 only: an *updateful* Alice (choosing
  after seeing Bob straight) swerves for every `u` (`updateful_swerves`: `crash < lose`), and the
  posterior on `unconditional` given "Bob straight" under the pre-growth policy is `1` for every
  `u > 0` (`posterior_straight`). So the case b.333 describes — "would not swerve just because
  crazy-Bob is a possibility (too improbable), but would overall choose to swerve now due to
  sane-Bob imitating crazy-Bob" — is exactly the updateful agent's; **EA-OMU does not swerve below
  the threshold** (`b333_verdict`), because it evaluates policies ex ante by the open-minded
  prior, never by the posterior. The claim "this is already the case for EAOMU" holds in M2, and
  M1 agrees on the threshold (ATTRIBUTION-UNVETTED on what was meant). The mandate's third
  variant — "Bob's type sees Alice's action *inside* the observe-then-act game" — is not a third
  model: her action there is `σ (bobMove …)`, and a Bob conditioning on it compares
  `payoff true (σ true)` with `payoff false (σ false)`, which is `bobMove` itself
  (`bobMoveObs_eq_bobMove`); so the two coherent models are M2 and the one-shot M1, both built
  (repair round 2, audit r2 adversarial N5 / fidelity N8).
* Numeric instance `inst` (`crash, win, lose, tie = −10, 1, −1, 0`): `thr = 2/11`; at `u = 1/2`
  EA-OMU swerves and is exploitable, at `u = 1/10` it goes straight (`inst_facts`).

Recorded, not formalized: "available" under *unobserved* own moves (b.315–316) — ill-posed as the
post says; here every own move is observed and none precedes the growth point.

Sources: bli-paper-2-011 (`udt-tiling-working-notes-2025-06-30` b.309–333; the third-party
definitions quoted at journal 2023-09-27 ll. 39–64); mandate T7.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.Omu

/-! ## The model -/

/-- **Bob's types**: the best responder (predicts Alice, maximizes his payoff) and the
unconditional ("crazy") Bob who goes straight no matter what.
Source: bli-paper-2-011 b.319–321 ("Bob takes the expectation-maximizing response to Alice's
policy"; "Bob is crazy and just goes straight no matter what")
Kind: D
Fidelity: exact -/
inductive BobType
  | bestResponder
  | unconditional
  deriving DecidableEq

/-- **Chicken payoffs** for the row player: `crash` (both straight) `< lose` (I swerve, you go
straight) `< tie` (both swerve) `< win` (I go straight, you swerve).
Source: bli-paper-2-011 b.319 ("Game of chicken"); mandate T7 ("crash worst")
Kind: D
Fidelity: exact (symmetric payoffs) -/
structure Payoffs where
  /-- Both straight. -/
  crash : ℚ
  /-- I go straight, the other swerves. -/
  win : ℚ
  /-- I swerve, the other goes straight. -/
  lose : ℚ
  /-- Both swerve. -/
  tie : ℚ
  /-- Crash is worst. -/
  crash_lt_lose : crash < lose
  /-- Losing is worse than tying. -/
  lose_lt_tie : lose < tie
  /-- Tying is worse than winning. -/
  tie_lt_win : tie < win

variable (P : Payoffs)

/-- The row player's payoff from `me` against `other` (`straight = true`).
Source: bli-paper-2-011 b.319
Kind: D
Fidelity: exact -/
def payoff (me other : Bool) : ℚ :=
  match me, other with
  | true, true => P.crash
  | true, false => P.win
  | false, true => P.lose
  | false, false => P.tie

/-- **Alice's policy**: her move as a function of the observed move of Bob.
Source: bli-paper-2-011 b.319 ("Bob moves before Alice"); mandate T7 ("Alice's policy at one node
plus the observe-Bob-then-act growth point")
Kind: D
Fidelity: exact -/
abbrev AlicePolicy := Bool → Bool

/-- **(M2) Bob's move as a function of his type and Alice's policy**: the best responder goes
straight iff that strictly beats swerving against Alice's responses (swerves on a tie — this
run's tie-break, disclosed); the unconditional Bob goes straight.
Source: bli-paper-2-011 b.319–321; mandate T7 (M2: "Bob's type sees her *policy*")
Kind: D
Fidelity: exact (tie-break disclosed) -/
def bobMove : BobType → AlicePolicy → Bool
  | .unconditional, _ => true
  | .bestResponder, σ => decide (payoff P false (σ false) < payoff P true (σ true))

/-- **The mandate's third variant is M2**: a best-responder Bob who conditions on Alice's
*realized action inside the observe-then-act game* — her response `σ true` if he goes straight,
`σ false` if he swerves — compares `payoff true (σ true)` with `payoff false (σ false)`, which is
`bobMove`'s comparison. "Bob's type sees Alice's action" and "sees her policy" coincide once her
action is a function of his move; the one-shot `bobMoveAct` (M1), where her move is chosen without
observing him, is the only genuinely different model (audit r2 adversarial N5 / fidelity N8).
Source: mandate T7 (M1 "inside the observe-then-act game"); audit r2 adversarial N5
Kind: D
Fidelity: n/a -/
def bobMoveObs (σ : AlicePolicy) : Bool := decide (payoff P false (σ false) < payoff P true (σ true))

/-- `bobMoveObs` is `bobMove .bestResponder`, definitionally: the "third model" is M2.
Source: mandate T7; audit r2 adversarial N5
Kind: L
Fidelity: n/a -/
theorem bobMoveObs_eq_bobMove (σ : AlicePolicy) : bobMoveObs P σ = bobMove P .bestResponder σ :=
  rfl

/-- **Alice's realized payoff** against type `θ` under policy `σ`.
Source: bli-paper-2-011 b.319
Kind: D
Fidelity: exact -/
def outcome (θ : BobType) (σ : AlicePolicy) : ℚ :=
  payoff P (σ (bobMove P θ σ)) (bobMove P θ σ)

/-- **The time-0 value under `H₀ = {bestResponder}`**.
Source: bli-paper-2-011 b.319 ("Alice initially has one hypothesis")
Kind: D
Fidelity: exact -/
def EU0 (σ : AlicePolicy) : ℚ := outcome P .bestResponder σ

/-- **The value under the open-minded prior on `H₁`** with `μ₁(unconditional) = u` (given, not
derived).
Source: bli-paper-2-011 b.311 ("open-minded priors"), b.320 ("if Alice weighs the new possibility
sufficiently highly in her (new) prior")
Kind: D
Fidelity: exact (`μ₁` given) -/
def EU1 (u : ℚ) (σ : AlicePolicy) : ℚ :=
  (1 - u) * outcome P .bestResponder σ + u * outcome P .unconditional σ

/-- Always straight.
Source: bli-paper-2-011 b.319 ("Alice initially expects to go straight")
Kind: D
Fidelity: exact -/
def alwaysStraight : AlicePolicy := fun _ => true

/-- Swerve iff Bob goes straight.
Source: bli-paper-2-011 b.320 ("Alice will choose to swerve")
Kind: D
Fidelity: exact -/
def swerveOnStraight : AlicePolicy := fun b => !b

/-- **"Swerves"**: the policy swerves on seeing Bob straight.
Source: bli-paper-2-011 b.320
Kind: D
Fidelity: exact -/
def Swerves (σ : AlicePolicy) : Prop := σ true = false

/-! ## The outcomes -/

/-- **Alice's payoff against the best responder**: `win` if she always goes straight, `tie` if she
mirrors Bob, `lose` if she swerves on straight (Bob then goes straight).
Source: none: infrastructure (the game's computation)
Kind: L
Fidelity: n/a -/
theorem outcome_br (σ : AlicePolicy) :
    outcome P .bestResponder σ =
      if σ true then (if σ false then P.win else P.tie) else P.lose := by
  have hcl := P.crash_lt_lose
  have hlt := P.lose_lt_tie
  have htw := P.tie_lt_win
  unfold outcome
  simp only [bobMove]
  cases h1 : σ true <;> cases h2 : σ false
  · -- swerve on straight, swerve on swerve: Bob compares `tie` (swerve) with `win` (straight)
    rw [show decide (payoff P false false < payoff P true false) = true from
      decide_eq_true (by simp only [payoff]; exact htw)]
    simp [h1, payoff]
  · -- swerve on straight, straight on swerve: Bob compares `lose` with `win`
    rw [show decide (payoff P false true < payoff P true false) = true from
      decide_eq_true (by simp only [payoff]; linarith)]
    simp [h1, payoff]
  · -- mirror: Bob compares `tie` (swerve) with `crash` (straight)
    rw [show decide (payoff P false false < payoff P true true) = false from
      decide_eq_false (by simp only [payoff]; linarith)]
    simp [h2, payoff]
  · -- always straight: Bob compares `lose` (swerve) with `crash` (straight)
    rw [show decide (payoff P false true < payoff P true true) = false from
      decide_eq_false (by simp only [payoff]; linarith)]
    simp [h2, payoff]

/-- **Alice's payoff against the unconditional Bob**: `crash` if she goes straight on straight,
`lose` if she swerves on straight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem outcome_unc (σ : AlicePolicy) :
    outcome P .unconditional σ = if σ true then P.crash else P.lose := by
  unfold outcome
  simp only [bobMove]
  cases σ true <;> simp [payoff]

/-- `EU1` in closed form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem EU1_eq (u : ℚ) (σ : AlicePolicy) :
    EU1 P u σ = if σ true then (if σ false then (1 - u) * P.win + u * P.crash
      else (1 - u) * P.tie + u * P.crash) else P.lose := by
  unfold EU1
  rw [outcome_br, outcome_unc]
  cases h1 : σ true <;> cases h2 : σ false <;> simp <;> ring

/-! ## EA-OMU and the threshold -/

/-- **The threshold** `thr = (win − lose)/(win − crash)`: EA-OMU swerves iff `μ₁(unconditional)`
exceeds it.
Source: bli-paper-2-011 b.320 ("sufficiently highly"); mandate T7 ("compute it")
Kind: D
Fidelity: exact -/
def thr : ℚ := (P.win - P.lose) / (P.win - P.crash)

/-- `0 < thr < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem thr_bounds : 0 < thr P ∧ thr P < 1 := by
  have hcl := P.crash_lt_lose
  have hlt := P.lose_lt_tie
  have htw := P.tie_lt_win
  have hwc : 0 < P.win - P.crash := by linarith
  unfold thr
  constructor
  · apply div_pos _ hwc; linarith
  · rw [div_lt_one hwc]; linarith

/-- **EA-OMU acceptable** at the growth point: optimal among the (all available) policies, judged
from the hypothetical time-0 state with the open-minded prior.
Source: bli-paper-2-011 b.310–312 ("begins to follow the optimal policy among the available ones,
judged from the (hypothetical) time 0 epistemic state")
Kind: D
Fidelity: exact (every policy available: no own move precedes the growth point) -/
def EAOMU_acceptable (u : ℚ) (σ : AlicePolicy) : Prop := ∀ σ', EU1 P u σ' ≤ EU1 P u σ

/-- The straight-on-straight value is below `lose` iff `u > thr` (for `u ≤ 1`, with the better
`σ false = true`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma straight_value_lt_lose_iff (u : ℚ) :
    (1 - u) * P.win + u * P.crash < P.lose ↔ thr P < u := by
  have hwc : 0 < P.win - P.crash := by linarith [P.crash_lt_lose, P.lose_lt_tie, P.tie_lt_win]
  unfold thr
  rw [div_lt_iff₀ hwc]
  constructor <;> intro h <;> nlinarith

/-- **Above the threshold EA-OMU swerves**: for `thr < u ≤ 1`, every EA-OMU-acceptable policy
swerves on seeing Bob straight.
Source: bli-paper-2-011 b.320 ("If Alice weighs the new possibility sufficiently highly in her
(new) prior, then Alice will choose to swerve"); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) `thr < u ≤ 1` -/
theorem eaomu_swerves_of_gt {u : ℚ} (hu : thr P < u) (hu1 : u ≤ 1) (σ : AlicePolicy)
    (h : EAOMU_acceptable P u σ) : Swerves σ := by
  have htw := P.tie_lt_win
  have hlt := (straight_value_lt_lose_iff P u).mpr hu
  unfold Swerves
  by_contra hne
  have h1 : σ true = true := by cases hσ : σ true; exact absurd hσ hne; rfl
  have hσ' := h swerveOnStraight
  rw [EU1_eq, EU1_eq] at hσ'
  simp only [swerveOnStraight, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h1] at hσ'
  have hu0 : 0 ≤ 1 - u := by linarith
  cases h2 : σ false
  · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hσ'
    have : (1 - u) * P.tie ≤ (1 - u) * P.win := mul_le_mul_of_nonneg_left htw.le hu0
    linarith
  · simp only [h2, ↓reduceIte] at hσ'
    linarith

/-- **Below the threshold EA-OMU goes straight**: for `u < thr`, every EA-OMU-acceptable
policy is "always straight".
Source: bli-paper-2-011 b.320 (the contrapositive: not sufficiently weighted, no swerve); mandate
T7
Kind: P
Fidelity: exact
Hyps: (a) `u < thr`; no `0 ≤ u` is needed (the inequality holds for `u < 0` too, where `EU1` is
no longer a mixture — the "prior" reading is `0 ≤ u ≤ 1`) -/
theorem eaomu_straight_of_lt {u : ℚ} (hu : u < thr P) (σ : AlicePolicy)
    (h : EAOMU_acceptable P u σ) : σ true = true ∧ σ false = true := by
  have htw := P.tie_lt_win
  have hu1 : u < 1 := lt_trans hu (thr_bounds P).2
  have hgt : P.lose < (1 - u) * P.win + u * P.crash := by
    have hwc : 0 < P.win - P.crash := by linarith [P.crash_lt_lose, P.lose_lt_tie]
    unfold thr at hu
    rw [lt_div_iff₀ hwc] at hu
    nlinarith
  have hσ' := h alwaysStraight
  rw [EU1_eq, EU1_eq] at hσ'
  simp only [alwaysStraight, ↓reduceIte] at hσ'
  have hpos : 0 < 1 - u := by linarith
  cases h1 : σ true <;> cases h2 : σ false
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hσ'; linarith
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hσ'; linarith
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hσ'
    have : (1 - u) * P.tie < (1 - u) * P.win := mul_lt_mul_of_pos_left htw hpos
    linarith
  · exact ⟨rfl, rfl⟩

/-- **Swerve-on-straight is EA-OMU-acceptable at and above the threshold** (ties at `u = thr`).
Source: bli-paper-2-011 b.320; mandate T7 ("ties at the threshold")
Kind: N+
Fidelity: exact
Hyps: (a) `thr ≤ u ≤ 1` -/
theorem eaomu_acceptable_swerveOnStraight {u : ℚ} (hu : thr P ≤ u) (hu1 : u ≤ 1) :
    EAOMU_acceptable P u swerveOnStraight := by
  have htw := P.tie_lt_win
  have hwc : 0 < P.win - P.crash := by linarith [P.crash_lt_lose, P.lose_lt_tie]
  have hle : (1 - u) * P.win + u * P.crash ≤ P.lose := by
    unfold thr at hu
    rw [div_le_iff₀ hwc] at hu
    nlinarith
  have hu0 : 0 ≤ 1 - u := by linarith
  intro σ'
  rw [EU1_eq, EU1_eq]
  simp only [swerveOnStraight, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h1 : σ' true <;> cases h2 : σ' false <;> simp
  · have : (1 - u) * P.tie ≤ (1 - u) * P.win := mul_le_mul_of_nonneg_left htw.le hu0
    linarith
  · exact hle

/-- **Always-straight is EA-OMU-acceptable at and below the threshold** (ties at `u = thr`).
Source: bli-paper-2-011 b.319–320; mandate T7
Kind: N+
Fidelity: exact
Hyps: (a) `u ≤ thr`; no `0 ≤ u` needed (the "prior" reading is `0 ≤ u ≤ 1`) -/
theorem eaomu_acceptable_alwaysStraight {u : ℚ} (hu : u ≤ thr P) :
    EAOMU_acceptable P u alwaysStraight := by
  have htw := P.tie_lt_win
  have hwc : 0 < P.win - P.crash := by linarith [P.crash_lt_lose, P.lose_lt_tie]
  have hge : P.lose ≤ (1 - u) * P.win + u * P.crash := by
    unfold thr at hu
    rw [le_div_iff₀ hwc] at hu
    nlinarith
  have hu1 : u ≤ 1 := hu.trans (thr_bounds P).2.le
  have hu0' : 0 ≤ 1 - u := by linarith
  intro σ'
  rw [EU1_eq, EU1_eq]
  simp only [alwaysStraight, ↓reduceIte]
  cases h1 : σ' true <;> cases h2 : σ' false <;> simp
  · exact hge
  · exact hge
  · have : (1 - u) * P.tie ≤ (1 - u) * P.win := mul_le_mul_of_nonneg_left htw.le hu0'
    linarith

/-! ## Awareness-growth exploitability and UE-OMU -/

/-- **Pre-growth acceptable**: optimal at time 0 under `H₀`.
Source: bli-paper-2-011 b.319
Kind: D
Fidelity: exact -/
def EU0_optimal (σ : AlicePolicy) : Prop := ∀ σ', EU0 P σ' ≤ EU0 P σ

/-- Pre-growth optimality is "always straight" (the unique maximum `win`).
Source: bli-paper-2-011 b.319 ("Alice initially expects to go straight, and hence, initially
expects Bob to swerve")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem EU0_optimal_iff (σ : AlicePolicy) : EU0_optimal P σ ↔ (σ true = true ∧ σ false = true) := by
  have hlt := P.lose_lt_tie
  have htw := P.tie_lt_win
  unfold EU0_optimal EU0
  constructor
  · intro h
    have := h alwaysStraight
    rw [outcome_br, outcome_br] at this
    simp only [alwaysStraight, ↓reduceIte] at this
    cases h1 : σ true <;> cases h2 : σ false <;> simp [h1, h2] at this ⊢ <;> linarith
  · rintro ⟨h1, h2⟩ σ'
    rw [outcome_br, outcome_br, h1, h2]
    simp only [↓reduceIte]
    cases σ' true <;> cases σ' false <;> simp <;> linarith

/-- **Awareness-growth exploitability** (Alice's criterion, adversary type `bestResponder`): the
best responder's optimal move against every EA-OMU-acceptable policy is straight — the move that
grows Alice's awareness — and every post-growth acceptable policy yields strictly lower value
against the best responder than every pre-growth acceptable one (both evaluated in the new state,
i.e. as realized outcomes against that type).
Source: bli-paper-2-011 b.316–318 (the definition quoted at journal 2023-09-27 ll. 52–55)
Kind: D
Fidelity: exact (one growth point; "the optimal policy of that type increases awareness" read as
"Bob's best response to the post-growth Alice is the growth-triggering move") -/
def Exploitable (u : ℚ) : Prop :=
  (∀ σ, EAOMU_acceptable P u σ → bobMove P .bestResponder σ = true) ∧
  (∀ σpre σpost, EU0_optimal P σpre → EAOMU_acceptable P u σpost →
    outcome P .bestResponder σpost < outcome P .bestResponder σpre)

/-- Against a policy that swerves on straight, the best responder goes straight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bobMove_br_of_swerves (σ : AlicePolicy) (h : Swerves σ) : bobMove P .bestResponder σ = true := by
  simp only [bobMove]
  unfold Swerves at h
  rw [h]
  apply decide_eq_true
  cases h2 : σ false <;> simp only [payoff] <;> linarith [P.lose_lt_tie, P.tie_lt_win]

/-- **The Chicken witness (N+): above the threshold EA-OMU is exploitable**, and rational Bob gains
by behaving like crazy Bob: his payoff from going straight against the swerving Alice is `win`,
against the pre-growth straight Alice (where he swerves) `lose`. (The second conjunct `lose < win`
is the payoff structure's own ordering, recorded to name Bob's gain, not a result; the content is
`Exploitable P u`.)
Source: bli-paper-2-011 b.321–323 ("Rational-Bob can 'exploit' this by *behaving like crazy
Bob*; ie, going straight"); mandate T7 (Chicken witness)
Kind: P
Fidelity: exact
Hyps: (a) `thr < u ≤ 1` -/
theorem exploitable_of_gt {u : ℚ} (hu : thr P < u) (hu1 : u ≤ 1) :
    Exploitable P u ∧ payoff P false true < payoff P true false := by
  refine ⟨⟨fun σ h => bobMove_br_of_swerves P σ (eaomu_swerves_of_gt P hu hu1 σ h), ?_⟩, ?_⟩
  · intro σpre σpost hpre hpost
    obtain ⟨h1, h2⟩ := (EU0_optimal_iff P σpre).mp hpre
    have hs := eaomu_swerves_of_gt P hu hu1 σpost hpost
    rw [outcome_br, outcome_br, h1, h2, hs]
    simp only [↓reduceIte, Bool.false_eq_true]
    linarith [P.lose_lt_tie, P.tie_lt_win]
  · simp only [payoff]; linarith [P.lose_lt_tie, P.tie_lt_win]

/-- **Below the threshold EA-OMU is not exploitable**: the post-growth acceptable policy is the
pre-growth one, so no strict loss.
Source: bli-paper-2-011 b.316–318; mandate T7
Kind: P
Fidelity: exact
Hyps: (a) `u < thr`; no `0 ≤ u` needed (the "prior" reading is `0 ≤ u ≤ 1`) -/
theorem not_exploitable_of_lt {u : ℚ} (hu : u < thr P) : ¬ Exploitable P u := by
  rintro ⟨_, h⟩
  have := h alwaysStraight alwaysStraight ((EU0_optimal_iff P _).mpr ⟨rfl, rfl⟩)
    (eaomu_acceptable_alwaysStraight P hu.le)
  exact lt_irrefl _ this

/-- **Growth is possible**: the unconditional Bob goes straight against every policy, and the best
responder goes straight against swerve-on-straight (so "Alice sees Bob coming on straight" is a
reachable observation under both types) — the model has a growth point (mandate's trap: a model
with no possible growth makes exploitability vacuous).
Source: mandate T7 (traps)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem growth_possible :
    (∀ σ, bobMove P .unconditional σ = true) ∧ bobMove P .bestResponder swerveOnStraight = true :=
  ⟨fun _ => rfl, bobMove_br_of_swerves P _ rfl⟩

/-- **UE-OMU acceptable**: EA-OMU acceptable unless revising post-growth is exploitable, in which
case only pre-growth acceptable policies are.
Source: bli-paper-2-011 b.326–327 ("they find EA-OMU policies acceptable unless revising policy
post-awareness growth would make them exploitable, in which case the only acceptable policies are
those which were pre-growth acceptable")
Kind: D
Fidelity: exact -/
def UEOMU_acceptable (u : ℚ) (σ : AlicePolicy) : Prop :=
  (Exploitable P u → EU0_optimal P σ) ∧ (¬ Exploitable P u → EAOMU_acceptable P u σ)

/-- **Above the threshold UE-OMU goes straight** (the pre-growth policy), where EA-OMU swerves.
Source: bli-paper-2-011 b.326–328; mandate T7
Kind: C (`exploitable_of_gt`, `EU0_optimal_iff`)
Fidelity: exact
Hyps: (a) `thr < u ≤ 1` -/
theorem ueomu_of_gt {u : ℚ} (hu : thr P < u) (hu1 : u ≤ 1) (σ : AlicePolicy) :
    UEOMU_acceptable P u σ ↔ (σ true = true ∧ σ false = true) := by
  have hex := (exploitable_of_gt P hu hu1).1
  unfold UEOMU_acceptable
  rw [← EU0_optimal_iff]
  constructor
  · intro h; exact h.1 hex
  · intro h; exact ⟨fun _ => h, fun hn => absurd hex hn⟩

/-- **Below the threshold UE-OMU and EA-OMU agree** (both: always straight).
Source: bli-paper-2-011 b.326–328; mandate T7
Kind: C (`not_exploitable_of_lt`)
Fidelity: exact
Hyps: (a) `u < thr` -/
theorem ueomu_of_lt {u : ℚ} (hu : u < thr P) (σ : AlicePolicy) :
    UEOMU_acceptable P u σ ↔ EAOMU_acceptable P u σ := by
  have hne := not_exploitable_of_lt P hu
  unfold UEOMU_acceptable
  constructor
  · intro h; exact h.2 hne
  · intro h; exact ⟨fun he => absurd he hne, fun _ => h⟩

/-! ## The b.333 check: M1 (Bob sees Alice's action), the posterior, and the updateful agent -/

/-- **(M1) Bob's move as a function of his type and Alice's *action*** (her policy is a plain
move, chosen without observing Bob): the best responder goes straight iff that strictly beats
swerving against her move.
Source: mandate T7 (M1: "Bob's type sees Alice's action")
Kind: D
Fidelity: exact (tie-break: swerve) -/
def bobMoveAct : BobType → Bool → Bool
  | .unconditional, _ => true
  | .bestResponder, a => decide (payoff P false a < payoff P true a)

/-- Alice's realized payoff in M1.
Source: mandate T7 (M1)
Kind: D
Fidelity: exact -/
def outcomeAct (θ : BobType) (a : Bool) : ℚ := payoff P a (bobMoveAct P θ a)

/-- The value under the open-minded prior in M1.
Source: mandate T7 (M1)
Kind: D
Fidelity: exact -/
def EU1Act (u : ℚ) (a : Bool) : ℚ :=
  (1 - u) * outcomeAct P .bestResponder a + u * outcomeAct P .unconditional a

/-- M1 outcomes against the best responder: `win` for straight (he swerves), `lose` for swerve (he
goes straight).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem outcomeAct_br (a : Bool) : outcomeAct P .bestResponder a = if a then P.win else P.lose := by
  have hcl := P.crash_lt_lose
  have htw := P.tie_lt_win
  unfold outcomeAct
  simp only [bobMoveAct]
  cases a
  · rw [show decide (payoff P false false < payoff P true false) = true from
      decide_eq_true (by simp only [payoff]; exact htw)]
    simp [payoff]
  · rw [show decide (payoff P false true < payoff P true true) = false from
      decide_eq_false (by simp only [payoff]; linarith)]
    simp [payoff]

/-- M1 outcomes against the unconditional Bob.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem outcomeAct_unc (a : Bool) : outcomeAct P .unconditional a = if a then P.crash else P.lose := by
  unfold outcomeAct
  simp only [bobMoveAct]
  cases a <;> simp [payoff]

/-- **In M1 EA-OMU strictly prefers swerving iff `u > thr`** — the same threshold as in M2.
Source: mandate T7 (b.333 check, M1)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem eaomuAct_swerve_iff (u : ℚ) : EU1Act P u true < EU1Act P u false ↔ thr P < u := by
  unfold EU1Act
  rw [outcomeAct_br, outcomeAct_br, outcomeAct_unc, outcomeAct_unc]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [← straight_value_lt_lose_iff]
  constructor <;> intro h <;> linarith

/-- **The two models agree on the EA-OMU swerve verdict**: for `thr < u ≤ 1` both swerve, for
`0 ≤ u < thr` neither does.
Source: mandate T7 ("your theorem says which model makes it true")
Kind: C
Fidelity: exact
Hyps: (a) the stated bounds on `u` -/
theorem eaomu_models_agree (u : ℚ) :
    (thr P < u → u ≤ 1 → (∀ σ, EAOMU_acceptable P u σ → Swerves σ) ∧
      EU1Act P u true < EU1Act P u false) ∧
    (u < thr P → (∀ σ, EAOMU_acceptable P u σ → σ true = true) ∧
      ¬ EU1Act P u true < EU1Act P u false) :=
  ⟨fun hu hu1 => ⟨fun σ h => eaomu_swerves_of_gt P hu hu1 σ h, (eaomuAct_swerve_iff P u).mpr hu⟩,
    fun hu => ⟨fun σ h => (eaomu_straight_of_lt P hu σ h).1,
      fun h => absurd ((eaomuAct_swerve_iff P u).mp h) (not_lt.mpr hu.le)⟩⟩

/-- **The posterior on `unconditional` given "Bob straight"** under Alice's policy `σ`: Bayes with
the two types' moves as likelihoods (`0/1`). Junk `0` when neither type goes straight.
Source: mandate T7 (b.333: "the 'Bob went straight' posterior")
Kind: D
Fidelity: exact -/
def posteriorUnc (u : ℚ) (σ : AlicePolicy) : ℚ :=
  u * (if bobMove P .unconditional σ then 1 else 0) /
    ((1 - u) * (if bobMove P .bestResponder σ then 1 else 0) +
      u * (if bobMove P .unconditional σ then 1 else 0))

/-- **Under the pre-growth policy the posterior given "Bob straight" is `1`** for every `u > 0`
(the best responder would have swerved): the observation looks like crazy Bob even when it is sane
Bob imitating him.
Source: bli-paper-2-011 b.333 ("sane-bob imitating crazy-bob"); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) `0 < u` -/
theorem posterior_straight {u : ℚ} (hu : 0 < u) : posteriorUnc P u alwaysStraight = 1 := by
  have hbr : bobMove P .bestResponder alwaysStraight = false := by
    simp only [bobMove, alwaysStraight]
    apply decide_eq_false
    simp only [payoff]; linarith [P.crash_lt_lose]
  unfold posteriorUnc
  rw [hbr]
  simp only [bobMove, Bool.false_eq_true, ↓reduceIte, mul_one, mul_zero, zero_add]
  exact div_self (ne_of_gt hu)

/-- **The updateful Alice swerves on seeing Bob straight, for every prior**: against a Bob who is
going straight, swerving (`lose`) beats straight (`crash`), whatever his type and whatever the
posterior.
Source: bli-paper-2-011 b.333 ("would overall choose to swerve now, due to sane-bob imitating
crazy-bob"); mandate T7
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem updateful_swerves : payoff P true true < payoff P false true := by
  simp only [payoff]; exact P.crash_lt_lose

/-- **The b.333 verdict**: below the threshold — "Alice would not swerve just because crazy-Bob is
a possibility" — EA-OMU goes straight in both models, although the updateful agent swerves and the
posterior given "Bob straight" is `1`: the case b.333 describes is the updateful agent's, and
"this is already the case for EAOMU" holds in M1 and M2 alike (EA-OMU evaluates ex ante by the
open-minded prior, never by the posterior).
Source: bli-paper-2-011 b.333; mandate T7 (b.333 check)
Kind: C
Fidelity: exact (two models; ATTRIBUTION-UNVETTED on what was meant)
Hyps: (a) `0 < u < thr` -/
theorem b333_verdict {u : ℚ} (hu0 : 0 < u) (hu : u < thr P) :
    (∀ σ, EAOMU_acceptable P u σ → σ true = true) ∧
    ¬ EU1Act P u true < EU1Act P u false ∧
    posteriorUnc P u alwaysStraight = 1 ∧
    payoff P true true < payoff P false true :=
  ⟨fun σ h => (eaomu_straight_of_lt P hu σ h).1,
    fun h => absurd ((eaomuAct_swerve_iff P u).mp h) (not_lt.mpr hu.le),
    posterior_straight P hu0, updateful_swerves P⟩

/-! ## The numeric instance -/

/-- The instance `crash, win, lose, tie = −10, 1, −1, 0`.
Source: mandate T7 (Chicken witness)
Kind: D
Fidelity: exact -/
def inst : Payoffs where
  crash := -10
  win := 1
  lose := -1
  tie := 0
  crash_lt_lose := by norm_num
  lose_lt_tie := by norm_num
  tie_lt_win := by norm_num

/-- **The instance**: `thr = 2/11`; at `u = 1/2` every EA-OMU-acceptable policy swerves and EA-OMU
is exploitable; at `u = 1/10` every EA-OMU-acceptable policy goes straight.
Source: mandate T7 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem inst_facts :
    thr inst = 2 / 11 ∧
    (∀ σ, EAOMU_acceptable inst (1 / 2) σ → Swerves σ) ∧ Exploitable inst (1 / 2) ∧
    (∀ σ, EAOMU_acceptable inst (1 / 10) σ → σ true = true) := by
  have ht : thr inst = 2 / 11 := by unfold thr inst; norm_num
  refine ⟨ht, fun σ h => eaomu_swerves_of_gt inst (by rw [ht]; norm_num) (by norm_num) σ h,
    (exploitable_of_gt inst (by rw [ht]; norm_num) (by norm_num)).1,
    fun σ h => (eaomu_straight_of_lt inst (by rw [ht]; norm_num) σ h).1⟩

end Cleanroom.Bli.UdtBliLearning.Omu
