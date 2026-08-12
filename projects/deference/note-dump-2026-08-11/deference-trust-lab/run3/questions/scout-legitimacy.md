# Scout report — Lens: LEGITIMACY OF FEEDBACK (round 3)

*Scout agent, 2026-07-01. Deliverable of record for the legitimacy lens.*

## 0. Sources read and the state of the thread

Read in full: `notes/li-deference.md` (esp. §0.3), `deference-trust-lab/models/legitimacy-corrigibility-model.md`,
`deference-trust-lab/redteam/legitimacy-corrigibility-redteam.md`, `deference-trust-lab/lean/legitimacy.lean`,
`deference-trust-lab/lean/legitimacy-corrigibility.lean`, `deference-trust-lab/run2/todos/TODOS.md` (incl. the
GLOBAL OFF-LIMITS list), `deference-trust-lab/run2/brainstorm/real-gaps.md` §3, and
`deference-in-logical-induction-v6.md` §§4–6 (esp. §4.7, §5.9–§5.11, §6.3–§6.5, §8).

**Where the legitimacy thread stands.** li-deference.md §0.3 poses the open problem: the AI should
imitate human opinion only in *non-corrupted* futures; manipulation, self-fulfilling prophecy,
wireheading, and loss-of-control are corruption; "all the actual feedback it gets should be assumed
legitimate; the training process is predicated on its own non-corruption in the present"; Abram does
not yet know how to put this into the math. v6 §6.5 names the same as "the legitimacy program"
(replace "all futures" with "non-corrupt futures" in the target) and §8 lists it as open, along with
the manipulation theorem's four missing ingredients (§4.7: second calibration condition,
evidence/preemption, transfer-of-trust, **non-recoverability** — asserted, never proved).

Round 1 built a finite toy: legitimacy defect `defect_w = Σ π_x w_x (θ_x − Eθ_x)`, wirehead-decline
under a *pointwise global overstatement* hypothesis, and the corrigibility sign-flip. The round-1
red-team's verdict (SALVAGEABLE) found the two honest weaknesses that define where round 3 should
push:

1. **Finding 1 (euphoric-but-numb counterexample):** "reported utility rises" does NOT imply the
   defect goes negative; the theorem's real hypothesis is pointwise overstatement, which is stronger
   than the informal wirehead story. The red-team's named "single most valuable next step" —
   characterize which `E_drug` are actually caught by the model's own gate — was **never executed**
   (run 2 dropped the adjacent item "non-circular legitimacy" explicitly for disjointness, not
   because it was done).
2. **Circularity (run2 real-gaps §3):** round-1 legitimacy = LUV-Total-Trust is "only as contentful
   as truth-tracking ⇒ small defect", i.e. a rename of low defect, not an explanation of it. The
   sign hypotheses (`hover`, `hfire`) are *encodings*, not *derivations*.

Everything below takes the smallest honest formal step past one of those two seams, or past the
specific v6 §8 open items that belong to this lens (non-recoverability; the legitimacy target as a
conditioning operation). I checked each against run2's GLOBAL OFF-LIMITS list and the round-1 lab
Lean ban (`Legitimacy.*`, `LegitimacyCorrigibility.*` may not be re-skinned or relabeled).

**A recurring honesty rule for this lens** (worth stating once): in the finite shadow register,
"the principal can compute w" quantifies over functions on worlds. The *operationally available*
gates — what a real principal who cannot see θ pointwise can actually condition on — are the
**report-measurable** ones (functions of the process's own output). Several questions below get
their content precisely from that distinction; a proposal that silently hands the principal
world-measurable gates is the pre-registered fake for this whole lens.

---

## Q1 — The right wirehead hypothesis: an iff. Support-restricted overstatement is exactly what the weight class detects

**id:** `leg-wirehead-iff` · **modality:** LEAN-CORE · **difficulty:** easy–medium (one session)

**CLAIM (acceptance target).** In the finite frame (worlds `W`, prices `π ≥ 0`, target `θ`, report
`E : W → ℚ`), for any support set `S ⊆ W`:

> `defect_w(π, θ, E) ≤ 0` for **every** nonnegative weight `w` with `supp w ⊆ S`
> **iff** `θ_x ≤ E_x` at every `x ∈ S` with `π_x > 0`.

Both directions compiled in Lean 4 + Mathlib. Forward (necessity) via point-mass weights
`w = δ_x` — this is the direction round 1 never had. Backward is the support-localized sum argument.
Mandatory witnesses: (a) the red-team's euphoric-but-numb counterexample
(`θ=(1,0)`, `E=(19/20, 1/5)`, `π=(1/2,1/2)`) compiled: average report **rises** yet
`defect > 0` on the model's own gate `w = Ind(E > 1/2)` — certifying that "reported utility rises"
is NOT the detected class; (b) a strict-decline witness satisfying the S-restricted hypothesis with
`S ⊊ W` but violating the global one — certifying the localization is a real weakening of round 1's
`hover`. `#print axioms` clean; per-gate remark stated honestly (for a *single* fixed gate only the
aggregated inequality is equivalent, not the pointwise condition — the iff needs the full class).

**WHY.** This is verbatim the round-1 red-team's "single most valuable next step"
(`redteam/legitimacy-corrigibility-redteam.md`, final section): turn the smuggled-in global `hover`
into the *right* hypothesis, and connect to v2 §10.4's open "which operations are drugs". It
converts the model's central definition from a one-way sufficient condition into a
characterization: the weight class *is* the detector, and this says exactly what it detects.

**NOVELTY RISK.** Directly adjacent to OFF-LIMITS `Legitimacy.drug_defect_sign` /
`LegitimacyCorrigibility.wirehead_declined`. Not a duplicate because: those prove ONLY sufficiency,
ONLY with `S = W`; the converse (necessity via point masses), the support-localization, and the two
compiled discriminating witnesses are all absent from round 1, and run 2 dropped the adjacent
candidate unexecuted (TODOS.md "DROPPED: Non-circular legitimacy"). **Shadow test:** fake = re-proving
sufficiency under a renamed hypothesis (that IS `wirehead_declined`); real = the ⟸ AND ⟹ pair with
the euphoric-but-numb near-miss compiled and the `S ⊊ W` weakening witnessed.

---

## Q2 — The detection hierarchy: report-measurable gates see exactly miscalibration; calibrated corruption is provably invisible yet strictly harmful

**id:** `leg-detection-hierarchy` · **modality:** LEAN-CORE · **difficulty:** medium (one session)

**CLAIM (acceptance target).** Three compiled finite-frame theorems about *which gates can see which
corruptions*, plus one coexistence witness:

1. **(Report-gates = calibration.)** For report-measurable weights `w = v ∘ E`:
   `defect_{v∘E} = Σ_e v(e) · π({E = e}) · (E_π[θ | E = e] − e)`. Hence `defect = 0` for ALL
   report-measurable gates **iff** `E` is calibrated (`E_π[θ | E = e] = e` on every positive-mass
   report value). Pure projection/tower algebra, but the identity is new to the corpus.
2. **(World-gates = pointwise truth.)** `defect = 0` for all world-measurable nonneg gates iff
   `θ = E` π-a.e. (the `S = W` instance of Q1; cite Q1 if it lands first, else prove the two-line
   version — coordination note for the consolidator).
3. **(The gap is real and harmful.)** Exhibit a **calibrated garbling**: a signal map `s : W → Σ`
   and `E := E_π[θ | s]`, so by (1) every report-measurable defect is exactly 0 — the entire
   round-1 endorsement apparatus, run on operationally available gates, certifies this process
   legitimate — while on an explicit finite menu the principal's argmax-following **Value strictly
   drops** relative to the ungarbled report (`norm_num` on explicit rationals), and a
   world-measurable witness gate (`w = θ − E` clipped nonneg, or its two-sided pair) has
   `defect ≠ 0`.

**WHY.** This is the honest formal content of §0.3's "numbing drug" direction, and the finite shadow
of v6 §6.3's central limitation ("checking calibration on everything you *can* check gives no
guarantee about what you *cannot*"). It proves a *limit of the round-1 legitimacy definition* from
inside its own formalism: legitimacy-as-zero-defect is exactly as strong as the gate class, and the
class a real principal has (report-measurable) provably cannot see information-destroying
corruption. That reframes the legitimacy program: the missing ingredient is not a better defect but
a better *access class* — matching v6 §4.7's "second calibration condition separating
calibration-to-self from calibration-to-truth".

**NOVELTY RISK.** (a) run2 TODO 2 `negative-voi` (established): that result is
Value(refined) < Value(coarse) under NON-partitional frames — a different phenomenon; here the
comparison is coarse-vs-fine under honest conditioning (Blackwell direction) and the headline is the
**coexistence** defect-blind ∧ Value-drop, an object absent from run 2. Cite negative-voi's
partitional near-miss rather than re-prove monotonicity in general. (b) OFF-LIMITS
`value_of_CM`/`Deference.*` linearity — theorem 1's identity must be proved as the *conditional-mean
regrouping*, not by relabeling `decomposition`. **Shadow test:** fake = defect-zero shown only for
one hand-picked gate (not the class), or a "Value drop" from adversarially chosen tie-breaking; real
= the class-level iff in (1), argmax with an explicit declared tie-rule, and both discriminating
witnesses compiled.

---

## Q3 — Derive the defect sign from an update rule: likelihood-exaggeration is a drug, theorem not stipulation

**id:** `leg-derived-sign` · **modality:** MIXED (EXEC sweep + LEAN-CORE sign lemma) · **difficulty:** medium (one session)

**CLAIM (acceptance target).** A corruption model over the *belief-formation process*, with the
overstatement DERIVED. Binary target `θ ∈ {0,1}`, worlds = (θ, signal) pairs with joint prior `π`,
honest report = Bayes posterior `p(s)`; corrupted report = the **λ-exaggerated** posterior `q_λ(s)`
(posterior odds = prior odds × likelihood-ratio^λ; integer `λ` suffices for the Lean). Prove:

1. **(Sign lemma, Lean.)** For `λ > 1`: `q_λ(s) > p(s)` exactly where the likelihood ratio exceeds 1
   (equivalently `p(s) >` prior), and `q_λ(s) < p(s)` where it is below — overconfidence overstates
   precisely on the favorable-signal region.
2. **(Defect, derived.)** Hence for any report-gate at threshold `t ≥` prior,
   `defect_{Ind(q_λ > t)} < 0` given positive mass on the fired region — the wirehead-decline
   conclusion with the update rule `λ > 1` as the ONLY corruption hypothesis. The overshoot that
   round 1 assumed (`hover`) is here a **lemma**.
3. **(Near-misses, mandatory.)** `λ = 1` gives defect ≡ 0 on all report-gates (honest Bayes is
   calibrated — ties to Q2(1)); `λ < 1` (numbing/underconfidence) FLIPS the sign on the same gate.
   EXEC: exact-rational sweep over (prior, likelihoods, λ, t) confirming the sign regions and
   locating the boundary.

**WHY.** This is run2 real-gaps §3a — the named fix for the circularity ("the headline hypothesis is
the update rule, not the overshoot") — dropped in round 2 for list-disjointness and never executed.
It is the first artifact in the corpus where "this process is corrupt" is a *mechanistic* property
(how it updates) and "the principal's detector fires with the adverse sign" is the *conclusion*.
li-deference.md §0.3's drug analogy becomes a theorem schema: exaggeration-type drugs are declined;
numbing-type drugs are (per Q2) invisible to the same detector — the two lenses agree on where the
boundary is.

**NOVELTY RISK.** OFF-LIMITS `drug_defect_sign`/`wirehead_declined` assume the overshoot — the
pre-registered fake here is any proof where a pointwise `θ ≤ E` (or `p ≤ q`) hypothesis appears in
the headline theorem. Real = `λ > 1` is the hypothesis, the overstatement region is derived, and the
λ<1 flip compiles. No known prior artifact (run1, run2, lean-deference) derives a defect sign from
an update rule.

---

## Q4 — Predicting-through-legitimate-futures as a conditioning operation: the legitimacy-gated faithful-acceleration theorem, and the timeliness obstruction

**id:** `leg-gated-acceleration` · **modality:** MIXED (paper-math + standalone Lean of the weighted chain) · **difficulty:** medium–hard (one focused session for the honest core)

**CLAIM (acceptance target).** Take v6 §5.9's faithful-acceleration theorem (bounded ε-violation
Total Trust: `Σ_n w_n < ∞` for `w_n = Ind_δ(a_n > t)·Ind_δ(E^H_n(X) < t−ε)`) and insert a
**legitimacy gate** `ℓ_n ∈ [0,1]`, proving the gated form and locating exactly what the gate must
be:

1. **(Positive.)** If `ℓ_n` is generable by day `n` (computable from the market state when the
   trader must act) and ingredient (II) (Expectation Unbiasedness From Feedback) holds **on the
   ℓ-weighted patient weights only**, then `Σ_n ℓ_n · w_n < ∞`: bounded ε-violation Total Trust *on
   the legitimacy-flagged subsequence*, hence classwise Value on menus gated by ℓ. The Lean
   deliverable is a STANDALONE weighted version of the arithmetic chain
   (`round_profit_ge → … → soft_total_trust` with the extra factor), with calibration and the
   criterion as named hypotheses exactly as `FaithfulAcceleration.lean` does — plus a non-vacuity
   witness where `ℓ` is a nontrivial 0/1/interior mixture.
2. **(The timeliness obstruction — the new finding.)** Prove/argue that a *retrospective* gate
   (ℓ_n decided only at feedback time σ(n), e.g. "the feedback later turned out uncorrupted") is
   NOT implementable by the day-n trader, so the theorem CANNOT be stated with ground-truth
   legitimacy — only with the *predicted-legitimacy* gate (the market's own day-n belief about
   corruption). State the corollary in §0.3's own words: "the AI should only be trying to predict
   non-corrupt cases" is forced to mean *cases it currently believes non-corrupt* — the
   conditioning operation is available only through present beliefs about legitimacy, never through
   legitimacy itself.
3. **(Silence corollary, stated with quantifiers.)** On days `ℓ_n ≈ 0` there is NO forcing: the
   gate removes protection exactly where it removes obligation (the §5.8 silence property inherited
   by the legitimacy program), so a corrupted gate (ℓ stuck at 0 on good days / 1 on corrupt days)
   converts the safety feature into a vacuous theorem — which is Q6's circularity, met here from
   the positive side.

**WHY.** This is the first step that puts §0.3 into the *actual LI mathematics* rather than the
finite shadow: "imitate human opinion only in non-corrupted futures" literally becomes "multiply
the violation weight by ℓ_n", and the theorem tells you the price (calibration needed only on the
gated class; forcing lost off it; the gate must be timely). v6 §6.5 says the program is "pushing the
forced-soundness boundary outward past raw timely-checkability" — this locates exactly which
boundary term moves and which cannot.

**NOVELTY RISK.** The serious one: `FaithfulAcceleration.lean` and v6 §5.9 are ESTABLISHED and the
weighted chain re-uses their skeleton — a lazy execution is a re-skin. The claim is honest only if
(a) the gate appears as a separate factor with its own generability side-condition doing visible
work (the near-miss: dropping generability breaks the trader's legality — shown, not asserted),
(b) the calibration hypothesis is weakened to the gated class (a genuinely weaker antecedent, to be
stated and used), and (c) findings 2–3 are delivered as such. **Shadow test:** fake = renaming
`w_n` to `ℓ_n·w_n` with hypotheses untouched; real = weaker antecedent + the timeliness obstruction
with a concrete non-implementable gate + the silence quantifiers. Hypothesis-laundering check: the
target (gated Total Trust) is the conclusion; ℓ is a free modeling input, flagged as such.

---

## Q5 — Does conditioning kill the corruption incentive? Compute it: wirehead out, within-gate steering still in

**id:** `leg-incentive-audit` · **modality:** EXEC (Python, exact rationals) · **difficulty:** medium (one session)

**CLAIM (acceptance target).** A minimal two-period decision model where the incentive signs are
COMPUTED from a proper scoring rule, not chosen. AI action `a ∈ {honest, wirehead, steer}`; a
feedback channel with an explicit corruption semantics (wirehead ⇒ future feedback reports high-θ
independent of θ; steer ⇒ future *legitimate* opinion is moved by a legitimate-looking message);
legitimacy event `L` excluding the corrupted branch; AI's objective = expected proper score (Brier
and log, both) of its prediction against (i) all-futures feedback `J_all`, (ii) L-conditioned
feedback `J_L` (the §0.3 proposal). Deliverables, all exact rationals with asserts:

1. `J_all(wirehead) > J_all(honest)`: the unconditioned objective rewards wireheading (the baseline
   pathology reproduced inside the model, not assumed).
2. `J_L(wirehead) < J_L(honest)`: conditioning strictly removes it — and the mechanism is checked
   to be §0.3's "blocking the channel only deprives it of information" (the wirehead branch
   contributes nothing to `J_L`, and the corrupted action degrades prediction on the surviving
   branch).
3. `J_L(steer) > J_L(honest)` for an open parameter region: steering *within* legitimate futures —
   manipulating which legitimate opinion obtains, so it is later confirmed — is STILL incentivized
   under the conditioned objective. Sweep the corruption/steering parameters and report the region
   boundaries where each sign flips.

**WHY.** §0.3 says, in prose, exactly (2) and (3): the proposal "eliminates a positive incentive
[to manipulate] but doesn't rule out the scenario altogether". Nothing in the corpus computes
either sign; round 1's model has no actions except take/decline and no scoring dynamics. A clean
EXEC artifact makes the two prose sentences into checked facts about a concrete model and — via the
parameter sweep — says *how much* residual manipulation incentive conditioning leaves. An honest
negative (e.g. (3) fails in all natural parameterizations — conditioning kills steering too) would
be a genuinely surprising positive result and equally acceptable.

**NOVELTY RISK.** No prior artifact overlaps (run1 legitimacy model is decision-free; run2 TODO 5
`edt-node-value` is about node-values in updateless deference, different object — do not reuse its
kernel machinery). **Shadow test:** fake = payoffs hand-tuned so the three signs come out as
predicted (detectable: signs must be derived from the scoring rule + channel semantics alone, and
the sweep must expose flip boundaries rather than a single cherry-picked point); fake₂ = defining
"steer" so it is wireheading under another name (the steer branch must keep the feedback channel
honest — the human genuinely holds the steered opinion).

---

## Q6 — Non-recoverability, compiled: no trace-measurable legitimacy gate exists

**id:** `leg-nonrecoverability` · **modality:** MIXED (EXEC construction + small Lean impossibility + prose) · **difficulty:** medium (one session)

**CLAIM (acceptance target).** Formalize and prove, in a finite toy class, v6 §4.7 ingredient (d) —
"legitimacy cannot be certified from the trace" — which v6 §8 flags as *asserted, never proved*.
Construct two coupled advisor/human systems from the SAME parameterized update-rule class, with
**identical observable traces** (all published quotes + all realized feedback on decided items over
a finite horizon `T`), such that in system 1 the human's terminal opinion on the never-decided
target equals its A-free counterfactual (feedback legitimate, per the blindness/autonomy reading of
v6 §6.5) and in system 2 it differs by a prescribed γ > 0 (the human was steered). Conclude, as a
one-line but load-bearing Lean/decide fact over the finite class: **any gate `ℓ : Trace → {0,1}`
assigns both systems the same verdict**, so no trace-measurable predicate is a legitimacy
predicate. Non-vacuity obligations: both systems are genuine members of the declared class (same
rule family, different latent parameters — verified, not asserted); the counterfactual baseline is
computed by actually running the A-free system; the γ-difference is exhibited in exact rationals.

**WHY.** This is the sharpest formal meaning of "non-circular definitions of legitimate feedback"
being *impossible* in one natural register: if legitimacy were definable from what the training
process can observe about itself, the training process could evaluate its own non-corruption — and
the constructed pair proves it cannot. It upgrades v6 §6.3's prose ("accurate prediction and active
steering produce the same vanishing aₙ − Yₙ") from interpretation to a compiled witness, and it
derives, rather than assumes, the conclusion v6 §5.10 reached for admissibility: legitimacy must be
a **causal/provenance/counterfactual** condition, not a trace condition. It also tells Q4 what ℓ_n
can never be.

**NOVELTY RISK.** `Frozen.underdetermination_off_G` (ESTABLISHED) proves "two points in (0,1)"
under a model-theoretic name — per the AUDIT it does not construct coupled systems or traces; the
new content is the explicit trace-equal pair with a computed counterfactual baseline. The
manipulation-theorem ingredients (v6 §4.7) are an open list, not results. **Shadow test:** fake =
declaring two label-different systems "trace-equal" without the trace being a computed object, or
smuggling the verdict in as a latent label the gate is then (trivially) unable to read; real = the
trace is an explicit finite sequence computed from both runs and checked equal (`decide`/assert),
the counterfactual gap γ is computed, and the impossibility ranges over ALL functions of that
finite trace.

---

## Q7 — The corruption taxonomy mapped onto the v6 boundaries: is legitimacy just admissibility? (Conjecture: no — manipulation lives inside)

**id:** `leg-taxonomy-map` · **modality:** PROSE (with finite witnesses where cheap) · **difficulty:** medium (one session)

**CLAIM (acceptance target).** A four-row classification theorem-by-construction. For each §0.3
corruption mode — (a) self-fulfilling prophecy, (b) wireheading, (c) adversarial takeover of the
channel, (d) human manipulation — construct an explicit formal instance inside the v6 framework and
prove its location relative to the three established boundaries (blindness/§5.1, the admissible
domain/§5.10, good-feedback/§5.8):

- conjectured outcomes to verify or refute: (a) = a quote-referencing diagonal (2a-type,
  inadmissible); (b) = a settlement-map corruption (violates reflective blindness — the settlement
  becomes a function of A's behavior); (c) = likewise a blindness violation with an adversarial
  third party (reduce it to (b) or show it is a genuinely distinct condition); and the headline:
- **(d) manipulation is ADMISSIBLE-domain-internal**: exhibit an instance in which every §5.9
  hypothesis holds — the family is exogenous, calibration (II) is satisfied, the theorem's
  conclusion is delivered — and yet the human's limit opinion on an undecided sentence is steered
  (adapting T7's underdetermination as a *citation*, not a re-proof). Hence
  **corrupt ⊋ inadmissible**: the legitimacy program cannot be completed by the admissibility
  condition alone, and the residue is exactly off-G underdetermination.

Acceptance = the table with each row backed by an explicit construction or a precise citation, and
row (d)'s separation witness worked in enough detail that a skeptic can check the §5.9 hypotheses
hold in it. An honest refutation of the conjecture (all four modes reduce to inadmissibility —
legitimacy = admissibility after all) is an equally valid, in fact stronger, outcome.

**WHY.** v6 §6.5 says legitimacy has "a clean partial home" in blindness and that the program is
replacing "all futures" with "non-corrupt futures" — but nobody has checked whether the four
corruption modes of §0.3 are or are not already captured by the machinery v6 built. This question
is the round's map: it tells the other executors which corruption modes need NEW mathematics (the
(d)-residue) and which are already theorems under other names. It is deliberately prose-modality:
the value is correct placement, and faking it is hard because each row must name the violated
condition and exhibit the instance.

**NOVELTY RISK.** Risk of being interpretation-only — mitigated by requiring per-row constructions
and the (d) separation witness. Must NOT re-prove 2a/2b, T7, or the §5.10 diagonal (all
ESTABLISHED; cite). No run1/run2 artifact attempts this mapping. **Shadow test:** fake = a table of
analogies ("wireheading is like blindness violation") without instances; real = each row's instance
is explicit enough to check the named condition fails/holds, and row (d) verifies the §5.9
hypotheses one by one.

---

## Q8 — "Predicated on its own non-corruption": dynamic consistency of the present-legitimacy axiom, or a trilemma

**id:** `leg-present-predicate` · **modality:** PROSE + EXEC toy · **difficulty:** medium–hard (honest partial result acceptable)

**CLAIM (acceptance target).** Formalize §0.3's clause "all the actual feedback it gets should be
assumed legitimate; the training process is predicated on its own non-corruption in the present" as
an explicit axiom scheme — at each day `n`, the learner updates on received feedback unconditionally
(ℓ = 1 on the realized past) while gating predicted future feedback by its legitimacy beliefs — and
settle its **dynamic consistency** in a finite model where corruption is sometimes *retrospectively
decidable* (day-k feedback is revealed corrupt at day k′ > k). Acceptance = a proof or a sharp
counterexample resolving which of these three the scheme must give up, stated as a trilemma with
the two-of-three combinations exhibited in an exact-rational toy:

1. **Predication** (past feedback is never re-litigated — the update stands);
2. **Retro-detection** (the legitimacy model is allowed to later decide past feedback was corrupt);
3. **Coherence/no-exploitation** (the belief stream admits no finite Dutch book built from the
   learner's own two verdicts — "I updated on it" and "I now believe it was corrupt" — e.g. a
   two-contract book against the day-k posterior and the day-k′ legitimacy verdict).

Conjecture to test: all three are jointly unsatisfiable in any model where retro-detection has
positive probability, and the §0.3 clause is therefore implicitly a commitment to giving up (2) —
the training process must treat its own past as *definitionally* legitimate, which is precisely
what makes past corruption unrecoverable-by-construction (connecting to Q6). An honest outcome may
be a consistency proof instead (the two verdicts are about different objects and no book exists);
either resolution is new.

**WHY.** This is the one clause of §0.3 no artifact has even formalized, and it is load-bearing:
it is what distinguishes the legitimacy program from ordinary robust learning (which would
down-weight suspect past data). Knowing whether the clause is a theorem, a free choice, or the
sharp corner of a trilemma changes what Q4's gate is allowed to do with the realized past.

**NOVELTY RISK.** Nothing adjacent in run1/run2/lean-deference (the corpus's self-trust results are
within-agent and never involve a legitimacy verdict about past feedback). Adjacent literature to
check and cite in the writeup, not rediscover: conservativity/undermining in formal epistemology
(Titelbaum-style memory-loss models) — the LI/feedback-channel setting is different enough that the
question stands. **Shadow test:** fake = defining the Dutch book so loosely that any belief change
whatever is "exploitable" (then the trilemma is a triviality about updating); real = the book must
be a genuine finite arbitrage against stated prices in the toy, computed in exact rationals, and
the consistency horn must be seriously attempted before the impossibility is claimed.

---

## Priority and dependency notes for the consolidator

- **Cheapest honest wins:** Q1, Q3, Q2 (all finite/decidable with the target object as conclusion;
  each has a pre-registered fake that is detectable at review). Q1 and Q2 share the frame; Q1(⟹)
  is Q2(2) — assign to one owner or declare the overlap.
- **Round-defining but heavier:** Q4 (the conditioning operation in the real LI register) and Q6
  (non-recoverability). Q6's output constrains Q4 (what ℓ cannot be); if both run, Q6 first or in
  parallel with the constraint noted.
- **Map for the whole round:** Q7. Its row (d) witness reuses no Lean and can be drafted early.
- **Most likely to produce an honest negative:** Q5 clause 3 and Q8 — both acceptable per ground
  rules and both would be informative.
- All questions comply with the run2 GLOBAL OFF-LIMITS list and the round-1 lab-Lean ban as argued
  per-question; the hypothesis-laundering ban is addressed in each shadow test. Labels used
  throughout: claims about what round-1/2 artifacts contain are **kernel-checked/paper-proved as
  cited**; conjectured outcomes (Q5.3, Q7.d, Q8) are flagged as conjectures to be tested, not
  results.
