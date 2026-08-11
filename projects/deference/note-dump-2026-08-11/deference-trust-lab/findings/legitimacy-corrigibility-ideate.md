# Legitimacy & Corrigibility — Ideation

*Thread: "Modeling Legitimacy & Corrigibility" (AGENDA §"Modeling Legitimacy & Corrigibility").*
*Author: ideation agent. Every claim flagged **PROVED / SKETCHED / CONJECTURE / INTERPRETATION**.
Cross-references: v2 = `deference-in-logical-induction-v2.md`; M&A = abramdemski "Meaning & Agency"
(`udt-representation-theorem/meaning-and-agency-reference.md`); AVE =
`udt-representation-theorem/agency-via-endorsement.md`; orientation = `findings/00-orientation.md`.*

---

## 0. The organizing idea (INTERPRETATION)

The lab's central object is the **single expert-specific premise** that the whole DDB↔LI Value
proof reduces to (v2 §10.1):

> **LUV-Total-Trust (novice N → expert E).** For every market-generable weight `w_n ∈ [0,1]`,
> `𝔼_n(⌜X_n · w_n⌝) ≂ₙ 𝔼_n(⌜𝔼_E(X_n) · w_n⌝)`.

For the *future self* this is free (it is the conditional martingale `ccee`, Thm 4.12.3). For a
*distinct* expert it is **not** free (v2 §10.4) — it must be earned. The thesis of this thread:

> **Legitimacy (of E, to N) := the property of E's belief-formation process that makes
> LUV-Total-Trust(N→E) hold.** Endorsement is N's *belief that* E is legitimate; legitimacy is the
> *fact* (relative to N's own coherent valuation of reality) that would warrant it. Wireheading /
> reward-hacking / manipulation are operations that **break** LUV-Total-Trust — they make the
> cross-agent martingale defect fail to vanish. The drug case is the *rationally anticipated*
> breakage of LUV-Total-Trust between present-self and a corrupted future-self.

This is exactly M&A's slogan "legitimacy is to endorsement as good is to utility," made operational:
the abstract relation is the martingale identity; "legitimate" is the specific instance we care
about (truth-tracking processes). It plugs straight into the v2 §10 modularization: **everything in
this thread is a statement about when, and on which subsequences, LUV-Total-Trust holds, fails, or
can be repaired.**

The six ideas below are ordered roughly by formalizability. §7 names the top pick.

---

## 1. Idea L1 — Legitimacy = LUV-Total-Trust; illegitimacy = a non-vanishing cross-martingale defect

**Candidate definition (INTERPRETATION, then SKETCHED).** Fix a novice inductor `(𝔼_n)` and an
*observable* expert estimate-stream `(𝔼_E(X_n))` (market-generable from N's prices, uniformly
bounded — the v2 §10.2 hypotheses). Define the **legitimacy defect** of E to N on weight class `𝒲`:
$$
\mathrm{Leg\text{-}defect}_{\mathcal W}(N\!\to\!E)\ :=\
\sup_{w\in\mathcal W}\ \limsup_n\ \big|\,\mathbb E_n(\ulcorner X_n w_n\urcorner)-\mathbb E_n(\ulcorner \mathbb E_E(X_n)\,w_n\urcorner)\,\big|.
$$
E is **legitimate-to-N (on 𝒲)** iff this defect is `0` (LUV-Total-Trust holds on 𝒲).

**Candidate proposition (SKETCHED, immediate from v2 §10.2).** If `Leg-defect = 0` on all
market-generable `w`, then **Value** holds: N would (timely) rather hand any observable bounded
decision to E than commit to a fixed option. *This is just v2's §10.2 Proposition restated with
"legitimate" as the name of its hypothesis* — so the legitimacy concept is **not** a new theorem,
it is a **naming** of the load-bearing premise. That is the point: it locates exactly *what truth-
tracking has to buy you* for deference to be safe. **Fidelity caveat:** L1 is only as contentful as
the claim that "truth-tracking process ⇒ small cross-martingale defect"; that implication is
**CONJECTURE** (it is the v2 §10.4 open characterization). So L1 is a *definition + reduction*, not
yet an earned theorem. Flag honestly.

**Why it bears on trust.** It says human-justifiable trust = the human's coherent valuation cannot
be Dutch-booked by betting "X" against "E's estimate of X" on any strategy the human can compute
from E's outputs. That is a *checkable-in-principle*, no-Dutch-book criterion for trust, dynamic and
feedback-driven, with no grain-of-truth assumption (v2 Summary pt 5).

**Setting:** logical induction (two inductors + deferral schedule). **Hardness:** the *definition*
and the *reduction to Value* are SKETCHED-easy (sit on v2 §10). The *characterization* of which
processes achieve zero defect is the hard open core (= orientation Q5).

---

## 2. Idea L2 — The drug/addiction case as a *rationally anticipated* deference failure (the cleanest model)

This is the AGENDA's flagship example: *"AI should avoid wireheading the way humans avoid addictive
drugs — they don't take the drug because they anticipate getting addicted and don't currently value
that outcome, even though they'd enjoy it."* The formal content is a **failure of LUV-Total-Trust
toward a future self that has been acted upon**, and crucially N can **prove it in advance**.

**The model (SKETCHED).** Two future-self streams over the same theory Γ:

- **`𝔼^{clean}_{f(n)}`** — the future self that results if N *abstains*. Self-trust 4.12.3 holds:
  LUV-Total-Trust(N → clean) is **free**. N endorses it.
- **`𝔼^{drug}_{f(n)}`** — the future self that results if N *takes the drug at day n*. This is the
  estimate-stream of a logical inductor whose **trader population / prices have been perturbed by an
  exogenous operation** (the "drug") that is *not* a market update — e.g. a fixed reassignment of
  high mass to a target sentence `θ` ("I am happy"), independent of Γ-evidence.

**Candidate proposition (CONJECTURE, sharply statable).** There is an efficiently computable weight
`w` and a sentence/LUV `X` such that
$$
\mathbb E_n\big(\ulcorner X_n\,w_n\urcorner\big)\ \not\!\eqsim_n\ \mathbb E_n\big(\ulcorner \mathbb E^{\mathrm{drug}}_{f(n)}(X_n)\,w_n\urcorner\big),
$$
i.e. `Leg-defect(N → drug) > 0`, **and** this gap is itself **N-provable / N-anticipated**: N's day-`n`
expectation of the future drug-estimate of `θ` is high (`𝔼_n(⌜𝔼^{drug}_{f(n)}(θ)⌝) ≈ 1`) while N's
*own* current estimate of `θ` stays low (`𝔼_n(θ) ≈ 0`). The witnessing weight is `w = Ind_δ(future
self endorses θ)`; conditioning on it, the two sides disagree because the drug-update is *not*
correlated with `θ`'s truth.

**The decision-theoretic payoff (SKETCHED).** Because N does **not** LUV-Total-Trust the drug-self,
N does **not** get a Value guarantee for handing decisions to it; and because N can *anticipate* the
defect at day `n`, a present trader can refuse the drug: betting on `θ` "the way the drug-self would"
loses money against N's own coherent prices. So **abstention is the no-Dutch-book action**. This is
the formal skeleton of "rational agents avoid addictive drugs / wireheading."

**Contrast that makes the model honest (INTERPRETATION).** The drug-self might be *happier* (higher
`𝔼^{drug}(θ)`), and might even be *immodest* and internally coherent. Legitimacy is **not**
calibration-of-the-future-self-to-itself; it is **correlation-with-reality-as-N-values-it**. The
drug-self fails *N's* cross-martingale even though it passes its *own* self-trust. This cleanly
separates "the process is confident/coherent" from "the process is truth-tracking," which is the
whole wireheading distinction.

**Why it bears on trust.** This is the load-bearing disanalogy between (good) self-trust and (bad)
trust-in-a-tampered-successor. Reward-hacking AI = an AI that has become its own drug-self; an
outside principal H should withhold endorsement for exactly the L2 reason.

**Setting:** logical induction, two future-self streams differing by an exogenous (non-market)
perturbation. **Hardness:** stating the *gap* is easy; the cleanest hard part is constructing the
"drug operation" as a well-typed object (a trader-population edit, or an oracle that overrides prices
on `θ`) and proving the defect is *anticipated* (the `𝔼_n(⌜𝔼^{drug}_{f(n)}(θ)⌝)≈1` while `𝔼_n(θ)≈0`
inequality). Medium. **This is the most distinctive idea of the thread.**

---

## 3. Idea L3 — Corrigibility as *absolute endorsement of the shutdown/modification map*

M&A defines **"Absolute" Endorsement** = control endorsement where the utility used is the
*observer's own* utility, and remarks (M&A, "Absolute Endorsement"): *"If Alice were to absolutely
endorse Bob's actions, then Alice should be fine with Bob modifying Alice's source code."* That is
**corrigibility**, verbatim. AVE makes this precise via the condensation/control-endorsement
machinery. The thread asks: lift this from a *belief/choice*-level relation to a **process**-level
one, and connect it to the LI deferral picture.

**Candidate definition (INTERPRETATION).** Let `H` be the human (slow trusted inductor / prior),
let `A` be the AI, and let `M : (beliefs, code) → (beliefs, code)` be a **modification map** that A
could apply to itself or that H could apply to A (shutdown is the special case `M = ⊥`, halt). A is
**corrigible w.r.t. M, to H** iff H **legitimacy-endorses the *map* M**: H's coherent valuation of
post-`M` outcomes (weighted by any H-computable selector) is ≂ to H's valuation of the pre-`M`
recommendation — i.e. **LUV-Total-Trust(H → "the world after H exercises M")** holds. Equivalently:
A treats H's shutdown/modification decisions as a *legitimate belief-/value-formation step*, so A's
own estimate stream already incorporates "if H decides to modify me, the modified me is the one H
endorses."

**Candidate proposition (CONJECTURE).** If A is corrigible-to-H in this sense **and** H
LUV-Total-Trusts A on the task subspace (A is legitimate-to-H there), then the *combined*
process — "A acts, but defers to H on whether to be shut down/modified" — is itself
LUV-Total-Trusted by H. I.e. corrigibility + task-legitimacy **compose** without H losing the Value
guarantee. Conversely, an A that resists shutdown is exactly one that has injected a weight `w` =
"H is about to modify me" on which the cross-martingale defect is large (A's estimates of post-mod
value diverge from H's) — *resistance is an illegitimacy signature*.

**The corrigibility/legitimacy tension to surface (RED-TEAM / INTERPRETATION).** Absolute
endorsement is *strong*: M&A itself warns that aligning to legitimacy-over-endorsement is "unilateral
imposition." So a candidate **impossibility-flavored** result: *full* corrigibility (H endorses
**every** modification map, including value-edits) **plus** A being a competent optimizer of a fixed
objective are in tension — if A endorses arbitrary edits to its own objective, it cannot also be
modeled as control-endorsed-by-H as optimizing *that* objective (the conditional-endorsement order of
M&A "Conditional Endorsement" breaks). This is the LI/endorsement analog of the known
corrigibility-vs-utility-maximization impossibilities (Soares et al.); worth stating in the
endorsement calculus.

**Why it bears on trust.** Corrigibility is the *safety property* humans most want; this frames it as
a legitimacy-endorsement of a particular map (shutdown), reusing the exact same martingale premise as
ordinary deference — unifying "trust A's beliefs" and "trust A to let itself be corrected."

**Setting:** endorsement calculus (AVE/M&A) for the impossibility half; logical induction (H, A two
inductors) for the composition half. **Hardness:** the composition proposition is medium-hard
(needs L1 + a clean "modification weight"); the tension/impossibility is conceptual-to-medium and
reuses existing endorsement Lean scaffolding (`udt-representation-theorem/lean/`).

---

## 4. Idea L4 — The legitimacy of a *training signal*: wireheading as corrupting the selector

Wireheading/reward-hacking specifically attacks the **signal that updates beliefs**, not the beliefs
directly. In LI the analog of "the training signal" is the **observation/feedback stream that the
deferral subsequence is keyed to** (orientation Q7: "trust only on subsequences with good feedback").
Make legitimacy a property of the **selector that picks the feedback subsequence.**

**Candidate definition (INTERPRETATION→SKETCHED).** Let `σ : ℕ → {0,1}` be a market-generable
**feedback selector** (σ(n)=1 marks days where N gets ground-truth feedback about E). "Good
feedback" (AGENDA, Eisenstat thread) = LUV-Total-Trust holds **restricted to the σ-subsequence**:
`𝔼_n(⌜X w σ⌝) ≂ₙ 𝔼_n(⌜𝔼_E(X) w σ⌝)`. A **manipulation/wireheading operation** is one that makes the
selector `σ` itself *correlated with E's errors* — i.e. E gains the ability to *choose when feedback
happens* so that feedback days are exactly the days E is right and non-feedback days are where E
deceives. Then legitimacy on σ no longer transfers to legitimacy off σ.

**Candidate proposition (CONJECTURE, the "treacherous-turn" formalization).** If E can make σ
E-generable in a way correlated with E's defect, there is a stream where (i) `Leg-defect` **on σ** is
0 (E looks legitimate on all observed feedback) yet (ii) `Leg-defect` **on `1−σ`** is bounded away
from 0 (E is illegitimate exactly where N never checks). This is the inner-alignment "wait until
trusted, then defect" trader (AGENDA, last para of Eisenstat thread) given a martingale signature:
**a trader that is correlated with `1−σ` and bets against E off-feedback.** N's protection: if N's
trader class can *also* generate `1−σ`-correlated weights, the LI criterion eventually prices the
deception in (the bad trader is exploited away) — giving a precise statement of *when learning
defeats treacherous turns and when it cannot* (it cannot if `1−σ` is not N-generable: the
unobservable case, AGENDA "human flourishing, values, ethics").

**Why it bears on trust.** This is the formal seam between "trust on subsequences with feedback"
(believed true) and "trust without feedback" (the hard case humans actually need). Legitimacy of the
*selector* is what makes feedback-trust generalize off-feedback — or provably fail to.

**Setting:** logical induction with a market-generable feedback selector σ. **Hardness:** medium-high.
The (i)/(ii) split is constructible (it is a relabeling of v2's hard/soft and on/off-support
machinery); the "learning defeats it iff `1−σ` is N-generable" claim is the contentful conjecture.
Closely tied to orientation Q5/Q7.

---

## 5. Idea L5 — Legitimacy is *non-monotone under self-modification*: a fixed-point/Löb obstacle

A subtle phenomenon: legitimacy of a successor is not preserved under the successor's own
self-modifications, and trying to *guarantee* it in advance hits a self-reference wall. This is the
legitimacy-thread's contact point with orientation Q10 (diagonalization) and the §5.2 false-hard /
true-soft split.

**Candidate proposition (CONJECTURE, Löb-flavored).** There is **no** *hard* internal certificate of
legitimacy: N cannot, on pain of the liar, hold a hard conditional of the form "conditional on E
asserting `φ`, `φ`" for E = a sufficiently expressive successor — exactly the Self-Trust 4.12.4
false-hard case with E in place of the future self. Formally: take E able to represent
`χ = "𝔼_E(χ) < ½"`; then hard-LUV-Total-Trust(N→E) on the weight `Ind_0(𝔼_E(χ)>½)` **fails** (the
v2 §0.3 / §5.2 liar). So **legitimacy can only ever be *soft* / asymptotic** — there is no
finite-frame, hard, in-advance legitimacy certificate for an expressive successor. By the §5.2
finite-collapse (PROVED, finite core), a successor that is both *modestly deferred to* and *cleanly
legitimate* must itself be an **infinite, self-referential reasoner** — i.e. **another logical
inductor** (v2 §10.3(b)). 

**Why it bears on trust.** It is a *limitative* result with a constructive silver lining: it says
"provable-in-advance, certain legitimacy of a smarter successor" is impossible (Löb/liar), so the
realistic target is *soft, asymptotic, no-Dutch-book* legitimacy — which is exactly what LI delivers.
It also tells you the *type* of thing a legitimately-trustable AI must be (an infinite-frame /
LI-like reasoner, not a finite Bayesian), connecting corrigibility to the §5 structural thesis.

**Setting:** logical induction (self-reference native). **Hardness:** the *negative* half (hard
legitimacy fails via the liar) is SKETCHED-easy — it is v2's existing liar argument re-pointed at an
external E. The *positive* half (soft legitimacy is the right notion + the §5.2 infinite-frame
necessity) is already PROVED in finite core (orientation Q3 would complete it in Lean). Good
red-team/audit value.

---

## 6. Idea L6 — Legitimacy is *not transitive*, and the failure is the trust-laundering attack

M&A Q1 asks whether conditional endorsement is transitive. For the safety story this matters: if H
endorses A, and A endorses B (a sub-process / delegated model / tool A spins up), does H endorse B?
If legitimacy were transitive, A could *launder* trust to an arbitrary B. The thread should pin down
**exactly when transitivity holds and when it is an attack.**

**Candidate proposition (CONJECTURE).** LUV-Total-Trust is **not** transitive in general: there are
inductors `H, A, B` with LUV-Total-Trust(H→A) and LUV-Total-Trust(A→B) but **not** LUV-Total-Trust(H→B).
The obstruction is precisely **observability / weight-class mismatch**: A's endorsement of B is on
A-generable weights, but H's Value guarantee needs H-generable weights, and these differ when B
exploits a weight A can compute but H cannot. *Transitivity is recovered* exactly when B is
H-observable (B's estimates are H-generable) — which is DDB's "transitivity" lemma (7.2.4) condition
re-expressed: in DDB the modestly-informed/CH structure makes deference compose; in LI the analog is
*shared generability*. (Contrast v2 §10.3(a): the *future self* is the join of all observable
experts precisely because it is maximally H-observable — so self-deference *is* transitive, but
deference to genuinely-more-powerful successors need not be. This is the tiling/Vingean register,
v2 §10.4.)

**Why it bears on trust.** Delegation chains (H trusts A, A spins up B, B spins up C…) are how
real AI systems scale; legitimacy non-transitivity is the formal reason "alignment is not closed
under delegation" — and the observability condition is a *design constraint* (keep delegated
sub-processes within the principal's generability/audit horizon) with teeth.

**Setting:** logical induction (three inductors); DDB finite frames for the clean transitivity-iff
statement. **Hardness:** medium. The finite-frame version is close to DDB Lemma 7.2.4 and could be a
clean probability-frame theorem; the LI version needs the §10.4 cross-agent characterization.

---

## 7. Triage and top pick

| idea | what it is | formalizability | safety payoff | flag |
|---|---|---|---|---|
| **L1** legitimacy = LUV-Total-Trust | definition + reduction to Value | **high** (sits on v2 §10) | locates *what truth-tracking buys* | SKETCHED def / CONJECTURE characterization |
| **L2** drug/addiction = anticipated deference failure | two future-selves, provable defect | **medium** (cleanest construction) | wireheading = self-drugging | CONJECTURE, sharply statable |
| **L3** corrigibility = absolute endorsement of mod-map | lift M&A absolute endorsement | medium (+ impossibility) | unifies trust-beliefs & trust-shutdown | INTERPRETATION + CONJECTURE |
| **L4** legitimacy of the training selector σ | manipulation corrupts feedback | medium-high | treacherous turn signature | CONJECTURE |
| **L5** no hard legitimacy certificate (Löb) | liar kills hard in-advance certs | high (negative half easy) | "provable certain trust" impossible | SKETCHED neg / PROVED-core pos |
| **L6** legitimacy non-transitivity | trust-laundering via delegation | medium | alignment ⊬ closed under delegation | CONJECTURE |

**Top pick: L2 (the drug/addiction model), developed *through* L1's definition.** Reasons:

1. **It is the AGENDA's own flagship intuition** ("AI avoids wireheading the way people avoid
   addictive drugs") and nothing in the lab has yet given it a formal skeleton. L1 supplies the
   vocabulary (legitimacy = LUV-Total-Trust); L2 supplies the *first non-trivial instance where the
   premise provably fails and the agent provably anticipates the failure*.
2. **It is the sharpest test of the legitimacy/endorsement distinction**: the drug-self is *happier
   and self-coherent* yet *illegitimate-to-N*, so it forces the model to separate "confident/calibrated
   to itself" from "truth-tracking for N" — the exact distinction wireheading turns on.
3. **It bolts directly onto v2 §10**: it is the negative companion to the §10.2 Value proposition —
   §10.2 says "legitimate ⇒ Value"; L2 exhibits "illegitimate ⇒ anticipated-defect ⇒ abstention is
   the no-Dutch-book move," using the *same* cross-martingale object. No new machinery; one new
   construction (the non-market "drug" perturbation) + one inequality
   (`𝔼_n(⌜𝔼^{drug}_{f(n)}(θ)⌝)≈1` while `𝔼_n(θ)≈0`).
4. **It yields a crisp, plausibly-Lean-checkable algebraic core** (see §8): on a finite frame, an
   exogenous perturbation of the expert distribution that is independent of the target's truth makes
   the novice's cross-expectation defect strictly positive and *sign-determined* — the finite shadow
   of "anticipated drug failure," in the same finite-frame style as the existing
   `LeanDeference.lean` `value_of_CM` / `CM_implies_immodest`.

Develop order: write L1 as the definition note; prove the finite-frame "drug defect is positive and
anticipated" lemma (L2 core) by hand and as a candidate Lean file; then L3 (corrigibility composition)
as the safety application. L5 is the best *red-team/limitative* companion and is cheap to state.

---

## 8. A small, crisp candidate for the Lean-verify agent (L2 finite core)

**Plain-English claim the Lean is meant to capture.** *In a finite probability frame, if the
"drugged expert" distribution `Q` is obtained from a clean expert by moving mass onto a target event
`θ` in a way uncorrelated with whether `θ` actually obtains, then the novice's expectation of "θ
weighted by the drugged-expert's high opinion of θ" exceeds the novice's expectation of "(drugged
expert's estimate of θ) weighted the same way" — a strictly positive cross-martingale defect with a
definite sign. The novice can see this gap (it is a function of the novice's own valuation), so it
constitutes an anticipated deference failure: deferring to the drugged expert is dominated.*

This is the finite shadow of L2, in the exact algebraic style of `value_of_CM`. I have **NOT**
compiled it. I have tried to make the Lean **faithful** and **non-vacuous** — see the fidelity audit
below the statement. Candidate file written to `lean/legitimacy.lean`, marked **UNCHECKED**.

Concretely (finite types `W` worlds, `π` novice distribution, two expert estimate-functions
`Eθ_clean, Eθ_drug : W → ℝ` giving the expert's estimate of indicator-`θ` at each world, and `θ : W →
ℝ` the actual `{0,1}` indicator), the lemma to verify is an **identity + sign** of the form
$$
\underbrace{\textstyle\sum_w \pi_w\,\theta_w\,w_w}_{\mathbb E_\pi(\theta\cdot W)}\ -\
\underbrace{\textstyle\sum_w \pi_w\,(\mathrm{E}\theta_{\mathrm{drug}})_w\,w_w}_{\mathbb E_\pi(\mathrm{E}_{\mathrm{drug}}(\theta)\cdot W)}\ =\
\textstyle\sum_w \pi_w\,w_w\,\big(\theta_w-(\mathrm{E}\theta_{\mathrm{drug}})_w\big),
$$
and: **if** at every `π`-supported world the drugged estimate overshoots the truth-correlation
(`(Eθ_drug)_w ≥ θ_w` with strict somewhere on positive-`π`, positive weight `w_w>0`), **then** the
defect is `≤ 0` strictly — i.e. the drugged expert is *systematically over-optimistic about θ
relative to reality*, the signed defect detects it, and (key) the defect is computable from
`π, θ, Eθ_drug, w` alone (all novice-side objects). The **anticipation** clause is that this is a
function of the novice's own data, so `𝔼_π` "sees" it.

**Fidelity audit (the most important part).**
- *Identity half* — `∑ π w (θ − Eθ_drug) = ∑ π θ w − ∑ π Eθ_drug w`: pure `Finset` linearity,
  **faithful, universal, non-vacuous** (mirrors `decomposition` in the existing Lean).
- *Sign half* — this is where smuggling could hide. The hypothesis `(Eθ_drug)_w ≥ θ_w on supp π,
  w_w ≥ 0` is **honest**: it says "the drug makes the expert *overstate* the target relative to its
  realized value," which is the substantive content of "moving mass onto θ uncorrelated with θ's
  truth" — it does **not** assume the conclusion (the conclusion is about the *signed weighted sum*,
  the hypothesis is *pointwise*; the implication is a real, if elementary, monotonicity step). It is
  **non-vacuous** (drug streams with `Eθ_drug > θ` exist).
- *Honest limitation* — what the finite lemma does **NOT** capture: (a) the **anticipation** is only
  modeled as "the defect is a function of novice-side data," not as `𝔼_n(⌜𝔼^{drug}_{f(n)}(θ)⌝)≈1`
  in the genuine LI asymptotic sense — that needs the LUV/asymptotic layer the existing Lean also
  leaves to prose; (b) it does **not** show abstention is no-Dutch-book — only that the defect has a
  definite exploitable sign; (c) "uncorrelated with truth" is *encoded* as the pointwise overshoot
  hypothesis, a modeling choice, not derived. So the Lean is a **faithful finite shadow of one
  inequality in L2**, no more — exactly the honesty boundary the existing `LeanDeference.lean`
  observes (orientation §3, "what the Lean does NOT cover"). Mark accordingly.

If even this is more than the verify-agent wants, the **identity half alone** (the decomposition) is
a guaranteed-faithful, guaranteed-fast one-liner that still earns its keep as "the legitimacy defect
decomposes as a single signed weighted sum."
</content>
</invoke>
