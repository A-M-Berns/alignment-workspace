# Scout: Fresh Eyes & Outside Connections — Candidate Research Questions (Round 3)

*Scout deliverable, run 3 (legitimacy & deference), 2026-07-01. Lens: everything previous
rounds did NOT consider — LI-paper self-trust theorems never exploited by this program;
legitimacy-shaped statements suggested by the UDT/endorsement corpus next door
(`udt-representation-theorem/`); the li-deference §0.3 time-travel worries recast as precise
mathematical statements.*

*Everything below is labeled. Sources read in full or in targeted depth: LI paper
`references/logical-induction/main.tex` (§4.8–4.12 exact statements: Introspection,
Paradox Resistance, Expectations of Probabilities, Iterated Expectations, cee/ceu/ccee/st,
Recurring Unbiasedness, Unbiasedness From Feedback, Non-Dogmatism block, deferral
functions); `li-deference.md` (§0.3 in full); `deference-in-logical-induction-v6.md`
(§6.3–6.7, §7, §8); `udt-representation-theorem/agency-via-endorsement.md` and
`meaning-and-agency-reference.md` (in full); `plan.md`; `lean-deference/AUDIT.md` (in full);
run2 `todos/TODOS.md` GLOBAL OFF-LIMITS (in full) and run2 `report/RESEARCH-REPORT.md`
(ledger + §2); run1 `models/legitimacy-corrigibility-model.md` (§0–2, enough to
delimit the off-limits objects).*

---

## 0. What the fresh-eyes audit of the LI self-trust section actually found

Three observations drive most of the questions below. Each is an *interpretation* until a
question turns it into a claim.

**(F1) The program has used four of the LI paper's self-reflection theorems and ignored the
rest.** The corpus's named LI hypotheses are `loe` (4.8.4 Linearity), `expprovind` (4.8.10),
`cee` (4.12.1 Expected Future Expectations), `ccee` (4.12.3 No Expected Net Update under
Conditionals), and `st` (4.12.4 Self-Trust). Never touched by any round: **Introspection
(4.11.1)**, **Paradox Resistance (4.11.2)** — the theorem that governs *self-referential /
prophecy-like sentences*, which is exactly the shape of li-deference §0.3's self-fulfilling
prophecy worry — **Expectations of Probabilities (4.11.3)** and **Iterated Expectations
(4.11.4)** (day-n introspective versions of the tower), **Recurring Unbiasedness /
Unbiasedness From Feedback (4.4.5–4.4.6)** *as objects of study* (UFB is cited as the named
`hbias` hypothesis in `FaithfulAcceleration.lean`, but its own hypothesis surface — the
deferral-schedule condition — has never been examined as the thing an adversary attacks),
and the **Non-Dogmatism block (4.6.x)**.

**(F2) The paper's own gate already sits at the future day.** `ccee` reads
`E_n(⌜X_n · w_{f(n)}⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n) · w_{f(n)}⌝)` — the weight `w` is evaluated at
day `f(n)`, i.e. LI self-trust *natively supports conditioning the deferral target on a
future-measurable event*, provided the weight sequence is P-generable. The legitimacy
program's stated goal ("the AI should predict human opinion only through non-corrupt
futures", li-deference §0.3; "replacing all futures with non-corrupt futures in the target",
v6 §6.5) is *syntactically* an instance of this gate. Nobody has written that down, or
identified exactly which hypothesis of ccee the corrupt cases break. That is Q2.

**(F3) Paradox Resistance is one half of a dichotomy the paper never states.** Thm 4.11.2
handles sentences χ with `Γ ⊢ χ ↔ (P_n(χ) < p)` — the *anti-inductive* (self-refuting)
orientation, where the induced price map is decreasing and there is a unique consistent
price, which LI finds. The *self-fulfilling* orientation (`χ ↔ P_n(χ) ≥ p` — bank runs,
li-deference §0.3 bullet 1) has an increasing response map with **multiple** consistent
prices, and no LI theorem selects among them. Equilibrium multiplicity is the precise
mathematical face of "the prophecy corrupts the feedback channel." That is Q1.

---

## Q1 — Self-fulfilling vs. self-refuting feedback targets: equilibrium multiplicity is the prophecy problem

**Title:** `prophecy-multiplicity` — the fixed-point dichotomy dual to Paradox Resistance.

**Claim (acceptance target).** Work with soft response maps on `[0,1]` (hard indicators are
illegal in LI; the paper's own Ind_δ ramp is the honest object). Fix rational `p ∈ (0,1)`
and ramp width `δ` with `0 < δ < min(p, 1−p)`. Define the *self-refuting* response
`τ⁻(x) = Ind_δ(x < p)` (the paper's paradox sentence: true iff priced below p) and the
*self-fulfilling* response `τ⁺(x) = Ind_δ(x ≥ p)` (bank-run sentence: true iff priced at or
above p), both as the explicit piecewise-linear clamps. Prove, kernel-checked and with the
fixed-point sets **computed from the response maps, never hypothesized**:

  (i) `τ⁻` has a **unique** fixed point `x⁻ ∈ (p−δ, p]` (existence by IVT/continuity,
      uniqueness because a continuous decreasing map has at most one fixed point — prove the
      general lemma for monotone-decreasing continuous `f : [0,1] → [0,1]`, then instantiate);
      moreover the iteration `x ↦ τ⁻(x)` … no dynamical claim needed for (i), the uniqueness
      is the content. This is the finite shadow of Paradox Resistance's `lim P_n(χ^p_n) = p`.
  (ii) `τ⁺` has **at least three** fixed points for the same `(p, δ)`: `0`, `1`, and an
      interior `x* ∈ [p−δ, p]` — all three exhibited as explicit rationals with
      `norm_num`-checked `τ⁺(x) = x` — and the fixed-point set is exactly `{0, x*, 1}`
      (decidable for the concrete piecewise-linear family).
  (iii) **Stability separation (the safety-relevant part):** for the discrete adjustment
      dynamics `x_{k+1} = x_k + η(τ(x_k) − x_k)` with small rational `η`, prove on the
      concrete family that in case (ii) the extreme fixed points `0` and `1` are attracting
      (orbits from below `x*` decrease monotonically to a neighborhood of 0, orbits from
      above increase to 1) while `x*` is repelling; and in case (i) the unique `x⁻` is
      attracting from both sides. Monotone-iteration arguments on explicit piecewise-linear
      maps; no fixed-point theory imports needed.

**Why it matters.** li-deference §0.3 bullet "Self-fulfilling prophecies: some bad things
could happen as a result of being predicted to happen, such as bank runs" is currently a
one-line worry. This result turns it into a theorem-shaped statement: **the corruption of a
prediction-dependent feedback channel is not that the AI predicts wrongly — every fixed
point is a self-consistent, criterion-compatible prediction — it is that the consistent-price
set has more than one element, so the *publication itself selects the outcome*, and the LI
criterion is silent about the selection.** LI's Paradox Resistance (main.tex §4.11, thm:lp)
is exactly the statement that the self-refuting orientation has a unique consistent price;
the program has never noticed that the theorem's scope boundary (decreasing response only)
coincides with the legitimacy boundary. Outside connection: this is the performative-
prediction literature's stability-vs-optimality gap (Perdomo et al.) reached from the LI
side; v6 §6.5 already flags the stop-gradient/performativity connection for *blindness*,
but not the multiplicity phenomenon.

**Modality.** LEAN-CORE (all three parts are finite real analysis over explicit
piecewise-linear maps; conclusions computed) + a PROSE seam paragraph connecting (i) to
thm:lp and (ii) to §0.3 (labeled interpretation).

**Difficulty.** Medium. The Lean is elementary but fiddly (piecewise-linear case analysis);
one focused session.

**Novelty risk.** No off-limits object touches paradoxical/self-referential *sentences'
price dynamics*. `SelfRefTarget.no_exact_quote` (off-limits) is about a ½-gap for an
*anti-inductive quote map* in the tracking problem — superficially adjacent (also a
discontinuity/anti-inductive phenomenon) but a different object (that result says *no exact
self-quote exists*; this one is about the fixed-point *count* of soft response maps and its
flip under orientation). The near-miss/shadow test: the fake version asserts the fixed-point
sets as hypotheses or picks maps where multiplicity is baked in by fiat; the real version
computes `Fix(τ)` from the ramp definition, and must also compile the (i)-vs-(ii) contrast
on the *same* `(p, δ)` so the orientation flip is the certified cause. Known mathematics
(bistability of monotone maps is textbook) — the contribution is lab-specific instantiation:
the two maps are the paper's own Ind_δ gates on the paper's own paradox sentences, and the
dichotomy is pinned to Paradox Resistance's scope. Must be framed exactly so (cite the
textbook fact, do not claim to discover bistability).

---

## Q2 — The legitimacy gate already lives inside ccee: future-indexed gating and the generability crux

**Title:** `ccee-legitimacy-gate` — gated deference targets are free for the self-case;
the entire open problem is who computes the gate.

**Claim (acceptance target).** Three parts, all paper-math with a small Lean finite core:

  (i) **The positive instance (composition, not new proof):** Define the *legitimacy-gated
      deferral target*: for a corruption-LUV sequence `C_n` and threshold `τ`, the gate
      `w_n := Ind_δ(C_n < τ)` and the gated tower statement
      `E_n(⌜X_n · w_{f(n)}⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n) · w_{f(n)}⌝)`.
      Verify in writing (theorem-by-theorem, hypothesis-by-hypothesis) that this **is an
      instance of ccee (main.tex thm 4.12.3)** whenever `⟨w_n⟩` is P-generable — i.e. "predict
      my future opinion only through futures my future self marks non-corrupt" is *already a
      theorem* for the self-case, with zero new machinery. State the corresponding gated
      Self-Trust instance from thm:st the same way.
  (ii) **The crux, isolated (the new content):** identify *exactly which hypothesis fails*
      in each corrupt case of li-deference §0.3, as a table: (a) if the corruption indicator
      is computed by the *gated process itself at day f(n)* (self-report), the gate is
      generable but worthless — a wireheaded future self reports `C = 0`; formalize this as
      a two-world finite frame (explicit rationals) where the self-reported gate passes,
      the gated tower holds, and the gated target still equals the corrupt value — i.e.
      **gated ccee is sound but not safe under self-reported gates** (LEAN-CORE, conclusion
      computed). (b) if the corruption indicator requires `𝒞_A`-computation (only the
      stronger process can detect its own manipulation), the gate is **not H-generable** and
      ccee for H simply does not apply — the failing hypothesis is generability, stated
      precisely. (c) the surviving positive class: corruption events decidable by day `f(n)`
      from a channel *outside* the gated process (the deductive ledger / an exogenous
      monitor) give a generable-and-honest gate; state the gated tower for that class as the
      honest positive fragment.
  (iii) **The scoping theorem (interpretation, argued):** conclude that the legitimacy
      program's mathematical content is not a new trust theorem but a *constraint on the
      gate's provenance*: legitimate gating = P-generable ∧ computed outside the gated
      channel. Relate to v6 §6.5's "pushing the forced-soundness boundary past raw
      timely-checkability toward checkable-and-legitimate": the gate provenance condition is
      the candidate formal definition of "-and-legitimate".

**Why it matters.** v6 §6.5 says the legitimacy formalization is "currently a desideratum,
not a model" and v6 §8 lists it as open. li-deference §0.3 ends: "I don't yet have a firm
idea about how to incorporate those ideas into the mathematical picture." This question
proposes the *first concrete incorporation*, and it is cheap because the mathematical object
(a future-indexed generable gate) already exists in the LI paper — observation (F2) above.
An honest negative outcome is fully acceptable: if (i) fails to be a genuine ccee instance
(e.g. the gate's dependence on `C_{f(n)}` breaks e.c.-ness of the LUV sequence), that
failure, precisely located, is itself the deliverable.

**Modality.** MIXED — PROSE for (i)/(ii-b)/(iii) (hypothesis-checking against the paper's
exact statements), LEAN-CORE for the (ii-a) finite frame.

**Difficulty.** Medium. (i) is careful reading; (ii-a) is a small finite frame; the risk
concentrates in getting the e.c./generability bookkeeping right.

**Novelty risk.** Run1's `Legitimacy.{defect_decomp, drug_defect_sign}` and
`LegitimacyCorrigibility.*` are off-limits — but those are **day-n witness-weight, one-stage
defect-sign objects** (legitimacy = LUV-Total-Trust on day-n computable weights; wirehead
overshoot ⇒ defect ≤ 0). The present object is different in the load-bearing place: the gate
is indexed at the **future** day `f(n)` through ccee's `w_{f(n)}` slot, and the result is a
*provenance dichotomy* on the gate, not a defect sign. The (ii-a) frame must NOT re-prove
the drug-defect sign lemma — the frame's conclusion is "gated tower holds ∧ gated target
corrupt" (a soundness/safety split), not "defect ≤ 0". HYPOTHESIS-LAUNDERING check: the
target object (the gated tower for the corrupt case) appears only as a *computed conclusion*
of the finite frame, never as a hypothesis; ccee is a type-(b) LI citation, allowed.

---

## Q3 — Mechanism non-identifiability: trust is not a function of the feedback channel's statistics

**Title:** `mechanism-blindness` — a kernel-checked finite frame where clean and corrupted
feedback are observationally identical but Total Trust holds in one and fails in the other.

**Claim (acceptance target).** Build an explicit finite frame: worlds
`W = Mechanism × Feedback × Θ` with `Mechanism ∈ {clean, manip}`, and two priors — or one
prior and a mechanism-mixture parameter — such that, `decide`/`norm_num`-checked:

  (i) the **observable channel statistics coincide**: the joint distribution of everything
      the novice can see (the feedback value, and its arrival pattern if modeled) is
      *identical* under `π_clean` and under `π_mix` (the mixture putting weight `λ > 0` on
      the manipulator mechanism) — exhibited as equal explicit rationals, `decide`-checked;
  (ii) the DDB/LeanDeference conditional-mass Total-Trust inequality
      `s·π{E(X) ≥ s} ≤ E_π(X·1[E(X) ≥ s])` — the exact form certified by
      `value_witness_iff_totalTrust_mass`, *cited as a tool, not re-proved* — **holds under
      `π_clean` for every indicator variable `X` and every threshold `s` on the declared
      finite grid** (a finite conjunction, fully `decide`-checked — the grid limitation
      declared loudly), and **fails under `π_mix`** at an explicit `(X, s)` with the numeric
      gap printed;
  (iii) **near-miss (mandatory):** enlarge the observation algebra so the mechanism bit is
      observable; then a mechanism-conditional Total Trust test *does* separate the two —
      the corrupted branch fails on its own fiber — certifying that the invisibility in
      (i)+(ii) is caused exactly by mechanism unobservability, not by the payoffs.

**Why it matters.** This is the finite, machine-checked skeleton of the single most
safety-relevant sentence in v6 §6.3: "the AI can shape the human's beliefs on unresolvable
questions, **and the record cannot reveal it**." The corpus's current formal witness for
that sentence is `Frozen.underdetermination_off_G`, which the AUDIT (§3.4, severity-High)
exposes as "two points in (0,1) wearing a model-theoretic name," and the AUDIT's own
recommendation 2 asks for a real model. Legitimacy reading: **legitimacy is a property of
the mechanism, and no statistic of the feedback stream can certify it** — which is precisely
why li-deference §0.3 says the process must be "predicated on its own non-corruption" rather
than testing for it. This complements Q2: Q2 says who must compute the gate; Q3 proves why a
gate computed from feedback statistics alone cannot exist.

**Modality.** LEAN-CORE (finite frame, all conclusions computed; possibly a small EXEC
search in exact rationals to *find* the frame before hand-verifying it in Lean).

**Difficulty.** Medium. The construction needs care (matching observables while splitting
the (θ, feedback) joint is a linear-algebra exercise with enough worlds), but the check is
fully decidable.

**Novelty risk.** Three adjacencies, all distinguishable: (a) `underdetermination_off_G`
(off-limits as an object) — that is a trivial existence of two reals; this is a genuine
frame with computed trust verdicts; the AUDIT explicitly requests this upgrade, so it is
gap-filling, not re-skinning. (b) run2 `trust-laundering` — that was two-place trust
*chains* (transitivity), verdict SHADOW; this is one novice, one channel, two *mechanisms*;
no chain anywhere; and the quantifier here is over a declared finite indicator grid, honest
about its scope, avoiding exactly the ∀X:W→ℝ shadow that sank trust-laundering. (c) the
`AntiExpert` frame (off-limits) — one agent vs. an unconditional martingale, a Total-Trust
*failure* witness; here the phenomenon is an *indistinguishable pair*, which AntiExpert does
not contain. Shadow test: the fake version hand-picks (i) as an assumption ("suppose
observables agree") — the real version exhibits the equality as computed rationals; and the
fake version omits (iii), leaving open that the payoffs, not the unobservability, cause the
failure.

---

## Q4 — Is conditional endorsement transitive? (Meaning & Agency, open question 1, made finite)

**Title:** `conditional-endorsement-order` — prove the trust order is a strict partial
order on finite frames, or exhibit a decide-checked 3-cycle.

**Claim (acceptance target).** Use the belief form of conditional endorsement from
`meaning-and-agency-reference.md` (§Conditional Endorsement) and
`agency-via-endorsement.md` (§Conditional Endorsement and Levels of Trust): on a finite
probability frame `(W, π)` with finite-valued "expert-report" variables `V₁, V₂, V₃ : W → Q`
(each value of `Vᵢ` encoding a probability report about a fixed target event `X ⊆ W`), say
**`π` endorses `Vᵢ` given `Vⱼ`** iff for all value pairs `(x, y)` with
`π(Vⱼ = x, Vᵢ = y) > 0`: `π(X | Vⱼ = x, Vᵢ = y) = y`. Define the derived strict relation
`Vᵢ ≻ Vⱼ` ("trusted more") iff `π` endorses `Vᵢ` given `Vⱼ` but not `Vⱼ` given `Vᵢ`.
Deliver exactly one of:

  (i) a proof, for all finite frames, that `≻` is transitive (hence a strict partial
      order), with the proof identifying the structural reason (e.g. endorsement-given =
      conditional-expectation refinement, and refinement is transitive); **or**
  (ii) an explicit finite frame (found by EXEC search over exact rationals, then
      hand-embedded in Lean) with three variables forming a cycle `V₁ ≻ V₂ ≻ V₃ ≻ V₁`, every
      one of the six endorsement/non-endorsement edges verified over the **full finite grid
      of value pairs** (this quantifier is finite — unlike run2's ∀X:W→ℝ — so a complete
      check is genuinely decidable), plus a non-vacuity certificate that all three variables
      are non-degenerate (non-constant, distinct).

**Why it matters.** `meaning-and-agency-reference.md` §Questions & Conjectures, question 1,
verbatim: "How well can we use conditional endorsement to characterize optimization power
(or more generally, level of endorsement)? **Is it transitive?**" — an explicitly posed,
never-attempted open question of Abram's own program. It is also the legitimacy question in
miniature: if the trust order can cycle, then "defer to the most-endorsed process" is
ill-defined and legitimacy cannot be defined as a maximum of the endorsement order — a
structural fact the li-deference program should know before building on endorsement.
Either outcome is a real result; my prior (interpretation): a cycle exists, by analogy
with Condorcet/nontransitive-dice structures, but conditional endorsement's exactness
(equality, not inequality) may be rigid enough to force transitivity — that tension is
exactly why the question is informative.

**Modality.** LEAN-CORE with an EXEC (Python, exact `fractions.Fraction`) search phase.

**Difficulty.** Medium-hard. The search space is small frames × rational-valued reports;
the risk is that endorsement-given is so rigid that examples where both `V_i`-given-`V_j`
endorsements even *hold* are scarce — which would itself be a reportable finding
(the order is nearly empty, hence trivially transitive; state it honestly).

**Novelty risk.** run2 `trust-laundering` (SHADOW, numbers uncitable) tested transitivity of
**two-place Total Trust across three agents' priors** — a different relation (threshold
inequality over all real-valued X, cross-prior) from three-place **conditional endorsement
within one prior** (exact equality over finite value pairs). No off-limits Lean object
concerns conditional endorsement. The M&A post itself only *poses* the question. Shadow
test: the run2 failure mode (an edge silently failing → vacuous cycle) is the pre-registered
fake; the real version decide-checks every edge over the complete finite conditioning grid
and ships the grid size in the statement.

---

## Q5 — The logical complexity of "legitimate": bounded legitimacy is learnable, global legitimacy is only assumable

**Title:** `legitimacy-is-pi1` — Non-Dogmatism corollaries locating the legitimacy
predicate in the arithmetic hierarchy.

**Claim (acceptance target).** Paper-math (short, two lemmas as direct corollaries of LI
theorems, each with the cited theorem's hypotheses checked line-by-line):

  (i) **Bounded legitimacy is learnable.** Let corruption events be decidable-by-day: there
      is an e.c. sequence of decidable sentences `legit_n` = "no corruption event occurs
      on or before day n" (the corruption monitor is a fixed poly-time check of the public
      record). If in fact no corruption ever occurs (all `legit_n` true, and `Γ` proves each
      — the decidability makes this the Provability Induction (thm 4.2.1) shape), then
      `P_n(legit_n) → 1` **in a timely manner**. Instance-checking, not new math; the
      deliverable is the exact verification that the legitimacy monitor fits the theorem's
      e.c./decidability hypotheses, plus the statement of what "timely" buys over "eventual".
  (ii) **Global legitimacy is not learnable, even when true.** Let `legit_∞` be the Π₁
      sentence "no corruption event ever occurs" (universal closure of the monitors). By
      Non-Dogmatism (thm 4.6.2): if `Γ ⊬ legit_∞` — which holds for any monitor whose
      violation is consistent with the base theory, i.e. any *real* channel — then
      `P_∞(legit_∞) < 1`: the inductor maintains forever-positive credence in eventual
      corruption **no matter how much clean history it sees**. Conversely `P_∞(legit_∞) > 0`
      if corruption-freedom is consistent — the assumption is *retainable* but never
      *certifiable*.
  (iii) **The reading (interpretation, labeled):** li-deference §0.3's clause "all the
      actual feedback it gets should be assumed legitimate; the training process is
      predicated on its own non-corruption in the present" is now a theorem-shaped
      necessity, not a design choice: because legitimacy is Π₁, LI epistemology *forces* the
      finitistic-consistency treatment (believe each bounded instance via (i); never the
      universal closure via (ii)) — exactly parallel to the paper's own Belief in Finitistic
      Consistency (thm 4.6.4) discussion. Consequence for Q2: any legitimacy gate must be
      day-indexed; a gate conditioning on global legitimacy conditions on an event the
      market never decides.

**Why it matters.** It answers, cheaply and rigorously, *why* the legitimacy program has the
shape li-deference §0.3 gives it, and it constrains every future formalization (gates must
be day-indexed — feeding directly into Q2's design). It is also the first use of the
Non-Dogmatism block (main.tex §4.6) anywhere in this program.

**Modality.** PROSE (instance-checking against exact paper statements; no Lean —
formalizing would require modeling the sentence-encoding machinery, which the ground rules'
honesty norms say not to fake).

**Difficulty.** Easy-medium. The main labor is honest hypothesis-checking of (i) (is the
monitor sequence genuinely e.c.? is "Γ proves each legit_n" the right truth condition, or
does one need Persistence of Knowledge (4.2.3)?). Half a session; low risk.

**Novelty risk.** No prior round used Non-Dogmatism or the finitistic-consistency block;
nothing in the off-limits list is adjacent. The result is deliberately modest —
the shadow test is about framing: the fake version dresses (ii) as a discovery about
corruption ("AIs can never trust their training!"); the real version presents both lemmas as
*instances* of known LI theorems whose composition and consequence for the gate design are
the new content. If (i)'s hypothesis-check fails (the monitor can't be made e.c.), that
negative is the deliverable.

---

## Q6 — Corrupting the schedule, not the values: the good-feedback hypothesis as attack surface

**Title:** `schedule-corruption` — Unbiasedness From Feedback assumes schedule integrity;
truth-correlated timing is a corruption channel the legitimacy program has not priced in.

**Claim (acceptance target).** The paper's Unbiasedness From Feedback (thm 4.4.6, quoted
exactly) requires: a strictly increasing deferral function `f` with the weighting's support
in `Im(f)`, and `Ind(φ_{f(n)})` **computable in `O(f(n+1))` time**. The claim to establish
(paper-math, with an EXEC toy optional):

  (i) **The attack model, stated precisely:** an adversary controls only *when* each
      feedback item becomes computable (eventual decidability preserved — no censorship;
      values untouched), and may choose the delay as a function of the item's truth value
      ("delay bad news"). Formalize as a decidability-time function `T(n)` chosen
      adversarially subject to `T(n) < ∞`.
  (ii) **The negative result:** exhibit a truth-correlated timing scheme and an e.c.
      decidable sentence sequence such that **no** deferral function satisfies UFB's
      hypothesis on any divergent weighting concentrated where the bias lives — so the
      theorem gives nothing — and the price sequence can sustain recurring nonzero bias:
      the w-weighted average bias has a nonzero limit point along the attacked subsequence
      (it must also have 0 as a limit point, by Recurring Unbiasedness (thm 4.4.5), which
      needs no feedback — state this ceiling honestly: the attack cannot produce
      *persistent* bias bounded away from 0 on any p-generable divergent weighting, only
      *recurrent* bias; the paper's own `θ`-clusters discussion is the template and must be
      cited as such, with the new content being the truth-correlated-timing mechanism that
      *produces* cluster-like behavior from an adversary rather than assuming it).
  (iii) **The positive contrast:** any *truth-independent* (exogenous) timing scheme with
      poly-time decidability restores UFB's hypothesis for some deferral function — so the
      exact legitimacy condition on the schedule is **timing ⫫ truth**, a
      provenance/independence condition of the same shape as Q2(iii)'s and the
      admissible-domain condition of v6 §5.10 (exogenous-family / payoff-observation
      separation). State the alignment reading: "assume feedback legitimate" must include
      *schedule* integrity; calibration checks on arrival-selected records are void.

**Why it matters.** v6 §6.7 already concedes the calibration trader "banks only where the
feedback target is observed on schedule — the good-feedback subsequence," and
`FaithfulAcceleration.lean`'s `hbias` names UFB as a hypothesis. But every corruption mode
in li-deference §0.3 (manipulation, self-fulfilling prophecy, adversarial takeover) has been
imagined as corrupting feedback *values*. Timing is a strictly cheaper attack (no false
statements ever made — every delayed item eventually resolves truthfully) that voids the
same guarantee, and it is invisible to any value-audit of the record. Fresh-eyes content:
reading the *hypothesis surface* of an LI theorem as the corruption surface, which no round
has done.

**Modality.** PROSE (the honest register: the claim is about which LI theorem hypotheses
fail; a mock-market EXEC would risk exactly the caricature run2 declined). An EXEC toy
(exact rationals) illustrating (ii)'s recurrent bias on a hand-built price sequence is
optional garnish, clearly labeled illustration-not-evidence.

**Difficulty.** Medium-high. The (ii) construction needs genuine care to avoid re-narrating
the paper's clusters example — the deliverable must derive the cluster structure *from the
timing adversary*. If that derivation turns out to be a one-line reduction, say so and
downgrade the claim honestly.

**Novelty risk.** v6 §6.7's "good-feedback-only reach" caveat states the *scope limit*; no
one has stated the *attack* (adversarial, truth-correlated timing) or the recovery condition
(timing ⫫ truth). Not adjacent to any off-limits Lean object (no Lean is proposed).
Off-limits check on framing: `averaging-hides-spikes` (run2, established) is about
average-vs-sup within rounds — different axis (magnitude concentration vs. schedule
selection); cite it as the sibling caveat, do not reprove it. Shadow test: the fake version
proves "if feedback never arrives, there is no unbiasedness" (vacuous truism); the real
version keeps eventual decidability of every item and derives recurrent bias from
truth-correlated delay alone, plus the (iii) recovery contrast.

---

## Q7 — Gate-tiling: is endorsement of a gated feedback process stable under the gated update itself?

**Title:** `gate-tiling` — the reflective-consistency test for legitimacy filters: does the
sober addict stay sober *and keep knowing why*?

**Claim (acceptance target).** A finite two-stage frame (all conclusions computed, explicit
rationals):

  Setup: worlds `W = Corrupt × Evidence × Θ`; prior `π`; a feedback channel `Y` (a function
  of Evidence and Corrupt); a **gate** `g` (a weight on feedback items, a function only of
  observables) intended to filter corrupted feedback. Stage-1 belief `π₁` := `π` updated on
  the *gated* feedback (conditioning where `g = 1`, discarding where `g = 0`; or Jeffrey
  weights — declare which). "Endorsement of the gated process" at a stage = the finite
  defect-zero condition over the declared finite weight family (indicator weights on
  observables — grid declared loudly).

  (i) **Instability witness (the content):** exhibit `(π, Y, g)` where stage-0 endorses
      gating over not-gating (computed: gated defect 0, ungated defect ≠ 0), **but** the
      gate filters exactly the evidence bearing on `Corrupt`, so `π₁`'s posterior on
      `Corrupt` is frozen at the prior, and stage-1 **no longer endorses the gate** for
      stage 2 (computed: from `π₁`, the gated process's defect is now nonzero, or the
      ungated one now has weakly smaller defect) — endorsement of the gate is **not
      preserved by the gated update**. The gate starves itself of its own justification.
  (ii) **Near-miss (mandatory):** the *gate-transparency* repair — the corruption indicator
      itself is always observed (only the payload is filtered) — restores preservation:
      stage-1 still endorses the gate, computed on the repaired frame. This certifies the
      instability's cause is filtering-the-justifier, not gating per se.
  (iii) **Interpretation (labeled):** this is the tiling/reflective-consistency face of
      legitimacy (plan.md: trust theorems via tiling): a legitimacy filter is only safe
      under RSI if gate-endorsement is a fixed point of the gated update, and (ii)'s
      transparency condition is the candidate sufficient condition. Connect to
      li-deference §0.3's drug analogy with the sharpened moral: the sober addict must keep
      *seeing the drug's existence* (transparency) while declining its payload — a policy of
      total avoidance destroys the knowledge that justifies avoidance in the successor.

**Why it matters.** li-deference §0.3 proposes the AI "should treat manipulation like sober
humans treat addictive drugs." Run1 formalized the *one-stage decline*
(`wirehead_declined`, off-limits). Nobody has asked the *dynamic* question — whether the
declining policy survives its own epistemic consequences — and that question is the
deference program's own signature move (tiling, v6 §8 "the tiling / Vingean-reflection
register") applied to its newest ingredient. A YES-always answer (instability impossible in
finite frames) would also be publishable within the lab: it would say gate-endorsement is
automatically self-reinforcing, a real (if suspicious — check for vacuity) structural fact.

**Modality.** LEAN-CORE (two-stage finite frame; posteriors and defects as explicit
rationals; both (i) and (ii) must compile).

**Difficulty.** Medium-hard. Two-stage bookkeeping is heavier than run1's one-stage frames;
the search for the instability witness may need an EXEC sweep first.

**Novelty risk.** The nearest off-limits objects: `Legitimacy.drug_defect_sign` (one-stage:
overshoot ⇒ defect sign) and `LegitimacyCorrigibility.wirehead_declined` /
`endorsed_signal_complies` (one-stage comply/decline verdicts). The differentiator is
structural and checkable: those results have **one** belief state and a sign conclusion;
this result's conclusion is a **comparison across the update** (endorsement-at-stage-0 vs.
endorsement-at-stage-1), an object that does not exist in any prior round. The
pre-registered fake: (a) an "instability" caused by choosing a stage-1 update rule that is
simply wrong (not Bayes on the gated record) — the real version uses genuine conditioning;
(b) hypothesizing the frozen posterior instead of computing it; (c) omitting the
transparency near-miss. Also distinct from run2 `edt-node-value` (decision-theoretic κ /
EDT-vs-UDT; no gates, no feedback filtering).

---

## Cross-cutting notes for the consolidator

- **Dependency structure:** Q5 (legitimacy is Π₁ ⇒ gates must be day-indexed) feeds Q2
  (gate design); Q3 (mechanism blindness ⇒ no statistical gate) motivates Q2's provenance
  condition and Q7's transparency condition; Q1 and Q6 are independent corruption channels
  (prophecy multiplicity; schedule attack). Q2+Q5+Q3 together would constitute a coherent
  first formal chapter of the legitimacy program: *what a legitimate gate must be* (future-
  indexed, generable, extra-channel, day-bounded) and *why nothing weaker works*.
- **Honesty pre-commitments:** every LEAN-CORE item above names its finite-grid limitation
  in the statement; every PROSE item is instance-checking against exact paper statements
  with the failing-hypothesis named; the fake versions are pre-registered per-question.
- **What I deliberately did not propose:** anything touching D3 / cross-agent
  LUV-Total-Trust discharge (v6 §8 calls it the common open problem; it is not a
  one-session target and every prior attempt reduced to it without discharging it);
  a minimal Lean market model (AUDIT rec. 5 — the right long-term fix, but "a project in
  its own right," and run3's session budget would produce exactly the kind of shadow the
  ground rules ban); and any re-run of run2's `trust-laundering` grid (worth doing, but it
  is a *repair* task owned by that TODO's spec, not a fresh-eyes question).

*End of scout file.*
