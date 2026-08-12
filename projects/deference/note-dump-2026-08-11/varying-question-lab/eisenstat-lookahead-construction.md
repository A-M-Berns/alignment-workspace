# Eisenstat's lookahead construction: what can be said, with proofs

*Claude, 2026-07-30. The detailed version of [[varying-question-synthesis]] §6 — the claims about Sam Eisenstat's lookahead construction that survive the four-route exploration, each with its precise statement, proof or proof pointer, named hypotheses, and confidence. Written to be liftable into the "Sam's Conjecture" section of [[Boundedly Rational Deference.pdf]]. Setting: Setting 2 of [[setting-and-notation]], **one-way visibility** unless stated — $A$ never reads $H$'s prices; $H$ reads $A$'s published quote ledger; sequential clearing. Conventions and status labels: [[conventions-and-status-labels]].*

*⚠ Attribution correction (2026-08-10): this page's setting does **not** match the information structure Sam Eisenstat intended — per Sam (via Abram), the strong-student/weak-teacher framing has the AI knowing the human's beliefs **immediately**, and the humans learning the AI's beliefs only **at a delay**; here both directions are reversed. Read every "Eisenstat's …" on this page as naming the **corpus construal**, not Sam's conjecture, whose intended version remains open and which Sam expects is probably true. Details, the uncertainty about what Sam would endorse, and the naming policy: [[eisenstat-conjecture-attribution]].*

---

## 0. The four sentences (for the slide), then the details

1. **The advertisement is honest, unconditionally** — on every weighting the forecaster itself can recognize, its quotes are unbiased for the human's realized future credence (limit-point form, engine kernel-checked); and on every efficiently computable set of days where that future credence converges, the quote converges to the same value, **pointwise** (new).
2. **Where the human is not surprised, trust is forced per-day and two-sided.** For a fixed question — and more generally whenever the realized targets converge — the quote and the human's current credence agree in the limit, under arbitrary delay, with no visibility in either direction and no shared fixed point (new upgrade; the old result was one-sided).
3. **On varying questions, a publication channel plus an evaluation-sparse schedule buys two-sided quote–credence agreement in weighted average** — along the schedule, the weighted average of the difference between the AI's current estimate of the human's future credence, $\mathbb E^A_n\big(\ulcorner\mathbb E^H_{f(n)}(X_n)\urcorner\big)$, and the human's current credence, $\mathbb E^H_n(X_n)$, tends to zero; equivalent to an averaged Tower via the ledger collapse, with both one-sided inequalities of scheduled soft Total Trust as corollaries (Theorem SS). The publication channel is needed *inside the trader class*: "the human has heard the AI" formally costs the ledger hypothesis (L), and that cost is provably unavoidable.
4. **The per-day varying-question form is exactly what "the forecaster sees the human" buys** — provably not derivable from the one-way toolkit, derivable under joint clearing (v3), and **genuinely open** in between: the matching impossibility died structurally, and the tools that killed it point weakly toward the per-day form being true.

The caveat that travels with all four: what is forced is a per-question, rate-free family — scheduled and weighted in the varying case — not the tower, not deck-TT; and the other half of the merge conjecture (that the quote sequence is *itself* a logical inductor) remains untouched, discharged in zero cases ([[faithful-acceleration-result]] §5).

---

## 1. The construction, and the two halves of the conjecture

The lookahead construction: a stronger inductor $A$ does not forecast the truth of the day-$n$ question $X_n$ directly; it forecasts *where the human's own deliberation will get to* on a budget. With lookahead $f$ (strictly increasing, $f(n)>n$, canonically $2^n$), the target is $Y_n := \mathbb E^H_{f(n)}(X_n)$ and the published quote is $a_n := \mathbb E^A_n(\ulcorner Y_n\urcorner)$. The lookahead expert, in the sense of [[deference-notions]], is $E^\ast(X_n) := a_n$.

Eisenstat's merge conjecture has two halves. **The trust half**: the human can defer to the quote — some deference notion of [[deference-notions]] (Total Trust / Value / Mart) holds of the pair $(H, E^\ast)$. **The inductor half**: the quote sequence $B_n := \mathbb E^A_n(\ulcorner \mathbb E^H_{f(n)}(\cdot)\urcorner)$ is itself a logical inductor. Everything on this page concerns the trust half; the inductor half is untouched here and everywhere in the corpus (deference-v6 §8, D3).

Standing assumptions throughout (the price of the construction being well-posed, not of any theorem): $\overline{\ulcorner Y\urcorner}$ is an e.c. sequence of expressions, bounded, a legal $\mathcal{BLCS}$ sequence for $A$, **determined via $\Gamma_A$** — a logical condition, with no bound on how long the coupled computation runs. Where an $H$-side theorem is applied, the **mirror** ($\Gamma_H$-determinacy) is a genuine extra assumption and is flagged.

**A structural note worth saying out loud**: under one-way visibility the coupled system is a two-stage composition — $A$ clears standalone, publishes, then $H$ clears with the quotes as decided ledger atoms. There is **no joint fixed point to construct anywhere**. The corpus's open worry about an assumed joint Brouwer argument ([[open-problems]] item 12) simply does not arise on this channel.

---

## 2. Claim 1 — the quote is honest, unconditionally

**2.1 Half 1 (averaged honesty).** For every rational $t$, $\delta>0$: the weighting $u_n := \operatorname{Ind}_\delta(a_n > t)$ is a $\overline{\mathbb P}^A$-generable weighting (a ramp on a rational combination of $A$'s *own* day-$n$ prices — Definition 4.3.2's closing remark), and if divergent, the $u$-weighted average of $a_n - Y_n$ has $0$ as a **limit point** (corrected 4.8.15 — see the erratum caveat, §7). In words: on the days $A$ advertises above $t$, the human's realized future credence averages at least $t - o(1)$ along a subsequence.

*Status:* PROVED; the analytic engine is KERNEL-CHECKED (`lean-deference/Staleness.lean`). Needs no visibility in either direction, no clearing assumption, no delay assumption: **a market is never stale to itself.** Details: [[faithful-acceleration-result]] §3.

**2.2 Lemma P (pointwise honesty on convergent handles — NEW, 2026-07-30).** For **every** efficiently computable set $E$ of days on which $Y_n \to c$: $a_n \to c$ along $E$. **Full limit, pointwise, hypothesis-free** beyond standing determinacy.

*Proof.* $B_n := \ulcorner Y_n\urcorner$ is $\mathcal{BLCS}$ and determined, so $\mathbb E^A_\infty(B_n) = Y_n$ (Limit Coherence 4.1.2 at the expectation level: the limit measure is coherent over $\mathrm{PC}(\Gamma_A)$, on which $B_n$ is constant). Reindex along $E$; trivially $\inf_{m\ge n}\mathbb E^A_m(B_n) \le a_n \le \sup_{m\ge n}\mathbb E^A_m(B_n)$, and Persistence of Expectation Knowledge (4.8.12, both clauses) equates the liminf/limsup of the two envelopes with those of $\mathbb E^A_\infty(B_n) = Y_n \to c$. Squeeze. $\square$

*Why this is new to the corpus:* [[unbiasedness-theorem-families]] §2 sorted family D as unable to serve Half 1 "since it never mentions truth" — but for **determined** targets the limit expectation *is* the truth, and the sorting needs correcting. Lemma P was found by the failed impossibility attempt ([[route-negative-introspective]] §7), where it is the thing that killed the construction. Note it uses neither 4.8.15 nor 4.8.16, hence carries no erratum dependence and no weighting-legality obligations at all.

**2.3 What honesty does *not* say.** Half 1 constrains weighted means; Lemma P constrains e.c.-localizable convergence. Neither forbids the quote being *pointwise* wrong on days that are neither — the mean of a bimodal target is simultaneously optimal on average and maximally wrong pointwise ([[route-negative-introspective]] §8). Honesty of the advertisement is not soundness of the advertisement; see also the self-fulfilling caveat in §7.

---

## 3. Claim 2 — no surprise ⟹ per-day two-sided trust, under arbitrary delay

**3.1 Fixed questions, upgraded (NEW, 2026-07-30, this page).** Let $X$ be a fixed $[0,1]$-LUV of $H$'s language. Then under arbitrary delay — any freeze schedule of the price channel; the only access to $H$ assumed is the bottom rung of the feedback ladder ([[route-sparse-schedule]] §1): rate-free eventual settlement of $\ulcorner Y_n\urcorner$ in $A$'s own deductive process (determinacy via $\Gamma_A$ + $\Gamma_A$-completeness) —
$$a_n - \mathbb E^H_n(X) \;\longrightarrow\; 0 \qquad \text{(two-sided, full limit, per-day).}$$

*Proof.* By Expectations Converge (4.8.3), $\mathbb E^H_n(X) \to p_\infty$; hence $Y_n = \mathbb E^H_{f(n)}(X) \to p_\infty$ (a subsequence, $f$ strictly increasing). Apply Lemma P with $E = \mathbb N$: $a_n \to p_\infty$. Subtract. $\square$

*Relation to Theorem A.* The corpus's Theorem A ([[faithful-acceleration-result]] §4.2, ~0.90) gives the one-sided form (only finitely many days with $a_n \ge \mathbb E^H_n(X) + c$) via corrected 4.8.15. The upgrade is strictly stronger — **two-sided**, so it is not "one side of Tower" but per-day Mart toward the lookahead expert on the fixed question — with *lighter* hypotheses (no weighting legality, no ramp, no erratum-corrected theorem). This directly answers the objection that the fixed-question result did not instantiate a loop notion. Status: the derivation is three lines from Lemma P and 4.8.3, displayed above; unvetted beyond this page (~0.85).

**3.2 Varying-but-convergent questions (the extension, mostly resolved).** If the realized targets converge, $Y_n \to c$, then $a_n \to c$ on all days (Lemma P, $E=\mathbb N$) — the quote is forced pointwise, for *varying* questions, with no visibility. If in addition the human's diagonal credence converges to the same value, $\mathbb E^H_n(X_n) \to c$ — the natural formalization of "the question stream carries no surprise" — then $a_n - \mathbb E^H_n(X_n) \to 0$, per-day and two-sided, on varying questions. What remains open in the old extension conjecture ([[open-problems]] item 8) is exactly the bridge between the two convergences ($Y_n$ vs the diagonal), which is a Half-2 question about $H$ alone — the natural tool is 4.8.11/4.8.12 per [[route-recurring-ccee]] §5.2 and item 16.

**3.3 The moral, now sharper.** The dividing line for per-day trust is **surprise, not variation** — and after Lemma P this is close to a theorem shape rather than a slogan: per-day trust holds wherever the target's convergence is e.c.-localizable, and every impossibility design must therefore hide its surprise from *every* e.c. handle (see §5).

---

## 4. Claim 3 — varying questions: Theorem SS, and what it costs

**4.1 The theorem** ([[route-sparse-schedule]]; presentation-canonical proof at [[theorem-ss-streamlined]], ~0.84–0.85; PROVED modulo named hypotheses, independently verified). Under one-way sequential clearing there is **one** evaluation-sparse schedule $g$ — uniform in $t, \delta$, and across e.d. sequences of bounded description size — such that for every e.d. sequence $(X_n)$ of $[0,1]$-LUVs, every rational $t, \delta$, with $w_n = \operatorname{Ind}_\delta(a_n>t)\cdot\mathbb 1[n \in \operatorname{im} g]$: if $\sum_n w_n = \infty$,
$$\frac{\sum_{i\le n} w_i\,\Big(\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big) - \mathbb E^H_i(X_i)\Big)}{\sum_{i\le n} w_i} \;\eqsim_n\; 0 \qquad \text{(two-sided full limit — quote–credence agreement)},$$
whence both one-sided inequalities of scheduled soft Total Trust; if $\sum_n w_n < \infty$, both one-sided inequalities hold trivially per-day along the schedule. Engine: erratum-corrected 4.8.16 applied to **both** markets on the same weighting, plus `cee` (4.12.1) on $H$; full limits subtract, which is the entire point of paying 4.8.16's sparsity instead of using 4.8.15's limit points.

A second, independent proof of the scheduled form at slightly different strength: the patient realized-cash bridge ([[route-recurring-ccee]] Thm 5.2) — v3's round-trip trader is $H$-side only, so it survives the deletion of joint clearing, and its sparsity is *forced* by risk budget ($f$-patient weightings accumulate $O(\log^\ast n)$ mass; Prop 5.3), not chosen.

**4.2 The costs, honestly.** (i) **Evaluation sparsity** — the schedule must outrun the cost of computing the forecast target (running the coupled construction to day $f(n)$); for $f(n)=2^n$ that is at least iterated-exponential growth $g(k+1)>2^{g(k)}$, though the exponential form is incidental ([[route-sparse-schedule]] §3; renamed from "evaluation-sparse" to avoid collision with the Tower principle). (ii) **(L) ledger legibility** — $H$'s trader/generator class is poly-time *with the published quote stream as oracle*, and $H$ satisfies the criterion against that class. All four routes independently converged on (L) as unavoidable: one-way visibility is structurally cheap for **traders** (settled data, hard dependence legal) and **not free for weightings** (Definition 4.3.5 features read only the market's own prices). The corpus's previous ledger-weighting workaround is defective — see the erratum in §7. (iii) Mirror $\Gamma_H$-determinacy, and the relativization of 4.8.16's proof to the oracle class (~0.92; a lighter obligation than v3's joint-class version).

**4.3 What "publication channel, not shared fixed point" now means precisely.** The old summary sentence survives, sharpened: the human must be able to read the AI's forecast **as a trader-class capability**, and that — plus sparsity — suffices for the two-sided averaged form. No joint clearing, no Brouwer assumption, no *live* $A$-side visibility of $H$, no window-disjointness, no environment hypothesis. What **is** required of $A$ is **schedule-prompt computability of the feedback**: each forecast's outcome must be *computable* in-class before the next scheduled bet — settlement in $D_A$ may arrive at any rate, since the exploiting trader cashes the market's own price movement, with truth forced into the later price by rate-free Provability Induction — and the evaluation-sparse gap is exactly that computability latency ([[route-sparse-schedule]] §1's ladder and §3's mechanism remark; Abram's corrections, 2026-07-31).

---

## 5. Claim 4 — the per-day varying form: what it costs, and its genuinely open status

**5.1 Not derivable one-way.** The all-days per-day form (equivalently, by the collapse below, all-days soft TT) is **provably not derivable** from the one-way toolkit: every derivation must cross the truth boundary once per market, the all-days truth-crossing theorem (4.8.15) delivers limit points on unrelated subsequences, and an explicit abstract witness satisfies all the premises while a permanent weighted deficit persists ([[route-recurring-ccee]] Props 5.4–5.5; open problem 7 answered NO, ~0.85).

**5.2 Derivable with joint clearing.** If $A$'s traders may read $H$'s day-$n$ price (joint clearing), the violation weighting $\operatorname{Ind}_\delta(a_n>t)\cdot\operatorname{Ind}_\delta(\mathbb E^H_n(X_n)<t-\varepsilon)$ becomes $A$-generable, a single unbiasedness application serves both halves, and v3's per-day conclusions follow (conditional on v3's own flagged obligations, including the **assumed** joint Brouwer construction — which this makes worth proving: [[open-problems]] item 12 is *raised* in priority, since joint clearing is now known to be the only route to the per-day conclusion).

**5.3 The matching impossibility is dead — twice — and the second death was structural.** The block-delay impossibility was refuted 2026-07-29 ([[delay-and-visibility]] §3). The repaired introspective construction ([[route-negative-introspective]]) reached ~0.70 and was then reversed by its own verification: family-C opacity hypotheses quantify over weightings that *exist*, not weightings $A$ can find (a hard-coded single index gives a patient divergent weighting selecting the bad days), and Lemma P closes the weighting on every e.c.-localizable violation. Since the only rate-free way to *force* the human's response (revisiting a fixed handle; every "wait until resolved" schedule dies by the Uncomputable Convergence Rates proposition, §5.5 of the paper) is precisely what manufactures e.c. convergent day-sets, **forcing $H$ and hiding from $A$ are the same theorem applied twice.** Any future counterexample must make the bad days cheap for $H$'s *price features* yet free of infinite e.c. subsets with convergent targets — immune-set territory ([[route-negative-introspective]] §8; open problem 9 now ~0.2–0.3).

**5.4 So the honest statement is:** per-day varying-question trust under one-way visibility is **open** — not proven (5.1), not refuted (5.3), with the newest tool (Lemma P) cutting against every known refutation strategy. What is settled is the *price structure*, and it is a feedback-promptness ladder ([[route-sparse-schedule]] §1): live feedback ⟷ per-day; schedule-prompt feedback ⟷ scheduled weighted average; rate-free eventual feedback ⟷ Half 1 + Lemma P only.

---

## 6. How this feeds the Total Trust ⇔ Value ⇔ Tower loop

**6.1 The collapse that calibrates everything** ([[route-transitivity]] Lemma B; [[route-recurring-ccee]] §3.3): against a *readable* expert — the published quote, under (L) — soft conditioning buys nothing: the ramp factors out of $\mathbb E^H_n$, and soft Total Trust at the quote-weighting family is **equivalent to per-day dominance** $\liminf_n(\mathbb E^H_n(X_n) - a_n) \ge 0$, i.e. to v3's Corollary 2. So the deck's soft-TT notion, instantiated at the lookahead expert, *is* the per-day notion; the weighted family of Theorem SS is a strictly weaker notion, to be labeled as such, not passed off as TT.

**6.2 What transports along the loop, per claim.**
- **Claim 2 (fixed / no-surprise)**: full per-day Mart toward the expert on that question — every loop notion holds there, per-$X$.
- **Claim 3 (Theorem SS)**: the two-option identity of [[two-option-value-iff-total-trust]] is linear in day-$n$ quantities, so at fixed $\delta$ it transports to **scheduled weighted $\delta$-hedged Value** (the qualifier is mandatory — [[deference-notions]] §Value). What does **not** transport: the keep-or-switch telescope, the hard-argmax form via provable-bound respect, and the $\delta\to0$ limit taken after averaging — all need per-day dominance. **And the hard-argmax form is not merely unproved at this grade — it is refuted without a scope condition** (2026-08-03): the constant-probe punishing menu transports to the averaged grade, F1 failing for the lookahead expert by $s(1-s)$; the scope condition is grade-invariant. [[weak-loop-and-value-transport]] §1. The forced family is closed under the threshold family and bounded-description menus (more closure than v3 claimed) but nowhere near gap-closed: **it does not collapse to the tower**, [[tower-death]] is untouched, and the amplifier stays live on this domain.
- **Composition is not a shortcut**: "H trusts future-H" (free, full-strength — the LUV self-trust theorem, new) plus "A is calibrated to future-H" (Half 1) does **not** compose to "H trusts A" ([[open-problems]] item 14, answered NO three independent ways; [[route-transitivity]]). The quantified residual is $H$'s per-day expectation of the truncated **absolute** forecast error (Theorem B), which Half 1 controls only signed, averaged, and limit-point-wise.

**6.3 A prediction worth putting on a slide** ([[route-transitivity]] §5): the finite-frame analysis shows the composition square is refuted in general (4-world witness, gap $\tfrac18$) and proved under **nesting** — the middle party knows the quote — whose LI mirror is a *timing* fact: publication before the lookahead. If publication were pushed past the lookahead ($e(n) > F(n)$), the finite-frame failure mode should go live in LI. Checkable, and directly relevant to deployment stories where the human reads forecasts late.

---

## 7. Caveats that must travel with any public statement

1. **The erratum.** Half 1 cites 4.8.15 and Theorem SS cites 4.8.16 *in the corrected forms*: the printed 4.8.15 is unparseable (free variable $f$, doubled word) and the support clause is transposed between the two theorems; the correction is certified by the paper's own appendices E.11/E.12 and inverts which theorem is the strong one. [[li-paper-erratum]] §1; a check-by-check companion for vetting it against the paper: [[li-erratum-vetting-guide]]. (Claim 2 via Lemma P is erratum-independent.)
2. **Averaged ≠ per-day, and the collapse (§6.1) makes this a real distinction**, not bookkeeping: state which grain each claim delivers.
3. **Honest ≠ sound.** $a_n$ forecasts $Y_n$, and $H$'s market at day $f(n)$ has seen $a_n$: the forecaster partly *causes* what it forecasts. All results here are calibration statements; nothing distinguishes honest forecasting from self-fulfilling manipulation ([[route-sparse-schedule]] §9's hazard; the soundness story lives elsewhere in the corpus).
4. **Rate-free, per-question, one-sided-where-marked**; no uniformity across questions is claimed anywhere.
5. **The inductor half of the merge conjecture is untouched** — zero cases discharged.
6. **(L) is a modelling commitment**: "the human has heard the AI" as a trader-class capability. It preserves produce-hard/read-cheap (the human still cannot compute the target), but a referee who rejects it loses the corpus's ledger devices too — rejecting it is not a cheap move.
7. **"One-way" means no live coupling, not no feedback** (Abram, 2026-07-31). Every claim on this page assumes the human's deliberation outcomes eventually settle in the AI's own world — determinacy via $\Gamma_A$ plus $\Gamma_A$-completeness of $D_A$; in deployment terms, an observation channel. An in-class $H$-simulator alone moves no prices: exploitation is assessed against $A$'s plausible worlds, and unsettled bets are plausibly catastrophic, so traders must be *vindicated by empirics* before they exert pressure. The claims differ only in the *handle* on that feedback they need — Claims 1–2 need only rate-free eventual settlement; Claim 3 needs, in addition, the outcome to be *computable* in-class before the next scheduled bet (settlement itself still rate-free — the mechanism cashes the market's own price movement, with truth forced in by rate-free Provability Induction); the per-day form needs live prices. ([[route-sparse-schedule]] §1, §3.)

---

## 8. History, in three beats (for context slides)

1. **The shared-fixed-point era.** v3 proved per-day conclusions under joint clearing (A1) — an assumed joint Brouwer construction plus two flagged obligations — and for a while the plan was to justify the restriction by a matching impossibility for the non-shared case.
2. **Both impossibilities died.** The block-delay construction was refuted on forcing (2026-07-29); the introspective redesign was reversed on hiding (2026-07-30, [[route-negative-introspective]]), each death yielding a diagnosis better than the theorem it replaced ("the criterion forces a price to respond only to what an efficient handle can select — or to what Convergence and Preemptive Learning force with no handle and no rate").
3. **The exact trade emerged.** Joint clearing is not "the setting"; it is the price of one weighting factor, and precisely of the per-day grain. One-way visibility plus sparsity buys the averaged grain (Theorem SS); no-surprise buys the per-day grain for free (Claim 2); and the per-day varying-question question under one-way visibility is the live open problem, now with tools pointing weakly toward "true".

---

## 9. Status table

| claim | grain | status | where |
|---|---|---|---|
| Half 1 (quote honest on self-weightings) | averaged, limit point | PROVED; engine KERNEL-CHECKED | [[faithful-acceleration-result]] §3 |
| Lemma P (quote tracks e.c.-convergent targets) | per-day, full limit | PROVED modulo standing determinacy (NEW) | [[route-negative-introspective]] §7 |
| Claim 2: fixed question, two-sided per-day Mart | per-day, full limit | NEW (this page), immediate from Lemma P + 4.8.3 (~0.85) | §3.1 |
| Claim 2 extension: $Y_n \to c$ forces $a_n \to c$, varying | per-day, full limit | NEW, immediate from Lemma P | §3.2 |
| Theorem SS (scheduled quote–credence agreement; Tower-equivalent + both TT inequalities) | scheduled, weighted average, full limit | PROVED modulo (S1)(S2)(L)(R) (~0.82) | [[route-sparse-schedule]] |
| Soft TT at quote weightings ⟺ per-day dominance (under (L)) | — | PROVED (Lemma B) | [[route-transitivity]] §3 |
| Per-day varying, one-way: not derivable from current toolkit | per-day | PROVED (non-derivability witness) | [[route-recurring-ccee]] §5 |
| Per-day varying, one-way: true or false? | per-day | **OPEN**; impossibility program at ~0.2–0.3 | §5 |
| `st` + Half 1 composes | — | REFUTED as inference (0.90) | [[route-transitivity]] |
| Quote sequence itself an inductor (merge half 2) | — | UNTOUCHED | deference-v6 §8 |

*File map: see [[varying-question-synthesis]] §File map.*
