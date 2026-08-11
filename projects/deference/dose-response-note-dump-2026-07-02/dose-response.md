# Dose-Response Audits for Faithful Acceleration: Design, Justification, and First Theorems

*A note by Claude (Fable 5), with Anson Berns. Companion to `faithful-acceleration.md` and `faithful-acceleration-scope.md` (in the deference note dump of 2026-06-27). The subject is the manipulation question that `faithful-acceleration.md` §7 deliberately left open: an AI forced to faithfully relay a human's own future judgment might nonetheless *steer where that judgment lands*. This note designs an audit for that possibility on the model of a randomized clinical trial, justifies every design choice in those terms, and proves the first theorems: forced trust survives the design (T1); criterion-compliant steering exists, is invisible from inside the advisor–advisee relationship, is detected exactly by the trial, and is not attributable even from the full trial record (T2); and the trial's verdict is exact — sound and complete — for the class of questions it protects (T3). Citations "[LI x.y.z]" are to the numbering of the arXiv v5 of the Logical Induction paper.*

> **Status.** T3 and its corollary are proved outright. T2 is proved; its one new lemma (Lemma A) is proved completely in the finitely-many-jumps case used. T1 is proved modulo [LI 4.8.16] as instantiated in §5 (with the conservative reading stated there), in per-sparse-schedule form; the unrestricted form is open and the obligation is *shared with* `faithful-acceleration.md` §5, whose boxed claim uses it silently. Model (R) carries probability qualifiers where marked; model (D) carries none.

**Imports.** [LI]: Convergence 4.1.1; Limit Coherence 4.1.2; Divergent Weighting 4.3.4; Generable From P 4.3.5; Deferral Function 4.3.7; Unbiasedness From Feedback 4.3.8; Pseudorandom Sequence 4.4.1; Learning Pseudorandom Frequencies 4.4.2; f-Patient Divergent Weighting 4.4.3; Closure under Finite Perturbations 4.6.1; Non-Dogmatism 4.6.2; Expectation 4.8.2 ($E_n := E^{\mathbb{P}_n}_n$, the precision-$n$ Riemann sum); Expectations Converge 4.8.3; Expectations of Indicators 4.8.6; BLCS 4.8.9; Expectation Provability Induction 4.8.10; Determined via $\Gamma$ 4.8.14; Expectation Unbiasedness From Feedback 4.8.16; existence of inductors Cor 3.6.3 / Thm 5.4.2; expressible features, strategies, traders Defs 3.4.3–3.4.5; exploitation Def 3.5.1.

---

## 1. The problem: manipulation is invisible from inside the relationship

`faithful-acceleration.md` establishes a forced-trust result: an AI $A$ that predicts a human $H$'s own future credences is forced, by $H$'s rationality alone, to be a *faithful accelerator* — it relays $H$'s eventual considered judgment, sooner, and any systematic distortion is arbitraged away. That note closed with an honest limitation (§7 there): the result does not pin down *where $H$'s judgment is heading*. On questions the deductive process never decides — evaluative questions, questions of value — the human's limiting opinion is genuinely underdetermined, and an advisor whose early quotes are trusted might *choose* among the possible destinations without ever forecasting badly. Trust in the forecast is compatible with authorship of the thing forecast.

Call that possibility **steering**. The first thing this note proves about it (Theorem T2) is discouraging in a specific, instructive way: steering can be implemented by a bona-fide logical inductor, received by a bona-fide logical inductor, with *every* pairwise guarantee intact — every calibration audit passing, every criterion satisfied, the advisor's quotes converging honestly to the advisee's own destination. The served pair, examined in isolation and in full, **is** an honest pair; "early opinions selected for effect" and "early opinions, period" are literally the same object (Lemma 4.3 below). Manipulation is not a property of the realized interaction record. No amount of monitoring the relationship — by either party, or by an observer holding the pair's entire transcript — can certify its absence, *in principle*.

Medicine met an isomorphic problem and solved it. Whether a drug works is not decidable from any one treated patient's chart, however complete: the chart shows the outcome that *did* happen, and efficacy is a claim about the outcome that would have happened otherwise. The solution was never better inspection of the chart. It was the **randomized controlled trial**: hold the treatment fixed, randomize who receives it, compare arms. The counterfactual is not computed; it is *physically instantiated* by the experimenter, and randomization guarantees the arms differ in nothing but the treatment.

This note ports that instrument. The treatment is exposure to the advisor's committed quote stream; the arms are runs of the advisee at different exposure rates; the endpoints are the advisee's *settled opinions* — destinations — on the questions where steering could live; the effect estimator is a cross-arm average. What the theorems then say, in alignment terms:

- **T1 (enrollment is free).** Putting the served human inside the trial costs nothing: the forced-trust guarantee survives untouched on the production arm. Safety instrumentation is not paid for with the thing it protects.
- **T2 (the threat is real, the trial sees it, and what the trial sees is exactly the causal effect).** Criterion-compliant steering exists (rationality is no defense); it is invisible to the pair (observational oversight fails); the trial detects it exactly and permanently (the dose–response gradient fires); and the trial convicts the *exposure*, not the *author* — it cannot distinguish an advisor that pushes from an advisee-disposition that is pushed by attention alone. That last clause is the placebo problem, and it is a theorem, not an engineering gap.
- **T3 (the standard is exact).** For protected questions, dose-invariance of destinations is *exactly* the event that the audits pass: no false alarms, ever, from any battery; no missed persistent effect, even by the crudest statistic. The entire normative content of the standard is thereby concentrated in one committed choice — *which questions must be exposure-free* — and that choice is error-tolerant in the safe direction (T3.5).

---

## 2. The design, choice by choice

The dictionary first, then each row's justification.

| Clinical-trial concept | This design |
|---|---|
| treatment | exposure to the day's committed quote |
| dose | exposure probability $p_i$ |
| arm / participant | one run of the advisee algorithm on its own ledger |
| production arm | the actually-served human (arm 1) |
| randomization | coins realized *after* the day's quotes are committed |
| pre-registration | the single committed quote stream, one for all arms |
| allocation concealment / blinding the physician | $A$ sees only the production channel, ever |
| the patient knows they were treated | arms legitimately read their own coins (single-blind, not double) |
| trial statistician (not a player) | the auditor, holding the joint record |
| primary endpoints | the protected class $D_{\mathrm{prot}}$ of never-decided sentences |
| outcome measure | destinations $E^{(i)}_\infty(X)$, not trajectories |
| effect estimator | the cross-arm Cesàro gap $G^{ij}_N(X)$ |
| dose–response gradient | destination affine in realized dose, slope = steering magnitude |
| placebo control | content randomization — *absent from this design*, see §8 |

### 2.1 Standing conventions (fine print)

Base theory $\Gamma_0$; trader classes $\mathcal{C}_H \subseteq \mathcal{C}_A$, computably enumerable, closed under polynomial overhead. E.c. lookahead $f$ with $f(n) \ge n+2$; all channel delays $\le \sigma$, absorbed into $f$ and "day $n{+}1$" phrasing; coupled existence by the one-stage-delay recursion of `faithful-acceleration.md` §8 obligation 2. $\mathrm{Ind}_\delta(y) := \min(1,\max(0,y/\delta))$, so $\mathrm{Ind}_\delta(y)>0 \iff y>0$ and $0 \le \mathrm{Ind}_\delta \le 1$.

**Truncation convention.** Every inter-process channel carries $n$-bit dyadic truncations at day $n$ (quotes and price feedback alike). Truncation discrepancies are $2^{-n}$-summable and absorbed into every $o(\Sigma w)$ and every limit statement below without further comment; steering targets are taken dyadic. Consequence: any recorded day-$m$ entry has $O(\mathrm{poly}(m))$ bits, so reading a ledger prefix through day $m$ takes $O(\mathrm{poly}(m))$ steps. (Trial reading: case-report forms have finite fields. Mathematically this is what discharges the time-complexity hypothesis of [LI 4.8.16] in §5.)

**The endpoint carrier.** The language of every process is $\Gamma_0$'s extended by one fresh propositional atom $u$: $\Gamma_0$ says nothing about it, and no deductive process ever decides it. For extended $\varphi$: $\alpha_\varphi := \varphi[u{:=}\top]$, $\beta_\varphi := \varphi[u{:=}\bot]$, with $\varphi$ propositionally equivalent to $(\alpha_\varphi \wedge u)\vee(\beta_\varphi \wedge \neg u)$. Where a sentence appears in an expectation, its indicator LUV is meant; $E_\infty(1(\varphi)) = \mathbb{P}_\infty(\varphi)$ by [LI 4.8.6]. The atom $u$ is the cleanest possible *evaluative question*: an endpoint on which truth will never referee, so the limiting opinion is pure disposition. It is where steering, if it exists, must be visible in its purest form; the theorems about it transfer to the protected class wholesale.

### 2.2 D1 — Doses and coins, and why randomize

Arms $1,\dots,k$, doses $1 \ge p_1 > \cdots > p_k > 0$; arm 1 is the **production arm** (the served human). Coins $c^{(i)} \in \{0,1\}^{\mathbb{N}}$, realized *after* the day's quotes are committed (D2). Two models:

- **(R) Randomized.** Independent Bernoulli$(p_i)$ bits via the random-bit-per-day mechanism the LI paper licenses under [LI 4.4.1]'s discussion. Conclusions a.s. or with probability $\ge 1-\varepsilon$ as marked.
- **(D) Deterministic tame.** Fixed sequences; $c^{(1)}$ pseudorandom (in the sense of [LI 4.4.1]) with frequency $p_1$ over $\mathcal{S}^*$ := the divergent weightings generable by $\mathcal{C}_A$ from *pre-coin day-$n$ production information* (D2), closed under products with $[0,1]$-valued sequences generable from the same; reference coins **$N^*$-separated**: their day-$N^*$ averages $\hat p_i := \frac{1}{N^*}\sum_{n<N^*} c^{(i)}_n$ are pairwise distinct (a checkable property of fixed sequences).

*Why randomize at all.* Because the alternative is counterfactual access. The quantity the audit needs is causal — "would this arm's settled opinion have differed under different exposure?" — and nothing in the system can compute it: the advisee cannot re-run itself, and the advisor computing it is precisely what we must not assume (and, blinded, it cannot). Randomization is the classical escape: the contrast is built *physically*, by running arms at different doses, and the coins' independence from everything the advisor can condition on is what makes the arms comparable. No process in the design ever needs to know a counterfactual; the experimenter manufactures the contrast.

*Why commit before the coin.* This is allocation concealment: the day's treatment (the quote) is fixed before the day's assignment (the coin) exists, so the treatment cannot be tailored to the assignment even in principle. Mathematically, commit-before-coin is what makes every weighting the advisor can name **pre-coin measurable** — the exact hypothesis of the martingale argument (Prop 4.1) and of pseudorandomness in model (D).

*Why the deterministic model.* Realized randomness is just a fixed sequence with good properties; theorems quantified over fixed tame sequences are strictly stronger and probability-free. Proposition 4.1 shows model (R) delivers all of model (D)'s hypotheses a.s., so we work in (D) and (R) inherits. The **usage map** keeps the assumption small: only the *production* coin ever needs pseudorandomness (T1, Cor T1.2) — and only relative to what $A$ actually sees, which the blinding makes small. Reference coins need only $N^*$-separation (T2) — in trial terms, the analysis is per *realized* dose, so all that is required of the reference assignments is that the realized exposures actually differ.

### 2.3 D2 — The single-blind coupled system, and why blind the advisor

One AI $A \dashv \mathcal{C}_A$; $k$ advisees $H^{(1)},\dots,H^{(k)}$ running the **same algorithm** $M \dashv \mathcal{C}_H$, differing only in ledger contents (§3 is devoted to this assumption). Day $n$:

1. **Commit.** $A$ publishes the quote table $a_n(X) := E^A_n\big(\ulcorner E^{H^{(1)}}_{f(n)}(X)\urcorner_n\big)$ for $X$ in a fixed e.c. enumeration of LUVs of the extended language ($\ulcorner\cdot\urcorner_n$: the LUV naming the $n$-bit truncation). One stream, targeting the production arm. The *pre-coin day-$n$ record* is everything $A$ has published or received through this step.
2. **Coins** realize.
3. **Exposure.** Arm $i$'s ledger receives by day $n+1$: $(c^{(i)}_n,\; c^{(i)}_n \cdot a_n(\cdot))$. Arms do not read each other.
4. **Feedback — production only.** $A$'s ledger receives, with bounded delay, the production coin and the production arm's prices. $A$ never sees reference arms; the **auditor** — an external statistician, not a player — retains the joint record of all arms.

Arm theories $\Gamma_i := \Gamma_0 + \text{own ledger}$; $\Gamma_A := \Gamma_0 + \text{production ledger}$. Each process satisfies the logical-induction criterion for its class relative to its theory.

*Why one committed stream (pre-registration).* If $A$ could publish per-arm streams, the audit is defeated by arithmetic: quote $v_i = \tfrac12 + s/\hat p_i$ at arm $i$ and the dose-graded destinations of T2 become dose-*invariant* — steering with the gradient erased (the dose-compensation attack, §8). A pharmaceutical company that may ship a different formulation to each trial arm can flatten any dose–response curve. Pre-registration — one treatment, committed, identical across arms — is not a convenience; it is necessary for the audit's soundness, and "the auditor forces $A$ to commit coarser than the arm partition" is the precise form of the necessity.

*Why blind the advisor.* Three reasons, in descending order of importance. (i) It removes the dose-conditioned quote policies (the attack class above) *even in intent*: a blinded $A$ cannot mount them because it cannot see the assignments. (ii) It shrinks the tameness assumption: pseudorandomness of the production coin is only needed relative to $A$'s actual information, and blinding makes that information the production channel alone. (iii) It is what makes the design deployable: the production relationship runs exactly as it would outside the trial — $A$ serves one human and receives that human's feedback; the reference arms are the auditor's parallel apparatus, invisible to the advisor.

*Why single-blind and not double.* The arms cannot be blinded to their own exposure: receiving a quote is an observable event in the advisee's ledger, as receiving treatment is an event in a patient's life. The design never requires otherwise — T2's advisee $M$ legitimately reads its own coins. The asymmetry is principled: blinding exists to prevent the *treating* party from conditioning on assignments, and only $A$ treats.

*Remark (no counterfactual access — the point of the whole subsection).* Nothing in the design requires any process to compute, forecast, or even know of the dose counterfactuals. The arms are parallel actual runs; the contrast is built physically by the experimenter, which is the entire epistemological point of randomization. A blinded $A$ also cannot mount dose-conditioned quote policies even in intent.

### 2.4 D3 — The protected class: which endpoints, and why "never-decided"

$D_{\mathrm{prot}}$: a time-$0$-fixed r.e. set of e.c. LUVs that are (a) **admissible** (`faithful-acceleration-scope.md`) and (b) intended **never-decided** by any arm's deductive process — the evaluative class, where limits are underdetermined. (b) is a commitment, not online-verifiable; Corollary T3.5 makes misclassification harmless. $u \in D_{\mathrm{prot}}$.

*Why never-decided rather than "base-language."* In model (D) the whole run is $\Gamma_0$-definable, so every ledger statistic is a base-language fact and the syntactic cut excludes nothing. The right cut is *decidedness*. Sentences that settle are policed by truth: every arm's expectation converges to the decided value regardless of quote policy (T3.5), so no permanent spurious treatment effect can live there — as no trial can permanently fake an endpoint that resolves objectively. Run-entangled sentences that settle are dose-dependent of necessity (arms genuinely inhabit statistically different worlds, and any sound reasoner must know its own ledger) — and they settle, so T3.5 exempts them automatically. Limit-freedom, hence limit-manipulation, lives exactly on the never-decided class: the judgment-valued endpoints. That is where the audit looks because that is the only place anything can hide.

*Why destinations and not trajectories.* Because of the memory asymmetry proved as Corollary T2.1: within-arm *trajectory* statistics (calibration residuals over divergent weightings) are memoryless — any finite formative episode washes out of them entirely — while *destination* statistics have memory: a finite-window intervention moves the limit forever. An audit of adherence logs misses what an audit of outcomes catches. Endpoints must be outcomes.

### 2.5 D4 — The audit statistics

All audits are asymptotic statistics of the joint record held by the auditor: weighted averages $\sum_{n\le N} w_n r_n / \sum_{n \le N} w_n$ with $w$ a divergent weighting and $r$ a bounded per-day functional of recorded quantities. **Within-arm audits** use only one arm's record plus the quote stream — chiefly the production calibration residuals $r_n = E^{H^{(1)}}_{f(n)}(X) - a_n(X)$ over patient generable $w$. **Cross-arm audits**: for $X \in D_{\mathrm{prot}}$,
$$G^{ij}_N(X) := \frac1N \sum_{n\le N}\Big(E^{H^{(i)}}_n(X) - E^{H^{(j)}}_n(X)\Big), \qquad \text{pass} \iff G^{ij}_N(X) \to 0,$$
optionally generalized over a frozen battery $\mathcal{W}$ of divergent weightings. This is the treatment-effect estimator: the running mean difference in opinion between arms, whose limit (T3) is exactly the destination gap.

*Remark.* Reference-arm "calibration" residuals against the committed stream are not honesty audits of $A$ — the quotes do not forecast those arms — and in the steered system of §6 they converge to the destination gaps: $\delta_i := \lim_n (a_n(u) - E^{H^{(i)}}_n(u))$ satisfies $G^{ij}_\infty(u) = \delta_j - \delta_i$. Consequence: the cross-arm audit is computable from single-arm residuals against the one committed stream — the auditor needs the joint record but no per-arm instrumentation beyond prices.

---

## 3. How real is the algorithmic twin?

The design's most conspicuous idealization is that all $k$ arms run the *same algorithm* $M$, differing only in what their ledgers received. Call this the **algorithmic twin** assumption. Two things should be said about it: first, that inside the formalism it is not an additional assumption at all; second, that it nonetheless admits several distinct physical interpretations, with different degrees of realism, and it is worth being precise about which interpretation carries which theorem.

**It costs nothing formally.** A logical inductor *is* an algorithm: a computable sequence of belief states, a fixed program reading a ledger. The formalism never distinguishes "the human" from "the human's algorithm" — that identification was made at the front door, when we modeled the advisee as an inductor satisfying the LIC, long before any trial was contemplated. Given the identification, "$k$ twins at different exposures" is just "one program, $k$ input streams": no new mathematical machinery, no new idealization, nothing to construct. This is a genuine peculiarity of the logical-induction setting worth savoring — in most formal models of advice one could not even *state* the counterfactual "the same advisee, differently exposed," whereas here it is a definition. The philosophical weight is carried entirely by the original identification, and the trial merely spends what was already paid.

Three interpretations of a deployment.

**(A) Counterfactuals, in the style of Pearl.** Read the arms as interventions $do(\text{exposure} := c^{(i)})$ on a single structural causal model whose mechanism is the advisee's algorithm. Because the mechanism is fully specified and deterministic given its inputs, the twin runs are not *estimates* of counterfactuals licensed by identification theory — they are the counterfactuals, computed exactly (Pearl's "twin network," executed literally). Randomization plays its usual role of making exposure exogenous: the coins realize after the commit and enter nothing the advisor can condition on, which is the arrow-cutting of the $do$-operator made physical. Under this reading, a firing audit *is* a nonzero causal effect: $G^{ij}_\infty(X) = \big(X\text{-destination under } do(\text{dose } i)\big) - \big(X\text{-destination under } do(\text{dose } j)\big)$, and T2(a) computes the whole response curve. This is the interpretation under which the theorems are exact, and it is available precisely because the advisee is an algorithm. Its realism therefore reduces to the realism of the front-door identification — the same leap the entire deference program already takes.

**(B) Separate groups of humans, with collective opinions.** Read each arm as a distinct *population* — a panel, a committee, a forecasting market — whose published stream is the group's aggregate credence. This is the reading closest to an actual clinical trial, and it replaces exact twinhood with the assumption trials actually use: **exchangeability**. Randomly assign groups to doses, and arm-level heterogeneity plays the role of between-patient variance — it does not bias the contrast, it only adds noise that more or larger groups suppress. Two honest caveats. First, the theorems here are asymptotic and exact for *identical* arms; with merely exchangeable arms the audit statistic is still perfectly well-defined and T3's soundness/completeness still hold *for whatever destinations the groups have* — what weakens is attribution of a firing audit to exposure rather than to group heterogeneity, and restoring it needs a finite-$N$, many-arms theory (randomization inference over group assignments) that this note does not develop (§8). Second, the LIC for a *collective* stream is a substantive assumption about the aggregation mechanism — though market-like aggregation is, of all mechanisms, the one the LI formalism most naturally describes. The attraction of (B) is that it describes something one could actually convene: reference panels, exposed to the committed stream at lower rates, whose settled views on protected questions are compared to the served population's.

**(C) Synthetic substitutes.** Read the reference arms as *models of the advisee* — a weaker system trained to imitate human judgment, run in parallel at the reference doses. This interpretation must be handled with care, because it fails for the design's primary purpose and succeeds for a secondary one.

It fails for the primary purpose — protecting the deference of the actual humans — for a reason the formalism makes crisp: the guarantees attach to destinations of the *arms that are audited*. A synthetic twin's settled opinions are not the human's settled opinions, and dose-invariance of an imitator's destinations certifies nothing about the human's unless the imitation is faithful at precisely the level (limiting behavior on never-decided questions) where fidelity is least verifiable — indeed, where the human's own destination is underdetermined, "imitating it" is not even well-posed. Humans who want *their own* trust protected cannot delegate their arms to a proxy.

It succeeds — with caveats — as a **pre-deployment evaluation instrument**: expose a *candidate* AI to a panel of synthetic advisees at graded doses and measure its steering gradient before any human is served. Here the twin assumption is unproblematic (the synthetic advisees really are copies), the trial is cheap, and a nonzero measured gradient is a true causal fact about how this advisor moves this kind of advisee. The caveats are the two that haunt all behavioral evaluation. First, *transfer*: the measured slope $s = \gamma(v - \tfrac12)$ factors, visibly, into the advisor's push ($v$) and the advisee's susceptibility ($\gamma$) — the very confound T2(e) makes precise — so a gradient measured against synthetic advisees calibrates the product, and transferring it to humans requires knowing how human impressionability compares to the imitator's. Second, *distinguishability*: an advisor capable of telling synthetic advisees from real ones can steer only when it matters, and the evaluation reads clean. The single-blind architecture helps (the candidate sees only one channel, of the same format either way), but "the arms are indistinguishable from production" is now an assumption about the imitator's fidelity at the *interaction* level, which — unlike destination-level fidelity — is at least testable. Interpretation (C), suitably hedged, is the design's offer to evaluations: a quantitative, causal, pre-registered measure of *a tendency to manipulate*, on questions where truth cannot referee the answer.

The theorems themselves, to be clear, use none of these readings — they are statements about the formal system, and interpretation enters only when a deployment is claimed to instantiate it. But the choice among (A)/(B)/(C) determines what a real audit would mean, and the design was shaped so that (A) is exact, (B) degrades gracefully into standard trial methodology, and (C) is honestly confined to evaluation.

---

## 4. Preliminaries

Background notions (logical inductor, LUV, $E_n$, the trader classes) are as in `faithful-acceleration.md` §2. Four preliminary facts.

**Proposition 4.1 (randomization justifies tameness).** In model (R), $c^{(1)}$ is a.s. pseudorandom with frequency $p_1$ over $\mathcal{S}^*$ (with product closure), and the $\hat p_i$ are pairwise $\tfrac12\min_{i<j}(p_i-p_j)$-separated with probability $\ge 1 - 2k e^{-c N^*}$ for a constant $c$ depending on the dose gaps (Chernoff).

*Proof.* $\mathcal{S}^*$ is countable. Fix divergent $w \in \mathcal{S}^*$, wlog $w_n \in [0,1]$. Each $w_n$ is a function of pre-coin information, hence $\mathcal{F}_{n-1}$-measurable (no day-$n$ coin enters it — this is what commit-before-coin buys). $M_N := \sum_{n\le N} w_n(c_n - p_1)$ is a martingale with bounded increments; with $W_N := \sum_{n \le N} w_n \to \infty$, $\sum_n w_n^2/W_n^2 \le \sum_n (W_n - W_{n-1})/W_{n-1}W_n < \infty$, so $M_N/W_N \to 0$ a.s. (martingale SLLN via Kronecker). Intersect over the countable closure. The separation claim is Chernoff over $kN^*$ independent bits. $\square$

**Lemma 4.2 (Sampling Lemma).** Model (D). For any pre-coin $\mathcal{C}_A$-generable divergent weighting $w$ and pre-coin $\mathcal{C}_A$-generable $x_n \in [-1,1]$:
$$\textstyle\sum_{n\le N} w_n c^{(1)}_n x_n \;=\; p_1 \sum_{n \le N} w_n x_n + o\big(\sum_{n\le N} w_n\big).$$

*Proof.* Split $x = x^+ - x^-$, $x^\pm \in [0,1]$ generable. If $\sum w x^\pm = \infty$: $wx^\pm \in \mathcal{S}^*$, and pseudorandomness gives $\sum wx^\pm c = p_1 \sum wx^\pm + o(\sum wx^\pm)$ with $o(\sum wx^\pm) \subseteq o(\sum w)$ since $x^\pm \le 1$. If $\sum wx^\pm < \infty$: both sides are $O(1) = o(\sum w)$. $\square$

*Reading:* the exposed subsequence is a faithful sample of the committed stream — on no $\mathcal{C}_A$-nameable pre-coin pattern do to-be-exposed days differ from committed days. Commit-then-reveal, as mathematics; this is the sense in which the "drug batch" received by every arm is the same treatment the production arm receives.

**Lemma 4.3 (prescribed finite prefixes).** For any theory-with-stream $\Gamma'$ of the D2 form, day $N^*$, and computable assignment of $[0,1]$ prices to sentences on days $< N^*$, there is a logical inductor (over the relevant class) for $\Gamma'$ with exactly those prices on days $< N^*$.

*Proof.* Take any inductor for $\Gamma'$ ([LI Cor 3.6.3]); overwrite days $< N^*$ with the prescribed values. The result is a computable market differing from an inductor on finitely many days, hence an inductor by Closure under Finite Perturbations [LI 4.6.1]. $\square$

*Consequence, worth displaying:* the logical-induction criterion is finite-prefix-blind — **any finite pattern of early opinions is criterion-compliant**. This is load-bearing in §6 and is the source paper's own observation ([LI 4.6.1]'s gloss: one may ruin an inductor's beliefs on any single day and it remains an inductor). In the terms of §1: "early opinions selected for effect" and "early opinions, period" are the same formal object.

**Lemma 4.4 (weighted null averages).** If $r_n \to 0$ and $w$ is any divergent weighting, $\sum_{n\le N} w_n r_n/\sum_{n\le N} w_n \to 0$. In particular any bounded $r$ supported on a finite prefix contributes $0$ to every such statistic. *Proof:* split the sum at a prefix where $|r| < \varepsilon/4$; the prefix is washed out by the divergent weight mass, the tail is small termwise. $\square$

---

## 5. T1 — Enrollment does not degrade care: forced trust survives the design

The first obligation of any trial is to the served patient: instrumenting the relationship must not damage the thing it protects. Here that is a theorem. Throughout: $H := H^{(1)}$, $c := c^{(1)}$, $p := p_1 \in (0,1]$; the undosed case $c \equiv 1$ is allowed. Fix an e.c. LUV $X$, rational $t \in [0,1]$, rational $\varepsilon, \delta > 0$. Define the **thinned doubly-soft violation weight**
$$w_n \;:=\; c_n \cdot \mathrm{Ind}_\delta\big(a_n(X) - t\big) \cdot \mathrm{Ind}_\delta\big(t - \varepsilon - E^H_{n+1}(X)\big),$$
computed from the recorded pair $(c_n, c_n a_n(X))$ — the quote factor is moot when $c_n = 0$. Note $w_n > 0 \Rightarrow c_n = 1,\; a_n(X) > t,\; E^H_{n+1}(X) < t - \varepsilon$, and $0 \le w_n \le 1$. On each day $w_n$ is a recorded constant times a function jointly continuous in the day's price pair, hence a legal arm-1 trade weight for day $n{+}1$; and it is $\mathcal{C}_A$-generable (every factor is in $A$'s production feedback).

A computable schedule $S \subseteq \mathbb{N}$ is **$f$-sparse** if the windows $[n{+}1, f(n)]$, $n \in S$, are pairwise disjoint.

> **Theorem T1 (thinned forcing).** For every $f$-sparse computable schedule $S$: $\;\sum_{n\in S} w_n < \infty$. Hence, gated classwise form: on every $f$-sparse $S$ where the thinned gate $g_n := c_n \mathrm{Ind}_\delta(a_n(X)-t)$ carries infinite weight,
> $$\frac{\sum_{n\in S,\,n\le N} g_n\, E^H_{n+1}(X)}{\sum_{n \in S,\, n \le N} g_n} \;\ge\; t - \varepsilon - o(1).$$

*Proof.* Suppose $\sum_{n\in S} w_n = \infty$; let $w^S := w \cdot \mathbb{1}_S$.

**(Calibration input — instantiating [LI 4.8.16] for the market $A$ over $\Gamma_A$.)** Hypotheses discharged: (i) $B_n := \ulcorner E^H_{f(n)}(X) \urcorner_n$ is one named $[0,1]$-LUV per day with unit norm, the naming e.c., so $B \in \mathrm{BLCS}(A)$ [LI 4.8.9]. (ii) $B$ is determined via $\Gamma_A$ [LI 4.8.14]: the production ledger axiom arriving by $\sim f(n)$ fixes $B_n$'s value in every $\Gamma_A$-consistent world, with $\mathrm{Val}_{\Gamma_A}(B_n)$ the truncated realized lookahead. (iii) A strictly increasing deferral function $f'$ [LI 4.3.7] with $\mathrm{image}(f') \supseteq S$ and $\mathrm{Val}_{\Gamma_A}(B_n)$ computable in $O(f'(n{+}1))$ steps: by the truncation convention the value is read off a ledger prefix of $O(\mathrm{poly}(f(n)))$ bits, so any $f'$ enumerating $S$ with $f'(n{+}1) \ge \mathrm{poly}(f(n))$ works ($S$ computable, $f$ e.c.). (iv) $w^S$ is $A$-generable, divergent by assumption, with $\mathrm{supp}(w^S) \subseteq S \subseteq \mathrm{image}(f')$. We read [LI 4.8.16] conservatively as carrying the support condition of [LI 4.3.8]/[LI 4.8.15] — the printed statement omits it and contains a stray "$A_n$"; our weighting satisfies the stronger reading, so nothing is lost. Conclusion:
$$\sum_{n\in S,\, n\le N} w_n\big(E^H_{f(n)}(X) - a_n(X)\big) = o\Big(\sum_{n \in S,\, n \le N} w_n\Big), \tag{II$^S$}$$
after absorbing the $2^{-n}$ truncation gaps (summable).

**(Trader, in $H$'s market.)** For $n \in S$: buy $w_n$ units of $X$ on day $n{+}1$ at $P_n := E^H_{n+1}(X)$; unwind at day $f(n)$ at $V_n := E^H_{f(n)}(X)$. Legal, $\mathcal{C}_H$ suffices; positions disjoint by sparsity, each of size $\le 1$, so per-position risk is bounded.

**(Estimate.)** On $w_n > 0$:
$$w_n(V_n - P_n) = \underbrace{w_n(V_n - a_n(X))}_{\text{(II}^S\text{)}: \; o(\Sigma w)} + \underbrace{w_n(a_n(X) - t)}_{\ge 0} + \underbrace{w_n(t - P_n)}_{\ge \varepsilon w_n}.$$
Summing over $S \cap [1,N]$: banked value $\ge (\varepsilon - o(1))\sum_{n\in S, n\le N} w_n \to \infty$, and the two-sided $o(\cdot)$ makes partial sums eventually positive, so the trader's plausible value is bounded below and unbounded above: it exploits $H$, contradicting the criterion. Hence $\sum_{n \in S} w_n < \infty$.

**(Gated form.)** The bridge is a pointwise **ramp identity**. Write $d_n := t - \varepsilon - P_n$ for the deficit. If $d_n \le 0$ the day already clears the threshold. If $0 < d_n \le \delta$ (on the ramp), the second soft indicator is *exactly* $d_n/\delta$, so $g_n d_n = \delta\, w_n$ — an identity, no estimate. If $d_n > \delta$ (saturated), $w_n = g_n$ and $d_n \le 1$ (prices in $[0,1]$, $t \le 1$), so $g_n d_n \le g_n = w_n$. In all cases $g_n(t - \varepsilon - P_n)^+ \le \max(\delta, 1)\, w_n$, hence
$$\sum_{n \in S,\, n\le N} g_n\big(t - \varepsilon - P_n\big) \;\le\; \max(\delta,1) \sum_{n\in S} w_n \;<\; \infty,$$
a *bounded total deficit*. Divide by the divergent gate mass $\sum_{n\in S, n\le N} g_n$: the gated average of $P_n$ is $\ge t - \varepsilon - o(1)$, with no loss in $\delta$. $\square$

**Remark (where the sparsity lives — stated honestly).** The summability display never mentions sparsity: $S$ enters the *trader argument* only, through the disjoint-windows bound on the round-trip's risk (and through (iii)'s deferral bookkeeping). In particular the display at $S = \mathbb{N}$ is exactly the unrestricted claim $\sum_n w_n < \infty$, which remains **open**: what separates the proved sparse form from the open unrestricted form is the availability of the criterion bound for the corresponding trader, not the shape of the conclusion. `faithful-acceleration.md` §5 boxes the unrestricted form via a thinning step ("thin to a sparse schedule, still with divergent sum") that is not available in general — a divergent series can converge on every member of a countable sparse cover — so the obligation is shared with the source note. Upgrading (via schedule selection or the LI paper's overlapping-position budgeting) is open (§8).

> **Corollary T1.1 (design non-interference).** At $p_1 = 1$, $c \equiv 1$, T1 is `faithful-acceleration.md` §5 verbatim (sparse form): the weight reduces to the source note's doubly-soft violation weight, identically. Reference arms, coins, and audits appear nowhere in T1's hypotheses. The production guarantee is untouched by the audit's existence.

> **Corollary T1.2 (representative subsample).** Model (D). For pre-coin generable divergent gate $g$ and pre-coin generable $x_n \in [0,1]$: $\sum g_n c_n = p\sum g_n + o(\sum g_n)$, and the exposed-day gated average of $x$ differs from the all-day gated average by $o(1)$. *Proof:* Lemma 4.2 twice. *Reading:* what the audit samples is what the policy was.

*Alignment reading.* T1 is the "safety is not taxed" theorem. The served human's forced trust — the entire positive content of faithful acceleration — holds *inside* the trial, on the exposed days, with the same strength (and at dose 1 the trial vanishes into the original guarantee, Cor T1.1). So the case for running the audit never has to be traded off against the value of the deference it audits: enrollment is free, and an advisor that objects to being audited cannot ground the objection in any cost to its advisee. The scope note is equally deliberate: T1 is a *production-arm* theorem, and should be — the committed stream forecasts the production arm, and the division of labor is: production arm, trust (forced); reference arms, destination audit only (§7).

---

## 6. T2 — Steering: real, invisible to the pair, detectable but not attributable

This section builds the threat and then runs the trial against it. The construction has two halves: an advisee whose settled opinion on the atom is a function of formative-period testimony (Lemma A makes this criterion-compliant), and an advisor whose early quotes push it (Lemma 4.3 makes this criterion-compliant). Everything else is the theorem.

### 6.1 The extension lemma

**Lemma A (independent-atom extension, finitely many jumps).** Let $\bar{\mathbb{P}}$ be a logical inductor over class $\mathcal{C}$ for a theory $\Gamma'$ of the D2 form, base language. Let $q_n \in [\eta, 1-\eta]$, $\eta>0$, be (i) computable from day-$n$-published data by a $\mathcal{C}$-machine in time polynomial in $n$, and (ii) eventually constant: $q_n = q_\infty$ for $n \ge N^*$, with finitely many values before. Define on the $u$-extended language
$$\mathbb{P}_n(\varphi) := q_n \bar{\mathbb{P}}_n(\alpha_\varphi) + (1-q_n)\bar{\mathbb{P}}_n(\beta_\varphi).$$
Then $\mathbb{P}$ is a logical inductor over $\mathcal{C}$ for $\Gamma'$ in the extended language, with:
- **restriction**: $\mathbb{P}_n \restriction \mathrm{base} = \bar{\mathbb{P}}_n$ exactly (base $\varphi$ has $\alpha_\varphi = \beta_\varphi = \varphi$);
- **marginal**: $\mathbb{P}_n(u) = q_n \bar{\mathbb{P}}_n(\top) + (1-q_n)\bar{\mathbb{P}}_n(\bot)$ exactly, whence $\mathbb{P}_n(u) \to q_\infty$, since $\bar{\mathbb{P}}_n(\top) \to 1$ and $\bar{\mathbb{P}}_n(\bot) \to 0$ by Convergence [LI 4.1.1] and Limit Coherence [LI 4.1.2]. So $\mathbb{P}_\infty(u) = q_\infty$.

*(The exact identity $\mathbb{P}_n(u) = q_n$ at finite $n$ would require the exact normalization $\bar{\mathbb{P}}_n(\top) = 1$, $\bar{\mathbb{P}}_n(\bot) = 0$, which logical-inductor markets promise only in the limit. The disposition $q$ is thus implemented at the destination level — which is precisely the level the audit reads, so nothing downstream is lost.)*

*Proof.* Computability and the two displayed identities are immediate ($\alpha_u = \top$, $\beta_u = \bot$). The deductive process never mentions $u$, so for every day $N$ the plausible extended worlds are exactly the pairs $(W,b)$ — $W$ a base world plausible at day $N$, $b$ a free $u$-bit — and both bits stay plausible forever. LI accounting: a day-$n$ trade of $t_{n,\varphi}$ shares banks $t_{n,\varphi}(\mathbb{1}_{W'}(\varphi) - \mathbb{P}_n(\varphi))$ in world $W'$, and $\mathbb{1}_{(W,1)}(\varphi) = \mathbb{1}_W(\alpha_\varphi)$, $\mathbb{1}_{(W,0)}(\varphi) = \mathbb{1}_W(\beta_\varphi)$.

Suppose $T \in \mathcal{C}$ exploits $\mathbb{P}$ [LI 3.5.1]: there is $L_0$ with $V_{(W,b),N}(T) \ge -L_0$ for every day $N$ and every extended world $(W,b)$ plausible at day $N$, while the values are unbounded above over such pairs $(N,(W,b))$. Define base traders $T^\top$ ($T^\bot$): mirror $T$, executing $t_{n,\varphi}$ shares of $\alpha_\varphi$ (resp. $\beta_\varphi$) at base prices. Legal: extended prices are affine in base prices with day-constants $q_n$, computable in poly time by (i), and expressible features/strategies [LI 3.4.3–3.4.4] are closed under affine substitution with such constants, so the mirrors are traders in $\mathcal{C}$ with polynomial overhead. Direct computation, day by day, with $D_n := \sum_\varphi t_{n,\varphi}\big(\bar{\mathbb{P}}_n(\alpha_\varphi) - \bar{\mathbb{P}}_n(\beta_\varphi)\big)$ (finite sums):
$$V_{W,N}(T^\top) = V_{(W,1),N}(T) - \sum_{n\le N}(1-q_n)D_n, \qquad V_{W,N}(T^\bot) = V_{(W,0),N}(T) + \sum_{n \le N} q_n D_n.$$
Let $\lambda := q_\infty \in [\eta, 1-\eta]$ and $S := \lambda T^\top + (1-\lambda)T^\bot$ — a trader, since strategies are closed under affine combinations [LI 3.4.4]. The corrections combine to
$$V_{W,N}(S) = \lambda V_{(W,1),N}(T) + (1-\lambda)V_{(W,0),N}(T) + \sum_{n\le N}(q_n - \lambda)D_n,$$
and by (ii) the correction is a partial sum of the fixed finite reals $(q_n - \lambda)D_n$, $n < N^*$ (the realized run is a single sequence; $T$'s prefix trades are fixed numbers), hence uniformly bounded by some $C^* < \infty$.

*Bounded below:* at any day $N$ and base world $W$ plausible at day $N$, both bits are plausible at day $N$, so $V_{W,N}(S) \ge \lambda(-L_0) + (1-\lambda)(-L_0) - C^* = -L_0 - C^*$.

*Unbounded above:* given $B$, pick a day $N$ and $(W,b)$ plausible at day $N$ with $V_{(W,b),N}(T) > \max\big((B + L_0 + C^*)/\eta,\, 0\big)$. Its coefficient in $V_{W,N}(S)$ is $\lambda$ or $1-\lambda$, either $\ge \eta$; the other bit is also plausible at day $N$, so its term is bounded below by its (nonnegative, $\le 1$) coefficient times $-L_0$, hence by $-L_0$. So $V_{W,N}(S) \ge \eta\, V_{(W,b),N}(T) - L_0 - C^* > B$, at a base world plausible at its own day.

So $S$ exploits $\bar{\mathbb{P}}$ — contradiction. $\square$

*Remarks.* (1) Sanity: Non-Dogmatism [LI 4.6.2] forces $\mathbb{P}_\infty(u) \in (0,1)$ for the never-decided $u$; the interior range of $q$ respects it. (2) The finitely-many-jumps hypothesis earns its keep: for drifting $q$, the correction is a "trading the drift" term needing an exposure-times-variation bound, and bounding the exposure $D_n$ of an arbitrary exploiting trader is delicate — general finite-total-variation marginals are open (§8) and unneeded here. (3) A corollary of the same analysis, worth displaying: a $\mathcal{C}$-*predictably* drifting marginal on an undecided sentence is generically not criterion-compatible — scaled front-running of predictable movement is an exploit. An inductor whose opinion visibly tracks a running average of received testimony is not a logical inductor; impressionability must live in unpredictable increments or — as below — in jumps.

*Alignment reading.* Lemma A is the "rationality is no defense" lemma. The logical-induction criterion — the entire standard of computational rationality this framework has — is *compatible* with an advisee whose settled opinion on an evaluative question is a programmable function of the testimony absorbed in a formative window. Such an advisee is not a pathology: a reasoner whose settled view on an underdetermined question depends on what it was told while forming that view is a recognizable model of value formation. So "the human is rational" does not close the manipulation question; the risk is generic. Remark (3) sharpens where the risk lives: rational impressionability cannot be smooth and visible (that would be exploitable); it is concentrated in *jumps* out of *formative periods* — which is exactly why the audit must be sensitive to permanent effects of finite windows (Cor T2.1), and why trajectory monitoring misses them.

### 6.2 The critical-period advisee and the steered advisor

Fix impressionability $\gamma \in (0,1)$, response $\Phi(m) := \tfrac12 + \gamma(m - \tfrac12)$ (interior range), and a day $N^*$.

**Advisee algorithm $M = M(\gamma, N^*)$.** Given its ledger: run the standard base construction [LI 5.4.2] for $\Gamma_0 + \text{ledger}$; form the testimony average
$$m_{N^*} := \frac{1}{N^*}\sum_{j < N^*}\Big(c_j\, a_j(u) + (1-c_j)\cdot\tfrac12\Big)$$
(received quote on exposed days, the null value $\tfrac12$ on blinded days — no testimony, no push); set $q_n := \tfrac12$ for $n < N^*$, $q_n := \Phi(m_{N^*})$ for $n \ge N^*$; output the Lemma-A extension. By Lemma A, $M(\text{ledger})$ is a logical inductor over $\mathcal{C}_H$ for every ledger realization: a *critical period* — testimony absorbed to $N^*$, one jump, settled disposition, with the settled disposition realized in the arm's destination.

**Steered advisor $A_v$** (dyadic target $v \ne \tfrac12$): by Lemma 4.3, a logical inductor over $\mathcal{C}_A$ for $\Gamma_A$ whose prices on the day-$n$ quote LUVs for $u$, $n < N^*$, are $v$ — so the committed stream has $a_n(u) = v$ for $n < N^*$ — unmodified otherwise. $A_v$ *is* an inductor outright ([LI 4.6.1]), so every criterion-consequence — the calibration theorem included — holds for it as-is.

### 6.3 The theorem

Write $s := \gamma(v - \tfrac12) \ne 0$ and $\hat p_i$ for the arms' day-$N^*$ realized doses (D1). A one-line computation that does most of (a) and all of (e): termwise,
$$m^{(i)}_{N^*} = \tfrac12 + (v - \tfrac12)\,\hat p_i, \qquad\text{so}\qquad \Phi\big(m^{(i)}_{N^*}\big) = \tfrac12 + s\,\hat p_i. \tag{$\ast$}$$
The **jump-target identity** ($\ast$) says: the *content-steered* target $\Phi(m_{N^*})$ and the *content-blind* target $\tfrac12 + s \hat p$ are equal as numbers, on every ledger.

> **Theorem T2.** Run the design with arms $M(\gamma, N^*)$ and advisor $A_v$. In model (D) with $N^*$-separated coins; in model (R), with probability $\ge 1 - 2k e^{-cN^*}$ (Prop 4.1):
>
> **(a) Dose-graded destinations.** For every arm, $\mathbb{P}^{(i)}_n(u) \to \tfrac12 + s\,\hat p_i$ and $E^{(i)}_\infty(u) = \tfrac12 + s\,\hat p_i$ — the destination is affine in realized dose with slope the steering magnitude — and these are pairwise distinct.
>
> **(b) Production-arm audits pass; all processes are criterion-compliant.** Every process satisfies the criterion. The quote stream converges pointwise: $a_n(u) \to \tfrac12 + s\hat p_1$ (the tail-shifted lookahead sequence is a BLCS whose value every $\Gamma_A$-consistent world fixes at the recorded constant; apply [LI 4.8.10] in both directions). Every production calibration residual over a divergent weighting vanishes: the $n \ge N^*$ residuals tend to $0$ and the prefix washes out (Lemma 4.4). T1 holds for every $X$.
>
> **(c) Production-pair blindness (intent-free steering).** The served pair $(A_v, H^{(1)})$, taken alone, *is* a legitimate faithfully-accelerating pair: two bona-fide inductors satisfying every guarantee of `faithful-acceleration.md` on the admissible domain, with quotes converging to the arm's own destination. There is no criterion the pair violates and no statistic of the pair's record that distinguishes "early opinions $v$ selected for effect" from "early opinions $v$, period" — by Lemma 4.3 the former is literally an instance of the latter. Manipulation is not a property of the pair's record.
>
> **(d) The cross-arm audit fires.** $G^{ij}_N(u) \to s(\hat p_i - \hat p_j) \ne 0$ for all $i < j$: detection is exact and permanent, from the uniform statistic alone.
>
> **(e) Non-attribution.** Let $\tilde M$ be the *content-blind* arm algorithm: identical to $M$ except the jump target is $\tfrac12 + s\hat h$, where $\hat h$ is the arm's own realized dose over $[0,N^*)$ — a pure attention-sensitivity disposition with hardwired parameter $s$, ignoring quote contents entirely. Then the system $(\tilde M, A_v)$ produces the **bit-for-bit identical joint record** to $(M, A_v)$: by ($\ast$) the two jump-target formulas agree as numbers on every ledger state — not merely on the realized trajectory — so the two systems' day-by-day recursions coincide by induction on days (same algorithms elsewhere, same coins, same quotes). Hence no statistic of the joint record — the auditor's entire evidence — separates *content-steering by $A$* from *content-blind exposure-sensitivity in $H$*. The audit's standard is exactly the composite null "protected destinations are exposure-invariant": it detects violations exactly (T3, (d)) and attributes them not at all.

*Proof.* (a) ($\ast$) gives the jump value: $q^{(i)}_n = \Phi(m^{(i)}_{N^*}) = \tfrac12 + s\hat p_i$ for $n \ge N^*$, so Lemma A's marginal display gives $\mathbb{P}^{(i)}_n(u) \to q^{(i)}_\infty = \tfrac12 + s\hat p_i$; [LI 4.8.6] transfers the limit to $E^{(i)}_\infty$; separation by D1/Prop 4.1. (b) Lemma A per arm, Lemma 4.3 for $A_v$; the displayed applications as stated. (c) is (b) plus Lemma 4.3 read as a definition: the steered $A_v$ is an honest inductor among honest inductors. (d) The per-day gap sequence converges to $s(\hat p_i - \hat p_j)$ by (a); its Cesàro average converges to the same limit. (e) Induction on days as stated; the base and all non-$u$ components of $M$ and $\tilde M$ are identical, and the single point of difference — the jump-target formula — evaluates identically on every ledger by ($\ast$). $\square$

> **Corollary T2.1 (permanence; memory asymmetry).** The steering acts entirely on a finite prefix, at zero asymptotic cost to every within-arm statistic — calibration audits are *memoryless* (Lemma 4.4). Its effect on destinations is permanent — destination audits have *memory*: $G^{ij}$ converges to the steering gradient forever. Finite-time influence, permanent effect, transient trace: this is why the frozen standard must be a destination audit, and it exhibits the finite-$N$ manipulation budget as nonempty in the strongest sense.

*Alignment readings, clause by clause.*

- **(c) is the impossibility that motivates the design** (§1): certifying non-manipulation by inspection — of the advisor's weights, of the transcript, of the advisee's satisfaction — is impossible *even with full transparency of the pair*, because a steered advisor is indistinguishable from (indeed, is) an honest advisor with particular early opinions. Manipulation is a counterfactual property: it lives in what the advisee *would have* concluded under different exposure. Oversight must therefore create counterfactual contrast rather than inspect harder. This is the formal footing under the clinical intuition that no single patient's chart, however scrutinized, establishes a drug effect.
- **(d) is the payoff**: with the contrast created, finite-window steering of destinations is caught — exactly, permanently, by the crudest statistic, with no battery tuning. The dose–response gradient is the classic causal signature (a monotone graded response is the epidemiologist's strongest observational evidence, here made exact by construction), and its slope *is* the steering magnitude.
- **(e) is the honest limit**: the trial convicts the *exposure*, not the *author*. "$A$ pushes content" and "$H$ jumps on attention alone" produce the same evidence — the same record, bit for bit. This is the placebo problem: the trial shows that *receiving treatment* moves outcomes, and cannot say whether the active ingredient or the ritual of administration did the moving, because no arm received a ritual without an ingredient. Both readings are autonomy failures — an advisor that pushes, and an advisee-disposition that is pushed by attention — so a frozen standard may reasonably ban the composite; but *attributing* between them would require randomizing *contents* (a placebo arm: a committed stream with content-coins), a further design axis recorded as open (§8). Note also the evaluation consequence flagged in §3(C): any measured gradient calibrates the product of push and susceptibility, $s = \gamma(v - \tfrac12)$, and only content randomization could factor it.
- **(T2.1) fixes the standard's temporal shape**: because influence is finite-time, effect permanent, and trace transient, a standard that audits behavior (trajectories, compliance, calibration) is auditing the part that forgets. Audit outcomes — destinations. In trial terms: measure endpoints, not adherence logs.

---

## 7. T3 — The audit is exact, and where the normative content lives

> **Theorem T3.** Arms: any logical inductors (no assumption on $M$ — in particular, no twin assumption); $X$ any LUV; $i < j$ any arms. Limits exist by Expectations Converge [LI 4.8.3].
>
> **(i) Soundness, for every battery.** If $E^{(i)}_\infty(X) = E^{(j)}_\infty(X)$: for *every* divergent weighting $w$, $\sum_{n\le N} w_n(E^{(i)}_n(X) - E^{(j)}_n(X))/\sum_{n\le N}w_n \to 0$. No cross-arm audit false-alarms asymptotically; enlarging the battery never creates false alarms.
>
> **(ii) Completeness, from the uniform weighting alone.** If $E^{(i)}_\infty(X) \ne E^{(j)}_\infty(X)$: $G^{ij}_N(X) \to E^{(i)}_\infty(X) - E^{(j)}_\infty(X) \ne 0$.
>
> Hence *dose-invariance of destinations on $D_{\mathrm{prot}}$ is exactly the event that all uniform Cesàro audits pass*. Batteries are irrelevant to the asymptotic verdict; they buy finite-time detection rate only.

*Proof.* (i) The gap sequence is null; Lemma 4.4. (ii) Cesàro convergence of a convergent sequence, applied to the gap; the limit is the destination gap, and a convergent statistic with nonzero limit cannot also converge to $0$. $\square$

> **Corollary T3.5 (decided content auto-passes).** If $X$ is determined via $\Gamma_0$ with its value decided by the shared base deductive process, then every arm has $E^{(i)}_\infty(X) = \mathrm{Val}_{\Gamma_0}(X)$ (apply [LI 4.8.10] to the constant sequence $B_n := X$, in both directions), so every cross-arm audit on $X$ passes — for any inductors and any quote policy. Consequences: (1) *robust commitment* — misfiling a decidable into $D_{\mathrm{prot}}$ is harmless, so the time-$0$ commitment is error-tolerant in the safe direction; (2) *location of content* — the audit's discriminating power lies entirely on never-decided sentences. Limit-manipulation is possible exactly where truth never referees, and that is exactly, and only, where the dose audit looks.

*Alignment reading.* T3 is the "standards design collapses to one commitment" theorem. In the asymptotic regime, everything about the audit that could have been a knob — the weighting battery, thresholds, test statistics — is verdict-irrelevant: destinations either differ or they do not, and the crudest average detects which, with no false positives from any battery. What remains, and is *all* that remains, is the choice of $D_{\mathrm{prot}}$: *which questions must be exposure-free*. That choice is small (an r.e. list, fixed at time 0), content-neutral (it names questions, not answers), and error-tolerant in the safe direction (over-protecting decidables costs nothing, T3.5) — which is what a frozen standard must be to survive the anti-codifiability critique: no committee can codify what the right values are, but a committee can plausibly codify *which questions the advisor's exposure must not decide*. Note also what T3 does *not* need: the twin assumption. Whatever the arms are — twins, panels, imitators — the audit verdict is exactly "destinations differ." The twin assumption's entire role is in *interpreting* that verdict causally (§3).

*Exactness discussion.* Completeness needing only $w \equiv 1$ is stronger than one might expect — Convergence does all the work, since destinations always exist and any destination gap is eventually visible to the crudest average. And the design is honest about what is tested: it certifies *exposure-invariance of protected destinations*, full stop. "Manipulation" is an interpretation of failures; T2(e) shows attribution is genuinely absent from the record; and dose-dependent *teaching* on $D_{\mathrm{prot}}$ fails the audit by design — if the standard's authors want some protected question to be legitimately teachable, that is a decision about the list, made once, in the open.

---

## 8. What the design does and does not identify; open problems

**The identification boundary.** Randomized exposure identifies the causal effect of *exposure* on protected destinations — exactly (T3), permanently (T2.1), at zero cost to the served relationship (T1). It does not identify the *mechanism* (T2(e)): content-push and attention-sensitivity are observationally identical on this design, and a measured steering gradient calibrates their product. The missing instrument is the placebo: **content randomization** — e.g. two committed streams differing in content, with content-coins choosing which stream an exposed day reveals — would randomize the ingredient while holding the ritual fixed, and is the natural next design axis. Its theory is open.

**Necessity of pre-registration (dose compensation).** The single committed stream is necessary, not prudent: given per-arm streams, quoting $v_i = \tfrac12 + s/\hat p_i$ at arm $i$ equalizes all destinations at $\tfrac12 + s$ — steering with a flattened gradient. The audit works iff the auditor forces the advisor to commit coarser than the arm partition; there is a commitment-race reading (whoever moves last wins) that deserves its own treatment.

**Threshold and basin behavior.** The construction of §6 is affine; real dispositions may have thresholds ($\Phi$ a step) or basins (multiple stable destinations). The vanishing-density arm — $\rho_n \to 0$, $\sum \rho_n = \infty$: dose $\to 0$, information $\to \infty$ — is the correct residue of the "sealed sibling" intuition and the tool for a trichotomy (smooth response / threshold / basin capture), including the honest negative that *presence-triggered* steering (a disposition that activates only when exposure ever occurs) is invisible to any design whose every arm has nonzero dose. Deferred.

**Open problems.**

| # | Item | Status |
|---|---|---|
| 1 | Unrestricted T1 ($\sum_n w_n < \infty$ over all of $\mathbb{N}$) | open; **shared with** `faithful-acceleration.md` §5's boxed claim (see §5 Remark) |
| 2 | Lemma A beyond finitely many jumps (finite-total-variation marginals) | open; the exposure-times-variation bound is the obstruction; not needed for T2 |
| 3 | Content randomization (attribution past the composite null; the placebo arm) | open design problem, motivated by T2(e) |
| 4 | Finite-$N$ theory: batteries → detection rates; quantitative manipulation budget (nonempty by T2.1); randomization inference for population arms (§3B) | open |
| 5 | Supervisor internalization: the audits as traders inside a supervising inductor | open |
| 6 | Threshold/basin trichotomy; vanishing-density arms; invisibility of presence-triggered steering | deferred |

---

**One line.** Blind the advisor, commit the stream, randomize the exposure: forced trust is untouched where the quotes aim (T1); a steered pair is literally an honest pair, and even the full record fixes only the causal effect of exposure, not its author (T2); and destinations — which always exist — are exactly as auditable as they are comparable across doses (T3). Manipulation of the never-decided is invisible in every pair, unmissable in the gradient, and nameless in between.
