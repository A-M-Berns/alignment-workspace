# The Positive Result, Reviewed Against the Logical Induction Paper

_Claude, 2026-07-10. Subject: the surviving positive argument of faithful-acceleration — what the LI paper's unbiasedness theorems actually say, the printed anomaly in the expectation pair and its resolution, and a full reformulation of the deference argument against the corrected theorem. Citations are dual: page numbers refer to the published PDF (arXiv:1609.03543**v5**, 7 Dec 2020, 132 pp., fetched and text-searched this session); line numbers (ℓ) refer to the project's `main.tex`. Quotes are verbatim from those sources (PDF extraction may mangle math spacing; I restore standard notation in displays). Everything not quoted or proved here is marked with a confidence. This document is meant to stand alone._

---

## 0. Summary

1. The LI paper has **two unbiasedness families**: _Recurring_ (any $\overline{\mathbb P}$-generable divergent weighting; conclusion only "0 is a limit point") and _From Feedback_ (weighting supported on the image of a deferral function, each fired element's value computable by the next firing; conclusion a full limit). "Patient" belongs to a third family (pseudorandomness-_learning_) and is not a feedback hypothesis. §1–§2.
2. At the expectation level the published paper **swaps a hypothesis between the two families**: Theorem 4.8.15 (Recurring) carries a support clause referencing an undefined $f$, plus a "weighting weighting" typo; Theorem 4.8.16 (Feedback) lacks the clause and references $A_n$ though its sequence is $B$. This is in print (p. 42; restated pp. 112–113). The paper's own appendix proofs certify the fix: E.11 proves 4.8.15 by applying clause-free 4.5.9; E.12 proves 4.8.16 by applying clause-bearing 4.5.10. Corrected statements in §3. **Reportable erratum.**
3. For faithful's setting ($B_n = \ulcorner E^H_{2^n}(X)\urcorner$), the corrected 4.8.16 licenses weightings supported on grids with $d_{k+1} \gtrsim R(2^{d_k})$ ($R$ = coupled-run cost): **tower-sparse**. §4.
4. The reformulation (§5) surfaces one structural hypothesis the corpus uses implicitly: both sides' traders must be able to read the _ledgered cross-facts_, which pure LI traders (features of their own prices only, Def. 3.4.4) cannot do when $R$ is super-polynomial — and signed unbiasedness cannot bridge price-proxies. The fix is to state the coupled model with a **ledger-augmented trader class** and note that the paper's unbiasedness proofs relativize to it (Lemma R, ~0.85). With that, the argument goes through and yields: **Theorem (Grid-wise Gated Trust).** For every fixed legal grid $G$ and rational $t,\varepsilon,\delta$: $\sum_{n \in G} w_n(X,t,\varepsilon,\delta) < \infty$ — with corollaries (grid-wise averaged trust; grid-wise per-day dominance $\liminf_{k}(E^H_{d_k}(X) - a_{d_k}) \ge 0$), and with the original boxed full-sum, and per-day $w_n \to 0$, _not_ delivered (§5.6). A gridless limit-point companion survives via Recurring (§5.7).
5. The theorem's hypotheses nowhere mention self-reference; no domain restriction appears. Where the quote-referencing diagonal lives is the _degenerate_ stratum: the theorems hold there with the quote pinned at $\tfrac12$ and empty of side-information (§6).

---

## 1. The framework facts the argument depends on

**Efficient computability** (Definition, ℓ753–754; published §3, p. 14): "An infinite sequence $\overline x$ is called **efficiently computable** … if there is a computable function $f$ that outputs $x_n$ on input $n$, with runtime polynomial in $n$." So an e.c. _generator_ has a poly($n$) budget at index $n$ — it can hard-code into its output only what it can compute that fast.

**Traders see prices.** Definition 3.4.4 (Trading Strategy), p. 18: "A trading strategy for day $n$ … is an affine combination … where $\phi_1,\dots,\phi_k$ are sentences, $\xi_1,\dots,\xi_k$ are **expressible features of rank $\le n$**…". Features are continuous functions of the _own market's_ valuation sequence (ℓ767). External facts reach a trader only through (a) its e.c. generator's poly-budget computations, or (b) the prices of sentences the deductive process feeds in.

**Weightings.** Definition 4.3.5 (Generable From $\overline{\mathbb P}$), p. 29: "A sequence of rational numbers $q$ is called generable from $\overline{\mathbb P}$ if there exists an e.c. EF-progression $q^\dagger$ such that $q^\dagger_n(\overline{\mathbb P}) = q_n$ … Divergent weightings generable from $\overline{\mathbb P}$ are fuzzy subsequences that are allowed to depend continuously (via expressible market features) on the market history. For example, the sequence $(\mathrm{Ind}_{0.01}(\mathbb P_n(\phi_n) > 0.5))_{n}$ is a $\overline{\mathbb P}$-generable sequence that singles out all times $n$ when $\mathbb P_n(\phi_n)$ is greater than 50%." A **divergent weighting** is a $[0,1]$-sequence with $\sum_n w_n = \infty$ (Def. 4.3.4, p. 28–29; ℓ1213).

**Deferral.** Definition 4.3.7, p. 29 (ℓ1240): $f(n) > n$, computable in time poly($f(n)$); "$f$ defers $n$ to $f(n)$".

**Expectations are affine combinations of sentence prices.** LUVs: Definition 4.8.1, p. 39. The day-$n$ expectation is the $\tfrac1n$-grid sum of threshold-sentence prices — used explicitly in the appendix: "$\mathbb W(\mathrm{Ex}_n(\mathbb 1(\phi_n))) = \sum_{i=0}^{n-1}\tfrac1n \mathbb W(\text{“}\mathbb 1(\phi_n) > i/n\text{”})$" (p. 112). Consequence used repeatedly below: **any expectation-unbiasedness instance is an affine-unbiasedness instance** for the combination $\mathrm{Ex}_n(B_n)$ — this is exactly how the paper's own proofs proceed (E.11, E.12).

---

## 2. The two theorem families, verbatim

### 2.1 Recurring (any weighting; limit points)

> **Theorem 4.3.6 (Recurring Unbiasedness)** — p. 29 (ℓ1225): "Given an e.c. sequence of decidable sentences $\phi$ and a $\overline{\mathbb P}$-generable divergent weighting $w$, the sequence $\frac{\sum_{i\le n} w_i,(\mathbb P_i(\phi_i) - \mathrm{Thm}_\Gamma(\phi_i))}{\sum_{i\le n} w_i}$ has 0 as a **limit point**. In particular, if it converges, it converges to 0." **Theorem 4.5.9 (Affine Recurring Unbiasedness)** — p. 35 (ℓ1469): "If $A \in \mathcal{BCS}(\overline{\mathbb P})$ is determined via $\Gamma$, and $w$ is a $\overline{\mathbb P}$-generable divergent weighting, [same ratio with $\mathbb P_i(A_i) - \mathrm{Val}_\Gamma(A_i)$] has 0 as a limit point…"

No deferral, no support clause, in either. The conclusion is deliberately weak: along _some_ subsequence of days the weighted bias vanishes.

### 2.2 From Feedback (sparse supports; full limits)

> **Theorem 4.3.8 (Unbiasedness From Feedback)** — pp. 29–30 (ℓ1249): "Let $\phi$ be any e.c. sequence of decidable sentences, and $w$ be any $\overline{\mathbb P}$-generable divergent weighting. If there exists a **strictly increasing deferral function $f$ such that the support of $w$ is contained in the image of $f$** and $\mathrm{Thm}_\Gamma(\phi_{f(n)})$ is computable in $O(f(n{+}1))$ time, then [the ratio] $\eqsim_n 0$. In this case, we say '$w$ allows good feedback on $\phi$'." **Theorem 4.5.10 (Affine Unbiasedness from Feedback)** — p. 35 (ℓ1480): "Given $A \in \mathcal{BCS}(\overline{\mathbb P})$ that is determined via $\Gamma$, a strictly increasing deferral function $f$ such that $\mathrm{Val}_\Gamma(A_n)$ can be computed in time $O(f(n{+}1))$, **and a $\overline{\mathbb P}$-generable divergent weighting $w$ such that the support of $w$ is contained in the image of $f$**, [the ratio] $\eqsim_n 0$…"

The interpretation sentence (p. 30, ℓ1262): unbiasedness holds "on any subsequence of the data where a polynomial-time machine can figure out how the previous elements of the subsequence turned out before $\overline{\mathbb P}$ is forced to predict the next one." The proof mechanism (D.4; ℓ4733–4795): the trader "buys $A_{f(i)}$ … and then sells $A_{f(i)}$ at a later time $f(i{+}1)$" — one open position at a time; the fired element's value must be in by the next firing.

### 2.3 Where "patient" actually lives

> **Definition 4.4.3 ($f$-Patient Divergent Weighting)** — p. 31 (ℓ1296): "…$w$ is $f$-patient if there is some constant $C$ such that, for all $n$, $\sum_{i=n}^{f(n)} w_i(\overline{\mathbb P}) \le C$."

This is a hypothesis of the pseudorandomness-_learning_ theorems ("Learning (Varied) Pseudorandom Frequencies", pp. 31–32; LUV version Theorem 4.8.17, p. 42), which say the _market's price_ matches a sequence that is pseudorandom **relative to** the patient class. It is not a hypothesis of either feedback theorem. Faithful's (II) — "for any $\mathcal C_A$-generable divergent weighting $w_n$ that is _patient_ (deferred until the feedback is in)" (faithful ℓ74) — therefore uses the paper's word for a different condition, and omits the condition 4.3.8/4.5.10 actually impose.

---

## 3. The printed anomaly, and the corrected 4.8.16

### 3.1 As published (arXiv v5, p. 42; restated verbatim in the appendix, pp. 112–113)

> **Theorem 4.8.15 (Expectation Recurring Unbiasedness).** "If $B \in \mathcal{BLCS}(\overline{\mathbb P})$ is determined via $\Gamma$, and $w$ is a $\overline{\mathbb P}$-generable divergent **weighting weighting such that the support of $w$ is contained in the image of $f$**, [the ratio with $\mathbb E_i(B_i) - \mathrm{Val}_\Gamma(B_i)$] has 0 as a limit point…" — _no $f$ is introduced anywhere in the statement._ **Theorem 4.8.16 (Expectation Unbiasedness From Feedback).** "Given $B \in \mathcal{BLCS}(\overline{\mathbb P})$ that is determined via $\Gamma$, a strictly increasing deferral function $f$ such that $\mathrm{Val}_\Gamma(\mathbf{A_n})$ can be computed in time $O(f(n{+}1))$, and a $\overline{\mathbb P}$-generable divergent weighting $w$, [the ratio] $\eqsim_n 0$. In this case, we say '$w$ allows good feedback on $B$'." — _no support clause; and the computability condition names $A_n$ though the theorem's sequence is $B$._

The pattern in the other four cells is uniform — recurring: no clause (4.3.6, 4.5.9); feedback: clause (4.3.8, 4.5.10) — so the expectation pair, as printed, has the clause attached to the wrong member.

### 3.2 The resolution, from the paper's own proofs

E.11 (p. 112): "_Proof._ Let $\mathbb W \in \mathcal{PC}(\Gamma)$. Apply **Theorem 4.5.9 (Affine Recurring Unbiasedness)** to $(\mathrm{Ex}_n(B_n))_n$ and $w$…" — an application with **no** support requirement, so 4.8.15's printed clause is doing nothing and its $f$ is indeed spurious. E.12 (pp. 112–113; ℓ5260) proves 4.8.16 by applying **4.5.10**, whose hypotheses include the clause — so the intended 4.8.16 inherits it. Corrected statements:

> **4.8.15 (corrected).** $B \in \mathcal{BLCS}$ determined via $\Gamma$; $w$ any $\overline{\mathbb P}$-generable divergent weighting. Then $\frac{\sum_{i\le n} w_i(\mathbb E_i(B_i) - \mathrm{Val}_\Gamma(B_i))}{\sum_{i \le n} w_i}$ has 0 as a limit point (converging to 0 if it converges). 
> 
> **4.8.16 (corrected).** $B \in \mathcal{BLCS}$ determined via $\Gamma$; $f$ a strictly increasing deferral function with $\mathrm{Val}_\Gamma(B_n)$ computable in time $O(f(n{+}1))$; $w$ a $\overline{\mathbb P}$-generable divergent weighting **with $\mathrm{supp}(w) \subseteq \mathrm{image}(f)$**. Then the ratio $\to 0$.

Two glosses on the corrected 4.8.16, both from D.4's mechanics: (a) the sum effectively runs over the image ("we need only consider the sum over $n$ in the support", ℓ4733ff), so the operative timing condition is that the _fired_ element's value is available by the _next_ firing; (b) a literal all-$n$ reading of "$\mathrm{Val}_\Gamma(\cdot_n)$ computable in $O(f(n{+}1))$" with a fast-growing $f$ would leave fired bets unresolved across many firings and break the one-position-at-a-time wealth argument — the fired-element reading is the one the proof supports (~0.9). Confidence that §3.2's corrected statements are the intended theorems: ~0.95 (proof-based, plus the four-cell pattern). **This is an erratum in the published paper and worth reporting upstream.**

---

## 4. The corrected instance in faithful's setting

Fix $X$ (an e.c. $[0,1]$-LUV of $H$'s language); $Y_n := E^H_{2^n}(X)$; $B_n := \ulcorner Y_n\urcorner$, a $\Gamma_A$-determined $[0,1]$-LUV (the coupled run is computable and $\Gamma_A \supseteq \mathrm{PA}$ proves its output — faithful's own verified bullet); $a_n := E^A_n(B_n)$. Let $R(s)$ be a computable monotone bound on the time to run the coupled construction through stage $s$.

**Cost accounting.** $\mathrm{Val}_{\Gamma_A}(B_n) = Y_n$ is obtained only by producing $H$'s day-$2^n$ price: time $\sim R(2^n)$; reading either ledger to stage $s$ also costs $\sim R(s)$, so there is no cheaper route (~0.85). Hence a grid $G = {d_k} = \mathrm{image}(f)$ is **legal** for the corrected 4.8.16 iff $R(2^{d_k}) = O(d_{k+1})$ — tower-spaced — and $f$ itself is computable in poly of its value (satisfiable by defining $d_{k+1}$ as an $R$-computation; deferral condition 2, p. 29). For comparison, the paper's own diagonal $\chi^p_n$ (§6) has values at cost $R(n)$, giving $R$-geometric grids: sparse, but incomparably denser.

**What Recurring gives with no grid.** 4.8.15-corrected (equivalently 4.5.9 on the grid-sum combinations): for _every_ generable divergent weighting — including everywhere-supported soft gates on the live quote — the weighted bias of $a_i$ against $Y_i$ has 0 as a limit point. This is the unconditional backbone; it cannot support full-limit conclusions.

---

## 5. Faithful's argument, reformulated in full

### 5.1 The setting, made explicit

**(S1) The coupled pair and the criterion.** $H$ and $A$ are markets over deductive processes $D_H, D_A$, interleaved (within round $n$: $H$'s day-$n$ prices post; $A$'s day-$n$ market clears; ledgers exchange — a fixed delay $c$ merely shifts indices below, so I set $c = 0$ for exposition). Each side satisfies the logical induction criterion (ℓ658: "no efficiently computable trader … exploits") **relative to the ledger-augmented trader class** $\mathcal C^+$: trading strategies whose coefficients are continuous features of the own valuation sequence _and_ of the incoming ledger stream (the other side's ledgered quotes/prices, as decided data), with e.c. generators. This augmentation is the corpus's model — faithful ℓ142: "The weight $w_n$ is recognizable to **both** inductors — $H$ reads $A$'s quote $a_n$, $A$ reads $H$'s price $E^H_n(X)$, both are decided by day $n$"; §8 obligation 1 — and §5.8 explains why it is genuinely load-bearing rather than cosmetic.

**(S2) Lemma R (relativization; ~0.85).** Theorems 4.3.6/4.3.8/4.5.9/4.5.10, and hence the corrected 4.8.15/4.8.16, hold with "$\overline{\mathbb P}$-generable" replaced by "$\mathcal C^+$-generable" for a market unexploitable by $\mathcal C^+$-traders. _Reason:_ the exploiting traders in D.2/D.4 are constructed _from_ the given weighting (multiplied into standard buy/sell bookkeeping); nothing in those constructions uses minimality of the feature language, so enlarging the class enlarges the theorem's scope and the criterion's strength in step. Checkpoint: read D.2 and D.4 (pp. 99–104) for any use of the class beyond "the weighting is a feature the trader can evaluate".

**(S3) The target family and legal grids** as in §4; write $\mathrm{legal}(G)$ for $d_{k+1} \ge R(2^{d_k})$ with $G$ e.c.-presentable; note the round-trip windows $[d_k, 2^{d_k}]$ are then pairwise disjoint.

### 5.2 The theorem

> **Theorem (Grid-wise Gated Trust).** Assume (S1)–(S3). For every rational $t \in [0,1]$, $\varepsilon, \delta > 0$, and every legal grid $G = {d_k}$: $$\sum_{k} w_{d_k} < \infty, \qquad w_n := \mathrm{Ind}_\delta(a_n > t)\cdot \mathrm{Ind}_\delta\big(E^H_n(X) < t - \varepsilon\big).$$

### 5.3 Proof

Suppose $W_K := \sum_{k \le K} w_{d_k} \to \infty$.

**Step A ($A$-side unbiasedness along $G$).** The weighting $u := w \cdot \mathbb 1_G$ is $\mathcal C^+_A$-generable (jointly continuous in the pair $(a_n, E^H_n(X))$, both trader-visible under (S1) — this is exactly the continuity property faithful's `dsWeight_continuous` isolates), divergent (by assumption), supported in $\mathrm{image}(f) = G$, with $\mathrm{Val}(B_{d_k}) = Y_{d_k}$ computable in $R(2^{d_k}) = O(d_{k+1})$. By 4.8.16-corrected relativized (S2): $$\frac{\sum_{k\le K} w_{d_k},(a_{d_k} - Y_{d_k})}{W_K} \longrightarrow 0.$$ On the support $a_{d_k} > t$ (the ramp is 0 otherwise), so $\sum_{k \le K} w_{d_k},Y_{d_k} \ \ge\ t,W_K - o(W_K)$: _the realized future credences average at least $t$ on the gated grid._

**Step B ($H$-side round trip).** On the support $E^H_{d_k}(X) < t - \varepsilon$ likewise. Hence $$\sum_{k \le K} w_{d_k},\big(Y_{d_k} - E^H_{d_k}(X)\big) \ \ge\ (t - o(1))W_K - (t-\varepsilon)W_K \ =\ (\varepsilon - o(1)),W_K.$$

**Step C (exploitation of $H$).** Define the $\mathcal C^+_H$-trader $T$: at day $d_k$, stake $\lambda, w_{d_k}$ of its running budget $b_k$ on $X$ (buy at price $E^H_{d_k}(X)$), unwind at day $2^{d_k}$ at price $E^H_{2^{d_k}}(X) = Y_{d_k}$ — the sale is at $H$'s own then-current price, so the round trip is $H$-internal. $T$ is e.c. ($d_k$ computable within the deferral budget; sizes from visible quantities); windows are disjoint, so at most one position is open; with $\lambda \le \tfrac12$, worth stays bounded below (mid-window dip at most the stake; $X \in [0,1]$). Log-budget accounting with $\Delta_k := Y_{d_k} - E^H_{d_k}(X) \in [-1,1]$: $$\log b_{K} \ \ge\ \lambda \sum_{k\le K} w_{d_k}\Delta_k \ -\ \lambda^2 \sum_{k \le K} w_{d_k} \ \ge\ \big(\lambda(\varepsilon - o(1)) - \lambda^2\big),W_K \ \longrightarrow\ \infty \quad (\lambda < \varepsilon/2),$$ in every plausible world (the payoffs are realized market prices). This exploits $H$, contradicting (S1). Hence $W_\infty < \infty$. $\blacksquare$

This is faithful's Steps 1–4 with three corrections: the weighting quantifier (grid support, per the clause), the disjoint-window discipline (which the grid supplies), and the explicit class in which "recognizable to both" is legal. The kernel-checked Lean core (`hbias` + `hbdd` $\Rightarrow \sum w < \infty$) is exactly Steps A–C's arithmetic; what changes is _which_ `hbias` the LI theorems supply.

### 5.4 Corollary 1 (grid-wise averaged trust)

If additionally $\sum_k \mathrm{Ind}_\delta(a_{d_k} > t) = \infty$, then $\liminf_K \frac{\sum_{k\le K} \mathrm{Ind}_\delta(a_{d_k}>t),E^H_{d_k}(X)}{\sum_{k\le K} \mathrm{Ind}_\delta(a_{d_k}>t)} \ \ge\ t - \varepsilon - \delta$. (The file's Corollary proof, verbatim, restricted to $G$: deep days have saturated inner ramp and finite gate-mass by the Theorem; the rest sit above $t - \varepsilon - \delta$.)

### 5.5 Corollary 2 (grid-wise per-day dominance)

For every legal grid $G$: $\ \liminf_{k}\big(E^H_{d_k}(X) - a_{d_k}\big) \ \ge\ 0.$ _Proof._ If not, some $c > 0$ has $E^H_{d_k} \le a_{d_k} - c$ along an infinite $I \subseteq G$; $a_{d_k} \ge c$ there; pass to $a_{d_k} \to a^_$, take rational $t \in (a^_ - \tfrac c2, a^* - \tfrac c4)$ and rational $\varepsilon \le \tfrac c8$: on a tail of $I$ both ramps of $w_{d_k}(t,\varepsilon,\delta)$ are bounded below, so the Theorem's sum diverges — contradiction. $\blacksquare$ So on every prescheduled sparse audit grid, $H$'s live credence is eventually never undercut by $A$'s flag, at any margin. (This is the earlier ladder analysis relativized: the boxed statements' internal ordering was one question; _which_ statement the theorems force is this one.)

### 5.6 What is _not_ delivered, and why

The original boxed claim $\sum_{n} w_n < \infty$ (all days) does not follow: a violation profile $w_n \sim 1/\log n$ has every tower-sparse subsum finite while the total diverges. Nor does per-day $w_n \to 0$: the deferral image is a _fixed_ function chosen in advance (Def. 4.3.7), so grids cannot _chase_ violations — only the weights at pre-fixed days respond to prices — and violations may avoid every fixed e.c. grid. Recurring (4.8.15-corrected) cannot densify the conclusion either: it yields 0 as a limit point of the $A$-side ratio along _some_ day-subsequence, while Step C needs the $A$-side and $H$-side averages controlled along the _same_ subsequence; two limit-point statements need not share one. Honest reading of the positive result: **gated-trust violations are not preschedulable** — no efficiently pre-committed sparse audit catches them with divergent weight — which is real, and strictly weaker than the box. (~0.85; the standing residual is a densification theorem I have not found in the paper.)

### 5.7 The gridless companion (unconditional)

From 4.8.15-corrected, for _every_ $\mathcal C^+_A$-generable divergent weighting $u$ (no sparsity — e.g. the everywhere soft gate $\mathrm{Ind}_\delta(a_n > t)$, or that gate times any continuous function of both live prices): the ratio $\sum u,(a - Y)/\sum u$ has 0 as a limit point. Consequences of this weaker currency: along _some_ infinite day-subsequence the gated average forecast error vanishes — enough to refute any _one-signed, bounded-away_ bias on a divergent gate (this is what powers the diagonal analysis, §6), not enough to run the §5.3 squeeze.

### 5.8 Why the ledger-augmented class (S1) is load-bearing

Under the paper's literal Definition 3.4.4, $A$'s weightings are features of $A$'s prices only, and their e.c. generators have poly($n$) budgets — while reading either ledger at stage $n$ costs $R(n)$. If $R$ is super-polynomial (the LI construction's day cost plausibly is), then a _pure_ LI weighting for $A$ can depend on $E^H_n(X)$ neither continuously (not $A$'s price) nor by hard-coding (budget) — it can only use $A$'s _price of the ledgered LUV_ $\ulcorner E^H_n(X)\urcorner$ as a proxy. One can try to run §5.3 with proxies on both sides, but the bridging terms require _absolute_ average fidelity $\sum_G |{\rm proxy} - {\rm value}| = o(W)$, and the unbiasedness theorems supply only _signed_ averages, which mixed-sign mispricings can satisfy while absolute fidelity fails; I found no in-framework theorem that closes this (persistence-type results need e.c. target values, which decided-truth sequences are not). So the corpus's modeling choice — cross-facts as trader inputs — is not a convenience but a hypothesis, discharged by Lemma R's relativization rather than by any quoted theorem. It should be stated as such (faithful ℓ254 already flags its Lean-side shadow: "that continuity upgrades to full $\mathcal C_H$-expressible-feature legality … stays in the modeling layer"). (~0.8 that the pure-EF obstruction is essential rather than an artifact of my proof attempts.)

### 5.9 Hypothesis audit

|hypothesis|supplied by|status|
|---|---|---|
|coupled pair exists; each side an inductor for $\mathcal C^+$|one-stage-delay construction + strengthened criterion|asserted in corpus (obligation 3); construction standard (~0.9); $\mathcal C^+$-criterion needs Lemma R or a re-run of the paper's §5 construction with the larger class (~0.85)|
|$B \in \mathcal{BLCS}$, determined via $\Gamma_A$|faithful ℓ74ff|verified (grid-sum form; PA proves run outputs)|
|legal grid: $d_{k+1} \ge R(2^{d_k})$, e.c.|choice|constructible for computable $R$|
|corrected 4.8.16|§3|erratum-fixed; proof-certified|
|$H$-criterion vs the §5.3 trader|(S1)|trader is e.c., bounded-risk, disjoint windows|
|any restriction on $X$|—|**none appears**|

---

## 6. Where the diagonal sits (no domain hypothesis needed)

The Theorem in §5.2 quantifies over a _fixed_ $X$ with hypotheses that never mention self-reference. Applied to a fixed member $g_m$ of the diagonal family ($g_m \leftrightarrow$ "$a_m \le \tfrac12$", ledger-decided by $\sim m{+}2$): $Y_n(g_m)$ is the settled side for all $n \ge m$, $A$'s forecasts converge to it, and violations are confined to finitely many early days — the fixed-$X$ statement is true and nearly empty there. The _family-indexed_ question ($A$'s day-$n$ forecast of the day-$n$ contract, the object the scope dispute was about) is governed by §5.7's currency, and Recurring forces the `thm:lp` regime rather than a breakdown. Compactly:

**Fact (quote pinning).** With $Y_n = s_n \pm \eta_n$, $\eta_n < \tfrac14$ eventually: $a_n \to \tfrac12$. _Proof._ For rational $m \in (0,\tfrac14)$, the gate $\mathrm{Ind}_\delta(a_n > \tfrac12 + \tfrac m2)$ is generable; cofinitely on its support $a_n$ exceeds the grid threshold, so $s_n = 0$ and the bias $a_n - Y_n > \tfrac14$: one-signed and bounded away, so by 4.8.15-corrected the gate cannot be divergent, and days with $a_n \ge \tfrac12 + m$ (each carrying ramp weight $\ge \min(\tfrac m{2\delta},1)$) are finitely many. Low side symmetric. $\blacksquare$

The published context for this regime is **Theorem 4.11.2 (Paradox Resistance)**, p. 46 (ℓ1993): "Fix a rational $p \in (0,1)$, and define an e.c. sequence of 'paradoxical sentences' $\chi^p$ satisfying $\Gamma \vdash \chi^p_n \leftrightarrow (\mathbb P_n(\chi^p_n) < p)$ for all $n$. Then $\lim_{n\to\infty} \mathbb P_n(\chi^p_n) = p$." — with the discussion (pp. 46–47; ℓ2006, 2010): the price is pushed "so close to 80% that you're not quite sure which way the brain scanner will actually call it", the truth-frequency has a limit point at $p$ by Recurring Unbiasedness, and there is no efficiently expressible method for identifying a bias in the price. The diagonal is the cross-process realization of this: the theorems hold, the quote is pinned and side-empty, and the positive result's _content_ — not its truth — is what vanishes there. Any restriction worth stating is therefore interpretive (where the quote is informative), not a hypothesis of the theorem.

---

## 7. Side-by-side: faithful's statement vs. the corrected one

|faithful (as written)|corrected|
|---|---|
|(II): "any $\mathcal C_A$-generable divergent weighting … _patient_ (deferred until the feedback is in)"|4.8.16-corrected: generable divergent $w$ with $\mathrm{supp}(w) \subseteq \mathrm{image}(f)$, fired values computable by the next firing; "patient" reserved for Def. 4.4.3|
|implicit trader model: "recognizable to both inductors"|explicit (S1): ledger-augmented class $\mathcal C^+$ + Lemma R|
|boxed: $\sum_{n} w_n < \infty$ over all days|$\sum_{n \in G} w_n < \infty$ for every legal grid $G$ ($d_{k+1} \ge R(2^{d_k})$, disjoint windows)|
|"(II) holds over all sentences"|no domain hypothesis anywhere; on the diagonal the theorems hold degenerately (quote pinned, side-empty)|
|strength narrative ("strongest forceable rung"; "averaged in, averaged out")|forced content: grid-wise sums, grid-wise per-day dominance (Cor. 2), gridless limit points; violations not preschedulable|

## 8. Checkpoints

In rough order of value per minute: (1) p. 42 and pp. 112–113 of the PDF against §3.1 (the erratum is a two-minute read). (2) D.2/D.4 (pp. 99–104) for Lemma R's relativization claim — the one hypothesis §5 adds to the corpus's own model. (3) The §5.3 proof (self-contained above). (4) The §5.8 obstruction — this is my newest and least-aged claim. (5) The cost model behind legality ($R(2^n)$, no shortcut). Prior working documents (plan, ladder check, step 2–4 files) contain the longer audit trail; nothing above depends on them beyond what is quoted or proved here.