# The Positive Result, Reviewed Against the Logical Induction Paper

_Claude, 2026-07-10; restructured same day after Abram's review (argument-first organization; the three theorem families presented as three, with both cross-cutting groupings; role reminders in each section; the erratum table made explicit; quote-block discipline). Citations are dual: page numbers refer to the published PDF (arXiv:1609.03543v5, 7 Dec 2020, 132 pp.); ℓ-numbers refer to the project's `main.tex`. **Quote convention:** blockquotes contain only verbatim source text, with macro names normalized to standard notation and elisions marked "…"; everything in my voice — attributions, glosses, corrected statements — sits outside the blocks._

---

## 0. Summary

**The argument, in one paragraph.** Fix a sentence-like target $X$, a threshold $t$, a margin $\varepsilon$. Call day $n$ a _violation day_ if $A$ flags high while $H$'s live credence is low: $E^A_n(\ulcorner E^H_{2^n}(X) \urcorner) > t$ but $E^H_n(X) < t - \varepsilon$. Abbreviate $a_n := E^A_n(\ulcorner E^H_{2^n}(X) \urcorner)$, $A$'s forecast of $H$'s lookahead credence $Y_n := E^H_{2^n}(X)$. Two logical-induction inputs squeeze the violation days. _Input U (unbiasedness):_ by the theorem faithful's ingredient (II) cites — LI **Theorem 4.8.16**, Expectation Unbiasedness From Feedback — $A$'s forecasts cannot stay biased against a legal weighting concentrated on violation days; since the gate has $a_n > t$, the _realized_ future credences $Y_n$ must average at least $t$ there. _Input C (criterion):_ an $H$-trader that buys $X$ on violation days at $H$'s low price ($< t-\varepsilon$) and unwinds at day $2^n$ at $H$'s own then-price ($= Y_n$) therefore banks $\ge \varepsilon$ per unit weight on average; if violation days carried divergent weight, its profit would diverge, exploiting $H$. Hence the violation weight is bounded: gated Total Trust. Everything then turns on _which weightings Input U actually grants_ — and the published statement of 4.8.16 misstates its own hypotheses (a transposition with its neighbor 4.8.15; §3), whose correction restricts Input U to sparse "feedback grids" and thereby re-quantifies the conclusion.

**Findings.** **(F1)** The printed 4.8.15/4.8.16 pair has a hypothesis transposed between them — an erratum in the published paper, fix certified by its own appendix proofs (§3). **(F2)** With the corrected 4.8.16, the argument goes through and yields a **grid-wise** theorem: $\sum_{n \in G} w_n < \infty$ for every fixed legal grid $G$ (spacing $d_{k+1} \gtrsim R(2^{d_k})$), with corollaries: grid-wise averaged trust and grid-wise per-day dominance $\liminf_k (E^H_{d_k}(X) - a_{d_k}) \ge 0$ (§5). **(F3)** The original boxed full-sum ($\sum$ over all days), and per-day $w_n \to 0$, are _not_ delivered; a gridless companion survives via the Recurring family, with only limit-point strength (§5.6–5.7). **(F4)** One hypothesis the corpus uses implicitly becomes explicit: both sides' traders must read the _ledgered cross-facts_, which the paper's literal trader class cannot do when the run cost $R$ is super-polynomial; stated as a ledger-augmented criterion plus a relativization lemma (§5.1). **(F5)** Faithful's word "patient" belongs to a third, different family of theorems (pseudorandomness-_learning_), not to the feedback family (§2.4). **(F6)** No domain restriction appears anywhere in the hypotheses; the quote-referencing diagonal is the stratum where the theorems hold _degenerately_ (§6).

---

## 1. The skeleton, and the complete list of what the argument depends on

Written as three steps, with the needed inputs named where they are used:

- **Step A** (uses **Input U**). Sum $A$'s forecast bias against the violation weighting $w$: if the weighting is one Input U grants, $\sum w (a_n - Y_n) = o(\sum w)$; on the gate $a_n > t$, so $\sum w, Y_n \ge t \sum w - o(\sum w)$.
- **Step B** (arithmetic). On violation days $E^H_n(X) < t - \varepsilon$, so the round-trip gain $\sum w (Y_n - E^H_n(X)) \ge (\varepsilon - o(1)) \sum w$.
- **Step C** (uses **Input C**, and **Input V** throughout). The buy-at-$n$, unwind-at-$2^n$ trader realizes Step B's gain against $H$; if $\sum w = \infty$, $H$ is exploited — contradiction. Input V is the standing requirement that $w$ be _legible_ to both sides: $A$'s theorem-instance needs $w$ in $A$'s weighting class; $H$'s trader needs to compute its stakes.

**Dependency manifest.** Definitions the theorem statements quantify over (§2.1): efficient computability (ℓ753; p. 14); features, rank, $\mathcal{EF}$-progressions (Defs 3.4.1–3.4.3, p. 17); trading strategies (Def 3.4.4, p. 18); divergent weightings and generability (Defs 4.3.4–4.3.5, pp. 28–29); deferral functions (Def 4.3.7, p. 29); LUVs, $\mathcal{BLCS}$, determined-via-$\Gamma$, and expectations as grid sums (Def 4.8.1 p. 39; p. 112). Theorems: **Input U is Theorem 4.8.16 corrected** (§3; the reason it is the protagonist: faithful ℓ74 cites exactly it for ingredient (II)); the **Recurring** theorems 4.3.6/4.5.9/4.8.15-corrected supply the gridless companion (§5.7) and the diagonal analysis (§6); the **criterion** (ℓ658) is Input C. Construction-level hypotheses (§5.1): the coupled pair exists; the ledgers; the augmented trader class with Lemma R. The **patient family** (Thms 4.4.2/4.4.5/4.8.17) is quoted for two reasons only: it is where faithful's word "patient" actually lives (diagnosis of the mis-citation), and it is the machinery the paper itself uses for hard-to-predict sequences, which frames §6.

---

## 2. The theorems drawn on, presented as three families

The paper proves three kinds of results about the weighted bias/frequency of an inductor's prices. Two are _unbiasedness_ theorems about the same ratio, differing in what they assume about the weighting and how strong a conclusion they buy; the third is not an unbiasedness theorem at all but a _price-learning_ theorem whose hypothesis is about the sentence sequence. Summarized, with the two cross-cutting groupings Abram asked to see separated:

|family|members (prop./affine/expect.)|hypothesis on the weighting $w$|deferral function's role|conclusion|role in this document|
|---|---|---|---|---|---|
|Recurring|4.3.6 / 4.5.9 / 4.8.15|any $\overline{\mathbb P}$-generable divergent|none — no $f$ appears|bias ratio has **0 as a limit point**|gridless fallback (§5.7); powers the diagonal (§6)|
|From Feedback|4.3.8 / 4.5.10 / 4.8.16|generable divergent **with $\mathrm{supp}(w) \subseteq \mathrm{image}(f)$**, fired values computable by the next firing|support + timing ("good feedback")|bias ratio $\to 0$ (**full limit**)|**Input U**; 4.8.16 is what (II) cites|
|Patient / learning|Thm 4.4.2; Def 4.4.3–4.4.4 + Thm 4.4.5; LUV version Thm 4.8.17|quantifies over all $f$-**patient** generable divergent $w$ — bounded mass per window $[n, f(n)]$|window-mass bound (bounded outstanding commitment)|the **price matches** the pseudorandom frequency: $\mathbb P_n(\phi_n) \eqsim_n p_n$|source of the word "patient" (F5); context for §6|

So the deferral function appears in _two_ of the three families, in different roles — one-at-a-time feedback (support in the image, previous fired value in before the next firing) versus boundedly-much-outstanding (mass per window) — and the "two vs three" of the earlier draft resolves as: two unbiasedness families plus one learning family. Both deferral roles descend from the "independent subsequence" idea of Garrabrant–Soares–Taylor 2016 (arXiv:1604.05280), where dense evaluation under unbounded delays is provably uninformative.

### 2.1 The definitions the theorem statements quantify over

Attribution and quotes; my glosses follow each block.

Efficient computability (ℓ753–754; §3, p. 14):

> An infinite sequence $\overline x$ is called **efficiently computable**, abbreviated e.c., if there is a computable function $f$ that outputs $x_n$ on input $n$, with runtime polynomial in $n$.

So an e.c. _generator_ has a poly($n$) budget at index $n$ — the fact that drives §5.1's visibility discussion.

Valuation features and rank (Def 3.4.1, p. 17; ℓ767–770):

> A valuation feature $\alpha : [0,1]^{\mathcal S \times \mathbb N^+} \to \mathbb R$ is a continuous function from valuation sequences to real numbers such that $\alpha(\overline{\mathbb V})$ depends only on the initial sequence $\mathbb V_{\le n}$ for some $n \in \mathbb N^+$ called the rank of the feature.

Expressible features and $\mathcal{EF}$-progressions (Def 3.4.3, p. 17; ℓ786–793): the algebraic closure of price features under rational constants, $+$, $\times$, $\max$, safe reciprocation; an $\mathcal{EF}$-progression has $n$-th member of rank $\le n$. Trading strategies (Def 3.4.4, p. 18) have expressible features of rank $\le n$ as coefficients — traders see their _own market's prices_ and nothing else directly.

Divergent weightings (Def 4.3.4, pp. 28–29; ℓ1213):

> A **divergent weighting** $\overline w \in [0,1]^{\mathbb N^+}$ is an infinite sequence of real numbers in $[0,1]$, such that $\sum_n w_n = \infty$.

Generability (Def 4.3.5, p. 29; ℓ1219–1223):

> A sequence of rational numbers $\overline q$ is called **generable from $\overline{\mathbb P}$** if there exists an e.c. $\mathcal{EF}$-progression $\overline{q'}$ such that $q'_n(\overline{\mathbb P}) = q_n$ for all $n$. … Divergent weightings generable from $\overline{\mathbb P}$ are fuzzy subsequences that are allowed to depend continuously (via expressible market features) on the market history. For example, the sequence $(\mathrm{Ind}_{0.01}(\mathbb P_n(\phi_n) > 0.5))_n$ is a $\overline{\mathbb P}$-generable sequence that singles out all times $n$ when $\mathbb P_n(\phi_n)$ is greater than 50%.

The example is the exact shape of the gates used everywhere below. Deferral functions (Def 4.3.7, p. 29; ℓ1240–1247):

> A function $f : \mathbb N^+ \to \mathbb N^+$ is called a **deferral function** if (1) $f(n) > n$ for all $n$, and (2) $f(n)$ can be computed in time polynomial in $f(n)$ …

Expectations: LUVs are Def 4.8.1 (p. 39); the day-$n$ expectation is the $\tfrac1n$-grid sum of threshold-sentence prices, used explicitly in the appendix (p. 112), e.g. in the displayed identity there:

> $\mathbb W(\mathrm{Ex}_n(\mathbb 1(\phi_n))) = \sum_{i=0}^{n-1} \tfrac1n, \mathbb W(\text{"}\mathbb 1(\phi_n) > i/n\text{"})$

Consequence used repeatedly: an expectation-unbiasedness instance _is_ an affine-unbiasedness instance for the combination $\mathrm{Ex}_n(B_n)$ — which is exactly how the paper's own appendix proofs proceed, and what lets §3's correction be certified.

### 2.2 The Recurring family (role: what holds with _no_ sparsity — the fallback and the diagonal's governor)

Theorem 4.3.6 (Recurring Unbiasedness), p. 29 (ℓ1225–1232):

> Given an e.c. sequence of decidable sentences $\overline\phi$ and a $\overline{\mathbb P}$-generable divergent weighting $\overline w$, the sequence $\dfrac{\sum_{i\le n} w_i (\mathbb P_i(\phi_i) - \mathrm{Thm}_\Gamma(\phi_i))}{\sum_{i \le n} w_i}$ has $0$ as a limit point. In particular, if it converges, it converges to $0$.

Theorem 4.5.9 (Affine Recurring Unbiasedness), p. 35 (ℓ1469): the same statement for determined-via-$\Gamma$ combination sequences, with $\mathbb P_i(A_i) - \mathrm{Val}_\Gamma(A_i)$. No deferral function, no condition on the support — _any_ generable divergent weighting — and correspondingly the weak conclusion: along _some_ subsequence of days the weighted bias vanishes. This is the family the argument falls back on wherever the feedback hypotheses fail (§5.7), and the only unbiasedness available on dense weightings on the diagonal (§6).

### 2.3 The Feedback family (role: **Input U** — the family ingredient (II) cites)

Faithful's ingredient (II) (ℓ74) attributes its unbiasedness input to "LI Thm 4.8.16". That theorem is the expectation-level member of this family; its propositional and affine siblings, which are printed correctly, fix what the family's hypotheses are.

Theorem 4.3.8 (Unbiasedness From Feedback), pp. 29–30 (ℓ1249–1258):

> Let $\overline\phi$ be any e.c. sequence of decidable sentences, and $\overline w$ be any $\overline{\mathbb P}$-generable divergent weighting. If there exists a strictly increasing deferral function $f$ such that the support of $\overline w$ is contained in the image of $f$ and $\mathrm{Thm}_\Gamma(\phi_{f(n)})$ is computable in $O(f(n{+}1))$ time, then $\dfrac{\sum_{i\le n} w_i(\mathbb P_i(\phi_i) - \mathrm{Thm}_\Gamma(\phi_i))}{\sum_{i\le n} w_i} \eqsim_n 0.$ In this case, we say "$\overline w$ allows good feedback on $\overline\phi$".

The paper's own interpretation, p. 30 (ℓ1262):

> In other words, $\overline{\mathbb P}$ is unbiased on any subsequence of the data where a polynomial-time machine can figure out how the previous elements of the subsequence turned out before $\overline{\mathbb P}$ is forced to predict the next one.

Theorem 4.5.10 (Affine Unbiasedness from Feedback), p. 35 (ℓ1480–1490): the affine version, with the same two hypotheses — the timing condition ($\mathrm{Val}_\Gamma(A_n)$ computable in time $O(f(n{+}1))$) and, verbatim, "a $\overline{\mathbb P}$-generable divergent weighting $\overline w$ such that the support of $\overline w$ is contained in the image of $f$". The proof mechanics (D.4, pp. 103–104; ℓ4733–4795) show what the hypotheses are for: the exploiting trader buys the element fired at $f(i)$ and sells it at $f(i{+}1)$ — one open position at a time, with the fired element's value in hand by the next firing.

Terminology for §3: call the hypothesis "the support of $\overline w$ is contained in the image of $f$" **the support clause**. A statement "has no clause" if it contains neither the support clause nor any deferral function at all.

### 2.4 The Patient / learning family (role: where "patient" actually lives; not an unbiasedness theorem)

Definition 4.4.3 ($f$-Patient Divergent Weighting), p. 31 (ℓ1296–1301):

> Let $f$ be a deferral function. We say that a divergent weighting $\overline w$ is **$f$-patient** if there is some constant $C$ such that, for all $n$, $\sum_{i=n}^{f(n)} w_i(\overline{\mathbb P}) \le C$. In other words, $\overline w$ is $f$-patient if the weight it places between days $n$ and $f(n)$ is bounded.

Definition 4.4.4 (Varied Pseudorandom Sequence), p. 31 (ℓ1305–1315): $\overline\phi$ is $\overline p$-varied pseudorandom relative to a set $S$ of $f$-patient weightings if for all $w \in S$ the $\overline p$-relative frequency ratio $\eqsim_n 0$. Then:

Theorem 4.4.5 (Learning Varied Pseudorandom Frequencies), pp. 31–32 (ℓ1317–1324):

> Given an e.c. sequence $\overline\phi$ of $\Gamma$-decidable sentences and a $\overline{\mathbb P}$-generable sequence $\overline p$ of rational probabilities, if there exists some $f$ such that $\overline\phi$ is $\overline p$-varied pseudorandom (relative to all $f$-patient $\overline{\mathbb P}$-generable divergent weightings), then $\mathbb P_n(\phi_n) \eqsim_n p_n$.

(Theorem 4.4.2 is the un-varied special case; Theorem 4.8.17, p. 42, is the LUV version.) Two things to notice. The hypothesis here is about the _sentence sequence_ (its frequencies converge against every patient weighting), not about a single weighting; and the conclusion is about the _price matching_ $p_n$, not about bias vanishing on a given weighting. So this family is a different kind of theorem from §2.2–§2.3 — which is why faithful's phrase "any $\mathcal C_A$-generable divergent weighting $w_n$ that is _patient_ (deferred until the feedback is in)" (ℓ74) is a mis-citation twice over: "patient" is this family's word, and the feedback family's actual hypothesis (the support clause) is different and is what the corrected 4.8.16 needs.

---

## 3. The expectation level: the printed erratum, and the corrected Input U

### 3.1 Why the expectation level, and the six cells

The argument's targets are LUVs ($Y_n$ is a $[0,1]$-valued quantity, not a sentence), so Input U must be the expectation-level member of the feedback family: Theorem 4.8.16 — exactly the theorem faithful cites. The two families at three levels give six statements; here is each cell's hypothesis on the weighting, as printed in arXiv v5:

|level|Recurring|From Feedback|
|---|---|---|
|propositional (p. 29–30)|**4.3.6**: no clause — no $f$ anywhere, any generable divergent $w$|**4.3.8**: support clause + timing condition|
|affine (p. 35)|**4.5.9**: no clause|**4.5.10**: support clause + timing condition|
|expectation (p. 42)|**4.8.15**: _carries the support clause_ — "such that the support of $w$ is contained in the image of $f$" — with **no $f$ introduced anywhere in the statement**, plus a "weighting weighting" typo|**4.8.16**: has $f$ and the timing condition but **no support clause**; and its timing condition names $A_n$ though the theorem's sequence is $B$|

In the propositional and affine rows the pattern is uniform: Recurring has no clause; Feedback has the clause. In the expectation row, as printed, the clause sits in the Recurring cell — where it is vacuous-slash-ill-formed, since that statement never introduces a deferral function — and is missing from the Feedback cell. The two cells' hypotheses look transposed.

### 3.2 The published statements, verbatim

Theorem 4.8.15 (Expectation Recurring Unbiasedness), p. 42 (ℓ1812–1820); restated E.11, p. 112:

> If $B \in \mathcal{BLCS}(\overline{\mathbb P})$ is determined via $\Gamma$, and $w$ is a $\overline{\mathbb P}$-generable divergent weighting weighting such that the support of $w$ is contained in the image of $f$, then the sequence $\dfrac{\sum_{i \le n} w_i (\mathbb E_i(B_i) - \mathrm{Val}_\Gamma(B_i))}{\sum_{i \le n} w_i}$ has $0$ as a limit point.

Theorem 4.8.16 (Expectation Unbiasedness From Feedback), p. 42 (ℓ1822–1832); restated E.12, pp. 112–113:

> Given $B \in \mathcal{BLCS}(\overline{\mathbb P})$ that is determined via $\Gamma$, a strictly increasing deferral function $f$ such that $\mathrm{Val}_\Gamma(A_n)$ can be computed in time $O(f(n{+}1))$, and a $\overline{\mathbb P}$-generable divergent weighting $w$, $\dfrac{\sum_{i\le n} w_i(\mathbb E_i(B_i) - \mathrm{Val}_\Gamma(B_i))}{\sum_{i\le n} w_i} \eqsim_n 0.$ In this case, we say "$w$ allows good feedback on $B$".

### 3.3 Resolution from the paper's own proofs, and the corrected statements

The appendix certifies which way the transposition goes. E.11's proof opens, p. 112:

> Proof. Let $\mathbb W \in \mathcal{PC}(\Gamma)$. Apply Theorem 4.5.9 (Affine Recurring Unbiasedness) to $(\mathrm{Ex}_n(B_n))_n$ and $w$ …

— an application of the _clause-free_ affine theorem, with no support requirement used or needed; so 4.8.15's printed clause (and its dangling $f$) is spurious. E.12 proves 4.8.16 by applying Theorem 4.5.10 (ℓ5260), whose hypotheses include the support clause; so the intended 4.8.16 inherits it, and the stray "$A_n$" is a copy residue from 4.5.10's statement. The corrected pair — my formulations, certified by those proofs (~0.95):

**4.8.15 (corrected).** $B \in \mathcal{BLCS}$ determined via $\Gamma$; $w$ _any_ generable divergent weighting. Then the weighted bias ratio has $0$ as a limit point (and converges to $0$ if it converges).

**4.8.16 (corrected) = Input U.** $B \in \mathcal{BLCS}$ determined via $\Gamma$; $f$ a strictly increasing deferral function; $w$ a generable divergent weighting with $\mathrm{supp}(w) \subseteq \mathrm{image}(f)$, such that the value of each _fired_ element is computable by the next firing ($\mathrm{Val}_\Gamma(B_{f(k)})$ in time $O(f(k{+}1))$ — the fired-element indexing is what D.4's buy-at-$f(i)$, sell-at-$f(i{+}1)$ mechanics support; a literal all-$n$ reading with fast-growing $f$ would leave fired bets unresolved across many firings and break the one-position wealth argument, ~0.9). Then the ratio $\to 0$.

This is an erratum in the published paper, worth reporting upstream, independent of everything downstream here.

---

## 4. Instantiating Input U in faithful's setting

Fix $X$ (an e.c. $[0,1]$-LUV of $H$'s language); $Y_n := E^H_{2^n}(X)$; $B_n := \ulcorner Y_n \urcorner$, a $\Gamma_A$-determined $[0,1]$-LUV (the coupled run is computable and $\Gamma_A \supseteq \mathrm{PA}$ proves its output — faithful's verified bullet); $a_n := E^A_n(B_n)$. Let $R(s)$ bound the time to run the coupled construction through stage $s$.

**Cost accounting.** $\mathrm{Val}_{\Gamma_A}(B_n) = Y_n$ is obtained only by producing $H$'s day-$2^n$ price: time $\sim R(2^n)$; reading either ledger to stage $s$ also costs $\sim R(s)$, so there is no cheaper route (~0.85). Hence a grid $G = {d_k} = \mathrm{image}(f)$ is **legal** for Input U iff $R(2^{d_k}) = O(d_{k+1})$ — tower-spaced — with $f$ computable in poly of its value (satisfiable by defining $d_{k+1}$ through an $R$-computation; Def 4.3.7's second condition). For contrast, the paper's own diagonal $\chi^p_n$ has values at cost $R(n)$: $R$-geometric grids — sparse, but incomparably denser.

**What the Recurring family gives with no grid** (used in §5.7 and §6): by 4.8.15-corrected — equivalently 4.5.9 applied to the grid-sum combinations — for _every_ generable divergent weighting, including everywhere-supported soft gates on the live quote, the weighted bias of $a_i$ against $Y_i$ has $0$ as a limit point. Unconditional, but limit-point only.

---

## 5. The argument executed

### 5.1 The setting, and the one hypothesis that must be made explicit

**(S1) Coupled pair, ledger-augmented criterion.** $H$ and $A$ are markets over deductive processes, interleaved (within round $n$: $H$'s day-$n$ prices post; $A$'s day-$n$ market clears; ledgers exchange — a fixed delay $c$ shifts indices and changes nothing asymptotically; I set $c = 0$). Each side satisfies the logical induction criterion (ℓ658) **relative to the ledger-augmented trader class $\mathcal C^+$**: strategies whose coefficients are continuous features of the own valuation sequence _and_ of the incoming ledger stream, with e.c. generators.

Why this must be a named hypothesis rather than a convenience: under the paper's literal Definition 3.4.4, $A$'s weightings are features of $A$'s prices only, and their generators have poly($n$) budgets, while reading either ledger at stage $n$ costs $R(n)$. If $R$ is super-polynomial (the LI construction's day cost plausibly is), a _pure_ LI weighting for $A$ can depend on $E^H_n(X)$ neither continuously (not $A$'s price) nor by hard-coding (budget) — only through $A$'s _price of the ledgered LUV_ as a proxy. Running §5.3 with proxies on both sides requires _absolute_ average proxy-fidelity along the grid, and the unbiasedness theorems supply only _signed_ averages, which mixed-sign mispricings can satisfy while absolute fidelity fails; I found no in-framework theorem closing this gap (~0.8 that the obstruction is essential). The corpus's own model asserts direct visibility — faithful ℓ142 states the weight "is recognizable to both inductors", and faithful ℓ254 flags the Lean-side shadow of exactly this seam ("that continuity upgrades to full $\mathcal C_H$-expressible-feature legality … stays in the modeling layer"). (S1) is that assertion, made explicit.

**(S2) Lemma R (relativization; ~0.85).** The theorems of §2.2–§2.3, hence the corrected 4.8.15/4.8.16, hold with "generable" meaning $\mathcal C^+$-generable, for a market unexploitable by $\mathcal C^+$-traders. Reason: the exploiting traders in D.2/D.4 are constructed _from_ the given weighting, multiplied into standard buy/sell bookkeeping; nothing uses minimality of the feature language, so enlarging the class enlarges theorem scope and criterion strength in step. Checkpoint: pp. 99–104.

**(S3) Targets and grids** as in §4; the round-trip windows $[d_k, 2^{d_k}]$ of a legal grid are pairwise disjoint.

### 5.2 Theorem (Grid-wise Gated Trust)

Assume (S1)–(S3). For every rational $t \in [0,1]$, $\varepsilon, \delta > 0$, and every legal grid $G = {d_k}$: $$\sum_k w_{d_k} < \infty, \qquad w_n := \mathrm{Ind}_\delta(a_n > t) \cdot \mathrm{Ind}_\delta\big(E^H_n(X) < t - \varepsilon\big).$$

### 5.3 Proof

Suppose $W_K := \sum_{k \le K} w_{d_k} \to \infty$.

**Step A (Input U along $G$).** The weighting $u := w \cdot \mathbb 1_G$ is $\mathcal C^+_A$-generable (jointly continuous in the visible pair $(a_n, E^H_n(X))$ — the continuity fact faithful's `dsWeight_continuous` isolates), divergent, supported in $\mathrm{image}(f) = G$, with $\mathrm{Val}(B_{d_k}) = Y_{d_k}$ computable in $R(2^{d_k}) = O(d_{k+1})$. By 4.8.16-corrected, relativized by Lemma R: $\sum_{k \le K} w_{d_k}(a_{d_k} - Y_{d_k}) = o(W_K)$. On the support $a_{d_k} > t$, so $$\sum_{k \le K} w_{d_k}, Y_{d_k} ;\ge; t,W_K - o(W_K).$$

**Step B.** On the support $E^H_{d_k}(X) < t - \varepsilon$, so $\sum_{k \le K} w_{d_k}\big(Y_{d_k} - E^H_{d_k}(X)\big) \ge (\varepsilon - o(1)) W_K$.

**Step C (Input C).** The $\mathcal C^+_H$-trader $T$: at day $d_k$, stake $\lambda, w_{d_k}$ of its running budget on $X$ at price $E^H_{d_k}(X)$; unwind at day $2^{d_k}$ at $H$'s own then-price $E^H_{2^{d_k}}(X) = Y_{d_k}$ — the round trip is $H$-internal. $T$ is e.c.; windows are disjoint, so at most one position is open; with $\lambda \le \tfrac12$ its worth is bounded below. With $\Delta_k := Y_{d_k} - E^H_{d_k}(X) \in [-1,1]$: $$\log b_K ;\ge; \lambda \sum_{k \le K} w_{d_k} \Delta_k ;-; \lambda^2 \sum_{k \le K} w_{d_k} ;\ge; \big(\lambda(\varepsilon - o(1)) - \lambda^2\big) W_K ;\to; \infty \quad (\lambda < \varepsilon/2)$$ in every plausible world (the payoffs are realized market prices). This exploits $H$, contradicting (S1). $\blacksquare$

This is faithful's Steps 1–4 with three corrections: the weighting quantifier (support clause), the disjoint-window discipline (supplied by the grid), and the explicit class in which "recognizable to both" is legal. The kernel-checked Lean core (`hbias` + `hbdd` $\Rightarrow \sum w < \infty$) is Steps A–C's arithmetic; what changed is which `hbias` the LI theorems supply.

### 5.4 Corollary 1 (grid-wise averaged trust)

If additionally $\sum_k \mathrm{Ind}_\delta(a_{d_k} > t) = \infty$: $\liminf_K \frac{\sum_{k \le K} \mathrm{Ind}_\delta(a_{d_k} > t), E^H_{d_k}(X)}{\sum_{k \le K} \mathrm{Ind}_\delta(a_{d_k} > t)} \ge t - \varepsilon - \delta$. (Faithful's Corollary proof restricted to $G$: deep days have saturated inner ramp and finite gate-mass by the Theorem; all other gated days sit above $t - \varepsilon - \delta$.)

### 5.5 Corollary 2 (grid-wise per-day dominance)

For every legal grid $G$: $\liminf_k \big(E^H_{d_k}(X) - a_{d_k}\big) \ge 0$. _Proof._ Otherwise some $c > 0$ has $E^H_{d_k} \le a_{d_k} - c$ along an infinite $I \subseteq G$; then $a_{d_k} \ge c$ there; pass to $a_{d_k} \to a^_$; pick rational $t \in (a^_ - \tfrac c2, a^* - \tfrac c4)$ and rational $\varepsilon \le \tfrac c8$: on a tail of $I$ both ramps of $w_{d_k}(t, \varepsilon, \delta)$ are bounded below, so the Theorem's sum diverges — contradiction. $\blacksquare$ On every prescheduled sparse audit grid, $H$'s live credence is eventually never undercut by $A$'s flag, at any margin.

### 5.6 What is _not_ delivered

The boxed $\sum_n w_n < \infty$ over all days does not follow: a violation profile $w_n \sim 1/\log n$ has every tower-sparse subsum finite while the total diverges. Per-day $w_n \to 0$ does not follow either: a deferral image is a _fixed_ function chosen in advance, so grids cannot chase violations — only the weights at pre-fixed days respond to prices — and violations may avoid every fixed e.c. grid. Nor can the Recurring family densify the conclusion: it yields $0$ as a limit point of the $A$-side ratio along _some_ day-subsequence, while Step C needs the $A$-side and $H$-side quantities controlled along the _same_ subsequence. Honest reading of the positive result: **gated-trust violations are not preschedulable** — no efficiently pre-committed sparse audit catches them with divergent weight — a real guarantee, strictly weaker than the box. (~0.85; standing residual: a densification theorem I have not found.)

### 5.7 The gridless companion (unconditional)

From 4.8.15-corrected (via 4.5.9 and Lemma R): for every $\mathcal C^+_A$-generable divergent weighting — e.g. the everywhere soft gate $\mathrm{Ind}_\delta(a_n > t)$, or that gate times any continuous function of both visible prices — the ratio $\sum u (a - Y)/\sum u$ has $0$ as a limit point. This refutes any _one-signed, bounded-away_ bias on a divergent gate (which is what §6 runs on), but cannot power the §5.3 squeeze.

### 5.8 Hypothesis audit

|hypothesis|supplied by|status|
|---|---|---|
|coupled pair exists; each side an inductor for $\mathcal C^+$|one-stage-delay construction + strengthened criterion|asserted in corpus (obligation 3); construction standard (~0.9); $\mathcal C^+$-criterion needs Lemma R or a re-run of the paper's §5 construction with the larger class (~0.85)|
|$B \in \mathcal{BLCS}$, determined via $\Gamma_A$|faithful ℓ74ff|verified (grid-sum form; PA proves run outputs)|
|legal grid: $d_{k+1} \ge R(2^{d_k})$, e.c.|choice|constructible for computable $R$|
|Input U = 4.8.16-corrected|§3|erratum-fixed; proof-certified|
|Input C vs the §5.3 trader|(S1)|trader is e.c., bounded-risk, disjoint windows|
|any restriction on $X$|—|**none appears**|

---

## 6. Where the diagonal sits (no domain hypothesis needed)

The §5.2 Theorem quantifies over a fixed $X$ with hypotheses that never mention self-reference. Applied to a fixed member $g_m$ of the diagonal family ($g_m \leftrightarrow$ "$a_m \le \tfrac12$", ledger-decided by $\sim m{+}2$): the fixed-$X$ statement is true and nearly empty — violations confine to finitely many pre-decision days. The _family-indexed_ question ($A$'s day-$n$ forecast of the day-$n$ contract) is governed by §5.7's currency, and the Recurring family forces the pinned regime rather than a breakdown:

**Fact (quote pinning).** With $Y_n = s_n \pm \eta_n$, $\eta_n < \tfrac14$ eventually: $a_n \to \tfrac12$. _Proof._ For rational $m \in (0, \tfrac14)$, the gate $\mathrm{Ind}_\delta(a_n > \tfrac12 + \tfrac m2)$ is generable; cofinitely on its support $a_n$ exceeds the grid threshold, so $s_n = 0$ and the bias $a_n - Y_n > \tfrac14$: one-signed and bounded away, so by §5.7 the gate cannot be divergent, and days with $a_n \ge \tfrac12 + m$ (each carrying ramp weight $\ge \min(\tfrac m{2\delta}, 1)$) are finitely many. Low side symmetric. $\blacksquare$

The paper's published context for this regime is Theorem 4.11.2 (Paradox Resistance), p. 46 (ℓ1993):

> Fix a rational $p \in (0,1)$, and define an e.c. sequence of "paradoxical sentences" $\overline{\chi^p}$ satisfying $\Gamma \vdash \chi^p_n \leftrightarrow (\mathbb P_n(\chi^p_n) < p)$ for all $n$. Then $\lim_{n \to \infty} \mathbb P_n(\chi^p_n) = p$.

The surrounding discussion (pp. 46–47; ℓ2006, 2010) adds that the truth-frequency has a limit point at $p$ by Recurring Unbiasedness, that there is no efficiently expressible method for identifying a bias in the price, and — the brain-scanner paragraph — that the price is pushed so close to $p$ that no one can tell which way each instance will resolve. The cross-process diagonal realizes the same regime: the theorems hold, the quote is pinned and side-empty, and what vanishes on the diagonal is the positive result's _content_, not its truth. Any restriction worth stating is interpretive (where the quote is informative), not a hypothesis of the theorem. Where §2.4's family enters: on such sequences the paper's own positive account is Theorem 4.4.5/4.8.17-style — the price falls back on the best patient-weighting statistics, here $\tfrac12$.

---

## 7. Side-by-side: faithful's statement vs. the corrected one

|faithful (as written)|corrected|
|---|---|
|(II): "any $\mathcal C_A$-generable divergent weighting … _patient_ (deferred until the feedback is in)"|Input U = 4.8.16-corrected: generable divergent $w$ with $\mathrm{supp}(w) \subseteq \mathrm{image}(f)$, fired values computable by the next firing; "patient" reserved for Def 4.4.3's family (§2.4)|
|implicit trader model: "recognizable to both inductors"|explicit (S1): ledger-augmented class $\mathcal C^+$ + Lemma R (§5.1)|
|boxed: $\sum_n w_n < \infty$ over all days|$\sum_{n \in G} w_n < \infty$ for every legal grid $G$ ($d_{k+1} \ge R(2^{d_k})$, disjoint windows)|
|"(II) holds over all sentences"|no domain hypothesis anywhere; on the diagonal the theorems hold degenerately (§6)|
|strength narrative ("strongest forceable rung"; "averaged in, averaged out")|forced content: grid-wise sums (§5.2), grid-wise per-day dominance (§5.5), gridless limit points (§5.7); violations not preschedulable (§5.6)|

## 8. Checkpoints

In rough order of value per minute: (1) the erratum — p. 42 and pp. 112–113 against §3 (two minutes). (2) D.2/D.4 (pp. 99–104) for Lemma R's relativization claim, the one hypothesis §5 adds to the corpus's own model. (3) The §5.3 proof, self-contained above. (4) The §5.1 obstruction argument — my newest claim. (5) The §4 cost model ($R(2^n)$, no shortcut). Prior working documents contain the longer audit trail; nothing above depends on them beyond what is quoted or proved here.