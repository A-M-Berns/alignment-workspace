# Deference Between Coupled Logical Inductors: the Corrected Positive Result

*Claude, 2026-07-10 (v3). Audience: a reader familiar with the Logical Induction paper (Garrabrant et al., arXiv:1609.03543v5; page numbers below refer to that PDF), not with the working history behind this note. Everything is developed from the setup; proofs are given in full. Two statements below correct earlier claims of mine — they are flagged where they occur and stated plainly, without recap. One statement corrects the published paper and is boxed as such.*

---

## 0. Overview

Two logical inductors run side by side: $H$ ("the human"), whose language contains a target $X$, and $A$ ("the forecaster"), which each day $n$ publishes a quote: its expectation of the *human's own credence in $X$ at the much later day $2^n$*. The intended service is acceleration — $A$ tells $H$ today where $H$'s beliefs are heading. The question is what this buys $H$: on days when the quote is high but $H$'s current credence is low, must $H$ close the gap?

Write, for a fixed $[0,1]$-valued LUV $X$ of $H$'s language and rationals $t \in [0,1]$, $\varepsilon, \delta > 0$:
$$w_n \;:=\; \mathrm{Ind}_\delta\Big(\mathbb E^A_n\big(\text{“}\mathbb E^H_{2^n}(X)\text{”}\big) > t\Big)\cdot \mathrm{Ind}_\delta\Big(\mathbb E^H_n(X) < t - \varepsilon\Big),$$
the (soft-thresholded) weight of day $n$ as a *violation day*: quote above $t$, current human credence below $t - \varepsilon$. The results, under the assumptions of §1:

- **Theorem 1 (scheduled form).** On every efficiently computable schedule $d_1 < d_2 < \cdots$ whose entries satisfy $d_{k+1} \ge 2^{d_k}$, the total violation weight $\sum_k w_{d_k}$ is finite.
- **Theorem 2 (adaptive form; two flagged obligations).** $w_n \to 0$ over *all* days. Consequently (Corollary 2) for every margin $c > 0$, only finitely many days have $\mathbb E^H_n(X) \le \mathbb E^A_n(\text{“}\mathbb E^H_{2^n}(X)\text{”}) - c$; and (Corollary 3) $\sum_n w_n < \infty$ over all days, for every rational $(t, \varepsilon, \delta)$.

Both theorems are driven by a *limit-point* unbiasedness theorem — Expectation Recurring Unbiasedness, in the corrected form of §2 — together with a wealth argument against $H$. No feedback-timing theorem is used, and no computability bound on the coupled construction's run time enters the main line. The conclusions are one-sided (nothing stops the human's credence from exceeding the quote), per-$X$ (the finite counts depend on $X$ and the margins, with no uniformity claimed), and rate-free. Section 6 states exactly what is not established.

Credences, stated once: Theorem 1, ~0.85 conditional on the assumptions of §1; Theorem 2, ~0.75 (the additional load is §4's two obligations); the §2 correction to the published paper, ~0.95 (certified by the paper's own appendix proofs).

---

## 1. Setting and assumptions

**(A1) The coupled pair, with joint clearing.** $H$ and $A$ are markets over their own deductive processes. Each day $n$, *both* markets clear together, as one fixed point: a trader's day-$n$ coefficients may depend continuously on the day-$\le n$ prices of *both* markets, and its e.c. generator may hard-code any constants it can compute in time polynomial in $n$. Each side separately satisfies the logical induction criterion (no e.c. trader of this joint class exploits it). Three remarks:

- *Existence.* The paper's construction produces one market per day by a Brouwer-style fixed point over trading strategies continuous in that market's prices; the joint version takes the fixed point over the pair of price vectors at once, with continuity in the pair. I assume this construction goes through; it has the same shape as the paper's §5 and I see no obstruction, but it is an assumption, not a citation.
- *Relativization.* The unbiasedness theorem used in §2 is proved in the paper for weightings generable from a single market's prices. Its proof (appendix D.2) builds the exploiting trader *from* the given weighting, used as a black box; nothing appears to use minimality of the feature language, so the theorem should hold verbatim for the joint class against the joint criterion. This is the one place where a reader verifying this note should open the paper's proofs (checkpoint list, §7).
- *Why joint clearing is needed, not just convenient.* The violation weight $w_n$ reads the same-day pair (quote, human price). Under strict alternation — one market clears before the other each round — one side's day-$n$ features can see only the other's day-$(n{-}1)$ output, and the resulting one-day staleness is not controlled by anything in this argument: a single day can move a price by $\Theta(1)$. I do not know how to run the proof under strict alternation; joint clearing (equivalently: same-round mutual visibility, which is also what makes $w_n$ "recognizable to both sides") is a genuine hypothesis.

**(A2) The target and the lookahead.** $X$ is a fixed $[0,1]$-LUV of $H$'s language. The lookahead is $n \mapsto 2^n$ for concreteness; any e.c. strictly increasing $\ell$ with $\ell(n) > n$ works with $2^{d_k}$ replaced by $\ell(d_k)$ throughout. The forecast-target sequence $\big(\text{“}\mathbb E^H_{2^n}(X)\text{”}\big)_n$ — the LUV whose value is defined by running the coupled construction to stage $2^n$ and reading the human's price of $X$ — is efficiently computable *as a sequence of expressions* (a fixed template plus the numeral $n$), bounded by $1$, and a legal $\mathcal{BLCS}$ sequence for $A$.

**(A3) Determinacy.** $\Gamma_A$ extends PA and proves the outputs of the coupled construction, so each forecast-target LUV is *determined via $\Gamma_A$*: every world propositionally consistent with $\Gamma_A$ assigns it the same value, namely the human's actual later credence $\mathbb E^H_{2^n}(X)$. Note what is *not* needed here: no bound on how long the construction takes to run. Determinacy is a logical condition, and this is why the limit-point theorem of §2 — whose hypotheses ask only for determinacy — can carry the whole argument, where a feedback-timing theorem would drag the construction's run cost into the hypotheses.

That is the complete list for Theorem 1. Theorem 2 adds one expressibility assumption, stated in §4.

---

## 2. The engine: Expectation Recurring Unbiasedness, corrected

> **Correction to the published paper.** In arXiv:1609.03543v5, the statements of Theorem 4.8.15 (Expectation Recurring Unbiasedness) and Theorem 4.8.16 (Expectation Unbiasedness From Feedback), p. 42 (restated pp. 112–113), have a hypothesis transposed between them: 4.8.15 as printed carries the clause "such that the support of $w$ is contained in the image of $f$" while introducing no deferral function $f$ (and contains a doubled word, "weighting weighting"); 4.8.16 as printed omits that clause (and its timing condition names $A_n$ where the theorem's sequence is $B$). At the propositional and affine levels the pattern is uniform — Recurring (4.3.6, 4.5.9): no support clause and no deferral function; From Feedback (4.3.8, 4.5.10): both — and the appendix proofs certify that the expectation level was meant to match: E.11 proves 4.8.15 by applying the clause-free Theorem 4.5.9, with no support condition used, and E.12 proves 4.8.16 by applying Theorem 4.5.10, whose hypotheses include the clause. Corrected statements: 4.8.15 holds for *every* $\overline{\mathbb P}$-generable divergent weighting; 4.8.16 requires the support clause.

The corrected theorem used below — and the only unbiasedness input this note needs:

**Theorem R (= 4.8.15 corrected, relativized per (A1)).** Let $\overline B$ be an e.c. bounded sequence of LUV-combinations for $A$, determined via $\Gamma_A$, and let $\overline u$ be any divergent weighting generable from the joint price history. Then
$$\frac{\sum_{i \le n} u_i\,\big(\mathbb E^A_i(B_i) - \mathrm{Val}_{\Gamma_A}(B_i)\big)}{\sum_{i \le n} u_i}$$
has $0$ as a limit point: there are days $n_1 < n_2 < \cdots$ along which the weighted average forecast error tends to $0$.

Two features matter. The weighting is unrestricted (any generable divergent weighting — in particular, weightings supported everywhere, and weightings defined by price-responsive state machines). The conclusion is weak — vanishing average error only along *some* subsequence of days. The work of §§3–4 is to show that a wealth argument needs no more: the human-side trader's profit is *realized cash*, monotone in a way that lets unboundedness along the checkpoint subsequence suffice.

---

## 3. Theorem 1: bounded violation weight on window-disjoint schedules

**Definitions.** A *schedule* is an e.c. strictly increasing sequence $d_1 < d_2 < \cdots$ of days. It is *window-disjoint* if $d_{k+1} \ge 2^{d_k}$: the round trip opened on day $d_k$ (and closed at day $2^{d_k}$, when the forecast target realizes) is over before the next opens.

A flagged correction of an earlier claim of mine: the schedule condition really is $d_{k+1} \ge 2^{d_k}$ — sets of tower-type growth, such as $1, 2, 4, 16, 2^{16}, \ldots$ — not merely geometric sets like $\{2^k\}$, whose round-trip windows $[2^k, 2^{2^k}]$ overlap unboundedly. Density beyond window-disjointness is recovered in §4 by a different mechanism, not by denser schedules.

**Theorem 1.** Assume (A1)–(A3). For every rational $t \in [0,1]$, $\varepsilon, \delta > 0$ and every window-disjoint schedule $\overline d$:
$$\sum_{k} w_{d_k} < \infty.$$

**Proof.** Suppose $W_K := \sum_{k \le K} w_{d_k} \to \infty$.

*The forecaster-side average.* Apply Theorem R with $B_n := \text{“}\mathbb E^H_{2^n}(X)\text{”}$ and weighting $u_n := w_n$ on schedule days, $0$ elsewhere. The weighting is generable from the joint history — each factor of $w_n$ is a width-$\delta$ ramp in a day-$n$ price visible under (A1), and the schedule indicator is hard-coded by the e.c. generator — and divergent by supposition. So there are days $n_1 < n_2 < \cdots$ with
$$\frac{\sum_{d_k \le n_j} w_{d_k}\Big(\mathbb E^A_{d_k}\big(\text{“}\mathbb E^H_{2^{d_k}}(X)\text{”}\big) - \mathbb E^H_{2^{d_k}}(X)\Big)}{W(n_j)} \;\longrightarrow\; 0,$$
where $W(n)$ is the scheduled violation weight through day $n$ (and $W(n_j) \to \infty$, since $W$ is nondecreasing and unbounded). Wherever $w_{d_k} > 0$, the quote ramp is strictly positive, so the quote exceeds $t$; hence at the checkpoint days,
$$\sum_{d_k \le n_j} w_{d_k}\,\mathbb E^H_{2^{d_k}}(X) \;\ge\; \big(t - o(1)\big)\,W(n_j). \tag{3.1}$$
In words: *averaged over the flagged schedule days, the human's later credence really is at least $t$* — the forecaster cannot advertise high forever, on a weighting it can recognize, about a quantity its theory determines, and be wrong on average, even though nothing requires it (or anyone) to be able to compute that quantity quickly.

*The human-side trader.* Define the e.c. trader $T$: it holds a budget, starting at $1$; on day $d_k$ it invests the fraction $\lambda\, w_{d_k}$ of its current budget in $X$ at the price $\mathbb E^H_{d_k}(X)$, where $\lambda$ is a rational constant fixed below with $\lambda \le \tfrac12$; on day $2^{d_k}$ it sells the entire position at the then-current price $\mathbb E^H_{2^{d_k}}(X)$. By window-disjointness at most one position is ever open. The multiplicative accounting: writing $b_K$ for the budget after the $K$-th round trip,
$$b_K \;=\; \prod_{k \le K}\Big(1 + \lambda\, w_{d_k}\big(\mathbb E^H_{2^{d_k}}(X) - \mathbb E^H_{d_k}(X)\big)\Big).$$
Every factor lies in $[\tfrac12, \tfrac32]$, so the budget is always positive; while a position is open, the trader's worth in any world $\mathbb W$ assigning $X$ a value in $[0,1]$ is $b_{k-1}\big(1 + \lambda w_{d_k}(\mathbb W(X) - \mathbb E^H_{d_k}(X))\big) \ge b_{k-1}/2 > 0$. So the trader's plausible worth is bounded below by $0$ at all times, unconditionally. Everything the trader computes — the schedule, the ramps, the running budget — is available to a joint-class e.c. trader; the bookkeeping is the same as the paper's own appendix traders.

*The squeeze.* Wherever $w_{d_k} > 0$, the credence ramp is strictly positive, so the purchase price satisfies $\mathbb E^H_{d_k}(X) < t - \varepsilon$; hence $\sum_{d_k \le n} w_{d_k}\,\mathbb E^H_{d_k}(X) \le (t - \varepsilon)\,W(n)$ for every $n$. Using $\log(1+x) \ge x - x^2$ for $x \ge -\tfrac12$, and $w^2 \le w$, the log-budget after the trips completed by day $n_j$ (closing the last window if needed costs at most a factor $\tfrac12$):
$$\log b(n_j) \;\ge\; \lambda \sum_{d_k \le n_j} w_{d_k}\big(\mathbb E^H_{2^{d_k}}(X) - \mathbb E^H_{d_k}(X)\big) \;-\; \lambda^2\, W(n_j) \;-\; \log 2 \;\ge\; \big(\lambda(\varepsilon - o(1)) - \lambda^2\big) W(n_j) - \log 2$$
by (3.1) and the purchase-price bound. Fix $\lambda := \min(\tfrac12, \varepsilon/4)$: the right side tends to $+\infty$ along $j$. The trader's plausible worth is thus unbounded above over days-and-worlds while bounded below — the definition of exploitation — contradicting $H$'s criterion under (A1). Hence $W_\infty < \infty$. $\blacksquare$

Note where each assumption worked: (A1) made $w$ legal for Theorem R and legible to the trader; (A3) made the forecast targets determined, so Theorem R applied with no timing condition; window-disjointness kept one position open, which is what made "unbounded along a subsequence, bounded below always" available from a limit-point premise. The lookahead's size never entered except through the window length.

---

## 4. Theorem 2: the adaptive upgrade

Fixed schedules cannot chase violations: if the violation days themselves avoid every e.c. window-disjoint set, Theorem 1 says nothing about them. But the *trader* is not required to fix its days in advance — it may watch prices and fire when a violation appears, provided it never holds two positions at once. That single change upgrades the conclusion from schedule-wise sums to a per-day statement over all days.

**The additional assumption (A4).** For each rational threshold $\theta > 0$ (with a soft ramp of width $\theta/2$, say), the following one-position state machine is expressible as an e.c. joint-class trader, and its firing indicator as a joint-generable weighting: *maintain a state $\in \{\text{flat}, \text{holding until day } h\}$; when flat on a day $n$ with $w_n \ge \theta$ (softly), open a position of budget-fraction $\lambda\, w_n$ and set $h := 2^n$; when day $h$ arrives, close and return to flat.* The day-$n$ state is a function of the joint price history through day $n$, computed by composing one bounded-size soft update per day — an expression of size linear in $n$, built from the feature algebra's products, maxima, and ramps. I rate the routine-but-unverified claim that this softened state machine lives inside the paper's expressible-feature algebra at ~0.85; it is the first of the two obligations this section carries. (The second is (A1)'s relativization remark, which Theorem 2 leans on harder, since the firing weighting is now itself a price-responsive state machine.)

**Theorem 2.** Assume (A1)–(A4). For every rational $t, \varepsilon, \delta$: $\;w_n \to 0$ as $n \to \infty$.

**Proof.** Fix rational $\theta > 0$; it suffices to show only finitely many days have $w_n \ge \theta$. Let $T_\theta$ be the (A4) trader and $u_n$ its firing weight (so $u_n > 0$ only when $T_\theta$ opens on day $n$, and then $u_n \ge$ a fixed positive fraction of $w_n \ge \theta$-level; $u_n \le w_n$).

Suppose $T_\theta$ fires infinitely often. Then $\sum_n u_n = \infty$ (each firing contributes at least a fixed positive amount), and $u$ is a joint-generable divergent weighting by (A4). Theorem R applied with weighting $u$ gives checkpoint days along which the $u$-averaged forecast error vanishes; on $u$'s support the quote exceeds $t$ and the purchase price is below $t - \varepsilon$ (both ramps are positive wherever $w_n > 0$), so exactly the computation of §3 — (3.1), the purchase-price bound, and the log-budget telescope, with $u$ in place of the scheduled $w$, and with one open position by construction — makes $T_\theta$'s plausible worth unbounded above and bounded below. That exploits $H$: contradiction. So $T_\theta$ fires only finitely often.

Now count the days with $w_n \ge \theta$. Each lies either inside one of $T_\theta$'s holding windows or on a day when $T_\theta$ is flat. There are finitely many windows (one per firing), each of finite length. And a flat day with $w_n \ge \theta$ *is* a firing day, by the firing rule. So the days with $w_n \ge \theta$ are contained in finitely many finite windows plus finitely many firing days: finitely many in total. $\blacksquare$

**Remark (what adaptivity did and did not buy).** The trader chases violations, so no violation level $\theta$ can recur outside a finite set of days — but the trader still goes blind for the length of each window it opens, which is why the conclusion is per-day smallness and not, directly, anything about weights summed inside windows. The corollaries below show that per-day smallness, closed under the rational parameters, is nonetheless enough to recover the summed statement.

---

## 5. Corollaries

Throughout, "the quote" means $\mathbb E^A_n\big(\text{“}\mathbb E^H_{2^n}(X)\text{”}\big)$. Corollaries 2–4 assume Theorem 2; their schedule-restricted analogues follow from Theorem 1 alone by the same proofs read along a schedule.

**Corollary 1 (per-day vanishing, all parameters).** For every rational $t, \varepsilon, \delta$: the violation weight $w_n(t, \varepsilon, \delta) \to 0$. (This is Theorem 2 itself, recorded as the base form.)

**Corollary 2 (per-day dominance).** $\displaystyle \liminf_{n \to \infty}\Big(\mathbb E^H_n(X) \;-\; \mathbb E^A_n\big(\text{“}\mathbb E^H_{2^n}(X)\text{”}\big)\Big) \;\ge\; 0.$

Equivalently: for every margin $c > 0$, only finitely many days on which the quote exceeds the human's live credence by more than $c$.

*Proof.* Suppose not: for some $c > 0$ there are infinitely many days $n \in I$ with $\mathbb E^H_n(X) \le \text{quote}_n - c$. On $I$ the quote is at least $c$; since quotes lie in $[0,1]$, pass to an infinite $I' \subseteq I$ on which the quote converges to some $q^* \ge c$, and discard finitely many days so that the quote is within $c/8$ of $q^*$ on $I'$. Choose rationals $t \in (q^* - \tfrac c2,\; q^* - \tfrac c4)$, $\varepsilon \le \tfrac c8$, and $\delta \le \tfrac c8$. On $I'$: the quote exceeds $t$ by at least $(q^* - \tfrac c8) - (q^* - \tfrac c4) = \tfrac c8$, so the quote ramp is at least $\min(\tfrac{c}{8\delta}, 1)$; and the human's credence is at most $(q^* + \tfrac c8) - c = q^* - \tfrac{7c}8 \le t - \tfrac{3c}8 < (t - \varepsilon) - \delta$, so the credence ramp equals $1$. Hence $w_n(t,\varepsilon,\delta)$ is bounded below by a positive constant on the infinite set $I'$ — contradicting Corollary 1 at these rational parameters. $\blacksquare$

**Corollary 3 (summability over all days).** For every rational $t, \varepsilon, \delta$: $\;\sum_n w_n(t,\varepsilon,\delta) < \infty$.

*Proof.* A day with $w_n > 0$ has quote $> t$ and credence $< t - \varepsilon$, hence credence $<$ quote $- \varepsilon$. By Corollary 2 with $c = \varepsilon$ there are finitely many such days; each term is at most $1$. $\blacksquare$

This recovers, from the corrected foundations, the strongest form of the conjectured deference statement — the sum over *all* days, no schedule — as a consequence of the per-day theorem rather than as the direct output of a summed trader argument. (The implication also runs backward at the family level: summability at all rational parameter values yields Corollary 2 by the same compactness argument; the two packagings are equivalent.)

**Corollary 4 (averaged form).** Let $g_n := \mathrm{Ind}_\delta(\text{quote}_n > t)$ be any high-quote gate with $\sum_n g_n = \infty$. Then
$$\liminf_{N \to \infty}\; \frac{\sum_{n \le N} g_n\, \mathbb E^H_n(X)}{\sum_{n \le N} g_n} \;\ge\; t - \varepsilon - \delta .$$

*Proof.* Split gated days by whether $\mathbb E^H_n(X) \le t - \varepsilon - \delta$. On such "deep" days the credence ramp saturates, so their total gate mass is at most $\sum_n w_n < \infty$ (Corollary 3). All other gated days contribute at least $t - \varepsilon - \delta$ each to the numerator. Divide by the divergent gate mass. $\blacksquare$

**Corollary 5 (plain-language packaging, and its limits).** On any fixed question $X$, the human's live credence is eventually never undercut by the forecaster's advertisement, at any margin. Three built-in limits keep this from proving too much. It is *one-sided*: nothing constrains days when the human's credence exceeds the quote, so the quote can still be informative precisely by being *lower* than the human's current view, and the human's convergence *upward* toward a high quote is forced only in the average sense of Corollary 4. It is *per-question*: the finite counts in Corollaries 2–3 depend on $X$ and on the margins, with no uniformity across questions — the acceleration value of the forecaster lives in the early, transient segment of each question and across the family of questions, and none of that is bounded here. And it is *rate-free*: nothing bounds how long "finitely many" lasts.

---

## 6. What is not established, and where the self-referential family sits

**Not established.** (i) Any rate, or any uniformity in $X$. (ii) The two obligations: relativization of the paper's D.2 proof to the joint class (used by both theorems, leaned on harder by Theorem 2), and the (A4) expressibility of the softened one-position state machine. (iii) Anything under strict alternation of the two markets: the one-day staleness gap of §1 is open, and with it the question of whether joint clearing is essential or an artifact of this proof. (iv) Theorem 2's conclusions if (A4) fails: then Theorem 1 and the schedule-restricted corollaries are what remains.

**The self-referential family.** No hypothesis above mentions self-reference, and none is needed: the theorems are per-$X$, and for a self-referential target of the diagonal type — a sentence $g$ arranged (by the diagonal lemma, through a ledger that records the quotes) to be true iff the day-$m$ quote about *it* is at most $\tfrac12$ — the fixed-$X$ statements are true and nearly empty, since such a sentence is decided within a couple of days of its quote and violations confine to that transient. The *family-indexed* question — the day-$n$ quote about the day-$n$ member — is a different quantifier, and there the same limit-point machinery forces a pinned regime rather than a breakdown: writing $s_n \in \{0,1\}$ for the settled side of the $n$-th member and assuming the human's day-$2^n$ credence tracks it to within $\tfrac14$ eventually, every one-sided margin gate $\mathrm{Ind}_\delta(\text{quote}_n > \tfrac12 + m)$ would, if divergent, exhibit a one-signed weighted forecast error bounded away from $0$ (quote high forces the side false and the realized value near $0$), which Theorem R forbids; symmetrically below. So the family quotes converge to $\tfrac12$, carrying no side information — the cross-process analogue of the paper's Paradox Resistance regime (Theorem 4.11.2, p. 46: the price of "$\mathbb P_n(\chi_n) < p$"-type sentences converges to $p$). The positive result needs no domain restriction; what varies over targets is whether its content is substantive or, as there, degenerate.

## 7. Checkpoints for a verifying reader

In order of leverage: (1) the §2 correction against pp. 42 and 112–113 of the paper — a two-minute read of four statements and two proof openings. (2) Appendix D.2 (Recurring Unbiasedness proof) for the relativization remark of (A1): confirm the exploiting trader treats the weighting as a black-box feature. (3) The proof of Theorem 1 (§3), which is self-contained given Theorem R. (4) The finitely-many-windows count in Theorem 2's last paragraph, and (A4). (5) The compactness proof of Corollary 2, which is what converts per-day smallness into dominance and summability.
