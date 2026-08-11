# Faithful acceleration: the corrected positive result

*The canonical statement of what is forced when a fast inductor publishes forecasts of a slow inductor's future beliefs — Eisenstat's merge conjecture, in the half that concerns trust. Setting: two logical inductors $H \dashv \mathcal C_H$ (the human) and $A \dashv \mathcal C_A$ (the forecaster), each satisfying the criterion over its own deductive process. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

*Supersedes, for the statement of the result: `faithful-acceleration.md`, `faithful-acceleration-scope.md`, `pointwise-tower-and-faithful-acceleration.md`, `fa-positive-result-corrected.md` (v1) and `fa-positive-results-corrected-v2.md` — v1/v2 rest on an architecture retracted at FA-chat msg 39 and are **actively misleading if read alone**. Best legacy file-form statement: `imported-chats/fa-positive-results-corrected-v3.md` (**cite that copy**, not the degraded root one — see [[index]]). This page adds the factoring and the two routes v3 does not have.*

*⚠ Attribution correction (2026-08-10): "Eisenstat's merge conjecture" on this page names the **corpus construal**, whose visibility structures (joint clearing / one-way with $H$ reading the ledger same-day / AI-side delay) do not match the information structure Sam Eisenstat intended — AI reads human beliefs immediately, humans see AI beliefs only at a delay. His intended conjecture is not settled by anything here; see [[eisenstat-conjecture-attribution]].*

---

## 1. The object

$X_n$ is an e.d. LUV of $H$'s language — the question. $f$ is an e.c. strictly increasing lookahead ($f(n) > n$; canonically $2^n$). Write

$$Y_n := \mathbb E^H_{f(n)}(X_n) \qquad\text{(the human's \emph{future} credence — the forecast target)}$$
$$a_n := \mathbb E^A_n(\ulcorner Y_n\urcorner) \qquad\text{(the quote)}$$

and, for rationals $t\in[0,1]$ and $\varepsilon,\delta>0$, the violation weight
$$w_n \;:=\; \operatorname{Ind}_\delta(a_n > t)\cdot\operatorname{Ind}_\delta\big(\mathbb E^H_n(X_n) < t-\varepsilon\big).$$

**Standing assumptions.** $\overline{\ulcorner Y\urcorner}$ is an e.c. sequence of expressions (a fixed template plus the numeral $n$), bounded, hence a legal $\mathcal{BLCS}$ sequence for $A$; and it is **determined via $\Gamma_A$** — every world propositionally consistent with $\Gamma_A$ assigns it the human's actual later credence. Determinacy is a *logical* condition: no bound on how long the coupled construction takes to run is needed anywhere in Half 1 or in the fixed-question route. $\Gamma_A$ extends PA, represents computations, and is consistent.

---

## 2. The factoring — the organizing fact of this page

Every version of the result is the composition of two independent claims.

> **Half 1 — the quote is honest about the future human.** On any gate $A$ itself can recognize, $A$'s quotes are unbiased for the realized $Y_n$.
>
> **Half 2 — the future human speaks for the present human.** Get from $Y_n$ back to $\mathbb E^H_n(X_n)$.

**Half 1 is free, and it is free unconditionally.** Half 2 is where all the difficulty lives — and, importantly, **where every visibility assumption in the corpus lives.** Recognizing this is what separates the genuinely general part of the result from the part that has been paying for a modelling convenience. See [[delay-and-visibility]] for the axes.

---

## 3. Half 1: the quote is honest

**Statement.** For every rational $t$ and $\delta>0$, put $u_n := \operatorname{Ind}_\delta(a_n > t)$. Then $u$ is a $\overline{\mathbb P}^A$-generable weighting, and if it is divergent, the $u$-weighted average of $a_n - Y_n$ has $0$ as a limit point. Equivalently: *on the days $A$ advertises above $t$, the human's realized future credence averages at least $t - o(1)$ along a subsequence.*

**Proof.** Recurring Unbiasedness (4.8.15, in the corrected clause-free form — [[li-paper-erratum]] §1) applied to $\overline{\ulcorner Y\urcorner}$ with weighting $u$. $\square$

**Why this needs nothing.** The gate is a ramp on $A$'s *own quote*. The quote is a rational combination of $A$'s own day-$n$ prices, so it is an expressible feature of rank $n$ writable in poly-time; and Definition 4.3.2's closing remark explicitly blesses ramps of expressible features as expressible $[0,1]$-features. So $u$ is generable **from $A$'s market alone**:

- no visibility of $H$ in either direction;
- no shared fixed point / joint clearing;
- no assumption about delay, freezes, or clearing order;
- no relativization obligation on appendix D.2 (the weighting lives in a single market's class, which is what 4.8.15 is stated for);
- no computability bound on the coupled construction.

**A market is never stale to itself.** That sentence is the whole content of Half 1, and it is why the delay literature was looking in the wrong place.

**Status: PROVED (prose), and its engine is KERNEL-CHECKED.** `Staleness.not_limitPointZero_of_one_signed` and `Staleness.wavg_eventually_ge_half` (`lean-deference/Staleness.lean`, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`): no nonnegative divergent weighting can carry persistently one-signed, bounded-away-from-zero error without contradicting the limit-point conclusion. Deliberately proved against the **weak** form (0 is a *limit point*, not a limit), since reading 4.8.15 as a limit is a slip this project has made before. The genuine content is that the *initial segment* of the weighted sum is unconstrained and gets washed out by the divergence of the accumulated weight — that is the step formalized. Non-vacuity guarded non-degenerately (`engine_hypotheses_satisfiable`, with an adverse initial segment). Per the Lean honesty caveat: what is **not** checked is that any particular weighting is in any particular generable class — the market is unmodeled.

---

## 4. Half 2: three routes, and what each costs

| route | Half 2 via | visibility needed | question | status |
|---|---|---|---|---|
| **v3** | human-side trader: buy $X_n$ at $H$'s low price on a flagged day, unwind at $f(n)$ at $H$'s own then-current price | gate reads the same-day **pair**, so **$A$ must read $H$'s day-$n$ price** ⟹ shared fixed point | varying | CONJECTURED (~0.85) |
| **convergence** | $\mathbb E^H_n(X)\to p_\infty$, so $Y_n\to p_\infty$ and the human-side factor collapses into a *constant* threshold | **none, in either direction** | fixed $X$ only | PROVED modulo named hypotheses (~0.90) |
| **`cee`** | the human's **own** self-calibration about its own future | $H$ reads $A$'s posted quote — **one-way only** | varying | CONJECTURED (~0.6), one named gap |

### 4.1 The v3 route (varying questions, shared fixed point)

The trader's payoff is **realized cash**, not an unbiasedness average: it buys at $\mathbb E^H_{d_k}(X)$ and sells at day $f(d_k)$ at $\mathbb E^H_{f(d_k)}(X) = Y_{d_k}$, which is *definitionally* the quantity $A$ forecast. That observation (FA-chat msg 39) is what retired the feedback theorem and the erratum from the load-bearing path.

- **Theorem 1 (scheduled).** On every e.c. window-disjoint schedule $d_{k+1}\ge 2^{d_k}$, $\sum_k w_{d_k} < \infty$. Window-disjointness is a *round-trip* condition, not mere sparsity: geometric sets $\{2^k\}$ have overlapping windows $[2^k, 2^{2^k}]$ and do **not** qualify (msg 41's own self-correction).
- **Theorem 2 (adaptive).** $w_n \to 0$ over all days, via a one-position adaptive trader that chases violations at each threshold level. Corollary 2: per-day dominance $\liminf_n(\mathbb E^H_n(X_n) - a_n)\ge 0$. Corollary 3: $\sum_n w_n<\infty$ over all days. Conditional on two flagged obligations — expressibility of the softened state machine in the feature algebra (~0.85), and the relativization of appendix D.2's proof to the joint class (~0.85), which Theorem 2 leans on harder because its firing weighting is itself price-responsive. Overall ~0.75.

**The cost, stated plainly.** The gate $w_n$ reads the same-day pair, so $A$'s traders must see $H$'s day-$n$ price. v3 buys this with **joint clearing** (A1): both markets clear together as one fixed point. v3 is explicit that this is a genuine hypothesis rather than bookkeeping, *and* that the joint construction's existence is **assumed, not cited** — "it has the same shape as the paper's §5 and I see no obstruction, but it is an assumption, not a citation." See [[joint-clearing-and-trader-class]].

### 4.2 The convergence route (fixed question, no visibility at all)

**Theorem A.** Let $X$ be a fixed $[0,1]$-LUV of $H$'s language, and let $A$ be delayed arbitrarily — any freeze schedule, including *never receiving $H$'s data at all*. Assume only the standing assumptions of §1. Then for every $c>0$ there are only finitely many days $n$ with
$$\mathbb E^A_n(\ulcorner \mathbb E^H_{f(n)}(X)\urcorner) \;\ge\; \mathbb E^H_n(X) + c.$$

**Proof.** By **Expectations Converge (4.8.3)**, $\mathbb E^H_n(X)\to p_\infty$; hence the determined values $Y_n = \mathbb E^H_{f(n)}(X)\to p_\infty$ as a subsequence of a convergent sequence. Suppose the displayed inequality holds infinitely often; then $a_n \ge p_\infty + c - o(1)$ infinitely often. Choose a rational $q\in(p_\infty+\tfrac c4,\,p_\infty+\tfrac c2)$ and set $\delta := \tfrac c8$. The weighting $u_n := \operatorname{Ind}_\delta(a_n > q)$ is generable from $A$'s own prices (§3), and divergent, since $q+\delta < p_\infty + \tfrac{5c}8 < p_\infty + c$ so infinitely many days carry weight $1$. On its support the quote exceeds $q$ while $Y_n\to p_\infty < q - \tfrac c4$, so the forecast error is eventually $\ge\tfrac c4$: one-signed and bounded away from zero. By Half 1's engine, $0$ is then not a limit point of the $u$-weighted average error — contradicting 4.8.15. $\blacksquare$

**Why this is the result to lead with.** It **strictly subsumes v3's Corollary 2 under weaker hypotheses**: no joint clearing, no human-side trader, no adaptive-trader obligations, no relativization obligation. For a fixed question, none of v3's machinery is needed. An independent adversarial pass (2026-07-29) checked every step — the weighting's legality, the divergence, the one-signedness, and the limit-vs-limit-point structure — and rated it **~0.90**, higher than any other statement in the FA corpus.

**Three citation repairs against its source** (`fa-block-staleness-impossibility.md` §2, which states this as its Theorem A): it cites "the paper's convergence theorem", but 4.1.1 is about *sentences* — the needed theorem is **4.8.3, Expectations Converge**, which does cover a $[0,1]$-LUV; it writes $\mathbb P^H_n(X)$ where it means $\mathbb E^H_n(X)$; and "suppose only that the targets are determined via $\Gamma_A$" omits that they must also lie in $\mathcal{BLCS}$ (v3 states this as (A2)). All three are cosmetic and the conclusion is unaffected.

**Named hypotheses:** 4.8.3; 4.8.15 corrected; $\mathcal{BLCS}$ membership and $\Gamma_A$-determinacy of the target template. **Status: PROVED modulo named hypotheses (~0.90)**, engine KERNEL-CHECKED, Theorem-A-specific assembly not yet in Lean.

**Extension (CONJECTURED, ~0.6).** The proof never uses fixedness *per se* — it uses that the human-side gate factor is eventually $A$-predictable, and gets that from convergence. So it should extend to a **varying** $X_k$ whose credences converge to a profile $A$ can eventually predict; the cleanest version assumes $\mathbb E^H_n(X_{k(n)})\to p_\infty$ for a single limit across blocks, and then runs verbatim. That makes the dividing line **surprise, not variation** — sharper than "novelty", and it is the natural next write-up.

### 4.3 The `cee` route (varying questions, one-way visibility)

*New, 2026-07-29; the reason this page exists rather than a pointer to v3. Unvetted.*

1. **`cee` (4.12.1)** is free and quantified over e.c. sequences of $[0,1]$-LUVs, so **varying questions are fine**: $\mathbb E^H_n(X_n) \eqsim_n \mathbb E^H_n(\ulcorner Y_n\urcorner)$. The present human's credence *is* its current expectation of its own future credence.
2. So deference reduces to comparing $\mathbb E^H_n(\ulcorner Y_n\urcorner)$ with $\mathbb E^A_n(\ulcorner Y_n\urcorner)$ — **two expectations of the same determined object**, which is a much better-behaved comparison than one between a present credence and a future one.
3. Apply 4.8.15 **to $H$** on the same gate: $H$'s expectations of $Y_n$ are unbiased for $Y_n$ along any $\mathcal C_H$-generable divergent weighting. ⚠ **Corrected 2026-07-29:** the gate must be $\tilde u_n := \operatorname{Ind}_\delta\big(\mathbb P^H_n(\ulcorner a_n > t\urcorner) > \tfrac12\big)$ — a ramp on **$H$'s own price of the sentence about the quote** — not on the quote itself. Saying $H$ "may read $A$'s posted quote as settled data" conflates *trader* legality (hard dependence on settled data: fine) with *weighting generability* (expressible features of the market's **own** prices: Definition 4.3.5, and $A$'s quote is not one, nor is it e.c.). The ledger device repairs it — once the quote atom is decided in $D_H$, Provability Induction drives $\mathbb P^H_n$ of it to its truth value, so $\tilde u$ agrees with $u$ up to finitely many days and a vanishing error. Details and the general trap: [[unbiasedness-theorem-families]] §6.
4. Both sides' errors are then against the *same* target on the *same* gate, so the $u$-weighted averages of $a_n$ and of $\mathbb E^H_n(X_n)$ agree.

**What this buys.** It never asks $A$ to see $H$. The only channel used is $H$ reading $A$'s published forecast — which is what publishing a forecast *means*. And one-way visibility is structurally cheap: continuity is required only in a trader's *own* prices, because those are the fixed-point variables of its own market's clearing; a cross-market stream already settled at read time may be depended on arbitrarily (msg 39, correcting v3's "jointly continuous in the pair" as an overstatement). So **sequential clearing suffices — no joint Brouwer argument, and hence none of A1's assumed existence.** See [[delay-and-visibility]].

**The gap, stated plainly.** Step 4 combines **two limit-point statements**, and 4.8.15 delivers each on *its own* subsequence; nothing yet puts them on a common one. Two ways out:

- **Sparse schedules.** Use Unbiasedness From Feedback (4.8.16 — the theorem that genuinely carries the support clause, per [[li-paper-erratum]] §1) to get full limits $\eqsim_n 0$ on both sides, which do combine. Cost: the support must sit in the image of a deferral $f$ with $Y_n$ computable by the next firing — tower-ish spacing, exactly what v3 was pleased to have removed. **A real trade: shared fixed point for schedule sparsity.**
- **A single application.** Find one object whose unbiasedness yields both halves at once. Not available; the thing most worth trying. Tracked at [[open-problems]].
- **Move steps off 4.8.15 onto full-limit theorems.** `ccee` (4.12.3) is natively *gated* and a **full limit**, so applying it at the quote gate removes one of the two limit points outright — the cheapest available improvement (~0.8). See [[unbiasedness-theorem-families]] §4.1, which also sorts every other calibration-like theorem by which half it can serve.

This is the same "keep the averages on common weightings" bookkeeping that FA-chat msg 43 flagged for [[anticipated-deference]] (~0.7). **Status: CONJECTURED (~0.6).**

---

## 5. What is forced, and what is not

**Honest strength.** What the positive result delivers is the **averaged, one-sided, per-question** form: a sparse, gate-weighted family of Total-Trust instances on specific bets. Specifically:

- **one-sided** — nothing stops the human's credence from *exceeding* the quote;
- **per-$X$** — the finite counts depend on $X$ and on the margins, with no uniformity claimed;
- **rate-free** — no bound on when the finitely many violations stop (and per [[open-problems]], Garrabrant–Soares–Taylor 2016 on unbounded delays suggests feeble rates are intrinsic here, not an artifact);
- **not gap-closed** — the forced family is nowhere near closed under the gap construction, so it does **not** collapse to the tower, and it is **not** deck-TT (which is quantified over *all* e.d. LUV sequences and the full threshold family). Consequences: [[total-trust-implies-mart]], [[value-iff-mart]], and the amplifier stays live on this domain ([[amplifier-counterexample]]).

**Not established.** That $B_n := \mathbb E^A_n(\ulcorner\mathbb E^H_{f(n)}(\cdot)\urcorner)$ is *itself a logical inductor* — the other half of Eisenstat's merge conjecture — is untouched here and remains discharged in zero cases (deference-v6 §8, D3). `faithful-acceleration.md` L213 is right that the trust result does not need it; it would be a bonus, not a lemma.

**The self-referential family is not a domain restriction.** On the quote-referencing diagonal the theorem holds *vacuously* — the quote is pinned and the gate is degenerate — so the diagonal is a degenerate stratum, not an exclusion. [[fa-scope-resolution]].

---

## 6. What to say about Eisenstat's conjecture

*(About the corpus construal — not Sam's intended version; [[eisenstat-conjecture-attribution]].)*

Three sentences, in the order that survives scrutiny:

1. **On a fixed question, the accelerator works under arbitrary delay, with no visibility in either direction and no shared fixed point** — only finitely many days on which the human lags the advertisement by any fixed margin (§4.2).
2. **On varying questions, what the accelerator needs is a publication channel, not a shared fixed point** — the human must be able to read the AI's forecast (§4.3). Whether that suffices outright, or costs a sparse schedule, is open.
3. **The shared fixed point was an artifact of the gate, not of the phenomenon.** v3 gated on the same-day *pair*; gate on the quote alone — plus the human's own price, which the human can always read — and the symmetric assumption disappears.

And the caveat that must travel with all three: what is forced is the averaged family of §5, not the tower and not deck-TT.

**Historical note.** The restriction to shared clearing was, for a while, going to be justified by a matching impossibility for the non-shared case. That impossibility is **refuted** — see [[delay-and-visibility]] §3. So there is no longer a reason to present the shared-fixed-point version as the headline.

## Related

- [[delay-and-visibility]] — the axes, Theorem A's home, and the refuted impossibility
- [[joint-clearing-and-trader-class]] — what A1 costs and why one-way is cheap
- [[li-paper-erratum]] — the corrected 4.8.15 this page runs on
- [[anticipated-deference]] — the same common-weighting bookkeeping, for future quotes
- [[open-problems]] — the common-subsequence gap; the rate question
- [[deference-notions]], [[setting-and-notation]] — definitions and the two settings
