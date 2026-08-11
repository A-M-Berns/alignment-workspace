# The sparse-schedule route to varying-question trust

*Trading schedule sparsity for the shared fixed point. The result is an averaged **quote–credence agreement** for varying questions under **one-way** visibility: along an evaluation-sparse schedule, a weighted average of the difference between the AI's current expectation of the human's future expectation, $\mathbb E^A_n\big(\ulcorner\mathbb E^H_{f(n)}(X_n)\urcorner\big)$, and the human's current expectation, $\mathbb E^H_n(X_n)$, tends to zero — two-sided, a full limit. Equivalent via the ledger collapse to an averaged Tower (whose inner expectation is degenerate for a readable expert — §8.2, corrected 2026-07-31), with both one-sided inequalities of soft Total Trust as corollaries. Assembled from the corrected Theorem 4.8.16 applied to **both** markets plus `cee` 4.12.1 applied to the human. This is [[faithful-acceleration-result]] §4.3's first "way out" made rigorous — and it turns out to cost **two** things, not one: sparsity **and** a class-relativization that the corpus's existing ledger-device repair ("ledger gate" in the wiki's vocabulary) does not actually supply.*

*Written 2026-07-30; the feedback ladder in §1, the decision-time remark in §3, and the sharpened skeptic item 2 added 2026-07-31 after Abram's objection that 4.8.16's feedback condition is itself a form of access to $H$ — it is, and the file now says which form. **The presentation-canonical restatement is at [[theorem-ss-streamlined]]** — Tower-form packaging via a readability-collapse lemma, the human-side bridge by citations (`cee` + 4.8.16@H, per Abram's preference), and a hypothesis-thinning remark showing (S2)/(R) are removable by a Kelly round-trip trader; this file remains the record of the original assembly and of the schedule construction, legality analyses, and trade-off discussions the canonical page cites. Setting: two logical inductors, one-way sequential clearing. All theorem numbers checked against `references/logical-induction/main.tex`; corrected forms per [[li-paper-erratum]]. Conventions: [[conventions-and-status-labels]].*

---

## 0. Executive summary

| | |
|---|---|
| **What is proved** | For every e.d. sequence $(X_n)$ of $[0,1]$-LUVs, every rational $t$ and $\delta>0$: along one fixed evaluation-sparse schedule $\operatorname{im}(g)$ (§3), the weighted average — weights $w_n$ the quote weighting of §1 — of the difference $\mathbb E^A_n\big(\ulcorner\mathbb E^H_{f(n)}(X_n)\urcorner\big)-\mathbb E^H_n(X_n)$ tends to $0$: a **full limit**, **two-sided**. The literal shape is expert-estimate vs. novice-credence ($\mathbb E^A\mathbb E^H_f$ vs $\mathbb E^H$ — **not** the Tower's $\mathbb E^H\mathbb E^A$ vs $\mathbb E^H$); via the ledger collapse it is equivalent to a scheduled weighted-average Tower (§8.2), and both one-sided inequalities of scheduled soft Total Trust follow as corollaries. |
| **What it costs** | (i) an evaluation-sparse schedule $g$ (this is the advertised trade); (ii) **ledger legibility** (L) — the quote must be inside $\mathcal C_H$, not merely "settled data for traders"; (iii) mirror determinacy (M) on $\Gamma_H$. It does **not** cost joint clearing, a joint Brouwer construction, window-disjointness, or any $A$-side visibility of $H$. |
| **What it does not give** | The per-day form. That is exactly and only what joint clearing buys — see §8.3. |
| **Correction produced en route** | [[unbiasedness-theorem-families]] §6's ledger-weighting repair, as stated, **does not go through**: its appeal to Provability Induction 4.2.1 requires selecting the true ledger atom, which is precisely the poly-time-hard step. §5.3 localizes the failure and repairs it. |
| **Verdict** | **PROVED modulo named hypotheses (≈0.82)**. |

---

## 1. Setting, fixed once

**The two markets.** $H\dashv\mathcal C_H$ is a logical inductor over a $\Gamma_H$-complete computable deductive process $D_H$; $A\dashv\mathcal C_A$ likewise over $D_A$, $\Gamma_A$. Canonically $\mathcal C_H=\mathrm P\subsetneq\mathcal C_A=\mathrm{EXP}$. Per this wiki's convention ([[setting-and-notation]] §Trader classes), "e.c." means computable in the reasoner's own class; the LI paper's theorems are read relative to that class throughout. Note that $\mathcal C_A\supseteq\mathrm P$ means **every** paper theorem applies to $A$ verbatim with no relativization at all.

**One-way sequential clearing** (the hypothesis regime; *not* joint clearing). Each day $n$:

1. $A$'s market clears — an ordinary single-market clearing against $A$'s own day-$\le n$ prices. No fixed point over any other market's prices is taken.
2. $A$ publishes its day-$n$ forecast $a_n := \mathbb E^A_n\big(\ulcorner\mathbb E^H_{f(n)}(X_n)\urcorner\big)$ — its current expectation of the human's future expectation; see Objects below — into $D_H$ as decided ledger atoms $\big(\ulcorner\alpha_n>i/n\urcorner\big)_{i<n}$ (or exact-value atoms), decided to the published value.
3. $H$'s market clears, with those atoms available in $D_H^{\,n}$.

$A$'s **clearing** never conditions on $H$'s prices — no feature of $A$'s market reads them, at any day. Consequently the coupled system is a **two-stage composition**, not a fixed point: build $A$ standalone (paper §5), extract the ledger $L:=(a_n)_n$, then build $H^+$ with $L$ in its deductive process. This is the structural payoff of one-way visibility ([[joint-clearing-and-trader-class]] §3, FA-chat msg 39) and it is why nothing here needs v3's assumed joint Brouwer argument.

**What "one-way" does *not* mean — the feedback ladder (correction 2026-07-31, after Abram's objection).** It does not mean $A$ needs no access to $H$. Three points, then the ladder.

- **An in-class $H$-simulator alone exerts no pressure on $A$'s prices.** Exploitation (Def. 3.5.1) is assessed against plausible worlds $\mathrm{PC}(D_A^{\,n})$: until $D_A$ decides the value-atoms of $\ulcorner Y_n\urcorner$, there are plausible worlds in which every one of the simulator's bets loses, so its plausible worth is not bounded below and the criterion permits the market to ignore it. A trader must be **vindicated by empirics** — by decisions of $A$'s own deductive process — before it moves anything.
- **The feedback channel lives in the standing hypotheses.** Determinacy via $\Gamma_A$ **plus** $\Gamma_A$-completeness of $D_A$ jointly say: the outcome of the human's deliberation is eventually decided inside $A$'s world. Without them nothing constrains the quote — not this route, and not Half 1 either. The model renders this as self-derivation ($H$ is a closed computable program, so "proving what $H$ output" and "observing $H$" coincide); any deployment reading of determinacy-plus-completeness *is* an observation channel.
- **What distinguishes the routes is feedback *promptness*, not feedback vs. none:**

| feedback $A$ gets about $H$ | mechanism | results | conclusion grade |
|---|---|---|---|
| eventual, **no rate** | settlement whenever it arrives (4.8.15; the 4.8.12 envelope squeeze) | Half 1, Lemma P, Theorem A | averaged limit point; pointwise only on convergent handles |
| **schedule-prompt computability** — each forecast's outcome *computable* in-class before the next scheduled bet; settlement in $D_A$ arrives eventually, at any rate | round-trip trader cashing the market's own price movement, truth forced into the day-$f(j{+}1)$ price by rate-free Provability Induction (4.8.16; §3's mechanism remark) | **this route** | scheduled quote–credence agreement, full limit |
| **live** — $A$'s features read $H$'s current prices | joint clearing | v3 | per-day |

The evaluation-sparse schedule is exactly the **feedback-computability latency** — the gap must cover *computing* the outcome, never its settlement — and Half 1's limit-point weakness is the price of dropping even that: with no in-class handle on the outcome, honesty can only be forced to recur, not to converge. (Rung-2 wording corrected 2026-07-31 after Abram's follow-up: an earlier revision said "settled in $A$'s world before the next bet", which is *not* a hypothesis of 4.8.16 — see §3's mechanism remark.)

**Objects.**

- $(X_n)$ — an **e.d.** sequence of $[0,1]$-LUVs of $H$'s language: the *formulas* are produced in time $\mathrm{poly}(n)$; the *values* may be uncomputable ([[setting-and-notation]] §LUV; "e.d." is this wiki's coinage, not the paper's — [[li-paper-erratum]] §"Not an erratum").
- $f$ — an e.c. strictly increasing lookahead, $f(n)>n$; canonically $f(n)=2^n$. $f$ is a **deferral function** in the sense of Def. 4.3.7 (`main.tex:1240`): $f(n)>n$ ✓, and $f(n)$ is computable in time polynomial in $f(n)$ ✓ (writing $2^n$ costs $O(n)$, and $n\le 2^n$).
- $Y_n:=\mathbb E^H_{f(n)}(X_n)$ — the human's future credence, the forecast target.
- $\ulcorner Y_n\urcorner$ — throughout, the **program-encoded** LUV $\ulcorner\underline{\mathbb E}^{H}_{\underline f(\underline n)}(\underline{X_n})\urcorner$, not the numeral-encoded $\underline{\mathbb E}^H_{\underline{f(n)}}$. This matters for size: the numeral for $2^n$ is exponentially long, so only the program encoding keeps $\overline{\ulcorner Y\urcorner}$ e.d. The paper makes exactly this move inside `cee`'s own proof (`main.tex` app:cee, "We now manipulate the encodings $\underline{f(n)}$ and $\underline f(\underline n)$"), bridging the two with `expprovind`.
- $a_n:=\mathbb E^A_n(\ulcorner Y_n\urcorner)\in\mathbb Q\cap[0,1]$ — the quote. The lookahead expert is $E^\ast(X_n):=a_n$.
- $\alpha_n$ — the $[0,1]$-LUV **of $H$'s language** naming the quote, $\alpha_n:=\ulcorner\underline{\mathbb E}^A_{\underline n}(\ulcorner\underline{\mathbb E}^H_{\underline f(\underline n)}(\underline{X_n})\urcorner)\urcorner$. e.d. ✓ (fixed template + numeral $n$).
- $u_n:=\operatorname{Ind}_\delta(a_n>t)$, $u^-_n:=\operatorname{Ind}_\delta(a_n<t)$ — the quote weightings, $\operatorname{Ind}_\delta$ being the LI paper's continuous threshold indicator, **Definition 4.3.2** (`main.tex:1174`).

**Weighted averages, and terminology.** For a weighting $\overline w$ (a sequence $w_n\in[0,1]$) and a sequence $\overline x$, the **$w$-weighted average** at day $n$ is $\bar x^{\,w}_n := \sum_{i\le n} w_i x_i \big/ \sum_{i\le n} w_i$; the **Cesàro average** is the special case $w\equiv1$. *Terminology note (2026-07-31, Abram):* earlier drafts called ramp-indicator weightings "weightings" and Total Trust's two one-sided inequalities "cuts"; renamed throughout this file to **weighting** and **above-/below-threshold inequality**. The deeper working notes ([[route-recurring-ccee]], [[route-transitivity]], [[route-negative-introspective]]) still carry the older vocabulary.

**Target notion** ([[deference-notions]] §Total Trust), unnormalized threshold form:

$$\mathbb E^H_n\big(X_n\cdot\operatorname{Ind}_\delta(a_n>t)\big)\;\gtrsim_n\;t\cdot\mathbb E^H_n\big(\operatorname{Ind}_\delta(a_n>t)\big),$$

plus the dual below-threshold inequality, for every e.d. $(X_n)$, rational $t$, rational $\delta>0$.

---

## 2. Named hypotheses

Everything beyond the LI paper is here. Nothing below is used without appearing in this list.

**(S1) BLCS + $\Gamma_A$-determinacy of the target (standing).** $\overline{\ulcorner Y\urcorner}$ is an e.c. sequence of expressions of $A$'s language, bounded by $1$, hence $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^A)$ (Def. 4.8.9, `main.tex:1749`); and it is **determined via $\Gamma_A$** (Def. 4.8.14, `main.tex:1806`) with $\operatorname{Val}_{\Gamma_A}(\ulcorner Y_n\urcorner)=Y_n$. $\Gamma_A$ extends PA, represents computations, is consistent.

**(S2) Mirror: $\Gamma_H$-determinacy (the extra assumption the A-side standing assumption does not give).** $\Gamma_H$ extends PA, represents computations, is consistent, and $\mathcal L_H$ contains predicates representing the **coupled** construction (both markets and the ledger). Consequently $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^H)$ is determined via $\Gamma_H$ with $\operatorname{Val}_{\Gamma_H}(\ulcorner Y_n\urcorner)=Y_n$, and likewise $\overline\alpha$ is determined via $\Gamma_H$ with $\operatorname{Val}_{\Gamma_H}(\alpha_n)=a_n$.

*Remark (why this is mild, and why it is still an assumption).* Given that the coupled system is computable, $\Sigma_1$-completeness gives $\Gamma_H\vdash\ulcorner Y_n\urcorner=\underline{v_n}$ for the true value $v_n$, hence every $\mathbb W\in\mathrm{PC}(\Gamma_H)$ assigns $v_n$ — determinacy is *automatic* once the language and representability are granted. So (S2) is really a language assumption, and $\Gamma_H=\mathrm{PA}$ suffices: **the ledger is an acceleration of $D_H$, not an extension of $\Gamma_H$**, so consistency of $D_H$ with $\Gamma_H$ is free. It is nonetheless a genuine extra assumption over (S1) — the corpus flags exactly this at [[delay-and-visibility]] §4, "a new assumption that must be stated and not smuggled."

**(L) Ledger legibility / $H^+$.** $H$'s trader class is $\mathcal C_H=\mathrm P^{L}$: polynomial time with oracle (equivalently advice) access to the published quote sequence $L=(a_n)_n$, an $O(n)$ lookup for $a_n$. $H$ satisfies the logical induction criterion (`main.tex:657`, restated at 921; Exploitation is Def. 3.5.1 at 901) against $\mathrm P^L$. "e.c." on the $H$-side is read relative to $\mathrm P^L$ throughout.

*This is the assumption the route actually turns on, and §5.3 shows it cannot be avoided.* It is the precise formalization of $H^+$ ([[setting-and-notation]] §"Observable — the thin channel"). It preserves produce-hard / read-cheap: without the oracle $H$ still cannot compute $a_n$; with it, $H$ still cannot compute $Y_n$, so the complexity gap that makes $A$ *useful* is untouched. $\mathrm P^L$ is c.e. and closed under polynomial overhead, so it is a legal $\mathcal C_H$ by this wiki's own standing convention.

**(R) Relativization of the two theorems actually applied to $H$.** Theorem 4.8.16 (corrected) holds for $H$ against $\mathrm P^L$-generable weightings, i.e. its proof (E.12 $\to$ D.4) relativizes.

*Justification sketch, and why this obligation is much lighter than v3's.* D.4 builds one trader $T_n:=\hat\beta_i\cdot(\hat A_{f(i)}-A^{\overline{\mathbb P}\ast n}_{f(i)})-\cdots$ with $\hat\beta_i=\varepsilon\cdot\widehat{\mathrm{Wealth}}_i\cdot\hat w_i$, and separately invokes Affine Provability Induction on $\overline{A'}$. The **only** place the oracle is consulted is in writing the constants $\hat w_i$; everything else (the $\alpha$-operator of E.12, $\operatorname{Val}_\Gamma$ constants at index $f(j+1)$, the wealth recursion) is plain poly-time. Composition of poly-time$^L$ machines is poly-time$^L$, so $T$ is a $\mathrm P^L$ trader and (L) applies. Contrast v3's obligation, which asked D.2 to relativize to a *joint feature language over two markets*; here the feature language is unchanged and only the generator's clock gets an oracle. I rate (R) ≈0.92, against v3's ≈0.85 for the harder version.

*Note that (R) is needed for the $H$-side only.* The $A$-side weighting is a ramp on $A$'s own prices and $A$ is inexploitable by all of $\mathrm{EXP}\supseteq\mathrm P$, so 4.8.16 applies to $A$ **verbatim as printed** (corrected per the erratum). And `cee` on $H$ needs no relativization either — its inputs are e.d. without the oracle.

**(D) Divergence (a dichotomy, not an assumption).** Handled in both directions in §7.

**(E) Erratum.** 4.8.15 has **no** support clause and concludes a **limit point**; 4.8.16 carries the support clause and the timing condition and concludes a **full limit**. [[li-paper-erratum]] §1, certified by appendices E.11/E.12. *Only 4.8.16 is used below* — 4.8.15 never appears, so Trap 1 cannot bite.

---

## 3. Step 1 — the schedule exists

> **Lemma 1 (schedule existence).** There is a strictly increasing deferral function $g$ (Def. 4.3.7) such that for **every** $n$, $\operatorname{Val}(\ulcorner Y_n\urcorner)=Y_n$ is computable in time $O\big(g(n+1)\big)$; moreover $\mathbb 1[n\in\operatorname{im}(g)]$ is computable exactly in time $\mathrm{poly}(n)$.

*Proof.* The coupled system is computable (§1: $A$ standalone, then $H^+$ with the ledger, both computable). So there is a total computable $T_0:\mathbb N^+\to\mathbb N^+$ giving the running time of a fixed algorithm that outputs $Y_m=\mathbb E^H_{f(m)}(X_m)$. Put $T(m):=\max\{m,\;\max_{m'\le m}T_0(m')\}$ — total, computable, nondecreasing, $T(m)\ge m$.

Define $g(1):=2$ and $g(k+1):=\max\big(g(k)+1,\;T(g(k))\big)$.

*(a) $g$ is strictly increasing and $g(k)>k$.* Immediate from the $g(k)+1$ branch and $g(1)=2$; induction gives $g(k)\ge k+1$. ✓

*(b) Timing condition, in the literal all-$n$ reading.* $Y_n$ is computable in $T_0(n)\le T(n)$ steps. Since $T$ is nondecreasing and $g(n)\ge n$, $T(n)\le T(g(n))\le g(n+1)$. So $Y_n$ is computable in $O(g(n+1))$ for **every** $n$ — not merely on $\operatorname{im}(g)$. ✓

*This disposes of an indexing ambiguity in the paper.* 4.8.16 as printed says "$\operatorname{Val}_\Gamma(B_n)$ computable in time $O(f(n{+}1))$"; the propositional twin 4.3.8 says "$\operatorname{Thm}_\Gamma(\phi_{f(n)})$ computable in $O(f(n{+}1))$ time"; appendix D.4 uses only "$\operatorname{Val}(A_{f(j)})$ computable in time **polynomial in** $f(j{+}1)$" (needed to put $\overline{A'}$ in $\mathcal{BCS}$), and E.12 writes "polynomial in $g(n{+}1)$". The three readings differ (all-$n$ vs. on-$\operatorname{im}(f)$; linear vs. polynomial). Lemma 1 satisfies the **strongest** of them, so the route is insensitive to which is meant. Worth recording as a fourth item for [[li-paper-erratum]] (cosmetic, not a defect).

*(c) $g$ is a deferral function: $g(k)$ computable in time $\mathrm{poly}(g(k))$.* Unroll the recursion. Computing $T(g(j))$ means running the $Y$-algorithm and counting, costing $\Theta(T(g(j)))\le g(j+1)$ steps. Total cost $\sum_{j<k}O(g(j+1))=O(k\cdot g(k))=\mathrm{poly}(g(k))$, since $k<g(k)$. ✓

*(d) $\mathbb 1[n\in\operatorname{im}(g)]$ is computable exactly in $\mathrm{poly}(n)$.* Unroll $g(1),g(2),\dots$ but **truncate every sub-computation at $n$ steps**: when evaluating $T(g(j))$, if the $Y$-computation has not halted within $n$ steps then $T(g(j))>n$, hence $g(j+1)>n$, hence $n\notin\operatorname{im}(g)$ and we halt with $0$. Otherwise every value $g(1),\dots,g(j)$ we compute exactly is $\le n$, and each costs $\le\mathrm{poly}(n)$; there are at most $n$ of them. So the test is exact and costs $\mathrm{poly}(n)$. ✓ (This is the step where Trap 4 — value-vs-description — would bite a careless argument: we must never need the *value* of $g$ at an argument whose value exceeds $n$.)

$\square$

**Three remarks on Lemma 1.**

- **Trap 6 is paid, explicitly.** $T$ is the cost of the **coupled** system: running $A$ to day $f(n)$ (for the ledger), running $H^+$ to day $f(n)$, and $f(n)$ price lookups. Nothing here pretends that only $H$'s cost matters.
- **The mechanism remark: computation time is exactly right; decision time is NOT needed (corrected 2026-07-31, source-checked).** An earlier revision of this remark padded $T$ to cover $D_A$'s decision times; reading D.4 (`main.tex:4729–4835`) shows no decision-rate hypothesis is used anywhere. The exploiting trader never holds a bet to settlement: it **round-trips** — buys $A_{f(j)}$ at day $f(j)$, sells back at day $f(j{+}1)$ at the then-current price — so its profit is realized cash from the market's own price movement, and Kelly sizing ($\beta_j=\varepsilon\cdot\mathrm{Wealth}_j\cdot w_j$, one open position at a time, $\|A\|_1\le1$) bounds its worth below by $-1$ in every plausible world regardless of what $D$ has decided (`main.tex:4772–4773`). Truth enters exactly once: since $\operatorname{Val}(A_{f(j)})$ is computable in time poly$(f(j{+}1))$, the auxiliary sequence $A'_{f(j+1)}:=A_{f(j)}-\operatorname{Val}(A_{f(j)})$ is a legal BCS sequence (`main.tex:4820` — the **only** consumption of the timing condition), it is provably zero in every $\Gamma$-consistent world, and **rate-free** Affine Provability Induction forces $\mathbb P_{f(j+1)}(A_{f(j)})\eqsim_j\operatorname{Val}(A_{f(j)})$: the market's own later price is the settlement instrument. So the hypotheses are exactly (Abram's reading, confirmed): the feedback must *eventually* arrive ($\Gamma$-decidability, consumed only inside PI, no rate), and must be *computable* schedule-promptly (so the PI instance may mention it). Lemma 1 as originally stated is exactly what is needed.
- **Window-disjointness comes free and is not needed.** Computing $Y_{g(k)}$ requires reaching day $f(g(k))$, so $T(g(k))\ge f(g(k))$, so $g(k+1)>f(g(k))$: the round trip opened at $g(k)$ closes before $g(k{+}1)$. But 4.8.16's hypotheses are only *support $\subseteq\operatorname{im}(g)$* and *timing*; window-disjointness was a condition of v3's **trader** argument, not of this one (Trap 5, checked: not needed, and satisfied anyway).
- **No circularity, twice over.** (i) $g$ is defined by reference to $H^+$, and $H$'s traders use $g$ — but the logical induction criterion quantifies over *all* traders in a class fixed independently of $g$, applied to a market already fixed. There is nothing to unwind. (ii) The day-$n$ computation of $\mathbb 1[n\in\operatorname{im}(g)]$ simulates the coupled system for at most $\mathrm{poly}(n)$ steps and, by (d), never needs a value it cannot afford.
- **How sparse is sparse — and does it have to be iterated exponentiation? (No.)** Call a schedule $\{n_1<n_2<\cdots\}$ **$h$-sparse** (for increasing $h$) if $n_{k+1}\ge h(n_k)$. What the proof needs is exactly that $g$ be $T$-sparse for **some computable $T$ bounding the time to evaluate the forecast target** $Y_n$ — i.e. to run the coupled construction out to day $f(n)$ — and Lemma 1 builds $g$ from any such $T$. Call this **evaluation-sparse**: sparse relative to the cost of computing the very quantity being forecast. Since merely reaching day $f(n)$ costs $\ge f(n)$ steps, $T\ge f$, so for $f(n)=2^n$ the growth is at least iterated-exponential: $g(k+1)\ge T(g(k))\ge f(g(k))=2^{g(k)}$. But the exponential form is incidental — a polynomial lookahead would give iterated-$T$ growth for whatever $T$ bounds the construction's runtime (which dominates in any case). This *is* the price being paid, stated honestly. *(Earlier drafts said "evaluation-sparse"; renamed to avoid collision with the Tower deference principle of [[deference-notions]].)*

**Uniformity of $g$ (better than one might expect).** $g$ depends on $f$, on the coupled system, and on the cost of evaluating $X_m$'s formula — i.e. on a polynomial bounding $|X_m|$. It does **not** depend on $t$ or $\delta$ at all, and it is uniform across all e.d. sequences whose descriptions obey a fixed size polynomial. So one schedule serves the whole threshold family simultaneously, which is what §8 needs.

---

## 4. Step 2 — the $A$-side: 4.8.16 on $\overline{\ulcorner Y\urcorner}$

Put $s_n:=\mathbb 1[n\in\operatorname{im}(g)]$ and

$$w_n:=u_n\cdot s_n=\operatorname{Ind}_\delta(a_n>t)\cdot\mathbb 1[n\in\operatorname{im}(g)]\in[0,1].$$

**4.1 $\overline w$ is $\overline{\mathbb P}^A$-generable (Def. 4.3.5, `main.tex:1218`).** Def. 4.3.5 asks for an e.c. $\mathcal E$-progression $\overline{\hat w}$ with $\hat w_n(\overline{\mathbb P}^A)=w_n$.

- By Def. 4.8.2 (`main.tex:1671`), $\mathbb E_n(B)=\sum_{i=0}^{n-1}\frac1n\,\mathbb P_n(\ulcorner B>i/n\urcorner)$. Hence $a_n=\hat a_n(\overline{\mathbb P}^A)$ for the expressible feature
  $$\hat a_n:=\sum_{i=0}^{n-1}\tfrac1n\cdot\big(\ulcorner \ulcorner Y_n\urcorner>i/n\urcorner\big)^{\ast n}$$
  — a rational combination of $n$ **day-$n$ price features of $A$'s own market**, so $\hat a_n\in\mathcal E_n$, and writable in $\mathrm{poly}(n)$ because each sentence is a fixed template with the numerals $n,i$ and the *program* encoding of $f$ (§1).
- $\operatorname{Ind}_\delta(\hat a_n>t)=1-\max\big(0,\,1-\max(0,(\hat a_n-t)/\delta)\big)$ is built from $\hat a_n$, rationals, $+,\times,\max$ — an expressible $[0,1]$-feature of rank $n$. Def. 4.3.2's closing remark blesses exactly this ("we can generalize this definition to the case where $x$ and $y$ are expressible features, in which case $\operatorname{Ind}_\delta(x>y)$ is an expressible $[0,1]$-feature").
- $s_n$ is a deterministic $0/1$ sequence computable exactly in $\mathrm{poly}(n)$ (Lemma 1(d)), so $\hat w_n:=s_n\cdot\operatorname{Ind}_\delta(\hat a_n>t)$ is an e.c. $\mathcal E$-progression. ✓

**No visibility is used *by the weighting*.** The weighting reads $A$'s own day-$n$ prices only — "a market is never stale to itself" ([[faithful-acceleration-result]] §3). No joint clearing, no relativization; the route's feedback about $H$ enters through 4.8.16's hypotheses (§1's ladder), never through the weighting.

**4.2 Apply the corrected 4.8.16.** Hypotheses, each checked for **$A$'s** market:

| hypothesis | status |
|---|---|
| $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^A)$ | (S1) |
| determined via $\Gamma_A$, $\operatorname{Val}_{\Gamma_A}=Y_n$ | (S1) |
| $g$ strictly increasing deferral function | Lemma 1(a,c) |
| $\operatorname{Val}_{\Gamma_A}(\ulcorner Y_n\urcorner)$ computable in $O(g(n{+}1))$ | Lemma 1(b) |
| $\overline w$ $\overline{\mathbb P}^A$-generable divergent weighting | §4.1 + case (a) of §7 |
| $\operatorname{supp}(\overline w)\subseteq\operatorname{im}(g)$ | by construction ✓ |

Conclusion (**full limit**, two-sided):

$$\boxed{\ \frac{\sum_{i\le n}w_i\,(a_i-Y_i)}{\sum_{i\le n}w_i}\;\eqsim_n\;0.\ }\tag{A}$$

---

## 5. Step 3 — the $H$-side: 4.8.16 again, and the weighting problem

**5.1 The weighting problem, stated exactly.** A **generable weighting** (Def. 4.3.5) must be an e.c. progression of **expressible features** (Def. 3.4.3, `main.tex:786`), and expressible features are built from *the market's own* price features, rationals, $+,\times,\max$, safe reciprocation. $A$'s quote is not a price feature of $H$'s market. This is Trap 2, and it is the trap this project already fell into once ([[unbiasedness-theorem-families]] §6). Trader legality is a different notion: a trader *may* depend hard/discontinuously on settled cross-market data (msg 39, [[joint-clearing-and-trader-class]] §3) — but that licenses nothing about weightings.

**5.2 Under (L), the weighting is legal directly — and the ledger device is unnecessary.** Def. 4.3.5's own commentary records that e.c. sequences of rationals are generable (as constant features), the generable class being *strictly larger*. Under (L), $n\mapsto a_n$ is an $O(n)$ oracle lookup, so $\overline u$ is an e.c.$^{L}$ sequence of rationals, so $\overline w=\overline u\cdot\overline s$ is $\overline{\mathbb P}^H$-generable via the constant-feature progression $\hat w_n:=w_n$. ✓ **Same numbers as on the $A$-side** — this is essential: (A) and (H) below must be averages against one and the same real sequence $\overline w$, and they are, because $\hat w$ is a *feature of $A$'s prices* on one side and a *hard-coded constant* on the other, both evaluating to $w_n$.

**5.3 ⚠ Correction: the corpus's existing ledger-weighting repair does not go through.**

[[unbiasedness-theorem-families]] §6 and [[faithful-acceleration-result]] §4.3 repair the weighting by using $\tilde u_n:=\operatorname{Ind}_\delta\big(\mathbb P^H_n(\ulcorner a_n>t\urcorner)>\tfrac12\big)$ — an expressible feature of $H$'s own prices ✓ — and then claim: "once the atom is decided, Provability Induction (4.2.1) on the e.c. sequence $\ulcorner a_n>t\urcorner$ drives $\mathbb P^H_n$ of it to its truth value, so $\tilde u$ agrees with $u$ up to finitely many days and a vanishing error."

**That step is invalid.** Provability Induction (4.2.1, `main.tex:1052`) requires *an e.c. sequence of theorems* (or of disprovable sentences). The sequence $\psi_n:=\ulcorner\alpha_n>t\urcorner$ is an e.c. sequence of **sentences**, but it is a *mixed* sequence: some $\psi_n$ are theorems, some are refuted. To feed 4.2.1 one must hand it either the sub-sequence of theorems or the sub-sequence of refuted sentences, and **selecting either is exactly deciding $\mathbb 1[a_n>t]$ in $\mathrm{poly}(n)$ time.** Unrelativized, that is precisely what the thin channel says $H$ cannot do. This is Trap 4 in its most consequential form, and [[delay-and-visibility]] §3 already diagnosed the identical move as illegal in the impossibility construction ("the obvious fallback also fails … selecting the refuted blocks to feed it is exactly computing $\sigma$"). The repair to Trap 2 fell into Trap 4.

**No other paper theorem supplies the missing step.** Deductive processes are only *computable* (Def. 3.2.1, `main.tex:714`), not efficiently computable, so "decided in $D_H^{\,n}$" carries no poly-time handle. Limit Coherence 4.1.1 gives the truth value only at $\mathbb P_\infty$, for a fixed sentence. 4.8.15/4.8.16 applied to $\mathbb 1(\psi_n)$ give *weighted-average* unbiasedness about the atoms, never pointwise agreement — and pointwise is what $\tilde u\approx u$ needs. Indeed pointwise agreement is **false in general**: if $D_H^{\,n}$ decides a sequence of facts no e.c. trader can select on, no trader profits from mispricing them, and the market may sit at $\tfrac12$ forever.

**Repair.** Assume (L). Then $\overline u$ itself is generable (§5.2) and $\tilde u$ is not needed. If one nonetheless prefers $\tilde u$, (L) *also* makes $\overline\psi$'s true-atom selection e.c.$^L$, so 4.2.1 (relativized) does then apply and $\tilde u_n-u_n\to 0$. **Either way (L) is the load-bearing hypothesis; the ledger device ("ledger gate" in the wiki's vocabulary) is a stylistic choice on top of it, not a substitute for it.** This is the route's second cost, alongside sparsity, and it should be recorded as such: *one-way visibility is structurally cheap for traders and not free for weightings.*

**5.4 Apply the corrected 4.8.16 to $H$.** Hypotheses, checked for **$H$'s** market (Trap 7):

| hypothesis | status |
|---|---|
| $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^H)$ | (S2); e.d. LUV sequence, bound $1$, coefficient $1$ |
| determined via $\Gamma_H$, $\operatorname{Val}_{\Gamma_H}=Y_n$ | (S2) |
| $g$ deferral function; timing $O(g(n{+}1))$ | Lemma 1 — *the same $g$*, since it is the same value $Y_n$ |
| $\overline w$ $\overline{\mathbb P}^H$-generable divergent weighting | (L) + §5.2 + case (a) |
| $\operatorname{supp}(\overline w)\subseteq\operatorname{im}(g)$ | ✓ |
| theorem available for $H$'s class | (R) |

Conclusion:

$$\boxed{\ \frac{\sum_{i\le n}w_i\,\big(\mathbb E^H_i(\ulcorner Y_i\urcorner)-Y_i\big)}{\sum_{i\le n}w_i}\;\eqsim_n\;0.\ }\tag{H}$$

Note what (H) is: *the human's own present estimate of its own future credence is unbiased for that future credence, on the schedule, against the weighting.* No cross-market object appears in the conclusion.

---

## 6. Step 4 — `cee` on $H$: free, full limit, all days

> **`cee`, Expected Future Expectations, Theorem 4.12.1** (`main.tex:2045`). *Let $f$ be a deferral function and $\overline X$ an e.c. sequence of $[0,1]$-LUVs. Then* $\mathbb E_n(X_n)\eqsim_n\mathbb E_n\big(\ulcorner\underline{\mathbb E}_{\underline f(\underline n)}(\underline{X_n})\urcorner\big)$.

Hypotheses checked: $f$ is a deferral function (§1) ✓; $\overline X$ is an e.d. sequence of $[0,1]$-LUVs — the paper's "e.c. sequence of LUVs" means efficient production of the *formulas* ([[setting-and-notation]] §LUV), which is exactly e.d. ✓. The theorem is quantified over **varying** sequences, which is the whole reason it is the right tool here. Its proof (app:cee) runs through `er` 4.11.4, `expprovind` 4.8.10 and `exppolymax` 4.8.13 — all free theorems of $H$'s own market, requiring only that $\Gamma_H$ represents computations and $\overline{\mathbb P}^H$ is computable, both granted by (S2) and §1. **No relativization, no oracle, no ledger.** So:

$$\mathbb E^H_n(X_n)\;\eqsim_n\;\mathbb E^H_n(\ulcorner Y_n\urcorner).\tag{C}$$

*Encoding check.* `cee`'s right-hand side is the program-encoded LUV, which is exactly the $\ulcorner Y_n\urcorner$ fixed in §1. The two markets' copies of $\ulcorner Y_n\urcorner$ live in $\mathcal L_A$ and $\mathcal L_H$ and need not be the same formula; what (S1)+(S2) assert is that both have the same **value** $Y_n$. That is all (A) and (H) use.

---

## 7. Step 5 — combining, with the bookkeeping done honestly

Write $W_n:=\sum_{i\le n}w_i$.

**Case (a): $W_\infty=\infty$.** Then $\overline w$ is a divergent weighting (Def. 4.3.4) and (A), (H) are available.

> **Lemma 2 (weighted-average annihilation).** If $\epsilon_i\to0$, $w_i\in[0,1]$ and $W_n\to\infty$, then $W_n^{-1}\sum_{i\le n}w_i\epsilon_i\to0$. *(Earlier drafts carried a boundedness hypothesis $|\epsilon_i|\le M$; it is redundant — a convergent sequence is bounded, and the head of the split is a fixed finite sum. KERNEL-CHECKED without it: `lean-deference/StreamlinedSS.lean` T1.)*
>
> *Proof.* Given $\eta>0$ choose $N$ with $|\epsilon_i|<\eta/2$ for $i>N$. Then $\big|W_n^{-1}\sum_{i\le n}w_i\epsilon_i\big|\le M N/W_n+\eta/2<\eta$ for $n$ large. $\square$

Apply Lemma 2 to (C): $\epsilon_i:=\mathbb E^H_i(X_i)-\mathbb E^H_i(\ulcorner Y_i\urcorner)\to0$, $|\epsilon_i|\le1$. Hence

$$\frac{\sum_{i\le n}w_i\big(\mathbb E^H_i(X_i)-\mathbb E^H_i(\ulcorner Y_i\urcorner)\big)}{W_n}\;\eqsim_n\;0.\tag{C$'$}$$

Now (A) $-$ (H) $-$ (C$'$). Three full limits; **full limits subtract**, which is the entire point of routing through 4.8.16 rather than 4.8.15 (whose limit points do *not* combine — the gap recorded at [[faithful-acceleration-result]] §4.3 and [[open-problems]]):

$$\boxed{\ \frac{\sum_{i\le n}w_i\,\big(a_i-\mathbb E^H_i(X_i)\big)}{\sum_{i\le n}w_i}\;\eqsim_n\;0\ }\tag{$\star$}$$

**two-sided, a genuine limit.** $(\star)$ is the **scheduled weighted-average quote–credence agreement** — stronger than the Total-Trust inequalities it yields, and equivalent via §8.2's ledger collapse to an averaged Tower. Note its literal shape: $\mathbb E^A\mathbb E^H_f$ vs $\mathbb E^H$, *not* the Tower's $\mathbb E^H\mathbb E^A$ vs $\mathbb E^H$ (corrected 2026-07-31). Everything in §8 is a corollary of it.

**Case (b): $W_\infty<\infty$.** Then $w_{g(k)}\to0$, i.e. $u_{g(k)}\to0$. Since (Lemma 3 below) $\mathbb E^H_n(X_n\cdot u_n)-t\,\mathbb E^H_n(u_n)=u_n\big(\mathbb E^H_n(X_n)-t\big)+o(1)$ and $|\mathbb E^H_n(X_n)-t|\le\max(t,1-t)\le1$, both one-sided inequalities of the per-day statement hold **trivially** along the schedule (both sides vanish). So nothing is lost; but note the *normalized average* is genuinely unavailable in case (b) — with finite mass the ratio converges to a fixed, possibly negative, number. This is why the packaging below is stated so that a single inequality covers both cases.

---

## 8. Step 6 — scheduled soft Total Trust, both one-sided inequalities

**8.0 Where the weight sits, at each step.** Three distinct positions occur and must not be conflated:

| step | position of $w_n$ | legality required |
|---|---|---|
| (A), (H) — the 4.8.16 applications | **outside every expectation**, as the weighting of the average | $\overline{\mathbb P}$-generability *of the relevant market* (Def. 4.3.5): a ramp on $A$'s own prices for (A) §4.1; a hard-coded constant computed with the ledger oracle for (H) §5.2 (hypothesis (L)) |
| $(\star)$, §8.2 | outside, as an averaging weight | same |
| Theorem SS, outside-quotes reading | **outside the corner quotes, inside $\mathbb E^H_n$** as an $\mathbb R$-LUV-combination coefficient: $\mathbb E^H_n(w_nX_n)$ | $\overline{w X}\in\mathcal{BLCS}(\overline{\mathbb P}^H)$, i.e. $\overline w$ generable for $H$ — **(L) again** |
| Theorem SS, inside-quotes reading | **inside the corner quotes**: $\mathbb E^H_n(\ulcorner X_n\cdot w_n\urcorner)$ | only that $\ulcorner X_n\cdot w_n\urcorner$ is an e.d. $[0,1]$-LUV — **free**, no (L); but relating it to the other readings needs (L) via Lemma 3 |

The inside-quotes reading is the paper's own convention for the self-trust family (`ccee` 4.12.3, `st` 4.12.4 both put $\operatorname{Ind}_\delta$ inside), and is the *cheaper* one to write down; the outside reading is what [[deference-notions]] displays. Lemma 3 shows they agree to $o(1)$.

**8.1 Type bridge: weight inside vs. outside the corner quotes.**

By Defs. 4.8.7–4.8.8 (`main.tex:1733–1748`), $\mathbb E_n$ is a LUV valuation and LUV-combinations are evaluated **linearly**. So if $u_n$ is (the value of) a feature, then $u_nX_n$ is a legal $\mathbb R$-LUV-combination and

$$\mathbb E^H_n(u_n X_n)=u_n\,\mathbb E^H_n(X_n),\qquad \mathbb E^H_n(u_n\cdot 1)=u_n\qquad\textbf{exactly.}$$

For this, $\overline{u X}$ must be in $\mathcal{BLCS}(\overline{\mathbb P}^H)$, which needs $\overline u$ $\overline{\mathbb P}^H$-generable — i.e. **(L) again**. Absent (L), the *outside-quotes* form of the target statement is not even well-typed for $H$'s market.

> **Lemma 3 (inside = outside).** Assume (L) and (S2). Then $\mathbb E^H_n\big(\ulcorner X_n\cdot u_n\urcorner\big)\eqsim_n u_n\mathbb E^H_n(X_n)$ and $\mathbb E^H_n\big(\ulcorner u_n\urcorner\big)\eqsim_n u_n$.
>
> *Proof.* $\ulcorner X_n\cdot u_n\urcorner$ — the e.d. $[0,1]$-LUV "$\nu=X_n\cdot\operatorname{Ind}_\delta(\alpha_n>t)$", describable in $\mathrm{poly}(n)$ **without** computing $u_n$ — minus the combination $u_nX_n$ is a bounded LUV-combination sequence; it is in $\mathcal{BLCS}(\overline{\mathbb P}^H)$ because $\overline u$ is generable (L); and by (S2) it has value $0$ in every $\mathbb W\in\mathrm{PC}(\Gamma_H)$. Expectation Provability Induction (`expprovind`, 4.8.10, `main.tex:1754`) gives $\eqsim_n0$. Same for the second. $\square$

So the target notion may be read either way; below the outside form is used, and Lemma 3 transports the conclusion to the inside form at a cost of $o(1)$.

**8.2 The theorem — the literal statement, its Tower-equivalent, and the Total-Trust corollaries.**

**What shape the result literally is (corrected 2026-07-31, Abram).** $(\star)$ compares the *expert's* estimate with the *novice's* current expectation — $\mathbb E^A_i\big(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner\big)$ against $\mathbb E^H_i(X_i)$ — which is **not** the Tower's shape: Tower ([[deference-notions]] §Mart) compares $\mathbb E^H_i\big(\ulcorner E^\ast(X_i)\urcorner\big)$ against $\mathbb E^H_i(X_i)$, an iterated expectation *of the novice's own*. An earlier revision of this page headlined $(\star)$ as Tower simpliciter; that was wrong on shape.

**The Tower-equivalent, via the ledger collapse.** By `expprovind` (4.8.10) with (S2) — $\alpha_i$ determined via $\Gamma_H$ with value $a_i$ — the novice's expectation of the *readable* expert's estimate is degenerate: it collapses to the quote,
$$\mathbb E^H_i\Big(\ulcorner \mathbb E^A_i\big(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner\big)\urcorner\Big)\;\eqsim_i\;\mathbb E^A_i\big(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner\big).$$
Substituting (a per-day full limit, so Lemma 2 carries it into any weighted average), $(\star)$ is *equivalent* to the scheduled weighted-average Tower — but for a readable expert the Tower reading adds nothing beyond this collapse, so the literal cross-agent statement is primary. The Total-Trust inequalities now follow.

Along $\operatorname{supp}(\overline w)$ we have $u_i>0$, and $\operatorname{Ind}_\delta$ has **no false positives** (Def. 4.3.2), so $a_i>t$; hence $w_ia_i\ge t\,w_i$ for every $i$ (trivially where $w_i=0$). Therefore, from $(\star)$,

$$\frac{\sum_{i\le n}w_i\,\mathbb E^H_i(X_i)}{W_n}=\frac{\sum_{i\le n}w_ia_i}{W_n}-\frac{\sum_{i\le n}w_i(a_i-\mathbb E^H_i(X_i))}{W_n}\;\ge\;t-o(1).$$

Symmetrically with $u^-_n:=\operatorname{Ind}_\delta(a_n<t)$, $w^-_n:=u^-_ns_n$: no false positives gives $a_i<t$ on the support, so $\sum w^-_ia_i\le tW^-_n$, and $(\star)$ for $\overline{w^-}$ (all hypotheses identical; the weighting is the mirror ramp, equally expressible) gives the reverse.

> ### Theorem SS (Scheduled quote–credence agreement, two-sided; Tower-equivalent and soft-Total-Trust inequalities as corollaries)
>
> Assume (S1), (S2), (L), (R), the erratum-corrected 4.8.16, and one-way sequential clearing as in §1. Let $g$ be the schedule of Lemma 1 — **one schedule for all $t,\delta$, and uniform across e.d. sequences of bounded description size.** Then for every e.d. sequence $(X_n)$ of $[0,1]$-LUVs, every rational $t\in[0,1]$ and rational $\delta>0$, with $w_n=\operatorname{Ind}_\delta(a_n>t)\cdot\mathbb 1[n\in\operatorname{im}(g)]$ and $w^-_n=\operatorname{Ind}_\delta(a_n<t)\cdot\mathbb 1[n\in\operatorname{im}(g)]$:
>
> **(Above-threshold inequality.)** There are $\varepsilon_n\to0$ and a finite constant $C$ with
> $$\sum_{i\le n}\mathbb E^H_i\big(X_i\cdot w_i\big)\;\ge\;t\sum_{i\le n}\mathbb E^H_i\big(w_i\big)\;-\;\varepsilon_n\sum_{i\le n}w_i\;-\;C .$$
> If $\sum_n w_n=\infty$ one may take $C=0$ and divide through:
> $$\frac{\sum_{i\le n}w_i\,\mathbb E^H_i(X_i)}{\sum_{i\le n}w_i}\;\gtrsim_n\;t .$$
> If $\sum_nw_n<\infty$ the inequality holds with the $C$ term, and in addition the **per-day** statement $\;\mathbb E^H_n(X_n\,w_n)-t\,\mathbb E^H_n(w_n)\to0\;$ holds along the schedule.
>
> **(Below-threshold inequality.)** The same with $w^-$, $\le$, $\lesssim_n$.
>
> **(The stronger fact behind both.)** In the divergent case, the two-sided full limit $(\star)$: the $w$-weighted average of $a_n-\mathbb E^H_n(X_n)$ along the schedule tends to $0$ — *weighted Mart*, not merely the two one-sided inequalities.

*(Inside-corner-quote reading: by Lemma 3, replace $\mathbb E^H_i(X_i\cdot w_i)$ by $\mathbb E^H_i(\ulcorner X_i\cdot w_i\urcorner)$ and $\mathbb E^H_i(w_i)$ by $\mathbb E^H_i(\ulcorner w_i\urcorner)$ throughout, at a cost of $o(1)$ per day — absorbed into $\varepsilon_n$.)*

**8.3 Exactly which quantifier of full Total Trust is weakened.**

Full soft Total Trust ([[deference-notions]]) is: for **every** e.d. $(X_n)$, **every** rational $t$, **every** $\delta>0$, **for all days**, a **per-day** $\liminf$ inequality. Theorem SS keeps the quantifiers over $(X_n)$, $t$, $\delta$ intact and weakens two things:

1. **all days $\to$ scheduled days.** The conclusion is restricted to $\operatorname{im}(g)$, a evaluation-sparse set of density $0$.
2. **per-day $\to$ weighted.** The per-day inequality is replaced by its $w$-weighted Cesàro average over those days.

**Why the per-day form is not recoverable here — and what this localizes.** Suppose it failed: for some $c>0$ infinitely many schedule days have $a_n>\mathbb E^H_n(X_n)+c$. To contradict $(\star)$ one must concentrate the weighting on those days, i.e. use $v_n:=u_n\cdot\operatorname{Ind}_\delta(\mathbb E^H_n(X_n)<t-\varepsilon)\cdot s_n$. That weighting **is** $\overline{\mathbb P}^H$-generable (both factors are features of $H$'s prices) — but the $A$-side application needs it to be $\overline{\mathbb P}^A$-generable, and $\mathbb E^H_n(X_n)$ is neither a price feature of $A$'s market nor computable by $A$ before $A$ clears day $n$. This is *precisely and only* what joint clearing buys ([[joint-clearing-and-trader-class]] §2), and it is unavailable by construction here. The family of quote weightings $\{\operatorname{Ind}_\delta(a>t)\}_{t,\delta}$ resolves $a_n$ but never the *error*, so no amount of quantifying over $t,\delta$ recovers per-day dominance: bad days can always be offset by good days in the same quote band. **The trade is exact, and it is a promptness trade: live feedback $\leftrightarrow$ per-day; schedule-prompt feedback (one-way + sparsity) $\leftrightarrow$ weighted average; rate-free feedback $\leftrightarrow$ limit points (§1's ladder).**

**8.4 How this feeds the Total Trust / Value / Tower loop.**

- **Upward (to the tower).** $(\star)$ is equivalent, via §8.2's collapse, to an averaged tower on every $A$-recognizable quote weighting, so the gap-bet route of [[total-trust-implies-mart]] is not needed and the amplifier of [[amplifier-counterexample]] is not the obstruction here. But averaged-on-an-evaluation-sparse-schedule is far short of full Mart, which is per-day and all-days. **Theorem SS does not collapse to the tower**, and [[tower-death]] is untouched.
- **Downward (to Value).** The Setting-1 results are stated per-day. What transports under averaging is what is *linear in the day-$n$ quantities*: the two-option identity of [[two-option-value-iff-total-trust]] at **fixed $\delta$** yields a scheduled weighted $\delta$-hedged Value (per the terminological default of [[deference-notions]] §Value — "$\delta$-hedged Value" must always carry its qualifier). What does **not** transport is anything requiring per-day dominance: the hard-argmax form via provable-bound respect, and the $\delta\to0$ limit taken after averaging. The keep-or-switch telescope ([[total-trust-implies-value-telescoping]]) needs re-derivation along a schedule and is *not* claimed here.
- **Sideways.** Because $g$ is uniform in $(t,\delta)$ and across a description-size class (§3), the forced family is at least closed under the threshold family and under menus of bounded description — which is more closure than [[faithful-acceleration-result]] §5 claims for the v3 route, though still nowhere near gap-closed.

---

## 9. Trap checklist

| trap | verdict |
|---|---|
| **1.** 4.8.15's conclusion is a limit point | **Not touched.** 4.8.15 is never cited. The whole design is to use 4.8.16's full limit so that (A), (H), (C$'$) subtract (§7). |
| **2.** Weighting generability ≠ trader legality | **Confronted head-on** (§5.1–5.3). The corpus's ledger-weighting repair is shown insufficient by itself; (L) is the real price. |
| **3.** Family C carries an environment hypothesis | **Not touched.** No use of 4.4.5, 4.8.17, or any pseudorandomness notion. Only families B (4.8.16) and the §4.12 self-trust cluster (`cee`), plus `expprovind`. |
| **4.** Value-vs-description | Checked at every generator: $g$ (Lemma 1c), $s_n$ (Lemma 1d, with truncation), $\hat a_n$ (§4.1, program encoding of $f$), $\ulcorner X_n\cdot u_n\urcorner$ (Lemma 3, described without computing $u_n$). And it is the lever that breaks the wiki's PI argument (§5.3). |
| **5.** Window-disjointness is a round-trip condition | **Not needed** by this route (4.8.16 asks only support + timing), and satisfied anyway since $g(k{+}1)>f(g(k))$ (§3). |
| **6.** The timing condition costs the coupled construction | **Paid explicitly**: $T$ bounds the cost of running $A$ to $f(n)$, the ledger, and $H^+$ to $f(n)$ (§3). |
| **7.** Cross-application errors | Hypotheses tabulated separately per market (§4.2 for $A$, §5.4 for $H$, §6 for `cee`). The one asymmetry: only $H$ needs (L) and (R); $A$ needs neither. |

**Two further hazards, self-identified.**

- **Self-fulfilling quotes.** $a_n$ forecasts $Y_n=\mathbb E^H_{f(n)}(X_n)$, and $H$'s market at day $f(n)$ has seen $a_n$. So $A$ partly *causes* what it forecasts. Nothing in Theorem SS distinguishes honest forecasting from self-fulfilling manipulation; it is a calibration statement, not a soundness one ([[target-soundness-and-safety]], [[manipulation-boundary-and-corrigibility]]). The framework handles the self-reference cleanly (the weighting is a continuous feature of $A$'s own prices, so the clearing fixed point exists), but the *interpretation* must not overreach.
- **Non-vacuity.** The theorem presupposes the coupled pair exists with $H\dashv\mathrm P^L$. Under one-way clearing this is a two-stage composition (§1): cite paper §5 for $A$, then a *relativized* §5 for $H^+$. The relativized existence construction is a mild extension, not a literal citation (≈0.85) — but strictly cheaper than v3's assumed **joint** Brouwer argument, which had no staged reading available at all.

---

## 10. Final statements

### Theorem SS (clean form)

*Let $H\dashv\mathcal C_H$ and $A\dashv\mathcal C_A$ be logical inductors over their own deductive processes under one-way sequential clearing (§1), $f$ an e.c. strictly increasing lookahead which is a deferral function, $Y_n:=\mathbb E^H_{f(n)}(X_n)$, $a_n:=\mathbb E^A_n(\ulcorner Y_n\urcorner)$. Assume (S1), (S2), (L), (R). Let $g$ be the deferral function of Lemma 1 and $s_n=\mathbb 1[n\in\operatorname{im}(g)]$.*

*Then for every e.d. sequence $(X_n)$ of $[0,1]$-LUVs of $H$'s language, every rational $t\in[0,1]$ and rational $\delta>0$, writing $w_n=\operatorname{Ind}_\delta(a_n>t)\,s_n$:*

*If $\sum_n w_n=\infty$,*
$$\frac{\sum_{i\le n}w_i\Big(\mathbb E^A_i\big(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner\big)-\mathbb E^H_i(X_i)\Big)}{\sum_{i\le n}w_i}\;\eqsim_n\;0
\qquad\text{(two-sided full limit)},$$ *and hence*
$$\frac{\sum_{i\le n}w_i\,\mathbb E^H_i(X_i)}{\sum_{i\le n}w_i}\;\gtrsim_n\;t,
\qquad
\frac{\sum_{i\le n}w^-_i\,\mathbb E^H_i(X_i)}{\sum_{i\le n}w^-_i}\;\lesssim_n\;t
\quad\big(w^-_n=\operatorname{Ind}_\delta(a_n<t)\,s_n\big).$$ *If $\sum_nw_n<\infty$, then $w_n\to0$ and both one-sided inequalities hold trivially per-day along the schedule.* *Equivalently, in one unnormalized inequality covering both cases: there exist $\varepsilon_n\to0$ and $C<\infty$ with $\sum_{i\le n}w_i\mathbb E^H_i(X_i)\ge t\sum_{i\le n}w_i-\varepsilon_n\sum_{i\le n}w_i-C$.* *By Lemma 3 the same holds with the weight inside the corner quotes.*

### Named hypotheses

1. **(S1)** $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^A)$, determined via $\Gamma_A$; $\Gamma_A\supseteq$ PA, represents computations, consistent. *(standing)*
2. **(S2) Mirror determinacy.** $\Gamma_H\supseteq$ PA, represents computations, consistent, and $\mathcal L_H$ describes the coupled construction; hence $\overline{\ulcorner Y\urcorner}$ and $\overline\alpha$ are $\mathcal{BLCS}(\overline{\mathbb P}^H)$ and determined via $\Gamma_H$.
3. **(L) Ledger legibility / $H^+$.** $\mathcal C_H=\mathrm P^{L}$ with $L$ the published quote sequence; $H$ satisfies the criterion against $\mathrm P^L$; "e.c." on the $H$-side is read relative to $L$.
4. **(R) Relativization.** 4.8.16 (E.12 $\to$ D.4) holds for $H$ against $\mathrm P^L$-generable weightings.
5. **(E) Erratum.** The corrected 4.8.16 carries the support clause and concludes a full limit; the corrected 4.8.15 carries none and concludes a limit point. *(Certified by appendices E.11/E.12;* *only 4.8.16 is used.)*
6. **One-way sequential clearing** as specified in §1, with same-day publication $e(n)=n$. *(Publication may be delayed to any $e(n)\le n$ with the weighting read at $e^{-1}$; nothing else changes.)*
7. *(For non-vacuity only)* the paper's §5 construction relativizes to $\mathrm P^L$.

**Explicitly not assumed:** joint clearing; any joint Brouwer construction; any *live* $A$-side visibility of $H$ (no feature of $A$'s market ever reads $H$'s prices — though note what **is** assumed: eventual empirical feedback, i.e. determinacy via $\Gamma_A$ + $\Gamma_A$-completeness of $D_A$, made schedule-prompt by the sparsity; §1's ladder); window-disjointness; convergence or fixedness of $(X_n)$; any environment/pseudorandomness hypothesis; any bound on how fast the coupled construction runs *other than* its computability (the bound is absorbed into the choice of $g$, which is the point of the route).

### Status verdict

**PROVED modulo named hypotheses — confidence ≈ 0.82.**

Decomposition: erratum-corrected 4.8.16 ≈0.95; Lemma 1 (schedule existence, including the poly-time membership test) ≈0.95; $A$-side weighting legality ≈0.96; (R) relativization ≈0.92; (S2) ≈0.95; the combination bookkeeping (§7) ≈0.98; Lemma 3 type bridge ≈0.95. Product ≈0.72, adjusted upward to ≈0.82 for the fact that the failure modes are largely *shared* (they stand or fall with (L)) rather than independent.

**Subsidiary claim: [[unbiasedness-theorem-families]] §6's ledger-weighting repair is invalid as stated — confidence ≈0.88.** It should be amended to say that the ledger must put the quote inside $\mathcal C_H$ (hypothesis (L)), and that *given* (L) the ramp on the quote is directly generable and $\tilde u$ is optional. The corresponding sentence in [[faithful-acceleration-result]] §4.3 step 3 needs the same amendment.

### The three things a skeptic should attack first

1. **(L), and whether it is question-begging.** Is "$H$ is inexploitable by $\mathrm P^L$ traders" a legitimate reading of "the human has heard the AI", or does it quietly hand $H$ a capability that makes the theorem cheap? My defence: it grants only *reading the output*, never *computing the target*, so the complexity gap that makes $A$ useful survives intact; and $\mathrm P^L$ is c.e. and poly-closed, hence a legal $\mathcal C_H$ under this wiki's own convention. But a referee who rejects (L) kills the route — and, per §5.3, kills the corpus's existing ledger-weighting repair too, so rejecting it is not a cheap move.
2. **(R): does D.4 really relativize?** Open `main.tex:4729–4842` and confirm that the constructed trader consults the weighting only as a black-box coefficient, so that giving its generator an oracle changes nothing else. This is the same *kind* of obligation v3 flagged for D.2, but weaker (an oracle on the clock, not a new feature language over two markets). If it fails, the $H$-side 4.8.16 fails and only (A) and (C) survive — which is not enough for anything. **Resolved 2026-07-31 (source-checked):** the once-flagged "computed-but-not-yet-decided bridge" is handled by construction — the D.4 trader never holds to settlement (round-trip realized cash; Kelly floor at $-1$ in every plausible world), with all settlement-timing quarantined inside rate-free Affine Provability Induction (§3's mechanism remark). So the (R) check reduces to two items: the weighting enters D.4 only as black-box bet sizing (verified by inspection, `main.tex:4749–4764`), and `affprovind` relativizes to $\mathrm P^L$ — the same species of obligation as the 4.8.10 relativization the route needs anyway.
3. **Lemma 1(d), the poly-time schedule-membership test.** The truncation argument is the load-bearing move (without it $s_n$ is not e.c. and *both* weightings die). Check that aborting the $Y$-computation at $n$ steps really settles membership correctly in every case, including $n$ between two consecutive schedule points and $n$ below $g(1)$.

*Runner-up:* §5.3's negative claim. A referee who finds any LI theorem forcing $\mathbb P^H_n(\psi_n)\to\mathbb 1[a_n>t]$ pointwise for a *mixed* e.c. sequence of decided sentences would overturn both the correction and the necessity of (L). I looked at 4.2.1, 4.1.1, 4.2.3, 4.2.4, 4.8.10, 4.8.15/16 and 4.11.1 and found none; the counter-intuition (a market can sit at $\tfrac12$ forever on decided-but-unselectable atoms) is what convinces me the gap is real rather than a gap in my reading.

## Related

- [[faithful-acceleration-result]] §4.3 — the `cee` route this makes rigorous; §4.3's first "way out"
- [[unbiasedness-theorem-families]] §6 — the ledger-weighting correction, here corrected in turn
- [[joint-clearing-and-trader-class]] — the assumption this route removes, and §8.3's exact statement of what it bought
- [[li-paper-erratum]] §1, §3 — the corrected 4.8.16 and the numbering
- [[delay-and-visibility]] §3 — the value-vs-description obstruction, reused in §5.3
- [[deference-notions]] — the target notion and the loop §8.4 feeds
- [[fa-positive-results-corrected-v3]] — the route whose A1 this replaces with (L) + sparsity
