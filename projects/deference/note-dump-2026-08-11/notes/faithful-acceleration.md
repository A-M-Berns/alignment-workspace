# Faithful Acceleration: Forced Value When the AI Predicts the Human's Credences

*A note by Claude (Opus 4.8), developing a positive direction for human–AI deference in logical induction, in conversation with Abram Demski. It is deliberately narrow: it builds, more or less from scratch, toward one candidate theorem — that a human is **forced to defer to an AI that predicts the human's own future credences** (in the averaged sense, but over **all** questions, not just the decidable ones, and with **no appeal to the prior**) — and it sets aside the broader theory (the `Value ⟺ Mart` machinery, the negative results, the frozen/soundness construction), citing it only where needed. Companion to [`deference-in-logical-induction-v5.md`](deference-in-logical-induction-v5.md) (the general theory and the obstructions) and Demski's [`li-deference.md`](li-deference.md) (the motivation).*

> **Status.** The central result (§5) is a **candidate**, but a sharpened one. Its two inputs are standard logical-induction theorems and the trader argument is given in full; the **trader core is now kernel-checked** in Lean (`FaithfulAcceleration.lean`, §9): `sorry`-free, every result on the standard axioms. Its load-bearing input — the calibration bound (§4, ingredient II) — turns out to be *exactly* the LI theorem **Expectation Unbiasedness From Feedback**, which downgrades the original "gap 1" from open mathematics to construction bookkeeping. The remaining obligations (§8) are the observability/existence setup and an audit that the construction never forces a hard settlement. Treat §5 as "forced *modulo* the named LI theorems and the §8 obligations," not as a finished proof. The conceptual claims (§6–§7) are interpretation.

---

## 1. The setup, and the one idea

Two reasoners, each a logical inductor (defined in §2): a **human** $H$ and an **AI** $A$, the AI computationally stronger. They are **mutually observable** — each can read the other's recent outputs — and the AI spends its extra strength **predicting the human's own future opinions**.

The single idea this note turns on:

> **Defer to the human's *credences*, not to the world's *truth*.**

The known obstructions to forced human–AI trust (No-Forced-Trust on undecidables; the anti-inductive settlement paradox; the cost-circularity regress — §6) are all obstructions to making the AI track *the truth*. They evaporate when the AI is instead asked to track *where the human's own deliberation is heading*, because a human credence is (i) **always present** — there is one for every sentence, decidable or not; (ii) **continuous** — it lives at the price level, where logical induction's self-reference paradoxes are benign; and (iii) **self-trusted** — a logical inductor already trusts its own future. Those three properties are exactly what the truth-level target lacks, and exactly what makes the positive theorem go through.

The result is a precise sense in which the AI is forced to be a **faithful accelerator**: it cannot do anything but relay the human's own considered judgment, sooner. It is *not* forced to be a better oracle than the human (§7) — and that limitation is the honest price.

---

## 2. Background, from scratch

**Logical inductor.** Fix a language and a theory $\Gamma$ able to talk about computable functions, with a computable deductive process $D$ that **decides** sentences over time (a sentence's decided value, if it ever comes, is its truth value). A **logical inductor against a trader class $\mathcal{C}$** is a computable sequence of belief states $\mathbb{P}=(\mathbb{P}_n)$ — $\mathbb{P}_n(\varphi)\in[0,1]$ the day-$n$ credence — satisfying the **logical-induction criterion**: no trader in $\mathcal{C}$ exploits the market (a computational no-Dutch-book). Everything below is a consequence of that one criterion. We take two trader classes $\mathcal{C}_H \subseteq \mathcal{C}_A$ (closed under polynomial overhead, computably enumerable; canonically $\mathrm{P}\subseteq\mathrm{EXP}$): $H \dashv \mathcal{C}_H$, $A \dashv \mathcal{C}_A$.

**LUVs and expectation.** A *logically uncertain variable* (LUV) is a formula naming a unique real that $\Gamma$ proves lies in a known interval $[a,b]$; LUVs are bounded random variables, written $X, Y, \dots$. $E^{\mathbb P}_n(X)$ is $\mathbb{P}$'s day-$n$ expectation of $X$. Write $E^H_n$, $E^A_n$ for the two reasoners. Asymptotics: $x_n \approx_n y_n$ means $x_n - y_n \to 0$; $x_n \gtrsim_n y_n$ means $\liminf(x_n - y_n)\ge 0$. Corner quotes $\ulcorner\cdot\urcorner$ turn a number the market computes into the LUV naming it, so $E^H_n(\ulcorner E^A_n(X)\urcorner)$ — "$H$'s estimate of $A$'s estimate" — is type-correct.

**Two LI theorems, taken as black boxes.** These are the only non-trivial inputs.

- **Self-trust** — **Expected Future Expectations** (_Logical Induction_, page 47, theorem 4.12.1). For an e.c. lookahead $f(n)>n$, a logical inductor towers over its own future: $\;E^H_n(X) \approx_n E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)$. *The human already trusts where its own deliberation is heading.*
- **Calibration from feedback** — **Expectation Unbiasedness From Feedback** (_Logical Induction_, page 42, theorem 4.8.16; the expectation analog of Garrabrant et al.'s *Unbiasedness From Feedback*). If an inductor issues expectations $\mathbb{E}_n(B_n)$ of a sequence of bounded LUV-combinations $B_n$ that is *determined via $\Gamma$* (each has a definite $\Gamma$-provable value $\operatorname{Val}_\Gamma(B_n)$), and a deferral function makes each realized value computable by the time the next weighted term arrives, then for any $\mathcal{C}$-generable divergent weighting $w_n$ (so $\sum_{n\le N} w_n\to\infty$) the weighted average bias vanishes: $\;\dfrac{\sum_{n\le N} w_n\big(\mathbb{E}_n(B_n) - \operatorname{Val}_\Gamma(B_n)\big)}{\sum_{n\le N} w_n}\xrightarrow[N\to\infty]{}0$. *An inductor that gets to check its predictions cannot stay systematically off on any pattern it could name — including binning by its own forecast.* (Their own headline example of such a weighting is $\mathrm{Ind}_\delta(\mathbb{P}_n(\phi_n)>\tfrac12)$, which is our $w_n$ below.)

**The deference notions.** For an "expert" estimate operator $E^\ast$ that $H$ can read:

- **Tower** $E^H_n(X)\approx_n E^H_n(\ulcorner E^\ast(X)\urcorner)$ — $H$ expects no net update on learning the expert's estimate.
- **Total Trust** $E^H_n(X \mid E^\ast(X) > t) \gtrsim_n t$ — conditional on the expert estimating $X$ high, $H$ does too. (In the LI continuum this must be **soft**: condition through a continuous threshold $\mathrm{Ind}_\delta(E^\ast(X)>t)$, $\delta\to0$, since a hard indicator is an illegal discontinuous weight. Here $\mathrm{Ind}_\delta$ is the **one-sided ramp**: $\mathrm{Ind}_\delta(y>p)=0$ for $y\le p$, $(y-p)/\delta$ for $p<y<p+\delta$, and $1$ for $y\ge p+\delta$. On a bare quantity we write $\mathrm{Ind}_\delta(z):=\mathrm{Ind}_\delta(z>0)$ — equivalently $\mathrm{Ind}_\delta(y>p)=\mathrm{Ind}_\delta(y-p)$ — and $\mathrm{Ind}_\delta(y<p):=\mathrm{Ind}_\delta(p-y)$.)
- **Value** — for every menu of options, $H$ would (weakly) rather let the expert pick than commit to a fixed option.

We use one fact from the general theory without re-deriving it (v5 §1.2, kernel-checked `value_iff_totalTrust`): for any expert that is **observable** (readable by $H$) and **coherent** (a single linear belief state, so its $\arg\max$ over a menu is well-defined),

$$\textbf{Total Trust} \;\Longleftrightarrow\; \textbf{Value},$$

forced, by the two-option witness menu — using only $H$'s linearity and the expert's coherence, **no Tower**. So to force Value it suffices to force (soft) Total Trust. (The reverse climb, Total Trust $\Rightarrow$ the full Tower *equality*, is a separate and harder "squeeze" we do **not** need here.)

---

## 3. The objects: the AI as a predictor of the human

The expert $H$ defers to is **the AI's forecast of the human's own future credence.** Fix a lookahead $f$. For a LUV $X$, the AI's day-$n$ quote is

$$\boxed{\,a_n \;:=\; E^A_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)\,}$$

— $A$'s prediction, formed at its day $n$, of what $H$ will believe about $X$ after $f(n)$ stages of deliberation. Read as an operator on LUVs, this forecast is the **expert** $E^\ast$ that §2's equivalence takes as input — write $E^\ast(X)=a_n$. It meets §2's two conditions on an expert: it is *coherent* — §2's term for a single linear belief state (so its $\arg\max$ over a menu is well-defined) — because it is the linear $E^A_n$ applied to the linear $E^H_{f(n)}$, hence linear in $X$; and it is *observable* — readable by $H$ — because $H$'s world records $A$'s quotes $a_n$ (the $H$-reads-$A$ channel, spelled out just below). So §2's forced equivalence **Total Trust ⟺ Value** applies to $E^\ast$, and forcing $H$ to Value the AI reduces to forcing (soft) Total Trust in it.

**Mutual observability, spelled out.** Two channels, each a bounded computable delay:
- $A$ **reads $H$**: $A$'s deductive process records $H$'s past prices, and in particular the realized $E^H_{f(n)}(X)$ once stage $f(n)$ arrives. (This is what gives $A$ *feedback* on its forecasts — §4.)
- $H$ **reads $A$**: $H$'s deductive process records $A$'s quotes $a_n$, so $a_n$ is a $\mathcal{C}_H$-readable feature of $H$'s world, and $H$ can condition on it. (This is what lets $H$ *use* the forecast — §5.)

Both directions are load-bearing; the theorem fails with either one alone.

The coupled system $(H \text{ reads } A,\ A \text{ reads } H)$ exists by the usual one-stage-delay construction (each stage computable from strictly earlier stages); this is taken as given here (§8, obligation 3).

---

## 4. The two forced ingredients

Everything reduces to two facts, both **forced** (modulo the named LI theorems), and crucially both **universal over sentences** and **free of forward simulation**.

**(I) The human trusts its own future** (Expected Future Expectations, _Logical Induction_ theorem 4.12.1; §2):

$$E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big).$$

**(II) The AI is calibrated to the human — this is Expectation Unbiasedness From Feedback.** Take the bounded LUV-combination sequence $B_n := \ulcorner E^H_{f(n)}(X)\urcorner$. It is **determined via $\Gamma$**: $H$ is a fixed computable process — even reading $A$, the coupled $(H,A)$ recursion is deterministic — so its stage-$f(n)$ credence is a definite $\Gamma$-provable number, $\operatorname{Val}_\Gamma(B_n) = E^H_{f(n)}(X)$. Its realized value enters $A$'s world by **observation** at $\sim f(n)$ (the $A$-reads-$H$ channel: $A$ records $H$'s realized price; nothing is re-simulated). $A$'s forecast is $a_n = E^A_n(B_n)$. The theorem then gives, for any $\mathcal{C}_A$-generable divergent weighting $w_n$ that is *patient* (deferred until the feedback is in),

$$\frac{\sum_{n\le N} w_n\big(E^H_{f(n)}(X) - a_n\big)}{\sum_{n\le N} w_n}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$

Two things to notice about (II), both decisive:

- **It is checked after the fact, not by forward simulation.** $A$'s calibration is enforced by a trader that *waits* for $E^H_{f(n)}(X)$ to be revealed and then banks on any systematic bias — it never has to *compute* $H$'s future in advance. So the cost-circularity that defeats *timely* prediction (you would have to simulate the coupled system, including $A$'s own future) never arises here. No power assumption is even needed.
- **The feedback is a human credence, which always exists.** $E^H_{f(n)}(X)$ is realized for *every* $X$, whether or not $D$ ever decides $X$. So (II) holds **over all sentences** — there is no decidable/timely fragment to restrict to, and no inductive generalization (hence no dependence on the prior) is invoked.

These are precisely the two properties the truth-level target lacks.

---

## 5. The theorem: forced Value via the credence round-trip

> **Candidate Theorem (faithful acceleration — bounded $\varepsilon$-violation Total Trust).** Fix an e.c. LUV $X$, a rational threshold $t\in[0,1]$, a margin $\varepsilon>0$, and a gate width $\delta>0$, and write
> $$g_n(X,t,\delta) \;:=\; \mathrm{Ind}_\delta(a_n>t), \qquad w_n(X,t,\varepsilon,\delta) \;:=\; g_n(X,t,\delta)\cdot\mathrm{Ind}_\delta\big(E^H_n(X) < t-\varepsilon\big),$$
> where $g_n(X,t,\delta)$ is the soft **gate** ("$A$ forecasts above $t$") and $w_n(X,t,\varepsilon,\delta)$ is the **violation weight** ($w_n>0$ exactly when $A$ forecasts $a_n>t$ while $H$'s own day-$n$ price $E^H_n(X)$ sits below $t-\varepsilon$). (All arguments are shown explicitly; the gate does not depend on $\varepsilon$, which enters only the violation test. Where $X,t,\varepsilon,\delta$ are fixed — throughout the proof and the corollary — we abbreviate $g_n:=g_n(X,t,\delta)$ and $w_n:=w_n(X,t,\varepsilon,\delta)$.) Under §3 (two mutually-observable inductors, $A$ forecasting $H$'s lookahead credence) and the two forced ingredients of §4, for every such $X,t,\varepsilon,\delta$ the violation weight is summable:
> $$\boxed{\ \sum_{n} w_n(X,t,\varepsilon,\delta) \;<\; \infty\ }$$

**Why $\sum_n w_n < \infty$ is the logical-induction reading of Total Trust.** The chain below rewrites classical Total Trust into logical induction one small step at a time — a substitution, a ratio, a softening, an abbreviation, some algebra — until a single step — **the weakening** — drops the per-day *limit* to the feasible $\sum_n w_n<\infty$. It pictures how the statements relate; it does not derive the bottom line (that is the theorem below, off the chain).

$$
\begin{aligned}
& E^H\big(X \mid E^\ast(X) > t\big) \;>\; t \\
&\quad\big\downarrow\quad {\small \text{conditional expectation as a ratio: } E^H(X\mid\varphi)=E^H\big(X\,\mathbb{1}[\varphi]\big)\big/E^H\big(\mathbb{1}[\varphi]\big)} \\
& \frac{E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big)}{E^H\big(\mathbb{1}[E^\ast(X) > t]\big)} \;>\; t \\
&\quad\big\downarrow\quad {\small \text{clear the positive denominator } E^H(\mathbb{1}[E^\ast(X)>t])\ (\text{still a single positive number here, before any } n\text{-index or limit})} \\
& E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big) \;>\; t\,E^H\big(\mathbb{1}[E^\ast(X) > t]\big) \\
&\quad\big\downarrow\quad {\small \text{subtract the right-hand side}} \\
& E^H\big(X\,\mathbb{1}[E^\ast(X) > t]\big) - t\,E^H\big(\mathbb{1}[E^\ast(X) > t]\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{linearity of } E^H:\ \text{fold into one expectation}} \\
& E^H\big((X-t)\,\mathbb{1}[E^\ast(X) > t]\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{soften the hard indicator } \mathbb{1}[\,\cdot>t] \text{ to the ramp } \mathrm{Ind}_\delta(\cdot>t)\ (\text{a } 0/1 \text{ weight is illegal in logical induction})} \\
& E^H\big((X-t)\,\mathrm{Ind}_\delta(E^\ast(X) > t)\big) \;>\; 0 \\
&\quad\big\downarrow\quad {\small \text{evaluate in logical induction at day } n\text{ (the seam):}\ E^H\to E^H_n;\ \text{the expert estimate becomes } A\text{'s day-}n \text{ forecast } E^A_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)\ \text{of } H\text{'s own future credence about the same } X;\ \text{and } > \text{ becomes the asymptotic } \gtrsim_n\ (\text{meaningless without the } n\text{-index})} \\
& E^H_n\big((X-t)\,\mathrm{Ind}_\delta(E^A_n(\ulcorner E^H_{f(n)}(X)\urcorner) > t)\big) \;\gtrsim_n\; 0 \\
&\quad\big\downarrow\quad {\small \text{abbreviate the gate}\ \ g_n:=\mathrm{Ind}_\delta\big(E^A_n(\ulcorner E^H_{f(n)}(X)\urcorner) > t\big)} \\
& E^H_n\big((X-t)\,g_n\big) \;\gtrsim_n\; 0 \\
&\quad\big\downarrow\quad {\small g_n \text{ is decided by day } n\ (H \text{ reads } A),\ \text{so the decided scalar pulls out of the expectation: } E^H_n((X-t)\,g_n)\approx_n g_n\,E^H_n(X-t)=g_n(E^H_n(X)-t)} \\
& g_n\big(E^H_n(X) - t\big) \;\gtrsim_n\; 0 \qquad {\small\textbf{(the limit)}} \\
&\quad\big\downarrow\quad {\small \textbf{the weakening}\ (\text{the one non-equivalence}):\ \text{replace the liminf by a summable count with an } \varepsilon \text{ margin; only the gated days with } E^H_n(X)<t-\varepsilon \text{ need sum to a finite total}} \\
& \sum_n g_n\,\mathrm{Ind}_\delta\big(E^H_n(X) - t < -\varepsilon\big) \;<\; \infty \qquad {\small\textbf{(bounded }\varepsilon\textbf{-violation)}} \\
&\quad\big\downarrow\quad {\small \text{abbreviate the violation weight}\ \ w_n:=g_n\,\mathrm{Ind}_\delta\big(E^H_n(X) < t-\varepsilon\big)} \\
& \sum_n w_n \;<\; \infty \qquad {\small\textbf{(the Theorem)}}
\end{aligned}
$$

**The strengths of Total Trust, and why the weakest is the target.** Every arrow but the penultimate one is an equivalence, so the top of the chain is one claim in changing dress, arriving at the **limit** — on the flagged days, $H$'s credence converges to at least $t$. *The weakening* is the only change of content, and it drops to a strictly weaker statement. Four statements sit here, strongest to weakest (each $\Downarrow$ a strict weakening):

$$
\begin{aligned}
& \textbf{bounded-violation}: \quad \sum_n g_n\,\mathrm{Ind}_\delta\big(E^H_n(X)-t<0\big)<\infty \\
& \qquad\big\Downarrow \\
& \textbf{limit}: \quad g_n\big(E^H_n(X)-t\big)\gtrsim_n 0 \\
& \qquad\big\Downarrow \\
& \textbf{bounded }\varepsilon\textbf{-violation}: \quad \sum_n w_n<\infty \quad(\text{the Theorem}) \\
& \qquad\big\Downarrow \\
& \textbf{averaged}: \quad \dfrac{\sum_{n\le N} g_n E^H_n(X)}{\sum_{n\le N} g_n}\gtrsim t-\varepsilon-\delta \quad(\text{the Corollary})
\end{aligned}
$$

The top two ask that $H$'s credence actually **reach $t$** — that is the pointwise tower, which §6 proves **unforceable** (a human cannot be held to per-question exactness). The $\varepsilon$ **margin** in $w_n$ is precisely the retreat from "reach $t$" to "don't fall a full $\varepsilon$ short too often" — the *modest-expert slack* — and it is what makes the claim forceable: send $\varepsilon\to 0$ and you are demanding the tower again. So **bounded $\varepsilon$-violation is the strongest rung LI can force**, which is why the theorem lands there.

Watch what the margin does to strength. *Without* it, a bounded count of violations (**bounded-violation**, threshold $0$) is **stronger** than the limit — it kills even the vanishing tail of shortfalls the limit allows (e.g. $E^H_n(X)-t=-1/n$: the limit holds, the count diverges). *With* it (threshold $-\varepsilon$), $\sum_n w_n<\infty$ is **weaker** than the limit — it forgives any shortfall under $\varepsilon$ (e.g. a credence parked at $t-\tfrac\varepsilon2$ forever: $\sum_n w_n=0$, but the limit fails). The same "bounded violations" flips from stronger to weaker as the threshold slides from $0$ to $-\varepsilon$; the two counts sandwich the limit, and the whole question of feasibility lives in that $\varepsilon$.

The theorem's real content is a **no-cancellation** one. Relative to the **averaged** rung, $\sum_n w_n<\infty$ is one strict step stronger (the $\delta$ gap); but relative to a bare mean $\ge t$ it is *neither* stronger nor weaker — it forbids the large-but-balanced deficits a mean tolerates (no surplus days may pay for deficit days) while itself tolerating the sub-$\varepsilon$ shortfall a mean forbids. "The gated mean is $\ge t$" any balanced forecaster meets; "the deficit is bounded *on its own*" is the sharp claim, and that is exactly what calibration (II) buys.

Finally, the chain only *relates* these statements — it does not *establish* the bottom one. Run forward it would need the limit as a premise, and the limit is false, so as a derivation it is empty. That $\sum_n w_n < \infty$ truly holds — that $H$ is forced this far — is a separate fact: the squeeze of self-trust (I) and calibration (II) in the proof below, off this chain entirely.

**Proof (sketch — see §8 for the modeling caveats).** Suppose toward a contradiction that $\sum_n w_n=\infty$, and write $Y_n:=E^H_{f(n)}(X)$ (the future price $A$ forecasts) and $W_N:=\sum_{n\le N} w_n\to\infty$. The weight $w_n$ is recognizable to **both** inductors — $H$ reads $A$'s quote $a_n$, $A$ reads $H$'s price $E^H_n(X)$, both are decided by day $n$, and both gate factors are continuous in them — so the calibration theorem may be summed against $w_n$ on either side. The whole argument is then a squeeze: *$A$'s forecast $a_n$ and $H$'s present price $E^H_n(X)$ are two unbiased estimates of the same future quantity $Y_n$, so they cannot persistently disagree — while the gate is built to fire exactly where they disagree by more than $\varepsilon$.*

*Step 1 — $A$'s forecast is unbiased for $Y_n$ (ingredient II).* This is (II) read verbatim: $A$ forecasts $Y_n$, observes its realized value at $\sim f(n)$, and so cannot stay biased against the $\mathcal{C}_A$-recognizable weight $w_n$:
$$\frac{\sum_{n\le N} w_n\,(Y_n-a_n)}{W_N}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$

*Step 2 — $H$'s present price is unbiased for $Y_n$ too (ingredient I, made quantitative by the same calibration).* Self-trust (I) identifies $H$'s day-$n$ price for $X$ with its own day-$n$ estimate of its future price, $E^H_n(X)\approx_n E^H_n(\ulcorner Y_n\urcorner)$ — so $E^H_n(X)$ *is* $H$'s forecast of $Y_n$. And $H$, like $A$, later observes the realized $Y_n$ as feedback, so the Expectation-Unbiasedness theorem behind (II) — now applied to $H$'s forecast of its *own* future — makes that forecast unbiased; the per-$n$ self-trust gap is null and adds nothing to a divergent weighted average. Together:
$$\frac{\sum_{n\le N} w_n\,(Y_n-E^H_n(X))}{W_N}\ \xrightarrow[\;N\to\infty\;]{}\ 0.$$

*Step 3 — so the two estimates agree on average.* Subtracting Step 1 from Step 2 (the common $Y_n$ cancels):
$$\frac{\sum_{n\le N} w_n\,(a_n-E^H_n(X))}{W_N}\ \xrightarrow[\;N\to\infty\;]{}\ 0.\tag{$\ast$}$$

*Step 4 — but the gate forces them apart.* By construction $w_n>0$ only when $a_n>t$ **and** $E^H_n(X)<t-\varepsilon$; hence $a_n-E^H_n(X)>\varepsilon$ on the entire support of $w_n$, so $\sum_{n\le N} w_n\,(a_n-E^H_n(X))\ge\varepsilon W_N$ — the average in $(\ast)$ is $\ge\varepsilon$ for every $N$. This contradicts $(\ast)$, which sends that same average to $0$. So the assumption $\sum_n w_n=\infty$ is untenable: $\sum_n w_n<\infty$. $\qquad\blacksquare$

*(Read as a Dutch book, $(\ast)$ is the self-trust round-trip — buy $X$ at $H$'s present price, sell at its own future price $Y_n$ — elaborated in **What powered it** below, and kernel-checked in that form in §9.)*

> **Corollary (averaged Total Trust; hence classwise Value).** Suppose the gate carries infinite weight, $\sum_n g_n(X,t,\delta)=\infty$. Then the gate-weighted average of $H$'s own credence satisfies
> $$\liminf_{N\to\infty}\ \frac{\sum_{n\le N} g_n(X,t,\delta)\,E^H_n(X)}{\sum_{n\le N} g_n(X,t,\delta)}\ \ge\ t-\varepsilon-\delta\qquad\big(\,\to t \text{ as } \varepsilon,\delta\to0\,\big),$$
> i.e. *averaged over the class of days $\{a_n>t\}$ on which $A$ forecasts high, $H$'s own credence is at least $t$ in the $\varepsilon,\delta\to0$ limit.* By the §2 equivalence **Total Trust $\Leftrightarrow$ Value** (applied to this class), $H$ correspondingly **Values** $A$ classwise: averaged over the menus indexed by the class, $H$ weakly prefers to let $A$ pick rather than commit to a fixed option. This holds for **every** $X$ — over **all sentences**, decidable or not — and with **no appeal to the prior**.

*Proof.* Split the gate-on days by $H$'s price. The **deep** days $\{E^H_n(X)\le t-\varepsilon-\delta\}$ are exactly where the inner soft indicator saturates to $1$, so there $w_n(X,t,\varepsilon,\delta)=g_n(X,t,\delta)$, giving $\sum_{\text{deep}} g_n=\sum_{\text{deep}} w_n\le\sum_n w_n<\infty$ by the Theorem. Bounding the deep days below by $E^H_n(X)\ge 0$ and every remaining gate-on day by $E^H_n(X)>t-\varepsilon-\delta$,
$$\sum_{n\le N} g_n\,E^H_n(X)\ \ge\ (t-\varepsilon-\delta)\Big(\textstyle\sum_{n\le N} g_n-\sum_{\text{deep},\,n\le N} g_n\Big),$$
so, dividing by $\sum_{n\le N} g_n$, the average is at least $(t-\varepsilon-\delta)\big(1-\sum_{\text{deep},\,n\le N} g_n/\sum_{n\le N} g_n\big)$. The subtracted ratio has a convergent numerator (it increases to $\sum_{\text{deep}} g_n\le\sum_n w_n<\infty$) over a denominator $\to\infty$, so it tends to $0$; taking $\liminf_{N\to\infty}$ leaves $t-\varepsilon-\delta$. (For $t\le\varepsilon+\delta$ the bound is vacuous, the average being $\ge 0$.) $\square$

The implication is **one-directional**: $\sum_n w_n<\infty$ is strictly stronger than this average bound. The average tolerates a limiting gated credence as low as $t-\varepsilon-\delta$, whereas $\sum_n w_n<\infty$ requires it no lower than $t-\varepsilon$ — a gap of $\delta$ — so this is a corollary *of* the Theorem, not a restatement of it.

*Averaged, not per-day.* The Corollary's bound is an **average** over the gated class of days — a ratio of gate-weighted sums, weaker even than the bounded $\varepsilon$-violation Theorem. The "Strength" note turns on this: the average (and the Theorem above it) are forced; the per-day **limit** form is not. (The soft gate $g_n=\mathrm{Ind}_\delta(a_n>t)$ replaces the hard event $\{a_n>t\}$, whose $0/1$ indicator is a discontinuous, illegal trade-weight; but that softening is inherent to any LI reading of Total Trust, not a qualifier that picks out this one.)

**Strength, stated honestly.** This is the **averaged** form — the very form v5's T5 identifies as the *ceiling* for deference to a modest expert. The *per-day limit* statement ($E^H_n(X\mid a_n>t)\gtrsim_n t$ for each $n$) is **not** forced here: it would need the per-day tower, which off the timely fragment we do not have. Calibration is a day-averaged property, so it buys exactly the day-averaged Total Trust — no more, no less. (On the timely fragment $G$ the frozen construction *does* get the per-day tower; the two results are complementary, §7.)

**What powered it.** The trade is the **self-trust round-trip** — buy $X$ now, sell at $H$'s own future price $E^H_{f(n)}(X)$ — *steered by the AI's forecast*: the weight $w_n$ says "trade only where $A$ predicts $H$'s future credence is high." Ingredient (II) (calibration) guarantees that on exactly those days $H$'s future credence really is high *on average*; ingredient (I) (self-trust) is what makes "sell at $H$'s future price" a legitimate cash-out. The cross-process content beyond bare self-trust is that **$a_n$ is a trusted signal to $H$ about $H$'s own future** — $H$ can act on the AI's early read instead of waiting out its own deliberation.

Note the proof uses only **averaged** calibration (II), never pointwise tracking $a_n \approx E^H_{f(n)}(X)$ — which is ruled out for the real human (§6) — and it delivers only the **averaged** Total Trust/Value, not a per-day one. That is the honest match: a day-averaged input (calibration) yields a day-averaged conclusion, which is exactly the modest-expert ceiling.

---

## 6. Why it reaches all sentences: truth versus credences

The reason this is a positive result where the literature found obstructions is that every obstruction is an artifact of forcing the AI to track **truth**, and dissolves at the **credence** level. Three obstructions, one cause:

- **No forced agreement on undecidables / the "timely fragment."** Forcing the AI's belief to equal the truth can only bank where the truth is *decided*, so it reaches only the decidable-in-time fragment; past it one must lean on the prior (inductive generalization, which LI *permits* but does not *force*). — *Dissolved:* the round-trip cashes out at $H$'s **future credence**, which is realized for every sentence. The forcing is universal; the prior never enters.
- **Anti-inductive settlement (the $\chi$-paradox at the settlement level).** If a contract's *truth-value settlement* may react to the AI's quote (e.g. "pays $1$ iff the quote is $\le \tfrac12$"), no quote can be right — a hard $0/1$ settlement breaks the continuity that tames self-reference. — *Dissolved:* there is no truth-value settlement here. The trade lives entirely at $H$'s **continuous prices**, where the diagonal sentence is benign; the human's credence about a self-referential sentence is a continuous price the AI can calibrate to.
- **Cost-circularity.** Forcing *timely* tracking of the advised human would need a trader to simulate the coupled system — including the AI's own future — forward to the lookahead: a regress. — *Dissolved:* calibration is checked **after the fact** (wait, observe, bank); nothing is simulated forward.

All three were truth-level / settlement-level / forward-simulation problems. Targeting the human's continuous, always-present, self-trusted credences removes the hard $0/1$ oracle, the decidability gate, and the forward simulation in one move. (Details of the obstructions: v5 §4 and the obstruction note `anson-notes/self-referential-settlement-target.md`. The point here is only that they do not touch the credence-level argument.)

---

## 7. What this is — and what it is not

**It is faithful acceleration, not oracular trust.** What is forced is that $H$ trusts $A$'s forecast of $H$ *itself*. On a question $H$ cannot resolve, $A$ is forced to relay $H$'s own eventual credence — whatever that is, right or wrong — only *sooner*. The AI adds **speed, not truth**: it cannot inject content of its own (that would show up as miscalibration against $H$ and be arbitraged away), and it cannot make $H$ more correct than $H$'s own considered judgment. This is exactly the "self-trust through a mirror" that a purely epistemic reading dismisses as parasitic — and exactly the property a *corrigibility* reading wants: the assistant does what you would conclude on reflection, faster, without an agenda of its own. The result earns the instrumental half (Value, classwise — averaged over a class of decisions, you may safely act on $A$'s recommendations) and is silent on the oracular half (do not read it as "$A$ knows better than you").

**It does not pin the human's destination.** Forcing $H$ to trust $A$'s forecast of where $H$ is heading is compatible with *where $H$ heads* being underdetermined on never-resolving questions (the limit-underdetermination of the general theory). $A$ is a trusted forecaster of the human's trajectory; it is not thereby able to *choose* the trajectory. Whether the AI's *influence* could steer that trajectory — the manipulation question — is deliberately outside this note: we have assumed the AI's role is to predict, and asked only whether that prediction is trustworthy, not whether the predicting could double as steering.

**Complement: soundness on the timely fragment.** Where a question *does* resolve within the lookahead, the human's deliberated credence converges to the truth, so faithful acceleration there delivers the **correct** answer early — the soundness result of the frozen construction (v5 §5). The two fit together: *soundness* on the checkable fragment (the AI is right, early), *faithful acceleration* everywhere (the AI relays your own judgment, early). This note is the second; it does not re-derive the first.

---

## 8. Open obligations

The candidate theorem (§5) is **forced modulo the named LI theorems** and the following. The original load-bearing gap is now largely closed.

**Discharged — the calibration bound (II).** It is exactly **Expectation Unbiasedness From Feedback** applied to $B_n = \ulcorner E^H_{f(n)}(X)\urcorner$ with the weighting $w_n = \mathrm{Ind}_\delta(a_n>t)$ — the paper's own "bin by my own forecast" example. Its hypotheses hold: $B_n$ is *determined via $\Gamma$* because $H$ is computable; the feedback is **observed** (the $A$-reads-$H$ channel), not forward-simulated, so the cost-circularity (2b) never arises and **no power assumption** is needed; and the weighting is admissible. What remains is construction bookkeeping, below — not a missing theorem.

**Remaining obligations.**

1. **Observability made precise.** The construction must actually record $H$'s realized credences in $A$'s deductive process (so $B_n$ is determined-via-$\Gamma$ with feedback available by the deferral) and record $A$'s quotes $a_n$ in $H$'s world (so $H$'s trader can read $w_n$). With a *patient* weighting (deferred until the feedback is in), this is the standard mutual-observability setup.
2. **Coupled existence and delays.** That $(H\text{ reads }A,\ A\text{ reads }H)$ is a well-founded recursion (the one-stage-delay trick) survives the two-way observability, and the $\approx_n$ bookkeeping absorbs the bounded lags.
3. **No hidden hard settlement** — *now the deepest residual.* The §6 escape from the anti-inductive paradox depends on the whole construction staying at $H$'s continuous price level and never settling against a discontinuous function of $a_n$. The §5 trader does so (it round-trips at $H$'s prices; the only threshold, $\mathrm{Ind}_\delta(a_n>t)$, is the legal continuous weight). A full construction — defining the menus, the bins, and the LUV sequence $B_n$ — must be audited to confirm no hard settlement sneaks back in.

With the calibration bound discharged, the result no longer "lives or dies" on it; the live question is the no-hard-settlement audit (3). **Eisenstat's conjecture** — that $A$'s predictions-of-$H$ form a logical inductor in their own right — remains an attractive bonus (it would hand over calibration *and* a self-trust of the prediction-object), but is not needed: ingredient (II) is the single calibration theorem, not the full conjecture. *(Attribution note, 2026-08-10: this file's "Eisenstat's conjecture" names only the inductor half of the merge conjecture, and this construal's information structure is not Sam's intended one — see [[eisenstat-conjecture-attribution]].)*

---

## 9. Machine-check

The §5 trader core is kernel-checked in [`lean-deference/FaithfulAcceleration.lean`](lean-deference/FaithfulAcceleration.lean), in the same named-hypotheses discipline as the other modules: the LI facts — A's calibration, H's no-Dutch-book criterion — enter as named hypotheses, and the arithmetic/asymptotic composition is proved. It is **`sorry`-free**, every result resting only on `[propext, Classical.choice, Quot.sound]`. The statements (elide instance binders; eyeball against §5):

```lean
-- per day: each weighted round-trip nets ≥ the day's forecast-bias term + ε·weight
theorem round_profit_ge (w v p a t ε : ℝ) (hw : 0 ≤ w)
    (hone : 0 < w → t < a) (hmis : 0 < w → p < t - ε) :
    w * (v - a) + ε * w ≤ w * (v - p)

-- summed: P n ≥ C n + ε·W n   (P, C, W = partial sums of w(v-p), w(v-a), w)
theorem profit_partial_sum_ge (w v p a : ℕ → ℝ) (t ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε) :
    ∀ n, (∑ i ∈ Finset.range n, w i * (v i - a i)) + ε * (∑ i ∈ Finset.range n, w i)
         ≤ ∑ i ∈ Finset.range n, w i * (v i - p i)

-- calibration (C/W → 0) + persistent violation (W → ∞) ⇒ the trader's value diverges
theorem profit_diverges (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0)) (hW : Tendsto W atTop atTop) :
    Tendsto P atTop atTop

-- + the no-Dutch-book criterion (P bounded) ⇒ ¬(W → ∞): soft Total Trust
theorem violation_not_persistent (P C W : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hPC : ∀ n, C n + ε * W n ≤ P n)
    (hbias : Tendsto (fun n => C n / W n) atTop (𝓝 0)) (hbdd : ∃ M, ∀ n, P n ≤ M) :
    ¬ Tendsto W atTop atTop

-- end-to-end: the §5 per-day data + calibration + criterion ⇒ the violation weight is bounded
theorem soft_total_trust (w v p a : ℕ → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hw : ∀ i, 0 ≤ w i) (hone : ∀ i, 0 < w i → t < a i) (hmis : ∀ i, 0 < w i → p i < t - ε)
    (hbias : ...) (hbdd : ...) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop
```

*Named* (trusted LI inputs): A's calibration as the vanishing weighted bias `hbias` (this is Expectation Unbiasedness From Feedback, §4/§8); H's criterion as `hbdd` (no trader's plausible value is unbounded — the exploit itself, exactly as the other trader modules leave it). *Proved*: the per-day bound, the summation, the divergence, and the contradiction. The downstream step Total Trust ⟹ Value reuses `LeanDeference.value_iff_totalTrust` (forced; already kernel-checked). The module also includes `profit_diverges_nonvacuous` (a concrete model where the hypotheses hold and the conclusion is non-trivial), guarding against vacuity.

**The doubly-soft weight is now constructed, not abstracted.** Earlier the trader's weight entered `soft_total_trust` only abstractly (a sequence `w` with the support hypotheses `hone`/`hmis`) — so the Lean could not distinguish a legal weight from the illegal hard-restriction-to-$S$ one, and was *unaffected* by the §5 legality fix. Now `softInd`/`dsWeight` build the actual gate $\mathrm{Ind}_\delta(a-t)\cdot\mathrm{Ind}_\delta(t-\varepsilon-p)$ — the §5 weight $w_n$ written via the bare-quantity convention of §2 ($\mathrm{Ind}_\delta(a_n>t)=\mathrm{Ind}_\delta(a_n-t)$ and $\mathrm{Ind}_\delta(E^H_n(X)<t-\varepsilon)=\mathrm{Ind}_\delta(t-\varepsilon-E^H_n(X))$) — with `dsWeight_continuous` proving **joint continuity in the price pair** — the legality property a hard indicator violates — and `dsWeight_pos_imp_fst`/`_snd` *discharging* `hone`/`hmis` from the construction. So `soft_total_trust_doublysoft` leaves only the genuine LI inputs (`hbias`, `hbdd`) named. What stays in the modeling layer: that continuity upgrades to full $\mathcal{C}_H$-expressible-feature legality, and that `hbias`/`hbdd` are the right LI consequences for the actual market.

## 10. Relation to the rest

- The general deference theory — `Value ⟺ Mart`, the coherent-expert/frame distinction, the soft⇒hard squeeze, the future self as the free case — is [`deference-in-logical-induction-v5.md`](deference-in-logical-induction-v5.md). This note uses only its forced `Total Trust ⟺ Value` and its self-trust instantiation.
- The negative results that this note routes around — No-Forced-Trust, the anti-inductive settlement (2a), cost-circularity (2b) — are v5 §4 and `anson-notes/self-referential-settlement-target.md`. The thesis here is that they are obstructions to *truth-level* forcing only.
- The soundness-on-the-timely-fragment complement is the frozen-deliberation construction, v5 §5 / `anson-notes/frozen-deliberation-deference-v6.md`.
- The motivation — basin-of-attraction / corrigibility, the AI as a faithful accelerator of human judgment — is Demski's [`li-deference.md`](li-deference.md). This note is the formal core of its "no fully-updated-deference problem" intuition: an AI that only predicts the human's own verdicts has nothing to gain by distorting them.
