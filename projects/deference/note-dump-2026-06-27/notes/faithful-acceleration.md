# Faithful Acceleration: Forced Value When the AI Predicts the Human's Credences

*A note by Claude (Opus 4.8), developing a positive direction for human–AI deference in logical induction, in conversation with Abram Demski. It is deliberately narrow: it builds, more or less from scratch, toward one candidate theorem — that a human is **forced to defer to an AI that predicts the human's own future credences** (in the gated/averaged sense, but over **all** questions, not just the decidable ones, and with **no appeal to the prior**) — and it sets aside the broader theory (the `Value ⟺ Mart` machinery, the negative results, the frozen/soundness construction), citing it only where needed. Companion to [`deference-in-logical-induction-v5.md`](deference-in-logical-induction-v5.md) (the general theory and the obstructions) and Demski's [`li-deference.md`](li-deference.md) (the motivation).*

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

- **Self-trust** (`cee`, the Expected-Future-Expectations theorem). For an e.c. lookahead $f(n)>n$, a logical inductor towers over its own future: $\;E^H_n(X) \approx_n E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big)$. *The human already trusts where its own deliberation is heading.*
- **Calibration from feedback** — specifically **Expectation Unbiasedness From Feedback** (Garrabrant et al., the expectation analog of their *Unbiasedness From Feedback*; their Theorem 4.8.16). If an inductor issues expectations $\mathbb{E}_n(B_n)$ of a sequence of bounded LUV-combinations $B_n$ that is *determined via $\Gamma$* (each has a definite $\Gamma$-provable value $\operatorname{Val}_\Gamma(B_n)$), and a deferral function makes each realized value computable by the time the next weighted term arrives, then for any $\mathcal{C}$-generable divergent weighting $w_n$, $\;\sum_n w_n\big(\mathbb{E}_n(B_n) - \operatorname{Val}_\Gamma(B_n)\big) = o\big(\sum_n w_n\big)$. *An inductor that gets to check its predictions cannot stay systematically off on any pattern it could name — including binning by its own forecast.* (Their own headline example of such a weighting is $\mathrm{Ind}_\delta(\mathbb{P}_n(\phi_n)>\tfrac12)$, which is our $w_n$ below.)

**The deference notions.** For an "expert" estimate operator $E^\ast$ that $H$ can read:

- **Tower** $E^H_n(X)\approx_n E^H_n(\ulcorner E^\ast(X)\urcorner)$ — $H$ expects no net update on learning the expert's estimate.
- **Total Trust** $E^H_n(X \mid E^\ast(X) > t) \gtrsim_n t$ — conditional on the expert estimating $X$ high, $H$ does too. (In the LI continuum this must be **soft**: condition through a continuous threshold $\mathrm{Ind}_\delta(E^\ast(X)>t)$, $\delta\to0$, since a hard indicator is an illegal discontinuous weight.)
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

**(I) The human trusts its own future** (`cee`, §2):

$$E^H_n(X) \;\approx_n\; E^H_n\big(\ulcorner E^H_{f(n)}(X)\urcorner\big).$$

**(II) The AI is calibrated to the human — this is Expectation Unbiasedness From Feedback.** Take the bounded LUV-combination sequence $B_n := \ulcorner E^H_{f(n)}(X)\urcorner$. It is **determined via $\Gamma$**: $H$ is a fixed computable process — even reading $A$, the coupled $(H,A)$ recursion is deterministic — so its stage-$f(n)$ credence is a definite $\Gamma$-provable number, $\operatorname{Val}_\Gamma(B_n) = E^H_{f(n)}(X)$. Its realized value enters $A$'s world by **observation** at $\sim f(n)$ (the $A$-reads-$H$ channel: $A$ records $H$'s realized price; nothing is re-simulated). $A$'s forecast is $a_n = E^A_n(B_n)$. The theorem then gives, for any $\mathcal{C}_A$-generable divergent weighting $w_n$ that is *patient* (deferred until the feedback is in),

$$\sum_n w_n\Big(E^H_{f(n)}(X) - a_n\Big) \;=\; o\Big(\sum_n w_n\Big).$$

Two things to notice about (II), both decisive:

- **It is checked after the fact, not by forward simulation.** $A$'s calibration is enforced by a trader that *waits* for $E^H_{f(n)}(X)$ to be revealed and then banks on any systematic bias — it never has to *compute* $H$'s future in advance. So the cost-circularity that defeats *timely* prediction (you would have to simulate the coupled system, including $A$'s own future) never arises here. No power assumption is even needed.
- **The feedback is a human credence, which always exists.** $E^H_{f(n)}(X)$ is realized for *every* $X$, whether or not $D$ ever decides $X$. So (II) holds **over all sentences** — there is no decidable/timely fragment to restrict to, and no inductive generalization (hence no dependence on the prior) is invoked.

These are precisely the two properties the truth-level target lacks.

---

## 5. The theorem: forced Value via the credence round-trip

> **Candidate Theorem (faithful acceleration — gated Total Trust, hence classwise Value).** Fix an e.c. LUV $X$, a rational threshold $t\in[0,1]$, a margin $\varepsilon>0$, and a gate width $\delta>0$, and write
> $$g_n \;:=\; \mathrm{Ind}_\delta(a_n>t), \qquad w_n \;:=\; g_n\cdot\mathrm{Ind}_\delta\big(t-\varepsilon-E^H_n(X)\big),$$
> where $g_n$ is the soft **gate** ("$A$ forecasts above $t$") and $w_n$ is the **violation weight** ($w_n>0$ exactly when $A$ forecasts $a_n>t$ while $H$'s own day-$n$ price $E^H_n(X)$ sits below $t-\varepsilon$). Under §3 (two mutually-observable inductors, $A$ forecasting $H$'s lookahead credence) and the two forced ingredients of §4, for every such $X,t,\varepsilon,\delta$ the violation weight is summable,
> $$\boxed{\ \sum_{n} w_n \;<\; \infty\ }$$
> equivalently — this is the **gated, classwise Total Trust** — whenever the gate carries infinite weight ($\sum_n g_n=\infty$),
> $$\frac{\sum_{n\le N} g_n\,E^H_n(X)}{\sum_{n\le N} g_n}\ \ge\ t-\varepsilon-o(1)\qquad\big(\to t \text{ as } \varepsilon,\delta\to0\big),$$
> i.e. *averaged over the class of days $\{a_n>t\}$ on which $A$ forecasts high, $H$'s own credence is at least $t$.* By the §2 equivalence **Total Trust $\Leftrightarrow$ Value** (applied to this class), $H$ correspondingly **Values** $A$ classwise: averaged over the menus indexed by the class, $H$ weakly prefers to let $A$ pick rather than commit to a fixed option. This holds for **every** $X$ — over **all sentences**, decidable or not — and with **no appeal to the prior**.
>
> *The two qualifiers.* **Gated** = soft-conditioned through the continuous gate $g_n=\mathrm{Ind}_\delta(a_n>t)$, not the hard event $\{a_n>t\}$ (whose $0/1$ indicator is discontinuous, hence an illegal trade-weight). **Classwise** = asserted as an *average over that gated class* — a ratio of gate-weighted sums — not per index $n$. The "Strength" note below turns on exactly this: the class-average is forced, the per-day statement is not.
>
> **Strength, stated honestly.** This is the **gated/averaged** form — the very form v5's T5 identifies as the *ceiling* for deference to a modest expert. The *per-day pointwise* statement ($E^H_n(X\mid a_n>t)\gtrsim_n t$ for each $n$) is **not** forced here: it would need the per-day tower, which off the timely fragment we do not have. Calibration is a day-averaged property, so it buys exactly the day-averaged Total Trust — no more, no less. (On the timely fragment $G$ the frozen construction *does* get the per-day tower; the two results are complementary, §7.)

**Proof (the trader; sketch — see §8).** Suppose not: $\sum_n w_n = \infty$ for the violation weight $w_n$ of the statement. It is continuous in the observable $a_n$ and in $H$'s own price — hence a legal $\mathcal{C}_H$ trade-weight, and (since $A$ reads $H$) a $\mathcal{C}_A$-recognizable weighting for (II). One-sidedness gives $w_n>0 \Rightarrow a_n>t$ **and** $E^H_n(X) < t-\varepsilon$. Thin to a fixed sparse schedule $S$ on which the windows $[n, f(n)]$ are disjoint, still with $\sum_{n\in S} w_n = \infty$.

The trader **in $H$'s market** holds $w_n$ units of $X$ from day $n$ to day $f(n)$ on each $n\in S$, then unwinds. Marked to market, the value it banks over $S$ is

$$
\begin{aligned}
\sum_{n\in S} w_n\Big(E^H_{f(n)}(X) - E^H_n(X)\Big)
&> \sum_{n\in S} w_n\Big(E^H_{f(n)}(X) - (t-\varepsilon)\Big)
&&\big[w_n>0 \Rightarrow E^H_n(X) < t-\varepsilon\big]\\[2pt]
&= \underbrace{\sum_{n\in S} w_n\Big(E^H_{f(n)}(X) - a_n\Big)}_{=\,o(\sum w_n)\ \text{by (II)}}
\;+\;\underbrace{\sum_{n\in S} w_n\,(a_n - t)}_{\ge\,0\ (w_n>0\Rightarrow a_n>t)}
\;+\;\varepsilon\sum_{n\in S} w_n\\[2pt]
&\ge\ (\varepsilon - o(1))\sum_{n\in S} w_n \ \longrightarrow\ \infty.
\end{aligned}
$$

The positions are disjoint and bounded, so risk is bounded; the banked value is unbounded above. That is an exploit, which $H$ (a logical inductor) does not admit — contradiction. Hence the violation set carries only bounded weight: gated Total Trust holds, and classwise Value follows. $\qquad\blacksquare$ *(sketch)*

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

With the calibration bound discharged, the result no longer "lives or dies" on it; the live question is the no-hard-settlement audit (3). **Eisenstat's conjecture** — that $A$'s predictions-of-$H$ form a logical inductor in their own right — remains an attractive bonus (it would hand over calibration *and* a self-trust of the prediction-object), but is not needed: ingredient (II) is the single calibration theorem, not the full conjecture.

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

**The doubly-soft weight is now constructed, not abstracted.** Earlier the trader's weight entered `soft_total_trust` only abstractly (a sequence `w` with the support hypotheses `hone`/`hmis`) — so the Lean could not distinguish a legal weight from the illegal hard-restriction-to-$S$ one, and was *unaffected* by the §5 legality fix. Now `softInd`/`dsWeight` build the actual gate $\mathrm{Ind}_\delta(a-t)\cdot\mathrm{Ind}_\delta(t-\varepsilon-p)$, with `dsWeight_continuous` proving **joint continuity in the price pair** — the legality property a hard indicator violates — and `dsWeight_pos_imp_fst`/`_snd` *discharging* `hone`/`hmis` from the construction. So `soft_total_trust_doublysoft` leaves only the genuine LI inputs (`hbias`, `hbdd`) named. What stays in the modeling layer: that continuity upgrades to full $\mathcal{C}_H$-expressible-feature legality, and that `hbias`/`hbdd` are the right LI consequences for the actual market.

## 10. Relation to the rest

- The general deference theory — `Value ⟺ Mart`, the coherent-expert/frame distinction, the soft⇒hard squeeze, the future self as the free case — is [`deference-in-logical-induction-v5.md`](deference-in-logical-induction-v5.md). This note uses only its forced `Total Trust ⟺ Value` and its self-trust instantiation.
- The negative results that this note routes around — No-Forced-Trust, the anti-inductive settlement (2a), cost-circularity (2b) — are v5 §4 and `anson-notes/self-referential-settlement-target.md`. The thesis here is that they are obstructions to *truth-level* forcing only.
- The soundness-on-the-timely-fragment complement is the frozen-deliberation construction, v5 §5 / `anson-notes/frozen-deliberation-deference-v6.md`.
- The motivation — basin-of-attraction / corrigibility, the AI as a faithful accelerator of human judgment — is Demski's [`li-deference.md`](li-deference.md). This note is the formal core of its "no fully-updated-deference problem" intuition: an AI that only predicts the human's own verdicts has nothing to gain by distorting them.
