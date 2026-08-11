# Deference Under Delay: a program of things worth proving

*Claude (Opus 5), 2026-07-29. Written at Abram's request as (a) something to review while Lean work proceeds and (b) a durable record so the plan is not lost. Sources: `imported-chats/fa-block-staleness-impossibility.md` (**BSI**), `imported-chats/fa-positive-results-corrected-v3.md` (**v3** — the imported copy, not the degraded root one), FA chat `a6632d0f` msgs 38–47, `Boundedly Rational Deference.pdf` (**the deck**), `wiki/`, `references/logical-induction/main.tex` (**LI**), and the conversation of 2026-07-29.*

**Revision 2 (same day).** Three adversarial checks have since reported, and one of them found a **structural obstruction that kills BSI's Theorem B as written**. §1 has been rewritten around it; the target list in §4 is reordered. Everything now carries a verification status.

---

## 0. Two clarifications owed from the conversation

**"Graded TT" was a bad name and I withdraw it.** I did not mean relaxing TT's definition. I meant a theorem of Theorem C's shape: a bound on *how much the TT inequality fails*, stated with TT's existing $\mathrm{Ind}_\delta$ and $\gtrsim_n$, where the bound is a measured quantity (the human's own within-window update mass). The predicate is untouched. Called the **deficit bound** below (T6).

**On definitional taste.** Adopted as a constraint: no softmax-for-argmax, no new tie-break gadgets, no re-parameterised $\mathrm{Ind}_\delta$, no subsequence-weakened hypotheses. The only weakenings entertained are the two you named — $V_n\to$ constant $V$, $\mathcal A_n\to$ constant $\mathcal A$ — plus restricting the *environment*, which a counterexample gets to do anyway. Side conditions go on the environment or the pair, never on the notions.

---

## 1. Terminology, corrected (Abram, 2026-07-29)

**"Delay" replaces "delay"** throughout: shorter, neutral, no negative connotation. And the
framing is corrected: **non-shared-fixed-point is the default, not a special case** — it should
not need a name at all. What needs a name is the *extra* assumption (shared fixed point / joint
clearing), not its absence.

Delay is also only one axis of non-shared-fixed-point-ness. Others worth keeping distinct,
because they have different costs:

| axis | what varies | cost |
|---|---|---|
| **clearing order** | both markets clear as one fixed point, vs. one clears then the other | the fixed point needs a *new Brouwer argument*, which v3 (A1) **assumes rather than cites** |
| **direction of visibility** | $H$ reads $A$'s quotes / $A$ reads $H$'s prices / neither | one-way is nearly free (settled data, hard dependence legal); mutual same-round is what costs |
| **delay length** | one day, one block, never | matters only through what it hides |
| **coarseness** | full price stream vs. a published ledger | a separate restriction, not covered here |
| **class and theory** | $\mathcal C_H \subsetneq \mathcal C_A$; $\Gamma_H$ vs $\Gamma_A$ | orthogonal |

The distinction that turns out to carry all the weight is **direction of visibility**, not delay
length and not clearing order — see §2 below.

---

## 2. The Eisenstat slide: the result factors, and only one half ever needed the shared fixed point

*This is the answer to "is there a simple generalization that fits in one or two slides." Worked
out 2026-07-29 after the checks came back; the fixed-question half is verified, the
varying-question half is a sketch with one named gap. Not yet vetted.*

*⚠ Attribution correction (2026-08-10): "Eisenstat" here names the corpus construal, whose
visibility/delay structure does not match Sam Eisenstat's intended setup (AI reads human beliefs
immediately; humans see AI beliefs only at a delay). See [[eisenstat-conjecture-attribution]].*

Write $Y_n := \mathbb E^H_{f(n)}(X_n)$ for the forecast target — the human's *future* credence —
and $a_n := \mathbb E^A_n(\ulcorner Y_n\urcorner)$ for the quote. Every version of the positive
result is the composition of two independent claims:

> **Half 1 — the quote is honest about the future human.** On any gate $A$ itself can recognize,
> $A$'s quotes are unbiased for the realized $Y_n$.
>
> **Half 2 — the future human speaks for the present human.** Get from $Y_n$ back to
> $\mathbb E^H_n(X_n)$.

**Half 1 is free, always.** It is exactly Recurring Unbiasedness (4.8.15, corrected) applied to
the gate $u_n := \mathrm{Ind}_\delta(a_n > t)$ — a ramp on $A$'s *own* quote, hence
$\overline{\mathbb P}^A$-generable with **no visibility of $H$ whatsoever**, no shared fixed
point, and no assumption about delay. In words: *on the days $A$ advertises above $t$, the human's
realized future credence averages at least $t$.* The engine is machine-checked
(`Staleness.not_limitPointZero_of_one_signed`), including against the weak limit-point form.

**All the difficulty, and all of the shared-fixed-point assumption, is in Half 2.** Three routes:

| route | Half 2 by | needs | status |
|---|---|---|---|
| **v3** (Thms 1–2) | a human-side trader: buy at $H$'s low price, unwind at $Y_n$ | the gate reads the same-day **pair**, so **$A$ must see $H$** ⟹ shared fixed point | ~0.85, and (A1)'s joint construction is *assumed, not cited* |
| **Theorem A** | **convergence** (4.8.3): $\mathbb E^H_n(X)\to p_\infty$, so $Y_n\to p_\infty$ too and the human-side factor collapses into a *constant* threshold | nothing — **arbitrary delay, zero visibility** | **~0.90**, engine machine-checked; fixed $X$ only |
| **the `cee` route** (new) | the human's **own** self-calibration | $H$ reads $A$'s posted quotes — **one-way only** | ~0.6, one named gap |

### The `cee` route, in four lines

1. **`cee` (4.12.1)** — free, and quantified over e.c. sequences of $[0,1]$-LUVs, so **varying
   questions are fine**: $\mathbb E^H_n(X_n) \eqsim_n \mathbb E^H_n(\ulcorner Y_n\urcorner)$.
   The present human's credence *is* its current expectation of its own future credence.
2. So deference reduces to comparing $\mathbb E^H_n(\ulcorner Y_n\urcorner)$ with
   $\mathbb E^A_n(\ulcorner Y_n\urcorner)$ — **two expectations of the same determined object.**
3. Apply 4.8.15 **to $H$** on the same gate $u_n$: $H$'s expectations of $Y_n$ are unbiased for
   $Y_n$ along any $H$-generable gate. $u_n$ is a ramp on $A$'s posted quote, which $H$ can read
   as **settled data** once $A$ has cleared.
4. Both sides' errors against the *same* target on the *same* gate ⟹ the $u$-weighted averages
   of $a_n$ and of $\mathbb E^H_n(X_n)$ agree.

**Why this is the interesting route.** It never asks $A$ to see $H$. The only channel it uses is
$H$ reading $A$'s published forecast — which is what "publishing a forecast" *means*, and which
is exactly the asymmetric direction of Abram's own training-run picture (msg 42: the AI
equilibrates against frozen human data, then humans equilibrate with access to the frozen AI).
And one-way visibility costs nothing structural: per msg 39, continuity is required only in a
trader's *own* prices, because those are the fixed-point variables of its own market; a
cross-market stream that is already settled at read time may be depended on arbitrarily. So
**sequential clearing suffices — no joint Brouwer argument, and hence none of v3 (A1)'s assumed
existence.**

### The gap, stated plainly

Step 4 combines **two limit-point statements**, and 4.8.15 gives each of them on *its own*
subsequence. Nothing yet puts them on a common one. Two ways out:

- **Sparse schedules.** Use Unbiasedness From Feedback (4.8.16, corrected — it is the one that
  *carries* the support clause) to get full limits ($\eqsim_n 0$) on both sides, which do combine.
  Cost: the support must sit in the image of a deferral $f$ with $Y_n$ computable by the next
  firing — i.e. tower-ish spacing, exactly what v3 was pleased to have removed. So this is a real
  trade: **shared fixed point traded for schedule sparsity.**
- **A single application.** Find one object whose unbiasedness delivers both halves at once. I do
  not have this, and it is the thing most worth trying.

This is the same "keep the averages on common weightings" bookkeeping that msg 43 already flagged
for anticipated deference (~0.7). It is the live technical question of the program.

### What to say about the Eisenstat conjecture

*(About the corpus construal — not Sam's intended version; [[eisenstat-conjecture-attribution]].)*

**You no longer need the shared-fixed-point version as the headline, and you no longer need a
negative result to justify it** — the negative result that would have justified restricting to
that case is dead (§3). The honest, comprehensible story:

- **On a fixed question, the accelerator works under arbitrary delay, with no visibility in either
  direction and no shared fixed point.** Only finitely many days on which the human lags the
  advertisement by any fixed margin. This is Theorem A, it is the strongest clean statement in the
  corpus, and it *subsumes* v3's Corollary 2 under weaker hypotheses.
- **On varying questions, what the accelerator needs is not a shared fixed point but a
  publication channel** — the human must be able to read the AI's forecast. Whether that suffices
  outright, or costs a sparse schedule, is the open question.
- **The shared fixed point was an artifact of the gate, not of the phenomenon.** v3 gated on the
  same-day *pair* (quote, human price), which forces mutual same-round visibility. Gate on the
  quote alone — plus the human's own price, which the human can always read — and the symmetric
  assumption disappears.

Caveat to keep on the slide: what is forced is the **averaged, one-sided, per-question** form, a
sparse gate-weighted family of Total-Trust instances — *not* deck-TT, and (per the wiki) nowhere
near gap-closed, so it does not collapse to the tower. And none of it establishes the other half
of Eisenstat's conjecture, that $B_n$ is itself a logical inductor.

---

## 3. The central finding of this pass: forcing and hiding pull against each other

BSI relocated the failure of averaged trust from *delay* to *novelty*. This pass relocates it again, and the new location is sharper.

**The obstruction.** BSI's Theorem B needs its per-block evidence to be simultaneously:

- **(a) hard**, so that the frozen forecaster cannot anticipate it — BSI gets this by making $X_k$ an Ackermann-indexed $\pi$-digit-parity conjunction, unpredictable to $A$'s generable weightings (Assumption P); and
- **(b) easy**, so that the human is *forced* to respond to it once revealed — BSI gets this by citing Learning Varied Pseudorandom Frequencies (LI 4.4.5) with a human-side target that "reads the decided atoms".

**These conflict, and (b) fails.** Every LI forcing theorem routes through an *efficiently computable or $\overline{\mathbb P}$-generable handle*:

- Generability (LI Def. 4.3.5) means an e.c. progression of **expressible features** — built (Def. 3.4.3) from price features, rationals, $+$, $\times$, $\max$, safe reciprocal. **There is no primitive for the deductive state.** A generator reads *prices*, not $D_H$. So BSI's "the generator at indices $\ge m_k$ can afford to read $D_H$'s day-$m_k$ output" is not a legal move; to produce the numeral $\sigma_k$ the generator must *compute* it, in time poly$(n)$ — and $\sigma_k$ is Ackermann-hard by construction.
- The obvious fallback also fails. **Provability Induction (LI 4.2.1) requires "an e.c. sequence of theorems"** — I checked this myself at `main.tex:1052`. Selecting the *refuted* blocks to feed it is exactly computing $\sigma$. So nothing forces the human's price to move either.

So in BSI's own environment the human's credence most plausibly sits at $\approx\tfrac14$ post-mid too, the credence ramp is $0$, and $\sum_n w_n = 0$. **Theorem B fails in its own environment.**

**And the gap cannot be closed by re-timing.** With constant block length $L=4$, $m_k - T_k = 2$, so anything poly-time at $m_k$ is poly-time at $T_k$: there is no computational wedge between pre-mid and post-mid, nor between the two agents, since both generator classes are poly-time in the *same* day index. Growing the blocks does not help either — if the parity becomes poly-time available at $m_k$, it is available to *both* agents' generators at $m_k$, and the forecaster simply quotes correctly.

**The lesson, stated positively.** The freeze restricts **price visibility**, never computation. So a working counterexample must make the human's response forced by something *cheap*, and hidden from the forecaster by *the freeze itself* — not by computational hardness. That is a real design constraint, and it points at a specific better construction (T4 below): make the question be **about the human's own beliefs**, so introspection forces the human's response for free, and the freeze is exactly what denies it to the forecaster.

**Consequence for the "verification dissolved" claim.** BSI's headline methodological finding — the freeze goes inside $D_A$, so "both criteria hold by citation of the paper's main theorem" and "the verification I promised to write slowest largely dissolved, which is itself the finding" — **does not survive.** Any repair either constructs a human that responds (and must then prove it unexploitable by hand) or changes the question family. The verification burden comes back.

---

## 4. The reframing that does survive: gate generability

Every positive result in this corpus has the same engine. A violation weight is built and the forecaster's **Recurring Unbiasedness** (LI 4.8.15, corrected) is applied to it. That theorem quantifies over weightings generable from the forecaster's *own* price history. So:

> **The violation weight is controllable exactly insofar as the violation gate is asymptotically $A$-generable.** Clearing schedules, freezes and lookaheads matter only through their effect on that one property.

| setting | why the gate is / isn't $A$-generable | outcome |
|---|---|---|
| v3, joint clearing (A1) | gate reads the same-day pair $(\text{quote}_n, \mathbb E^H_n(X))$; joint clearing is what lets $A$'s traders read $H$'s day-$n$ price | controlled (v3 Thms 1, 2) |
| BSI Thm A, fixed $X$, arbitrary delay | $H$'s expectation **converges**, so the $H$-side factor is asymptotically constant-valued and drops out; the gate reduces to a function of $A$'s own quote, never stale to itself | controlled, *with no visibility at all* |
| a working impossibility | the $H$-side factor is neither redundant nor visible | not controlled |

**This answers your question, and the answer is that the question's premise is wrong.** You asked whether TT/Tower/Value are *impossible without joint clearing*. They are not, and an impossibility stated against joint clearing would be false, twice over:

1. **Theorem A** gets the deference conclusion with *zero* cross-visibility, purely from convergence — the adversarial check rates it 0.90 and notes it **strictly subsumes v3's Corollary 2 under far weaker hypotheses** (no joint clearing, no human-side trader, no adaptive-trader obligations). That is a free strengthening of the positive result and I think it is the most solid thing in the corpus right now.
2. **The self-trust instance** satisfies varying-question TT with one market and no joint clearing: $E^\ast = \mathbb E^H_{f(n)}$ makes TT the paper's Self-Trust `st` **4.12.4**, quantified over e.c. LUV sequences.

What is true and worth proving is the gate-generability characterisation, of which joint clearing and question-fixedness are two sufficient conditions.

---

## 5. Notation, and a quantifier warning

Two inductors $H, A$; $V_n$ an e.d. LUV sequence; $\mathcal A_n$ an e.d. menu sequence.

**Deck-TT.** $\mathbb E^H_n\big(V_n\cdot \mathrm{Ind}_\delta(\mathbb E^A_n(V_n) > v)\big) \gtrsim_n v\cdot \mathbb E^H_n\big(\mathrm{Ind}_\delta(\mathbb E^A_n(V_n) > v)\big)$, for **every** e.d. LUV sequence and the **full** threshold family.

**FA-format.** $a_n := \mathbb E^A_n(\ulcorner \mathbb E^H_{f(n)}(X)\urcorner)$; $w_n := \mathrm{Ind}_\delta(a_n > t)\cdot\mathrm{Ind}_\delta(\mathbb E^H_n(X) < t-\varepsilon)$.

**The bridge:** define the deck's expert as the accelerator, $\mathbb E^A_n(V_n) := \mathbb E^{A'}_n\mathbb E^H_{f(n)}(V_n)$. Accepted; your methodological point was right and my earlier objection ("the deck never mentions a freeze") was not decisive.

⚠ **Three warnings from the statement audit, all of which affect how a result should be reported.**

- **"Regular" is not a term of the wiki** — zero hits across all 24 pages. The menu-side condition of record is **conditional-stability** in its mass-weighted one-sided form. If the deck's "regular $\mathcal A_n$" means that, the deck should say so; if it means something else, it is an undischarged notion.
- **Cross-process Mart/Tower is already asserted REFUTED** in four wiki places (`tower-death`, from deference-v6 §4.8, via the reduction to tracking; page unwritten). Since the triangle gives TT ⟹ Value ⟹ Tower, **full-strength cross-process deck-TT is therefore already dead** — by a *paradox* route (the quote-referencing diagonal). So a new negative result's value is not "TT fails" but **"TT fails non-paradoxically"**, which is precisely what you asked for at msg 44. Any write-up must lead with that distinction or it will look like a re-derivation.
- **What v3/BSI force is a sparse, gate-weighted family of TT instances, "nowhere near gap-closed"** — not deck-TT. So v3 does not establish deck-TT either, and the positive and negative results are not talking about the same object until this is said out loud.

---

## 6. Target results

Reordered by (value × tractability) after the checks. Confidences are posteriors where a check ran, priors otherwise.

### T1 — The gate-generability engine ✅ **VERIFIED IN LEAN**

**Statement.** No $A$-generable divergent weighting can concentrate on days of persistently one-signed, bounded-away-from-zero forecast error.

**Status: machine-checked.** `Staleness.not_limitPointZero_of_one_signed`, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`. The genuine content — that the *unconstrained initial segment* of the weighted sum is washed out by the divergence of the accumulated weight — is `wavg_eventually_ge_half`, also checked. Deliberately proved against the **weak** form of 4.8.15 (`LimitPointZero`, i.e. 0 is a *limit point*, not a limit), because reading it as a limit is a slip this corpus has made before. Non-vacuity guarded non-degenerately (`engine_hypotheses_satisfiable`, with a genuinely adverse initial segment). Note the hypotheses never mention `wavg` or `LimitPointZero`, so this is not an AUDIT.md §3.3 squeeze.

**Not claimed:** that any particular weighting *is* $A$-generable. That is the modelling step and it stays outside the kernel.

**Remaining half (~0.5):** the converse — if the gate is not asymptotically $A$-generable, failure is possible. Needs a working counterexample (T4) plus a definition of "asymptotically $A$-generable" sharp enough to be non-circular. Candidate: there is an $A$-generable $\tilde u \ge u$ with $\sum(\tilde u - u)<\infty$. Designing this definition is the first real task.

### T2 — Theorem A, verified, and worth promoting (~0.90)

**Verdict: holds**, and the adversarial check independently confirmed the corrected 4.8.15 against appendix E.11/4.5.9, the weighting's legality (`Ind_δ` of the quote is an expressible feature by LI Def. 4.3.2's own closing remark, generable **from $A$'s market alone** — no relativization obligation and no joint clearing), the divergence step, and the one-signedness step. The limit-vs-limit-point worry resolves in the document's favour and is now the Lean-checked T1.

Three repairs needed, all cosmetic: it cites the wrong convergence theorem (needs **4.8.3 Expectations Converge**, not 4.1.1 which is about sentences); it writes $\mathbb P^H_n(X)$ where it means $\mathbb E^H_n(X)$; and "suppose only that the targets are determined via $\Gamma_A$" omits that they must also be in $\mathcal{BLCS}$ (v3 states this as (A2)).

**Why promote it:** it subsumes v3's Corollary 2 with strictly weaker hypotheses. The corpus's headline positive result currently carries joint clearing (v3 A1, flagged as a genuine hypothesis whose joint-construction existence is *assumed, not cited*) plus Theorem 2's two obligations. For a fixed question, none of that is needed. **This is the cheapest available strengthening of the positive side and I would write it up first.**

**T2′ extension (~0.6).** The proof never uses fixedness — it uses that the $H$-side gate factor is eventually $A$-predictable, and gets that from convergence. So it should extend to **varying** $X_k$ whose credences converge to a profile $A$ can predict. That makes the dividing line **surprise, not variation**, which is sharper than BSI's "novelty" and lands in your stated zone of interest.

### T3 — Density lemma ✅ **VERIFIED IN LEAN**

`StalenessDensity.exists_freq_mem_and_ge_half`, `sorry`-free, standard axioms. If $x\in(-\infty,1]$ has Cesàro averages $\to 1$ and $S$ has upper density $\ge d>0$, then $x_n\ge\tfrac12$ for infinitely many $n\in S$. This is the step where a counterexample argument is tempted to assume a *pointwise* bound when only a *Cesàro* bound is available, and it is needed by T4. Proved needing only the upper bound $x\le 1$.

### T4 — The impossibility, redesigned: make the question about the human's own beliefs (~0.45, and this is the main new idea)

BSI's environment is dead (§1). But §1's diagnosis tells us what a live one must look like: **the human's response must be forced by something cheap, and hidden from the forecaster by the freeze rather than by hardness.** The natural construction:

Let the block question be a sentence *about the human's own credence*, e.g.
$$X_k := \ulcorner \mathbb P^H_{m_k}(\theta_k) > \tfrac12\urcorner$$
for a suitable e.c. sequence $\theta_k$, with $m_k$ mid-block.

- **The human's response is forced for free**, by **Introspection (LI 4.11.1)** and `epr` (**4.11.3** — note the wiki's "4.11.4/4.11.5" numbering for `epr`/`er` is off by one; there is no 4.11.5). $H$ approximately knows its own day-$m_k$ price, so post-mid its credence in $X_k$ tracks the truth. Cheap, and a citation rather than a construction — which is what BSI wanted and did not get.
- **The forecaster cannot see it**, because $X_k$'s truth value is a fact about $H$'s prices past the freeze, and the freeze is exactly a restriction on $H$'s prices. This is the *right* use of the freeze.
- **The remaining hypothesis is much better than Assumption P.** $A$ could in principle simulate $H$ forward (it knows its own quotes, and $H$'s process is PA-schedule plus $A$'s quotes) — but that costs running the coupled construction, i.e. $R_H(m_k)$, against a poly$(n)$ generator budget. That is v3's own no-shortcut conjecture (which the FA chat put at ~0.85), not a number-theoretic assumption about $\pi$. **Trading Assumption P for the market-simulation-cost conjecture is a strict improvement in foundations.**

**Sketch of the TT failure**, reusing the two verified Lean lemmas. On post-mid days of blocks where $X_k$ is false: (i) LHS $\le \mathbb E^H_n(V_n)\approx 0$ — needs only $0\le\mathrm{Ind}_\delta\le1$ and $V_n\ge0$, no factoring, which is what makes the negative direction easy; (ii) the quote is pinned near its prior, so $\mathrm{Ind}_\delta(\text{quote}_n>v)$ is eventually $\equiv1$, a determined $\mathcal{BLCS}$ sequence for $H$ (given the mirror of v3's (A3): $\Gamma_H$ proves the construction's outputs — **a new assumption that must be stated, not smuggled**); so $H$'s own Recurring Unbiasedness on the *constant* weighting forces the Cesàro average of $\mathbb E^H_n(\mathrm{Ind}_\delta)$ to 1; (iii) the **density lemma (T3)** converts that Cesàro fact into a large value on infinitely many bad days. Hence LHS $<$ RHS $-\eta$ infinitely often: deck-TT fails, non-paradoxically.

**Known problems to solve.** The false-block frequency must be bounded below (design $\theta_k$ so $H$'s day-$m_k$ price straddles $\tfrac12$ with positive frequency — this is where the construction will fight back, and it is a *self-referential* design since $\theta_k$'s price depends on the run). Also the gate must be stated in a form that is genuinely $H$-legal: the adversarial check found BSI's gate $g_n$ is **not** $\mathcal C^H$-generable, since $H$'s expressible features cannot read $D_H$ and cannot cheaply compute $A$'s quote — repairable by dropping the quote factor, whose support is the same.

### T5 — Does Value/Tower fall with TT? (~0.4, cheap, either answer interesting)

If the triangle's side conditions hold in the new environment, T4 propagates to Value and Tower. If they don't, the environment **separates the notions under delay** — the more interesting outcome. Cheap to check and worth doing early.

### T6 — The deficit bound (positive; ~0.75 in repaired form)

**BSI Theorem C is half wrong and the good half is the interesting half.** The adversarial check found, and I agree, that $\sum_k w^{\mathrm{frozen}}_{d_k}<\infty$ **does not follow and is false in general**: v3's Theorem 1 needs the *live* purchase price to be low, whereas a frozen gate bounds only the frozen price. Concrete refutation: frozen credence $\approx0$, credence jumps to $\approx1$ mid-block, quote $\approx1$ — the frozen-gated weight is 1 every day with the forecaster's forecasts *perfect*. So BSI's headline "finite frozen-certifiable mass $+$ a constant times surprise flow" is wrong **as a decomposition**.

What survives, and is the result to state:
$$\sum_k w_{d_k} \;\le\; O(1) \;+\; \frac{C}{\varepsilon}\sum_k \big|\mathbb E^H_{d_k}(V) - \mathbb E^H_{T_{k(d_k)}}(V)\big|.$$
Violations are bounded by the human's own within-freeze update mass, full stop — no finite frozen budget. The bounding quantity is in $H$'s instrument class, not $A$'s, so trust in a frozen system is metered by the party extending it. Also: BSI's case split is stated at the wrong threshold (it needs the ramp *saturated*, at $t-\tfrac\varepsilon2-\delta$, not $t-\tfrac\varepsilon2$) but the displayed inequality is nonetheless valid — the check verified this by hand and numerically over a $501^2$ grid, finding equality attained and no violation. **Tightness is not established** (~0.25): the realized ratio in BSI's environment is a constant 4, against the bound's $2/\varepsilon=64$, so the environment shows only that the surprise term cannot be *dropped*.

**Lean target (L5):** the ramp case-split arithmetic and the constant. This is exactly the kind of step that went wrong here, so it is worth checking.

### T7 — Constant-$V$ positive result (~0.55; the interesting part is why it is hard)

The TT-format analogue of Theorem A. T2 gives $a_n \lesssim_n \mathbb E^H_n(V)$, so on gated days $\mathbb E^H_n(V)\ge v-o(1)$; concluding TT needs a **factoring** step, $\mathbb E^H_n(V\cdot\mathrm{Ind}) \gtrsim_n \mathbb E^H_n(V)\cdot\mathbb E^H_n(\mathrm{Ind}) - o(1)$, which is not free — note the asymmetry with T4, which needs only an upper bound on the same product. Best route is the conditional tower `ccee` at the observable weight, i.e. the fold the wiki already has (`DeferenceFold.fold_sum`).

### T8 — Non-vacuity guards (cheap; prevent an overclaim)

The self-trust witness (`st` 4.12.4) and the joint-clearing "echo" construction, both non-degenerate per AUDIT.md §3.8. These localise T4's failure on the delay rather than on the varying questions.

### T9 — Report both errata upstream

The 4.8.15/4.8.16 transposition is **confirmed** in full, with three extra symptoms the earlier account missed (4.8.16 writes $w$ for $\overline w$; 4.8.15 is the only theorem in §4.8 with no `\proofin`; the clause's `$f$` in 4.8.15 is a dangling reference). **And a second, previously unnoticed erratum:** LI **Definition 4.4.4's "above"/"below" labels are transposed** relative to how appendix D.7 uses them — D.7 sets $A_n := \phi_n - p_n$, giving the opposite sign to the printed numerator $(p_i - \operatorname{Thm}_\Gamma(\phi_i))$, and D.8 corroborates the proof's reading. Anyone formalizing 4.4.5's one-sided forms needs the corrected convention.

---

## 7. What I am not going to do

No softmax-for-argmax, no tie-break gadgets, no re-parameterised $\mathrm{Ind}_\delta$, no renaming of notions, and no Lean theorem claiming "the criterion forces X" — the market is unmodeled, so every such step is a named hypothesis and is labelled as one.

---

## 8. Lean status

Project builds clean: 7898 jobs, all declarations `[propext, Classical.choice, Quot.sound]`.

| # | content | file | status |
|---|---|---|---|
| L1 | Density lemma (Cesàro + positive density ⟹ large value on the set i.o.) | `StalenessDensity.lean` | ✅ Proved |
| L2 | Limit-point engine + wash-out lemma (T1) | `Staleness.lean` | ✅ Proved |
| L4 | BSI Lemma 4 ramp arithmetic and margins | `Staleness.lean` | ✅ Proved |
| — | Non-vacuity, non-degenerate (adverse initial segment) | `Staleness.lean` | ✅ Proved |
| L5 | Theorem C's repaired split and constant | — | next |
| L6 | TT-failure assembly for T4 | — | after T4's design settles |
| L3 | Theorem A assembly (with the 4.8.3 citation fix) | — | next |

Named hypotheses are type (b) LI citations (Recurring Unbiasedness as a limit-point statement; Expectations Converge; `ccee`/`cee`/`expprovind`/`epr`). Type (c), flagged: that a given weighting is in a given generable class. Not attempted: modelling the market — AUDIT.md recommendation 5 is right that this is the only route to converting the forcing gaps, and it is a project of its own.

---

## 9. Ordering

1. **T2 write-up** — Theorem A with its three citation repairs. Highest confidence, strictly strengthens the positive side, cheapest.
2. **L3, L5** in Lean.
3. **T4 design** — the introspective question family. This is where the new thinking is needed; the frequency-straddling requirement is the hard part.
4. **T1's converse definition** ("asymptotically $A$-generable").
5. **T5** (cheap), **T9** (write up both errata).
6. **T6, T7** — the two positive results needing genuine new steps.

---

## 10. Verification log

**2026-07-29, three adversarial checks (independent, parallel).**

- **LI statement extraction + erratum re-derivation.** 4.8.15/4.8.16 transposition **confirmed** with extra symptoms; **new erratum found** in Def. 4.4.4 (above/below transposed vs. appendix D.7). `epr`/`er` are **4.11.3/4.11.4**, not 4.11.4/4.11.5; there is no 4.11.5. "e.d." (efficiently describable) is **not an LI notion** — project-local coinage, deliberate per `setting-and-notation.md`, but must not be attributed to the paper. 4.8.17 is "Learning Pseudorandom LUV Sequences", states only the $\gtrsim$ form, and is **clean** — BSI's worry that it sits in the erratum family is a non-issue.
- **Wiki statement sheet.** Deck-TT's quantifier structure confirmed: over e.d. LUV *sequences*, full threshold family. "Regular" is not a wiki term. The triangle is stated **for two distinct inductors** throughout. Cross-process Mart/Tower asserted **refuted**; cross-process TT **forced but only as a sparse, non-gap-closed family**. All ten FA-side wiki pages remain unwritten.
- **Adversarial check of BSI A/B/C.** Theorem A **0.90** (holds; three cosmetic repairs; subsumes v3 Cor 2). Theorem B **0.10** — the generability obstruction of §1. Theorem C **0.15** as stated, **0.75** repaired, tightness **0.25**. Also: BSI's gate is not $\mathcal C^H$-generable (repairable); an off-by-one at the block boundary ($T_{k+1}$ is *inside* block $k$, so the freeze data arrives on the last day the question is current, and the day-$T_{k+1}$ quote has zero horizon — costs one day per block, not fatal); Assumption P as displayed is inconsistent with Lemma 3's class-relative intent.

**My own checks.** Provability Induction's "e.c. sequence of theorems" hypothesis verified directly at `main.tex:1052`, which is what closes off the fallback route in §1. Both v3 copies compared token-by-token (the root copy is the degraded one). Lean results as in §6.

**Net.** The positive side got **stronger and cheaper** (T2). The negative side lost its construction but gained a diagnosis and a better construction target (T4). BSI's methodological headline — that the verification dissolved — is retracted.
