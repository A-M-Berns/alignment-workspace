# Delay and visibility

*What it costs when two inductors do not clear as one fixed point. Contains the fixed-question robustness theorem, the refutation of the matching impossibility, and the surviving trade-off bound. Setting: $H\dashv\mathcal C_H$ and $A\dashv\mathcal C_A$, each an ordinary logical inductor over its own deductive process. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

*Supersedes the page planned as `staleness-and-alternation` (never written), which was to be written from FA-chat msgs 42–43 and delta-report items D1–D2. Both are now out of date: msgs 44–47 developed the question, and a verification pass on 2026-07-29 refuted the impossibility. Primary sources: `imported-chats/2026-07-29__fa-chat-continuation-msgs-44-47__a6632d0f.md` and `imported-chats/fa-block-staleness-impossibility.md` (the only copy of the latter). Working document: `delay-program.md`.*

---

## 1. Terminology, and why "staleness" was the wrong word

**"Delay", not "staleness"** (Abram, 2026-07-29): shorter, neutral, and without the negative connotation that quietly framed the whole question as being about degradation.

And the framing itself was backwards. **Non-shared-fixed-point is the default**, not a special case deserving a name; what deserves a name is the *extra* assumption — shared clearing — not its absence. The corpus had drifted into treating the symmetric case as the home setting and every departure from it as a pathology, which is part of what sent the search for a matching impossibility in the wrong direction (§3).

**Delay is only one axis, and not the one that matters.** These come apart and have very different costs:

| axis | what varies | cost |
|---|---|---|
| **clearing order** | both markets clear as one fixed point, vs. one clears then the other | the joint fixed point needs a **new Brouwer argument**, which v3 (A1) *assumes rather than cites* — [[joint-clearing-and-trader-class]] |
| **direction of visibility** | $H$ reads $A$'s quotes / $A$ reads $H$'s prices / neither | **one-way is nearly free** (settled data at read time, hard dependence legal); mutual same-round is what costs |
| **delay length** | one day, one block, never | matters only through *what it hides*, never on its own |
| **ledger coarseness** | full price stream vs. a published summary | a separate restriction, not treated here |
| **class and theory** | $\mathcal C_H\subsetneq\mathcal C_A$; $\Gamma_H$ vs $\Gamma_A$ | orthogonal to all of the above |

**The finding of this page is that direction of visibility carries all the weight** — not delay length, and not clearing order. See [[faithful-acceleration-result]] §2 for the factoring that makes this visible: Half 1 of the positive result needs no visibility at all, and every visibility assumption in the corpus is paying for Half 2.

---

## 2. Fixed questions are delay-proof

**Theorem A.** For a *fixed* $[0,1]$-LUV $X$ and a forecaster delayed arbitrarily — any freeze schedule, including never receiving $H$'s data at all — for every $c>0$ only finitely many days have $a_n \ge \mathbb E^H_n(X) + c$.

Proof, hypotheses, the three citation repairs it needs, and the varying-but-convergent extension: **[[faithful-acceleration-result]] §4.2**. Status there: **PROVED modulo named hypotheses (~0.90)**, engine KERNEL-CHECKED, and it **strictly subsumes v3's Corollary 2 under weaker hypotheses.**

**The mechanism, in one sentence.** The human's expectation of a fixed LUV converges (4.8.3), so the human-side factor of the violation gate collapses into a *constant* threshold, leaving a gate that is a function of the forecaster's own quote — and **a market is never stale to itself.**

**The moral, which is the useful part.** An impossibility cannot be built on a question that sits still. Persistent misplaced trust requires the trusted party to be certified against a target that keeps moving out from under the certificate. So genuine averaged-trust failure needs *fresh* questions — and, per §3, rather more than that.

---

## 3. The matching impossibility is REFUTED

**Status: REFUTED** (2026-07-29). This is a correction to `fa-block-staleness-impossibility.md` §4 (its Theorem B, offered at ~0.75 conditional on its Assumption P) and to delta-report **D1**.

**What was claimed.** An environment $\mathcal E$ with one fresh question per block — $X_k := s_k\wedge s'_k$ for Ackermann-indexed $\pi$-digit parities — with evidence fed mid-block to $H$ and deferred in $A$'s process, in which both agents are the paper's *constructed* inductors (so both criteria hold **by citation**), the quote is pinned at $\tfrac14$ by the learning theorems, the human's credence drops to the truth, and the violation weight diverges on a gate legible to $H$ and provably not to $A$.

**Why it fails: forcing and hiding pull against each other.** The construction needs its evidence to be simultaneously

- **hard**, so the delayed forecaster cannot anticipate it (that is what the Ackermann indexing is for), and
- **easy**, so the human is *forced* to respond to it once revealed (that is what the citation of 4.4.5 is for).

The second fails, for a structural reason. Every LI forcing theorem routes through an **efficiently computable or $\overline{\mathbb P}$-generable handle**:

- **Generability (Definition 4.3.5)** means an e.c. progression of *expressible features*, and expressible features (Definition 3.4.3) are built from price features, rationals, $+$, $\times$, $\max$ and safe reciprocation. **There is no primitive for the deductive state.** A generator reads *prices*, not $D_H$. So the document's "the generator at indices $\ge m_k$ can afford to read $D_H$'s day-$m_k$ output" is not a legal move: to produce the numeral $\sigma_k$ the generator must *compute* it in poly$(n)$ time, and $\sigma_k$ is Ackermann-hard by construction. This is the value-versus-description conflation that [[setting-and-notation]] §LUV warns about, in its most consequential form: the *value* sits in $D_H$; the *numeral a poly-time generator can write down* does not.
- **The obvious fallback also fails.** Provability Induction (4.2.1, `main.tex:1052`) requires "an e.c. sequence of **theorems**" — and selecting the *refuted* blocks to feed it is exactly computing $\sigma$. So nothing forces the human's price to move either.

Hence in $\mathcal E$ the human's credence most plausibly sits at $\approx\tfrac14$ post-mid as well, the credence ramp is $0$, and $\sum_n w_n = 0$: the environment does not exhibit divergent violation weight.

**And it cannot be repaired by re-timing.** Both generator classes are poly-time in the *same* day index. With constant block length, mid-block and freeze differ by a constant, so anything poly-time at one is poly-time at the other: there is no computational wedge between pre-mid and post-mid, nor between the two agents. Growing the blocks does not help — if the parity becomes poly-time available mid-block, it is available to *both* agents' generators there, and the forecaster simply quotes correctly. **The freeze restricts price visibility, never computation.** That is the general obstruction, and it is why this looks structural rather than clerical.

**What else the same pass found in that document.** The gate $g_n$ is **not** $\mathcal C^H$-generable either (the human's expressible features cannot read $D_H$ and cannot cheaply compute $A$'s quote) — repairable by dropping the quote factor, whose support is the same. An off-by-one at the block boundary: $T_{k+1}$ lies *inside* block $k$ under the document's own convention, so the freeze data arrives on the last day the question is current and the day-$T_{k+1}$ quote has zero horizon; this costs one day per block, not the result. And Assumption P as displayed (relative to "either agent") is inconsistent with the class-relative reading the surrounding prose intends — which is precisely the crux above.

**What is retracted with it.** The document's *methodological* headline — that implementing the freeze inside $D_A$ makes both criteria hold by citation, so "the verification I promised to write slowest largely dissolved, which is itself the finding" — **does not survive.** Any repair either constructs a human that responds (and must then prove it unexploitable by hand) or changes the question family. The verification burden comes back.

**What survives, and is worth keeping.** The *diagnosis* is a real result about this setting, and it is more interesting than the theorem it replaces:

> **The logical induction criterion forces a price to respond only to what an efficiently computable handle can select.** Evidence that no efficient trader can use does not move a price, however plainly the deductive process has revealed it.

That reframes the whole question a second time. FA-chat msgs 44–47 relocated the failure from *delay* to *novelty*; this relocates it again, to **efficiently-exploitable surprise**. Novelty is not enough; the surprise has to be cheap.

---

## 4. The redesign target: make the question about the human's own beliefs

*CONJECTURED (~0.45). The construction §3's diagnosis points at.*

If the human's response must be forced by something *cheap*, and hidden from the forecaster by *the freeze* rather than by hardness, then the question should be about the human's own state. Take
$$X_k := \ulcorner \mathbb P^H_{m_k}(\theta_k) > \tfrac12\urcorner$$
for a suitable e.c. sequence $\theta_k$ and mid-block $m_k$.

- **The human's response is forced for free**, by Introspection (4.11.1) and `epr` (**4.11.3** — note the numbering correction in [[li-paper-erratum]] §3). $H$ approximately knows its own day-$m_k$ price, so post-mid its credence in $X_k$ tracks the truth. A citation, not a construction — which is what the refuted version wanted and did not get.
- **The forecaster cannot see it**, because $X_k$'s truth is a fact about $H$'s prices past the freeze, and the freeze is exactly a restriction on $H$'s prices. This is the *right* use of a delay.
- **The remaining hypothesis is better founded.** $A$ could in principle simulate $H$ forward — it knows its own quotes, and $H$'s process is a PA schedule plus those quotes — but that costs running the coupled construction, against a poly$(n)$ generator budget. That is v3's own no-shortcut conjecture (~0.85 in the FA chat), not a number-theoretic assumption about $\pi$. **Trading Assumption P for the market-simulation-cost conjecture is a strict improvement in foundations.**

**Sketch of the failure, with the two machine-checked lemmas doing real work.** On post-mid days of blocks where $X_k$ is false: (i) the Total-Trust left side is $\le \mathbb E^H_n(X_k)\approx 0$, needing only $0\le\operatorname{Ind}_\delta\le1$ and $X_k\ge0$ — **no factoring**, which is what makes the negative direction easier than the positive one; (ii) the quote sits near its prior, so $\operatorname{Ind}_\delta(a_n>v)$ is eventually $\equiv1$, a determined $\mathcal{BLCS}$ sequence for $H$ **given the mirror of v3's (A3) — that $\Gamma_H$ proves the construction's outputs, a new assumption that must be stated and not smuggled** — so $H$'s own Recurring Unbiasedness on the *constant* weighting forces the Cesàro average of $\mathbb E^H_n(\operatorname{Ind}_\delta)$ to $1$; (iii) the **density lemma** converts that Cesàro fact into a large value on infinitely many bad days.

Step (iii) is `StalenessDensity.exists_freq_mem_and_ge_half` (`sorry`-free, standard axioms): if $x\le 1$ has Cesàro averages $\to1$ and $S$ has upper density $\ge d>0$, then $x_n\ge\tfrac12$ for infinitely many $n\in S$. It exists because this is exactly the point at which an informal argument is tempted to assume a *pointwise* bound when only a *Cesàro* bound is available.

**The hard part that remains.** The false-block frequency must be bounded below — $\theta_k$ must be designed so $H$'s day-$m_k$ price straddles $\tfrac12$ with positive frequency — and that design is *self-referential*, since $\theta_k$'s price depends on the run. This is where the construction will fight back.

**Why bother, given the paradox route already exists.** Cross-process Mart/Tower is asserted **refuted** ([[tower-death]]), so via the triangle full-strength cross-process Total Trust is arguably already dead — but by a *paradox* route, through the quote-referencing diagonal. Abram's msg 44 asked precisely for the other kind: "the negative result we're looking for here should be cases where even the on-average sense of trust that avoids paradoxes must fail." So the value of this construction is not that trust fails but that it **fails non-paradoxically** — nobody exploited, nobody wrong. Any write-up must lead with that distinction or it reads as a re-derivation.

---

## 5. The trade-off bound, corrected

*What `fa-block-staleness-impossibility.md` §5 offers as its Theorem C, half of which fails.*

**REFUTED as stated:** the claim that the *frozen-gated* part of the violation weight is finite, $\sum_k w^{\mathrm{frozen}}_{d_k}<\infty$, does not follow and is false in general. v3's Theorem 1 turns on the *live* purchase price being low; a frozen gate bounds only the frozen price, leaving the live purchase price unconstrained. Concrete refutation: frozen credence $\approx0$, credence jumping to $\approx1$ mid-block, quote $\approx1$ — the frozen-gated weight is $1$ every day while the forecaster's forecasts are *perfect*. Nothing is violated; the human is merely surprised on a divergent gate, which the framework permits. So the document's headline decomposition — "finite frozen-certifiable mass $+$ a constant times the update flow" — is wrong: **there is no finite frozen-certifiable budget.**

**CONJECTURED (~0.75), the surviving form:**
$$\sum_k w_{d_k} \;\le\; O(1) \;+\; \frac{C}{\varepsilon}\sum_k \big|\mathbb E^H_{d_k}(X) - \mathbb E^H_{T_{k(d_k)}}(X)\big|.$$

Violations are bounded by the human's own within-delay update mass, full stop. Two further corrections: the document's case split is stated at the wrong threshold — it needs the ramp *saturated*, at $t-\tfrac\varepsilon2-\delta$ rather than $t-\tfrac\varepsilon2$, since a frozen credence just barely below the threshold gives a ramp value near $0$ against a violation weight of $1$ — but the displayed inequality is nonetheless **valid**, verified by hand and numerically over a $501^2$ grid in $(c,F)$ across a range of $(\varepsilon,\delta,t)$, with equality attained and no violation found. And **tightness is not established** (~0.25): the realized ratio of weight to displacement in the document's own environment is a constant $4$, against the bound's $2/\varepsilon = 64$, so the environment shows only that the surprise term cannot be *dropped* — not that the constant is right. Since the exhibiting environment is the refuted one of §3, tightness inherits that too.

**Why the surviving form is the interesting one anyway.** The bounding quantity is in $H$'s instrument class, not $A$'s: it is the human's own update magnitude. So the trust a delayed system can underwrite is **metered by the party extending it**, in real time, and by [[open-problems]]'s reading this is the honest cross-generational statement — each delay adds its own surprise flow to an un-certifiable residue that nothing later redeems, since the questions it accrued on have retired.

---

## 6. Status summary

| claim | status |
|---|---|
| Half 1 of the positive result needs no visibility at all | PROVED (prose); engine KERNEL-CHECKED |
| Theorem A: fixed questions are delay-proof, arbitrary delay, no visibility | PROVED modulo named hypotheses (~0.90) |
| Theorem A extends to varying-but-convergent questions | CONJECTURED (~0.6) |
| Varying questions need only *one-way* visibility (the `cee` route) | CONJECTURED (~0.6), one named gap — [[faithful-acceleration-result]] §4.3 |
| The matching impossibility in $\mathcal E$ | **REFUTED** (§3) |
| "The criterion forces response only to efficiently selectable evidence" | INTERPRETATION, but load-bearing (§3) |
| The introspective redesign | CONJECTURED (~0.45) (§4) |
| Frozen part of the trade-off is finite | **REFUTED** (§5) |
| Violations $\le O(1) + (C/\varepsilon)\cdot$ update mass | CONJECTURED (~0.75) |
| Tightness of the constant | CONJECTURED (~0.25) |
| Day-scale (one-day delay) version | OPEN (~0.6), deliberately not sketched |

## Related

- [[faithful-acceleration-result]] — the factoring, Theorem A's proof, the three routes
- [[joint-clearing-and-trader-class]] — what shared clearing costs; why one-way is cheap
- [[li-paper-erratum]] — 4.3.5 and 4.2.1, which do the work in §3
- [[anticipated-deference]] — the other post-v3 frontier item
- [[open-problems]] — the common-subsequence gap; the redesign; the day-scale question
- [[new-chats-2026-07]] — the reader's guide, including what D1/D2 said before this page
