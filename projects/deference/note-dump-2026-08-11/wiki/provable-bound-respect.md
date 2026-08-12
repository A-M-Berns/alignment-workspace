# Provable-bound respect: full Total Trust ⟹ Value in one step

*If $\Gamma$ proves the expert rates $X$ at least $s$, then a novice with full Total Trust rates $X$ at least $s$ too — because every cut at a threshold below $s$ is **provably full** (its ramp weight is identically $1$). One application to $\widehat S - O^i$ yields full-menu Value — for the argmax strategy itself — in a single step: no induction, no menu-size bound, any ledger-decided tie-break ([[ledger-decided-tie-breaks]]). This is where "Value needs Mart" dies.*

**Provenance.** This argument is the ⚠ strengthening discovered in the 2026-07-21 checking pass over the telescoping write-up (it is **not** in the session-`b9e8341b` extraction, whose Caveat 3 concluded the opposite — "hard-argmax Value therefore remains a Mart-only deliverable"). Split into its own page 2026-07-23. **Unvetted**, and worth vetting, since it further demotes what Mart is needed *for*.

**⚠ Superseded framing (2026-07-25).** This page works in the surrogate formulation — composite "$E^\ast$" is the linear extension of published quotes — under which the Lemma's hypothesis is exact ledger arithmetic and Application 2 looks unconditional. In the true LI setting ([[total-trust-implies-value]], the page of record) the Lemma survives as **bounds transfer** with an asymptotic hypothesis, but the one-step Value conclusion was a surrogate artifact: the expert-side content returns as **self-endorsement**, refuted without a decision-theoretic scope condition (punishing menus — which also refute unconditional argmax Value) and costing introspection. Read this page for the provably-full-cuts idea and the surrogate-level skeleton; read the current theorem there.

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor; expert $E^\ast$ **observable**, **coherent**, and **introspective** ([[expert-conditions]]). Menu apparatus as in [[deference-notions]]: e.d. finite menus $\{O^1_n, \dots, O^K_n\}$ of bounded $[a,b]$-LUVs, $m^j := E^\ast(O^j)$, $M_K := \max_j m^j$, and the canonical **followed strategy** $\widehat S := O^{j^\ast}$ with $j^\ast \in \arg\max_j m^j$ (least index; any ledger-decided tie-break — [[ledger-decided-tie-breaks]]) — an e.d. LUV by observability, with **(F1)** $\Gamma \vdash E^\ast(\widehat S) = M_K$ by coherence + introspection (see the Remark on [[mart-implies-value]] for why introspection is honestly part of F1's bill).

**Derived estimates.** For a bounded LUV-combination $D = c + \sum_j \alpha_j O^j$ with ledger-computable coefficients, $E^\ast(D) := c + \sum_j \alpha_j m^j$ — the expert's actual estimate by coherence, and a $\Gamma$-decided, $\mathcal{C}_H$-cheap quantity by observability.

**Hypothesis: full Total Trust.** Unlike the telescope ([[keep-or-switch-telescope]]) and the one-shot hedge ([[one-shot-hedge]]), which spend only the threshold-$0$ fragment, this page uses Total Trust as actually defined in [[deference-notions]] — quantified over **every** threshold $t$: for every e.d. bet sequence $X$ (from the class of bounded LUV-combinations built from menu options and observable expert-estimates), every $t$, and every ramp width $\delta$,

$$ E^H_n\big(X \cdot \operatorname{Ind}_\delta(E^\ast(X) > t)\big) \;\gtrsim_n\; t \cdot E^H_n\big(\operatorname{Ind}_\delta(E^\ast(X) > t)\big), $$

where $\operatorname{Ind}_\delta(x > t)$ is the ramp indicator: $0$ for $x \le t$, $1$ for $x \ge t + \delta$, linear between. Also used: the novice's own `loe` (4.8.4) and `expprovind` (4.8.10) for bookkeeping. **No tower, no Mart, no self-trust.**

## The principle

**Lemma (provable-bound respect).** Assume full Total Trust. If $\Gamma \vdash E^\ast(X_n) \ge s$ (uniformly in $n$), then $E^H_n(X_n) \gtrsim_n s$.

**Proof.** Fix $\varepsilon > 0$ and any ramp width $\delta < \varepsilon$. The weight $\operatorname{Ind}_\delta(E^\ast(X_n) > s - \varepsilon)$ is *provably identically $1$*: its argument $E^\ast(X_n)$ is a ledger-computed, $\Gamma$-decided quantity provably $\ge s > s - \varepsilon + \delta$, so the ramp evaluates to $1$ on every consistent world. Unnormalized TT at threshold $s - \varepsilon$ therefore reads

$$ E^H_n(X_n) \;=\; E^H_n\big(X_n \cdot \operatorname{Ind}_\delta(E^\ast(X_n) > s - \varepsilon)\big) \;\gtrsim_n\; (s - \varepsilon) \cdot E^H_n(1) \;\approx_n\; s - \varepsilon. $$

Since $\varepsilon > 0$ was arbitrary, $E^H_n(X_n) \gtrsim_n s$. $\blacksquare$

**Remark — this is genuinely a deference principle, not the novice's own `expprovind`.** `expprovind` carries "$\Gamma \vdash X_n \ge s$" (a bound on the *bet itself*) through $E^H_n$. Here $\Gamma$ bounds only the **expert's estimate** of $X_n$; nothing bounds $X_n$ in the worlds. That the novice's expectation respects the expert's provable bounds is deference content, and it is exactly what the full threshold family adds over the threshold-$0$ fragment: TT at thresholds where the cut is provably full turns each such threshold into an unconditional floor.

## Application 1: the hard telescope rungs

The hard rung LUV of [[keep-or-switch-telescope]], $Z_k = D_k \cdot \mathbb{1}[E^\ast(D_k) > 0]$, satisfies $\Gamma \vdash E^\ast(Z_k) = \max(0, E^\ast(D_k)) \ge 0$ (coherence + introspection, as in that page's Claim A). Provable-bound respect at $s = 0$ gives $E^H_n(Z_k) \gtrsim_n 0$ — the hard telescope step, closing the wedge term that threshold-$0$ TT leaves unbounded. The hard telescope then runs as written, without waiting for a finite-exact setting.

## Application 2: Value in one step

*(For a single linear read of just this argument, self-contained and with each fact stated where it is used: [[total-trust-implies-value]].)*

More directly, skip the induction entirely. The goal is **Value** ([[deference-notions]]): for every e.d. sequence of finite menus and every fixed index $i$,

$$ E^H_n\big(\widehat S_n\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big). $$

Fix $i$ and set $D := \widehat S - O^i$ — an e.d. bounded LUV-combination in TT's class. F1 gives

$$ \Gamma \vdash E^\ast(D) \;=\; M_K - m^i \;\ge\; 0, $$

so provable-bound respect at $s = 0$ yields $E^H_n(\widehat S - O^i) \gtrsim_n 0$, which by `loe` is exactly the Value inequality above — full-menu **Value**, for the argmax strategy itself, in one step. Compared with the telescope, every restriction falls away:

- **any ledger-decided tie-break** — $\widehat S$ is the canonical least-index strategy; F1 is tie-break-independent, so the $i$-promoted relabeling (and the Claim-B wrinkle) never arises;
- **no bound on menu size** — a single TT application per instance, so the bounded-$K$ restriction of the telescope's Setting disappears;
- **unhedged** — the conclusion concerns the argmax strategy itself, no $\delta$-loss.

## Amplifier cross-check

No conflict with [[amplifier-counterexample]]: the amplifier $g(e) = (1+2c)e - c$ passes all *parallel* threshold cuts only in the uniform single-bet setup of deference-v6 §1.6. On a bet whose estimate-distribution concentrates where $g < \mathrm{id}$, it violates precisely the provably-full negative cuts this page spends — which is boundedness-at-the-extremes biting, exactly as §1.6 says. An amplifier-like novice survives the threshold-$0$ fragment (hence the wedge on [[keep-or-switch-telescope]]) but not the full threshold family.

## What this recalibrates

The extraction's Caveat 3 read "hard-argmax Value remains a Mart-only deliverable." With this page, the honest summary of the whole Total Trust ⟹ Value cluster becomes:

> **threshold-$0$ TT ⟹ $\delta$-hedged Value** ([[keep-or-switch-telescope]], [[one-shot-hedge]]); **full TT ⟹ Value** (this page); **Mart is needed for neither.**

This further demotes what Mart is uniquely needed for: on the Value axis, nothing — Mart's remaining exclusive content is the pointwise *equality* itself (see [[total-trust-implies-mart]] for when TT recovers even that, and [[value-iff-mart]] for the assembled lattice).

## Status

**PROVED (prose, this page)** — **unvetted by Abram as of 2026-07-23; not machine-checked.** Artifact of the 2026-07-21 write-up checking pass, not of the source session; it contradicts (and, if vetted, corrects) the extraction's Caveat-3 conclusion. The Lemma is short enough to be a natural machine-check candidate alongside the telescope ([[open-problems]]).

## Related

- [[total-trust-implies-value-telescoping]] — overview of the result and its three routes
- [[keep-or-switch-telescope]] — the original induction route (threshold-$0$ fragment; the wedge this page closes)
- [[one-shot-hedge]] — one-step $\delta$-hedged Value from the threshold-$0$ fragment alone
- [[deference-notions]] — Total Trust's full definition; Value; the implication diagram
- [[amplifier-counterexample]] — the counterexample this page's cuts evade, and why
- [[total-trust-implies-mart]], [[value-iff-mart]] — what remains exclusive to the tower
- [[mart-implies-value]] — the F1 remark (coherence + introspection) this page's Application 2 leans on
- [[ledger-decided-tie-breaks]] — the tie-break condition F1 needs (necessary, not convenience)

*Source: the ⚠ strengthening under Caveat 3 of the pre-split [[total-trust-implies-value-telescoping]] (2026-07-21 write-up, recoverable from git history); apparatus from deference-v6 §1.1–§1.6.*
