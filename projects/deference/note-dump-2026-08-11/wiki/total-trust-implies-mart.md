# Total Trust ⟹ Mart (the gap-bet argument)

*If the Total-Trust quantifier ranges over a bet class closed under expert-referencing **gap-bets** $D = Z - \ulcorner E^\ast(Z)\urcorner$, then Total Trust pins the tower in two lines — no convex geometry. The "soft⇒hard squeeze" that deference-v6 §1.6 left as hard open prose was an artifact of quantifying Total Trust only over parallel cuts of a single fixed bet. This corroborates the Garrabrant–Eisenstat view that Total Trust is equivalent to iterated expectations in LI.*

**⚠ Rewrite pending (2026-07-27).** The argument below is stated at the surrogate level: its Step 1 asserts $\Gamma \vdash E^\ast(D) = E^\ast(Z) - E^\ast(\ulcorner E^\ast(Z)\urcorner) = 0$, which is exactly the retracted "expert expectations are exact and provably linear" assumption ([[total-trust-implies-value]] §Status). The true-setting replacement is short and already available: the expert's own `loe` plus asymptotic introspection give $E^A_n(D_n) \to 0$, so $E^A_n(\pm D_n) \gtrsim_n 0$, and **Lemma 1 of [[total-trust-implies-value]] applied twice at threshold $0$** transfers both bounds to the novice, giving $E^H_n(D_n) \approx_n 0$. That also disposes of this page's $\delta$-diagonalization and its unwritten introspection bookkeeping, since Lemma 1's step (b) is precisely the move that converts an asymptotic fact about a published decided quote into a provable weight-saturation. This arrow is no longer *needed* to reach the tower — [[value-implies-tower]] gets there from Value directly, more cheaply — but it remains the statement of record for **Total Trust** ⟹ Tower.

## Provenance

Surfaced 2026-07-21 during the wiki rebuild (flagged by a verification pass, then checked independently in the main session). **Not in deference-v6** — deference-v6 §1.6 frames Total Trust ⟹ tower as "genuine convex geometry… remains prose," and Appendix B leaves it at the amplifier obstruction. The legality of expert-referencing bets is the same move the telescoping proof already makes with its derived bets ([[total-trust-implies-value-telescoping]], session b9e8341b). Independent corroboration: Abram reports (2026-07-21) that Scott Garrabrant and Sam Eisenstat's view was that Total Trust really is equivalent to the tower/Mart in LI, though no specific argument was recalled — this page supplies one.

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H$ a logical inductor with its free `loe` (4.8.4) and `expprovind` (4.8.10); expert $E^\ast$ **observable**, **coherent**, **introspective**. Total Trust ([[deference-notions]]) in the unnormalized soft form: for every bet $D$ in the class $\mathcal{D}$ and rational threshold $t$,

$$\mathrm{TT}(D,t):\qquad E^H_n\big((D - t)\cdot \operatorname{Ind}_\delta(E^\ast(D) > t)\big) \gtrsim_n 0 .$$

**The load-bearing hypothesis (H1)** is the quantifier domain: $\mathcal{D}$ must be **closed under the gap construction** — for $Z \in \mathcal{D}$, the bet $Z - \ulcorner E^\ast(Z)\urcorner$ (and its negation/rescaling) is again in $\mathcal{D}$. In LI this is the natural reading: the expert's estimates are observable, hence world-decided facts the novice can legally bet on (the thin channel), and the derived bets of the telescoping proof already live in this class. deference-v6's §1.2-equivalent form of Total Trust quantifies over "e.d. bounded LUV-combinations built from menu options and observable expert-estimates," which contains the gap-bets.

## Statement

**Theorem.** For an observable, coherent, introspective expert, Total Trust over a gap-closed class $\mathcal{D}$ implies Mart on $\mathcal{D}$: for every $Z \in \mathcal{D}$,
$$E^H_n(Z) \;\approx_n\; E^H_n(\ulcorner E^\ast(Z)\urcorner).$$

With [[mart-implies-value]] and [[two-option-value-iff-total-trust]] this collapses the three notions at full quantifier strength: $\textbf{Value} \iff \textbf{Total Trust} \iff \textbf{Mart}$ (see [[value-iff-mart]] for the assembled lattice).

## Proof

Fix $Z \in \mathcal{D}$ (bounded, say $Z \in [0,1]$) and rational $\delta > 0$. Let
$$D := Z - \ulcorner E^\ast(Z)\urcorner \in [-1,1].$$

**Step 1 (introspection pins the expert's estimate of the gap).** The expert knows its own estimate and is coherent-linear on observables, so
$$\Gamma \vdash\; E^\ast(D) \;=\; E^\ast(Z) - E^\ast(\ulcorner E^\ast(Z)\urcorner) \;=\; E^\ast(Z) - E^\ast(Z) \;=\; 0 .$$

**Step 2 (both cuts fire with weight provably 1).** Apply $\mathrm{TT}(D, -2\delta)$. The soft weight is $\operatorname{Ind}_\delta(E^\ast(D) > -2\delta)$, and since $\Gamma \vdash E^\ast(D) = 0 \ge -2\delta + \delta$, the ramp sits at its top: $\Gamma \vdash \operatorname{Ind}_\delta(E^\ast(D) > -2\delta) = 1$. Carrying this provable identity through $E^H_n$ by `expprovind` and using `loe`:
$$E^H_n(D) + 2\delta \;=\; E^H_n\big((D + 2\delta)\cdot 1\big) \;\gtrsim_n\; 0, \qquad\text{i.e.}\qquad E^H_n(D) \gtrsim_n -2\delta .$$
The negation $-D$ is also in $\mathcal{D}$ (gap-bet of $\ulcorner E^\ast(Z)\urcorner$-side, or closure under negation) with $\Gamma \vdash E^\ast(-D) = 0$; the same cut gives $E^H_n(-D) \gtrsim_n -2\delta$, i.e. $E^H_n(D) \lesssim_n 2\delta$.

**Step 3 (diagonalize).** Both bounds hold for every rational $\delta > 0$; a standard diagonal over the countable family gives $E^H_n(D) \approx_n 0$, and `loe` splits $E^H_n(D) = E^H_n(Z) - E^H_n(\ulcorner E^\ast(Z)\urcorner)$. $\blacksquare$

**Threshold-range remark.** If Total Trust is only granted for thresholds $t \in [0,1]$ and $[0,1]$-bets, no negative thresholds are needed: rescale $D' := (D+1)/2 \in [0,1]$ with $\Gamma \vdash E^\ast(D') = \tfrac12$ and cut at $t = \tfrac12 - 2\delta$ (weight again provably 1); this yields the same bounds. So the argument spends nothing beyond the standard quantifier ranges.

## Consistency with the amplifier

No contradiction with [[amplifier-counterexample]] — the amplifier **fails gap-bet Total Trust**. In the measure model ($e = E^\ast(X)$ uniform, $g(e) = (1+2c)e - c$), take $Z = X\cdot\mathbb{1}[e \in [a,b]]$: then
$$E_\pi\big(Z - E^\ast(Z)\big) \;=\; \int_a^b (g(e) - e)\,de \;=\; c\,(b-a)(a+b-1) \;\ne\; 0 \quad (c>0,\ a+b\ne 1),$$
so some gap-bet cut is violated. The amplifier only ever survived the **parallel cuts of the bare bet** — it refutes the parallel-cut route to Mart, not this one. That is exactly the scoping the amplifier page now carries.

## What the theorem costs, honestly

1. **(H1) Gap-closure of the bet class.** This is where all the residual hardness lives. Settings that lack it:
   - **DDB frames**: the frame $P$ is not world-measurable, so $\ulcorner E^\ast(Z)\urcorner$ is not a legal bet and the argument is unavailable — DDB's "excruciating" convex-geometry direction is genuinely needed there. The moral of deference-v6 §2.1 relocates again: *even the squeeze* is cheap in LI **because of** observability ([[reversal-of-difficulty-vs-ddb]]).
   - **Domain-restricted Total Trust**, in particular the faithful-acceleration setting: the construction forces only the *gate-weighted* Total-Trust instances on specific bets ([[faithful-acceleration-result]]); that forced family is nowhere near gap-closed, so **no collapse to Mart follows there** — consistent with [[tower-death]] (cross-process Mart is refuted). Value$_\mathcal{D}$ ⟺ TT$_\mathcal{D}$ (deference-v6 §5.11) remains the whole truth on restricted domains, with Mart strictly stronger.
2. **(H2) Introspection precision.** Step 1 uses *provable* introspection. If the expert's self-knowledge is only asymptotic (an LI stage knowing its own prices approximately), the weight is not provably $1$ but is an **observable, eventually-decided** quantity converging to $1$; the cut then goes through asymptotically with an extra `expprovind`-on-decided-facts carry. This bookkeeping is routine but has not been written out.
3. **(H3) Estimate coverage.** The expert must publish estimates of the gap-bets themselves (equivalently: of arbitrary members of $\mathcal{D}$), not only of some target family — trivial for the future-self expert (`epr`/`er` price everything) but a real requirement on a thin-channel expert that only quotes $Y_n$.

## Status

**PROVED (prose, this page)** — verified independently twice at the wiki level (2026-07-21); **unvetted by Abram**; not machine-checked (a good candidate: the argument is three applications of stated axioms — see [[open-problems]]). If vetted, deference-v6 §1.6's "squeeze" question is **settled positively for gap-closed classes** and the convex geometry is confined to non-gap-closed domains. The claim it would revise: deference-v6 Appendix B's "squeeze stays prose" row, and every downstream use of "Value sits strictly below the tower" — see the reframing at [[value-iff-mart]].

## Related

- [[value-iff-mart]] — the assembled (now collapsed) equivalence and where separations survive
- [[amplifier-counterexample]] — the obstruction this page confines to parallel cuts / non-gap-closed domains
- [[two-option-value-iff-total-trust]] — Value ⟹ TT (the other leg of the circle)
- [[total-trust-implies-value-telescoping]] — TT ⟹ Value without gap-closure (weaker hypothesis, weaker conclusion: δ-hedged Value only)
- [[mart-implies-value]] — what Mart buys back (including Value itself — so with gap-closure, Value is TT-cheap after all)
- [[deference-notions]], [[expert-conditions]] — the notions and the exact expert bill
- [[faithful-acceleration-result]], [[tower-death]] — why none of this collapses the cross-process setting
