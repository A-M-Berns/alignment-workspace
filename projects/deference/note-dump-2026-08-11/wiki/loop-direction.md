# Loop direction (the liar probe)

*Why the equivalence loop runs **Total Trust ⟹ Value ⟹ Tower ⟹ Total Trust** ([[total-trust-implies-value]], [[value-implies-tower]], [[tower-implies-total-trust]]) and not the other way around. Arrow for arrow the reverse triangle — [[total-trust-implies-mart]], [[mart-implies-value]], [[two-option-value-iff-total-trust]] — is *cheaper*: the two directions share their three expensive ingredients, and the reverse's unique piece (the exact two-option identity) is the lightest thing in the corpus, while the forward's (the fold at the ramp) is a genuine asymptotic argument. But the reverse triangle does not close at true-LI strength: once Value is honestly restricted to conditional-stable menus (the restriction [[total-trust-implies-value]] §Necessity forces), its closing arrow cannot serve the Total-Trust instances whose quote hovers on the threshold. The certificate is the **liar probe** — the $K{=}2$ punishing option packaged with a constant — a two-option menu on which conditional-stability fails, Value is false, and the hard above-threshold inequality is itself false, all by the same margin $s(1-s)$, while full soft Total Trust holds. Entry into soft Total Trust must ride a weighting, not a selection; every known full-strength entry factors through the fold. **Unvetted by Abram as of 2026-08-02.***

**Name.** "Tower" throughout = the corpus's **Mart** ([[deference-notions]]), per the naming note of [[value-implies-tower]].

## The question

Six arrows among the three notions are on record, and three suffice ([[value-iff-mart]] ⚠ 2026-07-27). Two independent triangles could close the loop:

- **forward** (the 2026-07-27 circuit): Total Trust ⟹ Value ⟹ Tower ⟹ Total Trust;
- **reverse** (the older lattice of [[value-iff-mart]]): Total Trust ⟹ Tower ⟹ Value ⟹ Total Trust.

This page compares them. The per-arrow answer favours the reverse; the closing answer forces the forward.

## Per-arrow accounting: the shared costs cancel

| corner reached | forward arrow | reverse arrow |
|---|---|---|
| Value | [[total-trust-implies-value]]: bounds transfer + self-endorsement; (H2), (H3), tie-break; one named gap | [[mart-implies-value]]: four-step chain; the honest F1 carry is the same self-endorsement bill — (H2), (H3), tie-break, the same gap |
| Tower | [[value-implies-tower]]: probe menus; gap-bet quote pinning; (H3) vacuous on the probes, no tie-break | [[total-trust-implies-mart]] (⚠ rewrite pending): the same quote pinning, then bounds transfer twice at threshold $0$; needs gap-closure |
| Total Trust | [[tower-implies-total-trust]]: the fold at the ramp — scope-free, full soft strength | [[two-option-value-iff-total-trust]] read right-to-left: exact, kernel-checked — but see the liar probe below |

Both triangles pay the same three irreducible ingredients exactly once each:

- **Bounds transfer** (Lemma 1 of [[total-trust-implies-value]]: weighting saturation + `expprovind`). The forward pays it inside Total Trust ⟹ Value; the reverse inside Total Trust ⟹ Tower — the ⚠ rewrite of [[total-trust-implies-mart]] *is* two applications of it at threshold $0$.
- **Self-endorsement** (Lemma 2 there — where introspection's concentration gap, conditional-stability (H3) and the ledger-decided tie-break all land). The forward pays it inside Total Trust ⟹ Value; the reverse inside Tower ⟹ Value, where the honest true-setting F1 carry is the same lemma ([[mart-implies-value]] §Remark) — and per [[value-iff-mart]] ⚠, at full menu strength that arrow is refuted outright, so its Value quantifier must be restricted exactly as the forward arrow's is.
- **Gap-bet quote pinning** (the expert's own `loe` + introspection give $E^A_n\big(Z_n - \ulcorner E^A_n(Z_n)\urcorner\big) \approx_n 0$). The forward pays it in [[value-implies-tower]] Step 1; the reverse in [[total-trust-implies-mart]] Step 1.

What remains after cancelling is one unique ingredient per direction: the forward's **fold at the ramp** ([[tower-implies-total-trust]] — a real asymptotic argument, a full page) versus the reverse's **two-option identity** ([[two-option-value-iff-total-trust]] — exact, per $(X,s)$, kernel-checked, essentially free). By raw proof content the reverse triangle wins, and it also holds the only Lean artifacts on this ground. If the comparison ended here, the loop was built the wrong way round.

## The liar probe: the reverse closure breaks

The reverse triangle's closing arrow reads the two-option identity right-to-left: for each Total-Trust instance $(X, s)$, Value on the menu $\{X, \text{const } s\}$ *is* the above-threshold inequality at $(X, s)$. The trouble: post-[[total-trust-implies-value]] §Necessity, the honest Value hypothesis is restricted to conditional-stable menus — and **the instance picks the menu, not the prover**. There are instances whose menu is excluded, and at exactly those instances the identity targets a false statement.

**Construction.** Fix rational $s \in (0,1)$. By the diagonal lemma, form the two-option menu whose first option is the indicator of its own non-selection — the $K{=}2$ punishing option of [[total-trust-implies-value]] §Necessity — and whose second option is the constant probe:

$$ \mathcal O_n \;=\; \big\{\, O^1_n,\ \ \text{const } s \,\big\}, \qquad \Gamma \vdash\; O^1_n = \mathbb 1[\mathrm{sel}_n = 2], $$

where $\mathrm{sel}_n$ is this menu's own argmax selector on the published quotes (least-index rule; any ledger-decided tie-break shifts only boundary-day bookkeeping). Legality is the standard channel: the selection is ledger arithmetic in published quotes — the same observability that legalizes gap-bets and the punishing menu.

**The quote goes liar.** Writing $E^A_n(O^1_n)$ for both the published decided rational and the LUV naming it: coherence on the indicator gives $E^A_n(O^1_n) \approx_n \mathbb P^A_n(\mathrm{sel}_n = 2)$, and $\mathrm{sel}_n = 2$ holds iff $E^A_n(O^1_n)$ falls below the constant's quote $E^A_n(\text{const } s) \approx_n s$. So the quote satisfies the liar fixed point — "my value is the probability that I sit below $s$" — and the Paradox Resistance argument (4.11.2, run on the quote; the price-integral of an indicator tracks the underlying price within its $1/n$ discretization) pins

$$ E^A_n(O^1_n) \;\to\; s, \qquad \mathbb P^A_n(\mathrm{sel}_n = 2) \;\to\; s, \qquad \mathbb P^A_n(\mathrm{sel}_n = 1) \;\to\; 1 - s. $$

Interior selection mass, quote hovering on the threshold. At $s = \tfrac12$ this is Death in Damascus in constant-probe form.

**Four computations, one margin.** Let the novice be any inductor that Towers the expert — the loop's novices all do at this corner, and the self-trust instance $H = A$ is a concrete case. Two provable identities do all the work: $\Gamma \vdash \mathbb 1[\mathrm{sel}_n = 1]\cdot O^1_n = 0$ (the punishing structure) and $\Gamma \vdash \widehat S_n = s \cdot \mathbb 1[\mathrm{sel}_n = 2]$.

1. **Conditional-stability fails.** In the denominator-free form of (H3) ([[total-trust-implies-value]]): the selected-products side is $0 + s\,\mathbb P^A_n(\mathrm{sel}_n = 2) \to s^2$; the mass-weighted-quotes side is $\mathbb P^A_n(\mathrm{sel}_n = 1)\, E^A_n(O^1_n) + \mathbb P^A_n(\mathrm{sel}_n = 2)\cdot s \to (1-s)\,s + s^2 = s$. The deficit tends to $-s(1-s)$: the menu is outside the honest Value quantifier.

2. **Value is false on the menu** — so no strengthening of the Tower ⟹ Value arrow could re-admit it. Tower at $(O^1_n)$ plus `expprovind` on the decided quote (ε-outside pattern) give $E^H_n(O^1_n) \approx_n E^H_n\big(\ulcorner E^A_n(O^1_n)\urcorner\big) \to s$, hence

$$ E^H_n\big(\widehat S_n\big) \;=\; s\, E^H_n\big(\mathbb 1[\mathrm{sel}_n = 2]\big) \;\to\; s^2 \;<\; s \;=\; \lim_n E^H_n(\text{const } s). $$

Following the expert loses $s(1-s)$ against the constant — and the novice here satisfies *every* epistemic notion (Tower, and soft Total Trust per computation 4). The failure is decision-theoretic, exactly as in §Necessity: argmax-following is a bad decision rule against a choice-punishing option, whatever anyone believes.

3. **The hard above-threshold inequality at the instance is false.** The identity converts the Value deficit exactly — it is an equality, so the route loses nothing; the *target* is false:

$$ E^H_n\Big( \big(O^1_n - s\big) \cdot \mathbb 1[\mathrm{sel}_n = 1] \Big) \;=\; E^H_n\Big( -\,s\cdot \mathbb 1[\mathrm{sel}_n = 1] \Big) \;\to\; -\,s(1-s) \;<\; 0. $$

4. **Yet full soft Total Trust holds at $(O^1_n)$.** Immediate from the fold — [[tower-implies-total-trust]] applies to $(O^1_n)$ like any other e.d. bet; nothing about self-reference obstructs a weighting. By hand: at thresholds $v < s$ the weighting $\operatorname{Ind}_\delta\big(\ulcorner E^A_n(O^1_n)\urcorner > v\big)$ saturates and the conclusion is $E^H_n(O^1_n) \gtrsim_n v$, true since $E^H_n(O^1_n) \to s$; at $v = s$ the quote sits at the weighting's foot, the weighting tends to $0$, and the instance is vacuous; at $v > s$ likewise; the below-threshold halves mirror with the down-ramp.

So at the hovering quote the *soft* above-threshold inequality is vacuous-true, the *hard* one is false, and the gap between them is exactly the punishing structure's $s(1-s)$. The two-option identity computes the hard form; the reverse triangle's closing arrow therefore targets a false statement at precisely the instances its restricted hypothesis has gone silent on. This is the soft/hard boundary of [[total-trust-implies-value-telescoping]] §"The soft/hard boundary" biting the loop itself.

## What breaks, and what survives

- **Broken: the reverse triangle as an independent proof.** Its recorded closing gloss — "full-menu Value contains the two-option case, so Value ⟹ Total Trust in full" ([[two-option-value-iff-total-trust]]) — silently changed meaning when Value's quantifier was restricted on 2026-07-25: the honest, maximal-true Value does not contain the liar probe, and cannot (computation 2). A scope flag now sits on that page.
- **Survives: the implication itself.** Restricted Value still implies full soft Total Trust — but only via the forward arrows: probe menus are self-stable ([[value-implies-tower]] §"The scope condition is vacuous here"), so restricted Value delivers the full Tower, and the fold enters Total Trust with no scope condition. The reverse triangle closes only by borrowing exactly those two arrows — that is, by becoming the forward loop.
- **Survives: instance-by-instance patches, at a price.** At a *convergent* hovering quote the saturating instances are recoverable from shifted constant probes $\{O^1_n, \text{const } v\}$ with $v$ bounded away from the quote (provably-strict argmax, hence stable), and the at-threshold instances are vacuous — so this particular counterexample can be dodged threshold-by-threshold. But the dodge is bookkeeping the fold never needs, it recurses per-subsequence for quotes engineered to hover at moving thresholds, and its general viability is unassessed. The economical statement stands: **selection-based entry into Total Trust dies at the threshold; weighting-based entry does not notice the threshold.**

## The moral: who picks the menus

The asymmetry between the two directions is not in the mathematics of any single arrow but in quantifier polarity at the Value corner. **Leaving** Value ([[value-implies-tower]]), the *prover* picks the menus, and picks self-stable probes — the scope restriction never propagates. **Entering** Total Trust from Value, the *instance* picks the menu, and an adversarial instance sits its quote on the threshold, where honest Value goes silent and the hard-form target is false. The fold escapes the dilemma categorically: a weighting multiplies the bet instead of selecting between options, a ramp of a published quote is decided ledger arithmetic whatever the quote does, and no selection event is ever conditioned on. That is why the forward loop can charge the decision-theoretic scope condition exactly once, on its first arrow, and stay quantifier-tight the rest of the way around — and why the loop's direction is forced, not stylistic.

## Grade-invariance (added 2026-08-03)

The comparison transports one grade down. At the scheduled weighted-average grade of the varying-question lab (Theorem SS's notions), the liar probe's Value deficit is a per-day constant, so it survives averaging verbatim: the weak reverse closure through two-option menus computes averaged *hard* above-threshold inequalities, refuted at the probe, while the averaged *soft* instances are vacuous there — and the weak loop must likewise enter Total Trust through the fold. The weak-grade loop, the transport of the scope condition, and the refutation of the no-scope-condition weak-Value conjecture: [[weak-loop-and-value-transport]].

## Where the reverse triangle remains the simplest

- **Finite-exact / surrogate / DDB-style settings.** Hard indicators are legal, expectations exact, and — decisively — the bet family is not quote-closed (a DDB frame is not world-measurable), so liar probes cannot be formed and the leak has no ammunition. There the kernel-checked lattice of [[value-iff-mart]] is genuinely the lighter proof, which is why it was built first; nothing here disturbs it *as a surrogate-level statement*. This also explains why DDB could use their Lemma 7.1 innocently in both directions.
- **The hedged loop (observation, unwritten).** Weaken the Value corner to the $\delta$-hedged strategy and the selection disappears in favour of a weighting: [[soft-self-endorsement]] already delivers hedged Value with no conditional-stability and no tie-break, and the soft form of the two-option identity ([[two-option-value-iff-total-trust]] §Soft/LI form, kernel-checked at fixed $s$) closes hedged Value ⟺ soft Total Trust with nothing but `loe`. A loop **Total Trust ⟹ Tower ⟹ hedged Value ⟹ Total Trust** would be scope-condition-free at every corner — plausibly the simplest tight loop available, at the price of the Value corner no longer being the instrumental argmax notion. The one unwritten arrow, Tower ⟹ hedged Value, looks like a direct consequence of the fold equality of [[tower-implies-total-trust]] §"The other direction" (the hedged strategy is a combination of ledger-decided weightings). Worth a page if the hedged notion earns independent standing.

## Status

**PROVED (prose, this page)** — the liar-probe computations (1)–(4), given Paradox Resistance (4.11.2, quote form) and the standard `loe`/`expprovind` carries; a natural machine-check candidate (a finite worlds-sum plus two `Approx` carries — added to [[open-problems]] item 6; the Lean honesty caveat of [[conventions-and-status-labels]] applies). **INTERPRETATION** — the cost accounting and the who-picks-the-menus moral. **Unvetted by Abram as of 2026-08-02; not machine-checked.** Written in the 2026-08-02 session, from Abram's request to compare the two loop directions and see which is actually simplest.

## Related

- [[total-trust-implies-value]], [[value-implies-tower]], [[tower-implies-total-trust]] — the forward loop this page certifies as the forced direction; §Necessity there is the parent of the liar probe
- [[total-trust-implies-mart]], [[mart-implies-value]], [[two-option-value-iff-total-trust]] — the reverse triangle and its per-arrow debts
- [[value-iff-mart]] — the assembled lattice; its ⚠ updates are this page's prehistory
- [[total-trust-implies-value-telescoping]] §"The soft/hard boundary" — the hedged/hard gap this page shows biting the loop itself
- [[soft-self-endorsement]] — the hedged Value corner of the proposed hedged loop
- [[ledger-decided-tie-breaks]], [[defining-exogeneity]] — the selection-side apparatus the fold never consults
- [[open-problems]] — machine-check candidates (item 6)

*Source: this page (2026-08-02 Claude Code session); the punishing option from [[total-trust-implies-value]] §Necessity, the identity from [[two-option-value-iff-total-trust]], Paradox Resistance numbering per the dictionary in [[conventions-and-status-labels]].*
