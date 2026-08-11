# The δ-hedged variant: soft self-endorsement and hedged Value (true setting)

*Companion to [[total-trust-implies-value]], split out 2026-07-26. The soft-argmax strategy trades a $2\delta$ slack in the conclusion for a dramatically smaller bill: no tie-break, no conditional-stability — it survives even punishing menus — at the price of an introspection-for-features step. Setting, notation, and hypothesis (H1) are exactly those of the main page. Unvetted.*

## The soft strategy

$$ T_{\delta,n} := \sum_j \theta_j\, O^j_n, \qquad \varphi_j := \operatorname{Ind}_\delta\big(m^j_n > M_n - 2\delta\big), \quad \theta_j := \varphi_j \Big/ \sum_k \varphi_k. $$

The top option has $\varphi = 1$, so the normalization is safe; every $j$ with $\theta_j > 0$ has $m^j_n > M_n - 2\delta$; each $\theta_j$ is a **continuous**, $A$-market-generable feature of $A$'s own day-$n$ prices (the $m^j$ are finite sums of prices). No tie-break is needed at all — the soft strategy dissolves ties instead of breaking them.

## Soft self-endorsement

**Lemma (modulo one named item).** $E^A_n(T_{\delta,n}) \gtrsim_n M_n - 2\delta$, hence $E^A_n(T_{\delta,n} - O^i_n) \gtrsim_n -2\delta$ for every $i$.

*Proof sketch.* $A$'s own `loe` (4.8.4) with market-generable coefficients gives $E^A_n(\sum_j \theta_j O^j_n) \approx_n \sum_j E^A_n(\theta_j O^j_n)$; the fold step $E^A_n(\theta_j O^j_n) \approx_n \theta_j\, m^j_n$ is "the expert knows the weight" (`hknow`) for **continuous features of its own current prices** — the introspection condition of [[expert-conditions]] extended from bare estimates to market-generable features; then $\sum_j \theta_j m^j_n > M_n - 2\delta$ by construction. The feature-introspection extension is the named gap ([[open-problems]] item 4); for the future-self instance it is the `epr`/`er`/`st` family's territory. $\blacksquare$ (modulo)

**Margins corollary.** If eventually the argmax leads its runner-up by a fixed $\eta > 0$, then for $\delta < \eta/2$ the soft and hard selectors coincide ($\theta_{j^\ast} = 1$), so soft self-endorsement yields *hard* self-endorsement — an alternative route to the main page's Lemma 2 that replaces conditional-stability with a margin condition.

## δ-hedged Value

**Theorem.** Assume (H1) and soft self-endorsement. For every fixed $i$ and every $\delta > 0$:

$$ E^H_n\big(T_{\delta,n}\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big) - 2\delta. $$

*Proof.* $E^A_n(T_{\delta,n} - O^i_n) \gtrsim_n -2\delta$ (the lemma, $A$'s `loe` with constant coefficients, $m^i_n \le M_n$); the main page's Lemma 1 (bounds transfer) with $s = -2\delta$; the novice's `loe` splits. $\blacksquare$

## Robustness: the hedge survives punishment ⚠

For the proportional punishing menu $O^j = 1 - \theta_j$, the system has a consistent fixed point: the quotes price the punishment in ($m^j = 1 - \theta_j$), and $E^A_n(T_\delta) \approx \sum_j \theta_j m^j$ still lands within $2\delta$ of $M_n$ — soft self-endorsement is quote-relative and holds regardless. Contrast the hard selector, which on the punishing menu builds a liar with no fixed point ([[total-trust-implies-value]] §Necessity): the soft selector has a Brouwer fixed point instead. The exactness/paradox boundary of the whole corpus, again — and the reason the hedged variant needs **no decision-theoretic scope condition**: what it endorses is defined by the same quotes that already absorbed whatever the environment does.

## Status

**PROVED modulo the feature-introspection step** ([[open-problems]] item 4); punishment-robustness is a ⚠ this-session observation. **Unvetted by Abram as of 2026-07-26; not machine-checked.** Note the trade against the main page: weaker conclusion (a $2\delta$ slack, and $T_\delta \ne \widehat S$), radically weaker hypotheses (no (H3), no tie-break).

## Related

- [[total-trust-implies-value]] — setting, hypotheses, Lemma 1, and the argmax theorem this page is the fallback for
- [[keep-or-switch-telescope]], [[one-shot-hedge]] — the surrogate-era hedged routes (different formulation)
- [[expert-conditions]] — the introspection condition being extended
- [[open-problems]] — the feature-introspection gap

*Source: split from [[total-trust-implies-value]] 2026-07-26; originally from the 2026-07-24 rewrite (archived transcript in `imported-chats/`).*
