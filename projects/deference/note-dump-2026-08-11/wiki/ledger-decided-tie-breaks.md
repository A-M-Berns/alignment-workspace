# Tie-breaks must be ledger-decided

*The argmax strategy's tie-break rule must be computable from the published estimates — equivalently, $\Gamma$-decided given the ledger. This is a **necessary** condition, not bookkeeping: a definable-but-undecidable tie-break passes every legality check (it still yields a perfectly good e.d. LUV) yet breaks F1 by correlation, and with an adversarial rule breaks Value itself — the DDB frame/diagonal phenomenon re-entering the single-belief-state setting through the one crack the ties leave open.*

**Provenance.** Produced in the 2026-07-23 Claude Code session, in the discussion that also produced the e.d./e.c. distinction ([[setting-and-notation]] §LUV): Abram asked why the corpus's "any computable tie-break" is a restriction at all, refuted the first answer offered (legality — wrong, since e.d. LUVs need no computable values), and asked what the real reason is; the F1-correlation answer below is the result. **Unvetted by Abram as of 2026-07-23.**

**⚠ Reframing (2026-07-25, refined 2026-07-26).** This page's baseline was the exact-F1 picture, since retracted ([[total-trust-implies-value]]): for inductor-experts even ledger-decided tie-breaks yield endorsement only asymptotically, modulo introspection and a scope condition. The counterexample below stands — it refutes the asymptotic form too — but its moral is now subsumed by **conditional-stability**, and the subsumption is sharper than first recorded. Against the mass-weighted *one-sided* (H3), the two $\psi$-rules below separate exactly as they should:

- *Adversarial rule* (select $O^1$ iff $\neg\psi$): each product $\mathbb{1}[\mathrm{sel}=j]\cdot O^j$ is identically $0$ while $\mathbb{P}(\mathrm{sel}=j)\,E(O^j) = \tfrac12\cdot\tfrac12$, so (H3)'s two sides differ by $-\tfrac12$. **Excluded** — correctly, since this rule breaks Value outright.
- *Clairvoyant rule* (select $O^1$ iff $\psi$): each product is $\mathbb{1}_\psi$ resp. $\mathbb{1}_{\neg\psi}$, so the left side is $1$ against $\tfrac12$ on the right, a surplus of $+\tfrac12$. **Admitted** — also correctly: this rule *overshoots* ($E^\ast(\widehat S) = 1 > \tfrac12$), so it violates F1 as an equality but satisfies Value. Only the exact-F1 framing had reason to reject it.

The earlier note here said conditional-stability rejects the $\psi$-tie-break simpliciter ($E(O^1 \mid \mathrm{sel}=1) = 1 \ne \tfrac12$); that was the two-sided per-index form, which over-rejects. Ledger-decidedness retains its *definitional* role: the selector bits must be ledger arithmetic for $\widehat S$ to be a readable e.d. LUV and for the novice's weights to exist.

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H$ a logical inductor; expert $E^\ast$ observable and coherent. A finite menu of bounded bets $O^1, \dots, O^K$; the expert's estimates $E^\ast(O^j)$ are published on the ledger as $\Gamma$-decided rational facts. The **argmax strategy** is $\widehat S := O^{j^\ast}$ with $j^\ast$ selected from $\arg\max_j E^\ast(O^j)$ by some **tie-break rule** — the object under examination. **F1** is the fact the Value proofs lean on: $\Gamma \vdash E^\ast(\widehat S) = \max_j E^\ast(O^j)$.

## What legality does *not* require

A LUV is a formula; "efficient" constrains the production of *descriptions*, never the computability of described values ([[setting-and-notation]] §LUV — the e.d. point). So a tie-break rule of the form "the least $j$ in the argmax set satisfying $\psi(j)$, else the least" — with $\psi$ definable but undecidable — still yields a legal bet: the description is short and efficiently produced, the selection is $\Gamma$-provably unique (least element of a provably nonempty definable set), and it provably lands in the argmax set. Nothing in the definition of an e.d. LUV, in the market, or in the trading framework rejects it. **Computability of the tie-break cannot be derived from legality.**

## What F1 does require — and the correlation counterexample

With a ledger-decided rule, once the ledger facts are in, $\Gamma$ proves an outright **identity** $\widehat S = O^j$ for a specific $j$, and coherence transfers the estimate: $E^\ast(\widehat S) = E^\ast(O^j) = \max$. With an undecidable rule, $\Gamma$ proves only a **disjunction** — and expectations do not commute with disjunctions under correlation: the expert's estimate of $\widehat S$ becomes a mixture of *conditional* estimates, which can detach from the max entirely.

**Counterexample.** Let $\psi$ be undecidable with expert credence $P(\psi) = \tfrac12$. Menu: $O^1 = \mathbb{1}_\psi$, $O^2 = \mathbb{1}_{\neg\psi}$ — so the published estimates tie at $\max = \tfrac12$, and the argmax set is $\{1, 2\}$.

- *Clairvoyant rule* "select $O^1$ iff $\psi$": then in every world $\widehat S = \mathbb{1}_\psi \cdot \mathbb{1}_\psi + \mathbb{1}_{\neg\psi} \cdot \mathbb{1}_{\neg\psi} = 1$, so
  $$ E^\ast(\widehat S) = 1 \;>\; \tfrac12 = \max_j E^\ast(O^j). $$
- *Adversarial rule* "select $O^1$ iff $\neg\psi$": then $\widehat S \equiv 0$, so $E^\ast(\widehat S) = 0 < \tfrac12$ — and **Value itself fails substantively**, not just its proof: a novice that trusts the expert's estimates rates the fixed option $O^1$ at $\tfrac12$ and the "followed" strategy at $0$. Deferring loses. (Rightly so: following the expert with a $\psi$-adversarial tie-break is not following the expert — it is following an adversarial coin.)

Both rules are efficiently describable, provably unique, and provably select from the argmax set — they pass every check of the previous section. What they violate is exactly one thing: *the selection is not decided by $\Gamma$ given the ledger.* Note also where the corpus had silently assumed this: the **derived-estimates convention** ($E^\ast(c + \sum_j \alpha_j O^j) := c + \sum_j \alpha_j E^\ast(O^j)$ for *ledger-computable* coefficients) simply does not apply to these $\widehat S$ — the selector coefficients are not ledger-computable — which is the convention quietly excluding the pathology.

## Ledger-decided ⟺ computable from the ledger

The right condition is: **$\Gamma$ + the ledger facts decide which option was selected.** This is extensionally equivalent to "the tie-break is a computable function of the published estimates": one direction is $\Gamma$ representing computable functions and proving their computations; conversely, if the selection is always $\Gamma$-decided from the ledger, enumerating proofs computes it. So the corpus's traditional phrase "any computable tie-break" picks out the right class — but for a reason no page had stated: not because an uncomputable strategy fails to be a bet (it doesn't fail), but because an *undecided selection* severs coherence's grip on $E^\ast(\widehat S)$. (Efficiency — producing the rule's formula in polynomial time and evaluating it cheaply from the ledger — is a separate, mild requirement, the usual e.d./trader-cheapness bookkeeping.)

## Interpretation: the frame re-enters through the tie

An undecided selector is a *world-dependent recommendation*: which option "the expert picked" varies with the world, exactly like a DDB frame's $S_w$ — and $E^\ast(\widehat S)$ becomes a diagonal-style quantity, the very thing whose reconstruction makes DDB's Total Trust ⟹ Value direction excruciating ([[reversal-of-difficulty-vs-ddb]]). The single-belief-state setting is cheap *because* the followed strategy is one option with a $\Gamma$-decided identity ([[expert-conditions]]); the tie is the one crack where world-dependence can sneak back in, and ledger-decidedness is what seals it. The adversarial rule above is the LI-internal cousin of DDB's anti-expert.

## Consequences for the corpus

- Everywhere the apparatus says "least index; any computable tie-break" ([[deference-notions]], [[mart-implies-value]], the TT ⟹ Value cluster), read: any **ledger-decided** tie-break — and this is *necessary for F1*, not a convenience assumption. The pages now say so.
- The F1 cost accounting of [[mart-implies-value]] §Remark (coherence + introspection) gains a third line item: ledger-decidedness of the selection.
- The freedom Value's definition grants ("any computable tie-break") is exactly the freedom that keeps F1 tie-break-independent: every ledger-decided rule returns *some* argmax element as a provable identity, so the estimate is the max regardless of which.

## Status

**PROVED (prose, this page)** — the counterexample is elementary and self-contained; the ledger-decided ⟺ computable equivalence is a two-line proof-search argument. **Unvetted by Abram as of 2026-07-23; not machine-checked; produced by Claude in the 2026-07-23 session with no earlier source.** The counterexample would be a very easy finite-exact Lean check.

## Related

- [[setting-and-notation]] — the e.d./e.c. distinction this page leans on; the derived-estimates convention it exposes
- [[deference-notions]] — the menu apparatus and F1
- [[mart-implies-value]] — the F1 cost remark this page extends
- [[expert-conditions]] — single state cheap, frame dear; this page locates the crack between them
- [[reversal-of-difficulty-vs-ddb]] — the diagonal phenomenon the undecided selector re-imports
- [[total-trust-implies-value]], [[provable-bound-respect]], [[keep-or-switch-telescope]], [[one-shot-hedge]] — the proofs whose tie-break hygiene this page underwrites

*Source: this page (2026-07-23 Claude Code session); apparatus from deference-v6 §1.1 (`deference-in-logical-induction-v6.md`).*
