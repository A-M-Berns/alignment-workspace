# Value ⟹ Tower (the probe-menu argument)

*A direct proof, in the true LI setting, that a novice who Values an introspective expert also Towers it — without passing through Total Trust, without soft cuts, and without any decision-theoretic scope condition. The whole argument is the two-option identity of [[two-option-value-iff-total-trust]] aimed at one specific menu: "take the bet **Z minus what the expert says Z is worth**, or lose a fixed small amount." The expert always takes the bet; Value then forces the novice to agree with the expert about $Z$. **Unvetted by Abram as of 2026-07-27.***

**Name.** "Tower" is this page's word for what the rest of the corpus calls **Mart** ([[deference-notions]]): the universally quantified iterated-expectation collapse, one asymptotic equality per e.d. LUV sequence. There is no distinction — same statement, plainer name. The *conditional* tower (weighted form, `ccee`) is not a separate hypothesis either: the fold lemma shows the universal tower already contains it.

## Setting

The setting of [[total-trust-implies-value]], unchanged. $\Gamma$ a theory with its deductive process; $H \dashv \mathcal{C}_H$ and $A \dashv \mathcal{C}_A$ logical inductors over $\Gamma$ — novice and expert. Expectations are the LI paper's price-integrals, $E^H_n$ and $E^A_n$, taken of *formulas*; $[a,b]$-LUVs are allowed, the $[0,1]$ statements transporting affinely.

Two objects need naming before anything else, because the whole argument is about their relationship.

**The quote as a bet.** For an e.d. sequence of $[a,b]$-LUVs $(Z_n)$, write $\ulcorner E^A_n(Z_n)\urcorner$ for the *formula naming the expert's day-$n$ estimate of $Z_n$* — a rational-valued expression whose value is whatever number $A$'s day-$n$ computation outputs, decided by day $e(n) \ge n$ and published to the ledger. This is an $[a,b]$-LUV in its own right (an inductor's price-integral of an $[a,b]$-LUV lands in $[a,b]$), and the novice can read it $\mathcal{C}_H$-cheaply. That it is a legal bet at all is the **observability** assumption; everything below depends on it.

**The gap-bet.** Given $(Z_n)$, put

$$ G_n \;:=\; Z_n \;-\; \ulcorner E^A_n(Z_n)\urcorner, $$

a $[a-b,\, b-a]$-LUV: "hold $Z_n$, and pay the expert's price for it." Its negation $-G_n = \ulcorner E^A_n(Z_n)\urcorner - Z_n$ is the other side of the same trade.

**The target (Tower at $(Z_n)$).**

$$ E^H_n(Z_n) \;\approx_n\; E^H_n\big(\ulcorner E^A_n(Z_n)\urcorner\big), \qquad\text{where } x_n \approx_n y_n :\Leftrightarrow x_n - y_n \to 0. $$

The novice's estimate of $Z$ agrees with its estimate of *the expert's estimate of $Z$*. By the novice's `loe` (4.8.4) with unit coefficients this is the same as $E^H_n(G_n) \to 0$, and that is what gets proved.

## Hypotheses

**(H2) Introspection.** The expert asymptotically knows its own quotes: $E^A_n(\ulcorner E^A_n(X)\urcorner) \approx_n E^A_n(X)$, within $o(1)$ ([[expert-conditions]]; the `epr`/`er` family for the future-self instance). This is the *only* expert-side hypothesis, and it is the same (H2) the companion theorem uses.

**(V) Value, on probe menus.** The novice satisfies Value ([[deference-notions]]) on the two-option menu sequences constructed below — each consisting of a gap-bet and a constant. Concretely: for every fixed option index $i$, $E^H_n(\widehat S_n) \gtrsim_n E^H_n(O^i_n)$, where $\widehat S_n$ is the option the expert's quotes rate highest.

What is **not** assumed, and is worth listing because the corresponding page for the Total-Trust route assumes all of it: no Total Trust; no conditional-stability (H3) — §"The scope condition is vacuous here" shows it holds automatically on these menus; no ledger-decided tie-break, because the argmax below is eventually *strict*; no soft/ramped threshold cuts; no closure of any bet class beyond "the menu class contains gap-bets and constants."

## The probe menu

Fix a rational $\varepsilon > 0$ and offer the novice's expert the two-option menu

$$ \mathcal{O}_n \;=\; \big\{\, G_n, \;\; \text{const}(-\varepsilon) \,\big\}. $$

The idea in one line: **a constant option is a perfect probe.** Value on a menu $\{B, \text{const } c\}$ says nothing at all unless you know which option the expert takes — but once the expert provably takes $B$, Value collapses to the single inequality $E^H_n(B) \gtrsim_n c$, which is a direct statement about the novice's own valuation of $B$. So the art is picking a bet whose quote is pinned somewhere known. The gap-bet is exactly such a bet: introspection nails its quote to $0$, whatever $Z$ is.

## Proof

**Step 1 — the expert quotes the gap-bet at zero.** By the expert's own `loe` (4.8.4), splitting a difference with unit coefficients, and then (H2):

$$ E^A_n(G_n) \;\approx_n\; E^A_n(Z_n) \;-\; E^A_n\big(\ulcorner E^A_n(Z_n)\urcorner\big) \;\approx_n\; 0 . $$

Note what this does **not** depend on: anything whatsoever about $Z_n$. The gap-bet's quote is pinned by the expert's self-knowledge alone. (This is also why the probe menu can never turn into a punishing menu — see §Necessity-freedom below.) The same computation applied to $-G_n$ gives $E^A_n(-G_n) \approx_n 0$.

**Step 2 — the expert provably takes the gap-bet.** The two quotes on the menu are $E^A_n(G_n) \to 0$ and $E^A_n(\text{const}(-\varepsilon)) \approx_n -\varepsilon$ (the expert's `expprovind` on a provably-constant LUV). Their difference tends to $\varepsilon > 0$, so there is an $N$ with the gap-bet strictly top-quoted for all $n \ge N$ — strictly, so no tie-break is consulted. Both quotes are rationals output by a computable process and $\Gamma$ represents computable functions, so $\Gamma$ decides them, and therefore

$$ \Gamma \vdash \widehat S_n = G_n \qquad (n \ge N). $$

**Step 3 — Value against the constant option.** Value on this menu, at the index of the constant:

$$ E^H_n(G_n) \;\underset{\texttt{expprovind}}{\approx_n}\; E^H_n(\widehat S_n) \;\underset{\textbf{Value}}{\gtrsim_n}\; E^H_n\big(\text{const}(-\varepsilon)\big) \;\underset{\texttt{expprovind}}{\approx_n}\; -\varepsilon . $$

The first and last steps are `expprovind` (4.8.10) carrying provable identities — the identity of Step 2 for the first, "this LUV is provably $-\varepsilon$" for the last. The finitely many days below $N$ are invisible to a $\liminf$ (patch the theorem sequence with $\top$ below $N$ to keep it e.c., exactly as in [[total-trust-implies-value]] Lemma 1). Value against the *other* option is never used.

**Step 4 — the other side.** Run Steps 1–3 again on the menu $\{-G_n, \text{const}(-\varepsilon)\}$. Step 1 gave $E^A_n(-G_n) \approx_n 0$, so the expert takes $-G_n$ by the same margin, and Value yields $E^H_n(-G_n) \gtrsim_n -\varepsilon$, i.e. $E^H_n(G_n) \lesssim_n \varepsilon$ after the novice's `loe`.

**Step 5 — close.** Steps 3 and 4 hold for every rational $\varepsilon > 0$, each with its own menu sequence, so $\liminf_n E^H_n(G_n) \ge 0$ and $\limsup_n E^H_n(G_n) \le 0$: that is $E^H_n(G_n) \to 0$. The novice's `loe` splits it into $E^H_n(Z_n) \approx_n E^H_n(\ulcorner E^A_n(Z_n)\urcorner)$ — Tower at $(Z_n)$. Since $(Z_n)$ was an arbitrary e.d. sequence in the class, this is the universal Tower on that class. $\blacksquare$

**Why $\varepsilon$ must be fixed per menu.** One might hope to run a single menu sequence with a shrinking margin $\varepsilon_n \to 0$ and finish in one pass. That needs the expert's quote for $G_n$ to beat $-\varepsilon_n$, which requires a *rate* for the introspective convergence of Step 1 — and (H2) supplies none. So the argument is a family of menu sequences indexed by $\varepsilon$, diagonalized at the end, and it yields no rate.

## The scope condition is vacuous here

Value is **false** in general — selection-punishing menus refute it outright ([[total-trust-implies-value]] §Necessity) — so the honest form of hypothesis (V) restricts the menu quantifier to menus satisfying conditional-stability (H3 there). It is worth checking that this restriction does not quietly delete the menus this page needs. It does not; they satisfy (H3) automatically.

By Step 2, $\Gamma \vdash \mathrm{sel}_n = 1$ for $n \ge N$, so the expert's own provability induction gives $\mathbb{P}^A_n(\mathrm{sel}_n = 1) \to 1$ and $\mathbb{P}^A_n(\mathrm{sel}_n = 2) \to 0$. In the denominator-free form of (H3), $\sum_j \big[E^A_n(\mathbb{1}[\mathrm{sel}_n = j]\cdot O^j_n) - \mathbb{P}^A_n(\mathrm{sel}_n = j)\,E^A_n(O^j_n)\big]$:

- the gap-bet's term: $\mathbb{1}[\mathrm{sel}_n=1]\cdot G_n$ is provably $G_n$ and the mass is $1 - o(1)$, so the term is $o(1)$;
- the constant's term: both halves are $-\varepsilon\,\mathbb{P}^A_n(\mathrm{sel}_n=2) + o(1)$ with the mass tending to $0$, so the term is $o(1)$.

The sum tends to $0$, so (H3) holds with room to spare. **The expert already knows what it will pick, so there is no selection–value correlation for the scope condition to catch.**

## Necessity-freedom: the probe menu cannot become a punishing menu

The failure mode that refutes unconditional Value is a menu whose values chase its own selection, forcing the expert's quotes into a liar's fixed point with interior self-prediction mass. That cannot happen here, and the reason is structural rather than a side condition: **Step 1 pins the gap-bet's quote at $0$ using nothing but the expert's self-knowledge**, independent of $Z_n$'s syntax. Even if $Z_n$ is wildly selection-referencing — including referencing the selection on *this* menu — its quote and the quote of its own price move together, so the difference is $o(1)$ regardless, the argmax stays strict, and the mass stays degenerate. There is no fixed-point equation to solve.

This is also the sharpest available argument against the *menu-intrinsic* definitions of exogeneity surveyed at [[defining-exogeneity]]. Under those (menu formulas may mention no ledger atoms), probe menus are illegal by construction — a gap-bet is built out of the ledger — and Value ⟹ Tower is severed outright. Conditional-stability admits them because it asks about correlation rather than syntax, and so can distinguish a menu that reads the expert's *estimate* (benign; degenerate mass) from one that reads the expert's *selection* (the pathology).

## What the theorem costs

- **Expert:** introspection (H2), and its own `loe`. Nothing else — no coherence beyond what an inductor has, no exactness at any finite day.
- **Novice:** `loe` (4.8.4) and `expprovind` (4.8.10), both free LI theorems.
- **Channel:** observability — $\ulcorner E^A_n(Z_n)\urcorner$ must be a legal e.d. LUV — and the ledger must publish the quotes for the probe menu's two options, so that the selection is readable and $\widehat S_n$ is itself an e.d. LUV.
- **Menu class:** must contain, for each target $(Z_n)$ and rational $\varepsilon > 0$, the menus $\{\pm G_n, \text{const}(-\varepsilon)\}$. This is the substantive assumption, and §"Is this a fair demand?" is about it.
- **Bounds:** the two options must share a range; $[a-b, b-a]$ works for $\varepsilon \le b-a$.

## Is this a fair demand on Value?

Value is meant to be the *instrumental* notion — "let the expert pick" beats committing to a fixed option — and probe menus are not decision problems anyone faces. "Would you rather hold $Z$ and pay the expert's price for it, or lose $\varepsilon$?" is a bet, not a choice. Two readings, both worth holding:

- **In favour.** Trust in the deference literature has always been cashed out as willingness to bet: DDB's Total Trust is a family of conditional bets, and the two-option menu is precisely how they exhibit a Total-Trust instance as a Value instance (their Lemma 7.1). Demanding that a novice not think the expert's own fair bet is a bad deal is the minimal betting content of trust, and this page shows it is *exactly* the tower.
- **Against.** The stretch is real, and it is the same artificiality that made syntactic exogeneity conditions attractive. On a genuinely restricted menu class — ledger-free menus, the faithful-acceleration gate family, DDB frames where the selection is not world-measurable — probe menus are unavailable and **no tower follows**. Those are exactly the separations catalogued at [[value-iff-mart]] §"Where separations survive", and nothing here disturbs them.

So the theorem should be read as: *at full quantifier strength, where menus may reference the expert's published estimates, Value is already the tower.* The separations live below that strength, as they always have.

## Place in the circuit

With conditional-stability assumed as a restriction on the admissible menu sequences, the three notions close a loop, each arrow direct:

$$ \textbf{Total Trust} \;\longrightarrow\; \textbf{Value} \;\longrightarrow\; \textbf{Tower} \;\longrightarrow\; \textbf{Total Trust} $$

- **Total Trust ⟹ Value** — bounds transfer plus self-endorsement: [[total-trust-implies-value]]. This is the expensive leg; it is where conditional-stability and the introspective-concentration lemma are spent.
- **Value ⟹ Tower** — this page. Cheap: introspection only.
- **Tower ⟹ Total Trust** — the fold at the ramp weight $\operatorname{Ind}_\delta(E^A_n(X_n) > t)$, plus the provable threshold bound $E^A_n(X_n)\cdot w \ge t\cdot w$ carried through $E^H_n$ by `expprovind`: [[deference-notions]] §Total Trust. Also cheap.

Each arrow needs its own closure of the bet class — ramp-weighted products for the third, argmax composites for the first, gap-bets and constants for this one — but all three live inside the single natural class of e.d. bounded LUV-combinations built from the base bets together with the expert's observable estimates. So the loop closes without enlarging anything, and one lap is a consistency check rather than a ratchet. The price paid identically at every corner is that the ledger must price that whole class: free for the future-self expert (`epr`/`er` price everything), a real assumption for a thin-channel AI expert.

The alternative route to this arrow — Value ⟹ Total Trust ([[two-option-value-iff-total-trust]]) then Total Trust ⟹ Tower ([[total-trust-implies-mart]]) — remains valid but is a detour: it re-enters the Total-Trust corner the loop has already left, and it pays for soft cuts and a $\delta$-diagonalization that the pinned quote makes unnecessary.

The circuit's direction is itself forced, not aesthetic. Leaving Value, the *prover* picks the menus — this page's probes, which are self-stable. Entering Total Trust from Value, the *instance* picks them, and at bets whose quote hovers on the threshold the needed two-option menu fails conditional-stability with Value genuinely false on it — so the loop must exit Value here and enter Total Trust through the fold. The liar-probe certificate and the full comparison of the two directions: [[loop-direction]].

## Status

**PROVED (prose, this page)** — modulo nothing; the argument is Step 1 (expert `loe` + (H2)), Step 2 (a decided comparison), and two `expprovind` carries around one Value instance. **Unvetted by Abram as of 2026-07-27; not machine-checked.** Produced in the 2026-07-27 Claude Code session, as the direct replacement for routing Value ⟹ Tower through Total Trust. A good machine-check candidate: the chain is three `Approx`/`AsympLE` compositions of the shape already exercised in `lean-deference`, with the Value instance and the two provable identities as named hypotheses — the Lean honesty caveat of [[conventions-and-status-labels]] applies as always.

Downstream claims this revises: [[value-iff-mart]]'s per-arrow table, which routes Value to the tower through Total Trust; and the framing of [[total-trust-implies-mart]], which remains the *Total Trust* ⟹ Tower arrow but still states its Step 1 in the retracted surrogate form ("$\Gamma \vdash E^\ast(D) = 0$") and should be rewritten as two applications of [[total-trust-implies-value]] Lemma 1 at $s = 0$.

## Related

- [[total-trust-implies-value]] — the expensive leg of the loop; its Lemma 1 and hypothesis (H2), and the punishing-menu counterexample that forces the scope condition
- [[two-option-value-iff-total-trust]] — the two-option identity this page specializes; the other, older use of a constant option as a probe
- [[total-trust-implies-mart]] — Total Trust ⟹ Tower by gap-bets (the arrow this page does *not* replace)
- [[deference-notions]] — Tower/Mart, the fold, Total Trust, Value; the third arrow of the loop
- [[defining-exogeneity]] — why a syntactic scope condition would sever this arrow
- [[expert-conditions]] — what introspection is and what it costs in each instance
- [[value-iff-mart]] — the assembled equivalence, whose arrow table this page revises
- [[loop-direction]] — why the loop runs in this direction (the liar probe; who picks the menus)
- [[trichotomy-where-value-sits]], [[faithful-acceleration-result]] (both planned) — the restricted domains where probe menus are unavailable and no tower follows

*Source: this page (2026-07-27 Claude Code session), built on the two-option identity of deference-v6 §1.2 and the true-setting apparatus of [[total-trust-implies-value]]. Transcript: `imported-chats/2026-07-23__tt-value-cluster-revision-arc__5cf76191.md`, messages 65–71 — the argument is developed at 66 and stress-tested at 68.*
