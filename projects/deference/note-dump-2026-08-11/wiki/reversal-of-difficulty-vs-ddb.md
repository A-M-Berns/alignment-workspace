# The reversal of difficulty vs. DDB

*In DDB, Total Trust ⟹ Value is the "excruciating" direction and Value ⟹ Total Trust the easy one; in LI every arrow goes soft — the two-option identity makes Value ⟹ Total Trust exact, the telescoping proof makes Total Trust ⟹ Value cheap, and the gap-bet argument makes even Total Trust ⟹ Mart a two-liner. The convex geometry is not relocated but* confined: *it survives exactly where bets cannot mention the expert.*

## Setting

An **interpretation page** comparing two frameworks: DDB's finite probability frames (Dorst–Levinstein–Salow–Husic–Fitelson 2021, as read in deference-v6 §0.5) and this wiki's abstract single-expert LI setting ([[setting-and-notation]]) with an observable, coherent (introspective) expert. Sources: deference-v6 §1.3 (the table) and §2.1 (the moral), sharpened by the DDB-compatibility caveat of [[total-trust-implies-value-telescoping]] (2026-07-20 session; now the overview of the split proof cluster).

## The table

| | Value ⟹ Total Trust | Total Trust ⟹ Value |
|---|---|---|
| **DDB** (finite-frame expert) | easy (their Lemma 7.1 two-option construction) | **hard** — the "excruciating" convex-hull reconstruction plus Blackwell–Geanakoplos value-of-information |
| **LI** (observable coherent expert) | easy, **exact** — the boxed two-option identity, per $(X,s)$, no slack ([[two-option-value-iff-total-trust]], deference-v6 §1.2) | easy — the keep-or-switch telescope ([[keep-or-switch-telescope]]; route overview at [[total-trust-implies-value-telescoping]]) |

An honesty note on the LI row's right cell: deference-v6 §1.3 filled it with "§1.1, two towers" — i.e. it routed Total Trust ⟹ Value **through Mart**, which quietly presupposes the squeeze (the genuinely hard TT ⟹ Mart step). That was the gap the 2026-07-20 session found and closed: the telescoping proof derives the cell from Total Trust *alone* (at threshold $0$, for the $\delta$-hedged strategy), so the reversal-of-difficulty claim is now honestly earned rather than borrowed from one rung up.

## Where the hardness went — confinement, not conservation

deference-v6 §1.6 framed the residue as *relocated*: DDB's excruciating reconstruction reappearing one rung up, as the squeeze **Total Trust ⟹ Mart** — genuine convex geometry, obstructed by the amplifier. That framing is now superseded. At full quantifier strength the squeeze is a two-line **gap-bet** argument ([[total-trust-implies-mart]]): observability makes the expert's estimates world-decided facts, the gap-bet $Z - \ulcorner E^\ast(Z)\urcorner$ is a legal bet whose expert-estimate is provably $0$, and two soft cuts pin $E^H_n(Z) \approx_n E^H_n(\ulcorner E^\ast(Z)\urcorner)$. The amplifier only ever obstructed the *parallel-cut* route ([[amplifier-counterexample]]). So the honest geography: **the difficulty is not conserved in LI — it is confined to bet classes that cannot mention the expert.** DDB's frame is exactly such a class (not world-measurable), which is why the convex-hull direction is genuinely hard *there*; restricted-domain deference in this corpus (the faithful-acceleration family) is another ([[value-iff-mart]] §"Where separations survive").

## Why it reverses: what kind of object the expert is (deference-v6 §2.1)

**A DDB expert is an information frame** — a credence per world $P_w$, hence a *world-dependent* recommendation $S_w$. The realized return of "follow the expert" is the **diagonal** $\widehat S(w) = S_w(w)$, and the expert's score of the followed strategy is *not* the max (in the anti-expert frame it is $-1$ while the max is $.6$). Bridging the $\pi$-average of the diagonal to the $\pi$-average of the row-wise maxima is precisely DDB's hard direction.

**A coherent $E^\ast$ is a single belief state** — one set of estimates, one argmax, and the followed strategy is a *single option*; $E^\ast(\widehat S) = M$ holds by definition (F1). No diagonal to reconstruct: the bridge DDB builds by hand is handed over for free. The novice's uncertainty about $E^\ast$ is **logical** (a definite quantity it has not finished computing), not **which-world** uncertainty over which $P_w$ obtains. In deference-v6 §2.1's slogan: *a coherent single state is cheap; a frame is dear.* The tie-break is the one crack where a frame can re-enter the LI setting: an undecidable tie-break makes the selection world-dependent, and F1 fails by exactly the diagonal-style correlation of the previous paragraph — [[ledger-decided-tie-breaks]].

## The thin channel, sharpened by the telescope

The telescoping proof makes the mechanism concrete. Its rungs apply Total Trust to *derived* bets $D_k = O^k - \widehat S^{(k-1)}$ whose formulas mention the expert's estimates. In LI these are honest e.d. LUVs because **observability** — the thin channel of [[setting-and-notation]] — publishes the expert's estimates into the novice's world as *decided facts* the novice can bet on and condition on. In DDB the frame $P$ is not world-measurable: "$E(D_k)$" is not a fact of the world, $D_k$ is not a legal bet, and the induction is unavailable — leaving only the convex reconstruction. So §2.1's moral applies with full force: **the DDB-hard direction becomes cheap *because of* observability**, not because LI found a slicker proof of the same lemma. The single coherent state is what makes F1 free; the thin channel is what makes the keep-or-switch bets legal — and, pushed one step further, what makes the *gap-bets* legal, dissolving even the squeeze ([[total-trust-implies-mart]]). What DDB is missing is not a lemma but a channel.

(The remaining LI-side print of the continuum: what Total Trust at threshold $0$ delivers is the $\delta$-hedged strategy, not the hard argmax — the wedge of [[keep-or-switch-telescope]]; full Total Trust recovers the hard form via provably-full cuts ([[provable-bound-respect]], unvetted). In the finite-exact/DDB-style setting the distinction vanishes.)

## ⚠ Revision (2026-07-25): how much reversal survives the true setting

The LI-easy right cell was earned partly by definition: the surrogate reading of composite estimates makes the expert's endorsement of its own pick an arithmetic identity. In the true LI setting ([[total-trust-implies-value]]) the endorsement returns as a substantive lemma (**self-endorsement**), false without a decision-theoretic scope condition — and its failure mode is exactly a diagonal: an expert uncertain of its own selection is a small *frame*, its expectation of the followed strategy a selection-weighted mixture of conditional estimates. So the difficulty DDB meet head-on is not absent in LI; it is *confined* to the near-tie/self-referential layer and *dischargeable* by introspection + conditional-stability, versus DDB's full convex reconstruction. The reversal survives as a large quantitative asymmetry, not an absolute one.

## Status

**INTERPRETATION** — a reading of where the difficulty lives, not a new mathematical claim. Each cell rests on a component with its own page and status: the two-option identity ([[two-option-value-iff-total-trust]], exact), the telescope ([[keep-or-switch-telescope]], PROVED prose, unvetted), the gap-bet squeeze ([[total-trust-implies-mart]], PROVED prose, **unvetted** — the confinement claim of this page inherits that status), the amplifier ([[amplifier-counterexample]], KERNEL-CHECKED). The DDB-side characterizations are cited from deference-v6's reading of DDB, not re-proved here.

## Related

- [[total-trust-implies-value-telescoping]] — overview of the routes that earn the LI-easy cell honestly (the proof: [[keep-or-switch-telescope]])
- [[two-option-value-iff-total-trust]] — the exact two-option identity (the other easy cell)
- [[total-trust-implies-mart]], [[amplifier-counterexample]] — the confinement of the hardness, and its surviving witness
- [[mart-implies-value]] — the tower route the old table borrowed
- [[expert-conditions]] — single state vs. frame; what modesty survives
- [[ledger-decided-tie-breaks]] — the frame re-entering through undecided ties, and the condition that seals it
- [[deference-notions]] — the notions, the DDB map, the implication diagram

*Source: deference-v6 §1.3 (L213–220), §2.1 (L295–310); sharpening from `imported-chats/analysis/session-b9e8341b-proof.md` (Caveat 1).*
