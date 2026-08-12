# Total Trust ⟹ Value (overview of the routes)

*Full-menu Value from Total Trust alone — no tower, no squeeze. For the full-strength equivalence TT ⟺ Value ⟺ Mart ([[value-iff-mart]]), the primary arrow is **provable-bound respect**: full Total Trust delivers Value — for the argmax strategy itself — in one step, unbounded menus, any ledger-decided tie-break ([[ledger-decided-tie-breaks]]). The threshold-$0$ routes — the **keep-or-switch telescope** (the original session proof) and the **one-shot hedge** — are the *restricted-domain calibration*: they show that the weakest natural fragment of TT (threshold-$0$ cuts on derived bets) already buys $\delta$-hedged Value, which is what transfers to settings where trust is *forced* rather than assumed and only a sparse family of cuts is available. A fourth, **composite** route runs through the tower for gap-closed bet classes ([[total-trust-implies-mart]] + [[mart-implies-value]]). Honest summary: threshold-$0$ TT ⟹ $\delta$-hedged Value; full TT ⟹ Value; Mart is needed for neither.*

**Page history & provenance.** v1 of this page (2026-07-21) was a single self-contained write-up of the proof from the 2026-07-20 Claude Code session `b9e8341b` (extraction: `imported-chats/analysis/session-b9e8341b-proof.md`), with ⚠-marked checking-pass additions. On 2026-07-23 it was split: this page is now the **v2 overview**, and the proofs live in [[keep-or-switch-telescope]] (the session proof), [[provable-bound-respect]] (the v1 Caveat-3 ⚠ strengthening), and [[one-shot-hedge]] (**new math from the 2026-07-23 session** — not in the extraction). v1 is recoverable from git history. Every route is **unvetted by Abram as of 2026-07-23**.

**⚠ Status revision (2026-07-25).** Everything below is stated in the **surrogate formulation**: "$E^\ast(D)$" for a composite bet means the linear extension of the published option-quotes — arithmetic in the ledger — per the derived-estimates convention. [[total-trust-implies-value]], now the **page of record**, restates the problem in the true LI setting (expectations as the paper's price-integrals throughout) and shows the surrogate had built the expert-side content into notation: there, TT ⟹ Value factors into **bounds transfer** (robust) plus **self-endorsement**, which is *refuted* without a decision-theoretic scope condition (the punishing-menu counterexample — argmax Value is unconditionally false on selection-referencing menus), holds under decisive margins, and holds under **conditional-stability** modulo two named items. Honest current headline: *surrogate-TT ⟹ the inequalities below, as stated; true TT + introspection ⟹ δ-hedged Value; true TT + introspection + conditional-stability ⟹ argmax Value (modulo named items); unconditional argmax Value is false.* The table below remains correct about the surrogate.

## The question, and why it matters

Total Trust and Value are the two "one rung below the tower" deference notions ([[deference-notions]]): Total Trust is the soft-conditioned inequality family ("where the expert rates a bet above $t$, so does the novice"), Value is the instrumental menu notion: for every e.d. menu sequence and every fixed index $i$,

$$ E^H_n\big(\widehat S_n\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big) $$

— letting the expert pick (the argmax strategy $\widehat S$) is weakly preferred, by the novice's own lights, to committing to any fixed option. The two-option identity ([[two-option-value-iff-total-trust]]) makes them *exactly* equivalent — but only on **two-option menus**. Whether Total Trust alone yields **full-menu** Value was a genuine gap: the result is **not in deference-v6** (`deference-in-logical-induction-v6.md`) — its §1.2 stops at two-option menus, its §1.3 difficulty table routes "Total Trust ⟹ Value" through the tower (squeeze up to Mart, then [[mart-implies-value]]), and its §5.9-area gloss "Value ⟺ Total Trust, pinned by §1.2" overstates what §1.2 proves. The routes below close the gap without the tower, slotting naturally between deference-v6 §1.2 and §1.4 as a lemma; the DDB comparison ([[reversal-of-difficulty-vs-ddb]]) is where the difficulty tables get repaired.

Which *fragment* of TT each route spends matters beyond bookkeeping. Cross-process Mart is **refuted** ([[tower-death]]), and the positive constructions force only sparse, gate-weighted families of TT instances ([[faithful-acceleration-result]]) — so below full strength, "which cuts buy which form of Value" is the currency (the domain-relativity of [[deference-notions]] §Value, deference-v6 §5.11). Provable-bound respect spends an unusual fragment — cuts at negative thresholds whose conditioning weight is provably $\equiv 1$, i.e. instances where the conditioning does no work — which a forced family has no particular reason to contain; the threshold-$0$-on-derived-bets bill of the telescope and one-shot hedge is much closer to what forcing actually provides.

## The routes

Ordered by role: the first is the full-strength arrow, the middle two are the fragment calibration, the last also buys the tower.

| route | hypothesis | conclusion | menu size | tie-break | page |
|---|---|---|---|---|---|
| provable-bound respect | full TT (all thresholds) | **Value** | unbounded | any ledger-decided | [[provable-bound-respect]] |
| one-shot hedge | TT at threshold $0$ only | $\delta$-hedged Value | unbounded | canonical least-index | [[one-shot-hedge]] |
| keep-or-switch telescope | TT at threshold $0$ only | $\delta$-hedged Value (full Value in finite-exact settings) | uniformly bounded $K_n \le K$ | $i$-promoted (the ⚠ wrinkle) | [[keep-or-switch-telescope]] |
| composite gap-bet route | full TT over a **gap-closed** bet class | **Value**, and all of Mart | unbounded | any ledger-decided | [[total-trust-implies-mart]] + [[mart-implies-value]] |

**Provable-bound respect** ([[provable-bound-respect]]) — the primary arrow for the full-strength equivalence. Full TT contains the principle "the novice respects $\Gamma$-provable bounds on the expert's estimates" (cuts below a provable bound are provably full, hence unconditional floors). Applied to $\widehat S - O^i$, whose expert-estimate is provably $\ge 0$ by F1, this gives **Value** — for the argmax strategy itself — in one step, refuting the extraction's Caveat-3 conclusion that "hard-argmax Value remains a Mart-only deliverable." It is also the least-vetted piece of the cluster: a 2026-07-21 checking-pass artifact, in no source session.

**The one-shot hedge** ([[one-shot-hedge]]) — the sharpest form of the threshold-$0$ calibration: one `loe` split plus one TT application to $\widehat S - O^i$ (a single keep-or-switch rung whose "newcomer" is the argmax strategy $\widehat S$ itself) gives $\delta$-hedged Value with no menu-size bound and no relabeling. Produced in the 2026-07-23 session; if vetted, it supersedes the telescope as the canonical threshold-$0$ *proof*, with the telescope retained as the structural reading.

**The telescope** ([[keep-or-switch-telescope]]) — the original `b9e8341b` proof, and the structural one. Relabel the menu so the fixed option $O^i$ comes first; walk the menu as $K-1$ keep-or-switch decisions, the expert switching iff it rates the newcomer strictly higher; apply `loe` + TT$(D_k, 0)$ once per rung; telescope down to $E^H_n(O^i)$. Its Claim A (the generalized F1: the expert provably rates the chain at the running max) is what certifies the chain implements follow-the-expert.

**The composite gap-bet route** — not tower-free, so not this page's headline, but a genuine fourth route. When the bet class is **gap-closed** (bets may mention the expert's observable estimates, so the gap-bets $Z - \ulcorner E^\ast(Z)\urcorner$ are legal), full TT squeezes up to Mart in two lines ([[total-trust-implies-mart]], unvetted) and [[mart-implies-value]] finishes: Value, no menu-size bound. Both legs have their own pages, so it gets none here. Relative to provable-bound respect it proves more (all of Mart) from more (gap-closure); provable-bound respect stays strictly below the tower.

## Structural reading: two-option Value telescopes to full Value

By the two-option identity, each telescope rung TT$(D_k, 0)$ *is* Value on a two-option menu — so the telescope says: *"follow the expert on a $K$-menu" decomposes into $K-1$ pairwise keep-or-switch deferrals, and two-option Value telescopes to full-menu Value.* The convex-geometry squeeze of deference-v6 §1.6 is bypassed because Value never needed the tower *equality* at any point — only one-sided threshold inequalities. Value is "one rung below the tower," and these proofs show it lives there natively rather than being inherited from above ([[mart-implies-value]] derives the same conclusion from one rung up). The one-shot hedge makes the same point in compound form: it is the two-option construction applied to the menu $\{O^i, \widehat S\}$, with the menu-walking hidden inside F1. Full detail: [[keep-or-switch-telescope]] §"Structural reading".

## The soft/hard boundary

Where the LI continuum bites: with genuine soft weights, threshold-$0$ TT provably cannot reach the argmax strategy itself — nothing bounds the "wedge" term supported on $0 < E^\ast(D) \le \delta$, which is exactly the amplifier's surviving degree of freedom ([[keep-or-switch-telescope]] §"The wedge"). So the honest boundary runs:

> **threshold-$0$ TT ⟹ $\delta$-hedged Value** (telescope, one-shot hedge); **full TT ⟹ Value itself** (provable-bound respect); **Mart is needed for neither.**

In finite-exact / DDB-style settings hard indicators are legal weights, the wedge is empty, and both threshold-$0$ routes deliver Value itself directly.

Note that "threshold $0$" is *weaker in LI than it sounds*: in DDB's hard formulation the threshold-$0$ cut (with $\ge$, hence full conditioning mass on a bet whose expert-estimate is provably nonnegative) already contains provable-bound respect at $s = 0$. The soft ramp $\operatorname{Ind}_\delta(\cdot > 0)$ vanishes at the boundary, so a provably-nonnegative estimate earns no guarantee — the ramp needs headroom, which is exactly why provable-bound respect must reach for $-\varepsilon$ cuts, and why the wedge exists at all. The hedged/hard gap is thus a print of the LI continuum, not an artifact of proof technique.

## Compatibility caveat 1 — DDB: no contradiction with the "excruciating" direction

All routes apply TT to *derived* bets ($D_k$, or $\widehat S - O^i$) whose formulas mention the expert's estimates. In LI these are honest e.d. LUVs because **observability** puts the expert's estimates into the novice's world as decided facts — the thin channel ([[setting-and-notation]]). In DDB the expert is a *frame* $P$, not world-measurable: "$E(D)$" is a random variable over worlds the novice cannot read off, so the derived bets are not legal and none of these routes are available — which is why DDB's Total Trust ⟹ Value must instead reconstruct the expert from its cuts by convex geometry. This relocates the moral of deference-v6 §2.1: the DDB-hard direction is cheap here *because of* observability, not despite it. Full interpretation: [[reversal-of-difficulty-vs-ddb]].

## Compatibility caveat 2 — the amplifier: only the inequality, never the equality

The §1.6 amplifier $g(e) = (1+2c)e - c$ shows single-bet *parallel* cuts cannot pin the tower *equality* ([[amplifier-counterexample]]). No conflict: here TT is used over *all* derived bets, and only the *inequality* (Value) is concluded, never the equality (Mart). An amplifier-like novice — one that systematically overstates the expert's confidence yet satisfies every threshold cut of a single bet — survives the threshold-$0$ hypotheses and still fails the tower; but it **cannot fail hedged Value**, and against the full threshold family it fails the provably-full negative cuts ([[provable-bound-respect]] §"Amplifier cross-check"). The cluster thus calibrates exactly how much of the deference package Total Trust buys: all of the instrumental face, none of the pointwise equality.

## Consequences

- **Closes the gap in deference-v6's §5.9-area gloss.** deference-v6 glosses "Value ⟺ Total Trust, pinned by §1.2," but §1.2 proves only *two-option-menu* Value ⟺ TT. These routes supply the missing direction, making the equivalence honest at full-menu level: Value and Total Trust are cleanly equivalent *one rung below the tower* — $\delta$-hedged from the threshold-$0$ fragment, Value itself from the full family.
- **Feeds [[value-iff-mart]]:** the internal Value ⟺ TT equivalence is now direct in both directions. The remaining side of the triangle, TT ⟹ Mart, is settled for gap-closed bet classes by [[total-trust-implies-mart]]; the routes here stay relevant below gap-closure, where they are the only path to full-menu Value.
- **Repairs downstream conversions.** Corpus-level claims converting forced Total Trust into Value ([[faithful-acceleration-result]], via the precision flag on [[two-option-value-iff-total-trust]]) now have a full-menu backing.
- **Machine-check candidates** ([[open-problems]]): the three direct routes are short compositions of `Approx`/`AsympLE` steps plus F1/Claim-A algebra — the same shape as the existing kernel-checked chains (the Lean honesty caveat of [[conventions-and-status-labels]] would apply as usual).

## Status

All three direct routes: **PROVED (prose)** on their own pages; **unvetted by Abram as of 2026-07-23; not machine-checked.** Provenance tiers differ and matter for vetting order: the telescope is the `b9e8341b` session proof (extraction-faithful, with ⚠ write-up additions); provable-bound respect is a 2026-07-21 checking-pass artifact that *corrects* the extraction's Caveat 3; the one-shot hedge is 2026-07-23 session math with no earlier source. Suggested vetting order: **provable-bound respect first** — it is now the primary arrow and simultaneously the least-vetted piece — then the one-shot hedge and telescope for the threshold-$0$ calibration.

## Related

- [[keep-or-switch-telescope]], [[one-shot-hedge]], [[provable-bound-respect]] — the three direct routes; the composite runs through [[total-trust-implies-mart]] + [[mart-implies-value]]
- [[total-trust-implies-value]] — self-contained linear exposition of the primary arrow
- [[two-option-value-iff-total-trust]] — the two-option identity the routes build on
- [[mart-implies-value]] — the same conclusion from one rung up
- [[total-trust-implies-mart]] — TT *does* buy the tower equality when the bet class is gap-closed; [[amplifier-counterexample]] — what survives below gap-closure
- [[value-iff-mart]] — the assembled equivalence this cluster feeds
- [[deference-notions]] — TT, Value, menus/F1/F2, the implication diagram
- [[reversal-of-difficulty-vs-ddb]] — why this direction is cheap in LI and excruciating in DDB
- [[expert-conditions]] — what observable/coherent/introspective buy
- [[ledger-decided-tie-breaks]] — the tie-break condition all routes' F1 leans on

*Sources: `imported-chats/analysis/session-b9e8341b-proof.md` (telescope); v1 of this page, 2026-07-21, in git history (provable-bound respect, ⚠ items); the 2026-07-23 session (one-shot hedge, this split); deference-v6 §1.1–§1.6 (`deference-in-logical-induction-v6.md` L155–292).*
