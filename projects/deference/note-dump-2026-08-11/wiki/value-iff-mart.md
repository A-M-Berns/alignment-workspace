# Value ⟺ Total Trust ⟺ Mart (the assembled equivalence)

*At full quantifier strength — bets allowed to mention the expert's observable estimates — the three deference notions collapse: every arrow of the triangle is cheap, and the once-feared "squeeze" is a two-line gap-bet argument. Genuine separations survive only where the bet class is restricted: DDB frames, the faithful-acceleration domain, and the hard-vs-hedged strategy distinction below gap-closure.*

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor with its free `loe`/`expprovind`; expert $E^\ast$ **observable**, **coherent**, **introspective** (each component page states its exact bill; the two-option leg does without introspection). The quantifier domain $\mathcal{D}$ of bets/menus matters more than anything else on this page: call $\mathcal{D}$ **gap-closed** if it contains $Z - \ulcorner E^\ast(Z)\urcorner$ (and negations/rescalings) whenever it contains $Z$. The natural LI reading of the notions — the one deference-v6 §1.2's own two-option construction and the telescoping proof's derived bets already use — is gap-closed, because observability makes expert estimates world-decided facts. Source: deference-v6 §1.4–§1.6, session b9e8341b, and the 2026-07-21 gap-bet argument.

## Statement

For an observable, coherent, introspective expert and **gap-closed** $\mathcal{D}$:

$$\textbf{Mart} \iff \textbf{Total Trust} \iff \textbf{Value} \qquad \text{on } \mathcal{D},$$

by the circle: Mart ⟹ Value ([[mart-implies-value]]); Value ⟹ Total Trust on two-option menus, exactly ([[two-option-value-iff-total-trust]]); Total Trust ⟹ Mart by gap-bets ([[total-trust-implies-mart]]). This matches the Garrabrant–Eisenstat expectation that Total Trust is equivalent to iterated expectations in LI. deference-v6 §1.4 asserted "Value ⟺ Mart" but routed the reverse through an unproved convex-geometry squeeze; the collapse above replaces that route.

**⚠ Update (2026-07-27): the loop is shorter than this page draws it, and arrow (a) is worse.** Two changes from the triangle pass of that date, neither yet folded into the diagram or the table below.

- **Value ⟹ Mart is direct**, and it is the *cheapest* arrow of the three — not a composite of (b) and (d). Offer the gap-bet probe menu $\{Z - \ulcorner E^\ast(Z)\urcorner,\ \text{const}(-\varepsilon)\}$: introspection pins the gap-bet's quote at $0$ whatever $Z$ is, so the expert provably takes it, and Value against the constant reads off the novice's valuation of the gap-bet. Four lines, expert introspection only, no Total Trust and no ramp — and the scope condition is *automatically satisfied* on such menus, so restricting Value's quantifier costs nothing on the way up. [[value-implies-tower]]. Consequence for this page: the honest circuit is **Total Trust ⟹ Value ⟹ Mart ⟹ Total Trust**, three direct arrows, of which only the first is expensive. Six arrows exist; three suffice.
- **Arrow (a), Mart ⟹ Value, is *refuted* at full menu-quantifier strength** — not merely unproved. In the self-trust instance the tower is a paper theorem (`cee` 4.12.1), yet the punishing menu ($O^1 = \mathbb{1}[\mathrm{sel}=2]$, $O^2 = \mathbb{1}[\mathrm{sel}=1]$, so $\Gamma \vdash \widehat S \equiv 0$ while $\sum_i E^H_n(O^i) \approx 1$) still kills Value. So **no hypothesis quantified over all e.d. LUV sequences can imply Value quantified over all e.d. menus**; the fix has to restrict Value's own quantifier. The kernel check `value_argmax_asymptotic` is untouched — it always took the F1 carry as a named hypothesis — but the table's flat "KERNEL-CHECKED" oversells the arrow, and [[mart-implies-value]]'s title and framing outrun what is true.
- **The direction of the surviving circuit is forced, not stylistic (2026-08-02).** Per-arrow, the triangle drawn on this page is *cheaper* than the 07-27 circuit — the two directions share their three expensive ingredients (bounds transfer, self-endorsement, gap-bet quote pinning), and this page's unique piece (the exact two-option identity) is lighter than the circuit's (the fold). But with Value scope-restricted per the previous bullets, the identity-based closing arrow (b) no longer reaches every Total-Trust instance: the **liar probe** — $O^1 = \mathbb{1}[\mathrm{sel}=2]$ paired with $\text{const } s$, i.e. half a punishing menu plus a constant — is a two-option menu that fails conditional-stability, on which Value is false, and whose hard above-threshold inequality is itself false, all by $s(1-s)$, while soft Total Trust holds. So this page's triangle survives at surrogate/finite-exact strength only; at true-LI strength every known full-strength entry into Total Trust factors through the fold. [[loop-direction]].

**⚠ Scope note (2026-07-25).** The collapse is stated at the surrogate level (composite estimates = linear extensions of published quotes; F1 arithmetic). In the true LI setting the Value corner carries extra bills — introspection and the conditional-stability scope condition, without which argmax Value is false outright ([[total-trust-implies-value]]) — so the honest reading is: the *epistemic* corners (Total Trust, Mart) collapse as shown for gap-closed classes, while the *instrumental* corner (Value) joins them only inside the non-Newcomblike regime.

## The implication triangle, with per-arrow status

```
                 Mart (the tower) ⟺ conditional tower (the fold)
                ▲ │
   (d) gap-bets │ │ (a) KERNEL-CHECKED
   PROVED prose │ │     value_argmax_asymptotic
   (unvetted)   │ ▼
  Total Trust ─────► Value
        ▲  (c) telescoping: PROVED prose, δ-hedged
        │
        └──────────── (b) two-option: exact, per (X,s), KERNEL-CHECKED
                          value_iff_totalTrust   [Value ⟹ TT]
```

| arrow | page | status | needs gap-closure? |
|---|---|---|---|
| (a) Mart ⟹ Value | [[mart-implies-value]] | **KERNEL-CHECKED** (honesty caveat) | no |
| (b) Value ⟹ Total Trust | [[two-option-value-iff-total-trust]] | **KERNEL-CHECKED**, exact | no (two-option menus only) |
| (c) Total Trust ⟹ Value (full menu) | [[total-trust-implies-value-telescoping]] (overview; three routes) | **PROVED (prose)**, δ-hedged from threshold-$0$ TT; Value itself from full TT ([[provable-bound-respect]], unvetted) | no — derived bets only |
| (d) Total Trust ⟹ Mart | [[total-trust-implies-mart]] | **PROVED (prose), unvetted** | **yes** |
| Mart ⟹ Total Trust | [[deference-notions]] (fold + `expprovind`) | **PROVED (prose)** | no |

Arrow (c) is not made redundant by (d): it delivers full-menu Value from strictly weaker resources (no gap-closure — only menu-derived bets), which is what restricted-domain settings can actually use.

## Where separations survive

The collapse is a theorem *about the unrestricted notions*. Everything interesting downstream lives below gap-closure:

1. **Parallel cuts of a single bet do not pin the tower.** The [[amplifier-counterexample]] $g(e) = (1+2c)e - c$ passes every upper/lower/soft threshold cut of the bare bet while $g \ne \mathrm{id}$ — killed only by boundedness at the endpoints, and killed immediately by gap-bet cuts. This is now a statement about an impoverished quantifier, not an obstruction to (d).
2. **DDB frames.** The frame is not world-measurable, so gap-bets are illegal and DDB's biconvex/convex-hull direction is genuinely hard — the difficulty LI dissolves *because of* observability ([[reversal-of-difficulty-vs-ddb]], deference-v6 §2.1's moral).
3. **The faithful-acceleration domain.** The FA construction forces only a sparse gate-weighted family of Total-Trust instances on specific bets — nowhere near gap-closed — so nothing there collapses to Mart; and cross-process Mart is independently **refuted** ([[tower-death]]). Value$_\mathcal{D}$ ⟺ TT$_\mathcal{D}$ (deference-v6 §5.11) with Mart strictly stronger is the honest restricted-domain picture ([[faithful-acceleration-result]], [[trichotomy-where-value-sits]]).
4. **Argmax vs. δ-hedged strategy, below gap-closure.** From *threshold-$0$* Total Trust alone, Value comes only for the δ-hedged followed strategy; the near-threshold layer $E^H_n(D\cdot\mathbb{1}[0 < E^\ast(D) \le \delta])$ is unconstrained (the amplifier's surviving degree of freedom — the wedge of [[keep-or-switch-telescope]]). *With* gap-closure, (d) + (a) recover Value itself too — and ⚠ [[provable-bound-respect]] (unvetted) recovers it from the *full threshold family* even without gap-closure, which would shrink this separation to the threshold-$0$ fragment.

So the earlier slogan "Value sits one rung below the tower" survives as a statement about **proof resources and restricted domains** — Value needs less than Mart to obtain — not as a separation of the unrestricted notions.

## The fold, in one paragraph (deference-v6 §1.5)

By "the tower" this wiki always means the *universal* one — Mart on every e.d. LUV sequence — and that already contains its conditional form: for observable $w \in [0,1]$, $X \cdot w$ is itself an e.d. LUV, and since the expert knows the weight (introspection; `epr`/`er` for the future self), coherence gives $E^\ast(X\cdot w) = w\,E^\ast(X)$ — so Mart on $X\cdot w$ *is* the conditional tower `ccee` at $w$, and $w \equiv 1$ recovers the bare tower. The DDB marginal identity $\pi P = \pi$ is the tower on a bare-options set — a frame artifact with no privileged status in LI. Status: **PROVED (prose)**, finite-exact core kernel-checked (`DeferenceFold.fold_sum`). Full statement: [[deference-notions]].

## Status

**Composite.** Per-arrow statuses above are the content. The honest slogan: **the triangle closes; its newest side (d) is prose and awaits Abram's vetting** — if (d) falls, the fallback is the pre-collapse picture (Value ⟺ TT exactly; Mart strictly above, obstructed by the amplifier at parallel-cut strength; squeeze open). Every KERNEL-CHECKED cell carries the honesty caveat of [[conventions-and-status-labels]]. deference-v6 Appendix B's abstract-tier rows should be read as: forward arrow + the two-option identity ("witness" in Appendix B's own vocabulary) as stated there; its "squeeze stays prose" row is superseded by (d) *for gap-closed classes* if vetted.

## Related

- [[mart-implies-value]], [[two-option-value-iff-total-trust]], [[total-trust-implies-value-telescoping]], [[total-trust-implies-mart]] — the arrows
- [[loop-direction]] — the full comparison of the two loop directions; why this page's triangle survives only at surrogate strength
- [[amplifier-counterexample]] — the surviving obstruction, correctly scoped
- [[deference-notions]] — the notions and the fold
- [[reversal-of-difficulty-vs-ddb]] — the difficulty ledger against DDB
- [[expert-conditions]] — the exact expert bill per arrow
- [[value-gap-arbitrage]] — what a failure of Value means (the forcing question)
- [[faithful-acceleration-result]], [[tower-death]], [[trichotomy-where-value-sits]] — the restricted-domain consumers

*Source: deference-v6 §1.4 (L222–224), §1.5 (L226–230), §1.6 (L232–289); telescoping rung from session b9e8341b; gap-bet argument 2026-07-21 ([[total-trust-implies-mart]]).*
