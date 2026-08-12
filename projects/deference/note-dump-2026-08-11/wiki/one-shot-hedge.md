# The one-shot hedge: threshold-0 Total Trust ⟹ δ-hedged Value in one step

*The keep-or-switch telescope collapses to a single rung once the "newcomer" is the argmax strategy $\widehat S$ itself: one `loe` split plus one TT$(\cdot,0)$ application to the derived bet $\widehat S - O^i$ delivers the full soft theorem — same hypothesis fragment as the telescope, but with **no bound on menu size** and **no relabeled tie-break**. What the telescope keeps over this route is purely structural: the decomposition into pairwise deferrals.*

**Provenance.** ⚠ **This argument was produced in the 2026-07-23 Claude Code session** (the session that split the original [[total-trust-implies-value-telescoping]] page into this cluster), in response to Abram's question "do you think this same conclusion is possible without the induction?". It is **not** in the `b9e8341b` extraction and has no source outside this page. **Unvetted by Abram as of 2026-07-23.**

**⚠ Scope revision (2026-07-25).** Stated in the surrogate formulation (composite "$E^\ast$" = linear extension of published quotes). The novice-side inequality stands relative to surrogate-TT; the expert-endorsement gloss ($E^\ast(T_\delta)$ within $\delta$ of the max) is exact only as ledger arithmetic — the actual-expectation form is asymptotic self-endorsement, and menus must satisfy the decision-theoretic scope condition of [[total-trust-implies-value]] (page of record).

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor; expert $E^\ast$ **observable**, **coherent**, and **introspective** ([[expert-conditions]]). Menu apparatus as in [[deference-notions]]: e.d. finite menus $\{O^1_n, \dots, O^K_n\}$ of bounded $[a,b]$-LUVs, $m^j := E^\ast(O^j)$, $M_K := \max_j m^j$, and the canonical **followed strategy** $\widehat S := O^{j^\ast}$, $j^\ast \in \arg\max_j m^j$ (least index; any ledger-decided tie-break — [[ledger-decided-tie-breaks]]). Observability makes $\widehat S$ an e.d. LUV — the discontinuous argmax lives *inside the LUV formula*, never as a trade weight (exactly as in [[mart-implies-value]]) — and **(F1)** $\Gamma \vdash E^\ast(\widehat S) = M_K$ holds by coherence + introspection (the expert must resolve its own case-split; see the F1 Remark on [[mart-implies-value]]).

**Derived estimates.** For a bounded LUV-combination $D = c + \sum_j \alpha_j O^j$ with ledger-computable coefficients, $E^\ast(D) := c + \sum_j \alpha_j m^j$ — the expert's actual estimate by coherence, and a $\Gamma$-decided, $\mathcal{C}_H$-cheap quantity by observability.

**Hypotheses used — exactly these, nothing more:**

- **TT$(\cdot, 0)$** — the same threshold-$0$ fragment of Total Trust as [[keep-or-switch-telescope]]: for every e.d. bounded LUV-combination $D$ built from menu options and observable expert-estimates, and every ramp width $\delta$,
  $$ E^H_n\big(D \cdot \operatorname{Ind}_\delta(E^\ast(D) > 0)\big) \;\gtrsim_n\; 0, $$
  where $\operatorname{Ind}_\delta(x > 0)$ is the ramp indicator ($0$ for $x \le 0$, $1$ for $x \ge \delta$, linear between). This is the unnormalized soft form; full Total Trust ([[deference-notions]]) quantifies over all thresholds, none of which are used here.
- The novice's own `loe` (Linearity of Expectation, 4.8.4).
- Expert side: coherence + introspection, only through F1.

**No tower, no squeeze — and, unlike the telescope, no induction and no menu-size bound.**

## Construction

The target is **Value** ([[deference-notions]]): for every e.d. sequence of finite menus and every fixed index $i$,

$$ E^H_n\big(\widehat S_n\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big) $$

— in LI proper, with $\widehat S$ replaced by a $\delta$-hedged surrogate, since threshold-$0$ TT is soft (see the Statement below). Fix $i$; call $O^i$ the **comparison option**. Set

$$ D := \widehat S - O^i, \qquad \theta := \operatorname{Ind}_\delta\big(E^\ast(D) > 0\big), \qquad T_\delta := O^i + D \cdot \theta \;=\; (1-\theta)\,O^i + \theta\,\widehat S. $$

$T_\delta$ is a single keep-or-switch decision — incumbent $O^i$, newcomer $\widehat S$ — hedged across a $\delta$-ramp: a convex combination of two menu options, bounded, coefficient mass $1$.

**Legality check.** $D$ is an e.d. bounded LUV-combination in TT's class (its formula references menu options and observable estimates; the argmax case-split sits inside the LUV, decided by $\Gamma$ through the thin channel). The trade weight $\theta$ is legal: its argument $E^\ast(D) = M_K - m^i$ is a *continuous* ledger-computable function of the published estimates ($\max$ is continuous), so the ramp is $\mathcal{C}_H$-market-generable — the discontinuity obstruction of [[setting-and-notation]] does not arise. And F1 gives, provably,

$$ \Gamma \vdash E^\ast(D) = M_K - m^i \ge 0. $$

## Statement

**Theorem (one-shot hedge).** Assume TT$(\cdot, 0)$. Fix $\delta > 0$ and an index $i$. Then

$$ E^H_n(T_\delta) \;\gtrsim_n\; E^H_n(O^i_n), \qquad \Gamma \vdash M_K - \delta \;\le\; E^\ast(T_\delta) \;\le\; M_K. $$

The same conclusion as the telescoping theorem of [[keep-or-switch-telescope]] — the novice weakly prefers the hedged follow-the-expert strategy to any fixed option, and the expert rates it within $\delta$ of the menu max — for arbitrary (even unboundedly growing) menu size $K_n$, with the canonical least-index $\widehat S$ throughout.

## Proof

**Novice side.** $\Gamma \vdash T_\delta = O^i + D\cdot\theta$ by definition, with unit/bounded coefficients, so `loe` splits:

$$ E^H_n(T_\delta) \;\approx_n\; E^H_n(O^i) + E^H_n\big(D \cdot \operatorname{Ind}_\delta(E^\ast(D) > 0)\big) \;\gtrsim_n\; E^H_n(O^i), $$

the second step being exactly one instance of TT$(D, 0)$ at width $\delta$. That is the entire inequality: one `loe`, one TT.

**Expert side.** Write $d := M_K - m^i \ge 0$, so $E^\ast(T_\delta) = m^i + d\,\theta$ with $\theta = \operatorname{Ind}_\delta(d)$ a known scalar to the expert (introspection + observability, as in F1). Cases:

- $d \ge \delta$: $\theta = 1$, so $E^\ast(T_\delta) = m^i + d = M_K$.
- $0 \le d < \delta$: $E^\ast(T_\delta) = m^i + d\,\theta \ge m^i = M_K - d > M_K - \delta$.

And $E^\ast(T_\delta) \le M_K$ always, being a convex combination of $m^i \le M_K$ and $M_K$. So $\Gamma \vdash M_K - \delta \le E^\ast(T_\delta) \le M_K$ — a single $\delta$-loss, only at a near-tie between the comparison option and the max. $\blacksquare$

**Hard variant.** Where hard indicators are legal weights (finite-exact / DDB-style settings), take $T := O^i + D \cdot \mathbb{1}[E^\ast(D) > 0]$: if $M_K > m^i$ then $T = \widehat S$; if $M_K = m^i$ then $T = O^i$, which also attains the max. Either way $\Gamma \vdash E^\ast(T) = M_K$ exactly, and the same one-step argument gives Value with the "keep the comparison option on ties" tie-break. (In LI proper, Value itself needs the full threshold family — [[provable-bound-respect]].)

## Comparison with the telescope

Same hypothesis fragment, same conclusion — so what changed, and what is lost?

- **The bounded-$K$ restriction disappears.** The telescope composes $K-1$ asymptotic steps, forcing uniformly bounded menu size; here one `loe` and one TT application suffice regardless of $K_n$.
- **The tie-break wrinkle never arises.** The telescope relabels the menu to start at $O^i$, making its tie-break $i$-dependent (Claim B ⚠ of [[keep-or-switch-telescope]]); here $\widehat S$ is the canonical least-index strategy throughout, and the $i$-dependence survives only in the hedge $T_\delta$ itself — which any soft form has anyway.
- **The expert-side bill is identical.** Coherence + introspection, spent once through F1, versus once per rung through Claim A. Nothing new is assumed.
- **The bet class is not secretly richer.** One might worry that $\widehat S - O^i$ is a more complex bet than the telescope's rungs; it is not — the telescope's final rung $D_K = O^K - \widehat S^{(K-1)}$ already encodes the full first-max-wins argmax in its nested indicators. Both routes need TT over bets that mention the expert's estimates; neither needs more.
- **What the telescope keeps: the structure.** This route invokes two-option Value *once*, on the compound menu $\{O^i, \widehat S\}$ — it is the two-option construction of [[two-option-value-iff-total-trust]] with the argmax strategy itself as the second option, all the menu-walking hidden inside F1. The telescope instead exhibits follow-the-expert as $K-1$ pairwise keep-or-switch deferrals among the *actual* menu options, each rung a two-option-identity instance — the "two-option Value telescopes to full Value" moral. If the point is the lemma, this page is the leaner and more general proof; if the point is the decomposition, the telescope is the story.

## Status

**PROVED (prose, this page)** — the $\delta$-hedged form as stated; the hard variant in finite-exact settings. **Unvetted by Abram as of 2026-07-23; not machine-checked; produced by Claude in the 2026-07-23 session, with no source in the `b9e8341b` extraction.** Verification priorities for a vetting pass: (i) that $\widehat S - O^i$ is inside the bet class TT is assumed over (it mentions the argmax — same class the telescope's later rungs need, but worth confirming against any domain-restricted TT hypothesis, cf. the domain-relativity note in [[deference-notions]] §Value); (ii) the market-generability of the weight $\operatorname{Ind}_\delta(M_K - m^i > 0)$; (iii) the expert-side case analysis. If vetted, this supersedes the telescope as the canonical proof of threshold-$0$ TT ⟹ hedged Value, and the telescope remains as the structural reading. A one-`Approx`-one-`AsympLE` composition, plus the F1 algebra — an even easier machine-check candidate than the telescope ([[open-problems]]).

## Related

- [[total-trust-implies-value-telescoping]] — overview of the result and its three routes
- [[keep-or-switch-telescope]] — the original induction route this page collapses to one rung
- [[provable-bound-respect]] — Value itself (unhedged), from the full threshold family
- [[two-option-value-iff-total-trust]] — the two-option construction this page applies to the menu $\{O^i, \widehat S\}$
- [[mart-implies-value]] — source of the F1 remark (coherence + introspection) and of the e.d.-argmax legality argument
- [[deference-notions]] — Total Trust, Value, the menus/F1/F2 apparatus
- [[setting-and-notation]] — market-generable weights and the discontinuity obstruction
- [[ledger-decided-tie-breaks]] — the tie-break condition F1 needs

*Source: this page (2026-07-23 Claude Code session); apparatus from deference-v6 §1.1–§1.6 (`deference-in-logical-induction-v6.md`) and the pages cited above.*
