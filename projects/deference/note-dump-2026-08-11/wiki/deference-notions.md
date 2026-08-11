# Deference notions

*The five candidate formalizations of "the novice defers to the expert" — Mart (the tower), the conditional tower (the fold), Total Trust, Value, and Reflection — each with its exact quantifier structure, the map to DDB's notions, and the implication diagram linking them.*

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): a logical-inductor novice $H \dashv \mathcal{C}_H$ and an expert $E^\ast$ assumed **observable** and **coherent**, with **introspection** required only where stated ([[expert-conditions]]). Everything specializes to the two canonical instances: the future self $E^\ast = E^H_{f(n)}$ (all hypotheses become LI theorems) and the AI $E^\ast = E^A_n$ read through the thin channel, where $E^\ast(X) = a_n$ when $X = P^{(n)}$. Source: deference-v6 §0.5, §1 preamble, §1.5–1.6.

## Shared apparatus: menus and the followed strategy (deference-v6 §1)

Fix an e.d. sequence of finite **menus** $\mathcal{O}_n = \{O^1_n, \dots, O^k_n\}$ of bounded $[a,b]$-LUVs ("bets"), exogenous — a word that turned out to be load-bearing and nontrivial to define; the condition of record is **conditional-stability** ([[total-trust-implies-value]] §Hypotheses), with rejected alternatives surveyed at [[defining-exogeneity]]. Write $m^j_n := E^\ast(O^j_n)$, $M_n := \max_j m^j_n$, and $j^\ast(n) \in \arg\max_j m^j_n$ (least index; any **ledger-decided** tie-break — computable from the published estimates, which F1 *requires* rather than merely permits: [[ledger-decided-tie-breaks]]). The **followed strategy** — "let the expert decide" — is the single LUV

$$ \widehat S_n := O^{\,j^\ast(n)}_n, $$

the option the expert picks, evaluated at the world that obtains. Because $E^\ast$ is observable, $\widehat S_n$ is itself an e.d. LUV, so `argmax` never appears as a (discontinuous, hence illegal) trade *weight*. Coherence gives **(F1)** $E^\ast(\widehat S_n) = M_n$, tie-break-independently, and trivially **(F2)** $M_n \ge m^i_n$ — with a ⚠ 2026-07-25 caveat on F1's status: it is *exact* only in the surrogate reading of composite estimates (linear extension of published quotes) or for an assumed exactly-coherent expert; for an inductor-expert's actual expectations it is asymptotic, costs introspection and a ledger-decided tie-break, and **fails without a decision-theoretic scope condition** — selection-referencing menus refute it, and Value with it. Current treatment: [[total-trust-implies-value]] §Lemma 2 ("self-endorsement").

## The notions

### Mart — the tower (pointwise equality)

$$ \textbf{Mart}(H \to E^\ast):\quad \text{for every e.d. sequence of LUVs } (X_n):\qquad E^H_n(X_n) \;\approx_n\; E^H_n\big(\ulcorner E^\ast(X_n) \urcorner\big). $$

Quantifier structure: one asymptotic *equality* per e.d. LUV sequence — the difference tends to $0$ along days. This is iterated-expectation collapse toward the expert: the novice's estimate of $X$ agrees with its estimate of *the expert's estimate of $X$*. It is the strongest notion the wiki endorses, the "pointwise" or per-day face.

**Mart is not a theorem of the LI paper — it is the deference *hypothesis*, a claim about the $(H, E^\ast)$ pair.** Its self-trust instance ($E^\ast = E^H_{f(n)}$) is the paper's Expected Future Expectations, `cee` 4.12.1 — the one case where the tower is free. Whether it can be *forced* for a distinct expert is the subject of [[value-gap-arbitrage]] and everything downstream ([[tower-death]], [[frozen-deliberation-theorems]]).

### The conditional tower — the fold (ccee-style)

$$ \textbf{ccee}(H \to E^\ast):\quad \text{for every e.d. } (X_n) \text{ and every observable weight } w_n \in [0,1]:\qquad E^H_n(X_n \cdot w_n) \;\approx_n\; E^H_n\big(\ulcorner E^\ast(X_n) \cdot w_n \urcorner\big). $$

Here "observable weight" means $\mathcal{C}_H$-market-generable — continuous in the prices — so hard indicators are excluded by type. Setting $w \equiv 1$ recovers the bare tower; the self-trust instance is the paper's `ccee` 4.12.3.

**Fact (deference-v6 §1.5, the fold — status: PROVED).** The *universal* tower already contains its conditional form, provided the expert **knows the weight** (introspection; for the future self, `epr`/`er`): the product $X \cdot w$ is itself an e.d. LUV, and coherence plus knowledge of $w$ gives $E^\ast(X \cdot w) = w\, E^\ast(X)$, so Mart applied to $X \cdot w$ *is* the conditional tower at $w$. Hence "tower on every LUV" and "tower with every observable weight" are one principle. (Finite-exact core kernel-checked as `DeferenceFold.fold_sum`, whose hypothesis `hknow` is exactly "the expert knows the weight".)

The fold is also where LI dissolves a DDB puzzle: DDB's *marginal* identity $\pi P = \pi$ (satisfied by the anti-expert frame that fails Value) is just the tower applied to the bare options only — a frame artifact with no privileged status in LI. The watershed is *what is conditioned on*: a DDB frame conditions on the expert's **identity** $[P = \rho]$, which a modest frame does not know, so the fold fails there; a coherent $E^\ast$ conditions on its own **estimate** $E^\ast(X)$, which it does know, so the fold goes through.

### Total Trust (soft-conditioned inequality)

$$ \textbf{Total Trust}(H \to E^\ast):\quad \text{for every e.d. } (X_n) \text{ and every threshold } t:\qquad E^H_n\big(X_n \,\big|\, E^\ast(X_n) \ge t\big) \;\gtrsim_n\; t, $$

together with the lower cut $E^H_n(X_n \mid E^\ast(X_n) \le t) \lesssim_n t$. Quantifier structure: one asymptotic *inequality* per (LUV sequence, threshold, cut) — conditional on the expert being confident, the novice is at least that confident.

In the LI continuum the conditioning must be **soft**: a hard $\mathbb{1}[E^\ast(X) > t]$ is discontinuous (illegal as a weight) and liar-prone. The working form is the **unnormalized threshold form** with the ramp indicator $w_{t,\delta} = \operatorname{Ind}_\delta(E^\ast(X) > t)$ of width $\delta$:

$$ E^H_n(X_n \cdot w_{t,\delta}) \;\gtrsim_n\; t \cdot E^H_n(w_{t,\delta}), $$

with the conditional form recovered by dividing by the conditioning mass and letting $\delta \to 0$. Derivation from the tower (deference-v6 §1.6): the fold at weight $w_{t,\delta}$, plus the threshold bound $E^\ast(X)\cdot w \ge t \cdot w$ (provable, carried through $E^H_n$ by `expprovind`). So: tower $\Leftrightarrow$ conditional tower $\Rightarrow$ Total Trust — the first equivalence is the fold, the last arrow the threshold bound. The *converse* of the last arrow — recovering the equality from the family of inequalities — holds by a short gap-bet argument when the bet class may mention the expert's estimates ([[total-trust-implies-mart]]); from parallel cuts of a single bet it provably fails ([[amplifier-counterexample]]). The self-trust instance of Total Trust is the paper's Self-Trust `st` 4.12.4.

### Value (instrumental / menu notion)

$$ \textbf{Value}(H \to E^\ast):\quad \text{for every e.d. sequence of finite menus } \mathcal{O}_n \text{ and every fixed index } i:\qquad E^H_n(\widehat S_n) \;\gtrsim_n\; E^H_n(O^i_n). $$

Quantifier structure: one asymptotic inequality per (menu sequence, fixed option) — "let the expert pick" is weakly preferred, by the novice's own current lights, to committing to any fixed option. This is the decision-theoretic face: the notion alignment ultimately cares about ([[trichotomy-where-value-sits]]). Note it is **domain-relative**: Value over menus drawn from a family $D$ is equivalent to Total Trust over $D$, and no more (deference-v6 §5.11) — "Value on the admissible domain" does not imply unrestricted Value.

**Decision-theoretic scope (⚠ 2026-07-25).** For inductor-experts, *unconditional* argmax Value is **false**: selection-referencing menus (Death-in-Damascus-type; Counterfactual Mugging is the same family) make "follow the expert" lose by every light — [[total-trust-implies-value]] §Lemma 2. Epistemic trust yields instrumental trust only inside a non-Newcomblike regime, formalized there as conditional-stability. This was always going to be so: Value is a decision-theoretic notion, and no decision rule is optimal across all embedded environments.

**Terminological default (2026-07-23).** "Value" unqualified always means this argmax form. The $\delta$-hedged variant used by the threshold-$0$ TT ⟹ Value routes — the same inequality with $\widehat S$ replaced by a soft-blended surrogate — is a strictly weaker notion that must always carry its qualifier ("$\delta$-hedged Value"), never "Value" simpliciter.

### Reflection (too strong)

DDB's strongest principle: $\pi(\cdot \mid P = \rho) = \rho$ — conditioning on the expert's **entire identity**, then adopting its exact credence. It is deliberately **not** adopted here: Reflection is incompatible with a modest expert (a frame that does not fully know itself cannot be deferred to this way), and in LI the soft indicator can only ramp over *estimate*-thresholds, never over identity — so the trust hierarchy provably tops out at the tower and cannot reach Reflection (deference-v6 §1.6). Reflection $\Rightarrow$ Mart, never the converse. The ceiling is a feature: it is what lets a modest expert be deferred to at all ([[expert-conditions]]).

**⚠ Re-scoped 2026-07-28 ([[reflection-in-li]]).** The rejection above concerns the **function form** (conditioning on the expert's whole probability function) and exactness at finite days. The **value form** of Reflection — condition on the expert's estimate of the bet, adopt it — softens to the band limit-equality, which is a *theorem* given the tower and equivalent to Total Trust; it joins the circle rather than sitting above it. "Never the converse" is false for that reading. The LI paper's own §4.11–§4.12 draw the same line, including a refutation witness for the exact grade. Details and the modest/immodest synthesis: [[reflection-in-li]].

## Map to DDB's notions (deference-v6 §0.5)

DDB (Dorst–Levinstein–Salow–Husic–Fitelson 2021) work on a **finite probability frame** $\langle W, \mathcal{P} \rangle$: a credence $P_w$ per world, novice $\pi$, expert's-estimate random variable $E(X) : w \mapsto \sum_v P_w(v) X(v)$; the expert is *immodest* at $w$ if $P_w(P = P_w) = 1$.

| DDB notion | LI notion here | comment |
|---|---|---|
| Reflection $\pi(\cdot \mid P=\rho) = \rho$ | (rejected) | incompatible with modesty; strictly above the tower |
| Total Trust $E_\pi(X \mid E(X) \ge t) \ge t$ | soft Total Trust | hard cut becomes the $\operatorname{Ind}_\delta$ ramp |
| Value (menus, world-dependent strategy) | Value | DDB's followed strategy is a *diagonal* $\widehat S(w) = S_w(w)$; LI's is a single option — see [[expert-conditions]] |
| marginal martingale $\pi P = \pi$ | tower on the bare options only | a frame artifact; no privileged status in LI (§1.5) |
| — | Mart, the tower | the single principle the LI notions collapse toward |

DDB Theorem 2.2: on a finite frame, Total Trust $\Leftrightarrow$ Value; for immodest experts both coincide with Reflection, and modesty separates them (the anti-expert frame satisfies $\pi P = \pi$ yet fails Value). Their hard direction (Total Trust $\Rightarrow$ Value) is an "excruciating" convex-geometry reconstruction; the LI reversal of difficulty — that direction becoming easy while the squeeze back to the tower becomes the hard part — is [[reversal-of-difficulty-vs-ddb]], and the structural reason (single state vs. frame) is [[expert-conditions]]. Weatherson (2025) breaks Thm 2.2 both ways on infinite frames; LI excludes both failure modes by standing scope conditions — see [[expert-conditions]] §"Weatherson".

## Implication diagram

For an observable, coherent, introspective expert (arrows labeled with the page that proves them):

```
Reflection  (DDB only; rejected — incompatible with modesty)
    ⇓  (never ⇑)
Mart (the tower)  ⟺  conditional tower (the fold)      [fold: deference-v6 §1.5, PROVED; w≡1 gives ⇐]
    ⇓  threshold bound                 ⇑ gap-bets, for gap-closed bet classes — [[total-trust-implies-mart]]
    ⇓                                    (parallel cuts of one X insufficient — [[amplifier-counterexample]])
Total Trust  ⟺  Value                  [two-option menus, exact, per (X,s)] — [[two-option-value-iff-total-trust]]
```

Individual arrows and routes:

- **Mart $\Rightarrow$ Value** — direct, two tower steps + two `expprovind` steps: [[mart-implies-value]].
- **Value $\Leftrightarrow$ Total Trust** — the two-option menu $\{X, \text{const } s\}$, an exact identity, both directions: [[two-option-value-iff-total-trust]].
- **Total Trust $\Rightarrow$ Value** — independently of the two-option equivalence, by three direct routes (the keep-or-switch telescope, the one-shot hedge, and provable-bound respect — the last delivering the *hard*-argmax form from full TT): overview at [[total-trust-implies-value-telescoping]].
- **Total Trust $\Rightarrow$ Mart** — for a **gap-closed** bet class (bets may mention the expert's observable estimates), a two-line argument via gap-bets $Z - \ulcorner E^\ast(Z)\urcorner$: [[total-trust-implies-mart]] (PROVED prose, unvetted). From parallel cuts of a single bet alone it *fails* — the amplifier $g(e) = (1+2c)e - c$ passes every threshold cut: [[amplifier-counterexample]].
- **Value $\Leftrightarrow$ Total Trust $\Leftrightarrow$ Mart** — the assembled triangle; all three collapse at full quantifier strength, and the separations live on restricted domains: [[value-iff-mart]].

## Status

- **Mart, ccee, Total Trust, Value as *hypotheses*** — definitions, no status. Mart is **not a paper theorem**; its self-trust instance is `cee` 4.12.1 (see the dictionary in [[conventions-and-status-labels]]).
- **The fold (universal tower contains its conditional form, expert knows the weight)** — **PROVED (prose)**, deference-v6 §1.5; finite-exact core kernel-checked (`DeferenceFold.fold_sum`).
- **Tower $\Rightarrow$ Total Trust (threshold-bound derivation)** — **PROVED (prose)**, deference-v6 §1.6; composition of the fold and `expprovind`.
- **Total Trust $\not\Rightarrow$ tower from parallel cuts (amplifier)** — **KERNEL-CHECKED** (`amp_upper_cut_nonneg`, `amp_boundedness_forces_id`): [[amplifier-counterexample]]. **Total Trust $\Rightarrow$ tower for gap-closed classes** — **PROVED (prose), unvetted**: [[total-trust-implies-mart]] (supersedes deference-v6 Appendix B's "squeeze stays prose" row for gap-closed classes, if vetted).
- **Reflection too strong / ceiling at the tower** — **INTERPRETATION** (deference-v6 §1.6, §2.2), resting on the proved incompatibility of modesty with finite-frame conditional coherence ([[expert-conditions]]).

Per deference-v6 Appendix B, the §1–§2 tier is "the most solid tier" of the corpus; the Lean honesty caveat of [[conventions-and-status-labels]] applies to every kernel-checked item.

## Related

- [[setting-and-notation]] — the shared world and the two settings
- [[ledger-decided-tie-breaks]] — the tie-break hygiene F1 needs (undecidable rules break it by correlation)
- [[expert-conditions]] — what observable/coherent/introspective buy; why modesty forces an infinite process
- [[mart-implies-value]], [[two-option-value-iff-total-trust]], [[total-trust-implies-value-telescoping]], [[total-trust-implies-mart]], [[amplifier-counterexample]], [[value-iff-mart]] — the result pages for the diagram
- [[reversal-of-difficulty-vs-ddb]] — the difficulty table against DDB
- [[trichotomy-where-value-sits]] — which notion survives where, across processes

*Source: deference-v6 §0.5, §1 preamble, §1.5, §1.6 (`deference-in-logical-induction-v6.md`).*
