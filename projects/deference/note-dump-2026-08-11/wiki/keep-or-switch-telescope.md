# Total Trust ⟹ Value: the keep-or-switch telescope

*"Follow the expert on a $K$-menu" decomposes into $K-1$ pairwise keep-or-switch deferrals, each a two-option Value instance by the two-option identity of [[two-option-value-iff-total-trust]], and the chain telescopes: Total Trust **at threshold $0$ only** yields full-menu ($\delta$-hedged) Value — no tower, no squeeze. This is the original proof of the result; it needs uniformly bounded menu size, a restriction the one-step companion routes remove.*

**Provenance.** Proved in the 2026-07-20 Claude Code session (session `b9e8341b`, fourth user turn: "Can you prove total-trust → value similarly to how you proved mart→value?"); the proof exists only in that conversation and its faithful extraction `imported-chats/analysis/session-b9e8341b-proof.md`. This page is the self-contained exposition of that proof, split out of the original single-page write-up on 2026-07-23; the overview of the result and its companion routes ([[one-shot-hedge]], [[provable-bound-respect]]) is [[total-trust-implies-value-telescoping]]. Checks made during the write-up that go beyond the extraction are marked **⚠ (write-up)**.

**⚠ Scope revision (2026-07-25).** This page is stated in the surrogate formulation: "$E^\ast(D)$" in weights and in Claims A/B is the linear extension of the published quotes (ledger arithmetic). The novice-side telescope inequality stands as proved *relative to surrogate-TT*. But the reading of Claim A as "the expert rates the chain at the running max" is exact only about that arithmetic; about an inductor-expert's actual expectations it is asymptotic at best and requires the decision-theoretic scope condition of [[total-trust-implies-value]] — on selection-referencing (punishing) menus it is false, Value itself fails, and surrogate-TT over such domains is unsatisfiable (the contradiction moves into the hypothesis). "Exogenous" menus must be read per conditional-stability there ([[defining-exogeneity]] surveys the rejected menu-intrinsic definitions).

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): novice $H \dashv \mathcal{C}_H$ a logical inductor; expert $E^\ast$ **observable**, **coherent**, and **introspective** ([[expert-conditions]]). Menu apparatus as in [[deference-notions]]: an e.d. sequence of finite menus $\mathcal{O}_n = \{O^1_n, \dots, O^{K}_n\}$ of bounded $[a,b]$-LUVs, $m^j := E^\ast(O^j)$, and here the *running* max $M_k := \max_{j \le k} m^j$ (so $M_K$ is the usual $M_n$). Day index $n$ is suppressed in the construction; every object is per-day and the asymptotics quantify over $n$.

**Derived estimates.** For a bounded LUV-combination $D = c + \sum_j \alpha_j O^j$ with ledger-computable coefficients, write $E^\ast(D) := c + \sum_j \alpha_j m^j$ — the value *derived* from the published estimates by linearity. Coherence makes this the expert's actual estimate; observability makes it a $\mathcal{C}_H$-cheap, $\Gamma$-decided quantity the novice can condition on. This is what "$E^\ast(D)$" means inside every weight below.

**Hypotheses used — exactly these, nothing more:**

- **TT$(\cdot, 0)$** — a fragment of Total Trust. In full, Total Trust ([[deference-notions]]) says: for every e.d. bet sequence $X$, every threshold $t$, and every ramp width $\delta$,
  $$ E^H_n\big(X \cdot \operatorname{Ind}_\delta(E^\ast(X) > t)\big) \;\gtrsim_n\; t \cdot E^H_n\big(\operatorname{Ind}_\delta(E^\ast(X) > t)\big), $$
  where $\operatorname{Ind}_\delta(x > t)$ is the **ramp indicator** — the continuous surrogate for the (illegal-as-a-weight) hard indicator, equal to $0$ for $x \le t$, to $1$ for $x \ge t + \delta$, linear between. Read: "on the region where the expert rates $X$ above $t$, the novice's estimate is above $t$ too," in the unnormalized soft form deference-v6 §1.2 shows equivalent to the conditional one. This proof assumes only the **threshold-$t = 0$ instances**, where the right-hand side vanishes: over all e.d. bounded LUV-combinations $D$ built from menu options and observable expert-estimates, for every width $\delta$,
  $$ E^H_n\big(D \cdot \operatorname{Ind}_\delta(E^\ast(D) > 0)\big) \;\gtrsim_n\; 0. $$
  (The companion route [[provable-bound-respect]] is what spends thresholds other than $0$; this page never does.) In the finite-exact setting the hard indicator $\mathbb{1}[E^\ast(D) > 0]$ is a legal weight and the same hypothesis is used hard.
- The **novice's own** `loe` (Linearity of Expectation, 4.8.4) and `expprovind` (Expectation Provability Induction, 4.8.10) — free LI theorems of $H$ ([[setting-and-notation]]; label dictionary in [[conventions-and-status-labels]]).
- Expert-side facts only through **coherence + introspection** (Claim A below — the same `hknow` ingredient as the fold and as F1; cf. the Remark on [[mart-implies-value]]).

**No tower.** No Mart instance, no self-trust theorem (`cee`/`ccee`/`st`), no squeeze — Total Trust is the *only* deference hypothesis.

**⚠ (write-up) — uniformly bounded menu size.** The extraction leaves menu size implicit. The telescope applies `loe` and TT once per rung, i.e. $K-1$ times; the composition of finitely many $\approx_n / \gtrsim_n$ steps is only automatic when the number of rungs is uniform in $n$. So the honest scope is: menu sequences of **uniformly bounded size** $K_n \le K$. (Contrast [[mart-implies-value]], whose four-step chain is size-independent — "no bound on $k$". Unbounded $K_n$ would need uniform-in-rung error control that 4.8.4/4.8.10 as cited do not supply.) Both one-step companion routes remove this restriction: [[one-shot-hedge]] within the same threshold-$0$ fragment, [[provable-bound-respect]] using the full threshold family.

## Statement

The target is **Value** ([[deference-notions]]): for every e.d. sequence of finite menus and every fixed index $i$,

$$ E^H_n\big(\widehat S_n\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big) $$

— "letting the expert decide" is weakly preferred, by the novice's own lights, to committing in advance to any fixed option. Fix $i$; call $O^i$ the **comparison option**. Here "letting the expert decide" is implemented not by the one-shot argmax $\widehat S$ of [[deference-notions]] but by an equivalent **chain strategy**, defined precisely in the Construction section below: start holding the comparison option $O^i$, then walk through the other $K-1$ options one at a time, at each step keeping the incumbent or switching to the newcomer according to which the expert rates higher. The result after all $K-1$ decisions is written $\widehat S^{(K)}$; its **$\delta$-hedged variant** $\widehat S^{(K)}_\delta$ replaces each hard keep-or-switch by a soft blend across a ramp of width $\delta$ (the form LI's continuity constraints permit — see "The wedge" below). Claim A below certifies that the chain really implements follow-the-expert: the expert provably rates it at the menu max $M_K$ (within $\delta$, for the hedged variant).

**Theorem (Total Trust ⟹ Value, telescoping; soft/honest LI form).** Assume TT$(\cdot,0)$. Fix $\delta > 0$ and an index $i$, and let $\widehat S^{(K)}_\delta$ be the $\delta$-hedged chain strategy of the Construction, built starting from the comparison option $O^i$. Then

$$ E^H_n\big(\widehat S^{(K)}_\delta\big) \;\gtrsim_n\; E^H_n(O^i_n), \qquad \Gamma \vdash M_K - \delta \;\le\; E^\ast\big(\widehat S^{(K)}_\delta\big) \;\le\; M_K. $$

That is: "let the expert decide, hedging each keep-or-switch across a $\delta$-ramp" is weakly preferred, by the novice's own lights, to committing to any fixed option, and the expert rates the hedged strategy within $\delta$ of the full-menu max.

**Theorem (hard/finite-exact form).** In a setting where hard indicators are legal (finite-exact / DDB-style, or any setting granting TT with hard weights), the chain $\widehat S^{(K)}$ *is* the argmax strategy under the first-max-wins tie-break, $\Gamma \vdash E^\ast(\widehat S^{(K)}) = M_K$ exactly, and

$$ E^H_n\big(\widehat S^{(K)}\big) \;\gtrsim_n\; E^H_n(O^i_n) $$

— full-menu **Value** ([[deference-notions]]). "The wedge" below is the precise account of which of the two forms LI proper delivers.

## Construction — follow-the-expert as a chain of keep-or-switch decisions

Relabel the menu so the comparison option $O^i$ comes first, i.e. $O^1 = O^i$ in the processing order. Starting the chain *at* the comparison option is what makes the proof work: each rung will show the novice weakly prefers stage $k$ to stage $k-1$, so the telescope bottoms out exactly at $\widehat S^{(1)} = O^i$, giving $E^H_n(\widehat S^{(K)}) \gtrsim_n E^H_n(O^i)$ — the Value inequality for index $i$. Define recursively:

$$ \widehat S^{(1)} := O^1 = O^i, \qquad D_k := O^k - \widehat S^{(k-1)}, \qquad \widehat S^{(k)} := \widehat S^{(k-1)} + D_k \cdot \mathbb{1}\big[E^\ast(D_k) > 0\big] \quad (k = 2, \dots, K). $$

At each stage the expert compares the incumbent to the next option and switches iff it rates the newcomer strictly higher. Each $D_k$ and $\widehat S^{(k)}$ is an e.d. LUV: its formula references only menu options and the expert's observable estimates (the thin channel makes the indicator's argument a decided fact), so the hard indicator lives *inside a LUV formula*, never as a trade weight — the discontinuity obstruction does not arise here. As a combination, $\widehat S^{(k)} = \sum_j c_j O^j$ with $c_j \in \{0,1\}$, $\sum_j c_j = 1$: an $[a,b]$-valued combination of coefficient mass $1$, so the bounded forms of `loe`/`expprovind`/TT all apply.

The **$\delta$-hedged variant** replaces the hard indicator with the soft ramp:

$$ \widehat S^{(k)}_\delta := \widehat S^{(k-1)}_\delta + D_k \cdot \operatorname{Ind}_\delta\big(E^\ast(D_k) > 0\big), \qquad D_k := O^k - \widehat S^{(k-1)}_\delta, $$

(note $D_k$ now depends on $\delta$ through the incumbent). Writing $\theta_k := \operatorname{Ind}_\delta(E^\ast(D_k) > 0) \in [0,1]$, each $\widehat S^{(k)}_\delta = (1-\theta_k)\,\widehat S^{(k-1)}_\delta + \theta_k O^k$ is a *convex combination* of menu options — again bounded, coefficient mass $1$, all coefficients continuous ledger-computable functions.

### Claim A (F1, generalized): $\Gamma \vdash E^\ast(\widehat S^{(k)}) = M_k$

By induction on $k$. Base: $E^\ast(\widehat S^{(1)}) = m^1 = M_1$. Step: the indicator's value is a function of the expert's own estimates, which the expert knows (**introspection** — exactly the fold's `hknow`) and which are $\Gamma$-decided facts (**observability**); so it enters $E^\ast$ as a known scalar, and **coherence** (expert linearity) gives, with $E^\ast(D_k) = m^k - E^\ast(\widehat S^{(k-1)}) = m^k - M_{k-1}$ by linearity + the inductive hypothesis:

$$ E^\ast(\widehat S^{(k)}) \;=\; E^\ast(\widehat S^{(k-1)}) + E^\ast(D_k)\cdot\mathbb{1}\big[E^\ast(D_k) > 0\big] \;=\; M_{k-1} + \max\big(0,\; m^k - M_{k-1}\big) \;=\; M_k. \checkmark $$

*(Algebra verified in the write-up.)* Note Claim A is **not used in the telescope inequality itself** — the proof below consumes only `loe` and TT. Claim A is what certifies the *interpretation*: that the chain implements follow-the-expert (Claim B) and that the expert rates the final strategy at the max (the generalized F1).

**Soft Claim A: $\Gamma \vdash M_k - \delta \le E^\ast(\widehat S^{(k)}_\delta) \le M_k$, and the $\delta$-loss does not accumulate.** ⚠ (write-up — verified, slightly strengthening the extraction's one-sided $\ge M_K - \delta$.) Write $V_k := E^\ast(\widehat S^{(k)}_\delta)$, $d_k := E^\ast(D_k) = m^k - V_{k-1}$, so $V_k = (1-\theta_k)V_{k-1} + \theta_k m^k$ with $\theta_k = \operatorname{Ind}_\delta(d_k)$. Upper bound: $V_k$ is a convex combination of $V_{k-1} \le M_{k-1} \le M_k$ and $m^k \le M_k$. Lower bound, by cases on $d_k$: if $d_k \ge \delta$ then $\theta_k = 1$, $V_k = m^k$, and $m^k \ge V_{k-1} + \delta \ge M_{k-1}$ forces $M_k = m^k$; if $d_k \le 0$ then $V_k = V_{k-1} \ge M_{k-1} - \delta$ and $m^k \le V_{k-1} \le M_{k-1}$ forces $M_k = M_{k-1}$; if $0 < d_k < \delta$ then $V_k \ge V_{k-1}$, and either $M_k = M_{k-1}$ (inductive hypothesis suffices) or $M_k = m^k = V_{k-1} + d_k < V_{k-1} + \delta$, so $V_k \ge V_{k-1} > M_k - \delta$. In every case the loss stays a single $\delta$, uniformly in $k$ — the hedge only pays at the final near-tie, not once per rung.

### Claim B: $\widehat S^{(K)}$ is the argmax strategy — with a tie-break wrinkle ⚠

Since the chain switches only on *strict* improvement, $\widehat S^{(K)}$ selects the option with the maximal estimate, first occurrence winning ties **in the processing order** — the "first max wins" tie-break, which is ledger-decided (computable from the published estimates) — the property F1 actually needs; legality alone would not force it ([[ledger-decided-tie-breaks]]); and F1 is tie-break-independent (Claim A holds regardless), so $E^\ast(\widehat S^{(K)}) = M_K$ either way.

**⚠ (write-up) — the wrinkle the extraction glosses:** the relabeling promotes $O^i$ to the front, so the tie-break is **$i$-dependent**: at a tie for the max involving $O^i$, the chain returns $O^i$, whereas the canonical least-index $\widehat S$ of [[deference-notions]] may return a different option. So what the telescope literally proves is: *for each $i$, the $i$-promoted argmax strategy $\widehat S^{[i]}$ dominates $O^i$* — a per-$i$ family of strategies, not one fixed $\widehat S$ dominating all $i$. Three repairs: (1) if the argmax is eventually unique (no ties), all the $\widehat S^{[i]}$ coincide with $\widehat S$ and the wrinkle vanishes; (2) the difference $\Delta := \widehat S - \widehat S^{[i]}$ has $\Gamma \vdash E^\ast(\Delta) = 0$ (both sides are $M_K$ by tie-break-independent F1), and the provably-full cuts of [[provable-bound-respect]] applied to $\pm\Delta$ pin $E^H_n(\Delta) \approx_n 0$, bridging the two strategies — but this uses thresholds other than $0$; (3) accept the per-$i$ statement — the decision-theoretic content of Value ("for each committed option, following the expert is weakly better") survives intact, only the literal single-fixed-tie-break phrasing needs (1) or (2). The [[one-shot-hedge]] route avoids the wrinkle from the start by never relabeling.

## Proof — the telescope

For each $k = 2, \dots, K$, writing $Z_k := D_k \cdot \mathbb{1}[E^\ast(D_k) > 0]$ (an e.d. LUV; $\Gamma \vdash \widehat S^{(k)} = \widehat S^{(k-1)} + Z_k$ by definition):

$$
\begin{aligned}
E^H_n\big(\widehat S^{(k)}\big)
&\;\approx_n\; E^H_n\big(\widehat S^{(k-1)}\big) + E^H_n\big(D_k \cdot \mathbb{1}[E^\ast(D_k) > 0]\big)
&&[\texttt{loe } 4.8.4,\ \text{unit coefficients}]\\[2pt]
&\;\gtrsim_n\; E^H_n\big(\widehat S^{(k-1)}\big)
&&[\textbf{TT}(D_k,\, 0)].
\end{aligned}
$$

Telescoping the $K-1$ rungs from $K$ down to $1$:

$$ E^H_n\big(\widehat S^{(K)}\big) \;\gtrsim_n\; E^H_n\big(\widehat S^{(1)}\big) \;=\; E^H_n(O^i_n). \qquad \blacksquare $$

The soft telescope is **verbatim** with $\operatorname{Ind}_\delta$ in place of $\mathbb{1}$: the `loe` step splits off $Z_k^\delta := D_k \cdot \operatorname{Ind}_\delta(E^\ast(D_k) > 0)$ (now with a *continuous*, market-generable weight — legal even as a trade weight), and TT$(D_k, 0)$ at width $\delta$ is exactly $E^H_n(Z_k^\delta) \gtrsim_n 0$. Combined with soft Claim A this is the soft/honest theorem of the Statement. Where hard indicators are legal weights (finite-exact setting), the hard telescope above stands as written and Claim A is exact — full Value.

**Assumptions audit.** Novice side: `loe` (4.8.4) once per rung, and `expprovind` (4.8.10) only insofar as it backs the unnormalized-TT bookkeeping and the constant-LUV evaluations; TT$(D_k, 0)$ once per rung. Expert side: coherence + introspection, and only inside Claim A/B (the interpretation), not inside the inequality. No tower, no self-trust.

## Structural reading: two-option Value telescopes to full Value

By the deference-v6 §1.2 boxed two-option identity ([[two-option-value-iff-total-trust]]), TT$(D_k, 0)$ **is** Value on the two-option menu $\{D_k, \text{const } 0\}$ — the exact identity $E_\pi(\widehat S_{\{D_k,\,0\}}) - 0 = E_\pi(D_k \cdot \mathbb{1}[E^\ast(D_k) \ge 0])$ makes the two statements one, per instance. So the theorem says:

> *"Follow the expert on a $K$-menu" decomposes into $K-1$ pairwise keep-or-switch deferrals, and two-option Value telescopes to full-menu Value.*

The convex-geometry squeeze of deference-v6 §1.6 is **bypassed** because Value never needed $g = \mathrm{id}$ — the tower *equality* — at any point: only the one-sided threshold inequalities, one per rung. Value is "one rung below the tower," and this proof shows it lives there natively rather than being inherited from above ([[mart-implies-value]] proves the same conclusion from one rung up). This decomposition is the conceptual payload of this route: the one-step routes ([[one-shot-hedge]], [[provable-bound-respect]]) prove the same (or stronger) theorems, but only the telescope exhibits follow-the-expert as a *chain of pairwise deferrals among the actual menu options*, each rung a two-option-identity instance.

## The wedge — why threshold-$0$ TT stops at the hedged strategy

With genuine soft weights $\operatorname{Ind}_\delta$, the honest theorem concerns the **$\delta$-hedged** strategy $\widehat S^{(K)}_\delta$. Total Trust **at threshold $0$** does *not* give Value for the argmax strategy itself: threshold cuts only lower-bound high-region integrals and upper-bound low-region ones, so nothing lower-bounds the wedge term

$$ E^H_n\Big(D \cdot \big(\mathbb{1}[E^\ast(D) > 0] - \operatorname{Ind}_\delta(E^\ast(D) > 0)\big)\Big), \quad \text{supported on } 0 < E^\ast(D) \le \delta, $$

separating the hard rung from the soft one — and that missing bound is exactly the amplifier's surviving degree of freedom (a novice may value $D$ at $\approx -c$ where the expert's estimate sits just above $0$; [[amplifier-counterexample]]). In the finite-exact/DDB-style setting hard indicators are legal, the wedge is empty, and the induction gives full Value exactly.

The extraction concludes: "hard-argmax Value therefore remains a Mart-only deliverable." **⚠ (write-up): that overshoots.** The claim is accurate for the threshold-$0$ fragment used by this page, but TT as defined in [[deference-notions]] quantifies over *every* threshold, and cuts at negative thresholds — provably full ones — close the gap without Mart: see [[provable-bound-respect]].

## Status

**PROVED (prose, this page)** — the $\delta$-hedged soft form as stated; the hard form in finite-exact settings. **Unvetted by Abram as of 2026-07-23; not machine-checked.** The exposition is faithful to the extraction; the ⚠ items (bounded menu size, the Claim-B tie-break wrinkle and its repairs, the two-sided soft Claim A, and the overshoot flag on the extraction's "Mart-only" conclusion) are write-up additions and carry the same unvetted status. **Machine-check candidate** ([[open-problems]]): the telescope is a finite composition of `Approx`/`AsympLE` steps plus the Claim A induction — the same shape as the existing kernel-checked chains, and well within reach of the `lean-deference` style (the Lean honesty caveat of [[conventions-and-status-labels]] would apply as usual).

## Related

- [[total-trust-implies-value-telescoping]] — overview of the result and its three routes
- [[one-shot-hedge]] — same threshold-$0$ hypothesis, one rung, no menu-size bound (unvetted, 2026-07-23)
- [[provable-bound-respect]] — full TT ⟹ Value itself in one step (unvetted)
- [[two-option-value-iff-total-trust]] — the two-option identity this proof telescopes
- [[mart-implies-value]] — the same conclusion from one rung up (and with no menu-size bound)
- [[deference-notions]] — TT, Value, menus/F1/F2, the implication diagram
- [[reversal-of-difficulty-vs-ddb]] — why this direction is cheap in LI and excruciating in DDB
- [[expert-conditions]] — what observable/coherent/introspective buy (Claim A's exact bill)
- [[amplifier-counterexample]] — the degree of freedom the wedge term leaves open
- [[ledger-decided-tie-breaks]] — why the tie-break must be computable from the ledger (F1, not legality)

*Source: `imported-chats/analysis/session-b9e8341b-proof.md` (primary; 2026-07-20 session `b9e8341b`); setting and apparatus from deference-v6 §1.1–§1.6 (`deference-in-logical-induction-v6.md` L155–292).*
