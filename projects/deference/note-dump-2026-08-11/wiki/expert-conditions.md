# Expert conditions

*What the expert must be for the deference theory to run — observable, coherent, optionally introspective — what each condition buys, why a coherent single state is cheap where a DDB frame is dear, why a modest-but-coherent expert must be an infinite process, and how Weatherson's infinite-frame failures map onto LI's two standing scope conditions.*

## Setting

**Abstract single-expert setting** ([[setting-and-notation]]): a logical-inductor novice $H \dashv \mathcal{C}_H$ and an expert $E^\ast$, an observable sequence of estimates. The conditions below are conditions on $E^\ast$ alone; nothing here assumes the coupled cross-process structure (mutual observability, joint clearing), though both canonical instances — the future self $E^H_{f(n)}$ and a distinct inductor $A$ — satisfy all three conditions (for the self they are LI theorems; for an inductor-$A$ they hold by construction plus the quote ledger). Source: deference-v6 §2 (and §0.4 for the definitions).

## The three conditions, and what each buys

- **Observable.** $E^\ast$'s estimates are $\mathcal{C}_H$-cheap for $H$ to *read* (for the AI instance: the quote ledger — produce-hard, read-cheap; see [[setting-and-notation]]). This is what lets the deference relation be *stated* at all: the LUV $\ulcorner E^\ast(X) \urcorner$ is well-formed in $H$'s world, the followed strategy $\widehat S_n$ is an e.d. LUV (so no illegal `argmax` weight arises), and the two-option menus of [[two-option-value-iff-total-trust]] are constructible. One hygiene condition rides along: the argmax tie-break must be **ledger-decided**, or F1 fails by correlation — [[ledger-decided-tie-breaks]].
- **Coherent — a single belief state.** $E^\ast$ is a coherent expectation operator: linear, $\Gamma$-representable. This buys the selection identity **(F1)**: $\arg\max_j E^\ast(O^j)$ is well-defined and $E^\ast(\widehat S_n) = \max_j E^\ast(O^j_n)$ is $\Gamma$-provable, tie-break-independently — the step that makes [[mart-implies-value]] two lines instead of a convex-geometry reconstruction (§2.1 below). **⚠ (2026-07-25): exact coherence is an idealization the instances cannot satisfy** — a finite-day inductor is only asymptotically coherent (and *can* only be: §2.2's liar argument), so exact F1 holds only in the surrogate reading of composite estimates; the actual-expectation form is asymptotic **self-endorsement**, which additionally costs introspection and a decision-theoretic scope condition ([[total-trust-implies-value]] §Lemma 2).
- **Introspective (optional).** $E^\ast(\ulcorner E^\ast(X) \urcorner) \approx E^\ast(X)$: the expert knows its own estimates, approximately and increasingly. Needed **only** for the conditional/fold results — it is the "expert knows the weight" hypothesis of the fold ([[deference-notions]], deference-v6 §1.5). For the future self it is the paper's `epr`/`er` (4.11.4/4.11.5); for an inductor-$A$ it is $A$'s own introspection theorem.

That is the whole list. In particular the expert need **not** be truthful, need not be realizable inside the novice (§2.4), and need not be immodest (§2.2) — the last two being exactly where the LI story earns its keep over the finite-frame one.

## §2.1 — A coherent single state is cheap; a frame is dear

The reversal of difficulty against DDB ([[reversal-of-difficulty-vs-ddb]]) has one root cause: *what kind of object the expert is*.

**A DDB expert is an information frame** — a credence $P_w$ per world, hence a *world-dependent* recommendation $S_w$. The realized return of "follow the expert" is the **diagonal** $\widehat S(w) = S_w(w)$, and the expert's own score of the followed strategy, $E_a(\widehat S) = \sum_v P_a(v)\, S_v(v)$, is **not** the row-wise maximum (in the anti-expert frame $E_a(\widehat S) = -1$ while the max is $0.6$). Bridging the $\pi$-average of the diagonal to the $\pi$-average of the maxima is DDB's hard direction: a convex-hull reconstruction plus Blackwell–Geanakoplos value-of-information — the proof its authors call "excruciating".

**A coherent $E^\ast$ is a single belief state** — one set of estimates, one argmax, so the followed strategy is the *single option* $O^{j^\ast}$ and $E^\ast(\widehat S) = M$ holds by definition (F1). There is no world-dependent strategy and no diagonal to reconstruct. The novice's uncertainty about $E^\ast$ is **logical** — uncertainty about a definite quantity it has not finished computing — not *which-world* uncertainty about which $P_w$ obtains. The tower is exactly the bridge DDB build by hand, handed over instead by no-Dutch-book.

| | DDB | LI (general expert) |
|---|---|---|
| the expert is… | a frame (a credence per world) | a single coherent belief state |
| the recommendation is… | world-dependent $S_w$ | one option $O^{j^\ast}$ |
| $E_{\text{expert}}(\text{followed strategy})$ | not the max (diagonal mixes) | the max, by F1 |
| diagonal→row-wise bridge | reconstructed (convex hull) | free (the tower) |

Consequence: the natural cross-process experts are **other logical inductors** (or any coherent calibrated estimator) — single states, cheap to defer to. A frame is the expensive object, and LI never has to pay for one.

## §2.2 — Modest but coherent forces an infinite process

Is a coherent observable expert just *immodest*, collapsing to DDB's easy corner? No — and the modesty that survives is the point.

**What survives is incomplete self-knowledge, not identity-uncertainty.** A coherent inductor-expert knows its own estimates only approximately and increasingly (introspection), never to *paradoxical* completeness — complete self-knowledge would let the diagonal lemma build a liar it cannot settle. So $E^\ast$ knows enough to value its own choices (F1 needs only definite estimates of exogenous options) yet cannot host a sharp self-referential predicate about its own beliefs and stay consistent. This differs from DDB-modesty, which is uncertainty about *which credence function one is*.

**Finite frames cannot combine modesty with conditional-tower coherence.** On a *finite* frame, suppose the soft conditional tower holds for all bounded $X$. The finitely many values $\{E_w(X)\}$ leave a **spectral gap**; for ramp width $\delta$ below the gap the soft indicator equals the hard one, the threshold events then generate the expert's $\sigma$-algebra, and the hypothesis collapses to $E(X) = E_\pi(X \mid \mathcal{P})$ — immodesty on the novice's support. So on a finite frame, the very property that makes Value cheap *forces immodesty*.

A reasoner that is at once **modest** and **conditional-tower-coherent** therefore needs estimates taking continuum-many, gapless values — an **infinite, self-referential process**. Logical inductors are exactly that: a continuum of consistent completions, dense future estimates, and a permanent gap between the *hard* conditional tower (which the liar keeps false) and the *soft* one (which holds). Whether the expert is your future self or a different AI, clean modest deference lives only between infinite-frame processes — of which inductors are the concrete inhabitants. ⚠ (2026-07-25) The same permanent self-opacity has a second job: it keeps the expert's *self-conditionals* well-defined — self-uncertainty acts as endogenous exploration, grounding the conditional-stability scope condition of [[total-trust-implies-value]] without an exploration coin.

## §2.3 — Weatherson's infinite failures are LI's two scope conditions

Weatherson (2025) breaks DDB Theorem 2.2 in both directions on infinite frames. Each counterexample exploits exactly one thing the LI framework excludes for an independent, prior reason:

| failure | direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust $\not\Rightarrow$ Value | unbounded utility | bounded LUVs / finite-risk traders |
| **Bentham** | Value $\not\Rightarrow$ Total Trust | hard conditioning on a null tail | finite stages + soft $\operatorname{Ind}_\delta$ |

*Coin:* options with $2^i$-scale payoffs make the recommended strategy's diagonal worth $0$ while every fixed option has positive expectation — excluded in LI because expectations are defined only for **bounded** LUV-combinations (boundedness is the uniform-integrability that [[mart-implies-value]] needs). *Bentham:* Total Trust fails at a single measure-zero world — excluded because every LI statement quantifies over **finite** stages with $n \to \infty$ and conditions only **softly**, never on a hard null event. So the infinite-frame breakdown is not a threat LI must answer; it is two constraints LI already imposes, seen from outside.

## §2.4 — The realizability payoff

DDB's finite story is **realizable**: the novice's candidate set literally contains the expert's credence function. That is cognitively fake for the cases that matter. LI earns Total Trust $\Leftrightarrow$ Value **without** realizability — and this matters more across processes than for self-trust: the expert is a separate, possibly *larger* process, provably not realizable within the novice (a full internal model of it is barred by the liar), yet deference-as-Value still goes through, approximately and in a timely manner. A deference theorem that survives the removal of realizability — in the one setting where a finite mind reasons soundly about something bigger than itself — is the reassurance the finite-frame proof could not give.

## Status

Per deference-v6 Appendix B ("Abstract theory (§1–§2) — the most solid tier"):

- **§2.1 (single state cheap / frame dear)** — **PROVED**: the cheap direction is exact and tie-break-free (Lean `value_of_argmax`); the dear direction is witnessed by the anti-expert frame, checked numerically (sympy) and in Lean (`AntiExpert.stationary` + `AntiExpert.value_fails`: the marginal martingale holds, Value fails). Appendix B status `P`.
- **§2.2 (modest + coherent $\Rightarrow$ infinite process)** — the hard-indicator tail is **KERNEL-CHECKED** (`CM_implies_immodest`, the fiber-indicator core: the conditional tower on a fiber forces $P_w(P = P_w) = 1$); the **soft⇒hard reduction** (spectral gap collapses the soft indicator to the hard one) is **PROVED (prose)** only — Appendix B marks the step `Pr`. The Lean honesty caveat of [[conventions-and-status-labels]] applies.
- **§2.3 (Weatherson ↔ scope conditions)** — **INTERPRETATION**: a mapping of counterexamples onto standing framework features, not a mathematical claim; boundedness and soft conditioning live in the $[0,1]$-LUV typing and the $\operatorname{Ind}_\delta$ definition rather than in any theorem.
- **§2.4 (realizability payoff)** — **INTERPRETATION**.

## Related

- [[setting-and-notation]] — the shared world; the two settings
- [[deference-notions]] — the notions these conditions power, and the implication diagram
- [[reversal-of-difficulty-vs-ddb]] — the difficulty table §2.1 explains
- [[mart-implies-value]], [[two-option-value-iff-total-trust]] — where F1 and observability are spent
- [[ledger-decided-tie-breaks]] — the crack where a frame could re-enter, and what seals it
- [[amplifier-counterexample]] — the soft/hard gap that §2.2 shows is permanent for a modest expert; [[total-trust-implies-mart]] — the equality is nevertheless reachable for gap-closed bet classes
- [[no-forced-trust]] — what these conditions do *not* buy across processes (agreement on undecidables)

*Source: deference-v6 §2.1–2.4, with definitions from §0.4 (`deference-in-logical-induction-v6.md`).*
