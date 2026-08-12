# Setting and notation

*The shared formal world for the whole wiki — the deductive process and theory $\Gamma$, the novice $H$ with its free LI theorems, the expert/AI $A$ with its targets, quotes and schedules — and the **two settings** (abstract single-expert vs. coupled cross-process) that every downstream page declares between.*

## Setting

This page *defines* the settings; it assumes nothing beyond the LI framework of Garrabrant et al. Every result page in this wiki opens by declaring which of the two settings of §"The two settings" below it works in. Source: deference-v6 §0.2–0.4 and §0.6; conventions and the label→theorem dictionary in [[conventions-and-status-labels]].

## The shared world (deference-v6 §0.2)

Fix a language $\mathcal{L}$ with sentence set $\mathcal{S}$, a consistent theory $\Gamma$ able to represent computable functions (e.g. PA), and a $\Gamma$-complete computable **deductive process** $D = (D^1 \subseteq D^2 \subseteq \cdots)$ revealing $\Gamma$'s theorems over time. A sentence is **decidable** if $D$ eventually decides it; its decided value is its **truth value** — the only notion of truth in play. Terminology: $D$ *decides* sentences; contracts *pay out* at settlement — so "settled" never does double duty.

Two boundaries organize everything downstream:

- **decidable vs. undecidable** — whether $D$ ever decides the sentence;
- within the decidable, **resolves in time vs. not** — whether $D$ decides it by the **lookahead** $F(n)$ (the deliberation budget below). The in-time part is the **timely fragment $G$**, where the frozen construction's soundness lives ([[frozen-deliberation-theorems]]).

**Trader classes.** Fix complexity classes $\mathcal{C}_H \subseteq \mathcal{C}_A$, each closed under polynomial overhead and computably enumerable (so the LI existence theorem can dovetail against the class's traders); canonically $\mathrm{P} \subseteq \mathrm{EXP}$. The **human/novice** $H$ is a logical inductor against $\mathcal{C}_H$; the **AI/expert** $A$, when it is a distinct inductor, runs against $\mathcal{C}_A$. The strict gap $\mathcal{C}_H \subsetneq \mathcal{C}_A$ is load-bearing for the forcing results ([[complexity-gap-hinge]]): $A$ can simulate $H$'s deliberation out to the lookahead, but not conversely. "e.c." (efficiently computable) always means computable in the reasoner's own class — for the novice, $\mathcal{C}_H$ — and this wiki reserves it for objects a trader must actually *evaluate*: weights, features, tie-break rules. For bets the honest term is "**e.d.**" (efficiently *describable*) — see the LUV bullet below.

## The novice $H$, and its free tools (deference-v6 §0.3)

$H = (H_n)_{n\ge1}$ is a logical inductor over $\Gamma$: $H_n(\varphi) \in [0,1]$ is the day-$n$ price (credence) of $\varphi$, and no $\mathcal{C}_H$-trader exploits the market — the **logical-induction criterion**, the computational no-Dutch-book from which every property below flows.

- **LUV.** A *logically uncertain variable* is a formula $X$ (one free variable) that $\Gamma$ proves names a unique real; an **$[a,b]$-LUV** if $\Gamma$ proves the value lies in the rational interval $[a,b]$. **e.d., not e.c. (2026-07-23).** The LI paper says "e.c. sequence of LUVs," but what is efficient there is production of the *descriptions* (the formulas) — never the described values, which may be uncomputable: the halting-bit LUVs $\mathbb{1}_{\psi_n}$ are the canonical case, trivially describable, undecidable in value, and pricing exactly such things is the point of LI. Because "e.c. LUV" invites the misreading that the *value* is computable, this wiki breaks with the paper's vocabulary and writes "**e.d. LUV**" (*efficiently describable*); "e.c." is reserved for what traders must evaluate (weights, features, tie-break rules — [[ledger-decided-tie-breaks]] is where the distinction earns its keep). (The wiki keeps general $[a,b]$ bounds, as deference-v6 does, so thresholds and offsets keep their natural scale; the LI paper's $[0,1]$ statements lift by affine rescaling. The bound $a$ is unrelated to the AI's quote $a_n$ below.)
- **Worlds.** A world $W$ assigns truth values to all sentences; $\mathrm{PC}(\Gamma)$ is the set of consistent completions. $H_\infty$ is a coherent measure on $\mathrm{PC}(\Gamma)$ (LI Limit Coherence 4.1.1), and "$\Gamma \vdash D \ge 0$" is the same as "$W(D) \ge 0$ in every consistent world."
- **LUV-combinations.** Finite affine combinations $c + \sum_i \alpha_i X_i$ of LUVs; **bounded** means $\sum_i |\alpha_i|$ is uniform in $n$ (the uniform-integrability stand-in).
- **Expectation.** $E^H_n(X)$ is $H$'s day-$n$ estimate of $X$ — the LI paper's discretized $\int H_n(X > x)\,dx$, valued in $[a,b]$ for an $[a,b]$-LUV.
- **Corner quotes.** $\ulcorner e \urcorner$ is the syntactic name (Gödel code) of the value $e$. So $E^A_n(X)$ is a *number*, $\ulcorner E^A_n(X) \urcorner$ is *the LUV naming it*, and the nested $E^H_n(\ulcorner E^A_n(X) \urcorner)$ — the human's estimate of the AI's estimate — is type-correct.
- **Asymptotics.** $x_n \approx_n y_n :\Leftrightarrow \lim_n (x_n - y_n) = 0$; $\;x_n \gtrsim_n y_n :\Leftrightarrow \liminf_n (x_n - y_n) \ge 0$. Every deference statement is asymptotic ("up to vanishing error, in a timely manner").
- **Market-generable weights.** A real sequence is *$\mathcal{C}_H$-market-generable* if computed by a $\mathcal{C}_H$-expressible feature of $H$'s prices (prices, rationals, $+,\times,\max$, safe reciprocation) — hence **continuous** in the prices. Continuity lets the market clear (Brouwer) and defuses self-reference; a hard $\mathbb{1}[\cdot > t]$ indicator is discontinuous and therefore not a legal trade weight. The soft ramp $\operatorname{Ind}_\delta(\cdot)$ of [[deference-notions]] exists to respect this.

**The novice's two free theorems** — consequences of $H$'s own criterion, independent of any expert, used unconditionally throughout:

> **Linearity of expectation** (`loe`, LI Thm 4.8.4, bounded form). For bounded $\mathcal{C}_H$-market-generable coefficients $(\alpha_n), (\beta_n)$ and e.d. $[a,b]$-LUVs with $\Gamma \vdash Z_n = \alpha_n X_n + \beta_n Y_n$: $\;\alpha_n E^H_n(X_n) + \beta_n E^H_n(Y_n) \approx_n E^H_n(Z_n)$.

> **Expectation provability induction** (`expprovind`, LI Thm 4.8.10, bounded form). If a bounded LUV-combination is provably nonnegative — $\Gamma \vdash D_n \ge 0$, uniformly in $n$ — then $E^H_n(D_n) \gtrsim_n 0$ (and provable equality gives $\approx_n$). This is what carries a $\Gamma$-provable (in)equality *through* $E^H_n$.

$H$'s *self-trust* theorems — `cee` (4.12.1), `ccee` (4.12.3), `epr`/`er` (4.11.4/4.11.5), `st` (4.12.4) — are also LI theorems, but they concern $H$'s relation to its **own future self**; in the general setting they appear only as the self-case instantiation of the deference hypotheses ([[deference-notions]]), never as free tools about an external expert.

## The AI, the targets, the quotes, the schedules (deference-v6 §0.4)

The thing $H$ defers to is an **expert** $E^\ast$ — an observable sequence of estimates — instantiated either as $H$'s own future self $E^H_{f(n)}$ or as a distinct stronger inductor $A$. The AI case carries the timing structure:

**The deferred target.** $A$ does not forecast the truth of the day-$n$ question $P^{(n)}$ directly. It forecasts where $H$'s *own deliberation* would get to on a budget: run (a copy of) $H$ on $P^{(n)}$ out to the **lookahead** $F(n)$ — superpolynomial, canonically $2^n$ — and read off

$$ Y_n := \big(\text{$H$'s deliberation on } P^{(n)}, \text{ run to stage } F(n)\big). $$

*Which* copy of $H$ (sealed off from $A$'s current quote, or the live coupled $H$) is exactly the fork between the two positive constructions — [[frozen-deliberation-construction]] vs. [[faithful-acceleration-result]].

**The quote.** $A$'s published forecast for question $n$ is $a_n := E^A_n(\ulcorner Y_n \urcorner) \in \mathbb{Q} \cap [0,1]$ — operationally, its day-$n$ estimate of a contract $C_n$ that pays out $Y_n$. Two clocks matter: the day index $n$ (when $A$ *forms* the forecast) and the publication stage $e(n)$ (when $H$ may *read* it); conflating them is what an unanalyzed "observable" hides.

**The three schedules** (monotone, $\mathcal{C}_H$-computable, ordered $n \le e(n) < F(n) < \sigma(n)$):
- **publication $e(n)$** — when $a_n$ is posted into $H$'s world;
- **lookahead $F(n)$** — the deliberation budget defining $Y_n$, and the cutoff for "resolves in time"; its self-case analogue is the deferral $f(n) > n$ of the future self, likewise $\sim 2^n$;
- **payout $\sigma(n)$** — when $C_n$ pays out against $Y_n$.

**Observable — the thin channel.** $H$ cannot *recompute* $a_n$ (producing it means simulating $H$'s deliberation to the lookahead, a $\mathcal{C}_A$-hard job), but it can **read** it: at stage $e(n)$, $A$ publishes $a_n$ into $H$'s world as decided facts — a *quote ledger* of threshold atoms "$a_n \ge k/n$" that $D$ decides to the published value — so recovering $a_n$ is a $\mathcal{C}_H$-cheap $O(n)$ lookup. This **produce-hard / read-cheap** gap *is* the thin channel, and is what "observable" means across processes: $H$ can form selections and conditionings on $A$'s verdict because the verdict is a cheap-to-read fact, not because $H$ could derive it. $H^+$ denotes $H$ augmented to read the ledger — the realistic human who has heard the AI. (For the future self there is no ledger: $H$ reads its own future prices directly.)

**Coherent, introspective.** $A$ is a coherent expectation operator (a *single belief state*, not a DDB frame — [[expert-conditions]]); optionally introspective, $E^A_n(\ulcorner E^A_n(X) \urcorner) \approx E^A_n(X)$, needed only for the conditional/fold results.

**The honest reading of "$E^A_n(X)$ estimates $X$".** Since $a_n$ targets the deferred *credence* $Y_n$, the quote equals the *truth* of $X$ only on the timely fragment $G$, where $Y_n$ has converged to the decided value. Off $G$, $a_n$ faithfully estimates $H$'s pre-resolution credence, which is not pinned to truth — the entire soundness story ([[target-soundness-and-safety]], [[manipulation-boundary-and-corrigibility]]) turns on this gap.

## The two settings

The wiki's results live in two distinct settings; each page declares its own. They are related but not interchangeable.

**Setting 1 — abstract single-expert.** One logical inductor $H \dashv \mathcal{C}_H$, plus *any* expert $E^\ast$ that is **observable** and **coherent** (optionally introspective) in the sense of [[expert-conditions]] — a sequence of estimates $H$ can cheaply read, forming a single coherent belief state. Nothing is assumed about how $E^\ast$ is produced; it need not be an inductor and need not observe $H$. The deference notions of [[deference-notions]] are stated here, and the §1–§2 results — [[mart-implies-value]], [[two-option-value-iff-total-trust]], [[total-trust-implies-value-telescoping]], [[total-trust-implies-mart]], [[amplifier-counterexample]], [[value-iff-mart]], [[expert-conditions]] — are theorems of this setting: conditional on the deference hypotheses, unconditional in everything else. Its two canonical instances are the **future self** $E^\ast = E^H_{f(n)}$ (where every hypothesis is an LI theorem — the free case) and the AI $A$ read through the thin channel.

**Setting 2 — coupled cross-process.** Two **mutually observable** logical inductors $H \dashv \mathcal{C}_H$ and $A \dashv \mathcal{C}_A$ with $\mathcal{C}_H \subseteq \mathcal{C}_A$ (canonically $\mathrm{P} \subsetneq \mathrm{EXP}$): $H$ (i.e. $H^+$) reads $A$'s quote ledger, and $A$ — strong enough to simulate $H$ to the lookahead — observes $H$'s prices. Here the tower is not a hypothesis to assume but a property to **force** or **refute**, and the schedule structure $e(n) < F(n) < \sigma(n)$ is active. This is the setting of the §4 negative results ([[no-forced-trust]], [[anti-inductive-settlement]], [[cost-circularity]], [[tower-death]]) and the §5 positive constructions ([[frozen-deliberation-construction]], [[faithful-acceleration-result]]). The **corrected faithful-acceleration work** additionally assumes **joint clearing**: both markets clear each day as one fixed point, so a trader's day-$n$ coefficients may depend continuously on the day-$\le n$ prices of *both* markets (same-round mutual visibility). This is a genuine extra hypothesis, not a convenience — under strict alternation one side sees only the other's day-$(n{-}1)$ output, and the one-day staleness is uncontrolled. See [[joint-clearing-and-trader-class]] and [[delay-and-visibility]].

**Relationship.** Setting 2 instantiates Setting 1: the coupled $A$, read through the ledger, is an observable coherent (indeed introspective) expert for $H^+$, so every Setting-1 theorem applies to the pair — this is how, e.g., the forced Total Trust of [[faithful-acceleration-result]] converts to Value via the Setting-1 two-option identity ([[two-option-value-iff-total-trust]]). What Setting 2 adds is the structure the *forcing* question needs: mutual observability, the complexity gap, the schedules, and (for the corrected FA results) joint clearing. Conversely, nothing in Setting 1 promises that its hypotheses (the tower, Total Trust) *hold* for any particular pair — that is precisely the subject of [[value-gap-arbitrage]] and everything downstream of it.

## Dictionary, and the Savage framing (deference-v6 §0.6)

| DDB (finite frame) | this wiki |
|---|---|
| novice $\pi$ | the human $E^H_n$ (resp. $E^{H^+}_n$ once it reads $A$) |
| the expert (frame $\mathcal{P}$) | observable belief sequence $E^\ast$: future self $E^H_{f(n)}$, or the AI $E^A_n$ |
| expert's estimate $E(X)$ (a random variable) | the LUV $\ulcorner E^\ast(X) \urcorner$ — e.g. $\ulcorner a_n \urcorner$ |
| Total Trust (inequality) | soft Total Trust; self-instance = Self-Trust `st` (4.12.4) |
| the deference equality | the tower `Mart` / `ccee`; forced for the self (`cee`), across processes only where [[frozen-deliberation-theorems]] / [[faithful-acceleration-result]] say |
| Value | "defer the decision to the expert" |

**The Savage framing.** Options are **random variables** $O^j : \text{worlds} \to [a,b]$, evaluated under uncertainty — not events conditioned on the act. A payoff's value is fixed by the world, never by which option is selected, so "the option the expert picks" is read off the world, not a self-referential bet. Where genuine self-reference re-enters (hard conditioning in Total Trust; deference-punishing payoffs like the quote diagonal of [[fa-scope-resolution]]), it is flagged there.

## Status

This page is **definitions only** — no theorems (deference-v6's "Lean (§0)" note: the real-sequence calculus for $\approx_n / \gtrsim_n$ is defined in the Lean modules, but §0 proves nothing). The imported tools `loe`, `expprovind`, and the self-trust family are taken from the LI paper as black boxes (status `LI` in deference-v6 Appendix B's vocabulary); see the label→theorem dictionary in [[conventions-and-status-labels]], including the erratum note for 4.8.15/4.8.16 ([[li-paper-erratum]]). Joint clearing is an **assumption** of the corrected FA work, not a theorem — its status and the open strict-alternation question live at [[joint-clearing-and-trader-class]].

## Related

- [[conventions-and-status-labels]] — status vocabulary and the label→theorem dictionary
- [[deference-notions]] — the deference hypotheses stated over this setting
- [[expert-conditions]] — what "observable, coherent, introspective" buy
- [[complexity-gap-hinge]] — why $\mathcal{C}_H \subsetneq \mathcal{C}_A$ is load-bearing
- [[joint-clearing-and-trader-class]] — Setting 2's extra hypothesis for the corrected FA results
- [[frozen-deliberation-construction]], [[faithful-acceleration-result]] — the two instantiations of the target $Y_n$

*Source: deference-v6 §0.2–0.4, §0.6 (`deference-in-logical-induction-v6.md`).*
