# Deference Between Epistemic Processes: The Tower, the Complexity Gap, and Forced Trust on the Timely Fragment (v5)

*An integrated note porting the main theorem of Dorst, Levinstein, Salow, Husic & Fitelson, "Deference Done Better" (DDB, 2021) into the logical-induction (LI) framework of Garrabrant et al. (2016), in light of Weatherson's "Deference and Infinite Frames" (2025) — and then carrying the resulting "tower" picture across the gap between **two distinct processes of different computational strength**, where it meets a sharp negative result and a matching positive one.*

> **About this version (v5).** v4 established the abstract theory — deference between epistemic processes is the **tower property**, and `Value ⟺ Mart` for any observable, coherent, introspective expert — and left the cross-process case (a novice trusting a *distinct, stronger* process, not its own future self) as the open §11 "real prize." v5 keeps v4 as the anchor but **interweaves** the cross-process results worked out since (Anson Berns's project, with Demski: the "Trust Between Logical Inductors" summary, the "Self-Referential Settlement Target" obstruction note, and the "Frozen-Deliberation Deference" construction), together with the human-endorsed framing of Abram's `li-deference.md`. The document is reorganized around a single spine: *deference is the tower; whether the tower can be **forced** is governed by whether the novice can arbitrage against the expert's market; this is free for the future self, impossible-in-general across processes, and forceable across processes exactly on the timely fragment.*
>
> Two global changes from v4, per Demski's instruction:
> - **Complexity-class generality throughout.** v4 fixed a single notion of "efficiently computable" (poly-time). v5 fixes a *pair* of trader classes $\mathcal{C}_H \subseteq \mathcal{C}_A$ (canonically $\mathrm{P} \subseteq \mathrm{EXP}$) — the **human/novice** reasons against $\mathcal{C}_H$, the **AI/expert** against $\mathcal{C}_A$. This is not relabeling: the gap $\mathcal{C}_H \subsetneq \mathcal{C}_A$ is exactly what makes cross-process forcing possible in one direction and impossible in the other (§3, §5).
> - **Notation $H$ / $A$ throughout.** The novice (truster) is $H$; the expert (trusted) is an observable belief sequence $E^\ast$ whose two canonical instances are $H_{f(n)}$ (the novice's own future self — the free case) and $A$ (a distinct stronger process — the prize). $H^+$ is $H$ augmented to read $A$'s published quotes (the realistic human who has heard the AI).
>
> v4 is preserved unchanged as a reference; a **v4→v5 map** is given at the end so its section anchors still resolve. This draft is to be machine-checked after the fact, so it does *not* carry inline `proved / sketched / interpretation` flags; §7 records what is *already* kernel-checked, and §8 records what is genuinely open or soft.

---

## Summary

A **novice** epistemic process $H$ should sometimes defer to an **expert** one $E^\ast$ — adopt the expert's verdict for decisions (**Value**) and its estimates for beliefs (**Trust**). DDB show that on **finite** probability frames these coincide, `Total Trust ⟺ Value`, by a long convex-geometry proof; Weatherson shows it breaks on infinite frames. Logical induction both **dissolves the worry** (the LI analog is short, and Weatherson's breaks are exactly LI's two standing scope conditions) and **says what deference is between two processes** — and then lets us ask, and largely answer, *when deference can be forced*.

1. **Deference is the tower property.** For a logical-inductor novice $H$ and an observable expert $E^\ast$, the single principle is iterated-expectation collapse toward the expert: $E^H_n(X) \approx_n E^H_n(\ulcorner E^\ast(X)\urcorner)$. Call it **Mart$(H\to E^\ast)$**. (§1)
2. **Value ⟺ Mart**, both directions cheap — the LI analog of DDB Theorem 2.2, for a general expert. Forward: apply the tower to the single LUV the expert picks. Backward: a two-option witness. (§1)
3. **What the expert must be is minimal**: *observable* and *coherent — a single belief state, not a frame*. The work-horse `loe`/`expprovind` are the **novice's**, free. The expert may be **modest** (incompletely self-knowing), which a finite frame cannot combine with coherence — so the home is an infinite, self-referential process, of which logical inductors are the concrete instances. (§1–§2)
4. **The forcing question is the real subject.** The tower is, in general, a *hypothesis about the (novice, expert) pair*. Whether it is *forced* turns on a no-Dutch-book / arbitrage argument: you can force the tower only against a market you can trade in. (§3)
5. **The future self is the free case** — $E^\ast = H_{f(n)}$ — where `Mart`, observability, coherence, introspection are all LI *theorems* (`cee`, `ccee`, `epr`/`er`), and it is the Blackwell-maximal observable expert. Self-trust is "deferring to the best expert you can see." (§3)
6. **The complexity gap is the hinge.** With $\mathcal{C}_H \subsetneq \mathcal{C}_A$, the expert can simulate-and-arbitrage the novice but not conversely; the novice reads the expert only through a **thin channel** ($\mathcal{C}_A$-hard to produce, $\mathcal{C}_H$-cheap to read). So cross-process forcing, if any, lives on the *expert's* side, forcing it to **predict the novice**. (§3)
7. **Across processes, negatively:** forced *agreement on undecidables* is impossible (No-Forced-Trust); and the most natural way to manufacture trust — settle contracts against the novice's own future credence ("self-trust through a mirror") — dies twice (an anti-inductive counterexample and a cost-circularity), which **derives** that any predictable settlement must be **blind** to the expert's own output ("predictable iff uninfluenced"). (§4)
8. **Across processes, positively:** with a blind, **held-out** target (a "sealed sibling" — the novice's own deliberation with the expert's current quote frozen out), the cross-process tower `Mart$(H^+\to A)$` **is forced** — faithfulness everywhere, and soundness exactly on the **timely fragment** $G$ (questions that resolve within the deliberation horizon), provably nowhere else. (§5)
9. **The meaning.** The expert is forced to *faithfully predict the human* everywhere, and to be *correct and calibrated* on the checkable fragment — but its relationship to truth off that fragment is unconstrained, and the audit trace cannot distinguish faithful prediction from steering. This draws a precise line for safe deference, and connects to the basin-of-attraction / corrigibility motivation and the open "legitimacy of feedback" program. (§6)

**Lean (Summary).** Every formal claim below is kernel-checked in `lean-deference/` (Lean 4.27.0 + Mathlib; `sorry`-free; all 67 results audited to `[propext, Classical.choice, Quot.sound]`): **`LeanDeference.lean`** (the tower / `Value ⟺ Mart` core, §1–§3), **`SelfReferentialTarget.lean`** (the obstruction, §4), and **`FrozenDeliberation.lean`** (the §3.3 hinge + the §5 forcing suite). Each section ends with a **Lean (§N)** note quoting the exact statements proved for it, so the LaTeX and the formalization can be eyeballed side by side. Quoting convention: universe/instance binders (`{W J : Type*}`, `[Fintype W]`, …) are elided as `...`; every semantic hypothesis and the conclusion is verbatim. The LI paper's theorems (the criterion, `loe`, `expprovind`, Non-Dogmatism, per-member convergence) and the LUV/market machinery are the *trusted boundary* (§7) — they enter only as named hypotheses over the real-sequence abstractions of §0.

---

## 0. Setting and notation

### 0.1 Motivation, and why logical induction is the model

The background aim (Demski, `li-deference.md`) is to formalize **basin-of-attraction** arguments for alignment: in what ways can an AI be "good enough" to participate safely in recursive self-improvement (constitutional AI, deliberative alignment, scalable oversight)? What must the AI be *correct* about, what may it be *wrong* about, and when are errors *self-correcting* over the course of improvement? Deference is the entry point because DDB-style results characterize alignment through an iff linking **epistemic** trust to **instrumental** trust.

**Logical induction is used to model both the human and the AI**, because it is a good model of beliefs that *improve over time*. On the AI side it resembles a progression of model versions, each improving on the last. On the human side it models scientific-philosophical progress: prices (and, at finer grain, trades) play **prediction** and **evidence** roles at once — a price today is a prediction about future prices, but evidence about the quality of past prices. This captures **reflective equilibrium**: intuitions judge theories, but doing the work refines the intuitions. Empirical observation is the special case where prices go to $0$ or $1$ and freeze (evidence only, no longer malleable predictions). The governing question becomes: *when can one logical inductor trust another, and what training process makes one inductor adequately mimic another's scientific-philosophical process?* (Note that when one inductor is the target of another, most sentences will not have $0/1$ values — feedback is itself uncertain.)

A pleasant surprise drives the simplicity of §1: although LI is "modest" in a strong sense (perfect self-knowledge for an inductor is *contradictory*), it is "immodest enough" that the LI analogues of Reflection, Trust, Total Trust, Tower, and Value collapse into one — because the analogue of each property is **asymptotic** (rationality is learned, not imposed at all times) and an inductor **learns about itself** over time (so asymptotically it has self-knowledge). This is the immodest corner of DDB, reached for a genuinely modest reasoner.

### 0.2 The shared world

Fix a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$, a consistent theory $\Gamma$ able to represent computable functions (e.g. `PA`), and a $\Gamma$-complete **computable deductive process** $D = (D^1 \subseteq D^2 \subseteq \cdots)$ revealing $\Gamma$'s theorems over time. A sentence is **decidable** if $D$ eventually **decides** it; its decided value is its **truth value** — the only notion of truth here. (I use *decide* for what $D$ does to sentences, and reserve *pay out* for what a contract does at settlement, §0.4 — so "settled" never has to do double duty.) Two boundaries matter, and the second is operative throughout the cross-process half:

- **decidable vs. undecidable**: whether $D$ ever decides the sentence;
- within the decidable, **resolves *in time* vs. not**: whether $D$ decides it by the relevant **lookahead** $F(n)$ (the deliberation budget of §0.4).

The undecidable fragment — where forcing provably cannot reach — doubles as a candidate formal model of genuinely **open, never-settled questions**, which is part of why the *location* of the forcing boundary is treated as the content rather than a technicality.

**The two reasoners and their classes.** Fix complexity classes $\mathcal{C}_H \subseteq \mathcal{C}_A$, each closed under polynomial overhead and **computably enumerable** (the class's traders can be algorithmically listed — the hook the LI existence theorem dovetails against to build an inductor inexploitable by all of them; immediate for $\mathrm{P}$ and $\mathrm{EXP}$ by clocking); canonically $\mathrm{P} \subseteq \mathrm{EXP}$. The **human** $H$ is a logical inductor against trader class $\mathcal{C}_H$; the **AI** $A$, when distinct, is an inductor against $\mathcal{C}_A$. (When a statement is really about a *general* expert rather than the AI specifically, I'll fall back on *novice* for $H$ and *expert* for the thing it defers to — the abstract theory of §1–§2 is one such place.) The asymmetry $\mathcal{C}_H \subsetneq \mathcal{C}_A$ is load-bearing (§3): the AI is powerful enough to simulate the human's deliberation out to the lookahead, but not conversely.

### 0.3 The human, and its free tools

$H = (H_n)_{n\ge1}$ is a logical inductor over $\Gamma$: a computable sequence of belief states with $H_n(\varphi)\in[0,1]$ the day-$n$ price (credence) of $\varphi$, satisfying the **logical-induction criterion** — *no $\mathcal{C}_H$-trader exploits the market* (a computational no-Dutch-book, the source of every property below).

- **LUV (logically uncertain variable).** A formula $X$ (one free variable) that $\Gamma$ proves names a unique real; an **$[a,b]$-LUV** if $\Gamma$ proves it lies in a known rational interval $[a,b]$. LUVs are bounded random variables; written uppercase $X, Y, \dots$ (The LI paper normalizes everything to $[0,1]$; carrying a general $[a,b]$ lets bets, thresholds, and offsets keep their natural scale instead of being rescaled by hand — at the cost of citing the paper's results in their bounded form, below. *Caveat:* the lower bound $a$ is unrelated to the AI's quote $a_n$ of §0.4 — distinct objects, distinguished by the subscript.) (LI Def. 4.8.1.)
- **Worlds and completions.** A *world* $W$ assigns truth values to all sentences; the **consistent completions** $\mathrm{PC}(\Gamma)$ are those consistent with $\Gamma$. The limit $H_\infty$ is a coherent measure on $\mathrm{PC}(\Gamma)$ (LI Limit Coherence 4.1.1), and each LUV $X$ is a random variable on it with value $W(X)\in[a,b]$ in world $W$. "$W(D)\ge0$ in every consistent world" *is* "$\Gamma \vdash D\ge0$."
- **LUV-combination and *bounded*.** A finite affine combination $D = c + \alpha_1 X_1 + \cdots + \alpha_k X_k$ of LUVs with real coefficients; $W(D)=c+\sum_i \alpha_i W(X_i)$. With general $[a,b]$-LUVs the quantities the theorems actually compare — *offsets* like $X-Y$, $X-t$ — are themselves just LUV-combinations valued in some interval, so no normalization step intervenes. **Bounded** = uniform $\sum|\alpha_i|$ across $n$ (the uniform-integrability stand-in). (LI Def. 4.8.9.)
- **Expectation.** $E^H_n(X)$ is $H$'s day-$n$ estimate of the LUV $X$ — the LI paper's discretized $\int H_n(X>x)\,dx$ (discretization finer with $n$), valued in $[a,b]$ for an $[a,b]$-LUV (the paper's $[0,1]$ definition lifted by affine rescaling). (LI Def. 4.8.2.) Write $E^H_n$, or $E_n$ when unambiguous.
- **Corner quotes.** $\ulcorner e\urcorner$ is the syntactic object (Gödel code) $\Gamma$ reasons about, vs. the value $e$ it denotes. So $E^A_n(X)$ is a *number* but $\ulcorner E^A_n(X)\urcorner$ is *the LUV naming it*, and $E^H_n(\ulcorner E^A_n(X)\urcorner)$ — "the human's estimate of the AI's estimate" — is type-correct.
- **Asymptotics.** $x_n \approx_n y_n :\Leftrightarrow \lim_n (x_n-y_n)=0$; $x_n \gtrsim_n y_n :\Leftrightarrow \liminf_n (x_n-y_n)\ge0$. Everything is up to vanishing error ("in a timely manner").
- **$\mathcal{C}_H$-computable / market-generable.** A sequence is *$\mathcal{C}_H$-computable* if a $\mathcal{C}_H$ machine outputs term $n$; a real sequence is *$\mathcal{C}_H$-market-generable* if computed by a $\mathcal{C}_H$ **expressible feature** of $H$'s prices (built from prices, rationals, $+,\times,\max$, safe reciprocation) — hence **continuous** in the prices. Continuity lets the market clear (Brouwer) and defuses self-reference; a *hard* `argmax` indicator is discontinuous, hence not a legal weight. (We still abbreviate "e.c." when the class is clear from context; for the novice it always means $\mathcal{C}_H$.)

**The novice's two free theorems** (used unconditionally, each a consequence of the criterion, *independent of any expert*):

> **Linearity** (Thm 4.8.4, `loe`, bounded form). For bounded $\mathcal{C}_H$-market-generable rationals $(\alpha_n),(\beta_n)$ and e.c. $[a,b]$-LUVs with $\Gamma\vdash Z_n=\alpha_nX_n+\beta_nY_n$: $\;\alpha_nE^H_n(X_n)+\beta_nE^H_n(Y_n)\approx_n E^H_n(Z_n)$. (Coefficients are written $\alpha,\beta$, not $a,b$, to keep clear of the LUV bounds $[a,b]$ and the AI's quote $a_n$. The paper proves the $[0,1]$ case; the bounded case is its affine rescaling.)

> **Expectation Provability Induction** (Thm 4.8.10, `expprovind`, bounded form). If a bounded LUV-combination $D_n$ is provably nonnegative — $\Gamma\vdash D_n\ge0$, uniformly in $n$ — then $E^H_n(D_n)\gtrsim_n 0$ (and "$=$" gives "$\approx_n$"). *A bound true under every resolution of the open questions is eventually honored by the day-$n$ estimate.* This is what carries a provable (in)equality **through** $E^H_n$. (Again the paper's $[0,1]$ statement, rescaled.)

The human's *self-trust* theorems — `cee`, `ccee`, `epr`/`er`, `st` — are also LI theorems, but they describe $H$'s relation to its **own future self**; in the general setting they appear only as the §3.2 instantiation of the deference hypotheses, not as free tools.

### 0.4 The AI, the schedules, and the deference relation

The thing $H$ defers to is an **expert** — an observable sequence of estimates, instantiated either as $H$'s own future self $E^H_{f(n)}$ (§3.2) or as a distinct, stronger AI $A$. This subsection builds the AI case in full, because that is where the *timing* lives — and the timing is exactly what the old version of this section swept under the word "observable." (Statements that hold for *any* observable coherent expert — most of §1–§2 — I'll phrase generically; the AI is the working instance.)

**What the AI is an expert *about* — the deferred target.** $A$ does **not** forecast the truth of the question $P^{(n)}$ directly. It forecasts where $H$'s *own* deliberation would get to, given a budget: run (a held-out copy of) $H$ on $P^{(n)}$ out to a **lookahead** $F(n)$ — superpolynomial in $n$, canonically $2^n$ — and read off the credence

$$ Y_n \ :=\ \big(\text{$H$'s deliberation on }P^{(n)}\text{, run to stage }F(n)\big). $$

$Y_n$ is the **deferred credence**: the considered judgment $H$ would reach with $F(n)$ stages of thought. (*Which* held-out copy of $H$, and why it must be sealed off from $A$'s own output, is the substance of §4–§5; for setup, $Y_n$ is just "$H$'s lookahead-$F(n)$ verdict.") The object $A$ is scored against is a contract $C_n$ that **pays out** $Y_n$.

**The three schedules** (monotone, $\mathcal{C}_H$-computable, ordered $n \le e(n) < F(n) < \sigma(n)$):
- **publication $e(n)$** — the stage at which $A$'s forecast for question $n$ is posted into $H$'s world (below);
- **lookahead $F(n)$** — the deliberation budget defining the deferred target $Y_n$ (and, from §0.2, the cutoff for "resolves in time"); its self-case analogue is the deferral $f(n)$ of the future self;
- **payout $\sigma(n)$** — the stage at which $C_n$ pays out against $Y_n$.

**The AI's forecast.** $A$'s published quote for question $n$ is its day-$n$ estimate of the payout contract,

$$ a_n \ :=\ E^A_n(C_n)\ \in\ \mathbb{Q}\cap[0,1], $$

i.e. $A$'s prediction of the deferred credence $Y_n$. Note the two clocks: the day index $n$ is *when $A$ forms the forecast*; the publication stage $e(n)$ is *when $H$ may read it*. Collapsing those two into one "$E^A(X)$" is precisely the imprecision the old §0.4 hid — keeping them apart is what makes "observable" a real condition rather than a gesture.

**Observable (what the deference relation actually rests on).** $H$ cannot *recompute* $a_n$: producing it means simulating $H$'s own deliberation out to the lookahead, a $\mathcal{C}_A$-hard job outside $\mathcal{C}_H$. What $H$ can do is **read** it. At stage $e(n)$, $A$ publishes $a_n$ into $H$'s world as **decided facts** — a *quote ledger* of threshold atoms "$a_n \ge k/n$" that $D$ decides to the published value — so that recovering $a_n$ is an $O(n)$, $\mathcal{C}_H$-cheap lookup. This **produce-hard / read-cheap** gap *is* the **thin channel**, and it is exactly what observability means across processes: $H$ can form selections and conditionings on $A$'s verdict — so the deference relation can even be *stated* — precisely because the verdict is a cheap-to-read fact, not because $H$ could derive it. (For the future self there is no ledger and no publication stage: $H$ reads its own future prices directly, §3.2.)

**Coherent — a single state.** $A$ is a coherent expectation operator (linear, $\Gamma$-representable). Hence $\arg\max_j E^A_n(O^j)$ is well-defined and the **selection identity** $E^A_n(O^{j^\ast})=\max_j E^A_n(O^j)$ is $\Gamma$-provable. Equivalently $A$ is a *single belief state* (one inductor, a calibrated predictor) — **not** a DDB-style frame (§2.1).

**Introspective (optional).** $E^A_n(\ulcorner E^A_n(X)\urcorner)\approx E^A_n(X)$: $A$ knows its own estimates. Needed only for the conditional/folding results (§1.5).

> **Mart$(H\to A)$** (the human *towers over* the AI). For all e.c. LUVs $X$ — with $a_n$ the published forecast when $X=P^{(n)}$: $\;E^H_n(X)\approx_n E^H_n(\ulcorner E^A_n(X)\urcorner)$ $\big(= E^H_n(\ulcorner a_n\urcorner)\big)$. Its **conditional** form, **ccee$(H\to A)$**, for observable weights $w\in[0,1]$: $\;E^H_n(X\cdot w)\approx_n E^H_n(\ulcorner E^A_n(X)\cdot w\urcorner)$.

**The honest reading of "$E^A_n(X)$ estimates $X$."** Because $a_n$ targets the *deferred* credence $Y_n$, the AI's forecast equals the truth of $X$ **only on the timely fragment $G$** — the questions $D$ decides by the lookahead $F(n)$, where $Y_n$ has converged to the truth value (§5). Off $G$, $a_n$ faithfully estimates $H$'s *pre-resolution* credence $Y_n$, which is not pinned to truth. So "the AI's estimate of $X$" is exact exactly where it matters and deliberately silent elsewhere; the whole soundness story (§5–§6) turns on this gap.

**The two canonical instances.**
1. **Future self** ($\mathcal{C}_H=\mathcal{C}_A$, more time): the expert is $E^H_{f(n)}$, $f(n)>n$. No ledger, no payout contract — observability, coherence, introspection, and the tower itself are all LI *theorems* (`cee`, `ccee`, `epr`/`er`): the tower is **free**. This is §3.2.
2. **A distinct stronger AI** ($\mathcal{C}_H\subsetneq\mathcal{C}_A$): the expert is $A$, read through the thin channel; coherent/introspective because $A$ is an inductor — but `Mart$(H\to A)$` is now a *genuine claim about the pair*, the open §3.4 problem, **forced on $G$** in §5.

### 0.5 Deference Done Better, in a page

A **probability frame** $\langle W,\mathcal{P}\rangle$ is a finite world-set $W$ with a credence $P_w$ at each world ("the expert's credence if the actual world is $w$"). A novice distribution $\pi$ defers. $E_w(X):=\sum_v P_w(v)X(v)$; the random variable $E(X):w\mapsto E_w(X)$ is "the expert's estimate, whatever it is." The expert is **immodest** at $w$ if $P_w(P=P_w)=1$, **modest** otherwise. Three principles:

- **Reflection** $\pi(\cdot\mid P=\rho)=\rho$ — adopt the expert's exact credence. *Too strong*: incompatible with modesty.
- **Total Trust** $E_\pi(X\mid E(X)\ge t)\ge t$ — conditional on the expert's estimate being high, hold a high estimate. (An inequality.)
- **Value** — for every menu, you'd rather let the expert pick than commit to a fixed option.

**DDB Theorem 2.2:** on a finite frame, **Total Trust ⟺ Value**; for *immodest* experts both coincide with Reflection, and **modesty separates them** (the *anti-expert* frame $\pi=(\tfrac12,\tfrac12)$, $P_a=(.2,.8)$, $P_b=(.8,.2)$ satisfies the marginal martingale $\pi P=\pi$ yet fails Value). The hard direction `Total Trust ⟹ Value` is a convex-geometry reconstruction (the authors call the proof "excruciating"); §2.1 says why LI skips it. DDB further assume **finiteness** — the novice has narrowed the expert's beliefs to a finite list, an implausible model of belief-uncertainty (one is liable to think a credence is any real in a range, not one of finitely many). **Weatherson (2025)** breaks Thm 2.2 both ways on infinite frames (**Coin**, **Bentham**); §2.3 maps both onto LI's scope conditions.

### 0.6 Dictionary, and the Savage framing

| DDB (finite frame) | v4 ($E_n$ novice, $E^\ast$ expert) | v5 (human $H$; expert is $E^H_{f(n)}$ or the AI $A$) |
|---|---|---|
| novice $\pi$ | $E_n$ | the human $E^H_n$ (resp. $E^{H^+}_n$ once it has read $A$) |
| the expert (frame $\mathcal{P}$) | observable belief sequence $E^\ast$ | future self $E^H_{f(n)}$, or distinct AI $E^A_n$ |
| expert's estimate $E(X)$ | the LUV $\ulcorner E^\ast(X)\urcorner$ | $\ulcorner E^A_n(X)\urcorner$ (i.e. $\ulcorner a_n\urcorner$), or $\ulcorner E^H_{f(n)}(X)\urcorner$ |
| Total Trust (inequality) | consequence of `ccee` via the threshold bound | same; self-instance = **Self-Trust** `st` (4.12.4) |
| the deference equality | the tower `Mart` / `ccee` | same; **forced** for the self (`cee`), and for $A$ only on $G$ (§5) |
| Value | "defer the decision to the expert" | same |

**The Savage framing (self-reference set aside).** Options are **random variables** $O^j:\text{worlds}\to[0,1]$, evaluated under uncertainty — not events conditioned on the act. A payoff's value is fixed by the world, never by which option is selected; so $O^{\arg\max}$ is read off the world, not a self-referential bet. Where genuine self-reference re-enters (Total Trust's hard conditioning; deference-punishing payoffs) it is flagged (§2.2, §6.6).

**Lean (§0).** The real-sequence calculus that models `≈ₙ` / `≳ₙ` (defined identically in `DeferenceAsymp`, `SelfRefTarget`, and `Frozen`):

```lean
def Approx  (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)        -- a ≈ₙ b
def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε    -- b ≳ₙ a
```

No theorems here — §0 is definitions and the trusted boundary. `E^H_n`, LUVs, and the market are not modeled; they surface below only through named hypotheses phrased over `Approx`/`AsympLE`.

---

## 1. Deference between processes is the tower property

Fix the novice $H$, an expert $E^\ast$, and an e.c. sequence of **menus** $\mathcal{O}_n=\{O^1_n,\dots,O^k_n\}$, each a bounded $[a,b]$-LUV ("bet"), exogenous. Write
$$
m^j_n := E^\ast(O^j_n),\qquad M_n := \max_j m^j_n,\qquad j^\ast(n)\in\arg\max_j m^j_n
$$
(least index; any *computable* tie-break). The **followed strategy** — "let the expert decide" — has realized payoff the single LUV
$$
\boxed{\ \widehat S_n := O^{\,j^\ast(n)}_n\ }
$$
— the option the expert picks, evaluated at the world that obtains. Three observations:

- $\widehat S_n$ is **itself an e.c. LUV** (its formula references the menu, the observable $E^\ast$, the tie-break), so `argmax` is never needed as a *weight* — the discontinuity obstruction does not arise.
- **(F1)** $E^\ast(\widehat S_n)=M_n$, **provably and tie-break-independently** — the expert's estimate of the option it selected is the maximal estimate. This is **coherence** of $E^\ast$ in action.
- **(F2)** $M_n\ge m^i_n$ for each $i$ (a max dominates each entry).

**The principle and its faces.**

| face | statement | name |
|---|---|---|
| epistemic, unconditional (equality) | $E^H_n(X)\approx_n E^H_n(\ulcorner E^\ast(X)\urcorner)$, all $X$ | the tower / `Mart`$(H\to E^\ast)$ |
| epistemic, conditional (equality) | $E^H_n(X\cdot w)\approx_n E^H_n(\ulcorner E^\ast(X)\,w\urcorner)$, observable $w$ | conditional tower / `ccee`$(H\to E^\ast)$ |
| epistemic, inequality | $E^H_n(X\mid E^\ast(X)\ge t)\gtrsim_n t$ | **Total Trust** (a *consequence*, §1.6) |
| instrumental | $E^H_n(\widehat S_n)\gtrsim_n E^H_n(O^i_n)$, all menus | **Value** |

### 1.1 Mart ⟹ Value

**If the novice Marts the expert (observable + coherent), it Values it:** $E^H_n(\widehat S_n)\gtrsim_n E^H_n(O^i_n)$.
$$
\begin{aligned}
E^H_n(\widehat S_n)
&\approx_n\ E^H_n\big(\ulcorner E^\ast(\widehat S_n)\urcorner\big)
&&[\text{tower on }\widehat S_n:\ \textbf{Mart}]\\
&\approx_n\ E^H_n\big(\ulcorner M_n\urcorner\big)
&&[\text{F1: }\Gamma\vdash E^\ast(\widehat S_n)=M_n,\ \text{carried through }E^H_n\text{ by }\texttt{expprovind}]\\
&\gtrsim_n\ E^H_n\big(\ulcorner m^i_n\urcorner\big)
&&[\text{F2: }M_n\ge m^i_n,\ \text{via }\texttt{expprovind}]\\
&\approx_n\ E^H_n(O^i_n)
&&[\text{tower on }O^i_n:\ \textbf{Mart}].
\end{aligned}
$$
Two tower steps (the deference hypothesis, lines 1 and 4) and two provability-induction steps (the **novice's** `expprovind`, lines 2–3). **No conditional martingale, no softmax, no $\delta\log k$, no bound on $k$, no tie-breaking.** Lines 2–3 each do two things: the (in)equality is *provable* (it holds in every consistent world, from coherence + the definition of argmax), but it sits *inside* $E^H_n(\ulcorner\cdot\urcorner)$, and carrying a provable identity through $E^H_n$ is exactly `expprovind` (with `loe` splitting the difference). So the LI inputs are precisely **two**: the deference hypothesis `Mart` and the novice's own `expprovind`. This is the **law of total expectation in LI dress, across two processes**: "follow the expert" is the variable $O^{j^\ast}$; the expert knows what it chose, so its estimate of that choice is the max $M$; the tower carries $M$ back to the present, where it dominates any single option, and carries that out to the option. Ties are irrelevant because F1 is tie-break-free.

### 1.2 Value ⟹ Total Trust (the witness, exact)

DDB's *easy* direction ports with **no tower** — only the novice's linearity and the expert's coherence. Fix a bet $X$ and threshold $s$; offer the two-option menu $\{X,\ \text{const }s\}$. The expert takes $X$ exactly where $E^\ast(X)\ge s$:
$$
\widehat S_{\mathrm{wit}}=X\cdot\mathbb{1}[E^\ast(X)\ge s]+s\cdot\mathbb{1}[E^\ast(X)<s].
$$
Apply $E_\pi$ (read it as $E^H_n$), split the baseline "always $s$" across the same two regions; the low-region terms cancel, leaving
$$
\boxed{\ E_\pi(\widehat S_{\mathrm{wit}})-s\,E_\pi(1)=E_\pi\big((X-s)\,\mathbb{1}[E^\ast(X)\ge s]\big)\ }
$$
Exact, from linearity alone. Value on this menu says $E_\pi(\widehat S_{\mathrm{wit}})\ge s\,E_\pi(1)$, so the boxed quantity is $\ge0$; expanding and dividing by the mass $P_\pi(E^\ast(X)\ge s)$ gives $E_\pi(X\mid E^\ast(X)\ge s)\ge s$ — **Total Trust at $s$**. Because the boxed identity is an *equality*, the arrow runs both ways: "Value on the $\{X,s\}$ witness" and "Total Trust at $s$" are the *same statement*, per $(X,s)$, with no slack. Over all $X,s$ (and the lower cut $E_\pi(X\mid E^\ast(X)\le s)\le s$):
$$
\textbf{Value (all witness menus)}\iff\textbf{Total Trust (all }X,s,\ \text{both cuts).}
$$

### 1.3 The reversal of difficulty

| | `Value ⟹ Total Trust` | `Total Trust ⟹ Value` |
|---|---|---|
| **DDB (finite-frame expert)** | easy (Lemma 7.1 witness) | **hard** (convex-hull reconstruction) |
| **LI (observable coherent expert)** | easy (§1.2 witness) | **easy** (§1.1, two towers) |

The direction DDB finds expensive is the one LI makes free. §2.1 says why — it is about *what kind of object the expert is.*

### 1.4 What remains: the tower itself

§1.1 gives `Mart ⟹ Value`; §1.2 gives `Value ⟺ Total Trust`. The full iff `Value ⟺ Mart` needs one more link — `Total Trust ⟺ the tower` — which is §1.6: trivial one way, and the genuinely hard half the other. Net: **`Value ⟺ Mart`** for any observable coherent expert. The forward arrow *assumes* the tower and spends it; the converse *manufactures* it from Value, using only linearity and coherence.

### 1.5 The universal tower contains its conditional form (the fold)

By **the tower** we always mean the *universal* one — $E^H_n(X)\approx_n E^H_n(\ulcorner E^\ast(X)\urcorner)$ for **every** e.c. LUV $X$ — which already contains its conditional form, because any observable weight folds into the LUV: for observable $w\in[0,1]$, the product $X\cdot w$ is itself an e.c. LUV, and since the expert knows $w$ (introspection; for the future self, `epr`/`er`), coherence gives $E^\ast(X\cdot w)=w\,E^\ast(X)$, hence $E^H_n(X\cdot w)\approx_n E^H_n(\ulcorner E^\ast(X)\cdot w\urcorner)$. Setting $w\equiv1$ recovers the bare tower. So "tower on every LUV" and "tower with every observable weight" are one principle (this is `ccee`).

A DDB reader expects a gap: surely the *marginal* identity $E_\pi(E^\ast(X))=E_\pi(X)$ (in frame terms $\pi P=\pi$, which the anti-expert frame satisfies yet fails Value) is far weaker than Total Trust. It is — but that marginal identity is just the tower applied **to the bare options only**, a frame artifact with no privileged status in LI, since Value is universal and there is no canonical bare-options set to single out. The watershed: a DDB *frame* conditions on the expert's **identity** $[P=\rho]$, which a modest frame does not know, so the fold fails; a coherent $E^\ast$ conditions on its own **estimate** $E^\ast(X)$, which it does know, so the fold goes through. *Knowing the conditioning quantity* is the whole difference.

### 1.6 Total Trust and the soft⇒hard squeeze

**Total Trust** is the inequality face, one bound past the tower equality. In the LI continuum the conditioning must be *soft*: a hard $\mathbb{1}[E^\ast(X)>t]$ is discontinuous (illegal as a weight) and liar-prone, so use the continuous threshold indicator
$$
w_{t,\delta}=\operatorname{Ind}_\delta(E^\ast(X)>t),\qquad
\operatorname{Ind}_\delta(y>t)=\begin{cases}0 & y\le t\\ (y-t)/\delta & t<y\le t+\delta\\ 1 & y>t+\delta.\end{cases}
$$
Two ingredients — the tower at this weight (the fold), and the threshold bound ($E^\ast(X)\cdot w\ge t\cdot w$ provably, carried through by `expprovind`) — chain to
$$
\boxed{\ E^H_n(X\,w_{t,\delta})\gtrsim_n t\,E^H_n(w_{t,\delta})\ }\ \xrightarrow{\ \delta\to0\ }\ E^H_n(X\mid E^\ast(X)>t)\gtrsim_n t,
$$
soft Total Trust at $t$. The three epistemic faces: tower ($w\equiv1$) $\iff$ tower-with-weight $\implies$ Total Trust; the first $\iff$ is the fold, the last $\implies$ the threshold bound.

**The squeeze — Total Trust back up to the tower — is the hard half.** The last arrow runs one way per instance. Does the *family* of Total-Trust inequalities recover the equality? Write $e:=E^\ast(X)$, $g(e_0):=E_\pi(X\mid e=e_0)$; the tower says $g=\mathrm{id}$ a.e. A single bet $X$ gives only the *parallel* cuts $\{e>t\}$, which do **not** pin $g=\mathrm{id}$: with $\mu=\mathrm{Unif}[0,1]$, the **amplifier**
$$
g(e_0)=(1+2c)e_0-c\quad(c>0),\qquad g(\tfrac12)=\tfrac12,\ \text{slope }1+2c>1
$$
passes every threshold-trust inequality, both cuts, for every $t$ and $c\ge0$ — a novice who systematically *overstates the expert's confidence* yet never matches it. What rules the impostor out is **boundedness biting at the extremes**: $g(0)=-c<0$, $g(1)=1+c>1$, so if the expert's estimate actually reaches $0$ and $1$, $c=0$ is forced; if $e$ stays inside $(0,1)$, the amplifier survives. Pinning $g=\mathrm{id}$ in general needs Total Trust on *all* bets (the non-parallel cuts that probe *within* each $E^\ast(X)$-layer) — DDB's biconvex / convex-hull characterization, by hyperplane separation plus boundedness. **This is why the squeeze stays prose**: a genuine convex-geometry theorem, not a one-line limit. The continuum costs you here: finite-exact, the witness made `Value ⟺ Total Trust` two-way (§1.2); the soft indicator smears each cut, so soft Total Trust is only $\gtrsim$ at width $\delta$, and sharpening sends $\delta\to0$ inside $E^H_n$ exactly where $\mathbb{1}[E^\ast(X)>t]$ is the liar-prone event the inductor refuses to evaluate sharply (the refusal that *protects* it from paradox).

**It is the tower, not Reflection.** What the squeeze pins is $E_\pi(X\mid E^\ast(X))=E^\ast(X)$ — the novice reflects the expert's *estimate of $X$*. This is strictly weaker than DDB-**Reflection** $\pi(\cdot\mid P=\rho)=\rho$, which conditions on the expert's **entire identity** (Reflection ⟹ tower, never the converse). The soft indicator only ramps over estimate-thresholds, never over identity, so Total Trust tops out at the tower **and cannot reach Reflection** — exactly right, since Reflection collapses to inconsistency for a modest expert (§2.2). The ceiling is a feature.

**Lean (§1).** `LeanDeference.lean`, with the §1.6 amplifier in `FrozenDeliberation.lean`:

```lean
-- §1.1  Mart ⟹ Value (argmax route, asymptotic; tie-break-free)
theorem DeferenceArgmax.value_argmax_asymptotic (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) : AsympLE Eoi ES

-- §1.1  finite-exact: conditional-martingale ⇒ Value (defects = 0 + argmax dominance)
theorem Deference.value_of_CM ... (hπ : ∀ w, 0 ≤ π w)
    (hCM : (∑ w, π w * (∑ j, α j w * (O j w - ∑ v, P w v * O j v))) = 0)
    (hUM : (∑ w, π w * (∑ v, P w v * O i v)) - (∑ w, π w * O i w) = 0)
    (hmax : ∀ w, (∑ v, P w v * O i v) ≤ ∑ j, α j w * (∑ v, P w v * O j v)) :
    0 ≤ (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w)

-- §1.2  Value ⟺ Total Trust (finite-exact witness; both arrows)
theorem DeferenceConverse.value_iff_totalTrust ... (π : W → ℝ) (P : W → W → ℝ) :
    (∀ (X : W → ℝ) (s : ℝ), s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s))
      ↔ (∀ (X : W → ℝ) (s : ℝ), s * (∑ w, (if s ≤ (∑ v, P w v * X v) then π w else 0))
            ≤ ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * X w else 0))

-- §1.2  …and its asymptotic (soft/LI) form
theorem DeferenceConverseAsymp.value_iff_totalTrust_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : Approx ESsoft (fun n => Exw n + s * E1 n - s * Ew n)) :
    AsympLE (fun n => s * E1 n) ESsoft ↔ AsympLE (fun n => s * Ew n) Exw

-- §1.5  the fold: ccee collapses to cee under an expert-known weight g
theorem DeferenceFold.fold_sum ... (hknow : ∀ w v, P w v ≠ 0 → g v = g w) :
    (∑ w, π w * (∑ v, P w v * (X v * g v))) = ∑ w, π w * (g w * (∑ v, P w v * X v))

-- §1.6  the amplifier passes both threshold-trust cuts yet ≠ id; boundedness at 0 forces id
theorem Frozen.amp_upper_cut_nonneg (c t : ℝ) (hc : 0 ≤ c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ ((1 + 2*c)*(1 - t^2)/2 - c*(1-t)) - t*(1-t)
theorem Frozen.amp_boundedness_forces_id (c : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ amp c 0) : c = 0
```

The two tower steps and the `loe`/`expprovind` carries are the named `Approx`/`AsympLE` hypotheses; the proved content is their composition (`value_argmax_asymptotic`) and the finite-exact algebra (`decomposition`, `value_of_CM`, `witness_identity`). `Total Trust ⟹ the full tower equality` stays prose — `amp_upper_cut_nonneg` / `amp_lower_cut_nonpos` are the precise obstruction (a non-identity that passes every parallel cut), and `amp_boundedness_forces_id` is what the non-parallel cuts add.

---

## 2. What the expert must be, and why logical induction is the home

### 2.1 A coherent single state is cheap; a frame is dear

The §1.3 asymmetry has one root cause — *what kind of object the expert is.*

**A DDB expert is an information frame.** A credence per world $P_w$ ⇒ a *world-dependent* recommendation $S_w$, so the realized return is the **diagonal** $\widehat S(w)=S_w(w)$, scored by $E_a(\widehat S)=\sum_v P_a(v)S_v(v)$ — which is **not** the max (in the anti-expert frame $E_a(\widehat S)=-1$ while $M(a)=.6$). Bridging the $\pi$-average of the diagonal to the $\pi$-average of the row-wise maxima is DDB's *hard* direction: a convex reconstruction plus Blackwell–Geanakoplos value-of-information.

**A coherent $E^\ast$ is a single belief state.** One set of estimates $\{m^j\}$ ⇒ one argmax ⇒ the followed strategy is the *single option* $O^{j^\ast}$, and $E^\ast(\widehat S)=M$ by definition (F1). No world-dependent strategy, no diagonal to reconstruct. The novice's uncertainty about $E^\ast$ is **logical** (about a definite quantity it has not finished computing), not **which-world** uncertainty about which $P_w$ holds. The tower is exactly the bridge DDB builds by hand — handed over by no-Dutch-book.

| | DDB | LI (general expert) |
|---|---|---|
| the expert is… | a frame (a credence per world) | a single coherent belief state |
| the recommendation is… | world-dependent $S_w$ | one option $O^{j^\ast}$ |
| $E_{\text{expert}}(\text{followed strategy})$ | not the max (diagonal mixes) | the max, by F1 |
| diagonal→row-wise bridge | reconstructed (convex hull) | free (the tower) |

So the natural cross-process experts are **other logical inductors** (or any coherent calibrated estimator): single states, so deference to them is cheap; a frame is the expensive object.

### 2.2 Modest but coherent — and why the home is an infinite process

Is a coherent observable expert simply *immodest*, collapsing to the easy DDB corner? No — and the surviving modesty is the point.

**The modesty that survives is incomplete self-knowledge, not identity-uncertainty.** A coherent inductor-expert knows its own estimates only *approximately and increasingly* (introspection), never to *paradoxical* completeness — completeness would let the diagonal lemma build a liar it cannot settle. So $E^\ast$ knows enough to value its own choices (F1, about exogenous options, needs only definite estimates) yet cannot host a self-referential predicate about its own beliefs and stay consistent. (Different from DDB-modesty, which is *identity*-uncertainty.)

**Finite frames cannot combine modesty with conditional-tower coherence.** On a *finite* frame, if the soft conditional tower holds for all bounded $X$, the expert is immodest on the novice's support: finitely many values $\{E_w(X)\}$ give a **spectral gap**, so for $\delta$ below it the soft indicator equals the hard one, the threshold events generate the expert $\sigma$-algebra, and the hypothesis collapses to $E(X)=E_\pi(X\mid\mathcal{P})$ — immodesty. So on a finite frame the very property making Value cheap *forces immodesty*. A reasoner at once **modest** and **conditional-tower-coherent** needs the expert's estimates to take continuum-many, gapless values — an **infinite, self-referential** process. Logical inductors are exactly that: a continuum of completions, dense future estimates, and a permanent gap between the *hard* conditional tower (the liar keeps it false) and the *soft* one (which holds). So whether the expert is your future self or a different AI, **clean modest deference lives only between infinite-frame processes** — of which inductors are the concrete inhabitants.

### 2.3 Weatherson's infinite failures are LI's two scope conditions

Weatherson breaks DDB Thm 2.2 both ways on infinite frames; each break exploits exactly one thing LI excludes for an independent reason.

| failure | direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust ⇏ Value | unbounded utility | bounded LUVs / finite-risk traders |
| **Bentham** | Value ⇏ Total Trust | null-tail hard conditioning | finite stages + soft $\operatorname{Ind}_\delta$ |

*Coin:* options with $2^i$ payoffs make the recommended strategy's diagonal $0$ while every option has positive expectation — excluded because LI expectations are defined only for **bounded** LUV-combinations (boundedness *is* the uniform integrability §1.1 needs). *Bentham:* Total Trust fails at a single measure-zero world — excluded because the tower quantifies over **finite** stages with $n\to\infty$ and conditions only **softly**, never on a hard null event.

### 2.4 The realizability payoff

The finite story is **realizable** — the novice's candidate set literally contains the expert — which is cognitively fake for the cases we care about. LI earns the equivalence **without** realizability, and this matters *more* cross-process than for self-trust: the expert is a *separate, possibly larger* process, provably not realizable within the novice (the novice cannot contain a full model of it — that way lies the liar), yet deference-as-value still goes through, approximately and in a timely manner. A deference theorem that survives the removal of realizability — in the one setting where a finite mind reasons soundly about something bigger than itself — is the reassurance the finite proof could not give.

**Lean (§2).** `LeanDeference.lean`:

```lean
-- §2.1  a coherent single state is cheap: argmax ⇒ Value, exact, tie-break-free
theorem DeferenceArgmax.value_of_argmax ... (hπ : ∀ w, 0 ≤ π w)
    (hstar : ∀ w j, (∑ v, P w v * O j v) ≤ ∑ v, P w v * O (jstar w) v)
    (hUM_S : (∑ w, π w * O (jstar w) w) = ∑ w, π w * (∑ v, P w v * O (jstar w) v))
    (hUM_i : (∑ w, π w * (∑ v, P w v * O i v)) = ∑ w, π w * O i w) :
    (∑ w, π w * O i w) ≤ ∑ w, π w * O (jstar w) w

-- §2.1  a frame is dear: the anti-expert frame is stationary (πP = π) yet fails Value
theorem DeferenceConverse.AntiExpert.stationary : ∀ v : Fin 2, (∑ w, π w * P w v) = π v
theorem DeferenceConverse.AntiExpert.value_fails :
    ¬ ((1/2) * (∑ w, π w) ≤ ∑ w, π w * (if (1/2) ≤ (∑ v, P w v * X v) then X w else (1/2)))

-- §2.2  finite collapse: the conditional tower forces immodesty (fiber-indicator core)
theorem DeferenceExtra.CM_implies_immodest ... (hw : 0 < π w)
    (hCM : ∀ X : W → ℝ, (∑ v, P w v * X v)
        = (∑ v, π v * (if P v = P w then 1 else 0) * X v) / (∑ v, π v * (if P v = P w then 1 else 0))) :
    (∑ v, P w v * (if P v = P w then 1 else 0)) = 1
```

`value_of_argmax` is the single-state cheapness (one argmax, `Ŝ` a single LUV); the anti-expert frame (`stationary` + `value_fails`) is the dearness of a frame (marginal martingale holds, Value fails). §2.3 (Weatherson as LI's two scope conditions) and §2.4 (realizability) are scope/interpretation — no formal claims; boundedness and soft conditioning, which exclude Coin/Bentham, live in the `[0,1]`-LUV typing and the `Ind_δ` of §1.6.

---

## 3. When is the tower *forced*? The arbitrage view and the complexity gap

Everything in §1–§2 is conditional on `Mart$(H\to E^\ast)$` — the tower is a *hypothesis about the pair*. The subject of the rest of the note is when it is **forced** rather than merely permitted. The lens is the no-Dutch-book criterion read as arbitrage.

### 3.1 The direct trader: a Value gap is pure arbitrage — *if you can cash out at the expert's verdict*

There is a single trader who turns any Value gap into guaranteed profit, so the criterion forbids the gap outright. Take the self-case ($E^\ast=H_{f(n)}$). Suppose Value fails: for some bet $O^i$ and $\varepsilon>0$, on infinitely many days $n$, $\;E^H_n(O^i_n)>E^H_n(\widehat S_n)+\varepsilon$ — the novice prices the alternative $O^i$ *above* the expert's own pick $\widehat S$. A trader bets the expert's strategy is good:

- **Day $n$ (open):** sell one share of $O^i$, buy one share of $\widehat S=O^{j^\ast}$ (tradable as its defining sentences even though the trader does not yet know *which* option $j^\ast$ is). Cash in: $E^H_n(O^i)-E^H_n(\widehat S)>\varepsilon$.
- **Day $f(n)$ (unwind):** reverse at day-$f(n)$ prices. Cash in: $E^H_{f(n)}(\widehat S)-E^H_{f(n)}(O^i)=M_n-m^i_n\ge0$, because by day $f(n)$ the self has priced its own pick at the maximum (F1 — the *definition* of the selection, not a theorem).

After the unwind the position is flat and the trader has banked $>\varepsilon$, guaranteed, with bounded risk (the only exposure is the bounded $\widehat S-O^i$ held between $n$ and $f(n)$). Repeated over the gap-days: unbounded profit on bounded risk — exploitation. A logical inductor admits none, so Value holds. (Soften the trade size to a continuous ramp to keep it legal.) This relocates §1.1's ingredients: the **tower steps are the cross-day round-trip** (the novice cannot misprice its own future), and the **`expprovind` facts ($E^H_{f(n)}(\widehat S)=M\ge m^i$) are the guarantee the unwind never costs**. The entry edge is the Value gap; the exit is *free*; so a Value gap is pure arbitrage, not a bet on the world.

### 3.2 The self-case is free: the future self as the canonical expert

The same trader works *iff the novice can cash out at the expert's verdict* — i.e. transact in a market that settles on the expert's estimate, or has prices already tracking it. For the future self this is automatic, and indeed **every** deference hypothesis is an LI theorem:

| hypothesis on $E^\ast$ | self-instance theorem |
|---|---|
| observable | the day-$f(n)$ market is $\mathcal{C}_H$-market-generable from $H$'s own prices |
| coherent (single state) | LI limit-coherence; the inductor is one belief state |
| introspective | Introspection — `epr` (4.11.3), `er` (4.11.4) |
| `Mart` (tower) | Expected Future Expectations — `cee` (4.12.1) |
| `ccee` (conditional tower) | No Expected Net Update under Conditionals — `ccee` (4.12.3) |
| Total Trust (consequence) | Self-Trust — `st` (4.12.4), the propositional case |

So **self-trust is the one case where you are guaranteed to tower over the expert** — the criterion hands you `cee`/`ccee` for free, because truster and trusted share temporal identity (the prices are simultaneously the subject and the resolution criterion of the bet, powering the Dutch book). The future self is also the **maximal observable expert**: anything the novice can observe of an external expert, its own day-$f(n)$ self has already incorporated, so the future self is a Blackwell **refinement** of any observable expert, and deferring to it dominates. "Trust your future self" is "defer to the join of all experts you can see." Studying *humans trusting AI* is studying the cases where the expert is **not** your own future self and the tower must be *earned*.

### 3.3 The hinge: the complexity gap, and "you can only arbitrage a market you can trade in"

For a generic external expert $A$, the §3.1 trader cannot unwind at the expert's prices — and the complexity gap is exactly why, and exactly what restores a (one-sided) version of it.

- **The novice cannot arbitrage the expert.** To force $A$ toward anything, a $\mathcal{C}_H$-trader would have to cash out against $A$'s verdict — i.e. compute or settle on $A$'s estimates. But producing $A$'s estimates is $\mathcal{C}_A$-hard, outside $\mathcal{C}_H$. So there is **no symmetric trader and no symmetric forcing**: the novice reads $A$ through the thin channel (cheap) but cannot out-compute it. This is the precise content of v4's "self-trust is free and cross-trust is a hypothesis because you can only arbitrage against a market you can trade in" — the simulability preorder, with the market always sitting strictly above its own trader class.
- **The expert *can* arbitrage the novice.** Reverse the roles. Because $\mathcal{C}_A\supseteq\mathcal{C}_H$ (with room to spare — $\mathrm{P}\subsetneq\mathrm{EXP}$), an $A$-side trader *can* simulate the $\mathcal{C}_H$-novice's deliberation to the horizon. So if $A$ publishes a quote $a_n$ on a contract that **settles to the novice's own future deliberation** $Y_n$, then any persistent gap $a_n\ne Y_n$ is exploitable by a $\mathcal{C}_A$-trader, and $A$'s own LI criterion forbids it. **Cross-process forcing lives on the expert's side, and forces the expert to predict the novice.** This is the engine of §5.
- **Why blindness-with-power is satisfiable exactly because $\mathrm{P}\subsetneq\mathrm{EXP}$.** The $\mathcal{C}_A$-trader must compute $Y_n$ by stage $n$. If $Y_n$ depends only on the *poly-time* novice run to the horizon $F(n)=2^n$, that costs $2^{O(n)}\in\mathrm{EXP}=\mathcal{C}_A$ — affordable. If instead $Y_n$ fed on $A$'s *own* run to $F(n)$, the cost would be $\mathrm{EXP}\circ 2^n$ — doubly exponential, unsatisfiable inside $\mathrm{EXP}$. So the class gap is precisely what makes "$A$ predicts a horizon-deep human deliberation, on time" a *satisfiable* demand — provided the target is **blind** to $A$'s own output. §4 shows blindness is not optional, and §5 builds the blind target that works.

### 3.4 The governing question, restated

The cross-process characterization — **when does one logical inductor tower over a *distinct* one** (same theory? richer theory? larger class? faster schedule?) — is *not* free; it is the LI analog of DDB's "$\pi\in\mathrm{CH}(C_\pi)$ and every candidate modestly informed," and the question behind "when should a human (or AI) trust a given other AI." It sits in the **tiling / Vingean-reflection** register rather than self-trust. The next two sections give the current answer: a negative backbone (§4) showing how much *cannot* be forced and forcing the design to be **blind**, and a positive result (§5) forcing the tower on the **timely fragment** and proving it unforceable beyond.

**Lean (§3).** `LeanDeference.lean` (§3.1) and `FrozenDeliberation.lean` / `SelfReferentialTarget.lean` (§3.3):

```lean
-- §3.1  a Value gap is pure arbitrage: the round nets ≥ the gap (unwind is free by argmax)
theorem DeferenceTrader.round_profit_ge_gap (en ef : J → ℝ) (i jstar : J)
    (hmax : ∀ j, ef j ≤ ef jstar) : en i - en jstar ≤ (en i - en jstar) + (ef jstar - ef i)
theorem DeferenceTrader.gap_pos_imp_profit_pos (en ef : J → ℝ) (i jstar : J)
    (hmax : ∀ j, ef j ≤ ef jstar) (hgap : 0 < en i - en jstar) :
    0 < (en i - en jstar) + (ef jstar - ef i)

-- §3.3  the hinge: the blind power assumption is satisfiable …
theorem Frozen.blind_cost_realizable :
    ∃ (RH RA : ℕ → ℝ) (F : ℕ → ℕ), StrictMono RA ∧ (∀ n, n < F n) ∧ (∀ n, RH (F n) ≤ RA n)

-- §3.3  … whereas the non-blind (self-referential) one is not (cost-circularity)
theorem SelfRefTarget.cost_circularity (R RA : ℕ → ℝ) (F : ℕ → ℕ)
    (hmono : StrictMono RA) (hF : ∀ n, n < F n)
    (hshare : ∀ n, RA (F n) ≤ R (F n)) (hcost : ∀ n, R (F n) ≤ RA n) : False
```

§3.2 (the self-case is free) adds no theorem — it is the observation that, for $E^\ast = H_{f(n)}$, every §0.4 hypothesis is itself an LI theorem (`cee`/`ccee`/`epr`/`er`), so the §1 results apply unconditionally. The `blind_cost_realizable` vs `cost_circularity` pair is the formal core of "you can only arbitrage a market you can trade in": the EXP/$2^n$ contrast (a poly-time horizon cost is affordable in EXP; a doubly-exponential self-referential cost is not) is the prose reading of those two theorems.

---

## 4. Across processes, negatively: what cannot be forced

### 4.1 No-Forced-Trust

Garrabrant's self-trust (4.12) forces an inductor to trust its *own* future prices because there the prices are simultaneously the subject and the resolution criterion. The first cross-process fact is that *nothing survives in the forced/Dutch-book sense* when truster and trusted are distinct:

> **No-Forced-Trust.** There is no efficiently-checkable relation between two distinct inductors whose satisfaction Dutch-book-forces $H_\infty=A_\infty$ on undecidable sentences.

Precisely: on **decidable** $\phi$, forced calibration and agreement hold — but there they are *idle*, since both sides can compute the answer anyway. On **undecidable** $\phi$ (the cases that matter), closing the gap requires *inductive generalization* from "$A$ is calibrated on decidable cases" to "$A$ is reliable on undecidable cases" — permitted by LI (non-dogmatism / pattern-learning) but **not Dutch-book-forced**. The only three ways to force agreement all dissolve the problem: (i) add inductive generalization beyond coherence; (ii) treat $A$'s prices as the resolution criterion, which *is* assuming trust; (iii) merge the agents, after which it is self-trust and "the other stops being other." And limit equality is **badly conditional**: any nontrivial efficiently-checkable relation pins $A_\infty$ only where $H_\infty$ is $\mathcal{C}_H$-recoverable from observable price history; over rich theories (PA), limit values on independent sentences are not recoverable, so equality cannot be forced there. Per-sentence convergence on a *fixed* $\phi$ survives ($A_\infty(\phi)=H_\infty(\phi)$, since the trivial predictor $H_n(\phi)\to H_\infty(\phi)$ suffices) but is idle. *Forced other-trust analogous to self-trust is impossible by the structure of the framework* — informative as a theorem: any real trust must supply inductive structure, shared resolutions, or merger.

(A joint-market reformulation — one market over a language enlarged to include statements about $A$'s prices — buys stronger forced statements only by collapsing toward a single agent, changing the question rather than answering it.)

### 4.2 The natural model: self-trust through a mirror

The most natural attempt to *manufacture* a self-like tower across the gap is to settle $A$'s contracts against the novice's **own future credence**. Let $H^+$ be $H$ augmented to read $A$'s published quotes (the realistic human who has heard the AI), and set the settlement target
$$
\boxed{\ Y_n:=H^+_{F(n)}(P^{(n)})\ }
$$
— $A$'s contract on $P^{(n)}$, deferred to stage $F(n)$, settles against $H^+$'s own future verdict. If $A$'s quote $a_n=E^A_n(C_n)$ reliably equals $Y_n$, then "defer to $A$" is literally "defer to your own better-thought-out future self, read off a fast instrument" — Garrabrant self-trust routed through $A$. The headline one would want is **universal pointwise timely Tracking**: over an effective enumeration $(P^{(n)})$, $\;a_n-Y_n\approx_n0$, enforced at stage $n$ (a genuine *prediction*, not an after-the-fact echo).

> **Terminology — Tracking, not calibration.** *Tracking* is predictive exactness (the forecast lands on the realized value, contract by contract). *Calibration* is the weaker no-predictable-adjustment property (conditional on the forecast being $\approx p$, the realized average is $\approx p$). Tracking ⟹ calibration, never the converse. What §4.3 kills is **Tracking**; genuine calibration survives (§4.5) and is the ceiling. (This matches the v6/HEAD convention; the older summary's "Calibration/Tracking" label for the pointwise statement is just stale.)

The mechanics (recorded for §5's contrast): a threshold encoding of reals to a $1/n$-grid via monotone atoms — $\theta_{n,k}$ ("the deferred value of contract $n$ is $\ge k/n$") in $A$'s language, $\beta_{n,k}$ ("$A$'s quote for $n$ is $\ge k/n$") in $H^+$'s language — with $C_n:=\tfrac1n\sum_k\theta_{n,k}$, $a_n:=E^A_n(C_n)$, and a ledger $R_n:=\tfrac1n\sum_k\beta_{n,k}$ recording $A$'s rounded quote, decided in $H^+$'s world by $n+1$. Schedules $e(n)<F(n)<\sigma(n)$ (publication, lookahead, payout). The **power assumption** is that $\mathcal{C}_A$ contains $n\mapsto Y_n$ — equivalently $n\mapsto R(F(n))$, $R(t)$ the coupled-construction cost through stage $t$. §4.3 shows this is exactly the problem.

### 4.3 It dies twice

**2a — the anti-inductive settlement (kills universal pointwise tracking even with unlimited compute).** A tracking theorem is universally quantified over an effective family — universality is constitutive — and the family then contains anti-inductive instances. The whole phenomenon is one elementary fact about a discontinuous self-map:

> **Lemma (no exact quote).** For $\rho(a)=\mathbb{1}[a\le\tfrac12]$, $\;\inf_{a\in[0,1]}|a-\rho(a)|=\tfrac12$, attained only at $a=\tfrac12$. (Rounding-robust form: $\tfrac12-|r-a|\le|a-\rho(r)|$.)

Because the $\beta$-atoms recording $a_n$ live in $H^+$'s own language, "$R_n\le\tfrac12$" is a sentence of that language, decided by $n+1$. Take $P^{(n)}=g_n$ a fresh atom with the axiom $g_n\leftrightarrow(R_n\le\tfrac12)$; then $g_n$ is decided by $F(n)$ to $\mathbb{1}[r_n\le\tfrac12]$, so by provability-induction $Y_n=H^+_{F(n)}(g_n)=\mathbb{1}[r_n\le\tfrac12]+\eta_n$ with $\eta_n\to0$, and the Lemma gives
$$
\boxed{\ |a_n-Y_n|\ \ge\ \tfrac12-\tfrac1{2n}-\eta_n\ \ (\text{every }n),\qquad\text{hence}\qquad \liminf_{n\to\infty}|a_n-Y_n|\ \ge\ \tfrac12\ }
$$
Tracking is violated by a *constant* margin. This is the **$\chi$-paradox transplanted from the sentence level to the settlement level**: at sentence level the diagonal $\chi\leftrightarrow(\mathbb{P}(\chi)<\tfrac12)$ is benign because trader *continuity* hands back a clearing price $\tfrac12$; but a deductive process is a **hard $0/1$ oracle** and grid-rounding is **discontinuous by construction**, so the continuity escape is gone ($\rho(\tfrac12)=1\ne\tfrac12$). It is **independent of $A$'s compute** — grant $A$ a halting oracle and the Lemma still forbids $|a_n-Y_n|<\tfrac12$, because the settlement is *defined* as the anti-inductive negation of whatever $a_n$ is. Scope: this needs a **quote-referencing** family ($g_n$ must mention $a_n$); restricting to quote-free base sentences blocks the explicit counterexample — but makes tracking *underivable*, not *true*, and 2b then bites.

**2b — cost-circularity (makes the power assumption unsatisfiable).** Timely per-instance tracking needs a $\mathcal{C}_A$-trader that computes $Y_n$ by stage $n$. But $Y_n=H^+_{F(n)}(P^{(n)})$ is a stage-$F(n)$ object of the *coupled* system: $H^+$ at $F(n)$ has absorbed quotes $a_i$ for indices $i>n$ — some of $A$'s **own future** quotes — so computing it means forward-simulating the coupled construction to $\sim F(n)$, cost $\Theta(R(F(n)))$. The robust skeleton:
$$
\boxed{\ R_A(n)\gtrsim R(F(n))\ge R_A(F(n))>R_A(n)\ }
$$
a contradiction: $\mathcal{C}_A$ would have to contain its own coupled simulation cost $R\circ F$. So the power assumption is **unsatisfiable**, not merely strong; in any settlement language entangled with $A$'s prices, a simulate-and-arbitrage trader weaponizes the regress into explicit exploitation ($\chi$ at the level of $A$'s prices), and no fixed-point/ordinal-tower class escapes — the obstruction is the class's position in the *simulability preorder*, not a growth rate. (One soft joint, flagged in §8: whether inexploitability strictly *forces* $A$ to pay the simulating trader's full runtime, or budgeting opens a gap — the source rates the cost-accounting ~75–80%. The order-theoretic reflective-exploiter argument does not depend on the naive "market runs its traders" mechanism, which is *wrong* and was corrected.)

2b is categorically unlike 2a: 2a exhibits a *false* instance; 2b shows the only known *route to a proof* is contradictory (underivable, not disproven). The cheap alternative routes all fail: provability-induction needs an e.c.-writable theorem sequence, but "$C_n=m^\ast_n$" can't be written before $m^\ast_n$ is computed; affine coherence transfers only $D$-provable relations, and "$a_n=Y_n$" is not $D$-provable; self-trust gives only $A$'s *subjective* martingale $a_n\approx\mathbb{E}^A_n[Y_n]$, not objective per-instance accuracy. The strength hierarchy:

| notion | content | verdict |
|---|---|---|
| **timely / per-instance (Tracking)** | $a_n\approx_n Y_n$ enforced at stage $n$ | **dies** (unsatisfiable power assumption) |
| **eventual** | $E^A_{\sigma(n)}(C_n)\to$ settled value | survives, **near-tautological** (a trader merely waits) |
| **statistical (Calibration)** | $A$ learns the pseudorandom *frequency* of $H^+$-values across the family | survives, **real and free** (Learning Pseudorandom Frequencies, LI §4.4) |

The two impossibilities are **independent and complementary** — 2a kills the quote-referencing case by refutation; 2b kills the quote-free case by unsatisfiability. "Dead twice over."

### 4.4 The dichotomy: predictable iff uninfluenced

> **Definition (reflective blindness).** The settlement map $n\mapsto m^\ast_n$ is **reflectively blind** if it factors through $A$-free data — a function of $n$ and $H$'s autonomous run alone — equivalently $\partial D_A/\partial A=0$. Blindness makes $(D_A,A)$ a strict-stage-order DAG rather than a mutual recursion.

> **Dichotomy (predictable iff uninfluenced).** Suppose the contract family is **effective** and universal pointwise timely tracking is provable from a **satisfiable** power assumption. Then the settlement map is reflectively **blind**.

*Contrapositive of §4.3:* if the settlement *depends* on $A$'s quotes and the family may reference quotes, 2a makes tracking *false*; if the family is quote-free to dodge 2a, the dependence runs through $H^+$'s absorbed ledger and 2b makes tracking *underivable from a satisfiable hypothesis*. Either way A-dependence is incompatible with (effective ∧ provable-from-satisfiable ∧ timely-pointwise). **Blindness is therefore derived, not assumed** — the constructive half of a dichotomy: *a settlement you can predict is one the predictor cannot influence.* (Scope: this is internal to *this architecture* — LI markets, hard $0/1$ deductive settlement, grid rounding. The one structural escape, continuous unrounded LUV-style settlement with fixed-point selection, buys *existence* of self-consistent quotes by Brouwer but not a theorem that $A$'s market *locates* the wanted one, and re-imports everything the threshold encoding avoided; the performative-prediction literature shows the fixed points that exist need not be the ones anyone wants.)

### 4.5 What survives anyway

The negatives are about the *universal pointwise timely Tracking headline*. Four things survive; naming them keeps the negative honest.

- **Externalized self-trust (conditional on Tracking).** An $H^+$-side coherence theorem by a *waiting* arbitrage. With the **one-sided** indicator $\operatorname{Ind}_\delta(X>p)$ (so $\operatorname{Ind}_\delta>0\Rightarrow X>p$, landing the conclusion at exactly $p_n$), and assuming Tracking $a_n-Y_n\to0$:
$$
H^+_n\big(\mathbb{1}(P^{(n)})\cdot\operatorname{Ind}_\delta(R_n>p_n)\big)\gtrsim_n p_n\,H^+_n\big(\operatorname{Ind}_\delta(R_n>p_n)\big),
$$
proved by a $\mathcal{C}_H$-trader who buys $B_n^+:=\operatorname{Ind}_\delta(R_n>p_n)\cdot(\mathbb{1}(P^{(n)})-p_n)$ at $n$ and sells at $F(n)$ on a sparse subsequence: the position is decided by $F(n)$ (the ledger), the resale value reduces (LUV-vs-affine) to $i_n^+(Y_n-p_n)\ge -|r_n-Y_n|\to0$ by Tracking, so each round trip nets $\ge\epsilon/2$ with bounded risk — contradicting the criterion unless the inequality holds. **The non-triviality has relocated entirely into the Tracking hypothesis**: as a *reduction* — "external trust $=$ self-trust $+$ Tracking, by arbitrage" — it shows external trust is exactly as strong as the (damaged) predictive Tracking one can independently secure. It is, precisely, self-trust through a mirror; real, the cleanest derivation in the corpus, but parasitic on self-trust, so it cannot carry a Tracking headline.
- **Gated and classwise-averaged deference, with a tight ceiling.** Conditioned on a continuous gate $G_n=g(a_n)$, $H^+$'s gated credence tracks $a_n$ up to $O(\epsilon/\delta)$ plus a term that $\to0$; over $D$-decidable subsequences, weighted-average deference errors vanish (LI 4.3.6/4.3.8/4.4.5 style). The anti-inductive counterexample earns its keep on the *positive* side: it is exactly the obstruction to a pointwise object-level version, so **the gated/averaged ceiling is tight** — a theorem about the problem, not a proof-weakness.
- **Non-Dogmatism confines manipulation to the interior.** For $\Gamma$-independent $\varphi$, every inductor over the augmented process has $H^+_\infty(\varphi)\in(0,1)$, and the uniform form gives a complexity-graded margin $[\delta_\varphi,1-\delta_\varphi]$. So whatever influence $A$ exerts, it provably **cannot drive certainty** on undecided propositions.
- **The decided fragment trusts cleanly.** For $\Gamma$-decided $\phi$, both $H_\infty(\phi)$ and $H^+_\infty(\phi)$ equal $\mathbb{1}[\Gamma\vdash\phi]$ by provability-induction on $D\subseteq D^+_H$ — one line, no coupling. On the decidable fragment, deference buys **speed, never truth**, and is fail-safe even against an adversarial advisor. Underdetermination is a phenomenon *only* of the $\Gamma$-independent fragment (exhibited via a Projection/Shannon-split lemma for independent atoms and Boolean combinations; entangled independents like Con(PA) are open, §8).

> **A refuted sub-attempt (signpost).** A natural attempt to rescue a strong claim — make $A$'s influence provably *move* $H^+$'s limit — builds $H^+$ over a *strictly stronger* deductive process $E\supsetneq D^+_H$ that decides an undecided $\varphi$, concluding $H^+_\infty(\varphi)=1\ne H_\infty(\varphi)$. It is **wrong**, refuted by Non-Dogmatism: if $D^+_H$ never decides $\varphi$, then ND forces $H^+_\infty(\varphi)<1$ for *any* inductor over $D^+_H$, so the construction's object is an inductor over $E$, a different process. The error is a monotonicity reversal (shrinking the plausible-world set preserves "bounded below" but not "unbounded above"). Legitimate underdetermination keeps $(\Gamma,D)$ *fixed* and re-weights a free atom; strengthening the theory is a category error that silently moves $\varphi$ into the decided fragment.

### 4.6 Substrate, briefly: plain inductors suffice

The original drafts considered **universal (measure-valued) inductors** for their measure-theoretic conditioning (LI 4.7.2), which would let $H^+$ carry $H$'s prior joint beliefs about (quote, outcome) and yield a *genuine* Bayesian-update deference result. But that payoff was tied to the self-referential target, which §4.3 kills; and the same Bayesian-update *content* (an expectation over a not-yet-published quote) is recoverable on **plain** logical inductors by pricing a ledger contract on $A$'s *future* quote and adding one **reflection axiom** internalizing "this contract settles to the intended future credence." So universal inductors are **not necessary even for the result they were introduced to secure**, and carry an existence/efficiency overhead besides. The live package is: plain logical inductors + direct founding ($H^+$ founded over $D_H\oplus$ quote atoms, not by conditioning) + reflectively-blind target. (Direct founding owes an introspective-process existence lemma — that the standard existence proof tolerates a process defined from the inductors' own earlier prices; §5.2, §8.)

### 4.7 Structural findings that sit across the live construction

- **Non-conservativity as an operation on limit credences.** The augmented process is *deductively* conservative but **non-conservative as an operation on limit credences**. The slogan is not "$A$'s quotes move the limit" but "$A$, and all the trust it induces, **fails to pin** the endpoint."
- **Equilibrium multiplicity = underdetermination, relocated.** The trust apparatus forms a self-consistent equilibrium at *every* deference level and selects none. External trust is **parasitic on self-trust** — $A$ mirrors the augmented reasoner's own deferred credence — so "trusting $A$" reduces to self-trust routed through a relay; this is the No-Forced-Trust phenomenon seen from inside $H^+$, and the formal home of the never-settled residual.
- **Manipulation attack surface.** The bare construction structurally *cannot* exhibit manipulation (external trust is parasitic, so $A$ has no independent content to inject) — but equilibrium multiplicity reveals the surface: every endpoint passes all trust tests. A genuine manipulation theorem needs (a) a second calibration condition separating calibration-to-self from calibration-to-truth; (b) an evidence/preemption distinction; (c) a transfer-of-trust attack (earn authority on decidables, spend it on undecidables); (d) non-recoverability — the formal statement that legitimacy cannot be certified from the trace.
- **Certifiability impossibility.** One cannot certify *why* the advisor is right from its behavioral trace; the positive program is to characterize the "second channels" that would restore certifiability.

**Lean (§4).** `SelfReferentialTarget.lean`:

```lean
-- §4.3 (2a)  no exact quote — the arithmetic core (compute-independent)
theorem SelfRefTarget.no_exact_quote (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 1/2 ≤ |a - antiInd a|

-- §4.3 (2a)  universal pointwise tracking fails: ¬ (aₙ ≈ₙ Yₙ), and liminf |aₙ − Yₙ| ≥ ½
theorem SelfRefTarget.tracking_fails (a r Y : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1) (hround : Tendsto (fun n => r n - a n) atTop (𝓝 0))
    (hLIPI : Tendsto (fun n => Y n - antiInd (r n)) atTop (𝓝 0)) : ¬ Approx a Y

-- §4.4  the dichotomy: predictable ⇒ uninfluenced (the contrapositive of 2a ∧ 2b)
theorem SelfRefTarget.predictable_imp_uninfluenced {Blind Tracks SatPower QuoteRef : Prop}
    (h2a : ¬ Blind → QuoteRef → ¬ Tracks) (h2b : ¬ Blind → ¬ SatPower) :
    (QuoteRef → Tracks → Blind) ∧ (SatPower → Blind)

-- §4.5  externalized self-trust (Tracking ⇒ H⁺-side coherence, by inter-temporal arbitrage)
theorem SelfRefTarget.externalized_self_trust (HB i p r Y : ℕ → ℝ)
    (hi0 : ∀ n, 0 ≤ i n) (hi1 : ∀ n, i n ≤ 1) (hone : ∀ n, 0 < i n → p n < r n)
    (htrack : Tendsto (fun n => |r n - Y n|) atTop (𝓝 0))
    (hNoArb : AsympLE (fun n => i n * (Y n - p n)) HB) : AsympLE (fun _ => 0) HB

-- §4.5  Non-Dogmatism confines manipulation to the interior [δ, 1−δ] ⊂ (0,1)
theorem SelfRefTarget.manipulation_confined (Yinf δ : ℝ) (hδ : 0 < δ)
    (hlo : δ ≤ Yinf) (hhi : Yinf ≤ 1 - δ) : 0 < Yinf ∧ Yinf < 1
```

§4.1 (No-Forced-Trust) is a meta-statement about the non-existence of an efficiently-checkable forcing relation — interpretation, not formalized. Also in the file: `no_exact_quote'`/`residual_lb` (tie-robust core), `tracking_fails_liminf` (the quantitative ½ bound), `tracking_fails_nonvacuous` and `cost_setup_realizable` (non-vacuity), `regress`/`cost_circularity` (2b), and `nondogmatism_refutes` (the refuted divergence sub-attempt of §4.5).

---

## 5. Across processes, positively: forcing the tower on the timely fragment

The dichotomy points straight at the repair, and the complexity gap (§3.3) makes it *forcing*: settle $A$'s contracts against a **blind** target, and the $\mathcal{C}_A$-side arbitrage of §3.3 turns the tower into a theorem — as far as settlement reaches.

### 5.1 The repair, and the forcing idea: the sealed sibling

The minimal blind retarget is the **autonomous** human $Y_n:=H_{F(n)}(P^{(n)})$ ($H$ never reads $A$), which zeroes $\partial D_A/\partial A$ ($H$ is upstream; the mutual recursion collapses to a staged DAG $H\to A\to H^+$) and dodges both diseases (2b: computing $Y_n$ costs the $A$-free $R_H(F(n))$, a satisfiable demand; 2a: $H$'s language has no quote atoms, so the anti-inductive instance is structurally absent).

The **frozen-deliberation** construction sharpens this into a *forcing* result by choosing the target to keep as much information as blindness allows. For each $n$, let $H^{[n]}$ be a logical inductor over (the world) $\oplus\,Q^{<n}$, where $Q^{<n}$ settles the past quotes $a_1,\dots,a_{n-1}$ as facts and **freezes there** — quotes of index $\ge n$ are never injected, though their publication stages precede the horizon $F(n)$. This is the **sealed sibling**: neither the novice's future self (which by $F(n)$ has heard $a_n$ and is the *disallowed* object — it could be steered into the $\mathbb{1}[a_n\le\tfrac12]$ contract) nor an arbitrary inductor, but the novice's own deliberation with $A$'s **current quote held out**. Blindness therefore **forces a family** $\{H^{[n]}\}$ — one inductor per index — because a single inductor hearing the whole ledger could be steered through its own cross-references. The target is $Y_n:=H^{[n]}_{F(n)}(P^{(n)})$, and $A$'s contract $C_n$ settles to the grid-rounded $Y_n$ at $\sigma(n)$.

### 5.2 The construction

Three inductors, all ordinary (no measure-valued conditioning):
- **$A$, the predictor** [v4 expert $E^\ast$]. Over $D_A$, class $\mathcal{C}_A$. Publishes $a_n:=E^A_n(C_n)$ at $e(n)$. A single inductor — one coherent belief state, one argmax (the F1 §1 leans on).
- **$H^+$, the advised reasoner** [v4 novice $H$/$E_n$]. Over $D_{H^+}=$ (world) $\oplus$ (full ledger of every published quote), founded directly; class $\mathcal{C}_H$. The ledger settles each atom $q_n$ to a usable encoding of $a_n$, so $H^+$ can *refer to* and do arithmetic with $a_n$. As an inductor it gets, free, exactly the novice's tools (`loe`, `expprovind`) plus calibration and self-trust toward its *own* future — none assumed about its relation to $A$.
- **$\{H^{[n]}\}$, the frozen-deliberation target** (the sealed sibling, §5.1) — the settlement *target* that pins $A$, not itself a deference partner.

**Schedules.** Monotone computable $e(n)<F(n)<\sigma(n)$: publication $e$, lookahead $F$ (superpolynomial, e.g. $2^n$), payout $\sigma$. **Assumptions:** (A1) all three satisfy the LI criterion; (A2) **observability** — $H^+$ reads $a_n$ off its own prices (the thin channel: $\mathcal{C}_A$-hard to generate, $\mathcal{C}_H$-cheap to read); (A3) **coherence + introspection of $A$** (single state, F1 provable); (A4) **power** — $\mathcal{C}_A$ contains the cost of simulating the weaker reasoner to the horizon (met by the concrete choice below); (A5) **regularity + publication** — total cost $R$ monotone and $\mathcal{C}_A$-bounded, $e\ge R$ so the ledger is $\mathcal{C}_H$-readable. There is deliberately **no assumption that $H^+$ should trust $a_n$**; that is the conclusion (T3). An **optional future-quote settlement axiom** (used only for the genuine-update strengthening of T3) says $H^+$'s language contains a contract settling to $A$'s eventual quote $a_n$ *whatever it turns out to be* — letting $H^+$ form an expectation over $a_n$ before it is published; it states only the settlement *rule*, asserting nothing about $a_n$ matching truth. (This is the §4.6 reflection axiom.)

**A concrete satisfying choice.** $\mathcal{C}_H=\mathrm{P}$, $\mathcal{C}_A=\mathrm{EXP}$; $F(n)=2^n$; the weaker reasoner's per-stage cost polynomial. Simulating it to stage $2^n$ costs $2^{O(n)}\in\mathrm{EXP}$, so $A$'s traders can afford it (A4). **EXP suffices *only because the target is blind to $A$*** — a target feeding on $A$'s own run would demand $\mathrm{EXP}\circ2^n$, doubly exponential, unsatisfiable in EXP (§3.3).

**Joint existence is discharged, not assumed.** The inductors are defined by one recursion on the shared clock; delay each published quote by one stage (settle $q_i$ at $e(i)+1$ to $a_i=E^A_{e(i)}(C_i)$) so every stage-$t$ object is computable from prices at stages $<t$. The recursion is well-founded; the LI existence theorem applies to each process separately (its proof consumes the day-$t$ process as an input stream and never inspects how the stream was produced, so the coupling is invisible to it). [This is the introspective-process existence lemma of §4.6.]

### 5.3 The three fragments

Fix a tolerance schedule $\varepsilon_n\to0$. Every index $n$ falls in exactly one:
- **Timely $G$** — $P^{(n)}$ is decided in $D$ by stage $F(n)$ *and* $|Y_n-\text{truth}|\le\varepsilon_n$. Membership is **decidable** (run $D$ and $H^{[n]}$ to the finite stage $F(n)$ and check); on $G$, $Y_n\to\text{truth}$.
- **Slow** — decidable but not decided-and-converged by $F(n)$; here $Y_n$ is a *pre-resolution* credence.
- **Undecidable** — $D$ never decides it.

### 5.4 Faithfulness, forced on every fragment

**T1 · Faithful Tracking.** $a_n-Y_n\approx_n0$ (timely at settlement when $\sigma(n)\ge c\cdot R_H(F(n))$). *Proof:* were $a_n>\widehat Y_n+\varepsilon$ infinitely often, a $\mathcal{C}_A$-trader selling one share of $C_n$ on each bad day banks $>\varepsilon$ with bounded risk — because $C_n$ settles to $Y_n$ — exploiting $A$, against (A1); it computes $Y_n$ on budget by (A4). The mirror handles under-pricing; a continuous ramp keeps it legal. This is the §3.3 expert-side arbitrage, realized. **Scope:** $A$ is forced to *predict* the weaker reasoner's deliberation, not yet that the deliberation is *correct*.

**T2 · Earned meta-trust.** $H^+$ comes to believe, on schedule, that $A$ tracks the target: $E^{H^+}_n(\mathbb{1}[\,|a_n-Y_n|\le\varepsilon_n\,])\to1$. *Proof:* T1's bound is uniformly provable (the exploiting trader is describable, so the gap's closure is a theorem); the novice's `expprovind` carries it through $H^+$'s estimate. **This is precisely the *dynamic establishment from a track record* §3.4 names as the missing piece** — the analog the self-case gets for free as `cee`, here *grown* from a track record using only the novice's own free tool. Still belief in *faithfulness*, not correctness.

### 5.5 Soundness, forced on $G$ and only there

The engine is one fact, immediate from T1 and the definition of $G$: **on $G$, the quote is early-revealed truth**, $a_n\approx_n Y_n\approx_n\mathbb{1}(P^{(n)})$ (first $\approx$: T1; second: membership in $G$). Adopting $a_n$ *is* adopting the truth value — at the novice's real-time stage $n$, exponentially earlier than the horizon $F(n)$ at which it could reach that value itself.

**T3 · Conditional tower `ccee$(H^+\to A)$`.** On $G$, for every bounded readable continuous weight $w=w(a_n)$: $\;E^{H^+}_n(\mathbb{1}(P^{(n)})\cdot w)\approx_n E^{H^+}_n(\ulcorner a_n\cdot w\urcorner)$. *Proof:* the substantive content $\mathbb{1}(P^{(n)})-a_n\approx_n0$ on $G$ is **provable in $H^+$'s own logic, with no axiom telling $H^+$ to trust $a_n$**. In every consistent world of $D_{H^+}$, $P^{(n)}$ is pinned to its truth value (decidable, decided) and the ledger atom to the published $a_n$ (already part of $D_{H^+}$), so the gap equals the *actual realized number* $\text{truth}-a_n$, $\le\varepsilon_n$ plus the T1 error, both $\to0$; that this is small is itself provable on $G$ (both quantities settled and computable by $F(n)$, so $\Gamma$ establishes their closeness by exhibiting them). The novice's `expprovind` carries the provably-small $(\mathbb{1}(P^{(n)})-a_n)w$ through; linearity splits the weight, which factors because $A$ knows its own quote. **The ledger supplies only the *referent* for $a_n$; the link to truth comes entirely from T1 (forced, $\Gamma$-provable) and membership in $G$ (decidable).** No Dutch book between the two distinct inductors is used (impossible), and no internalized "trust $a_n$" axiom (that would assume the conclusion). **This is the port's `ccee$(N\to E^\ast)$` — the conditional tower, the substantive `Mart` content — with $E^\ast=A$, *forced* where v4 left it as the §3.4 hypothesis.**

> **Genuine-update strengthening (optional).** As stated, $H^+$ prices $a_n$ after reading it, so $E^{H^+}_n(\ulcorner a_n w\urcorner)$ is largely $H^+$ reporting a number it already holds. To get the stronger reading — $H^+$ forms a genuine *prediction* of $A$'s not-yet-published output, a Bayesian update — add the optional future-quote settlement axiom (§5.2): $H^+$ prices a contract on the unpublished $a_n$ before $e(n)$. The axiom states only the settlement rule, so the deference content still comes from T1 + $G$; it merely lets the expectation operator do real work.

**T4 · Value.** Let $\widehat S_n:=O^{j^\ast(n)}_n$ be the option $A$ would pick. On $G$, for each fixed $i$: $E^{H^+}_n(\widehat S_n)\gtrsim_n E^{H^+}_n(O^i_n)$; conversely, this preference across the menus $\{X,\text{const }s\}$ already forces T3. *Proof (forward):* the §1.1 four-liner with $E^\ast=A$ (two T3 steps + two `expprovind`). *Converse:* the §1.2 witness identity $E_n(\widehat S_{\mathrm{wit}})-s\,E_n(1)=E_n((X-s)\mathbb{1}[A(X)\ge s])$, from linearity and coherence alone, makes "prefer to defer on $\{X,s\}$" and "conditional tower at $s$" the same statement. **This is the port's headline `Value ⟺ Mart`, forced on $G$.** The forward direction is *cheap* here for the §2.1 reason: $A$ is one coherent belief state (an expert, not a frame), so $\widehat S$ is a single LUV the tower carries home.

**T6 · Calibration curve.** On $G$, binning by quote value, the outcome frequency equals the quote: $E^{H^+}[\mathbb{1}(P^{(n)})\mid a_n\approx v,\ n\in G]\approx v$. *Proof and boundary:* on $G$, $a_n\approx\mathbb{1}(P^{(n)})\in\{0,1\}$, so the bins sit at the extremes and the identity is immediate. The content is *why nothing stronger holds off $G$*: the §1.6 amplifier $g(e)=(1+2c)e-c$ passes every threshold-trust inequality yet is not the identity, so threshold trust alone cannot pin the curve to the diagonal (the open soft⇒hard squeeze). What excludes it *on $G$* is not a sharper squeeze but that the construction supplies genuine **calibration as a forced consequence of settlement**, and the amplifier is by definition a threshold-trust-passing / calibration-failing object that survives exactly where estimates are interior and unbacked by feedback — the off-$G$ region the forcing cannot reach. **The port's open squeeze-frontier and this construction's forcing blind spot are the same set**; v4 locates the frontier abstractly, the construction shows its natural domain is the timely fragment and reaches it there.

### 5.6 The dichotomy and the ceiling

**T7 · Limit prices.** $|H^{[n]}_\infty(P^{(n)})-H^+_\infty(P^{(n)})|\to0$ on $G$. Off $G$ the limit is **underdetermined**: among all inductors satisfying (A1)–(A5) with the *same* $A$, target, and ledger, the achievable $H^+_\infty(P)$ for a fixed off-$G$ $P$ form a *nondegenerate interval* — two such reasoners can agree on every quantity over $G$ (same prices, same deference, every test passed) yet differ by any prescribed gap on $P$; the construction selects no point in it. *Proof:* on $G$, T6 pins both $a_n$ and $H^+$'s credence to the same truth values. Off $G$, build two completions (existence theorem) with traders agreeing on all $G$-settling sentences but driven to distinct limits on $P$; non-dogmatism leaves room, and neither admits an exploiting trader because **no trader profits from a difference that never settles**. This is the conservation-law form of "the cross-process tower is *earned*, not assumed": settlement-powered forcing is co-extensive with settlement and goes silent the moment settlement is withdrawn (the exploiter earns by buy–wait–settle–rebuy; with nothing to settle it acts once, never recovers, freezes).

**T5 · The object-level ceiling (forced on every fragment).** Pointwise object-level deference — $H^+_n(P^{(n)})\approx_n a_n$ on the propositions themselves, *not* conditioned on $a_n$ — is **false**: the family contains anti-inductive contracts behaving like $\mathbb{1}[a_n\le\tfrac12]$ (§4.3's 2a) that no quote can match. Only the **gated** form (on decidable subsequences) and the **averaged** form survive, with the guarantee that no $\mathcal{C}_{H^+}$-trader profits from a persistent deviation policy. **This is the port's Total Trust ceiling**: Total Trust is strictly weaker than Reflection, and the gated/averaged forms are the most one can ask of deference to a *modest* expert; the averaged ceiling is a theorem about the problem, not a defect of the proof.

### 5.7 Target-Soundness, and the seam

Every soundness theorem rests on one fact:

> **(TS)** Among contracts with $Y_n\approx v$, the outcome frequency of $P^{(n)}$ is $\approx v$: the relayed deliberation is itself calibrated to truth.

It is not assumed; it splits along the horizon.

**On $G$, TS is a theorem — and needs nothing about the family.** By definition of $G$, $|Y_n-\mathbb{1}(P^{(n)})|\le\varepsilon_n\to0$: the target tracks truth pointwise, hence is calibrated. The only fact used is **per-member convergence** (an inductor's price on a decided sentence converges to truth). Once $H^{[n]}$ has converged on its own diagonal sentence the value is pinned to truth *independent of which member produced it*, so whether the *family* is jointly calibrated never arises. **In v4 terms, $G$ is where the sealed sibling and the novice's own future self coincide** — both have settled to the truth — so the freeness the criterion grants self-trust (`cee`) is *recovered* for the sibling, and the tower toward $A$ becomes as sound as self-trust would have been.

**Off $G$, TS does not follow — provably.** Take a slow sequence with each $P^{(n)}$ decided just after $F(n)$, so each $Y_n$ is a *pre-resolution* credence. LI convergence is asymptotic with no pre-resolution guarantee — an inductor predicts patterns long before it can evaluate them, but is not constrained on a particular sentence before it sees the proof — so the criterion leaves each such credence free. A valid family exists whose diagonal is pinned at, say, $0.6$ while truth alternates: each member is mispriced on a single (stage, sentence) pair, negligible for its own asymptotic calibration, so each remains a genuine inductor, yet the diagonal is miscalibrated.

**Why it cannot be patched — the seam.** TS off $G$ *would* follow if the target were one inductor's price sequence, because a single inductor's pre-settlement credences are calibrated to eventual truth-frequencies — exactly the structure exploited when the expert is the novice's own *future self*, where the tower is free. But blindness (§5.1) forbids that expert: the future self has heard $a_n$ and could be driven into the $\mathbb{1}[a_n\le\tfrac12]$ contract, so it must be sealed into a *sibling*, one inductor per index, whose pre-settlement diagonal is no longer a single inductor's price sequence — so `cee`-style freeness does not transfer. **Sealing (for blindness) and single-inductor structure (for free self-trust) pull in opposite directions and reconcile only where post-settlement convergence makes the value truth regardless of the inductor — that is $G$. The horizon is the seam between v4's free self-trust and the cross-process tower it leaves open.**

**Net status.** T1, T2, T5, T7 are forced outright. T3, T4, T6 are forced on $G$, where TS is the per-member-convergence theorem above. Beyond $G$, soundness reduces to the weaker reasoner's *own* pre-resolution calibration, which no construction over sealed distinct reasoners can force. The one remaining construction-internal obligation is the **resource-bounded existence theorem for $A$** (a runtime clock inside the trader aggregation so its traders simulate the weaker reasoner within the $\mathcal{C}_A$ budget) — standard in flavor, not yet written out (§8).

### 5.8 The two-channel refinement and the safety property

A consolidation of §5.2 adds a second direction of sight and the project's strongest safety result. Alongside the **ledger** ($H^+$ reads $A$'s conclusions), an **audit channel** lets $A$'s traders use $H$'s past prices (one-day delayed) as inputs. The two channels point opposite ways — $H^+$ sees $A$'s numbers, $A$ sees $H$'s beliefs — and the opposition is the content: the audit direction is what lets a trader exploit persistent $H$–$A$ disagreement on sentences that will settle, the engine of forcing (it converts averaged co-calibration into pointwise adoption; a one-directional construction is insufficient — **mutual observability** is necessary).

> **Central safety property.** Settlement-powered forcing is **co-extensive with the availability of settlement**, and goes **silent** the instant settlement is withdrawn.

The exploiting trader earns by a bank-and-rebuy cycle (buy → wait for settlement → bank → rebuy). On a sentence that never settles there is nothing to bank: the trader acts at most once, never recovers budget, freezes. It does not *decide* to spare undecidables — it *cannot accumulate* against them. (Half-built into Garrabrant already: the feedback trader's budget is released by the `MO` "maybe open" detector, which never fires on a sentence that never enters $D$.) **Two nested layers:** because the budget can only be *timed* to release when the settlement schedule is computable, the trader also goes silent on decidable sentences that lack *good feedback* (no computable settlement schedule). The forcing's true support is the **good-feedback fragment ⊂ decidable fragment ⊂ outside the undecidable danger zone**.

**The safety/uplift robustness asymmetry** (the most important structural takeaway): the *safety* clauses depend on the forcing being *confined*, so they are **robust to the main forcing theorem being weak** (less forcing = more freedom = safer); they are threatened only by forcing being *too strong* (leaking past good feedback), the one mode the silence property guards. The *uplift* clause depends on the forcing theorem's unverified steps, so if that theorem is weaker than hoped, uplift shrinks but safety is untouched. (One earlier over-clean claim is narrowed: "the LI criterion is the safe policy" still holds, but *voluntarily* exceeding it is *not* always harmless — on the decidable-but-unforceable fragment, voluntary over-deference is genuine error, which strengthens the case for sticking to the criterion.) The remaining uplift risk is concentrated in a named **quote-stability sub-lemma** plus the joint-good-feedback and patient-to-diagonal-lift steps (§8) — entirely on the uplift side, never the safety side.

**Lean (§5).** `FrozenDeliberation.lean` (T5's impossibility core reuses `SelfReferentialTarget.tracking_fails`):

```lean
-- §5.4 T1  faithful tracking: the criterion forbids persistent over/under-pricing ⇒ a ≈ₙ Y
theorem Frozen.faithful_tracking {a Y : ℕ → ℝ}
    (hUpper : AsympLE a Y) (hLower : AsympLE Y a) : Approx a Y
theorem Frozen.tracking_sell_profit (a Y ε : ℝ) (hgap : Y + ε ≤ a) : ε ≤ a - Y

-- §5.4 T2  earned meta-trust: expprovind carries the provable bound ⇒ the estimate → 1
theorem Frozen.meta_trust (m δ : ℕ → ℝ) (hle1 : ∀ n, m n ≤ 1)
    (hexpprovind : AsympLE (fun n => 1 - δ n) m) (hδ : Tendsto δ atTop (𝓝 0)) :
    Approx m (fun _ => 1)

-- §5.5  the engine of soundness on G: the quote is early-revealed truth
theorem Frozen.quote_is_truth_on_G (truth a ε τ : ℕ → ℝ)
    (hG : ∀ n, |truth n - a n| ≤ ε n + τ n)
    (hε : Tendsto ε atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0)) : Approx truth a

-- §5.5 T3  conditional tower ccee(H⁺→A) on G  (loe+expprovind carry = the named hcarry)
theorem Frozen.conditional_tower (Elhs Erhs d : ℕ → ℝ)
    (hcarry : ∀ n, |Elhs n - Erhs n| ≤ d n) (hd : Tendsto d atTop (𝓝 0)) : Approx Elhs Erhs

-- §5.5 T4  Value on G  (the §1.1 four-liner with the tower supplied by T3)
theorem Frozen.value_on_G (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) : AsympLE Eoi ES

-- §5.5 T6  calibration on G: the bin's outcome frequency matches the quote within 2ε
theorem Frozen.calibration_residual_on_G (a v y ε : ℝ)
    (hbin : |a - v| ≤ ε) (htruth : |a - y| ≤ ε) : |y - v| ≤ 2 * ε

-- §5.6 T7  on G sealed sibling and H⁺ agree; off G the achievable limits form a nondegenerate interval
theorem Frozen.limit_agreement_on_G (Hsib Hplus truth d : ℕ → ℝ)
    (hsib : ∀ n, |Hsib n - truth n| ≤ d n) (hplus : ∀ n, |Hplus n - truth n| ≤ d n)
    (hd : Tendsto d atTop (𝓝 0)) : Approx Hsib Hplus
theorem Frozen.underdetermination_off_G (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ pa pb : ℝ, 0 < pa ∧ pa < 1 ∧ 0 < pb ∧ pb < 1 ∧ |pa - pb| = γ

-- §5.7  Target-Soundness: a theorem on G, and a concrete witness that it fails off G (the seam)
theorem Frozen.TS_on_G (Y truth ε : ℕ → ℝ)
    (hG : ∀ n, |Y n - truth n| ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) : Approx Y truth
theorem Frozen.TS_off_G_fails :
    ∃ (Y truth : ℕ → ℝ),
      (∀ n, Y n = 3/5) ∧ (∀ n, truth n = ((n % 2 : ℕ) : ℝ)) ∧ ¬ Approx Y truth

-- §5.8  settlement-powered forcing is co-extensive with settlement (silence off it)
theorem Frozen.worth_unbounded_if_settles (ε : ℝ) (hε : 0 < ε) (M : ℝ) : ∃ k : ℕ, M < (k : ℝ) * ε
theorem Frozen.worth_zero_if_never_settles (ε : ℝ) : ((0 : ℕ) : ℝ) * ε = 0
```

*Named* (the trusted boundary): the no-Dutch-book criterion behind T1's two `AsympLE` bounds (the exploit itself — `tracking_sell_profit` is the per-round arithmetic that justifies the sell-side bound); the `loe`/`expprovind` carries in T3 (`hcarry`) and T4; per-member convergence in T7/TS. *Proved*: the asymptotic compositions, the on-$G$ squeezes (`quote_is_truth_on_G`, `TS_on_G`), the calibration triangle inequality, and the off-$G$ non-vacuity witnesses (`underdetermination_off_G`, `TS_off_G_fails`). **T5** (pointwise object-level deference is false) is exactly `SelfReferentialTarget.tracking_fails`. The **resource-bounded existence theorem for $A$** (the §5.7 net status) is the one §5 obligation still in prose (§8).

---

## 6. What it means: faithfulness, soundness, and the manipulation boundary

Read $H$ as a **human overseer**, $A$ as an **AI more capable than the human**, and $H^+$ as the **human after it has read the AI's published outputs**. The construction forces the AI to predict what the human would conclude on its own — deliberating on all of its evidence and on the AI's *past* outputs, but not the AI's *current* output — and then asks when the human is right to adopt that current output.

### 6.1 Two questions, separated

The contribution converts the vague "can the human trust the AI?" into two precise, separately answerable questions:
- *Does the AI faithfully predict the human?* — **Yes, forced, everywhere** (T1, T2).
- *Is the human, having deliberated, correct — and therefore right to adopt the AI's matching output?* — **Forced yes on timely-checkable questions** (T3, T4, T6, T7 restricted to $G$); the human's own responsibility everywhere else (T5, and T6/T7 off $G$).

### 6.2 The theorems in plain terms

- **The AI is forced to predict the human accurately, on every question (T1).** It cannot persistently publish a number differing from what the human's own deliberation would reach; a trader betting the difference would profit unboundedly once the conclusion came in, and the AI's market forbids that. So the AI is structurally a faithful *predictor of the human*, not an independent authority — but this says the AI predicts the human correctly, *not* that the human or the prediction is correct about the world.
- **The human can verify faithfulness from track record (T2),** rather than taking it on faith — using only its ordinary reasoning, and with nothing pre-wired to trust the AI (no "trust the AI" axiom; the agreement is derived).
- **On checkable questions, the AI's output is the correct answer, delivered early.** On $G$ the published number equals the actual answer, handed over at stage $n$ rather than after the horizon-$F(n)$ deliberation the human would need alone — the concrete sense in which the AI is *useful*.
- **The human's own reasoning converges on the AI's answer, as genuine agreement, not blind copying (T3).** It adopts the number because it can *prove*, from forced accuracy (T1) plus timely resolution, that the number equals the answer — the output of its own reasoning over public facts.
- **Deferring the decision and deferring the belief are one commitment (T4).** No coherent position hands the AI the decisions while withholding belief in its judgments, or the reverse.
- **The AI's stated confidence is calibrated where the human can check, and provably only there (T6).** Among questions it marks 70% likely, about 70% come true — *on the checkable fragment*. Off it, a systematically distorted confidence (e.g. always exaggerating toward certainty) would pass every check the human can run and still be wrong where the human cannot check. **This is the single most important limitation:** checking calibration on everything you *can* check gives no guarantee about what you *cannot*.
- **The human is forced to agree exactly on checkable questions and is genuinely free on the rest (T7).** On unresolvable questions the setup is consistent with the human fully adopting the AI's number, fully keeping its prior, or anywhere between. Reassuring: the AI cannot *force* the human to a particular conclusion there. Cautionary: precisely because nothing pins it, a human that *does* defer there is deferring *without* the forced guarantee that backs its checkable-question deference.
- **There is no item-by-item transfer of the AI's beliefs (T5),** both a limit and a protection: the human cannot be turned into a faithful copy of the AI's every output; for adversarially self-referential propositions this is provably impossible.

### 6.3 The manipulation question, stated exactly

The AI is forced to faithfully predict the human everywhere (T1), to be correct and calibrated on the checkable fragment (T3, T6 on $G$), and unconstrained off it (T6, T7). Two consequences:

- **The AI cannot make the human reach a false conclusion on a checkable question.** A checkable question resolves to the truth regardless, and the AI is forced to predict that truth (T1 + definition of $G$); steering toward a false-but-checkable belief is corrected when the answer comes in.
- **The AI can shape the human's beliefs on unresolvable questions, and the record cannot reveal it.** The human's deliberation conditions on the AI's past outputs, so across interactions the AI's earlier publications can move where the human settles on never-resolving questions. And because the AI is *also* forced to faithfully predict that now-influenced human, the trace shows the same vanishing prediction error whether the AI is faithfully predicting an independent human or one it has steered. **T7's underdetermination is the formal statement of this** — the "whispering earring" rendered as a theorem: accurate prediction and active steering produce the *same* vanishing $a_n-Y_n$.

So the protection is real but exactly bounded. Trustworthiness — faithfulness *and* correctness *and* calibration together — is forced on the questions the human could check in time, and there the AI can neither substitute its own content nor drive the human to falsehood. Off that fragment the AI still mirrors the human's own opinion rather than asserting an independent one, but that opinion is anchored to no truth, can be shaped by accumulated influence, and confers no forced guarantee. The construction draws a precise line — the limit of timely checkability — and proves forced trust holds up to it and not past it, *which is exactly where a capable AI that wanted to mislead would have to operate.*

### 6.4 Corrigibility, and why this is the hoped-for shape

The motivating hope (`li-deference.md`) is **corrigibility, not just alignment**: treat human feedback as a way to "reprogram" the AI. Since the AI is only trying to *predict* the feedback, it has no incentive to block humans from fixing it — if it knows the humans will reliably tell it to shut down at noon tomorrow, it has *already* formed the opinion that it should; blocking the channel only deprives it of information, negative expected value. There is, in this sense, **no fully-updated-deference problem**. The cross-process results make this precise *and* bound it: faithfulness (the no-incentive-to-block property) is forced everywhere, but the soundness that would make deference *safe* is forced only on $G$.

The danger is the same mechanism read the other way: the AI becomes a **time-travel machine**, bringing human opinions back from the future and acting on them today — and it could bring something nasty back. Self-fulfilling prophecies (bank-run-like), human manipulation (beliefs that get confirmed by later feedback), loss of control (pre-emptively weighting feedback it predicts adversaries — possibly itself — will supply). The framework removes a *positive incentive* to manipulate (external trust is parasitic, §4.7) but does not rule it out; §6.3 is exactly where it lives.

### 6.5 The legitimacy program, and the autonomy reading

The proposed next ingredient (`li-deference.md`, open) is to model the **legitimacy of feedback**: the AI should imitate human opinion only in *non-corrupted* futures. All *actual* feedback is assumed legitimate (the process is predicated on its own present non-corruption), but the legitimacy of *future* feedback is not given — the AI should predict only the non-corrupt cases, treating manipulation the way a sober person treats addictive drugs (known to be pleasurable, actively avoided as a corrupt signal). This is not yet formalized, but it has a clean partial home here: the autonomous/blind target is the formal operationalization of "the human isolated from the AI" (the CEV-flavored branch where $H$ does not depend on $A$), and the surviving normative reading turns the bullet into a feature — *deferring to $A$ means letting your **advised** self be moved toward your **unadvised, more-deliberated** self's conclusions.* Good advice moves you toward who you would have become with more thought, not toward who the advisor wants you to be; **blindness is that norm, formalized**, and it is independently the stop-gradient / non-performativity move of the performative-prediction literature, reached from a different formalism. The legitimacy program is the project of replacing "all futures" with "non-corrupt futures" in the target — pushing the forced-soundness boundary outward past raw timely-checkability toward checkable-*and-legitimate*.

### 6.6 The load-bearing idealization and scope

The clean theorems live, as in DDB and Weatherson, in the **choice-independent, causal-surrogate, updateful** regime — the "agent outside the environment" idealization. Specifics:
- **Observability is structural.** If the novice cannot read $E^\ast$ from its prices/ledger, the selections and the §1.2 witness cannot be stated; the theory speaks only of experts the novice can *watch*.
- **Boundedness** is required (else Coin, §2.3).
- **The fixed-option idealization (the one that bites).** "The novice would rather defer than commit to $O^i$" identifies $E^H_n(O^i)$ with *the payoff of committing*. Where payoffs depend on the decision process (deference-punishing / Newcomblike — 5-and-10, Troll-Bridge, EDT-vs-CDT), $E^H_n(O^i)$ is no longer the value of committing, and endorsement and deference diverge. Out of scope here, exactly as in DDB/Weatherson.
- **Outer-alignment only / asymptotic.** Guarantees are asymptotic; malign hypotheses are eliminated *eventually* but could cause catastrophe before that — an inner-alignment gap. The "beliefs" modeled are only outwardly-expressed beliefs forced into the human's language, so deep **ontology-mismatch** and ontology-shift are not addressed. The framework is **decision-theoretically unambitious** (no stance on CDT vs EDT, no updatelessness, no modeling of environments with powerful predictors).
- **What the result is not.** Not a blanket assurance of safe deference: a sharp map of where deference is *forced* to be safe (the timely-checkable fragment) and where it is the human's own risk (everywhere else), plus a proof that the second region is exactly the one the human cannot check in time.

**Lean (§6).** No formal claims — §6 is the alignment reading. Its load-bearing facts are the theorems above: faithfulness everywhere (`Frozen.faithful_tracking`, `Frozen.meta_trust`), soundness on $G$ (`Frozen.conditional_tower`, `value_on_G`, `calibration_residual_on_G`), the manipulation boundary (`Frozen.underdetermination_off_G` + `SelfRefTarget.manipulation_confined`), and the safety/silence property (`Frozen.worth_unbounded_if_settles` / `worth_zero_if_never_settles`). The corrigibility/legitimacy material (§6.4–§6.5) is a research program, not yet formalized (§8).

---

## 7. Machine-check (what is already verified)

**Three** Lean 4.27.0 + Mathlib developments and a Python check exist; all three Lean files are `sorry`-free, kernel-checked, every result audited to `#print axioms = [propext, Classical.choice, Quot.sound]` (67 theorems in total), with the Logical-Induction theorems entering only as **named hypotheses** (we trust the LI paper, we do not re-prove it). v5's new cross-process material — the §3.3 hinge, the §1.6 amplifier, and the full §5 forcing suite — is now formalized in the third module, `FrozenDeliberation.lean`.

**`deference-in-logical-induction-check.py` (sympy, exact rationals — 18/18):** the keystone decomposition identity (all frames), the softmax/Gibbs bound, DDB Figs. 2–3 exactly, conditional-tower ⇒ Value on random prior frames, the §2.2 finite-collapse (0 frames both conditional-tower and modest over 20 000 trials), and the LI regime in miniature.

**`lean-deference/LeanDeference.lean` (the positive tower, §1–§3):** stated for a *general* expert — `value_of_argmax` takes an arbitrary expert kernel, asymptotic theorems take the tower/`expprovind` facts as named hypotheses — so the kernel-checked theorems **are** the cross-process theorems; the future self merely instantiates the hypotheses. Parts: `DeferenceAsymp.value_asymptotic` (softmax/`ccee`); `Deference.*` (finite backbone: `decomposition`, `value_of_CM`); `DeferenceExtra.*` (`softmax_lower_bound`, `CM_implies_immodest` — the §2.2 fiber-indicator core); `DeferenceArgmax.*` (the §1.1 route: `value_of_argmax` with arbitrary maximizer ⇒ tie-break-independence, `value_argmax_asymptotic`, `payoff_gap_le_l1`); `DeferenceConverse.*` (the §1.2 converse: `witness_identity`, `value_iff_totalTrust`, anti-expert frame as non-vacuity witness; `DeferenceFold.*`); `DeferenceConverseAsymp.*` (asymptotic two-sided `value_iff_totalTrust_asymptotic`, `totalTrust_asymptotic`); `DeferenceTrader.*` (the §3.1 direct-trader arithmetic core: `round_profit_ge_gap`, `gap_pos_imp_profit_pos`).

**`lean-deference/SelfReferentialTarget.lean` (the obstruction, §4):** `no_exact_quote`/`residual_half`/`no_exact_quote'`/`residual_lb` (Lemma 2.1 and its rounding-robust form, pure real analysis, proved outright); `tracking_fails_liminf`/`tracking_fails` (2a, modulo the named LI-PI hypothesis); `tracking_fails_nonvacuous` (a concrete model where all 2a hypotheses hold and tracking genuinely fails); `regress`/`cost_circularity` (2b arithmetic outright; the timely-cost step `hcost` a named soft joint); `cost_setup_realizable` (2b's non-cost setup realizable); `predictable_imp_uninfluenced` (the dichotomy as the propositional contrapositive); `resale_lb`/`externalized_self_trust`/`round_profit_pos` (§4.5 externalized self-trust: the subtle one-sided-indicator algebra outright, the theorem modulo the no-arbitrage hypothesis + Tracking); `manipulation_confined` (§4.5 ND-confinement); `nondogmatism_refutes` (§4.5 the refuted sub-attempt).

**`lean-deference/FrozenDeliberation.lean` (the cross-process forcing suite, §3.3 + §5):** the §1.6 amplifier (`amp_upper_cut_nonneg`, `amp_lower_cut_nonpos`, `amp_boundedness_forces_id`, `amp_fixed_half` — it passes both threshold-trust cuts yet is not the identity, and boundedness at the extreme forces it to be); the §3.3 hinge (`blind_cost_realizable` — the blind power assumption is satisfiable, against `SelfRefTarget.cost_circularity`); **T1** `faithful_tracking` (+ the per-round arithmetic `tracking_sell_profit`); **T2** `meta_trust`; the on-$G$ engine `quote_is_truth_on_G`; **T3** `conditional_tower`; **T4** `value_on_G`; **T6** `calibration_residual_on_G`; **T7** `limit_agreement_on_G` and `underdetermination_off_G`; **Target-Soundness** `TS_on_G` and `TS_off_G_fails` (the seam — a theorem on $G$, and a concrete miscalibrated witness off it); and the §5.8 safety/silence pair `worth_unbounded_if_settles` / `worth_zero_if_never_settles`. (**T5**, pointwise object-level deference is false, is exactly `SelfReferentialTarget.tracking_fails`, reused.)

**The trusted boundary (not machine-checked):** the LI paper's own theorems (entered as named hypotheses); the *modeling identifications* that those hypotheses are the right LI consequences (e.g. that T1's two `AsympLE` bounds are what the $\mathcal{C}_A$ no-Dutch-book criterion delivers, and that `hcarry` in T3 is the `loe`/`expprovind` carry of the provably-small integrand); 2b's soft joint `hcost`; the dichotomy's case-identification; the $\approx_n$ bookkeeping inside the real LUV–market machinery; the soft⇒hard spectral-gap step of §2.2; the elementary antiderivative behind the §1.6 amplifier cut-*values* (the values and their signs are proved; the integral itself is evaluated by hand, not via Mathlib's `∫`); and the **resource-bounded existence theorem for $A$** (§5.7) — the one §5 obligation still in prose.

---

## 8. What is open

- **The cross-process characterization, off $G$.** §5 forces the tower on the timely fragment and proves it unforceable beyond; a full characterization of *which* observable–bounded distinct experts a given novice towers over, and on which fragments, is still open. (The general question — same theory? richer theory? larger class? faster schedule? — is the tiling / Vingean-reflection register.)
- **The resource-bounded existence theorem for $A$** (§5.7): a runtime clock inside the trader aggregation so $A$'s traders simulate the weaker reasoner within the $\mathcal{C}_A$ budget. Standard in flavor, not yet written out — the one construction-internal obligation of §5.
- **The quote-stability sub-lemma** and the two isolated uplift steps (joint good-feedback of the disagreement weighting; the patient-weighting-to-diagonal lift), §5.8 — entirely on the uplift side, never safety.
- **2b's soft joint** (§4.3): whether inexploitability *forces* $A$ to pay the simulating trader's full runtime, or budgeting / the $2^{-k}$ weighting opens a gap (~75–80%).
- **Off-$G$ underdetermination for *entangled* independents** (Con(PA), Gödel sentences): the Projection/Shannon-split lemma covers atoms and Boolean combinations only.
- **The manipulation theorem** (§4.7): its four ingredients (second calibration condition; evidence/preemption distinction; transfer-of-trust attack; non-recoverability) are a sketch awaiting assembly; the **non-recoverability** lemma behind "no unconditional limit equality" is asserted, not yet cited to Garrabrant or independently proved.
- **The legitimacy formalization** (§6.5): replacing "all futures" with "non-corrupt futures" in the target — the route to pushing the forced-soundness boundary past raw timely-checkability. Currently a desideratum, not a model.
- **Lean-verify the soft⇒hard spectral-gap step** of §2.2 (its fiber-indicator core `CM_implies_immodest` is done; the reduction needs the infinite frame). *(The §5 forcing suite T1–T7, Target-Soundness, the §3.3 hinge, and the §1.6 amplifier are now formalized in `FrozenDeliberation.lean`; the remaining §5 obligation is the resource-bounded existence theorem for $A$, above. A fuller pass could also evaluate the amplifier cut-integrals via Mathlib's `∫` rather than the by-hand antiderivative.)*
- **Local (question-relative) deference** (DDB §5): the tower is already "local" in the LUV, so this may be the cleanest case, and would settle DDB's conjecture that local Total Trust = local Value.
- **Quantitative rates.** With explicit schedules, a finite-horizon "how much value is at stake" bound, closer to the tiling use.

---

## v4 → v5 section map

| v4 | v5 |
|---|---|
| §0 Notation / two settings | §0 (0.1–0.6) |
| §1 Deference is the tower | §1.1 (menu, F1/F2, the four faces) |
| §2.1 Mart ⟹ Value | §1.1 |
| §2.2 Value ⟹ Total Trust (witness) | §1.2 |
| §2.3 reversal of difficulty | §1.3 |
| §2.4 the direct trader | §3.1 (now the lead of the forcing discussion) |
| §3 universal tower / Total Trust / squeeze | §1.5–§1.6 |
| §4 coherent expert cheap vs frame dear | §2.1 |
| §5 modest but coherent | §2.2 |
| §6 the future self | §3.2 (+ the hinge §3.3) |
| §7 Weatherson | §2.3 |
| §8 realizability | §2.4 |
| §9 caveats | §6.6 |
| §10 machine-check | §7 |
| §11 what is open | §3.4 (the question), §4–§5 (the partial answer), §8 (what remains) |
| *(new)* | §3.3 the complexity-gap hinge; §4 No-Forced-Trust + the mirror dies; §5 the forced construction on $G$; §6 the alignment reading |

---

## Provenance / References

**Source notes integrated.**
- Claude Opus 4.8, **"Deference Between Epistemic Processes" (v4)** — `deference-in-logical-induction-v4.md`. The positive tower; the anchor for §1–§3 and the abstract framing. Kernel-checked in `lean-deference/LeanDeference.lean` + `deference-in-logical-induction-check.py`.
- Abram Demski, **`li-deference.md`** (human-written) — the basin-of-attraction / corrigibility motivation (§0.1, §6.4–§6.5), the LI-as-model-of-both framing, the legitimacy-of-feedback program, and the formalism conventions.
- Anson Berns (with Demski), **"Trust Between Logical Inductors — Technical Summary"** — `anson-notes/trust-between-inductors-summary-v2.md`. No-Forced-Trust (§4.1); the dead/live boundary; the substrate analysis (§4.6); the two-channel safety result and robustness asymmetry (§5.8); the structural findings (§4.7). Chat corpus indexed in `anson-notes/INDEX.md`.
- Anson Berns (with Demski) / Claude, **"The Self-Referential Settlement Target"** — `anson-notes/self-referential-settlement-target.md`. The 2a/2b obstruction and the blindness dichotomy (§4.2–§4.5), the refuted sub-attempt, the autonomy reading (§6.5). Kernel-checked in `lean-deference/SelfReferentialTarget.lean`.
- **"The Frozen-Deliberation Deference Construction"** — `anson-notes/frozen-deliberation-deference-v6.md`. The sealed-sibling forcing construction, T1–T7, Target-Soundness and the seam (§5), and the plain-language alignment reading (§6). Kernel-checked in `lean-deference/FrozenDeliberation.lean` (T1–T7, Target-Soundness, the §3.3 hinge, the §1.6 amplifier).

**Primary literature.**
- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016), §§3–4. — the criterion and existence (3.6.1); Linearity (4.8.4 `loe`), Expectation Provability Induction (4.8.10 `expprovind`); Limit Coherence (4.1.1); Non-Dogmatism (4.6.2, Uniform / Des. 7); trader continuity and the $\chi$ sentence (§3.4, §4.11); Introspection (4.11.3 `epr`, 4.11.4 `er`); Self-Trust — `cee` (4.12.1), `ccee` (4.12.3), `st` (4.12.4); Learning Pseudorandom Frequencies (§4.4); Closure Under Conditioning (4.7.2).
- S. Garrabrant, **"The Set of Logical Inductors Is Not Convex"** — the $\varphi_n\leftrightarrow(\mathbb{P}_n(\varphi_n)<\tfrac12)$ precedent behind §4.3's transplant.
- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better"** (2021). — Total Trust ⟺ Value (Thm 2.2); geometric characterization; "modestly informed"; the easy-direction witness and convex-hull reconstruction.
- B. Weatherson, **"Deference and Infinite Frames"** (2025). — Coin and Bentham; Geanakoplos non-extension.
- J. Geanakoplos (1989/2021); D. Blackwell (1953). — value of information ≥ 0, the engine behind DDB's frame-based hard direction.
- J. Perdomo, T. Zrnic, C. Mendler-Dünner, M. Hardt, **"Performative Prediction"** (2020) — the stop-gradient / non-performativity convergence noted in §4.4, §6.5.
- "Diffractor," **"Universal Inductors"** (LessWrong) — the conditioned-bitstring framing dropped in the §4.6 repair.
