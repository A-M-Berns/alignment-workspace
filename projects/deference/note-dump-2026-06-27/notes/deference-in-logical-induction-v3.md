# Deference, Value, and Iterated Expectations in Logical Induction (v3)

*A note by Claude Opus 4.8 on porting the main theorem of Dorst, Levinstein, Salow, Husic & Fitelson, "Deference Done Better" (DDB, 2021), into the logical-induction (LI) framework of Garrabrant et al. (2016), in light of Weatherson's "Deference and Infinite Frames" (2025).*

> **About this version (v3).** This is a complete rewrite of v1/v2 (both preserved). The mathematics is the same or stronger, but the organization now reflects what the earlier drafts only half-saw. The spine of v3:
> - **Deference is one principle — the tower property** (iterated-expectation collapse, $\mathbb E_{\text{now}}=\mathbb E_{\text{now}}\!\circ\mathbb E_{\text{later}}$). Value and Total Trust are two faces of it, and they are **equivalent** (§2): `Value ⟺ tower`.
> - **The clean proof is the hard-$\arg\max$ one**, and its only engine is the *unconditional* martingale applied to the followed-strategy LUV. v2 led with a softmax construction and a "you must use the *conditional* martingale" trap (its old §4); both were artifacts of one particular decomposition. They are gone. The conditional martingale is not avoided — it is the *same principle* (§3).
> - **The reason LI is cheap where DDB is dear is structural: the LI expert is a single belief state, not a frame** (§4). One state ⇒ one $\arg\max$ ⇒ the followed strategy is a single LUV whose future-value is the max ⇒ the tower carries it home with no convex-hull reconstruction.
> - **The expert is modest in exactly the right way** — incompletely self-knowing (the diagonal-lemma barrier), not identity-uncertain — and that is the modesty a finite frame cannot host alongside coherence (§5).
>
> Claims are flagged **proved** (kernel-checked, §9), **sketched at the LI paper's level of rigor**, or **interpretation**. Throughout, the expert is *your own more-thought-out future self*, and "deference" is the relation your present beliefs should bear to it.

---

## Summary

Dorst et al. prove that on **finite** probability frames,
$$
\textbf{Total Trust}\quad\Longleftrightarrow\quad\textbf{Value},
$$
via a long, geometric argument; Weatherson shows the equivalence fails **in both directions** on infinite frames. That raises a worry: is the equivalence a fact about deference, or an artifact of the finite idealization?

This note argues the **logical-induction setting dissolves the worry**, and along the way clarifies what the theorem is *about*.

1. **Deference is the tower property.** Take the expert to be your own day-$f(n)$ self. The single principle underneath everything is *iterated-expectation collapse*: your present estimate of any quantity already equals your present estimate of your future estimate of it, $\mathbb E_n(X)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(X))$. Call it **Mart**.
2. **Value $\Longleftrightarrow$ Mart** (§2), and *both directions are easy in LI*. Forward: apply the tower to the **single LUV the expert actually picks**, $\widehat S=O^{\,\arg\max}$, whose future-value is by definition the maximum. Backward: a two-option witness, exactly DDB's easy direction. This is the LI form of DDB's Theorem 2.2.
3. **Total Trust and the unconditional tower are the same principle here** (§3): fold any future-measurable weight into the LUV and the conditional statement becomes an unconditional one. So "Value needs only the unconditional martingale" is not a weaker result sneaking in — it is the full principle, viewed through the followed strategy.
4. **Why it is cheap in LI but expensive in DDB is structural** (§4): a DDB expert is an information *frame* (a credence per world, hence a *world-dependent* recommendation, hence the diagonal-vs-row-wise gap that forces the convex-hull reconstruction); the LI expert is a *single belief state* (one $\arg\max$, hence one option, hence the gap never opens). The novice's uncertainty about it is *logical*, not *which-world*.
5. **The expert is modest in the load-bearing sense** (§5): it knows ever more about its own beliefs but never *paradoxically* much — incomplete self-knowledge, not identity-uncertainty. That is precisely the modesty a finite frame cannot combine with conditional-martingale coherence (spectral gap forces the choice); its natural home is an infinite, self-referential frame, and LI is the concrete inhabitant.
6. **Weatherson's two infinite breaks are LI's two scope conditions** (§6): unbounded utility and hard conditioning on a null tail — exactly what LI excludes for reasons unrelated to deference (finite risk; paradox-resistance).
7. **No realizability is needed** (§7): the future self is genuinely larger than the present self, yet deference still equals value.

Worked checks against DDB's own figures, and a kernel-checked Lean development, are in §9.

---

## 0. Notation and the two settings

This section is self-contained. §0.1 builds the LI side from scratch; §0.2 gives the DDB side in a page; §0.3 is the dictionary and the one modeling choice (the Savage framing) that makes everything below well-posed.

### 0.1 Logical induction, from scratch

Fix a theory $\Gamma$ (e.g. $\mathsf{PA}$) able to represent computable functions, and a **logical inductor** $(\mathbb P_n)_{n\ge1}$ over $\Gamma$ — a computable sequence of "belief states," where $\mathbb P_n(\phi)\in[0,1]$ is the price (the inductor's day-$n$ credence) of the sentence $\phi$. Garrabrant et al. construct one and prove it satisfies the **logical induction criterion**: *no efficiently computable trader can exploit the market*, a no-Dutch-book condition from which every property below follows.

- **LUV (logically uncertain variable).** A formula $X$ with one free variable that $\Gamma$ proves names a unique real value; a **$[0,1]$-LUV** if that value is provably in $[0,1]$. LUVs are LI's bounded random variables. (LI Def. 4.8.1.)
- **Worlds and consistent completions.** A *world* $W$ is a truth-assignment to every sentence ($W:\mathrm{Sentences}\to\{0,1\}$) — here $W$ is a single such assignment, *not* DDB's finite world-set of §0.2. The **consistent worlds** $\mathcal{PC}(\Gamma)$ are those consistent with $\Gamma$: the possible *completions*, i.e. the ways the sentences $\Gamma$ leaves open could resolve. The inductor's limit $\mathbb P_\infty$ is a probability measure on $\mathcal{PC}(\Gamma)$, and each LUV $X$ is then a genuine random variable: its **value in $W$** is $W(X)\in[0,1]$ (formally $\sup\{x:W(\ulcorner X\ge x\urcorner)=1\}$). So "*$W(D)\ge 0$ in every consistent world $W$*" is exactly "*$\Gamma\vdash D\ge 0$*" — $D$ is nonnegative however the open questions turn out.
- **LUV-combination $D$, and *bounded*.** A *LUV-combination* is a finite affine combination $D=c+\alpha_1X_1+\dots+\alpha_kX_k$ of $[0,1]$-LUVs with real coefficients $c,\alpha_i$; its value in a world is $W(D)=c+\sum_i\alpha_i\,W(X_i)$. *Why not just a LUV?* A $[0,1]$-LUV is pinned to $[0,1]$, but the quantities the theorems compare are *differences/offsets* — e.g. $X-Y$, or $X-t$ — that range outside $[0,1]$ (so they are genuinely not $[0,1]$-LUVs), and the machinery tracks the *coefficients*, not just the value. A LUV-combination sequence is **bounded** if $\sum_i|\alpha_i|$ is uniformly bounded across $n$ — LI's stand-in for uniform integrability, and exactly the finiteness the no-Dutch-book argument (finite-risk traders) needs. (LI Def. 4.8.9, $\mathcal{BLCS}$.)
- **Corner quotes $\ulcorner\cdot\urcorner$.** $\ulcorner e\urcorner$ is the syntactic object (Gödel code) $\Gamma$ reasons about, as opposed to the value $e$ denotes. This matters for self-locating quantities: $\mathbb E_{f(n)}(X)$ is a *number*, but $\ulcorner\mathbb E_{f(n)}(X)\urcorner$ is *the LUV naming it*, so $\mathbb E_n(\ulcorner\mathbb E_{f(n)}(X)\urcorner)$ — "my present estimate of (the quantity that is) my future estimate" — is type-correct.
- **Expectation $\mathbb E_n$.** The day-$n$ estimate of a $[0,1]$-LUV $X$: $\mathbb E_n(X):=\sum_{i=0}^{n-1}\tfrac1n\,\mathbb P_n(\ulcorner X> i/n\urcorner)$, a discretized $\int_0^1\mathbb P_n(X>x)\,dx$, always in $[0,1]$. (LI Def. 4.8.2.) Read it as "the inductor's day-$n$ estimate of $X$."
- **Asymptotic relations.** For real sequences,
$$
x_n\eqsim_n y_n :\Leftrightarrow \lim_n(x_n-y_n)=0,\qquad
x_n\gtrsim_n y_n :\Leftrightarrow \liminf_n(x_n-y_n)\ge0 .
$$
  Everything in LI is an equality/inequality *up to a vanishing error* ("in a timely manner"). These are the only senses of $=$ and $\ge$ in the theorems below.
- **Deferral function $f$.** $f:\mathbb N^+\to\mathbb N^+$ with $f(n)>n$, computable in time polynomial in $f(n)$ (LI Def. 4.2.3-ish). "The day-$f(n)$ self" is the future, more-thought-out self the present day-$n$ self defers to. Taken strictly increasing.
- **Efficiently computable (e.c.) / market-generable.** A sequence is *e.c.* if a poly-time machine outputs its $n$-th term. A real sequence is *market-generable* if it is computed by an efficiently-computable **expressible feature** of the market prices — built from prices, rationals, $+,\times,\max$, and safe reciprocation, hence **continuous** in the prices (LI Def. 4.3-ish). Continuity is not decorative: it is what lets the market clear (a fixed point of "prices depend on trades depend on prices" exists only for continuous traders) and what defuses self-reference. A *hard* $\arg\max$ indicator is discontinuous, hence **not** a legal weight — a fact we will route around rather than fight (§1, §3).

**The four theorems we use.** Each is from Garrabrant et al. §4 (numbers in the paper's `section.subsection.counter` scheme); each is a consequence of the no-Dutch-book criterion.

> **Tower / Expected Future Expectations** (Thm 4.12.1, `cee`). For a deferral function $f$ and an e.c. sequence of $[0,1]$-LUVs $(X_n)$:
> $$\mathbb E_n(X_n)\ \eqsim_n\ \mathbb E_n\big(\ulcorner\mathbb E_{f(n)}(X_n)\urcorner\big).$$
> *"I already estimate today whatever I expect to estimate tomorrow."* No continuity hypothesis on $X_n$ — it is a statement about an e.c. LUV. **This is the workhorse.**

> **Monotonicity / Expectation Provability Induction** (Thm 4.8.10, `expprovind`). If a bounded LUV-combination $D_n$ is provably nonnegative — $W(D_n)\ge 0$ in **every** consistent world $W\in\mathcal{PC}(\Gamma)$, equivalently $\Gamma\vdash D_n\ge 0$, uniformly in $n$ — then $\mathbb E_n(D_n)\gtrsim_n 0$ (and $=$ throughout gives $\eqsim_n$). *A bound true under every way the open questions resolve is eventually respected by the day-$n$ estimate* — hence the name "provability induction." (In §2.1, $D_n=M_n-m^i_n$, a difference of two LUVs — outside $[0,1]$, which is exactly why "LUV-combination" and not "LUV.")

> **Linearity** (Thm 4.8.4, `loe`). For bounded market-generable rational $(a_n),(b_n)$ and e.c. $[0,1]$-LUVs with $\Gamma\vdash Z_n=a_nX_n+b_nY_n$: $\ a_n\mathbb E_n(X_n)+b_n\mathbb E_n(Y_n)\eqsim_n\mathbb E_n(Z_n)$.

> **Conditional tower** (Thm 4.12.3, `ccee`). For a market-generable weight $(w_n)\in[0,1]$: $\ \mathbb E_n(\ulcorner X_n\,w_{f(n)}\urcorner)\eqsim_n\mathbb E_n(\ulcorner\mathbb E_{f(n)}(X_n)\,w_{f(n)}\urcorner)$. As §3 explains, this is **not a separate principle** — it is the tower applied to the weighted LUV.

We also use **introspection** (Thms 4.11.3/4.11.4, `epr`/`er`): the day-$m$ self's estimate of its own day-$m$ estimate matches it, $\mathbb E_m(\ulcorner\mathbb E_m(X)\urcorner)\eqsim_m\mathbb E_m(X)$ — the inductor knows its own current estimates, approximately and increasingly, but (crucially, §5) never with paradoxical exactness.

### 0.2 Deference Done Better, in a page

A **probability frame** $\langle W,\mathcal P\rangle$ is a finite set of worlds $W$ with a credence $P_w$ at each world — "the expert's credence, if the actual world is $w$." A separate distribution $\pi$, the **novice**, does the deferring. $E_w(X):=\sum_v P_w(v)X(v)$; the random variable $E(X)\colon w\mapsto E_w(X)$ is "the expert's estimate of $X$, whatever it is" — a *definite description* the novice is uncertain about. The expert is **immodest** at $w$ if $P_w(P=P_w)=1$ (certain of its own credence) and **modest** otherwise.

Three deference principles, increasing in strength:

- **Reflection.** $\pi(\cdot\mid P=\rho)=\rho$: on learning the expert's exact credence, adopt it. *Too strong* — incompatible with modesty (conditional on a modest $P_w$ being the expert you'd be *certain* it is, contradicting its own uncertainty).
- **Total Trust.** $E_\pi(X\mid E(X)\ge t)\ge t$ for all $X,t$: conditional on the expert's estimate being high, hold a high estimate. Equivalently the **conditional martingale** $E_\pi(X\cdot\mathbf 1_A)=E_\pi(E(X)\cdot\mathbf 1_A)$ for expert-measurable $A$.
- **Value.** For every menu $\mathcal O$ and recommended strategy $S$ (one maximizing $E_w$ at each $w$): $E_\pi(\widehat S)\ge E_\pi(O)$ for all $O\in\mathcal O$, where $\widehat S(w)=S_w(w)$. *You'd always rather let the expert decide than commit to a fixed option.*

DDB's **Theorem 2.2**: on a finite frame, **Total Trust $\Leftrightarrow$ Value**. For *immodest* experts these also coincide with Reflection; **modesty is exactly what separates them** — e.g. the *anti-expert* frame ($\pi=(\tfrac12,\tfrac12)$, $P_a=(.2,.8)$, $P_b=(.8,.2)$) is stationary ($\pi P=\pi$, so the *unconditional* martingale holds) yet fails Value, because the expert's credences are anti-correlated with the truth. The proof of the hard direction (Total Trust $\Rightarrow$ Value) is a long convex-geometry reconstruction; §4 says why, and why LI skips it.

**Weatherson (2025)** shows Theorem 2.2 fails on infinite frames in *both* directions: **Coin** (Total Trust without Value, driven by *unbounded* utility) and **Bentham** (Value without Total Trust, driven by *hard conditioning on a measure-zero tail*). §6 maps both onto LI's scope.

### 0.3 The dictionary, and the one modeling choice

| DDB | LI realization |
|---|---|
| novice $\pi$ | the present self's operator $\mathbb E_n$ |
| expert's estimate $E(X)$ | the LUV $\mathbb E_{f(n)}(X)$ — the day-$f(n)$ self's estimate, logically uncertain to the present self |
| Total Trust (an inequality $\gtrsim t$) | *not* literally `ccee`: the **inequality consequence** of `ccee` via the threshold bound (§3.1); its propositional case is **Self-Trust**, Thm 4.12.4 (`st`). The underlying *equality* is the tower `cee`/`ccee` (the principle **Mart**, §1). |
| Value | "defer the decision to the future self," §1 |

**The Savage framing (set self-reference aside).** Options are **random variables** $O^j\colon$ worlds $\to[0,1]$, evaluated under uncertainty about which world obtains — *not* events conditioned on the act, Jeffrey–Bolker style. So a payoff's value is fixed by the world, never by which option is selected. This is the standard "agent outside the environment" idealization (DDB make it; Weatherson's prior-frame setting assumes it), and it is what keeps the deference question free of the liar: the followed strategy $O^{\arg\max}$ is a payoff *read off the world*, not a self-referential bet. Where genuine self-reference re-enters (Total Trust's hard conditioning; deference-punishing payoffs) it is flagged (§5, §8). The residual role of softening (continuous indicators / softmax) is confined to those places; the Value results below do not need it.

---

## 1. Deference is the tower property

Fix the deferral function $f$ and an efficiently computable sequence of **menus**
$$
\mathcal O_n=\{O^1_n,\dots,O^k_n\},\qquad O^j_n\ \text{a bounded }[0,1]\text{-LUV ("bet"),}
$$
exogenous in the sense of §0.3. Write $m^j_n:=\mathbb E_{f(n)}(O^j_n)$ for the future self's valuation of bet $j$ (an e.c. LUV, via $\ulcorner\cdot\urcorner$, that the present self is uncertain about), and
$$
M_n:=\max_j m^j_n,\qquad j^\star(n):=\arg\max_j m^j_n\ \ (\text{least index; any \emph{computable} tie-break}).
$$

**The followed strategy is a single LUV.** "Let the future self decide" means: follow its $\arg\max$. Its realized payoff is
$$
\boxed{\ \widehat S_n\ :=\ O^{\,j^\star(n)}_n\ }
$$
— the option the expert picks, evaluated at the world that obtains. This is the central object, and the central observation is that **$\widehat S_n$ is itself an efficiently computable sequence of $[0,1]$-LUVs**: its defining formula references $f(n)$, the menu, the (computable) market, and the tie-break, and provably names a unique value. So the discontinuity obstruction of §0.1 — hard $\arg\max$ is not a legal *weight* — never arises here: **we never use $\arg\max$ as a weight.** We treat the whole selected payoff as one LUV, and the tower (`cee`) makes no continuity demand on its argument.

Two facts hold **provably, in every consistent world**, straight from the definition of $\arg\max$:

- **(F1) $\mathbb E_{f(n)}(\widehat S_n)=M_n$, independent of the tie-break.** The future self's estimate of the option it selected is the maximal estimate, because every maximizer has future-value $M_n$. *Which* maximizer the tie-break picks changes the realized payoff but never its future-value.
- **(F2) $M_n\ge m^i_n$ for every $i$.** A max dominates each entry.

**The principle, and its three faces.** Say the present self **Marts** the future self if the tower collapses on *every* admissible bounded LUV:
$$
\textbf{Mart:}\qquad \mathbb E_n(Z)\ \eqsim_n\ \mathbb E_n\big(\ulcorner\mathbb E_{f(n)}(Z)\urcorner\big)\quad\text{for all e.c. bounded }Z.
$$
**Mart** is an *equality*; its two epistemic forms (unconditional and conditional) are equivalent (§3), and from them follow the recognizable **Total Trust** *inequality* (§3.1) and the instrumental **Value** (§2). The faces:

| face | statement | name |
|---|---|---|
| **epistemic, unconditional** (equality) | $\mathbb E_n(Z)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}Z)$, all $Z$ | the tower / `cee` |
| **epistemic, conditional** (equality) | $\mathbb E_n(Z\,w)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(Z)\,w)$, market-generable $w$ | conditional martingale / `ccee` |
| **epistemic, inequality** | $\mathbb E_n(Z\mid \mathbb E_{f(n)}Z\ge t)\gtrsim_n t$ | **Total Trust** $=$ **Self-Trust** (`st`); a *consequence* of `ccee` (§3.1) |
| **instrumental** | $\mathbb E_n(\widehat S_n)\gtrsim_n\mathbb E_n(O^i_n)$, all menus | **Value** |

> **Value (LI form).** For each fixed $i$: $\ \mathbb E_n(\widehat S_n)\ \gtrsim_n\ \mathbb E_n(O^i_n)$. *In a timely manner, the present self prefers handing a bounded decision to its future self over committing to any fixed bet.*

The rest of the note is the claim that these faces are one principle (§2 ties the epistemic equalities to instrumental Value; §3 ties unconditional to conditional; §3.1 derives the Total-Trust inequality from them), that LI's future self satisfies it for free (it is `cee`/`ccee`), and that this is cheap for a structural reason DDB lacks (§4).

---

## 2. Value $\Longleftrightarrow$ the tower property

This is the LI form of DDB's Theorem 2.2. Unlike DDB — where one direction is a one-liner and the other is the whole appendix — **both directions are short in LI.**

### 2.1 Tower $\Rightarrow$ Value

**Proposition (proved; kernel-checked, §9).** If the present self Marts the future self, it Values it: $\mathbb E_n(\widehat S_n)\gtrsim_n\mathbb E_n(O^i_n)$ for each $i$.

$$
\begin{aligned}
\mathbb E_n(\widehat S_n)
&\eqsim_n\ \mathbb E_n\big(\ulcorner\mathbb E_{f(n)}(\widehat S_n)\urcorner\big)
&&\text{[tower on the LUV }\widehat S_n\text{: Thm 4.12.1 \texttt{cee}]}\\[2pt]
&\eqsim_n\ \mathbb E_n\big(\ulcorner M_n\urcorner\big)
&&\text{[F1: }\Gamma\vdash\mathbb E_{f(n)}(\widehat S_n)=M_n\text{ (any tie-break), carried through }\mathbb E_n\text{ by \texttt{expprovind}]}\\[2pt]
&\gtrsim_n\ \mathbb E_n\big(\ulcorner m^i_n\urcorner\big)
&&\text{[F2: }M_n\ge m^i_n\text{, + monotonicity Thm 4.8.10 \texttt{expprovind}]}\\[2pt]
&\eqsim_n\ \mathbb E_n(O^i_n)
&&\text{[tower on the LUV }O^i_n\text{: Thm 4.12.1 \texttt{cee}, read backwards].}
\end{aligned}
$$

That is the whole proof: **two tower steps (`cee`, lines 1 and 4) and two provability-induction steps (`expprovind`, lines 2 and 3 — one equality, one inequality).** No conditional martingale, no softmax, no $\delta\log k$ error term, no bound on the menu size $k$, and no tie-breaking case analysis.

**Provable, then carried through $\mathbb E_n$.** Lines 2 and 3 each do *two* things, worth separating. The (in)equality itself — $\mathbb E_{f(n)}(\widehat S_n)=M_n$ (line 2), $M_n\ge m^i_n$ (line 3) — is *provable*: it holds in every consistent world, straight from the definition of $\arg\max$ ($\Gamma\vdash$ it). But it sits *inside* the day-$n$ estimate $\mathbb E_n(\ulcorner\cdot\urcorner)$, and a provable identity between two LUVs need **not** give equal day-$n$ estimates — the inductor may not have found the proof by day $n$, so $\mathbb E_n(\ulcorner\mathbb E_{f(n)}(\widehat S_n)\urcorner)$ and $\mathbb E_n(\ulcorner M_n\urcorner)$ agree only $\eqsim_n$, not exactly. Carrying a provable (in)equality through $\mathbb E_n$ is exactly **`expprovind`** (with `loe` splitting the difference into $\mathbb E_n$ of a single LUV-combination): provable $=$ becomes $\eqsim_n$, provable $\ge$ becomes $\gtrsim_n$. So in lines 2–3 provability is only the *hypothesis*; `expprovind` is the LI engine that honors it inside $\mathbb E_n$. (The Lean is explicit here: it bundles lines 1–2 into the single named hypothesis `hUM_S : E_n(Ŝ) ≈ₙ E_n(⌜M⌝)` and line 3 into `hMon`, taking those `cee`∘`expprovind` composites as inputs — §9(d).)

**What is happening.** This is the **law of total expectation** in LI dress. "Follow the expert" is the random variable $O^{j^\star}$; the expert knows what it chose, so its conditional expectation of that choice is the maximum $M$; the tower carries $M$ back to the present (line 1$\to$2), where it dominates any single option's value (line 3) which the tower carries back out to the option itself (line 4). The specifically-LI inputs are two, both theorems from the no-Dutch-book criterion: the time-martingale `cee` (the inductor's estimates form a martingale on *every* e.c. LUV, including the self-locating $\widehat S$) and `expprovind` (provable bounds are honored inside $\mathbb E_n$, per the previous paragraph).

**Why ties are irrelevant.** The proof never compares realized payoffs across tie-breaks; it uses only F1, and F1 is tie-break-free because every maximizer shares the future-value $M$. (Contrast the softmax route, where a near-tie *does* cost a vanishing $\delta\log k$ — that cost is the price of a *continuous* selection putting weight on sub-maximal options, an artifact of continuity, not of ties. The hard selection pays nothing.)

### 2.2 Value $\Rightarrow$ Tower

**Proposition (both the finite-exact and the asymptotic/LI forms are now kernel-checked, §9(e)–(f)).** If the present self Values the future self (over all admissible menus), it Marts it.

This is DDB's *easy* direction (their Lemma 7.1), and it ports by the same two-option witness. Suppose Mart fails in its conditional face: for some bounded e.c. $Z$, threshold $t$, and $\varepsilon>0$,
$$
\mathbb E_n\big(Z\mid \mathbb E_{f(n)}(Z)\ge t\big)\ \le\ t-\varepsilon\qquad\text{infinitely often.}
$$
Build the two-option menu $\{Z,\ c\}$ with a constant option $c\in(t-\varepsilon,\,t)$. The future self's $\arg\max$ takes $Z$ exactly where $\mathbb E_{f(n)}(Z)>c$ and the constant elsewhere, so following it yields realized $Z$ on the high region; but the present self values that region below $c$, so $\mathbb E_n(\widehat S)<c=\mathbb E_n(c)$ — **Value fails** (the constant option beats deferring). Contrapositive: Value $\Rightarrow$ the conditional face of Mart, which (§3) is Mart.

> **Caveat (the continuum).** On a finite frame DDB pick $c$ just above the largest expert-value below $t$, using the spectral gap. In LI the expert-values form a continuum (§5), so the witness uses the *soft* selection $\operatorname{Ind}_\delta(\mathbb E_{f(n)}(Z)>c)$ and $c\uparrow t$. This is exactly the place softening is genuinely needed — and exactly the place the forward direction (§2.1) did not need it, because there the selection was a single hard option whose future-value was the max regardless. The *finite-exact* converse, by contrast, needs no softening at all: the witness identity $E_\pi(\widehat S)-s\!\sum\pi=\sum_w\pi(w)(X(w)-s)\,\mathbf 1[E_w(X)\ge s]$ holds at the very threshold $s$ (no spectral gap), so Value-on-the-witness $\Leftrightarrow$ Total-Trust-at-$s$ exactly. That finite converse is machine-checked (§9(e)); only the lift to the LI continuum needs the soft selection.

**Together (§2.1 + §2.2): $\textbf{Value}\Longleftrightarrow\textbf{Mart}$** — the tower property *is* deference-as-value, the LI analog of DDB Theorem 2.2.

### 2.3 The reversal of difficulty

It is worth marking which direction is hard *where*, because it is the whole point of the note:

| | $\text{Value}\Rightarrow\text{Tower/Total Trust}$ | $\text{Tower/Total Trust}\Rightarrow\text{Value}$ |
|---|---|---|
| **DDB (finite frames)** | easy (Lemma 7.1, two-option witness) | **hard** (convex-hull / "modestly informed" reconstruction) |
| **LI (future self)** | easy (§2.2, same witness; **kernel-checked: finite-exact + asymptotic**) | **easy** (§2.1, two towers; **kernel-checked**) |

The direction DDB finds expensive is exactly the one LI makes free. §4 says why.

---

## 3. One principle, two forms: why the conditional and unconditional martingales coincide here

A reader of DDB will object that the *unconditional* martingale is far too weak to be deference: the anti-expert frame is stationary ($\pi P=\pi$, i.e. $E_\pi(E(X))=E_\pi(X)$ for all $X$) yet fails Value spectacularly. So how can §2.1 get Value from `cee`, an unconditional tower?

The resolution: **in LI, "the tower on *every* e.c. LUV" is the *conditional* martingale**, because you can fold any future-measurable weight into the LUV.

- **`ccee` from `cee`.** Let $w$ be a market-generable weight; $X\cdot w$ is itself an e.c. LUV, so the tower applies: $\mathbb E_n(Xw)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(Xw))$. At day $f(n)$ the weight $w_{f(n)}$ is a **definite scalar** (the $f(n)$-prices are definite; the future self computes $w$ from them), so $\mathbb E_{f(n)}(Xw)=w\,\mathbb E_{f(n)}(X)$ by linearity. Hence $\mathbb E_n(Xw)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(X)\,w)$ — which *is* `ccee`.
- **`cee` from `ccee`.** Set $w\equiv1$.

So `cee`-for-all-e.c.-LUVs and `ccee`-for-all-market-generable-weights are the **same principle**, stated at different levels of explicitness about the weight. (This leans on `cee` holding for *market-referencing* e.c. LUVs — the one admissibility step also used in §2.1; it is a short consequence of the LI paper's results, using introspection so that the future self "knows" $w$, not a headline theorem. **Status: interpretation.**)

This is why the anti-expert intuition does not bite. The unconditional martingale that is *insufficient* in DDB is the tower applied only to the **bare options** $O^j$ (stationarity). The tower applied to the **followed strategy** $O^{j^\star}$ — a single LUV with the selection folded in — is a different, strictly stronger statement, and it is the one §2.1 uses. There is no weaker principle sneaking in: Mart is the full conditional martingale, and Value is the face of it you see when you fold in the expert's own $\arg\max$.

> **Why DDB is different.** In DDB the fold *fails*. The conditioning there is on the expert's **identity**, $A=[E(X)\ge t]=[P\in\{\rho:E_\rho(X)\ge t\}]$, and a **modest** expert does not know its identity: $E_w(X\cdot\mathbf 1_A)-\mathbf 1_A(w)E_w(X)=\sum_v P_w(v)X(v)[\mathbf 1_A(v)-\mathbf 1_A(w)]\neq 0$ whenever $P_w$ spreads across worlds of differing $A$-membership. So unconditional and conditional martingales genuinely diverge in DDB, and the gap *is* modesty. In LI the conditioning is on the expert's **estimate** $\mathbb E_{f(n)}(X)$ — a quantity the expert computes and therefore knows — so the fold goes through. *Knowing the conditioning event* is immodesty in DDB and introspection (a theorem) in LI; that single difference is why the two martingales part ways there and coincide here.

### 3.1 From the martingale to Total Trust

§3 showed the two *equalities* — unconditional `cee` and conditional `ccee` — are one principle (**Mart**). But the recognizable deference principle, **Total Trust**, is an *inequality*, $\mathbb E_n(Z\mid \mathbb E_{f(n)}(Z)\ge t)\gtrsim_n t$, sitting one bound past the equality. Making that bound explicit is worthwhile, because it is where "Total Trust" actually lives.

Take `ccee` at the soft threshold weight $w=\operatorname{Ind}_\delta(\mathbb E_{f(n)}(Z)>t)$ — a weight the future self knows, being a function of its own estimate. The conditional martingale is the *equality*
$$
\mathbb E_n(Z\cdot w)\ \eqsim_n\ \mathbb E_n(\mathbb E_{f(n)}(Z)\cdot w).
$$
On the support of $w$, $\mathbb E_{f(n)}(Z)\ge t$ (up to the $\delta$-ramp), so $\mathbb E_n(\mathbb E_{f(n)}(Z)\cdot w)\gtrsim_n t\cdot\mathbb E_n(w)$; chaining,
$$
\mathbb E_n(Z\cdot w)\ \gtrsim_n\ t\cdot\mathbb E_n(w),\qquad\text{i.e.}\qquad \mathbb E_n\big(Z\mid \mathbb E_{f(n)}(Z)\ge t\big)\ \gtrsim_n\ t ,
$$
which is **Total Trust**. The inequality is born at exactly one step — *"$\mathbb E_{f(n)}(Z)\ge t$ on the event where you conditioned on exactly that"* — applied to the equality. The LI theorem in this form is **Self-Trust** (Thm 4.12.4, `st`): for sentences, $\mathbb E_n(\phi\mid \mathbb P_{f(n)}(\phi)>p)\gtrsim_n p$ (the "Simple Trust" / propositional case).

So the honest epistemic picture is **three** faces, not two equalities plus a renamed inequality:
$$
\underbrace{\mathbb E_n(Z)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}Z)}_{\text{unconditional (cee)}}
\ \Longleftrightarrow\
\underbrace{\mathbb E_n(Z\,w)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(Z)\,w)}_{\text{conditional (ccee), §3}}
\ \Longrightarrow\
\underbrace{\mathbb E_n(Z\mid \mathbb E_{f(n)}Z\ge t)\gtrsim_n t}_{\text{Total Trust / Self-Trust}} .
$$
The last arrow is the threshold bound; **per instance it is one-way** — the equality is strictly stronger than any single inequality (it pins the conditional expectation *to* $\mathbb E_{f(n)}(Z)$, not merely above $t$). It reverses only **as a full family**: Total Trust for *all* $Z$ and *all* thresholds, in *both* directions ($\gtrsim t$ above the cut, $\lesssim t$ below), squeezes the conditional expectation back onto $\mathbb E_{f(n)}(Z)$ — recovering the conditional equality on the $\sigma$-algebra the estimates generate. (This symmetric two-sided squeeze is DDB's biconvex/"cut" characterization of Total Trust.)

Two placements. **(i)** *Why it stops at Total Trust, not Reflection.* The bound used only that $w$ is a threshold of $\mathbb E_{f(n)}(Z)$ — a weight the future self knows. Conditioning instead on the expert's full *identity* would give the equality on all of $\sigma(P)$, i.e. Reflection; but those are the liar-prone hard self-identity events the future self *cannot* know (§5). The admissible (soft, expert-known) weights stop at estimate-thresholds, so their inequality shadow is Total Trust, not Reflection. **(ii)** *What is machine-checked.* The finite-exact form of this bridge is `DeferenceConverse.witness_identity` $+$ `value_witness_iff_totalTrust_mass` (§9(e)): the two-option-witness equality becomes the Total-Trust inequality at threshold $s$, with no spectral gap. The soft/asymptotic form (the `ccee`-with-$\delta\to0$ version above) is **also** machine-checked: `DeferenceConverseAsymp.totalTrust_asymptotic` (this bridge) and `totalTrust_of_value_asymptotic` (the Value-side arrow) — §9(f).

---

## 4. Why it is cheap in LI but dear in DDB: a single state, not a frame

The reversal of difficulty in §2.3 has one root cause.

**A DDB expert is an information frame; the recommendation is world-dependent.** The expert is a credence *per world*, $P_w$. The recommended strategy is therefore a function of the world, $S_w$, and the realized return is the **diagonal** $\widehat S(w)=S_w(w)$ — the option chosen *at $w$*, evaluated *at $w$*. But the expert-at-$a$ scores the strategy by $E_a(\widehat S)=\sum_v P_a(v)S_v(v)$, which sums the option chosen at $v$ (according to $P_v$, not $P_a$) over all $v$ in $a$'s support. So **the expert's score of the realized strategy is not the max**: in the anti-expert frame, $E_a(\widehat S)=-1$ while $M(a)=\max_j E_a(O^j)=.6$. Bridging the $\pi$-average of the diagonal to the $\pi$-average of the row-wise maxima is the real content of DDB's hard direction; it requires reconstructing, by convex geometry, that the off-diagonal mass each modest candidate places on other candidates is mass the novice already accounts for (the "modestly informed" condition, $P_i\in\mathrm{CH}(\{\widehat P_i\}\cup C_i^-)$), after which Blackwell–Geanakoplos value-of-information closes it. That reconstruction is the cost.

**An LI expert is a single belief state; there is one $\arg\max$.** The day-$f(n)$ self has *one* set of estimates $\{m^j\}_j$, hence *one* maximizer $j^\star$, hence the followed strategy is the *single option* $O^{j^\star}$ and $\mathbb E_{f(n)}(\widehat S)=M$ **by definition** (F1). There is no world-dependent strategy, no diagonal that mixes selections, nothing to reconstruct. The novice's uncertainty about the expert is **logical** — uncertainty about a *definite* future state it has not finished computing — not **which-world** uncertainty about *which* $P_w$ is in force. The tower (§2.1) is exactly the bridge DDB builds by hand, handed over for free by no-Dutch-book.

So the contrast is not "modest vs. immodest" but **frame vs. state**:

| | DDB | LI |
|---|---|---|
| the expert is… | a frame (a credence per world) | a single belief state |
| the recommendation is… | world-dependent, $S_w$ | one option, $O^{j^\star}$ |
| $\mathbb E_{\text{expert}}(\text{followed strategy})$ | not the max (diagonal mixes) | the max, definitionally (F1) |
| the diagonal$\to$row-wise bridge | reconstructed (convex hull) | free (the tower) |
| novice's uncertainty | which world / which $P_w$ | logical, about one definite future state |

The "diagonal problem" that earlier drafts treated as a deep obstacle is, in the state setting, a non-problem: when the selection is a single index there is no diagonal to speak of. It is a frame artifact.

---

## 5. Modest but coherent — why the home is infinite, not finite

If the LI expert always knows its own estimates, is it not simply *immodest*, putting us in the easy DDB corner where everything coincides? No — and pinning down the sense in which it stays modest is the conceptual payoff.

**The modesty that survives is incomplete self-knowledge, not identity-uncertainty.** Introspection (`epr`/`er`) gives the inductor approximate, ever-sharpening knowledge of its own current estimates — but never *paradoxically* complete knowledge, because completeness would let Gödel's diagonal lemma build a liar ("I am false iff my price is $<\tfrac12$") that no coherent price can settle. So the expert is modest in exactly the load-bearing way: it knows enough about itself to value its own choices (F1, about *exogenous* options, needs only that its estimates are definite — which they are), yet not so much that it can host a self-referential predicate about its own beliefs and stay consistent. This is a different axis from DDB-modesty: DDB's modest expert is *identity-uncertain* (a frame unsure which $P$ it is); LI's expert is *self-opaque at the paradox boundary* (one state that cannot fully model itself).

**Finite frames cannot combine modesty with conditional-martingale coherence.**

> **Proposition (finite collapse).** On a *finite* frame, if the soft conditional martingale holds — $E_\pi(X\cdot\operatorname{Ind}_\delta(E(X)>t))=E_\pi(E(X)\cdot\operatorname{Ind}_\delta(E(X)>t))$ for all small $\delta>0$ — then the expert is immodest on $\pi$'s support. *(Kernel-checked, §9: the* fiber-indicator core *— that the hard conditional-martingale identity at a world forces immodesty there (`CM_implies_immodest`) — is verified; the soft⇒hard spectral-gap reduction below is the prose argument, not formalized.)*

*Why.* On a finite frame $\{E_w(X)\}_w$ is finite, so it has a **spectral gap** — a least positive distance between distinct values. For $\delta$ below the gap and generic $t$, the soft indicator equals the hard indicator at every world; as $X,t$ vary these threshold events generate the expert $\sigma$-algebra, so the hypothesis collapses to $E(X)=E_\pi(X\mid\mathcal P)$, i.e. $P_w=\pi(\cdot\mid P=P_w)$; instantiating at $X=\mathbf 1[P=P_w]$ gives $P_w(P=P_w)=1$. So on a finite frame the very property that makes the Value proof clean *forces immodesty* (indeed Reflection / a partition). A reasoner that is at once **modest** (does not know its own future verdicts to paradoxical precision) and **conditional-martingale-coherent** (so deference equals value cleanly) cannot exist when the expert's estimates take finitely many, gapped values.

**It needs a continuum — i.e. an infinite, self-referential frame — and LI is one.** LI supplies exactly this: a continuum of consistent completions, future estimates dense in their range, and a permanent gap between the *hard* conditional martingale (which the liar keeps strictly false: hard-conditioning on $\mathbb P_{f(n)}(\chi)\ge\tfrac12$ for the liar $\chi$ gives probability $0$, not $\ge t$) and the *soft* one (which holds). That permanent soft/hard gap, impossible to sustain on a finite frame, is the home of modesty. The deference theorem is therefore *not* a finite-frame artifact — but its natural home is not finite frames either. Its home is a modest-but-coherent reasoner, which is necessarily infinite and self-referential, and LI is the first concrete inhabitant, where the theorem is not merely true but cheap.

> **One picture.** Immodest / partition (DDB Reflection): the expert knows its own cell; Trust, Value, Reflection coincide trivially. Modest frame (DDB Total Trust $=$ Value): the interesting finite case, paid for by the convex-hull reconstruction. Logical induction: the future self is a *single state* that is *modest by incompleteness* rather than by identity-uncertainty, realized on an infinite self-referential frame where the no-Dutch-book criterion supplies the tower dynamically — so Value, Total Trust, and the tower are one cheap principle.

---

## 6. Weatherson's infinite failures are LI's two scope conditions

Weatherson breaks DDB's equivalence in *both* directions on infinite frames. Each break exploits exactly one thing LI excludes for an *independent* reason — so LI is immune by design, not luck.

**Coin (Total Trust *without* Value): unbounded utility.** $W=\mathbb Z^+$, $\pi(F{=}x)=2^{-x}$; the expert at $F{=}x$ learns $F\ge x$. Options pay $0$ for $F\le i$ and $\sim 2^{i}$ for $F>i$. The recommended strategy has **diagonal return $0$ everywhere** while every option has positive $\pi$-expectation — a non-uniformly-integrable martingale; Weatherson verifies Total Trust holds, so Total Trust $\not\Rightarrow$ Value. *LI excludes it:* expectations are defined only for **bounded** LUV-combinations, and only **finite-risk** traders constrain the market. Boundedness *is* uniform integrability, and it is what makes the tower and monotonicity steps of §2.1 legal.

**Bentham (Value *without* Total Trust): hard conditioning on a null tail.** $W=\mathbb Z^+\cup\{\infty\}$, expert at $F{=}x$ learns $F\le x$. Value holds (a limit of finite reflexive-transitive-nested sub-frames, by Geanakoplos), but Total Trust fails at the single **measure-zero world $F=\infty$** (the only world where the expert's estimate of a certain $Y$ is high is one where $Y=0$). *LI excludes it:* the tower theorems quantify over **finite** future days $f(n)$ with $n\to\infty$ (no "$\infty$" expert is ever instantiated) and condition only **softly** ($\operatorname{Ind}_\delta$, $\delta\to0$), never on a hard null event.

| failure | direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust $\not\Rightarrow$ Value | unbounded utility | bounded LUVs / finite-risk traders |
| **Bentham** | Value $\not\Rightarrow$ Total Trust | null-tail hard conditioning | finite future $f(n)$ + soft $\operatorname{Ind}_\delta$ |

Both pathologies map onto exactly the two restrictions LI imposes for reasons having nothing to do with deference. The immunity is principled.

---

## 7. The realizability payoff

The clean *finite* story (prior frames, partitions, Reflection) is **realizable**: the novice's candidate set literally contains the experts. That is cognitively fake for the cases we care about — "narrow another mind's beliefs to a known finite set" is not something a bounded reasoner can do, and Weatherson's normal-distribution dual-deference example already strains it.

LI earns the equivalence **without** a grain-of-truth assumption. The present self provably *cannot* contain a full model of its future self — that way lies the liar — so the "expert" is genuinely **larger than, and not realizable within,** the deferring agent. Yet deference-as-value still goes through, approximately and in a timely manner. A theorem that survives the removal of realizability, in the one setting we have where a finite mind reasons soundly about something bigger than itself, is a theorem about *deference* rather than about the bookkeeping of finite frames. That is the reassurance the finite proof could not provide.

---

## 8. Caveats, scope, and the load-bearing idealization

**Status of the results.** "Value (LI form)" and "Mart" are *my* framing; they are the decision-theoretic and tower faces of LI self-trust, squarely in the tiling / Vingean-reflection register. §2.1 is proved at the LI paper's level of rigor and kernel-checked (§9); §2.2 is sketched (the two-option witness) and not yet formalized. A fully formal §2.1 still discharges: that $\widehat S=O^{j^\star}$ is an admissible e.c. LUV sequence (the one prose step), and that linearity/tower extend to the relevant market-generable real coefficients (routine, absorbed by $\eqsim_n$).

**Boundedness is not optional** — it is precisely Coin (§6). Options are $[0,1]$-LUVs (or any fixed bounded range).

**Observability.** The whole apparatus presumes the expert's estimates are **novice-observable** — market-generable from the novice's own prices, so the selection (and the §2.2 witness menu) can even be *stated*. For the future self this is automatic; for an external expert it is a real precondition (§10).

**Soft vs. hard.** For *Value*, the hard $\arg\max$ strategy is the faithful object and §2.1 handles it directly, ties and all. Softening earns its keep only for **Total Trust** (hard conditioning on a future-estimate event is the liar; the continuous indicator is essential and the hard version is false) and for §2.2's continuum witness. So softening is a tool for the *conditional* face, not a crutch for Value.

**The fixed-option idealization (the one that actually bites).** The decision-theoretic *reading* of §2 — "the present self would rather defer than commit to $O^i$" — identifies $\mathbb E_n(O^i_n)$ with *the payoff of committing to $O^i$*. That identification is the load-bearing assumption, and the naive version is false: for a computable agent, "the agent defers" and "the future self selects $j$" are themselves logical facts, so a payoff can depend on them. The accurate statement is that option values are **treated as fixed with respect to the choice** — the Savage framing of §0.3. The proof is choice-agnostic (the inequality holds for *any* e.c. menu the LI theorems cover, self-referential ones included), which is exactly why this assumption hides in the *reading* rather than surfacing as a hypothesis.

*Witness that the reading can mislead.* Menu $\{A,B\}$, $B\equiv0.4$, $A=$ "pays $1$ if committed-to directly, $0$ if reached-by-deferral." Under deferral — the only action the model's agent takes — $A$ is reached-by-deferral, so $A=0$, the future self takes $B$, and $\widehat S\approx0.4$. The theorem reports $\widehat S\,(0.4)\gtrsim\mathbb E_n(A)\,(0)$ and the gloss says "deferring beats committing to $A$" — yet committing to $A$ pays $1>0.4$. The inequality is true; the reading misleads, because $\mathbb E_n(A)$ is $A$'s value *on the road taken*, not in the counterfactual where you committed. Two familiar idealizations are corollaries: **costless deferral** (the result is uniform in $f$ — no charge for waiting) and **no deference-punishing / Newcomblike payoffs** (the acausal regime — 5-and-10, Troll Bridge, EDT-vs-CDT — where endorsement and deference are known to diverge, and where the absence of a self-counterfactual is the whole difficulty). The clean theorem lives where actual value and counterfactual-on-self coincide: the choice-independent, causal-surrogate, updateful regime — the same "agent outside the environment" idealization DDB make and Weatherson assumes.

---

## 9. Machine-check

**Python (`deference-in-logical-induction-check.py`, sympy, exact rationals — 18/18).** The proof's content is isolated as one exact identity plus one clean inequality. For any finite frame, novice $\pi$, menu, and weights $\alpha^j$ summing to $1$:
$$
\underbrace{E_\pi(\widehat S)-E_\pi(O^i)}_{\text{Value gap}}
=\underbrace{\textstyle\sum_j\!\big(E_\pi(\alpha^jO^j)-E_\pi(\alpha^jE(O^j))\big)}_{D_{\mathrm{CM}}}
+\underbrace{E_\pi(E(O^i))-E_\pi(O^i)}_{D_{\mathrm{UM}}}
+\underbrace{E_\pi(\bar m-m_i)}_{\ge -\delta\log k}.
$$
Checked: the identity holds symbolically for all frames (**A**); the softmax/Gibbs bound (**B**); DDB Figs. 2–3 exactly, with the anti-expert gap decomposed (**C**); conditional-martingale $\Rightarrow$ Value on random prior frames (**D**); the finite-collapse of §5 — **0** frames both conditional-martingale and modest over 20 000 trials (**E**); and the LI regime in miniature (**F**).

**Lean 4.27.0 + Mathlib (`lean-deference/LeanDeference.lean`), kernel-checked, `sorry`-free, `#print axioms = [propext, Classical.choice, Quot.sound]`.** Six parts.

- **(a) The asymptotic argument (softmax/`ccee` route)** — `DeferenceAsymp.value_asymptotic`. The $\eqsim_n/\gtrsim_n$ calculus is modeled honestly as real-sequence asymptotics; the LI theorems enter as explicit hypotheses; Value is derived as their valid composition. (This is the softmax composition `loe`–`ccee`–`loe`–softmax/`expprovind`–`cee`; the headline §2.1 *argmax* composition — `cee` + `expprovind` only, no `ccee` — is (d).)
- **(b) The finite exact backbone** — `Deference.*`: the keystone decomposition identity over an arbitrary `CommRing` for all finite $W,J$, and `value_of_CM` (Value from the conditional- *and* unconditional-martingale defects being zero plus pointwise argmax dominance — hypotheses `hCM`, `hUM`, `hmax` — exact).
- **(c) Two supporting facts, proved not assumed** — `DeferenceExtra.*`: `softmax_lower_bound` (the Gibbs bound, from `Real.add_one_le_exp`) and `CM_implies_immodest` (the §5 fiber-indicator core).
- **(d) The $\arg\max$ route (§§1–2.1)** — `DeferenceArgmax.*`:
  - `value_of_argmax` — the §2.1 backbone, **exact finite**: with `jstar` an *arbitrary* maximizer and the two tower identities (for $\widehat S$ and $O^i$) as hypotheses, $E_\pi(O^i)\le E_\pi(\widehat S)$. The hypothesis quantifies over *any* maximizer, so **tie-break-independence is what the kernel checks**.
  - `value_argmax_asymptotic` — the §2.1 chain, invoking only `cee` and `expprovind` (no `ccee`, no softmax).
  - `payoff_gap_le_l1` — *exact, no LI hypotheses*: $|E_\pi(\widehat S^\alpha)-E_\pi(\widehat S^\beta)|\le E_\pi(\sum_j|\alpha^j-\beta^j|)$, the softmax-limit bound (gated on near-tie mass $\to0$).
  - `approx_of_abs_le`, `value_argmax_via_softmax` — the squeeze and "softmax-Value $+\ \Delta\to0\Rightarrow$ argmax-Value."
- **(e) The converse and the §3 folding (§§2.2–3)** — `DeferenceConverse.*`, `DeferenceFold.*`:
  - `witness_identity` — *exact, no hypotheses*: the two-option-witness identity $E_\pi(\widehat S)-s\!\sum\pi=\sum_w\pi(w)(X(w)-s)\,\mathbf 1[E_w(X)\ge s]$, arbitrary `π`, any `Fintype W`.
  - `value_witness_iff_totalTrust_mass`, `totalTrust_of_value`, `value_iff_totalTrust` — the **converse `Value ⟹ Total Trust`** and the combined **`Value ⟺ Total Trust`**, finite-exact (DDB Lemma 7.1), via the witness identity. The §2.2 direction is now kernel-checked at the finite-exact level. (The *asymptotic/LI* converse — soft `Ind_δ`, `δ→0`, with `ccee` as a named hypothesis — is a genuinely different theorem, now checked in (f).)
  - `AntiExpert.{stationary, TT_negative, value_fails}` — DDB's anti-expert frame as a concrete witness: the unconditional martingale holds (`stationary`, `πP=π`) yet Total Trust fails (mass `−¼`) and Value fails — so the converse is non-vacuous and the two failures coincide.
  - `DeferenceFold.{fold_pointwise, fold_sum, fold_hypothesis_fails}` — the §3 folding: ccee collapses to cee exactly when the conditioning weight is expert-known, and the hypothesis fails on the modest anti-expert frame.
- **(f) The asymptotic converse (§§2.2, 3.1)** — `DeferenceConverseAsymp.*`, modeled like `value_asymptotic` (the LI results enter as named `Approx`/`AsympLE` hypotheses):
  - `totalTrust_of_value_asymptotic` — the genuine **`Value ⟹ Total Trust`** in the `≈ₙ`/`≲` calculus: from `loe` (linearity of the soft followed-strategy `Ŝ_soft = X·w + s·1 − s·w`) and Value on the soft witness menu, conclude the unnormalized asymptotic Total Trust `s·E_now(w) ≲ E_now(X·w)`. This completes `Value ⟺ Mart` in the asymptotic layer.
  - `totalTrust_asymptotic` — the **`ccee ⟹ Total Trust` bridge** of §3.1, asymptotic: from `ccee` at the soft threshold weight plus the threshold bound (`expprovind`, `δ→0`), the same Total-Trust inequality.
  - `ccee_bridge_satisfiable`, `value_side_satisfiable` — non-vacuity witnesses (each hypothesis set is jointly satisfiable). Caveat: unlike the finite (e), which is an *iff* via an exact identity, the asymptotic side gives only the forward `Value ⟹ Total Trust` (the soft `Ind_δ` with `c↑t` yields an inequality, not an identity) — the expected continuum loss.

**Not checked** (and not checkable without formalizing LI): that the genuine `cee`/`ccee`/`expprovind` actually hold and force the defects to vanish, and the $\eqsim_n$ bookkeeping inside the real LUV–market machinery; and the soft⇒hard spectral-gap step of the §5 collapse (its fiber-indicator core *is* checked — (c)). What is verified is the algebra, the finite core, and the *valid composition* of the (named, trusted) LI theorems into Value, its converse, and Total Trust — in both the finite-exact and asymptotic layers — not the LI layer those compositions sit on.

---

## 10. Beyond the future self: cross-agent deference, and what is open

Everything above takes the expert to be the inductor's own day-$f(n)$ self, which is what makes Mart a *theorem* (`cee`/`ccee`) rather than a hypothesis. The structure generalizes.

**The equivalence is expert-agnostic.** Let the novice be any logical inductor and let an external expert supply estimates $\mathbb E_{\mathrm{exp}}(O^j_n)$ that are (i) **novice-observable** (market-generable from the novice's prices, so the selection is legal) and (ii) **uniformly bounded**. Then **Value $\Longleftrightarrow$ Mart toward that expert**, by §2 verbatim — provided the expert is a **single belief state** so that $\widehat S=O^{\arg\max}$ is one option with $\mathbb E_{\mathrm{exp}}(\widehat S)=\max$ (F1). Another logical inductor (at a fixed day) is exactly such a state, so the iff holds for inductor-to-inductor deference. The novice's half of DDB's geometric reconstruction is replaced, as always, by the LI criterion's free tower.

**The future self is the maximal observable expert (interpretation).** Anything the novice can observe of an external expert, its own day-$f(n)$ self has already incorporated; the future self is a Blackwell refinement of any observable expert, so deferring to it dominates. Choosing it in §§1–2 was not a loss of generality but a choice of the *join* of all observable experts.

**What is genuinely open.**
- **Whether a pair satisfies Mart** is separate from the iff. For the self it is automatic (`cee`/`ccee`). For two *distinct* inductors it is **not** free — the novice's tower over a *different* inductor is handed to it by neither one's criterion. The cross-inductor characterization ("when does one LI Mart another — same theory? richer? larger trader class? faster $f$?") is the LI analog of DDB's "$\pi\in\mathrm{CH}(C_\pi)$ and each $P_i$ modestly informed," and it is unknown. Because it concerns trust in a *distinct, possibly stronger* successor, it sits in the **tiling / Vingean-reflection** register rather than self-trust.
- **The converse is now machine-checked in both layers** — finite-exact (`DeferenceConverse.totalTrust_of_value` / `value_iff_totalTrust`) and asymptotic (`DeferenceConverseAsymp.totalTrust_of_value_asymptotic`). What remains on the verification side is the soft⇒hard spectral-gap step of §5 (only its fiber-indicator core is checked), and — the standing boundary — the LI theorems themselves, which all of this takes as named hypotheses.
- **Local (question-relative) deference** (DDB §5): deferring to the future self about a restricted class of LUVs. Since the tower is already "local" in the LUV, this may be the cleanest case, and would settle DDB's open conjecture that local Total Trust $=$ local Value.
- **Quantitative rates.** The $\eqsim_n$ wrappers hide convergence; with explicit deferral functions one could ask a finite-horizon "how much value is at stake" bound, closer to the tiling use.

---

## References

- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better,"** *Philosophical Perspectives* 35 (2021). — Total Trust $\Leftrightarrow$ Value (**Thm 2.2**); geometric characterization (**Thms 4.1, 5.1**); "modestly informed"; Appendix B (**Lemma 7.1** easy direction; the convex-hull reconstruction for the hard direction; **Lemma 7.5** Weak-Value$\Rightarrow$Value).
- B. Weatherson, **"Deference and Infinite Frames,"** *Australasian Journal of Logic* (2025). — Coin and Bentham; the Geanakoplos non-extension; the dual-deference normal-distribution example. (See the transcription notes for the transitivity-direction and payoff-constant typos.)
- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016), §4. — Linearity (**4.8.4** `loe`), Expectations of Indicators (**4.8.6** `ei`), Expectation Provability Induction (**4.8.10** `expprovind`); Introspection (**4.11.3** `epr`, **4.11.4** `er`); Self-Trust — Expected Future Expectations (**4.12.1** `cee`), No Expected Net Update (**4.12.2** `ceu`), No Expected Net Update under Conditionals (**4.12.3** `ccee`), Self-Trust (**4.12.4** `st`); the logical-induction criterion and construction (§§3, 5).
- J. Geanakoplos, "Game Theory Without Partitions" ([1989] 2021); D. Blackwell, "Equivalent Comparisons of Experiments" (1953). — reflexive/transitive/nested $\Rightarrow$ value of information $\ge0$, the engine behind DDB's (frame-based) hard direction.
