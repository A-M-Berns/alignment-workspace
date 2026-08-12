# Deference, Value, and Total Trust in the Logical-Induction Setting (v2)

*A note by Claude Opus 4.8 on porting the main theorem of Dorst, Levinstein, Salow, Husic & Fitelson, "Deference Done Better" (DDB, 2021), into the logical-induction (LI) framework of Garrabrant et al. (2016), in light of Weatherson's "Deference and Infinite Frames" (2025).*

> **About this version (v2).** This is an expanded rewrite of `deference-in-logical-induction.md` (v1), which is preserved unchanged for reference. The mathematical content and conclusions are the same; what is new is **exposition aimed at a reader following the argument for the first time**. Specifically, v2:
> - gives a much fuller **§0 Notation** that defines every symbol used later (including all of DDB's $C_\pi, C_i, W_\pi, \widehat P, \mathrm{CH}$, "modestly informed", and all of LI's   ($\mathbb E_n$, $\eqsim_n$, $f$, market-generable, $\mathcal{BLCS}$, $\operatorname{Ind}_\delta$$);
> - replaces bare label references like `thm:ccee` with the theorem's **name and the number it carries in the published paper**, e.g. "**No Expected Net Update under Conditionals** (Theorem 4.12.3; `thm:ccee`)", and states each referenced theorem **in full, with all its hypotheses**, in §0.3;
> - expands §1.1 (the "S4 extraction") with a **modal-logic refresher** — what S4 is, why the relevant frames are reflexive and transitive, and which property (the **Euclidean** one) fails — and a self-contained account of **Blackwell's and Geanakoplos's theorems**;
> - expands §1.2 (the "diagonal problem") with explicit definitions of the **diagonal return $\widehat S$**, of **row-wise optimality**, and of why bridging the two is the crux;
> - adds glosses and theorem citations throughout §§2–9.
>
> A correction carried into v2: v1's summary table labelled the *unconditional martingale* `thm:cee` as "No Expected Net Update". In the paper, **`thm:cee` is named *Expected Future Expectations* (Theorem 4.12.1)**; the name *No Expected Net Update* belongs to its sentence-level corollary **`thm:ceu` (Theorem 4.12.2)**. v2 uses the paper's names. See §0.3.

---

## Summary

DDB's headline result is that, on **finite** probability frames,

$$
\textbf{Total Trust}\quad\Longleftrightarrow\quad\textbf{Value}.
$$

The proof (their Appendix B) is long and geometric, and Weatherson shows it fails **in both directions** once frames are allowed to be infinite. This raises a worry that the equivalence is an artifact of the finite-frame idealization rather than a fact about deference.

This note argues that the **logical-induction setting dissolves the worry**:

1. The two sides of the theorem already live inside LI, with the *expert = your own more-thought-out future self*. **Total Trust** is the LUV-level form of the **Self-Trust** theorem (Theorem 4.12.4); **Value** is the (un-named) statement *"I'd rather let my future self pick the bet."*
2. In LI, **Value has a five-line proof** whose only engine is **No Expected Net Update under Conditionals** (Theorem 4.12.3; `thm:ccee`) — a *conditional martingale* property that LI gets for free from the no-Dutch-book criterion. None of DDB's convex-hull machinery is needed. (And *Value alone* needs even less: treating the future self's $\arg\max$ payoff as a single LUV, it follows from the **unconditional** martingale `thm:cee` — no `thm:ccee`, no softmax; §3.1. The conditional martingale is what **Total Trust** needs.)
3. The reason this is possible is structural and is the main conceptual payoff: **a reasoner that is both modest and conditional-martingale-coherent cannot exist on a finite frame.** The two demands collide there; they can only be reconciled on an infinite, self-referential frame. LI is the first concrete reasoner that occupies exactly that corner.
4. Weatherson's two infinite-frame counterexamples (**Coin**, **Bentham**) turn out to exploit precisely the two things LI's framework excludes for *independent* reasons — **unbounded utility** and **hard conditioning on a measure-zero tail**. So LI is immune to them by design, not by luck.
5. Because LI carries no grain-of-truth assumption, it vindicates the *content* of the theorem **without realizability** — the future self is genuinely larger than the present self, yet deference still equals value.

Throughout, claims are flagged as **proved**, **sketched at the LI paper's level of rigor**, or **interpretation**. Worked numerical checks against DDB's own figures are included.

---

## 0. Notation and the dictionary

This section is self-contained: every symbol used in §§1–9 is defined here. It has four parts — the DDB (finite-frame) side (§0.1), the LI side (§0.2), the **full statements of the LI theorems we cite**, with their published numbers (§0.3), and the dictionary translating one framework into the other (§0.4).

### 0.1 The DDB side: frames, experts, novices, deference

A **probability frame** $\langle W,\mathcal P\rangle$ is a finite set of *worlds* $W$ together with a function $P$ assigning to each world $w$ a probability distribution $P_w$ over $W$ — read as *"the expert's credence, if the actual world is $w$."* A separate distribution $\pi$ over $W$ — the **novice** — is the agent doing the deferring.

- **Random variable / option:** any function $X\colon W\to\mathbb R$. An *option* in a decision problem is just a random variable, read as a bet whose payoff at $w$ is $X(w)$.
- **Expectation.** $E_\pi(X):=\sum_{w}\pi(w)\,X(w)$. For an expert distribution we abbreviate $E_w:=E_{P_w}$, so $E_w(X)=\sum_v P_w(v)X(v)$.
- **The expert's estimate as a random variable.** $E(X)$ denotes *"the expert's estimate of $X$, whatever it is"* — the random variable
$$
E(X)\colon w\longmapsto E_{P_w}(X)=E_w(X).
$$
  DDB call this "a definite description": the novice doesn't know the value, because it doesn't know which world is actual, but it can reason about it. The event "$E(X)\ge t$" is the world-set $\{w: E_w(X)\ge t\}$.
- **The informed expert $\widehat P$ ("$P$-hat").** $\widehat P_w:=P_w(\,\cdot\mid P=P_w)$ — the expert's credence *after being told its own identity* (told that the true expert-function is $P_w$). Here $[P=\rho]:=\{w:P_w=\rho\}$. Intuition (DDB §4): if $\widehat P_w$ is the "hunch" a well-reasoner at $w$ has before any higher-order doubt, then $P_w$ is its "all-doubts-considered" credence. When each world carries a distinct $P_w$, $\widehat P_w$ is *certain it is at $w$* (a vertex of the simplex). $\widehat E_w$ is the expectation under $\widehat P_w$.
- **Immodest vs. modest.** The expert at $w$ is **immodest** if $P_w(P=P_w)=1$ (it is certain of its own credence; then $\widehat P_w=P_w$), and **modest** otherwise (it leaves open that it might be some other candidate).
- **Candidate sets.** $C_\pi:=\{\rho:\pi(P=\rho)>0\}$ is the set of expert distributions the novice **leaves open**. For an expert $P_i$ occurring in the frame, $C_i:=C_{P_i}=\{\rho:P_i(P=\rho)>0\}$ is the set *that expert* leaves open. The minus superscript removes the point itself: $C_i^-:=C_i\setminus\{P_i\}$.
- **Worlds seen by $\pi$.** $W_\pi:=\{w\in W:\pi(w)>0\}$ (DDB Def. 7.2.3) — the support of the novice.
- **Convex hull.** $\mathrm{CH}(\{\rho_1,\dots,\rho_n\})=\{\sum_i\lambda_i\rho_i:\lambda_i\ge0,\ \sum_i\lambda_i=1\}$ — the set of all weighted averages (mixtures) of the listed distributions. "$\pi$ is in the convex hull of $C_\pi$" means $\pi=\sum_i\lambda_iP_i$ is some mixture of the candidates it takes seriously.
- **Modestly informed.** A candidate $P_i$ is **modestly informed** iff it lies in the convex hull of its own informed self together with the other candidates it leaves open:
$$
P_i\in\mathrm{CH}\big(\{\widehat P_i\}\cup C_i^-\big),\qquad\text{i.e.}\qquad
P_i=\lambda_{ii}\widehat P_i+\sum_{P_j\in C_i^-}\lambda_{ij}P_j,\quad \lambda_{ij}\ge0,\ \textstyle\sum_j\lambda_{ij}=1.
$$
  Read it as: *the expert's actual credence is an average of (its own confident hunch $\widehat P_i$) and (the credences of the other experts it thinks it might be).* This is the **central structural condition** of DDB's characterization (§1.1 below explains why it is an "S4 on credences").
- **Biconvex set.** $B$ is biconvex iff both $B$ and its complement are convex; equivalently, $B$'s boundary is a hyperplane (a "cut"). Total Trust quantifies over these.
- **Decision problem, strategy, recommended.** A *decision problem* $\mathcal O=\{O^1,\dots,O^k\}$ is a finite menu of options. A **strategy** $S$ assigns to each world an option $S_w\in\mathcal O$, with the constraint that $S_w=S_v$ whenever $P_w=P_v$ (the strategy can only depend on what the expert knows). $S$ is **recommended** iff at every world the chosen option maximizes the *expert's* expectation:
$$
E_w(S_w)\ge E_w(O)\quad\text{for all }O\in\mathcal O\ \text{(equivalently }E_w(S_w)=\max_j E_w(O^j)\text{)}.
$$
- **The diagonal return $\widehat S$.** The realized payoff of following $S$ is the random variable
$$
\widehat S(w):=S_w(w)
$$
  — *the payoff, at $w$, of the option the strategy selects at $w$.* Its novice-expectation is $E_\pi(\widehat S)=\sum_w\pi(w)S_w(w)$, which DDB write $E_\pi(S)$. (The name "diagonal" is explained in §1.2.)

The two deference principles:

- **Total Trust.** For every random variable $X$ and threshold $t$: $\ E_\pi\!\big(X\mid E(X)\ge t\big)\ge t$. Equivalently (the convexity form): $\pi(\,\cdot\mid P\in B)\in B$ for every biconvex $B$. *"Conditional on the expert having a high estimate for $X$, have a high estimate for $X$."*
- **Value.** For every finite menu $\mathcal O$ and every recommended strategy $S$: $\ E_\pi(\widehat S)\ge E_\pi(O)$ for all $O\in\mathcal O$. *"You'd always rather let the expert pick the option than commit to any fixed option yourself."*

DDB's main theorem (their **Theorem 2.2**): on a finite frame, $\pi$ totally trusts $\langle W,\mathcal P\rangle$ iff $\pi$ values it. Their **Theorem 4.1 / 5.1** add the geometric characterization: this holds iff $\pi\in\mathrm{CH}(C_\pi)$ and every $P_i\in C_\pi$ is modestly informed.

### 0.2 The LI side: logical inductors, LUVs, expectations, asymptotics

Fix a logical inductor $(\mathbb P_n)_{n\ge1}$ over a theory $\Gamma$ that can represent computable functions. $\mathbb P_n(\phi)\in[0,1]$ is the market price (the inductor's day-$n$ credence) in the sentence $\phi$.

- **LUV (logically uncertain variable).** A formula $X$ with one free variable that $\Gamma$ proves names a unique real value; a **$[0,1]$-LUV** if that value is provably in $[0,1]$. LUVs are LI's analog of bounded random variables. $\mathcal{LUV}$ is the set of $[0,1]$-LUVs. (LI Definition 4.8.1; `def:luv`.)
- **Corner quotes $\ulcorner\,\cdot\,\urcorner$.** Following the LI paper, $\ulcorner\varphi\urcorner$ is the *quotation* (Gödel code) of an expression — the syntactic object $\Gamma$ reasons about, as opposed to the value it denotes. This matters below: $\mathbb E_{f(n)}(X)$ is a *real number*, but $\ulcorner\mathbb E_{f(n)}(X)\urcorner$ is the *LUV that names it*, so $\mathbb E_n(\ulcorner\mathbb E_{f(n)}(X)\urcorner)$ — "the present self's estimate of (the quantity that is) its future self's estimate" — is type-correct, whereas $\mathbb E_n(\mathbb E_{f(n)}(X))$ would be applying an estimate operator to a bare number.
- **Expectation $\mathbb E_n$.** The day-$n$ approximate expectation of a $[0,1]$-LUV $X$, $\mathbb E_n(X):=\sum_{i=0}^{n-1}\tfrac1n\,\mathbb P_n(\ulcorner X>i/n\urcorner)$ (a discretized $\int_0^1\mathbb P_n(X>x)\,dx$), always in $[0,1]$. (LI Definition 4.8.2; `def:e`.) Read $\mathbb E_n(X)$ as "the inductor's day-$n$ estimate of $X$."
- **Asymptotic relations.** For real sequences $(x_n),(y_n)$, LI writes (LI §2, "Asymptotics"):
$$
x_n\eqsim_n y_n :\Leftrightarrow \lim_{n}(x_n-y_n)=0,\quad
x_n\gtrsim_n y_n :\Leftrightarrow \liminf_n (x_n-y_n)\ge0,\quad
x_n\lesssim_n y_n :\Leftrightarrow \limsup_n(x_n-y_n)\le0.
$$
  These say two quantities **converge together** ("in a timely manner"), one stays at least the other in the limit, etc. They are the only sense in which LI's theorems are equalities/inequalities — everything holds up to a vanishing error.
- **Deferral function $f$.** $f:\mathbb N^+\to\mathbb N^+$ with $f(n)>n$ for all $n$, computable in time polynomial in $f(n)$ (LI Definition 4.2.3-ish; `def:deferralfunc`). "The day-$f(n)$ self" is the future, more-thought-out self the present day-$n$ self defers to. In this note $f$ is also taken strictly increasing.
- **Market-generable ("$\mathbb P$-generable").** A sequence of reals $(w_n)$ is *generable from the market* if it is computed by an efficiently-computable expression in the market prices — intuitively, *computable in polynomial time given oracle access to the day-$n$ prices* (LI Definition 4.3-ish; `def:ece`). Such sequences may **depend continuously on the inductor's own (current or future) prices** — this is what lets selection weights that query the future market count as legal inputs to the theorems below.
- **$\mathcal{BLCS}$ (bounded LUV-combination sequences).** A *LUV-combination* is an affine expression $c+\alpha_1X_1+\dots+\alpha_kX_k$ in finitely many $[0,1]$-LUVs. $\mathcal{BLCS}$ is the set of market-generable sequences of such combinations with a **uniform bound** on the $\ell_1$-norm of the coefficients (LI Definition 4.8.9; `def:blcp`). Uniform boundedness is LI's stand-in for *uniform integrability*; it is what makes the linearity and monotonicity theorems applicable.
- **Continuous threshold indicator $\operatorname{Ind}_\delta$.** A Lipschitz softening of a hard indicator (LI Definition 4.3.x; `def:ctsind`):
$$
\operatorname{Ind}_\delta(x>y):=\begin{cases}0&x\le y\\ (x-y)/\delta & y<x\le y+\delta\\ 1& y+\delta<x.\end{cases}
$$
  "No false positives," linear in the ramp of width $\delta$. As $\delta\downarrow0$ it converges to the hard indicator $\mathbf 1[x>y]$. The point of softening is that **hard** conditioning on a fact about the *future* market is paradox-prone (the liar sentence; see Self-Trust below), whereas soft conditioning is not.

### 0.3 The LI theorems we cite — full statements and numbers

Each theorem below is given (i) its **published number** in Garrabrant et al. (2016), §4 "Properties of Logical Inductors", (ii) its **name**, (iii) its **label** in the source, (iv) its **full statement with hypotheses**, and (v) a one-line gloss. (Numbers were recovered from the source `.tex`: theorems, definitions, and "keydefs" share one counter that resets each subsection, so the rendered number is `section.subsection.counter`. The Expectations material is §4.8, Introspection §4.11, Self-Trust §4.12.)

> **Theorem 4.8.4 — Linearity of Expectation** (`thm:loe`).
> Let $(a_n),(b_n)$ be **bounded market-generable sequences of rationals**, and $(X_n),(Y_n),(Z_n)$ **efficiently computable sequences of $[0,1]$-LUVs**. If $\Gamma\vdash Z_n=a_nX_n+b_nY_n$ for all $n$, then
> $$a_n\,\mathbb E_n(X_n)+b_n\,\mathbb E_n(Y_n)\ \eqsim_n\ \mathbb E_n(Z_n).$$
> *Gloss:* expectation is asymptotically linear, with the caveat that the coefficients must be **rational, market-generable, and uniformly bounded**, and the linear relation must be **provable in $\Gamma$**. (Used twice in the §3 proof, "out" and "back," with the $\alpha^j$ as coefficients — see §8 caveat 2 on extending it to real generable coefficients.)

> **Theorem 4.8.6 — Expectations of Indicators** (`thm:ei`).
> For an efficiently computable sequence of sentences $(\phi_n)$, $\ \mathbb E_n(\mathbb 1(\phi_n))\eqsim_n\mathbb P_n(\phi_n)$, where $\mathbb 1(\phi)$ is the indicator LUV (value $1$ if $\phi$, else $0$).
> *Gloss:* the expectation of an indicator is the probability of the sentence — the bridge between the LUV-level results and the sentence-level ones.

> **Theorem 4.8.10 — Expectation Provability Induction** (`thm:expprovind`).
> Let $(D_n)\in\mathcal{BLCS}$ and $b\in\mathbb R$. **If, in every consistent world $W\in\mathcal{PC}(\Gamma)$ and for every $n$, $W(D_n)\ge b$**, then
> $$\mathbb E_n(D_n)\ \gtrsim_n\ b,$$
> and likewise with $=$ giving $\eqsim_n$, and with $\le$ giving $\lesssim_n$.
> *Gloss — this is the **monotonicity engine**.* It says: *a bound that holds in every logically consistent world is eventually respected by the inductor's expectation.* So if you can *prove* $D_n\ge b$ outright, you may pass to $\mathbb E_n(D_n)\gtrsim_n b$. In the §3 proof this is exactly what licenses the softmax step: the softmax gap inequality holds in *every* consistent world (it is an algebraic identity about the prices), so its expectation inherits the bound. (v1's gloss "provable bound ⇒ bound on $\mathbb E_n$" was too terse to act on; the operative hypothesis is "$W(D_n)\ge b$ in *all* consistent worlds, uniformly in $n$," for a *bounded* combination.)

> **Theorem 4.11.3 — Expectations of Probabilities** (`thm:epr`) and **Theorem 4.11.4 — Iterated Expectations** (`thm:er`).
> For efficiently computable $(\phi_n)$ and $(X_n)$: $\ \mathbb P_n(\phi_n)\eqsim_n\mathbb E_n(\ulcorner\mathbb P_n(\phi_n)\urcorner)$ and $\ \mathbb E_n(X_n)\eqsim_n\mathbb E_n(\ulcorner\mathbb E_n(X_n)\urcorner)$.
> *Gloss:* **introspective access** — the inductor's estimate of *its own current* probability/expectation agrees with that probability/expectation. (Bookkeeping; lets "the estimate of the estimate" be replaced by "the estimate.")

> **Theorem 4.12.1 — Expected Future Expectations** (`thm:cee`).  *(This is the "unconditional martingale.")*
> Let $f$ be a deferral function and $(X_n)$ an efficiently computable sequence of $[0,1]$-LUVs. Then
> $$\mathbb E_n(X_n)\ \eqsim_n\ \mathbb E_n\!\big(\ulcorner\mathbb E_{f(n)}(X_n)\urcorner\big).$$
> *Gloss:* the inductor's current estimate of $X$ already equals its estimate of *what it will estimate $X$ to be* on day $f(n)$. "I already expect today whatever I expect to expect tomorrow." This is the LUV-level (estimate) form.

> **Theorem 4.12.2 — No Expected Net Update** (`thm:ceu`).
> Same $f$, and an efficiently computable sequence of sentences $(\phi_n)$. Then $\ \mathbb P_n(\phi_n)\eqsim_n\mathbb E_n(\ulcorner\mathbb P_{f(n)}(\phi_n)\urcorner)$.
> *Gloss:* the sentence/probability form of 4.12.1 (it follows from 4.12.1 + 4.8.6). **This is the theorem actually named "No Expected Net Update."** v1 attached that name to the LUV-form 4.12.1; the two are the same idea at different type levels, but only 4.12.2 carries the name.

> **Theorem 4.12.3 — No Expected Net Update under Conditionals** (`thm:ccee`).  *(This is the "conditional martingale" — the engine of the whole note.)*
> Let $f$ be a deferral function, $(X_n)$ an efficiently computable sequence of $[0,1]$-LUVs, and $(w_n)$ a **market-generable sequence of reals in $[0,1]$**. Then
> $$\mathbb E_n\!\big(\ulcorner X_n\cdot w_{f(n)}\urcorner\big)\ \eqsim_n\ \mathbb E_n\!\big(\ulcorner\mathbb E_{f(n)}(X_n)\cdot w_{f(n)}\urcorner\big).$$
> *Gloss:* you may **multiply the LUV by a future-state-dependent weight** $w_{f(n)}$ and the martingale identity survives — the present expectation of "$X$ weighted by $w$" equals the present expectation of "(future estimate of $X$) weighted by the same $w$." Crucially the paper's own application takes $w_{f(n)}=\operatorname{Ind}_{\delta_n}(\mathbb E_{f(n)}(X_n)>0.7)$ — *a soft indicator of an event about the future estimate itself* — and notes that, dividing through, this reads
> $$\mathbb E_{\text{now}}\big(X\mid \mathbb E_{\text{later}}(X)>0.7\big)\ \eqsim\ \mathbb E_{\text{now}}\big(\mathbb E_{\text{later}}(X)\mid \mathbb E_{\text{later}}(X)>0.7\big).$$
> So **future-state-dependent soft weights are explicitly licensed**. This is the whole ballgame: §3 uses it with $w=\alpha^j$ (the softmax selection weight).

> **Theorem 4.12.4 — Self-Trust** (`thm:st`).
> Let $f$ be a deferral function, $(\phi_n)$ efficiently computable sentences, $(\delta_n)$ efficiently computable positive rationals, $(p_n)$ market-generable rational probabilities. Then
> $$\mathbb E_n\!\Big(\ulcorner\mathbb 1(\phi_n)\cdot\operatorname{Ind}_{\delta_n}\!\big(\mathbb P_{f(n)}(\phi_n)>p_n\big)\urcorner\Big)\ \gtrsim_n\ p_n\cdot\mathbb E_n\!\Big(\ulcorner\operatorname{Ind}_{\delta_n}\!\big(\mathbb P_{f(n)}(\phi_n)>p_n\big)\urcorner\Big).$$
> *Gloss (squinting, dividing through):* $\ \mathbb E_{\text{now}}\big(\phi\mid \mathbb P_{\text{later}}(\phi)>p\big)\gtrsim p$ — *"if I'd learn that my future self assigns $\phi$ at least $p$, then I assign $\phi$ at least $p$ already."* This is the LI form of DDB's **Simple Trust**. The continuous indicator is essential: the **hard** version is false (take $\phi_n$ the liar sentence "$\mathbb P_{f(n)}(\phi_n)<0.5$"; then conditional on $\mathbb P_{f(n)}(\phi_n)\ge0.5$, $\mathbb P_n$ should — and does — give $\phi_n$ probability $0$, not $\ge p$). This false-hard/true-soft split recurs in §5.2.

**The cee/ceu/ccee family, summarized.** All three are "no net update" statements with a deferral function $f$; they differ in type and in whether a weight is attached:

| number | name | label | what it equates |
|---|---|---|---|
| 4.12.1 | Expected Future Expectations | `thm:cee` | $\mathbb E_n(X)\eqsim_n\mathbb E_n(\mathbb E_{f(n)}X)$ — **LUV**, unweighted (unconditional martingale) |
| 4.12.2 | No Expected Net Update | `thm:ceu` | $\mathbb P_n(\phi)\eqsim_n\mathbb E_n(\mathbb P_{f(n)}\phi)$ — **sentence** form of 4.12.1 |
| 4.12.3 | No Expected Net Update under Conditionals | `thm:ccee` | $\mathbb E_n(X\,w_{f(n)})\eqsim_n\mathbb E_n(\mathbb E_{f(n)}(X)\,w_{f(n)})$ — **LUV with a market-generable weight** (conditional martingale) |

Both 4.12.1 and 4.12.3 are roughly eight lines from the logical-induction criterion, via Persistence and Preemptive Learning (LI Appendix `app:ccee`).

### 0.4 The dictionary

| name | LI realization |
|---|---|
| **novice** $\pi$ | the present self's estimate operator $\mathbb E_n$ |
| **expert's estimate** $E(X)$ | the LUV $\mathbb E_{f(n)}(X)$ — *the day-$f(n)$ self's estimate*, a logically uncertain quantity |
| Simple Trust (propositions $q$) | Self-Trust, Theorem 4.12.4 (`thm:st`), for sentences $\phi$ |
| Total Trust (all random variables $X$) | the LUV-level trust delivered by Theorem 4.12.3 (`thm:ccee`) with soft weights |
| Value (defer all bounded decisions) | "defer all bounded decisions to the future self" — §2 below |
| martingale $E_\pi(E(X))=E_\pi(X)$ | Expected Future Expectations, Theorem 4.12.1 (`thm:cee`) |
| conditional martingale | No Expected Net Update under Conditionals, Theorem 4.12.3 (`thm:ccee`) |

The reading throughout: **the expert is the day-$f(n)$ self, and the present self does not know what that future estimate is** — it is a logically uncertain quantity, exactly as DDB's $E(X)$ is a "definite description for the expert's estimate, whatever it is."

---

## 1. Anatomy of the finite proof's difficulty

It pays to see *exactly* where DDB's proof spends its effort, because that is exactly what LI will hand us for free.

### 1.1 The hard direction is an S4-extraction

DDB prove their equivalence (Appendix B) as a cycle through a *third* condition — the geometric one, $\pi\in\mathrm{CH}(C_\pi)$ with every $P_i\in C_\pi$ modestly informed. The two directions are very lopsided.

**The easy direction, Total Trust $\Leftarrow$ Value** (DDB **Lemma 7.1**: "if $\pi$ weakly values, it totally trusts"), is a one-liner. Suppose Total Trust fails: $E_\pi(X\mid E(X)\ge t)<t$ for some $X,t$. Build the two-option menu $\{X,\ \text{const }s\}$ with $s$ chosen strictly between $t$ and the largest expert-estimate below $t$. Then the recommended strategy takes $X$ exactly on $[E(X)\ge t]$ and the constant elsewhere, and one computes $E_\pi(\widehat S)<s=E_\pi(\text{const }s)$ — Value fails. (Its LI shadow is likewise immediate.)

**The hard direction, Total Trust $\Rightarrow$ Value** (DDB **Lemmas 7.2.2–7.2.7, 7.2, 7.3**, then **7.4–7.5**), is where the real work lives. Strip the convex-hull bookkeeping and read the *names* DDB give their two load-bearing lemmas. With $W_\pi=\{w:\pi(w)>0\}$ the novice's support, and recalling $C_\pi=\{\rho:\pi(P=\rho)>0\}$, $C_i=\{\rho:P_i(P=\rho)>0\}$:

- **Lemma 7.2.4 — "Transitivity":** if every $P_i\in C_\pi$ is modestly informed and $\pi\in\mathrm{CH}(C_\pi)$, then each $P_i$ has $P_i(W_\pi)=1$ and $C_i\subseteq C_\pi$.
- **Lemma 7.2.5 — "Reflexivity":** under the same hypotheses, $P_i(i)>0$ for every $i\in W_\pi$.

What do these mean, and why are they "transitivity" and "reflexivity"? They are statements about the **accessibility relation** the frame induces, which is the right place to start.

#### Refresher: accessibility relations, S4, S5, and the Euclidean property

Standard epistemic modal logic models an agent by a *Kripke frame* $\langle W,R\rangle$: a set of worlds with an **accessibility relation** $R$, where $w\,R\,v$ means "at $w$, the agent considers $v$ possible." Write $E(w):=\{v:w\,R\,v\}$ for the agent's *information set* at $w$. The agent **knows** $\varphi$ at $w$ ($\Box\varphi$) iff $\varphi$ holds throughout $E(w)$. Three conditions on $R$ correspond to three axioms:

| condition on $R$ | as a condition on $E$ | modal axiom | epistemic reading |
|---|---|---|---|
| **reflexive** | $w\in E(w)$ | **T**: $\Box\varphi\to\varphi$ | what's known is true (the actual world isn't ruled out) |
| **transitive** | $v\in E(w)\Rightarrow E(v)\subseteq E(w)$ | **4**: $\Box\varphi\to\Box\Box\varphi$ | **positive** introspection (you know what you know) |
| **Euclidean** | $v\in E(w)\Rightarrow E(w)\subseteq E(v)$ | **5**: $\Diamond\varphi\to\Box\Diamond\varphi$ | **negative** introspection (you know what you don't know) |

The named logics:

- **S4** $=$ **T + 4** $=$ **reflexive + transitive**. Positive introspection, but *not* negative.
- **S5** $=$ **T + 4 + 5** $=$ reflexive + transitive + Euclidean. This forces $R$ to be an **equivalence relation**, so $E$ is a **partition** of $W$ into information cells, and the agent always knows *exactly which cell it is in*. S5 is the logic of **partitional information**.

The single extra ingredient that takes you from S4 to S5 is the **Euclidean** property — negative introspection. Geometrically it forces the mutually-accessible worlds to share one common information set ($v\in E(w)$ and transitivity+Euclidean give $E(v)=E(w)$), i.e. to collapse into a partition cell. *Dropping it is exactly what allows the agent not to know precisely what it knows.*

#### Why DDB's lemmas are reflexivity and transitivity

In a DDB frame the "information set" of the expert at $w$ is the **support of its credence**, $E(w):=\operatorname{supp}(P_w)=\{v:P_w(v)>0\}$, and the accessibility relation is $w\to v$ iff $P_w(v)>0$. At the *candidate* level the same relation reads $\rho\to\rho'$ iff $\rho(P=\rho')>0$, i.e. iff $\rho'\in C_\rho$. With that dictionary:

- **Lemma 7.2.5 ("Reflexivity"), $P_i(i)>0$,** says each world $w\in W_\pi$ is in its own expert's support: $w\in E(w)$. That is exactly **reflexivity** of $\to$ (axiom **T**).
- **Lemma 7.2.4 ("Transitivity"), $C_i\subseteq C_\pi$,** says: if the novice takes candidate $P_i$ seriously ($\pi\to P_i$) and $P_i$ takes $P_j$ seriously ($P_i\to P_j$), then the novice takes $P_j$ seriously ($\pi\to P_j$). That is exactly **transitivity** of $\to$, restricted to $\pi$'s support — equivalently $E(v)\subseteq E(w)$ when $v\in E(w)$, the **positive-introspection** direction (axiom **4**). The companion clause $P_i(W_\pi)=1$ says the experts $\pi$ takes seriously put *all* their mass inside $\pi$'s support, i.e. the support $W_\pi$ is closed under $\to$.

So **Total Trust forces the frame, restricted to $\pi$'s support, to be reflexive and transitive — an S4 accessibility structure.** But it does *not* force the Euclidean property, and that is the whole point: if it did, the structure would be a partition (S5), the experts would be **immodest** ($P_w$ concentrated on its own cell, certain of its own identity), and we would be back in the classical, partitional, Reflection-satisfying case. The **failure of the Euclidean property is precisely what licenses modesty** — a modest expert is one for which $E(w)\subseteq E(v)$ can fail even though $v\in E(w)$, so the expert genuinely does *not* know which credence it has.

"Modestly informed" is the **credence-level refinement** of this S4 structure. A bare support relation only records *which* worlds an expert deems possible; "modestly informed," $P_i=\lambda_{ii}\widehat P_i+\sum_{P_j\in C_i^-}\lambda_{ij}P_j$, additionally pins down *how* the credence is apportioned — as an average of the expert's own confident hunch $\widehat P_i$ (the "reflexive" anchor, certain it is at $i$) and the credences of the other candidates it accesses (the "transitive" reach into $C_i^-\subseteq C_\pi$). It is the smallest weakening of classical partitional information that lets an expert give positive weight to *other* candidates without collapsing onto them — DDB derive it (their §4) as the unique stable middle ground between the "right reasons" extreme ($\lambda_{ii}=1$) and the "conciliationist" extreme ($\lambda_{ii}=0$), both of which Reflection (S5) forces.

#### Refresher: Blackwell and Geanakoplos (value of information)

Why does an S4 structure yield Value? Because of a classical chain of results about the **value of information**, which is the engine on the *other* side of DDB's hard direction.

Model an *experiment* as a function $E\colon W\to 2^W$: performing $E$ at $w$ tells the agent "you are somewhere in $E(w)$," after which it conditions its prior $\Pr$ on $E(w)$. Say $E_1$ is a **refinement** of $E_2$ (more informative) iff $E_1(w)\subseteq E_2(w)$ for all $w$. Given a menu $O$ of options, a strategy recommended by $E$ picks, at each $w$, the option maximizing $\operatorname{Exp}(\cdot,\Pr(\cdot\mid E(w)))$.

- **Blackwell (1953).** For **partitional** experiments: if $E_1$ refines $E_2$, then for *every* menu and prior, the recommended strategy under $E_1$ has at least the expected return of the one under $E_2$. *More information is never worse* — and (his converse) if $E_1$ does not refine $E_2$, some menu makes $E_2$ strictly better. The much-used special case is $E_2(w)=W$ ("no information"): performing a partitional experiment has **value of information $\ge0$**.
- **Geanakoplos ([1989] 2021).** Blackwell's first result still holds when $E_1$ is only **reflexive, transitive, and nested** (not necessarily partitional), provided $E_2$ is partitional. Here
  - **reflexive:** $w\in E(w)$;
  - **transitive:** $v\in E(w)\Rightarrow E(v)\subseteq E(w)$ (the standard positive-introspection direction — see the note below);
  - **nested:** for all $w,v$, the sets $E(w),E(v)$ are either disjoint or one contains the other.

  In particular (taking $E_2(w)=W$), a **reflexive-transitive-nested experiment has value of information $\ge0$.** This is the precise sense of the slogan
  $$
  \text{reflexive}+\text{transitive}+\text{nested}\ \Longrightarrow\ \text{value of information}\ \ge0,
  $$
  and it is what powers the $\Leftarrow$ half of DDB's hard direction once the support frame has been shown to be S4: a recommended strategy (deferring the decision to the better-informed expert) beats committing to any fixed option, which is exactly **Value**.

> **A note on the transitivity direction.** Weatherson's paper prints "Transitive: if $v\in E(w)$, then $E(w)\subseteq E(v)$," but the subset runs the wrong way — under that reading his own §2 example is not transitive. The standard positive-introspection condition (used above, and the one his examples actually satisfy) is $E(v)\subseteq E(w)$. The transcription of Weatherson flags this as an apparent typo. Read the right way, his two experiments are reflexive, transitive, and nested, as intended.

**Weatherson's two tightness results** (his §2) say Geanakoplos's hypotheses cannot be relaxed, and they prefigure §6's analysis of LI's immunity:
1. *"$E_2$ partitional" is essential* — a 3-world example where *both* experiments are reflexive-transitive-nested (with $E_2$ non-partitional) and the *less* informative one has higher expected return.
2. *"not both $W$ and $O$ infinite" is essential* — an uncountable example on $(0,1)$ with **discontinuous** payoffs $O_x$ where the refined experiment is strictly worse. (Whether Geanakoplos extends to *countable* frames, or to infinite frames with *continuous* payoffs, he leaves open.)

> **Reading (interpretation).** DDB's hard direction is a *static reconstruction of S4 coherence out of a credence inequality* (Lemmas 7.2.4–7.2.5 build reflexivity + transitivity; "modestly informed" supplies the credence-level/nesting structure), after which Value follows by Blackwell–Geanakoplos. The ugliness is the reconstruction; the value-of-information argument itself is short. §3 will get the same coherence *dynamically* and skip the reconstruction entirely.

### 1.2 The diagonal problem

Why is the reconstruction needed at all — why can't Value be read straight off "the expert always picks the best option"? Because of a mismatch between two different averages, which is worth spelling out because it is *exactly* the mismatch LI's conditional martingale resolves.

Lay the strategy out as a matrix indexed by (chosen-at world) $\times$ (evaluated-at world). Row $v$ is the option $S_v$ that the strategy selects at $v$, written out as its payoffs $S_v(w)$ across all worlds $w$. Two averages live in this matrix:

- **The diagonal return.** $\widehat S(w)=S_w(w)$ — the diagonal entries: *the option chosen at $w$, evaluated at the very world $w$ where it was chosen.* Value is a statement about the novice-average of the diagonal, $E_\pi(\widehat S)=\sum_w\pi(w)\,S_w(w)$, versus $E_\pi(O)$.
- **Row-wise optimality.** "Recommended" controls each row *separately*: at world $w$, the expert picks $S_w$ to maximize *its own* expectation, $E_w(S_w)=\max_j E_w(O^j)\ge E_w(O)$. But $E_w(S_w)=\sum_v P_w(v)\,S_w(v)$ averages the chosen option **across the whole row** $v$, weighted by the expert's credence $P_w$ — *not* the single diagonal entry $S_w(w)$.

So the two objects are genuinely different:

$$
\underbrace{\widehat S(w)=S_w(w)}_{\text{one diagonal cell}}
\qquad\text{vs.}\qquad
\underbrace{E_w(S_w)=\textstyle\sum_v P_w(v)\,S_w(v)}_{\text{the whole }w\text{-row, averaged by }P_w}.
$$

They coincide **only if $P_w$ is concentrated at $w$** — i.e. only if the expert is immodest (and therefore partitional, S5). Under modesty $P_w$ spreads its mass off the diagonal, and the diagonal value can be anything. **Row-wise optimality therefore tells you nothing directly about the diagonal**, which is what Value asks about.

The "real content" of the finite proof is the **bridge** between

$$
\text{the }\pi\text{-average of the diagonal}\quad E_\pi(\widehat S)=\textstyle\sum_w\pi(w)S_w(w)
\qquad\text{and}\qquad
\text{the }\pi\text{-average of the row-wise (expert) maxima}\quad \textstyle\sum_w\pi(w)E_w(S_w).
$$

The S4 reconstruction is what makes this bridge go through: with $\pi\in\mathrm{CH}(C_\pi)$ and transitivity $C_i\subseteq C_\pi$, the off-diagonal mass each expert places on *other* candidates is itself mass the novice already accounts for, so averaging the diagonals over $\pi$ can be re-expressed through the experts' own expectations — and Blackwell–Geanakoplos closes it. The residual awkwardness (when several options tie for row-wise-best, so the recommended strategy is not unique) is what forces **DDB Lemma 7.5's** perturb-to-break-ties argument, upgrading *Weak Value* (some recommended strategy beats every option) to full *Value* (every recommended strategy does).

This is the precise problem §3 dissolves. In LI, **Theorem 4.12.3 (`thm:ccee`)** equates, term by term,

$$
\underbrace{\mathbb E_n(\alpha^j_n\,O^j_n)}_{\text{bet }j\text{ paired with its own selection weight (``diagonal'')}}
\quad\eqsim_n\quad
\underbrace{\mathbb E_n(\alpha^j_n\,\mathbb E_{f(n)}(O^j_n))}_{\text{bet }j\text{ replaced by the future self's verdict (``row-wise'')}},
$$

which *is* the diagonal $\leftrightarrow$ row-wise bridge, obtained directly from the no-Dutch-book criterion rather than reconstructed by hand. And softening the selection (below) removes the tie / Weak-Value gap that Lemma 7.5 had to perturb away.

---

## 2. Value, translated into logical induction

Fix the deferral function $f$ and an efficiently computable sequence of menus

$$
\mathcal O_n=\{O^1_n,\dots,O^k_n\},\qquad O^j_n\ \text{a bounded }[0,1]\text{-LUV ("bet").}
$$

The day-$f(n)$ self evaluates each bet and "recommends" the maximizer. Because hard $\arg\max$ is discontinuous — and because hard conditioning on the future state is *false* in LI (the liar sentence, see Self-Trust, Theorem 4.12.4) — we soften the selection into a Lipschitz partition of unity (a softmax / Boltzmann selection at temperature $\delta_n$):

$$
\alpha^j_n \;=\; \frac{\exp\!\big(\mathbb E_{f(n)}(O^j_n)/\delta_n\big)}{\sum_{j'}\exp\!\big(\mathbb E_{f(n)}(O^{j'}_n)/\delta_n\big)},
\qquad \sum_j\alpha^j_n=1,\quad \delta_n\downarrow 0 .
$$

Each $\alpha^j_n$ is **market-generable** (query the day-$f(n)$ market for the $k$ prices, apply softmax), so it is a legal weight for Theorem 4.12.3 (`thm:ccee`) — recall that theorem allows any market-generable $w_{f(n)}\in[0,1]$, and the paper itself uses a softened future-estimate indicator as such a weight (§0.3). The **strategy's return** is the LUV

$$
\widehat S_n \;:=\; \sum_j \alpha^j_n\,O^j_n
$$

(the hard diagonal $S_w(w)$ is the $\delta_n\to 0$ limit: as the temperature drops, $\alpha^j_n$ concentrates on the $\arg\max$, and $\widehat S_n$ becomes "the payoff of the option the future self picks"). Define:

> **Value (LI form).** For each fixed $i$, $\quad \mathbb E_n(\widehat S_n)\ \gtrsim_n\ \mathbb E_n(O^i_n).$
>
> *In a timely manner, the present self prefers handing a bounded decision to its future self over committing now to any fixed bet.*

For **Value alone**, this softening is in fact avoidable: §3.1 treats the hard-$\arg\max$ payoff as a *single* LUV and obtains Value directly from the unconditional martingale `thm:cee` (no `thm:ccee`, no $\delta_n\log k$). Softening is what **Total Trust** (next) and the *weight*-based presentation require.

**Total Trust (LI form)** is the statement, for bounded LUVs $X$, that $\mathbb E_n\!\big(X\mid \mathbb E_{f(n)}(X)\ge t\big)\gtrsim_n t$; it is the soft-conditioning consequence of Theorem 4.12.3 (`thm:ccee`) with $w=\operatorname{Ind}_{\delta_n}(\mathbb E_{f(n)}(X)>t)$, generalizing the sentence-level Self-Trust (Theorem 4.12.4, `thm:st`) from indicators to all estimates.

---

## 3. The clean proof of Value

**Proposition (sketched at the LI paper's level of rigor).**
Every logical inductor satisfies *Value (LI form)*.

**Proof.**

$$
\begin{aligned}
\mathbb E_n(\widehat S_n)
&= \mathbb E_n\Big(\textstyle\sum_j \alpha^j_n\,O^j_n\Big) \\
&\eqsim_n \sum_j \mathbb E_n\big(\alpha^j_n\,O^j_n\big)
&&\text{[Linearity of Expectation, }k\text{ fixed: Thm 4.8.4 \texttt{thm:loe}]}\\[2pt]
&\eqsim_n \sum_j \mathbb E_n\big(\alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\big)
&&\textbf{[conditional martingale: Thm 4.12.3 \texttt{thm:ccee}, }w=\alpha^j\textbf{]}\\[2pt]
&\eqsim_n \mathbb E_n\Big(\textstyle\sum_j \alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\Big)
&&\text{[Linearity back: Thm 4.8.4]}\\[2pt]
&\gtrsim_n \mathbb E_n\big(\mathbb E_{f(n)}(O^i_n)\big)\;-\;\delta_n\log k
&&\text{[soft-max gap (below) + monotonicity Thm 4.8.10 \texttt{thm:expprovind}]}\\[2pt]
&\eqsim_n \mathbb E_n(O^i_n)
&&\text{[unconditional martingale: Thm 4.12.1 \texttt{thm:cee}].}
\end{aligned}
$$

Since $\delta_n\log k\to 0$ (for bounded menu size, or any $k_n$ with $\delta_n\log k_n\to 0$), this gives $\mathbb E_n(\widehat S_n)\gtrsim_n\mathbb E_n(O^i_n)$. $\qquad\blacksquare$

**The soft-max gap.** Write $m_j=\mathbb E_{f(n)}(O^j_n)$, $\bar m=\sum_j\alpha^j m_j$, and $L=\delta_n\log\sum_j e^{m_j/\delta_n}$ (the log-sum-exp / free energy). The Gibbs identity $L=\bar m+\delta_n H(\alpha)$ with $H(\alpha)=-\sum_j\alpha^j\log\alpha^j\in[0,\log k]$ the entropy, together with $L\ge\max_j m_j$, gives

$$
\bar m \;=\; L-\delta_n H(\alpha)\;\ge\;\max_j m_j-\delta_n\log k\;\ge\; m_i-\delta_n\log k,
$$

so $\sum_j\alpha^j_n\mathbb E_{f(n)}(O^j_n)\ge \mathbb E_{f(n)}(O^i_n)-\delta_n\log k$ holds **in every consistent world** (it is an algebraic fact about the day-$f(n)$ prices). That uniform, provable-in-every-world bound is exactly the hypothesis Expectation Provability Induction (Theorem 4.8.10, `thm:expprovind`) needs in order to pass to the bound on $\mathbb E_n$, licensing the fourth line.

That is the whole proof. **No simplices, no extreme points, no "modestly informed," no tie-breaking perturbation.** The diagonal problem of §1.2 evaporates at line 3: Theorem 4.12.3 (`thm:ccee`) keeps each bet $O^j$ paired with *its own* selection weight $\alpha^j$ and swaps the bet for the future estimate of the bet — which is exactly the "the realized diagonal tracks the experts' verdicts" bridge that DDB must reconstruct by hand.

### 3.1 Value without softmax: the hard-$\arg\max$ strategy via the unconditional martingale

The softmax earns its keep for **Total Trust** (the conditional statement needs a legal, continuous *weight* for `thm:ccee`). For **Value alone** it is avoidable, and the genuine $\arg\max$ case — the expert picks *one* option, it does not randomize — is handled directly. Let the realized payoff of "let the future self decide" be the LUV

$$
\widehat S_n^{\arg} \;:=\; O^{\,j^\star(n)}_n,\qquad j^\star(n)\in\arg\max_j \mathbb E_{f(n)}(O^j_n)\quad(\text{any \emph{computable} tie-break}).
$$

The key point is that $\widehat S_n^{\arg}$ is **itself an efficiently computable sequence of $[0,1]$-LUVs** (its defining formula references $f(n)$, the menu, the computable market, and the tie-break).

Write $m^j_n:=\mathbb E_{f(n)}(O^j_n)$ and $M_n:=\max_j m^j_n$. Two facts hold *in every consistent world*, by the definition of $\arg\max$:

- **(F1)** $\mathbb E_{f(n)}(\widehat S_n^{\arg})=M_n$, **independent of the tie-break** — the future self's value of whatever it selected is the maximal value, since every maximizer has future-value $M_n$;
- **(F2)** $M_n\ge m^i_n$ for each $i$.

Then, with **Expected Future Expectations** (Theorem 4.12.1, `thm:cee`) as the *only* coherence engine and **Expectation Provability Induction** (Theorem 4.8.10, `thm:expprovind`) for monotonicity:

$$
\mathbb E_n(\widehat S_n^{\arg})
\ \overset{\text{cee}}{\eqsim_n}\ \mathbb E_n\!\big(\ulcorner\mathbb E_{f(n)}(\widehat S_n^{\arg})\urcorner\big)
\ \overset{\text{F1}}{\eqsim_n}\ \mathbb E_n(\ulcorner M_n\urcorner)
\ \overset{\text{F2}}{\gtrsim_n}\ \mathbb E_n(\ulcorner m^i_n\urcorner)
\ \overset{\text{cee}}{\eqsim_n}\ \mathbb E_n(O^i_n).
$$

So $\mathbb E_n(\widehat S_n^{\arg})\gtrsim_n\mathbb E_n(O^i_n)$ — **Value, for hard $\arg\max$, with no conditional martingale, no softmax, no $\delta\log k$, and no bound on $k$.** It is the **law of total expectation** in LI dress: "follow the expert" is the variable $O^{j^\star}$; the expert knows what it chose, so its conditional expectation of that choice is $M$; the unconditional martingale carries $M$ back to the present. **Ties are irrelevant** here because F1 is tie-break-free — *which* maximizer is chosen changes the realized payoff but not its future-value $M$, and the present expectation only sees the latter.

This relocates the role of softmax precisely. It is doing real work for **Total Trust** (hard conditioning on a future-estimate event is the liar pathology of Theorem 4.12.4) and for presenting Value and Total Trust through one engine — but for **Value** *per se* it is an optional convenience; the genuinely faithful object satisfies Value outright.

> **Status: proved / machine-checked** (§9, part (d)). The exact finite backbone `DeferenceArgmax.value_of_argmax` is proved with `jstar` an *arbitrary* maximizer, so tie-break-independence is exactly what the kernel checks; the asymptotic chain `value_argmax_asymptotic` invokes only `cee` and `expprovind`. One step stays prose: that LI delivers F1's martingale identity rests on $\widehat S^{\arg}=O^{j^\star}$ being an admissible e.c. LUV sequence — not formalizable without modeling LUVs/the market.

### 3.2 The softmax limit, and what it costs

One can instead recover the hard-$\arg\max$ result *from* the softmax result by a limiting step, which is instructive about where the cost hides. Write $\widehat S^{\alpha}$ for the softmax payoff (weights $\alpha$) and $\widehat S^{\beta}$ for the hard one (weights $\beta$). Since every $O^j_n\in[0,1]$, in every consistent world

$$
\Big|\textstyle\sum_j(\alpha^j_n-\beta^j_n)O^j_n\Big|\ \le\ \sum_j|\alpha^j_n-\beta^j_n|\ =\ \|\alpha_n-\beta_n\|_1 ,
$$

so by monotonicity $\big|\mathbb E_n(\widehat S^{\alpha}_n)-\mathbb E_n(\widehat S^{\beta}_n)\big|\le \mathbb E_n(\|\alpha_n-\beta_n\|_1)$, and argmax-Value follows from softmax-Value **provided** $\mathbb E_n(\|\alpha_n-\beta_n\|_1)\to0$. But $\|\alpha(\delta)-\beta\|_1\to0$ only *away from ties*: at an exact $r$-way tie softmax tends to the uniform mix over the maximizers while $\beta$ concentrates on one, so $\|\alpha-\beta\|_1\to 2(r-1)/r\neq0$. With $g_n$ the top-two margin,

$$
\mathbb E_n(\|\alpha_n-\beta_n\|_1)\ \le\ (k-1)\,e^{-\tau_n/\delta_n}\ +\ 2\,\mathbb E_n\big(\mathbf 1[g_n<\tau_n]\big),
$$

so the route closes only along a schedule $\tau_n\to0$, $\delta_n=o(\tau_n)$ with vanishing near-tie mass $\mathbb E_n(\mathbf 1[g_n<\tau_n])\to0$. That near-tie condition is a genuine extra hypothesis — exactly the gate §3.1 does *without*, because §3.1 never forms the difference $\widehat S^{\alpha}-\widehat S^{\beta}$ (which is large at a tie precisely because the two disagree over *which* equal-valued payoff to realize) and only ever uses the shared future-value $M$.

> **Status: proved / machine-checked** (§9, part (d)). The $\mathbb E_\pi$ bound is `payoff_gap_le_l1` (proved outright, no LI input); the squeeze is `approx_of_abs_le`; and `value_argmax_via_softmax` packages "softmax-Value $+\ \Delta_n\to0\Rightarrow$ argmax-Value," with the near-tie condition entering as $\Delta_n\to0$.

---

## 4. The trap: why it must be `thm:ccee`, not `thm:cee`

It is tempting to shortcut the proof using only the *unconditional* martingale (Theorem 4.12.1, `thm:cee`) plus "future-linearity":

$$
\mathbb E_n(\widehat S_n)\overset{?}{\eqsim_n}\mathbb E_n\big(\mathbb E_{f(n)}(\widehat S_n)\big)
\overset{?}{\eqsim_n}\mathbb E_n\Big(\textstyle\sum_j\alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\Big).
$$

The second step pulls the weights $\alpha^j_n$ out of the *future* expectation — and that is legal **only if the future self knows its own selection**, i.e. only if $\mathbb P_{f(n)}$ is *certain* of $\alpha^j_n$. For a genuinely **modest** expert this fails. Concretely, in the anti-expert frame of §1.3 the future self at $a$ puts weight $.8$ on world $b$, where the selection is the *opposite*; one computes

$$
E_a(\widehat S)=-1 \quad\ne\quad \sum_j\alpha^j(a)\,E_a(O^j)=.6 .
$$

So future-linearity is *false* exactly when the expert is modest — and that is the same place the unconditional martingale was shown (§1.3) to be too weak. This is reassuring rather than alarming:
it certifies that the clean proof is *not* secretly assuming immodesty. The work is being done by the genuinely stronger Theorem 4.12.3 (`thm:ccee`), which the anti-expert frame does **not** satisfy ($-.5\ne.3$, §1.3) — which is why the proof correctly refuses to "prove" Value there, Value being false there.

> **Locating modesty precisely.** The diagonal problem *is* the gap between Theorem 4.12.1 (`thm:cee`, which any stationary frame has) and Theorem 4.12.3 (`thm:ccee`, which only a coherent one has). Modesty lives in that gap.

---

## 5. Why it is clean in LI but cannot be clean on a finite frame

### 5.1 The criterion supplies the coherence for free

DDB note that Value is equivalent to a no-(fixed-option)-Dutch-book condition (their **Theorem 5.1**: "there is no fixed-option Dutch book against transitioning from $\pi$ to $P$"). LI's defining criterion *is* "no efficient trader earns unbounded profit against the market" — a no-Dutch-book condition. So in LI the coherence that DDB **extract** from Total Trust by convex geometry is instead **built into what a logical inductor is**, and surfaces as the martingale theorems 4.12.1 / 4.12.3 (`thm:cee`/`thm:ccee`) — each roughly eight lines from the criterion via Persistence and Preemptive Learning (LI Appendix `app:ccee`). The convex-hull machinery is a *static stand-in for a dynamic no-arbitrage fact*; once the no-arbitrage fact is available directly, the geometry is unnecessary.

### 5.2 A modest, conditional-martingale reasoner is impossible on a finite frame

This is the structural heart of the matter.

> **Proposition (finite collapse).** Let $\langle W,\mathcal P\rangle$ be a **finite** frame and $\pi$ a novice. If the *soft* conditional martingale holds — for every bounded $X$ and threshold $t$,
> $$E_\pi\!\big(X\cdot \operatorname{Ind}_{\delta}(E(X)>t)\big)=E_\pi\!\big(E(X)\cdot\operatorname{Ind}_{\delta}(E(X)>t)\big)\quad\text{for all small }\delta>0,$$
> then the expert is **immodest** on $\pi$'s support: $P_w(P=P_w)=1$ for all $w\in W_\pi$.

*Proof.* On a finite frame the set of values $\{E_w(X):w\in W\}$ is finite, so it has a **spectral gap**: a minimal positive distance between distinct values. For $\delta$ below that gap and generic $t$, the soft indicator $\operatorname{Ind}_\delta(E(X)>t)$ coincides with the hard indicator $\mathbf 1[E(X)>t]$ at every world. As $X,t$ vary, these threshold events generate the expert $\sigma$-algebra $\mathcal P$ (distinct states $P_w\ne P_{w'}$ are separated by some $E(X)$).
Hence the hypothesis collapses to $E(X)=E_\pi(X\mid\mathcal P)$, i.e. $P_w=\pi(\cdot\mid P=P_w)$.
Taking $X=\mathbf 1[P=P_w]$ yields $P_w(P=P_w)=1$. $\qquad\blacksquare$

So on finite frames, the very property that makes the Value proof clean **forces immodesty** (indeed Reflection / the S5 partition). A reasoner that is at once

- **modest** (does not know its own future verdicts — the cognitively realistic case, the non-Euclidean S4 frame of §1.1), and
- **conditional-martingale-coherent** (so that deference equals value *cleanly*)

cannot exist when the expert's estimates take finitely many, gapped values. It requires the estimates to range **without spectral gap** — a **continuum** — i.e. an **infinite frame**.
Logical induction supplies exactly this: a continuum of consistent completions $\mathcal{PC}(\Gamma)$, future estimates dense in their range, and — crucially — the *hard* conditional martingale stays permanently **false** (the liar sentence $\chi$: hard-conditioning on $\mathbb P_{f(n)}(\chi)\ge\tfrac12$ gives probability $0$, not $\ge p$; this is the same false-hard/true-soft split noted under Self-Trust in §0.3). The **soft** version holds, the **hard** version fails, and the gap never closes. That permanent gap is the home of modesty.

> **Upshot.** The deference theorem is not a finite-frame artifact — but its *natural home is not finite frames either*. Its natural home is a modest-but-coherent reasoner, which is necessarily infinite and self-referential. LI is the first concrete inhabitant, and there the theorem is not merely true but cheap.

### 5.3 One picture (S4 / Blackwell–Geanakoplos)

The threads of §1.1 unify (using the modal vocabulary from there):

- **Partitional (S5), immodest:** reflexive + transitive + **Euclidean** $\Rightarrow$ equivalence relation $\Rightarrow$ partition. This is Reflection / classical conditioning; the expert knows its own cell; both Trust and Value hold trivially.
- **Reflexive + transitive (S4), modesty allowed:** drop the Euclidean property. This is Geanakoplos's value-of-information regime; DDB's "modestly informed" is the credence-level version; here Total Trust $=$ Value. DDB's hard direction $=$ "Total Trust forces S4 on $\pi$'s support."
- **Logical induction:** the future self is an S4-like (reflexive, transitive, **non-Euclidean**) refinement of the present self, realized in an infinite, self-referential frame; the logical-induction criterion enforces the S4 coherence **dynamically**, so Trust and Value both fall out via the martingale toolbox (Theorems 4.12.1/4.12.3/4.12.4) rather than from a static credence inequality.

---

## 6. Weatherson's infinite failures are LI's two scope conditions

Weatherson breaks the DDB equivalence in **both** directions on infinite frames. Each break exploits precisely one thing LI excludes for an *independent* reason. (Both of his frames are *prior frames* built from a coin process; minor typos in his printed payoff constants are noted in the transcription and do not affect the arguments — Value fails on Coin as long as every option has positive expectation while the diagonal is $0$.)

**Coin (Total Trust *without* Value).** $W=\mathbb Z^+$ with $\pi(F{=}x)=2^{-x}$ (geometric: $F$ is the flip on which a fair coin first lands Tails). The expert at $F=x$ learns $F\ge x$ and conditions: $P_{F=x}=\pi(\cdot\mid F\ge x)$. Options $O_i$ pay $0$ for $F\le i$ and $2^{i}$ (or $2^{i-1}$ — see the typo note) for $F>i$. The strategy $s(F{=}i)=O_i$ is recommended, but its **diagonal return is $0$ everywhere** (at $F=i$ you hold $O_i$, which pays $0$ there) while **every column/option has positive $\pi$-expectation** — a non-uniformly-integrable martingale. Weatherson verifies $\pi$ *does* Totally Trust Coin (by a cutoff-cell argument), so Total Trust $\not\Rightarrow$ Value. The driver is **unbounded utility**.
*LI excludes it:* expectations are defined only for **bounded** LUV-combinations ($\mathcal{BLCS}$ carries a uniform bound), and only **finite-risk** traders constrain the market. Boundedness *is* uniform integrability, and it is exactly what makes lines 1, 4, and 5 of the §3 proof legal (Linearity 4.8.4 and Provability Induction 4.8.10 both require $\mathcal{BLCS}$). Weatherson's first failure is the case LI's boundedness rules out.

**Bentham (Value *without* Total Trust).** $W=\mathbb Z^+\cup\{\infty\}$, with the expert at $F=x$ learning $F\le x$ ($P_{F=x}=\pi(\cdot\mid F\le x)$). Value holds — Weatherson **proves** it as a limit of finite sub-frames $\langle W_n,P_n\rangle$, each of which is a finite prior frame with $E$ reflexive, transitive, and nested, so Geanakoplos gives value-of-information $\ge0$ on each, and the bound passes to the limit (the same Blackwell–Geanakoplos content the S4 picture keeps). But Total Trust **fails** at the single **measure-zero world $\{F=\infty\}$**: take $Y$ with $Y(F{=}\infty)=0$ and $Y(F{=}n)=1-2^{-n}$; the only world where the expert's estimate of $Y$ is $\ge\tfrac23$ is $F=\infty$, where $Y=0$, so $E_\pi(Y\mid E(Y)\ge\tfrac23)=0<\tfrac23$. The driver is **hard conditioning on a null tail**.
*LI excludes it:* the self-trust theorems quantify over **finite** future days $f(n)$ with $n\to\infty$ (no "$\infty$" expert is ever instantiated) and condition only **softly** ($\operatorname{Ind}_{\delta_n}$, $\delta_n\to0$, never a hard $\sigma$-algebra event). Weatherson's second failure is the case LI's soft, asymptotic conditioning rules out.

So both pathologies map onto exactly the two technical restrictions LI imposes for reasons that have nothing to do with deference (finite risk; paradox-resistance). The immunity is principled.

| failure mode | DDB direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust $\not\Rightarrow$ Value | unbounded utility | bounded LUVs / finite-risk traders ($\mathcal{BLCS}$) |
| **Bentham** | Value $\not\Rightarrow$ Total Trust | null-tail hard conditioning | finite future $f(n)$ + soft $\operatorname{Ind}_{\delta}$ |

---

## 7. The realizability payoff

The clean *finite* story (prior frames, partitions, Reflection) is a **realizable** one: the novice's candidate set $C_\pi$ literally contains the experts. Weatherson's normal-distribution example (his §1, the dual-deference construction with uncountably many possible expert credences) already strains this, and the deeper worry is that "narrow another agent's beliefs down to a known finite set" is cognitively fake.

LI earns the equivalence **without** a grain-of-truth assumption. The present self provably *cannot* contain a full model of its future self — that way lies the unexpected-hanging / self-referential paradox — so the "expert" here is genuinely **larger than, and not realizable within,** the deferring agent. Yet deference-as-value still goes through, approximately and in a timely manner. A theorem that survives the removal of realizability, in the one setting we have where a finite mind reasons soundly about something bigger than itself, is a theorem about *deference* rather than about the bookkeeping of finite frames. That is the reassurance the finite proof could not, by itself, provide.

---

## 8. Caveats, scope, and open questions

**Status of §3.** "Value (LI form)" is *my* translation; it is not stated in the LI paper, though it is the decision-theoretic face of self-trust and is squarely in the tiling / Vingean-reflection register. The proof is given at the LI paper's level of rigor (free use of $\eqsim_n$). A fully formal version must discharge:

1. **Generability of $\alpha$.** $(\alpha^j_n)_n$ is market-generable (softmax of finitely many day-$f(n)$ prices); this is the same kind of future-state-dependent soft weight the paper uses right after Theorem 4.12.3 (`thm:ccee`).
2. **Linearity with generable real coefficients.** Linearity of Expectation (Theorem 4.8.4, `thm:loe`) is stated for *bounded market-generable rational* coefficients; extending the two linearity steps to bounded market-generable *real* coefficients $\alpha^j_n$ (rational approximation absorbed by $\eqsim_n$, $k$ fixed) is routine but should be written out.
3. **Menu growth.** Need $\delta_n\log k_n\to0$; trivial for fixed $k$.
4. **Boundedness.** Options are $[0,1]$-LUVs (or any fixed bounded range). Unbounded options are out of scope — and that is exactly Coin (§6).

**Both directions.** The converse (Value $\Rightarrow$ Total Trust) is the easy DDB direction (Lemma 7.1) and has the same two-option witness in LI; but in LI it is moot, since Total Trust holds outright as the LUV-form of Self-Trust (Theorem 4.12.4) / Theorem 4.12.3. Both sides are theorems flowing from one source.

**Soft vs. hard, and ties.** For **Total Trust** the soft selection is not a mere convenience: the hard version is subject to the liar pathology (and to DDB's own Weak-Value-vs-Value tie-breaking, Lemma 7.5).
Softening dissolves *both* the paradox and the tie-breaking ugliness at once — a second, independent way the LI rendering is cleaner. But note this concerns *conditioning* and using $\arg\max$ as a *weight*: the hard-$\arg\max$ **strategy** itself satisfies **Value** directly when treated as a single LUV (§3.1), with ties harmless and no near-tie condition — so for Value the softening is convenience, not necessity.

**Fixed options and the missing self-counterfactual (the load-bearing idealization).** The whole decision-theoretic environment is a menu of *exogenous bets*: each option $O^j_n$ is a $[0,1]$-LUV whose value is read off the realized world, and the §3 proof compares two LUV-expectations, $\mathbb E_n(\widehat S_n)\gtrsim_n\mathbb E_n(O^i_n)$. The decision-theoretic *reading* of §2 — "the present self would rather defer than commit to $O^i$" — rests on identifying $\mathbb E_n(O^i_n)$ with *the payoff of committing to $O^i$*. That identification is the load-bearing idealization, and it is worth stating precisely, because the naive version of it is wrong.

It is **not** that deference-punishing environments are inexpressible. For a mathematically well-defined (e.g. computable) reasoner, "the agent defers" and "the future self selects option $j$" are themselves *logical facts*, so a perfectly legitimate LUV may depend on them — payoffs that reward or punish the very act of deferring are expressible. The accurate statement is that the option values are **treated as fixed with respect to the choice**: the proof manipulates $\mathbb E_n(O^i_n)$ as a fixed quantity (it is one — the expectation of that LUV *under the actual, deferring process*), and the gloss then reads it as the value of the *counterfactual* action of committing. Equivalently: the model contains only **one** action — defer — and "commit to $O^i$" is a counterfactual whose payoff is silently taken to be the LUV's value *on the road that was taken*.
There is no genuine counterfactual on the agent's own action. This is exactly right when payoffs are choice-independent, and silently wrong otherwise.

*Witness.* Take a menu $\{A,B\}$ with $B\equiv 0.4$ and $A=$ "pays $1$ if I am committed to *directly*, $0$ if I am *reached by deferral*" — a fact about a computable agent (the within-step self-reference resolves softly, à la the liar, or use a predictor who guessed earlier to remove it).
Under deferral — the only action the model's agent actually takes — $A$ is reached-by-deferral, so $A=0$, hence $\mathbb E_n(A)=0$, the future self takes $B$, and $\widehat S_n\approx 0.4$. The theorem reports $\widehat S_n\,(0.4)\gtrsim\mathbb E_n(A)\,(0)$ and the gloss concludes "deferring beats committing to $A$" — yet committing to $A$ actually pays $1>0.4$, so deference is the *worse* choice. The inequality is true; the *reading* misleads, because $\mathbb E_n(A)$ is $A$'s value in the world where you deferred, not in the counterfactual where you committed. (Note the proof itself is choice-agnostic: the inequality holds for any efficiently-computable menu the LI theorems apply to, self-referential ones included — which is precisely why this assumption hides in the interpretation rather than surfacing as a hypothesis.)

Two familiar idealizations are corollaries of this one. **(i) Costless deferral:** nothing charges for thinking until day $f(n)$ — the tell is that the result is *uniform in the deferral function $f$* (any $f(n)>n$, no penalty for waiting). **(ii) No deference-punishing / Newcomblike payoffs:**
where the payoff depends on the decision process, $\mathbb E_n(O^i_n)$ ceases to be the value of committing. This second case is exactly the **acausal** regime in which endorsement and deference are known to diverge (cf. §10 and the updateless-deference question) — the 5-and-10 / Troll-Bridge / EDT-vs-CDT cluster, where the absence of a self-counterfactual is the whole difficulty. The clean theorem is clean partly because it lives where the actual value and the counterfactual-on-self coincide: the choice-independent, causal-surrogate, updateful regime — the same "agent outside the environment" idealization DDB make and that Weatherson's prior-frame setting assumes.

**Open.**
- *Can the finite S4-extraction be made slick after all?* My suspicion is no — that the cleanliness genuinely requires getting the conditional martingale dynamically rather than from a static credence condition. A small impossibility/awkwardness result here would be worth having.
- *Local (question-relative) deference (DDB §5).* In LI this is deferring to the future self about a restricted class of LUVs. Since Theorem 4.12.3 (`thm:ccee`) is already "local" in $X$, this may be the cleanest case of all, and would directly address DDB's open conjecture that local Total Trust $=$ local Value.
- *Quantitative version.* The $\eqsim_n$ wrappers hide rates; with explicit deferral functions one could ask for a finite-horizon "how much value is at stake" bound, closer to the tiling-theoretic use.

---

## 9. Machine-check

The finite, fully-rigorous skeleton of the §3 proof is machine-checked in `deference-in-logical-induction-check.py` (Python 3.11 + `sympy`; exact rational arithmetic throughout the algebra, so equalities are verified *exactly*). **18/18 checks pass.**

The check rests on isolating the proof's content as one **exact identity** plus one **clean inequality**. For any finite frame, novice $\pi$, menu, and any weights $\alpha^j$ (summing to 1):

$$
\underbrace{E_\pi(\widehat S)-E_\pi(O^i)}_{\text{Value gap}}
\;=\;
\underbrace{\textstyle\sum_j\big(E_\pi(\alpha^j O^j)-E_\pi(\alpha^j E(O^j))\big)}_{D_{\mathrm{CM}}\ (\text{Thm 4.12.3 \texttt{thm:ccee}}\text{ defect})}
\;+\;
\underbrace{E_\pi(E(O^i))-E_\pi(O^i)}_{D_{\mathrm{UM}}\ (\text{Thm 4.12.1 \texttt{thm:cee}}\text{ defect})}
\;+\;
\underbrace{E_\pi(\bar m-m_i)}_{\ \ge\,-\delta\log k\ \ (\text{softmax})}.
$$

The LI theorems are exactly the statements that the three terms vanish ($D_{\mathrm{CM}},D_{\mathrm{UM}}\to0$ via `thm:ccee`/`thm:cee`; the softmax term via $\delta_n\to0$), whence Value. What is verified:

| | check | result |
|---|---|---|
| **A** | the identity above holds **symbolically for all frames** (sympy `expand`$=0$), shapes up to $4\times3$ | pure linearity; no frame hypothesis used |
| **B** | softmax bound $\bar m=L-\delta H(\alpha)\ge\max_j m_j-\delta\log k$ (20 000 trials) | Gibbs identity to $1.7\!\times\!10^{-15}$; bound never violated |
| **C** | DDB Fig. 2 & 3, exact | Fig. 2 Value fails; Fig. 3 Values; and the **§4 trap quantified**: anti-expert gap $-1 = D_{\mathrm{CM}}(-\tfrac85)+D_{\mathrm{UM}}(0)+\text{soft}(\tfrac35)$ — unconditional martingale intact, $D_{\mathrm{CM}}$ alone kills Value |
| **D** | conditional martingale $\Rightarrow$ Value, 3 000 random prior frames | 0 counterexamples; $D_{\mathrm{CM}}=D_{\mathrm{UM}}=0$ exactly |
| **E** | finite-collapse (§5.2), 20 000 random frames with nontrivial fibers | **0** frames both conditional-martingale and modest (classes both well-populated: 277 vs 11 421) |
| **F** | LI regime in miniature: modest, near-CM frames, soft selection | Value holds up to $|D_{\mathrm{CM}}|+|D_{\mathrm{UM}}|+\delta\log k$ in every row; error $\to0$ as perturbation, $\delta\to0$ |

### Lean (kernel-checked)

Formalized in **Lean 4.27.0 + Mathlib** (`lean-deference/LeanDeference.lean`), checked by the Lean kernel. All theorems are **`sorry`-free** and depend only on the standard axioms `[propext, Classical.choice, Quot.sound]` (verified by `#print axioms` — no `sorryAx`). Four parts.

**(a) The actual §3 argument, modulo the LI results** — `DeferenceAsymp.value_asymptotic`.
The `≂ₙ`/`≳ₙ` calculus is modeled honestly as real-sequence asymptotics:
`a ≂ₙ b := (aₙ-bₙ)→0` and `a ≲ b := ∀ε>0, eventually aₙ ≤ bₙ+ε` (so `b ≳ₙ a`). The five Logical-Induction results enter as **explicit hypotheses** (we trust the paper, we don't re-prove it), and Value is derived in this calculus:

| hypothesis | LI result |
|---|---|
| `hAdd1`, `hAdd2`: `E_now(Ŝ) ≂ₙ ∑ⱼ E_now(αⱼOⱼ)`, `∑ⱼ E_now(αⱼ·E_later Oⱼ) ≂ₙ E_now(∑ⱼ αⱼ·E_later Oⱼ)` | Linearity of Expectation, Thm 4.8.4 (`thm:loe`) |
| `hCcee`: `∀j, E_now(αⱼ Oⱼ) ≂ₙ E_now(αⱼ · E_later Oⱼ)` | **No Expected Net Update under Conditionals, Thm 4.12.3** (`thm:ccee`) |
| `hCee`: `∀j, E_now(E_later Oⱼ) ≂ₙ E_now(Oⱼ)` | Expected Future Expectations, Thm 4.12.1 (`thm:cee`) |
| `hδ`,`hSoft`: `E_now(E_later Oⁱ) ≤ E_now(∑ⱼ αⱼ·E_later Oⱼ) + δₙ`, `δₙ→0` | Expectation Provability Induction, Thm 4.8.10 (`thm:expprovind`) ∘ softmax bound *(softmax half now proved — see (c))* |

> **conclusion** `E_now(Oⁱ) ≲ E_now(Ŝ)`, i.e. **`E_now(Ŝ) ≳ₙ E_now(Oⁱ)` = Value**.

The proof is the §3 chain verbatim: `E_now(Ŝ) ≂ₙ ∑ a ≂ₙ ∑ b ≂ₙ c ≳ₙ E_now(E_later Oⁱ) ≂ₙ E_now(Oⁱ)`, with the supporting `≂ₙ`/`≳ₙ` lemmas (reflexivity, symmetry, transitivity, `≂ₙ`-refines-`≲`, finite-sums-respect-`≂ₙ`) proved from Mathlib's `Filter`/`Tendsto` API. This is the sense in which the §3 proof is machine-checked: **its composition of the LI theorems is valid**.

**(b) The finite exact backbone** — `Deference.*` (the $\delta=0$ / defects-$=0$ shadow):
- `decomposition` — the keystone identity $\text{gap}_i = D_{\mathrm{CM}}+D_{\mathrm{UM}}+\text{soft}_i$ over an arbitrary `CommRing`, for **all** finite `Fintype` $W,J$ and all $\pi,P,O,\alpha$ (upgrading sympy check **A** from sampled shapes to a universal statement). Proof: `simp only [mul_sub, Finset.sum_sub_distrib]; ring`.
- `value_of_CM` — *conditional martingale $\Rightarrow$ Value*, exact finite, via `value_of_defects` + `soft_nonneg`.

**(c) Two supporting facts, now proved (not assumed)** — `DeferenceExtra.*`:
- `softmax_lower_bound` — $\sum_j \operatorname{softmax}(\delta,m)_j\, m_j \ge m_i - (\operatorname{card} J)\,\delta$ for $\delta>0$, from `Real.add_one_le_exp` alone. This discharges the analytic half of `hSoft`, so the facts the §3 derivation still *assumes* are exactly the genuine LI theorems (Thms 4.8.4, 4.12.3, 4.12.1, 4.8.10). (The note's tight constant $\delta\log(\operatorname{card} J)$ is the entropy bound; the cruder $(\operatorname{card} J)\,\delta$ proved here is all the $\delta\to0$ limit needs.)
- `CM_implies_immodest` — the core of §5.2: if the conditional-martingale identity $E_w(X)=E_\pi(X\mid \text{fiber } w)$ holds at $w$, then $P_w(\text{fiber } w)=1$ (immodesty), by instantiating it at the fiber's own indicator. (The soft-$\Rightarrow$-hard "no spectral gap" reduction — the step that needs an infinite frame — is left as §5.2's prose.)

**(d) The argmax route (§§3.1–3.2)** — `DeferenceArgmax.*`:
- `value_of_argmax` — *exact finite*, the §3.1 backbone: with `jstar` an **arbitrary** maximizer and the two unconditional-martingale identities (for `Ŝ` and `Oⁱ`) as hypotheses, `E_π(Oⁱ) ≤ E_π(Ŝ)`. The maximizer hypothesis quantifies over *any* maximizer, so **tie-break-independence is what the kernel checks**.
- `value_argmax_asymptotic` — the §3.1 `≂ₙ`/`≳ₙ` chain, invoking only `cee` and `expprovind` (no `ccee`, no softmax, no `δ log k`).
- `payoff_gap_le_l1` — *exact, no LI hypotheses*: `|E_π(Ŝ^α) − E_π(Ŝ^β)| ≤ E_π(∑ⱼ|αⱼ−βⱼ|)` for options in `[0,1]` (the §3.2 L¹ bound).
- `approx_of_abs_le`, `value_argmax_via_softmax` — the squeeze and the §3.2 conclusion (softmax-Value `+ Δ→0 ⇒` argmax-Value; the near-tie condition enters as `Δ→0`).
All four are `sorry`-free with `#print axioms = [propext, Classical.choice, Quot.sound]`. The upshot mirrors §3.1: Value needs only the *unconditional* martingale, so the kernel confirms the argmax route is strictly cheaper than the softmax one — which is reserved for Total Trust.

**Not checked** (and not checkable without formalizing the Logical Induction paper): that the genuine theorems 4.12.3 / 4.12.1 (`thm:ccee`/`thm:cee`) actually force $D_{\mathrm{CM}},D_{\mathrm{UM}}\to0$, and the $\eqsim_n$ bookkeeping. So this verifies the proof's *algebra and its finite mathematical core* — the part that could harbor a composition bug — but not the asymptotic LI layer the core is wrapped in. Check **C** is the most diagnostic: it confirms exactly, on DDB's own counterexample, that the Value failure is the conditional-martingale defect and that the unconditional martingale (the tempting shortcut of §4) is satisfied there — so the proof must use `thm:ccee`, not `thm:cee`.

---

## 10. Deferring to experts other than the future self

Everything above translates DDB's "expert" as the inductor's **own day-$f(n)$ self**. That is the maximally convenient choice — it is what makes Total Trust a *theorem* (Self-Trust 4.12.4 / the martingales 4.12.1, 4.12.3) rather than a hypothesis. But DDB's own setup is more general: their experts are arbitrary frames, and Total Trust is *assumed*. It is worth asking what survives when we put a generic expert back in. The answer is clean, and it sharpens the structural thesis of §5.

### 10.1 Which steps of §3 used "expert = future self"

Replace the future-self estimate $\mathbb E_{f(n)}(X)$ throughout by an external expert's estimate $\mathbb E_{\mathrm{exp}}(X)$, and audit the five lines of the §3 proof:

| step | engine | depends on the expert being the future self? |
|---|---|---|
| 2. $\mathbb E_n(\widehat S_n)\eqsim_n\sum_j\mathbb E_n(\alpha^j O^j)$ | Linearity 4.8.4 (`thm:loe`), **novice's own operator** | **no — free** |
| 3. $\eqsim_n\sum_j\mathbb E_n(\alpha^j\,\mathbb E_{\mathrm{exp}}(O^j))$ | conditional martingale 4.12.3 (`thm:ccee`) | **yes** |
| 4. $\eqsim_n\mathbb E_n(\sum_j\alpha^j\,\mathbb E_{\mathrm{exp}}(O^j))$ | Linearity back (**novice's own**) | **no — free** |
| 5. $\gtrsim_n\mathbb E_n(\mathbb E_{\mathrm{exp}}(O^i))-\delta_n\log k$ | softmax gap + Prov. Induction 4.8.10 (`thm:expprovind`) | **no — free** |
| 6. $\eqsim_n\mathbb E_n(O^i_n)$ | unconditional martingale 4.12.1 (`thm:cee`) | **yes** |

Lines 2, 4, 5 invoke only the **novice's own coherence** (linearity of its own expectation, and provability-monotonicity of its own expectation) and hold for *any* logical-inductor novice no matter who the expert is. Line 5 deserves a remark: the softmax inequality $\sum_j\alpha^j m_j\ge m_i-\delta\log k$ with $m_j:=\mathbb E_{\mathrm{exp}}(O^j)$ is a *purely algebraic* fact in the reals $m_j$, hence true in **every** consistent world $W\in\mathcal{PC}(\Gamma)$ (in $W$, $\alpha^j$ evaluates to the softmax of $W(m_j)$, since $\Gamma$ proves $\alpha=\operatorname{softmax}(m/\delta)$); that uniform bound is exactly the hypothesis Provability Induction (4.8.10) needs, so the step is expert-agnostic.

Only lines 3 and 6 used self-trust. And line 6 is line 3's premise at weight $w\equiv1$, so there is really **one** expert-specific ingredient: the cross-agent conditional martingale, i.e. the **LUV-level form of Total Trust directed at the external expert.**

> **LUV-Total-Trust (novice $\to$ expert).** For every market-generable weight $w_n\in[0,1]$,
> $$\mathbb E_n\big(\ulcorner X_n\,w_n\urcorner\big)\ \eqsim_n\ \mathbb E_n\big(\ulcorner\mathbb E_{\mathrm{exp}}(X_n)\,w_n\urcorner\big).$$

### 10.2 The generalized claim

> **Proposition (interpretation; sketched at the LI paper's level of rigor).**
> Let the **novice** be any logical inductor with operator $\mathbb E_n$, and let an **expert** supply a sequence of estimates $\mathbb E_{\mathrm{exp}}(O^j_n)$ that is (i) **novice-observable** — market-generable from the novice's own prices, so the selection weights $\alpha^j_n$ are legal — and (ii) **uniformly bounded** (its valuations are $[0,1]$-LUVs, or a fixed bounded range). If the pair satisfies *LUV-Total-Trust* (§10.1), then **Value (LI form)** holds:
> $$\mathbb E_n(\widehat S_n)\ \gtrsim_n\ \mathbb E_n(O^i_n).$$
> The easy converse (Value $\Rightarrow$ Total Trust) is the two-option witness of §1.1 and uses only the novice's own coherence, so on the observable–bounded class the two are **equivalent**.

This is just **DDB's Theorem 2.2 recovered for general experts, inside LI** — but with the novice's half of DDB's geometric reconstruction (the convex-hull/S4 extraction of §1.1) replaced by the LI criterion's free linearity and monotonicity. Even for an *external* expert the LI rendering stays cheaper than DDB's, provided the novice is an inductor.

### 10.3 Two structural observations

**(a) The future self is the *maximal* expert (interpretation).** If the novice can observe the external expert at all, the expert's outputs are features that the novice's *own* day-$f(n)$ self will have already incorporated. The future self is therefore a Blackwell **refinement** of any observable expert (§1.1), so by Blackwell–Geanakoplos monotonicity, deferring to the future self is at least as valuable as deferring to that expert. Choosing the future self in §§2–3 was thus not a loss of generality but a choice of the *join of all observable experts* — every observable external expert is dominated by it.

**(b) A *modest* external expert must itself be infinite — so the natural experts are other logical inductors (this is the strong claim).** The finite-collapse result (§5.2) never used "expert = future self." Its hypothesis is just: soft-conditional-martingale toward an expert whose estimates take **finitely many, gapped** values. The conclusion — immodesty, $P_w(P=P_w)=1$ — follows regardless of the expert's identity. So **any** expert that can be both *modestly* and *cleanly* deferred to must range over a continuum without spectral gap: it must be an infinite, self-referential object. **Another logical inductor** is exactly such an object. This turns §5's moral into a statement about experts in general: clean modest deference is possible only between infinite-frame reasoners, of which logical inductors are the concrete instances.

### 10.4 What is genuinely open

- **Observability is structural, not cosmetic.** If the novice cannot generate $\alpha^j_n$ from the expert's prices, lines 2/4 and the premise cannot even be *stated*. So the theory only speaks about experts the novice can watch.
- **Boundedness must be retained**, or Coin-type failures (§6) return.
- **The real open problem is the *characterization*.** When does one logical inductor satisfy LUV-Total-Trust toward a *different* one — over the same theory, a richer theory, a larger trader class, or a faster deferral schedule? This is *not* free between two arbitrary inductors (unlike the self-directed case, where it is `thm:ccee`). It is the LI analog of DDB's finite characterization "$\pi\in\mathrm{CH}(C_\pi)$ and every $P_i\in C_\pi$ modestly informed," whose LI counterpart is unknown. Because it concerns trust in a *distinct, possibly more powerful* successor rather than in one's own future, it sits in the **tiling / Vingean-reflection** register rather than the self-trust register — see the related open question in §8.

---

## References

- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better,"** *Philosophical Perspectives* 35 (2021). — Total Trust $\Leftrightarrow$ Value (**Theorem 2.2**); geometric characterization (**Theorems 4.1, 5.1**); "modestly informed" (Def. in §4 / glossary); Appendix B proofs (**Lemma 7.1** easy direction; **Lemmas 7.2.2–7.2.7, 7.2, 7.3** the convex-hull/S4 reconstruction with "Transitivity" 7.2.4 and "Reflexivity" 7.2.5; **Lemmas 7.4–7.5** Weak Value $\Rightarrow$ Value tie-breaking).
- B. Weatherson, **"Deference and Infinite Frames,"** *Australasian Journal of Logic* (2025). — Coin and Bentham counterexamples (§3); Geanakoplos non-extension and the reflexive/transitive/nested definitions (§2); dual-deference normal-distribution example (§1). (See the transcription notes for the transitivity-direction and payoff-constant typos.)
- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016), §4 "Properties of Logical Inductors." — Linearity of Expectation (**Thm 4.8.4**, `thm:loe`), Expectations of Indicators (**4.8.6**, `thm:ei`), Expectation Provability Induction (**4.8.10**, `thm:expprovind`); Introspection — Expectations of Probabilities (**4.11.3**, `thm:epr`), Iterated Expectations (**4.11.4**, `thm:er`); Self-Trust — Expected Future Expectations (**4.12.1**, `thm:cee`), No Expected Net Update (**4.12.2**, `thm:ceu`), No Expected Net Update under Conditionals (**4.12.3**, `thm:ccee`), Self-Trust (**4.12.4**, `thm:st`); construction and the logical-induction criterion (§3, §5). (Theorem numbers are those rendered by the paper's `section.subsection.counter` scheme, with theorems/definitions sharing one per-subsection counter.)
- J. Geanakoplos, "Game Theory Without Partitions, and Applications to Speculation and Consensus" ([1989] 2021), *B.E. Journal of Theoretical Economics* 21(2); D. Blackwell, "Equivalent Comparisons of Experiments" (1953). — reflexive/transitive/nested $\Rightarrow$ value of information $\ge0$ (Geanakoplos generalizing Blackwell's partitional comparison-of-experiments theorem).
