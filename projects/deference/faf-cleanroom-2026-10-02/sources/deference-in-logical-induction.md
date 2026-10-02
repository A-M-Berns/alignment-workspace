# Deference, Value, and Total Trust in the Logical-Induction Setting

*A note on porting the main theorem of Dorst, Levinstein, Salow, Husic & Fitelson,
"Deference Done Better" (DDB, 2021), into the logical-induction (LI) framework of
Garrabrant et al. (2016), in light of Weatherson's "Deference and Infinite Frames" (2025).*

---

## Summary

DDB's headline result is that, on **finite** probability frames,

$$
\textbf{Total Trust}\quad\Longleftrightarrow\quad\textbf{Value}.
$$

The proof (their Appendix B) is long and geometric, and Weatherson shows it fails **in both
directions** once frames are allowed to be infinite. This raises a worry that the equivalence
is an artifact of the finite-frame idealization rather than a fact about deference.

This note argues that the **logical-induction setting dissolves the worry**:

1. The two sides of the theorem already live inside LI, with the *expert = your own more-thought-out future self*. **Total Trust** is the LUV-level form of the **Self-Trust** theorem; **Value** is the (un-named) statement *"I'd rather let my future self pick the bet."*
2. In LI, **Value has a five-line proof** whose only engine is **No Expected Net Update under Conditionals** (`thm:ccee`) — a *conditional martingale* property that LI gets for free from the no-Dutch-book criterion. None of DDB's convex-hull machinery is needed.
3. The reason this is possible is structural and is the main conceptual payoff: **a reasoner that is both modest and conditional-martingale-coherent cannot exist on a finite frame.** The two demands collide there; they can only be reconciled on an infinite, self-referential frame. LI is the first concrete reasoner that occupies exactly that corner.
4. Weatherson's two infinite-frame counterexamples (**Coin**, **Bentham**) turn out to exploit precisely the two things LI's framework excludes for *independent* reasons — **unbounded utility** and **hard conditioning on a measure-zero tail**. So LI is immune to them by design, not by luck.
5. Because LI carries no grain-of-truth assumption, it vindicates the *content* of the theorem **without realizability** — the future self is genuinely larger than the present self, yet deference still equals value.

Throughout, claims are flagged as **proved**, **sketched at the LI paper's level of rigor**, or **interpretation**. Worked numerical checks against DDB's own figures are included.

---

## 0. Notation and the dictionary

**DDB.** A frame $\langle W,\mathcal P\rangle$ assigns to each world $w$ an "expert" credence $P_w$ on $W$. A *novice* credence $\pi$ on $W$ is given. For a random variable $X\colon W\to\mathbb R$, the expert's estimate is itself a random variable

$$
E(X)\colon w\longmapsto E_{P_w}(X),
$$

read (DDB's phrase) as *"a definite description for the expert's estimate of $X$, whatever it is."* The two principles:

- **Total Trust.** For every random variable $X$ and threshold $t$: $\ E_\pi\!\big(X\mid E(X)\ge t\big)\ge t$. Equivalently (their convexity form): $\pi(\,\cdot\mid P\in B)\in B$ for every *biconvex* $B$ (a halfspace).
- **Value.** For every finite menu $\mathcal O$ of options and every recommended strategy $S$ (which picks, at each $w$, an option maximizing $E_{P_w}$): $\ E_\pi(S)\ge E_\pi(O)$ for all $O\in\mathcal O$, where $E_\pi(S):=\sum_w\pi(w)\,S_w(w)$ is the **diagonal** return.

**LI.** Fix a logical inductor $(\mathbb P_n)_{n\ge 1}$ over a theory $\Gamma$ that can represent computable functions, with expectation operators $\mathbb E_n=\mathbb E_n^{\mathbb P_n}$ on $[0,1]$-LUVs, and a deferral function $f$ (so $f(n)\ge n$, strictly increasing). Read:

$$
\textbf{novice }\pi \;=\; \mathbb E_n,\qquad
\textbf{expert's estimate }E(X) \;=\; \text{the LUV }\ \mathbb E_{f(n)}(X),
$$

i.e. the expert is the *day-$f(n)$ self*, and the present self does **not** know what that future estimate is — it is a logically uncertain quantity, exactly as DDB's $E(X)$ is a "definite description." The relevant LI theorems (all consequences of the logical-induction criterion):

| name | statement (schematically) | role |
|---|---|---|
| Linearity of Expectation (`thm:loe`) | $\mathbb E_n(aX+bY)\eqsim_n a\mathbb E_n X+b\mathbb E_n Y$ | bookkeeping |
| Expectation Provability Induction (`thm:expprovind`) | provable bound $\Rightarrow$ bound on $\mathbb E_n$ | **monotonicity** |
| Expectations of Probabilities (`thm:epr`), Iterated Expectations (`thm:er`) | introspective access | bookkeeping |
| **No Expected Net Update** (`thm:cee`/`thm:ceu`) | $\mathbb E_n(X_n)\eqsim_n\mathbb E_n\!\big(\mathbb E_{f(n)}(X_n)\big)$ | **unconditional martingale** |
| **No Expected Net Update under Conditionals** (`thm:ccee`) | $\mathbb E_n\!\big(X_n\,w_{f(n)}\big)\eqsim_n\mathbb E_n\!\big(\mathbb E_{f(n)}(X_n)\,w_{f(n)}\big)$ | **conditional martingale** |
| **Self-Trust** (`thm:st`) | $\mathbb E_n\!\big(\phi\mid \mathbb P_{f(n)}(\phi)>p\big)\gtrsim_n p$ | **(Simple) Trust** |

In `thm:ccee`, $(w_m)$ is any **market-generable** $[0,1]$-valued sequence (the LI paper's "$\overline{\mathbb P}$-generable": computable in polynomial time with oracle access to the market prices) — and the paper's own application takes $w_{f(n)}=\operatorname{Ind}_{\delta_n}\!\big(\mathbb E_{f(n)}(X_n)>0.7\big)$, a *soft indicator of an event about the future estimate*. So future-state-dependent soft weights are explicitly allowed. This is the whole ballgame.

The map between principles:

| DDB | LI |
|---|---|
| Simple Trust (propositions $q$) | Self-Trust `thm:st` (sentences $\phi$) |
| Total Trust (all random variables $X$) | the LUV-level trust delivered by `thm:ccee` |
| Value (defer all decisions) | *"defer all bounded decisions to the future self"* (§2 below) |
| martingale $E_\pi(E(X))=E_\pi(X)$ | No Expected Net Update `thm:cee` |
| conditional martingale | No Expected Net Update under Conditionals `thm:ccee` |

---

## 1. Anatomy of the finite proof's difficulty

It pays to see *exactly* where DDB's proof spends its effort, because that is exactly what LI will hand us for free.

### 1.1 The hard direction is an S4-extraction

The easy direction, Total Trust $\Leftarrow$ Value (DDB Lemma 7.1), is a one-liner: a Total-Trust violation $E_\pi(X\mid E(X)\ge t)<t$ is witnessed by the two-option menu $\{X,\ \text{const }s\}$ with $s\lesssim t$. (Its LI shadow is likewise immediate.)

The hard direction is Total Trust $\Rightarrow$ Value (Lemmas 7.2.2–7.2.7, 7.3, then 7.4–7.5). Strip the convex-hull bookkeeping and read the *names* DDB give their load-bearing lemmas:

- **Lemma 7.2.4 — "Transitivity":** each $P_i\in C_\pi$ has $P_i(W_\pi)=1$ and $C_i\subseteq C_\pi$.
- **Lemma 7.2.5 — "Reflexivity":** $P_i(i)>0$ for $i\in W_\pi$.

Together with "modestly informed" ($P_i\in\mathrm{CH}(\{\widehat P_i\}\cup C_i^-)$), these say that, on $\pi$'s support, the frame is a **reflexive + transitive** accessibility structure — an **S4** frame — but **not necessarily Euclidean**, hence not a partition. The non-Euclideanness is what *licenses modesty*. And

$$
\text{reflexive + transitive + nested}\ \Longrightarrow\ \text{value of information}\ \ge 0
$$

is **Geanakoplos's theorem** (the generalization of Blackwell that Weatherson's §2 probes). So:

> **Reading.** DDB's hard direction is a *static reconstruction of S4 coherence out of a credence inequality*, after which Value follows by Blackwell–Geanakoplos. The ugliness is the reconstruction; the value argument itself is short.

### 1.2 The diagonal problem

Why is the reconstruction needed at all? Because Value compares the **diagonal** return $E_\pi(\widehat S)$, $\widehat S(w)=S_w(w)$, against $E_\pi(O)$, while row-wise optimality only controls $E_w(S_w)=\max_j E_w(O^j)$ at each $w$ separately. Bridging "average the diagonal" and "average the row-wise maxima" is the real content; it is what forces Lemma 7.5's perturb-to-break-ties argument.

### 1.3 It is the *conditional* martingale that discriminates, not the unconditional one

A clean way to feel the diagonal problem is to notice that the obvious bridge — the unconditional martingale $E_\pi(E(X))=E_\pi(X)$, i.e. stationarity $\pi P=\pi$ — is **neither necessary nor sufficient** for Value. Two checks against DDB's own figures:

**Anti-expert frame (DDB Fig. 2).** $\pi=(\tfrac12,\tfrac12)$, $P_a=(.2,.8)$, $P_b=(.8,.2)$.
- Stationary: $\pi P=(.5,.5)=\pi$. So the **unconditional** martingale holds.
- Bet menu $O_a=(1,-1),\,O_b=(-1,1)$: expert picks $O_b$ at $a$, $O_a$ at $b$; diagonal $\widehat S=(-1,-1)$, so $E_\pi(\widehat S)=-1<0=E_\pi(O_a)$. **Value fails.**
- Conditional check, $A=\{\text{select }O_b\}=\{a\}$: $E_\pi(O_b\mathbf 1_A)=-.5$ but $E_\pi(E(O_b)\mathbf 1_A)=.3$. The **conditional** martingale fails — exactly where Value fails.

**Valued modest frame (DDB Fig. 3).** $\pi=(\tfrac12,\tfrac12)$, $P_a=(.9,.1)$, $P_b=(.2,.8)$.
- Not even stationary: $\pi P=(.55,.45)\ne\pi$, and for $X=\mathbf 1_a$, $E_\pi(E(X))=.55\ne.5=E_\pi(X)$. The unconditional martingale **fails**, yet **Value holds**.

So the unconditional martingale is a red herring; the object that tracks Value is the **conditional** martingale $E_\pi(O\,\mathbf 1_A)=E_\pi(E(O)\,\mathbf 1_A)$ for expert-measurable $A$. Keep this in mind: LI will supply exactly the conditional version (softened), and §4 shows the unconditional version is genuinely too weak.

---

## 2. Value, translated into logical induction

Fix the deferral function $f$ and an efficiently computable sequence of menus

$$
\mathcal O_n=\{O^1_n,\dots,O^k_n\},\qquad O^j_n\ \text{a bounded }[0,1]\text{-LUV ("bet").}
$$

The day-$f(n)$ self evaluates each bet and "recommends" the maximizer. Because hard $\arg\max$ is discontinuous — and because hard conditioning on the future state is *false* in LI (the liar sentence, see `thm:st`) — we soften the selection into a Lipschitz partition of unity:

$$
\alpha^j_n \;=\; \frac{\exp\!\big(\mathbb E_{f(n)}(O^j_n)/\delta_n\big)}{\sum_{j'}\exp\!\big(\mathbb E_{f(n)}(O^{j'}_n)/\delta_n\big)},
\qquad \sum_j\alpha^j_n=1,\quad \delta_n\downarrow 0 .
$$

Each $\alpha^j_n$ is market-generable (query the day-$f(n)$ market for the $k$ prices, apply softmax), so it is a legal `thm:ccee` weight. The **strategy's return** is the LUV

$$
\widehat S_n \;:=\; \sum_j \alpha^j_n\,O^j_n
$$

(the hard diagonal $S_w(w)$ is the $\delta_n\to 0$ limit). Define:

> **Value (LI form).** For each fixed $i$, $\quad \mathbb E_n(\widehat S_n)\ \gtrsim_n\ \mathbb E_n(O^i_n).$
>
> *In a timely manner, the present self prefers handing a bounded decision to its future self over committing now to any fixed bet.*

Total Trust (LI form) is the statement, for bounded LUVs $X$, that $\mathbb E_n\!\big(X\mid \mathbb E_{f(n)}(X)\ge t\big)\gtrsim_n t$; it is the soft-conditioning consequence of `thm:ccee` with $w=\operatorname{Ind}_{\delta_n}(\mathbb E_{f(n)}(X)>t)$, generalizing the sentence-level `thm:st` from indicators to all estimates.

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
&&\text{[linearity, }k\text{ fixed: \texttt{thm:loe}]}\\[2pt]
&\eqsim_n \sum_j \mathbb E_n\big(\alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\big)
&&\textbf{[conditional martingale: \texttt{thm:ccee}, }w=\alpha^j\textbf{]}\\[2pt]
&\eqsim_n \mathbb E_n\Big(\textstyle\sum_j \alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\Big)
&&\text{[linearity back]}\\[2pt]
&\gtrsim_n \mathbb E_n\big(\mathbb E_{f(n)}(O^i_n)\big)\;-\;\delta_n\log k
&&\text{[soft-max gap (below) + monotonicity \texttt{thm:expprovind}]}\\[2pt]
&\eqsim_n \mathbb E_n(O^i_n)
&&\text{[unconditional martingale: \texttt{thm:cee}].}
\end{aligned}
$$

Since $\delta_n\log k\to 0$ (for bounded menu size, or any $k_n$ with $\delta_n\log k_n\to 0$), this gives $\mathbb E_n(\widehat S_n)\gtrsim_n\mathbb E_n(O^i_n)$. $\qquad\blacksquare$

**The soft-max gap.** Write $m_j=\mathbb E_{f(n)}(O^j_n)$, $\bar m=\sum_j\alpha^j m_j$, and $L=\delta_n\log\sum_j e^{m_j/\delta_n}$. The Gibbs identity $L=\bar m+\delta_n H(\alpha)$ with $H(\alpha)=-\sum_j\alpha^j\log\alpha^j\in[0,\log k]$ and $L\ge\max_j m_j$ gives

$$
\bar m \;=\; L-\delta_n H(\alpha)\;\ge\;\max_j m_j-\delta_n\log k\;\ge\; m_i-\delta_n\log k,
$$

so $\sum_j\alpha^j_n\mathbb E_{f(n)}(O^j_n)\ge \mathbb E_{f(n)}(O^i_n)-\delta_n\log k$ holds in every consistent world, licensing the monotonicity step.

That is the whole proof. **No simplices, no extreme points, no "modestly informed," no tie-breaking perturbation.** The diagonal problem of §1.2 evaporates at line 3: `thm:ccee` keeps each bet $O^j$ paired with *its own* selection weight $\alpha^j$ and swaps the bet for the future estimate of the bet, which is exactly the "the realized diagonal tracks the experts' verdicts" bridge that DDB must reconstruct by hand.

---

## 4. The trap: why it must be `thm:ccee`, not `thm:cee`

It is tempting to shortcut the proof using only the *unconditional* martingale `thm:cee` plus "future-linearity":

$$
\mathbb E_n(\widehat S_n)\overset{?}{\eqsim_n}\mathbb E_n\big(\mathbb E_{f(n)}(\widehat S_n)\big)
\overset{?}{\eqsim_n}\mathbb E_n\Big(\textstyle\sum_j\alpha^j_n\,\mathbb E_{f(n)}(O^j_n)\Big).
$$

The second step pulls the weights $\alpha^j_n$ out of the *future* expectation — and that is legal **only if the future self knows its own selection**, i.e. only if $\alpha^j_n$ is $\mathbb P_{f(n)}$-measurable in the strong sense that $\mathbb P_{f(n)}$ is *certain* of it. For a genuinely **modest** expert this fails. Concretely, in the anti-expert frame of §1.3 the future self at $a$ puts weight $.8$ on world $b$, where the selection is the *opposite*; one computes

$$
E_a(\widehat S)=-1 \quad\ne\quad \sum_j\alpha^j(a)\,E_a(O^j)=.6 .
$$

So future-linearity is *false* exactly when the expert is modest — and that is the same place the unconditional martingale was shown (§1.3) to be too weak. This is reassuring rather than alarming: it certifies that the clean proof is *not* secretly assuming immodesty. The work is being done by the genuinely stronger `thm:ccee`, which the anti-expert frame does **not** satisfy ($-.5\ne.3$, §1.3) — which is why the proof correctly refuses to "prove" Value there, Value being false there.

> **Locating modesty precisely.** The diagonal problem *is* the gap between `thm:cee` (which any stationary frame has) and `thm:ccee` (which only a coherent one has). Modesty lives in that gap.

---

## 5. Why it is clean in LI but cannot be clean on a finite frame

### 5.1 The criterion supplies the coherence for free

DDB note that Value is equivalent to a no-(fixed-option)-Dutch-book condition. LI's defining criterion *is* "no efficient trader earns unbounded profit" — a no-Dutch-book condition. So in LI the coherence that DDB extract from Total Trust by convex geometry is instead **built into what a logical inductor is**, and surfaces as the martingale theorems `thm:cee`/`thm:ccee` (each ~8 lines from the criterion via Persistence and Preemptive Learning, App. `app:ccee`). The convex-hull machinery is a *static stand-in for a dynamic no-arbitrage fact*; once the no-arbitrage fact is available directly, the geometry is unnecessary.

### 5.2 A modest, conditional-martingale reasoner is impossible on a finite frame

This is the structural heart of the matter.

> **Proposition (finite collapse).** Let $\langle W,\mathcal P\rangle$ be a **finite** frame and $\pi$ a novice. If the *soft* conditional martingale holds — for every bounded $X$ and threshold $t$,
> $$E_\pi\!\big(X\cdot \operatorname{Ind}_{\delta}(E(X)>t)\big)=E_\pi\!\big(E(X)\cdot\operatorname{Ind}_{\delta}(E(X)>t)\big)\quad\text{for all small }\delta>0,$$
> then the expert is **immodest** on $\pi$'s support: $P_w(P=P_w)=1$ for all $w\in W_\pi$.

*Proof.* On a finite frame the set $\{E_w(X):w\in W\}$ is finite, so for $\delta$ below the minimal gap and generic $t$, $\operatorname{Ind}_\delta(E(X)>t)=\mathbf 1[E(X)>t]$ at every world. As $X,t$ vary, these threshold events generate the expert $\sigma$-algebra $\mathcal P$ (distinct states $P_w\ne P_{w'}$ are separated by some $E(X)$). Hence the hypothesis gives $E(X)=E_\pi(X\mid\mathcal P)$, i.e. $P_w=\pi(\cdot\mid P=P_w)$. Taking $X=\mathbf 1[P=P_w]$ yields $P_w(P=P_w)=1$. $\qquad\blacksquare$

So on finite frames, the very property that makes the Value proof clean **forces immodesty** (indeed Reflection). A reasoner that is at once

- **modest** (does not know its own future verdicts — the cognitively realistic case), and
- **conditional-martingale-coherent** (so that deference equals value *cleanly*)

cannot exist when the expert's estimates take finitely many, gapped values. It requires the estimates to range without spectral gap — a **continuum** — i.e. an **infinite frame**. Logical induction supplies exactly this: a continuum of consistent completions $\mathcal{PC}(\Gamma)$, future estimates dense in their range, and — crucially — the *hard* conditional martingale stays permanently **false** (the liar sentence $\chi$: hard-conditioning on $\mathbb P_{f(n)}(\chi)\ge\tfrac12$ gives probability $0$, not $\ge p$). The soft version holds, the hard version fails, and the gap never closes. That permanent gap is the home of modesty.

> **Upshot.** The deference theorem is not a finite-frame artifact — but its *natural home is not finite frames either*. Its natural home is a modest-but-coherent reasoner, which is necessarily infinite and self-referential. LI is the first concrete inhabitant, and there the theorem is not merely true but cheap.

### 5.3 One picture (S4 / Blackwell–Geanakoplos)

The threads unify:

- **Partitional (S5), immodest:** Reflection; classical conditioning; both Trust and Value trivially hold.
- **Reflexive + transitive (S4), modesty allowed:** Geanakoplos value-of-information; DDB's "modestly informed"; Total Trust $=$ Value. DDB's hard direction $=$ "Total Trust forces S4 on $\pi$'s support."
- **Logical induction:** the future self is an S4-like (reflexive, transitive, non-Euclidean) refinement of the present self, realized in an infinite self-referential frame; the criterion enforces the S4 coherence dynamically, so Trust and Value both fall out via the martingale toolbox.

---

## 6. Weatherson's infinite failures are LI's two scope conditions

Weatherson breaks the equivalence in both directions. Each break exploits precisely one thing LI excludes for an independent reason.

**Coin (Total Trust without Value).** $W=\mathbb Z^+$, $\pi(F{=}x)=2^{-x}$, expert learns $F\ge x$; options $O_i$ pay $2^{i}$ on $\{F>i\}$. The diagonal return is $0$ everywhere while each column has positive expectation — a non-uniformly-integrable martingale. The driver is **unbounded utility**.
*LI excludes it:* expectations are defined only for **bounded** LUV-combinations ($\mathcal{BLCS}$ carries a uniform bound), and only **finite-risk** traders constrain the market. Boundedness is uniform integrability, which is what makes lines 1, 4 and 5 of the §3 proof legal. Weatherson's first failure is the case LI's boundedness rules out.

**Bentham (Value without Total Trust).** $W=\mathbb Z^+\cup\{\infty\}$, expert learns $F\le x$; Value holds as a limit of finite S4 sub-frames (Geanakoplos), but Total Trust fails at the single **measure-zero world $\{F=\infty\}$**, where the expert learns nothing yet $E(Y)=\tfrac23$ while $Y=0$. The driver is **hard conditioning on a null tail**.
*LI excludes it:* the self-trust theorems quantify over **finite** future days $f(n)$ with $n\to\infty$ (no "$\infty$" expert is ever instantiated) and condition only **softly** ($\operatorname{Ind}_{\delta_n}$, $\delta_n\to 0$). Weatherson's second failure is the case LI's soft, asymptotic conditioning rules out. (Note Weatherson *proves* Bentham's Value via finite S4 restrictions + a limit — the same Blackwell–Geanakoplos content LI keeps.)

So both pathologies map onto exactly the two technical restrictions LI imposes for reasons that have nothing to do with deference (finite risk; paradox-resistance). The immunity is principled.

| failure mode | DDB direction lost | driver | LI's excluding feature |
|---|---|---|---|
| **Coin** | Total Trust $\not\Rightarrow$ Value | unbounded utility | bounded LUVs / finite-risk traders |
| **Bentham** | Value $\not\Rightarrow$ Total Trust | null-tail hard conditioning | finite future $f(n)$ + soft `Ind`$_{\delta}$ |

---

## 7. The realizability payoff

The clean *finite* story (prior frames, partitions, Reflection) is a **realizable** one: the novice's candidate set $C_\pi$ literally contains the experts. Weatherson's normal-distribution example already strains this, and the deeper worry is that "narrow another agent's beliefs down to a known finite set" is cognitively fake.

LI earns the equivalence **without** a grain-of-truth assumption. The present self provably *cannot* contain a full model of its future self — that way lies the unexpected-hanging paradox — so the "expert" here is genuinely **larger than, and not realizable within,** the deferring agent. Yet deference-as-value still goes through, approximately and in a timely manner. A theorem that survives the removal of realizability, in the one setting we have where a finite mind reasons soundly about something bigger than itself, is a theorem about *deference* rather than about the bookkeeping of finite frames. That is the reassurance the finite proof could not, by itself, provide.

---

## 8. Caveats, scope, and open questions

**Status of §3.** "Value (LI form)" is *my* translation; it is not stated in the LI paper, though it is the decision-theoretic face of self-trust and is squarely in the tiling / Vingean-reflection register. The proof is given at the LI paper's level of rigor (free use of $\eqsim_n$). A fully formal version must discharge:

1. **Generability of $\alpha$.** $(\alpha^j_n)_n$ is market-generable (softmax of finitely many day-$f(n)$ prices); this is the same kind of future-state-dependent soft weight the paper uses right after `thm:ccee`.
2. **Linearity with generable real coefficients.** `thm:loe` is stated for p-generable *rational* coefficients; extending the two linearity steps to bounded market-generable *real* coefficients $\alpha^j_n$ (rational approximation absorbed by $\eqsim_n$, $k$ fixed) is routine but should be written out.
3. **Menu growth.** Need $\delta_n\log k_n\to 0$; trivial for fixed $k$.
4. **Boundedness.** Options are $[0,1]$-LUVs (or any fixed bounded range). Unbounded options are out of scope — and that is exactly Coin.

**Both directions.** The converse (Value $\Rightarrow$ Total Trust) is the easy DDB direction and has the same two-option witness in LI; but in LI it is moot, since Total Trust holds outright as the LUV-form of `thm:st`/`thm:ccee`. Both sides are theorems flowing from one source.

**Soft vs. hard, and ties.** The soft selection is not a mere convenience: the hard version is subject to the liar pathology (and to DDB's own Weak-Value-vs-Value tie-breaking, Lemma 7.5). Softening dissolves *both* the paradox and the tie-breaking ugliness at once — a second, independent way the LI rendering is cleaner.

**Open.**
- *Can the finite S4-extraction be made slick after all?* My suspicion is no — that the cleanliness genuinely requires getting the conditional martingale dynamically rather than from a static credence condition. A small impossibility/awkwardness result here would be worth having.
- *Local (question-relative) deference (DDB §5).* In LI this is deferring to the future self about a restricted class of LUVs. Since `thm:ccee` is already "local" in $X$, this may be the cleanest case of all, and would directly address DDB's open conjecture that local Total Trust $=$ local Value.
- *Quantitative version.* The $\eqsim_n$ wrappers hide rates; with explicit deferral functions one could ask for a finite-horizon "how much value is at stake" bound, closer to the tiling-theoretic use.

---

## 9. Machine-check

The finite, fully-rigorous skeleton of the §3 proof is machine-checked in
`deference-in-logical-induction-check.py` (Python 3.11 + `sympy`; exact rational
arithmetic throughout the algebra, so equalities are verified *exactly*). **18/18 checks pass.**

The check rests on isolating the proof's content as one **exact identity** plus one **clean
inequality**. For any finite frame, novice $\pi$, menu, and any weights $\alpha^j$ (summing to 1):

$$
\underbrace{E_\pi(\widehat S)-E_\pi(O^i)}_{\text{Value gap}}
\;=\;
\underbrace{\textstyle\sum_j\big(E_\pi(\alpha^j O^j)-E_\pi(\alpha^j E(O^j))\big)}_{D_{\mathrm{CM}}\ (\text{\texttt{thm:ccee}}\text{ defect})}
\;+\;
\underbrace{E_\pi(E(O^i))-E_\pi(O^i)}_{D_{\mathrm{UM}}\ (\text{\texttt{thm:cee}}\text{ defect})}
\;+\;
\underbrace{E_\pi(\bar m-m_i)}_{\ \ge\,-\delta\log k\ \ (\text{softmax})}.
$$

The LI theorems are exactly the statements that the three terms vanish ($D_{\mathrm{CM}},D_{\mathrm{UM}}\to 0$ via `thm:ccee`/`thm:cee`; the softmax term via $\delta_n\to 0$), whence Value. What is verified:

| | check | result |
|---|---|---|
| **A** | the identity above holds **symbolically for all frames** (sympy `expand`$=0$), shapes up to $4\times3$ | pure linearity; no frame hypothesis used |
| **B** | softmax bound $\bar m=L-\delta H(\alpha)\ge\max_j m_j-\delta\log k$ (20 000 trials) | Gibbs identity to $1.7\!\times\!10^{-15}$; bound never violated |
| **C** | DDB Fig. 2 & 3, exact | Fig. 2 Value fails; Fig. 3 Values; and the **§4 trap quantified**: anti-expert gap $-1 = D_{\mathrm{CM}}(-\tfrac85)+D_{\mathrm{UM}}(0)+\text{soft}(\tfrac35)$ — unconditional martingale intact, $D_{\mathrm{CM}}$ alone kills Value |
| **D** | conditional martingale $\Rightarrow$ Value, 3 000 random prior frames | 0 counterexamples; $D_{\mathrm{CM}}=D_{\mathrm{UM}}=0$ exactly |
| **E** | finite-collapse (§5.2), 20 000 random frames with nontrivial fibers | **0** frames both conditional-martingale and modest (classes both well-populated: 277 vs 11 421) |
| **F** | LI regime in miniature: modest, near-CM frames, soft selection | Value holds up to $|D_{\mathrm{CM}}|+|D_{\mathrm{UM}}|+\delta\log k$ in every row; error $\to0$ as perturbation, $\delta\to0$ |

### Lean (kernel-checked)

Formalized in **Lean 4.27.0 + Mathlib** (`lean-deference/LeanDeference.lean`), checked by the
Lean kernel. All theorems are **`sorry`-free** and depend only on the standard axioms
`[propext, Classical.choice, Quot.sound]` (verified by `#print axioms` — no `sorryAx`). Three parts.

**(a) The actual §3 argument, modulo the LI results** — `DeferenceAsymp.value_asymptotic`.
The `≂ₙ`/`≳ₙ` calculus is modeled honestly as real-sequence asymptotics:
`a ≂ₙ b := (aₙ-bₙ)→0` and `a ≲ b := ∀ε>0, eventually aₙ ≤ bₙ+ε` (so `b ≳ₙ a`). The five
Logical-Induction results enter as **explicit hypotheses** (we trust the paper, we don't
re-prove it), and Value is derived in this calculus:

| hypothesis | LI result |
|---|---|
| `hAdd1`, `hAdd2`: `E_now(Ŝ) ≂ₙ ∑ⱼ E_now(αⱼOⱼ)`, `∑ⱼ E_now(αⱼ·E_later Oⱼ) ≂ₙ E_now(∑ⱼ αⱼ·E_later Oⱼ)` | thm:loe (linearity) |
| `hCcee`: `∀j, E_now(αⱼ Oⱼ) ≂ₙ E_now(αⱼ · E_later Oⱼ)` | **thm:ccee** (No Expected Net Update under Conditionals) |
| `hCee`: `∀j, E_now(E_later Oⱼ) ≂ₙ E_now(Oⱼ)` | thm:cee (No Expected Net Update) |
| `hδ`,`hSoft`: `E_now(E_later Oⁱ) ≤ E_now(∑ⱼ αⱼ·E_later Oⱼ) + δₙ`, `δₙ→0` | thm:expprovind ∘ softmax bound *(softmax half now proved — see (c))* |

> **conclusion** `E_now(Oⁱ) ≲ E_now(Ŝ)`, i.e. **`E_now(Ŝ) ≳ₙ E_now(Oⁱ)` = Value**.

The proof is the §3 chain verbatim: `E_now(Ŝ) ≂ₙ ∑ a ≂ₙ ∑ b ≂ₙ c ≳ₙ E_now(E_later Oⁱ) ≂ₙ E_now(Oⁱ)`,
with the supporting `≂ₙ`/`≳ₙ` lemmas (reflexivity, symmetry, transitivity, `≂ₙ`-refines-`≲`,
finite-sums-respect-`≂ₙ`) proved from Mathlib's `Filter`/`Tendsto` API. This is the sense in
which the §3 proof is machine-checked: **its composition of the LI theorems is valid**.

**(b) The finite exact backbone** — `Deference.*` (the $\delta=0$ / defects-$=0$ shadow):
- `decomposition` — the keystone identity $\text{gap}_i = D_{\mathrm{CM}}+D_{\mathrm{UM}}+\text{soft}_i$ over an arbitrary `CommRing`, for **all** finite `Fintype` $W,J$ and all $\pi,P,O,\alpha$ (upgrading sympy check **A** from sampled shapes to a universal statement). Proof: `simp only [mul_sub, Finset.sum_sub_distrib]; ring`.
- `value_of_CM` — *conditional martingale $\Rightarrow$ Value*, exact finite, via `value_of_defects` + `soft_nonneg`.

**(c) Two supporting facts, now proved (not assumed)** — `DeferenceExtra.*`:
- `softmax_lower_bound` — $\sum_j \operatorname{softmax}(\delta,m)_j\, m_j \ge m_i - (\operatorname{card} J)\,\delta$ for $\delta>0$, from `Real.add_one_le_exp` alone. This discharges the analytic half of `hSoft`, so the facts the §3 derivation still *assumes* are exactly the genuine LI theorems (thm:loe, ccee, cee, expprovind). (The note's tight constant $\delta\log(\operatorname{card} J)$ is the entropy bound; the cruder $(\operatorname{card} J)\,\delta$ proved here is all the $\delta\to0$ limit needs.)
- `CM_implies_immodest` — the core of §5.2: if the conditional-martingale identity $E_w(X)=E_\pi(X\mid \text{fiber } w)$ holds at $w$, then $P_w(\text{fiber } w)=1$ (immodesty), by instantiating it at the fiber's own indicator. (The soft-$\Rightarrow$-hard "no spectral gap" reduction — the step that needs an infinite frame — is left as §5.2's prose.)

**Not checked** (and not checkable without formalizing the Logical Induction paper): that the
genuine theorems `thm:ccee`/`thm:cee` actually force $D_{\mathrm{CM}},D_{\mathrm{UM}}\to0$, and
the $\eqsim_n$ bookkeeping. So this verifies the proof's *algebra and its finite mathematical
core* — the part that could harbor a composition bug — but not the asymptotic LI layer the
core is wrapped in. Check **C** is the most diagnostic: it confirms exactly, on DDB's own
counterexample, that the Value failure is the conditional-martingale defect and that the
unconditional martingale (the tempting shortcut of §4) is satisfied there — so the proof must
use `thm:ccee`, not `thm:cee`.

---

## References

- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better,"** *Philosophical Perspectives* 35 (2021). — Total Trust $\Leftrightarrow$ Value (Thm 2.2), characterization (Thm 4.1, 5.1), Appendix B proofs.
- B. Weatherson, **"Deference and Infinite Frames,"** *Australasian Journal of Logic* (2025). — Coin and Bentham counterexamples (§3); Geanakoplos non-extension (§2).
- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016). — Expectations (§4 / `thm:cee`–`thm:ccee`), Introspection (`thm:epr`,`thm:er`), Self-Trust (`thm:st`); construction and the logical-induction criterion (§2, §5).
- J. Geanakoplos, "Game Theory Without Partitions…" (1989/2021); D. Blackwell, "Equivalent Comparisons of Experiments" (1953). — reflexive/transitive/nested $\Rightarrow$ value of information.
