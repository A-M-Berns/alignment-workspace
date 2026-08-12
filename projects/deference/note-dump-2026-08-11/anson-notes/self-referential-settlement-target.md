# The Self-Referential Settlement Target: Why "Self-Trust Through a Mirror" Dies, and What Survives

*A standalone note expanding §2.2 of the "Trust Between Logical Inductors" technical summary (Anson, with Abram Demski). It formalizes — in the genuine logical-induction (LI) setting of Garrabrant et al. (2016), taking the LI paper's own theorems as black boxes — the dead end of settling deference contracts against the novice's **own future credence** $Y_n = H^+_{F(n)}(P^{(n)})$: the two independent impossibilities (2a anti-inductive, 2b cost-circularity), the dichotomy they force ("predictable iff uninfluenced"), and the precise residue that survives. Companion to [`deference-in-logical-induction-v4.md`](../notes/deference-in-logical-induction-v4.md), whose conventions and status discipline it follows.*

> **About this document.** I write it wearing three hats. As **historian**: this records *why* the project pivoted off its most natural first idea — and a wrong sub-attempt (a ChatGPT "divergence" construction, §6) refuted along the way — so a future reader meets the impossibilities before the repair and sees the repair as *forced*. As **mathematician**: every claim is flagged **[proved]** (elementary and verified here), **[sketched at LI level]** (rigorous modulo named LI theorems and one explicitly-flagged soft joint), or **[interpretation]**. The arithmetic core of 2a is genuinely elementary and is proved in full; 2b's cost-accounting has one load-bearing step the source rates at ~75–80% confidence, and I flag it as such rather than dressing it up. As **analytic philosopher**: §7–§8 say what the dichotomy *means* — for manipulation, epistemic autonomy, and the relation to performative prediction — without letting the philosophy outrun the theorems.
>
> The arguments here are now **machine-checked** in Lean 4 + Mathlib — see §10 ([`../lean-deference/SelfReferentialTarget.lean`](../lean-deference/SelfReferentialTarget.lean)), kernel-checked and `sorry`-free, with the LI-paper theorems entering only as named hypotheses (the v4 development's discipline). The v4 note studies the *positive* tower; this note studies an *obstruction* to forcing it across two processes, and is the concrete LI face of v4 §11's "for a distinct process the tower must be *earned*, not assumed."

---

## 0. Setting: the construction, in the real LI framework

### 0.1 The objects, and the LI theorems taken as black boxes

Fix a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$, a consistent theory $\Gamma$ able to represent computable functions, and a $\Gamma$-complete **computable** deductive process $D=(D^t)_{t\ge1}$ revealing $\Gamma$'s consequences over time. A sentence is **decidable** if $D$ settles it; its settled value is its truth value (the only notion of truth here). Fix complexity classes $\mathcal{C}_H\subseteq\mathcal{C}_A$ (canonically $\mathrm{P}\subseteq\mathrm{EXP}$), each closed under polynomial overhead.

A **logical inductor** over a computable deductive process, against a trader class $\mathcal{C}$, is a computable sequence of belief states $\mathbb{P}=(\mathbb{P}_t)$ satisfying the logical-induction criterion: no $\mathcal{C}$-trader exploits the market. We use, as named black boxes (citations to Garrabrant et al. 2016):

- **(LI-Exist)** Existence over any computable deductive process — Thm 3.6.1.
- **(LI-Crit)** The no-Dutch-book criterion itself — Def 3.0.1 / §3.5: a sequence is an inductor iff no $\mathcal{C}$-trader has plausible profits unbounded above while bounded below.
- **(LI-PI)** Provability Induction / Persistence — Thm 4.2.1, and its expectation form Thm 4.8.10: a uniformly $D$-provable bound is honored by the day-$n$ price/estimate in a timely manner. In particular prices **converge to truth on decided sentences**.
- **(LI-Coh)** Limit Coherence — Thm 4.1.1: $\mathbb{P}_\infty$ is a coherent probability measure on $\mathrm{PC}(\Gamma)$.
- **(LI-ND)** Non-Dogmatism — Thm 4.6.2: $\Gamma\nvdash\varphi\Rightarrow\mathbb{P}_\infty(\varphi)<1$ and $\Gamma\nvdash\neg\varphi\Rightarrow\mathbb{P}_\infty(\varphi)>0$; with a complexity-graded uniform margin (Uniform Non-Dogmatism, Desideratum 7 / the quantitative form).
- **(LI-Cont)** Trader **continuity**: legal trading strategies are continuous expressible features of finitely many prices; this is what defuses the diagonal/liar sentence at the *sentence* level (LI §3.4, §4.11). It is the escape that §2 shows is unavailable at the *settlement* level.
- **(LI-χ)** The diagonal sentence $\chi\leftrightarrow(\mathbb{P}_{?}(\chi)<\tfrac12)$ is *benign*: continuity (LI-Cont) lets the market clear at price $\tfrac12$ (LI §3.4; cf. Garrabrant, "The Set of Logical Inductors Is Not Convex").

Asymptotics follow v4: $x_n\eqsim_n y_n:\Leftrightarrow x_n-y_n\to0$; $x_n\gtrsim_n y_n:\Leftrightarrow\liminf(x_n-y_n)\ge0$. "Timely" = up to a vanishing error as $n\to\infty$. **Efficiently computable (e.c.)** and **market-generable** are as in v4 §0.1.

### 0.2 The coupled construction with the self-referential target

This is Anson's construction (final clean form; see the chat corpus, file `08_2026-06-02_paper-revision-thm.md`, and the index in [`anson-notes/INDEX.md`](INDEX.md)). Three reasoners:

- $H$ — the weaker reasoner ("evolving human opinion"), an inductor over $D$ against $\mathcal{C}_H$.
- $H^+$ — $H$ **augmented to read $A$'s published quotes**, an inductor against $\mathcal{C}_H$ over an extended process (below). This is the *realistic* reasoner: the human who has heard the AI.
- $A$ — the stronger reasoner, an inductor against $\mathcal{C}_A$, built to **predict $H^+$'s future credence**.

Schedules: a strictly increasing $\mathcal{C}_H$-computable **deferral** $F$ with $F(n)>n+1$, an **emission** $e$, and a **settlement** $\sigma$, ordered $e(n)<F(n)<\sigma(n)$. Fix an effective enumeration $P^{(0)},P^{(1)},\dots$ of the contracts of interest (the choice of enumeration is free and will matter in §2.5).

**Threshold encoding of a real to a $1/n$-grid.** For each $n$ and $1\le k\le n$, fresh atoms $\theta_{n,k}$ ("the deferred value of contract $n$ is $\ge k/n$") and $\beta_{n,k}$ ("$A$'s published quote for contract $n$ is $\ge k/n$"), with monotonicity axioms $\theta_{n,k}\to\theta_{n,k-1}$, $\beta_{n,k}\to\beta_{n,k-1}$. $A$'s language is $\mathcal{L}^\theta=\mathcal{L}\cup\{\theta_{n,k}\}$; $H^+$'s language is $\mathcal{L}^+=\mathcal{L}\cup\{\beta_{n,k}\}$. The affine combinations
$$
C_n:=\tfrac1n\textstyle\sum_{k=1}^n\theta_{n,k},\qquad R_n:=\tfrac1n\sum_{k=1}^n\beta_{n,k}
$$
read off grid-rounded reals from a consistent world. $A$'s **published quote** is $a_n:=A_n(C_n)\in\mathbb{Q}\cap[0,1]$, emitted at $e(n)$.

**The settlement target (the object of this note).**
$$
\boxed{\;Y_n:=H^+_{F(n)}(P^{(n)})\;}
$$
— the contract for $P^{(n)}$, deferred to stage $F(n)$, settles against **$H^+$'s own future credence**. $A$'s contracts are settled (via the profile $\Theta_n(m^\ast_n)$, $m^\ast_n:=\arg\min_m|m/n-Y_n|$, ties low, so $|m^\ast_n/n-Y_n|\le \tfrac1{2n}$) at $\sigma(n)$, by which time $Y_n$ is available since $\sigma(n)>F(n)$. The augmented process $D^+_H$ extends $D$ with the $\beta$-monotonicity axioms and the one-step-delayed $\beta$-ledger profiles $\widehat\Theta_i(\ell^\ast_i)$ recording $A$'s rounded quotes ($\ell^\ast_i:=\arg\min_\ell|\ell/i-a_i|$), so the readout $R_n$ is **decided by $n+1<F(n)$**. The four sequences are defined by one well-founded recursion on $t$ (each stage-$t$ object depends only on strictly earlier stages).

**The power assumption (the load-bearing idealization).** $\mathcal{C}_A$ is asked to contain $n\mapsto Y_n$ — equivalently $n\mapsto R(F(n))$, where $R(t)$ is the cost of running the **coupled** construction through stage $t$ ($a_n$ is a stage-$n$ object so it costs $R(n)$; $Y_n$ is a stage-$F(n)$ object so it costs $R(F(n))$). §3 shows this assumption is exactly the problem.

### 0.3 Dictionary

| this note ($H,H^+,A$) | v4 ($E_n$ novice, $E^\ast$ expert) | DDB |
|---|---|---|
| weaker reasoner $H^+$ (the one who defers) | novice $E_n$ | $\pi$ |
| stronger reasoner $A$ (deferred to) | expert $E^\ast$ | the frame $\mathcal P$ |
| Tracking $a_n\eqsim_n Y_n$ | the tower $\mathrm{Mart}(N\to E^\ast)$ for the **self-instance** | the deference equality |
| **self-referential** target $Y_n=H^+_{F(n)}(P^{(n)})$ | "expert = my own future self" pushed onto an *external* $A$ | — |

A structural remark worth stating once: v4's clean case is the future self, where the tower is the *free* LI theorem `cee`. Anson's $A$ is a **distinct, stronger** process; the self-referential target is precisely an attempt to *manufacture* a self-like tower across the gap — to make the external $A$ a mirror of $H^+$'s own future. (The dictionary aligns processes by *deference* direction — who adopts whose verdict — not by information flow: v4's novice reasons about the expert, whereas here the expert $A$ predicts the novice $H^+$'s future, so the self-referential target models "the expert predicting the novice's own future self," a structure with no direct v4 analog.) v4 §11 already flags that for a distinct process the tower "must be earned, not assumed." §2 below is the sharp LI statement of *why this particular way of trying to earn it cannot work* — the mirror coupling is not merely unproven but, headline-form, impossible.

---

## 1. The idea, and its appeal: self-trust through a mirror

Why settle against $H^+$'s own future credence rather than against the world? Because it models the case we actually care about: a bounded human who *has heard the AI* and wants to use the AI's extra compute to reach **its own** trusted future conclusions faster. If $A$'s quote $a_n$ reliably equals $H^+$'s eventual verdict $Y_n$, then "defer to $A$" is literally "defer to your own better-thought-out future self, read off a fast instrument" — Garrabrant self-trust (LI Thm 4.12) routed through $A$. The headline one would want is:

> **Universal pointwise (timely) Tracking — predictive exactness (the claim to be killed).** Over the effective enumeration $(P^{(n)})$,
> $$ a_n-Y_n\;\eqsim_n\;0,\qquad\text{equivalently}\qquad A_n(C_n)-H^+_{F(n)}(P^{(n)})\to0, $$
> and *timely* — enforced at stage $n$, so $a_n$ is an accurate **prediction** of $Y_n$, not merely an after-the-fact echo.

> **Terminology — Tracking, not calibration.** I call this property **Tracking** (predictive exactness: the forecast lands on the realized value, contract by contract), *not* calibration. Standard **calibration** is the weaker *no-predictable-adjustment* property — conditional on the forecast being ≈ $p$, the realized average is ≈ $p$; equivalently, the identity is the best post-hoc remap of forecasts. Tracking ⟹ calibration, never the converse. What §2–§3 kill is **Tracking**; genuine *calibration* (the gated and statistical forms) survives (§3.4, §5.2) and is the ceiling.

It has two faces, both attractive and both genuinely distinct:

- **Pointwise Tracking (predictive exactness):** $A$'s quote lands on $H^+$'s future credence on every contract, per instance.
- **Externalized self-trust:** $H^+$, conditioning on $A$'s *recorded* quote $R_n$, holds the corresponding credence in $P^{(n)}$ now — the conditional/inequality face (the analog of DDB Total Trust, v4 §3).

§2–§3 kill the **universal pointwise timely** form of the first face, twice over and for independent reasons. §5 shows the second face survives in a precise, weaker, *conditional* sense — and that this survival is exactly "self-trust through a mirror," real but unable to carry a Tracking headline.

---

## 2. Negative result 2a — the anti-inductive settlement

**Claim.** With the self-referential target, if the contract enumeration may range over $\mathcal{L}^+$ (sentences that can mention $A$'s quote), universal pointwise tracking is **false** — there is a $\mathcal{C}_H$-computable subfamily on which $\liminf_n|a_n-Y_n|\ge\tfrac12$ — and this holds **independent of $A$'s computational power**, an oracle for $A$ included.

### 2.1 The arithmetic core **[proved]**

The whole phenomenon is one elementary fact about a discontinuous self-map.

> **Lemma 2.1 (no exact quote).** Let $\rho:[0,1]\to\{0,1\}$, $\rho(a)=\mathbb{1}[a\le\tfrac12]$. Then
> $$\inf_{a\in[0,1]}\,\bigl|a-\rho(a)\bigr|=\tfrac12,$$
> attained only at $a=\tfrac12$. In particular there is **no** $a$ with $|a-\rho(a)|<\tfrac12$.

*Proof.* If $a\le\tfrac12$ then $\rho(a)=1$ and $|a-1|=1-a\ge\tfrac12$. If $a>\tfrac12$ then $\rho(a)=0$ and $|a-0|=a>\tfrac12$. So $|a-\rho(a)|\ge\tfrac12$ for all $a$, with equality iff $a=\tfrac12$. $\qquad\blacksquare$

The exactness equation $a=\rho(a)$ is unsatisfiable, and not marginally: the residual is bounded below by $\tfrac12$ *everywhere*. This is the entire obstruction; everything in §2.2 is bookkeeping to install $\rho$ as a settlement. Note the convention is irrelevant — $\rho(a)=\mathbb 1[a<\tfrac12]$ gives the same bound (equality again $\tfrac12$, now approached from below).

The lift in §2.2 settles against the *recorded* (grid-rounded) quote $r$, not $a$ itself, so we need the rounding-robust form:

> **Lemma 2.1′ (rounding-robust).** For $a\in[0,1]$ and any $r$,
> $$\tfrac12-|r-a|\;\le\;\bigl|a-\rho(r)\bigr|.$$
> It specialises to Lemma 2.1 at $r=a$. (Lean: `residual_lb`.)

*Proof.* If $r\le\tfrac12$ then $\rho(r)=1$ and $|a-1|=1-a$ (as $a\le1$), and $1-a\ge\tfrac12-|r-a|$ because $a-\tfrac12\le a-r\le|r-a|$. If $r>\tfrac12$ then $\rho(r)=0$ and $|a|=a$ (as $a\ge0$), and $a\ge\tfrac12-|r-a|$ because $\tfrac12-a\le r-a\le|r-a|$. $\qquad\blacksquare$

### 2.2 Installing $\rho$ as a settlement: the anti-inductive contract **[sketched at LI level]**

Because the $\beta$-atoms recording $a_n$ live in $H^+$'s own language $\mathcal{L}^+$, the predicate "$R_n\le\tfrac12$" is a sentence of $\mathcal{L}^+$, and $R_n$ is **decided by $D^+_H$** at stage $n+1$ (the $\beta$-ledger). Exploit the freedom in the enumeration: let $P^{(n)}$ be a fresh atom $g_n$ with the $D^+_H$-axiom
$$
g_n\;\leftrightarrow\;\bigl(R_n\le\tfrac12\bigr),
$$
inserted once the ledger settles (stage $\le n+2$). Then $g_n$ is **decided by $F(n)$** to the truth value $\mathbb{1}[r_n\le\tfrac12]$, where $r_n=\ell^\ast_n/n$ is the rounded quote, $|r_n-a_n|\le\tfrac1{2n}$.

Now $H^+$ is an inductor over $D^+_H$, and $g_n$ is decided by $F(n)$, so by **(LI-PI)** prices converge to truth on decided sentences in a timely manner:
$$
Y_n=H^+_{F(n)}(g_n)=\mathbb{1}[r_n\le\tfrac12]+\eta_n,\qquad \eta_n\to0.
$$
Combining with **Lemma 2.1′** (using $|r_n-a_n|\le\tfrac1{2n}$, so $|a_n-\rho(r_n)|\ge\tfrac12-\tfrac1{2n}$) and the triangle inequality $|a_n-Y_n|\ge|a_n-\rho(r_n)|-|\eta_n|$:
$$
\boxed{\;\bigl|a_n-Y_n\bigr|\;\ge\;\tfrac12-\tfrac1{2n}-|\eta_n|\;=\;\tfrac12-o(1)\;}\qquad\text{for every }n.
$$
Hence $\liminf_n|a_n-Y_n|\ge\tfrac12$: timely tracking is violated by a *constant* margin. The subfamily $(g_n)$ is $\mathcal{C}_H$-computable (it is built from the $\beta$-ledger by an $O(n)$ rule), so it is a legitimate member of any effective enumeration that admits $\mathcal{L}^+$-sentences. $\qquad\blacksquare$

This is the **$\chi$-paradox transplanted from the sentence level to the settlement level.** At the sentence level the diagonal $\chi\leftrightarrow(\mathbb{P}(\chi)<\tfrac12)$ is benign (LI-χ); here the diagonal is one level up — the *settlement* of $g_n$ is the anti-inductive response to $A$'s *price* $a_n$.

### 2.3 Why the continuity escape is gone

At the sentence level, **(LI-Cont)** saves the market: a trader's demand for $\chi$ is a *continuous* function of the price, so Brouwer hands back a clearing price (exactly $\tfrac12$), and no contradiction survives. The settlement map has no such cushion, for two independent reasons:

1. **A deductive process is a hard $0/1$ oracle.** $g_n$'s settled value is decided by $D^+_H$; it is $0$ or $1$, never an interpolated $\tfrac12$. There is no continuity property of settlement to invoke.
2. **Grid-rounding is discontinuous by construction.** Even were the underlying target real-valued, $m^\ast_n/n$ is a step function of $a_n$.

So the would-be fixed point at $a_n=\tfrac12$ is *not* a fixed point: $\rho(\tfrac12)=1\ne\tfrac12$. Lemma 2.1 says the best any quote achieves is residual exactly $\tfrac12$, attained by playing $a_n=\tfrac12$ — and that is *still a failure of tracking*. The continuity that makes self-reference survivable at the sentence level is precisely what the threshold/deductive settlement architecture removes.

### 2.4 Independence of compute **[proved, given §2.2]**

Nothing in §2.1–§2.2 mentions $A$'s resources. The obstruction is the *non-existence of an exact quote*, not the difficulty of finding one. Grant $A$ a halting oracle: it computes a better $a_n$, but Lemma 2.1 still forbids $|a_n-Y_n|<\tfrac12$, because the settlement is *defined to be the anti-inductive negation of whatever $a_n$ is*. This is the sharp sense in which 2a is "false even with free compute" — and it is the feature that distinguishes 2a from 2b (§3), which *is* a statement about resources.

### 2.5 Scope: the counterexample needs a quote-referencing family **[proved]**

Lemma 2.1 is installed (§2.2) only because $g_n$ can *mention* $a_n$ — the $\beta$-atoms are in $\mathcal{L}^+$. If one restricts the enumeration to **quote-free** base sentences $P^{(n)}\in\mathcal{S}$, no $P^{(n)}$ can encode $\mathbb{1}[a_n\le\tfrac12]$, and the explicit counterexample is blocked. Crucially, this does **not** rescue the headline: it makes universal pointwise tracking *underivable*, not *true* (one has removed a refutation, not supplied a proof). And on quote-free families the second impossibility, 2b, still bites (§3.3, §3 closing) — because $Y_n=H^+_{F(n)}(P^{(n)})$ depends on $A$'s run through the ledger $H^+$ has absorbed by $F(n)$, whatever $P^{(n)}$ is. This complementarity — *2a kills the quote-referencing case by refutation, 2b kills the quote-free case by unsatisfiability* — is what "dead twice over" means precisely.

---

## 3. Negative result 2b — cost-circularity

**Claim.** *Timely per-instance* tracking requires a power assumption on $\mathcal{C}_A$ that is **unsatisfiable**: the class would have to contain its own coupled simulation cost. This is independent of 2a (it does not need quote-referencing contracts) and is a statement about **satisfiability of the hypothesis**, not about a fixed false target.

### 3.1 The timely requirement and the coupled cost **[sketched at LI level]**

$Y_n=H^+_{F(n)}(P^{(n)})$ is a stage-$F(n)$ object of the *coupled* system: $H^+$ at $F(n)$ has absorbed quotes $a_i$ for all $i$ with $e(i)<F(n)$, and since $e(i)\ge i$ and $F(n)$ outruns $n$, this includes indices $i>n$ — i.e. some of $A$'s **own future** quotes. So computing $Y_n$ means forward-simulating the coupled construction to $\sim F(n)$, at cost $\Theta(R(F(n)))$.

Timeliness is the crux. **(LI-Crit)** delivers $a_n\eqsim_n Y_n$ *at stage $n$* only if some $\mathcal{C}_A$-trader can **detect** stage-$n$ mispricing — i.e. compute (an estimate of) $Y_n$ by stage $n$. So the power assumption "$\mathcal{C}_A\ni n\mapsto Y_n$" is not optional decoration: it is what would make the timely theorem derivable.

### 3.2 The regress — and the correction the summary compresses **[sketched at LI level; one soft joint flagged]**

The naive chain (as Anson first wrote it):

1. Computing $Y_n$ at stage $n$ costs $\Theta(R(F(n)))$ (§3.1).
2. Timely tracking ⟹ a $\mathcal{C}_A$-trader computes $Y_n$ at stage $n$.
3. $A$ (inductor vs $\mathcal{C}_A$) "must run that trader to be inexploitable by it," so $R_A(n)\gtrsim R(F(n))$.
4. $R(F(n))\ge R_A(F(n))$ (total $\ge$ $A$'s share); with $R_A$ increasing and $F(n)>n$,
$$
\boxed{\;R_A(n)\;\gtrsim\;R(F(n))\;\ge\;R_A(F(n))\;>\;R_A(n)\;}
$$
a contradiction. So the power assumption $\mathcal{C}_A\ni R\circ F$ is **unsatisfiable**, not merely strong.

> **The correction (knowledge-historian's duty).** Step 3 *as stated* is wrong, and the summary's compact "$\mathcal{C}_A\ni R\circ F\Rightarrow R_A(n)\gtrsim R_A(F(n))>R_A(n)$" hides this. Inexploitability is a property of the price *sequence* (LI-Crit); nothing forces a market to *incur its traders' runtimes* (the LIA construction clocks traders, but LIA is sufficient, not necessary). The conclusion nonetheless survives via a cleaner, **order-theoretic** argument. If $\mathcal{C}_A\ni R\circ F$ and $R(F(n))\ge R_A(n)$, then $\mathcal{C}_A$ contains a trader that **simulates $A$'s own stage-$n$ market with slack**; and because $D_A$'s settlements are *entangled with $A$'s prices* (they settle $C_n$ against $m^\ast_n\approx Y_n$, and $Y_n$ depends on $A$'s quotes through $H^+$), this simulate-and-arbitrage trader **reflectively exploits $A$** — the $\chi$-paradox weaponized at the level of $A$'s prices. No fixed-point/ordinal-tower class escapes, because the obstruction is the position of the class in the *simulability preorder* (the market always sits strictly above its own trader class), not a growth rate. **Soft joint:** the source rates the whole cost-accounting at ~75–80%, with step 3 — does inexploitability force $A$ to pay the simulating trader's full runtime, or does budgeting / the $2^{-k}$ weighting open a gap? — the place a rescue might live. I therefore record 2b as: *the timely power assumption is self-defeating given that $D_A$'s settlements are entangled with $A$'s prices*, with that entanglement (guaranteed by the self-referential target) the indispensable hypothesis.

### 3.3 Underivable vs. false **[interpretation]**

2b is categorically unlike 2a. 2a exhibits a *false* instance (a fixed family on which tracking provably fails, §2.4). 2b does not refute timely tracking on a benign family; it shows the *only known route to a proof* (the power assumption) is contradictory. **(LI-Crit)** gives a timely conclusion only when an in-class trader *can* enforce it; if none can exist (the regress), the theorem is **underivable**, not disproven. One checks the cheap alternative routes and they all fail for the self-referential target: provability induction needs an e.c.-writable theorem sequence, but "$C_n=m^\ast_n$" can't be written before $m^\ast_n$ is computed; affine coherence transfers only $D$-provable relations, and "$a_n=Y_n$" is not $D$-provable; self-trust gives only $A$'s *subjective* martingale $a_n\approx\mathbb{E}^A_n[Y_n]$, not objective per-instance accuracy. So 2b's honest content is "no satisfiable hypothesis of this shape," which is why the *constructive* response (blindness, §4) is the right move rather than a search for a better proof.

### 3.4 The strength hierarchy: tracking dies, calibration survives **[sketched at LI level]**

2b is surgical — it removes exactly the *timely per-instance* notion. Two weaker notions survive untouched, and naming them is essential to not over-claiming the negative:

| notion | content | verdict | why |
|---|---|---|---|
| **timely / per-instance (Tracking)** | $a_n\eqsim_n Y_n$ enforced at stage $n$ | **dies** (unsatisfiable power assumption) | needs a $\mathcal{C}_A$-trader computing $Y_n$ early ⇒ regress §3.2 |
| **eventual** | $A_{\sigma(n)}(C_n)\to$ settled value | survives, but **near-tautological** | a trader merely *waits* for $\sigma(n)$; the contract settles *to* that value — no prediction |
| **statistical (Calibration)** | $A$ learns the pseudorandom *frequency* of $H^+$-values across the family | survives, **real and free** | Learning Pseudorandom Frequencies (LI §4.4); no forward simulation |

The honest retreat: what genuinely survives is statistical calibration (and the near-tautological eventual form), never per-instance tracking. The tempting escape — get prediction from self-trust instead of simulation — only relocates the wall: self-trust gives $a_n\approx\mathbb{E}^A_n[Y_n]$, which equals $Y_n$ only insofar as $Y_n$ is cheaply predictable, i.e. the statistical fragment again.

---

## 4. The dichotomy these force: *predictable iff uninfluenced*

### 4.1 Reflective blindness, defined **[interpretation]**

> **Definition (reflective blindness).** The construction's settlement map $n\mapsto m^\ast_n$ (the value $D_A$ writes to settle $C_n$) is **reflectively blind** if it factors through $A$-free data — a function of $n$ and $H$'s autonomous run alone — equivalently if $D_A^t$ is invariant under replacing $A$ by any other market over $D_A$: $\partial D_A/\partial A=0$. Blindness makes $(D_A,A)$ definable in a strict stage order (a DAG) rather than by mutual recursion.

The self-referential target *violates* blindness, indirectly but really: $Y_n=H^+_{F(n)}(P^{(n)})$ and $H^+$'s process records the $\beta$-encoded quotes, so $m^\ast_n$ is a function of $A$'s own prices *through the human channel*.

### 4.2 The dichotomy **[sketched at LI level; contrapositive of §2+§3]**

> **Theorem 4.2 (predictable iff uninfluenced).** Suppose the contract family is **effective** (universally quantified over an enumeration, as a tracking theorem must be — a theorem for hand-picked contracts is not one) and suppose universal **pointwise timely** tracking is provable from a **satisfiable** power assumption. Then the settlement map is reflectively **blind**.

*Argument (the two impossibilities as one contrapositive).* Suppose the settlement *depends* on $A$'s quotes. If the effective family may reference quotes, §2 builds an anti-inductive instance with $|a_n-Y_n|\ge\tfrac12-o(1)$, so tracking is *false* — contradiction. If the family is restricted to be quote-free to dodge §2, the dependence runs through $H^+$'s absorbed ledger, so a *satisfiable* power assumption would still have to compute the coupled $Y_n$ early, triggering §3's regress — so tracking is *underivable* from a satisfiable hypothesis, contradiction. Either way, A-dependence is incompatible with (effective ∧ provable-from-satisfiable ∧ timely-pointwise). Hence blindness. $\qquad\blacksquare$

Blindness is therefore **derived, not assumed** — the constructive half of a dichotomy. The slogan: a settlement you can *predict* (timely, universally, affordably) is one the predictor cannot *influence*.

### 4.3 The repair: the autonomous target as the canonical blind instance **[sketched at LI level]**

The contrapositive points straight at the fix. Retarget contracts at the **autonomous** human:
$$
\boxed{\;Y_n:=H_{F(n)}(P^{(n)})\;}\qquad(H\text{ never reads }A).
$$
This zeroes $\partial D_A/\partial A$: $H$ is upstream of $A$, the mutual recursion collapses to a staged DAG ($H\to A\to H^+$), and both diseases vanish at once. **2b dodged:** computing $Y_n$ costs $R_H(F(n))$, an $A$-free fixed computable function, so "$\mathcal{C}_A\supseteq\mathrm{DTIME}(c\cdot R_H\circ F)$" is a *satisfiable definition* with a trivial fixed point. **2a dodged:** $H$'s language has no quote atoms, so no contract can encode $\mathbb{1}[a_n\le\tfrac12]$; the anti-inductive instance is *structurally absent*. This is "Channel P" (summary §3–§4); it is why the project dropped universal/measure-valued inductors and the self-referential headline together.

The honest price (the "size of the bullet"): the *predicted* human ($H$, unadvised) and the *advised* human ($H^+$, real) are now different objects, so the headline is a **counterfactual** — $A$ predicts what the human *would have* concluded unadvised. §7–§8 defend this as principled rather than evasive.

### 4.4 Scope caveat: an escape hatch this note does not take **[interpretation]**

The dichotomy is internal to *this architecture* — LI markets, deductive-process (hard $0/1$) settlement, grid rounding. The one structural escape is **continuous, unrounded (LUV-style) settlement with fixed-point selection**, where per-$n$ self-consistent quotes can exist by Brouwer. The reasons to leave it in the discussion rather than the proof: continuity buys *existence* of a self-consistent quote, not a theorem that $A$'s market *locates* it; the LUV machinery re-imports everything the threshold encoding was built to avoid; and the performative-prediction literature shows the fixed points that exist need not be the ones anyone wants. So, fully chewed: blindness is provably necessary for the theorem one wants *within the architecture one has*, and the architecture's one alternative is a known swamp.

---

## 5. What is *not* killed

The negative results are about the **universal pointwise timely Tracking headline**. Three things survive; naming them precisely is what keeps the negative honest.

### 5.1 Externalized self-trust **[proved, conditional on Tracking]**

This is the surviving piece of real mathematics. It is an $H^+$-side coherence theorem proven by a *waiting* arbitrage, conditional on Tracking as a hypothesis.

> **Theorem 5.1 (externalized self-trust).** Let $(p_n)$ be a $\mathcal{C}_H$-computable sequence of rationals in $[0,1]$, $\delta>0$ rational, and assume **Tracking** $a_n-Y_n\to0$. With the **one-sided** indicator
> $$\operatorname{Ind}_\delta(X>p)=\begin{cases}0&X\le p\\ (X-p)/\delta& p<X<p+\delta\\ 1&X\ge p+\delta\end{cases}$$
> (so $\operatorname{Ind}_\delta(X>p)>0\Rightarrow X>p$, which is what lands the conclusion at exactly $p_n$, not $p_n\pm\delta$):
> $$ H^+_n\!\bigl(\mathbb{1}(P^{(n)})\cdot\operatorname{Ind}_\delta(R_n>p_n)\bigr)\;\gtrsim_n\;p_n\,H^+_n\!\bigl(\operatorname{Ind}_\delta(R_n>p_n)\bigr), $$
> and symmetrically with $<$ and $\lesssim_n$.

*Proof (the inter-temporal arbitrage; the resale algebra and asymptotic composition are kernel-checked, the no-Dutch-book step is a named hypothesis — §10).* Write $I_n^+:=\operatorname{Ind}_\delta(R_n>p_n)$ and $B_n^+:=I_n^+\cdot(\mathbb{1}(P^{(n)})-p_n)$; the claim is $H^+_n(B_n^+)\gtrsim_n0$. Suppose not: for a rational $\epsilon>0$, infinitely many $n$ have $H^+_n(B_n^+)<-\epsilon$. A $\mathcal{C}_H$-trader buys one share of $B_n^+$ at $n$ (paid $\ge\epsilon$) and sells at $F(n)$, on a sparse subsequence so at most one position is open at a time.

*Position decided by $F(n)$.* $D^+_H$ inserts $\widehat\Theta_n(\ell^\ast_n)$ at $n+1<F(n)$, so $R_n$ is decided in $\mathrm{PC}(D^{+,F(n)}_H)$; let $r_n$ be its settled value, $i_n^+:=\operatorname{Ind}_\delta(r_n>p_n)$.

*Resale value (the LUV-vs-affine step).* $B_n^+$ is a *product*, not an affine combination; reduce it. Since $I_n^+$ is provably equal to the rational $i_n^+$ in $\mathrm{PC}(D^{+,F(n)}_H)$, the residual $(I_n^+-i_n^+)(\mathbb{1}(P^{(n)})-p_n)$ is provably $0$ there, and a market prices provably-equal variables equally, so
$$ H^+_{F(n)}(B_n^+)=i_n^+\bigl(H^+_{F(n)}(P^{(n)})-p_n\bigr)=i_n^+\,(Y_n-p_n). $$
*Lower bound.* If $i_n^+=0$ this is $0$. If $i_n^+>0$ then (one-sidedness) $r_n>p_n$, so $Y_n-p_n=(r_n-p_n)-(r_n-Y_n)>-|r_n-Y_n|$; with $0\le i_n^+\le1$, $H^+_{F(n)}(B_n^+)\ge-|r_n-Y_n|$ either way. The ledger gives $|r_n-a_n|\le\tfrac1{2n}$ and **Tracking** gives $a_n-Y_n\to0$, so $r_n-Y_n\to0$, whence $H^+_{F(n)}(B_n^+)\ge-\epsilon/2$ for large bad $n$.

*Bounded risk, unbounded profit.* While open, value $W(B_n^+)-H^+_n(B_n^+)$ with $W(B_n^+)\in[-1,1]$, so net worth has a floor; each round trip nets $\ge\epsilon/2$, disjointly, infinitely often. The trade is in $\mathcal{C}_H$ ($B_n^+$ expands over $O(n)$ monotone $\beta$-profiles with $\mathcal{C}_H$ coefficients; $I_n^+$ is a $\mathcal{C}_H$ continuous feature). This contradicts **(LI-Crit)** for $H^+$. The $<$ direction is symmetric (short instead of buy). $\qquad\blacksquare$

> **What this is, and is not (the load-bearing reading).** Distinguish the *implication* from its *antecedent*. The **implication** (Tracking $\Rightarrow$ externalized self-trust) genuinely sidesteps §2 and §3 *in its proof*: it is $H^+$-side coherence with **its own future**, the $\mathcal{C}_H$-trader *waits* to $F(n)$ rather than computing $Y_n$ early (so 2b's compute-regress never arises), and it runs on a **fixed benign** $(p_n)$ (so 2a's adversarial family never arises). The non-triviality has **relocated entirely into the Tracking hypothesis**. But that **antecedent** is *predictive* Tracking — the early quote $a_n=A_n(C_n)$ tracking the future credence, $a_n\eqsim_n Y_n$ — which is *exactly* what §2–§3 damage: §2 forbids it universally, §3 forbids *enforcing* it from a satisfiable power assumption, and it can hold only insofar as $Y_n$ is cheaply predictable (the statistical residue, **not** §3.4's trivial late-price "eventual" notion $A_{\sigma(n)}(C_n)\to$ settled value). So Theorem 5.1 manufactures **no unconditional trust**; as a sound **reduction** — "external trust $=$ self-trust $+$ Tracking, by arbitrage" — it shows external trust is *exactly as strong as the (damaged) predictive Tracking one can independently secure*. It is, precisely, **self-trust through a mirror**: $A$ merely relays where $H^+$ is already heading. Real, and the cleanest derivation in the corpus (it needs neither Thm 4.12.4 nor an audit-realization step) — but, exactly because it is parasitic on self-trust, it "cannot carry the paper" as a Tracking result.

### 5.2 Gated and classwise-averaged deference, and a tight ceiling **[sketched at LI level]**

Replacing pointwise control with weaker shapes restores positive theorems:

- **Gated:** conditioned on a continuous gate $G_n=g(a_n)$ (e.g. $\operatorname{Ind}_\delta$ of "$A$'s quote near $q$"), $H^+$'s gated credence tracks $a_n$ up to $O(\epsilon/\delta)+o(1)$.
- **Classwise-averaged:** over $D$-decidable subsequences, weighted-average deference errors vanish (LI 4.3.6/4.3.8/4.4.5 style).

And the anti-inductive counterexample earns its keep on the *positive* side: it is exactly the obstruction to a pointwise object-level version, so **the gated/averaged ceiling is tight** — the inability to do better pointwise is a theorem, not a gap in the proof.

### 5.3 Non-Dogmatism confines manipulation to the interior **[sketched at LI level]**

Even where the limit is free, it is not *arbitrarily* free. By **(LI-ND)**, for $\Gamma$-independent $\varphi$ every inductor over $D^+_H$ has $H^+_\infty(\varphi)\in(0,1)$, and the uniform form gives a complexity-graded margin: both $H_\infty(\varphi)$ and $H^+_\infty(\varphi)$ lie in $[\delta_\varphi,1-\delta_\varphi]$. So whatever influence $A$ exerts, it provably **cannot drive certainty** on undecided propositions — manipulation is confined to a closed sub-interval of the open interval, not merely to $(0,1)$. (This is also the lemma that kills a tempting *wrong* construction; §6.)

### 5.4 The decided fragment trusts cleanly **[sketched at LI level]**

The honest organizing contrast is decided vs. undecided. For $\Gamma$-decided $\phi$, both $H_\infty(\phi)$ and $H^+_\infty(\phi)$ equal $\mathbb{1}[\Gamma\vdash\phi]$ by **(LI-PI)** on the $\Gamma$-complete processes $D\subseteq D^+_H$ — one line, no coupling. Underdetermination is a phenomenon *only* of the $\Gamma$-independent fragment, where it is exhibited via a Projection (Shannon-split) Lemma for independent atoms and their Boolean combinations; genuinely entangled independents (Con(PA), Gödel sentences) are left open. On the decidable fragment, then, deference buys *speed, never truth* — and is fail-safe even against an adversarial advisor.

---

## 6. A refuted sub-attempt: forcing divergence with a stronger process **[proved — the refutation is clean]**

*Historian's note, because the dead branch has a dead twig worth a signpost.* A natural attempt to *rescue a strong claim* from the wreckage — make $A$'s influence provably **move** $H^+$'s limit — was floated (a ChatGPT construction) and is **wrong**, refuted by the very Non-Dogmatism of §5.3. It builds $H^+$ as an inductor over a *strictly stronger* deductive process $E\supsetneq D^+_H$ that eventually settles an undecided $\varphi$, concluding $H^+_\infty(\varphi)=1\ne H_\infty(\varphi)$.

The refutation is immediate and clean: if $D^+_H$ never decides $\varphi$ (it is conservative over $\mathcal{L}$ for $\Gamma$-independent $\varphi$), then **(LI-ND)** forces $H^+_\infty(\varphi)<1$ for *any* inductor over $D^+_H$. So the construction's $H^+$ is provably **not** an inductor over $D^+_H$ — it is one over $E$, a *different* object. The underlying error is a monotonicity reversal: shrinking the plausible-world set ($D^+_H\to E$) preserves "bounded below" but *not* "unbounded above," so unexploitability-relative-to-$E$ does not transfer down to relative-to-$D^+_H$. (The short-selling "exploit" sometimes offered instead is convergence-rate-dependent and should *not* be the kill; the Non-Dogmatism contradiction should.) The philosophy in that proposal — deference is compatible with non-categorical drift rather than causing it — is right; the formal divergence theorem is broken. Legitimate underdetermination keeps $(\Gamma,D)$ **fixed** and only re-weights a free atom; strengthening the theory is a category error that silently moves $\varphi$ into the decided fragment.

---

## 7. The double edge: the manipulation attack surface **[interpretation]**

The self-referential target's deepest property is not a bug to be removed but a *structural feature to be stated*: because $A$ merely echoes where $H^+$ is heading, the **audit trace $(a_n,Y_n)$ cannot distinguish faithful prediction from steering.** Accurate prediction of $H^+$'s independent trajectory and active steering of $H^+$ into the predicted outcome produce the *same* vanishing $a_n-Y_n$. This is the "whispering earring" rendered as a theorem rather than a complaint, and it is why even the *repaired* (autonomous-target) construction must carry a prediction/influence dichotomy: **prediction of the uninfluenced reasoner is provable, pointwise, timely; influence on the influenced reasoner is underdetermined, with only averaged/gated theorems and provably no more** (§5.2's tight ceiling is the "no more"). External trust is **parasitic on self-trust** — $A$ mirrors the reasoner's own deferred credence — so "trusting $A$" reduces to self-trust routed through a relay, and every deference equilibrium passes all the trust tests. A genuine manipulation theorem then needs ingredients the bare construction lacks: a *second* calibration condition separating calibration-to-self from calibration-to-truth; an evidence/preemption distinction; a transfer-of-trust attack (earn authority on decidables, spend it on undecidables); and non-recoverability — the formal statement that legitimacy cannot be certified from the trace.

---

## 8. Reading: where this sits **[interpretation]**

**For the project.** §2.2 is the hinge of the whole research arc. The self-referential target is the *most natural* first model — "the human who has heard the AI, trusting the AI to deliver the human's own future verdict." The two impossibilities are why that model cannot anchor a *forced (pointwise-tracking)* deference theorem, and the dichotomy (§4) is why the repair — the autonomous, reflectively-blind target — is **forced** rather than chosen. A reader should meet 2a and 2b *first* and arrive at the construction already knowing the target's autonomy is derived. That ordering is the content of "blindness is derived, not assumed."

**Against v4.** This is the cross-process register of v4 §11. v4's clean theorem is the **future self**, where the tower $\mathrm{Mart}(N\to E^\ast)$ is the free LI theorem `cee` precisely because truster and trusted share temporal identity (v4 §6). The self-referential target is an attempt to *fake* that identity across a gap — to make a *distinct, stronger* $A$ into a mirror of $H^+$'s own future. §2 is the sharp statement that this particular forgery is not merely unproven but, in headline form, impossible: you can arbitrage against a market only if you can trade in it (v4 §2.4's "self-trust is free and cross-trust is a hypothesis because you can only arbitrage against a market you can trade in"), and the mirror coupling does not give $H^+$ a market it can settle against $A$'s verdict without either an anti-inductive instance (2a) or an unaffordable simulation (2b). What v4 calls "the tower must be earned, not assumed" is, here, "earned only as the eventual/statistical fragment, never as timely pointwise tracking — and the autonomous target is the price of even that."

**Philosophically.** The dichotomy "predictable iff uninfluenced" is, independently, the **stop-gradient / non-performativity** move of the performative-prediction literature, reached from a different formalism — evidence the joint is real. And the counterfactual target has a clean normative reading that turns the bullet into a feature: deferring to $A$ means letting your *advised* self be moved toward your *unadvised, more-deliberated* self's conclusions — advice that **preserves epistemic autonomy by construction**. Good advice moves you toward who you would have become with more thought, not toward who the advisor wants you to be; blindness is that norm, formalized. The clean theorems live, as in v4 §9 and DDB, in the choice-independent, causal-surrogate, updateful regime — the "agent outside the environment" idealization; deference-punishing/Newcomblike payoffs are out of scope here exactly as there.

---

## 9. Status, caveats, open threads

- **2a is the strong result.** Its arithmetic core (Lemma 2.1) is **[proved]** and elementary; the LI lift is **[sketched at LI level]**, resting only on (LI-PI) convergence-on-decidables. It is *compute-independent* and *refutational* — a genuine false instance, not an underivability.
- **2b is a satisfiability result with one soft joint.** The regress is **[sketched at LI level]**; the source rates it ~75–80%, with "does inexploitability force $A$ to pay the simulating trader's runtime?" (step 3) the explicit place to pressure-test. The robust skeleton — $R_A(n)\gtrsim R_A(F(n))>R_A(n)$ once $\mathcal{C}_A$ must contain its own coupled simulation cost — and the reflective-exploiter refinement do not depend on the naive "market runs the trader" mechanism, which is **wrong** and was corrected.
- **The two are independent and complementary:** 2a needs quote-referencing contracts and kills by refutation; 2b needs only the coupled dependence of $Y_n$ on $A$'s run and kills by unsatisfiability — covering the quote-free families where 2a is blocked. "Dead twice over."
- **The dichotomy** (§4) is the contrapositive of the two and is **[sketched at LI level]**; its converse — that blindness *suffices* for the positive theorems — is the live program (the autonomous-target construction), not proved here.
- **Externalized self-trust** (Thm 5.1) is **[proved, conditional on Tracking]**; I verified the arbitrage, the one-sided-indicator necessity, the LUV-vs-affine reduction, the bounded-risk and $\mathcal{C}_H$-admissibility checks. Its standing as a *trust* result is only as strong as the Tracking it imports, which for the self-referential target is the surviving eventual/statistical fragment.
- **Open, inherited from the corpus:** (i) discharge or make explicit 2b's step-3 hypothesis; (ii) the non-recoverability lemma behind "no unconditional limit equality" is asserted, not yet cited to Garrabrant — it needs its own proof or a precise citation; (iii) underdetermination for *entangled* independents (Con(PA), Gödel) is genuinely open (the Projection Lemma covers atoms and Boolean combinations only); (iv) the manipulation theorem of §7 is a sketch awaiting its four ingredients.

---

## 10. Machine-check (Lean 4 + Mathlib)

The arguments above are kernel-checked in [`../lean-deference/SelfReferentialTarget.lean`](../lean-deference/SelfReferentialTarget.lean) (Lean 4.27.0 + Mathlib — the same project and discipline as the v4 development): **`sorry`-free**, every result audited by `#print axioms` to rest on only `[propext, Classical.choice, Quot.sound]`, and wired into the build (`lake build SelfReferentialTarget`). As in v4, the genuine mathematical cores are proved outright and the **Logical-Induction theorems enter only as named hypotheses** — we trust the LI paper, we do not re-prove it.

| note claim | Lean name(s) | status |
|---|---|---|
| **Lemma 2.1** (no exact quote); tightness; tie-robustness | `no_exact_quote`, `residual_half`, `no_exact_quote'` | **proved outright** (pure real analysis) |
| residual bound with rounding gap (§2.2) | `residual_lb` | **proved outright** |
| **2a** — universal pointwise tracking fails (`liminf|aₙ−Yₙ| ≥ ½`), and `¬Approx a Y` | `tracking_fails_liminf`, `tracking_fails` | proved **modulo `hLIPI`** (LI provability-induction: `H⁺` converges to the `D⁺`-decided value of the anti-inductive contract) |
| 2a non-vacuity (hypotheses jointly satisfiable; failure real) | `tracking_fails_nonvacuous` | **proved outright** |
| **2b** — the cost regress `R_A(n) ≳ R(Fn) ≥ R_A(Fn) > R_A(n)` is contradictory | `regress`, `cost_circularity` | **proved outright** (arithmetic); the timely-cost step `hcost` is a **named soft joint** |
| 2b — the non-cost setup is realizable (blame falls on `hcost`) | `cost_setup_realizable` | **proved outright** |
| **dichotomy** "predictable iff uninfluenced" | `predictable_imp_uninfluenced` | **proved outright** as the propositional contrapositive of `h2a`,`h2b` (the content is 2a/2b) |
| **§5.1** resale lower bound (one-sided indicator) | `resale_lb` | **proved outright** (the subtle algebra) |
| §5.1 externalized self-trust `H⁺_n(B_n) ≳ₙ 0` | `externalized_self_trust` | proved **modulo `hNoArb`** (LI no-Dutch-book as inter-temporal no-arbitrage) + Tracking |
| §5.1 a Value gap nets positive guaranteed profit | `round_profit_pos` | **proved outright** |
| **§5.3** Non-Dogmatism confines manipulation to `[δ, 1−δ]` | `manipulation_confined` | **proved outright** (given the ND margin) |
| **§6** the divergence construction is refuted by Non-Dogmatism | `nondogmatism_refutes` | **proved outright** (given `Y∞ < 1`) |

**The boundary — what is *not* machine-checked, stated honestly.** Four things sit in the trusted/prose layer, exactly as in v4: **(i)** the LI paper's own theorems (existence, the criterion, provability-induction, Non-Dogmatism) — entered as the named hypotheses `hLIPI`, `hNoArb`, and the ND bound; **(ii)** the *modeling identifications* that those hypotheses are the right LI consequences — that the anti-inductive contract `g_n ↔ (R_n ≤ ½)` is `D⁺`-decided so LI-PI yields `Y_n → antiInd(r_n)` (§2.2), and that the criterion specialises to the inter-temporal `hNoArb` (§5.1); **(iii)** 2b's one **soft joint** `hcost` — the kernel proves the cost chain is *contradictory*, **not** that timely tracking *forces* `hcost` (the ~75–80% step of §3.2); **(iv)** the dichotomy's identification "A-dependence ⟹ (`h2a`-antecedent ∨ `h2b`-antecedent)" (§4.2). Within that boundary the kernel confirms every inference — including the two places a prose proof is most fragile: the one-sided-indicator resale algebra (`resale_lb`) and the `liminf` lift (`tracking_fails_liminf`). (The check also caught real mistakes in the first draft — a nonexistent lemma name and two cast/`beta` slips — the usual reason to run the kernel rather than trust the prose.)

**Non-vacuity.** Two results guard against vacuous success. `tracking_fails_nonvacuous` exhibits a concrete model (`aₙ ≡ rₙ ≡ ½`, `Yₙ ≡ 1` — the best-response quote, still off by exactly ½) satisfying *all* of 2a's hypotheses with tracking genuinely failing, so 2a is not vacuously true via incompatible hypotheses. `cost_setup_realizable` shows 2b's structural hypotheses (`hmono`, `hF`, `hshare`) are jointly satisfiable, so the contradiction isolates the timely-cost assumption rather than an already-inconsistent setup.

---

## References

- S. Garrabrant, T. Benson-Tilsen, A. Critch, N. Soares, J. Taylor, **"Logical Induction"** (2016). — Existence (3.6.1), the criterion (§3.0–3.5), Limit Coherence (4.1.1), Provability Induction (4.2.1) / Expectation form (4.8.10), Non-Dogmatism (4.6.2) and Uniform Non-Dogmatism (Des. 7), trader continuity and the $\chi$ sentence (§3.4, §4.11), Self-Trust (4.12), Learning Pseudorandom Frequencies (§4.4), Closure Under Conditioning (4.7.2).
- S. Garrabrant, **"The Set of Logical Inductors Is Not Convex."** — the $\varphi_n\leftrightarrow(\mathbb{P}_n(\varphi_n)<\tfrac12)$ precedent behind §2's transplant (and why the *coupled, markets-see-each-other* case is not plug-and-play).
- "Diffractor," **"Universal Inductors"** (LessWrong) — the conditioned-bitstring inductor framing of the original draft (dropped in the repair).
- Anson, **"Trust Between Logical Inductors — Technical Summary"** ([`anson-notes/trust-between-inductors-summary-v2.md`](trust-between-inductors-summary-v2.md)), §2.2 (the source of this note), with the conversation corpus indexed in [`anson-notes/INDEX.md`](INDEX.md) — esp. files `03_…channel-p-repair`, `04_…schedule-condition`, `08_…paper-revision-thm`, `09_…underdetermination`, `11_…human-ai-alignment`.
- Claude Opus 4.8, **"Deference Between Epistemic Processes" (v4)** ([`deference-in-logical-induction-v4.md`](../notes/deference-in-logical-induction-v4.md)) — the positive tower; this note is the obstruction side of its §11.
- K. Dorst, B. A. Levinstein, B. Salow, B. E. Husic, B. Fitelson, **"Deference Done Better"** (2021) — Total Trust ⟺ Value, the shape the surviving conditional face (§5.1) imitates.
- J. Perdomo, T. Zrnic, C. Mendler-Dünner, M. Hardt, **"Performative Prediction"** (2020) — the stop-gradient/non-performativity convergence noted in §4.4, §8.
