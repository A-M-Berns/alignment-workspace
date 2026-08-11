# The transitivity route: does trust compose?

*Open problem 14. Setting: coupled cross-process, **one-way** visibility (A clears, publishes into $D_H$, then H clears). Target: soft Total Trust of H in the lookahead expert $E^\ast(X_n):=a_n$. Conventions: [[conventions-and-status-labels]]. Theorem numbers are arXiv v5 numbers in the **corrected** forms of [[li-paper-erratum]]; source of truth `references/logical-induction/main.tex`. Written 2026-07-30.*

*Every asymptotic statement below is labelled **FULL LIMIT** or **LIMIT POINT**, and every weighting is tagged with the market it must be legal for.*

*Parallel note in this lab: [[route-recurring-ccee]] (same date), which reaches the same headline verdict on open problem 14 by a shorter path and independently derives the LUV form of Self-Trust (its T4 = my Lemma A). Points of agreement, and the one point where I think its diagnosis is incomplete, are marked ⟂ throughout.*

---

## 0. Verdict up front

| question | verdict | confidence |
|---|---|---|
| **Open problem 14** — does `st` + Half 1 compose into soft TT of H in A? | **NO.** Not as an inference: the two inputs' conclusions are jointly satisfiable with the target false (Prop. 7.1, explicit witness). | 0.90 |
| Which of `st` / `cee` / `ccee` is the right Input 1? | **`ccee` 4.12.3 + `expprovind` 4.8.10**, yielding the LUV-level self-trust **`est`** (Lemma A). `st` 4.12.4 is type-wrong (propositional; its gate is on $\mathbb P_{f(n)}(\phi_n)$, not on $\mathbb E_{f(n)}(X_n)$); `cee` is ungated, hence not of trust shape. | 0.92 |
| Is the corpus's recorded "direction of composition" worry real? | **YES, and it is a theorem-level obstruction, not a vibe** — the correctly-shaped finite-frame square is **REFUTED** by an explicit 4-world witness *even with Input 2 strengthened to exact calibration on every gate* (Witness 5.2). ⟂ This is the point where I part company with [[route-recurring-ccee]] §7.2, which calls the failure "not a direction-of-composition subtlety but a grain mismatch". There are **two** independent obstructions. | 0.90 |
| Is the direction obstruction fatal *here*? | **No** — in this setting it is discharged for free by `ccee` at an H-generable gate, which is exactly the LI mirror of the finite-frame nesting condition $\sigma(a)\subseteq\mathfrak M$ ("future-H knows the quote"); that in turn needs only publication before the lookahead. So the corpus's worry is correct in general and dischargeable in this setting. | 0.85 |
| What kills the composition, then? | The **grain/strength** obstruction, quantified exactly: the gate substitution's residual is $\mathbb E^H_n(\ulcorner\min(1,|a_n-Y_n|/\delta)\urcorner)$ — H's own day-$n$ expectation of the **truncated absolute** forecast error, **per day** (Lemma C, Theorem B). Half 1 supplies a **signed, gate-weighted, limit-point** quantity. Sparsity (4.8.16) repairs limit-point→limit, a *different* deficit, and leaves this one untouched. | 0.90 |
| Is transitivity a fourth route? | **No.** Its only non-vacuous repair abandons the gate transfer, at which point `est` is not used at all and the argument is the `cee` route with `ccee`-gating. **"Transitivity is not a fourth route; it is the `cee` route said differently"** — and in its literal form it is *strictly worse* than the `cee` route (Prop. 6.3). | 0.85 |
| Positive residue | **Theorem B** (robust self-trust with an explicit error budget) and **Corollary B.1** (composition closes under per-day accuracy (UA), with H's learning of the accuracy free by 4.2.1). Both new; both free of visibility assumptions. | 0.88 |
| Is a counterexample to naive transitivity constructible? | At the **inference** level, yes, exhibited (Prop. 7.1). At the level of an actual inductor pair it is **exactly open problem 9**, and this note supplies its design: the gate must be built from **H's own price of $\ulcorner Y_n\urcorner$**, which one-way visibility hides from A. | 0.55 for realizability |

---

## 1. Setting, notation, named hypotheses

Two logical inductors: $H\dashv\mathcal C_H$ over a $\Gamma_H$-complete deductive process $D_H$, and $A\dashv\mathcal C_A$ over $D_A$; canonically $\mathrm P\subseteq\mathrm{EXP}$. $(X_n)$ is an e.d. sequence of $[0,1]$-LUVs of H's language. $f$ is a deferral function (Def. 4.3.7, `main.tex:1240`), $f(n)>n$, strictly increasing, computable in time polynomial in $f(n)$; canonically $f(n)=2^n$. Write

$$Y_n:=\mathbb E^H_{f(n)}(X_n),\qquad a_n:=\mathbb E^A_n(\ulcorner Y_n\urcorner),\qquad h_n:=\mathbb E^H_n(X_n),\qquad g_n:=\mathbb E^H_n(\ulcorner Y_n\urcorner).$$

For rational $t\in[0,1]$, rational $\delta>0$, the three gates that matter:

$$u_n:=\operatorname{Ind}_\delta(a_n>t)\quad(\textbf{A's own quote — legal for }A),$$
$$\hat u_n:=\operatorname{Ind}_\delta\big(\mathbb E^H_n(\ulcorner a_n\urcorner)>t\big)\quad(\textbf{H's reading of the quote — legal for }H),$$
$$\beta_n:=\operatorname{Ind}_\delta(Y_n>t)\quad(\textbf{H's own future price — legal for }H\textbf{ at index }f(n)).$$

$\operatorname{Ind}_\delta$ is Def. 4.3.2 (`main.tex:1174`); its closing remark blesses ramps of expressible features as expressible $[0,1]$-features, which is what makes all three legal *in the market indicated*. Divergent weighting: Def. 4.3.4; generable from $\overline{\mathbb P}$: Def. 4.3.5 (`main.tex:1218`), an e.c. $\mathcal{EF}$-progression, so the $m$-th term has **rank $\le m$** — it may reference day-$\le m$ prices of *its own* market and nothing else.

**Why $\hat u$ and not $u$ on H's side.** $\overline u$ is not an expressible feature of H's market and is not e.c. (computing it means running A); this is the trap recorded at [[unbiasedness-theorem-families]] §6. But $\mathbb E^H_n(\ulcorner a_n\urcorner)$ *is* an expressible feature of rank $n$: by Def. 4.8.2 it is the finite rational combination $\sum_{i<n}\tfrac1n\mathbb P^H_n(\ulcorner \ulcorner a_n\urcorner>i/n\urcorner)$ of day-$n$ prices of sentences writable in poly$(n)$ (fixed template naming A's algorithm, the numeral $n$, and $i/n$). So $\hat u$ is $\overline{\mathbb P}^H$-generable **with no ledger hypothesis at all**; the ledger is needed only to relate $\hat u$ to $u$. ⟂ This is a cleaner repair than the wiki's $\tilde u_n=\operatorname{Ind}_\delta(\mathbb P^H_n(\ulcorner a_n>t\urcorner)>\tfrac12)$, which converges to the *hard* indicator of $a_n>t$ and so does not match A's ramp; [[route-recurring-ccee]] §2 independently found that defect.

### Named hypotheses

- **(Γ-REP)** $\Gamma_H$ and $\Gamma_A$ extend PA, are consistent, and represent computations — the paper's own standing assumption from §4.8 onward (`main.tex:1633`). Consequence used repeatedly: for every $W\in\mathcal{PC}(\Gamma_H)$ and every $n$, $W$ assigns the LUVs $\ulcorner a_n\urcorner,\ulcorner u_n\urcorner,\ulcorner \hat u_n\urcorner,\ulcorner Y_n\urcorner,\ulcorner\beta_n\urcorner$ their actual values, and $W(\ulcorner X_n\cdot c_n\urcorner)=c_nW(X_n)$ for any such determined constant $c_n$. Applied to a *coupled* system, so it is declared rather than inherited silently; it is the same assumption §4.11–4.12's proofs make (`main.tex:5504–5560`).
- **(BLCS-A)**, **(DET-A)** — standing, from the problem statement: $\overline{\ulcorner Y\urcorner}$ is a bounded e.c.-expression $\mathcal{BLCS}$ sequence for A, determined via $\Gamma_A$ with $\operatorname{Val}_{\Gamma_A}(\ulcorner Y_n\urcorner)=Y_n$.
- **(MIRROR)** — the same for H: $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^H)$, determined via $\Gamma_H$. Used **only** where 4.8.15 is applied to H's market (§9, the `cee`-route comparison). Not used by Lemma A, Lemma B, Lemma C, or Theorem B.
- **(P)** *Same-day publication.* $a_n$ is decided in $D_H$ by day $n$. Used only for (LL).
- **(LL)** *Ledger legibility.* $\mathbb E^H_n(\ulcorner a_n\urcorner)\eqsim_n a_n$ (**FULL LIMIT**). This is what converts statements about $\hat u$ into statements about $u$, at Lipschitz cost $1/\delta$. It is **not** free: determinacy alone never gives timeliness (the paper's own $\pi[\mathrm{Ack}(n,n)]=7$ example, `main.tex:1143`, is determined and sits at $0.1$ forever). What buys it is (P) plus H's traders being able to *read* the ledger — which in the strict LI framework means the read must be poly-time, since Def. 4.3.5 gives traders no primitive for the deductive state. The lab's setting stipulates $O(n)$-readability; the honest form of that stipulation is a relativized trader class ([[route-recurring-ccee]] (H⁺-CLASS)). I therefore state every result twice: once in $\hat u$ form (no (LL)), once in $u$ form (with (LL)).
- **(DIV)** — the relevant gate has divergent mass (needed only for Half 1).
- **(UA)** *Uniform accuracy* — used only in Corollary B.1, and stated there.

**One-way visibility.** A clears first each day and never reads H's prices; H's day-$n$ market is defined given $a_{\le n}$. No joint fixed point, no Brouwer construction. This is a hypothesis about the *setting*, and §7.3 is where it earns its keep — it is what makes the counterexample design coherent.

---

## 2. Input 1: which of `st`, `cee`, `ccee`?

Read the printed statements. `st` **4.12.4** (`main.tex:2092–2110`):

$$\mathbb E_n\Big(\ulcorner \mathbb 1(\phi_n)\cdot\operatorname{Ind}_{\delta_n}\big(\mathbb P_{f(n)}(\phi_n)>p_n\big)\urcorner\Big)\;\gtrsim_n\;p_n\cdot\mathbb E_n\Big(\ulcorner\operatorname{Ind}_{\delta_n}\big(\mathbb P_{f(n)}(\phi_n)>p_n\big)\urcorner\Big),$$

for $\overline\phi$ e.c. sentences, $\overline\delta$ e.c. positive rationals, $\overline p$ a $\overline{\mathbb P}$-generable sequence of rational probabilities. Three features, all load-bearing: (i) it is **propositional** — the object is $\mathbb 1(\phi_n)$, the gate is on a future *probability*; (ii) the gate is on H's **own future price**, inside the corner quotes, because H does not know it at day $n$; (iii) it is one-sided, with sequences $(p_n,\delta_n)$.

`ccee` **4.12.3** (`main.tex:2068–2075`): for $\overline X$ e.c. $[0,1]$-LUVs and $\overline w$ a $\overline{\mathbb P}$-generable $[0,1]$ sequence,

$$\mathbb E_n\big(\ulcorner X_n\cdot w_{f(n)}\urcorner\big)\;\eqsim_n\;\mathbb E_n\big(\ulcorner \mathbb E_{f(n)}(X_n)\cdot w_{f(n)}\urcorner\big)\qquad\textbf{(FULL LIMIT)}.$$

**The $w_{f(n)}$ indexing is a generalisation, not a restriction.** The weight is the $f(n)$-th term of a generable sequence, hence an expressible feature of rank $\le f(n)$ — which *includes* every feature of rank $\le n$. So both "gate on the day-$f(n)$ price" and "gate on a day-$n$ feature" are legal: pull back along $f$, setting $w_m:=(\text{the wanted feature})$ for $m\in\operatorname{im}f$ and $w_m:=0$ otherwise. The progression is e.c. because $f$ is strictly increasing and poly-computable in $f(n)$, so deciding $m\in\operatorname{im}f$ and recovering $f^{-1}(m)$ costs poly$(m)$. (This point is not made in [[unbiasedness-theorem-families]] §4.1, which applies `ccee` "at weight $w:=u$" without the reindexing; the conclusion there is rescued by this remark, and it is worth recording, since read naively $w_{f(n)}$ looks like it *forbids* a day-$n$ gate.)

**Lemma A (`est` — the LUV form of Self-Trust). FULL LIMIT, all days, free.** Let $\overline X$ be e.d. $[0,1]$-LUVs, $p$ rational, $\delta>0$ rational, $\beta_n:=\operatorname{Ind}_\delta(\mathbb E^H_{f(n)}(X_n)>p)$. Then

$$\mathbb E^H_n\big(\ulcorner X_n\beta_n\urcorner\big)\;\gtrsim_n\;p\cdot\mathbb E^H_n\big(\ulcorner\beta_n\urcorner\big),$$

and dually $\mathbb E^H_n(\ulcorner X_n\beta'_n\urcorner)\lesssim_n p\,\mathbb E^H_n(\ulcorner\beta'_n\urcorner)$ for $\beta'_n:=\operatorname{Ind}_\delta(Y_n<p)$.

*Proof.* $\overline\beta$ pulled back along $f$ is $\overline{\mathbb P}^H$-generable in $[0,1]$: at index $m=f(n)$ it is $\operatorname{Ind}_\delta(\mathbb E_m(X_n)>p)$, and $\mathbb E_m(X_n)=\sum_{i<m}\tfrac1m\mathbb P_m(\ulcorner X_n>i/m\urcorner)$ is an expressible feature of rank $m$ (Def. 4.8.2 + Def. 3.4.3), with the sentences writable in poly$(m)$ since $n<m$. `ccee` 4.12.3 gives $\mathbb E^H_n(\ulcorner X_n\beta_n\urcorner)\eqsim_n\mathbb E^H_n(\ulcorner \mathbb E^H_{f(n)}(X_n)\cdot\beta_n\urcorner)$. The ramp has no false positives ($\operatorname{Ind}_\delta(z>p)>0\Rightarrow z>p$), so in every $W\in\mathcal{PC}(\Gamma_H)$, by (Γ-REP), $W\big(\ulcorner \mathbb E_{f(n)}(X_n)\beta_n\urcorner-p\ulcorner\beta_n\urcorner\big)=\beta_n(Y_n-p)\ge0$; the sequence is in $\mathcal{BLCS}$ (constant rational coefficients $1,-p$; the LUVs are e.d.), so `expprovind` 4.8.10 finishes. Dual: $\operatorname{Ind}_\delta(z<p)>0\Rightarrow z<p$. $\square$

Equivalently, one may mimic the paper's own proof of `st` (`main.tex:5504–5560`) verbatim, substituting `er` 4.11.4 for `epr` 4.11.3 and $X_n$ for $\mathbb 1(\phi_n)$; the final step is `exppolymax` 4.8.13, exactly as there. Both routes are two lines. ⟂ Convergent with [[route-recurring-ccee]] T4.

**Why this is the right Input 1, and `st` is not.** The target quantifies over general e.d. $[0,1]$-LUVs $(X_n)$; `st` cannot be instantiated at a general LUV, only at $\mathbb 1(\phi_n)$. Even restricting to propositional $X_n=\mathbb 1(\phi_n)$, `st`'s gate is on $\mathbb P^H_{f(n)}(\phi_n)$ whereas the middle term supplied by Half 1 is $Y_n=\mathbb E^H_{f(n)}(X_n)$; these agree only up to `ei` 4.8.6 / `epr` 4.11.3, i.e. up to a vanishing error, which would then have to be pushed through the $1/\delta$-Lipschitz ramp and tracked. Doing that buys nothing that Lemma A does not give directly. And `cee` 4.12.1 is ungated, so it is the *tower*, not a trust inequality; getting Total Trust out of it is precisely the fold plus the threshold bound ([[deference-notions]]), which at the LI level *is* `ccee` + `expprovind`. So: **Input 1 = `ccee` + `expprovind` = Lemma A; `st` is its propositional shadow.**

**Note where `ccee`'s real value lies.** `ccee` is needed exactly when the gate is *not* known to H at day $n$ — which is the case for $\beta$ (a future price) and not the case for $\hat u$ (a day-$n$ feature). Hence: `ccee`'s genuine home is Input 1 of the transitivity route, **not** step 1 of the `cee` route, where the gate is day-$n$ measurable and plain `cee` + 4.8.10 suffices. This is a second, independent argument for the verdict on **open problem 13** reached in [[route-recurring-ccee]] §0 (the accounting claim is refuted: `ccee` removes neither limit point).

---

## 3. The target, at its own grain

**Lemma B (Gate-Knowledge Collapse). FULL LIMIT.** Let $\overline c$ be a bounded $\overline{\mathbb P}^H$-generable sequence of rationals in $[0,1]$ and $\overline X$ e.d. $[0,1]$-LUVs. Then $\mathbb E^H_n(\ulcorner X_nc_n\urcorner)\eqsim_n c_n\,\mathbb E^H_n(X_n)$ and $\mathbb E^H_n(\ulcorner c_n\urcorner)\eqsim_n c_n$.

*Proof.* `loe` 4.8.4 with coefficient sequences $\overline a:=\overline c$, $\overline b:=0$, and $Z_n:=\ulcorner X_nc_n\urcorner$. Its hypotheses: $\overline c$ bounded generable rationals ✓; $\overline X,\overline Z$ e.c. sequences of $[0,1]$-LUVs ✓ ($Z_n$'s defining formula names H's own day-$n$ market and is writable in poly$(n)$); and $\Gamma_H\vdash Z_n=c_nX_n$, which holds by (Γ-REP) since $\Gamma_H$ proves the numeral value of the determined constant $c_n$. Second claim: same with $X_n:=$ the constant LUV $1$. $\square$

*(Scope note: this settles, for gates that are generable **rational** features of the truster's own current prices, the "introspection for market-generable features" item — [[open-problems]] item 4 — in the affirmative, by `loe` rather than by anything in §4.11–4.12. It does not cover irrational-valued continuous features, for which `loe`'s rational-coefficient hypothesis fails; but every $\operatorname{Ind}_\delta$ ramp of rational width on rational prices is rational, which covers the corpus's uses.)*

**Proposition 3.1 (the target is per-day).** With $\hat u$ as the gate, the unnormalized threshold form of soft Total Trust,

$$\mathbb E^H_n\big(\ulcorner X_n\hat u_n\urcorner\big)\;\gtrsim_n\;t\cdot\mathbb E^H_n\big(\ulcorner\hat u_n\urcorner\big),$$

is **equivalent** to the per-day dominance statement $\liminf_n \hat u_n\big(\mathbb E^H_n(X_n)-t\big)\ge0$. Under (LL) the same holds with $u$ in place of $\hat u$, at cost $O(1/\delta)\cdot o(1)$.

*Proof.* Lemma B applied to both sides. $\square$

This is not bookkeeping; it is the single most important structural fact about the target in this setting, and it should be stated wherever soft TT is asserted of a *published* expert:

> **Soft conditioning buys nothing when the truster can read the gate.** The LI soft-TT form conditions on the truster's *within-day* uncertainty about the gate's value. `st`'s gate is a future price, unknown to H at day $n$, so the soft form there is genuinely weaker than per-day dominance. A published quote is known to H at day $n$, so the ramp factors out and the target *is* per-day dominance — the same conclusion as v3's Corollary 2 and Theorem A ([[faithful-acceleration-result]] §4.2). Consequently the "averaged, gate-weighted family of Total-Trust instances" of §5 there is **strictly weaker than soft TT**, not merely a bookkeeping variant of it; Prop. 7.1 below separates them.

⟂ [[route-recurring-ccee]]'s comparison table records the same equivalence ("per-day $\equiv\liminf(h_n-a_n)\ge0$"); Lemma B is the proof.

---

## 4. The formal composition attempt, and the exact residual

Instantiate Lemma A at $p:=t$ and the same $\delta$: the gate is $\beta_n=\operatorname{Ind}_\delta(Y_n>t)$. The target's gate is $\hat u_n=\operatorname{Ind}_\delta(\bar a_n>t)$ where $\bar a_n:=\mathbb E^H_n(\ulcorner a_n\urcorner)$ (write $a_n$ for $\bar a_n$ under (LL)). The composition is the substitution $\beta\rightsquigarrow\hat u$. Here is exactly what it costs.

**Lemma C (Bridge). FULL LIMIT.** Put $e_n:=\min\big(1,|\bar a_n-Y_n|/\delta\big)\in[0,1]$. Then

$$\mathbb E^H_n\big(\ulcorner X_n\hat u_n\urcorner\big)-t\,\mathbb E^H_n\big(\ulcorner\hat u_n\urcorner\big)\;\;\gtrsim_n\;\;\Big[\mathbb E^H_n\big(\ulcorner X_n\beta_n\urcorner\big)-t\,\mathbb E^H_n\big(\ulcorner\beta_n\urcorner\big)\Big]\;-\;(1+t)\,\mathbb E^H_n\big(\ulcorner e_n\urcorner\big).$$

*Proof.* $\operatorname{Ind}_\delta(\cdot>t)$ is $(1/\delta)$-Lipschitz with range $[0,1]$, so $|\hat u_n-\beta_n|\le e_n$ pointwise. Let

$$D_n:=\ulcorner X_n\hat u_n\urcorner-t\ulcorner \hat u_n\urcorner-\ulcorner X_n\beta_n\urcorner+t\ulcorner\beta_n\urcorner+(1+t)\ulcorner e_n\urcorner .$$

$\overline D\in\mathcal{BLCS}$: constant rational coefficients $1,-t,-1,t,1+t$ (bounded), and each LUV is e.d. (formulas naming A's algorithm, H's market at days $n$ and $f(n)$, and the rationals $t,\delta$ — all writable in poly$(n)$, since $f$ is poly-computable in $f(n)$ and the *description* need not be evaluated). For every $W\in\mathcal{PC}(\Gamma_H)$, by (Γ-REP) the four constants take their actual values and $W(X_n)\in[0,1]$, so

$$W(D_n)=W(X_n)(\hat u_n-\beta_n)-t(\hat u_n-\beta_n)+(1+t)e_n\;\ge\;-(1+t)|\hat u_n-\beta_n|+(1+t)e_n\;\ge\;0 .$$

`expprovind` 4.8.10 gives $\mathbb E^H_n(D_n)\gtrsim_n0$; expectations of LUV-combinations are linear by definition (Def. 4.8.8, `main.tex:1740`), so rearranging gives the claim. $\square$

Combining Lemmas A and C:

> **Theorem B (robust self-trust — the honest composition). PROVED modulo (Γ-REP). FULL LIMIT, all days, no visibility assumption.** For every e.d. $(X_n)$, every rational $t$ and rational $\delta>0$,
> $$\mathbb E^H_n\big(\ulcorner X_n\hat u_n\urcorner\big)\;\gtrsim_n\;t\cdot\mathbb E^H_n\big(\ulcorner \hat u_n\urcorner\big)\;-\;(1+t)\,\mathbb E^H_n\big(\ulcorner \min(1,|\bar a_n-Y_n|/\delta)\urcorner\big),$$
> and by Lemma B equivalently $\;\liminf_n\big[\hat u_n(\mathbb E^H_n(X_n)-t)+(1+t)\mathbb E^H_n(\ulcorner e_n\urcorner)\big]\ge0$. The dual cut holds with $\operatorname{Ind}_\delta(\bar a_n<t)$, $\lesssim$, and the same residual.

**Reading.** H already totally trusts an *infallible* forecaster of its own future self, for free and at full per-day strength (that is Lemma A: gate on $Y_n$ itself). Replacing the infallible forecaster by a fallible one costs exactly the residual — H's own expectation of the truncated absolute forecast error. Nothing about A enters Theorem B except through that one number. So the whole of open problem 14 reduces to: **what does Half 1 say about $\mathbb E^H_n(\ulcorner \min(1,|a_n-Y_n|/\delta)\urcorner)$?**

**The four-fold answer: nothing usable.**

| the residual needs | Half 1 supplies | independent? |
|---|---|---|
| **per day** ($n$ by $n$) | a **gate-weighted average** over $i\le n$ | this is deficit **D1** |
| **absolute value** $|a_n-Y_n|$ | the **signed** average of $a_i-Y_i$ | subsumed by D1 at the averaged grain, but see §6.1: it is what makes the *sandwich* repair fail |
| **a limit** | a **limit point** (corrected 4.8.15, [[li-paper-erratum]] §1) | deficit **D2** — repaired only by 4.8.16's sparsity |
| **H's day-$n$ expectation** of the error | the **realized** error | deficit **D3** — real, but dischargeable free (Cor. B.1) |
| any gate | only $\overline{\mathbb P}^A$-generable gates | not binding here (the residual is ungated) |

D1 and D2 are logically independent: 4.8.16 converts limit point to limit and leaves the average an average.

---

## 5. The middle term as object vs. subject, made precise

The corpus's recorded worry ([[unbiasedness-theorem-families]] §4.2) is that $Y_n$ is an **object** in Input 2 (a predicted quantity) and a **subject** in Input 1 (a truster whose gated expectations matter), and that trust need not be transitive across such a party. Here is what that amounts to, stated so it can be checked.

**The asymmetry, in one sentence.** `est`'s conditioning is *within a day*, over H's day-$n$ credal uncertainty about the value of $\beta_n$; Half 1's conditioning is *across days*, a weighted average over $n$. These are different operations on different index sets, and there is no product rule joining them. In particular:

> **`est`'s gate fires with the truth, not with the advertisement.** On any day where A is badly wrong — $a_n$ high, $Y_n$ low — the future-price gate $\beta_n$ is *zero*, so `est` says nothing at all about that day, while the target's gate $\hat u_n$ is *one*, so the target says everything about it. Input 1 is silent exactly where Input 2's averaging has hidden a failure.

That is the whole content of the direction worry, and §7's witness is its incarnation. But the worry has a second, purely structural face, which survives even when all averaging slack is removed. To see it, drop to the finite frame — where the prior work `deference-trust-lab/run3/work/tt-transitivity-forall/` lives, but with the *correctly shaped* square.

### 5.1 The correctly shaped finite-frame square

Fix a finite probability space $(W,\pi)$ — H's beliefs. Let $\mathfrak M$ be a $\sigma$-algebra (future-H's information) and $m:=\mathbb E_\pi[X\mid\mathfrak M]$ (future-H's estimate: the middle term). Let $\mathfrak A$ be A's $\sigma$-algebra and $a$ an $\mathfrak A$-measurable quote. Then:

- **Link 1 (Input 1, free):** $\pi$ Totally Trusts $m$, for all $X$ and all $t$. *(The law of total expectation read as a TT statement — this is precisely the prior work's `TT_condExpert`.)*
- **Link 2 (Input 2, in its strongest possible form):** $\mathbb E_\pi[(a-m)g]=0$ for every $\mathfrak A$-measurable $g$, i.e. $a=\mathbb E_\pi[m\mid\mathfrak A]$. *(This is Half 1 with all slack removed: exact, per-gate, no averaging, no subsequence, no sign issue.)*
- **Question:** does $\pi$ Totally Trust $a$?

**Theorem 5.1 (nesting suffices).** If $a$ is $\mathfrak M$-measurable (equivalently $\sigma(a)\subseteq\mathfrak M$), then $\pi$ Totally Trusts $a$: for every $X$ and $t$, $\mathbb E_\pi[X\,\mathbb 1(a\ge t)]\ge t\,\pi(a\ge t)$. *Proof.* $\mathbb 1(a\ge t)$ is $\mathfrak M$-measurable, so $\mathbb E_\pi[X\mathbb 1(a\ge t)]=\mathbb E_\pi[m\,\mathbb 1(a\ge t)]$ (tower over $\mathfrak M$). $\mathbb 1(a\ge t)$ is $\sigma(a)$-measurable, so $\mathbb E_\pi[m\,\mathbb 1(a\ge t)]=\mathbb E_\pi[a\,\mathbb 1(a\ge t)]\ge t\,\pi(a\ge t)$ (Link 2 at that gate). $\square$

Note the economy: the second step uses Link 2 **only on the quote's own gates** — exactly Half 1's gate class. The first step uses the nesting.

**Witness 5.2 (REFUTED without nesting).** $W=\{1,2,3,4\}$, $\pi$ uniform; $\mathfrak M=\sigma\{\{1,2\},\{3\},\{4\}\}$; $\mathfrak A=\sigma\{\{1,3\},\{2,4\}\}$; $X=(0,1,1,0)$. Then

$$m=\big(\tfrac12,\tfrac12,1,0\big),\qquad a=\mathbb E_\pi[m\mid\mathfrak A]=\big(\tfrac34,\tfrac14,\tfrac34,\tfrac14\big),\qquad \mathbb E_\pi[X\mid\mathfrak A]=\big(\tfrac12,\tfrac12,\tfrac12,\tfrac12\big).$$

Link 1 holds (checked at every threshold). Link 2 holds **exactly** on both $\mathfrak A$-cells. At $t=\tfrac34$ the event $\{a\ge t\}=\{1,3\}$ has $\pi=\tfrac12$, and $\mathbb E_\pi[X\mathbb 1]=\tfrac14<\tfrac38=t\,\pi(\{1,3\})$: **Total Trust fails, by exactly $\tfrac18$.** (It also fails at $t=\tfrac58$, by $\tfrac1{16}$.) Verified by exact rational arithmetic; a random sweep of 4000 frames over $|W|=4$ found 895 failures overall and **0 failures among the 1982 frames where $a$ is $\mathfrak M$-measurable**, corroborating Theorem 5.1 and the sharpness of its hypothesis.

**Diagnosis.** $a=\mathbb E[m\mid\mathfrak A]\ne\mathbb E[X\mid\mathfrak A]$ because conditional expectations do not commute across non-nested $\sigma$-algebras: $\mathbb E[X\mid\mathfrak A]=\mathbb E\big[\mathbb E[X\mid\mathfrak A\vee\mathfrak M]\mid\mathfrak A\big]$, and replacing the inner term by $m=\mathbb E[X\mid\mathfrak M]$ is illegitimate unless $\mathfrak A\subseteq\mathfrak M$ (or at least $\sigma(a)\subseteq\mathfrak M$). **So the direction worry is a theorem-level obstruction, not a stylistic caution: with Input 2 at maximal strength — exact calibration to the middle term on every one of A's own gates — the conclusion still fails.** Prior work of this project has been burned by asserting such steps; here the assertion would have been false.

### 5.2 Obstruction O1 (direction) is discharged in *this* setting — and exactly how

Translate Theorem 5.1's two steps into LI:

| finite frame | LI |
|---|---|
| $\mathbb E_\pi[X\,\mathbb 1(a\ge t)]=\mathbb E_\pi[m\,\mathbb 1(a\ge t)]$, needing $\sigma(a)\subseteq\mathfrak M$ | $\mathbb E^H_n(\ulcorner X_n\hat u_n\urcorner)\eqsim_n\mathbb E^H_n(\ulcorner Y_n\hat u_n\urcorner)$ — **`ccee` 4.12.3 at the H-generable gate $\hat u$; FULL LIMIT; free** |
| $\mathbb E_\pi[m\,\mathbb 1(a\ge t)]=\mathbb E_\pi[a\,\mathbb 1(a\ge t)]$, Link 2 at the quote's own gate | "H's gated estimate of $Y_n$ is at least $t$" — **not supplied**; this is where Half 1 must come in, and it is deficits D1–D3 |

So the LI mirror of the nesting condition is *free*: the gate $\hat u$ is a feature of H's **own day-$n$ prices**, and `ccee` handles any generable gate. The reason it is free is a timing fact — $\hat u_n$ is available to H at day $n<f(n)$, so future-H is a priori in a position to know it — which is exactly $\sigma(a)\subseteq\mathfrak M$ in the frame. **Prediction, and it is checkable:** if publication were pushed past the lookahead ($e(n)>F(n)$), the target's gate could not be built from H's day-$n$ prices at all, and Witness 5.2's failure mode would be live rather than dormant. The corpus's direction worry is therefore correct in general and neutralised here by the publication schedule, not by anything about trust.

⟂ This is where I disagree with [[route-recurring-ccee]] §7.2's "the failure is not a direction-of-composition subtlety but a grain mismatch". Both obstructions are present. The direction one is real (Witness 5.2 is a proof that it is not vacuous) and happens to be discharged in this setting; the grain one is what actually kills the route. Recording only the second would leave the corpus with an unearned belief that the first was never a problem — and would mispredict the delayed-publication regime.

### 5.3 Obstruction O2 (grain) is what kills it

With O1 discharged, the composition reduces to: on gate days, is H's estimate of $Y_n$ at least $t$? Half 1 says the gate-weighted average of $a_i-Y_i$ has $0$ as a limit point, and $a_i>t$ on the gate's support; so along **some** subsequence the gate-weighted average of the **realized** $Y_i$ is $\ge t-o(1)$. From that to "H's day-$n$ estimate of $Y_n$ is $\ge t$" there are two further steps — average $\to$ per-day, and realized $\to$ H-estimated — and the second is the `cee` route's second unbiasedness application, on H's market, at the gate $\hat u$, which is again a limit point on its own subsequence. That is the common-subsequence gap ([[open-problems]] item 7), now reached *through* the transitivity framing rather than around it.

---

## 6. Repairs, each tried and killed honestly

### 6.1 (a) The gate sandwich

*The idea.* Split gate days into $\eta$-good ($|\bar a_n-Y_n|\le\eta$) and exceptional, hoping Half 1's unbiasedness controls the exceptional ones in average.

*What works.* On $\eta$-good days the sandwich is genuine and two-sided: $\operatorname{Ind}_\delta(Y_n>t+\eta)\le\hat u_n\le\operatorname{Ind}_\delta(Y_n>t-\eta)$, and more simply $|\hat u_n-\beta_n|\le\eta/\delta$. That is Lemma C with $e_n\le\eta/\delta$, giving soft TT with slack $2\eta/\delta$ — a clean, sharp statement.

*Why it dies.* Three reasons, in increasing order of seriousness.
1. **Gate domination alone is useless.** $\hat u\le\beta'$ bounds $\mathbb E^H_n(\ulcorner\hat u\urcorner)$ from above ✓ but also bounds $\mathbb E^H_n(\ulcorner X\hat u\urcorner)$ from above ✗ — the wrong direction on the side that needs a lower bound. Only a *two-sided* sandwich helps, and two-sidedness is exactly $|\bar a-Y|$ small, i.e. absolute-value control.
2. **The good-day set is not a legal index set.** To restrict any of the theorems to $\{n:|\bar a_n-Y_n|\le\eta\}$ one needs that set to be e.c.-recognisable; it is not — recognising it requires $Y_n$, i.e. running H to day $f(n)$. Lemma C is stated unconditionally precisely to avoid this; the price is that the exceptional days appear as an additive residual rather than being excised.
3. **The exceptional days are not controlled in average by Half 1, because of cancellation.** Half 1 constrains $\sum u_i(a_i-Y_i)/\sum u_i$; the residual needs $\sum u_i\,|a_i-Y_i|$ *and* needs it per day. Unbiasedness is invariant under sign-cancelling perturbations of the error that change $\operatorname{Ind}_\delta(a_n>t)$ arbitrarily — indeed that change *which days are gate days*. There is no unbiasedness theorem in the paper with an absolute value in it; families A and B ([[unbiasedness-theorem-families]] §1) both compare a price to a truth value in a signed average, and family C is an environment hypothesis, not a guarantee.

**Corollary B.1 (the one clean positive from the sandwich). PROVED modulo (Γ-REP) + (UA).** Assume **(UA)**: for every rational $\varepsilon>0$, $|\bar a_n-Y_n|<\varepsilon$ for all sufficiently large $n$. Then the full target holds, per day, at every $(t,\delta)$, both cuts:
$$\mathbb E^H_n(\ulcorner X_n\hat u_n\urcorner)\gtrsim_n t\,\mathbb E^H_n(\ulcorner\hat u_n\urcorner),\qquad\text{equivalently}\qquad \liminf_n\hat u_n\big(\mathbb E^H_n(X_n)-t\big)\ge0 .$$
*Proof.* By Theorem B it suffices that $\mathbb E^H_n(\ulcorner e_n\urcorner)\to0$. Fix rational $\varepsilon>0$ and let $N$ witness (UA). The sequence $\psi_n:=\ulcorner|\bar a_n-Y_n|<\varepsilon\urcorner$ for $n\ge N$, $\psi_n:=\ulcorner0=0\urcorner$ for $n<N$, is e.c. (fixed template plus numeral; $N$ is a constant) and consists of $\Gamma_H$-theorems by (Γ-REP) and (UA). Provability Induction 4.2.1 gives $\mathbb P^H_n(\psi_n)\eqsim_n1$. Since $e_n\le\varepsilon/\delta+\mathbb 1(|\bar a_n-Y_n|\ge\varepsilon)$ provably, `expprovind` 4.8.10 and `ei` 4.8.6 give $\limsup_n\mathbb E^H_n(\ulcorner e_n\urcorner)\le\varepsilon/\delta$. Let $\varepsilon\downarrow0$. $\square$

**What Corollary B.1 is and is not.** It is a genuine factoring theorem: *per-day accuracy against the future human composes with free self-trust to give per-day soft Total Trust, and H's learning of the accuracy is itself free* (deficit D3 dischargeable, by 4.2.1 — this is worth having, because "even a perfect forecaster must be *recognised* as perfect" is a real-looking objection, and it is answered). It is **not** a deference theorem, because (UA) is a strengthening of Half 1 from "unbiased in gate-average, subsequentially, signed" to "accurate per day, absolutely" — and that strengthening is false in general. Indeed 4.8.15 *forces* A to be unbiased and permits it to be per-day wrong: on an $A$-pseudorandom target, quoting the mean is optimal and the per-day error is $\Theta(1)$ forever.

### 6.2 (b) Using `cee`/`ccee` as Input 1 — the collapse into the `cee` route

The only way to avoid needing $|\bar a-Y|$ is to stop transferring the gate: keep the target's gate $\hat u$ throughout, and use `ccee` at $\hat u$ (or `cee` plus Lemma B — they are the same here, §2). That step is Theorem 5.1's first step, and after it the argument is:

1. `ccee`/`cee` at $\hat u$: $\hat u_n(h_n-g_n)\eqsim_n0$. **FULL LIMIT, free.**
2. Half 1 (A's 4.8.15 at $u$): $\overline{(a-Y)}^u_n\to0$ along $N_A$. **LIMIT POINT.**
3. H's 4.8.15 at $\hat u$ (needs (MIRROR) and (LL)): $\overline{(g-Y)}^{\hat u}_n\to0$ along $N_H$. **LIMIT POINT.**
4. Combine on $N_A\cap N_H$ — not supplied.

**Proposition 6.3.** This is precisely [[faithful-acceleration-result]] §4.3's chain; `est` does not appear in it. Hence: **the transitivity framing is not a fourth route.** Moreover, in its literal form (§4) it is *strictly worse* than the `cee` route: Theorem B's residual is vacuous ($e_n\equiv1$) on any target where A cannot beat the mean, whereas on exactly such targets the `cee` route still delivers its averaged conclusion. Example: $Y_n\in\{0,1\}$ A-pseudorandom, $a_n\equiv\tfrac12$, $t=0.4$, $\delta=0.05$ — the gate fires every day, $e_n\equiv1$ so Theorem B says nothing, yet $h_n\eqsim g_n\eqsim\tfrac12\ge t$ and the target holds. **The gate transfer demands absolute-error control where the `cee` route demands only signed-average control; that is a strictly larger ask.**

**Which gap does the transitivity route inherit?** Neither, and that is the point. Theorem B *evades* the common-subsequence gap entirely — it uses no unbiasedness theorem at all, and is a full limit per day. It pays for the evasion with a residual no hypothesis-free theorem controls. Attempting to fill the residual with Half 1 re-inherits the common-subsequence gap **and** adds the cancellation deficit on top. So the honest accounting is: *the transitivity route trades the common-subsequence gap for a strictly larger one.*

### 6.3 (c) Sparse schedules via corrected 4.8.16

On a schedule $S=\operatorname{im}g$ with support $\subseteq S$ and $\operatorname{Val}_{\Gamma}(Y_n)$ computable in $O(g(n{+}1))$ (evaluation-sparse — [[route-sparse-schedule]] §3; the trade the corpus already knows), corrected 4.8.16 upgrades steps 2 and 3 above from limit points to **full limits**, which do combine — closing the `cee` route on $S$. That is deficit **D2**, and it is the whole of what sparsity buys.

It does **not** rescue transitivity. Deficit D1 (average vs per day) and the cancellation inside it are untouched by sparsity: a full-limit average is still an average. Concretely, the witness of §7 restricted to $S$ (put the sparse bad set inside $S$, sparse within $S$) satisfies both inputs *with full limits* and still refutes the per-day target. So there is no scheduled transitivity theorem beyond the scheduled `cee` route, and I do not pursue the schedule further — that route is being worked directly elsewhere in this lab ([[route-sparse-schedule]]).

---

## 7. The counterexample

### 7.1 Non-derivability (the inference is refuted)

**Proposition 7.1. PROVED (prose).** There are two scenarios — assignments of numerical sequences to $(Y_n,a_n,h_n,g_n,\text{H's expectations of the quoted products})$ — that

- agree on all of Half 1's data (both have gate $u\equiv1$ and gate-weighted error $\to0$, a **full limit**, hence also a limit point, hence also the 4.8.16-strength conclusion),
- both satisfy `est` (Lemma A) at every threshold,
- both satisfy `cee`, `ccee` at the gate, and H's own 4.8.15 at the gate (exactly, with zero error),

and in which the target respectively **holds** and **fails**. Therefore the target is not entailed by the conjunction of Input 1's and Input 2's conclusions, even with the free H-side theorems thrown in and even at 4.8.16 strength.

*The witness.* Fix $t=\tfrac12$, $\delta=\tfrac14$. Let $D\subseteq\mathbb N$ be infinite with density $0$ (e.g. $|D\cap[1,n]|=O(\log n)$).

| | $n\notin D$ | $n\in D$ |
|---|---|---|
| $Y_n$ | $1$ | $0$ |
| $a_n$ | $1$ | $1$ |
| $h_n=g_n$ | $1$ | $0$ |
| $u_n=\hat u_n$ | $1$ | $1$ |
| $\beta_n=\operatorname{Ind}_\delta(Y_n>t)$ | $1$ | $0$ |

Scenario 2 is the same with $D=\varnothing$.

*Checks (all exact).*
- **Half 1:** $\frac1n\sum_{i\le n}(a_i-Y_i)=|D\cap[1,n]|/n\to0$ — a full limit, so a fortiori $0$ is a limit point. ✓ (Numerically: $0.06$ at $n=10^2$, $9\cdot10^{-3}$ at $10^3$, $2.4\cdot10^{-4}$ at $2^{16}$, for $D=\{2^k\}$.)
- **`est`:** H knows $Y_n$ in this scenario, so by Lemma B $\mathbb E^H_n(\ulcorner X_n\beta_n\urcorner)=\beta_nh_n=\beta_n$ and $t\,\mathbb E^H_n(\ulcorner\beta_n\urcorner)=\tfrac12\beta_n$. ✓ for all $n$.
- **`cee`/`ccee`:** $h_n=g_n$ exactly. ✓
- **H's own 4.8.15 at the gate:** $g_n=Y_n$ exactly, so the weighted average error is $0$. ✓
- **Target, per-day form:** on $n\in D$, $\hat u_n(h_n-t)=-\tfrac12$. So $\liminf_n\hat u_n(h_n-t)=-\tfrac12<0$: **fails**, infinitely often, at margin $\tfrac12$. ✗
- **Target, gate-weighted form:** $\frac1n\sum_{i\le n}u_ih_i\to1\ge t$. ✓ — so the witness *separates* the per-day target from the averaged surrogate, confirming §3's warning.

*What it localises.* On $D$, `est`'s gate $\beta$ is switched **off** — the future-price gate is honest about exactly the days on which the advertisement is dishonest — while the target's gate is switched **on**. Input 1 is structurally blind to the failure set. That is the object/subject asymmetry, realised.

### 7.2 Strengthening Input 2 to all A-generable gates

A real forecaster satisfies 4.8.15 at *every* $\overline{\mathbb P}^A$-generable divergent gate, not just at $u$. Under that strengthening the witness survives only if $D$ is **A-pseudorandom**: if $D$ were e.c. (say $D=\{2^k\}$), the weighting $v_n:=\mathbb 1(n\in D)$ would be A-generable and divergent, and 4.8.15 at $v$ would force $\overline{(a-Y)}^v$ to have $0$ as a limit point, killing $a\equiv1,Y\equiv0$ on $D$. So the witness upgrades to a statement about actual inductors only if $D$ is invisible to every A-generable weighting **while being visible to H**.

### 7.3 Realizability: this is open problem 9, with a design

The upgrade demands a set $D$ that A cannot detect and H can. Three observations, in order of how much they help:

1. **H has an information channel A structurally lacks.** By `cee`, H's best estimate of $Y_n$ *is* its own current credence $h_n$ — introspection, free. A must forecast $Y_n=\mathbb E^H_{f(n)}(X_n)$, which means simulating H to day $f(n)=2^n$ at day $n$: not merely outside $\mathcal C_A$-per-day, but outside any plausible budget. The complexity gap $\mathcal C_H\subseteq\mathcal C_A$ does **not** close this, because the gap is about power at a given day, and the obstruction is about the *lookahead*.
2. **One-way visibility is what makes the design coherent.** The natural detector of $D$ is $v_n:=\operatorname{Ind}_{1/4}\big(\mathbb E^H_n(\ulcorner Y_n\urcorner)<\tfrac14\big)$ — a ramp on **H's own price of the target**. It is $\overline{\mathbb P}^H$-generable, so H's theorems see it; it is not $\overline{\mathbb P}^A$-generable (it is a feature of the *other* market's prices, and it is not e.c.), and under one-way clearing A cannot read it even in principle, since H's day-$n$ prices do not exist when A clears. So A's unbiasedness theorems are blind to precisely the gate that exposes it. *This is the design open problem 9 was missing, and it matches that item's own note that "the human's own price must straddle the threshold with positive frequency".*
3. **The hard part is timeliness, and it is genuinely hard.** A can (budget permitting) simulate H's day-$(n{-}1)$ market. If H's foreknowledge of $D$ is visible in its prices *before* day $n$, A can learn the pattern from its own side and correct. A real construction must therefore make H's recognition of a $D$-day arrive exactly at day $n$ — a self-referential design requirement. That is the same wall open problem 9 reports, and I have not climbed it.

**Verdict on constructibility: CONJECTURED (~0.55).** Note the consistency check this provides: if the composition were valid, it would prove that *no* such construction exists — i.e. it would settle open problem 9 negatively — and the corpus rates that construction ~0.45. So the corpus's own credences already imply the composition is at most ~0.55, before any of the analysis above. The analysis above is what pushes it to $\le0.10$.

---

## 8. The prior work: `deference-trust-lab/run3/work/tt-transitivity-forall/`

Three files: `TTTransitivity.lean` (485 lines, `sorry`-free, axiom-audited to `[propext, Classical.choice, Quot.sound]`), `tt_search.py` (exact Fourier–Motzkin decision procedure, no grids), `tt_search_output.txt`.

**What it established (and it is solid).**
- `TT_condExpert`: a partition conditional-expectation expert is Totally Trusted by its own prior, for **all** $X$ and **all** $s$ — the finite law of total expectation read as a TT statement. KERNEL-CHECKED.
- A concrete $\mathrm{Fin}\,3$ chain: $\pi_H\ \mathrm{TT}\ P_A$ and $\pi_A\ \mathrm{TT}\ P_B$ both hold with the genuine $\forall X\forall s$ quantifier, yet $\pi_H\ \mathrm{TT}\ P_B$ fails, with exact gap $\tfrac18$. So **chain-transitivity of Total Trust is false**.
- The exact characterisation `TT_condExpert_cross_iff`: for positive priors, $\pi_H$ Totally Trusts the $\pi_A$-conditional expert of a partition **iff** the two priors' conditionals agree on every cell — correcting run2's slogan "the obstruction is prior mismatch" to the sharper "conditional mismatch on a cell", with `sharper_recovery` showing prior identity is sufficient but not necessary.
- It is scrupulously honest about scope: "a finite-frame DDB statement over an ordered field… It is NOT an LI/asymptotic result."

**What it left open, and where it does not apply to open problem 14.** Its square is the **chain** $H\to A\to B$: Link 2 is "$\pi_A$ trusts $P_B$", a *trust* statement with the middle party as **subject twice**. Open problem 14's Link 2 is "A is *calibrated to* future-H", with the middle party as **object**. So the prior counterexample refutes a composition that open problem 14 does not assert, and — this is the trap — its refutation says nothing about ours, in either direction. Anyone citing it as settling item 14 would be citing the wrong square. (Nor is it a special case: our Link 2 is not implied by, and does not imply, "future-H Totally Trusts A".)

**How this note extends it.** §5.1 supplies the correctly shaped square — Link 1 = `TT_condExpert` verbatim (so the prior lemma is reused, not superseded), Link 2 = exact calibration $a=\mathbb E_\pi[m\mid\mathfrak A]$ — and settles it: **REFUTED in general (Witness 5.2), PROVED under nesting (Theorem 5.1)**. The lever is different from the prior work's: there it was cellwise conditional agreement between two priors; here there is one prior throughout, and the lever is **measurability of the quote w.r.t. the middle party's $\sigma$-algebra** — i.e. whether the middle party knows what the forecaster said. Both are "the composition fails for a structural reason, and the structural reason is nameable"; they are different structures. Witness 5.2 and Theorem 5.1 are elementary enough to be worth a short Lean file in the prior work's style (`TT_condExpert` is already there; the nesting theorem is two tower steps, and the witness is a `norm_num` on $\mathrm{Fin}\,4$ rationals) — recommended, not done here.

**One correction of emphasis.** The prior work's header calls its result "the first machine-checked statement in this lab whose SUBJECT is trust between two agents". True, but the statement it checks is about a *chain*; the honest one-line summary for the corpus is "**chain**-transitivity of finite-frame TT is false", and item 14's entry should not point at it without that qualifier.

---

## 9. Relation to the `cee` route and the common-subsequence gap

Summarised, because it is the thing most likely to be misremembered:

| | uses `est`? | uses A's 4.8.15? | uses H's 4.8.15? | limit points consumed | residual |
|---|---|---|---|---|---|
| **Theorem B** (this note) | yes | no | no | **0** | $\mathbb E^H_n(\ulcorner\min(1,\lvert\bar a_n-Y_n\rvert/\delta)\urcorner)$, per day, uncontrolled |
| Theorem B + (UA) | yes | no | no | 0 | none — but (UA) is a strengthened Half 1 |
| transitivity with Half 1 filling the residual | yes | yes | no | 1 | absolute-vs-signed cancellation — **not fillable** |
| the `cee` route (§4.3) | **no** | yes | yes | 2, on unrelated subsequences | the common-subsequence gap |
| the `cee` route on a 4.8.16 schedule | no | yes | yes | 0 (full limits) | none, but sparsity + averaged conclusion only |

So: Theorem B **evades** the common-subsequence gap; the composition **re-inherits** it and adds cancellation; the scheduled version fixes only the inherited part. And the target that any averaged route reaches is, by Prop. 3.1 and the witness of §7.1, strictly weaker than soft Total Trust as defined.

---

## 10. Deliverables

### (a) Verdict on open problem 14

**Trust does not compose.** Precisely:

- As an **inference**, the composition is **REFUTED**: Prop. 7.1 exhibits two scenarios satisfying the conclusions of Input 1 (`est`) and Input 2 (Half 1, at 4.8.16 strength) plus `cee`, `ccee` and H's own 4.8.15, differing on the target. **Confidence 0.90.**
- The failure has **two independent causes**, and the corpus's recorded worry names the first correctly: **O1 (direction/subject-object)** — real, and a theorem-level obstruction even with Input 2 at maximal strength (Witness 5.2, finite frame); **discharged in this setting** by `ccee` at an H-generable gate, whose availability is exactly the publication-before-lookahead timing. **Confidence 0.90** that O1 is real in general; **0.85** that it is discharged here. **O2 (grain/strength)** — the gate substitution's residual is H's day-$n$ expectation of the *truncated absolute* forecast error (Lemma C, exact); Half 1 supplies a signed gate-average with a limit point. Not repairable by sparsity, which fixes a different deficit. **Confidence 0.90.**
- **Transitivity is not a fourth route.** Its only non-vacuous repair drops the gate transfer, at which point `est` is unused and the argument *is* the `cee` route; in its literal form it is strictly worse than the `cee` route (Prop. 6.3). **Confidence 0.85.**

### (b) The composed theorem that does exist, and the obstruction lemma

**Theorem B (robust self-trust).** For every e.d. $(X_n)$, rational $t$, rational $\delta>0$, with $\hat u_n=\operatorname{Ind}_\delta(\mathbb E^H_n(\ulcorner a_n\urcorner)>t)$ and $e_n=\min(1,|\mathbb E^H_n(\ulcorner a_n\urcorner)-Y_n|/\delta)$:
$$\mathbb E^H_n(\ulcorner X_n\hat u_n\urcorner)\;\gtrsim_n\;t\,\mathbb E^H_n(\ulcorner\hat u_n\urcorner)-(1+t)\,\mathbb E^H_n(\ulcorner e_n\urcorner)\qquad\textbf{(FULL LIMIT, all days)},$$
plus the dual cut; under (LL) the same with the true quote gate $u$, at cost $O(1/\delta)\cdot o(1)$. **Named hypotheses: (Γ-REP)** only (plus (LL),(P) for the $u$ form). No visibility assumption, no joint clearing, no schedule, no (MIRROR), no divergence. **Corollary B.1.** Under **(UA)** ($\forall\varepsilon>0$, eventually $|\bar a_n-Y_n|<\varepsilon$) the residual vanishes — H's recognition of the accuracy being free, by Provability Induction 4.2.1 — and the **full per-day target holds at every $(t,\delta)$, both cuts.**

**Obstruction Lemma.** Any composition of the shape "`est` at future-price gates + a control $C$ on $(a_n-Y_n)$ ⟹ soft TT at the quote gate" requires $C$ to bound $\mathbb E^H_n(\ulcorner\min(1,|a_n-Y_n|/\delta)\urcorner)$ per day. No hypothesis-free theorem supplies this, because: (i) families A and B compare a price to a truth value in a *signed weighted average*, and are invariant under sign-cancelling perturbations of the error which change the quote gate — and hence change which days are gate days — arbitrarily; (ii) family C is an environment hypothesis, not a guarantee ([[unbiasedness-theorem-families]] §1); (iii) family D never mentions truth. Prop. 7.1 shows the requirement is not an artefact of this proof: the target is not entailed by the premises.

### (c) What the prior `tt-transitivity-forall` work had right and wrong

**Right, and reusable:** `TT_condExpert` (Link 1, kernel-checked); the falsity of **chain**-transitivity with the honest $\forall X\forall s$ quantifier; the exact cellwise-conditional characterisation; the correction of run2's slogan; its own scope honesty. **Nothing in it is wrong.** **Wrong to cite for item 14:** its square is $H\to A\to B$ with the middle party a *truster*; item 14's middle party is a *predicted object*. The two are logically independent. **Extended here:** the correctly shaped square is settled — REFUTED in general (Witness 5.2, $|W|=4$, gap $\tfrac18$; corroborated by an exhaustive-style random sweep), PROVED under nesting (Theorem 5.1), with the LI dictionary of §5.2 showing why the LI setting sits on the provable side of that line.

### (d) Status per corpus convention

| item | status |
|---|---|
| Lemma A (`est`, LUV form of Self-Trust) | **PROVED (prose)**, modulo (Γ-REP). Convergent with [[route-recurring-ccee]] T4. |
| Lemma B (Gate-Knowledge Collapse), Prop. 3.1 (target is per-day) | **PROVED (prose)**, modulo (Γ-REP) |
| Lemma C (Bridge), **Theorem B** | **PROVED modulo named hypotheses** ((Γ-REP); + (LL),(P) for the $u$ form) |
| Corollary B.1 | **PROVED modulo named hypotheses** ((Γ-REP), (UA)) |
| Theorem 5.1 (nesting ⟹ TT, finite frame) | **PROVED (prose)**, elementary; Lean-ready |
| Witness 5.2 (direction obstruction, finite frame) | **REFUTED** (of the general square), exact rational witness, machine-verified arithmetic; Lean-ready |
| Prop. 7.1 (non-derivability witness) | **PROVED (prose)** as a statement about the abstract data |
| Realizability of Prop. 7.1 by an actual inductor pair | **CONJECTURED (~0.55)** — open problem 9's family; §7.3 supplies the gate design |
| Prop. 6.3 (transitivity ⊆ the `cee` route; strictly worse in literal form) | **PROVED (prose)** |
| Open problem 14 | **REFUTED as an inference** (0.90); the surviving content is Theorem B + Cor. B.1 |
| Open problem 13, touched | second independent argument for [[route-recurring-ccee]]'s verdict: **accounting claim REFUTED**; `ccee`'s real home is Input 1, not the `cee` route |
| Open problem 4, touched | **affirmative for rational generable gates**, by `loe` 4.8.4 (Lemma B) — not by anything in §4.11–4.12 |
| `ccee`'s $w_{f(n)}$ indexing | **clarified**: rank $\le f(n)$ *includes* rank $\le n$, so day-$n$ gates are legal by pullback along $f$ — the wiki §4.1 application is rescued, but not for the reason given there |

Nothing here is in Lean. The three Lean-ready items are Theorem 5.1, Witness 5.2, and the arithmetic of Lemma C.

### (e) The three things a skeptic attacks first

1. **Lemma B, and with it Prop. 3.1's claim that the target is per-day.** The attack: `loe` 4.8.4 requires $\Gamma_H\vdash Z_n=c_nX_n$ with $c_n$ a *numeral*, i.e. it requires $\Gamma_H$ to pin H's own day-$n$ prices — a self-referential demand, and one that the LI paper makes only from §4.8 onward and only for a single market. If (Γ-REP) is weaker than assumed for the coupled system, the collapse degrades and the target regains genuine soft-conditioning content, which would *weaken* the target and make the composition easier. This is the highest-value attack, and it attacks a conclusion in my favour. Defence: the paper's own `st`/`ccee` proofs make exactly this move ("for all $W\in\mathcal{PC}(\Gamma)$, $W(\ulcorner\mathbb E_n(X_n)\urcorner)=\mathbb E_n(X_n)$", `main.tex:5504–5560`), and $H$'s market is computable by construction.
2. **Prop. 7.1's status as a *non-derivability* result.** The attack: a witness in free numerical sequences shows only that a particular premise set fails to entail the target; a real pair of inductors satisfies infinitely many further constraints, so the composition could still be *true* while unprovable from these two inputs. Correct, and I concede it — which is why §7.2–7.3 do the extra work and why realizability sits at 0.55, not higher. But note that open problem 14 as posed asks whether the two inputs *compose*, and that is exactly what Prop. 7.1 answers. The stronger claim (soft TT is false for some pair) is open problem 9.
3. **The claim that O1 is discharged (§5.2).** The attack: the finite-frame dictionary is an analogy, and "$\mathfrak A\subseteq\mathfrak M$" has no literal LI meaning — `ccee` at an H-generable gate might be doing something else entirely, and the real LI content of non-nesting might reappear as a further hidden deficit in the step "H's gated estimate of $Y_n$ is $\ge t$". Defence: the correspondence is exact at the level of *what each step proves* (Theorem 5.1's two steps map onto `ccee`-at-$\hat u$ and Link-2-at-the-quote's-own-gate, in that order, with the same measurability requirements), and the residual identified in §5.3 is visibly the second step and nothing else. But the mapping is a reading, not a theorem, and a skeptic is entitled to demand it be checked against a delayed-publication regime, where it makes a falsifiable prediction.

## Related

- [[unbiasedness-theorem-families]] §4.2 (the framing and the warning), §1 (the four families), §6 (the gate/ledger trap)
- [[faithful-acceleration-result]] §2 (the factoring), §3 (Half 1), §4.3 (the `cee` route and its gap), §5 (honest strength)
- [[deference-notions]] (soft TT's unnormalized threshold form; the fold; `st` as the self-instance), [[setting-and-notation]] (the ledger, the thin channel)
- [[li-paper-erratum]] §1 (corrected 4.8.15/4.8.16), §3 (numbering)
- [[open-problems]] items 4, 7, 9, 13, 14
- `deference-trust-lab/run3/work/tt-transitivity-forall/` (prior work; §8)
- `varying-question-lab/[[route-recurring-ccee]]`, `varying-question-lab/[[route-sparse-schedule]]` (parallel routes, same lab)
