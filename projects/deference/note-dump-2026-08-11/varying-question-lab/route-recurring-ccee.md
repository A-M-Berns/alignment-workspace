# The recurring `ccee` route: the strongest all-days varying-question trust statement under one-way visibility

*Setting: coupled cross-process, **one-way** visibility (A clears, publishes, then H clears). Regime: **all days, no schedule.** Target: soft Total Trust of H in the lookahead expert $E^\ast(X_n) := a_n$, unnormalized threshold form. Conventions: [[conventions-and-status-labels]]. Written 2026-07-30.*

*Every asymptotic conclusion below is explicitly labelled **FULL LIMIT** or **LIMIT POINT**. Theorem numbers are arXiv v5 numbers, in the corrected forms of [[li-paper-erratum]]; source of truth `references/logical-induction/main.tex`.*

---

## 0. Verdicts up front

| question | verdict | confidence |
|---|---|---|
| **Open problem 13** — does `ccee` (4.12.3) remove one of the two limit points in the `cee` route? | **Split.** The *gated identity* $\mathbb E^H_n(\ulcorner X_n u_n\urcorner)\eqsim_n\mathbb E^H_n(\ulcorner Y_n u_n\urcorner)$ is **TRUE, a FULL LIMIT, all days** (§3) — so the "cheapest improvement" is real and now proved. But the accounting claim is **REFUTED**: it removes *neither* of the two limit points. `cee` was already a full limit, and the step `ccee` replaces was never one of the two. The count stays at **two**. Moreover `ccee` is not even needed: `cee` + 4.8.10 gives the same identity, because the quote gate is day-$n$ measurable and `ccee`'s $w_{f(n)}$ indexing is strictly more general than required. | 0.88 |
| **Open problem 7** — is there a single application of an LI theorem yielding both halves at once? | **NO, under one-way visibility** — and provably not, in three independent senses: (a) a *structural* argument (§5.6): no theorem in the paper quantifies over two markets, and each market's criterion constrains only its own prices against the shared $\operatorname{Val}_\Gamma$, so any derivation must invoke a family-A/B theorem once per market; (b) an explicit **non-derivability witness** (§5.5) showing the premise set {A's 4.8.15 on $u$; H's 4.8.15 on $u$; `cee`/`ccee`; $\bar a_n\ge t$} is consistent with a *uniform, permanent* trust violation — so no bookkeeping can close it; (c) a **risk obstruction** (§5.4): the only known full-limit H-side bridge (the realized-cash trader) has bounded risk **iff** its weighting is $f$-patient, and $f$-patient weightings accumulate only $O(\log^\ast n)$ mass — provably not all-days. The single application **does** exist under joint clearing; that is exactly what v3 is. | 0.85 |
| Can 4.8.12 / 4.8.13 (family D) remove the remaining limit point? | **NO.** For $\Gamma$-determined $\overline B$ their combination collapses to Expectation Coherence 4.8.11 — $\liminf_n\mathbb E_n(B_n)\ge\liminf_n\operatorname{Val}(B_n)$ and dually (§5.2). These are *pointwise envelope* bounds, not averages, and they are vacuous on a gate that switches off infinitely often. Family D never mentions truth (this is the corpus's own §2 sorting) and the determined case is the one place it touches truth — through 4.8.11, which is weaker than what is needed. | 0.90 |
| Open problem 16 (4.8.12 replaces convergence in Theorem A) — touched | **Unaffected by the above, but the same collapse applies**: for determined sequences 4.8.12+4.8.13 give exactly 4.8.11. Theorem A needs a *pointwise* envelope, which is precisely what 4.8.11 supplies — so 16 is plausibly YES for Theorem A even though family D fails here. Not pursued. | 0.5, unchanged |
| Open problem 14 (`st` composes with Half 1) — touched | **NO under one-way visibility, same obstruction** (§7.2). The LUV form of `st` is free, full-limit, all days — but at the gate "*future*-H exceeds $p$". Transporting that gate to "A quotes above $t$" *is* Half 1, which is an average statement, not a per-day one. | 0.8 |

**Headline positive results (§6).** All-days, one-way, varying questions, no schedule:

- **T1 (FULL LIMIT).** The gated tower identity — H's present gated credence equals H's gated expectation of its own future credence, exactly, on every legal gate.
- **T2 (LIMIT POINT).** On every A-generable gate with divergent mass, the gate-weighted **realized future human credence** is $\ge t - o(1)$ infinitely often.
- **T3 (Oscillation Theorem, ALL DAYS, unconditional).** A *permanent* gated trust deficit of margin $c$ forces the gate-weighted realized future credence to oscillate forever with amplitude $\ge c$. Contrapositive: **if the gate-weighted realized future credence converges, recurring soft Total Trust holds** — $\limsup_n$ of the gated average of $\mathbb E^H_n(X_n)$ is $\ge t$; if the gated average of $\mathbb E^H_n(X_n)$ also converges, this upgrades to a **FULL LIMIT**.
- **T4 (FULL LIMIT, free).** H totally trusts its own future self at the *future-credence* gate — the LUV form of `st` 4.12.4, which the paper does not state. This localizes the entire remaining deficit to one step: transporting the gate from "future-H exceeds $t$" to "A quotes above $t$".

**Status of the route as a whole: the `cee`/`ccee` route is REFUTED as an all-days deference argument** (in the precise sense of §5.5: its premise set does not entail its conclusion), and **PROVED modulo named hypotheses in the weakened forms T1–T4**. The wiki's CONJECTURED (~0.6) for the `cee` route should be revised: the *identity* half is now proved, the *combination* half is refuted, and what survives is T3.

---

## 1. Setting and named hypotheses

Two logical inductors, $H\dashv\mathcal C_H$ over a $\Gamma_H$-complete deductive process $D^H$, and $A\dashv\mathcal C_A$ over $D^A$; canonically $\mathrm P\subseteq\mathrm{EXP}$. $(X_n)$ is an e.d. sequence of $[0,1]$-LUVs of $H$'s language. $f$ is a deferral function (Def. 4.3.7, `main.tex:1240`): $f(n)>n$, strictly increasing, computable in time polynomial in $f(n)$; canonically $f(n)=2^n$. Write

$$Y_n := \mathbb E^H_{f(n)}(X_n),\qquad a_n := \mathbb E^A_n(\ulcorner Y_n\urcorner),\qquad h_n := \mathbb E^H_n(X_n),\qquad g_n := \mathbb E^H_n(\ulcorner Y_n\urcorner).$$

For rational $t\in[0,1]$ and rational $\delta>0$ put the **quote gate**

$$u_n := \operatorname{Ind}_\delta(a_n > t)\in[0,1]\cap\mathbb Q \qquad(\text{Def. 4.3.2}),$$

and for a weighting $\theta$ with $\Theta_n:=\sum_{i\le n}\theta_i$ write $\bar x^{\,\theta}_n := \Theta_n^{-1}\sum_{i\le n}\theta_i x_i$; when $\theta=u$ the superscript is dropped ($\bar a_n,\bar Y_n,\bar h_n,\bar g_n$).

**Order of clearing (ONE-WAY).** Each day $n$: A's market clears in the ordinary single-market way (A never reads H); $a_n$ is then published into $D^H$ as decided ledger atoms; then H's market clears. The composite system is computable and there is no joint fixed point to construct ([[joint-clearing-and-trader-class]] §3). No circularity: A's market is defined without reference to H; $H$'s day-$n$ state is defined given $a_{\le n}$; $Y_n$ refers to H at day $f(n)$, which refers to $a_{\le f(n)}$ — all well-founded.

### Named hypotheses

- **(BLCS-A)** $\overline{\ulcorner Y\urcorner}$ is an e.c. sequence of expressions (fixed template plus numeral), bounded, hence a legal $\mathcal{BLCS}$ sequence for $A$. *(Standing.)*
- **(DET-A)** $\overline{\ulcorner Y\urcorner}$ is determined via $\Gamma_A$ (Def. 4.8.14), with $\operatorname{Val}_{\Gamma_A}(\ulcorner Y_n\urcorner)=Y_n$. $\Gamma_A$ extends PA, represents computations, is consistent. *(Standing.)*
- **(MIRROR)** *Genuinely extra, and used only on H's side.* $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}(\overline{\mathbb P}^H)$ and is determined via $\Gamma_H$, with $\operatorname{Val}_{\Gamma_H}(\ulcorner Y_n\urcorner)=Y_n$. Equivalently: $\Gamma_H$ represents the computation of the coupled system, so $\Gamma_H$ pins H's own day-$f(n)$ expectation. This is the same standing assumption §4.11–§4.12 of the paper make about $\Gamma$ and $\overline{\mathbb P}$ (their `epr`/`er`/`cee` proofs all say "for all $W\in\mathcal{PC}(\Gamma)$, $W(\ulcorner\mathbb E_n(X_n)\urcorner)=\mathbb E_n(X_n)$"), but here it is being applied to a *coupled* market, so it must be declared.
- **(Γ-REP-H)** $\Gamma_H$ represents the computation of $\overline{\mathbb P}^A$ and hence of $a_n$, $u_n$: for every $W\in\mathcal{PC}(\Gamma_H)$ and every $n$, $W(\ulcorner u_n\urcorner)=u_n$ and $W(\ulcorner X_n\cdot u_n\urcorner)=u_n\,W(X_n)$. *(Implied by (MIRROR) in practice; listed separately because §3 uses it and §5 does not.)*
- **(H⁺-CLASS)** *The ledger hypothesis, and the one that does the most work.* H's trader class is $\mathcal C_{H^+}$ := functions computable in time polynomial in $n$ **given the published quote stream $a_1,\dots,a_n$ as input**, and $H$ satisfies the logical-induction criterion against $\mathcal C_{H^+}$. Correspondingly "e.c." in every H-side theorem application is read as "$\mathcal C_{H^+}$-computable", and Def. 4.3.5 generability is relativized to the same notion. See §2 for why this is unavoidable and what it costs.
- **(DIV)** $\sum_n u_n=\infty$. Without it every gated statement is about finitely much mass and is vacuous. (Divergence is *not* automatic and is not implied by anything below.)
- **(F-INV)** — *not* a hypothesis. It is a lemma: for any deferral function $f$, the predicate $m\in\operatorname{im}(f)$ and the value $f^{-1}(m)$ are computable in time polynomial in $m$. *Proof.* Let $h$ be the polynomial with $f(j)$ computable in $\le h(f(j))$ steps, wlog monotone. For $j=1,2,\dots$: run $f$ on $j$ for $h(m)$ steps. If it halts with value $v$: return $j$ if $v=m$, "no" if $v>m$, continue if $v<m$. If it does not halt in $h(m)$ steps then $f(j)>m$ (else it would halt in $h(f(j))\le h(m)$ steps): return "no". Since $f(j)>j$, the loop stops by $j=m$. Total $m\cdot h(m)$. $\square$ (The paper uses this silently in the `cee`/`ceu`/`ccee` proofs when it says "$Y_m:=X_n$ if $m=f(n)$ … observe that $(Y_m)_m$ is e.c.".)

---

## 2. Gate legality: the ledger, correctly

This section discharges **traps 2 and 4** and corrects [[unbiasedness-theorem-families]] §6.

**The trap, restated.** Definition 4.3.5 (Generable From $\overline{\mathbb P}$) demands an **e.c.** $\mathcal{EF}$-progression: $q_n=\tilde q_n(\overline{\mathbb P})$ with $\tilde q_n$ an expressible feature of *rank $\le n$*, the whole progression producible in poly time. Expressible features (Def. 3.4.3, appendix A.2) are built from the market's **own** price features, rationals, $+,\times,\max$, safe reciprocal. Two independent obligations therefore sit on any weighting: (i) it must be a continuous function of the market's own prices; (ii) the *description* must be producible in poly time. A's quote $a_n$ fails (ii) for a plain-$\mathrm P$ H: producing it means running A.

**The wiki's repair is defective as literally written.** The proposed gate is
$$\tilde u_n := \operatorname{Ind}_\delta\big(\mathbb P^H_n(\ulcorner a_n>t\urcorner)>\tfrac12\big).$$
Suppose the tracking one wants does hold, i.e. $\mathbb P^H_n(\ulcorner a_n>t\urcorner)\to\mathbb 1[a_n>t]$. Then $\operatorname{Ind}_\delta(\cdot>\tfrac12)$ evaluated at a quantity converging to $\{0,1\}$ converges to the **hard** indicator: $\tilde u_n=\mathbb 1[a_n>t]$ for all large $n$. But A's side must use the **ramp** $u_n=\operatorname{Ind}_\delta(a_n>t)$ (the hard indicator is discontinuous, hence not generable from A's prices). So $\tilde u$ and $u$ disagree on every day with $t<a_n\le t+\delta$, and the two 4.8.15 applications are then taken against *different* weightings — which destroys the comparison the route exists to make. **This is a real defect and should be recorded in the wiki.**

**Two correct repairs.**

*(R1) Relativize generability (used as primary below).* Under **(H⁺-CLASS)**, $a_n$ is computable in poly time from the published stream, so the constant-valued progression $\tilde u_n:\equiv\operatorname{Ind}_\delta(a_n>t)$ — rank $0$, trivially continuous in H's prices, poly-time producible — is a legal $\overline{\mathbb P}^H$-generable weighting *in the relativized sense*. So the **raw gate $u$ is legal for H**, matching A's gate exactly.

*(R2) Stay inside plain generability, with a corrected ledger gate.* Let the ledger decide $\ulcorner a_n\urcorner$ to precision $1/n$ and put $\hat a_n:=\mathbb E^H_n(\ulcorner a_n\urcorner)$, $\tilde u_n:=\operatorname{Ind}_\delta(\hat a_n>t)$. Then $\tilde u_n$ is a rank-$n$ expressible feature of H's own prices with a poly-time description (writing the *formula* $\ulcorner\mathbb E^A_n(\ulcorner Y_n\urcorner)\urcorner$ is poly-time even though its *value* is not — **trap 4**), and since $\operatorname{Ind}_\delta$ is $\tfrac1\delta$-Lipschitz, $|\tilde u_n-u_n|\le|\hat a_n-a_n|/\delta$. So R2 works **iff** $\hat a_n\to a_n$.

**Lemma 2.1 (Ledger tracking).** Assume (H⁺-CLASS). Let $\overline Z$ be an e.c. sequence of $[0,1]$-LUVs determined via $\Gamma_H$ with values $z_n$, and suppose a $\mathcal C_{H^+}$-machine computes rationals $\hat z_n$ with $|\hat z_n-z_n|\le\varepsilon_n\to0$. Then $\mathbb E^H_n(Z_n)\eqsim_n z_n$ (**FULL LIMIT**). *Proof.* $B_n:=Z_n-\hat z_n$ is a bounded LUV-combination; its trailing coefficient $-\hat z_n$ is a rank-$0$ feature with a $\mathcal C_{H^+}$-poly-time description, so $\overline B\in\mathcal{BLCS}(\overline{\mathbb P}^H)$ *in the relativized sense*. Fix $\varepsilon>0$, let $N$ be such that $\varepsilon_n\le\varepsilon$ for $n\ge N$, and replace $B_n$ by $0$ for $n<N$ (finitely many changes; still e.c.). Every $W\in\mathcal{PC}(\Gamma_H)$ gives $W(B_n)=z_n-\hat z_n\ge-\varepsilon$, so Expectation Provability Induction **4.8.10** gives $\mathbb E^H_n(B_n)\gtrsim_n-\varepsilon$. As $\varepsilon>0$ was arbitrary, $\mathbb E^H_n(Z_n)\gtrsim_n\hat z_n$; symmetrically $\lesssim_n$. $\square$

**The honest accounting.** R2 needs Lemma 2.1, which needs (H⁺-CLASS); R1 needs (H⁺-CLASS) directly. **There is no version of this route in which H's plain-$\mathrm P$ trader class suffices**, and that is not an artifact: if no H-side trader can read the quote, nothing constrains H's prices on quote-referencing sentences, and no trust statement about H's relation to A is available at all. (Note in particular that **the wiki's appeal to Provability Induction 4.2.1 for the tracking step is wrong**: 4.2.1 requires an e.c. sequence of *theorems*, i.e. a uniform truth value, whereas the pattern $\mathbb 1[a_n>t]$ is exactly the non-e.c. case 4.2.1 is explicitly said not to cover. The correct citation is 4.8.10 plus a readable approximant, i.e. Lemma 2.1.)

**What (H⁺-CLASS) costs, compared with joint clearing.** It is a *relativization* obligation of the same species as v3's D.2 remark — the proofs of 4.8.10/4.8.15 build traders *from* the given data as a black box and use nothing about minimality of the feature language — but it carries **no existence obligation**: there is no joint Brouwer fixed point to assume, because A clears alone and H clears against constants. That asymmetry is the whole content of "one-way is cheap".

**A's side needs none of this** (trap 2): $u_n$ is a ramp on a rational combination of A's *own* day-$n$ prices, hence natively an expressible feature of rank $n$ with a poly-time description, and Def. 4.3.2's closing remark blesses the ramp. Half 1 is free.

---

## 3. The gated identity — open problem 13

### 3.1 The `ccee` instantiation, with the $w_{f(n)}$ indexing done honestly

`ccee` **4.12.3** (`main.tex:2068`) reads: *let $f$ be a deferral function, $\overline X$ an e.c. sequence of $[0,1]$-LUVs, and $\overline w$ a $\overline{\mathbb P}$-generable sequence of reals in $[0,1]$; then*
$$\mathbb E_n\big(\ulcorner \enc{X_n}\cdot\enc{w}_{\enc f(\enc n)}\urcorner\big)\;\eqsim_n\;\mathbb E_n\big(\ulcorner \enc{\mathbb E}_{\enc f(\enc n)}(\enc{X_n})\cdot \enc{w}_{\enc f(\enc n)}\urcorner\big).$$

**The indexing (trap 5), spelled out.** $\overline w$ generable means $w_m=\tilde w_m(\overline{\mathbb P})$ with $\tilde w_m\in\mathcal{EF}_m$ — *rank $\le m$*. The weight that appears is $w_{f(n)}$, of rank $\le f(n)$: a **future**-measurable gate. That is the theorem's point (the paper's own example is $w_{f(n)}=\operatorname{Ind}_{\delta_n}(\mathbb E_{f(n)}(X_n)>0.7)$, a gate on the *deferred* expectation). Our quote gate lives at day $n$, so we must supply $\overline w$ as the **pullback of $u$ along $f$**:

$$w_m := \begin{cases} u_{f^{-1}(m)} & m\in\operatorname{im}(f)\\ 0&\text{otherwise,}\end{cases}\qquad\text{so } w_{f(n)}=u_n .$$

*Legality.* By (F-INV) the case split and $f^{-1}(m)$ are poly($m$)-time; under (H⁺-CLASS) reading $a_{f^{-1}(m)}$ is $O(m)$; the resulting feature is a rank-$0$ constant (or, under R2, rank $f^{-1}(m)\le m$); values lie in $[0,1]$. So $\overline w$ is a legal $\overline{\mathbb P}^H$-generable $[0,1]$-sequence. Note this is the *degenerate* end of `ccee`'s range — the theorem permits rank up to $f(n)$ and we use rank $\ll n$ — which is exactly why `ccee` turns out to be more machinery than the job needs (§3.2).

*Type-checking the proof at this instance.* The appendix chain for `ccee` (`app:ccee`, `main.tex:5460`) applies 4.8.10 to combinations carrying the real coefficient $w_{f(n)}$ and evaluated at $\mathbb E_{f(n)}$; those are legal because they are read as the **reindexed** progression $C_m:=\ulcorner X_{f^{-1}(m)}\cdot w_m\urcorner - w_m X_{f^{-1}(m)}$ (rank $\le m$, $\|C_m\|_1\le2$, e.c. by (F-INV)), whose conclusion is then read along $m=f(n)$. The final step is 4.8.13 (`exppolymax`), which converts $\mathbb E_{f(n)}(B_n)\eqsim_n0$ into $\mathbb E_n(B_n)\eqsim_n0$ via $\inf_{m\ge n}\le\mathbb E_{f(n)}\le\sup_{m\ge n}$. All of this survives our instantiation verbatim.

**Conclusion (`ccee` form).**
$$\boxed{\;\mathbb E^H_n\big(\ulcorner X_n\cdot u_n\urcorner\big)\;\eqsim_n\;\mathbb E^H_n\big(\ulcorner Y_n\cdot u_n\urcorner\big)\;}\qquad\textbf{FULL LIMIT, all days.}$$

### 3.2 The cheaper derivation: `cee` + 4.8.10 (no `ccee` needed)

Because $u_n$ is *day-$n$ measurable*, the gate simply factors out of $\mathbb E^H_n$:

1. Every $W\in\mathcal{PC}(\Gamma_H)$ has $W(\ulcorner X_n u_n\urcorner - u_nX_n)=0$ by (Γ-REP-H); the sequence is in $\mathcal{BLCS}(\overline{\mathbb P}^H)$ (coefficients $1$ and $-u_n$, both generable, $\|\cdot\|_1\le2$); so **4.8.10** gives $\mathbb E^H_n(\ulcorner X_nu_n\urcorner)\eqsim_n u_n\,h_n$. (Equivalently **4.8.4** `loe` with $a_n:=u_n$, $b_n:=0$ — legal because market prices and hence $u_n$ are *rational*.)
2. **`cee` 4.12.1** gives $h_n\eqsim_n g_n$ (**FULL LIMIT**); multiplying by $u_n\in[0,1]$ preserves it.
3. **4.8.10** again gives $u_n g_n\eqsim_n\mathbb E^H_n(\ulcorner Y_nu_n\urcorner)$.

Same boxed conclusion, and additionally the *factored* form
$$\mathbb E^H_n(\ulcorner X_n\cdot u_n\urcorner)\;\eqsim_n\;u_n\,h_n,\qquad \mathbb E^H_n(\ulcorner u_n\urcorner)\;\eqsim_n\;u_n .$$

### 3.3 Verdict on open problem 13

**(a) The identity: PROVED modulo named hypotheses (BLCS/DET/Γ-REP-H, H⁺-CLASS).** FULL LIMIT, all days, varying questions, no subsequence anywhere. `ccee` delivers it; so does `cee`+4.8.10, more cheaply. So the "cheapest available improvement" is genuinely available.

**(b) The accounting claim: REFUTED.** [[unbiasedness-theorem-families]] §4.1 says applying `ccee` at the quote gate "removes one of the two limit points". It does not. The two limit points in the `cee` route are *A's* 4.8.15 and *H's* 4.8.15. `ccee` replaces step 1 of that route — which was **`cee`, already a full limit**. The step that `ccee` leaves standing, in the wiki's own words "H's expectation of $Y_n$ against $Y_n$'s realized value", **is** H's 4.8.15, i.e. the same limit point that was there before. Formally:

| route | step 1 | step 2 (H↔truth) | step 3 (A↔truth) | limit points |
|---|---|---|---|---|
| `cee` | `cee` 4.12.1 (FULL LIMIT) | 4.8.15 on H (LIMIT POINT) | 4.8.15 on A (LIMIT POINT) | **2** |
| `ccee` | `ccee` 4.12.3 (FULL LIMIT) | 4.8.15 on H (LIMIT POINT) | 4.8.15 on A (LIMIT POINT) | **2** |

**(c) A third finding.** Because the gate is day-$n$ measurable, §3.2 shows the *conditional* form of the target collapses:
$$\mathbb E^H_n(\ulcorner X_nu_n\urcorner)\gtrsim_n t\,\mathbb E^H_n(\ulcorner u_n\urcorner)\iff \liminf_n\;u_n\big(h_n-t\big)\ge0,$$
i.e. **soft Total Trust at the quote gate is equivalent to per-day dominance on the gate's support** — and, quantifying over all rational $(t,\delta)$ and using v3's compactness argument (its Corollary 2 proof), equivalent to $\liminf_n(h_n-a_n)\ge0$, which is *exactly* v3's Corollary 2. So the target of this note is **as strong as v3's headline conclusion**, and reaching it under one-way visibility would strictly improve on v3. That is the correct calibration for the rest of the document: we are not chasing a weakened notion, we are chasing v3's conclusion with joint clearing deleted.

---

## 4. Half 1, restated on the record

**Theorem T2 (Half 1).** Assume (BLCS-A), (DET-A), (DIV). Then
$$\bar Y_n=\frac{\sum_{i\le n}u_iY_i}{\sum_{i\le n}u_i}\;\ge\;t-o(1)\quad\text{along an infinite set }N_A .$$
**LIMIT POINT.** *Proof.* 4.8.15 (corrected, clause-free) applied to $A$ with $\overline B:=\overline{\ulcorner Y\urcorner}$ and weighting $u$ gives an infinite $N_A$ on which $\bar a_n-\bar Y_n\to0$. The ramp has no false positives, so $u_i>0\Rightarrow a_i>t$, whence $\bar a_n\ge t$ for every $n$. $\square$

Legality of $u$ for A: §2. Nothing else is used — no visibility, no joint clearing, no delay assumption, no computability bound on the coupled construction. Engine kernel-checked (`lean-deference/Staleness.lean`).

Dual gate: with $u^-_n:=\operatorname{Ind}_\delta(a_n<t)$ one gets $\bar Y^{\,u^-}_n\le t+o(1)$ along an infinite set. Every statement below dualizes; only the upper half is written out.

---

## 5. Half 2 — the remaining comparison, and why it does not close

### 5.1 Exact localization

After T1 the only thing standing between us and the target is the H-side bridge
$$\Delta_n \;:=\; \bar h_n-\bar Y_n\;=\;\frac{\sum_{i\le n}u_i\big(\mathbb E^H_i(X_i)-\mathbb E^H_{f(i)}(X_i)\big)}{\sum_{i\le n}u_i}.$$
Note what this object is: **H's own price of $X_i$ at day $i$ against H's own price of $X_i$ at day $f(i)$**, gate-weighted. Truth in the external sense never appears — the "truth" here is a later price. This is why it is tempting to think family D should settle it, and why (§5.2) it does not.

Corrected 4.8.15 applied to $H$ (needs **(MIRROR)**, plus the relativized generability of $u$ from §2) gives: $\Delta_n\to0$ along an infinite set $N_H$ — **LIMIT POINT** — using `cee` to replace $g_i$ by $h_i$.

So the total premise set of the route is:
- **(P1)** $\bar a_n\ge t$ for all $n$; $\bar a_n-\bar Y_n\to0$ on $N_A$. *(A's 4.8.15, LIMIT POINT.)*
- **(P2)** $\Delta_n=\bar h_n-\bar Y_n\to0$ on $N_H$. *(H's 4.8.15 + `cee`, LIMIT POINT.)*
- **(P3)** the gated identity T1. *(FULL LIMIT.)*

and the target is $\limsup_n\bar h_n\ge t$ (recurring form) or $\liminf_n u_n(h_n-t)\ge0$ (per-day form).

### 5.2 Family D: 4.8.12 and 4.8.13

Exact statements (`main.tex:1782`, `main.tex:1794`), for arbitrary $\overline B\in\mathcal{BLCS}$, no fixedness, no convergence hypothesis:

- **4.8.12** $\liminf_n\inf_{m\ge n}\mathbb E_m(B_n)=\liminf_n\mathbb E_\infty(B_n)$; $\limsup_n\sup_{m\ge n}\mathbb E_m(B_n)=\limsup_n\mathbb E_\infty(B_n)$.
- **4.8.13** $\liminf_n\mathbb E_n(B_n)=\liminf_n\sup_{m\ge n}\mathbb E_m(B_n)$; $\limsup_n\mathbb E_n(B_n)=\limsup_n\inf_{m\ge n}\mathbb E_m(B_n)$.

**Lemma 5.1 (what family D gives, and its collapse).** If $\overline B\in\mathcal{BLCS}$ is determined via $\Gamma$ then $\mathbb E_\infty(B_n)=\operatorname{Val}_\Gamma(B_n)$ (Limit Coherence 4.1.2: $\mathbb P_\infty$ is a measure on $\mathcal{PC}(\Gamma)$, on which $B_n$ is constant), and chaining $\inf_{m\ge n}\le\sup_{m\ge n}$ through 4.8.12–4.8.13,
$$\liminf_n\mathbb E_n(B_n)\;\ge\;\liminf_n\operatorname{Val}_\Gamma(B_n),\qquad \limsup_n\mathbb E_n(B_n)\;\le\;\limsup_n\operatorname{Val}_\Gamma(B_n).$$
These are **exactly Expectation Coherence 4.8.11** specialized to determined sequences. So *for our purpose family D contributes nothing beyond 4.8.11.* $\square$

**Why that does not serve.** Instantiate $B_n:=\ulcorner Y_nu_n\urcorner-t\,u_n$ (legal $\mathcal{BLCS}$; $\operatorname{Val}=u_n(Y_n-t)$; $\mathbb E^H_n(B_n)\eqsim_nu_n(h_n-t)$ by T1). Lemma 5.1 yields
$$\liminf_n u_n(h_n-t)\;\ge\;\liminf_n u_n(Y_n-t),\qquad \limsup_n u_n(h_n-t)\;\le\;\limsup_n u_n(Y_n-t).$$
The right-hand side of the first inequality is $\le0$ as soon as the gate switches off infinitely often (each such day contributes $0$), and $\le0$ also whenever a gated day has $Y_n<t$. So the lower bound is vacuous. **Family D is a pointwise envelope theorem; the deficit is an averaged one.** No re-indexing repairs this: family D always compares $\mathbb E_m(B_n)$ for a *fixed* $n$ across $m$, so it cannot produce diagonal averages $\bar h_n$ at all, whose terms are day-$i$ prices for $i$ ranging.

One might try to smuggle the average inside: running-average combinations *are* legal ($B_n:=\Theta_n^{-1}\sum_{i\le n}u_i\ulcorner Y_i\urcorner-\bar h_n$ has rank-$\le n$ coefficients, $\|B_n\|_1\le2$, and is e.c.; note $\mathbb E_n$ is *exactly* linear on LUV-combinations by the $\alpha_m$ device of appendix A.3, so no error accrues). But then $\mathbb E^H_n(B_n)=\Theta_n^{-1}\sum_{i\le n}u_i\mathbb E^H_n(\ulcorner Y_i\urcorner)-\bar h_n$ involves H's **day-$n$** beliefs about *past* targets, and bounding those against H's day-$i$ beliefs is precisely an unbiasedness statement again. Circular.

**Verdict:** family D cannot bound H's gated expectation against realized $Y$ with a full limit or a usable one-sided bound. (For open problem 16 the same collapse is *good* news: Theorem A needs exactly a pointwise envelope, which 4.8.11 supplies — different requirement, different outcome.)

### 5.3 Exhaustive sweep of §4.8, §4.11, §4.12

| # | name | what it gives here | serves Half 2? |
|---|---|---|---|
| 4.8.3 | Expectations Converge | $\mathbb E_\infty(X)$ exists for a **fixed** $X$ | **No** — fixedness is exactly what the varying-question regime removes (it is Theorem A's engine, not this route's) |
| 4.8.4 | Linearity of Expectation | factors rational generable coefficients out of $\mathbb E_n$ | **Used** (T1, §3.2) — a tool, not a bridge |
| 4.8.6 | Expectations of Indicators | $\mathbb E_n(\mathbb 1(\phi_n))\eqsim_n\mathbb P_n(\phi_n)$ | translation only |
| 4.8.10 | Expectation Provability Induction | carries $\Gamma$-provable (in)equalities through $\mathbb E_n$ | **Used** (T1, Lemma 2.1, T4) — a tool |
| 4.8.11 | Expectation Coherence | $\liminf_n\mathbb E_n(B_n)\ge\liminf_n\inf_WW(B_n)$, dually | **No** — pointwise envelope; §5.2 |
| 4.8.12 | Persistence of Expectation Knowledge | with 4.8.13 collapses to 4.8.11 on determined sequences | **No** — §5.2 |
| 4.8.13 | Expectation Preemptive Learning | ditto; also the $\mathbb E_{f(n)}\Rightarrow\mathbb E_n$ transfer used inside `ccee`/`st` | **No** as a bridge; **used** as a tool |
| 4.8.15 | Expectation Recurring Unbiasedness (corrected: no support clause) | the bridge, on any generable divergent weighting | **Yes — but LIMIT POINT.** This is the whole problem |
| 4.8.16 | Expectation Unbiasedness From Feedback (corrected: carries support $\subseteq\operatorname{im}f$ **and** $\operatorname{Val}_\Gamma(B_n)$ computable in $\mathcal O(f(n{+}1))$) | the bridge as a **FULL LIMIT** | **Counts as failure here** — support in $\operatorname{im}f$ is a sparse schedule, and the timing condition additionally demands that H's day-$f(n)$ expectation be computable in $\mathcal O(f(n{+}1))$ time, a bound on the coupled construction that the corpus was pleased to remove. Different route |
| 4.8.17 | Learning Pseudorandom LUV Sequences | **the shape of a closure**: *if* for every $f$-patient generable weighting $w$ one has $\bar Y^{\,w}_n-t\gtrsim_n0$, *then* $h_n-t\gtrsim_n0$ **per day** | **Family C — off limits** (trap 3): its hypothesis is about the environment, and here the environment is exactly what we are trying to conclude about. Worth recording as the *exact* shape a future closure would need: an all-patient-weightings, full-$\liminf$ strengthening of Half 1 |
| 4.11.1 | Introspection | H's beliefs about its own day-$n$ prices | no truth term |
| 4.11.2 | Paradox Resistance | governs the degenerate quote-referencing diagonal | not the main line |
| 4.11.3 | `epr` | $\mathbb P_n(\phi_n)\eqsim_n\mathbb E_n(\ulcorner\mathbb P_n(\phi_n)\urcorner)$ | tool |
| 4.11.4 | `er` | $\mathbb E_n(X_n)\eqsim_n\mathbb E_n(\ulcorner\mathbb E_n(X_n)\urcorner)$ — reindexed, $\mathbb E^H_{f(n)}(\ulcorner Y_n\urcorner)\eqsim_nY_n$ | **used** (H knows $Y_n$ at day $f(n)$) |
| 4.12.1 | `cee` | $h_n\eqsim_ng_n$ | **used**, FULL LIMIT |
| 4.12.2 | `ceu` | propositional `cee` | same content |
| 4.12.3 | `ccee` | gated `cee` at any gate of rank $\le f(n)$ | **used**; strictly more than needed at a rank-$n$ gate (§3) |
| 4.12.4 | `st` | soft TT of H in future-H at a gate on H's **own future price** | **used** (T4); the gate is the wrong one, §7.2 |

Nothing else in §4.8/§4.11/§4.12 mentions both a market's prices and $\operatorname{Val}_\Gamma$ with an averaged conclusion. Families A and B are the only truth-crossing families ([[unbiasedness-theorem-families]] §2, confirmed here by inspection), family A (4.3.3) has no LUV analogue in §4.8, and family B is 4.8.15/4.8.16.

### 5.4 The realized-cash trader, and an exact risk obstruction

The one mechanism that does give a **FULL LIMIT** H-side bridge is v3's realized-cash round trip. Under one-way visibility it is **H-side only**, so it is legal here — v3 needed joint clearing only because *its* gate had an H-price factor that had to be A-generable.

**Theorem 5.2 (patient H-side bridge).** Assume (H⁺-CLASS). Let $\theta$ be an $\mathcal C_{H^+}$-generable divergent weighting that is **$f$-patient** ($\exists C\;\forall n:\sum_{i=n}^{f(n)}\theta_i\le C$). Then
$$\frac{\sum_{i\le n}\theta_i\big(Y_i-\mathbb E^H_i(X_i)\big)}{\sum_{i\le n}\theta_i}\;\longrightarrow\;0\qquad\textbf{(FULL LIMIT).}$$
*Proof.* Trader: on day $i$ buy $\theta_i$ units of the bundle $\alpha_i(X_i)$ (appendix A.3) at its day-$i$ price $\mathbb E^H_i(X_i)$; on day $f(i)$ sell the same bundle at its then price $\mathbb E^{\mathbb P_{f(i)}}_i(X_i)$. Coefficients: $\theta_i$ is rank $\le i\le f(i)$ and, by (F-INV) and dynamic programming (appendix A.2.2), producible in poly time at both days. Each completed round trip contributes **cash** $\theta_i\big(\mathbb E^{\mathbb P_{f(i)}}_i(X_i)-\mathbb E^H_i(X_i)\big)=\theta_i(Y_i-h_i)+\theta_i\varepsilon_i$ with $\sup_{i\ge n}|\varepsilon_i|\to0$ by the Mesh Independence Lemma (appendix E.2), and holds no shares afterwards. At any day $n$ the open positions are $\{i\le n: f(i)>n\}=(f^{-1}(n),n]$, whose plausible value in any world lies in $[-\sum_{(f^{-1}(n),n]}\theta_i,\;+\sum\theta_i]$; by $f$-patience at $m:=f^{-1}(n)$ this window mass is $\le C$. Hence the trader's plausible net worth is bounded below by (accumulated cash) $-C$. If $\sum_i\theta_i(Y_i-h_i)$ were unbounded above the net worth would be bounded below and unbounded above — exploitation of $H$, contradicting the criterion for $\mathcal C_{H^+}$. The mirror trader (sell then buy) bounds it above. So $\sum_{i\le n}\theta_i(Y_i-h_i)$ is **bounded**, and dividing by $\Theta_n\to\infty$ gives the claim. $\square$

**Proposition 5.3 (the risk obstruction — why this cannot be all-days).** (i) For the round-trip trader, uniform boundedness of the open-position mass is *equivalent* to $f$-patience of $\theta$, since the open window at day $n$ is exactly $(f^{-1}(n),n]$ and $f$-patience at $f^{-1}(n)$ is exactly the statement that this window carries mass $\le C$. (ii) If $\theta$ is $f$-patient with constant $C$ then $\Theta_n\le C\cdot k(n)$ where $k(n):=\min\{k:f^{k}(1)\ge n\}$, because $[1,n]$ is covered by the $k(n)$ windows $[f^{j}(1),f^{j+1}(1)]$. For $f(n)=2^n$, $k(n)=\Theta(\log^\ast n)$. So an $f$-patient divergent weighting accumulates mass like $\log^\ast n$: **$f$-iterate-sparse (iterated-$f$ growth), and nowhere near all days.** $\square$

Proposition 5.3 says the sparsity in v3's Theorem 1 ("window-disjoint, $d_{k+1}\ge2^{d_k}$") is not an artifact of that proof: it is *forced* by the budget, for any weighting whatsoever. Combining Theorem 5.2 with T2 on the same patient gate gives, along $N_A$, $\bar h^{\,\theta}_n=\bar Y^{\,\theta}_n+o(1)\ge t-o(1)$: **one** limit point instead of two — which is precisely the sparse route (the other agent's). It is recorded here because it is a genuinely new observation that **v3's Theorem 1 survives the deletion of joint clearing** (the trader is H-side; only the gate had to change), and because it beats 4.8.16 on hypotheses (no $\mathcal O(f(n{+}1))$-computability of $\operatorname{Val}_\Gamma$).

### 5.5 The non-derivability witness

**Proposition 5.4.** The premise set (P1)–(P3) of §5.1 does **not** entail $\limsup_n\bar h_n\ge t$, nor any lower bound on $\bar h_n$ in terms of $t$ whatsoever.

*Witness.* Take $t=\tfrac12$, $\delta=\tfrac1{20}$, and the data
$$a_i\equiv0.6\;(\Rightarrow u_i\equiv1,\ \text{since }0.6>t+\delta),\qquad h_i=g_i\equiv0.4,\qquad Y_i\in\{0,1\}\ \text{in blocks}$$
where the blocks are chosen greedily: emit $1$s until $\bar Y_n\ge0.6-\tfrac1n$, then $0$s until $\bar Y_n\le0.4+\tfrac1n$, and repeat. Since $|\bar Y_{n+1}-\bar Y_n|\le\tfrac1{n+1}$ and each phase moves $\bar Y$ monotonically toward $1$ resp. $0$, both phases terminate, so $\bar Y_n$ comes within $\tfrac1n$ of $0.6$ infinitely often and within $\tfrac1n$ of $0.4$ infinitely often. Then:

- $\bar a_n\equiv0.6\ge t$ ✓ and $\bar a_n-\bar Y_n=0.6-\bar Y_n\to0$ along the $0.6$-times: **(P1)** ✓ with $N_A$ = those times.
- $\bar h_n-\bar Y_n=0.4-\bar Y_n\to0$ along the $0.4$-times: **(P2)** ✓ with $N_H$ = those times.
- $h_n\equiv g_n$, so `cee` and T1 hold identically: **(P3)** ✓.
- Yet $\bar h_n\equiv0.4=t-0.1$ for every $n$: the gated average of H's live credence sits a **fixed margin below $t$, permanently**, and the per-day form fails at every single day. $\square$

$N_A$ and $N_H$ are disjoint, which is the whole content: nothing in the premises forces them to meet. **Consequence:** no rearrangement, no auxiliary bookkeeping, and no additional *ungated* full-limit identity can close the `cee`/`ccee` route in the all-days regime. Any closure must add a premise that is not in the set — which is what §5.4's patience does (sparsity), and what joint clearing does (a single market whose criterion sees both prices).

*Scope, stated precisely (and this matters).* Proposition 5.4 is a statement about **derivability from the cited premises**, at the level of the abstract real-sequence data. It is **not** a proof that the deference conclusion is false for actual coupled logical inductors — that would require exhibiting markets realizing the witness, which is open problem 9's business. The witness does look realizable: H sitting at $0.4$ while its own later credences swing in long correlated blocks is precisely the paper's $\overline{\mathrm{cluster}}$ scenario (main.tex:1155–1163), and A quoting a constant $0.6$ is not exploitable because $D^A_n$ cannot decide $Y_i$ for $i\gtrsim\log n$ — deciding $Y_i$ means running the coupled construction to day $f(i)$ — so the standing-sell trader's *plausible* net worth is unbounded below and no exploitation arises. I rate realizability ~0.6 and non-derivability ~0.95.

### 5.6 Structural argument, and the verdict on open problem 7

**Proposition 5.5 (no two-market theorem).** Every theorem in §4.1–§4.12 is a statement about **one** market $\overline{\mathbb P}$, its own generable weightings, and $\operatorname{Val}_\Gamma$/$\mathcal{PC}(\Gamma)$. A conclusion relating $\overline{\mathbb P}^A$-quantities to $\overline{\mathbb P}^H$-quantities can therefore only be obtained by composing statements each of which compares one market to the shared $\operatorname{Val}_\Gamma$. In the present problem the only shared determined object is $\overline{\ulcorner Y\urcorner}$. Hence any derivation must cross the truth boundary **twice** — once for A, once for H — and each crossing is an application of family A or family B (family D never mentions truth; family C assumes the environment). In the all-days regime, family A has no LUV analogue and family B's all-days member is 4.8.15, whose conclusion is a **LIMIT POINT**. Two limit points, on unrelated subsequences. $\square$

**Where the single application does exist.** Under **joint clearing**, A's weightings may read H's day-$n$ prices; then the violation gate $w_n=\operatorname{Ind}_\delta(a_n>t)\cdot\operatorname{Ind}_\delta(h_n<t-\varepsilon)$ is A-generable, one application of 4.8.15 to A on $w$ together with the H-side realized-cash trader closes everything, and there is only one limit point to manage. **That is exactly v3.** So the honest answer to open problem 7 is: *the single application is precisely the thing joint clearing buys, and buying it is what "$A$ must read $H$" means.* One should stop looking for it under one-way visibility.

**Candidate single applications, checked and rejected.**

| candidate | fails because |
|---|---|
| 4.8.15 on A with $B_n:=\ulcorner Y_n\urcorner-\ulcorner h_n\urcorner$ | conclusion involves $\mathbb E^A_n(\ulcorner h_n\urcorner)$, A's belief about H's *present* price. Bounding that against $a_n$ (A's belief about H's *future* price) is a tower hypothesis about A — assuming the conclusion |
| 4.8.15 on A with $B_n:=\ulcorner h_n\urcorner$ | gives $\bar q_n\approx\bar h_n$ on a subsequence, $q_i:=\mathbb E^A_i(\ulcorner h_i\urcorner)$; still needs $\bar q_n\ge t$, same tower hypothesis |
| 4.8.15 on H with $B_n:=\ulcorner Y_n\urcorner-a_n$ | the constant $a_i$ cancels; identical to (P2) |
| an adaptive weighting that turns off when the deficit is large | such a weighting reads H's prices, hence is **not A-generable** under one-way visibility. Under joint clearing it is legal — and it is v3's Theorem 2 |
| a weighting driven by realized feedback $Y_i$ ($i\le f^{-1}(n)$, legal for H — $Y_i$ is a rank-$f(i)$ expressible feature) | the feedback available by day $n$ covers only indices $\le f^{-1}(n)$, an $O(\log^\ast)$-fraction of the mass; making it a positive fraction is $f$-patience again (Prop. 5.3) |

---

## 6. The strongest honest all-days statements

Throughout: (BLCS-A), (DET-A), (MIRROR), (Γ-REP-H), (H⁺-CLASS), (DIV); $(X_n)$ any e.d. sequence of $[0,1]$-LUVs; $t$ rational, $\delta>0$ rational; $u_n=\operatorname{Ind}_\delta(a_n>t)$.

> **T1 (Gated tower identity). FULL LIMIT, ALL DAYS.**
> $$\mathbb E^H_n\big(\ulcorner X_n\cdot u_n\urcorner\big)\;\eqsim_n\;u_n\,\mathbb E^H_n(X_n)\;\eqsim_n\;u_n\,\mathbb E^H_n\big(\ulcorner Y_n\urcorner\big)\;\eqsim_n\;\mathbb E^H_n\big(\ulcorner Y_n\cdot u_n\urcorner\big).$$
> *(§3; `ccee` 4.12.3 at the pullback weight, or `cee` 4.12.1 + 4.8.10. No subsequence.)*

> **T2 (Half 1: the advertisement is honest about the future human). LIMIT POINT.** There is an infinite $N_A\subseteq\mathbb N$ with $\displaystyle\liminf_{n\in N_A}\Big(\frac{\sum_{i\le n}u_iY_i}{\sum_{i\le n}u_i}-t\Big)\ge0.$ *(§4; 4.8.15 on A. Free — no visibility in either direction.)*

> **T3 (Oscillation Theorem). ALL DAYS, unconditional.** Suppose there are $c>0$ and $N$ with $\bar h_n\le t-c$ for all $n\ge N$ (a *permanent* gated trust deficit of margin $c$). Then
> $$\limsup_n\bar Y_n\;\ge\;t\qquad\text{and}\qquad\liminf_n\bar Y_n\;\le\;t-c,$$
> so the gate-weighted realized future human credence oscillates forever with amplitude $\ge c$. Equivalently, **the following three cannot all hold: (a) the gate has divergent mass; (b) $\bar Y_n$ converges; (c) $\bar h_n\le t-c$ eventually.**
> *Proof.* $\limsup\bar Y_n\ge t$ is T2. On $N_H$ (from (P2)) $\bar Y_n=\bar h_n+o(1)\le t-c+o(1)$, so $\liminf\bar Y_n\le t-c$. $\square$

> **T3′ (Contrapositive — the deference statement that survives). ALL DAYS.** If the gate-weighted realized future human credence $\bar Y_n$ **converges**, then
> $$\lim_n\bar Y_n\;\ge\;t\qquad\text{and}\qquad\limsup_n\;\frac{\sum_{i\le n}u_i\,\mathbb E^H_i(X_i)}{\sum_{i\le n}u_i}\;\ge\;t\quad(\textbf{LIMIT POINT}),$$
> and if moreover $\bar h_n$ converges, then
> $$\lim_n\;\frac{\sum_{i\le n}u_i\,\mathbb E^H_i(X_i)}{\sum_{i\le n}u_i}\;=\;\lim_n\bar Y_n\;\ge\;t\quad(\textbf{FULL LIMIT}),$$
> i.e. **soft Total Trust in unnormalized threshold form, on the gate, over all days**.
> *Proof.* Let $\bar Y_n\to L$. Along $N_A$, $\bar a_n\to L$; since $\bar a_n\ge t$ always, $L\ge t$. Along $N_H$, $\bar h_n\to L$, so $L$ is a limit point of $\bar h_n$ and $\limsup\bar h_n\ge L\ge t$. If $\bar h_n\to L'$ then $L'=L$ by (P2). $\square$
>
> This is the exact analogue of the paper's own proviso for its calibration and unbiasedness theorems: *the conclusion is a genuine limit on subsequences where the frequency of truth converges, and a limit point otherwise.* Here "the frequency of truth" is the gate-weighted realized future credence. It is an **environment condition**, but a plain convergence condition on the target — not a family-C pseudorandomness hypothesis relative to a class, and not a schedule.

> **T3″ (Dual).** With $u^-_n:=\operatorname{Ind}_\delta(a_n<t)$ and the corresponding averages, the mirror statements hold with all inequalities reversed: a permanent gated *over*-trust deficit forces oscillation, and convergence of $\bar Y^{\,u^-}$ gives $\liminf_n\bar h^{\,u^-}_n\le t$, upgrading to a full limit when $\bar h^{\,u^-}$ converges.

**And what is NOT true.** By Proposition 5.4, the unconditional versions — $\limsup_n\bar h_n\ge t$, or "the gated violation weight cannot have weighted average bounded away from $0$", or "trust failures cannot be persistent-in-average" — are **not derivable** from the route's premises. The convergence proviso in T3′ is not a stylistic hedge; deleting it makes the statement unprovable by these means.

---

## 7. Two by-products

### 7.1 The LUV form of Self-Trust (not in the paper)

**Theorem T4.** Let $\overline X$ be an e.c. sequence of $[0,1]$-LUVs, $p$ rational, $\delta>0$ rational, $v_n:=\operatorname{Ind}_\delta\big(\mathbb E^H_{f(n)}(X_n)>p\big)=\operatorname{Ind}_\delta(Y_n>p)$. Then
$$\mathbb E^H_n\big(\ulcorner X_n\cdot v_n\urcorner\big)\;\gtrsim_n\;p\cdot\mathbb E^H_n\big(\ulcorner v_n\urcorner\big)\qquad\textbf{(FULL LIMIT, all days, no extra hypotheses).}$$
*Proof.* $\overline v$ pulled back along $f$ is $\overline{\mathbb P}^H$-generable in $[0,1]$ (it is literally `ccee`'s own motivating example: $\tilde w_m=\operatorname{Ind}_\delta(\mathbb E^{\mathbb P_m}_m(X_{f^{-1}(m)})>p)$, rank $m$, poly-time by (F-INV)). `ccee` 4.12.3 gives $\mathbb E^H_n(\ulcorner X_nv_n\urcorner)\eqsim_n\mathbb E^H_n(\ulcorner \mathbb E^H_{f(n)}(X_n)\cdot v_n\urcorner)$. The ramp has no false positives, so in every $W\in\mathcal{PC}(\Gamma_H)$, $W\big(\ulcorner \mathbb E_{f(n)}(X_n)v_n\urcorner-p\ulcorner v_n\urcorner\big)=v_n(\mathbb E_{f(n)}(X_n)-p)\ge0$; 4.8.10 finishes. $\square$

This is exactly `st` 4.12.4 with LUVs in place of sentences; the paper states only the propositional form. It says: **H already totally trusts its own future self, at full strength, over all days, for free.**

### 7.2 The deficit, localized (verdict on open problem 14)

T4 and the target differ in **one** place — the gate. T4's gate is $\operatorname{Ind}_\delta(Y_n>p)$ (future-H exceeds $p$); the target's gate is $\operatorname{Ind}_\delta(a_n>t)$ (A quotes above $t$). To transport, one needs "on days A quotes above $t$, H's future self exceeds $t$" — with the strength required, *per day*. That statement is Half 1, and Half 1 is an **averaged limit-point** statement (T2), not a per-day one. So `st` + Half 1 does **not** compose under one-way visibility, and the failure is not a direction-of-composition subtlety (the concern recorded at [[unbiasedness-theorem-families]] §4.2) but a grain mismatch: the middle term is known per-day in one premise and only on average in the other. **Verdict on open problem 14: NO under one-way visibility, all days** (~0.8). Under joint clearing the transport is exactly what v3's adaptive trader performs.

This is the cleanest available statement of what the whole problem is: *the human's trust in its own future self is free and total; the entire deference deficit is the cost of moving the gate from the human's future self to the AI's advertisement.*

---

## 8. What dropping joint clearing costs (task 5)

| dimension | full soft TT (target, [[deference-notions]]) | v3 Thm 2 + Cor. 2–4 (joint clearing) | **this note** (one-way, all days) |
|---|---|---|---|
| clearing | — | **joint** (Brouwer construction *assumed*, not cited) | **one-way sequential; no fixed point to construct** |
| visibility | — | A reads H's day-$n$ price | H reads A's ledger only |
| days | all | all | all (no schedule) |
| questions | varying | v3 (A2) states a **fixed** $X$; the argument is question-agnostic | varying, genuinely |
| conclusion grain | per-day $\gtrsim_n$ at every gate ( $\equiv\liminf(h_n-a_n)\ge0$ ) | per-day: $w_n\to0$, $\liminf(h_n-a_n)\ge0$, $\sum_nw_n<\infty$ | **recurring / averaged, and conditional**: T3′ needs $\bar Y_n$ to converge |
| statement about $\mathbb E^H_n(X_n)$, unconditional | yes | yes | **none — provably not derivable** (Prop. 5.4) |
| statement about realized $Y_n$, unconditional | — | — | **yes**: T2, limit point, free |
| gated identity | assumed (the fold) | not needed | **T1, proved, FULL LIMIT** |
| self-trust at the future gate | the `st` instance | — | **T4, proved, FULL LIMIT, free** |
| extra obligations | — | joint Brouwer (**assumed**); D.2 relativization (~0.85); (A4) state-machine expressibility (~0.85) | (H⁺-CLASS) relativization of Def. 4.3.5/4.8.10/4.8.15 to the ledger-augmented class; (MIRROR) |
| limit points consumed | 0 | 1 (A's 4.8.15) | 2, on unrelated subsequences — and that is fatal (Prop. 5.4) |

**Reading of the table.** Dropping joint clearing costs exactly one thing, and it is a big one: the ability to build a gate that reads *both* prices, which is what lets a single unbiasedness application serve both halves. What it buys is the deletion of an assumed Brouwer construction and of two flagged obligations. The rest of the table — T1, T2, T4 — is unaffected: those are free in both regimes. The per-day → recurring degradation and the appearance of the convergence proviso are not bookkeeping losses; they are the precise price of the missing gate.

---

## 9. Final statements, hypotheses, verdicts, status

### (a) Final theorem statements, with honest quantifiers

For **every** e.d. sequence $(X_n)$ of $[0,1]$-LUVs of H's language, **every** rational $t\in[0,1]$ and rational $\delta>0$, writing $Y_n=\mathbb E^H_{f(n)}(X_n)$, $a_n=\mathbb E^A_n(\ulcorner Y_n\urcorner)$, $u_n=\operatorname{Ind}_\delta(a_n>t)$, $\bar x_n=\frac{\sum_{i\le n}u_ix_i}{\sum_{i\le n}u_i}$, and assuming (BLCS-A), (DET-A), (MIRROR), (Γ-REP-H), (H⁺-CLASS), (DIV):

1. **T1** — $\mathbb E^H_n(\ulcorner X_n u_n\urcorner)\eqsim_n\mathbb E^H_n(\ulcorner Y_nu_n\urcorner)$. **FULL LIMIT, all days.**
2. **T2** — $\exists$ infinite $N_A$: $\liminf_{n\in N_A}(\bar Y_n-t)\ge0$. **LIMIT POINT.** (Uses only (BLCS-A), (DET-A), (DIV).)
3. **T3** — for every $c>0$: not both [$\bar h_n\le t-c$ for all large $n$] and [$\bar Y_n$ converges]. Equivalently, a permanent gated deficit of margin $c$ forces $\limsup_n\bar Y_n-\liminf_n\bar Y_n\ge c$. **ALL DAYS, unconditional.**
4. **T3′** — if $\bar Y_n$ converges then $\lim_n\bar Y_n\ge t$ and $\limsup_n\bar h_n\ge t$ (**LIMIT POINT**); if in addition $\bar h_n$ converges then $\lim_n\bar h_n\ge t$, i.e. $\mathbb E^H_n(X_n\cdot u_n)\gtrsim_nt\,\mathbb E^H_n(u_n)$ in gate-average (**FULL LIMIT**). Dual cut: T3″.
5. **T4** — $\mathbb E^H_n(\ulcorner X_n\operatorname{Ind}_\delta(Y_n>p)\urcorner)\gtrsim_np\,\mathbb E^H_n(\ulcorner \operatorname{Ind}_\delta(Y_n>p)\urcorner)$ for every rational $p$. **FULL LIMIT, all days, no hypotheses beyond the LI setting.**
6. **Prop. 5.4** — the premises of the route do not entail the unconditional form of T3′; explicit witness.
7. **Prop. 5.3** — any weighting for which the round-trip bridge has bounded risk is $f$-patient, hence accumulates mass $O(\log^\ast n)$ for $f(n)=2^n$.
8. **Thm 5.2** — on any $f$-patient $\mathcal C_{H^+}$-generable divergent gate the H-side bridge is a **FULL LIMIT**; combined with T2, one limit point remains. (v3's Theorem 1, with joint clearing deleted.)

### (b) Named hypotheses

(BLCS-A), (DET-A) — standing, from the problem statement. **(MIRROR)** — $\Gamma_H$-determinacy and $\mathcal{BLCS}(\overline{\mathbb P}^H)$-membership of $\overline{\ulcorner Y\urcorner}$. Used only where 4.8.15 is applied to H (i.e. (P2), T3, T3′). **T1, T2, T4 do not use it.** **(Γ-REP-H)** — $\Gamma_H$ represents A's computation, so quote constants are pinned in every $\Gamma_H$-consistent world. Used in T1. **(H⁺-CLASS)** — H's trader class and H's generability notion are relativized to poly-time-with-the-published-ledger, and H satisfies the criterion against that class. Used everywhere on H's side; **unavoidable** (§2). **(DIV)** — the gate has divergent mass. (F-INV) is a lemma, not a hypothesis.

Not assumed anywhere: joint clearing; any Brouwer construction beyond the paper's; any bound on the coupled construction's runtime; any support/schedule restriction; any environment/pseudorandomness hypothesis (family C is untouched).

### (c) Verdicts on the open problems

- **Item 13** (does `ccee` remove one of the two limit points?) — **the identity: YES and now PROVED** (T1, full limit, all days); **the accounting claim: REFUTED** — the count stays at two, because the step `ccee` upgrades was `cee`, already a full limit. Additional finding: `ccee` is not needed; `cee`+4.8.10 suffices, since the quote gate is day-$n$ measurable and `ccee`'s $w_{f(n)}$ is strictly more general. **Confidence 0.88.** The wiki entry and open-problems item 13 should both be rewritten.
- **Item 7** (a single application yielding both halves) — **NO under one-way visibility.** Structural (Prop. 5.5), non-derivable (Prop. 5.4), and budget-obstructed (Prop. 5.3). The single application exists exactly under joint clearing and *is* v3. **Confidence 0.85.**
- **Item 7, sub-question** (can family D remove the remaining limit point?) — **NO.** 4.8.12+4.8.13 collapse to 4.8.11 on determined sequences and give only pointwise envelopes, vacuous on a switching gate. **Confidence 0.90.**
- **Item 14** (`st` + Half 1 composes) — **NO under one-way visibility, all days**; the obstruction is a grain mismatch, not a direction mismatch. **Confidence 0.8.**
- **Item 16** (4.8.12 replaces convergence in Theorem A) — **not settled here**, but the collapse of §5.2 is relevant and probably favourable: Theorem A wants a *pointwise* envelope, which is exactly 4.8.11's content. Recommend re-stating item 16 as "does 4.8.11 suffice?", which is a cheaper question.
- **Item 12** (does the joint Brouwer construction exist?) — **raised in priority by this note**, not lowered. §5.6 shows joint clearing is not one route among three but the *only* route to the all-days per-day conclusion; if its construction fails, that conclusion has no proof at all.

### (d) Status per corpus convention

- **T1, T4, Lemma 2.1, Thm 5.2, Prop. 5.3, Prop. 5.5** — **PROVED modulo named hypotheses.** (T2 is PROVED modulo (BLCS-A)/(DET-A) with its engine KERNEL-CHECKED in `lean-deference/Staleness.lean`; nothing new here is in Lean.)
- **T3, T3′, T3″** — **PROVED modulo named hypotheses** (they are two-line consequences of T2 + (P2) + T1).
- **Prop. 5.4** — **PROVED (prose)**, as a non-derivability statement about the abstract data. Its *realizability* by coupled inductors is **CONJECTURED (~0.6)** and would, if established, be a genuine impossibility result (open problem 9's family).
- **The `cee`/`ccee` route as an all-days deference argument** — **REFUTED**, with Prop. 5.4 as the counterexample. Its wiki status CONJECTURED (~0.6) should be replaced by: *identity half PROVED; combination half REFUTED; surviving content T3/T3′.*
- **The wiki's ledger gate $\tilde u_n=\operatorname{Ind}_\delta(\mathbb P^H_n(\ulcorner a_n>t\urcorner)>\tfrac12)$** — **DEFECTIVE as written** (converges to the hard indicator, so it does not match A's ramp) and its cited justification (Provability Induction 4.2.1 on a non-e.c. truth pattern) is **wrong**. Repairs: §2 (R1) or (R2)+Lemma 2.1.

### (e) The three things a skeptic should attack first

1. **(H⁺-CLASS), and the claim that it is unavoidable and cheap.** Everything on H's side — T1, (P2), Lemma 2.1, Thm 5.2 — rests on H satisfying the criterion against ledger-reading traders *and* on Def. 4.3.5/4.8.10/4.8.15 relativizing to that class. The relativization is the same species as v3's D.2 obligation and I have argued (not proved) that the appendix proofs treat the weighting as a black box. If Def. 4.3.5 must stay strictly plain-$\mathrm P$, then repair (R2) is forced, and (R2) needs Lemma 2.1, which itself needs the relativized 4.8.10. **This is the single load-bearing joint of the whole note.**
2. **Proposition 5.4's status as a *refutation of the route*.** It is a non-derivability statement, not an impossibility theorem. A skeptic should press on whether some *further free* LI theorem about H — not in the premise set (P1)–(P3), and not in the §5.3 sweep — constrains the witness data. My sweep is exhaustive over §4.8/§4.11/§4.12 but not over §4.1–§4.7 (I checked only that those families are propositional/non-averaged or family C). A second reader should re-run the sweep over §4.5 (the affine level) in particular.
3. **The (MIRROR) hypothesis under coupling.** It asks $\Gamma_H$ to determine H's *own* day-$f(n)$ expectation inside a system whose day-$\le f(n)$ history includes A's quotes about that very quantity. I argued in §1 that the composition is well-founded under one-way clearing, which is exactly the point at which the corresponding claim would fail under joint clearing. A skeptic should check that the determinacy really is the *logical* condition of Def. 4.8.14 and not a disguised computability claim — and, separately, that 4.8.15 applied to H against $\operatorname{Val}_{\Gamma_H}$ of a quantity H itself produces is not degenerate.

## Related

- [[faithful-acceleration-result]] §4.3 — the `cee` route this note evaluates (status now to be revised)
- [[unbiasedness-theorem-families]] §4.1, §6 — the `ccee` conjecture (refuted as accounting) and the ledger gate (defective as written)
- [[li-paper-erratum]] — the corrected 4.8.15/4.8.16 used throughout
- [[joint-clearing-and-trader-class]] — what joint clearing buys; §5.6 sharpens this to "the only route to the per-day conclusion"
- [[open-problems]] items 7, 9, 12, 13, 14, 16
- [[fa-positive-results-corrected-v3]] — Theorems 1–2, Corollaries 2–4, compared in §8
