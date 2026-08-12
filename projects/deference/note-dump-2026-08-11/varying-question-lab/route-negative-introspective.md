# The introspective route to a non-paradoxical failure of averaged trust — and why it does not exist

*Claude, 2026-07-30. **REVISED the same day, after adversarial verification; the verdict is reversed.** The first draft of this file asserted a counterexample (Theorem N) at ~0.70. A leak found in review, which I then strengthened into a simpler and more general form, **refutes it**. What replaces it is an obstruction that looks structural, one new hypothesis-free lemma about the forecaster, and a set of design kills that were correct the first time. Setting: two logical inductors over their own deductive processes, **one-way visibility** — $A$ never reads $H$'s prices; $H$ reads $A$'s quote ledger. Sequential clearing, no joint fixed point. Conventions: [[conventions-and-status-labels]]. Numbering per [[li-paper-erratum]] §3.*

---

## 0. Lead: what this delivers now

The target was a **non-paradoxical** failure of soft Total Trust — Abram's msg-44 request: *"cases where even the on-average sense of trust that avoids paradoxes must fail."* Not the quote-referencing diagonal, where the theorem holds vacuously; a genuine environment in which both agents satisfy their criteria by citation, every question is decided, nobody is Dutch-booked, and trust fails anyway.

**I did not get it, and I now believe the reason is structural rather than technical.** The deliverable is therefore the obstruction, stated precisely, plus the pieces that survive:

> **Finding 1 (the new lemma, hypothesis-free).** **Expectation Preemptive Learning (4.8.13) applied to $A$** gives: for *every* efficiently computable set $E$ of days on which the realized target $Y_n$ converges to a value $c$, the quote satisfies $a_n \to c$ along $E$. No pseudorandomness hypothesis, no visibility, no simulation-cost conjecture — only the standing $\mathcal{BLCS}$/determinacy assumption. Call this **Lemma P**. It is a *strictly stronger, pointwise, full-limit* companion to Half 1 on e.c. gates, and it belongs in [[unbiasedness-theorem-families]] §3's option table, correcting that page's sorting result (which places family D on Half 2's side and says it "cannot serve Half 1 at all, since it never mentions truth" — for **determined** targets it can, because there the limit expectation *is* the truth).

> **Finding 2 (the obstruction).** The only rate-free way to certify that $H$'s market has separated on a handle *by an efficiently computable day* is **Preemptive Learning (4.2.4) on a schedule that revisits a fixed sentence cofinally** — and every such schedule hands $A$ an e.c. day-set on which $Y$ converges, so Lemma P closes the gate on exactly the days where $H$'s response was forced. **The straddle engine is symmetric between the two markets.** Forcing $H$ and hiding from $A$ are not merely in tension (that was the refuted predecessor's problem); on this route they are the *same theorem applied twice*.

> **Finding 3 (the revisiting leak, as a named negative result).** *Revisiting leaks through **any** decidable family, shared or not, at any patience — and it needs neither the forecaster's prices, nor its deductive process, nor any scheduling cleverness: a single hard-coded index suffices.* Any family-C pseudorandomness hypothesis about a **revisited** value sequence is false, because a weighting that hard-codes one index is efficiently computable, is patient if made sparse, and is divergent *precisely because of* the revisiting. This kills my (NH-2) outright and, I expect, kills family-C hypotheses in any future revisiting construction.

> **Finding 4 (the direction of surprise is backwards — retained from the first draft).** A failure driven by *the human being surprised* — §4 of `delay-and-visibility`, and the original task framing — cannot be built on the one-way channel at all: by `ceu` (4.12.2) the human's present credence already equals its own forecast of its future credence, the very object $A$ forecasts, on no better information about $H$. Any write-up leading with "the human lags" describes an environment that does not exist.

Three design kills (§3) survive unchanged and are worth keeping: the liar-like $\theta_k$ dies on *forcing*, not on paradox-disqualification; the pseudorandom-question design dies on margin; and the "decide it mid-block" design dies twice, the second time on a **hard impossibility** — the §5.5 proposition *Uncomputable Convergence Rates* (`main.tex:2680`) proves no efficiently computable schedule can ever be certified late enough for a price to have resolved.

**Net effect on the corpus.** [[open-problems]] item 9 ("a non-paradoxical cross-process impossibility", ~0.45) should go **down**, not up — **~0.20** for the introspective route specifically, ~0.3 overall. Correspondingly, the *per-day* form of the positive result on the one-way channel — which the first draft claimed to refute — should go **up**: Lemma P is a new, free tool pointing that way, and it is a *full limit*, which is exactly the currency open problem 7 is short of.

---

## 1. Setting and notation

Language of $\mathrm{PA}$; theories $\Gamma_H,\Gamma_A$ as declared per variant. $H\dashv\mathcal C_H$ over $D_H$, $A\dashv\mathcal C_A$ over $D_A$, $\mathcal C_H\subseteq\mathcal C_A$. **Baseline:** $\mathcal C_H=\mathcal C_A=\mathcal{EC}$ and both agents are literally $\mathrm{LIA}(\cdot)$ (Definition 5.4.1), so both criteria hold by literal citation of `thm:lia`.

**One-way channel.** $D_A$ contains no sentence recording any price of $H$; $D_H$ contains threshold atoms for $A$'s quotes $a_m$, $m<n$. Consequence: **$A$'s market does not depend on $H$ at all**, the system clears sequentially, and no joint Brouwer argument is needed anywhere (open problem 12 does not arise).

Questions: e.d. $(X_n)$; lookahead $f(n):=2^n$; target $Y_n:=\mathbb E^H_{f(n)}(X_n)$; quote $a_n:=\mathbb E^A_n(\ulcorner Y_n\urcorner)$.

**Soft Total Trust**, upper cut, unnormalized threshold form:
$$\forall\,\text{e.d. }(X_n)\ \forall t\in\mathbb Q\ \forall\delta>0:\qquad \mathbb E^H_n(X_n\cdot u_n)\ \gtrsim_n\ t\cdot\mathbb E^H_n(u_n),\qquad u_n:=\operatorname{Ind}_\delta(a_n>t).$$
$\gtrsim_n$ is $\liminf_n(\cdot)\ge0$: **per-day**, so a fixed-margin deficit infinitely often refutes it. Violation weight $w_n:=\operatorname{Ind}_\delta(a_n>t)\cdot\operatorname{Ind}_\delta(\mathbb E^H_n(X_n)<t-\varepsilon)$.

$\operatorname{Ind}_\delta$ is Definition 4.3.2: $0$ if $x\le y$, $(x-y)/\delta$ on $(y,y+\delta]$, $1$ if $x>y+\delta$. **No false positives** — used throughout.

**Standing assumption (NH-4).** $\overline{\ulcorner Y\urcorner}\in\mathcal{BLCS}$ and is determined via $\Gamma_A$. Discharged in every variant below by $H$'s market being a computable function and $\Gamma_A\supseteq\mathrm{PA}$ representing computations. **This is the only input Lemma P needs**, which is why Lemma P is so hard to escape.

---

## 2. Design constraints, and one correction to the refutation's diagnosis

`delay-and-visibility` §3's surviving diagnosis — *"the criterion forces a price to respond only to what an efficiently computable handle can select"* — is true of selection-based forcing (Provability Induction 4.2.1, the unbiasedness family, family C) and **false as a general statement**. Two theorems force prices with no handle at all:

- **Convergence (4.1.1) + Limit Coherence (4.1.2):** for each *fixed* decidable $\varphi$, $\mathbb P_m(\varphi)\to\operatorname{Val}(\varphi)$; likewise $\mathbb E_m(B)\to\operatorname{Val}(B)$ for determined $B$ (4.8.3 + limit coherence). No selection. **No rate** — and this is a theorem, not a gap: the §5.5 proposition *Uncomputable Convergence Rates* shows any function bounding the time to reach $1-\varepsilon$ on provable sentences is uncomputable.
- **Preemptive Learning (4.2.4, and its expectation form 4.8.13):** converts "eventually" into "timely, on the diagonal", again with no handle.

This correction is what made the first draft's construction possible. **It is also what destroys it**, because — and this is the step the first draft missed — the correction applies *symmetrically to $A$*. §7.

Constraints carried forward:

- **(C1) Forcing** must be discharged by an explicit trader with expressible-feature coefficients over the market's **own** prices, or by a rate-free theorem. Family C builds environments; it never extracts guarantees.
- **(C2) Hiding** must be structural in the feature algebra: Definition 3.4.3 builds expressible features from *the market's own* price features, rationals, $+,\times,\max$, safe reciprocal — no primitive names another market's prices.
- **(C3) No generator wedge**: nothing may need $A$'s generators to fail at a computation $H$'s generators can do at the same day index.

---

## 3. The three candidate straddle designs — all three dead, and the kills stand

### 3.1 (a) $\theta_k$ liar-like — DEAD on forcing, not on paradox

Take $\Gamma_H\vdash\theta_k\leftrightarrow(\mathbb P^H_{m_k}(\theta_k)<\tfrac12)$. Paradox Resistance (4.11.2) gives $\mathbb P^H_{m_k}(\theta_k)\to\tfrac12$ and (paper's remark, `main.tex:2005`) truth frequency with a limit point at $\tfrac12$ — the straddle *and* unpredictability to everyone. Worthless nonetheless:

**Claim.** For every e.c. sequence of positive rationals $\eta_k\to0$, $\big|\mathbb P^H_{m_k}(\chi_{m_k})-\tfrac12\big|\le2\eta_k$ for all but finitely many $k$. *Proof.* Otherwise the trader buying $\operatorname{Ind}_{\eta_k}(\tfrac12-\eta_k>\mathbb P^H_{m_k}(\chi_{m_k}))$ shares (positive only when the price is below $\tfrac12-\eta_k$, hence only when $\chi$ is true) and selling the mirror image above banks $\ge\tfrac12-\eta_k$ per unit once $D_H$ decides, with holdings bounded below: exploitation. $\square$

So Introspection (4.11.1), whose hypothesis is that the price lies in $(a_n+\delta_n,b_n-\delta_n)$ **with a margin**, has nothing to bite on, and neither does any $\operatorname{Ind}$-ramp trader. **General principle:** any device that *pins* the price at the threshold buys unpredictability by destroying the margin the forcing needs; a usable straddle must have the price *cross* with a margin, never *sit* on it.

(The disqualification question — is $\theta_k$-referencing-$H$'s-own-price "paradoxical" in the sense `fa-scope-resolution` excludes? — never has to be answered. My answer would have been *no*: the excluded stratum is the **quote**-referencing diagonal, where the quote is pinned and the gate degenerate; $\theta_k$ referencing $H$'s own price leaves $A$'s quote a live object and $X_k$ a decided question. But it is moot.)

### 3.2 (b) $\theta_k$ pseudorandom for $\mathcal C_H$ — DEAD as a question family

4.4.5 puts the price *at the base rate*: at $\tfrac12$ that is §3.1's knife edge; off $\tfrac12$ there is no straddle; and a *varied* ($\overline{\mathbb P}^H$-generable) target is, at the root of its recursion, an e.c. object, hence available to $A$'s generators too — (C2) fails. Family C survives only as a source of hardness for the environment, and §6 shows that even that use is unsafe under revisiting.

### 3.3 (c) $\theta_k$ decided by $D_H$ mid-block — DEAD twice, the second time by a hard impossibility

1. **No selection.** $D_H$ deciding $\theta_k$ does not move $\mathbb P^H_n(\theta_k)$: traders read *prices*, not $D$ (Definitions 3.4.3, 3.5.1). This is the refutation's diagnosis verbatim and is not repaired by moving which sentence is hard.
2. **No certifiable schedule.** The repair "make $m_k$ late enough that the price has resolved" cannot be executed: $(X_k)$ e.d. forces $m_k$ e.c., and by the §5.5 proposition **no computable function bounds any logical inductor's convergence time on provable sentences**. This is the most useful single fact I found while checking §4's sketch: it kills an entire family of would-be constructions, permanently, for every inductor and by any argument.

**The only escape from (2) is to stop naming the day** and let Preemptive Learning name it — which requires revisiting, which §6–§7 show is fatal.

### 3.4 The surprise is pointing the wrong way (retained; independent of everything below)

Suppose the deficit is to come from $H$'s day-$n$ ignorance of something $A$ knows.

- **(i) $A$'s information is $\overline{\mathbb P}^A$-generable or e.c.** Then it is *in the quote*. $H$ reads the ledger, so $\ulcorner a_n>t\urcorner$ is a decided atom of $D_H$ and $H$'s traders can select the flagged days by a legal feature of $H$'s own prices; a trader that buys $X_n$ on flagged days and unwinds at $f(n)$ collects realized cash whenever $A$ is right, so $H$'s credence is forced up. (This is the `cee` route working. Corrected citation for the ledger step: §10.3.)
- **(ii) $A$'s information is not $A$-generable.** Then the quote cannot carry it either, and by **`ceu` (4.12.2)** $\mathbb P^H_n(\varphi_n)\eqsim_n\mathbb E^H_n(\ulcorner\mathbb P^H_{f(n)}(\varphi_n)\urcorner)$: $H$'s present credence already equals its own forecast of its future credence — exactly what $A$ forecasts, on no better information about $H$.

Checked concretely: the lagging variant $X_n:=\ulcorner\mathbb P^H_{h(n)}(\psi_{h(n)})>\tfrac14\urcorner$ with $n<h(n)<f(n)$ gives $\mathbb E^H_n(X_n)\approx a_n$ — human and forecaster identically ignorant, zero deficit. **The driver would have to be the human's private knowledge.** §7–§8 show the human cannot have any that is simultaneously forced and hidden.

---

## 4. The construction (specified in full, because its failure is the result)

### 4.1 Auxiliary hard family
$$\pi_k:=\ulcorner\text{the }\operatorname{Ack}(k,k)\text{-th binary digit of }\pi\text{ is }1\urcorner,\qquad \tau_k:=\operatorname{Val}_{\mathrm{PA}}(\pi_k)\in\{0,1\}.$$
e.c. as a sequence of *formulas* (the value is not computed); each $\mathrm{PA}$-decidable. The paper's own example and its own hedge.

### 4.2 The revisiting probe schedule
Fix an e.c. $\kappa:\mathbb N^+\to\mathbb N^+$, surjective with **infinite fibres** and unbounded gaps — the round-robin enumeration $1;\,1,2;\,1,2,3;\dots$, computable in $O(j)$. Put $\psi_j:=\pi_{\kappa(j)}$.

### 4.3 The questions
$g(n):=\max(1,\lfloor n/2\rfloor)$ (e.c., $g(n)<n$ for $n\ge2$, $g(2j)=j$); threshold $c:=\tfrac14$; for $n\ge2$,
$$\boxed{\ X_n:=\ulcorner\,\mathbb P^H_{g(n)}\big(\psi_{g(n)}\big)>\tfrac14\,\urcorner\ },\qquad \sigma_n:=\operatorname{Val}_{\mathrm{PA}}(X_n)\in\{0,1\}.$$
**e.d. ✔** fixed template plus poly-size numerals $g(n),\kappa(g(n))$ and the (fixed) index of the program computing $H$'s market. **Decidable ✔** $H$'s market is a computable function, so $X_n$ is a claim about a terminating computation; hence also $\ulcorner Y_n\urcorner$ is determined via $\Gamma_A$ (NH-4 discharged), with no bound needed on how long the coupled construction takes to run. Read as $\{0,1\}$-LUVs via 4.8.6.

### 4.4 Deductive processes and well-foundedness
$$D_H^n:=\{\mathrm{PA}\text{-theorems of}\le n\text{ characters}\}\cup\{\text{decided value of }X_m:2\le m\le n\}\cup\{\text{quote atoms for }a_m:m<n\},$$
$$D_A^n:=\{\mathrm{PA}\text{-theorems of}\le n\text{ characters}\}.$$
Both nested, finite, computable, consistent, $\mathrm{PA}$-complete — legal deductive processes (Definition 3.2.1), so `thm:lia` applies to each. Nothing is implemented in a modified trader class. **Well-foundedness:** $\mathrm{LIA}_n$ depends only on $D^{\le n}$ (through $\mathrm{TradingFirm}^D_n$, whose $\mathrm{Budgeter}^D$ reads $\mathrm{PC}(D_m)$, $m\le n$ — `main.tex:2350`) and on $\mathrm{LIA}_{\le n-1}$; $D_H^n$ needs $\mathbb P^H_{g(m)}$ with $g(m)<m\le n$. Strong recursion on $n$; Kleene's recursion theorem supplies the single index that $X_n$'s template names.

**Ledger hygiene.** $\sigma_n$ depends indirectly on $a_m$ for $m<g(n)$. Not a quote-referencing diagonal: $X_n$ mentions neither $a_n$ nor $A$, and its truth is not defined to punish any quote. And $A$ knows its own quotes, so this channel can only *add* information on $A$'s side.

### 4.5 Parameters
$\delta_0:=\tfrac1{16}$ (handle width); $t:=\tfrac16$, $\delta:=\tfrac1{24}$, $\varepsilon:=\tfrac1{12}$; intended quote floor $\bar q:=\tfrac13$.
$$\lambda_n:=\operatorname{Ind}_{\delta_0}\!\big(\mathbb P^H_{g(n)}(\psi_{g(n)})>\tfrac14+\tfrac1{16}\big),\qquad \mu_n:=\operatorname{Ind}_{\delta_0}\!\big(\mathbb P^H_{g(n)}(\psi_{g(n)})<\tfrac14-\tfrac1{16}\big).$$
By no-false-positives: $\lambda_n>0\Rightarrow\sigma_n=1$; $\mu_n>0\Rightarrow\sigma_n=0$; $\lambda_n\mu_n=0$; $\lambda_n=1$ iff the probe price exceeds $\tfrac38$; $\mu_n=1$ iff it is below $\tfrac18$. Both are expressible features of $H$'s **own** market of rank $g(n)\le n$ (Definition 4.3.2's closing remark), describable in $\mathrm{poly}(n)$: **$\mathcal C_H$-legal.**

---

## 5. What survives: two forced facts, both intact

### 5.1 Lemma F (introspective response) — explicit trader, no hypotheses

> **Lemma F.** $\displaystyle\sum_n\Big[\lambda_n\big(1-\mathbb P^H_n(X_n)\big)+\mu_n\,\mathbb P^H_n(X_n)\Big]<\infty$; in particular both terms $\to0$.

*Proof.* Let $T_n:=(\lambda_n-\mu_n)\cdot\big(X_n-\mathbb P_n(X_n)\big)$, $\mathcal C_H$-legal by §4.5 (its coefficients are rank-$g(n)$, hence constants at the day-$n$ fixed point; no continuity subtlety arises, and none is needed since they are continuous anyway). $D_H^n$ decides $X_n$, so every $W\in\mathrm{PC}(D_H^m)$ with $m\ge n$ assigns $W(X_n)=\sigma_n$ ($D$ nested). By no-false-positives,
$$W\Big(\sum_{i\le N}T_i\Big)=\sum_{i\le N}\Big[\lambda_i\big(1-\mathbb P^H_i(X_i)\big)+\mu_i\,\mathbb P^H_i(X_i)\Big]\ \ge\ 0$$
for all $N$ and all $W\in\mathrm{PC}(D_H^N)$: bounded below by $0$, unbounded above if the sum diverges. That is exploitation (Definition 3.6.1), so the sum converges. $\square$

Applied at the lookahead — pad $\widehat X_m:=X_{f^{-1}(m)}$ on $\operatorname{im}f$ and $\ulcorner0{=}0\urcorner$ off it; $f(n)=2^n$ makes $f^{-1}$ e.c. — this gives $\lambda_n(1-Y_n)\to0$ and $\mu_nY_n\to0$.

**Lemma F is the one clean gain of the whole exercise, and it is reusable.** It forces an inductor's credence in a question *about its own settled prices* with a two-line trader, because Definition 3.4.3 hands a trader its own market's prices as **arguments** rather than asking it to compute them. This is what `delay-and-visibility` §4 wanted from Introspection 4.11.1 and did not get: 4.11.1 is a *same-day* statement carrying a margin hypothesis and does not reach a day-$n$ belief about a day-$g(n)$ price; `epr` 4.11.3 is about expectations of prices, not threshold sentences. §4's "forced for free, a citation not a construction" is wrong as stated and right in substance — the citation has to be replaced by this trader.

### 5.2 Lemma S (the straddle) — Preemptive Learning does it, with no design at all

> **Lemma S.** $\liminf_j\mathbb P^H_j(\psi_j)=0$ and $\limsup_j\mathbb P^H_j(\psi_j)=1$; hence $\mu_n=1$ for infinitely many $n$ and $\lambda_n=1$ for infinitely many $n$.

*Proof.* By (NH-1) there are $k_0,k_1$ with $\tau_{k_0}=0,\tau_{k_1}=1$: if all but finitely many $\tau_k$ agreed, the tail of $(\pi_k)_k$ would be an e.c. sequence of theorems (or of refutations) and Provability Induction would contradict the frequency clause of (NH-1) — which is stated for the **unrevisited** index sequence, see §6.4. Fix $\epsilon>0$. $\pi_{k_0}$ is $\mathrm{PA}$-decidable and false, so $\mathbb P^H_m(\pi_{k_0})\to0$ by Convergence (4.1.1) with Limit Coherence (4.1.2). Choose $N_\epsilon$ with $\mathbb P^H_m(\pi_{k_0})<\epsilon$ for all $m\ge N_\epsilon$; then $\sup_{m\ge j}\mathbb P^H_m(\pi_{k_0})\le\epsilon$ for every $j\ge N_\epsilon$. Since $\kappa^{-1}(k_0)$ is infinite, infinitely many diagonal indices $j$ satisfy $\sup_{m\ge j}\mathbb P^H_m(\psi_j)\le\epsilon$. Hence $\liminf_j\sup_{m\ge j}\mathbb P^H_m(\psi_j)=0$, and **Preemptive Learning (4.2.4)** gives $\liminf_j\mathbb P^H_j(\psi_j)=0$. Dually for the $\limsup$ using $k_1$. Finally $g(2j)=j$ transfers both to the designated days. $\square$

**Revisiting is not a convenience here; it is necessary.** To make $\sup_{m\ge j}\mathbb P^H_m(\psi_j)$ small at infinitely many diagonal indices, $\psi_j$ must have *already converged* by day $j$ for infinitely many $j$. We cannot name such $j$ (§3.3, via §5.5), so the only way to guarantee infinitely many is to have each sentence reappear cofinally. Schedules in which each sentence appears only finitely often — including long consecutive blocks with growing lengths — reduce to the uncertifiable case, since $\sup_{m\ge j}$ ranges over *all* later days and picks up the pre-convergence values whenever convergence happens after $j$. **Hold this thought; §7 turns it against us.**

---

## 6. The leak: (NH-2) is false, and no carrier repair fixes it

The first draft's opacity hypothesis was:

> **(NH-2), as it stood.** There is a deferral $f_A$ such that for every $\overline{\mathbb P}^A$-generable $f_A$-patient divergent weighting $\overline v$,
> $$\frac{\sum_{i\le n}v_i\big(\operatorname{Val}_{\Gamma_A}(\ulcorner Y_i\urcorner)-\tfrac13\big)}{\sum_{i\le n}v_i}\ \gtrsim_n\ 0,$$
> with the intended conclusion $a_n\gtrsim_n\tfrac13$ by 4.8.17 applied to $B_n:=\ulcorner Y_n\urcorner-\tfrac13$.

**It is false.**

### 6.1 The reviewer's leak: verified correct, with one caveat

$$v_n:=\operatorname{Ind}_{1/16}\big(\mathbb P^A_n(\pi_{\kappa(g(n))})<\tfrac18\big)\cdot\mathbb 1[n\in E],\qquad E\text{ e.c. with } n_{j+1}>f_A(n_j).$$

Every legality point checks out.

- **Generability ✔.** $\pi_{\kappa(g(n))}$'s Gödel code is poly-time from $n$; $\mathbb P_n(\varphi)$ is a legal price feature of rank $n$ for *any* sentence $\varphi$; Definition 4.3.2's closing remark makes the ramp an expressible $[0,1]$-feature; $\mathbb 1[n\in E]$ is a rational constant computed in poly time. So $\overline v$ is an e.c. $\mathcal{EF}$-progression, i.e. generable from $\overline{\mathbb P}^A$ (Definition 4.3.5).
- **Patience — the reviewer's key point, and my error ✔.** Sparse support gives patience for **any** $f_A$: if $n_{j+1}>f_A(n_j)$ with $f_A$ increasing, a window $[n,f_A(n)]$ meets $E$ in at most two points, so $\sum_{i=n}^{f_A(n)}v_i\le2$. Since 4.8.17's hypothesis reads "there exists a deferral $f$ such that for **any** generable $f$-patient divergent weighting…", **no choice of $f_A$ evades sparse weightings.** My first draft implicitly assumed a patience escape; there is none.
- **Divergence ✔.** $\mathbb P^A_m(\pi_k)\to\tau_k$ for each $k$ ($D_A$ is $\mathrm{PA}$-complete; 4.1.1 + 4.1.2), so cofinally many revisits to any false $k$ fire the ramp; (NH-1) supplies infinitely many false $k$.
- **Support value — the one soft joint.** The old-biased schedule is meant to make the per-$k$ finitely many "$A$-resolved, $H$-not-yet" days asymptotically negligible. **Caveat, stated for the record:** the per-index exception counts are uncomputable and may grow faster than any computable function, so a *fixed e.c.* old-biased schedule cannot be certified to make their partial sums negligible against the stage count. The reviewer's construction therefore needs an argument it does not yet have.

**The caveat does not save (NH-2)**, because a strictly simpler weighting works and needs none of this.

### 6.2 The elementary leak, which is decisive

> Let $k_0$ be **any** index with $\tau_{k_0}=0$ (one exists, §5.2), let $E_{k_0}$ be a sparse e.c. subset of $\{n:\kappa(g(n))=k_0\}$ with $n_{j+1}>f_A(n_j)$, and put $v_n:=\mathbb 1[n\in E_{k_0}]$.

- **e.c. ✔** — a Turing machine may have the constant $k_0$ hard-coded. Membership is decided by iterating $n_1,n_2,\dots$ past $n$: at most $O(\log n)$ iterations (each gap at least doubles under any $f_A(n)\ge2n$), each a bounded search under round-robin $\kappa$. Poly time. Hence $\overline{\mathbb P}^A$-generable.
- **$f_A$-patient ✔** by sparsity, for every $f_A$, as in §6.1.
- **Divergent ✔** — infinite support with weight $1$, and it is infinite **precisely because of the revisiting**.
- **Support value ✔** — for large $n\in E_{k_0}$, $\mathbb P^H_{g(n)}(\pi_{k_0})<\tfrac18$, so $\mu_n=1$ and $Y_n\to0$ (Lemma F at the lookahead).

So the $v$-average of $\operatorname{Val}(\ulcorner Y_i\urcorner)-\tfrac13$ tends to $-\tfrac13<0$. **(NH-2) is false.** No forecaster prices are used, no deductive-process timing is used, and no scheduling analysis is needed: the leak is a fact about the *environment*, not about what $A$ can discover.

**The error being corrected.** My §6.1 decomposition — "(NH-2) reduces to (NH-1) + the feature algebra + simulation cost" — conflated *"$A$ cannot find the weighting"* with *"the weighting does not exist"*. 4.8.17's hypothesis quantifies over what exists. Family-C hypotheses are statements about the environment; they are not protected by anyone's ignorance.

> **Named finding — the revisiting leak.** *Under a schedule that revisits a fixed sentence cofinally, no family-C pseudorandomness hypothesis about the resulting value sequence can hold, for either market, at any patience — because a weighting that hard-codes one revisited index is efficiently computable, patient by sparsity, and divergent by revisiting.* This is exactly why the paper's own $\pi$-digit example is safe: it never revisits, so a single-index weighting has finite support and is not divergent. Revisiting destroys precisely that protection.

### 6.3 Adjudication of the proposed repair (PA-independent carriers): correct in itself, insufficient here

The proposal: a computable family $(G_k)$ mutually independent over $\mathrm{PA}$; $\Gamma_H:=\mathrm{PA}+\{G_k\leftrightarrow\pi_k\}$, $\Gamma_A:=\mathrm{PA}$; $\psi_j:=G_{\kappa(j)}$, so $D_A$ **never** decides a carrier.

On its own terms it checks out, and one point improves:

- **Constructibility ✔.** Mostowski's independence theorem (1961; see Smoryński, *Self-Reference and Modal Logic*) gives a recursive sequence of sentences independent over any consistent r.e. extension of $\mathrm{PA}$; consistency of the full infinite extension follows by compactness.
- **Legality ✔, and cleaner than proposed.** Axiomatize $\Gamma_H$ by the **biconditionals** $G_k\leftrightarrow\pi_k$ rather than by the assignment $G_k\equiv\tau_k$: the biconditional sequence is e.c., so $\Gamma_H$ is a computably axiomatized consistent extension of $\mathrm{PA}$ and $D_H$ needs no oracle for $\tau$. 4.1.1/4.1.2/4.2.4 then apply relative to $\Gamma_H=\bigcup_nD_H^n$, which is the paper's own convention.
- **Determinacy ✔.** $\ulcorner Y_n\urcorner$ is still determined via $\Gamma_A=\mathrm{PA}$, because $X_n$ is about $H$'s *price* — a computation output — not about $G_k$'s truth, and $\mathrm{PA}$ proves the outputs of the (computable, if slow) coupled construction.
- **e.d. and decidability ✔.** The template mentions only the construction, never a carrier directly.
- **$A$'s prices go digit-silent ✔.** $\mathbb P^A_m(G_k)$ converges into $(0,1)$ (Non-Dogmatism 4.6.2) and carries no information about $\tau_k$, so §6.1's price-proxy leak dies structurally rather than by scheduling.
- **Theory asymmetry.** $\Gamma_H\supsetneq\Gamma_A$ is admissible — `delay-and-visibility` §1 lists "class and theory" as an axis orthogonal to delay and visibility — but it should be stated plainly as a cost, since a negative result would then be *using* it.

**But it does not fix the leak**, because §6.2 needs no forecaster prices at all. Substituting $G_{k_0}$ for $\pi_{k_0}$ changes nothing: $\mathbb P^H_m(G_{k_0})\to\tau_{k_0}$ (now via $\Gamma_H$), $\mu_n=1$ on late visits, $Y_n\to0$ along the hard-coded e.c. sub-schedule, (NH-2) false. **Verdict: correct engineering aimed at the wrong joint.**

**Variant B** (an exogenous evidence stream in $D_H$, deferred in $D_A$, which the first draft offered as the (NH-3)-free fallback) **dies identically** — and the reviewer's suspicion that it would need the same old-biased analysis is over-generous to it: the elementary leak never mentions $D_A$'s timetable, so the "era after $L(k)$" question does not arise. A $\Gamma_H=\Gamma_A$ version fares no better.

### 6.4 Collateral: (NH-1) must be re-indexed

As first stated, (NH-1) asserted frequency $\tfrac12$ for $\overline\tau$ against every patient generable divergent weighting **of each market** — which the same single-index weighting falsifies once revisiting is in play. It must be stated for the **unrevisited** family $(\pi_k)_k$ on the paper's own diagonal, which is consistent and is all §5.2 actually uses. Recorded as an error in the first draft.

---

## 7. Lemma P, and the collapse

The leak shows the *hypothesis* fails. Something stronger is true: the criterion **positively forces the gate shut**.

> **Lemma P (Preemptive symmetry).** Let $E\subseteq\mathbb N^+$ be efficiently computable and suppose $Y_n\to c$ as $n\to\infty$ along $E$. Then $a_n\to c$ along $E$.

*Proof (for $c=0$; the general case by translating by the constant $c$).* Put $B_n:=\ulcorner Y_n\urcorner$ for $n\in E$ and $B_n:=0$ (the constant-$0$ LUV) otherwise. Then $\overline B$ is a bounded, $\overline{\mathbb P}^A$-generable $\mathbb R$-LUV-combination sequence, i.e. $\overline B\in\mathcal{BLCS}$ (Definition 4.8.8) — this uses only that $E$ and the templates are e.c. For each fixed $n$, $\mathbb E^A_m(B_n)\to\operatorname{Val}(B_n)$ as $m\to\infty$: **Expectations Converge (4.8.3)** supplies the limit, and **Limit Coherence (4.1.2)** together with $\Gamma_A$-determinacy (NH-4) identifies it as $Y_n$ (resp. $0$). Hence $\inf_{m\ge n}\mathbb E^A_m(B_n)\le\operatorname{Val}(B_n)$, so
$$\limsup_n\ \inf_{m\ge n}\mathbb E^A_m(B_n)\ \le\ \max\Big(0,\ \limsup_{n\in E}Y_n\Big)\ =\ 0 .$$
By **Expectation Preemptive Learning (4.8.13)**, $\limsup_n\mathbb E^A_n(B_n)=\limsup_n\inf_{m\ge n}\mathbb E^A_m(B_n)\le0$. On $E$, $\mathbb E^A_n(B_n)=a_n\ge0$; off $E$ it is $0$. Therefore $a_n\to0$ along $E$. $\square$

**No hypotheses beyond NH-4.** No visibility, no pseudorandomness, no simulation-cost conjecture, no bound on how long the coupled construction takes to run, and no assumption about $D_A$'s timetable.

> **Corollary (collapse of the construction).** For each false $k$, the set $E_k:=\{n:\kappa(g(n))=k\}$ is e.c. and $Y_n\to0$ along $E_k$ (Lemma F + §5.2). By Lemma P, $a_n\to0$ along $E_k$. The intended bad days are exactly the late members of $\bigcup_{k\text{ false}}E_k$, so the gate $u_n=\operatorname{Ind}_\delta(a_n>t)$ closes on each of them. **Theorem N is refuted:** the environment contains no infinite set of days carrying both an open gate and a low human credence. Symmetrically, on visits to a true $k$, $a_n\to1$ and $\mathbb E^H_n(X_n)\to1$ — agreement again. On the remaining days ($H$ not yet resolved) $\mathbb E^H_n(X_n)\approx1$ and $Y_n\approx1$, so there is no deficit there either.

**Why this is more than the leak restated.** The leak says my hypothesis was false; Lemma P says the *conclusion* I wanted is false, and would be false for any inductor $A$ over any deductive process, however ignorant. It closes the escape "choose a cleverer $A$ that happens not to notice", which the existence grade would otherwise permit.

### 7.1 The residual crack, and why I do not think it can be widened

Lemma P is asymptotic *within each* $E_k$, non-uniformly in $k$. So for each false $k$ there is a window of visits $[H_k,C_k)$ — after $H$'s market has resolved the probe, before $A$'s quote has caught up — on which the violation would occur, and there are infinitely many $k$. A counterexample could in principle live in $\bigcup_k[H_k,C_k)$.

Non-emptiness is an **uncontrolled race** between two markets' convergence rates on a designer-chosen schedule, and I see no way to certify $H_k<C_k$ for infinitely many $k$:

- The §5.5 proposition says both $H_k$ and $C_k$ are uncomputable in $k$; it is a *proof* that no computable design pins either.
- No theorem orders the two. In the baseline ($\Gamma_H=\Gamma_A=\mathrm{PA}$, $\mathcal C_H=\mathcal C_A$) the two markets run the *same algorithm* on nearly the same process; asserting that $H$ resolves first is asserting a rate comparison the framework does not supply.
- The carrier repair does not order them: $A$ never needs to resolve $G_k$; it needs the $\mathrm{PA}$-decidable $\ulcorner Y_n\urcorner$, and Lemma P routes around $D_A$'s timetable entirely.

I record the crack as the one place a future construction could live, at **~0.15**, noting that exhibiting it would require exactly the kind of claim §5.5 forbids anyone from computing.

---

## 8. The obstruction, stated generally

> **Obstruction (Preemptive symmetry).** Consider any construction in which the violation days are days where $H$'s credence in $X_n$ is *forced* away from the profile $A$ quotes. The forcing routes through a handle that is one of:
>
> 1. **an efficiently computable object** — then $A$'s generators have it too (C3: both classes are poly-time in the same day index), and $A$ quotes correctly;
> 2. **a converged price of a fixed object**, made available at an e.c.-nameable day. Certifying "converged by day $j$" at infinitely many nameable $j$ is impossible without revisiting (§3.3 + §5.2), and revisiting makes the day-set $\{n:\text{the handle is }\varphi\}$ efficiently computable — on which $Y$ converges, so **Lemma P** forces $a_n$ to the same limit. Gate closed;
> 3. **a price pinned at the threshold by self-reference** — then Paradox Resistance (4.11.2) and §3.1's trader deny the margin, and nothing is forced at all.
>
> In every case the gate closes on exactly the days where $H$'s response was forced. **The one-way channel hides $H$'s prices from $A$'s feature algebra but not from $A$'s eventual knowledge, and Preemptive Learning converts eventual knowledge into timely diagonal knowledge for $A$ exactly as it does for $H$.**

**Which of the mandatory checks kills it.** Not Check 2 — Theorem A is properly evaded ($\mathbb E^H_n(X_n)$ has $\liminf0$ and $\limsup1$, so neither Theorem A nor its convergent extension applies). Not Check 3 — the asymmetry is in the feature algebra, not the complexity classes (§9). It is **Check 1, in a form the corpus had not inventoried.** Half 1 was taken to be an *averaged* constraint on the quote, so a bimodal human credence around an honest mean looked safe — and against 4.8.15 alone it *is* safe. Lemma P shows that on **e.c. gates with convergent targets** the constraint is pointwise and full-limit; and the straddle design is precisely the thing that manufactures such gates.

**Structural or technical?** Structural, on this route, for three converging reasons: the impossibility in §3.3 is a theorem of the paper; the necessity of revisiting in §5.2 follows from it; and Lemma P follows from theorems carrying no hypotheses. What is *not* established is that no other straddle engine exists — §3 kills the three that were on the table and I know of no fourth, but that is an absence of ideas, not a proof.

**Reading.** This is a hint that the positive conjectures are **true** for the per-day form on the one-way channel — the opposite of what the first draft concluded.

---

## 9. The mandatory consistency checks, re-run

**Check 1 — Half 1 is a theorem.** The environment passes it and in fact *exceeds* it: with $a_n\approx\bar q$ and $Y_n\in\{0,1\}$ of mean $\bar q$, the Cesàro error is identically $0$, not merely recurrent to $0$. The first draft's enumeration of what Half 1 permits — pointwise error of any size at any density; one-signed error on gates $A$ cannot generate; averages recurring to $0$ while pointwise error is large on a sub-density — **stands, as a statement about 4.8.15.** The error was in treating 4.8.15 as the *only* constraint on the quote. **Half 1 has a stronger sibling on e.c. gates: Lemma P.** Any future attempt must be audited against both, and the audit question is now: *is the bad-day set covered by e.c. subsets on which $Y$ converges?*

**Check 2 — Theorem A and the convergent extension.** Passed: $\mathbb E^H_n(X_n)$ does not converge and there is no limit profile for $A$ to predict; the questions are pairwise distinct and not e.c.-predictable; and the surprise is efficiently exploitable by $H$'s traders (Lemma F is $O(\mathrm{poly}(n))$ and reads only $H$'s own prices). Sanity check in the other direction: fixing $X$ restores Theorem A and removes the violation, so nothing was smuggled.

**Check 3 — no generator wedge.** Passed. Lemma F asks $H$'s trader only to *evaluate* a ramp on a price it is handed; $H$'s generators cannot compute $\mathbb P^H_{g(n)}$ either. Lemma S asks nothing of anyone. (C2) is a theorem about Definition 3.4.3 and holds at every class, including $\mathcal C_A=$ all computable functions. And the obstruction never needs $A$ to be weaker than $H$ — Lemma P shows $A$ *succeeds* with no extra power at all, which is the sharpest possible form of passing this check.

---

## 10. Corpus consequences — three retractions and three additions

### 10.1 RETRACTED: "trust does not compose" (open problem 14)
The first draft claimed `st` 4.12.4 $+$ Half 1 $\not\Rightarrow$ TT$(H\to A)$ on the strength of Theorem N. **Withdrawn.** Open problem 14 is open again, and Lemma P is a reason to be *more* optimistic about it: it supplies a hypothesis-free, pointwise, full-limit Half 1 on e.c. gates, much closer to the shape a composition argument needs than 4.8.15's limit point.

### 10.2 RETRACTED: "the `cee` route can only ever deliver an averaged conclusion" (open problem 7)
**Withdrawn, and reversed.** Lemma P is a full limit, so it removes a limit-point statement outright wherever the gate can be taken e.c. — the same currency `unbiasedness-theorem-families` §4.1 seeks from `ccee` (open problem 13). Concrete suggestion: run the `cee` route with Lemma P in place of $A$'s 4.8.15 on a fixed e.c. schedule $\overline d$, leaving only $H$'s limit point to place.

### 10.3 RETRACTED: "the shared fixed point is not an artifact of the gate for the per-day form"
**Withdrawn**; `faithful-acceleration-result` §6 sentence 3 stands as written. Separately, the sibling analysis (`varying-question-lab/[[route-recurring-ccee]]` §2) is right about two citation defects that touch this file: the corpus's ledger gate $\operatorname{Ind}_\delta(\mathbb P^H_n(\ulcorner a_n>t\urcorner)>\tfrac12)$ converges to the **hard** indicator rather than the ramp, and the 4.2.1 citation is wrong (Provability Induction needs an e.c. sequence of *theorems*). My §3.4(i) uses the same move and takes the same repair: select the true atoms by **ledger lookup**, which is e.c. because the atoms are decided in $D_H$, yielding two e.c. theorem-sequences (one for $\ulcorner a_n>t\urcorner$, one for its negation); and where a LUV-valued conclusion is wanted, cite **Expectation Provability Induction 4.8.10** — whose printed form is exactly "if $W(D_n)\ge b$ in all consistent worlds then $\mathbb E_n(D_n)\gtrsim_n b$" — on the tail of the LUV-combinations $\ulcorner u_n\urcorner-(1-\epsilon)$, rather than 4.2.1. The first draft's §9 paragraph on the lagged-ledger reading is corrected accordingly; no load-bearing step depended on it.

### 10.4 ADDED: Lemma P belongs in the option table
`unbiasedness-theorem-families` §3 lists three options for Half 1 (4.8.15, 4.8.16, 4.3.3), and its §2 sorting result says family D "cannot serve it at all, since it never mentions truth". **For determined targets that is wrong**: the limit expectation *is* the truth (4.8.3 + 4.1.2), so 4.8.12/4.8.13 convert into statements about truth. Lemma P should be a fourth row — *"on any e.c. gate where the target converges: pointwise, full limit, cost: nothing"* — with its limitation stated: the gate must be **e.c.**, where 4.8.15 allows any $\overline{\mathbb P}$-generable gate.

### 10.5 ADDED: the revisiting leak as a standing warning
§6.2, as a named finding. Any construction that revisits a sentence cofinally forfeits every family-C hypothesis about the resulting values, for both markets, at every patience.

### 10.6 ADDED: §5.5 is a load-bearing impossibility for this program
The *Uncomputable Convergence Rates* proposition (`main.tex:2680`) is cited nowhere in the wiki. It should be, in `delay-and-visibility`: it forbids any construction whose legality depends on a price having converged by an efficiently computable day, which is the natural repair for half the designs in this area.

---

## 11. Hypotheses, status, and what a skeptic attacks first

### 11.1 Named hypotheses, as they now stand

- **(NH-1) $\pi$-digit hardness**, stated for the **unrevisited** index sequence $(\pi_k)_k$ on the paper's own diagonal (corrected, §6.4); the paper's own hedge, held to the paper's own standard. Used only to get "both truth values occur infinitely often". *~0.9.*
- **(NH-4) $\mathcal{BLCS}$ membership and $\Gamma_A$-determinacy of $\overline{\ulcorner Y\urcorner}$**, discharged by computability of the coupled construction. The **only** input Lemma P needs. *~0.95.*
- **(NH-5) Legality of the self-referential $D_H$** — well-founded joint recursion, Kleene's recursion theorem, $\mathrm{LIA}_n$ reading only $D^{\le n}$. *~0.9.*
- **(NH-2) $A$-side opacity — WITHDRAWN, FALSE** (§6.2).
- **(NH-3) market-simulation cost — no longer used anywhere.** Lemma P routes around it: $A$ never needs to simulate $H$. (Note for reuse: it remains v3's no-shortcut conjecture, ~0.85 at $\mathcal C_A=\mathrm{EXP}$ and near-certain at $\mathcal C_A=\mathcal{EC}$.)

### 11.2 Status

| claim | status |
|---|---|
| (a) liar-like $\theta_k$ | **DEAD** — the criterion grinds the margin below every e.c. ramp; forcing dies, not paradox-disqualification (§3.1) |
| (b) pseudorandom-for-$H$ question family | **DEAD** — no margin, or no straddle (§3.2) |
| (c) decide it mid-block | **DEAD twice**, the second by the §5.5 impossibility (§3.3) |
| Lemma F (introspective forcing trader) | **PROVED**, no hypotheses (§5.1) — reusable |
| Lemma S (straddle via 4.2.4 + revisiting) | **PROVED** modulo (NH-1) (§5.2) |
| revisiting is necessary for Lemma S | **PROVED** modulo the §5.5 impossibility (§5.2) |
| (NH-2) opacity | **REFUTED** (§6.2) |
| the reviewer's price-proxy leak | **CORRECT**, modulo an unfinished schedule analysis (§6.1) |
| the PA-independent-carrier repair | **CORRECT in itself, INSUFFICIENT** — aimed at the wrong joint (§6.3) |
| Variant B (exogenous evidence stream) | **DEAD**, same reason (§6.3) |
| **Lemma P** (4.8.13 for $A$ on e.c. gates) | **PROVED**, hypothesis-free given (NH-4) (§7) |
| **Theorem N (the counterexample)** | **REFUTED** — the gate closes on every bad day (§7 Corollary) |
| the obstruction (§8) | **PROVED for this route**; looks structural, not technical |
| residual per-index race window | **OPEN, ~0.15**; probably not certifiable, by §5.5 |
| "the human is surprised" as the driver | **REFUTED as a design** (§3.4) |
| first draft's §10.1–§10.3 corollaries | **RETRACTED** |

**Verdict. The introspective route to a non-paradoxical Total Trust failure under one-way visibility does not work, and the obstruction looks structural: ~0.20** that some repair of this route succeeds (down from ~0.70 for the route as written). Open problem 9 overall: **~0.3**, down from ~0.45. The corresponding *positive* claim — that per-day deference is forceable on the one-way channel — deserves to go **up**, with Lemma P as both new evidence and a new tool.

### 11.3 What a skeptic attacks first

1. **Lemma P's padding step.** That $\overline B$ (padded with the constant-$0$ LUV off $E$) is in $\mathcal{BLCS}$, and that 4.8.13's $\limsup$ over the padded sequence really pins $a_n$ on $E$ rather than being swamped by the padding. I believe both are clean — $\mathcal{BLCS}$ needs generable, bounded, $\mathbb R$-LUV-combination (Definition 4.8.8) ✔, and the padding contributes $0$ to both sides ✔ — but this is now the single load-bearing step of the document and deserves a Lean pass; it is a short `limsup`/`Approx` composition of the established `lean-deference` shape.
2. **Whether $\mathbb E^A_m(B_n)\to Y_n$ for fixed $n$.** Uses 4.8.3 for existence and 4.1.2 + determinacy for the identification. If $\Gamma_A$-determinacy is doubted, Lemma P weakens and the §7.1 crack widens.
3. **Whether revisiting is truly necessary for Lemma S.** §5.2 argues it is, via §5.5. **A skeptic who exhibits a fourth straddle engine — separating $H$'s price at e.c.-nameable days without an e.c. pattern, without a converged fixed object, and without a self-referential pin — breaks the obstruction. This is the highest-value attack.**
4. **The per-index race (§7.1).** Someone may find a design that provably orders $H_k<C_k$ — e.g. by making $A$'s catch-up require a strictly harder computation than $H$'s resolution. I could not, and §5.5 suggests why.
5. **Lemma F's exploitation bookkeeping** — bounded below by $0$; $\mathrm{Budgeter}$ is the identity on a trader that never goes negative in any plausible world. Unchanged, and worth one careful pass since Lemma F is the piece most likely to be reused.
6. **(NH-5)**, the self-referential $D_H$ — routine, but a construction step rather than a citation.
7. **The reviewer's §6.1 schedule analysis**, if anyone wants that version rather than §6.2's; it is not needed for the conclusion.

---

## 12. One-paragraph summary for the wiki

*Redesign of `delay-and-visibility` §4, attempted and **abandoned**; open problem 9 should be graded down, not up.* The questions $X_n:=\ulcorner\mathbb P^H_{g(n)}(\psi_{g(n)})>\tfrac14\urcorner$ are legal, and the human's response to them is forced unconditionally by a two-line trader whose selection coefficient is a ramp on the human's **own settled price** (Lemma F) — not by Introspection 4.11.1, which is same-day and carries a margin hypothesis it cannot meet here, so §4's "forced for free, by citation" is wrong as stated though right in substance. The straddle, which §4 called the hard self-referential part, needs no self-reference at all: Preemptive Learning (4.2.4) on a schedule that **revisits** hard sentences at unbounded gaps forces the diagonal price to reach $0$ and $1$ infinitely often, rate-free — and rate-free is mandatory, because the §5.5 proposition *Uncomputable Convergence Rates* proves that no efficiently computable schedule can ever certify that a price has resolved. But revisiting is fatal twice over. First, it destroys every family-C hypothesis about the resulting values: a weighting that **hard-codes a single revisited index** is efficiently computable, patient by sparsity, and divergent, so no pseudorandomness assumption survives — the *revisiting leak*, which needs neither the forecaster's prices nor its deductive process, and which no carrier-independence repair touches. Second, and decisively, **Expectation Preemptive Learning (4.8.13) applied to the forecaster** shows that on *any* efficiently computable day-set where the realized target converges, the quote converges to the same value — hypothesis-free, no visibility, no simulation-cost conjecture (*Lemma P*). Revisiting manufactures exactly such day-sets, so the gate closes on precisely the days where the human's response was forced: **the straddle engine is symmetric between the two markets.** The obstruction generalizes — every available handle is either efficiently computable (the forecaster has it), a converged price of a fixed object (Lemma P mirrors it), or pinned at the threshold by self-reference (Paradox Resistance denies the margin) — and it looks structural rather than technical. Two things are worth keeping: **Lemma F**, as a reusable forcing tool for questions about a market's own prices; and **Lemma P**, a pointwise, full-limit Half 1 on efficiently computable gates, which corrects `unbiasedness-theorem-families`'s sorting claim that family D cannot serve Half 1 and offers a new attack on the common-subsequence gap (open problem 7). Finally, the motivating story was backwards in the first place: by `ceu` (4.12.2) the human's present credence already equals its own forecast of its future credence, so a failure driven by *the human's surprise* cannot be built on this channel at all.
