# The calibration / unbiasedness / learning families, and which half each serves

*An inventory of the LI paper's "the learning works well" theorems, sorted by what they can be used **for** in the faithful-acceleration argument. The organizing claim: the two halves of that argument ([[faithful-acceleration-result]] §2) draw on **almost disjoint** families, and knowing which is which tells you where each option can possibly help. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

*Written 2026-07-29 in answer to Abram's question — the paper frames §4.3 as two notions, but there are meaningfully more than two ideas, and they are not interchangeable. All statements checked against `references/logical-induction/main.tex`; numbering per the corrections in [[li-paper-erratum]] §3.*

---

## 1. Four families, not two

The paper's §4.3 is titled "Calibration and Unbiasedness", which reads as two notions. There are four ideas, distinguished by **what the price is being compared to**:

| family | the price is compared to | gate / quantifier | conclusion strength |
|---|---|---|---|
| **A. Calibration** (4.3.3) | the **frequency of truth**, on days when the price sits in a band | a *band on the market's own price* | limit point in the band; **two-sided** |
| **B. Unbiasedness** (4.3.6, 4.3.8; 4.5.9, 4.5.10; 4.8.15, 4.8.16) | the **truth value** $\operatorname{Val}_\Gamma$, averaged | *any* $\overline{\mathbb P}$-generable divergent weighting | limit point (Recurring) or full limit (From Feedback) |
| **C. Learning frequencies** (4.4.2, 4.4.5; 4.5.11; 4.8.17) | a **given target sequence** $\overline p$ | all $f$-patient generable weightings, *as a hypothesis about the environment* | $\eqsim_n$ / $\gtrsim_n$ tracking of the target |
| **D. Trajectory** (4.1.1, 4.2.3, 4.2.4; 4.8.3, 4.8.12, 4.8.13) | **the price's own future/limit values** — truth never appears | none, or all of $\mathcal{BLCS}$ | equalities between liminf/limsup and limit values |

**The paper itself insists A and B are different ideas**, and says which is weaker (`main.tex:1209`):

> "calibration alone is not a very strong property: a reasoner can always cheat to improve their calibration (i.e., by assigning probability 80% to things that they're sure are true, in order to bring up the average truth of their '80%' predictions). What we really want is some notion of 'unbiasedness', which says that there is no efficient method for detecting a predictable bias."

**C is a different logical type** from A and B and it is easy to mistake for them. A and B are unconditional theorems about any logical inductor. C has a *hypothesis about the environment* — that the sequence is pseudorandom relative to the relevant weighting class — and concludes the price matches a target. So C is a tool for **building environments**, not for extracting guarantees from an arbitrary pair. Reaching for C when you needed A or B is exactly the error that killed the block-delay impossibility ([[delay-and-visibility]] §3).

**D mentions truth nowhere at all.** These are the "you can't beat the market by waiting" theorems. They look least like calibration and turn out to be the most useful for Half 2.

---

## 2. The sorting result

Write $Y_n := \mathbb E^H_{f(n)}(X_n)$ (the human's future credence) and $a_n := \mathbb E^A_n(\ulcorner Y_n\urcorner)$ (the quote).

> **Half 1** — *the quote is honest about the future human* — compares **$A$'s price to the truth**. Only families **A** and **B** can serve it. C can only serve it by assuming the environment; D cannot serve it at all, since it never mentions truth.
>
> **Half 2** — *the future human speaks for the present human* — compares **$H$'s present price to $H$'s own future price**. Truth does not enter. So families A, B and C are largely beside the point, and the tools are **D** plus the self-trust cluster **§4.12**, which is not in the §4.3–4.5 calibration story at all.

That is the answer to "do these give different options for step 1 or step 2": **they split, and the split is nearly clean.** The one theorem that spans both is 4.8.15, because it can be applied to $H$'s market as well as $A$'s — and that double use is precisely where the current gap sits (§4).

---

## 3. Options for Half 1

| option | what it gives | cost | status |
|---|---|---|---|
| **4.8.15 Expectation Recurring Unbiasedness** (corrected) | on any $A$-generable divergent gate, the weighted average of $a_n - Y_n$ has $0$ as a limit point | **none** — gate on $A$'s own quote is free | in use; engine KERNEL-CHECKED |
| **4.8.16 Unbiasedness From Feedback** (corrected) | the same average $\eqsim_n 0$ — a **full limit** | support $\subseteq \operatorname{im} f$ **and** $\operatorname{Val}_\Gamma(Y_n)$ computable in time $O(f(n{+}1))$ — computing $Y_n$ means running the construction to day $f(n)$, so tower-ish spacing | available, costly; the thing v3 was pleased to remove |
| **4.3.3 Recurring Calibration**, applied to the sentence $\psi_n := \ulcorner \mathbb E^H_{f(n)}(X_n) > t\urcorner$ | on days when $\mathbb P^A_n(\psi_n)$ sits in a band $(a,b)$, the **frequency** with which the human really does end up above $t$ has a limit point in $[a,b]$ | needs $\overline\psi$ e.c. and $\Gamma_A$-decidable — free, given $\Gamma_A$ proves the construction's outputs, which is already assumed | **UNTRIED. The interesting one.** |

**Why 4.3.3 is worth trying.** Its gate is *a band on the market's own price* — which is exactly the shape Half 1 wants, and it is the only theorem in the paper whose gate is *natively* of that shape rather than needing a weighting to be constructed and argued legal. And its conclusion is **two-sided** (a limit point *in $[a,b]$*, both bounds), where 4.8.15 gives one limit point of a signed average. In words it delivers: *when the AI says 80% that the human will end up above $t$, the human ends up above $t$ about 80% of the time.* That is a more natural rendering of "the advertisement is honest" than an average-of-values statement, and it is closer to what a reader wants from a deference result.

**Two warnings.** First, the paper's own caveat: calibration is *gameable* and strictly weaker than unbiasedness, so a Half 1 built on 4.3.3 alone buys less — it constrains frequencies on bands the market itself selects, and says nothing about biases detectable by other efficient means. Whether that is enough for the deference conclusion depends on Half 2's shape and has not been checked. Second, 4.3.3 is a **propositional** theorem: there is no "Expectation Recurring Calibration" in §4.8 (verified — §4.8 has Provability Induction, Coherence, Persistence, Preemptive Learning, the two Unbiasedness theorems, and Learning Pseudorandom LUV Sequences, but no calibration analogue). Routing through the sentence $\psi_n$ is how to reach the LUV setting, and it changes the object from "the human's future credence" to "whether the human's future credence clears $t$" — a genuine change of target, not a translation.

**Family C is a trap here.** 4.8.17 and 4.4.5 look like they say "the quote is right", but they say "the quote matches a target *given the environment is hard for the quoter's class*". Using them for Half 1 smuggles in an environment assumption; using them to *build* an environment is legitimate and is what they are for.

---

## 4. Options for Half 2

This is the family the calibration story does not contain. All four options compare $H$'s present price to $H$'s own future price.

| option | statement | gated? | limit or limit point? |
|---|---|---|---|
| **`cee` 4.12.1** | $\mathbb E_n(X_n) \eqsim_n \mathbb E_n(\ulcorner \mathbb E_{f(n)}(X_n)\urcorner)$ | no | **full limit** |
| **`ceu` 4.12.2** | $\mathbb P_n(\phi_n)\eqsim_n \mathbb E_n(\ulcorner\mathbb P_{f(n)}(\phi_n)\urcorner)$ | no | **full limit** |
| **`ccee` 4.12.3** | $\mathbb E_n(\ulcorner X_n\cdot w_{f(n)}\urcorner)\eqsim_n \mathbb E_n(\ulcorner\mathbb E_{f(n)}(X_n)\cdot w_{f(n)}\urcorner)$, for $\overline w$ $\overline{\mathbb P}$-generable in $[0,1]$ | **yes** | **full limit** |
| **`st` 4.12.4** | $\mathbb E_n(\ulcorner\mathbb 1(\phi_n)\cdot\operatorname{Ind}_{\delta_n}(\mathbb P_{f(n)}(\phi_n)>p_n)\urcorner)\gtrsim_n p_n\cdot\mathbb E_n(\ulcorner\operatorname{Ind}_{\delta_n}(\cdots)\urcorner)$ | **yes**, on $H$'s *own future price* | $\gtrsim_n$, one-sided |
| **4.8.3 Expectations Converge** | $\mathbb E_\infty(X)$ exists, for fixed $X$ | — | limit |
| **4.8.12 Persistence of Expectation Knowledge** | $\liminf_n\inf_{m\ge n}\mathbb E_m(B_n) = \liminf_n \mathbb E_\infty(B_n)$, and dually | — | equality of liminf/limsup |

### 4.1 `ccee` is the one that attacks the current gap

The gap in the `cee` route ([[faithful-acceleration-result]] §4.3) is that it combines **two limit-point statements** — $A$'s 4.8.15 and $H$'s 4.8.15 — each delivered on its own subsequence. Every step that can be moved off 4.8.15 and onto a **full-limit** theorem reduces that problem.

`ccee` is a full limit *and* it is natively gated: applied at weight $w := u$ (the quote gate), it gives
$$\mathbb E^H_n(\ulcorner X_n\cdot u\urcorner) \;\eqsim_n\; \mathbb E^H_n(\ulcorner Y_n\cdot u\urcorner)$$
with **no subsequence introduced at all** — because it is proved from $H$'s own coherence, not by an unbiasedness/exploitation argument. So the gated present credence equals the gated expectation-of-future-credence, exactly. That removes one of the two limit points; **one remains** ($H$'s expectation of $Y_n$ against $Y_n$'s realized value), to be matched against $A$'s. So `ccee` does not close the gap but it halves it, and it is strictly better than the ungated `cee` for this purpose. **This is the first thing to try.**

### 4.2 `st` suggests a different framing: trust composes

`st` 4.12.4 is the self-trust instance of Total Trust ([[deference-notions]]): $H$ *already* totally trusts its own future self, as a theorem, with no hypotheses about anything. Combined with Half 1 — $A$ is calibrated to $H$'s future self — the natural shape is a **transitivity**:

$$H \text{ trusts future-}H \;(\texttt{st}, \text{free}) \;+\; A \text{ is calibrated to future-}H \;(\text{Half 1, free}) \;\Longrightarrow\; H \text{ trusts } A.$$

If that composes, it is a much better story than the current one: both inputs are theorems with no visibility assumptions, and the conclusion is deference. **The thing to check is that it composes in the right direction.** "$A$ is calibrated to future-$H$" is not the same as "future-$H$ endorses $A$", and trust is not obviously transitive across a party that is being *predicted* rather than *deferred to* — the middle term appears as an object in one premise and as a subject in the other. That is exactly the kind of step this project has got wrong before, so it wants writing out rather than asserting. Note there is prior partial work on TT transitivity in `deference-trust-lab/run3/work/tt-transitivity-forall/`.

### 4.3 Family D is the right tool for the varying-question extension

Theorem A's convergence route ([[faithful-acceleration-result]] §4.2) uses 4.8.3, which needs a **fixed** $X$. The extension to varying questions (T2′, ~0.6) has been looking for a substitute, and **4.8.12 Persistence of Expectation Knowledge is the natural candidate**: it is stated for an *arbitrary* $\mathcal{BLCS}$ sequence — no fixedness, no convergence hypothesis — and it equates $\liminf_n \inf_{m\ge n}\mathbb E_m(B_n)$ with $\liminf_n \mathbb E_\infty(B_n)$. That is precisely a statement bounding the *future* trajectory by limit values, uniformly along the sequence, which is what Theorem A's proof needs of the human side. 4.8.13 (Expectation Preemptive Learning) is its companion in the other direction.

This is the cheapest untried item on the list, and it is well matched to the target: it would turn "fixed question" into "any question sequence whose limit values behave", i.e. it would make the dividing line **surprise, not variation**.

---

## 5. What does not serve either half

- **Non-Dogmatism (4.6.x), Occam bounds, universal-semimeasure domination** — about never assigning $0$/$1$ and about prior mass; used elsewhere in the corpus (e.g. [[externalized-self-trust-and-non-dogmatism]]) but not calibration-like in the needed sense.
- **Coherence and Learning Exclusive-Exhaustive Relationships (4.1.2, 4.5.1, 4.5.5, 4.8.11)** — structural constraints at a fixed day; they are the "free tools" the novice uses inside proofs (`loe`, `expprovind`), not sources of Half 1 or Half 2.
- **Trust in Consistency (4.9.x)** — a different subject.
- **Paradox Resistance (4.11.2)** — governs the degenerate diagonal stratum ([[fa-scope-resolution]]), not the main line.

---

## 6. A correction to the `cee` route's gate

Working through the generability requirements here surfaced an error in [[faithful-acceleration-result]] §4.3 as first drafted, which is recorded there and repeated here because it is a general trap.

The claim was that the gate $u_n = \operatorname{Ind}_\delta(a_n > t)$ is $\mathcal C_H$-generable because $H$ "may read $A$'s posted quote as settled data once $A$ has cleared". **That conflates two different legality notions:**

- a **trader** may depend on settled cross-market data arbitrarily, including hard (discontinuous) dependence — this is msg 39's correction and it is right;
- a **generable weighting** (Definition 4.3.5) must be an e.c. progression of *expressible features*, and expressible features (Definition 3.4.3) are built from **the market's own price features**, rationals, $+$, $\times$, $\max$, safe reciprocal. $A$'s quote is not an expressible feature of $H$'s market, and it is not e.c. either (computing it means running $A$).

**The repair is the corpus's existing ledger device.** Feed $A$'s quotes into $D_H$ as decided transcript atoms — already assumed — and gate on **$H$'s own price of the sentence about the quote**:
$$\tilde u_n := \operatorname{Ind}_\delta\big(\mathbb P^H_n(\ulcorner a_n > t\urcorner) > \tfrac12\big),$$
which *is* an expressible feature of $H$'s market. Once the atom is decided, Provability Induction (4.2.1) on the e.c. sequence $\ulcorner a_n > t\urcorner$ drives $\mathbb P^H_n$ of it to its truth value, so $\tilde u$ agrees with $u$ up to finitely many days plus a vanishing error. This is the "$H^+$ reads $A$'s quote ledger" mechanism of [[setting-and-notation]] §Setting 2, and it is why the ledger is in the setting in the first place.

**Note the asymmetry this exposes.** $A$'s side of Half 1 needs no ledger — the gate is a ramp on $A$'s *own* quote, which is natively an expressible feature of $A$'s market. Only $H$'s side needs the ledger. So the one-way channel is doing double duty: it delivers the quote to $H$'s deductive process *and* it is what makes the gate legal for $H$'s weightings.

---

## 7. Status

| claim | status |
|---|---|
| Four families, distinguished by what the price is compared to | INTERPRETATION (and the A/B distinction is the paper's own) |
| Half 1 can draw only on A and B; Half 2 on D and §4.12 | PROVED (prose, this page) — by inspection of what each theorem compares |
| 4.3.3 route to Half 1, via the sentence "future credence $> t$" | **UNTRIED**; two-sided conclusion, native band gate, but calibration is the weaker notion |
| `ccee` removes one of the two limit points in the `cee` route | CONJECTURED (~0.8); the cheapest improvement available |
| Trust transitivity via `st` + Half 1 | CONJECTURED (~0.5); direction of composition is the thing to check |
| 4.8.12 substitutes for convergence in the varying-question extension | CONJECTURED (~0.6); cheapest untried item |
| The gate needs the ledger, not "settled data" | PROVED (prose, §6) — a correction to this wiki's own earlier draft |

## Related

- [[faithful-acceleration-result]] — the two halves, and the three routes to Half 2
- [[delay-and-visibility]] — where mistaking family C for A/B did real damage
- [[li-paper-erratum]] — the corrected 4.8.15/4.8.16, the 4.4.4 sign transposition, and the numbering
- [[deference-notions]] — `st` as the self-trust instance of Total Trust
- [[setting-and-notation]] — the quote ledger and $H^+$
- [[open-problems]] — the common-subsequence gap this page proposes attacking with `ccee`
