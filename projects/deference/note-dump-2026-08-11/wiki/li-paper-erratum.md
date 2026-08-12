# Errata in the Logical Induction paper

*Three defects in the printed text of Garrabrant et al., *Logical Induction* (arXiv:1609.03543v5). All are editing artifacts, not mathematical errors: in every case the appendix proofs are correct and settle what the statements were meant to say. Source of truth throughout is `references/logical-induction/main.tex`, with line numbers given so each can be re-found. Conventions: [[conventions-and-status-labels]]. Master map: [[index]].*

*Provenance: erratum 1 found in the FA chat (`imported-chats/2026-07-01__…a6632d0f.md` msgs 17–19), reported in `fa-positive-results-corrected-v3.md` §2; errata 2 and 3 found 2026-07-29 during an independent verification pass. All three re-derived from source on 2026-07-29 — see [[delay-and-visibility]] and [[faithful-acceleration-result]] for the results that depend on them.*

---

## 1. The support clause is transposed between 4.8.15 and 4.8.16

**Status: CONFIRMED**, re-derived twice independently from `main.tex` and its appendix.

**What is printed.** Theorem 4.8.15, Expectation Recurring Unbiasedness (`main.tex:1812–1820`), reads:

> "If $\overline{B}\in\mathcal{BLCS}$ is determined via $\Gamma$, and $\overline w$ is a $\overline{\mathbb P}$-generable divergent weighting **weighting such that the support of $\overline w$ is contained in the image of $f$**, [the weighted average error] has $0$ as a limit point."

Two defects visible on the face of it: the doubled word "weighting weighting", and **$f$ is a free variable** — 4.8.15 introduces no deferral function, so as printed the theorem is unparseable.

Theorem 4.8.16, Expectation Unbiasedness From Feedback (`main.tex:1822–1832`), **omits** that clause — although it *does* declare a strictly increasing deferral function $f$, which is precisely the variable the clause needs. Its timing condition also reads $\operatorname{Val}_\Gamma(A_n)$ where the theorem's sequence is $\overline B$ (macros: `\aff`$=A$ at line 164, `\affluv`$=B$ at line 167), and it writes $w$ where $\overline w$ is meant.

**Why the appendix settles it.** Appendix E.11 (`main.tex:5240–5258`) proves 4.8.15 by "Apply Theorem `recunbiasedaff`" — that is **4.5.9**, Affine Recurring Unbiasedness, whose hypotheses are only $\overline A\in\mathcal{BCS}$ determined via $\Gamma$ and $\overline w$ a $\overline{\mathbb P}$-generable divergent weighting: **no deferral function and no support clause**, and its own 114-line proof (appendix D.1, `main.tex:4558–4675`) never mentions $f$ at all. E.11 passes $\overline w$ through unchanged, so it never needs the clause.

Appendix E.12 (`main.tex:5260–5282`) proves 4.8.16 by applying **4.5.10**, Affine Unbiasedness from Feedback, which *does* carry the clause — and appendix D.4's proof of 4.5.10 **uses it essentially**, defining its bias only over the image of $f$ and arguing "since we need only consider the sum over $n$ in the support of $f$" (`main.tex:4739–4742`).

**The pattern is otherwise uniform.** Six statements, three levels, two theorems each — Recurring is clause-free and From-Feedback carries the clause at the propositional level (4.3.6 / 4.3.8) and the affine level (4.5.9 / 4.5.10). Only the expectation pair has them exchanged. Together with the un-renamed $A\to B$, the diagnosis is a copy-paste of 4.5.9/4.5.10 into 4.8.15/4.8.16 in which the clause landed on the wrong theorem and one symbol substitution was missed. Corroborating detail: **4.8.15 is the only theorem in §4.8 with no `\proofin{...}` pointer**, even though appendix E.11 exists and is labelled.

**Corrected statements, for citation and formalization.**

- **4.8.15** — If $\overline B\in\mathcal{BLCS}(\overline{\mathbb P})$ is determined via $\Gamma$ and $\overline w$ is **any** $\overline{\mathbb P}$-generable divergent weighting, then $\big(\sum_{i\le n}w_i(\mathbb E_i(B_i)-\operatorname{Val}_\Gamma(B_i))\big/\sum_{i\le n}w_i\big)_n$ **has $0$ as a limit point**; in particular if it converges it converges to $0$. *(Delete the clause; delete one "weighting".)*
- **4.8.16** — Given $\overline B\in\mathcal{BLCS}$ determined via $\Gamma$, a strictly increasing deferral function $f$ with $\operatorname{Val}_\Gamma(B_n)$ computable in time $\mathcal O(f(n{+}1))$, and a $\overline{\mathbb P}$-generable divergent weighting $\overline w$ **whose support is contained in the image of $f$**, the weighted average error $\eqsim_n 0$. *(Add the clause; $A_n\to B_n$; $w\to\overline w$.)*

**Direction of the correction, which is easy to get backwards.** The swap makes **4.8.15 stronger** (a spurious hypothesis removed: limit-point unbiasedness against *every* generable divergent weighting) and **4.8.16 weaker** (a restriction added to the full-limit theorem). Confidence ~0.95, and it is certified by the paper's own appendix rather than resting on our reading.

**Load-bearing?** No — and this matters, because the FA corpus once thought otherwise. Msg 39 of the FA chat retracted the architecture that made 4.8.16 the protagonist; the corrected positive result runs on the **clause-free 4.8.15** plus realized-cash accounting. The erratum remains a real fact about the paper worth reporting upstream, but no result here depends on it. See [[faithful-acceleration-result]].

**Note also**: 4.8.15's conclusion is a **limit point**, not a limit. Reading it as a limit is a slip this project has made more than once; the contrapositive is machine-checked against the weak form as `Staleness.not_limitPointZero_of_one_signed` ([[faithful-acceleration-result]] §Half 1).

---

## 2. Definition 4.4.4's "above"/"below" labels are transposed

**Status: CONFIRMED** (found 2026-07-29; not previously recorded anywhere in this corpus).

**What is printed.** Definition 4.4.4, Varied Pseudorandom Sequence (`main.tex:1305–1312`), defines $\overline\phi$ to be $\overline p$-varied pseudorandom via
$$\frac{\sum_{i\le n} w_i\cdot\big(p_i - \operatorname{Thm}_\Gamma(\phi_i)\big)}{\sum_{i\le n} w_i}\;\eqsim_n\; 0,$$
and then says: "we can replace $\eqsim_n$ with $\gtrsim_n$ or $\lesssim_n$, in which case we say $\overline\phi$ is **varied pseudorandom above $\overline p$** or **varied pseudorandom below $\overline p$**, respectively."

**Why that is backwards.** With the numerator as printed, $\gtrsim_n 0$ says the $w$-weighted truth frequency is at most $p$ — which is "below", not "above". Appendix D.7's proof of 4.4.5 (`main.tex:4948–4964`) confirms the intended reading: it sets $A_n := \phi_n - p_n$, so $\operatorname{Val}_\Gamma(A_i) = \operatorname{Thm}_\Gamma(\phi_i) - p_i$ — **the opposite sign** — and asserts that pseudorandomness *above* $\overline p$ gives $\sum w_i\operatorname{Val}(A_i)/\sum w_i \gtrsim_n 0$. Appendix D.8 corroborates: given frequency exactly $p$ and a rational $q<p$, it says $\overline\phi$ "is varied pseudorandom above $q$", which requires $(\operatorname{Thm}-q)\gtrsim 0$.

**Correction.** Either read the numerator as $\big(\operatorname{Thm}_\Gamma(\phi_i) - p_i\big)$, or swap the words "above" and "below" in the printed 4.4.4. The two-sided $\eqsim_n$ case is sign-symmetric and unaffected — so anything citing only the two-sided form is safe.

**Who needs this.** Anyone using the one-sided forms of **4.4.5** (Learning Varied Pseudorandom Frequencies) or its LUV analogue **4.8.17**. Note that 4.8.17 states *only* the $\gtrsim$ form, so the convention matters there. Appendix D.7 also carries two harmless typos of its own: the display's numerator index should be $A_i$ not $A_n$, and `\thmval{...}` is written with braces where parentheses are meant, so it prints without them.

---

## 3. Numbering corrections for §4.11, and one in §4.3

**Status: CONFIRMED** by walking the shared theorem counter (`main.tex:37–63` alias `definition`, `keydef`, `theorem`, `lemma`, … onto one counter, reset only at `\subsection` since `secnumdepth` is 2).

§4.11 (Introspection) contains exactly **four** numbered items:

| # | name | label | line |
|---|---|---|---|
| 4.11.1 | Introspection | `thm:ref` | 1969 |
| 4.11.2 | Paradox Resistance | `thm:lp` | 1992 |
| **4.11.3** | Expectations of Probabilities (`epr`) | `thm:epr` | 2014 |
| **4.11.4** | Iterated Expectations (`er`) | `thm:er` | 2022 |

**There is no Theorem 4.11.5.** [[conventions-and-status-labels]]'s dictionary previously listed `epr` as 4.11.4 and `er` as 4.11.5 — both off by one; corrected there.

Similarly in §4.3 (Calibration and Unbiasedness): propositional **Recurring Unbiasedness is 4.3.6** (`main.tex:1225`), not 4.3.7 — 4.3.7 is Definition *Deferral Function* (`main.tex:1240`). Unbiasedness From Feedback is 4.3.8 (`main.tex:1249`), as recorded. Also worth having: $\operatorname{Ind}_\delta$ is Definition **4.3.2**, Continuous Threshold Indicator (`main.tex:1174`), whose closing remark explicitly blesses expressible-feature arguments — "we can generalize this definition to the case where $x$ and $y$ are expressible features, in which case $\operatorname{Ind}_\delta(x>y)$ is an expressible $[0,1]$-feature". That remark is what makes the quote-gate legal in [[faithful-acceleration-result]] §Half 1. And **Generable From $\overline{\mathbb P}$ is Definition 4.3.5** (`main.tex:1218`), which matters for [[delay-and-visibility]] §"why forcing and hiding conflict".

---

## Not an erratum: 4.8.17 is clean

`fa-block-staleness-impossibility.md` flags a worry that Theorem 4.8.17's printed form "participates in the family of statements around the erratum". It does not. 4.8.17, Learning Pseudorandom LUV Sequences (`main.tex:1834–1844`), is clean: one-sided ($\gtrsim$), with a patience hypothesis and **no support clause**. Its appendix (E.13) supplies all three sign cases. Applying it to $B_n - c$ and $c - B_n$ (both in $\mathcal{BLCS}$; $\mathbb E_n$ is linear on LUV-combinations) yields the two-sided form when needed. That worry is discharged.

**Separately, and not a paper defect:** "**e.d.**" (efficiently *describable*) is **not an LI notion** — zero occurrences in `main.tex`. It is this wiki's own coinage, deliberately introduced at [[setting-and-notation]] §LUV, and must not be attributed to the paper. The paper's notions are "e.c." (Definition 3.3.1) and the strictly larger "$\overline{\mathbb P}$-generable" (Definition 4.3.5).

---

## Reporting upstream

All three are worth sending to the authors. Erratum 1 is the consequential one for readers (it inverts which of two theorems is the strong one); erratum 2 will silently flip a sign for anyone using the one-sided learning theorems; erratum 3 is cosmetic but affects every citation of `epr`/`er`. Nothing here threatens any result in the paper.

## Related

- [[faithful-acceleration-result]] — the result that runs on the corrected 4.8.15
- [[delay-and-visibility]] — where 4.3.5's "no primitive for the deductive state" does real work
- [[unbiasedness-theorem-families]] — the six-statement anatomy across the three levels
- [[conventions-and-status-labels]] — the label → theorem dictionary, corrected per §3
