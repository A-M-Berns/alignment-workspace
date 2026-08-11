# Does faithful acceleration reach *all* sentences? — the quote-referencing exception

*A decision note (Claude Opus 4.8, with Abram Demski). [`faithful-acceleration.md`](faithful-acceleration.md) states the positive result over **all sentences**; [`pointwise-tower-and-faithful-acceleration.md`](pointwise-tower-and-faithful-acceleration.md) states it over an **admissible domain** = all sentences *except a quote-referencing family*. They can't both be right. This note works out which is, in enough detail to decide. **Bottom line up front:** the admissible-domain version (pointwise) is correct; faithful over-claims, and its §6 conflates two different self-referential sentences. The fix is to bring faithful up to the admissible-domain framing — the reverse of "sync pointwise to faithful."*

---

## 0. What's at stake, in one paragraph

The positive result forces $H$ to (gated/classwise) **Total Trust** $A$, by a trade that leans on **ingredient (II): calibration** — $A$'s forecast $a_n$ is unbiased, on average, for $H$'s realized lookahead credence $Y_n = E^H_{f(n)}(X)$. The whole reach-everything claim rests on the line "a human credence $E^H_{f(n)}(X)$ exists for *every* sentence $X$, decidable or not, so (II) holds for every $X$." The question is whether that last step is true. It is **not** — there is a constructible family of $X$ on which $E^H_{f(n)}(X)$ exists but is a **hard $0/1$ value that reacts against $a_n$**, and there calibration provably fails. So the credence *existing* is necessary but not sufficient; the positive result holds off that family, i.e. on the *admissible domain*.

---

## 1. The two claims, verbatim

**faithful-acceleration.md — "all sentences":**
- §4(II): "The feedback is a human credence, which always exists. $E^H_{f(n)}(X)$ is realized for *every* $X$… So **(II) holds over all sentences** — there is no decidable/timely fragment to restrict to…"
- §5 (theorem): "…holds for **every** $X$ — over **all sentences**, decidable or not…"
- §6 (anti-inductive bullet): "*Dissolved:* there is no truth-value settlement here. The trade lives entirely at $H$'s **continuous prices**, where the diagonal sentence is benign; the human's credence about a self-referential sentence is a continuous price the AI can calibrate to."

**pointwise-tower-and-faithful-acceleration.md — "admissible domain":**
- §3 (claim): "$H$ is forced into gated (classwise) Total Trust… over its **admissible domain** (all sentences but the quote-referencing 2a family; §4.1)…"
- §3.2: "Existence is necessary but not sufficient: where the credence-target hard-settles as an anti-inductive function of $a_n$, calibration *fails* — the 2a diagonal sits *outside* the admissible domain."
- §4.1: "Averaged Total Trust dies too… whatever $A$ quotes, the gate $\mathrm{Ind}_\delta(a_n>\tfrac12)$ (or, if $A$ stays low, the uniform weight) carries a persistent $\ge\tfrac12$ bias… Expectation Unbiasedness From Feedback **cannot apply**… Calibration breaks exactly where tracking does."

These flatly disagree. The disagreement is entirely about one family of sentences, so let us look at it directly.

---

## 2. Two self-referential sentences that look alike but aren't

Both documents agree the construction needs **mutual observability**: $H$ reads $A$'s quotes $a_n$ (that is how $H$ can *use* the forecast). The moment $H$ can read $a_n$, $H$'s language can express sentences *about* $a_n$. Consider two self-referential sentences:

- **Price-level liar** $\chi \;\leftrightarrow\; \big(P^H(\chi) < \tfrac12\big)$ — "$H$'s own credence in me is below a half." Self-reference through $H$'s **own price**.
- **Quote-referencing diagonal** $g_n \;\leftrightarrow\; \big(a_n \le \tfrac12\big)$ — "the AI's quote on me is at most a half." Self-reference through $A$'s **quote**, which $H$ reads. (Constructible by the diagonal lemma exactly as in [`self-referential-settlement-target.md`](anson-notes/self-referential-settlement-target.md) §2a; the $\beta$-ledger that records $a_n$ is what lets $g_n$ name it.)

faithful §6's defense — "the credence about a self-referential sentence is a continuous price the AI can calibrate to" — is **true for $\chi$** and **false for $g_n$**. That is the whole issue. Here is why they diverge.

---

## 3. Why $\chi$ is benign and $g_n$ is fatal

The target the positive result calibrates to is $Y_n = E^H_{f(n)}(X)$ — $H$'s lookahead credence in $X$. Compare the two:

**$\chi$ (benign).** $\chi$ talks about $H$'s *own price*. The logical-induction framework tames this exactly: a trader's demand for $\chi$ is a *continuous* function of the price, so the market **clears $\chi$ at $\tfrac12$** (a Brouwer fixed point) and $\chi$ is **never decided** by $D$. Hence
$$E^H_{f(n)}(\chi) \;\approx\; \tfrac12 \qquad(\text{continuous, and independent of } a_n).$$
$A$ forecasts $a_n \approx \tfrac12$ and is calibrated; the trade round-trips at a continuous price near $\tfrac12$. Nothing breaks. This is faithful §6's valid case, and faithful is right about it.

**$g_n$ (fatal).** $g_n$ talks about $A$'s *quote* $a_n$, and $H$ **reads** $a_n$ — so "$a_n \le \tfrac12$" is a settled fact in $H$'s deductive process (recorded by stage $\sim n{+}1 < f(n)$). Therefore $g_n$ is **decided**, and convergence-on-decided-sentences gives
$$E^H_{f(n)}(g_n) \;\longrightarrow\; \mathbb{1}[a_n \le \tfrac12] \qquad(\text{hard } 0/1, \text{ and an anti-inductive function of } a_n).$$
The target is no longer a continuous price near $\tfrac12$; it is a $0/1$ value engineered to be the **opposite** of where $a_n$ sits. The credence *exists* — it is $\mathbb 1[a_n\le\tfrac12]$ — but it is not a "benign continuous price," so faithful §6's premise fails here.

**The clean distinction.** For $\chi$ the target is *continuous* and *independent of $a_n$*. For $g_n$ the target is *discontinuous* ($0/1$) and an *anti-inductive function of $a_n$*. The two properties are linked: it is $0/1$ *because* $g_n$ hard-decides, and anti-inductive *because* $g_n$ references the $a_n$ that $H$ reads. faithful's §1 lists three properties of a credence — "always present, continuous, self-trusted" — and §6 leans on **continuous**. On the quote-referencing family the credence is *present* but *not continuous*. That is the gap.

---

## 4. Calibration provably fails on $g_n$ (the gate argument)

It is worth seeing that the *averaged* ingredient (II), not just the pointwise tower, dies here — because that is precisely what faithful's "all sentences" needs and what pointwise denies.

Suppose, for contradiction, that (II) held for $X = g_n$: for every $\mathcal{C}_A$-generable **divergent** weighting $w$,
$$\sum_n w_n\big(a_n - Y_n\big) = o\Big(\textstyle\sum_n w_n\Big), \qquad Y_n = \mathbb 1[a_n \le \tfrac12].$$
Write the per-day bias $b_n := a_n - \mathbb 1[a_n\le\tfrac12]$. Note its **sign is pinned to which side of $\tfrac12$ the quote is on**:
$$a_n > \tfrac12 \;\Rightarrow\; b_n = a_n \;\ge\; \tfrac12 \;(>0); \qquad a_n \le \tfrac12 \;\Rightarrow\; b_n = a_n - 1 \;\le\; -\tfrac12 \;(<0).$$

1. **Gate on the high side**, $w_n = \mathrm{Ind}_\delta(a_n > \tfrac12)$. If this gate were divergent, (II) would force $\sum w_n b_n = o(\sum w_n)$; but $b_n \ge \tfrac12$ on the gate, so $\sum w_n b_n \ge \tfrac12\sum w_n$ — not $o(\cdot)$. So the gate is **non-divergent**: $a_n > \tfrac12$ on only bounded weight.
2. **Gate on the low side**, $w_n = \mathrm{Ind}_\delta(\tfrac12 - \delta - a_n)$ (i.e. $a_n < \tfrac12-\delta$). Same argument with $b_n \le -\tfrac12$: also **non-divergent**, so $a_n < \tfrac12$ on only bounded weight.
3. Together (1)+(2): on **all but bounded weight**, $a_n = \tfrac12 \pm o(1)$, hence $a_n \le \tfrac12$, hence $Y_n = \mathbb 1[a_n\le\tfrac12] = 1$, hence $b_n = a_n - 1 \to -\tfrac12$.
4. Now take the **uniform** weighting $w_n \equiv 1$ (divergent). By step 3, $\frac1N\sum_{n\le N} b_n \to -\tfrac12 \ne 0$ — violating (II).

So no quote sequence $a_n$ satisfies (II) on the quote-referencing diagonal: every behavior is exploitable on *some* legal gate. Concretely, this is the "$\ge\tfrac12$ gate-visible bias whatever $A$ quotes" of pointwise §4.1, made explicit. **Calibration cannot hold there.**

*(LI-theorem reading.)* Expectation Unbiasedness From Feedback (Thm 4.8.16) is a theorem: it holds for *any* inductor whose feedback target is determined-via-$\Gamma$ with good feedback. Its conclusion is what we just showed is unsatisfiable. So on this family the theorem **cannot be invoked** — its applicability breaks because the feedback target $\mathbb 1[a_n\le\tfrac12]$ is a hard, discontinuous, anti-inductive function of $A$'s own forecast. This is the $\chi$-paradox of §2a reappearing *inside ingredient (II)*: the same `no_exact_quote` bound ($|a - \mathbb 1[a\le\tfrac12]| \ge \tfrac12$) that kills pointwise *tracking* also forces the gate-visible bias that kills *calibration*. **Calibration breaks exactly where tracking does**, and on the same family.

---

## 5. So the positive result does not reach $g_n$ — it avoids it

The positive theorem is *proved from* (II). On the quote-referencing diagonal (II) is unavailable, so the proof yields nothing there; and independently, the conclusion (gated Total Trust) is itself false there (step 4 above is exactly a gate on which $H$'s credence stays low while $A$ forecasts high or stays pinned — the violation the theorem says has bounded weight in fact has unbounded weight). **Both faces — the negative's tower and the positive's averaged Total Trust — die together on $g_n$.** That coincidence is the real "fit" between the two results, and it is what pointwise §4.1 says and faithful currently misses.

The honest description is therefore *avoidance*, not conquest: the construction is sound precisely as long as its contracts stay off the quote-referencing diagonal — i.e. stay in the **admissible domain**. This is not a side condition bolted on; it is exactly the positive note's own deepest open obligation, **§8 obligation 3 ("no hidden hard settlement")**: the escape from §2a holds only while the construction never settles a contract against a discontinuous function of $a_n$. "Admissible domain" is the name of the region where that obligation is met.

---

## 6. Verdict

| | faithful (current) | pointwise (current) | correct? |
|---|---|---|---|
| scope of the positive result | **all sentences** | **admissible domain** (all but quote-referencing 2a family) | **pointwise** |
| anti-inductive obstruction | "dissolved" (§6) | survives on the quote-referencing diagonal; the positive *avoids* it (§4.1) | **pointwise** |
| $\chi \leftrightarrow (P^H(\chi)<\tfrac12)$ | benign ✓ | benign ✓ | both right |
| $g_n \leftrightarrow (a_n\le\tfrac12)$ | (implicitly covered — wrong) | excluded — calibration fails | **pointwise** |

pointwise is the corrected version; faithful over-claims. So **"sync pointwise to faithful" would import an error into the doc that already fixed it.** The right move is the reverse — upgrade faithful to the admissible-domain framing — after which the two agree on the correct claim.

---

## 7. The recommended fix (three edits to faithful, one to pointwise)

**faithful-acceleration.md:**
1. **§4(II), second bullet.** Replace "(II) holds **over all sentences**" with: existence of the credence is *necessary but not sufficient*; (II) holds over the **admissible domain** — all $X$ except the quote-referencing family, where $E^H_{f(n)}(X)$ hard-settles as an anti-inductive function of $a_n$ (then $Y_n=\mathbb 1[a_n\le\tfrac12]$ and calibration fails, §6/§4.1 of pointwise).
2. **§5 (theorem).** "over **all sentences**, decidable or not" → "over its **admissible domain** (all sentences but the quote-referencing 2a family)".
3. **§6 (anti-inductive bullet).** Rewrite the "*Dissolved*" to distinguish the two self-references: the **price-level liar** $\chi$ is genuinely benign (continuous, $a_n$-independent, never decides); the **quote-referencing** $g_n$ is **not** dissolved — $H$ reads $a_n$, so $g_n$ decides and the credence hard-settles to $\mathbb 1[a_n\le\tfrac12]$, where calibration fails. The obstruction is *avoided* (kept off the diagonal — §8 obligation 3), not dissolved.

**pointwise-tower-and-faithful-acceleration.md:**
4. **§0 (one-paragraph version)** still says the positive result is forced "over *all* sentences," out of step with its own body (§3–§7 say "admissible domain"). Align §0 to "admissible domain" (or "all but the quote-referencing family").

After these, both notes assert the same, correct claim, and faithful's §1 "three properties" stay honest (the *continuous* property — not just *present* — is what the admissible domain secures).

---

## 8. The one genuine residual (so the decision is fully informed)

There is a real subtlety worth flagging, separate from the over-claim above. Two framings of "the positive result excludes $g_n$" are available, and they are not quite the same:

- **(a) Calibration fails on $g_n$** (the gate argument, §4). Clean and self-contained: *given* the construction, ingredient (II) cannot hold on that family.
- **(b) The construction is set up to avoid $g_n$** (obligation 3). The stronger, constructive reading: a full construction is *defined* so that its contract LUVs never hard-settle against $a_n$, keeping everything on the continuous-price level. Whether such a construction *exists* in general — i.e. whether obligation 3 can always be discharged — is the positive note's named open problem.

Both point the same way (the quote-referencing family is out), so the **scope claim ("admissible domain") is right regardless**. The residual uncertainty is only about *how* the admissible domain is secured — by a fact (calibration fails there anyway) or by a construction obligation (don't build the diagonal) — and that uncertainty already lives in faithful §8 / pointwise §6. The fix in §7 does not depend on resolving it; it only stops faithful from claiming the family is reached.

---

## 9. One-line summary

A human credence exists for every sentence, but it is a **benign continuous price** only when the sentence is self-referential through $H$'s *own price* ($\chi$); when it is self-referential through *$A$'s quote that $H$ reads* ($g_n$), the credence hard-settles to an anti-inductive $0/1$ and calibration fails. So faithful acceleration is forced over the **admissible domain** (all but that quote-referencing family), not literally all sentences — pointwise is right, faithful over-claims, and the sync should run faithful ← pointwise.
