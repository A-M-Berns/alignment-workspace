# Vetting guide: the 4.8.15/4.8.16 erratum, read in tandem with the LI paper

*Claude, 2026-07-31, at Abram's request. A check-by-check companion for verifying the LI-paper correction that Theorem SS ([[route-sparse-schedule]]) cites — designed to be read with arXiv:1609.03543v5 open. Section/appendix numbering below matches the version Abram is reading (confirmed: 4.3.8's proof is D.5 there and here). `main.tex:<line>` references are to `references/logical-induction/main.tex` for grep; short verbatim quotes are given as visual anchors for the PDF. The archival record of the erratum is [[li-paper-erratum]]; this page restructures it as a walkthrough and adds the D.4 mechanism findings of 2026-07-31.*

---

## 0. What actually needs vetting — smaller than "the erratum"

Theorem SS cites **corrected 4.8.16**, which is the *printed* 4.8.16 **plus** an extra hypothesis (support of the weighting ⊆ image of the deferral function) and two symbol repairs (Aₙ→Bₙ, w→w̄). It never cites 4.8.15 in any form.

Two consequences for the vetting:

1. **You cannot shortcut via "fewer hypotheses, a fortiori."** If the printed 4.8.16 is *false as printed* (too strong — no support clause), citing it establishes nothing. The truth of corrected 4.8.16 must come from somewhere, and it does: from 4.5.10 (whose printed statement carries the clause) plus the reduction in E.12. Those two are the load-bearing checks (§3–§4).
2. **The other half of the erratum — clause-free 4.8.15 — is not load-bearing for Theorem SS.** It is load-bearing for Half 1 and Theorem A elsewhere in the corpus, so it is covered separately and more briefly (§5).

So the minimal claim to vet is: **"corrected 4.8.16 is a theorem, certified by the paper's own appendix."** Everything else is context.

## 1. The checks, in order (the five-minute map)

1. Read printed 4.8.15 and 4.8.16 side by side; confirm the visible defects (§2).
2. Read printed 4.5.9 and 4.5.10; confirm the clause sits where the erratum says (§3).
3. Read E.12; confirm it is a valid proof of the *corrected* 4.8.16 and an invalid proof of the printed one (§4).
4. Spend the real time in D.4 — the only proof with content; everything else is reduction (§4.1).
5. If vetting Half 1 too: E.11 and D.1 (§5).
6. Map corrected 4.8.16's hypotheses onto Theorem SS's named hypotheses (§6).
7. Falsifiers: what finding would kill what (§7).

## 2. Check A — the printed statements and their visible defects

**Open Theorem 4.8.15 (Expectation Recurring Unbiasedness)** — `main.tex:1812–1820`. You should see, verbatim in the hypothesis:

> "…and $\overline w$ is a $\overline{\mathbb P}$-generable divergent **weighting weighting** such that the support of $\overline w$ is contained in the image of $f$…"

Two defects visible with no interpretation: the doubled word, and **$f$ is free** — 4.8.15 declares no deferral function, so the printed statement is unparseable. Corroborating detail: 4.8.15 is the only theorem in §4.8 with no "Proof in:" pointer, though its appendix section (E.11) exists and is labelled.

**Open Theorem 4.8.16 (Expectation Unbiasedness From Feedback)** — `main.tex:1822–1832`. You should see: a deferral function $f$ *is* declared (the variable the clause above needed); the timing condition reads "$\operatorname{Val}_\Gamma(A_n)$ can be computed in time $\mathcal O(f(n{+}1))$" although the theorem's sequence is $\overline B$ (the macros: `\aff` $=A$ at `main.tex:164`, `\affluv` $=B$ at `main.tex:167` — an un-renamed symbol from the affine parent); and **no support clause**.

*What this establishes:* the printed expectation pair is textually damaged and, in the support clause, differs from its affine parents. It does not yet establish which way to repair it — that is §3–§4.

## 3. Check B — the affine parents, where the clause actually lives

**Open Theorem 4.5.9 (Affine Recurring Unbiasedness)** — `main.tex:1469–1478`. Hypotheses: $\overline A \in \mathcal{BCS}$ determined via $\Gamma$; $\overline w$ a generable divergent weighting. **No deferral function, no support clause.** Conclusion: the weighted average error "has 0 as a **limit point**."

**Open Theorem 4.5.10 (Affine Unbiasedness from Feedback)** — `main.tex:1480–1490`. Hypotheses: determinacy; "a strictly increasing deferral function $f$ such that $\operatorname{Val}(A_n)$ can be computed in time $\mathcal O(f(n{+}1))$"; **and** "a generable divergent weighting $\overline w$ such that the support of $\overline w$ is contained in the image of $f$." Conclusion: $\eqsim_n 0$ — a **full limit**.

**Open the propositional pair 4.3.6 / 4.3.8** (`main.tex:1225`, `main.tex:1249–1260`): same split — 4.3.6 clause-free with limit point; 4.3.8 carries the deferral function, the computability condition, and the support clause, with full limit.

*What this establishes:* in **both** other levels of the six-member family, the Recurring column is clause-free/limit-point and the From-Feedback column carries clause+timing/full-limit. Only the printed expectation pair breaks the pattern — in exactly the way a copy-paste that dropped the clause onto the wrong theorem would, with the un-renamed $A_n$ as the fingerprint.

| level | Recurring (clause-free, limit point) | From Feedback (clause + timing, full limit) |
|---|---|---|
| propositional | 4.3.6 | 4.3.8 (proof: D.5, "special case of 4.5.10") |
| affine | 4.5.9 (proof: D.1) | **4.5.10 (proof: D.4 — the content)** |
| expectation | 4.8.15 (proof: E.11) | **4.8.16 (proof: E.12)** |

## 4. Check C — E.12 certifies the corrected 4.8.16

**Open appendix E.12** — `main.tex:5260–5282`. The entire proof: fix a world; "Apply Theorem `wubaff` [4.5.10] to $(\alpha_n(B_n))_n$" — noting first that "if $\operatorname{Val}(B_n)$ can be computed in time polynomial in $g(n+1)$, then so can $\operatorname{Val}(\alpha_k(B_n))$" (the timing condition transfers through the α-encoding); then Lemma `conluvapprox` converts world-expectations to $\operatorname{Val}$ at cost $b/n \to 0$.

The one thing to notice: **4.5.10's hypotheses include the support clause, and E.12 passes the weighting through unchanged.** So E.12 is a *valid* proof of 4.8.16-with-the-clause and an *invalid* proof of 4.8.16-as-printed — it silently consumes a hypothesis the printed statement does not carry. This is the erratum, certified by the paper's own appendix rather than by anyone's reading.

Two small legality items to confirm while there: the α-encoding keeps $\|\alpha_n(B_n)\|_1$ bounded (needed for 4.5.10's WLOG normalization at `main.tex:4734`), and the reindexing keeps the progression e.c.

### 4.1 Check C′ — D.4, the only proof with content (spend the time here)

D.5 and E.12 are one-step reductions; **everything real is in appendix D.4** (`main.tex:4733–4835`), the proof of 4.5.10. Walkthrough with the checkpoints:

1. **`main.tex:4737–4742`** — the proof's first move defines $\mathrm{Bias}_k$ **summing over the image of $f$ only**, and says "we need only consider the sum over $n$ in the support of $f$." *This is the support clause being used essentially, in the proof's second sentence.* A reader who wants one line of evidence that the clause belongs to this theorem: this is it.
2. **`main.tex:4749–4764`** — the trader. On day $f(i)$: buy $\beta_i = \varepsilon\cdot\mathrm{Wealth}_i\cdot w_i$ copies of $A_{f(i)}$; on day $f(i{+}1)$: sell them back at the then-current price (the second, negative term of $T_n$). A **round trip** — profit is realized cash from the market's own price movement; no bet is ever held to settlement. Check the rank/e.c. legality note at `main.tex:4765`, and that the weighting enters *only* as the black-box factor in $\beta_i$ (this is what makes the relativization obligation (R) light).
3. **`main.tex:4772–4773`** — the Kelly floor: "$T$'s minimum worth is bounded below by $-1$" *in any plausible world*, because at most an $\varepsilon$-fraction of wealth is staked and only one position is open. **No settlement, no decision by $D$, is needed for boundedness below.**
4. **`main.tex:4775–4811`** — the log-wealth ledger and the inequality $\log(1+x)\ge x - x^2$. Pure algebra; two cosmetic index slips in the vicinity (a $j$ where an $i$ is meant at `main.tex:4790`; a $\mathbb P_{f(i)}$ for $\mathbb P_{f(j)}$ inside the absolute value at `main.tex:4797`) — do not be alarmed by them; the computation is right.
5. **`main.tex:4813–4823`** — the single point of contact with truth. The auxiliary sequence $A'_n := A_{f(i)} - \operatorname{Val}(A_{f(i)})$ at days $n = f(i{+}1)$ "is in $\mathcal{BCS}$ **because** $\operatorname{Val}(A_{f(j)})$ is computable in time polynomial in $f(j{+}1)$" (`main.tex:4820`) — *the only consumption of the timing condition in the entire proof* — and then **Affine Provability Induction** (`affprovind`) gives $\mathbb P_{f(j+1)}(A_{f(j)}) \eqsim \operatorname{Val}(A_{f(j)})$: the market's own later price is the settlement instrument. Confirm `affprovind`'s own statement (appendix B.1, `app:affprovind`) carries no rate or patience hypothesis — settlement timing is quarantined there, rate-free.
6. **`main.tex:4824–4834`** — endgame: persistent bias $< -3\varepsilon$ infinitely often makes $\log\mathrm{Wealth}$ exceed $\varepsilon^2\sum w_j - C$ infinitely often; divergent weighting ⟹ unbounded wealth ⟹ exploitation.

*The moral for the timing question (Abram's, 2026-07-31, confirmed here):* the hypotheses are exactly (a) the feedback eventually arrives — Γ-decidability, consumed only inside rate-free PI — and (b) the feedback **can be computed** schedule-promptly, consumed only at checkpoint 5. There is no decision-rate hypothesis anywhere. Contrast the *next* proof, D.6, whose trader builds an explicit settlement tracker ($\mathrm{DefinitelySettled}$, `main.tex:4857+`) and waits — and which is exactly the column (family C) that carries the $f$-**patience** hypothesis instead. The paper's two timing hypotheses are the shadows of its two trader designs.

## 5. Check D — the other half (clause-free 4.8.15), only if vetting Half 1 / Theorem A

**Open E.11** (`main.tex:5240–5258`): "Apply Theorem `recunbiasedaff` [4.5.9] to $(\alpha_n(B_n))_n$ and $\overline w$" — the weighting passes through unchanged to the clause-free 4.5.9; $f$ is never mentioned. **Open D.1** (`main.tex:4558–4675`): 114 lines proving 4.5.9 with no deferral function anywhere (grep `\deff` in that range: no hits). So clause-free 4.8.15 is likewise certified by the paper's own appendix. Direction warning, easy to get backwards: the swap makes **4.8.15 stronger** (spurious hypothesis removed) and **4.8.16 weaker** (restriction added). And 4.8.15's conclusion is a **limit point**, never a limit — the corpus has slipped on this before ([[li-paper-erratum]] §1, end).

*Label-drift note:* v3 and [[joint-clearing-and-trader-class]] refer to "appendix D.2's proof" for 4.8.15's relativization obligation; in this version the content proof is **D.1** (D.2 is the propositional special case). Same species of check either way.

## 6. Check E — mapping corrected 4.8.16's hypotheses onto Theorem SS

| corrected 4.8.16 hypothesis | Theorem SS instantiation | where checked |
|---|---|---|
| $\overline B \in \mathcal{BLCS}(\overline{\mathbb P})$ | $\overline{\ulcorner Y\urcorner}$, program-encoded | (S1) for $A$; (S2) for $H$ — [[route-sparse-schedule]] §2 |
| determined via $\Gamma$, $\operatorname{Val} = Y_n$ | coupled system computable, $\Gamma \supseteq$ PA represents computations | (S1)/(S2) |
| strictly increasing deferral function $g$ | Lemma 1's schedule | [[route-sparse-schedule]] §3(a),(c) |
| $\operatorname{Val}(B_n)$ computable in $\mathcal O(g(n{+}1))$ | $T$-bound on running the coupled system to day $f(n)$ | Lemma 1(b) — computation time only, per §4.1 above |
| $\overline w$ generable divergent | quote-ramp × schedule indicator; for $H$ under (L) | [[route-sparse-schedule]] §4.1, §5.2; divergence = case split §7 |
| support $\subseteq \operatorname{im}(g)$ | by construction | trivially |
| the theorem holds for $H$'s relativized class | (R): weighting is black-box in D.4 (checkpoint 2) + `affprovind` relativizes | [[route-sparse-schedule]] §2(R), skeptic item 2 (resolved form) |

## 7. Falsifiers — what finding would kill what

- **If 4.5.10's printed statement lacked the support clause** → the pattern argument collapses. (It doesn't — §3, quoted.)
- **If D.4 nowhere used the support restriction** → the clause would be superfluous, printed 4.8.16 possibly fine — Theorem SS survives unchanged (it satisfies the clause anyway), but the erratum's 4.8.16-half would be wrong. (It is used in the proof's second sentence — §4.1 checkpoint 1.)
- **If `affprovind` carried a rate or patience hypothesis** → D.4's settlement quarantine fails and the timing condition would be under-strength — this *would* threaten Theorem SS. (Check it: `app:affprovind`; it doesn't.)
- **If E.12's timing-transfer step ("so can $\operatorname{Val}(\alpha_k(B_n))$") failed** → corrected 4.8.16 unproven at the expectation level even granting 4.5.10 — check the α-encoding cost.
- **If D.1 secretly used a deferral function** → clause-free 4.8.15 unproven → **Half 1 and Theorem A** in trouble (not Theorem SS).

## Related

- [[li-paper-erratum]] — the archival record (statements, provenance, the 4.4.4 sign transposition, numbering corrections)
- [[route-sparse-schedule]] — the theorem this guide serves; §1 feedback ladder, §3 mechanism remark
- [[unbiasedness-theorem-families]] — the family sorting the six-member grid lives in
- [[varying-question-synthesis]] — the surrounding exploration; file map at the end
