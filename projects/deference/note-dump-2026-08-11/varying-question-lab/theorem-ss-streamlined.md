# Theorem SS, streamlined: three citations, one arbitrage lemma, and arithmetic

*Claude, 2026-07-31, from Abram's read-through of [[route-sparse-schedule]]; revised the same day per Abram's preferences — the human-side bridge is proved by existing LI theorems rather than a bespoke strategy (the trader survives as a hypothesis-thinning remark), and the lemmas are numbered in the order the chain uses them, L1→L4 from the human's credence outward. A fresh, self-contained presentation of the scheduled quote–credence agreement / Tower-form theorem. The schedule construction, the legality analyses, and the feedback ladder all remain in [[route-sparse-schedule]] and are cited rather than duplicated. Conventions: [[conventions-and-status-labels]]; terminology per the 2026-07-31 rules (weighting, above-/below-threshold inequality).*

---

## 0. Statement

**Setting** (full detail: [[route-sparse-schedule]] §1). Two logical inductors under one-way sequential clearing: each day, $A$'s market clears against its own prices; $A$ publishes its forecast into $H$'s deductive process as decided ledger atoms (value-atoms of the quote-naming LUV, decided same-day to precision $1/n$); then $H$ clears. $(X_n)$ is an e.d. sequence of $[0,1]$-LUVs of $H$'s language; $f$ is the lookahead ($f(n)>n$, canonically $2^n$).

**Named hypotheses.**

- **(S1)** — standing, $A$-side only: the sequence of quote targets $\ulcorner\mathbb E^H_{f(n)}(X_n)\urcorner$ is $\mathcal{BLCS}(\overline{\mathbb P}^A)$ and determined via $\Gamma_A$, with value $\mathbb E^H_{f(n)}(X_n)$.
- **(SCHED)** — the evaluation-sparse schedule $g$ of [[route-sparse-schedule]] §3 Lemma 1: strictly increasing deferral function with the target's value computable in time $O(g(k{+}1))$ and poly-time membership test; its gaps exceed $f$, so **at most one lookahead window is ever open across schedule days** (window-disjointness, automatic).
- **(L)** — ledger access: $H$ satisfies the logical-induction criterion against $\mathrm P^L$, poly-time traders with lookup access to the published quote stream; the schedule weighting, read off the ledger, is $\mathrm P^L$-generable.
- **(S2′)** — mild mirror determinacy, used only by the citation-based L2: $\Gamma_H\supseteq$ PA represents computations and $\mathcal L_H$ describes the (computable) coupled system, so the target sequence is $\mathcal{BLCS}(\overline{\mathbb P}^H)$ and determined via $\Gamma_H$ — automatic by $\Sigma_1$-completeness given the language ([[route-sparse-schedule]] §2's remark; ~0.95). *Removable*: the trader-based variant (§3's remark) needs neither this nor (R′).
- **(R′)** — the $H$-side 4.8.16 is read against the $\mathrm P^L$ class. Status much improved by the D.4 source-check: the constructed trader consults the weighting only as black-box bet sizing (`main.tex:4749–4764`), so what remains is relativized `affprovind` — the same species of fact the setting needs everywhere. *Also removable by the trader variant.*
- **Paper inputs**: corrected 4.8.16 ([[li-paper-erratum]] §1; vetting: [[li-erratum-vetting-guide]]), applied to **both** markets — verbatim for $A$, (R′)-relativized for $H$; and `cee` 4.12.1, which applies to $H\dashv\mathrm P^L$ **verbatim with no relativization**: its proof constructs plain e.c. traders, and inexploitability against the larger class $\mathrm P^L$ implies inexploitability against the subclass.

**The weighting.** For rational $t$, $\delta>0$: $w_i := \operatorname{Ind}_\delta\big(\mathbb E^A_i(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner) > t\big)\cdot\mathbb 1[i\in\operatorname{im}(g)]$ — one sequence of rationals with two legality certificates: native for $A$ (a ramp on a rational combination of $A$'s own day-$i$ prices), ledger-lookup for $H$ under (L). Same numbers on both sides, which is what lets the averages subtract.

> **Theorem SS (streamlined).** For every e.d. sequence $(X_n)$ of $[0,1]$-LUVs, every rational $t\in[0,1]$ and rational $\delta>0$: if $\sum_i w_i=\infty$, then
> $$\frac{\sum_{i\le n} w_i\Big(\mathbb E^H_i\big(\ulcorner\, \mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\,\urcorner\big) \;-\; \mathbb E^H_i(X_i)\Big)}{\sum_{i\le n} w_i}\;\eqsim_n\;0\qquad\textbf{(Tower form, two-sided full limit)}$$
> and equivalently with the published number $\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)$ in place of the outer $\mathbb E^H_i(\ulcorner\cdot\urcorner)$ **(agreement form)**. If $\sum_i w_i<\infty$, then $w_i\to0$ along the schedule and every displayed per-day quantity vanishes there, so the unnormalized forms hold with an additive constant. Both one-sided inequalities of scheduled soft Total Trust follow, and a menu form (§8).

**The proof in one line.** The human's present credence is its present *self-forecast* (`cee` — L1); that self-forecast is unbiased for the realized future credence given schedule-prompt feedback (4.8.16 applied to $H$ — L2); the forecaster's market must learn the same target (4.8.16 applied to $A$ — L3); and a market's estimate of a published number is that number (the readability collapse — L4, packaging the result in Tower form). All conclusions are full limits against the same weighting, and full limits add. Reading from the human's credence outward:

$$\mathbb E^H_i(X_i)\;\underset{\text{L1}}{\eqsim_i}\;\mathbb E^H_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\;\underset{\text{L2}}{\approx_{\bar w}}\;\mathbb E^H_{f(i)}(X_i)\;\underset{\text{L3}}{\approx_{\bar w}}\;\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\;\underset{\text{L4}}{\eqsim_i}\;\mathbb E^H_i\Big(\ulcorner \mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\urcorner\Big)$$

---

## 1. The common notion, and the one combination rule

For a weighting $\overline w$ with $W_n:=\sum_{i\le n}w_i\to\infty$, write $x\approx_{\bar w}y$ for: the $w$-weighted average of $x_i-y_i$ tends to $0$ (full limit). Two facts carry the whole assembly:

1. **Same-$\overline w$ additivity.** $x\approx_{\bar w}y$ and $y\approx_{\bar w}z$ give $x\approx_{\bar w}z$ — algebra of real sequences, valid because all three averages use the *same* numeric weights and normalizer.
2. **Per-day is a universal donor.** If $x_i-y_i\to0$ and is bounded, then $x\approx_{\bar w}y$ for **every** divergent-mass $\overline w$: given $\eta$, split the sum at the day $|x_i-y_i|<\eta/2$; the head is a constant, washed out by $W_n\to\infty$. So per-day full limits (L1, L4) enter any averaged context free of parameter-matching.

The theorem's engineering reduces to: L2 and L3 must be stated against the *same* $\overline w$ (they are — one number sequence, one schedule; the schedule can serve both because the quantity fed back is one and the same object, the human's day-$f(i)$ expectation), and all conclusions must be full limits (they are — which is what rules out 4.8.15 and its non-combining limit points).

---

## 2. L1 — the human's present credence is its present self-forecast (`cee`, free)

> **Lemma L1 (`cee`, Expected Future Expectations, 4.12.1 — per-day, free).**
> $$\mathbb E^H_i(X_i)\;\eqsim_i\;\mathbb E^H_i\Big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\Big).$$
> *Hypotheses checked:* $f$ is a deferral function; $(X_i)$ e.d. — exactly `cee`'s quantifiers, varying questions included. Applies to $H\dashv\mathrm P^L$ **verbatim** (plain-trader proof; subclass argument in §0). Enters the average by the donor rule.

---

## 3. L2 — the self-forecast is unbiased for the realized future credence (4.8.16 at $H$)

No *single* LI theorem gives "present credence tracks realized future credence": the per-day form is **false** in general (that surprise exists is the whole subject), and the paper's only instruments pairing a present price with a later *realized* value in averaged form are the unbiasedness family, which need a determined target. Hence the split into L1 (free self-trust) and this lemma (self-forecast unbiasedness).

> **Lemma L2 (corrected 4.8.16, applied to $H$).** Under (S2′), (SCHED), (L), (R′), if $\sum_i w_i=\infty$:
> $$\frac{\sum_{i\le n} w_i\Big(\mathbb E^H_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)-\mathbb E^H_{f(i)}(X_i)\Big)}{\sum_{i\le n} w_i}\;\longrightarrow\;0\qquad\text{(two-sided full limit).}$$
> *Hypotheses checked:* the target $\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner$ is $\mathcal{BLCS}(\overline{\mathbb P}^H)$ and $\Gamma_H$-determined with value $\mathbb E^H_{f(i)}(X_i)$ — (S2′); the deferral function is (SCHED)'s $g$, and the timing condition is the **same** Lemma 1(b) bound as on the $A$-side, since it is the same value being fed back; the weighting is $\mathrm P^L$-generable — (L); support $\subseteq\operatorname{im}(g)$ by construction; the theorem for the $\mathrm P^L$ class — (R′).

In words: *the human's self-forecast of its own future credence is unbiased for the realized future credence, on any schedule that gives its traders computable feedback* — the same statement L3 makes about the forecaster, applied reflexively. The pleasing symmetry of the citation route: **both averaged halves are the same theorem**, once about $H$'s forecast of its own future, once about $A$'s forecast of the same future.

**Remark (hypothesis thinning — the trader variant).** Both (S2′) and (R′) are *removable*: a bespoke Kelly round-trip trader — buy $X_i$'s expectation-bundle at day $i$, sell at day $f(i)$, stake $\eta\cdot\mathrm{Wealth}\cdot w_i$, at most one trip open by window-disjointness, worth $\ge-1$ in every world with no settlement consulted, $\log(1+x)\ge x-x^2$ ledger — proves the fused statement $\mathbb E^H_{f(i)}(X_i)\approx_{\bar w}\mathbb E^H_i(X_i)$ (L1+L2 in one step) directly from the criterion, with no determinacy and no theorem citation (this file's first revision; template = D.4's own accounting, per [[li-erratum-vetting-guide]] §4.1; cf. [[route-recurring-ccee]] Thm 5.2). The citation route is primary per Abram's preference (2026-07-31): standard theorems over bespoke strategies; the trader remark is the proof that the extra hypotheses are conveniences, not necessities. *The remark's analytic engine is KERNEL-CHECKED (`lean-deference/StreamlinedSS.lean`, part T2), with two corrections to earlier drafted constants: the honest quadratic term in the log-wealth ledger is $4\eta^2W_n$ with **no** additive $O(1)$ (unboundedness threshold $5\eta$, not $3\eta$), and the mesh errors need $|\epsilon_i|\le1$ at **every** day — the $|x|\le\tfrac12$ side condition of the log inequality is per-day, not eventual.*

---

## 4. L3 — the forecaster's market learns the same target (4.8.16 at $A$)

> **Lemma L3.** Under (S1) and (SCHED), if $\sum_i w_i=\infty$:
> $$\frac{\sum_{i\le n} w_i\Big(\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)-\mathbb E^H_{f(i)}(X_i)\Big)}{\sum_{i\le n} w_i}\;\longrightarrow\;0\qquad\text{(two-sided full limit).}$$

*Proof.* Corrected 4.8.16 applied to $A$'s market with target sequence $\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner$: determinacy and $\mathcal{BLCS}$ membership are (S1); the deferral function is (SCHED)'s $g$, whose timing condition (target computable in $O(g(k{+}1))$) is Lemma 1(b) of [[route-sparse-schedule]]; the support of $\overline w$ is in $\operatorname{im}(g)$ by construction; and $\overline w$ is $\overline{\mathbb P}^A$-generable natively — the quote is a rational combination of $A$'s own day-$i$ prices (Def. 4.8.2), the ramp is an expressible feature (Def. 4.3.2's closing remark), the schedule indicator is e.c. (Lemma 1(d)). **No relativization is involved in this application: $A$ is a plain market and every hypothesis is checked against the paper as printed (in the erratum-corrected form).** $\square$

*The mechanism, for intuition (source-checked at [[li-erratum-vetting-guide]] §4.1):* D.4's exploiting trader is itself a round-trip Kelly trader — L3 and L2 are the same organism, except that D.4's seller exits at a price that rate-free Provability Induction has pinned to the *computable true value*, which is where (S1) and the timing condition are consumed. The feedback ladder discussion ([[route-sparse-schedule]] §1) applies verbatim.

---

## 5. L4 — the readability collapse: a market's estimate of a published number is that number

> **Lemma L4.** Under (L) and same-day publication: $\mathbb E^H_i\Big(\ulcorner \mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\urcorner\Big)\;\eqsim_i\;\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)$ — per-day, full limit.

*Proof.* Write $\alpha_i$ for the LUV of $H$'s language naming the quote (poly-size template plus numeral plus program code — cheap to *describe*, hard to *evaluate*). By the publication step, the day-$i$ ledger contains $\alpha_i$'s value-atoms decided to precision $1/i$; hence **every** world propositionally consistent with $D_H^{\,i}$ assigns $\alpha_i$ a value within $1/i$ of the published number $q_i$. Suppose $\mathbb E^H_i(\alpha_i)<q_i-\varepsilon$ infinitely often, for some rational $\varepsilon>0$. The trader that, on each such day, buys one unit of $\alpha_i$'s expectation-bundle (appendix A.3; bundle payoff within mesh $1/i$ of the LUV's value) at price $\mathbb E^H_i(\alpha_i)$ holds a position whose value **in every plausible world, the same day,** is at least $q_i-1/i-\mathbb E^H_i(\alpha_i)-1/i\ge\varepsilon-2/i$. Recognizing the buying days is a poly-time ledger computation — this is where (L)'s trader-level half is consumed. Accumulated plausible worth is bounded below by $0$ and grows by $\ge\varepsilon/2$ per instance: exploitation. The criterion forbids it; the mirror trader gives the other side. $\square$

*Remarks.* No settlement is waited for — the atoms are already decided when the trade is placed; no $\Gamma_H$-determinacy, no provability-induction citation is needed (though `expprovind` 4.8.10, relativized, packages the same fact if a citation is preferred). This lemma is *the* degeneracy of a readable expert: it is why the Tower form and the agreement form coincide here, and why headlining either alone is a choice of emphasis, not of content.

---

## 6. Assembly

All conclusions are statements about one numeric weighting $\overline w$. L1 and L4 are per-day, hence $\approx_{\bar w}$ by the donor rule; L2 and L3 are natively $\approx_{\bar w}$. Chain by same-$\overline w$ additivity, in lemma order:

$$\mathbb E^H_i(X_i)\;\approx_{\bar w}\;\mathbb E^H_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\;\approx_{\bar w}\;\mathbb E^H_{f(i)}(X_i)\;\approx_{\bar w}\;\mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\;\approx_{\bar w}\;\mathbb E^H_i\Big(\ulcorner \mathbb E^A_i\big(\ulcorner \mathbb E^H_{f(i)}(X_i)\urcorner\big)\urcorner\Big).$$

The outer ends give the Tower form; dropping the last link gives the agreement form. In the finite-mass case ($\sum w_i<\infty$) the terms $w_i$ vanish along the schedule and each per-day product vanishes with them. $\blacksquare$

---

## 7. The two variants, and what each costs

| ingredient | citation-based (primary, this page) | trader-based (the §3 remark) |
|---|---|---|
| L3: 4.8.16 applied to $A$ | required | required |
| $H$-side of the bridge | L1 (`cee` 4.12.1, verbatim) + L2 (4.8.16 applied to $H$) | one bespoke Kelly round trip (fuses L1+L2) |
| (S2′) mild mirror determinacy | required (~0.95, $\Sigma_1$-completeness) | **not needed** |
| (R′) $H$-side 4.8.16 for $\mathrm P^L$ | required (much improved by the D.4 inspection) | **not needed** |
| ledger collapse to Tower form | L4, decided-atom arbitrage (citation-free; or relativized 4.8.10) | same |
| un-refereed bespoke surface | L4 only | L4 + the Kelly accounting |

The trade: the citation route maximizes reliance on refereed theorems and exhibits the pleasing symmetry (both averaged halves are 4.8.16, applied to each market's forecast of the human's future); the trader route minimizes hypotheses. Both share (S1), (SCHED), (L), one-way clearing with same-day publication, the divergence case split, and every scope caveat (scheduled, averaged, per-question, rate-free; honest-not-sound; nothing off-schedule). Relative to the original assembly in [[route-sparse-schedule]] §§4–8, the citation route is the same three applications repackaged — its genuine additions are the Tower-form packaging via L4, the explicit chaining discipline of §1, and the recorded removability of (S2′)/(R′).

## 8. Corollaries

**Soft Total Trust, both one-sided inequalities, scheduled and averaged.** On $\overline w$'s support the ramp has no false positives, so $w_i\cdot\mathbb E^A_i\big(\ulcorner\mathbb E^H_{f(i)}(X_i)\urcorner\big)\ge t\,w_i$ pointwise; combined with the agreement form, the $w$-weighted average of $\mathbb E^H_i(X_i)$ is $\ge t-o(1)$. The below-threshold inequality re-runs everything with the mirror ramp $\operatorname{Ind}_\delta(\cdot<t)$ — a genuinely separate application (averaged statements are relative to their weighting; every hypothesis re-checks identically). For the official form with the weight inside the corner quotes, the difference-bundle $\ulcorner X_i\cdot w_i\urcorner-w_i\cdot X_i$ is pinned near $0$ in every day-$i$-plausible world (the ledger decides $w_i$'s value to Lipschitz error $O(1/(\delta i))$), so the same decided-atom arbitrage as L4 equates the two readings — still trader-level only.

**Band reading, all thresholds at once.** Quantifying over rational $(t,\delta)$ — one schedule serves all — on scheduled days when the forecaster quotes confidently in a band, the human's credence averages into that band: no persistent average bias at any level, in either direction.

**Value (recorded 2026-07-31, in answer to Abram's question; the general-menu claim is NEW and unvetted).** Two levels:

- *Two-option menus: exact transport.* The two-option identity of [[two-option-value-iff-total-trust]] is a per-day algebraic identity between the Value difference on the menu $\{X_i,\ \text{const } t\}$ and the Total-Trust threshold difference at $t$ — so it survives any weakening verbatim: the scheduled averaged TT inequalities above **are** scheduled averaged two-option Value, same weighting, same schedule, both directions. The weak notions sit in the same equivalence pattern as the strong ones.
- *General finite menus: conjectured transport, with a twist (~0.7).* The Mart⟹Value route ([[mart-implies-value]]) applies the agreement form to the followed strategy $\widehat S_i$ and to each fixed option $O^j_i$ — both e.d. sequences, so Theorem SS covers them — against a **common** weighting (e.g. the bare schedule indicator; no threshold ramp is needed for Value). The usually-problematic step, F1 ($E^\ast(\widehat S) = \max_j E^\ast(O^j)$ — the self-endorsement that forced the deck's Regularity hypothesis), appears to become **free for the lookahead expert**: the selection is by *published* quotes with a ledger-decided tie-break, so "$\widehat S_i = O^{j^\ast}_i$" is decided data and the quote of the followed strategy provably near-equals the max quote — the readability collapse degenerating F1 exactly as L4 degenerated the Tower's inner layer and Lemma B degenerated soft conditioning. Conjectured conclusion: **scheduled weighted-average Value over arbitrary e.d. bounded menus, with no decision-theoretic scope condition**, the Newcomblike pathologies being absorbed into the honest averaged quotes (selection-referencing menus should land in the degenerate pinned stratum rather than refuting the statement — the [[total-trust-implies-value]] counterexample targeted the expert's *internal conditional* expectations, which this route never touches). Needs: the F1-for-lookahead near-identity written out (tie-break hygiene per [[ledger-decided-tie-breaks]]), and a stress test against the selection-referencing counterexample. Not claimed as a theorem yet.

  ⚠ **REFUTED as stated (2026-08-03) — the stress test failed.** The constant-probe punishing menu $\{\mathbb 1[\mathrm{sel}_i = 2],\ \text{const } s\}$ of [[loop-direction]], run against the lookahead expert in this theorem's own setting, kills the no-scope-condition form: "$\widehat S_i = O^{j^\ast}_i$ is decided data" holds for $\Gamma$ and for the day-$f(i)$ human, but **not for $A$ same-day** — $A$'s access to its own argmax is introspective, the punishing fixed point hovers with interior self-prediction mass, and $A$'s forecast of the *selected* option's future credence is a mass-weighted mixture ($\to s^2$), not the max ($\to s$). Scheduled averaged argmax Value then fails by $s(1-s)$ on the bare schedule weighting, while Theorem SS itself still holds at $\widehat S_i$ — the failure is instrumental (F1), not epistemic. **Averaging launders oscillation, not bias.** What survives: the two-option/hedged transport above (exact), and the repaired conjecture under a lookahead-adapted conditional-stability condition or decisive quote-margins (~0.8). Full computation and the repaired statement: [[weak-loop-and-value-transport]] §1.

## 9. Status, and what a skeptic should attack first

**PROVED modulo named hypotheses.** Citation route: **~0.84** ((R′) improved by the D.4 inspection; (S2′) mild; L4 the only bespoke piece). Trader route: **~0.85** (fewest hypotheses; bespoke surface L4 + the Kelly accounting). Skeptic's order of attack:

1. **(R′) written out** — relativized `affprovind` for the $\mathrm P^L$ class; the weighting-as-black-box half is already verified by inspection (`main.tex:4749–4764`).
2. **L4's precision bookkeeping** — atoms to $1/i$, bundle mesh $1/i$, and the same-day publication convention $e(n)=n$ (any $e(n)\le n$ works with the weighting read at $e^{-1}$).
3. **The Kelly accounting of the §3 remark** (trader route only) — the mesh error inside the logarithm: **KERNEL-CHECKED** (`StreamlinedSS.lean` T2, with corrected constants — §3 remark). What remains un-formalized of the trader route is the market-facing step (worth $\ge-1$ with a single open window; trader legality), per the honesty caveat.
4. **Non-vacuity** — the pair $(H\dashv\mathrm P^L, A)$ exists: the paper's §5 construction for $A$ verbatim, and a relativized §5 for $H^+$ (~0.85; strictly cheaper than any joint construction).
5. **The §8 Value conjecture** — the F1-for-lookahead near-identity and the selection-referencing stress test.

**Formal verification (2026-07-31, independently rebuilt): `lean-deference/StreamlinedSS.lean` — KERNEL-CHECKED**, Lean 4 / Mathlib v4.27.0, sorry-free, all 26 audited theorems on axioms `[propext, Classical.choice, Quot.sound]`. Covered (Lean part-labels T1–T5 predate the L-renumbering): the $\approx_{\bar w}$ calculus and the universal donor rule (T1 — §1 here); the Kelly ledger, mesh absorption, and unboundedness engine (T2 — the §3 remark); the arbitrage engine of L4, with `NoArb` shown genuinely refutable (T3 — §5); the full assembly `theorem_SS` from market-level named hypotheses, with a joint-satisfiability witness, plus the finite-mass case (T4 — §6); and the above-threshold Total-Trust corollary arithmetic with the ramp indicator (T5 — §8). Per the standing Lean honesty caveat ([[conventions-and-status-labels]]): the market, traders, legality, the schedule construction, and 4.8.16 itself are unmodeled — they enter exactly as the named hypotheses. A byproduct correction to [[route-sparse-schedule]] §7 Lemma 2 is recorded there.

## Related

- [[route-sparse-schedule]] — the original assembly, the schedule construction (Lemma 1), the feedback ladder, the (L) analysis, and the exact statement of what joint clearing buys instead
- [[route-recurring-ccee]] §5.4 — Thm 5.2, the round-trip bridge behind the §3 remark; Prop 5.3, why sparsity is forced
- [[li-erratum-vetting-guide]] — vetting the 4.8.16 citations against the paper
- [[two-option-value-iff-total-trust]], [[mart-implies-value]], [[total-trust-implies-value]], [[ledger-decided-tie-breaks]] — the Value transport of §8
- [[eisenstat-lookahead-construction]] — where this result sits among the claims about the lookahead construction
- [[varying-question-synthesis]] — the surrounding exploration; file map at the end
