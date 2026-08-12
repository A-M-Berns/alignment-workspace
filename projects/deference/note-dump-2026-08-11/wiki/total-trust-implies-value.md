# Total Trust ⟹ Value (true LI setting)

*The theorem, stated and proved with expectations as the LI paper defines them: **Total Trust + introspection + conditional-stability ⟹ argmax Value.** Two lemmas: bounds transfer (proved) and self-endorsement (proved modulo one named item). Some scope condition is provably necessary — a selection-punishing menu refutes unconditional argmax Value outright. **Unvetted by Abram as of 2026-07-26.** Side material lives elsewhere: the $\delta$-hedged variant at [[soft-self-endorsement]], the survey of rejected exogeneity definitions at [[defining-exogeneity]], the earlier surrogate-formulation cluster at [[total-trust-implies-value-telescoping]].*

## Setting

$\Gamma$ a theory as in [[setting-and-notation]], with its deductive process; $H \dashv \mathcal{C}_H$ and $A \dashv \mathcal{C}_A$ logical inductors over $\Gamma$ (novice and expert). For an $[a,b]$-LUV $X$, the day-$n$ expectation is the paper's price-integral,

$$ E_n(X) \;:=\; a + \frac{b-a}{n}\sum_{k=0}^{n-1} \mathbb{P}_n\!\Big(X > a + \tfrac{k}{n}(b-a)\Big), $$

the $[0,1]$ definition transported affinely (benign; all bets live in one fixed $[a,b]$, and ramp/Lipschitz constants scale by $(b-a)$). $E^A_n(X)$ and $E^H_n(X)$ are the two inductors' expectations *of the formula $X$*, determined by their prices on its threshold sentences — no other notion of estimate appears on this page.

**Menus and the ledger.** An e.d. sequence of finite menus $\{O^1_n, \dots, O^K_n\}$ of $[a,b]$-LUVs. The expert publishes its quotes to a ledger the novice reads $\mathcal{C}_H$-cheaply as $\Gamma$-decided rational facts — for the options, $m^j_n := E^A_n(O^j_n)$, and also for the strategy bets built from them below (**rich-ledger observability**; with per-option quotes only, composite estimates are unreadable and one is forced back to the surrogate formulation of the earlier cluster). Write $M_n := \max_j m^j_n$. Publication timing ($e(n) \ge n$) is folded into the asymptotics.

**The strategy.** "Hold whichever option the ledger rates highest":

$$ \widehat S_n \;:=\; \textstyle\sum_j c_j\, O^j_n, \qquad c_j := \mathbb{1}[j = j^\ast], \quad j^\ast := \text{least } j \text{ maximizing } m^j_n $$

(any tie-break computable from the quotes; [[ledger-decided-tie-breaks]]). For the novice the $c_j$ are decided constants by trading time. For the expert *at day $n$* they are discontinuous functions of its own same-day quotes, decided only at $e(n) \ge n$ — the self-reference Lemma 2 must handle.

**The goal (Value).** For every fixed index $i$:

$$ E^H_n\big(\widehat S_n\big) \;\gtrsim_n\; E^H_n\big(O^i_n\big), \qquad\text{where } x_n \gtrsim_n y_n :\Leftrightarrow \liminf_n (x_n - y_n) \ge 0. $$

## Hypotheses

**(H1) Total Trust.** For every $(X_n)$ in the quantified e.d. family, every threshold $t$, every ramp width $\delta > 0$:

$$ E^H_n\big(X_n \cdot \operatorname{Ind}_\delta(E^A_n(X_n) > t)\big) \;\gtrsim_n\; t \cdot E^H_n\big(\operatorname{Ind}_\delta(E^A_n(X_n) > t)\big), $$

the ramp's argument being the published quote — readable, hence market-generable as a weight. Full threshold family.

**(H2) Introspection.** The expert asymptotically knows its own quotes: $E^A_n(\ulcorner E^A_n(X)\urcorner) \approx_n E^A_n(X)$, within $o(1)$ ([[expert-conditions]]; `epr`-family for the future-self instance). Used only through Lemma 2's concentration step.

**(H3) Conditional-stability** (Abram, 2026-07-25; mass-weighted one-sided form 2026-07-26) — the scope condition. *Selection is not, on average, bad news about the option selected:*

$$ \sum_j \mathbb{P}^A_n(\mathrm{sel}_n = j)\Big[\,E^A_n(O^j_n \mid \mathrm{sel}_n = j) \;-\; E^A_n(O^j_n)\,\Big] \;\gtrsim_n\; 0. $$

The LI conditional is $E(X \cdot \mathbb{1}_\varphi)/\mathbb{P}(\varphi)$, so each leading product cancels its own denominator and the condition is equivalently, with no division appearing anywhere:

$$ \sum_j E^A_n\big(\mathbb{1}[\mathrm{sel}_n = j]\cdot O^j_n\big) \;\gtrsim_n\; \sum_j \mathbb{P}^A_n(\mathrm{sel}_n = j)\; m^j_n. $$

Three features of this form, each load-bearing:

- **No $\varepsilon$-proviso.** Multiplying by the self-prediction mass instead of dividing by it removes the vanishing denominator, which is the only thing that ever made a "mass $\ge \varepsilon$" side condition necessary. Every quantity appearing is one the expert actually prices, so the condition is a single inequality between two aggregates of $A$'s own beliefs — no subsequences, no thresholds, no uniformity obligation.
- **One-sided.** Only $\gtrsim$ is needed, because Lemma 1 transfers *lower* bounds only and the Theorem needs only $E^A_n(\widehat S_n) \gtrsim_n M_n$. The pathology being excluded is selection being bad news about the selected option; selection being *good* news is harmless and in fact helps (see the clairvoyant tie-break of [[ledger-decided-tie-breaks]], which this form correctly admits — it overshoots Value rather than breaking it).
- **Aggregated over $j$.** Individual gaps may be large provided they cancel. That is not a leak: where they cancel, the conclusion holds anyway.

Reading: where the chooser remains uncertain which option it will pick, its conditionals track its unconditionals; where self-uncertainty vanishes instead, the corresponding term's mass is $\approx 1$ on a near-certain event and conditioning is automatically trivial. This is the non-Newcomblike regime stated in the belief stream rather than in menu syntax. *Some* scope condition is provably necessary (§Necessity), and rejected menu-intrinsic alternatives are surveyed at [[defining-exogeneity]]. Note the condition applies to the **menu options**; strategy bets like $\widehat S - O^i$ are selection-referencing through their *coefficients*, which is what the machinery handles.

## Lemma 1 — bounds transfer

**Lemma.** Let $(X_n)$ be a sequence of $[a,b]$-LUVs in the e.d. family (H1) quantifies over, with the expert's quotes $E^A_n(X_n)$ published to the ledger, and let $s$ be a rational. If $E^A_n(X_n) \gtrsim_n s$, then $E^H_n(X_n) \gtrsim_n s$.

**What it says, and what it costs.** The novice's own valuation eventually respects any lower bound the expert's published quotes eventually respect. Nothing about menus, selection or strategies enters: $X_n$ is an arbitrary bet in the family and $s$ an arbitrary constant. This is the half of the theorem Total Trust was *designed* to deliver, so the proof is close to an unpacking of the definition — the only real work is getting from (H1)'s **weighted** form to an unweighted conclusion.

That weighted form is not an artifact. (H1) does not say "if the expert quotes above $t$ then the novice values above $t$"; it says that for any weight the novice can compute from what it can see, the weighted aggregate does not fall below $t$. It has to be stated that way because a trader may only buy a bet in quantities that are continuous, market-generable functions of visible prices, so "the novice systematically undervalues bets the expert rates above $t$" is only ever expressible as a *buying pattern* that profits. The unweighted reading is recovered by exhibiting a legal weight that is eventually identically $1$.

**Proof.** Fix $\varepsilon > 0$ and a ramp width $\delta$ with $0 < \delta < \varepsilon/2$. Put $t := s - \varepsilon$ and

$$ w_n \;:=\; \operatorname{Ind}_\delta\big(E^A_n(X_n) > t\big) \;\in\; [0,1], $$

the ramp that is $0$ while the quote is at or below $t$, rises linearly, and is exactly $1$ once the quote reaches $t + \delta$. Three observations, then the chain.

*(a) The weight is legal.* Its argument is the published quote — a rational the novice reads $\mathcal{C}_H$-cheaply — and $\operatorname{Ind}_\delta$ is continuous and piecewise-linear, so $w_n$ is market-generable for the novice. The continuity is not decoration: a sharp $\mathbb{1}[\text{quote} > t]$ jumps at the threshold and is not available as a trader's coefficient at all. Ramping the threshold is the price of stating (H1) legally.

*(b) The weight is eventually $1$, and provably so.* $E^A_n(X_n) \gtrsim_n s$ means $\liminf_n (E^A_n(X_n) - s) \ge 0$, so with the slack $\varepsilon - \delta > \varepsilon/2 > 0$ there is an $N$ with $E^A_n(X_n) > s - \varepsilon + \delta = t + \delta$ for all $n \ge N$ — the ramp's saturation point. Hence $w_n = 1$ for $n \ge N$, and $\Gamma$ *proves* it: the day-$n$ quote is a rational output by a computable process, $\Gamma$ represents computable functions and proves their computations, so $\Gamma$ decides the quote's value and $w_n = 1$ follows by rational arithmetic. Therefore also $\Gamma \vdash X_n w_n = X_n$ for $n \ge N$. Note what this step does *not* use: nothing about the expert being accurate, calibrated, honest, or even an inductor — only that its quote is a published decided number.

*(c) Saturation makes the ramp free.* On every day that matters the ramp is evaluated in its flat region, so the linear interpolation contributes no error at all. In this lemma the ramp is machinery, not slack. (Contrast [[soft-self-endorsement]], where the ramp is evaluated *on* its slope and the resulting $2\delta$ survives into the conclusion.)

Now the chain, every step on the novice's side:

$$ E^H_n(X_n) \;\approx_n\; E^H_n(X_n w_n) \;\gtrsim_n\; (s-\varepsilon)\,E^H_n(w_n) \;\approx_n\; s - \varepsilon. $$

- **First step.** $\Gamma \vdash X_n w_n = X_n$ for $n \ge N$ by (b), so `expprovind` (4.8.10) forces the two expectations together. The days below $N$ are invisible to a $\liminf$; formally, replace the sentence at each $n < N$ by $\top$ so that the sequence of theorems is e.c.
- **Second step.** A single instance of (H1), at bet $X_n$, threshold $t = s - \varepsilon$, ramp width $\delta$. This is the only appeal to any deference hypothesis in the whole lemma.
- **Third step.** $\Gamma \vdash w_n = 1$ for $n \ge N$, so provability induction drives $E^H_n(w_n) \to 1$ and hence $(s-\varepsilon)E^H_n(w_n) \to s - \varepsilon$, whatever the sign of $s - \varepsilon$.

Taking $\liminf$s, $\liminf_n E^H_n(X_n) \ge s - \varepsilon$; and $\varepsilon > 0$ was arbitrary. $\blacksquare$

### Remarks on Lemma 1

- **This $\varepsilon$ is cheap, and the pattern is the one to aim for.** It is quantified *outside* a self-contained argument: each $\varepsilon$ gets its own weight, its own (H1) instance, its own $N$, and the conclusions are intersected at the end. Nothing needs to be uniform in $\varepsilon$. Lemma 2's Step 3 now has the same shape — which is the point of the mass-weighted (H3). The version of (H3) that divided by self-prediction mass forced an $\varepsilon$ *inside* a finite sum, where sub-$\varepsilon$ terms had to be controlled simultaneously with the limit; that was a real uniformity obligation, and multiplying through by the mass removes it.
- **Timing is absorbed, except in one place.** Every quote-dependent fact above is routed through provability rather than through the novice's day-$n$ prices, so publication lag ($e(n) \ge n$) costs nothing in the chain: `expprovind` and provability induction only need the sentences to be $\Gamma$-theorems eventually. The lag is *not* absorbed in (H1) itself, whose weight must be market-generable at trading time — so read (H1), and the lemma, at the first day the quote is readable. That is the whole content of "published to the ledger", and it is where the read-cheap side of the produce-hard/read-cheap gap ([[complexity-gap-hinge]]) is spent.
- **Threshold-zero Total Trust already suffices here.** If (H1) is available only at threshold $0$, the conclusion survives whenever the e.d. family is closed under adding rational constants: apply it to $Y_n := X_n - (s - \varepsilon)$, whose quote is $E^A_n(X_n) - (s-\varepsilon)$ up to $o(1)$ by the expert's own `loe`, hence eventually exceeds $\varepsilon/2 > \delta$; the ramp saturates, the same chain gives $E^H_n(Y_n) \gtrsim_n 0$, and the novice's `loe` returns $E^H_n(X_n) \gtrsim_n s - \varepsilon$. This is where $\delta < \varepsilon/2$ rather than $\delta < \varepsilon$ earns its keep, and where the $[a,b]$ generalization pays for itself — the translate leaves $[0,1]$. So the threshold-zero restriction that looks crippling in the older pages is not a restriction *for bounds transfer*; if it costs anything, it costs it elsewhere.
- **What $X_n$ gets instantiated to, and why the ledger must be rich.** In the Theorem, Lemma 1 is applied not to a menu option but to the composite $\widehat S_n - O^i_n$. So (H1)'s ramp takes *the composite's* quote as its argument, and the novice must be able to read it: **rich-ledger observability is spent exactly here**, and nowhere else. Given only per-option quotes, the novice's best proxy for the composite quote is $m^{j^\ast}_n - m^i_n$ — but licensing that proxy is precisely self-endorsement, i.e. Lemma 2. The rich ledger is therefore what keeps the two lemmas independent; on a thin ledger they entangle, which is what forced the surrogate formulation of [[total-trust-implies-value-telescoping]].
- **Formalization.** The only non-constructive step is the choice of $N$: it exists but is not computed from $\varepsilon$, and the theorem sequence is e.c. only because a fixed constant may be hard-coded. Everything else is an `Approx`/`AsympLE` composition of the shape already exercised in `lean-deference` ([[open-problems]] item 6).

This half makes no claim about what the expert thinks of any composite; all such claims live in Lemma 2.

## Lemma 2 — self-endorsement

**Lemma (modulo one named item).** Assume (H2) and (H3). Then $E^A_n(\widehat S_n) \gtrsim_n M_n$; in particular $E^A_n(\widehat S_n - O^i_n) \gtrsim_n 0$ for every $i$.

**Proof sketch, in three steps.**

*Step 1 — decomposition (no hypothesis used).* $\widehat S_n$ is by construction the formula $\sum_j \mathbb{1}[\mathrm{sel}_n = j]\cdot O^j_n$. Each summand is itself an LUV, and the expert's `loe` (4.8.4) splits the sum with **unit** coefficients:

$$ E^A_n(\widehat S_n) \;\approx_n\; \sum_j E^A_n\big(\mathbb{1}[\mathrm{sel}_n = j]\cdot O^j_n\big). $$

Worth being explicit, since it is the step most easily mis-stated: the discontinuous selector never appears as a *coefficient* in `loe`. It sits inside the LUVs being added, and the coefficients are all $1$. (Bounds bookkeeping: each product lies in $[\min(a,0), \max(b,0)]$ and the sum provably in $[a,b]$; `expprovind` converts.)

*Step 2 — the scope condition.* (H3), in its denominator-free form, is exactly the statement that this sum is $\gtrsim_n \sum_j \mathbb{P}^A_n(\mathrm{sel}_n = j)\, m^j_n$. Nothing else is asked of it.

*Step 3 — concentration (the named gap).* A mass-weighted average of quotes is below the max, so Step 2 alone does not finish; the mass must sit on near-maximal options. That is the **introspective-concentration lemma** to be extracted from (H2): $\mathbb{P}^A_n(\mathrm{sel}_n = j) \to 0$ whenever $m^j_n \le M_n - \varepsilon$, the selection being ledger arithmetic in quotes the expert knows within $o(1)$. Granting it, split the sum at $\varepsilon$: the near-max indices carry mass $1 - o(1)$ and contribute at least $(M_n - \varepsilon)(1 - o(1))$, the sub-max indices carry mass $o(1)$ and contribute at least $\min(a,0)\cdot o(1) \to 0$; so $\sum_j \mathbb{P}^A_n(\mathrm{sel}_n=j)\,m^j_n \gtrsim_n M_n - \varepsilon$, and $\varepsilon$ is arbitrary. Finally $E^A_n(O^i_n) = m^i_n \le M_n$ by definition of the quotes. $\blacksquare$ (modulo Step 3)

Note the $\varepsilon$ in Step 3 is a **quote-gap** threshold, not a conditioning-mass threshold: it never sits under a denominator, so it raises no uniformity obligation — the ordinary "fix $\varepsilon$, take $\liminf$, let $\varepsilon \to 0$" pattern of Lemma 1 applies unchanged.

**Named gap:** the concentration lemma ([[open-problems]] item 1). The previously listed second gap — a uniform-in-$\varepsilon$ restatement of (H3) over e.d. subsequences — is **retired**: it was an artifact of forming conditionals at all, and the mass-weighted form dissolves it rather than solving it.

**One-sidedness is deliberate.** Earlier versions claimed $E^A_n(\widehat S_n) \approx_n M_n$, pinned two-sidedly. The upper bound is never consumed downstream — the Theorem needs only $E^A_n(\widehat S_n) \gtrsim_n m^i_n$ — and dropping it is what lets (H3) be one-sided, which is what admits benignly-correlated menus (selection as good news) instead of excluding them.

**Timing remark (staleness).** Self-endorsement must be *same-day*: it is $E^A_n$ of a strategy built from the day-$n$ quotes. Evaluating at a later day does not help — by then the selectors are decided constants but the quotes have moved, and a stale argmax is a pick the current expert has no reason to endorse. The self-reference cannot be waited out; it is handled introspectively, which is what (H2) and (H3) are for.

## Theorem — argmax Value

**Theorem.** Assume (H1)–(H3). Then for every fixed $i$: $\;E^H_n(\widehat S_n) \gtrsim_n E^H_n(O^i_n)$.

**Proof.** Lemma 2 gives $E^A_n(\widehat S_n - O^i_n) \gtrsim_n 0$ (the difference bet is in the quantified family; its quote tracks $E^A_n(\widehat S_n) - m^i_n$ by the expert's `loe` with constant coefficients). Lemma 1 transfers: $E^H_n(\widehat S_n - O^i_n) \gtrsim_n 0$. The novice's `loe` splits the difference. $\blacksquare$

## Necessity of the scope condition

**The punishing menu (Abram, 2026-07-24).** Take $O^j_n := 1 - \mathbb{1}[\mathrm{sel}_n = j]$ — every option is worth $0$ if chosen, $1$ otherwise. These are legal e.d. LUVs (the selection is ledger arithmetic — the same channel that legalizes gap-bets), and on this menu:

- $\Gamma \vdash \widehat S_n = \sum_j \mathbb{1}[\mathrm{sel}=j](1 - \mathbb{1}[\mathrm{sel}=j]) = 0$ by pure logic, so both inductors' `expprovind` drives $E^A_n(\widehat S_n) \approx_n 0 \approx_n E^H_n(\widehat S_n)$;
- the quotes go liar-like (the top-quoted option is worth $0$, the others $1$, so the argmax chases itself), and $M_n$ stays bounded away from $0$ (collapsed quotes on provably-$1$ options are exploitable);
- hence self-endorsement fails in the limit, and **argmax Value itself fails** — $E^H_n(O^i_n) \approx 1$ on unchosen days — for *any* deference hypothesis.

Note `expprovind` cannot rescue anything here: what is provable is quote-dominance (the selected option has the top *estimate*), never value-dominance, and there is no provable value bound to transfer. This is a decision-theoretic failure, not an epistemic one — a choice-punishing environment against which argmax-following is simply a bad decision theory (Death in Damascus; Counterfactual Mugging is the same family) — and it is *bracketed*, not solved: (H3) excludes it **by its epistemic signature**, with no syntax inspection. The arithmetic is immediate in the denominator-free form. Here $\mathbb{1}[\mathrm{sel}_n = j]\cdot O^j_n = \mathbb{1}[\mathrm{sel}_n=j](1 - \mathbb{1}[\mathrm{sel}_n=j])$ is provably $0$, while $E^A_n(O^j_n) \approx_n 1 - \mathbb{P}^A_n(\mathrm{sel}_n = j)$, so (H3)'s two sides differ by

$$ 0 \;-\; \sum_j \mathbb{P}^A_n(\mathrm{sel}_n=j)\big(1 - \mathbb{P}^A_n(\mathrm{sel}_n=j)\big) \;=\; -\Big(1 - \sum_j \mathbb{P}^A_n(\mathrm{sel}_n=j)^2\Big) \;<\; 0 $$

for any non-degenerate self-prediction — bounded away from $0$ exactly when the chooser stays uncertain, which is when the menu does its damage. Death in Damascus scores the same way (two options at mass $\approx \tfrac12$, conditionals $\approx 0$ against unconditionals $\approx \tfrac12$: the sum is $\approx -\tfrac12$). The menu convicts itself in the belief stream. The same test subsumes the tie-break correlation channel of [[ledger-decided-tie-breaks]] — and, being one-sided, convicts only the adversarial rule there, correctly leaving the clairvoyant one alone.

A constant-probe variant — one punishing option $\mathbb{1}[\mathrm{sel}_n = 2]$ paired with $\text{const } s$ — drives the expert's quote to a liar fixed point at $s$ and shows the same pathology reaching the Total-Trust corner: it is why the equivalence loop cannot be closed through the two-option identity and must enter Total Trust through the fold. [[loop-direction]].

## Assumptions audit

- **Novice:** `loe` (4.8.4), `expprovind` (4.8.10), Total Trust (H1). No tower, no Mart.
- **Expert:** a logical inductor; its own `loe`; introspection (H2). Nothing exact at any finite day, anywhere.
- **Environment:** conditional-stability (H3) — necessary in some form, per §Necessity.
- **Channel:** rich-ledger observability; ledger-decided tie-break (definitional — the selector bits must be ledger arithmetic).
- **Bounds:** one fixed $[a,b]$; the paper's $[0,1]$ statements lift affinely.

## Status

**PROVED modulo one named gap** (the concentration lemma — [[open-problems]] item 1); **REFUTED without a scope condition** (the punishing menu); **unvetted by Abram as of 2026-07-26; not machine-checked.** Page history: earlier versions (exact expert-side claims → asymptotic surrogate lemma → factored true-setting form → the present mass-weighted (H3), each revision at Abram's objection) are in git history, with the discussion archived at `imported-chats/2026-07-23__tt-value-cluster-revision-arc__5cf76191.md`; the surrogate-era route cluster survives, correctly scoped, at [[total-trust-implies-value-telescoping]]. The mass-weighted denominator-free (H3) and the Lemma 1 expansion date from 2026-07-26, the former from Abram's proposal to multiply through by the self-prediction mass.

## Related

- [[soft-self-endorsement]] — the $\delta$-hedged variant: weaker conclusion, but needs neither (H3) nor a tie-break, and survives even punishing menus
- [[defining-exogeneity]] — rejected menu-intrinsic definitions of the scope condition, and the wider decision-theory discussion (policy-trust direction)
- [[total-trust-implies-value-telescoping]] — the surrogate-formulation cluster (overview)
- [[ledger-decided-tie-breaks]] — the tie-break's definitional role; its correlation channel is subsumed by (H3)
- [[deference-notions]], [[expert-conditions]] — the official notions; what introspection is and buys
- [[open-problems]] — the named gaps, the satisfiability-breadth conjecture, the policy-trust direction

*Source: the 2026-07-23 → 07-26 Claude Code sessions (see the archived transcript); apparatus from the LI paper via [[conventions-and-status-labels]] and deference-v6 §1 (`deference-in-logical-induction-v6.md`).*
