# Reflection in the LI setting (the bifurcation)

*Reflection splits into two inequivalent readings when translated to LI, and their fates are opposite. The **value form** — condition on the expert's estimate of this bet, adopt that estimate — softens to the band limit-equality, which is a **theorem** given Tower and joins the circle as a fourth equivalent face: soft value-Reflection ⟺ Total Trust ⟺ Value ⟺ Tower. The **function form** — condition on the expert's entire probability function (DDB's reading) — is never a substantive further hypothesis in LI: where the function is decided it conditions on a known fact and does nothing, and where it is undecided no legal weight can express it. What is genuinely unreachable is not a stronger *notion* but a stronger *grade*: exactness at finite days, which the LI paper's own self-trust discussion refutes with a witness. **Unvetted by Abram as of 2026-07-28.***

## The two classical forms

The literature writes "Reflection" for two different principles:

**Value form** (van Fraassen's Reflection; the Skyrms 1990 result on the slides): condition on the expert's credence *in the particular claim*, and adopt it —

$$ \mathbb{P}_{\mathrm{nov}}\big(X \;\big|\; \mathbb{P}_{\mathrm{exp}}(X) = x\big) \;=\; x . $$

**Function form** (DDB's official Reflection): condition on the expert's *entire probability function*, and adopt its verdict wholesale —

$$ \pi\big(\cdot \;\big|\; P = \rho\big) \;=\; \rho . $$

On a finite frame with an immodest expert these are close enough to interchange, which is why the literature slides between them. A modest expert separates them, and LI separates them decisively: they translate differently, and one survives while the other dissolves.

**Terminology note.** The labels "value form" / "function form" are this wiki's, not established usage. DDB call the function-conditioning principle simply **Reflection** (and its modesty-permitting repair **New Reflection**); van Fraassen's original principle is the value-conditioning one; the literature has no standard name-pair for the distinction. ("Local/global" is unavailable: DDB already use it for a different axis — *which questions* one defers on, their §5.) "Function form" per Abram (2026-07-28); an earlier draft said "identity form", following the corpus's older "conditioning on the expert's entire identity" phrasing, which is likewise home-grown.

## The value form is a theorem (given Tower)

Setting of [[total-trust-implies-value]]. The LI translation of "the expert's estimate of $V_n$ equals $s$" cannot be a sharp event (a hard indicator is an illegal weight, and exactness is the wrong grade — see §Exactness below); the honest rendering is a **band**: the quote lies within $\varepsilon$ of $s$. The translation of the value form is then exactly the **band limit-equality** proved at [[tower-implies-total-trust]] §"The other direction": with the band weight

$$ b_n \;:=\; \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner > s - \varepsilon\big) \cdot \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner < s + \varepsilon\big), $$

Tower gives the two-sided pinch

$$ (s - \varepsilon)\, E^H_n(b_n) \;\lesssim_n\; E^H_n\big(V_n\, b_n\big) \;\lesssim_n\; (s + \varepsilon)\, E^H_n(b_n), $$

and wherever the conditioning mass is bounded away from $0$, the normalized reading: conditional on the expert's estimate sitting in the band, the novice's conditional estimate sits in the same band. Soft, asymptotic, mass-caveated — and **proved**, not assumed.

## It joins the circle

Soft value-Reflection is not merely a consequence; it is *equivalent* to the other three faces, because it gives back Total Trust by a short partition argument.

**Claim (band form ⟹ Total Trust).** Assume the unnormalized band statement above for all bands. Fix a bet sequence $(V_n)$, threshold $v$, width $\delta$, and the Total-Trust weight $w_n := \operatorname{Ind}_\delta(\ulcorner E^A_n(V_n)\urcorner > v)$. Choose finitely many thresholds $v = t_0 < t_1 < \cdots < t_K$ with $t_K$ past the top of the bet's range, and write the telescoping decomposition

$$ w_n \;=\; \sum_{k=0}^{K-1} \Big[ \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner > t_k\big) \;-\; \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner > t_{k+1}\big) \Big] $$

(the final ramp is identically $0$, the quote never reaching past the range). Each bracketed difference is a legal $[0,1]$-valued weight, positive only where the quote lies strictly between $t_k$ and $t_{k+1} + \delta$ — a band weight. The lower half of the band statement at each band gives $E^H_n(V_n \cdot [\text{band } k]) \gtrsim_n t_k \cdot E^H_n([\text{band } k])$, and every $t_k \ge v$. Summing the finitely many bands with the novice's `loe` (unit coefficients):

$$ E^H_n\big(V_n\, w_n\big) \;\gtrsim_n\; v \cdot E^H_n\big(w_n\big). $$

The low side is symmetric. $\blacksquare$ (Status: **PROVED (prose, this page)**, unvetted.)

With [[tower-implies-total-trust]] (Tower ⟹ the band statement) and the rest of the circuit, the loop becomes a square: on conditional-stable menu sequences,

$$ \textbf{soft value-Reflection} \;\iff\; \textbf{Total Trust} \;\iff\; \textbf{Value} \;\iff\; \textbf{Tower}. $$

This vindicates the slides' four-notion equivalence chain *for the value form, at asymptotic grade* — the LI analogue of the immodest-case collapse, reached by a reasoner that is provably not exactly immodest (below).

## The LI paper's own reflection discussion (§4.11–§4.12)

The paper never uses the word "Reflection" (its only uses of "reflect" are incidental), but §4.11 *Introspection* and §4.12 *Self-Trust* are a complete reflection theory for the future-self expert, and the line it draws is exactly the one above: **value form, band grade, soft weights** — with the exact grade not merely avoided but *refuted*.

- **Introspection (4.11.1) is band-form self-knowledge.** For any efficiently written pattern of the form "$a_n < \mathbb{P}_n(\varphi_n) < b_n$" — a *band* event over the reasoner's own prices — the inductor learns to believe it when true and disbelieve it when false, with vanishing error. The paper's own starting point for self-reflection is already interval-valued, not exact.
- **Paradox Resistance (4.11.2)** — on the family $\chi^p_n \leftrightarrow \big(\mathbb{P}_n(\chi^p_n) < p\big)$, prices converge to $p$: the quantitative form of "exact self-knowledge is barred by the liar," with the paper's brain-scanner discussion as the intuition.
- **`ccee` (4.12.3) is glossed by the paper itself as a conditional-expectation identity.** Dividing the weight out of both sides, they read it as: my expected value of $X$ now, given that I will rate $X$ above $0.7$ later, equals whatever I expect to rate it later, conditional on the same — the conditional tower in conditional-expectation dress, the same object this wiki's fold delivers.
- **Self-Trust (4.12.4) settles exact-vs-soft, with a witness.** The paper stresses that `st` is deliberately *weaker* than the hard-conditioned statement — and that the hard version is **false**: for the paradoxical family $\varphi_n := \ulcorner \mathbb{P}_{f(n)}(\varphi_n) < 0.5 \urcorner$, each conjunction $\varphi_n \wedge \big(\mathbb{P}_{f(n)}(\varphi_n) \ge 0.5\big)$ is disprovable, so

  $$ \mathbb{P}_n\Big(\varphi_n \wedge \big(\mathbb{P}_{f(n)}(\varphi_n) \ge 0.5\big)\Big) \;\eqsim_n\; 0 , $$

  i.e. conditional on the future price sitting exactly at-or-above the threshold, the *correct* current credence in the paradoxical sentence is $0$, not $0.5$. In the paper's words: "with discrete conjunctions, the result would be undesirable (not to mention false)," and the desirable reading is that the inductor "retain[s] the ability to think it can outperform its future self's beliefs when its future self confronts paradoxes" — conditioned on *exactly* $0.5$, answer "very low"; conditioned on *extremely close to* $0.5$, answer "roughly $0.5$."
- **The adoption remark is the paper's too.** Glossing the sentence-level future-expectation theorem: "if $\overline{\mathbb{P}}$ knows that its future self is going to assign some sequence $\overline{p}$ of probabilities to $\overline{\varphi}$, then it starts assigning $\overline{p}$ in a timely manner" — adoption of the expert's numbers, gated on being able to know them, exactly the readability condition of §Function form below.
- **Precedent.** The paper cites Christiano et al. 2013 (*Definability of Truth in Probabilistic Logic*) for the introspection desideratum; that paper's result is the same verdict one level down — exact self-reflection $\mathbb{P}(\ulcorner\varphi\urcorner) = p$ is unsatisfiable, while the open-interval (band) form is consistent. The exact-vs-band boundary predates LI; LI adds the *learning* of the band form in a timely manner, and the trading-language explanation of why the boundary sits where it does.

## What is genuinely unreachable — three separate things, each precise

**1. Exactness (the "=" and the sharp event).** At any finite day, the exact self-instance is contradictory, not merely unproven: complete self-knowledge would let the diagonal lemma build a liar the inductor cannot settle, and Paradox Resistance (LI 4.11.2) is the quantitative residue — on the sentence asserting its own price is below $p$, the price is pinned near $p$ while the truth value sits on the wrong side. The trading language enforces the same boundary by type: a sharp indicator of a price event is discontinuous, hence not a weight any trader can hold. So every consistent translation is soft (ramps), banded ($\varepsilon$), and asymptotic ($\approx_n$) — the softenings are not losses of nerve but exactly what survives the liar. And this is not only an expressibility barrier: on the paradoxical family the exactly-conditioned demand is **false** — conditional on the future price sitting exactly at the threshold, the correct credence is $0$, not the threshold (the disprovable-conjunction witness of §The LI paper's own reflection discussion) — so a reasoner *satisfying* exact Reflection there would simply be wrong, and the inductor's refusal is accuracy, not weakness.

**2. Function-conditioning.** DDB's form conditions on *which probability function the expert is*. In LI this is never a substantive hypothesis, by cases on timing:

- **Decided function** (the observable AI, quotes published to the ledger): the expert's day-$n$ state, so far as the novice's world represents it, is a decided fact. Conditioning on a known fact is idle, and what remains of function-Reflection is outright **adoption**: $E^H_n(V_n) \approx_n E^A_n(V_n)$. But adoption is already a *consequence* of Tower plus readability — the quote is a ledger rational the novice can use as a generable coefficient, so $E^H_n(\ulcorner E^A_n(V_n)\urcorner) \approx_n E^A_n(V_n)$, and Tower supplies the other link. Nothing above the Tower is being assumed; function-Reflection has collapsed *into* it.
- **Undecided function** (the future self at deferral $f(n)$, or any not-yet-published state): the day-$n$ novice cannot read the state, and no legal weight can condition on it — a weight is a continuous function of finitely many prices, while the conditioning object is the whole function, and the event "$P = \rho$" over continuum-many candidates is exactly the kind of sharp, non-generable predicate the language excludes. Here `cee` stays a genuine *forecast* of the future quote, not an adoption of it — which is why self-trust is interesting at all.

So "Reflection is different" has precise content: the function form is idle where the function is decided and inexpressible where it is not. There is no reading on which it is a live, stronger demand.

**3. The wrong kind of modesty.** DDB's modest expert is **identity-uncertain** — it gives positive probability to being some other credence function. An inductor-expert is never that: it knows its own definition, and its self-opacity is a bounded, shrinking *error about its own estimates*, forced by the liar rather than assumed ([[expert-conditions]] §"incomplete self-knowledge, not identity-uncertainty"). This favours the self-knowledge reading of immodesty over the "doesn't know they're the expert" reading (Abram's footnote in `li-deference.md`): the operative quantity everywhere in the LI development is estimate-self-knowledge — it is what F1, the fold, and the probe menus consume — and de-se identity plays no role in any proof.

## Between modest and immodest (the slide-12 picture)

- **At every finite day, modest — forcibly.** Exact self-knowledge is inconsistent with inductor-hood (the liar), so modesty is not an assumption to relax but a theorem. This is *stronger* modesty than DDB's, and of a different kind (estimate-error, not identity-uncertainty).
- **In the limit, immodest.** Self-knowledge of estimates is learned (`epr`/`er`): asymptotically the inductor knows its own quotes. Since every LI deference notion is itself asymptotic, the asymptotic self-knowledge is the only kind the notions ever consume — so the equivalence structure lands at DDB's *immodest* corner, Skyrms' chain included, with every "$=$" softened to "$\approx_n$".
- **The finite-day modesty is where all the softenings live**: the $\delta$-ramps (no sharp conditioning), the $\varepsilon$-bands (no exact estimate events), the missing rates (introspection converges with no modulus, so every argument diagonalizes $\varepsilon$ outside), and the mass caveats (conditioning may be vacuous). The shape of every theorem in the circle is the shape of the liar being kept at bay.

## Downstream revisions

[[deference-notions]] §Reflection asserts "Reflection ⟹ Mart, never the converse" and "the trust hierarchy provably tops out at the tower and cannot reach Reflection." Both claims are correct for the **exact and function-conditioning** readings and false for the soft value form (Tower ⟹ band limit-equality, above). That section should be re-scoped to name the bifurcation; its "ceiling is a feature" moral survives intact, attached to the exact and function-conditioning readings.

## Status

**DISCUSSION with two proved components**: the band limit-equality from Tower is proved at [[tower-implies-total-trust]]; the partition argument (band form ⟹ Total Trust) is **PROVED (prose, this page)**. The bifurcation reading, the adoption remark, and the modest/immodest synthesis are **INTERPRETATION**. **Unvetted by Abram as of 2026-07-28; nothing machine-checked.** Written for the *Boundedly Rational Trust* slides (the Skyrms slide, the "Reflection is different" note, and the "between modest & immodest" slide). Revised same day at Abram's prompt: the LI paper's §4.11–§4.12 consulted and summarized (its `st` discussion supplies the refutation witness for the exact grade, upgrading "inexpressible" to "false, desirably"); "identity form" renamed **function form**, with the terminology note.

## Related

- [[tower-implies-total-trust]] — the band limit-equality (Reflection over estimates) and both halves of Total Trust
- [[deference-notions]] — the notion inventory this page re-scopes at §Reflection
- [[expert-conditions]] — modesty as forced incomplete self-knowledge; the liar argument; why the home is an infinite process
- [[total-trust-implies-value]], [[value-implies-tower]] — the other faces of the square
- [[value-iff-mart]] — the assembled equivalence and where separations survive
- `li-deference.md` §0.1 — Abram's footnote on the two readings of immodesty, which the LI development supports
- LI paper §4.11 (Introspection 4.11.1, Paradox Resistance 4.11.2, `epr`/`er`) and §4.12 (`cee`/`ccee`/`st` and the discrete-conjunction passage) — the paper's reflection discussion, nameless but complete; Christiano et al. 2013 (cited there) for the exact-vs-band precedent

*Source: this page (2026-07-28 Claude Code session); apparatus from [[tower-implies-total-trust]], deference-v6 §1.6/§2.2, and LI §4.11–§4.12 (`references/logical-induction/main.tex`).*
