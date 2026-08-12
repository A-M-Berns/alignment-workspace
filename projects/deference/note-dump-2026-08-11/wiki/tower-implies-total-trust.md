# Tower ⟹ Total Trust (the fold at the ramp, true LI setting)

*The third arrow of the loop, in the setting of [[total-trust-implies-value]] and [[value-implies-tower]]: a novice who Towers an inductor-expert satisfies both halves of soft Total Trust — conditioning on the quote being high, and on it being low — and, on band weights, the conditional **limit-equality** (Reflection over estimates). One Tower instance — at the **ramp-weighted bet** $V_n \cdot w_n$ — plus the expert's own linearity and provable ramp arithmetic. No scope condition, no introspection hypothesis beyond what an inductor's own `loe` supplies, no tie-break. This closes the loop **Total Trust ⟹ Value ⟹ Tower ⟹ Total Trust**. **Unvetted by Abram as of 2026-07-27.***

**Name.** "Tower" as in [[value-implies-tower]] — what the older corpus calls **Mart** ([[deference-notions]]). This page is the true-LI-setting replacement for the abstract fold-plus-threshold-bound sketch (v6 §1.6 forward; [[deference-notions]] §Total Trust), which charged an abstract expert with coherence + introspection (`hknow`); here the expert is an inductor and its own `loe` pays that bill.

## Setting

The setting of [[total-trust-implies-value]], unchanged. $\Gamma$ a theory with its deductive process; $H \dashv \mathcal{C}_H$ and $A \dashv \mathcal{C}_A$ logical inductors over $\Gamma$ (novice and expert); expectations are the paper's price-integrals of formulas, $[a,b]$-LUVs transporting affinely. The expert's day-$n$ quote for a bet $V_n$ in the quantified family — the rational $E^A_n(V_n)$ — is published to the ledger and readable $\mathcal{C}_H$-cheaply as a $\Gamma$-decided fact (**observability**); $\ulcorner E^A_n(V_n)\urcorner$ is the LUV naming it. Publication timing ($e(n) \ge n$) is absorbed exactly as in [[total-trust-implies-value]] Lemma 1's timing remark: every quote-dependent fact below is routed through provability, and the one place a weight must be market-generable at trading time is the *statement* of the Total-Trust conclusion itself, read at the first day the quote is readable.

**The target (soft Total Trust at $(V_n, v, \delta)$).** For every bet sequence $(V_n)$ in the e.d. family, every rational threshold $v$ and ramp width $\delta > 0$, with the ramp weight

$$ w_n \;:=\; \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner > v\big), $$

the unnormalized form of the Total-Trust inequality

$$ E^H_n\big(V_n \cdot w_n\big) \;\gtrsim_n\; v \cdot E^H_n\big(w_n\big). $$

(Full Total Trust also has a second half, conditioning on the quote being *below* $v$; it, and the two-sided equality both halves are shadows of, are derived in §"The other direction" below.)

## Hypotheses

**(T) Tower, on the ramp-weighted class.** $E^H_n(X_n) \approx_n E^H_n(\ulcorner E^A_n(X_n)\urcorner)$ for e.d. sequences $(X_n)$ including the products $V_n \cdot w_n$. This closure is not a new tax: the ramp's argument is a published quote, so $V_n \cdot w_n$ is an e.d. LUV by the same observability that legalizes gap-bets — and the Tower delivered by [[value-implies-tower]] is quantified over arbitrary e.d. $(Z_n)$, so it already covers these products.

**Expert side: its own `loe`, nothing more.** The weight $w_n$ is a continuous piecewise-linear function of $A$'s *own* day-$n$ prices — an expressible feature of its market, hence a legal $A$-generable coefficient. So the expert's Linearity of Expectation (4.8.4) applies with $w_n$ as the coefficient: this is where the abstract fold's "the expert knows the weight" is discharged for free. No (H2) is separately charged, and no exactness at any finite day is used.

**Novice side:** `loe` (4.8.4) and `expprovind` (4.8.10), free.

**Not assumed:** no conditional-stability (H3) — nothing on this page selects anything; no tie-break; no menus at all.

## Three facts

**(a) The weight is decided.** $A$ is computable and $\Gamma$ represents computable functions, so $\Gamma$ decides the quote $E^A_n(V_n)$, and with it the weight: $\Gamma$ proves $w_n$ equal to a specific rational in $[0,1]$ (for rational $v, \delta$, the ramp is rational arithmetic on a decided rational). Below, $w_n$ stands for the formula and for this decided rational interchangeably; no separate symbol is introduced for the value.

**(b) The expert folds the weight out.** By (a), $\Gamma$ proves the product $V_n \cdot w_n$ equal to the scalar multiple of $V_n$ by $w_n$'s decided value; and $w_n$, as a continuous function of $A$'s own prices, is a legal bounded $A$-generable coefficient. So the expert's `loe` gives

$$ E^A_n(V_n \cdot w_n) \;\approx_n\; w_n \cdot E^A_n(V_n) . $$

**(c) Ramp arithmetic, provably.** The one fact needed about the ramp's shape: **it is positive only where the quote exceeds $v$.** So the product $\big(E^A_n(V_n) - v\big)\cdot w_n$ is nonnegative — either $w_n = 0$ and it vanishes, or $w_n > 0$ and both factors are positive. This is exact rational arithmetic between decided quantities, per day, no asymptotics anywhere; hence

$$ \Gamma \vdash\; \ulcorner E^A_n(V_n)\urcorner \cdot w_n \;\ge\; v \cdot w_n . $$

Note this never uses the ramp's *slope* — any $[0,1]$-valued weight vanishing wherever the quote is at most $v$ would satisfy it. The slope's job is elsewhere: continuity is what makes $w_n$ legal as a market weight for the novice, and a generable coefficient for the expert in (b). The two jobs are independent, which is why the bound costs nothing.

## Proof

$$ E^H_n\big(V_n w_n\big) \;\underset{\textbf{(T)}}{\approx_n}\; E^H_n\big(\ulcorner E^A_n(V_n w_n)\urcorner\big) \;\underset{\text{(b) carry}}{\approx_n}\; E^H_n\big(\ulcorner E^A_n(V_n)\urcorner \cdot w_n\big) \;\underset{\text{(c) + \texttt{expprovind}}}{\gtrsim_n}\; v \cdot E^H_n\big(w_n\big). $$

- **First step** — the Tower hypothesis at the weighted bet $(V_n w_n)$, verbatim.
- **Second step — the carry.** Both LUVs are $\Gamma$-decided rationals: $\ulcorner E^A_n(V_n w_n)\urcorner$ decides to the expert's actual quote of the product, and $\ulcorner E^A_n(V_n)\urcorner \cdot w_n$ to $w_n \cdot E^A_n(V_n)$; the two rationals differ by $o(1)$ by (b). Fix rational $\varepsilon > 0$: eventually the difference is provably within $\varepsilon$ (decided rational arithmetic), so `expprovind` on $\pm$(the difference LUV) pins $|E^H_n(\cdot) - E^H_n(\cdot)| \lesssim_n \varepsilon$; patch the finitely many early days with $\top$ to keep the theorem sequence e.d., and diagonalize over $\varepsilon$ — the same $\varepsilon$-outside pattern as [[total-trust-implies-value]] Lemma 1.
- **Third step — in detail, since 4.8.10 does not mention pairs of expectations.** `expprovind` is a statement about *one* expectation against *one constant*: for a bounded e.d. sequence of LUV-combinations $(D_n)$ and a single $b$, if $W(D_n) \ge b$ in every consistent world $W$, for all $n$, then $E^H_n(D_n) \gtrsim_n b$. The step's two-expectation inequality is therefore really an argument about a single difference bet, in four small moves:

  1. *Package the comparison as one bet.* Set $D_n := \ulcorner E^A_n(V_n)\urcorner \cdot w_n \;-\; v \cdot w_n$. The product $\ulcorner E^A_n(V_n)\urcorner \cdot w_n$ is itself a legitimate bounded LUV: both factors are $\Gamma$-decided, so $\Gamma$ proves the product formula names the rational $w_n \cdot E^A_n(V_n)$, and its range sits in $[\min(a,0), \max(b,0)]$. Hence $D_n$ is a bounded LUV-combination with **constant** coefficients $(1, -v)$ — a legal member of the class 4.8.10 quantifies over, e.d. because its formula only reads the ledger.
  2. *Check the world-bound, at a constant threshold.* By (c), in every consistent world $W(D_n) = \big(E^A_n(V_n) - v\big)\, w_n \ge 0$ — indeed $D_n$ takes the *same* value in every consistent world, both factors being decided; 4.8.10 needs only the bound. Crucially the threshold is the constant $0$, uniform in $n$: 4.8.10 has no form with an $n$-varying threshold, which is exactly why the step is arranged as a *difference bet against $0$* rather than as a direct comparison of two $n$-varying quantities. (Where an $n$-varying provable value genuinely must be carried — the second step's carry — the workaround is the $\varepsilon$-outside pattern: for each fixed $\varepsilon$ the eventual provable bound "$\ge -\varepsilon$" *is* constant, and $\varepsilon$ is diagonalized afterwards. Here no $\varepsilon$ is needed.)
  3. *Apply 4.8.10* at $b = 0$: $\;E^H_n(D_n) \gtrsim_n 0$. One expectation, one constant — the theorem as stated.
  4. *Split with linearity.* The novice's `loe` (4.8.4) — with the provable definitional identity $\Gamma \vdash D_n = 1 \cdot \big(\ulcorner E^A_n(V_n)\urcorner \cdot w_n\big) + (-v) \cdot w_n$ and the bounded, trivially $H$-generable constant coefficients $1$ and $-v$ — converts the one-bet statement into the two-expectation statement:
  $$ E^H_n(D_n) \;\approx_n\; E^H_n\big(\ulcorner E^A_n(V_n)\urcorner \cdot w_n\big) \;-\; v \cdot E^H_n(w_n). $$
  Combined with move 3, this is the third step's inequality. $\blacksquare$

  This two-move pattern — `expprovind` on a single provably-signed difference bet at a constant threshold, then `loe` with constant coefficients to split — is what "carried through $E^H_n$ by provability induction" abbreviates everywhere on this page: the low side's chain and the band pinch of §"The other direction" use it verbatim with the sign (respectively both signs) flipped.

## The other direction, and the limit-equality

The chain's first two steps never consult the *direction* of the ramp: facts (a) and (b) used only that the weight is ledger-decided, $[0,1]$-valued, and generable from the expert's own prices. So what the proof actually establishes, before any threshold arithmetic, is the two-sided **fold equality**

$$ E^H_n\big(V_n \cdot u_n\big) \;\approx_n\; E^H_n\big(\ulcorner E^A_n(V_n)\urcorner \cdot u_n\big) \qquad\text{for every such weight } u_n $$

— the `ccee`-shaped conditional tower. Both halves of Total Trust are one-sided shadows of this single equality, cast through the ramp arithmetic of (c); at weights that are provably $1$ it specializes to [[provable-bound-respect]]-style unconditional floors. Nothing in the chain is soft except the weight itself.

**The low side.** Define the down-ramp $\operatorname{Ind}_\delta(x < v) := \operatorname{Ind}_\delta(-x > -v)$ — equal to $1$ for $x \le v - \delta$, to $0$ for $x \ge v$, linear between — and take $u_n := \operatorname{Ind}_\delta(\ulcorner E^A_n(V_n)\urcorner < v)$: decided and generable exactly as in (a) and (b). It is positive only where the quote is *below* $v$, so $\big(E^A_n(V_n) - v\big)\, u_n \le 0$, giving $\Gamma \vdash \ulcorner E^A_n(V_n)\urcorner \cdot u_n \le v \cdot u_n$. The chain reruns verbatim with only the last step's direction reversed:

$$ E^H_n\big(V_n\, u_n\big) \;\approx_n\; E^H_n\big(\ulcorner E^A_n(V_n)\urcorner \cdot u_n\big) \;\lesssim_n\; v \cdot E^H_n\big(u_n\big). $$

*(Alternative bookkeeping.* The low side is also literally an **instance** of the high side, applied to $(-V_n)$ at threshold $-v$ — the definitional-economy route, useful when Total Trust is stated with the high side only. It carries one wrinkle worth naming: that route's weight ramps over the quote $\ulcorner E^A_n(-V_n)\urcorner$, which equals $-E^A_n(V_n)$ only up to the expert's asymptotic `loe`; since the ramp is $1/\delta$-Lipschitz, the two candidate weights differ by $o(1)/\delta$ per fixed $\delta$, absorbed by the same $\varepsilon$-outside carry as the proof's second step. Rerunning the chain directly, as above, avoids the wrinkle entirely.)*

**The limit-equality (band conditioning).** The two halves combine into the conditional *equality* that the DDB notion gestures at. Fix a rational $s$ and rationals $\varepsilon > \delta > 0$, and take the **band weight**

$$ b_n \;:=\; \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner > s - \varepsilon\big) \,\cdot\, \operatorname{Ind}_\delta\big(\ulcorner E^A_n(V_n)\urcorner < s + \varepsilon\big), $$

a product of ramps — still decided, still generable, $[0,1]$-valued, positive only where the quote lies strictly between $s - \varepsilon$ and $s + \varepsilon$. Ramp arithmetic now runs in *both* directions on the same weight,

$$ \Gamma \vdash\; (s - \varepsilon)\, b_n \;\le\; \ulcorner E^A_n(V_n)\urcorner \cdot b_n \;\le\; (s + \varepsilon)\, b_n , $$

and the fold equality pinches the novice from both sides:

$$ (s - \varepsilon)\, E^H_n(b_n) \;\lesssim_n\; E^H_n\big(V_n\, b_n\big) \;\lesssim_n\; (s + \varepsilon)\, E^H_n(b_n). $$

Wherever the conditioning mass does not vanish — along any subsequence with $E^H_n(b_n) \ge \mu > 0$ — dividing through gives the normalized reading: the conditional expectation $E^H_n(V_n\, b_n)\,/\,E^H_n(b_n)$ lies within $[s - \varepsilon,\, s + \varepsilon]$ asymptotically. *Conditional on the expert's estimate sitting in a small band, the novice's conditional estimate sits in the same band* — the limit-equality form of Total Trust, i.e. Reflection **over estimates**. This is the ceiling of the hierarchy, and the construction shows exactly why: the band weight ramps over the expert's published *estimate*, a decided fact; Reflection proper would condition on the expert's entire *identity*, which no legal weight can express and no modest expert knows ([[deference-notions]] §Reflection). The mass caveat is essential and standard: on days the novice gives the band no credence, conditioning on it is vacuous and no normalized statement exists — the unnormalized pinch above is the honest universally-valid form.

## Place in the circuit — the loop closes

$$ \textbf{Total Trust} \;\xrightarrow{\;\text{(H2), (H3)}\;} \; \textbf{Value} \;\xrightarrow{\;\text{(H2)}\;} \; \textbf{Tower} \;\xrightarrow{\;\text{this page}\;} \; \textbf{Total Trust} $$

- **Total Trust ⟹ Value** — bounds transfer + self-endorsement; where conditional-stability (H3) and introspection (H2) are spent: [[total-trust-implies-value]].
- **Value ⟹ Tower** — probe menus; (H2) only, and (H3) is vacuous on the probes: [[value-implies-tower]].
- **Tower ⟹ Total Trust** — this page; no deference-side hypothesis beyond Tower itself, the expert's own `loe`, and observability.

So around the whole loop, the decision-theoretic scope condition is charged **exactly once** (on the first arrow), introspection is charged on the first two (and subsumed by the expert's inductor-hood here), and the channel condition — the ledger prices the closure class each arrow needs (argmax composites; gap-bets and constants; ramp-weighted products) — is charged identically at every corner. On conditional-stable menu sequences the three notions therefore stand or fall together, at matching asymptotic grade. Each arrow's bet-class needs stay inside the single natural class of e.d. bounded LUV-combinations built from base bets plus observable quotes, per the closure paragraph of [[value-implies-tower]].

The fold is also the only known full-strength entry into Total Trust from below. The alternative — closing from Value through the two-option identity — computes the *hard* above-threshold inequality, which is **false** at bets whose quote hovers on the threshold (there the soft form is vacuous-true and honest scope-restricted Value is silent); the liar-probe certificate is at [[loop-direction]]. Entry into soft Total Trust rides a weighting, never a selection — the loop's direction is forced, not stylistic.

## Status

**PROVED (prose, this page)** — three facts and a three-step chain, each step an `Approx`/`AsympLE` composition of the shape already exercised in `lean-deference`; a natural machine-check candidate alongside its two companion arrows (the Lean honesty caveat of [[conventions-and-status-labels]] applies). **Unvetted by Abram as of 2026-07-27; not machine-checked.** Written in the 2026-07-27 session to close the loop for the *Boundedly Rational Trust* slides; supersedes, for the true LI setting, the abstract fold + threshold-bound sketch recorded at [[deference-notions]] §Total Trust. Expanded same day at Abram's request: the low side derived directly (and via the $-V_n$ instance route, with its Lipschitz wrinkle); the band-conditional limit-equality added; the `expprovind`+`loe` pattern behind step 3 spelled out. Revised 2026-07-28 per Abram's exposition feedback (now recorded in [[conventions-and-status-labels]] §Exposition style): "cut" dropped in favour of the two *halves* of the condition; the shadow variables for the quote and the weight's decided value eliminated; the ramp-arithmetic case split compressed to its one-line content — the ramp is positive only where the quote exceeds the threshold.

## Related

- [[total-trust-implies-value]] — the first arrow (the expensive one); the setting this page inherits; Lemma 1's timing remark and $\varepsilon$-outside pattern
- [[value-implies-tower]] — the second arrow; delivers the Tower quantifier this page consumes; the circuit paragraph this page completes
- [[deference-notions]] — the notions; the abstract fold this page re-proves in the true setting
- [[provable-bound-respect]] — the provably-full-weight specialization
- [[total-trust-implies-mart]] — the converse squeeze (Total Trust ⟹ Tower by gap-bets), the loop's redundant-but-instructive diagonal
- [[loop-direction]] — why the loop runs in this direction: the two-option alternative to this page's fold dies at quote-hovering bets (the liar probe)
- [[expert-conditions]] — what observability and introspection mean per instance

*Source: this page (2026-07-27 Claude Code session), at Abram's request to close the loop for the slides; apparatus from [[total-trust-implies-value]] and the LI paper (`loe` 4.8.4, `expprovind` 4.8.10).*
