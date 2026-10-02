# dp-learner-nr — findings about the sources

Severity scale ([STANDARDS](../../STANDARDS.md) §5): **blocking** (the note's conclusion does not follow as printed) / **local error** / **imprecision** / **presentation**. Each entry names the Lean declaration that settles it where one exists (namespace `Cleanroom.Decision.DpLearnerNr`, files under `Cleanroom/Decision/DpLearnerNr/`). Attribution claims about what a person meant are labelled ATTRIBUTION-UNVETTED per `research/CLAUDE.md`. Formalizer: Fable 5.1 [scrubbed], 2026-10-01. Mandate: `dp-learner-nr-mandate`.

## F1 — The tremble swamping is bypass-specific (mandate known issue 1) — **imprecision**, proved in Lean

Source: [tb-theta-shadow](../../sources/decision-problems/wiki/tb-theta-shadow.md) "What the tree shows" ("**'The troll punishes exploration' is reproduced, not confirmed:** fixed forced mass swamps vanishing trembles. At `θ = 0.05`, `P(bad∣cross)` at the stay label is `0.513, 0.913, 0.991, 1.000` …"); [clean-source-and-policy-responsiveness](../../sources/decision-problems/directions/clean-source-and-policy-responsiveness.md) l. 84 ("every tremble device … is swamped by the forced mass").

What is proved. On the bypass `tbTheta θ` the swamping is real: `tb_tremble_stay_pBot` gives `P(bot ∣ cross) = θ/(θ + (1−θ)ε/2)` at the stay label, `tb_tremble_stay_swamped` gives the explicit limit (`> 1 − δ` for `0 < ε < δθ`) and `tb_tremble_stay_neg` re-founds dp-sl-2-071's `tremble_neg` (`Tremble.lean`). On the doc-faithful tree — the one the same wiki page calls "*verbatim* Proposition 10's rule" — every tremble device returns `P(bot ∣ cross) = θ` and the value `10 − 20θ` at every label and every `ε > 0` (`tbThetaDoc_tremble`), and `swamping_contrast` states both under one hypothesis package. So the qualitative claim about Troll Bridge ("the troll punishes exploration is reproduced") rests on the tree the note itself says is the wrong shape; on the doc-faithful tree nothing is swamped, because crossing carries no forced mass. The five-evaluation split of the wiki's table is likewise bypass-specific: on the doc-faithful tree every evaluator except per-node forcing coincides at `10 − 20θ` — at mixed labels `q > 0` (`tbThetaDoc_five`); under every tremble `ε > 0` of the stay label the act-conditional and `nuCond` are `10 − 20θ` and `θ` directly (`tbThetaDoc_tremble`, `swamping_contrast`), and the other evaluators there follow from `tbThetaDoc_five` at the label `ε/2` through the identification `tremble (procQ 0) ε = procQ (ε/2)` (a `FinDistr` extensionality, `tremble_procQ_w`; not shipped — audit r2 fidelity N6). The wiki's table and its act-conditional `−10` are the bypass tree's at the *untrembled stay label* `q = 0`, where the doc-faithful tree's act-conditional is the junk value `0/0 = 0` (`tbThetaDoc_stay_condExp_junk`), not `10 − 20θ`; at mixed labels the bypass act-conditional `(−10θ + 10(1−θ)q)/(θ + (1−θ)q)` still differs from `10 − 20θ`, so the split is bypass-specific there too. (Wording corrected at audit r1 fidelity §3.1.) Surviving neighbour: the wiki's own "Bypass-shaped versus doc-faithful" paragraph, now with the contrast as one theorem.

## F2 — The threshold reader is undefined at `q = ½`; the printed one-box threshold is the corner comparison, not the grid comparison (mandate known issue 2) — **local error / presentation**, proved in Lean

Source: [policy-level-fdt-learner](../../sources/decision-problems/directions/policy-level-fdt-learner.md) §2.2 ("Against a *threshold reader* (`f = r` if `q > ½`, `1−r` if `q < ½`) … the learner sits at `q = 0.6` and collects `M·r + 0.4K` … One-box iff `r > ½ + K/2M = 0.5005`").

The grid `Π = {0, 0.1, …, 1}` contains `0.5`, where the note's `f` is undefined. With `f(½) := 1 − r` (`thr`, `PolicyValues.lean`) the grid argmax is `6/10` iff `r > ½ + 3K/(10M)` (`newcomb_threshold_grid_iff`): the comparison is `M r + (2/5)K > M(1−r) + K`, not the `q = 1` versus `q = 0` corner comparison `M r > M(1−r) + K ⟺ r > ½ + K/(2M)` that the note prints (`newcomb_threshold_corner_iff`). At `M = 1000, K = 1` the two thresholds are `0.5003` and `0.5005`. With `f(½) := r` instead, the grid label `½` beats `6/10` whenever `K > 0` (`newcomb_threshold_half_wins`; only "beats `6/10`" is proved — that `½` is then the grid argmax also needs `r > ½ + K/(2M)`), so "`q = 0.6`" also depends on the convention at `½`. The note's sentence "One-box iff `r > ½ + K/2M`" admits both readings — the corner comparison `q = 1` vs `q = 0`, under which it is right (`newcomb_threshold_corner_iff`), and the grid-argmax switch, under which the threshold is `½ + 3K/(10M)` (`newcomb_threshold_grid_iff`); the parts that do not survive as stated are the undefined `f(½)` and the printed label `0.6`. The note's verdict (one-box against a sufficiently accurate threshold reader, exploit its level set) survives.

## F3 — NR1 versus ¬(β) is not a modal distinction (mandate known issue 3) — **imprecision**, shown in Lean

Source: [non-responsiveness](../../sources/decision-problems/wiki/non-responsiveness.md) "NR1" ("Non-responsiveness is *not* the bare negation of (β) — a constant crosser, a constant stayer and a coin all negate (β) — but the replacement of (β) by (β′) with a specific `P₀`").

In GL the constant crosser `⊤` *is* a `BetaPrime` agent (`betaPrime_top`, with `r := ⊤`), and the constant stayer `⊥` is one too and satisfies the schema `H ⊥` (`betaPrime_bot`), so "negates (β)" cannot be rendered as `⊬ H c` either: the modal (β) is a schema, not a biconditional with an expectation term. The distinction the note draws lives in the arithmetic layer (a specific `P₀`, a specific comparison), which D1 abstracts to "GL decides `r`" (`Modal.lean`). The note's claim is true in its arithmetic reading; it has no modal rendering, and the package does not invent a predicate to separate the cases.

## F4 — Axiom NR does not pin NR-cf at the stay label (mandate known issue 4) — inherited, cited

`dp-causal-consist`'s `cfNR_ne_kPart` (finding F4 there). This package states the K-partition identity only at mixed labels (`cfMarginal_eq_kPart_tb`, `tbThetaDoc_nrcf_cross`) and cites F4 at the stay label rather than claiming a value. Not re-litigated.

## F5 — Numerals that are not theorems (mandate known issue 5; plan rule 4) — **presentation**

- **"exact 0.4574"** (`dp-cf-2-inventory` 024, `dynamic.md` DY-14: "`P(refuse forever)` … Beta(1,1), θ=0.6: 0.457 myopic (exact 0.4574)") is an infinite-horizon absorption probability with an unstated truncation; it is not a theorem of this package. Target 12 (not reached) would state `P(trap) ∈ [2/5, 1/2]` with the lower bound exact (the first heads episode traps w.p. `1 − θ = 2/5`).
- **"4"** for the enforcer payoff ([non-responsiveness-learnability](../../sources/decision-problems/directions/non-responsiveness-learnability.md) §8 C: "enforcer payoff when cross, u=+10: 4") is at payoffs scaled by `10`; at `q = 7/10`, `c = 3/10` the payoff is `2/5` (`enforcer_instance`). The identity itself is `enforcer_payoff`: `q − c` on `A = a`, `0` otherwise, in every world.
- **`19/40`** ([non-responsiveness-learnability](../../sources/decision-problems/directions/non-responsiveness-learnability.md) §8 B: "largest coherent `P(cross)` at which the unshielded agent still crosses = 19/40") is a grid artifact (step `1/40`, `ε = 1/100`); the theorem is `P(Cross) < ½ + ε` (`nr1_unshielded_threshold`), and the crossing instance `P(Cross) = 2/5 < ½ + 1/100` is shipped (`crossWitness_facts`). The grid value `19/40 = 0.475` is below `0.51` as it must be; nothing finer is claimed.
- The swamping decimals `0.513, 0.913, 0.991, 1.000` and the values `−0.26, −8.27, −9.81, −10.00` ([tb-theta-shadow](../../sources/decision-problems/wiki/tb-theta-shadow.md), dp-core-2-016) are instances of `tb_tremble_stay_pBot`/`tb_tremble_value`; one exact instance (`20/39` at `θ = 1/20, ε = 1/10`) is shipped (`tb_tremble_stay_instance`).
- The simulation totals `2620`/`17520` (§2.2) and the flag-reading Omega's `≈ 740` versus `≈ 501` ([policy-level-fdt-learner](../../sources/decision-problems/directions/policy-level-fdt-learner.md) §2.3) are recorded, not formalized.

## F6 — "Lemma 8's proof uses (β) exactly once" is a proof-structure claim about the GL proof shipped in `dp-troll-bridge` (mandate known issue 6) — **presentation**

Source: [non-responsiveness](../../sources/decision-problems/wiki/non-responsiveness.md) "Where it comes from" and `dp-core-2-inventory` 038 ("Lemma 8's single use of (β)").

In `dp-troll-bridge` the lesion is one use of axiom L on the boxed schema (`boxdotH_iff_boxdot_neg`, `lobian_lesion_schema`); "exactly once" is a fact about that proof, not about the doc's. What this package proves is the *consequence* the note draws: under (β′) a decided crosser is unafflicted (`betaPrime_crosser_not_afflicted`), so the step the note calls "from `P(□⊥ ∣ Cross) = 1` to `¬Cross`" has no counterpart — the (β′) agent's crossing is decided by a comparison the hypothetical proof cannot reach.

## F7 — The leak: the session note's §9.3 reason was wrong and the wiki's correction is now a theorem — **local error** (in the superseded note), resolved

Source: [marginal-formula-learner](../../sources/decision-problems/wiki/marginal-formula-learner.md) "The act-level agent" item 2 ("*corrected*: the session note said the formula alone shields the marginal because the proof constrains `P(w ∣ a)`, never consulted. Wrong as the reason: under coherence a believed `Cross → □⊥` moves `P(□⊥)` through `P(Cross)`"); [non-responsiveness](../../sources/decision-problems/wiki/non-responsiveness.md) "NR2".

`leak` (`Leak.lean`): for any finitely additive `P` with `P(Cross → Incon) ≥ 1 − ε`, `P(Incon) ≥ P(Cross) − ε`; `nr1_unshielded_threshold`: an NR1 rule fed `P`'s own `Incon`-marginal crosses only if `P(Cross) < ½ + ε`; `li_leak` (`LeakLI.lean`): the same at the LI level, asymptotically, by affine provability induction composed with `dp-troll-bridge`'s coherence step. The wiki's `19/40` sentence and the N+ witnesses agree. The shield is the *language* (NR3), which FAF cannot render (F10).

## F8 — The one-point learner's "verbatim Proposition 10" identification is ATTRIBUTION-UNVETTED — **presentation**

Source: [tb-theta-shadow](../../sources/decision-problems/wiki/tb-theta-shadow.md) ("*verbatim* Proposition 10's rule 'cross iff `10 − 20 P₀(□⊥) > 0`' with `P₀ = θ`"); [clean-source-and-policy-responsiveness](../../sources/decision-problems/directions/clean-source-and-policy-responsiveness.md) §9 C.

The doc has no tree. What the package proves is the *value* identity: the doc-faithful tree's deviation gap is `10(1 − 2θ)`, positive iff `θ < ½` (`tbThetaDoc_gap_pos_iff`), and the one-point learner's greedy policy is `cross` iff `θ < ½` (`onePointLearner_facts`). That the doc's bridge *is* `tbThetaDoc` is a reading; the identification of 𝔅 with `CDT_G` (`bot → m`) is `dp-causal-consist`'s T7. The wiki's "verbatim" is accurate for the rule, not a claim about a tree the doc contains.

## F9 — "Inert" in the refuser trap must mean "no transfer on heads" — **imprecision** (in the mandate's gloss; the sources are consistent)

Source: `dynamic.md` DY-13 ("instantiations `h₁` (Omega couples) and `h₀` (heads branch inert) … a refuser's data have likelihood ratio 1"); `grounding.md` GR-15 ("pay iff `π > x/y`"); `dp-learner-nr-mandate` target 11(a) ("an inert variant where the heads branch pays regardless").

Under `δ_refuse` the coupled mugging gives `hZero` on heads; for the likelihood ratio to be `1` the inert branch must also give `hZero` on heads — i.e. *no* transfer whatever the act (`mugInert`, `Refuser.lean`; `refuser_nu_eq`). Under that reading the myopic rule is exactly the sources' `(πy − x)/2 > 0 ⟺ π > x/y` (`myopic_pay_iff`): paying under `h₀` costs `x/2`, earns nothing. A heads branch that "pays regardless" (transfers `y` whatever the act; `mugPaysRegardless`) would make the refuser's heads episodes informative — `hOne` has mass `0` on `mug1` and `½` on the pays-regardless mugging (`refuser_informative_paysRegardless`) — so the likelihood ratio would not be `1`. The myopic rule does *not* decide between the readings: under pays-regardless the heads transfer `y/2` enters both `𝔼[pay]` and `𝔼[refuse]` and cancels, and `𝔼[pay] − 𝔼[refuse]` is the same `(πy − x)/2` (`myopic_pay_paysRegardless`). So the choice of reading rests on the likelihood-ratio clause alone. (Audit r1 fidelity §2.1 refuted an earlier version of this paragraph that claimed the pays-regardless reading contradicts the stated rule; corrected 2026-10-01, with the correction a theorem.) The mandate's gloss is the imprecision; DY-13 and GR-15 are consistent with the no-transfer reading.

## F10 — NR3 (the anonymous marginal) is not formalizable in FAF; NR2-for-NR3 is by construction — **imprecision** in what can be claimed, recorded

Source: [non-responsiveness](../../sources/decision-problems/wiki/non-responsiveness.md) "NR3"; `dp-learner-nr-mandate` target 8 trap (iii).

FAF has no object for "a sublanguage not naming the agent", so the two-inductor architecture is not stated. The package renders NR3's *consequence*: the NR3 rule's marginal `p` is a free sequence with no coherence link to `cross` (`e1_static` takes `limsup p < ½` as a hypothesis), and the per-round lesion is refuted at the modal level by decidedness (`conjectureF_v_per_round`) and at the LI level by a world (`li_decided_crosser_no_lesion`). No theorem "NR3 ⟹ NR2" is shipped: it would be a definitional squeeze (the marginal is a different history that nothing links to `cross`). The claim that an LI over `𝓛_exo` can still learn about `w` from observations is not attempted.

## F11 — E3's separators, collected (mandate target 8(e)) — recorded

- The **unshielded marginal learner** (one coherent inductor) satisfies E1's conclusion on the original troll only on days with `P(Cross) < ½ + ε` (`nr1_unshielded_threshold`) and is trapped by the self-misprediction troll (`self_misprediction_troll_lesion`, `self_misprediction_troll_stays`: the exploring-agent schema with `x` read as "crossed while `P_t(cross) < ½ + ε`").
- The **exploring-agent troll** as a tree (`tbThetaExplore`, `Explore.lean`) punishes every coin crossing (LICDT `= −10` at every label) and leaves the deliberate label's gap `10(1−ε)(1−2θ)`: the NR3 learner's deliberate crossings are unpunished and its verdict is Proposition 10's rule scaled by `1 − ε`.
- The **flag-reading Omega** and the **stricter troll** are not policy-fair (`flagFill_not_policyFair`, `stricterTrigger_not_policyFair`): there is no round law `F(π, w)`, so the learner's verdict there is an artifact of its exploration schedule — a trap, not a dilemma, in the 2020 journal's second test (ATTRIBUTION-UNVETTED as a reading of the journal).

## F12 — E2 (the growing-bound Löb) is OPEN-in-prose; FAF has no bounded provability (mandate target 18) — recorded

Sources: [non-responsiveness-learnability](../../sources/decision-problems/directions/non-responsiveness-learnability.md) §5 E2; [policy-level-fdt-learner](../../sources/decision-problems/directions/policy-level-fdt-learner.md) §4.5, §6 negative half; `dp-core-2-inventory` 047, 041.

FAF's `Modal.GL` has one box; a parametric `□_M` is not statable without touching FAF's logic, and a Kripke-frame rendering (a family of accessibility relations indexed by `M`, converse-well-founded in the limit) was not written. The three notes' diagnosis stands as prose: fixed `M` safe (the only modal content is target 8(b)'s "a decided crosser is unafflicted"), growing `M` eventually trapped, the proof-length/search-bound fixed point unwritten (post 11 l. 174 "I omit the proof here"). The asymptotic Löb over `∀^∞ t (cross_t → bad_t)` is Σ₂ about an LI's limit; FAF has no provability predicate over LI-limit statements. No Lean statement is shipped; failure to state is not evidence either way.

## F13 — The conditional-contract bundle is not a FAF `Sentence`; Claim CC-limit is pointed, not proved (mandate target 9) — recorded

Source: [non-responsiveness-learnability](../../sources/decision-problems/directions/non-responsiveness-learnability.md) §2.1 ("Claim CC-limit … not in the sources as stated").

The enforcer's payoff identity is exact rational algebra (`enforcer_payoff`); the LI claim (`∑_{t : A_t = a} |c_t − q_t| < ∞` from non-exploitability) needs a market good whose world-value depends on its own price (the refund), which FAF's `Sentence`/`Valuation` cannot express; it is `li-splice-condition`'s per `plan`. The toy-market crossings `0, 5, 11, 17` are illustration. Whether the author already had the prior-independent form is ATTRIBUTION-UNVETTED (the note says so itself).

## F14 — dp-sl-070 (Eisenstat's tiling result via Appel) — recorded only, ATTRIBUTION-UNVETTED

`dp-sl-inventory` 070 reports, through `sl-workflow/posts/08-…md` ll. 41–45, a tiling result and a non-correctibility criterion attributed to Eisenstat. The primaries were not read; the result is out of this package's type (no LI criterion for correctibility is stated here). Per the mandate this item's plan §9 row reads `recorded in dp-learner-nr-findings, not a target`.

## F15 — The per-variable partition test is rendered at the type level — **presentation** (a disclosed (c))

Source: [policy-level-fdt-learner](../../sources/decision-problems/directions/policy-level-fdt-learner.md) §1.2(iii), §1.5(c); `dp-learner-nr-mandate` D4.

`PolicyLearner` (`Policy.lean`) carries `W` (exogenous configurations) and `R` (responsive observables) as types, with `ExogenousCoord L visited f` the invariance of the pushforward along a coordinate map `f` — the per-variable test for `f := Prod.fst` and for any coordinate of a product. `E` is the per-cell *mean* payoff, not the histogram. Both are disclosed in the structure's docstring; the Dirichlet-multinomial test itself (target 17) was not reached.

## F16 — The "exploration coin is a world coordinate" renders hypothesis H's (h1) failing on purpose — **presentation**

`tbThetaExplore` (`Explore.lean`) writes the exploration coin into the world (`ExW := Bool × Bool × Act2`) and the payoff reads it (`exPay`); this is exactly the failure of `dp-referents-cdt`'s P04-A′ hypothesis (h1) ("no payoff reads the coin"), which is what the exploring-agent troll *is*. The separation LICDT `−10` versus the deliberate gap `10(1−ε)(1−2θ)` is the tree-level form of [clean-source-and-policy-responsiveness](../../sources/decision-problems/directions/clean-source-and-policy-responsiveness.md) §9 C's row; the P04-A′ coincidence under H (target 16(a)) was not formalized here.

## F17 — Conjecture F(v) as printed is false at staying rounds; the surviving form is "at every crossing round" — **imprecision**, proved in Lean (added at repair round 1)

Source: [policy-level-fdt-learner](../../sources/decision-problems/directions/policy-level-fdt-learner.md) §6 Conjecture F (v) ("For every `t`, `T ⊬ (π_t = cross → □⊥)`").

At a round where the decided learner *stays*, `T ⊢ ¬(π_t = cross)`, hence `T ⊢ (π_t = cross → □⊥)` by propositional logic — the lesion sentence is provable, vacuously. In the package's modal rendering this is the second disjunct of `conjectureF_v_two_cases` (`Modal.lean`): at every round the (β′) agent either provably crosses and `GL ⊬ (cross t 🡒 □⊥)`, or provably stays and `GL ⊢ (cross t 🡒 □⊥)` (`betaPrime_stayer_vacuous_lesion`, via `dp-troll-bridge`'s `dispositional_respect_two_cases` (i)). So (v)'s unqualified "for every `t`" is false whenever some round's comparison favours staying; the correct statement is "at every crossing round" — which is exactly `conjectureF_v_per_round` (`GL ⊢ r t → GL ⊬ (cross t 🡒 □⊥)`). The note's intended content (Proposition 10 iterated, the agent is never *trapped*) survives; the quantifier does not. Pointed out by audit r1 adversarial §3.8.
