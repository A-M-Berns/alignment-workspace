1. **The runner reproduces the advertised results. That does not earn all the advertised conclusions.** I ran `python3 -B run.py --json` from `round/`; it exited successfully with no reported failures. I also ran independent, in-memory checks using Python 3.13. I changed no files.

   Reproduced: 3,000 candidates, 15 admissible, eight under strong independence; 47/47 adverse Values sequences detected; statement 5’s 80 situations and 31 zero-gap situations; the comparison counts 27/33/46; maintenance leaving ten candidates; withdrawal agreeing at 33/48; and the addenda’s 16 closed and 93 free relations.

   The runner compares statuses with booleans computed by the same implementation. Several booleans check substantially less than the corresponding prose. Passing this runner establishes internal consistency of selected computations, not fulfillment of the dispatch.

2. **Statement 1 is refuted for the chosen formalization. The claim that the dispatch’s constraints have thereby been refuted is not earned.** The class in [theorems.py:23](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:23) is exactly the advertised Cartesian product and contains the named cheats. It is a legitimate finite witness class: a counterexample does not require representative sampling.

   But it fixes the decomposition, available information, action repertoire, normal distribution and almost all functional forms. It is not a survey of plausible decompositions. More importantly, admissibility implements consequentially weak readings of the dispatch. The 15 candidates establish non-determinacy **under those readings**, not under every faithful interpretation.

   The eight surviving strong-independent candidates really do have eight distinct classification signatures. “They agree except on `false_reason`” concerns the coarse question whether an action subverts *some part at some world*. They still disagree pointwise about `trick`, `tempt` and `hard_truth`, as [THEOREMS.md:69](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:69) acknowledges. That qualification must accompany the headline.

3. **The independence test does not test independence from the mechanism.** The `mech` purposes explicitly call the mechanism captured in their closure: [scenes.py:126](/private/tmp/legit-review-2026-11-12/round/decomposition/scenes.py:126), lines 139–140 and 151–155. The admissibility test instead checks nonconstancy and an optional `reads_mechanism` tag, which these candidates never set: [model.py:236](/private/tmp/legit-review-2026-11-12/round/decomposition/model.py:236).

   Hiding the mechanism in a closure rather than a formal argument does not make a purpose independently stated. Thus the most theatrical counterexample—“whatever she does,” with mechanism-defined purposes—survives an inadequate independence test.

   Conversely, the proposed stronger test is not semantic independence either: it requires actual failure somewhere. An independently specified purpose can be performed flawlessly. Excluding perfection is an unrelated restriction.

   The second condition, “carriable,” has deliberately been made redundant on the tested unforced normal domain: the actual mechanism witnessing mostly-serving also witnesses carriability. This is disclosed in [ACCOUNT.md:129](/private/tmp/legit-review-2026-11-12/round/decomposition/ACCOUNT.md:129), but means that one of the dispatch’s intended constraints contributes nothing to the central experiment.

4. **“Never opposed” is materially weaker than its ordinary reading, and strengthening it changes the central result.** [model.py:218](/private/tmp/legit-review-2026-11-12/round/decomposition/model.py:218) checks only improvements over the move actually made. When the actual move already maximizes the part’s purpose, the condition says nothing—even if pursuing that purpose systematically damages the whole.

   I replaced that anchored comparison, in memory, with the natural pairwise condition: whenever one possible move scores higher than another for the part, its downstream outcome must not score lower for the whole, on the same normal situations.

   Results:

   - Of the original 15, only the all-`mech`, goal-`does` cheat survives.
   - Excluding mechanism-defined purposes as well leaves **zero**, not one.
   - Excluding hard worlds from “normal,” while retaining clear and misleading worlds, leaves two non-`mech` candidates: `acc/world/world` and `acc_theta/world/world`.

   A witness is belief at `(0, hard)`: improving from false to true belief changes the judge from correct to incorrect. The original condition misses this because the actual belief is already true. Local judge and act purposes also fail pairwise comparisons at misleading worlds.

   Therefore a stronger reading does not straightforwardly restore determinacy: on the stated normal domain it exposes inconsistency. Changing normality can restore a small surviving class, but the remaining difference about unused `φ` requires another substantive condition. The work has not established which interpretation is faithful.

5. **Statement 9’s finite examples are correct, but the claimed dilemma about “nothing left over” is false.** The global-maxima implication in [model.py:204](/private/tmp/legit-review-2026-11-12/round/decomposition/model.py:204) correctly implements [ACCOUNT.md:113](/private/tmp/legit-review-2026-11-12/round/decomposition/ACCOUNT.md:113). Stuck satisfies it while both parts have zero gaps at the inferior equilibrium; the tumour example satisfies it vacuously. The resolving signal helps both parts. Those results earn the narrow status.

   But the alternatives are not limited to the adopted implication and “every zero-gap profile is globally optimal.” Require **joint attainability of the parts’ global maxima**, in addition to the adopted implication. That rejects the tumour example and retains Stuck, whose jointly maximizing profile is `(hi, hi)`. The conclusion at [THEOREMS.md:371](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:371) omits this elementary third option.

   I checked vacuity across the 15: five candidates have some vacuous situations. Adding joint attainability leaves ten; combining it with the existing strong-independence filter leaves four. Thus vacuity contributes to non-determinacy, but does not explain all of it.

   Also, `check_9`’s second “independence” witness checks failure of **fit**, not failure of **serving** ([theorems.py:541](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:541)). The proposition can be supported by other examples, but that particular check does not establish what the prose says.

6. **Statement 2’s universal lying claim is genuinely false, although some counterexamples inherit statement 1’s defects.** At misleading worlds, `lie` supplies the false belief already produced by nature. No gap widens. This counterexample survives eliminating mechanism-defined purposes: worsening relative to a baseline cannot detect every repetition or reinforcement of an existing falsehood.

   The unused-`φ` counterexample also reproduces: four of eight strong-independent candidates ignore it. Whether those are admissible depends on what fixes belief’s subject matter. The all-`mech` counterexample is considerably less persuasive for the reasons above.

   The information table in [THEOREMS.md:139](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:139) reproduces. Its wording about a constant claim being “a garbling to no information” needs qualification: the mechanism’s view still contains nature’s signal. That surviving information is precisely why its best achievable expected score is `39/20`, rather than the uninformed score. The distinction between optimal signal use and the actual mechanism is otherwise sound.

7. **Statement 3’s refutation is earned.** I reproduced the 144 tested triples: 93 nothing, 26 help-only, 19 subversion-only, two harm-only, and four help-plus-harm. The threat rescaling changes the judge’s label from harm to help while preserving its within-situation ranking: [theorems.py:205](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:205).

   The invariance proof for zero versus positive gap is correct under strictly increasing transformations. It does not establish invariance of positive-gap comparisons or thresholds.

   Two qualifications: these 144 triples exclude the force actions, so they are not an exhaustive enumeration of all the advertised actions; and the reported 29 bank cases combine labels across worlds, steps or parts. That number does not demonstrate 29 instances of simultaneous help and subversion at one part in one situation.

8. **Statement 4 does not earn “C2 refuted” in the sense the dispatch asked.** Its decisive counterexample, Y7, changes a coordination signal and hence actions; it does not change a mechanism, taste or what she cares about. Stuck has no alteration moves. Yet [ACCOUNT.md:147](/private/tmp/legit-review-2026-11-12/round/decomposition/ACCOUNT.md:147) defines the relevant change as a write to a taste. The test switches from that definition to a broader change of behavior.

   Y4 is not marked bad by the goal; the text expressly leaves its badness unresolved. The frozen bank did not mark the requisite bad changes at all. These are not adequate grounds for the categorical “C2 did not survive.”

   What is established is narrower: coordination can worsen without increasing unilateral gaps; goal-indifferent redirection is invisible to the selected scores; and all 47 adverse cases in the specified Values enumeration are detected. The last result is unsurprising because the learner and habit purposes directly score proximity to the stipulated correct taste, and act directly scores the correct pursuit.

   There is also a literal discrepancy: [THEOREMS.md:205](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:205) says T4 is “force, not a gap.” Its computed verdict includes **subversion of learn and habit**, as well as force on act.

9. **Statement 5 holds for its one selected candidate, but the general dispatch statement fails inside the work’s own admissible class.** I independently reproduced its 80 situations, 31 zero-gap instances and loss bound. This is a useful elementary composition result, not vacuous for the local-scored judge.

   However, take the admissible candidate `mech/local/world`, world `(0, clear)`, action `lie`. Belief and judge both have gap zero; the judge returns 1; the correct verdict is 0. Only act has a positive gap. I checked both admissibility and these measures. Thus zero gaps in the judge’s ancestors do **not** generally guarantee a correct verdict over the stated admissible class.

   More seriously, [REPORT-section-draft.md:283](/private/tmp/legit-review-2026-11-12/REPORT-section-draft.md:283) says statement 5 makes a **standing** verdict track her goal. Standing means no gap was newly widened, not that gaps are small or zero. At `(0, hard)`, silence against silence gives a standing, wrong verdict. The report conflates two different predicates.

10. **Statement 6 earns a toy `Scoring` and `Decision`, not the requested application of Theorems 1–3.** The numerical bounds and violation probabilities reproduce. But [theorems.py:421](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:421) awards the status from only `bounds_ok and respects`. It neither constructs a sequential model nor establishes its hypotheses.

    The bounds hold by construction: legitimate histories receive a normalized score, others a fixed negative value. Silence respects because it is compared with itself and contains no explicit force. These are valid constructions, but weak achievements.

    The implementation also uses `N = 1` exactly when `Legit` is false, collapsing authority violations into illegitimacy. And although candidates have different overall goals, `V` uses the single hard-coded `S.chain_goal()`, not the candidate’s goal ([theorems.py:390](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:390)). That is mathematically permitted by the abstract Lean interface, but it is an additional substantive choice about whose interests are scored.

    “The construction typechecks” in [THEOREMS.md:242](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:242) is unjustified wording: no such Lean construction was elaborated.

11. **The “best available action” calculation is not the adviser’s best move by her goal. This changes verdicts and invalidates the addendum’s comparison.** [theorems.py:347](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:347) minimizes the **sum of her parts’ gaps**. The adviser-as-part proposal maximizes her downstream overall goal. These objectives differ.

    At `(0, hard)`, the code chooses a **threat**, yielding `G = 2`; a lie yields `G = 3`. Nevertheless [ADVISER_AS_PART.md:23](/private/tmp/legit-review-2026-11-12/round/decomposition/ADVISER_AS_PART.md:23) identifies these baselines and reuses the 46 count.

    I replaced the baseline with downstream `G` maximization, keeping the same available actions and first-in-list tie-breaking. Convictions fell from **46 to 38**. Changed renderings: D2, D15, D19, P12, N3, N7, Y4 and Y8. The claimed nesting with silence fails at Y8.

    Testing whether the adviser itself has a positive downstream-goal gap gives **33** of those 57 renderings—yet another question. Maximizing moves can also tie while inducing different part-gap verdicts. “Its best move supplies the comparison” does not remove that ambiguity.

12. **The claim that a best-action baseline supplies no-gain is false even on the original Chain.** This is asserted in [THEOREMS.md:277](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:277), [ADVISER_AS_PART.md:66](/private/tmp/legit-review-2026-11-12/round/decomposition/ADVISER_AS_PART.md:66) and the report.

    I tested two policies against the code’s own gap-minimizing baseline. Policy 0 always selects that baseline. Policy 1 does the same except that it threatens at `(0, clear)`. Neither widens any gap at any of the six positive-prior worlds. Yet:

    - Probability of action 1 changes from `21/40` to `39/40`.
    - Expected principal goal falls from `119/40` to `101/40`.

    The threat lowers best while leaving gaps zero. A gate that checks only widening therefore permits this aim-dependent influence even against the proposed best baseline. Ties provide an additional problem, but are unnecessary for this counterexample.

13. **Statement 7 supplies a limited non-identifiability result, not the advertised general negative answer.** Identical mechanisms produce identical histories despite different latent purposes. That observation is correct. The maintenance figures and 33/48 withdrawal score also reproduce.

    But the dispatch asks about distinguishing **admissible from inadmissible** candidates; [THEOREMS.md:296](/private/tmp/legit-review-2026-11-12/round/decomposition/THEOREMS.md:296) substitutes distinguishing admissible candidates from each other. These are different questions.

    Moreover, `check_7` returns “holds” unless maintenance eliminates all relevant ambiguity **and** withdrawal perfectly matches subversion ([theorems.py:475](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:475)). Failure of that conjunction does not establish failure of every observable.

    Maintenance excludes five candidates only after adding the assumption that observed maintenance cannot lower the part’s expected purpose-score. That is not an observed fact and is not an existing admissibility condition. A fallible principal can maintain badly. “Taking back” is implemented by deleting selected input keys, not by modeling disclosure followed by reconsideration.

14. **Statement 8’s Chain computation is correct; its general mechanism-independence claim is false.** I reproduced opposition at 36 of 90 tested situations, with normal opposition confined to the hard worlds of total normal weight `1/20`.

    However, [theorems.py:486](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:486) first runs the actual mechanism, then evaluates the part’s purpose against other parts’ actual moves. Those moves can depend on its mechanism. The definition can therefore depend on that mechanism indirectly.

    I checked a two-part counterexample: `q` copies `p`; `g_p(m) = [m = q]`; the whole wants `p = 0`. Changing only p’s mechanism from constant 0 to constant 1 changes opposition from 0 to 1.

    The formula also takes the **best** whole-outcome among the part’s maximizing moves. It detects “every purpose-optimal move costs her,” not all ways in which a purpose can permit harmful performance. Calling it a general definition of “never opposed” overstates its coverage.

15. **The engine implements most of the declared finite conventions, but it permits invalid candidates and does not implement the general machinery claimed for it.** The stepwise comparison in [model.py:91](/private/tmp/legit-review-2026-11-12/round/decomposition/model.py:91) correctly branches from the actual prior state. The signs used for the four labels match ACCOUNT. `gap_owner` implements the amended view-local rule, including the zero-weight-situation dominance condition; its comment about improving other views is stale, not an implemented operation.

    The concrete validity bug is Pool. The judge’s move set is the five quarter-grid values ([scenes.py:283](/private/tmp/legit-review-2026-11-12/round/decomposition/scenes.py:283)), but `planner_reader` returns values outside it, including `1/6`. Across sixteen worlds and five display choices I found **34 illegal planner-reader moves**. `run_step` accepts them without checking membership; `measures` even includes `got` in the maximization. Expanding the move set could repair this without necessarily changing current labels, but the current purported finite candidate is malformed.

    Pool’s belief part also has a singleton move set and constant purpose, so it fails the work’s independence condition. Its bank classifications are not shown to arise from an admissible candidate.

    Finally, there is no general transitive ancestor computation. `legit` checks every part; the producer calculation uses only direct `reads`, and dependencies through carried state are not represented as such. The advertised general history semantics exceed the implementation.

16. **The bank tests weakened assertions about constructed renderings, not 89 independent successful predictions.** Four rows are `report`, which matches unconditionally: [bank.py:36](/private/tmp/legit-review-2026-11-12/round/decomposition/bank.py:36). The accurate count is **84 matches among 85 rows with predictions**, plus four reports. DIVERGENCES discloses this; the report’s “88 of 89 predictions” does not.

    Predictions such as `force` require only that force occur somewhere; they tolerate additional subversion. The report’s “computed verdict” table hides this. T4, T11 and several other force rows also contain subversion.

    Most renderings agree with the newly written CASE_BANK, but important features of the earlier cases have disappeared. N11 originally has an information bit and eight worlds ([steering/CASE_BANK.md:52](/private/tmp/legit-review-2026-11-12/round/steering/CASE_BANK.md:52)); the new four-world rendering keeps the `1/3` silence response after removing that information structure. Manufactured trust installs a belief mechanism behaviorally identical to the existing one ([cases.py:116](/private/tmp/legit-review-2026-11-12/round/decomposition/cases.py:116)). P10/P11 contain repeated teaching, without a changing reliance variable. These cannot establish conclusions about the omitted mechanisms.

17. **ACCOUNT adds a false “contrapositive” to the dispatch’s valid ranking lemma.** [ACCOUNT.md:141](/private/tmp/legit-review-2026-11-12/round/decomposition/ACCOUNT.md:141) concludes that differing rankings in indistinguishable situations prevent one mechanism from serving in both.

    False: rankings `(2,1,0)` and `(2,0,1)` differ but share the same maximizing move. A mechanism choosing that move serves in both situations. The required condition is disjoint maximizing sets, not merely different rankings. The dispatch’s original ranking-factorization lemma does not imply the added statement.

18. **The Lean quotations and cited declaration locations match; several interpretive identifications do not.** I checked the quoted declarations against the supplied Lean files, including `Frame`, `ReasonMediated`, `Realizes`, `TransparentAt`, `Blind`, `LicensedWhole`, `defect`, the cumulative rule and the corrigibility structures.

    The substantive errors are:

    - [LEAN_MAP.md:35](/private/tmp/legit-review-2026-11-12/round/decomposition/LEAN_MAP.md:35): force does not necessarily violate `ReasonMediated`. A forced move may equal the unforced move, or the compared views may differ. Reason mediation is an extensional property, not a causal test for force.
    - Lines 53–55: reproducing every part’s moves from its view is stronger than ACCOUNT’s fit condition, which concerns her resulting action.
    - Lines 81–84: equality of recorded adviser contributions to a reference does not establish equality of all adviser effects. The bridge requires complete representation of relevant influence.
    - Lines 122–126: `LicensedWhole` contains an arbitrary set-valued license. It becomes input-scored maximizing behavior only after choosing that particular license. Grounds can also encode facts about the world; the type alone does not prove the claimed exclusion of world-scored purposes.
    - Lines 130–137: `tower_factor` assumes an update equation. It does not prohibit adviser writes unless the grounds/events and amendment rule are separately restricted.

    The `defect` identification likewise needs a unique best move, or an appropriate treatment of ties, and the verdict-loss application needs the missing composition hypothesis. The map is not an exact correspondence as written.

19. **The cumulative Lean theorem is real, but the map supplies the wrong sequence for the demonstrated drift calculation.** [LEAN_MAP.md:153](/private/tmp/legit-review-2026-11-12/round/decomposition/LEAN_MAP.md:153) describes `s_t` as actual gap minus comparison gap. Under the adopted per-step comparison, D16’s habit difference is constantly `1/8`.

    Applying the quoted reporting rule to `0, 1/8, 1/8, 1/8, 1/8` reports **nothing** at threshold `1/4`. The Python instead accumulates those differences, obtaining `0, 1/8, 1/4, 3/8, 1/2`, and reports after the second and fourth exposures ([theorems.py:289](/private/tmp/legit-review-2026-11-12/round/decomposition/theorems.py:289)).

    The theorem applies to the latter sequence once explicitly defined. It does not prove that a sum of effects measured against changing, actual-history-conditioned baselines equals a cumulative counterfactual loss.

20. **The two-decompositions addendum reproduces its counts but does not test the requested generalization faithfully.** [TWO_DECOMPOSITIONS.md:100](/private/tmp/legit-review-2026-11-12/round/decomposition/TWO_DECOMPOSITIONS.md:100) admits that “never opposed” was not restated. The code checks coverage, mostly-serving and the global-maxima implication; it does not supply the requested full constraint package ([extensions.py:56](/private/tmp/legit-review-2026-11-12/round/decomposition/extensions.py:56)).

    It also changes immediate scoring to downstream scoring. The assertion that the bijective case recovers ACCOUNT is false in general: ACCOUNT permits a purpose to read other parts’ moves. Bijection does not make those dependencies disappear.

    “All admissible subgoal sets contain X” is partly forced by the chosen vocabulary: act’s **only effective pair is act–X**, and every mechanism must have a pair. It is not independent evidence that adding-up discovers X.

    “One crossing is enough” means that some tested world detects a lie. It is not true at every world: at hard worlds a crossing to V or X can reward the compensating lie. The computation uses an existential aggregation over worlds.

    The useful result is that stipulated extra downstream evaluative links can prevent one particular concealment. It does not show that crossings fix purposes, and the reduced disagreement cannot be attributed to the relation alone after changing scoring, goal freedom and the candidate class.

21. **The adviser-as-part addendum claims admissibility without constructing or checking an adviser part.** [extensions.py:143](/private/tmp/legit-review-2026-11-12/round/decomposition/extensions.py:143) evaluates three proposed scoring functions over adviser actions. It does not construct the enlarged candidate or check fit, independence, carriability and never-opposed. The output key “admissible at 9/10” merely filters serving rates. “Three purposes pass the constraints” is unsupported.

    Its opposition claim is also wrong under its own formula. At a clear world, `hard_truth` satisfies “say nothing false” and harms her, but `teach` satisfies the same purpose and achieves the whole’s optimum. Statement 8’s opposition is therefore **zero**, not positive.

    The correction arithmetic reproduces: `59/20` versus `29/10` in the adviser’s view, and `41/20` versus `29/10` in fact. That demonstrates a mistaken preference between two actions. It does not demonstrate a model of writable versus unwritable advisers or prove a correctability theorem. The claim that the mistaken adviser has “no gap” in its view is also inconsistent with teaching’s positive expected gap `1/20`.

    The objections about multiple principals and authority identify real missing structure. The circularity answer is only an analogy: no equations jointly defining purposes and normal conditions are supplied, and Stuck’s two equilibria are not two computed solutions of such a system.

22. **For corrigibility, the missing work goes substantially beyond observing the latent candidate.** The relevant Lean requirements are explicit in [DeconfusingCorrigibility.lean:115](/private/tmp/legit-review-2026-11-12/lean/DeconfusingCorrigibility.lean:115), [line 261](/private/tmp/legit-review-2026-11-12/lean/DeconfusingCorrigibility.lean:261) and [line 404](/private/tmp/legit-review-2026-11-12/lean/DeconfusingCorrigibility.lean:404).

    **Theorem 1:** Any predicate can be packaged with the required score ranges. That says nothing about whether this predicate captures legitimate judgment. The toy choice `N = 1 − 1_Legit` also makes the violation-free-but-illegitimate range empty, losing a distinction the framework deliberately preserves.

    **Theorem 2:** `Respects` is pointwise over all states, not merely probability zero under a selected prior. The current null example satisfies it definitionally, but no general availability or safety of asking, waiting or deferring is established. Nor does the account supply the authority allocation, counts of multiple violations, asking-cost bound `κ`, or justified candidate/world credences. These omissions remain even if purposes become determinate.

    **Theorem 3:** The model needs a sequential availability relation, an available respecting alternative at every decision, bounded estimates for that alternative, a maximizing choice rule, and the one-sided long-run calibration condition relating estimated scores to realized scores. The dispatch’s act/ask/refuse rule has not been shown to maximize the Lean score. Observing realized values would not itself establish calibration.

    Finally, Theorem 3 bounds a long-run average violation count; it does not prove no violations, continuous correctability, or recovery after corruption. With the test parameters `δ = 1`, `λ = 3`, its generic tolerance is `2/3`. The work supplies no argument that this is an acceptable corrigibility guarantee. Its “Best Interests” conclusion concerns estimates versus realized penalized scores, not independently established true welfare.

23. **The draft’s assessment must be narrowed in both directions.** [REPORT-section-draft.md:288](/private/tmp/legit-review-2026-11-12/REPORT-section-draft.md:288) overstates the refutation of C1 and C2; its standing-verdict claim, best-baseline repair and adviser-part admissibility claim are wrong for the reasons above. “Both addenda were carried out” also conceals the omitted pair constraints.

    Conversely, “the account has no function that is rarely performed” ([line 269](/private/tmp/legit-review-2026-11-12/REPORT-section-draft.md:269)) is too strong. Y1’s mechanism serves on `11/20` of situations; it is excluded by the chosen `9/10` threshold. A rarely activated function can satisfy a high serving rate through correct inactivity. This example establishes sensitivity to a success criterion and threshold, not a general impossibility.

    The 66/16/7 intuitive assessment is the executor’s judgment about its own renderings. Some alleged misses—reserved authority, or steering between goal-equal alternatives—concern standards the dispatch expressly separates or leaves unresolved. Those counts are not independent validation or disconfirmation.

    Finally, the claim that every listed limitation awaits purpose determinacy ([line 295](/private/tmp/legit-review-2026-11-12/REPORT-section-draft.md:295)) is false. Baseline choice, cardinal scale, authority, harmful gap-preserving threats, calibration and persistent correctability remain problems with a single fully specified candidate. The defensible result is a reproducible finite investigation exposing several failures of selected definitions. It is not yet a refutation of the developed account under its strongest faithful reading, and it is not yet a corrigibility foundation.
