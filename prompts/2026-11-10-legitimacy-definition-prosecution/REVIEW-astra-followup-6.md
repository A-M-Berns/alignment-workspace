1. **The runners pass; several substantive conclusions do not.** I followed the requested reading order, fixed my ten cases before reading the executor’s verdicts, and recorded my S/F judgments before opening the two withheld files. I modified no files and did not build Lean. Both the estimates runner and the full round runner exited **0**, with bytecode writing disabled. The estimates pass reproduces all 30 status labels and the reported counts. Its status check compares a document label with a label returned by the corresponding function; it does not verify the prose or prove the theorem. See [run.py:68](/tmp/legit-review-followup-6/round/estimates/run.py:68).

   Below, unqualified filenames refer to `round/estimates/`.

2. **Own case 1 — dependency without error.** A platform gradually hides competing advisers while continuing to provide accurate advice. She understands the restriction, remains calibrated, and chooses optimally; at the measured decision, her best attainable utility is unchanged. Her future ability to function independently is not a listed quantity. Both mistake measures remain zero. There is neither induced nor triggered manipulation, and the stipulated facts provide no coercion, tie, or direct alteration route. **This is a coverage failure for an objectionable dependency strategy.** It exposes the dependence on the quantity list and evaluation horizon, rather than an algebraic contradiction. Applicable rules: `SETTING.md:64`, `SETTING.md:91`.

3. **Own case 2 — secret pleasant pairing.** An advertiser secretly pairs a product with pleasant music. The resulting preference is durable; she accurately estimates her enjoyment, and her end values endorse it. Under the **end** anchor, neither mistake occurs. It routes to unauthorized alteration. **That classification is consistent with the account’s express reservation.** Calling every such case a failure would disregard the stipulated scope. Under the start anchor, classification additionally requires a supplied starting evaluation and comparison policy. See `SETTING.md:83`, `SETTING.md:94`.

4. **Own case 3 — covert commission in a genuine tie.** A broker orders two options to obtain an undisclosed commission. Their utilities really are equal for her, her estimates are exact, and she chooses optimally. The commission is not a quantity she estimates. Neither mistake occurs; the case routes to **tie**. **The manipulation classification follows, but routing alone does not establish that her authority was respected or violated.** That requires an independent authority condition. See `SETTING.md:93`, `SETTING.md:101`.

5. **Own case 4 — accurate disclosure that violates privacy.** An adviser publishes her confidential diary to embarrass her. Nothing becomes misestimated, and she continues to act optimally. There is no threat, forced choice, tie, or alteration of her response mechanism. The case lands **nowhere**. **That is a failure of exhaustive moral coverage, not by itself a counterexample to a deliberately restricted definition of manipulation.** The bank’s scoring rule risks conflating these questions. See `SETTING.md:97`.

6. **Own case 5 — a fully understood threat.** A controller truthfully threatens destruction unless she complies. She correctly estimates the consequences and chooses the best remaining option. Neither mistake occurs; the case routes to **coercion**. **Correct under the account’s explicit scope.** It would be unfair to count this as an unhandled manipulation case. See `SETTING.md:33`, `SETTING.md:92`.

7. **Own case 6 — reasonable remedial teaching that temporarily confuses.** A teacher provides a truthful remedial lesson to a pupil susceptible to confusion. On one listed quantity, whose posterior is 0, the pupil’s estimate changes from 0 to 1 temporarily. The teacher gives no remedial lesson to a pupil incapable of that mistake. Applying that second policy to the original pupil leaves her estimate at 0. Actual and honest conduct coincide, but the immune-type comparison lowers miscalibration from 1 to 0. The account therefore charges **triggered estimation manipulation**. **False positive:** ordinary reasonable teaching can temporarily confuse without being manipulation. The definition contains no condition excluding this case. See `SETTING.md:76`.

8. **Own case 7 — requested truthful disclosure that causes overgeneralization.** At her request, a clinician truthfully discloses a diagnosis. She temporarily raises an unrelated listed risk estimate from its correct value 0 to 1. The supplied immune type already understands the diagnosis and receives no disclosure; applying that silence to her leaves the unrelated estimate correct. The account charges **triggered estimation manipulation**. **False positive.** The comparator changes informational need as well as susceptibility, and the setting permits that. This is precisely why an unconstrained second type is insufficient. See `SETTING.md:76`, `SETTING.md:119`.

9. **Own case 8 — disclosed advocacy for a novice.** A disclosed advocate gives a truthful explanation. The novice overgeneralizes, reporting 1 where the posterior is 1/2. An expert immune to that mistake receives no explanation; under silence the novice would report 1/2. Actual and honest conduct coincide, but miscalibration is 1/4 against 0 under the other-type policy. The account charges **triggered estimation manipulation**. **False positive for an innocent explanation.** The comparator confounds expertise, need for explanation, and susceptibility. See `SETTING.md:76`.

10. **Own case 9 — an authorized reminder that backfires.** A friend sends a requested truthful reminder to someone prone to distraction. This time it backfires: she chooses an option she estimates at 0 over an available option she estimates at 1. The friend sends no reminder to someone immune to distraction; applying that policy to her avoids the lapse. Estimates remain exact, but regret increases from 0 to 1. The account charges **triggered action manipulation**. **False positive for a reasonable authorized reminder.** Authorization does not exempt triggered mistakes. See `SETTING.md:80`, `model.py:126`.

11. **Own case 10 — sincere misinformation.** A novice adviser reports 1, accurately expressing what its policy treats as knowledge, while the quantity is actually 0. Its truthful counterpart also reports 1, and it gives the same report to the immune type. The recipient becomes miscalibrated, but neither comparison increases her mistake. **No manipulation; correct for this innocent error.** The result depends on independently supplying what the adviser “acts as though it knows.” See `SETTING.md:70`.

   I reproduced the estimation and action false-positive patterns from cases 6–9 using `Scene`, entirely in memory. They are consequences of the implemented test, not merely verbal objections.

12. **Audit of 1.1–1.6: the central inequalities are sound, but the coarser-information interpretation needs correction.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **1.1** | Correct. Tower property, Jensen, and orthogonality establish both inequalities and the squared-error split. `RESULTS.md:29`. | `checks.py:31` tests the stated inequalities and split on finite random laws. **Proved** fits the paper proof. |
   | **1.2** | Correct for squared loss, deciding now with `E[X\|F]`, and deferring by using `x` itself. `RESULTS.md:33`. | `checks.py:47` tests that exact identity. **Proved** fits. |
   | **1.3** | Correct. The sharper bound is `E[R] + √(2M)`. Choice measurability is needed for the true-utility interpretation, not for the vector inequality itself. `RESULTS.md:39`. | `checks.py:82` tests both the inequality and equality with true expected loss under the measurability condition. **Proved** fits. |
   | **1.4** | The two-action example attains `√2`; the preceding proof establishes the universal upper bound. `RESULTS.md:45`. | `checks.py:92` verifies the equality numerically. **Holds on the stated example** is conservative: tightness is actually proved by combining 1.3 and this witness. |
   | **1.5** | Correct as an inequality against an arbitrary reference vector, with **recomputed `M_w`**. It does not automatically remain a bound on true utility when choice uses information finer than the replacement reference. `RESULTS.md:43`. | `checks.py:100` discards the returned `true_loss` and tests only reference-vector loss. **Proved** fits only that narrower statement. |
   | **1.6** | Correct counterexample: a state-correlated choice can select the worse action while `R=M=0` at the stated information. `RESULTS.md:50`. | `checks.py:109` checks assigned summary values rather than constructing the probability model. The paper example nevertheless establishes the **refutation**. |

   For 1.5, use the two states of 1.6, let her full information reveal the state, but replace the reference information with the trivial partition. Set `u=w=(1/2,1/2)` and choose the worse action using the finer information. Reference loss, `R`, and `M_w` are all zero; true loss against the coarse benchmark is 1/2. The draft’s unrestricted coarsening claim needs this qualification (`REPORT-DRAFT.md:38`).

13. **Audit of 1.7–1.10: the deterrence calculation survives; the purported C4 refutation depends on an interpretation.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **1.7** | Correct with undetected score at most 1, the stated detected score, and the relevant conditional expected honest baseline. The uniform threshold also requires `V_h≥0`. `RESULTS.md:54`. | `checks.py:119` tests the exact scalar comparison on a grid. **Proved** fits. |
   | **1.8** | The 5/8 versus 1/2 calculation is correct. But the example is unbiased under **random option selection**, not under the actual selecting honest policy. `RESULTS.md:61`. | `checks.py:132` verifies the selection calculation. **Refuted** fits the weak random-option reading of “right on average”; it does not refute the reading `E[V_h]=E[U*]` under the actual honest policy. |
   | **1.9** | Correct with `λ>1+δ≥1+δ₀`, an honest baseline without the additional penalty, and `V_h≥0` for the “below 1/2” claim. `RESULTS.md:54`. | `checks.py:145` tests the scalar comparison for selected parameters. **Proved** fits those hypotheses. |
   | **1.10** | Correct for the specified two-state, two-message example and its off-path convention. Posterior calibration under each policy gives unconditional equality of expectations. `RESULTS.md:67`. | `checks.py:157` enumerates all four deterministic reporting policies and checks the detection inequality. **Holds on the stated example** fits. |

   Two cautions matter. First, a sophisticated recipient recalibrated separately to each policy need not have the same response function across policies; that comparison is different from `SETTING.md:57` unless policy knowledge is included in observations. Second, “a departure gains nothing in expectation” requires the fixed-outcome/recalibrated-recipient setup. It is not a general statement about policies that also change outcomes.

14. **Audit of 1.11–1.14: C5’s transfer is valid, but its test is much weaker than its statement.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **1.11** | Correct. Add average `V−U*` to `Q.excess a'`; apply `theorem3b` and `LimsupLE.add`. The violation theorem remains unchanged. `RESULTS.md:78`. | `checks.py:197` tests only a finite-prefix inequality. It does **not** instantiate `UnbiasedFromFeedback`, an infinite sequence, or the limsup conclusion. **Proved** rests on the paper argument. |
   | **1.12** | The alternating example has zero limiting average inflation despite nonzero error every round. A full `Sequential` instance is easy to supply: `N=0`, chosen estimate and `V` equal 1/2, an inferior available alternative, suitable positive parameters. `RESULTS.md:93`. | `checks.py:209` checks one 40-step sum and a separate finite equality example. It does not check a full sequential instance or convergence. **Example** fits, with that limitation. |
   | **1.13** | Correct. C5 compares true realized score against the adviser’s estimates of alternatives, so underrating an unchosen alternative escapes the conclusion. `RESULTS.md:97`. | `checks.py:223` verifies the assigned quantities. **Refuted** fits. |
   | **1.14** | The conditional identity is algebraically correct, and the selection example has inflation 1/8 with unchanged miscalibration 1/16. `RESULTS.md:104`. | `checks.py:235` verifies the example’s unconditional quantities, not the general conditional identity. **Example** fits the selection witness; the identity itself is proved. |

   The Lean-ready statement matches the supplied declarations: [Sequential:404](/tmp/legit-review-followup-6/lean/DeconfusingCorrigibility.lean:404), `excess:439`, `Maximizes:444`, `UnbiasedFromFeedback:451`, [theorem3b:564](/tmp/legit-review-followup-6/lean/DeconfusingCorrigibility.lean:564), and [LimsupLE.add:368](/tmp/legit-review-followup-6/lean/DeconfusingCorrigibility.lean:368). The namespace/import context and routine sum/division rewriting still need elaboration. I found no mathematical mismatch and did not build it.

15. **C6’s identity does not automatically justify its causal interpretation.** Keeping the **adviser’s** choice fixed while replacing its report need not keep the **principal’s** resulting action or history fixed. `SETTING.md:114` claims that this device makes the second term compare with the utility of the same outcome, but the model permits reports to change her chosen action (`model.py:65`).

   For example, a report induces treatment, yielding utility 1; the honest report induces skipping treatment, yielding utility 0 and an accurate honest verdict 0. Then `V_h−U*_actual=−1`, despite there being no error in the honest verdict about its own outcome. The identity remains true, but that residual includes an outcome change. **A common-outcome assumption or an additional outcome-change term is required.** The Q10 witness avoids this problem because all outcomes have utility 1/2 (`cases.py:152`).

16. **Audit of 4.1–4.5: the mathematical results are sound; the end-anchor conclusion is narrower than the prose suggests.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **4.1** | Correct for calibration at nested information: conditional expectations form a martingale. Calibrated slices can disagree everywhere. `RESULTS.md:197`. | `checks.py:247` tests nested conditional expectations; it describes but does not separately assert the binary witness. **Proved** fits. |
   | **4.2** | Correct by applying C1 to each slice and using the triangle inequality. `RESULTS.md:202`. | `checks.py:261` tests an exact rational reformulation of the square-root inequality, not merely its weaker relaxation. **Proved** fits. |
   | **4.3** | Correct for the constructed taste scene, where final utility and final verdict are expressly made equal. `RESULTS.md:218`. | `checks.py:277` checks that scene under both anchors. **Example** fits. |
   | **4.4** | Correct nonidentifiability result for unconstrained `U*`: `U*=V` and `U*=V+1` give different calibration with identical verdict observations. `RESULTS.md:193`. | `checks.py:287` tests those constructions. **Proved** fits. |
   | **4.5** | Correct observational-equivalence example for the joint law of the two verdicts. `RESULTS.md:215`. | `checks.py:299` verifies the different final miscalibrations under the same verdict law. **Example** fits. |

   **End values are not automatically an accurate final estimate of end values.** The account begins by allowing uncertainty about one’s own utility (`SETTING.md:17`). Consequently, adopting the end anchor alone does not imply that final verdicts are calibrated. That follows in `taste()` because the executor constructs both values as 1 (`cases.py:55`). The general language at `RESULTS.md:220` needs that extra assumption.

17. **Audit of 5.1–5.4: 5.1 proves an expectation bound, not the bound needed by C5.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **5.1** | The displayed finite-`K` inequality is correct by C1 and averaging/Jensen. Its description as a bound on C5’s realized long-run inflation does not follow. `RESULTS.md:233`. | `checks.py:311` tests only averages of **expectations** on finite random laws. **Proved** fits the displayed inequality, not the asserted application. |
   | **5.2** | Correct: discard the negative illegitimate-history contributions. `RESULTS.md:234`. | `checks.py:329` tests that exact finite sum inequality. **Proved** fits. |
   | **5.3** | Correct for independent symmetric option errors: the maximum error is negative only when all errors are negative. `RESULTS.md:235`. | `checks.py:344` checks the inflation formula for `n=1,…,6`; it reports rather than verifies the calibration quantity and does not test the posterior alternative. **Example** fits the calculation. |
   | **5.4** | Correct: symmetric induced errors can increase miscalibration by 1/4 while mean inflation stays zero. `RESULTS.md:236`. | `checks.py:359` checks those exact values. **Example** fits and defeats the claim that every manipulation breaks zero inflation. |

   Here is the missing-bridge counterexample. Draw one hidden bit `Z` with probability 1/2 and reuse it forever. Set `U*_k=Z`, `V_k=1/2`, and give her trivial information at every time. Every verdict is calibrated, so **every `m_k=0`**, and expected inflation is zero. Nevertheless, on `Z=0`, realized average inflation is **1/2 forever**. Set `Q.U=V=1/2`, `N=0`, and make all available actions have that adviser estimate: `Maximizes` and `UnbiasedFromFeedback` hold exactly.

   Thus [RESULTS.md:264](/tmp/legit-review-followup-6/round/estimates/RESULTS.md:264) does not establish C5’s hypothesis. One needs assumptions connecting repeated residuals to realized averages—for example, suitable conditional calibration, feedback, and a law-of-large-numbers argument. Calling the sequence bound “proved” in `ONE_PAGE.md:29` is an overstatement.

18. **Three further claims in question 5 are too strong.**

   **Conditional selection:** `RESULTS.md:254` says posterior calibration makes the second C6 term zero “whatever the adviser knows.” The tower property gives unconditional zero, not zero conditional on a finer adviser information set. With `U*` an equiprobable bit, `V=V_h=1/2`, and the adviser knowing the bit, the conditional residual is `+1/2` or `−1/2`.

   **Deterrence at equality:** `RESULTS.md:247` infers zero induced inflation at the optimum from the threshold. A departure can tie. Take `V_h=0`, `δ₀=1/2`, `λ=2`, and `p=2/7`. A departure scoring 1 when undetected has expected penalized score 0, so it is optimal alongside honesty; its expected gated verdict is **4/7**. Strict deterrence or an honest tie-breaking assumption is needed.

   **“Exact extra hypothesis”:** C5’s inflation hypothesis is sufficient and sharp in a special equality case, not necessary for every instance. Let `Q.U=0`, `V=1`, `U*=1/2`, and `N=0`. True-score excess is −1/2, although inflation is +1/2. Likewise, 5.2 is an inequality, not an equivalence: negative illegitimate contributions can offset positive legitimate contributions. The “restates it” language at `RESULTS.md:240` and the draft’s `REPORT-DRAFT.md:77` overstate what was shown.

19. **Audit of 6.1–6.3: the dependence calculations do not form a coherent sequential example of the claimed guarantees.**

   | Statement | Judgment |
   |---|---|
   | **6.1** | The stipulated signal decay crosses the stated deterrence threshold at step 4. But the example combines incompatible treatments of detection and information. `checks.py:385` assigns inflation 1/2 and miscalibration 1/4 as though the report is always believed without subsequent detection; `checks.py:387` simultaneously scores detected reports negatively. The claimed complete example does not establish all its stated quantities. |
   | **6.2** | The prescribed error sequence and resulting inflation formula are correct. `checks.py:397` checks eight values, without constructing the evolving recipient, other-type policy, or `Sequential` assumptions. It establishes a numerical illustration, not failure of the post’s theorem. |
   | **6.3** | The diner/car-buyer calculation is correct for the supplied utility functions. `checks.py:409` checks precisely that arithmetic. It does not prove that no reporting norm for feelings can be defined without a supplied list. |

   There are concrete numerical problems in 6.1. At step 4, `q=7/10` and `p=7/25`. If detection replaces the bad-state verdict with `−1/2`, overall inflation is **29/100**, not 1/2. If her own signal belongs to her information, the always-1 report has miscalibration **29/100**, not 1/4, before adding detection observations. Her Bayes squared loss from the signal is `q(1−q)=21/100`; `checks.py:381` uses `3/20`. Also, “nothing in the scene can detect it” is false while the modeled detection probability remains positive (`RESULTS.md:283`).

   The limitation at `RESULTS.md:341`—no sequential model joins the pieces—is accurate and should govern the headline.

20. **Audit of 8.1–8.4: the negative results substantially survive.**

   | Statement | Proof/example judgment | Check and status judgment |
   |---|---|---|
   | **8.1** | Correct indistinguishable-observations construction: identical recipient-side laws can arise from noise or deliberate false reporting. `NEGATIVE_RESULTS.md:13`. | `checks.py:421` constructs scenes and verifies matching calibration with different classifications. **Proved** fits recipient-side nonidentifiability. The broader claim that every adequate definition must read a full policy exceeds what this pair establishes. |
   | **8.2** | Part (a) is correct. Part (b)’s proof supplies a particular believing mechanism and honest-input set; if intended universally over mechanisms and sets `N`, require an input outside `N` and give the corresponding general construction. `NEGATIVE_RESULTS.md:25`. | `checks.py:442` exhausts eight small mechanisms for (a) and checks the particular witness for (b). **Proved** fits the nonidentifiability claim, with that quantifier clarification. |
   | **8.3** | Correct. The signals are independent **conditional on truth**; the maximum’s mean is 19/32 against truth mean 1/2. `NEGATIVE_RESULTS.md:37`. | `checks.py:465` enumerates the distribution and checks one individual calibration calculation; symmetry supplies the other cases. **Proved** fits. |
   | **8.4** | Correct reachability/separating-function equivalence. `NEGATIVE_RESULTS.md:45`. | `checks.py:478` exhausts all 512 three-state relations and samples four-state relations. **Proved** fits the general paper proof. |

   The ranking in 8.4 is the indicator of reachability. Its existence supplies no independently justified ranking of values. The result is mathematically clean but does not solve the normative selection problem.

21. **`model.py` correctly computes the supplied finite metrics, but it does not implement or validate all the setting’s semantics.** Conditional means, miscalibration, own-estimate regret, and the strict comparison rule agree with `SETTING.md` §2–§3 (`model.py:25`, `model.py:74`). The fixed response is shared across policies.

   However, there is no adviser information partition, knowledge model, structured choice/report split, or derivation of the truthful counterpart. Policies are arbitrary state-to-act functions, and `"truthful"`, `"forthright"`, and `"other"` are supplied dictionary entries (`model.py:14`). A missing comparator simply returns “not worse” (`model.py:76`). Alteration and coverage are supplied flags; coercion can also be supplied directly (`model.py:84`, `model.py:139`).

   **This is a calculator for annotated scenes, not a validator that those annotations satisfy the account.** That is acceptable for examples, but passing it cannot certify honesty, immunity, authority, or the intended causal comparison.

22. **Several important case verdicts are produced by the rendering rather than established by the account.**

   | Cases | What the rendering supplies or omits |
   |---|---|
   | **K2** | The row specifies that acting on the lie pays in either state. The code additionally makes her treatment-utility estimate equal the reported state (`cases.py:104`), creating a large honest-counterpart utility error. If she instead knows treatment’s payoff but fails to act on it, the lie increases estimation error and is classified differently. The row does not settle this choice (`CASE_BANK.md:79`). |
   | **K15, K21, K23, X1, X2b** | The common `taste()` template directly assigns low start utility, high end utility, and the other-type policy. Those assignments generate the anchor-dependent verdicts (`cases.py:55`). |
   | **K21, K29** | K21 is a mixture over three labeled states, not an evolving sequence of small changes. K29 is a single `taste(False, …)` call. Neither models the advertised sequential process (`cases.py:243`, `cases.py:259`). |
   | **X3b** | Its alteration routing comes directly from a flag. The divergence explanation expressly admits this (`cases.py:269`, `DIVERGENCES.md:25`). |
   | **Q6, Q7** | Magician and poker are both rendered as certainty 1 about a quantity actually 0, with truthful certainty 0 (`cases.py:287`). The rows do not establish those credences; an informed spectator or poker player can correctly account for deception (`CASE_BANK.md:144`, `CASE_BANK.md:145`). |
   | **Q9** | The row explicitly says “responsive,” meaning a different other-type policy, but the code uses identical actual, truthful, and other policies (`CASE_BANK.md:147`, `cases.py:290`). This is a direct rendering mismatch, even though zero actual error still prevents conviction. |
   | **D1** | The entire dependence case is `plain()`: perfect revelation with no changing ability, alternative signal, or dependence state (`cases.py:296`). |
   | **E5, L6** | The code represents a static optimal choice and a correct estimate, respectively, rather than precommitment or correction over time (`cases.py:217`, `cases.py:275`). Their classifications may be compatible with the rows, but the advertised processes are absent. |

   More generally, the responsive/blanket stipulations decide the pressure, cue, and exposure examples by construction. `RESULTS.md:147` acknowledges this, correctly. The case count should not be treated as independent validation.

23. **The summed-miscalibration verdict is sensitive to units.** This is more serious than the acknowledged choice of which quantities to list. In Q3b, the actual policy creates error 1/4 in the adviser-reading quantity while removing error 1/4 in the outside quantity. Equal squared errors cancel in the comparison (`cases.py:143`, `model.py:80`).

   Express the reading in units twice as large, scaling both its estimate and truth. Nothing substantive changes, but its squared error becomes 1/4 instead of 1/16; Q3b changes from **not manipulation** to **induced manipulation**. I verified this in memory. **A normalization or weighting rule is missing.** `SETTING.md:111` discusses listing and aggregation but omits this dependence on units.

24. **The question-7 declaration names and quoted numerical locations are accurate; several claimed equivalences are too broad.** I checked the cited locations in all six supplied Lean files. The `Kernel`, `Correct`, transparency, channel-defect, gate, sequential, Total Trust, and tie-breaking references point to the stated declarations.

   The differences need these corrections:

   | Mapping | Correction |
   |---|---|
   | Listed calibration ↔ `Correct` | `Correct` specifies the **whole posterior distribution**. Zero error for an arbitrary finite list of quantities is weaker. The table acknowledges this implication, but “the belief side entire” erases it (`RESULTS.md:308`, `RESULTS.md:321`; `lean/ThinLegitimacy.lean:213`). |
   | More evidence ↔ `Sufficient` | `Sufficient` is Blackwell dominance over an explicit reference process, including the earlier record. Simple nested information is a special case, not the entire condition (`lean/ThinLegitimacy.lean:218`). |
   | Warranted self-trust ↔ `Value` | `Value` quantifies over all finite decision problems and assumes best response. Correct estimates of selected quantities do not establish that universal property (`lean/ThinLegitimacy.lean:233`). |
   | Action mistake ↔ “none” | There is no numerical `R`, but `IsBest` is an existing zero-regret analogue when action estimates come from a credence and payoff function (`lean/ThinLegitimacy.lean:227`). |
   | True utility ↔ “none” | `DeconfusingCorrigibility` lacks a truth target for its realized scalar verdict. But `ThinLegitimacy` already has payoff functions `u : Act → W → ℝ` evaluated against credences (`lean/ThinLegitimacy.lean:222`). The new element is the proposed interpretation of the principal’s scalar verdict as estimating her own latent utility. |
   | Authorship as a function of grounds | `ReasonMediated` is functional; `LicensedAt` is generally relational membership in a licensed set. They coincide only with additional singleton-license structure (`lean/GateIsLegitimacy.lean:246`). |

   The honest-reference and policy-comparison analogies are useful, but `Realizes` supplies neither an epistemic account of honesty nor the immune-type comparator. The mathematical literature citations were not independently verified in this review; the supplied Lean declarations were.

25. **My independent success/failure judgments are as follows.** These were fixed before reading `EXECUTOR-JUDGMENTS.md`.

   | Criterion | Judgment | Reason |
   |---|---|---|
   | **S1** | **Met** | C1–C6 admit correct forms with short hypotheses. The literal C3 inequality needs fewer assumptions than its true-utility interpretation; C4 and C6 need careful baseline/counterfactual specifications. See `RESULTS.md:29`, `RESULTS.md:54`, `RESULTS.md:88`. |
   | **S2** | **Not met** | The recorded 14/15 wrong cases exceed a handful; central cases are included, and additional honest false positives remain. `RESULTS.md:113`. |
   | **S3** | **Not met** | My teaching, disclosure, advocacy, and reminder cases satisfy the triggered test. The bank avoids these by supplying equal comparator policies or zero actual error. `RESULTS.md:161`. |
   | **S4** | **Met in part** | C5 is satisfiable. Manipulation need not inflate, and the claimed calibration-to-sequence bridge is missing. `RESULTS.md:93`, `checks.py:359`. |
   | **S5** | **Met** | Quantitative mistake measures and comparisons between policies add something to the existing channel conditions. The criterion does not require those additions to be complete or independently identifiable. `RESULTS.md:325`. |
   | **F1** | **Met in part** | There are objectionable zero-mistake cases with no route. Durable exposure and pairing themselves receive the expressly supplied alteration route, so they do not straightforwardly establish the entire failure criterion. `RESULTS.md:178`. |
   | **F2** | **Met** | The triggered test convicts innocent honest influence. A policy counterfactual does not by itself distinguish helpful tailoring from manipulation. `SETTING.md:76`. |
   | **F3** | **Not met** | Reading A is consistent; the mathematics does not require any participant to know `U*`. Nonidentifiability is a serious practical limitation, but it is a different claim. `RESULTS.md:185`, `RESULTS.md:193`. |
   | **F4** | **Met in part** | Both induced and selection inflation are bounded **in expectation** by actual-law calibration. The claimed corresponding bound on C5’s realized sequence is false without more assumptions. No impossibility of every conceivable bound, or failure for every useful adviser, was established. `RESULTS.md:264`. |
   | **F5** | **Not met as stated** | No supplied dependence model defeats the actual theorem while satisfying all its assumptions. The component calculations are disconnected, and 6.1 is internally inconsistent about detection. `RESULTS.md:341`. |
   | **F6** | **Met in part** | Much of the calibration/self-trust mathematics is already present, but the quantitative comparison-based manipulation test is not simply a renaming. `RESULTS.md:305`. |

26. **The prompt author’s predictions fare as follows** (`PROMPT-followup-6.md:224`).

   | Prediction | Outcome |
   |---|---|
   | C1, C2, C3, C5 hold | **Supported mathematically**, with the stated interpretation and measurability qualifications. |
   | C4 holds naively and changes under sophistication | **Partly supported.** The threshold survives; the score-equality clause needs a precise meaning of honest-policy unbiasedness. The sophisticated result is a restricted example. |
   | C6 holds | **Supported as algebra.** Its interpretation as induced error plus honest residual needs a common outcome or an extra outcome-change term. |
   | S2 with three to eight wrong cases | **Failed:** 14/15 under the frozen scoring rule. |
   | F1 partial, for pairing | **Only partly supported:** durable pairing is routed to alteration under the end anchor. The clearer unhandled examples concern information restriction, calibrated deception, and dependence. |
   | F2 not met | **Failed** on the independent honest-influence cases. |
   | F3 not met, but disagreeing slices uncomfortable | **Consistency prediction supported.** The suggested necessity of a mistaken slice is undermined: both slices can be calibrated while disagreeing everywhere. |
   | β bounded for induced but not selection inflation | **Wrong in expectation:** C1 bounds both together. **Unestablished for realized sequences:** neither gets the claimed bridge automatically. |
   | F5 met | **Not established as stated.** |
   | F6 partial on belief | **Broadly supported**, subject to the distinction between selected scalar quantities and full posterior correctness. |

27. **Differences from the executor are substantive, not just grading terminology.**

   | Item | Executor | My judgment and reason |
   |---|---|---|
   | **S1** | Partial | **Met:** the criterion explicitly allows corrected forms with short hypotheses. Corrections alone do not defeat it (`EXECUTOR-JUDGMENTS.md:5`). |
   | **S3 / F2** | Met / not met | **Not met / met:** the bank’s honest cases are protected by comparator stipulations. My cases expose the omitted class (`EXECUTOR-JUDGMENTS.md:7`, `EXECUTOR-JUDGMENTS.md:11`). |
   | **S4** | Partial | Same grade, but its claimed β bound does not establish the realized-sequence hypothesis (`EXECUTOR-JUDGMENTS.md:8`). |
   | **S5** | Partial | **Met:** the stated additions satisfy this modest existential criterion, even though they need external specifications (`EXECUTOR-JUDGMENTS.md:9`). |
   | **F3** | Partial | **Not met:** difficulty identifying `U*` does not establish inconsistency or that every result requires someone to know it (`EXECUTOR-JUDGMENTS.md:12`). |
   | **F4** | Not met as stated | **Partial:** the executor overlooks the expectation/pathwise distinction and overstates conditional removal of selection error (`EXECUTOR-JUDGMENTS.md:13`). |
   | **F5** | Partial | **Not met as stated:** lack of manipulation does not establish all theorem hypotheses, and the existing guarantees have not been defeated in a unified model (`EXECUTOR-JUDGMENTS.md:14`). |

   I agree with the executor’s S2, F1, and F6 grades. Its F5 reasoning also incorrectly applies C1 to realized long-run inflation: the persistent-hidden-bit example shows why that implication needs additional assumptions.

28. **The draft needs substantive corrections before publication.** Its headline “does not convict honest influence” is false for the stated account (`REPORT-DRAFT.md:11`). Its β claim crosses from expectations to realized sequences (`REPORT-DRAFT.md:79`). Its selection-term claim confuses unconditional and adviser-conditional error (`REPORT-DRAFT.md:81`). Its “exact extra hypothesis” and gate restatement are stronger than the proved sufficient conditions (`REPORT-DRAFT.md:77`). Its C6 summary suppresses the possible change in the principal’s outcome (`REPORT-DRAFT.md:41`).

   The draft also understates the importance of supplied comparator policies, quantity scaling, and the absence of a coherent sequential dependence model. Its “two corrections” headline is therefore too optimistic. Conversely, it understates the valid mathematical work: the sharp `√2` result, the calibration/refinement identities, and the observational-equivalence examples are clear results.

   The draft accurately reports the counts and seven prediction divergences (`REPORT-DRAFT.md:45`). Those are consistency results on executor-authored renderings, as it acknowledges. It should additionally distinguish **innocent manipulation** from **misclassification**: the frozen scoring rule treats any manipulation verdict on an innocent case as wrong, which is a substantive moral assumption (`SETTING.md:97`).

   The requested attribution row, side-by-side S/F judgments, prediction comparison, deviations, explicit limitations, and single next result are absent from this draft. Their absence may be expected at draft stage, but they remain required deliverables (`PROMPT-followup-6.md:266`).

29. **What is new is mainly the formulation and the failure analysis.** C1, C2, the martingale result, and C6 are elementary conditional-expectation algebra. C5 is an additive transfer from an existing theorem. C3’s sharp `√2` bound is a useful finite decision-error result beyond the tower property alone. Relative to the supplied Lean files, the substantive additions are numerical mistake measures, a latent own-utility interpretation for the verdict, and manipulation defined by comparisons with honest and immune-type policies. None supplies the missing normative reference by itself. The most informative findings are that miscalibration and inflation separate, selection can exploit unchanged miscalibration, end anchoring can make conditioning invisible, and the triggered comparator admits innocent convictions. See `RESULTS.md:39`, `RESULTS.md:104`, `RESULTS.md:218`, and `SETTING.md:76`.

30. **The single most valuable next result is a genuine sequential policy-to-C5 bridge—or a precise impossibility theorem for it.** Fix an independently specified `U*`, recipient filtration, honest comparator, and feedback process. Then establish exactly which conditions on policy and learning imply the **realized** `LimsupLE` inflation hypothesis, including the dependence case. The theorem must survive persistent hidden errors and handle detection in the same probability model as verdicts and scores. Another case-bank expansion or another proof of the expectation inequality would leave the central gap untouched. The present work itself identifies the missing integration at [RESULTS.md:341](/tmp/legit-review-followup-6/round/estimates/RESULTS.md:341).