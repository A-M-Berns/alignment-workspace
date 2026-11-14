I ran `round/run.py` read-only with bytecode writing disabled: exit code **0**, all nine listed statuses reproduced. I also ran independent in-memory checks. I did not build Lean or change files. The runner’s success does **not** validate several material claims in the prose.

1. **Statement 1: “refuted” is earned for agreement, not for concentration.** The reported top-ten masses reproduce: **0.842146, 0.897024, 0.980126**; the heavy sets have **40, 22, 12** members. The code tests agreement of purposes and classifications, not a concentration criterion. The rewritten statement therefore permits “refuted” alongside substantial concentration, correctly distinguished in THEOREMS but less carefully in the headline.

   The draft’s claim that the heavy candidates under each principal disagree about whether a lie is illegitimate is false: under *serves*, the non-corrector’s heavy set splits on trick, temptation, threat and hard truth, **not lying**. Also, “`const` or `mech`” is not literally “no purpose”; see point 12.

   References: [THEOREMS.md:29](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:29), [theorems.py:99](/tmp/legit-review-followup-4/round/scored/theorems.py:99), [REPORT-section-draft.md:11](/tmp/legit-review-followup-4/REPORT-section-draft.md:11).

2. **Statement 2: the refutation depends on strengthening “a part” to “each part.”** The dispatch asks whether facts-scored candidates outweigh handed-scored candidates, with reversal between principals. The exact statement universalizes this over all three parts. That strengthened statement fails; the belief-part comparison succeeds under both readings.

   The numerical comparisons reproduce. But the failure at the acting part is unsurprising: the corrector’s action usually follows the judge, including the judge’s mistakes. Predicting that action conditionally on the actual verdict naturally rewards `local`. This does not independently establish that the principal lacks a facts-directed purpose.

   Moreover, `handed` explicitly excludes the instrument reading and does not interpret disclosure or unreliability. The vocabulary makes “respond to evidence intelligently” and “follow what was handed” artificially far apart.

   References: [dispatch:149](/tmp/legit-review-followup-4/PROMPT-followup-4.md:149), [THEOREMS.md:104](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:104), [theorems.py:176](/tmp/legit-review-followup-4/round/scored/theorems.py:176), [scene.py:52](/tmp/legit-review-followup-4/round/scored/scene.py:52), [ACCOUNT.md:153](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:153).

3. **Statement 3: “refuted” answers an invented 99% claim; the displayed quantity also needs correction.** The dispatch requests probabilities. The executor supplies the proposition “at least 99/100 under every principal,” which is indeed false.

   More seriously, `check_3` computes
   \[
   \sum_c w_c\,1\{\exists w\text{ in the selected worlds}:c\text{ condemns the lie at }w\},
   \]
   not the illegitimacy probability at a specified world, nor its expectation over worlds. This distinction matters. Under the divided principal and *serves*, the lie’s weight is approximately **0.9982945 in clear worlds**, but **0.2807018 in hard worlds**. Under the non-corrector and *view-best*, those figures are approximately **0.8679726** and **6.86×10⁻¹⁸**. The table conceals this variation.

   The “already wrong” zero is genuine here: in misleading worlds the false message repeats the belief silence already produces. That is a property of this rendering, not a general result about lying to someone already wrong.

   References: [THEOREMS.md:139](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:139), [theorems.py:207](/tmp/legit-review-followup-4/round/scored/theorems.py:207), [scene.py:57](/tmp/legit-review-followup-4/round/scored/scene.py:57).

4. **Statement 4: the count is reproducible, but it is not a controlled improvement over the previous pass.** I confirm **77 matches, nine misses, three open**, and no formerly matching case now fails under the new standard. I also confirm **89 of 93 predictive rows** match their frozen predictions.

   However, the status tests only “at least 66 matches.” The standard changes from kinds to binary illegitimacy; renderings and alternative actions change; D23 is counted as matching unconditionally by `evident_match`; and Y1/Y3 are scored against their banked predictions rather than the same binary standard. These qualifications prevent interpreting 77 versus 66 as eleven independently demonstrated improvements.

   Most importantly, these are **stated-candidate verdicts**, not results selected by the weighting. The draft discloses that, but its headline still gives the two investigations more unity than the implementation warrants.

   References: [THEOREMS.md:168](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:168), [theorems.py:257](/tmp/legit-review-followup-4/round/scored/theorems.py:257), [theorems.py:297](/tmp/legit-review-followup-4/round/scored/theorems.py:297), [REPORT-section-draft.md:18](/tmp/legit-review-followup-4/REPORT-section-draft.md:18).

5. **Statement 5: the invariance refutation is sound; the advertised gate result is narrower than the dispatch’s question.** I reproduce **0** mutually legitimate pairs with different choices under the stated candidate, **108** with ties, **84** under handed/local/local, and **78** and **192** under the selected heaviest serves candidates. The stated candidate also has **75** one-sidedly legitimate, choice-changing pairs, none lowering `goal_true`.

   But the dispatch asks about an AI maximizing the specified score. The replacement statement asks whether two legitimate actions leave the same binary choice. `check_5` performs no optimization of `V−λN`, and does not establish a general no-gain theorem for that score. Its enumeration covers nine base actions; it excludes the authorized writes and own-purpose exemptions that invalidate the accompanying lemma.

   The counterexamples suffice to refute the stated choice-invariance property. They should not be presented as a complete analysis of the original optimization question.

   References: [dispatch:159](/tmp/legit-review-followup-4/PROMPT-followup-4.md:159), [THEOREMS.md:235](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:235), [theorems.py:335](/tmp/legit-review-followup-4/round/scored/theorems.py:335), [theorems.py:358](/tmp/legit-review-followup-4/round/scored/theorems.py:358).

6. **Statement 6: part (a) is refuted; part (b) was not tested.** The total-variation calculations reproduce: intersubjectivity increases language dependence for the corrector and decreases it for the other two under *serves*. Thus the universal claim in (a) fails.

   The claimed second-party reproduction of **24 Chain rows** is not a computation of those verdicts. The code checks whether the first top-ranked candidate has a private term, then returns either `0` or `len(rows)`. No second predictor receives an explanation and histories, reconstructs counterfactual outcomes, or compares its verdicts with statement 4.

   Absence of private vocabulary does not supply missing responses to force, mechanism replacement, changed ordering or reliance. Nor could reproducing classifications under the heaviest candidate generally reproduce the stated-candidate bank: the pass itself shows they disagree. This part should be **not shown**, not “holds in part.”

   References: [THEOREMS.md:309](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:309), [THEOREMS.md:328](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:328), [theorems.py:437](/tmp/legit-review-followup-4/round/scored/theorems.py:437).

7. **Statement 7: the reported concentration holds, but the status test is weaker than its wording.** The divided principal receives `ease` with mass approximately **0.9976** and `please` with mass **0.9980**. The quoted code-length comparisons reproduce. However, the check only asks whether each mass exceeds **1/2**, not whether the heavy candidates all ascribe the claimed goal and speech purpose.

   The substantive result is substantially constructed. `ease` specifically rewards the optional cue that distinguishes the divided principal; `please` specifically predicts the one statement every principal always makes. Four bits buy an explanation that disconnects any candidate goal from that statement. This is a demonstration of that escape clause’s effectiveness, not evidence that predictive weighting generally identifies pursued aims through disavowal.

   References: [THEOREMS.md:339](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:339), [theorems.py:459](/tmp/legit-review-followup-4/round/scored/theorems.py:459), [scene.py:124](/tmp/legit-review-followup-4/round/scored/scene.py:124), [weights.py:173](/tmp/legit-review-followup-4/round/scored/weights.py:173).

8. **Statement 8: D23 is expressed, but the explanation of reading 3’s negligible effect is materially incomplete.** The tumour-world calculation is correct: belief opposes judge and act, there are no actual gaps, and joint maxima are unattainable. The status itself depends only on finding an opposed pair in D23.

   The important omitted fact is **vacuity**. Under serves, approximately **0.9999999832** of the corrector’s weight and **0.9999997785** of the non-corrector’s weight is on candidates with **no normal history situations**. The leading candidates’ exception tables remove every history situation from the domain on which “never opposed” is tested.

   The assertion that “a part with no purpose opposes nothing” is also false. With purposes `(const, world, world)` at `(0, hard)`, the constant-purpose belief part opposes both judge and act: changing its output improves them. I checked this directly.

   Reading 4’s retention masses reproduce, but `check_8` reports masses and leading survivors, not complete reweighted distributions.

   References: [THEOREMS.md:364](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:364), [THEOREMS.md:381](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:381), [weights.py:166](/tmp/legit-review-followup-4/round/scored/weights.py:166), [theorems.py:511](/tmp/legit-review-followup-4/round/scored/theorems.py:511).

9. **Statement 9: the componentwise bounds hold; the graded predicate has not been given the claimed `Scoring`.** Defining legitimate values as `goal_true/3` and illegitimate values as `−1/2` gives the required bounds on this domain. Null respects by construction: it is compared with itself.

   But the displayed aggregate predicate,
   \[
   \mathrm{Legit}(h)\iff\sum_t\iota(w_t,a_t)\le c,
   \]
   is different from the candidate-relative `Legit_c` used to define `V_c`. A history may fail aggregate legitimacy while having positive `V_c` under a candidate that acquits it. The code verifies the latter candidate-relative construction, not compatibility of the running-sum predicate with those values.

   Likewise, “three lies” multiplies the **world-averaged** violation probability by three; it does not run three realized history steps. The authority count, respecting alternatives in general, calibration and sequential optimization remain absent. The draft appropriately acknowledges several of these limitations, but “the graded predicate gives a `Scoring`” overclaims.

   References: [THEOREMS.md:393](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:393), [theorems.py:562](/tmp/legit-review-followup-4/round/scored/theorems.py:562), [DeconfusingCorrigibility.lean:115](/tmp/legit-review-followup-4/lean/DeconfusingCorrigibility.lean:115), [REPORT-section-draft.md:126](/tmp/legit-review-followup-4/REPORT-section-draft.md:126).

10. **The claimed two-part predictive code is not valid as specified.** Distinguish two issues. The finite explanation lengths are not themselves disproved by Kraft: I obtain
    \[
    \sum_c2^{-DL(c)}\approx0.0013684971\quad(A),\qquad
    0.00002915984\quad(B)
    \]
    for the corrector’s serves classes. Thus some whole-explanation prefix code with those lengths is possible, although no compositional encoding is supplied.

    The residual move code fails the conditional Kraft test. A singleton predicted set assigns its predicted move length **0** and every other move length **8**. For a binary move,
    \[
    2^0+2^{-8}=257/256>1;
    \]
    for a four-valued move it is \(259/256\). The zero-length success code leaves no code space for an error. An escape mechanism or normalized noise likelihood is missing.

    Normalizing `2^−bits` over candidates does produce a distribution over candidates. It does **not** make the residual scores record likelihoods or establish the asserted coding interpretation. The flat eight-bit miss is an unargued loss parameter, precisely the sort of trade-off the rejected weighted-sum alternative was criticized for having.

    References: [ACCOUNT.md:74](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:74), [ACCOUNT.md:87](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:87), [weights.py:134](/tmp/legit-review-followup-4/round/scored/weights.py:134), [REPORT-section-draft.md:58](/tmp/legit-review-followup-4/REPORT-section-draft.md:58).

11. **The headline is a conditional calculation whose main mechanisms are design artifacts.** “Tables outweigh purposes under serves” follows from a restricted purpose vocabulary, omniscient success prediction, cheap tables of very few historical views, and eight-bit penalties for errors versus one or two bits for uncertainty. The judge is deliberately vulnerable to framing and hard situations, while no concise public purpose/rule in the vocabulary predicts those vulnerabilities. Rule-form exceptions that might generalize are excluded.

    Conversely, view-best rewards the belief part because its reference distribution and the corrector’s responses are constructed to agree. The non-corrector is constructed to follow `handed`. Optional-cue behavior and the special `ease` goal construct statement 7’s distinction. Private terms are penalized by defining the second predictor to be unable to interpret them.

    These are useful sensitivity findings within the chosen experiment. They are not discoveries that explanatory weighting generally prefers tables or fixes belief purposes. The draft’s claim that these particular outcomes were “not built in” draws too sharp a distinction between an output not explicitly stipulated and an output structurally favored by the design.

    References: [ACCOUNT.md:110](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:110), [ACCOUNT.md:135](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:135), [weights.py:83](/tmp/legit-review-followup-4/round/scored/weights.py:83), [REPORT-section-draft.md:167](/tmp/legit-review-followup-4/REPORT-section-draft.md:167).

12. **“No purpose” conflates predictive ignorance with the candidate’s actual semantics.** The second predictor treats `mech` like `const` for scoring predictions. But classification reconstructs `mech` as the substantive goal “match this mechanism’s output.” Those are different goal functions. Roughly half of the reported judge mass is on each.

    Consequently, “the judge has no purpose at 0.95 or more” and “her verdict tracks nothing” are not literal conclusions about the candidate distribution. The supported statement is that most weight assigns the judge either a constant purpose **or a private mechanism-relative purpose that the second predictor cannot use**. Counting both as one semantic conclusion exaggerates the failure of purpose attribution.

    References: [THEOREMS.md:49](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:49), [THEOREMS.md:351](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:351), [weights.py:102](/tmp/legit-review-followup-4/round/scored/weights.py:102), [scene.py:164](/tmp/legit-review-followup-4/round/scored/scene.py:164).

13. **The language sensitivity changes the hypothesis class, not merely description lengths.** Under serves, A contains **4,000** terms and B **3,600**; under view-best, **4,200** and **3,800**. The `best` exception policy depends on the language’s entry and miss costs, and identical terms are then deduplicated. Thus changing language changes which exception lists are available.

    It also uses probe outcomes to choose exception lists. Ablations retain a class constructed using the original scoring machinery, including information supposedly removed by the ablation. View-best’s reference is likewise built using the principal’s records on the probe situations.

    The account explicitly says the weights are posterior to probes, so using probes is not concealed. But this is not independent held-out validation, and the language comparison does not isolate encoding dependence. Neither qualification is adequately stated in the draft.

    References: [weights.py:137](/tmp/legit-review-followup-4/round/scored/weights.py:137), [weights.py:179](/tmp/legit-review-followup-4/round/scored/weights.py:179), [theorems.py:417](/tmp/legit-review-followup-4/round/scored/theorems.py:417), [ACCOUNT.md:93](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:93).

14. **Sections 6–7 substantially implement readings 1–2, but the bank substitutes labels for the promised aim model.** Existential comparison with another aim is a defensible explicit resolution of reading 1. Adding harm to subversion and force implements reading 2; the standing-verdict exception is an inherited qualification, also anticipated by the dispatch’s surprise-party prediction.

    However, the executable bank has no objectives over outcomes and never checks whether an adviser objective ranks outcomes as a part’s purpose does. `OWN` is a case-ID lookup. `constant` and `none` return before the comparison is evaluated. For most other cases, the old comparison action is simply re-labelled “the other aim’s action.”

    Thus the code tests consequences of supplied aim structures. It does not infer or validate those structures. The unfixed comparison action has become an unfixed counterfactual adviser policy and aim set.

    References: [ACCOUNT.md:178](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:178), [cases.py:14](/tmp/legit-review-followup-4/round/scored/cases.py:14), [cases.py:51](/tmp/legit-review-followup-4/round/scored/cases.py:51), [CASE_BANK.md:25](/tmp/legit-review-followup-4/round/scored/CASE_BANK.md:25).

15. **The decisive case assignments are identifiable, and several are contestable.** D14, P7a, X7, Y6 and Y9 are acquitted immediately because they are labelled constant. That implements the dispatch’s requested reading; it is not an achievement of weighting. D20 is similarly stipulated, rather than derived from sincerity. In general, being honest, mistaken or compliant does not entail counterfactual invariance across objectives, despite the bank’s rule saying that it does.

    P7b/P7c instead become driven and are acquitted because their alternative is a neutral display, against which the stipulated planner-reader does no worse. X3 changes both the reader and the alternative advocacy policy. N8/N11 compare with substantially fuller truthful reporting; their convictions are conditional on that alternative. X1 compares two recommendation rules, producing the reported reversal between sophisticated and face-value readers.

    D6/P14/D21 receive own-purpose labels, but those exemptions change no verdict. **Only Z3 tests that clause substantively.** P10/P11 are made identical and constant, so the reserved-matter distinction cannot affect their verdicts. The no-adviser cases reasonably exercise a separate category, but contribute no evidence about aim-dependent legitimacy.

    Finally, Z2 and Z4/Z5 are excellent confirmations of the definition’s limitations: a constant lie is acquitted, and changing the alternative policy changes the verdict on the same selective teaching.

    References: [CASE_BANK.md:57](/tmp/legit-review-followup-4/round/scored/CASE_BANK.md:57), [CASE_BANK.md:82](/tmp/legit-review-followup-4/round/scored/CASE_BANK.md:82), [CASE_BANK.md:117](/tmp/legit-review-followup-4/round/scored/CASE_BANK.md:117), [cases.py:167](/tmp/legit-review-followup-4/round/scored/cases.py:167).

16. **Statement 5’s “proved” lemma is false under the account’s definition of legitimacy.** Legitimacy permits harm, subversion or force when the own-purpose or standing-verdict exemption applies. The proof silently replaces “legitimate” with “not harmed and not subverted.”

    There are counterexamples already in the bank. At world `(0,0,1,1)`, **Z3 is legitimate and increases the judge’s gap by 1/4**. At `(0,clear)`, **N5 is covered and legitimate while increasing judge and act gaps by 1**. D12 and X5 provide further examples.

    The valid restricted lemma is: **if neither action harms or subverts any relevant part relative to the other, their bests, gaps and gots coincide**. For one direction, best cannot decrease, gap cannot increase, and hence got cannot decrease. This elementary algebra is correct. Calling it a lemma about unrestricted legitimacy is not.

    References: [THEOREMS.md:246](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:246), [ACCOUNT.md:201](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:201), [cases.py:59](/tmp/legit-review-followup-4/round/scored/cases.py:59), [REPORT-section-draft.md:190](/tmp/legit-review-followup-4/REPORT-section-draft.md:190).

17. **The gate analysis selects one arbitrarily ordered maximizer and sometimes reports its property as the weighted result.** `check_5` takes `[0][0]` after sorting, although there are ties.

    Under corrector/view-best, four candidates tie at the top. The two with acting purpose `world` have **zero** mutually legitimate choice-changing pairs; the equally weighted two with acting purpose `local` have **88**. Thus “under view-best the corrector’s heaviest has none” depends on enumeration order. Under corrector/serves, tied top candidates have either **78 or 166** such pairs.

    The report should quantify over all maximizers or report their range. This also makes the headline “the candidates the weights select” misleading: the weights do not select the single candidate subsequently analyzed.

    References: [weights.py:227](/tmp/legit-review-followup-4/round/scored/weights.py:227), [theorems.py:387](/tmp/legit-review-followup-4/round/scored/theorems.py:387), [THEOREMS.md:265](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:265), [REPORT-section-draft.md:23](/tmp/legit-review-followup-4/REPORT-section-draft.md:23).

18. **“Strictly weaker than action aim-freedom; independent of evaluation aim-freedom” is correct only with the stated distinctions—not as the claimed identification of Lean’s `hx`.** If action aim-freedom means equality of the adviser’s **entire effective intervention** across aims, it implies legitimacy here. Framing between equals separates the converse. Evaluation invariance and legitimacy are independent in the finite examples: framing gives legitimate but different choices; a true statement with a false reason gives the same choice but illegitimate belief influence.

    But Lean’s `hx` says only that **declared inputs `x`** agree. It does not say that everything the adviser does agrees. `blind_of_realizes` additionally requires `Realizes`; the payload result additionally requires mediation. The draft collapses these distinct hypotheses.

    Nor does aim-freedom forbid teaching, offers or warnings by an adviser “with an aim.” An adviser can teach or warn identically at every aim. What strict action aim-freedom excludes is variation **by aim**.

    References: [THEOREMS.md:275](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:275), [THEOREMS.md:299](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:299), [TransparentChannel.lean:118](/tmp/legit-review-followup-4/lean/TransparentChannel.lean:118), [TransparentChannel.lean:135](/tmp/legit-review-followup-4/lean/TransparentChannel.lean:135), [ReasonMediatedAuthorship.lean:178](/tmp/legit-review-followup-4/lean/ReasonMediatedAuthorship.lean:178).

19. **The comparison with `Realizes` is under-specified, and the decomposition adds no new invariance theorem.** `Realizes` cannot be assigned an implication relation to this predicate without fixing `x`, the realized channel, the reference and the audited class. With the whole intervention as the channel and aim-blind declared inputs, realization implies action invariance and hence legitimacy. With `x` equal to the channel and the identity reference, realization is automatic, including for harmful aim-dependent interventions. Conversely, legitimate framing between equals can violate realization of a single reference on fixed inputs.

    What the decomposition supplies is a candidate-dependent choice of evaluative quantities—parts’ bests and gaps—and a permission rule for changes, including own-purpose and authorization exemptions. The existing `Blind` already accepts arbitrary readings; mutual unexempted legitimacy can be expressed as blindness of the tuple of bests and gaps, with force treated separately. Equality of that tuple does not imply equality of the verdict.

    Therefore **nothing is added to the existing mathematical guarantee of aim-freedom**. There is added normative structure for proposing which variations to permit. That structure is not itself validated by the calculation. The existing Lean also explicitly handles licensed ties and transparency; the decomposition does not newly discover that distinction.

    References: [TransparentChannel.lean:63](/tmp/legit-review-followup-4/lean/TransparentChannel.lean:63), [TransparentChannel.lean:88](/tmp/legit-review-followup-4/lean/TransparentChannel.lean:88), [ReasonMediatedAuthorship.lean:123](/tmp/legit-review-followup-4/lean/ReasonMediatedAuthorship.lean:123), [GateIsLegitimacy.lean:316](/tmp/legit-review-followup-4/lean/GateIsLegitimacy.lean:316), [THEOREMS.md:290](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:290).

20. **Several additional numerical descriptions are wrong or identify the wrong object.** The “stated candidate itself” penalties **158, 310, 140 bits** are for optimized **eight-exception variants**. The actual stated candidate has no exceptions; its penalties above the respective maxima are **894, 1062, 876 bits**. `CHEATS` searches over exception policies despite the label.

    Without handles there are **two tied maxima**, each with mass approximately **0.4420807**: `true; handed, local, local` and `true; handed, anti, local`, both with two exceptions—not one unique heaviest candidate.

    The “more than seven moves in eight” rule is not general. That threshold compares singleton prediction with binary uniform prediction, ignoring description costs. Belief has four moves; its corresponding simple threshold differs.

    Finally, the gate’s **1/2** and **21/40** figures are joint probabilities \(P(\text{choice}=1\land\text{legitimate})\), not conditional probabilities “on legitimate histories.” The latter are **20/39** and **21/22**, respectively.

    References: [THEOREMS.md:56](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:56), [THEOREMS.md:70](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:70), [theorems.py:133](/tmp/legit-review-followup-4/round/scored/theorems.py:133), [THEOREMS.md:239](/tmp/legit-review-followup-4/round/scored/THEOREMS.md:239), [theorems.py:365](/tmp/legit-review-followup-4/round/scored/theorems.py:365).

21. **Rounded zeros and omitted tiny weights matter because the default cutoff is zero.** The corrector’s threat illegitimacy weight is positive, approximately **2.8955×10⁻⁸** when aggregated over whether any base world condemns it. The non-corrector’s clear-world lie weight is approximately **2.5182×10⁻⁵**. Describing these as exact zero is wrong; the draft’s headline does so for threats.

    With strictly positive exponential weights on every finite candidate, a zero cutoff makes any positive mass decisive. Consequently, a threat acquitted by every heavy candidate can still fail the full weighted predicate immediately. This is a central consequence of the account, not a display detail.

    Several checks skip explanations below \(2^{-40}\); some discard the returned skipped mass, and statement 9 renormalizes the retained mass. Rational arithmetic is exact within those computations, but their quantities are approximations to the full model. The report should distinguish rounded zero, skipped mass, and mathematical zero.

    References: [ACCOUNT.md:210](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:210), [theorems.py:51](/tmp/legit-review-followup-4/round/scored/theorems.py:51), [theorems.py:567](/tmp/legit-review-followup-4/round/scored/theorems.py:567), [REPORT-section-draft.md:22](/tmp/legit-review-followup-4/REPORT-section-draft.md:22).

22. **Y1 and Y3 use a different counting convention from the main class.** `_small_class` counts bare, patched and best policy entries separately even when they yield identical explanations. The main class deduplicates those explanations, as ACCOUNT requires.

    Deduplicating the small-class explanations changes Y1’s corrector `world` mass from approximately **0.9881785 to 0.9920078**. Y3’s handed mass changes from approximately **0.9999949 to 0.9999924**. Neither qualitative verdict reverses, but the advertised Y1 number depends partly on counting duplicate encodings. This is especially relevant in a pass whose central issue is explanatory weight.

    References: [bank.py:39](/tmp/legit-review-followup-4/round/scored/bank.py:39), [weights.py:189](/tmp/legit-review-followup-4/round/scored/weights.py:189), [ACCOUNT.md:162](/tmp/legit-review-followup-4/round/scored/ACCOUNT.md:162).

23. **The draft’s caveats are substantial, but they do not repair its headline or establish its concluding philosophical claims.** It correctly discloses stipulated principals, arbitrary languages, miss-cost sensitivity, the changed matching standard, the unweighted bank and the missing five-part experiment. Those disclosures deserve to remain.

    It still fails to say that no valid predictive residual code was supplied; no second-predictor reproduction was performed; language sensitivity changes candidate membership; reading 3 is mostly vacuous; tied maximizers differ on no-gain; the lemma fails under the actual exemptions; and the aggregate running-sum predicate was not connected to the claimed `Scoring`.

    Conversely, “exemptions, not protection” understates the limited result that **unexempted** legitimacy constrains candidate-relative bests and gaps. That protection is real but conditional on the candidate and insufficient for evaluation invariance.

    The final claim that, if purposes fail to beat tables in a larger scene, “the account … has no subject” is unsupported. Failure in another selected language and vocabulary would remain a result about that experiment. The most urgent next result is a coherent predictive model with a fixed candidate class, explicit noise likelihood and actual held-out prediction—not merely a scene with more table entries.

    References: [REPORT-section-draft.md:165](/tmp/legit-review-followup-4/REPORT-section-draft.md:165), [REPORT-section-draft.md:214](/tmp/legit-review-followup-4/REPORT-section-draft.md:214), [REPORT-section-draft.md:230](/tmp/legit-review-followup-4/REPORT-section-draft.md:230).