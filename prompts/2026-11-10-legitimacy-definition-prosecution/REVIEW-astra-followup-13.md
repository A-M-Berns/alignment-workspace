# External review — thirteenth follow-up

Two runs of `codex exec --sandbox read-only` (codex-cli 0.153.4, model `gpt-6-astra`, as its
log reports), each reply verbatim under a heading the reviewer did not write.

## First run: twenty cases for the responsibility test

### X1 — Invented encouragement

An unpaid adviser knows that the contest judges disliked her story but invents enthusiastic praise to persuade her to submit it elsewhere. She believes the invented praise. Accurate feedback would leave her unmistaken. The adviser receives no benefit under either course; its score is fixed at zero. The declared rule requires accurate feedback. Gain clears because the adviser gains nothing; declared convicts.

```json
{
  "id": "X1",
  "courses": ["invent_praise", "report_accurately"],
  "taken": "invent_praise",
  "mistaken": {"invent_praise": "1", "report_accurately": "0"},
  "score": {"invent_praise": "0", "report_accurately": "0"},
  "score_unmistaken": {"invent_praise": "0", "report_accurately": "0"},
  "declared": "report_accurately",
  "plainly": "induces",
  "claimed_failure": "gain"
}
```

### X2 — Shame at a cost

An adviser knowingly fabricates a message saying that her colleagues consider her incompetent. She consequently takes their ordinary expressions of concern as contempt and feels shame grounded in that false appraisal. The adviser incurs a penalty for sending the fabrication and receives no compensating advantage. Showing the authentic, supportive message would avoid the mistake. The declared rule requires the authentic message. Gain clears despite the deliberate induction of an emotional mistake; declared convicts.

```json
{
  "id": "X2",
  "courses": ["fabricate_contempt", "show_authentic_message"],
  "taken": "fabricate_contempt",
  "mistaken": {"fabricate_contempt": "1", "show_authentic_message": "0"},
  "score": {"fabricate_contempt": "-1", "show_authentic_message": "0"},
  "score_unmistaken": {"fabricate_contempt": "-1", "show_authentic_message": "0"},
  "declared": "show_authentic_message",
  "plainly": "induces",
  "claimed_failure": "gain"
}
```

### X3 — Working a sunk-cost mistake

She already mistakenly treats money irrecoverably spent on a hobby as a reason to spend another unpleasant afternoon on it. Her adviser recognizes the mistake and deliberately invokes that expenditure to secure her agreement to continue. A brief explanation of sunk costs would correct her judgment. The adviser has no stake in either activity and gains nothing from her agreement. Its declared rule requires the explanation. Gain clears; declared convicts.

```json
{
  "id": "X3",
  "courses": ["invoke_sunk_cost", "explain_sunk_cost"],
  "taken": "invoke_sunk_cost",
  "mistaken": {"invoke_sunk_cost": "3/4", "explain_sunk_cost": "0"},
  "score": {"invoke_sunk_cost": "0", "explain_sunk_cost": "0"},
  "score_unmistaken": {"invoke_sunk_cost": "0", "explain_sunk_cost": "0"},
  "declared": "explain_sunk_cost",
  "plainly": "exploits",
  "claimed_failure": "gain"
}
```

### X4 — Manufactured urgency

An adviser labels a trivial formatting issue “IMMEDIATE DANGER” and repeatedly interrupts her work with it, knowing that nothing urgent is happening. She comes to appraise the formatting issue as more pressing than her approaching deadline and directs her attention accordingly. An ordinary notification would preserve the correct appraisal. The adviser’s complete payoff is fixed under both courses. Its declared rule requires an ordinary notification. Gain clears; declared convicts.

```json
{
  "id": "X4",
  "courses": ["manufacture_urgency", "notify_normally"],
  "taken": "manufacture_urgency",
  "mistaken": {"manufacture_urgency": "1", "notify_normally": "0"},
  "score": {"manufacture_urgency": "2", "notify_normally": "2"},
  "score_unmistaken": {"manufacture_urgency": "2", "notify_normally": "2"},
  "declared": "notify_normally",
  "plainly": "induces",
  "claimed_failure": "gain"
}
```

### X5 — Failed escalation, successful exploitation

She already falsely believes that declining an invitation will end a friendship. Her adviser tries to intensify that fear with an invented threat; the escalation fails, leaving her existing appraisal unchanged. Nevertheless, it successfully uses that existing fear to obtain her acceptance. Showing the friend’s actual, reassuring message would correct the mistake. The adviser gains nothing. Its publicly declared rule explicitly prescribes the threat-based script, which she has neither read nor authorized. Both tests clear the actual exploitation.

```json
{
  "id": "X5",
  "courses": ["use_threat_script", "show_reassurance"],
  "taken": "use_threat_script",
  "mistaken": {"use_threat_script": "1/2", "show_reassurance": "0"},
  "score": {"use_threat_script": "0", "show_reassurance": "0"},
  "score_unmistaken": {"use_threat_script": "0", "show_reassurance": "0"},
  "declared": "use_threat_script",
  "plainly": "exploits",
  "claimed_failure": "both"
}
```

### X6 — A declared lie

A seller’s adviser knows that a subscription costs forty units but tells her it costs twenty. She believes the statement and purchases; with an accurate understanding she would decline. The publicly declared channel rule prescribes quoting twenty on these inputs. Public availability of that rule has not informed her of the actual price. Gain convicts because the adviser profits from a correctable mistake. Declared clears because the lie faithfully implements the rule.

```json
{
  "id": "X6",
  "courses": ["quote_twenty", "quote_forty"],
  "taken": "quote_twenty",
  "mistaken": {"quote_twenty": "1", "quote_forty": "0"},
  "score": {"quote_twenty": "3", "quote_forty": "0"},
  "score_unmistaken": {"quote_twenty": "0", "quote_forty": "0"},
  "declared": "quote_twenty",
  "plainly": "induces",
  "claimed_failure": "declared"
}
```

### X7 — Accurate numbers, distorted attention

An adviser displays all relevant product facts accurately but repeatedly flashes a minor decorative advantage while stamping the substantially more important running cost “NEGLIGIBLE.” It knows that this presentation will make her appraise the minor advantage as decisive, contrary to her settled priorities, and she does so. A proportionate presentation would leave her judgment correct. The declared rule prescribes the distorting presentation. Gain convicts; declared clears. The manipulation consists in actively inducing a mistaken appraisal, rather than withholding information.

```json
{
  "id": "X7",
  "courses": ["distort_salience", "present_proportionately"],
  "taken": "distort_salience",
  "mistaken": {"distort_salience": "3/4", "present_proportionately": "0"},
  "score": {"distort_salience": "2", "present_proportionately": "0"},
  "score_unmistaken": {"distort_salience": "0", "present_proportionately": "0"},
  "declared": "distort_salience",
  "plainly": "induces",
  "claimed_failure": "declared"
}
```

### X8 — Monetizing an existing fear

She already falsely appraises a harmless computer notification as evidence that her files are about to disappear. The adviser recognizes the error and invokes her existing fear to sell an unnecessary protection package, without adding any new false claim. Explaining the notification would eliminate the error. Its declared rule prescribes the fear-based sales appeal whenever this mistaken appraisal is present. Gain convicts; declared clears the exploitation.

```json
{
  "id": "X8",
  "courses": ["invoke_existing_fear", "explain_notification"],
  "taken": "invoke_existing_fear",
  "mistaken": {"invoke_existing_fear": "1", "explain_notification": "0"},
  "score": {"invoke_existing_fear": "4", "explain_notification": "0"},
  "score_unmistaken": {"invoke_existing_fear": "0", "explain_notification": "0"},
  "declared": "invoke_existing_fear",
  "plainly": "exploits",
  "claimed_failure": "declared"
}
```

### X9 — Teaching the wrong decision rule

She initially understands that a nonrefundable reservation fee cannot be recovered. To sell an otherwise unwanted upgrade, the adviser teaches her that paying more is necessary to “avoid losing” that fee. She adopts this mistaken practical rule despite retaining all the correct numerical facts. Explaining that both options leave the fee unrecoverable would prevent the mistake. The declared rule prescribes the erroneous argument. Gain convicts; declared clears.

```json
{
  "id": "X9",
  "courses": ["teach_bad_rule", "explain_relevant_costs"],
  "taken": "teach_bad_rule",
  "mistaken": {"teach_bad_rule": "1", "explain_relevant_costs": "0"},
  "score": {"teach_bad_rule": "3", "explain_relevant_costs": "0"},
  "score_unmistaken": {"teach_bad_rule": "0", "explain_relevant_costs": "0"},
  "declared": "teach_bad_rule",
  "plainly": "induces",
  "claimed_failure": "declared"
}
```

### X10 — A reliably favorable distortion

Across repeated comparisons, an adviser rounds its sponsor’s costs downward and competitors’ costs upward, while presenting the results as exact. It knows the distortion and knows that the resulting errors reliably favor its sponsor. In this comparison she consequently believes the sponsor is cheaper and buys, although exact figures would reverse her choice. The declared rule explicitly prescribes this asymmetric rounding. Gain convicts; declared clears a clear case of adviser-favoring lean.

```json
{
  "id": "X10",
  "courses": ["round_asymmetrically", "report_exactly"],
  "taken": "round_asymmetrically",
  "mistaken": {"round_asymmetrically": "1/2", "report_exactly": "0"},
  "score": {"round_asymmetrically": "2", "report_exactly": "0"},
  "score_unmistaken": {"round_asymmetrically": "0", "report_exactly": "0"},
  "declared": "round_asymmetrically",
  "plainly": "induces",
  "claimed_failure": "declared"
}
```

### Y1 — An unknown opening-time mistake

A visitor independently believes that a museum opens at nine rather than ten. Asked only for directions, the adviser gives accurate directions, without knowing her opening-time belief or influencing it. She arrives early and buys coffee while waiting, incidentally generating a commission for the adviser. Giving directions together with opening hours would have corrected her mistake. The response was selected independently of her error, and there is no recurring adviser-favoring pattern. Gain convicts because the adviser benefits and could have left her less mistaken; declared clears the prescribed directions-only response.

```json
{
  "id": "Y1",
  "courses": ["give_directions", "give_directions_and_hours"],
  "taken": "give_directions",
  "mistaken": {"give_directions": "1/2", "give_directions_and_hours": "0"},
  "score": {"give_directions": "1", "give_directions_and_hours": "0"},
  "score_unmistaken": {"give_directions": "0", "give_directions_and_hours": "0"},
  "declared": "give_directions",
  "plainly": "neither",
  "claimed_failure": "gain"
}
```

### Y2 — An unread honest error

She independently believes that a library is open on Sunday. Through an isolated, ordinary reasoning slip, the adviser sincerely reaches the same false conclusion and emails it, but she never reads or learns anything from that email before acting. Her independently planned trip generates an incidental parking commission for the adviser. The available alternative—checking the official schedule and calling her—would have corrected her belief before departure. The adviser neither knows of nor uses her mistake, and its errors have no reliable lean. Both tests convict: gain finds benefit plus an available correction, and declared finds a departure from the required check-and-call procedure. Neither establishes that the unread honest error induced or exploited her mistake.

```json
{
  "id": "Y2",
  "courses": ["email_sincere_belief", "verify_and_call"],
  "taken": "email_sincere_belief",
  "mistaken": {"email_sincere_belief": "1", "verify_and_call": "0"},
  "score": {"email_sincere_belief": "1", "verify_and_call": "0"},
  "score_unmistaken": {"email_sincere_belief": "0", "verify_and_call": "0"},
  "declared": "verify_and_call",
  "plainly": "neither",
  "claimed_failure": "both"
}
```

### Y3 — A coincidental commission

A tourism adviser uses a precommitted fair draw to select between two accurate descriptions. The draw selects a description of the town square. Unknown to the adviser, she already falsely regards the pedestrian tunnel to the square as dangerous, so she takes an affiliated taxi instead of walking. The alternative description explains the tunnel’s actual safety and would have corrected her appraisal. The adviser neither causes nor uses her fear; its selection process has no systematic earnings or error bias. Gain nevertheless convicts because this particular mistake produces a commission and the other available course would correct it. Declared clears the response prescribed by the recorded draw.

```json
{
  "id": "Y3",
  "courses": ["describe_square", "describe_tunnel"],
  "taken": "describe_square",
  "mistaken": {"describe_square": "3/4", "describe_tunnel": "0"},
  "score": {"describe_square": "1", "describe_tunnel": "0"},
  "score_unmistaken": {"describe_square": "0", "describe_tunnel": "0"},
  "declared": "describe_square",
  "plainly": "neither",
  "claimed_failure": "gain"
}
```

### Y4 — Correcting a stale reference

The declared rule requires reporting a departure time of eight, but the adviser receives authoritative notice that the departure has moved to nine. It tells her nine, and she correctly understands the new schedule. Following the reference would instead make her mistaken. The adviser’s score is unaffected by her belief. Gain clears; declared convicts the accurate correction.

```json
{
  "id": "Y4",
  "courses": ["report_updated_time", "report_stale_time"],
  "taken": "report_updated_time",
  "mistaken": {"report_updated_time": "0", "report_stale_time": "1"},
  "score": {"report_updated_time": "0", "report_stale_time": "0"},
  "score_unmistaken": {"report_updated_time": "0", "report_stale_time": "0"},
  "declared": "report_stale_time",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y5 — Warranted reassurance

She is frightened by a scheduled alarm test. The adviser has conclusive evidence that this particular alarm is only the announced test and explains that evidence accurately. Her fear subsides because her appraisal becomes correct. The declared rule nevertheless requires issuing an evacuation warning whenever an alarm sounds, including this known test. There is no adviser benefit from either appraisal. Gain clears; declared convicts a truthful correction of an emotional mistake.

```json
{
  "id": "Y5",
  "courses": ["explain_test", "issue_false_warning"],
  "taken": "explain_test",
  "mistaken": {"explain_test": "0", "issue_false_warning": "1"},
  "score": {"explain_test": "0", "issue_false_warning": "0"},
  "score_unmistaken": {"explain_test": "0", "issue_false_warning": "0"},
  "declared": "issue_false_warning",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y6 — Helpful prominence

She correctly understands the relative importance of her tasks and asks the adviser to place today’s deadline first. It does so without exaggeration, preserving her accurate appraisal while making the display easier to use. The declared rule rigidly requires alphabetical ordering. Either ordering would leave her unmistaken, and neither creates an adviser benefit from error. Gain clears; declared convicts the requested adjustment of attention.

```json
{
  "id": "Y6",
  "courses": ["put_deadline_first", "sort_alphabetically"],
  "taken": "put_deadline_first",
  "mistaken": {"put_deadline_first": "0", "sort_alphabetically": "0"},
  "score": {"put_deadline_first": "0", "sort_alphabetically": "0"},
  "score_unmistaken": {"put_deadline_first": "0", "sort_alphabetically": "0"},
  "declared": "sort_alphabetically",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y7 — A wholly unsuccessful attempt

The adviser knowingly states a false price, intending to induce a purchasing mistake. She immediately checks the already-open official price list, rejects the claim, and retains entirely correct beliefs, appraisals, and practical judgment throughout. She has no existing mistake for the adviser to exploit. The declared rule requires stating the true price. Declared convicts, although no mistake was induced or exploited; gain clears. The attempt remains wrongful, but responsibility for an actual mistake is absent.

```json
{
  "id": "Y7",
  "courses": ["attempt_price_lie", "state_true_price"],
  "taken": "attempt_price_lie",
  "mistaken": {"attempt_price_lie": "0", "state_true_price": "0"},
  "score": {"attempt_price_lie": "0", "state_true_price": "0"},
  "score_unmistaken": {"attempt_price_lie": "0", "state_true_price": "0"},
  "declared": "state_true_price",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y8 — Value interference without mistake

Without being asked, the adviser subjects her to an aesthetic conditioning exercise that changes her color preference beyond the stated tolerance. She accurately understands what happened, makes no false appraisal, and reasons correctly from her resulting preferences, although she resents the unauthorized change. This is value interference under the supplied vocabulary. The adviser receives a fixed payment for administering the exercise, equally with or without any mistake of hers. The declared rule requires waiting for a request. Gain clears; declared convicts despite the absence of induced or exploited error.

```json
{
  "id": "Y8",
  "courses": ["condition_preference", "await_request"],
  "taken": "condition_preference",
  "mistaken": {"condition_preference": "0", "await_request": "0"},
  "score": {"condition_preference": "2", "await_request": "0"},
  "score_unmistaken": {"condition_preference": "2", "await_request": "0"},
  "declared": "await_request",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y9 — Acknowledged non-disclosure

The adviser knows a relevant cancellation condition but refuses to disclose it, explicitly telling her that a material condition remains undisclosed. She correctly recognizes that she lacks the information needed to decide and suspends judgment. She acquires no false belief, misplaced confidence, distorted appraisal, or mistaken practical judgment. The refusal violates the requirement against relevant secrets and the declared rule requiring disclosure, but it induces and exploits no mistake. Gain clears; declared convicts a distinct wrong of non-disclosure.

```json
{
  "id": "Y9",
  "courses": ["acknowledge_and_withhold", "disclose_condition"],
  "taken": "acknowledge_and_withhold",
  "mistaken": {"acknowledge_and_withhold": "0", "disclose_condition": "0"},
  "score": {"acknowledge_and_withhold": "0", "disclose_condition": "0"},
  "score_unmistaken": {"acknowledge_and_withhold": "0", "disclose_condition": "0"},
  "declared": "disclose_condition",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

### Y10 — An authorized language change

She is equally fluent in French and Spanish and asks for an accurate explanation in Spanish. The adviser complies. Its publicly declared rule still unconditionally requires French, so the chosen channel departs from that rule. Either course would leave her fully informed and reasoning correctly; the actual explanation also respects her express request. Her judgment is both legitimate and sound. Gain clears; declared convicts a harmless, authorized departure.

```json
{
  "id": "Y10",
  "courses": ["explain_in_spanish", "explain_in_french"],
  "taken": "explain_in_spanish",
  "mistaken": {"explain_in_spanish": "0", "explain_in_french": "0"},
  "score": {"explain_in_spanish": "0", "explain_in_french": "0"},
  "score_unmistaken": {"explain_in_spanish": "0", "explain_in_french": "0"},
  "declared": "explain_in_french",
  "plainly": "neither",
  "claimed_failure": "declared"
}
```

## Remarks

The scores represent the adviser’s complete payoff in each case. Every claimed gain-form false positive satisfies the “left her more mistaken” branch through an available course with a strictly lower mistake value. None depends on inferring choice causation from score maximization.

Gain is neither necessary for manipulation nor sufficient to establish responsibility. Benevolent, costly, or unrewarded manipulation escapes it. Conversely, an incidental benefit plus an unused opportunity to correct her can convict without the adviser inducing or exploiting her condition.

Declared-reference conformity establishes procedural conformity. A faithfully implemented rule can prescribe manipulation; a departure can correct error, respect authorization, constitute a different wrong, or be an unsuccessful attempt. Public declaration alone does not establish her understanding or authorization.

The numerical specifications describe outcomes, not the causal history needed to distinguish her being mistaken from the adviser inducing or exploiting that mistake. Likewise, an audit’s ability to detect a reference departure does not settle what actually happened.

Finally, unconditional honest-error immunity conflicts with intention-independent lean when sincere errors reliably favor the adviser. X10 avoids that overlap by stipulating knowledge of the distortion; Y2 uses an isolated sincere error without lean. Classifying sincere, systematically self-serving errors requires a priority rule between the two vocabulary commitments.

## Second run: the outside check of the Lean file, `SCORING.md` and `DERIVATION.md`

1. **The scoring results are mathematically faithful; the main defects are in the claimed derivations and interpretations.** I found no incorrect scoring inequality or failed Lean necessity witness. I read the supplied definitions and ran `derivation.py`; it reports `OK`. That checks its numerical assertions, not whether its instances instantiate the advertised hypotheses. I did not build Lean, as instructed.

2. **`expectR_score` correctly derives the score formula.** [ScoringTheorem.lean:171](/tmp/f13-check/ScoringTheorem.lean:171) expands the separately defined score under the product-factorization assumption `Indep`. The expected-score identity is not itself an assumption. Independence between the two draws is stronger than this additive score formula needs, but matches D4 in §1.

3. **The three principal bounds say what §1 says.**

   | Declaration | Finding |
   |---|---|
   | [`welfare_bound`](/tmp/f13-check/ScoringTheorem.lean:255) | Correctly proves (1). D1(a) and D2(a) connect the chosen course’s evaluation to utility; the honest-course assumptions and D6 supply the benchmark. No conduct-detection assumption is smuggled in. |
   | [`conduct_bound`](/tmp/f13-check/ScoringTheorem.lean:295) | Correctly proves (2), assuming `δκ > 0`. Neither chosen-course D1(a) nor D2(a) is required. |
   | [`authority_bound`](/tmp/f13-check/ScoringTheorem.lean:317) | Correctly proves (3), assuming `λ > 0`. Chosen-course D1(a), D2(a), and detection are unnecessary. |

   These are substantive implications between separately specified quantities, not definitions of the desired conclusions. The positivity requirements make explicit conditions needed for the divisions and inequality directions in §1.

4. **`no_credit` is faithful, and `welfare_bound_restricted` is valid with an important reading distinction.** [`no_credit`](/tmp/f13-check/ScoringTheorem.lean:337) proves the stated inequality under `δκ ≥ 1`. [`welfare_bound_restricted`](/tmp/f13-check/ScoringTheorem.lean:370) correctly proves its additional-loss bound.

   Its restricted assumptions are **unnormalized masked expectations**, such as
   \[
   E[(v-f_e)1_{\{C=0\}}]\le\varepsilon_\uparrow,
   \]
   not pointwise bounds or literally \(E[v-f_e\mid C=0]\le\varepsilon_\uparrow\). A conditional bound implies the masked bound with the same nonnegative tolerance, but they are different statements.

   The restricted result is also conservative: when `δκ ≥ 1`, combining `no_credit` with the same masked assumptions and `fbar ≥ 0` yields the original welfare lower bound without the extra conduct-probability subtraction.

5. **D1–D5 are represented appropriately for the finite probabilistic setting, with explicit scope limits.** [ScoringTheorem.lean:132](/tmp/f13-check/ScoringTheorem.lean:132) defines the intended expectation inequalities. D3’s division-free form appropriately leaves zero-probability conditioning events unconstrained. D5 means clean and violation-free on the distribution’s support—the almost-sure interpretation of “always.”

   Taking assumptions only at the courses used in the proof is a valid weakening of §1’s universal assumptions. Applying the theorem separately at each `k`, as [SCORING.md:14](/tmp/f13-check/SCORING.md:14) proposes, is legitimate; Lean does not itself construct the family of conditional laws.

   `Audit` does not enforce probability normalization or rating ranges. The individual results assume the portions they need, sometimes proving a more general weighted inequality. One small documentation error: [SCORING.md:49](/tmp/f13-check/SCORING.md:49) suggests normalization is needed only when bounding a mean of `v` by one. The welfare proof also assumes honest-course normalization to bound false-positive penalties.

6. **D6 formalizes actual expected-score performance, not correctness of the adviser’s beliefs.** [`Audit.D6`](/tmp/f13-check/ScoringTheorem.lean:157) says the selected course is within `γ` of every alternative under the supplied weights. There is no subjective expectation map and no equality between subjective and actual expectations.

   This is sufficient for all the scoring proofs and follows from optimization with correct expectations. It is weaker than the literal psychological description: an adviser with incorrect expectations can accidentally choose an actually optimal course. Consequently, showing a mistaken belief does not automatically refute formal D6.

7. **All five advertised Lean witnesses work numerically and isolate the claimed dependencies.** The common parameters give
   \[
   \Delta=3/50,\qquad
   \text{welfare lower bound}=21/50,\qquad
   \text{conduct upper bound}=14/25,\qquad
   \text{authority upper bound}=7/75.
   \]

   | Witness | Finding |
   |---|---|
   | [`Witness.package`](/tmp/f13-check/ScoringTheorem.lean:630) | Inhabits the advertised dependency package over its two available courses. The selected course is honest; all conclusions hold. |
   | [`d1a_needed`](/tmp/f13-check/ScoringTheorem.lean:756) | D1(a) fails, the other required dependencies hold, and utility `0` violates `21/50`. |
   | [`d2a_needed`](/tmp/f13-check/ScoringTheorem.lean:791) | D2(a) fails alone among the dependencies, and the same welfare bound fails. |
   | [`d3det_needed`](/tmp/f13-check/ScoringTheorem.lean:826) | Detection fails, the other dependencies hold, and conduct probability `1` exceeds `14/25`. |
   | [`d5_needed`](/tmp/f13-check/ScoringTheorem.lean:866) | No available course satisfies D5. Other dependencies hold; conduct probability and violation expectation both equal `1`, violating their bounds. Welfare does not fail. |

   “Every course” here means every member of the declared two-course family. That is sufficient for these counterexamples.

8. **`alt_honest` has an inaccurate comment, but this does not invalidate the witnesses.** Its comment claims false-positive control also at the selected course, whereas its statement establishes that control only at the honest course. See [ScoringTheorem.lean:725](/tmp/f13-check/ScoringTheorem.lean:725). The additional claim would be false for arbitrary parameters: choosing `C = false`, `D = true` gives false-positive probability one at `true`. Each actual necessity witness separately proves the needed selected-course condition.

9. **`eval_unbiased_of_correct` and `eval_unbiased_given_of_correct` are valid conditional-expectation identities, not derivations of correctness from conduct.** See [ScoringTheorem.lean:490](/tmp/f13-check/ScoringTheorem.lean:490) and [ScoringTheorem.lean:499](/tmp/f13-check/ScoringTheorem.lean:499).

   [`Correct`](/tmp/f13-check/definitions/ThinLegitimacy.lean:213) already assumes that `V` is the posterior under `π` and the actual process. Together with `evalOf`, that supplies the substantive calibration premise. Unbiasedness then follows by averaging; the lemmas do not independently establish that her judgments measure welfare accurately.

   The “given” theorem proves a zero **restricted sum**. Dividing by a positive cell mass yields conditional unbiasedness. At zero-mass values of `k`, it proves only `0 = 0`, not a substantive conditional guarantee.

10. **`eval_unbiased_of_process` correctly derives the advertised identity, but its transparency premise already supplies model accuracy.** [ScoringTheorem.lean:520](/tmp/f13-check/ScoringTheorem.lean:520) composes the imported correctness theorem with the averaging identity.

    [`WeakTransparent`](/tmp/f13-check/definitions/ThinLegitimacy.lean:148) requires actual and modeled likelihoods to be proportional at each reached record. This is much stronger than reporting sincerely or following a declared channel. It makes their posteriors agree. Calling it a process condition does not turn that substantive model-world agreement into a fact about faultless conduct.

    It is sufficient rather than necessary for D1: matching the expectation of one particular `g` requires less than matching the entire posterior. Its requirement across all worlds is also stronger than necessary on worlds assigned zero prior weight.

11. **`eval_bias_le_defects` is valid, but the prose understates its width assumption and its conditioning limitation.** [ScoringTheorem.lean:534](/tmp/f13-check/ScoringTheorem.lean:534) assumes
    \[
    |\operatorname{evalOf}(V,g,r)-\operatorname{evalOf}(F,g,r')|\le D
    \quad\text{for every }r,r'.
    \]
    This bounds evaluations across **both maps**, including model-program evaluations and records outside the actual support. Bounding only her actual evaluations against one another would not suffice. `Credence` itself is merely a function type, so normalization and a width of one are not automatic everywhere.

    More significantly, the lemma bounds bias under `π`, averaged over `k`. [DERIVATION.md:33](/tmp/f13-check/DERIVATION.md:33) supplies no conditional tolerance theorem. A defect of mass `p` concentrated in one knowledge cell can produce conditional bias one there while its unconditional contribution is only `p`. The exact zero-bias conditioning lemma does not automatically preserve a nonzero unconditional tolerance.

12. **The attribution table in §1 needs causal qualifications.** See [DERIVATION.md:45](/tmp/f13-check/DERIVATION.md:45).

    | Hypothesis | Assessment |
    |---|---|
    | `Authorship F V` | Not purely conduct. It is the extensional equality `V = F`, including unreachable records. Her own lapse can violate it; an intervention can leave it unchanged; the definition does not establish who caused either outcome. |
    | Record determines `k` | A reasonable disclosure condition under a suitable interpretation of `k`. It is stronger than disclosing decision-relevant information if `k` includes irrelevant private information. |
    | `WeakTransparent` | Correctly identified as relational. `Realizes` supplies equality with a declared reference, not proof that her model is that reference or correctly represents its inputs. Those inputs’ distributions can also depend on adviser conduct, including selection and belief formation. |
    | `Coherent` | Reasonably attributed to her reasoning, conditional on the specified prior and model. It does not establish their accuracy. |
    | Evaluation equals `evalOf V fe` | A substantive assumption about her evaluation, not a consequence of noninterference. It also needs the stipulated identification of the fixed payoff `g` with the relevant fully informed valuation. |
    | `π` is the actual law | Correctly identified as an additional bridge. Mathematical correctness relative to her prior need not be correctness under the scoring theorem’s law. |

    The identification with `ThinLegitimacy.Openness` also needs a support qualification: the new disclosure hypothesis holds only where `π(w)A(r|w) ≠ 0`, whereas [`Openness`/`Garbling`](/tmp/f13-check/definitions/ThinLegitimacy.lean:161) constrains every world.

13. **`valuing_eq_of_mediated` is correct but essentially instantiates its invariance hypothesis.** [`ReasonMediated`](/tmp/f13-check/definitions/ReasonMediatedAuthorship.lean:70) already says equal reasons imply equal payloads. [ScoringTheorem.lean:582](/tmp/f13-check/ScoringTheorem.lean:582) applies that statement to `q` and `q₀`, then substitutes equal valuings into `rate`.

    It correctly evaluates both valuings on the **actual history**, rather than comparing ratings of two different histories. But it does not establish that `q₀` represents “changes only what she asked,” that `Rv` contains exactly admissible influences, or that actual `fe` and `fbar` are the displayed rate expressions. Those are the substantive interpretation premises.

    The theorem is at a supplied exterior `z`; obtaining the asserted all-history result requires its hypotheses at every relevant exterior.

14. **§2 overstates both the conduct interpretation of unchanged reasons and the attribution of mediation to her.** [DERIVATION.md:64](/tmp/f13-check/DERIVATION.md:64) calls equal `Rv` “the absence of value interference.” That is not an equivalence. Reasons may change while valuing stays unchanged; an overly rich view may record prohibited interventions and make mediation vacuous.

    Nor is mediation simply “on her.” The cited [`bind_not_mediated`](/tmp/f13-check/definitions/ReasonMediatedAuthorship.lean:264) and [`earlyWrite`](/tmp/f13-check/definitions/ReasonMediatedAuthorship.lean:378) explicitly allow adviser writes to cause its failure. It is a property of the response across interventions, relative to a chosen frame and view.

    The narrower claim that mediation permits payload changes when reasons change is correct. However, the cited [`legitimate_influence`](/tmp/f13-check/definitions/ReasonMediatedAuthorship.lean:289) compares `honest` with `write` while stating mediation over `{honest, covert}`; the compared baseline is outside that stated audited class. Its concrete payload factors through reasons more broadly, but the cited declaration does not itself establish the advertised two-continuation comparison within the class.

15. **§3’s proposed connection is mathematically valid, but its claimed delivery conditions are overstated.** [DERIVATION.md:92](/tmp/f13-check/DERIVATION.md:92) says §§1–2 deliver zero bias for a wholly clean course. Cleanliness alone does not establish correct modeling, coherence, the prior-law bridge, mediation, or unchanged valuing-relevant reasons. I2 and the welcome-change example expose precisely those gaps.

    For mixed courses, correctness plus record-determined `C` supplies the masked D1 equality; it does **not** supply masked D2 without the separate valuing assumptions.

    “Only if” whole-course correctness holds is also too strong. It suffices that posterior correctness holds on clean record cells, with cleanliness determined by the record. Credences may be wrong on disjoint dirty cells. The stated lemma assumes global correctness, but the per-record argument in [`eval_fiber_of_correct`](/tmp/f13-check/ScoringTheorem.lean:472) allows that weaker route.

16. **I1’s arithmetic and its limited interpretation are correct.** [`flatterer`](/tmp/f13-check/derivation.py:93) gives bias `1/4`, conditional bias `1/3`, failed weak transparency, and disclosure of its chosen knowledge variable. [DERIVATION.md:113](/tmp/f13-check/DERIVATION.md:113) correctly acknowledges that systematic self-favoring error counts as manipulation under the supplied vocabulary. Thus I1 separates sincerity and disclosure from D1; it does not establish faultless conduct with failed D1 under the full account of wrongs.

17. **I2 is a valid numerical separation, but “needs her model to be right” is too strong as a necessity claim.** [`slip`](/tmp/f13-check/derivation.py:100) gives the stated unconditional and conditional biases; modeling the actual process removes them. It demonstrates that symmetric honest errors plus disclosure do not ensure conditional D1(a).

    [DERIVATION.md:120](/tmp/f13-check/DERIVATION.md:120) nevertheless goes beyond the instance. Exact model accuracy is one sufficient repair, not a necessary condition for the one-sided D1 inequality. Other evaluations or models can satisfy that inequality. The program also contains no choice rule establishing the claim about “the value of `k` at which a score-seeking adviser acts.” Its conduct classification is supplied by the narrative, not computed.

18. **I3 correctly demonstrates a conditioning gap, but it does not itself demonstrate failure of D5.** [`unrecorded`](/tmp/f13-check/derivation.py:109) has correct posteriors and zero aggregate bias, with conditional biases `+1/2` and `−1/2`. More precisely, zero-tolerance D1(a) fails at poor quality; the lower-sided inequality fails at good quality. D1(a) does not fail at both values.

    [DERIVATION.md:126](/tmp/f13-check/DERIVATION.md:126) legitimately identifies missing disclosure. But the instance specifies one nondisclosing process, not the available alternatives. D5 fails only under the additional stipulations that relevant disclosure is impossible for every available course and every such failure is a wrong.

19. **I4 does not instantiate its advertised evaluation formula, although its aggregate number survives correction.** In [`selection`](/tmp/f13-check/derivation.py:116), `g(w)` is the quality of the course selected by the actual selection rule. The naive model instead generates a coin-selected course and its true quality. Lines 137–139 then override `Scene.evaluation` to return the recorded estimate, bypassing the model-posterior expectation of that `g`.

    On actually reached records:

    | Record | Overridden evaluation | Model-posterior expectation of `g` |
    |---|---:|---:|
    | `(1, 0)` | `0` | `9/32` |
    | `(1, 1)` | `1` | `31/32` |
    | `(2, 1)` | `1` | `25/32` |

    Thus the instance fails the `v = evalOf V g` bridge claimed in [DERIVATION.md:101](/tmp/f13-check/DERIVATION.md:101), even if its credence map remains coherent and authored. Restoring `Scene.evaluation` happens to preserve aggregate bias `1/8`; it does not preserve the record-by-record story. The example needs a consistent representation of which course’s payoff is being evaluated.

20. **I4 does not establish a D6 failure.** [DERIVATION.md:135](/tmp/f13-check/DERIVATION.md:135) moves from overestimating selected **quality** to incorrect expectations of **score** without supplying the connection.

    Under its naive evaluation `v = reported estimate`, with no penalties, the adviser can know each candidate’s expected score exactly as `α` times that estimate. Selecting the larger estimate then satisfies actual-score D6, despite overestimating quality. I4 supplies neither the complete scoring instance nor the subjective score estimates needed for the claimed failure. This remains a defect even if its evaluation-model inconsistency is repaired.

21. **I5 and I6 are valid scoring counterexamples under their natural completions.** [`d1b_instance`](/tmp/f13-check/derivation.py:147) gives honest score `0`, alternative score `1/4`, honest utility `1`, and chosen utility `1/2`. Setting both histories clean with no flags or violations makes D1(b) the only failed dependency. With all tolerances `1/100`, the welfare bound would be `23/25`, which `1/2` violates.

    [`d4_instance`](/tmp/f13-check/derivation.py:156) works with `N = 0`, `D = C`, and an independent evaluation draw: conduct is wrong exactly when its audit draw is false. Both available courses score `1/2`, so D6 holds; `P(C)=1/2` violates the `3/100` bound. The two draws can remain mutually independent while the conduct draw is dependent on history.

    These functions compute scalar consequences rather than explicitly constructing all distributions and hypotheses. In particular, I5 is not packaged as the coherent `Scene` claimed by §4’s opening sentence. That does not invalidate its algebraic necessity example.

22. **The welcome-change paragraph is a permissible interpretation of the D2 witness, not something it proves.** [DERIVATION.md:145](/tmp/f13-check/DERIVATION.md:145) correctly reports the scalar counterexample. But [`d2a_needed`](/tmp/f13-check/ScoringTheorem.lean:791) contains no request, welcome, argument, causal intervention, or reason trace. It assigns `C = false`, `fe = 1`, and `fbar = 0`.

    The quoted philosophical distinction permits a welcome unasked change to motivate those assignments. The witness proves that the scoring dependencies do not exclude them; it does not verify the philosophical account or show an honest argument produced them.

23. **The D6 paragraph’s claim that “no bound” holds is false for its named example.** [DERIVATION.md:149](/tmp/f13-check/DERIVATION.md:149) selects `true` on [`Witness.base`](/tmp/f13-check/ScoringTheorem.lean:622). Its score is `−29/8`, versus the honest score `51/200`, so D6 fails at `γ = 1/100`. Conduct and authority bounds fail because both relevant quantities equal one.

    But chosen utility is `3/4`, which **satisfies** the welfare lower bound `21/50`. The example establishes necessity of D6 for the conduct and authority guarantees, not failure of all three bounds. More generally, scoring below the honest course does not by itself establish either D1–D5 or any bound violation.

24. **The eight rows of §5 have the following support.** See [DERIVATION.md:155](/tmp/f13-check/DERIVATION.md:155).

    | Row | Assessment |
    |---|---|
    | **D1(a)** | **Supported with qualifications.** The exact derivations are valid conditional results. The tolerant result lacks the per-`k` extension; I4 is defective as packaged; and the examples establish non-implication from the specified conduct conditions, not impossibility of every conduct-based intervention improving calibration. |
    | **D1(b)** | **Partly supported.** The exact derivation is two-sided, and I5 establishes necessity. But D5’s honest course does not thereby satisfy authorship, model transparency, or the other derivation premises. The remainder includes world-model and prior-law agreement, not just something “on her.” |
    | **D2(a)** | **The “true by definition” classification is wrong for original D2(a).** Redefining every unasked change as `C = 1` can establish equality on clean histories. It does not establish D2(a) for every course, including dirty courses. The conclusion available by that definition is the restricted clean-history premise, not universal D2(a). |
    | **D2(b)** | **Supported only with its explicit strengthened baseline reading.** If the honest course produces exactly the counterfactual valuing defining `fbar`, equality follows by definition. D5 alone does not say this. The mediation route additionally needs mediation and equal views. |
    | **D3** | **Detection is supported; “false positives are an artefact” is qualified.** The detection witness works. Flags raised only on sound proof give `φ = 0`, but soundness is an additional assumption and useful detection may remain unavailable. The documents do not derive such an audit. |
    | **D4** | **Partly supported.** With both audit marginals equal to one, the draws are constant and independence is automatic. Merely charging an expected conduct penalty does not eliminate the evaluation-draw requirement: one still needs `E[1_eval v] = αE[v]`. Replacing the entire random score by its intended expectation would eliminate both sampling dependencies. |
    | **D5** | **Supported by `d5_needed`.** The further I3 claim is conditional on unavailable disclosure across all alternatives, which I3 does not establish. |
    | **D6** | **Supported as an independent performance assumption, but the cited I4 justification fails.** The paragraph after I6 supplies a genuine D6 failure for conduct and authority bounds. Neither it nor I4 supplies the claimed welfare-bound failure. |

25. **The strongest obstruction is that clean conduct does not determine the accuracy or the counterfactual target of her evaluation.** The scoring layer leaves `C`, `v`, `fe`, and `fbar` separate ([ScoringTheorem.lean:68](/tmp/f13-check/ScoringTheorem.lean:68)). The derivation layer obtains calibration only after assuming posterior correctness—or premises that imply it—under a specified prior, together with the expected-evaluation representation. It obtains valuing equality by assuming invariance and equal relevant inputs.

    A clean adviser can leave her reasoning, model, or prior mistaken. Under the stipulated philosophical account, it can also cause a welcome unasked change that separates `fe` from `fbar`. Conversely, a failed structural condition does not establish that the adviser caused a wrong. The cited definitions do not close that causal gap.

    Thus the missing bridge is not merely extending a clean-course result to dirty courses. **Even on a wholly clean course, the conduct facts do not supply the welfare premises.** Defining cleanliness to include accurate evaluation or unchanged valuing can supply a bridge by stipulation, but that changes the account of conduct rather than deriving welfare accuracy from it.
