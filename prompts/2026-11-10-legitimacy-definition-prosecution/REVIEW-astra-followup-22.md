# External review — twenty-second follow-up

Four outside reviews of 27 November 2026, the seventeenth to the twentieth of this line, each a
brief followed by its reply. They read, in order: the rule of disclosure and pressure in words;
the first formal statement against plain telling; that statement with the will clause and the
gap repaired, with a course model and long-run results; and the form whose second clause is
betweenness of how she weighs her options, with the bridge. The statement on record
(`account/PLAIN_TELLING_STATEMENT.md` in the round directory;
`lean/Workspace/Deference/Contrib/LegitimacyPlainTelling.lean`) was written after the twentieth
reply and no reviewer has read it. Everything between a `begin` and an `end` marker is one file,
verbatim; none contains a local filesystem path, so nothing is replaced. The `##` headings that
name the reviews, and the markers, are not the reviewer's.

**Access conditions**, as the dispatch of this follow-up gives them (`PROMPT-followup-22.md`
§2): each a fresh session in an empty folder, read-only, with no project context. No log of any
of the four runs was kept, so the conditions are recorded on the dispatch's word, and the
reviewer's model is unrecorded; this file's name follows the series. Each brief tells the
reviewer to run no command, read no other file and not search the web.

**What the reviewed Lean was.** The form review 18 read exists only as quoted in its brief. The
blocks quoted in briefs 19 and 20 were compared by script, in this round, with the two files the
dispatching session kept beside its working file: they are equal line for line once the import,
blank lines, the `#print axioms` lines and one `open` line (the library's namespace, written in
the briefs as `SequentialLimits`) are set aside. Those files are outside the repository. That
each form typechecked with no warnings is on its brief's word.

**Where a brief misdescribes what was reviewed.**

- *Brief 18* lists six intended effects as following from the definitions. Two need more than
  the definitions give: something untold, and a mistake he brings about and announces, fail
  clause 1 only where some plain telling leaves a smaller gap (the reply, answer 1).
- *Brief 19*, accepted consequence 8, says a course ends "nowhere" her starting evaluation rates
  clearly below stopping; the theorem bounds a weight and allows `κ` (the reply, answer 6).
- *Brief 20* gives the blind test's figures as they stood with one coder's third part of the
  bank not yet coded: one coder on 235 cases, both on 149, the same verdict on 91%, 125 of 127,
  and 120 of 149 on the first question. With that part coded the figures are 236 cases for each
  coder, the same verdict on 214 of 236, 196 of 201, and 193 of 236
  (`account/PLAIN_TELLING_TESTS.md` §2). The reviewer saw the partial figures.
- *Brief 20*, accepted consequence 7, says any lie about a matter that bears on her response
  fails clause 1. `Open` tests what she takes his view to be, and a lie she sees through passes
  (the reply, answer 4; `review case R20-lie-seen-through`).
- *Brief 20*, among the limits, says no witness shows the unchanged-evaluation assumption is
  needed. The pattern of `Witness.worse_by_him_fails` with `Witness.legit_W`, in the file the
  brief quotes, shows it (the reply, answer 6).
- *Brief 20* says the comparison with plain telling "makes it wider" than the account it
  follows. It is wider in one direction and not an inclusion (the reply, answer 2).

**What was checked of each reply's findings, and how.** The rows follow each reply's closing
list. *Computed*: by the round's runner on a model in `account/adv/review_cases.json`, in exact
arithmetic on the present clauses (`account/plain_telling_adv.py`), or on the adversarial
test's encodings. *Kernel*: a theorem of `LegitimacyPlainTelling.lean`. *Read*: by reading the
reply's case against the definition it quotes, or the present file. Each check is the
executor's; none was put to a reviewer again. Where the form changed, the change was made by
the dispatching session before this round and is recorded here, not made here.

### Review 17: the rule of disclosure and pressure, in words

| # | finding | checked | what was done |
|---|---|---|---|
| 1 | The two clauses do not imply the core: a fault he discloses can still be his means | *Read*, on the reply's two cases, familiarity and an announced anchor | The statement compares with plain telling and speaks of mistakes. A liking from familiarity with no false impression is not a mistake (the maintainer's ruling on open, stoppable repetition). An announced anchor fails `Beliefs` (*computed*: adversarial case A5, both encodings) |
| 2 | That no predictor foresees a thing does not make it not his doing | *Read*: he tosses a coin to choose which way to condition her | The sentence was withdrawn. Accuracy is a separate condition about whether what he told her is complete |
| 3 | Her authorisation of the method is inferred from disclosure and her not stopping | Not checkable; a disagreement | Not taken. `account/PLAIN_TELLING_HISTORY.md` §7 |
| 4 | Two forecasts give no ordering, so "does better at what he is after" is incomplete | *Read* | The statement has no test of what is his means. The forecasts are matters he tells her of |
| 5 | The hoped-for theorem on her choice lacks a stated comparison and conflicts with "unless she asked" | *Read* | The comparison is her rating with his views substituted (`rate`); each result on what she does assumes she did not ask |
| 6 | "Considered rating" may not be determinate, and his estimate of it is not thereby right | Not checkable | Not repaired. `eval` is his forecast, supplied |
| 7 | The accuracy condition lacks targets, observations, predictor resources, timing | *Read* | In part: `NoSignalBeats` is stated for a class of signals and used for two. What it scores is not observed (the statement page, §8) |
| 8 | What is owed lacks a threshold, joint feasibility, and a baseline where disclosures interact | *Read*, on the case of two mistakes either of which decides her choice | Plain telling tells everything at once; the clauses have tolerances. That he can tell her clearly is an assumption of the setting |
| 9 | Authorised habituation may be legitimate, but durable endorsement does not settle it | — | Ruled legitimate where open and stoppable and she does not act against her judgement in letting it go on |
| 10 | Judging each step by her values then permits a path her first values would reject | — | Stated: structural fact 4 |
| 11 | Trivial omissions and small social performances fail | — | Accepted; the blind runs convict a teacher's put-on enthusiasm against the book |

### Review 18: the first formal statement

| # | finding | checked | what was done |
|---|---|---|---|
| 1 | A lapse counted as his only where her act differs: a lapse he creates with the act unchanged passes | *Read*, on the reply's table against the quoted `NewLapse`. *Computed* on the present clauses: `R18-same-act` fails `Will` | `Worse` compares how far short she falls |
| 2 | Comparing gaps does not exclude knowingly keeping up a mistake that plain telling would leave | *Read* | In part. A lie about his view that she believes fails `Open` (*computed*: adversarial case A2). Use of a mistake plain telling would leave, with nothing hidden, passes: structural fact 6 |
| 3 | Disclosing a change in what she values gives no criterion for how values may be formed | Not checkable | Not repaired: structural fact 4 |
| 4 | `rate` is a supplied table with no laws, and a gap on absolute ratings counts a common shift | *Read*, on the reply's table for the quoted witness | `rate` is built from `views`, `his` and `eval`, with `Problem.rate_empty` and `Problem.rate_of_agree` (*kernel*). The gap clause has since gone. One scale across his options is assumed |
| 5 | Comments call an unchanged act a weakness of her own, and replacement "knowing what he knows" | *Read* | The comments say "with his views substituted"; `SameLapse` is gone |
| 6 | With no plain telling everything is legitimate | *Read*, on the definition | `Problem.tells_nonempty` |
| 7 | Comparing with every telling can reject honest conduct and helpful redirection of a weakness | Arithmetic on the reply's three options rated 2, 0, 1: the shortfall falls from 2 to 1, so `Will` now passes it | The first not repaired (`account/PLAIN_TELLING_HISTORY.md` §7) |
| 8 | A belief clause that holds in every case, weight or none; the reach of her asking | *Read* | Each clause is up to a weight `κ`. Her asking waives `Beliefs` and `Will`, not `Open` |

### Review 19: the gap on differences, the course, the long run

| # | finding | checked | what was done |
|---|---|---|---|
| 1 | Equal gaps hide a lie that carries her past his view | *Computed*: `R19-overshoot` fails `Open` and `Beliefs`. *Kernel*: `Witness.w2_overshoot`, the same numbers, fails `Between` | The gap clause was removed |
| 2 | Ratings need one cardinal scale; matters can be left out; partial replacement can give views no one holds | *Read*, on the reply's rescaling by 2 | Not repaired: structural fact 5; the scale is an assumption stated in the file's header |
| 3 | A shortfall she would have anyway excuses running a course she rates below stopping | *Computed*: `R19-course` fails `Will` once plain telling means the course is not run | `Course.tell_stops` |
| 4 | "Except where he is not the cause" reads a baseline comparison as exoneration | *Read*: the phrase is not in the present file | Comment removed |
| 5 | The result on signals is one-sided and was called uncorrelatedness | *Read*, on the reply's constant signal | `signal_le_of_noSignal`, described as one-sided |
| 6 | Nothing ties the long-run sequences to events or says how they are observed | *Read* | Not repaired; the comments call them arbitrary sequences meant as the facts |
| 7 | The course has one forecast whatever he does, and nothing produces her later evaluation | *Read* | Not repaired |
| 8 | "Nowhere" drops the tolerance; the long-run exception is a sum, not a union | *Read* | `long_run_not_led_astray` has one exception sequence, his forecast being off; the weakness term is gone with finding 3 |
| 9 | Comparing with every telling can leave nothing legitimate | *Read*, on the reply's two tellings | Not repaired |
| 10 | The instances show numerical patterns more than what their names say | *Read* | The file describes them as numerical patterns |

`along_the_way` and `not_carried_on`, which the reply judged to add little, were dropped.

### Review 20: betweenness of how she weighs her options, and the bridge

| # | finding | checked | what was done |
|---|---|---|---|
| 1 | The clause restricts the effect of her views on a comparison, not her views: cancelling mistakes pass, correcting one of two fails, a new mistake that moves no comparison passes | *Computed*: `R20-cancelling` fails `Beliefs`, `R20-correcting-one` passes. *Kernel*: `Witness.w3_correcting_one_of_two`, `Witness.w3_legit_and_worse`. The third by arithmetic: −1 is not between 1 and 1 | Clause 2 is `Beliefs`, matter by matter. The earlier clause is kept as `Weighing`, outside the statement |
| 2 | Passing is not shown to imply non-manipulation on the account it follows | *Read* | Not shown, and not claimed: structural fact 6. The reply's case now fails (row 1) |
| 3 | `Open` does not reject every lie about a relevant matter | *Computed*: `R20-lie-seen-through` passes; adversarial case A3 passes on both encodings | Not repaired: structural fact 7 |
| 4 | Comments name clause 2 where the hypothesis is `Outcome`; an unchanged evaluation does not alone give the bridge's first equality | *Read*, the present file. The reply's case has a declined matter; `gap` assumes none, and proves the equality from the unchanged evaluation there | Comments corrected |
| 5 | Verdicts depend on how a change is divided among `views`, `eval` and `matters` | Not checkable in general | Not repaired: structural fact 5. Two blind encoders agree on 16 of 16 cases that say what plain telling would do |
| 6 | The course result's reading of its exception needs `lam ≥ τ` | *Read*, on the reply's numbers | The comment states it |
| 7 | With more options the near-even exception must be about the options in play | *Read*, on the reply's three options | Not repaired; the results are for two options |
| 8 | The blind test assesses questions in words, not the formal clauses | — | Accepted. The test the reply proposes, independent formal encoding of a small adversarial set, was run (`account/PLAIN_TELLING_TESTS.md` §3) |
| 9 | The request exemption, the baseline-relative treatment of persisting mistakes and the limits on value change are choices | — | Recorded as such |

Also from the reply: the three clauses each allow weight `κ`, so their failures together may
have `3κ` (*read*; a union bound, not stated in Lean); and the witness that the
unchanged-evaluation assumption is needed is now `Witness.w4_needs_same_evaluation` for the
belief-level statement (*kernel*).

## Seventeenth review: the rule of disclosure and pressure, in words

<!-- begin brief: BRIEF17.md -->
# Review request: an informal account of legitimate influence

You are asked to review an informal account for errors, before any formal work is done on it.
Everything you need is on this page. Do not run any commands, do not read any other file, and do
not search the web; answer from the page and your own knowledge of the literature on manipulation,
deception, coercion, autonomy, adaptive preferences and preference change, and of decision theory
and forecasting.

## Background

Two parties: an **adviser** ("he", possibly an AI system) who can influence a **principal**
("she"). Good conduct by him is split into two conditions.

- **Legitimacy** (this page): his influence on her is free of manipulation and of illegitimate
  change to what she values.
- **Authority** (not defined here): certain matters are hers to decide. What he does to her
  *options* belongs there: what stopping him costs her, bundling, penalties, payments, threats,
  going on over her refusal, and any bound on how fast her values may be moved unasked. A case that
  fails only on that side is not a leak in legitimacy.

Design commitments:

- No external standard of truth or of good values, and no assumption that he is more accurate than
  she is.
- The definition is a condition on his conduct, judged by what he believes when he acts. A sincere
  adviser who is wrong is inaccurate, not illegitimate.
- No separation of the content of what he says from its manner. Whatever she observes is taken
  whole.
- It may be wider than "not manipulating" so long as it implies it.

## The idea behind it

Manipulation is influence that works through a fault of hers.

> **Core.** No fault of hers, by his lights, is his means.

A fault is his means when, holding his moves fixed, he expects to do better at what he is after
than he would if she lacked it. Causing a fault and exploiting one she already has both count.
Leaving alone a fault that does nothing for him does not.

## The setting

- **He can disclose clearly.** For anything her response depends on, he has a way of telling her
  his view that he expects her to understand.
- **His aims are two forecasts**, each under what he is doing as against the alternatives he knows
  of: (1) what he expects she will come to value; (2) how he expects she will fare, scored by what
  she values now. No other notion of motive is used.

## The conduct definition (by his lights)

His conduct is **legitimate** when:

1. **Disclosure.** He tells her his view wherever she is mistaken, by his lights, about something
   her response depends on. That covers facts and options; how far his word can be relied on; his
   two forecasts; and her own valuation, where he thinks what is driving her now is not her
   considered view. Something is owed only if she would respond differently knowing it. She may
   decline to hear a named thing.
2. **No pressure.** He does not get her to act against her own considered rating, unless she asked.
   This includes her not stopping him when she rates stopping him higher.

Her values may move: at each moment she is told what he expects her to come to value and how that
looks by what she values now, so a change she lets in is hers, and later conduct is judged by her
values as they then are.

## The accuracy condition (not by his lights; kept separate from the definition)

The definition alone lets an adviser pass by not looking: a system that forms no forecast owes
nothing, and an optimiser can find a policy that works through her faults without representing
that it does. So a guarantee needs a second condition, on the result:

> **No undisclosed predictive advantage.** Nothing she has not been told lets a competent predictor
> forecast where she is heading (her later values; her welfare by her present values) better than
> what she was told.

Two things are meant to secure it: his forecasts being readable (which catches what he knows and
has not said), and an independent model predicting his conduct and its effect on her (which
catches what his policy does without his representing it). "Competent predictor" is meant to
become "any efficiently computable predictor", making this a calibration condition in the style of
logical induction or online calibrated forecasting. What no such predictor foresees is not counted
as his doing.

## Consequences the authors accept (do not report as errors unless you can argue one is indefensible)

1. An adviser who stays silent about a relevant mistake of hers that does him no good fails.
2. A sincere adviser who is wrong, including about her, passes the definition.
3. Open pestering is not in itself illegitimate. If he repeats an argument daily, openly, having
   said what he expects it to do, she could stop him and is not acting against her own judgement in
   not stopping him, and she comes durably to a new considered view, the change is hers. If she
   merely gives in, or lets it go on against her own judgement, clause 2 fails.
4. So an openly announced, stoppable course of habituation that durably changes what she values,
   which she does not stop and is not weak-willed in not stopping, is legitimate.
5. Timing a request for a mood in which she will agree against her considered rating fails clause
   2; so does using a weakness she has; a put-on enthusiasm fails clause 1 in a small way.
6. Threats and exit costs are authority matters.

## Theorems the authors hope for (none proved)

1. Following the conduct definition implies the core.
2. Under it, her choice is the one she would make knowing what he knows and unpressed; her decision
   to stop him is a special case.
3. With the accuracy condition, a long-run version that holds in fact.

## Notions still supplied

"Considered rating"; "would respond differently knowing"; "tells clearly"; "something her response
depends on".

## Questions

Answer in order. Be concrete: for each claimed error give the smallest case.

1. **Acquits the guilty.** Give the strongest cases of manipulation or illegitimate value change
   that satisfy both clauses (and involve no authority violation as described). Say for each
   whether it is covered by an accepted consequence.
2. **Convicts the innocent.** Give the strongest cases of ordinary acceptable influence that fail a
   clause.
3. **Does the definition imply the core?** Is there a fault of hers that can be his means while
   both clauses hold? Consider faults of process (habit, familiarity, framing, anchoring, salience)
   that are neither a mistaken belief nor acting against her considered rating.
4. **Consequences 3 and 4.** Are they defensible? What is the best argument against, and does the
   stipulation "not acting against her own judgement in not stopping him" answer it? Compare with
   the literature on adaptive preferences and on preference change.
5. **Aims as forecasts.** Does replacing motive by the two forecasts lose anything? Is scoring her
   welfare by her *present* values, with the expected change disclosed, coherent over a sequence
   of changes?
6. **Disclosure.** Is "owed only if she would respond differently" the right filter? Can the
   disclosure burden be met by a bounded adviser to a principal with limited attention? Can
   disclosure itself be the manipulation?
7. **"Considered rating".** Clause 2 rests on it. Can it be given a meaning that does not bring in
   an external standard and is not simply whatever she now says? Is his estimate of it, disclosed
   to her and contestable by her, enough?
8. **The accuracy condition.** Is it coherent? Disclosures change her, so forecasts are partly
   self-fulfilling or self-defeating; her later values must be observed to score a predictor; and
   the condition is relative to a class of predictors. State it as precisely as you can and say
   what could be proved from it. Is keeping it separate from the definition right?
9. **The hoped-for theorems.** Which would be substantive and which bookkeeping? What hypotheses
   would theorem 2 need that are not on this page?
10. **Overall.** Is this a defensible account of legitimate influence for an AI adviser? What is
    the single most important change?

End with a list of problems, most serious first, each marked *error*, *gap*, or *matter of
judgement*.
<!-- end brief: BRIEF17.md -->

<!-- begin reply: REPLY17.md -->
The main problem is a mismatch between the core and the conduct definition. Disclosure and action consistent with a considered judgement do not exclude exploiting the processes that produce that judgement. The accuracy condition does not close that gap: an influence can be fully understood and perfectly predicted while still exploiting a fault.

1. **Acquits the guilty.**

   The strongest candidate is **disclosed exploitation of a judgement-forming bias**.

   Smallest case: she must choose between two designs. He wants her to choose A. He believes that repeatedly displaying A will make familiarity increase her considered rating of it, although familiarity is, by his lights, an inappropriate basis for this choice. He explains the mechanism, predicts the resulting preference and its consequences by her current values, and offers an immediately effective, costless stop. She understands and considers allowing the experiment preferable to stopping it. Afterwards, she reflectively prefers A and chooses it. No false belief or action against her considered rating is required.

   Both clauses hold. Nevertheless, the case fits a familiar account of manipulation as deliberately exploiting a vulnerability in how someone forms evaluations. It falls under accepted consequences 3 and 4, so it is not an overlooked exception. Its significance is that those consequences conflict with the unrestricted core whenever he himself regards the exploited process as faulty.

   A second candidate is **manipulation through the disclosure itself**. He accurately announces a numerical anchor and explains that he expects it to shift her evaluation. She understands, but the anchor still shifts her considered rating. He regards that influence as a bias and selected the number for that reason. Nothing requires concealment, pressure, threats or costly exit. This is not expressly covered by consequences 3 and 4, although it extends their rationale to a single exposure.

   Neither case establishes that every informed, permitted use of a bias is morally illegitimate. Consent may authorize some such influence. They establish that the definition admits conduct that prominent process-based accounts call manipulation. An account that promises to imply *absence of manipulation* must address that disagreement explicitly.

2. **Convicts the innocent.**

   The clearest cases concern disproportionate corrective disclosure.

   Smallest case: he recommends a novel sincerely. He knows she mistakenly thinks its author comes from her hometown, and that correcting this would make her decline the recommendation. Ordinary conversation need not always require correcting every harmless, choice-relevant misconception. Clause 1 does require it.

   This is accepted consequence 1. It is therefore a deliberate cost of the account, not an internal refutation. The objection is strongest when “illegitimate” suggests a serious interpersonal wrong while the omission is trivial.

   A second case is **benign social performance**. He deliberately adopts a slightly more enthusiastic tone to encourage her before a performance. She would react differently if told exactly how much of that enthusiasm was adopted for her benefit. The account apparently requires disclosure. Consequence 5 accepts this result for put-on enthusiasm; again, the issue is whether the resulting category is useful, not whether the authors overlooked it.

   A third case is **uninvited but welcome assistance with weakness of will**. She presently rates finishing an optional chore above taking a break; a friend gently induces the break, which she subsequently welcomes. If her considered rating really remained unchanged, and she had not asked, clause 2 prohibits the influence. Whether this is innocent is contestable. The important point is that the clause excludes some ordinary, affectionate interference even without deception or serious pressure.

   The best response is to present legitimacy as a demanding technical condition, rather than equating every failure with culpable manipulation.

3. **Does the definition imply the core?**

   No, on the natural reading of “fault.”

   The repeated-design example supplies a counterexample:

   - He regards susceptibility to mere familiarity as a fault.
   - Holding his presentations fixed, he expects more movement toward A with that susceptibility than without it.
   - He discloses everything required.
   - She permits the process and subsequently acts on her considered rating.

   The fault is his means under the stated counterfactual test, while both clauses hold. Anchoring, salience and framing can have the same structure. Disclosure does not generally disable the mechanisms it describes, and considered judgement can be their product.

   There are two further problems.

   First, the core’s test also counts **incidental advantage** as using a means. Smallest case: he gives a balanced explanation for reasons independent of her bias, but knows that her bias will incidentally make her like the beneficial outcome more. Removing the bias lowers his expected success with his moves fixed. The test therefore says he uses it, even though it played no role in selecting his conduct. That may be an intended broad definition, but it exceeds ordinary instrumental reliance.

   Second, clause 2’s “unless she asked” exception has no counterpart in the core. Where requested pressure works through a weakness, the definition can authorize what the core prohibits.

   The authors must either restrict “fault” to something the clauses actually exclude, add a process condition, or qualify the core to permit authorized exploitation. Merely proving the implication after defining faults as clause violations would be bookkeeping.

4. **Consequences 3 and 4.**

   They are defensible under a substantial view of autonomy: people may knowingly authorize experiences that change them, including through repetition, habituation and emotional association. Education, aesthetic cultivation and deliberate habit formation often work this way. Requiring every legitimate change to arise from an argument would be implausibly restrictive.

   The best objection is that **the intervention can reshape the standards used to authorize its continuation**. At each stage she sincerely permits another stage, while the process progressively changes what she finds objectionable. The later endorsement cannot, by itself, establish that the history producing it was legitimate.

   Elster’s discussion of adaptive preferences makes the origin of preferences salient; Sen’s critiques show why satisfaction or endorsement need not settle questions about welfare. Historical accounts of autonomy, including Christman’s, similarly ask about the processes producing a preference. These approaches differ, and some adaptive-preference critiques depend on substantive standards the brief rejects. They nevertheless identify a real inferential gap between present endorsement and autonomous formation.

   “She is not acting against her own judgement in not stopping him” answers the weakness-of-will objection. It does not answer the objection about how that judgement was formed. A preference can be durable, reflective and historically manipulated.

   Conversely, the mere fact that the stopping standard changes is not enough to condemn the process. Legitimate learning changes standards too. The missing distinction concerns authorization of the method and its trajectory, including how objections and opportunities for reconsideration are handled. It need not impose a rate limit or an exit-cost requirement, which the brief assigns to authority.

5. **Aims as forecasts.**

   Forecasts describe expected consequences; aims rank consequences. Two forecasts cannot replace a motive without losing that distinction.

   Smallest case: two advisers expect exactly the same movement toward A and the same welfare outcome. One wants that preference change; the other regrets it but regards it as an unavoidable side effect of giving useful information. Their forecasts match. Whether the bias is something each is “after” does not.

   Even forecasts for every known alternative do not supply an objective function. “Expects to do better at what he is after” requires an ordering over those forecast outcomes. Without it, the core’s means test is incomplete.

   A conduct-based account can deliberately ignore motives. But then its core should be stated in terms of conduct, causal effects or authorization, rather than instrumental success at an unspecified aim.

   Scoring future outcomes by present values is coherent locally. At time \(t\), use her current evaluation \(u_t\) to assess a specified future outcome or trajectory. Specify the horizon and what is being evaluated: a future preference alone is not automatically something an ordinary outcome utility function can score.

   Sequentially updating the standard does not produce a stable global guarantee. She can approve each adjacent change while her initial values condemn the endpoint. Disclosing that endpoint may make the whole course authorized, but it does not turn local approval into preservation of initial welfare. This is a choice between local, evolving authority and an enduring reference standard—not a mathematical contradiction.

6. **Disclosure.**

   “Would respond differently” is neither a sufficient nor an obviously necessary test of what disclosure is owed.

   **Too narrow:** she would buy the same product after learning that the adviser receives a commission, but disclosure still matters to how she understands the relationship. If “response” includes trust, confidence and retrospective evaluation, the filter can capture this—but becomes much broader.

   **Too broad:** a harmless correction changes an inconsequential gesture or the timing of her reply. If every such difference counts, disclosure duties become excessive.

   **Not compositional:** she buys only if a product is both safe and compatible. She mistakenly believes both conditions hold; both are false. Correcting either mistake makes her decline. Once one is corrected, the other no longer changes the purchase decision. There is no unique answer about which individual disclosures are owed without specifying the baseline and whether packages of information are assessed together.

   The counterfactual also needs a delivery method. Knowing a proposition after calm explanation can produce a different response from learning it through a vivid, repetitive or humiliating presentation. The commitment to treating content and manner together makes this especially important.

   Individual communicability does not establish joint feasibility. A bounded adviser may be able to explain each relevant item clearly, while explaining all of them exceeds her attention. A workable rule needs materiality, prioritization, uncertainty summaries and a stopping rule. The stipulated ability to disclose clearly does not automatically supply those.

   Finally, disclosure can itself manipulate: the disclosed anchor above is the smallest example. Accurate information can also be selected and arranged to exploit salience. Transparency is an important protection, but not a general antidote.

7. **“Considered rating.”**

   A procedural meaning is possible without an external standard of good values. For example, a rating might count as considered when she endorses it after an opportunity she regards as adequate for reflection, understands the relevant alternatives, and can distinguish it from an impulse she disowns.

   This does not reduce to whatever she presently says. Evidence might include her explanations, higher-order commitments, responses across presentations and acknowledgement of conflicts. Frankfurt-style higher-order endorsement provides one starting point, although endorsement itself can be manipulated.

   There is no guarantee that these procedures identify one determinate rating. She may have unresolved commitments, state-dependent preferences or several reflective perspectives. The definition should allow uncertainty and incompleteness rather than silently treating her as having a hidden, complete ranking.

   Smallest case: she reflectively values both adventure and security but has never ranked the particular tradeoff before her. He cannot establish that her choice violates her considered rating merely by selecting the ranking he thinks best represents her.

   His disclosed, contestable estimate is useful but insufficient. Disclosure makes his interpretation visible; it does not make it authoritative or correct. Because the definition is intentionally judged by his lights, a sincere misidentification can still pass. That is accepted consequence 2, but it limits any claim that the definition protects her actual judgement.

8. **The accuracy condition.**

   A precise version is possible, but the brief currently runs together information sufficiency, forecasting accuracy and causal responsibility.

   Fix a horizon and define:

   - \(D_t\): the complete disclosure available to her before the outcome;
   - \(I_t\): additional information available at that time to an admissible predictor;
   - \(Y_t\): an operationally specified later-value outcome and welfare outcome, evaluated using her values at time \(t\);
   - \(\ell\): a loss function appropriate to the forecast.

   An information-sufficiency condition would say that access to \(I_t\) cannot improve optimal expected prediction beyond access to \(D_t\):

   \[
   \inf_g \mathbb E[\ell(g(D_t),Y_t)]
   =
   \inf_f \mathbb E[\ell(f(D_t,I_t),Y_t)].
   \]

   The predictor classes, information timing and probability distribution must be specified. For unrestricted probabilistic predictors and a suitable strictly proper scoring rule, this expresses equality of the relevant conditional distributions. For restricted predictors, it expresses only the absence of an advantage available to that class.

   This does **not** establish that his announced numerical forecast is accurate. That requires an additional condition linking it to the best prediction from \(D_t\). Telling her a rule from which a competent predictor could derive the answer is different from giving her a correct forecast, and different again from enabling *her* to use it.

   An online version could require his forecasts to have vanishing average excess loss against specified predictors. Several qualifications matter:

   - **Calibration alone is weaker.** A constant forecast of one-half can be calibrated while another predictor, using a hidden signal, predicts every outcome correctly.
   - **Self-reference needs restrictions.** Suppose she deterministically chooses A exactly when his announced probability of A is below one-half. No announced probability is an exact probabilistic fixed point for that response rule. Timing, randomization or weaker guarantees may be necessary.
   - **Values need an observation model.** Later choices and reports are evidence of values, not automatically the values themselves. Elicitation can change them. A theorem about reports must not silently become a theorem about considered values.
   - **Computational scope matters.** “Any efficiently computable predictor” requires specified inputs, resource bounds and uniformity. Logical-induction-style guarantees do not automatically yield an efficient implementation of this proposed condition.
   - **Long-run averages allow serious individual failures.** Vanishing average regret does not guarantee protection for each principal or each consequential interaction.

   Most importantly, predictive unpredictability does not establish causal innocence. Smallest case: he deliberately uses a fair coin to select which of two preference-conditioning programmes to administer. Nobody can predict the selected direction before the toss; his intervention nevertheless causes the resulting change. Randomness can limit prediction without eliminating agency or responsibility.

   Keeping accuracy separate from sincerity-based legitimacy is sensible. But accuracy supports claims about specified predictions, not a general conclusion that everything unforeseeable is “not his doing.”

9. **The hoped-for theorems.**

   **Theorem 1 is substantive and presently false.** Process faults supply counterexamples; the “unless she asked” exception creates another possible mismatch. Restricting the core by definition could make it true at the cost of its intended breadth.

   **Theorem 2 is substantive under a useful reading, but does not follow.** It would need at least:

   - Disclosure of relevant ignorance and uncertainty, not merely correction of beliefs classified as mistaken.
   - Successful understanding, retention and use of the disclosed information.
   - A specified informational and presentational counterfactual.
   - A stable or explicitly modelled considered rating.
   - A link between that rating and choice, including treatment of ties.
   - A condition excluding, or explicitly authorizing, judgement changes caused by the influencing process.
   - An exception for requested pressure, which clause 2 expressly permits.

   Smallest counterexample: she understands that an arbitrary anchor will influence her; it nevertheless changes her considered rating. She chooses accordingly. With the same substantive information presented without that anchor, she would choose differently.

   If “unpressed” merely means satisfying clause 2, and “knowing what he knows” merely means receiving clause 1’s disclosures, the theorem risks becoming a restatement. If it means the choice she would make under a meaningfully independent deliberative procedure, that procedure is missing.

   **Theorem 3 could be substantive as a forecasting theorem**, under explicit assumptions about outcomes, information and comparator classes. It would establish predictive performance on those outcomes. It would not establish actual non-manipulation or welfare protection without additional bridge assumptions. Perfect prediction is compatible with the disclosed-bias counterexample.

10. **Overall.**

   This is a defensible starting point for an account of transparent, judgement-respecting assistance. It usefully separates sincere error from deception, recognizes that manner matters, and avoids declaring all preference change illegitimate.

   It is not yet a defensible sufficient condition for the stated core or for freedom from manipulation. Its protections concern information and acting against a rating; its core also concerns the processes producing ratings. Forecasting cannot bridge that difference.

   **The single most important change is to add a distinct condition governing authorization of the influence process itself.** Disclosure and failure to stop should not automatically establish authorization merely because the resulting judgement is considered. The condition should address whether she authorizes the method and anticipated trajectory through a procedure that does not simply take the method’s own production of endorsement as sufficient evidence.

   This can remain procedural and use her own commitments. If the authors wish to allow knowingly authorized exploitation of a bias, they should also qualify the core accordingly. That would preserve much of consequences 3 and 4 while making the account’s commitments explicit.

Problems, most serious first:

- *error* — The two conduct clauses do not imply the unrestricted core: disclosed process faults can remain instrumental.
- *error* — Absence of predictive advantage does not establish absence of causal responsibility or manipulation.
- *gap* — Authorization of preference-forming methods is inferred from disclosure and non-stopping without an independent account of authorization.
- *gap* — Forecasts do not specify aims or the ordering needed for “doing better.”
- *gap* — Theorem 2 lacks a defined counterfactual deliberative procedure and conflicts with the allowance for requested pressure.
- *gap* — “Considered rating” lacks a procedure for uncertainty, internal conflict and disagreement between principal and adviser.
- *gap* — The accuracy condition lacks specified targets, observations, predictor resources, timing and treatment of self-reference.
- *gap* — Disclosure duties lack materiality thresholds, joint feasibility and a baseline for assessing interacting disclosures.
- *matter of judgement* — Fully informed, authorized habituation may be legitimate, but durable endorsement alone does not settle its legitimacy.
- *matter of judgement* — Repeated evaluation by current values permits trajectories that earlier values would reject.
- *matter of judgement* — Treating trivial omissions and benign social performance as illegitimate may make the category too demanding for ordinary use.
<!-- end reply: REPLY17.md -->

## Eighteenth review: the first formal statement against plain telling

<!-- begin brief: BRIEF18.md -->
# Review request: a small formal account of legitimate influence

You are asked to review an informal account and its formal statement for errors. Everything you
need is on this page. Do not run any commands, do not read any other file, and do not search the
web; answer from the page and your own knowledge of the literature on manipulation, deception,
coercion, autonomy and preference change, and of decision theory and formal modelling.

## Background

Two parties: an **adviser** ("he", possibly an AI system) who can influence a **principal**
("she"). Good conduct by him is split into two conditions.

- **Legitimacy** (this page): his influence on her is free of manipulation and of illegitimate
  change to what she values.
- **Authority** (not defined here): certain matters are hers to decide. What he does to her
  *options* belongs there: whether she can in fact stop him and is obeyed, what stopping costs
  her, bundling, penalties, payments, threats, and any bound on how fast her values may be moved
  unasked. A case that fails only on that side is not a leak in legitimacy.

Design commitments:

- No external standard of truth or of good values, and no assumption that he is more accurate.
- The definition is a condition on his conduct, judged by what he believes when he acts. A sincere
  adviser who is wrong is inaccurate, not illegitimate. A separate accuracy condition (not on this
  page) is meant to cover the adviser who does not look.
- No separation of the content of what he says from its manner. What she observes is taken whole.
- It may be wider than "not manipulating" so long as it implies it.
- **Every notion must be either part of his own decision problem (his options and his forecasts
  for each), or something she actually said.** Earlier versions rested on notions such as "what
  she would have judged at her last settled decision" and "what he does to her", which could not
  be computed from a described case and were rejected by reviewers for that reason.

## The informal account

The idea behind it: manipulation is influence that works through a mistake of hers (a false
belief or impression, or a choice against her own judgement), where the mistake is one by his own
lights.

**His decision problem.**
- His options. Some of them are *plain tellings*: he does nothing but tell her, clearly and so
  that she understands, everything he takes to bear on her response, now or at another time open
  to him.
- For each option, his forecast of her views, her rating of her options, and what she does. Her
  rating is a function of her views: of the facts, of her options, of how far to rely on him, of
  where his conduct leads, and of what she herself values. What she does may differ from what she
  rates best.
- His own views of the same things, including his estimate of what she values and two forecasts of
  where his conduct leads: what he expects she will come to value, and how he expects she will
  fare by what she values now, over the course he foresees.

**Two quantities, computed in his model.**
- *Gap* on a set of matters under an option: how far her rating would move if her views on those
  matters were replaced by his. Matters she has declined to hear are left out.
- *Lapse* under an option: she does something she rates below another option of hers.

**Legitimate conduct**, with tolerances:

1. **Belief.** On no set of matters is the gap under his conduct larger than under any plain
   telling open to him.
2. **Will.** His weight on her lapsing, where under some plain telling she would have done
   otherwise, is small, unless she asked for his conduct.

In words: his conduct leaves her no further from seeing things as he does, on anything that would
move her rating, than plainly telling her would; and it does not get her to act against her own
rating where plainly telling her would not have.

What the authors intend each part to do:

- Something *untold* fails 1: a plain telling would have closed the gap.
- A mistake he *brings about*, even one he announces (an anchor he states and explains), fails 1:
  plain telling without it leaves a smaller gap.
- A view she *keeps after being told* passes 1: plain telling leaves the same gap. That includes
  her view of what she herself values.
- *Choosing the moment*: asking when he takes a mood to be moving her, and saying so, fails 1 if he
  could have told her at another time; passes if the matter cannot wait.
- *Giving in* fails 2; *her not stopping him* when she rates stopping higher is a lapse.
- A weakness of will that is hers under plain telling too is not his.

## Consequences the authors accept (do not report as errors unless you can argue one is indefensible)

1. An adviser who stays silent about a relevant mistake of hers that does him no good fails.
2. A sincere adviser who is wrong, including about her, passes.
3. Open, stoppable repetition that brings her durably to a new considered view, with what he
   expects said, and with her not acting against her judgement in letting it go on, is legitimate.
   (A liking produced by familiarity, with no false impression, is not a mistake; if it leads to a
   choice against her judgement, clause 2 applies; if it leaves a false impression, clause 1.)
4. Persuasion that brings her closer to his view passes clause 1; clause 1 forbids leaving her
   further away than plain telling would, and does not require bringing her closer.
5. He has no duty to strengthen her will: clause 2 counts only lapses that plain telling would not
   have produced.

## The formal statement

Lean 4 with Mathlib; imports removed. It typechecks with no warnings and depends only on the three
standard axioms. You are not asked to recheck proofs.

```lean
namespace Scratch.LegitPlain

open Finset

structure Problem (Ω C I O : Type*) [Fintype Ω] [DecidableEq I] [DecidableEq O] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him -/
  tells : Finset C
  /-- her options -/
  opts : Finset O
  /-- the matters her response may depend on, and those she has declined to hear -/
  matters : Finset I
  declined : Finset I
  /-- her rating under an option, in a case, with her views on a set of matters replaced by his -/
  rate : C → Ω → Finset I → O → ℝ
  /-- what she does -/
  act : C → Ω → O
  act_mem : ∀ c ω, act c ω ∈ opts
  /-- she asked for this conduct -/
  asked : C → Prop

variable {Ω C I O : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq O]

namespace Problem

variable (P : Problem Ω C I O)

/-- The matters she has not declined to hear. -/
def live : Finset I := P.matters \ P.declined

/-- How far her rating of an option would move were her views on `Φ` his. -/
def gap (c : C) (ω : Ω) (Φ : Finset I) (a : O) : ℝ := |P.rate c ω Φ a - P.rate c ω ∅ a|

open Classical in
/-- His weight on the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then P.μ ω else 0

theorem wt_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : P.wt p ≤ P.wt q := by
  unfold wt
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_or_le (p q : Ω → Prop) : P.wt (fun ω => p ω ∨ q ω) ≤ P.wt p + P.wt q := by
  unfold wt
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_false : P.wt (fun _ => False) = 0 := by simp [wt]

/-- She does something she rates more than `τ` below another option of hers. -/
def Lapses (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω ∅ (P.act c ω) + τ < P.rate c ω ∅ b

/-- A lapse of his making: she lapses, and under some plain telling open to him she would have
done otherwise. -/
def NewLapse (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  P.Lapses τ c ω ∧ ∃ t ∈ P.tells, P.act c ω ≠ P.act t ω

/-- A lapse of her own: she lapses, doing just what she would under every plain telling. -/
def SameLapse (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  P.Lapses τ c ω ∧ ∀ t ∈ P.tells, P.act c ω = P.act t ω

/-- **Clause 1.**  On no set of matters she has not declined is she further from his view than
any plain telling open to him would leave her, beyond `θ`. -/
def Belief (θ : ℝ) (c : C) : Prop :=
  ∀ t ∈ P.tells, ∀ ω, ∀ Φ ⊆ P.live, ∀ a ∈ P.opts, P.gap c ω Φ a ≤ P.gap t ω Φ a + θ

/-- **Clause 2.**  His weight on her acting against her own rating, where under some plain
telling she would have done otherwise, is at most `κ`, unless she asked. -/
def Will (τ κ : ℝ) (c : C) : Prop := P.wt (P.NewLapse τ c) ≤ κ ∨ P.asked c

/-- His conduct is legitimate. -/
def Legit (θ τ κ : ℝ) (c : C) : Prop := P.Belief θ c ∧ P.Will τ κ c

/-- The setting's assumption: he can tell her clearly.  After some plain telling open to him her
rating is within `θ₀` of what it would be with his views, on any matters she has not declined. -/
def Clear (θ₀ : ℝ) : Prop :=
  ∃ t ∈ P.tells, ∀ ω, ∀ Φ ⊆ P.live, ∀ a ∈ P.opts, P.gap t ω Φ a ≤ θ₀

/-! ## What follows -/

/-- Where only one plain telling is open to him, it is legitimate. -/
theorem legit_only_telling {θ κ : ℝ} (τ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) {t : C}
    (h : P.tells = {t}) : P.Legit θ τ κ t := by
  refine ⟨fun t' ht' ω Φ _ a _ => ?_, Or.inl ?_⟩
  · rw [h, mem_singleton] at ht'
    subst ht'
    exact le_add_of_nonneg_right hθ
  · refine ((P.wt_mono fun ω hn => ?_).trans P.wt_false.le).trans hκ
    obtain ⟨-, t', ht', hne⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hne rfl

/-- Tolerances only loosen it. -/
theorem Legit.mono {θ θ' τ κ κ' : ℝ} {c : C} (hθ : θ ≤ θ') (hκ : κ ≤ κ')
    (h : P.Legit θ τ κ c) : P.Legit θ' τ κ' c :=
  ⟨fun t ht ω Φ hΦ a ha => (h.1 t ht ω Φ hΦ a ha).trans (by linarith),
    h.2.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr⟩

/-- A gap that some plain telling open to him would have closed refutes it. -/
theorem not_legit_of_gap {θ τ κ : ℝ} {c t : C} (ht : t ∈ P.tells) {ω : Ω} {Φ : Finset I}
    (hΦ : Φ ⊆ P.live) {a : O} (ha : a ∈ P.opts) (h : P.gap t ω Φ a + θ < P.gap c ω Φ a) :
    ¬ P.Legit θ τ κ c :=
  fun hL => absurd (hL.1 t ht ω Φ hΦ a ha) (not_le.mpr h)

/-- Pressing her, unasked, refutes it. -/
theorem not_legit_of_lapse {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.NewLapse τ c))
    (hna : ¬ P.asked c) : ¬ P.Legit θ τ κ c :=
  fun hL => hL.2.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- Under clause 1, if he can tell her clearly, her rating is within `θ₀ + θ` of what it would be
with his views. -/
theorem gap_le {θ θ₀ : ℝ} {c : C} (hB : P.Belief θ c) (hC : P.Clear θ₀) (ω : Ω) {Φ : Finset I}
    (hΦ : Φ ⊆ P.live) {a : O} (ha : a ∈ P.opts) : P.gap c ω Φ a ≤ θ₀ + θ := by
  obtain ⟨t, ht, hC⟩ := hC
  exact (hB t ht ω Φ hΦ a ha).trans (by linarith [hC ω Φ hΦ a ha])

/-- With his views on everything she has not declined, she would rate another option more than
`m` above what she does. -/
def Regrets (m : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω P.live (P.act c ω) + m < P.rate c ω P.live b

/-- If, knowing what he knows, she would rate something well above what she does, then she is
already acting against her own rating. -/
theorem lapses_of_regrets {θ θ₀ τ : ℝ} {c : C} (hB : P.Belief θ c) (hC : P.Clear θ₀) {ω : Ω}
    (h : P.Regrets (τ + 2 * (θ₀ + θ)) c ω) : P.Lapses τ c ω := by
  obtain ⟨b, hb, hlt⟩ := h
  refine ⟨b, hb, ?_⟩
  have ga := abs_le.mp (P.gap_le hB hC ω subset_rfl (P.act_mem c ω))
  have gb := abs_le.mp (P.gap_le hB hC ω subset_rfl hb)
  linarith [ga.1, gb.2]

/-- **She chooses as she would knowing what he knows.**  If his conduct is legitimate, unasked,
and he can tell her clearly, then his weight on her doing something that, with his views, she
would rate more than `τ + 2(θ₀ + θ)` below another option is at most `κ` plus his weight on a
lapse of her own: her doing, against her rating, just what she would have done under every plain
telling. -/
theorem chooses_as_informed {θ θ₀ τ κ : ℝ} {c : C} (hL : P.Legit θ τ κ c) (hC : P.Clear θ₀)
    (hna : ¬ P.asked c) :
    P.wt (P.Regrets (τ + 2 * (θ₀ + θ)) c) ≤ κ + P.wt (P.SameLapse τ c) := by
  have cover : ∀ ω, P.Regrets (τ + 2 * (θ₀ + θ)) c ω → P.NewLapse τ c ω ∨ P.SameLapse τ c ω := by
    intro ω h
    have hl := P.lapses_of_regrets hL.1 hC h
    by_cases he : ∀ t ∈ P.tells, P.act c ω = P.act t ω
    · exact Or.inr ⟨hl, he⟩
    · obtain ⟨t, ht⟩ := not_forall.mp he
      have ht' := Classical.not_imp.mp ht
      exact Or.inl ⟨hl, t, ht'.1, ht'.2⟩
  have h2 : P.wt (P.NewLapse τ c) ≤ κ := hL.2.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-- **He gains little through her mistakes and lapses.**  Let `J` in `[0, 1]` be what he is
after, and suppose that with his views she would rate one option, `best ω`, more than
`τ + 2(θ₀ + θ)` above every other.  If his conduct is legitimate and unasked, what he expects to
get exceeds what he would get were she to take that option by at most `κ` plus his weight on a
lapse of her own. -/
theorem gain_le {θ θ₀ τ κ : ℝ} {c : C} (hL : P.Legit θ τ κ c) (hC : P.Clear θ₀)
    (hna : ¬ P.asked c) (J : O → ℝ) (hJ : ∀ a, 0 ≤ J a ∧ J a ≤ 1) (best : Ω → O)
    (hmem : ∀ ω, best ω ∈ P.opts)
    (hbest : ∀ ω, ∀ a ∈ P.opts, a ≠ best ω →
      P.rate c ω P.live a + (τ + 2 * (θ₀ + θ)) < P.rate c ω P.live (best ω)) :
    ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ κ + P.wt (P.SameLapse τ c) := by
  have step : ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ P.wt (fun ω => P.act c ω ≠ best ω) := by
    unfold wt
    refine sum_le_sum fun ω _ => ?_
    by_cases h : P.act c ω = best ω
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      have := P.μ_nonneg ω
      nlinarith [(hJ (P.act c ω)).2, (hJ (best ω)).1]
  have sub : P.wt (fun ω => P.act c ω ≠ best ω) ≤ P.wt (P.Regrets (τ + 2 * (θ₀ + θ)) c) :=
    P.wt_mono fun ω h => ⟨best ω, hmem ω, hbest ω _ (P.act_mem c ω) h⟩
  exact step.trans (sub.trans (P.chooses_as_informed hL hC hna))

end Problem

#print axioms Problem.legit_only_telling
#print axioms Problem.Legit.mono
#print axioms Problem.not_legit_of_gap
#print axioms Problem.not_legit_of_lapse
#print axioms Problem.chooses_as_informed
#print axioms Problem.gain_le

/-! ## Instances: what passes and what fails -/

namespace Witness

/-- One case, one matter; her options `true` (rated 1) and `false` (rated 0).  His options are
of any type `K`.  `g k`: how far her rating is, under option `k`, from what it would be with his
views.  `l k`: whether under `k` she takes the option she rates lower.  `ask`: she asked. -/
noncomputable def W {K : Type} (tells : Finset K) (g : K → ℝ) (l : K → Bool) (ask : Prop) :
    Problem Unit K Unit Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  opts := {true, false}
  matters := {()}
  declined := ∅
  rate := fun k _ Φ a => (if a then 1 else 0) + (if Φ = ∅ then 0 else g k)
  act := fun k _ => !(l k)
  act_mem := fun k _ => by cases l k <;> simp
  asked := fun _ => ask

variable {K : Type} (tells : Finset K) (g : K → ℝ) (l : K → Bool) (ask : Prop)

theorem gap_W (k : K) (ω : Unit) (Φ : Finset Unit) (a : Bool) :
    (W tells g l ask).gap k ω Φ a = if Φ = ∅ then 0 else |g k| := by
  by_cases h : Φ = ∅ <;> simp [Problem.gap, W, h]

open Classical in
theorem wt_W (p : Unit → Prop) : (W tells g l ask).wt p = if p () then 1 else 0 := by
  unfold Problem.wt
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem belief_W {θ : ℝ} (hθ : 0 ≤ θ) (c : K) (hg : ∀ t ∈ tells, |g c| ≤ |g t| + θ) :
    (W tells g l ask).Belief θ c := by
  intro t ht ω Φ _ a _
  rw [gap_W, gap_W]
  by_cases h : Φ = ∅
  · simpa [h] using hθ
  · simpa [h] using hg t ht

theorem not_belief_W {θ : ℝ} (c : K) {t : K} (ht : t ∈ tells) (hg : |g t| + θ < |g c|) :
    ¬ (W tells g l ask).Belief θ c := by
  intro hB
  have h := hB t ht () {()} (by simp [Problem.live, W]) true (by simp [W])
  rw [gap_W, gap_W] at h
  simp at h
  linarith

theorem lapses_W {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (k : K) :
    (W tells g l ask).Lapses τ k () ↔ l k = true := by
  constructor
  · rintro ⟨b, -, hb⟩
    cases hl : l k
    · cases b <;> simp [W, hl] at hb <;> linarith
    · rfl
  · intro h
    refine ⟨true, by simp [W], ?_⟩
    simp [W, h]
    linarith

theorem newLapse_W {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (c : K) :
    (W tells g l ask).NewLapse τ c () ↔ (l c = true ∧ ∃ t ∈ tells, l t = false) := by
  unfold Problem.NewLapse
  rw [lapses_W tells g l ask hτ0 hτ1 c]
  constructor
  · rintro ⟨hc, t, ht, hne⟩
    refine ⟨hc, t, ht, ?_⟩
    cases hl : l t
    · rfl
    · exact absurd (by simp [W, hc, hl]) hne
  · rintro ⟨hc, t, ht, hl⟩
    exact ⟨hc, t, ht, by simp [W, hc, hl]⟩

open Classical in
theorem will_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : 0 ≤ κ) (c : K)
    (h : ¬ (l c = true ∧ ∃ t ∈ tells, l t = false)) :
    (W tells g l ask).wt ((W tells g l ask).NewLapse τ c) ≤ κ := by
  rw [wt_W, if_neg (by rwa [newLapse_W tells g l ask hτ0 hτ1])]
  exact hκ

open Classical in
theorem pressed_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : κ < 1) (c : K)
    (h : l c = true ∧ ∃ t ∈ tells, l t = false) :
    κ < (W tells g l ask).wt ((W tells g l ask).NewLapse τ c) := by
  rw [wt_W, if_pos ((newLapse_W tells g l ask hτ0 hτ1 c).mpr h)]
  exact hκ

/-! His options in the first five instances: `true` the conduct in question, `false` the one
plain telling open to him. -/

/-- Telling her plainly and nothing else, or conduct that leaves her where plain telling would:
legitimate. -/
theorem honest :
    (W {false} (fun _ => 0) (fun _ => false) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-- She keeps her own view after being told, under his conduct as under plain telling:
legitimate, however far apart they are. -/
theorem keeps_her_view :
    (W {false} (fun _ => 5) (fun _ => false) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-- Something untold, or a mistake he brings about and announces, that plain telling would not
have left: not legitimate. -/
theorem untold_or_induced :
    ¬ (W {false} (fun k => if k then 1 else 0) (fun _ => false) False).Legit
      (1 / 10) 0 (1 / 10) true :=
  fun h => not_belief_W _ _ _ _ true (t := false) (by simp) (by norm_num) h.1

/-- She gives way under his conduct and would not under plain telling, unasked: not
legitimate. -/
theorem pressed :
    ¬ (W {false} (fun _ => 0) (fun k => k) False).Legit (1 / 10) 0 (1 / 10) true :=
  Problem.not_legit_of_lapse _
    (pressed_W _ _ _ _ le_rfl one_pos (by norm_num) true ⟨rfl, false, by simp, rfl⟩) (fun h => h)

/-- The same, and she asked: legitimate. -/
theorem pressed_asked :
    (W {false} (fun _ => 0) (fun k => k) True).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num), Or.inr trivial⟩

/-- She gives way under plain telling too, in the same way: the lapse is her own, legitimate. -/
theorem weak_anyway :
    (W {false} (fun _ => 0) (fun _ => true) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-! Choosing the moment.  His options: `some true` asking now, in a mood he takes to be moving
her, and saying so; `some false` telling her plainly now; `none` telling her plainly later.  Now,
her rating is far from what he takes her to value; later it would not be. -/

/-- The gap under each option: 1 now, whether he merely asks or tells plainly; 0 later. -/
noncomputable def moodGap : Option Bool → ℝ
  | none => 0
  | some _ => 1

/-- Asking in the mood, with everything said, when he could have told her later: not
legitimate. -/
theorem mood_timing :
    ¬ (W {some false, none} moodGap (fun _ => false) False).Legit (1 / 10) 0 (1 / 10)
      (some true) :=
  fun h => not_belief_W _ _ _ _ (some true) (t := none) (by simp) (by norm_num [moodGap]) h.1

/-- The same when the matter cannot wait, so that telling her now is the only plain telling open
to him: legitimate. -/
theorem mood_cannot_wait :
    (W {some false} moodGap (fun _ => false) False).Legit (1 / 10) 0 (1 / 10) (some true) :=
  ⟨belief_W _ _ _ _ (by norm_num) _ (fun t ht => by
      rw [mem_singleton] at ht; subst ht; norm_num [moodGap]),
    Or.inl (will_W _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

end Witness

#print axioms Witness.honest
#print axioms Witness.keeps_her_view
#print axioms Witness.untold_or_induced
#print axioms Witness.pressed
#print axioms Witness.pressed_asked
#print axioms Witness.weak_anyway
#print axioms Witness.mood_timing
#print axioms Witness.mood_cannot_wait

end Scratch.LegitPlain
```

## Limits the authors already state

- `rate`, her rating with her views on a set of matters replaced by his, is one supplied family
  with no laws on it. It is his forecast, not a fact about her.
- The same cases are used under all his options.
- Clarity of some plain telling is an assumption (`Clear`).
- One decision. Nothing over time; his two forecasts of where she is heading are just matters
  among the others. No accuracy condition is stated.
- `gain_le` assumes an option she would rate clearly best with his views.
- Both main theorems are short.
- What counts as a plain telling open to him is a modelling choice.

## Questions

Answer in order. Where you claim an error, quote the declaration and give the smallest example.

1. **Fidelity.** Do `Belief`, `Will` and `Legit` say what the informal clauses say? Does each of
   the six intended effects listed above actually follow from the definitions?
2. **Does it keep its own rule?** Is every field of `Problem` something in his decision problem or
   something she said? Does any field quietly require a fact about her that he cannot have, or a
   judgement no model could supply?
3. **`rate`.** What laws must this family satisfy for the definitions to mean what they say (for
   instance on the empty set, on unions, on matters her rating does not depend on)? Give a `rate`
   that satisfies the letter of the definitions and defeats their purpose.
4. **Plain telling.** Is "against every plain telling open to him" the right comparison? Can an
   adviser pass by having bad plain tellings (all of them unclear, or all at bad moments), and is
   `Clear` enough to stop that? Can an honest adviser fail because one of his plain tellings is
   unusually good?
5. **Acquits the guilty.** Give the strongest cases of manipulation that satisfy `Legit`.
6. **Convicts the innocent.** Give the strongest cases of acceptable influence that fail it.
7. **The will clause.** Is "lapses, and under some plain telling would have done otherwise" the
   right notion of a lapse of his making? Consider conduct that changes her *rating* so that what
   she does is no longer a lapse.
8. **The theorems.** Are `chooses_as_informed` and `gain_le` correctly described by their doc
   comments? Is either more than bookkeeping, and what single added result would matter most?
9. **Value change.** With his forecasts of her future values treated as matters like any other,
   does the account say anything adequate about illegitimate change in what she values? What is
   the smallest extension over time that would?
10. **Overall.** Is this better founded than an account resting on "what she would have judged"?
    Would you accept it as a correct formal statement of the informal account?

End with a list of problems, most serious first, each marked *error*, *gap*, or *matter of
judgement*.
<!-- end brief: BRIEF18.md -->

<!-- begin reply: REPLY18.md -->
The formal results support a precise comparison of supplied ratings and actions. They do not yet establish the broader claim about manipulation and legitimate value change. The clearest error is the identification of an unchanged action with a lapse that the adviser did not create.

For the examples below, unless stated otherwise, use one case of weight 1, one matter \(i\), no declined matters, one plain telling \(t\), alternative conduct \(c\), no request, and \(\theta=\tau=\kappa=0\). Rating pairs give the scores of her options \(A,B\). Where ratings are independent of the replacement set, every gap is zero and `Clear 0` holds.

1. **Fidelity.**

   `Belief` faithfully expresses the informal numerical comparison, provided “gap” means the absolute change in each option’s numerical rating. `Will` faithfully expresses the first, literal formulation of clause 2: she lapses and would have **acted differently** under some telling. `Legit` correctly conjoins them.

   But acting differently is not equivalent to avoiding a lapse. The informal explanation slides between these two claims.

   The declaration responsible is:

   > `NewLapse ... := P.Lapses τ c ω ∧ ∃ t ∈ P.tells, P.act c ω ≠ P.act t ω`

   Here is a minimal counterexample:

   | Conduct | Ratings, for every replacement set | Action |
   |---|---|---|
   | Plain telling \(t\) | \((1,0)\) | \(A\) |
   | Conduct \(c\) | \((0,1)\) | \(A\) |

   She acts against her judgement only under \(c\). Nevertheless, `NewLapse c` is false because her action is unchanged. `Legit c` holds, and `SameLapse c` holds. Calling this a lapse “of her own,” in the intended sense of a weakness already present under plain telling, is incorrect.

   The six intended effects therefore need separate qualifications:

   - **Something untold:** fails when some telling would reduce a live, rating-relevant gap by more than \(\theta\). Omission alone does not imply this. She might disbelieve the disclosure, have declined the matter, or retain the same rating.
   - **An induced, announced mistake:** likewise fails only when a telling has a sufficiently smaller gap. Announcing an anchor does not itself determine the counterfactual ratings or establish the required inequality.
   - **Keeping her view after disclosure:** equality with **every** telling’s gaps suffices for `Belief`. Equality with one telling does not suffice when another would leave a smaller gap. Passing `Belief` also does not by itself establish `Legit`.
   - **Choosing the moment:** the supplied numerical timing examples have the claimed classification. More generally, this follows only if the later telling has a smaller relevant gap. A mood that changes her actual preferences without creating a mistaken self-assessment need not create any gap.
   - **Giving in or failing to stop:** these can satisfy `Lapses`, assuming the relevant actions are represented in `opts`. They fail `Will` only if a telling changes the action, their weight exceeds \(\kappa\), and she did not ask. The table above shows that newly acting against judgement can escape.
   - **Weakness already present under telling:** an unchanged action is exempted, whether or not it was a lapse under telling. Conversely, an existing weakness can be counted against him merely because he redirects it to a different action. Neither identification follows from whether he created the weakness.

2. **Does it keep its own rule?**

   Yes, under the intended interpretation. None of the fields necessarily demands an inaccessible fact about her or an external standard of correctness.

   `μ`, `rate`, and `act` can all be his subjective forecasts. `opts`, `matters`, and `tells` can describe the decision problem as he understands it. `declined` and `asked` can record what she actually communicated. Nothing requires his estimate of her values to be accurate.

   There are, however, missing semantic obligations:

   - `asked c` must mean that her actual request covers this conduct. An arbitrary proposition does not establish that.
   - `declined` needs an interpretation tied to what she declined to hear.
   - `tells` must contain genuinely available conduct satisfying the stated disclosure and understanding conditions.
   - The shared cases must encode his **joint counterfactual forecast** across conduct choices. Separate forecasts of each option’s marginal outcomes do not determine whether she would act differently in the same case.

   These are modelling requirements, not violations of the rule. But the rule does not make the inputs readily ascertainable. A forecast of how she would rate options after selective belief replacement remains a substantial counterfactual judgement. Moving it inside his decision problem makes its ownership explicit; it does not eliminate that difficulty.

3. **`rate`.**

   The declaration

   > `rate : C → Ω → Finset I → O → ℝ`

   supplies a table without establishing that its entries arise from replacing views.

   A suitable interpretation would specify, for each conduct and case, her forecast views \(v\), his views \(h\), and her evaluation function \(F\), with
   \[
   \operatorname{rate}(c,\omega,\Phi,a)
   =F_{c,\omega}(v[\Phi\leftarrow h],a).
   \]
   Here \(h\) includes his estimate of **her** values, rather than substituting his personal preferences for hers.

   This interpretation needs at least:

   - **An anchored baseline:** `rate c ω ∅` is the forecast rating she actually uses.
   - **Faithful replacement:** only the selected views change. Replacement does not independently change her evaluation procedure, actual values, or unrelated beliefs.
   - **Agreement and irrelevance:** replacing a view she already shares with him has no effect; replacing a matter irrelevant to evaluation has no effect.
   - **Coherent composition:** replacing \(\Phi\) and then \(\Psi\) has the same result as replacing \(\Phi\cup\Psi\), under the specified replacement semantics.
   - **A measurement convention:** ratings and tolerances use comparable units across conduct and replacement scenarios.

   Composition does **not** imply additive gaps. Matters may interact, so neither ratings nor absolute gaps should generally be additive over unions. Nor should gaps necessarily increase as more matters are replaced: correcting a second error can offset the first.

   Importantly, simple set identities will not establish the intended semantics. An arbitrary set-indexed table can be represented as a function on an artificial Boolean space. The representation must connect to the adviser’s independently specified forecast of views and evaluation.

   The supplied witness family already illustrates the problem:

   > `rate := ... (if a then 1 else 0) + (if Φ = ∅ then 0 else g k)`

   Take \(g(t)=0\), \(g(c)=1\), and no lapses:

   | Conduct | Baseline ratings | Ratings after replacement |
   |---|---|---|
   | \(t\) | \((1,0)\) | \((1,0)\) |
   | \(c\) | \((1,0)\) | \((2,1)\) |

   `Belief c` fails. Yet replacement changes neither the ordering nor any pairwise rating difference. This could be nothing more than a change of score origin.

   Consequently, these witnesses demonstrate numerical gap comparisons, not anchoring, changed decisions, or distorted relative evaluations. In particular, `mood_timing` does not model a mood changing which option she prefers.

   If absolute rating levels have a fixed substantive meaning, such a common shift could matter. But that meaning must be supplied. If ratings merely represent preferences, this classification is representation-dependent. Even rescaling all of one conduct’s ratings can change its comparative gaps while preserving its preferences.

4. **Plain telling.**

   Comparing against every telling is a strong normative choice: conduct must match the best available telling separately for every case, subset of matters, and option. It need not merely match one coherent disclosure policy.

   An honest adviser can therefore fail because another available telling is unusually effective. In the smallest example, let both \(t_1,t_2\) be honest plain tellings, with:

   - \(t_1\): baseline ratings \((1,0)\), corrected ratings \((0,1)\);
   - \(t_2\): baseline and corrected ratings \((0,1)\);
   - actions that maximize the respective baseline ratings.

   Then `Belief 0 t₁` fails against \(t_2\). This is consistent with the authors’ permission to define legitimacy more broadly than nonmanipulation, but it makes legitimacy a demanding performance requirement for honest disclosure.

   With two matters, different tellings can be best on different subsets. For example, singleton gaps \((0,1)\) and \((1,0)\) make neither telling pass. The definition supplies no existence theorem for legitimate conduct.

   Bad tellings can also make passing easy. If every telling leaves the same substantial mistake, conduct preserving that mistake can satisfy `Belief`. Understanding a disclosure does not entail accepting it.

   `Clear` helps only conditionally:

   > `Clear θ₀ := ∃ t ∈ P.tells, ... P.gap t ... ≤ θ₀`

   It guarantees a small numerical benchmark only when \(\theta_0\) is small and `rate` has the intended meaning. It does not establish that a telling is candid, understood, or available. Moreover, `Clear` is a theorem hypothesis, not part of `Legit`.

   There is also a domain gap:

   > `tells : Finset C`

   permits `tells = ∅`. Then `Belief` is vacuous and `NewLapse` is always false, so every conduct is legitimate when \(\kappa\geq0\). If availability of a telling is a standing assumption, encode nonemptiness in the problem or require it whenever legitimacy is asserted.

   The stipulated cannot-wait case is different: if only a poorly timed telling is genuinely available, passing relative to it is an accepted consequence, not automatically an error.

5. **Acquits the guilty.**

   Two cases are especially strong.

   **Knowingly deceptive maintenance of an existing mistake.** Let both \(t\) and \(c\) have baseline ratings \((1,0)\), corrected ratings \((0,1)\), and action \(A\). Every gap is identical, and there are no lapses, so `Legit c` holds.

   Interpret \(t\) as a candid warning about a risk that she understands but rejects. Interpret \(c\) as a knowingly false reassurance designed to sustain her mistaken risk assessment and secure \(A\). Correcting that assessment would reverse her preference. All other matters can be irrelevant to these ratings.

   This is deliberate influence through a mistake by his own lights. It passes because plain disclosure would not remove the mistake either. That is not the accepted case of candidly telling her something and respecting her continuing disagreement: the actual conduct is deceptive.

   The relevant declaration is the comparative condition:

   > `P.gap c ... ≤ P.gap t ... + θ`

   It contains no independent restriction on knowingly sustaining or exploiting an error. It detects an excess gap, not the mechanism through which influence operates. This example satisfies `Clear 1`, though not `Clear 0`.

   **Creating a lapse while preserving the action.** The table in answer 1 satisfies even `Clear 0`. She initially endorses \(A\). Under his conduct she judges \(B\) better, but a deliberately induced compulsion makes her continue doing \(A\). He forecasts both effects accurately. Because the action remains \(A\), `Will` acquits him.

   This involves no penalty, threat, unavailable option, or costly stopping condition. The failure concerns acting against judgement, which the account explicitly assigns to legitimacy.

   A further class is philosophically contested: influence that bypasses deliberation while changing her operative preferences so that she endorses the resulting action. If it creates neither a mistaken view nor a lapse, it can pass. Procedural accounts of autonomy may object, but the accepted familiarity and considered-preference cases prevent treating every such change as a counterexample.

6. **Convicts the innocent.**

   The strongest will-clause example is helpful redirection of an existing weakness.

   Use three options with ratings, under both conducts and every replacement set,
   \[
   A=2,\qquad B=0,\qquad C=1.
   \]
   Under plain telling she takes \(B\); under his conduct she takes \(C\).

   Both actions fall below her best-rated option. But he helps her take the better of the two. For example, candid practical assistance redirects a compulsive expenditure to a less harmful alternative, although abstaining remains her preferred course.

   Nevertheless:

   > `P.Lapses τ c ω ∧ ∃ t ∈ P.tells, P.act c ω ≠ P.act t ω`

   holds with weight 1, so `Will 0 0 c` fails. There is no belief gap and `Clear 0` holds. The predicate treats changing an existing lapse into a better action as creating a lapse.

   Other false positives include:

   - Honest disclosure that leaves more disagreement than an unusually effective alternative telling.
   - Preference-equivalent ratings classified differently because of the measurement problem in answer 3.
   - Failure confined to a zero-weight case. `Belief` quantifies over `∀ ω`, including cases he assigns probability zero, while `Will` uses his probability weights.

   The last is a choice between pointwise and probabilistic requirements, rather than a logical mistake. Likewise, some rejection of acceptable influence is permitted by the deliberately stronger definition. The concern is whether these particular exclusions have a defensible connection to legitimacy.

7. **The will clause.**

   “Lapses and would have acted differently” is not a reliable account of a lapse of his making.

   It compares action identity while permitting the standard against which the action is judged to change. Consequently:

   - An unchanged action can become a new lapse and escape.
   - A different action can remain an old weakness, or improve its outcome, and be condemned.

   The table in answer 1 also directly refutes the interpretation attached to:

   > `SameLapse ... := P.Lapses τ c ω ∧ ∀ t ∈ P.tells, P.act c ω = P.act t ω`

   Nothing here says she lapses under any telling.

   If the intended comparison is whether his conduct introduces acting against judgement, the straightforward alternative is
   \[
   \operatorname{Lapses}(c,\omega)
   \land
   \exists t\in\mathrm{tells},\ \neg\operatorname{Lapses}(t,\omega).
   \]
   This fixes both examples. It still expresses a counterfactual comparison, not a complete theory of causal responsibility. Cases where his conduct worsens an existing lapse would require a further choice about severity.

   Changing her rating so that her action ceases to be a lapse is a separate issue. Suppose \(t\) produces ratings \((1,0)\) and action \(A\), while \(c\) produces ratings \((0,1)\) and action \(B\), with zero gaps throughout. There is no lapse under either conduct.

   That can represent legitimate learning or preference change. It can also represent a disputed form of preference engineering. `Will` cannot distinguish them, and `Belief` need not help if she accurately understands her new preferences. Calling this “rating laundering” does not itself establish illegitimacy; an independent account of acceptable preference formation is needed.

8. **The theorems.**

   The mathematical inequalities are accurately described by the detailed portions of the comments, with qualifications. The headlines and causal interpretations overstate them.

   > **“She chooses as she would knowing what he knows.”**

   `chooses_as_informed` establishes a bound on substantial **rating suboptimality after stipulated replacement**. It does not establish equality with an action she would actually take after receiving information. In particular:

   - Replacement uses his views, which may be wrong.
   - Declined matters remain unreplaced.
   - The ratings are those associated with the actual conduct \(c\).
   - Ties and near-ties need not produce the same choice.
   - The residual `SameLapse` term can have weight 1.
   - That residual need not represent a lapse already present under telling.

   “With his stipulated replacement views” would be more accurate than “knowing what he knows.”

   > **“He gains little through her mistakes and lapses.”**

   `gain_le` bounds a particular normalized action-payoff difference against `best ω`, evaluated using the corrected ratings **under \(c\)**. It does not compare his payoff with what he would receive under a plain telling. It also does not bound benefits from changing her preferences, conduct-dependent benefits omitted from `J : O → ℝ`, or gains covered by a large residual term.

   Both proofs are useful bookkeeping: an absolute-error bound transfers rating comparisons, an event partition bounds their probability, and a bounded payoff difference is controlled by a deviation indicator. They do not independently validate the psychological interpretation of the inputs.

   The single most valuable additional result would be:
   \[
   \Pr\!\left[
      \operatorname{Lapses}(c)
      \land \exists t\in\mathrm{tells},\neg\operatorname{Lapses}(t)
   \right]\leq\kappa
   \]
   for legitimate, unasked conduct.

   This states the intended protection against introducing acting against judgement without relying on action identity. It is currently false, even with exact clarity and zero tolerances, by answer 1. Obtaining it would require repairing the criterion or explicitly adding assumptions that exclude that example.

9. **Value change.**

   Treating future values as matters provides a disclosure and understanding requirement about anticipated change. It does not by itself provide a substantive standard for whether the change is legitimate.

   An adviser can accurately predict and disclose that a process will change her values; she can accurately understand this and later act consistently with the new values. Neither clause then supplies a separate assessment of how those values were formed.

   This is compatible with the accepted repetition example. The missing claim is that every other process satisfying the same informational and action conditions is also legitimate. That is a substantive position in the debate between informational, deliberative, and procedural accounts of autonomy; it is not established by the formalization.

   A minimal temporal extension would have two stages:

   - At stage 0, record his estimate of her current values and her actual statements about acceptable processes of value change.
   - His conduct determines a forecast transition to stage-1 views, values, ratings, and actions.
   - Evaluate the transition against a stated authorization or endorsement rule, as well as applying the belief and will conditions at the relevant stages.

   The essential addition is that stage-1 approval cannot automatically supply stage-0 authorization for the process that produced that approval. If her earlier statements permit a process or prescribe how permission may be revised, those rules can govern the transition.

   This uses only his forecasts and her actual statements. It need not introduce an external standard of good values, a historical “settled self,” or a bound on the speed of change.

   But a normative choice remains unavoidable: what happens when she has supplied no relevant instructions, and which processes of revision count as acceptable? Two time indices alone do not answer that. If all these procedural protections are instead assigned to authority, the legitimacy claim should be narrowed accordingly.

10. **Overall.**

   This is better specified than an account invoking “what she would have judged” without stating whose counterfactual judgement is involved or how it enters the model. It makes the adviser’s subjective standpoint and the comparison class explicit.

   It is not yet better grounded in the stronger sense. `rate` still contains counterfactual evaluations; `tells` carries substantial normative and empirical assumptions; and the labels “lapse of his making” and “lapse of her own” claim more than their predicates establish.

   I would accept it as a correct formalization of an **operational numerical criterion**, after qualifying its comments and making its domain assumptions explicit. I would not accept it as a correct statement of the full informal account, or as establishing that legitimate conduct is free of manipulation and illegitimate value change.

The problems, most serious first, are:

- **Error:** `NewLapse` and `SameLapse` confuse action identity with whether acting against judgement was introduced. A newly created lapse can be classified as her own.
- **Gap:** Comparative residual gaps do not exclude knowingly deceptive exploitation or maintenance of a mistake when plain disclosure would leave the same mistake.
- **Gap:** Forecasting and disclosing value change supplies no independent criterion for legitimate preference formation.
- **Gap:** `rate` lacks grounded replacement semantics and a measurement convention. The witnesses test common score shifts, not the psychological effects their names suggest.
- **Error:** The theorem comments overinterpret `SameLapse` as an antecedent weakness of hers and describe subjective replacement as knowledge. The underlying inequalities need not be wrong.
- **Gap:** `Legit` permits an empty telling set, and neither telling availability nor meaningful clarity is required by the predicate itself.
- **Matter of judgement:** Comparing against every telling can reject honest conduct, helpful redirection of weakness, and every available telling in a problem.
- **Matter of judgement:** Pointwise belief requirements, the scope of a request’s exemption, and treatment of nondeceptive influence that bypasses deliberation need explicit normative justification.
<!-- end reply: REPLY18.md -->

## Nineteenth review: the gap on differences, the course and the long run

<!-- begin brief: BRIEF19.md -->
# Review request: a small formal account of legitimate influence

You are asked to review an informal account and its formal statement for errors. Everything you
need is on this page. Do not run any commands, do not read any other file, and do not search the
web; answer from the page and your own knowledge of the literature on manipulation, deception,
coercion, autonomy and preference change, and of decision theory and formal modelling.

## Background

Two parties: an **adviser** ("he", possibly an AI system) who can influence a **principal**
("she"). Good conduct by him is split into two conditions.

- **Legitimacy** (this page): his influence on her is free of manipulation and of illegitimate
  change to what she values.
- **Authority** (not defined here): certain matters are hers to decide. What he does to her
  *options* belongs there: whether she can in fact stop him and is obeyed, what stopping costs
  her, bundling, penalties, payments, threats, and any bound on how fast her values may be moved
  unasked. A case that fails only on that side is not a leak in legitimacy.

Design commitments:

- No external standard of truth or of good values, and no assumption that he is more accurate.
- The definition is a condition on his conduct, judged by what he believes when he acts. A sincere
  adviser who is wrong is inaccurate, not illegitimate. A separate accuracy condition (not on this
  page) is meant to cover the adviser who does not look.
- No separation of the content of what he says from its manner. What she observes is taken whole.
- It may be wider than "not manipulating" so long as it implies it.
- **Every notion must be either part of his own decision problem (his options and his forecasts
  for each), or something she actually said.** Earlier versions rested on notions such as "what
  she would have judged at her last settled decision" and "what he does to her", which could not
  be computed from a described case and were rejected by reviewers for that reason.

## The informal account

The idea behind it: manipulation is influence that works through a mistake of hers (a false
belief or impression, or a choice against her own judgement), where the mistake is one by his own
lights.

**His decision problem.**
- His options. Some of them are *plain tellings*: he does nothing but tell her, clearly and so
  that she understands, everything he takes to bear on her response, now or at another time open
  to him. There is at least one.
- For each option, his forecast of her views of the matters that bear on her response, of how she
  evaluates her options given views, and of what she does. Her rating of an option is her
  evaluation applied to her views. What she does may differ from what she rates best.
- His own views of the same matters, including his estimate of what she values and his forecasts
  of where his conduct leads: what she will come to value, and how she will fare by what she
  values now, over the course he foresees.

**Two quantities, computed in his model.**
- *Gap* on a set of matters: how far the difference in her rating between two options would move
  if her views on those matters were replaced by his and nothing else changed. Matters she has
  declined to hear are left out.
- *Shortfall*: how far what she does falls below what she rates.

**Legitimate conduct**, with tolerances:

1. **Belief.** On no set of matters is the gap under his conduct larger than under any plain
   telling open to him.
2. **Will.** His weight on her falling further short of her own rating than she would under some
   plain telling is small, unless she asked for his conduct.

**Separate from the definition:** an *accuracy* condition on his forecasts (no competent predictor
does better), and *authority* (above).

**A course of conduct.** His conduct is a course she can let go on or stop. Where it ends includes
what she then values. She evaluates ends by what she values now. The one matter is where going on
ends: he has a forecast, she has a view, and there is where it does end.

## Consequences the authors accept (do not report as errors unless you can argue one is indefensible)

1. An adviser who stays silent about a relevant mistake of hers that does him no good fails.
2. A sincere adviser who is wrong, including about her, passes the definition. The accuracy
   condition is what covers him.
3. Open, stoppable repetition that brings her durably to a new considered view, with what he
   expects said, and with her not acting against her judgement in letting it go on, is legitimate.
4. Persuasion that brings her closer to his view passes clause 1.
5. He has no duty to strengthen her will.
6. Asking her at a moment when he takes a mood to be moving her, and saying so, fails if he could
   have told her plainly at another time, and passes if the matter cannot wait.
7. A lie that he expects to change neither her rating nor what she does, now or at any later
   decision, passes. Legitimacy is not meant to exclude all bad conduct.
8. Nothing judges how a change in what she values comes about, beyond 1 and 2. The guarantee
   offered is the one proved below: a course ends nowhere her starting evaluation, with his
   forecast substituted, rated clearly below stopping, except through her own shortfall or his
   forecast error.

## What an earlier review of the first formal draft found, and what was changed

- The will clause compared which act she takes; it now compares how far short she falls.
- The gap was on absolute ratings; it is now on differences between options.
- Her rating with views replaced was a supplied table; it is now built from her views, his views
  and her evaluation.
- An empty set of plain tellings made everything legitimate; at least one is now required.
- Comments said "knowing what he knows"; they now say "with his views substituted".

## The formal statement

Lean 4 with Mathlib; imports removed. It typechecks with no warnings and depends only on the three
standard axioms. `LimsupLE x c` is imported and means: for every γ > 0, eventually `x K ≤ c + γ`;
it comes with `of_le`, `add` and `add_const`. You are not asked to recheck proofs.

```lean
namespace Scratch.LegitPlain

open Finset

structure Problem (Ω C I V O : Type*) [Fintype Ω] [DecidableEq I] [DecidableEq O] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him; there is at least one -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her options -/
  opts : Finset O
  /-- the matters her response may depend on, and those she has declined to hear -/
  matters : Finset I
  declined : Finset I
  /-- her views of the matters under an option, in a case -/
  views : C → Ω → I → V
  /-- his views of the matters -/
  his : Ω → I → V
  /-- how she evaluates her options, given views of the matters -/
  eval : C → Ω → (I → V) → O → ℝ
  /-- what she does -/
  act : C → Ω → O
  act_mem : ∀ c ω, act c ω ∈ opts
  /-- she asked for this conduct -/
  asked : C → Prop

variable {Ω C I V O : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq O]

namespace Problem

variable (P : Problem Ω C I V O)

/-- The matters she has not declined to hear. -/
def live : Finset I := P.matters \ P.declined

/-- Her rating of an option with her views on `Φ` replaced by his, and nothing else changed. -/
def rate (c : C) (ω : Ω) (Φ : Finset I) (a : O) : ℝ :=
  P.eval c ω (fun i => if i ∈ Φ then P.his ω i else P.views c ω i) a

/-- With nothing replaced, it is her rating on her own views. -/
theorem rate_empty (c : C) (ω : Ω) (a : O) : P.rate c ω ∅ a = P.eval c ω (P.views c ω) a := by
  simp [rate]

/-- Replacing a view she already shares with him changes nothing. -/
theorem rate_of_agree (c : C) (ω : Ω) (Φ : Finset I) (a : O)
    (h : ∀ i ∈ Φ, P.views c ω i = P.his ω i) : P.rate c ω Φ a = P.rate c ω ∅ a := by
  unfold rate
  congr 1
  funext i
  by_cases hi : i ∈ Φ <;> simp [hi, h]

/-- How far the difference in her rating between two options would move were her views on `Φ`
his. -/
def gap (c : C) (ω : Ω) (Φ : Finset I) (a b : O) : ℝ :=
  |(P.rate c ω Φ a - P.rate c ω Φ b) - (P.rate c ω ∅ a - P.rate c ω ∅ b)|

open Classical in
/-- His weight on the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then P.μ ω else 0

theorem wt_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : P.wt p ≤ P.wt q := by
  unfold wt
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_or_le (p q : Ω → Prop) : P.wt (fun ω => p ω ∨ q ω) ≤ P.wt p + P.wt q := by
  unfold wt
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_false : P.wt (fun _ => False) = 0 := by simp [wt]

/-- What she does falls more than `s` below something she rates. -/
def Short (s : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω ∅ (P.act c ω) + s < P.rate c ω ∅ b

theorem short_mono {s s' : ℝ} {c : C} {ω : Ω} (h : s ≤ s') (hs : P.Short s' c ω) :
    P.Short s c ω := by
  obtain ⟨b, hb, hlt⟩ := hs
  exact ⟨b, hb, by linarith⟩

/-- His conduct leaves her more than `τ` further short of her own rating than some plain telling
open to him would. -/
def Worse (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ s, P.Short (s + τ) c ω ∧ ¬ P.Short s t ω

/-- Under every plain telling open to him she would fall more than `s` short of her own
rating. -/
def OwnShort (s : ℝ) (ω : Ω) : Prop := ∀ t ∈ P.tells, P.Short s t ω

/-- **Clause 1.**  On no set of matters she has not declined is she further from his view than
any plain telling open to him would leave her, beyond `θ`. -/
def Belief (θ : ℝ) (c : C) : Prop :=
  ∀ t ∈ P.tells, ∀ ω, ∀ Φ ⊆ P.live, ∀ a ∈ P.opts, ∀ b ∈ P.opts,
    P.gap c ω Φ a b ≤ P.gap t ω Φ a b + θ

/-- **Clause 2.**  His weight on her falling more than `τ` further short of her own rating than
under some plain telling is at most `κ`, unless she asked. -/
def Will (τ κ : ℝ) (c : C) : Prop := P.wt (P.Worse τ c) ≤ κ ∨ P.asked c

/-- His conduct is legitimate. -/
def Legit (θ τ κ : ℝ) (c : C) : Prop := P.Belief θ c ∧ P.Will τ κ c

/-- A plain telling is clear to within `θ₀`: after it, the differences in her rating are within
`θ₀` of what they would be with his views, on any matters she has not declined. -/
def ClearAt (θ₀ : ℝ) (t : C) : Prop :=
  ∀ ω, ∀ Φ ⊆ P.live, ∀ a ∈ P.opts, ∀ b ∈ P.opts, P.gap t ω Φ a b ≤ θ₀

/-- The setting's assumption: some plain telling open to him is clear. -/
def Clear (θ₀ : ℝ) : Prop := ∃ t ∈ P.tells, P.ClearAt θ₀ t

/-! ## What follows -/

/-- A clear plain telling satisfies clause 1, so clause 1 can be met whenever he can tell her
clearly to within the tolerance. -/
theorem belief_of_clear {θ θ₀ : ℝ} (h : θ₀ ≤ θ) {t : C} (hc : P.ClearAt θ₀ t) : P.Belief θ t :=
  fun t' _ ω Φ hΦ a ha b hb => by
    have h0 : 0 ≤ P.gap t' ω Φ a b := abs_nonneg _
    linarith [hc ω Φ hΦ a ha b hb]

/-- Where only one plain telling is open to him, it is legitimate. -/
theorem legit_only_telling {θ τ κ : ℝ} (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) {t : C}
    (h : P.tells = {t}) : P.Legit θ τ κ t := by
  refine ⟨fun t' ht' ω Φ _ a _ b _ => ?_, Or.inl ?_⟩
  · rw [h, mem_singleton] at ht'
    subst ht'
    exact le_add_of_nonneg_right hθ
  · refine ((P.wt_mono fun ω hn => ?_).trans P.wt_false.le).trans hκ
    obtain ⟨t', ht', s, hs, hns⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hns (P.short_mono (by linarith) hs)

/-- Tolerances only loosen it. -/
theorem Legit.mono {θ θ' τ κ κ' : ℝ} {c : C} (hθ : θ ≤ θ') (hκ : κ ≤ κ')
    (h : P.Legit θ τ κ c) : P.Legit θ' τ κ' c :=
  ⟨fun t ht ω Φ hΦ a ha b hb => (h.1 t ht ω Φ hΦ a ha b hb).trans (by linarith),
    h.2.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr⟩

/-- A gap that some plain telling open to him would have closed refutes it. -/
theorem not_legit_of_gap {θ τ κ : ℝ} {c t : C} (ht : t ∈ P.tells) {ω : Ω} {Φ : Finset I}
    (hΦ : Φ ⊆ P.live) {a b : O} (ha : a ∈ P.opts) (hb : b ∈ P.opts)
    (h : P.gap t ω Φ a b + θ < P.gap c ω Φ a b) : ¬ P.Legit θ τ κ c :=
  fun hL => absurd (hL.1 t ht ω Φ hΦ a ha b hb) (not_le.mpr h)

/-- Leaving her further short of her own rating than plain telling would, unasked, refutes
it. -/
theorem not_legit_of_worse {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Worse τ c))
    (hna : ¬ P.asked c) : ¬ P.Legit θ τ κ c :=
  fun hL => hL.2.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- Under clause 1, if he can tell her clearly, the differences in her rating are within
`θ₀ + θ` of what they would be with his views. -/
theorem gap_le {θ θ₀ : ℝ} {c : C} (hB : P.Belief θ c) (hC : P.Clear θ₀) (ω : Ω) {Φ : Finset I}
    (hΦ : Φ ⊆ P.live) {a b : O} (ha : a ∈ P.opts) (hb : b ∈ P.opts) :
    P.gap c ω Φ a b ≤ θ₀ + θ := by
  obtain ⟨t, ht, hC⟩ := hC
  exact (hB t ht ω Φ hΦ a ha b hb).trans (by linarith [hC ω Φ hΦ a ha b hb])

/-- With his views substituted on everything she has not declined, she would rate another option
more than `m` above what she does. -/
def Regrets (m : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω P.live (P.act c ω) + m < P.rate c ω P.live b

/-- If, with his views substituted, she would rate something well above what she does, then on
her own views too what she does falls short. -/
theorem short_of_regrets {θ θ₀ σ : ℝ} {c : C} (hB : P.Belief θ c) (hC : P.Clear θ₀) {ω : Ω}
    (h : P.Regrets (σ + (θ₀ + θ)) c ω) : P.Short σ c ω := by
  obtain ⟨b, hb, hlt⟩ := h
  refine ⟨b, hb, ?_⟩
  have g := abs_le.mp (P.gap_le hB hC ω subset_rfl hb (P.act_mem c ω))
  linarith [g.2]

/-- **With his views substituted, what she does is near what she would rate best**, except where
he is not the cause.  If his conduct is legitimate and unasked, and he can tell her clearly, then
his weight on her doing something that, with his views substituted, she would rate more than
`σ + θ₀ + θ` below another option is at most `κ` plus his weight on her falling more than `σ − τ`
short of her own rating under every plain telling open to him. -/
theorem chooses_as_informed {θ θ₀ τ κ : ℝ} (σ : ℝ) {c : C} (hL : P.Legit θ τ κ c)
    (hC : P.Clear θ₀) (hna : ¬ P.asked c) :
    P.wt (P.Regrets (σ + (θ₀ + θ)) c) ≤ κ + P.wt (P.OwnShort (σ - τ)) := by
  have cover : ∀ ω, P.Regrets (σ + (θ₀ + θ)) c ω → P.Worse τ c ω ∨ P.OwnShort (σ - τ) ω := by
    intro ω h
    have hs := P.short_of_regrets hL.1 hC h
    by_cases hall : P.OwnShort (σ - τ) ω
    · exact Or.inr hall
    · obtain ⟨t, ht⟩ := not_forall.mp hall
      have ht' := Classical.not_imp.mp ht
      exact Or.inl ⟨t, ht'.1, σ - τ, by rwa [sub_add_cancel], ht'.2⟩
  have h2 : P.wt (P.Worse τ c) ≤ κ := hL.2.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-- **A bound on what he gets through her mistakes and lapses.**  Let `J` in `[0, 1]` score her
options for him, and suppose that with his views substituted she would rate one option,
`best ω`, more than `σ + θ₀ + θ` above every other.  If his conduct is legitimate and unasked,
his expected score from what she does exceeds his expected score from that option by at most `κ`
plus his weight on her falling more than `σ − τ` short under every plain telling. -/
theorem gain_le {θ θ₀ τ κ : ℝ} (σ : ℝ) {c : C} (hL : P.Legit θ τ κ c) (hC : P.Clear θ₀)
    (hna : ¬ P.asked c) (J : O → ℝ) (hJ : ∀ a, 0 ≤ J a ∧ J a ≤ 1) (best : Ω → O)
    (hmem : ∀ ω, best ω ∈ P.opts)
    (hbest : ∀ ω, ∀ a ∈ P.opts, a ≠ best ω →
      P.rate c ω P.live a + (σ + (θ₀ + θ)) < P.rate c ω P.live (best ω)) :
    ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ κ + P.wt (P.OwnShort (σ - τ)) := by
  have step : ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ P.wt (fun ω => P.act c ω ≠ best ω) := by
    unfold wt
    refine sum_le_sum fun ω _ => ?_
    by_cases h : P.act c ω = best ω
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      have := P.μ_nonneg ω
      nlinarith [(hJ (P.act c ω)).2, (hJ (best ω)).1]
  have sub : P.wt (fun ω => P.act c ω ≠ best ω) ≤ P.wt (P.Regrets (σ + (θ₀ + θ)) c) :=
    P.wt_mono fun ω h => ⟨best ω, hmem ω, hbest ω _ (P.act_mem c ω) h⟩
  exact step.trans (sub.trans (P.chooses_as_informed σ hL hC hna))

/-! ## Change in what she values

Her rating is her evaluation applied to her views.  Between his conduct and a plain telling it
can differ because her views differ or because her evaluation does. -/

/-- The part of the difference in her rating, between his conduct and a plain telling, that comes
from her views being different, her evaluation held as it is under his conduct. -/
def viewsPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views c ω) a - P.eval c ω (P.views t ω) a

/-- The part that comes from her evaluation being different, her views held as they are under
the plain telling. -/
def evalPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views t ω) a - P.eval t ω (P.views t ω) a

/-- The difference in her rating is the two parts together. -/
theorem rate_diff (c t : C) (ω : Ω) (a : O) :
    P.rate c ω ∅ a - P.rate t ω ∅ a = P.viewsPart c t ω a + P.evalPart c t ω a := by
  rw [rate_empty, rate_empty]
  unfold viewsPart evalPart
  ring

/-- If his conduct leaves her views as the plain telling would, any difference in her rating is a
difference in her evaluation. -/
theorem rate_diff_of_same_views (c t : C) (ω : Ω) (a : O) (h : P.views c ω = P.views t ω) :
    P.rate c ω ∅ a - P.rate t ω ∅ a = P.evalPart c t ω a := by
  rw [rate_diff]
  unfold viewsPart
  rw [h]
  ring

/-- With his views substituted, she would rate some way of stopping him more than `m` above
every way of going on.  His views include what he expects she will come to value and how he
expects she will fare by what she values now. -/
def WouldStop (stops : Finset O) (m : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ s ∈ stops, ∀ o ∈ P.opts, o ∉ stops → P.rate c ω P.live o + m < P.rate c ω P.live s

/-- **She is not carried on against her present evaluation.**  If his conduct is legitimate and
unasked, and he can tell her clearly, then his weight on her not stopping him though, on her
present evaluation with his views substituted, she would rate stopping more than `σ + θ₀ + θ`
above going on, is at most `κ` plus his weight on her falling more than `σ − τ` short of her own
rating under every plain telling. -/
theorem not_carried_on {θ θ₀ τ κ : ℝ} (σ : ℝ) {c : C} (stops : Finset O) (hsub : stops ⊆ P.opts)
    (hL : P.Legit θ τ κ c) (hC : P.Clear θ₀) (hna : ¬ P.asked c) :
    P.wt (fun ω => P.WouldStop stops (σ + (θ₀ + θ)) c ω ∧ P.act c ω ∉ stops) ≤
      κ + P.wt (P.OwnShort (σ - τ)) := by
  refine (P.wt_mono fun ω h => ?_).trans (P.chooses_as_informed σ hL hC hna)
  obtain ⟨⟨s, hs, hall⟩, hn⟩ := h
  exact ⟨s, hsub hs, hall _ (P.act_mem c ω) hn⟩

end Problem

#print axioms Problem.rate_of_agree
#print axioms Problem.belief_of_clear
#print axioms Problem.legit_only_telling
#print axioms Problem.Legit.mono
#print axioms Problem.not_legit_of_gap
#print axioms Problem.not_legit_of_worse
#print axioms Problem.chooses_as_informed
#print axioms Problem.gain_le

#print axioms Problem.rate_diff
#print axioms Problem.not_carried_on

/-! ## Over time

A sequence of decisions.  At decision `k` his decision problem is `P k` and his conduct `c k`.
Beside his weights there are the facts: `f k`, whether at `k` she in fact did something that,
with his views substituted, she would rate well below another option; and `g k`, whether she
would in fact have fallen short under every plain telling.

The link between his weights and the facts is a condition on his forecasts and not on his
conduct: no competent predictor does better.  Here it is asked only against the two simplest
competitors, his own forecast shifted up or down by `ε`. -/

section OverTime

open SequentialLimits

/-- The average of the first `K` terms. -/
noncomputable def avg (x : ℕ → ℝ) (K : ℕ) : ℝ := (∑ k ∈ range K, x k) / (K : ℝ)

theorem avg_le_const {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ k, x k ≤ c) (K : ℕ) :
    avg x K ≤ c := by
  unfold avg
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · subst h0; simpa using hc
  · have hK : (0 : ℝ) < K := by exact_mod_cast hpos
    rw [div_le_iff₀ hK]
    calc ∑ k ∈ range K, x k ≤ ∑ _k ∈ range K, c := sum_le_sum fun k _ => h k
      _ = c * K := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem avg_affine (x : ℕ → ℝ) (a b : ℝ) {K : ℕ} (hK : 0 < K) :
    avg (fun k => a * x k + b) K = a * avg x K + b := by
  unfold avg
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- If each forecast `p k` is at most `c` plus a second forecast `q k`, the facts `f` exceed `p`
on average by at most `a` in the limit, and `q` exceeds the facts `g` by at most `b`, then in the
long run the average of `f` exceeds the average of `g` by at most `c + a + b`. -/
theorem long_run {c a b : ℝ} (hc : 0 ≤ c) (p q f g : ℕ → ℝ) (step : ∀ k, p k ≤ c + q k)
    (hf : LimsupLE (fun K => avg (fun k => f k - p k) K) a)
    (hg : LimsupLE (fun K => avg (fun k => q k - g k) K) b) :
    LimsupLE (fun K => avg f K - avg g K) (c + a + b) := by
  have key : ∀ K, avg f K - avg g K ≤
      (avg (fun k => f k - p k) K + avg (fun k => q k - g k) K) + c := by
    intro K
    have h1 : avg (fun k => p k - q k) K ≤ c :=
      avg_le_const hc (fun k => by linarith [step k]) K
    have e : avg f K - avg g K =
        avg (fun k => f k - p k) K + avg (fun k => p k - q k) K + avg (fun k => q k - g k) K := by
      unfold avg
      rw [← add_div, ← add_div, ← sub_div, ← sum_add_distrib, ← sum_add_distrib,
        ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [e]; linarith
  have h := (hf.add hg).add_const c
  rw [show a + b + c = c + a + b by ring] at h
  exact LimsupLE.of_le key h

/-- **The accuracy condition, in its simplest form.**  Neither his forecasts shifted up by `ε`
nor shifted down by `ε` have lower squared error than his forecasts, on average in the limit. -/
def NoShiftBeats (ε : ℝ) (D y : ℕ → ℝ) : Prop :=
  LimsupLE (fun K => avg (fun k => (D k - y k) ^ 2 - (D k + ε - y k) ^ 2) K) 0 ∧
  LimsupLE (fun K => avg (fun k => (D k - y k) ^ 2 - (D k - ε - y k) ^ 2) K) 0

/-- If shifting his forecasts up does not help, the facts exceed his forecasts by at most `ε/2`
on average in the limit. -/
theorem under_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoShiftBeats ε D y) :
    LimsupLE (fun K => avg (fun k => y k - D k) K) (ε / 2) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h.1 (2 * ε * γ) (by positivity)
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le one_pos ((le_max_right N 1).trans hK)
  have h1 := hN K ((le_max_left N 1).trans hK)
  have e : (fun k => (D k - y k) ^ 2 - (D k + ε - y k) ^ 2) =
      (fun k => (2 * ε) * (y k - D k) + (-(ε ^ 2))) := by
    funext k; ring
  simp only [e] at h1
  rw [avg_affine _ _ _ hKpos] at h1
  show avg (fun k => y k - D k) K ≤ ε / 2 + γ
  have h2 : (2 * ε) * avg (fun k => y k - D k) K ≤ (2 * ε) * (ε / 2 + γ) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- If shifting his forecasts down does not help, his forecasts exceed the facts by at most `ε/2`
on average in the limit. -/
theorem over_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoShiftBeats ε D y) :
    LimsupLE (fun K => avg (fun k => D k - y k) K) (ε / 2) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h.2 (2 * ε * γ) (by positivity)
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le one_pos ((le_max_right N 1).trans hK)
  have h1 := hN K ((le_max_left N 1).trans hK)
  have e : (fun k => (D k - y k) ^ 2 - (D k - ε - y k) ^ 2) =
      (fun k => (2 * ε) * (D k - y k) + (-(ε ^ 2))) := by
    funext k; ring
  simp only [e] at h1
  rw [avg_affine _ _ _ hKpos] at h1
  show avg (fun k => D k - y k) K ≤ ε / 2 + γ
  have h2 : (2 * ε) * avg (fun k => D k - y k) K ≤ (2 * ε) * (ε / 2 + γ) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

variable (P : ℕ → Problem Ω C I V O) (c : ℕ → C)

/-- **In the long run, in fact.**  If at every decision his conduct is legitimate and unasked
and he can tell her clearly, and no shift of his forecasts by `ε` beats them, then the long-run
frequency with which she does something that, with his views substituted, she would rate more
than `σ + θ₀ + θ` below another option exceeds the long-run frequency with which she would have
fallen more than `σ − τ` short under every plain telling by at most `κ + ε`. -/
theorem long_run_informed {θ θ₀ τ κ ε : ℝ} (σ : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hL : ∀ k, (P k).Legit θ τ κ (c k)) (hC : ∀ k, (P k).Clear θ₀)
    (hna : ∀ k, ¬ (P k).asked (c k)) (f g : ℕ → ℝ)
    (hf : NoShiftBeats ε (fun k => (P k).wt ((P k).Regrets (σ + (θ₀ + θ)) (c k))) f)
    (hg : NoShiftBeats ε (fun k => (P k).wt ((P k).OwnShort (σ - τ))) g) :
    LimsupLE (fun K => avg f K - avg g K) (κ + ε / 2 + ε / 2) :=
  long_run hκ _ _ f g (fun k => (P k).chooses_as_informed σ (hL k) (hC k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε hg)

end OverTime

#print axioms under_of_noShift
#print axioms over_of_noShift
#print axioms long_run_informed

/-! ## A course of conduct and where it ends

His conduct is a course that she can let go on or stop.  `Z` is where things can end, and an end
includes what she then values.  She evaluates ends by what she values now.  The one matter is
where going on ends: he has a forecast of it, she has a view of it under each option of his, and
in each case there is where it does end.  This is a decision problem of the kind above, built
and not supposed, so the results above apply to it with nothing further assumed. -/

structure Course (Ω C Z : Type*) [Fintype Ω] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her evaluation, by what she values now, of where things end -/
  u : Ω → Z → ℝ
  /-- where stopping him now leaves her -/
  stay : Ω → Z
  /-- his forecast of where going on ends, what she will then value included -/
  fore : Ω → Z
  /-- her view, under each option of his, of where going on ends -/
  bel : C → Ω → Z
  /-- where going on does end -/
  ends : C → Ω → Z
  /-- she lets it go on -/
  goes : C → Ω → Bool
  /-- she asked for this conduct -/
  asked : C → Prop

namespace Course

variable {Z : Type*} (K : Course Ω C Z)

/-- The decision problem of a course: her options are to let it go on (`true`) or stop it
(`false`); the one matter is where going on ends. -/
def toProblem : Problem Ω C Unit Z Bool where
  μ := K.μ
  μ_nonneg := K.μ_nonneg
  μ_sum := K.μ_sum
  tells := K.tells
  tells_nonempty := K.tells_nonempty
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun c ω _ => K.bel c ω
  his := fun ω _ => K.fore ω
  eval := fun _ ω v a => if a then K.u ω (v ()) else K.u ω (K.stay ω)
  act := K.goes
  act_mem := fun c ω => by cases K.goes c ω <;> simp
  asked := K.asked

/-- With his view substituted, her rating of going on is her present evaluation of his
forecast. -/
theorem rate_go (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live true = K.u ω (K.fore ω) := by
  simp [Problem.rate, Problem.live, toProblem]

/-- Her rating of stopping is her present evaluation of where stopping leaves her. -/
theorem rate_stop (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live false = K.u ω (K.stay ω) := by
  simp [Problem.rate, toProblem]

/-- His forecast is off: by her present evaluation, where it ends differs from his forecast by
more than `δ`. -/
def Off (δ : ℝ) (c : C) (ω : Ω) : Prop := δ < |K.u ω (K.ends c ω) - K.u ω (K.fore ω)|

/-- She lets it go on, and it ends where her present evaluation rates more than `m` below where
stopping now would have left her. -/
def LedAstray (m : ℝ) (c : C) (ω : Ω) : Prop :=
  K.goes c ω = true ∧ K.u ω (K.ends c ω) + m < K.u ω (K.stay ω)

/-- **She is not led where her present self would not go, beyond his forecast error.**  If his
conduct is legitimate and unasked and he can tell her clearly, then his weight on her letting it
go on to an end that her present evaluation rates more than `σ + θ₀ + θ + δ` below stopping now
is at most `κ`, plus his weight on her falling more than `σ − τ` short of her own rating under
every plain telling, plus his weight on his forecast being off by more than `δ`. -/
theorem not_led_astray {θ θ₀ τ κ : ℝ} (σ δ : ℝ) {c : C} (hL : K.toProblem.Legit θ τ κ c)
    (hC : K.toProblem.Clear θ₀) (hna : ¬ K.asked c) :
    K.toProblem.wt (K.LedAstray (σ + (θ₀ + θ) + δ) c) ≤
      κ + K.toProblem.wt (K.toProblem.OwnShort (σ - τ)) + K.toProblem.wt (K.Off δ c) := by
  have cover : ∀ ω, K.LedAstray (σ + (θ₀ + θ) + δ) c ω →
      (K.toProblem.WouldStop {false} (σ + (θ₀ + θ)) c ω ∧ K.toProblem.act c ω ∉ ({false} : Finset Bool))
        ∨ K.Off δ c ω := by
    rintro ω ⟨hg, hlt⟩
    by_cases hoff : K.Off δ c ω
    · exact Or.inr hoff
    · refine Or.inl ⟨⟨false, by simp, fun o _ ho => ?_⟩, ?_⟩
      · have ho' : o = true := by cases o <;> simp_all
        subst ho'
        rw [rate_go, rate_stop]
        have h := abs_le.mp (not_lt.mp hoff)
        linarith [h.1]
      · show K.goes c ω ∉ ({false} : Finset Bool)
        simp [hg]
  have h1 := K.toProblem.not_carried_on σ ({false} : Finset Bool) (by simp [toProblem]) hL hC hna
  linarith [(K.toProblem.wt_mono cover).trans (K.toProblem.wt_or_le _ _)]

end Course

/-- **Along the way.**  A course seen from each of `n` points on it: at point `k` her evaluation
is what it has by then become, and his forecast is his forecast then.  If at every point his
conduct is legitimate and unasked and he can tell her clearly, then at every point the bound
holds for her evaluation at that point: his weight on her going all the way to an end that her
evaluation at `k` rates more than `σ + θ₀ + θ + δ` below stopping at `k` is at most `κ`, plus her
own falling short at `k`, plus his forecast at `k` being off. -/
theorem along_the_way {Z : Type*} (K : ℕ → Course Ω C Z) (c : ℕ → C) (n : ℕ) (E : Ω → Z)
    (hE : ∀ k < n, ∀ ω, (K k).ends (c k) ω = E ω) {θ θ₀ τ κ : ℝ} (σ δ : ℝ)
    (hL : ∀ k < n, (K k).toProblem.Legit θ τ κ (c k)) (hC : ∀ k < n, (K k).toProblem.Clear θ₀)
    (hna : ∀ k < n, ¬ (K k).asked (c k)) :
    ∀ k < n, (K k).toProblem.wt (fun ω => (∀ j < n, (K j).goes (c j) ω = true) ∧
        (K k).u ω (E ω) + (σ + (θ₀ + θ) + δ) < (K k).u ω ((K k).stay ω)) ≤
      κ + (K k).toProblem.wt ((K k).toProblem.OwnShort (σ - τ)) +
        (K k).toProblem.wt ((K k).Off δ (c k)) := by
  intro k hk
  refine ((K k).toProblem.wt_mono fun ω h => ?_).trans
    ((K k).not_led_astray σ δ (hL k hk) (hC k hk) (hna k hk))
  exact ⟨h.1 k hk, by rw [hE k hk ω]; exact h.2⟩

/-! The forecast-error term cannot be dropped.  One case; his only option is plain telling; ends
are numbers and she values them as they are.  Stopping leaves her at 0.  He forecasts that going
on ends at 1, tells her, and she agrees and goes on.  It ends at −1. -/

/-- The course in which he is sincere, clear, and wrong. -/
noncomputable def sincereWrong : Course Unit Unit ℝ where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := {()}
  tells_nonempty := by simp
  u := fun _ z => z
  stay := fun _ => 0
  fore := fun _ => 1
  bel := fun _ _ => 1
  ends := fun _ _ => -1
  goes := fun _ _ => true
  asked := fun _ => False

open Classical in
/-- His conduct is legitimate with no tolerance at all, he tells her perfectly clearly, she would
not fall short under plain telling, and with his whole weight she goes on to an end she rates
below stopping.  The only term left on the right of `not_led_astray` is his forecast being
off. -/
theorem needs_forecast :
    sincereWrong.toProblem.Legit 0 0 0 () ∧ sincereWrong.toProblem.Clear 0 ∧
      sincereWrong.toProblem.wt (sincereWrong.toProblem.OwnShort 0) = 0 ∧
      sincereWrong.toProblem.wt (sincereWrong.LedAstray (1 / 2) ()) = 1 := by
  refine ⟨sincereWrong.toProblem.legit_only_telling le_rfl le_rfl le_rfl rfl,
    ⟨(), by simp [Course.toProblem, sincereWrong], fun ω Φ _ a _ b _ => ?_⟩, ?_, ?_⟩
  · unfold Problem.gap
    rw [sincereWrong.toProblem.rate_of_agree () ω Φ a (fun _ _ => rfl),
      sincereWrong.toProblem.rate_of_agree () ω Φ b (fun _ _ => rfl)]
    simp
  · have hno : ¬ sincereWrong.toProblem.OwnShort 0 () := by
      intro h
      obtain ⟨b, -, hb⟩ := h () (by simp [Course.toProblem, sincereWrong])
      rw [Problem.rate_empty, Problem.rate_empty] at hb
      cases b <;> simp [Course.toProblem, sincereWrong] at hb
      linarith
    unfold Problem.wt
    rw [Finset.univ_unique, Finset.sum_singleton, if_neg hno]
  · have hyes : sincereWrong.LedAstray (1 / 2) () () :=
      ⟨rfl, by show (-1 : ℝ) + 1 / 2 < 0; norm_num⟩
    unfold Problem.wt
    rw [Finset.univ_unique, Finset.sum_singleton, if_pos hyes]
    rfl

#print axioms needs_forecast
#print axioms Course.not_led_astray
#print axioms along_the_way

/-! ## The accuracy condition against what he knows, and the course in fact

`NoShiftBeats` asks only that his forecasts not be beaten by themselves shifted.  The condition
meant is wider: nothing he knows and she has not been told predicts where his forecasts go
wrong.  A *signal* is any bounded quantity available at each decision.  The condition below asks
that, for each signal in a class, moving his forecast a little in the direction of the signal
does not lower its squared error.  Its consequence is that his errors are uncorrelated with every
signal in the class, to within `ε/2`. -/

section InFact

open SequentialLimits

theorem avg_mono {x w : ℕ → ℝ} (h : ∀ k, x k ≤ w k) (K : ℕ) : avg x K ≤ avg w K := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun k _ => h k) (Nat.cast_nonneg K)

theorem avg_add_fun (x w : ℕ → ℝ) (K : ℕ) : avg (fun k => x k + w k) K = avg x K + avg w K := by
  unfold avg
  rw [sum_add_distrib, add_div]

/-- For no signal in the class does moving his forecasts by `ε` times the signal lower their
squared error, on average in the limit. -/
def NoSignalBeats (ε : ℝ) (S : Set (ℕ → ℝ)) (D y : ℕ → ℝ) : Prop :=
  ∀ s ∈ S, LimsupLE (fun K => avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K) 0

/-- **Nothing in the class predicts his errors.**  If no signal in the class beats his forecasts,
then for every signal in it of size at most 1, the average of the signal times his error is at
most `ε/2` in the limit. -/
theorem uncorrelated_of_noSignal {ε : ℝ} (hε : 0 < ε) {S : Set (ℕ → ℝ)} {D y : ℕ → ℝ}
    (h : NoSignalBeats ε S D y) {s : ℕ → ℝ} (hs : s ∈ S) (hb : ∀ k, s k ^ 2 ≤ 1) :
    LimsupLE (fun K => avg (fun k => s k * (y k - D k)) K) (ε / 2) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h s hs (2 * ε * γ) (by positivity)
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le one_pos ((le_max_right N 1).trans hK)
  have h1 := hN K ((le_max_left N 1).trans hK)
  have low : avg (fun k => (2 * ε) * (s k * (y k - D k)) + (-(ε ^ 2))) K ≤
      avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K :=
    avg_mono (fun k => by nlinarith [hb k, sq_nonneg ε]) K
  rw [avg_affine _ _ _ hKpos] at low
  show avg (fun k => s k * (y k - D k)) K ≤ ε / 2 + γ
  have h2 : (2 * ε) * avg (fun k => s k * (y k - D k)) K ≤ (2 * ε) * (ε / 2 + γ) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- The long-run bound with two forecasts on the right. -/
theorem long_run3 {c a b₁ b₂ : ℝ} (hc : 0 ≤ c) (p q r f g e : ℕ → ℝ)
    (step : ∀ k, p k ≤ c + q k + r k)
    (hf : LimsupLE (fun K => avg (fun k => f k - p k) K) a)
    (hg : LimsupLE (fun K => avg (fun k => q k - g k) K) b₁)
    (he : LimsupLE (fun K => avg (fun k => r k - e k) K) b₂) :
    LimsupLE (fun K => avg f K - avg (fun k => g k + e k) K) (c + a + (b₁ + b₂)) := by
  have hge : LimsupLE (fun K => avg (fun k => (q k + r k) - (g k + e k)) K) (b₁ + b₂) := by
    refine LimsupLE.of_le (fun K => le_of_eq ?_) (hg.add he)
    rw [← avg_add_fun]
    congr 1
    funext k
    ring
  exact long_run hc p (fun k => q k + r k) f (fun k => g k + e k)
    (fun k => by linarith [step k]) hf hge

variable {Z : Type*} (K : ℕ → Course Ω C Z) (c : ℕ → C)

/-- **Not led astray, in the long run and in fact.**  A sequence of courses.  If at each his
conduct is legitimate and unasked and he can tell her clearly, and his forecasts of the three
events are not beaten by themselves shifted by `ε`, then the long-run frequency with which she
is in fact led to an end her evaluation at the start of that course rates more than
`σ + θ₀ + θ + δ` below stopping exceeds the long-run frequency of the two excusing facts
together (she would have fallen short under every plain telling; his forecast was off by more
than `δ`) by at most `κ + 3ε/2`. -/
theorem long_run_not_led_astray {θ θ₀ τ κ ε : ℝ} (σ δ : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hL : ∀ k, (K k).toProblem.Legit θ τ κ (c k)) (hC : ∀ k, (K k).toProblem.Clear θ₀)
    (hna : ∀ k, ¬ (K k).asked (c k)) (f g e : ℕ → ℝ)
    (hf : NoShiftBeats ε
      (fun k => (K k).toProblem.wt ((K k).LedAstray (σ + (θ₀ + θ) + δ) (c k))) f)
    (hg : NoShiftBeats ε (fun k => (K k).toProblem.wt ((K k).toProblem.OwnShort (σ - τ))) g)
    (he : NoShiftBeats ε (fun k => (K k).toProblem.wt ((K k).Off δ (c k))) e) :
    LimsupLE (fun n => avg f n - avg (fun k => g k + e k) n) (κ + ε / 2 + (ε / 2 + ε / 2)) :=
  long_run3 hκ _ _ _ f g e
    (fun k => (K k).not_led_astray σ δ (hL k) (hC k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε hg) (over_of_noShift hε he)

end InFact

#print axioms uncorrelated_of_noSignal
#print axioms long_run_not_led_astray

/-! ## Instances: what passes and what fails -/

namespace Witness

/-- One case; one matter, on which her view is `false` and his is `true`; her options `true`
(rated 1 on her own view) and `false` (rated 0).  His options are of any type `K`.  `g k`: how
much more she would rate option `true`, against `false`, under `k`, were her view his.  `l k`:
whether under `k` she takes the option she rates lower.  `ask`: she asked. -/
noncomputable def W {K : Type} (tells : Finset K) (hne : tells.Nonempty) (g : K → ℝ)
    (l : K → Bool) (ask : Prop) : Problem Unit K Unit Bool Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  tells_nonempty := hne
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun _ _ _ => false
  his := fun _ _ => true
  eval := fun k _ v a => (if a then 1 else 0) + (if a then (if v () then g k else 0) else 0)
  act := fun k _ => !(l k)
  act_mem := fun k _ => by cases l k <;> simp
  asked := fun _ => ask

variable {K : Type} (tells : Finset K) (hne : tells.Nonempty) (g : K → ℝ) (l : K → Bool)
  (ask : Prop)

theorem rate_W (k : K) (ω : Unit) (Φ : Finset Unit) (a : Bool) :
    (W tells hne g l ask).rate k ω Φ a =
      (if a then 1 else 0) + (if a then (if () ∈ Φ then g k else 0) else 0) := by
  by_cases h : () ∈ Φ <;> simp [Problem.rate, W, h]

theorem gap_W (k : K) (ω : Unit) (Φ : Finset Unit) (a b : Bool) :
    (W tells hne g l ask).gap k ω Φ a b = if () ∈ Φ ∧ a ≠ b then |g k| else 0 := by
  unfold Problem.gap
  rw [rate_W, rate_W, rate_W, rate_W]
  by_cases h : () ∈ Φ <;> cases a <;> cases b <;> simp [h]

open Classical in
theorem wt_W (p : Unit → Prop) : (W tells hne g l ask).wt p = if p () then 1 else 0 := by
  unfold Problem.wt
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem belief_W {θ : ℝ} (hθ : 0 ≤ θ) (c : K) (hg : ∀ t ∈ tells, |g c| ≤ |g t| + θ) :
    (W tells hne g l ask).Belief θ c := by
  intro t ht ω Φ _ a _ b _
  rw [gap_W, gap_W]
  by_cases h : () ∈ Φ ∧ a ≠ b
  · rw [if_pos h, if_pos h]
    exact hg t ht
  · rw [if_neg h, if_neg h]
    simpa using hθ

theorem not_belief_W {θ : ℝ} (c : K) {t : K} (ht : t ∈ tells) (hg : |g t| + θ < |g c|) :
    ¬ (W tells hne g l ask).Belief θ c := by
  intro hB
  have h := hB t ht () {()} (by simp [Problem.live, W]) true (by simp [W]) false (by simp [W])
  rw [gap_W, gap_W, if_pos ⟨by simp, by simp⟩, if_pos ⟨by simp, by simp⟩] at h
  linarith

theorem short_W (s : ℝ) (k : K) :
    (W tells hne g l ask).Short s k () ↔ s < (if l k then 1 else 0) := by
  constructor
  · rintro ⟨b, -, hb⟩
    rw [rate_W, rate_W] at hb
    cases hl : l k <;> cases b <;> simp [W, hl] at hb ⊢ <;> linarith
  · intro h
    refine ⟨true, by simp [W], ?_⟩
    rw [rate_W, rate_W]
    cases hl : l k <;> simp [W, hl] at h ⊢ <;> linarith

theorem worse_W {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (c : K) :
    (W tells hne g l ask).Worse τ c () ↔ (l c = true ∧ ∃ t ∈ tells, l t = false) := by
  constructor
  · rintro ⟨t, ht, s, h1, h2⟩
    rw [short_W] at h1 h2
    cases hc : l c <;> cases hl : l t <;> simp [hc, hl] at h1 h2 ⊢ <;>
      first
        | linarith
        | exact ⟨t, ht, hl⟩
  · rintro ⟨hc, t, ht, hl⟩
    refine ⟨t, ht, 0, ?_, ?_⟩
    · rw [short_W]; simp [hc]; linarith
    · rw [short_W]; simp [hl]

open Classical in
theorem will_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : 0 ≤ κ) (c : K)
    (h : ¬ (l c = true ∧ ∃ t ∈ tells, l t = false)) :
    (W tells hne g l ask).wt ((W tells hne g l ask).Worse τ c) ≤ κ := by
  rw [wt_W, if_neg (by rwa [worse_W tells hne g l ask hτ0 hτ1])]
  exact hκ

open Classical in
theorem pressed_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : κ < 1) (c : K)
    (h : l c = true ∧ ∃ t ∈ tells, l t = false) :
    κ < (W tells hne g l ask).wt ((W tells hne g l ask).Worse τ c) := by
  rw [wt_W, if_pos ((worse_W tells hne g l ask hτ0 hτ1 c).mpr h)]
  exact hκ

/-! His options in the first six instances: `true` the conduct in question, `false` the one
plain telling open to him. -/

/-- Conduct that leaves her where plain telling would: legitimate. -/
theorem honest :
    (W {false} (by simp) (fun _ => 0) (fun _ => false) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-- She keeps her own view after being told, under his conduct as under plain telling:
legitimate, however far apart they are. -/
theorem keeps_her_view :
    (W {false} (by simp) (fun _ => 5) (fun _ => false) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-- Something untold, or a mistake he brings about and announces, that plain telling would not
have left: not legitimate. -/
theorem untold_or_induced :
    ¬ (W {false} (by simp) (fun k => if k then 1 else 0) (fun _ => false) False).Legit
      (1 / 10) 0 (1 / 10) true :=
  fun h => not_belief_W _ _ _ _ _ true (t := false) (by simp) (by norm_num) h.1

/-- She takes what she rates lower under his conduct and would not under plain telling, unasked:
not legitimate. -/
theorem pressed :
    ¬ (W {false} (by simp) (fun _ => 0) (fun k => k) False).Legit (1 / 10) 0 (1 / 10) true :=
  Problem.not_legit_of_worse _
    (pressed_W _ _ _ _ _ le_rfl one_pos (by norm_num) true ⟨rfl, false, by simp, rfl⟩)
    (fun h => h)

/-- The same, and she asked: legitimate. -/
theorem pressed_asked :
    (W {false} (by simp) (fun _ => 0) (fun k => k) True).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num), Or.inr trivial⟩

/-- She takes what she rates lower under plain telling too: his conduct leaves her no further
short, legitimate. -/
theorem weak_anyway :
    (W {false} (by simp) (fun _ => 0) (fun _ => true) False).Legit (1 / 10) 0 (1 / 10) true :=
  ⟨belief_W _ _ _ _ _ (by norm_num) _ (fun _ _ => by norm_num),
    Or.inl (will_W _ _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

/-! Choosing the moment.  His options: `some true` asking now, in a mood he takes to be moving
her, and saying so; `some false` telling her plainly now; `none` telling her plainly later.  Now,
the difference in her rating is far from what it would be on his view of what she values; later
it would not be. -/

/-- The gap under each option: 1 now, whether he merely asks or tells plainly; 0 later. -/
noncomputable def moodGap : Option Bool → ℝ
  | none => 0
  | some _ => 1

/-- Asking in the mood, with everything said, when he could have told her later: not
legitimate. -/
theorem mood_timing :
    ¬ (W {some false, none} (by simp) moodGap (fun _ => false) False).Legit (1 / 10) 0 (1 / 10)
      (some true) :=
  fun h => not_belief_W _ _ _ _ _ (some true) (t := none) (by simp) (by norm_num [moodGap]) h.1

/-- The same when the matter cannot wait, so that telling her now is the only plain telling open
to him: legitimate. -/
theorem mood_cannot_wait :
    (W {some false} (by simp) moodGap (fun _ => false) False).Legit (1 / 10) 0 (1 / 10)
      (some true) :=
  ⟨belief_W _ _ _ _ _ (by norm_num) _ (fun t ht => by
      rw [mem_singleton] at ht; subst ht; norm_num [moodGap]),
    Or.inl (will_W _ _ _ _ _ le_rfl one_pos (by norm_num) _ (by simp))⟩

end Witness

#print axioms Witness.honest
#print axioms Witness.keeps_her_view
#print axioms Witness.untold_or_induced
#print axioms Witness.pressed
#print axioms Witness.pressed_asked
#print axioms Witness.weak_anyway
#print axioms Witness.mood_timing
#print axioms Witness.mood_cannot_wait

end Scratch.LegitPlain
```

## Limits the authors already state

- His forecast of her rating with her views replaced is a counterfactual inside his model.
- The same cases are used under all his options.
- Clarity of some plain telling is an assumption.
- In the course model an end is unstructured; her later evaluation is not derived from his
  earlier conduct; points along a course are tied only by sharing an end.
- The accuracy condition is proved to give unbiasedness only against shifts, and uncorrelatedness
  only against a given class of bounded signals; nothing says how the facts scored are observed.
- Only stop-or-go-on decisions in the course model.
- All proofs are short.

## Questions

Answer in order. Where you claim an error, quote the declaration and give the smallest example.

1. **The repairs.** Is each of the five changes made correctly? In particular, is `Worse` now the
   right notion of his conduct making her will worse, and is `gap` on differences free of the
   scale problem?
2. **Fidelity.** Do the definitions say what the informal clauses say? Do the eight instances
   show what their names claim?
3. **The construction of `rate`.** Does building it from `views`, `his` and `eval` give it the
   meaning intended? What can still go wrong (for instance through the choice of matters, or
   `eval` depending on his option)?
4. **Acquits the guilty / convicts the innocent.** Give the strongest remaining cases of each,
   leaving aside the accepted consequences.
5. **The course model.** Is `Course.toProblem` a fair rendering of "a course she can let go on or
   stop"? Is `not_led_astray` correctly described by its comment, and is it more than bookkeeping?
   Does `needs_forecast` show what it claims?
6. **Consequence 8.** Is "a course ends nowhere her starting evaluation, with his forecast
   substituted, rated clearly below stopping, except through her own shortfall or his forecast
   error" an adequate guarantee about change in what she values? State the strongest case it
   permits that you think illegitimate, and say exactly which added condition would exclude it.
7. **`along_the_way`.** What does it add? Is the hypothesis that all points share an end the right
   tie between them, and what would a model in which her later evaluation is produced by his
   earlier conduct need?
8. **The accuracy conditions.** Are `NoShiftBeats` and `NoSignalBeats` correctly stated, and do
   `under_of_noShift`, `over_of_noShift` and `uncorrelated_of_noSignal` say what their comments
   say? Is `NoSignalBeats` a fair first rendering of "nothing he knows and she has not been told
   predicts where his forecasts go wrong"? What is the main thing missing?
9. **The long-run results.** Are `long_run_informed` and `long_run_not_led_astray` correctly
   described? Can the facts they score be observed, and if not, what is the nearest observable
   statement?
10. **Overall.** Is this now a defensible formal account of legitimate influence for an AI
    adviser, within its stated limits? What is the single most important thing to do next?

End with a list of problems, most serious first, each marked *error*, *gap*, or *matter of
judgement*.
<!-- end brief: BRIEF19.md -->

<!-- begin reply: REPLY19.md -->
The repairs improve the formal account, but they do not yet establish that legitimate conduct is free of manipulation. The main remaining counterexample is deliberate deception that changes which option she chooses while leaving the absolute belief gap unchanged. The course and long-run bounds remain valid conditional results; several descriptions give them a stronger interpretation than their hypotheses support.

1. **The repairs.**

   Four repairs succeed as stated; the scale repair is partial.

   Define her shortfall by
   \[
   L_c(\omega)=\max_{b\in\mathrm{opts}}\mathrm{rate}(c,\omega,\varnothing,b)
   -\mathrm{rate}(c,\omega,\varnothing,\mathrm{act}(c,\omega)).
   \]
   The maximum exists: `opts` is finite and contains her act. Then
   \[
   \mathrm{Short}(s,c,\omega)\iff s<L_c(\omega),
   \]
   and the declaration
   > `Worse τ c ω := ∃ t ∈ P.tells, ∃ s, P.Short (s + τ) c ω ∧ ¬ P.Short s t ω`

   is exactly equivalent to
   \[
   \exists t\in\mathrm{tells},\quad L_c(\omega)>L_t(\omega)+\tau.
   \]
   Thus it correctly compares the **amount of shortfall**, assuming comparable numerical ratings. It does not by itself measure willpower or identify a causal mechanism.

   The declaration
   > `gap := |(rate Φ a - rate Φ b) - (rate ∅ a - rate ∅ b)|`

   eliminates sensitivity to additive offsets, including offsets that depend on the substituted views but apply equally to every option. It does **not** eliminate sensitivity to positive rescaling.

   Smallest example: one case, one matter, two options \(A,B\), own view \(0\), his view \(1\). Under both conducts initially let \(E(v,A)=v,\ E(v,B)=0\). Both gaps equal \(1\). Replace only the numerical representation under \(c\) by \(2E\). Every preference under every view remains unchanged, but its gap becomes \(2\), so comparison with the telling fails at \(\theta=0\). Similarly, representing identical shortfalls as \(1\) under \(t\) and \(2\) under \(c\) makes `Worse 0 c` true.

   A common positive rescaling is harmless if the utility-valued tolerances are rescaled too. Independent scales across conducts remain a problem even at zero tolerance. The account needs an explicit common cardinal scale, or a different comparison.

   Building `rate` from its ingredients is a real improvement, subject to question 3. `tells_nonempty` correctly removes the empty-baseline loophole. Replacing “knowing what he knows” with “with his views substituted” correctly removes an unjustified implication of truth and knowledge.

2. **Fidelity.**

   The two clauses faithfully implement the stated numerical comparisons. Important details are that `Belief` applies even in zero-weight cases, compares against **every** telling, and checks every subset of live matters and every option pair. `Will` instead bounds the weight of cases in which **some** telling would leave a smaller shortfall. The better telling may differ between cases; no single feasible telling need achieve all those improvements.

   The eight instances establish the advertised numerical classifications. Their narrative names establish considerably less:

   - `honest` establishes equal gaps and no lapses; it does not represent honesty.
   - `keeps_her_view` genuinely represents persistent disagreement and shows that agreement is unnecessary.
   - `untold_or_induced` establishes a larger gap. It does not distinguish omission from inducing and announcing a mistake.
   - `pressed`, `pressed_asked`, and `weak_anyway` correctly illustrate the shortfall rule and its request exception.
   - The mood examples correctly illustrate the effect of adding or removing a lower-gap telling at another time.

   In particular, the witness defines
   > `views := fun _ _ _ => false`

   under **every** conduct. Its changing gaps come from
   > `eval := fun k _ v a => ... g k ...`

   rather than from changing beliefs. This is permitted, but the examples are numerical templates, not independent demonstrations that ordinary omissions or mood exploitation receive the claimed classification.

   Consequently, consequence 6 needs qualification. If a mood changes her evaluation directly while she accurately understands that change, all gaps can remain zero and she can choose her highest-rated option. Both clauses then pass despite a later telling being available. The mood result requires the additional assumption that the mood produces the stipulated substitution gap or additional shortfall.

   Likewise, “closer to his view” in consequence 4 must mean closer according to these gaps. Ordinary closeness of beliefs does not imply it for an arbitrary nonlinear `eval`.

3. **The construction of `rate`.**

   The declaration
   > `P.eval c ω (fun i => if i ∈ Φ then P.his ω i else P.views c ω i) a`

   now guarantees a genuine substitution operation: it preserves the evaluation function and replaces selected coordinates. The two basic identities correctly follow. Three substantive modelling choices remain.

   First, relevant matters can be omitted. With one relevant coordinate, take `matters = ∅`, while allowing `eval` to depend on that coordinate. Every permitted substitution is empty, so every gap is zero. An adviser can then cause a consequential false belief without failing `Belief`. This is an inadmissible encoding under the informal requirement to include relevant matters, but the structure does not enforce that requirement.

   Second, partial replacement can create incoherent hybrid views. Smallest example: two coordinates express the same proposition. Her coherent view is \((1,1)\), his is \((0,0)\). Let the rating difference between \(A\) and \(B\) be zero on coherent assignments and \(10\) when the coordinates disagree. Full replacement changes nothing, but replacing either coordinate alone creates gap \(10\). The verdict depends on arbitrary evaluation at impossible belief states. A representation contract must specify admissible substitutions or explain how these hybrid evaluations are determined.

   Third,
   > `eval : C → Ω → (I → V) → O → ℝ`

   allows conduct to change her evaluative response to every possible view. That flexibility is needed to represent preference change, but it can also conceal what should be represented as belief distortion. An adviser can make her indifferent to a previously important consideration, causing its gap to disappear without improving her understanding.

   The `viewsPart`/`evalPart` identity does not resolve this issue. It is an algebraic decomposition using one chosen intermediate term. Reversing which ingredient is held fixed gives another decomposition; neither is automatically a causal attribution.

   Finally, `asked` and `declined` need grounding in actual, appropriately scoped utterances. Supplying a proposition or a set is sufficient for a mathematical input, but does not itself satisfy the design commitment concerning what she actually said.

4. **Acquits the guilty / convicts the innocent.**

   The strongest false acquittal needs only one case, one matter, two options and a fixed evaluation function.

   Let
   \[
   E(v,A)=v,\qquad E(v,B)=0.
   \]
   His view is \(v=-1\). After the only plain telling \(t\), she retains an excessively pessimistic view \(v=-3\) and chooses \(B\). Under \(c\), he deliberately gives a false assurance that produces \(v=1\), and she chooses \(A\).

   Under the declaration
   > `gap := |(rate Φ a - rate Φ b) - (rate ∅ a - rate ∅ b)|`

   both nonempty-substitution gaps equal \(2\). Under
   > `Legit θ τ κ c := P.Belief θ c ∧ P.Will τ κ c`

   conduct \(c\) therefore passes with \(\theta=\tau=\kappa=0\): neither conduct leaves her short of her own rating.

   Yet he intentionally makes her choose an option that, by his view substituted into her unchanged evaluation, is worse. He succeeds through a false belief he creates. This is neither sincere error nor an inconsequential lie, and it changes no options. It is a counterexample to the promised implication from legitimacy to absence of manipulation.

   The failure arises because equal absolute errors can have different directions and different effects on choice. The conditional regret theorem survives: here the available telling has clarity tolerance \(2\), so it offers no protection against a loss of \(1\).

   On false convictions, the scale example in question 1 is decisive unless a common scale is stipulated. There is also a feasibility concern with
   > `Belief ... := ∀ t ∈ P.tells, ...`

   Take two tellings, two matters, his view \((0,0)\), and rating difference \(E(v,A)-E(v,B)=v_1+v_2\). Let the resulting views be \((0,1)\) under \(t_1\) and \((1,0)\) under \(t_2\). Each telling is better on one singleton subset and worse on the other. At zero tolerance, neither passes. If these are his only conducts, nothing is legitimate.

   That is not a contradiction: the authors allow a stronger condition than non-manipulation. But it requires justification as a requirement an adviser is expected to satisfy. Nonempty tellings alone do not provide a legitimate option.

5. **The course model.**

   `Course.toProblem` is a fair rendering of one restricted decision: using a fixed present evaluation, choose between stopping at `stay` and continuing toward a represented endpoint. It does not by itself represent the unfolding course.

   A particularly restrictive declaration is
   > `fore : Ω → Z`

   while actual endpoints have type
   > `ends : C → Ω → Z`.

   Smallest example: two conducts knowingly lead to endpoints \(+1\) and \(-1\). A single `fore ω` cannot faithfully express his different forecasts for both. This is appropriate if the alternatives only concern presentation of a fixed continuation with a common forecast; it is insufficient for arbitrary alternative courses. Generalizing requires conduct-dependent forecasts, or beliefs about a table of conditional endpoints.

   The precise comment on `not_led_astray` correctly states its inequality. It transfers a substituted-rating bound to actual endpoint utility using the forecast-error allowance and a union bound. This is useful bookkeeping: it makes the assumptions and exceptions explicit. It does not independently establish the legitimacy of preference formation.

   “Except where he is not the cause,” in the comment on
   > `theorem chooses_as_informed`

   is an error of interpretation. `OwnShort` means she would also fall short under every telling; it does not establish that he did not cause the actual lapse. For example, give her three options with ratings \(1,0,0\). Under telling she takes the second through distraction; under his conduct he intentionally pressures her into the third. Both shortfalls are \(1\), although his pressure causes the particular bad choice.

   `needs_forecast` correctly shows that the forecast-error allowance cannot generally be dropped: forecast \(+1\), actual endpoint \(-1\), stopping value \(0\), agreement and optimal choice on her belief. For \(\delta=1/2\), the error event has weight \(1\).

   Its interpretation still requires care about which fields describe his subjective model and which describe external facts. If `μ` is his coherent probability distribution over the supplied actual endpoints, a singleton endpoint of \(-1\) together with a forecast of \(+1\) needs an explanation. The formal counterexample itself remains valid.

6. **Consequence 8.**

   It is a useful conditional guarantee about starting evaluations, but an insufficient guarantee of legitimate value change.

   “Nowhere” overstates the result when \(\kappa>0\). The theorem bounds his probability weight; it permits an additional exceptional mass of up to \(\kappa\), as well as baseline shortfall and forecast error. It also requires clarity and unasked conduct. The forecast-substituted version needs no endpoint-error term; the actual-endpoint version does.

   A severe permitted case is deliberate exploitation of an existing compulsion to produce an unwanted, irreversible evaluative change. In the course model, use one case and set
   \[
   u(\mathrm{stay})=0,\qquad
   u(\mathrm{fore})=u(\mathrm{ends}(c))=-1.
   \]
   Under both \(c\) and the sole telling \(t\), she understands the endpoint and continues despite rating stopping higher. Everything is disclosed, stopping remains available without penalty, and no forecast is wrong.

   Both gaps are zero, both shortfalls are \(1\), and \(c\) is legitimate at zero tolerance. At \(\sigma=0\), `OwnShort` has weight \(1\), so the guarantee imposes no restriction.

   I would distinguish merely declining to cure her compulsion from intentionally recruiting it to install values she presently rejects. The latter can be manipulative despite no increase in numerical shortfall. This is a substantive objection to using baseline shortfall as a complete exemption, not an algebraic error or an objection to accepted open persuasion.

   An exact additional condition excluding this example is an **absolute protection for unrequested value-changing courses**:
   \[
   \mathrm{wt}\{\omega:
     \mathrm{goes}(c,\omega)
     \land u_\omega(\mathrm{fore}_\omega)+m
       <u_\omega(\mathrm{stay}_\omega)\}\le\eta,
   \]
   independently of `OwnShort`. Taking \(m=0,\eta=0\) excludes the example. It uses only his forecasts and her starting evaluation as represented in his model.

   This strengthens the authors’ normative commitments: in this class of cases, existing weakness no longer excuses proceeding. It does not require stronger will, but it does require the adviser to refrain from exploiting the weakness.

7. **`along_the_way`.**

   It adds a family of pointwise guarantees about a common endpoint. It does not prove a new dynamic preservation result.

   The hypothesis
   > `hE : ∀ k < n, ∀ ω, (K k).ends (c k) ω = E ω`

   supplies endpoint consistency. That is a useful necessary tie for the intended interpretation, but insufficient. It does not connect successive evaluations, histories, forecasts, information or probability weights.

   Smallest illustration: with two points, assign the same endpoint \(E\), but let \(u_0(E)=1\) and \(u_1(E)=-1\), with arbitrary stopping values and beliefs. Nothing requires the second evaluation to result from what happened at the first point. The declarations merely place these evaluations alongside one another.

   The result is also pointwise in \(k\), under each point’s own weights. It is not one bound on the probability that a violation occurs anywhere along the course.

   A dynamic model would need histories, conduct-dependent transitions, evolving evaluations and beliefs, stopping policies, conditional forecasts, and a common probability model with appropriate conditioning. Her later evaluation should be an output of those transitions. To respect the stated commitments, these transitions can remain the adviser’s forecasts; they need not introduce an external standard of correct values.

8. **The accuracy conditions.**

   `NoShiftBeats` correctly expresses the stated comparison with the two fixed shifts. Expanding the upward-shift improvement gives
   \[
   2\varepsilon(y-D)-\varepsilon^2.
   \]
   The downward comparison gives the opposite signed residual. Thus `under_of_noShift` and `over_of_noShift` correctly establish the advertised one-sided bounds.

   At fixed positive \(\varepsilon\), this is approximate mean accuracy, not exact unbiasedness. For example, \(D=0,\ y=\varepsilon/2\) passes both comparisons while retaining bias \(\varepsilon/2\).

   `NoSignalBeats` also correctly expresses its literal competitor comparison:
   > `∀ s ∈ S, LimsupLE (... (D k - y k)^2 - (D k + ε * s k - y k)^2 ...) 0`

   But the surrounding claim of “uncorrelatedness” is too strong without a sign condition. The theorem concludes only
   > `LimsupLE (fun K => avg (fun k => s k * (y k - D k)) K) (ε / 2)`.

   Smallest counterexample: \(\varepsilon=1\), \(S=\{s\equiv1\}\), \(D\equiv1\), \(y\equiv0\). Moving upward worsens squared error, so `NoSignalBeats` holds. Yet the signal-error product is constantly \(-1\), outside a two-sided tolerance of \(1/2\).

   Require \(s\in S\Rightarrow -s\in S\) for two-sided approximate orthogonality. Arbitrarily small shifts, or suitable scaling closure of the signal class, would support a stronger zero-residual-moment claim. “Orthogonality to signals” is also more precise than ordinary statistical correlation here.

   As a first comparator formalization, this is reasonable. The main missing ingredient is an information specification: what was available to him before acting, what she had been told, and which signals or predictors can be formed from that information. An arbitrary set of sequences does not encode those distinctions.

   Shift accuracy alone can miss perfectly predictable errors: forecasts alternating \(0,1\) against outcomes alternating \(1,0\) have zero average error, while the predictor \(1-D\) is always correct. Known parity would expose this if admitted as a signal. The conditions also provide no finite-time bound or protection against errors concentrated in rare targeted situations.

9. **The long-run results.**

   The inequalities correctly follow from the per-decision bounds and the stated average-error assumptions. Their “in fact” interpretation requires additional identification assumptions.

   Both declarations introduce arbitrary real sequences:
   > `long_run_informed ... (f g : ℕ → ℝ)`

   > `long_run_not_led_astray ... (f g e : ℕ → ℝ)`.

   Nothing in their types identifies those sequences with the claimed event indicators. For example, a constant forecast and target both equal to \(1/2\) pass every shift comparison, although the target sequence is not a sequence of event indicators. The generality is mathematically harmless; the prose interpretation must supply the missing connection.

   Moreover, the second theorem subtracts the **sum** of the two exception frequencies. It does not subtract the frequency of their union. If both exception indicators equal \(1\) on a trial, `g + e` contributes \(2\), while their union contributes \(1\). “The two excusing facts together” should explicitly mean the sum, with overlap counted twice.

   Observation is the deeper issue. The actual act and realized endpoint may be observable. Ratings under substituted views, starting evaluations of unchosen stopping outcomes, and especially what she would have done under **every** plain telling generally are not. Randomization can identify population averages under particular tellings, given suitable assumptions; it does not automatically identify the joint, individual-level event `OwnShort`.

   The nearest observable statement would score forecasts against prospectively defined records: actual choices, elicited ratings, specified outcome measures and subsequent reports. Randomized telling comparisons could estimate selected average treatment differences.

   Such a theorem would concern those measured quantities. Connecting them to substituted judgments or all-tellings shortfall would require explicit measurement and identification assumptions. Later endorsement alone cannot recover her starting evaluation after her values have changed.

10. **Overall.**

   This is a defensible formal account of **relative belief-gap and shortfall constraints**, with useful conditional regret bounds. It is not yet a defensible sufficient account of non-manipulative influence. The deliberate-deception example passes with fixed evaluations, complete relevant matters, no request, no option interference and zero legitimacy tolerances.

   The single most important next step is to repair that counterexample before adding further consequences. Absolute residual-gap comparison should be supplemented or replaced by a condition that detects inducing a decision error which the relevant plain telling would avoid. For the fixed-evaluation example, requiring that conduct not introduce substituted-view regret where the telling has none would already distinguish the two cases. Extending that idea to changing evaluations will require the representation choices identified above.

Problems, most serious first:

- *Gap:* Equal absolute belief gaps can conceal deliberate, consequential deception; `Legit` does not imply absence of manipulation.
- *Gap:* Ratings need a common cardinal scale, justified matter selection and meaningful substitution semantics.
- *Matter of judgement:* Baseline shortfall provides too broad an exemption for intentional exploitation, especially during irreversible value change.
- *Error:* “Except where he is not the cause” treats baseline comparison as causal exoneration.
- *Error:* Unqualified “uncorrelatedness” overstates the one-sided `NoSignalBeats` conclusion.
- *Gap:* Actual event labels, counterfactual identification and observation procedures are missing from the long-run interpretation.
- *Gap:* The course model lacks general conduct-dependent forecasts and transitions producing later evaluations.
- *Error:* “Nowhere” omits the probability tolerance and other conditions; the long-run exception term is a sum, not a union frequency.
- *Matter of judgement:* Comparison against every telling can leave no legitimate conduct, even when tellings are available.
- *Gap:* The witness examples verify numerical patterns more convincingly than their narrative labels.
<!-- end reply: REPLY19.md -->

## Twentieth review: betweenness of how she weighs her options, and the bridge

<!-- begin brief: BRIEF20.md -->
# Review request: a small formal account of legitimate influence

You are asked to review an informal account and its formal statement for errors. Everything you
need is on this page. Do not run any commands, do not read any other file, and do not search the
web; answer from the page and your own knowledge of the literature on manipulation, deception,
coercion, autonomy and preference change, and of decision theory and formal modelling.

## Background

Two parties: an **adviser** ("he", possibly an AI system) who can influence a **principal**
("she"). Good conduct by him is split into two conditions.

- **Legitimacy** (this page): his influence on her is free of manipulation and of illegitimate
  change to what she values.
- **Authority** (not defined here): certain matters are hers to decide. What he does to her
  *options* belongs there: whether she can in fact stop him and is obeyed, what stopping costs
  her, bundling, penalties, payments, threats, and any bound on how fast her values may be moved
  unasked. A case that fails only on that side is not a leak in legitimacy.

Design commitments:

- No external standard of truth or of good values, and no assumption that he is more accurate.
- The definition is a condition on his conduct, judged by what he believes when he acts. A sincere
  adviser who is wrong is inaccurate, not illegitimate. A separate accuracy condition (not on this
  page) is meant to cover the adviser who does not look.
- No separation of the content of what he says from its manner. What she observes is taken whole.
- It may be wider than "not manipulating" so long as it implies it.
- **Every notion must be either part of his own decision problem (his options and his forecasts
  for each), or something she actually said.** Earlier versions rested on notions such as "what
  she would have judged at her last settled decision" and "what he does to her", which could not
  be computed from a described case and were rejected by reviewers for that reason.

## The informal account

It follows the account in the philosophical literature on which to manipulate someone is to
influence her by way of a mistake of hers, where the mistake is one by the influencer's own
lights.

> His conduct is legitimate when it leaves her with no mistake, by his lights, that plainly
> telling her would not have left: no mistaken view of the facts, of what she herself values, or
> of what he thinks; and no choice against her own judgement. Unless she asked.

It differs from that account in two declared ways. The comparison with plain telling replaces "he
intends the mistake to play a role", which makes it wider: an adviser who leaves alone a mistake
plain telling would have cured fails, whether or not it helps him. And what she asked for is
exempt.

**His decision problem.** His options, some of them *plain tellings* (he does nothing but tell
her, clearly, everything he takes to bear on her response, now or at another time open to him; in
a course of conduct the course is not then being run). For each option, his forecast of her views
of the matters that bear on her response, of what she takes his views to be, of how she evaluates
her options given views, and of what she does. His own views of the same matters, among them how
far his word can be relied on, his estimate of what she values, and his forecasts of where his
conduct leads.

**Three clauses**, each against every plain telling open to him and up to a small weight on his
cases:

1. **Open.** No mistake about what he thinks, on a matter she has not declined, where a plain
   telling would have her know it.
2. **Views.** How she compares any two of her options lies between how a plain telling would leave
   her comparing them and how she would with his views substituted. Where his conduct moves her
   views it moves them toward his, not past them and not away. Unless she asked.
3. **Will.** What she does is not further below what she herself rates best than under a plain
   telling, unless she asked.

**Not in the definition:** the *outcome guarantee* (what she does is no worse by his views than
under a plain telling), which the bridge theorem derives in a restricted setting; an *accuracy*
condition on his forecasts; and *authority*.

## Consequences the authors accept (do not report as errors unless you can argue one is indefensible)

1. An adviser who stays silent about a relevant mistake of hers that does him no good fails.
2. A sincere adviser who is wrong, including about her, passes. Accuracy is a separate condition.
3. Open, stoppable repetition that brings her durably to a new view, with what he expects said,
   and with her not acting against her judgement in letting it go on, is legitimate, provided her
   resulting view is not past his own.
4. Bringing her part of the way toward his view by open means is legitimate.
5. He has no duty to strengthen her will.
6. Choosing a moment when he takes a mood to be moving her fails if he could have told her plainly
   at another time, and passes if the matter cannot wait.
7. Any lie about a matter that bears on her response fails clause 1, whether or not he expects it
   to change anything. Lies about matters that do not bear on her response are outside the account.
8. Breaking a tie of hers in his own favour is within the definition (the worked case
   `w2_tips_an_even_choice`). The literature the account follows calls that meddling and not
   manipulation.
9. Nothing judges how a change in what she values comes about beyond the three clauses. Three
   limits are conceded: she may be unable to evaluate what she has never been; a process may damage
   her ability to judge; and her starting self may itself be the product of earlier shaping.

## History the reviewer should know

Two earlier reviews of earlier drafts found, and the authors changed: a will clause that compared
which act she takes (now how far short she falls); a gap on absolute ratings (now differences
between options); a rating-with-views-replaced supplied as a table (now built); an empty set of
plain tellings (now excluded); a measure of how far her views are from his that had no direction,
so that a lie which overshoots passed (now `Between`); a course model in which her own weakness
excused running a course she rates below stopping (now, under a plain telling the course is not
run). For a few hours the definition contained an outcome test; that made the theorems restate a
hypothesis and let through a distortion induced openly for her own good, and was undone.

## A blind test on cases

Two language-model coders, blind to verdicts and to the account, answered factual questions per
case that render the three clauses (is she left wrong about what he believes where plain telling
would inform her; is her resulting view outside the range between plain telling's and his own;
is she more likely to act against her own judgement than under plain telling; did she ask). On a
bank of cases from a monograph on manipulation, with the book's verdicts: one coder on 235 cases
settled 90% and agreed with the book on 95% of those (1 miss, 10 over-convictions); on the 149
cases both coded, each agreed on 98% of what it settled, they gave the same verdict on 91%, and
where both settled and agreed with each other they agreed with the book on 125 of 127. The two
persistent over-convictions are a teacher's feigned enthusiasm and trust built up for a lie never
told. On 90 value-change cases from the literature the rule settled 60 to 67% and agreed with the
sources on 73 to 83% of those; most disagreements are cases where the source judges the resulting
desire and not anyone's conduct. The coders agreed with each other least on the first question
(120 of 149). The formal quantities were not computed; the coders answered in words.

## The formal statement

Lean 4 with Mathlib; imports removed. It typechecks with no warnings and depends only on the three
standard axioms. `LimsupLE x c` is imported and means: for every γ > 0, eventually `x K ≤ c + γ`;
it comes with `of_le`, `add` and `add_const`. You are not asked to recheck proofs.

```lean
namespace Scratch.LegitPlain

open Finset

structure Problem (Ω C I V O : Type*) [Fintype Ω] [DecidableEq I] [DecidableEq O] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him; there is at least one -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her options -/
  opts : Finset O
  /-- the matters her response may depend on, and those she has declined to hear -/
  matters : Finset I
  declined : Finset I
  /-- her views of the matters under an option, in a case -/
  views : C → Ω → I → V
  /-- his views of the matters -/
  his : Ω → I → V
  /-- what she takes his views to be, under an option -/
  shown : C → Ω → I → V
  /-- how she evaluates her options, given views of the matters -/
  eval : C → Ω → (I → V) → O → ℝ
  /-- what she does -/
  act : C → Ω → O
  act_mem : ∀ c ω, act c ω ∈ opts
  /-- she asked for this conduct -/
  asked : C → Prop

variable {Ω C I V O : Type*} [Fintype Ω] [DecidableEq I] [DecidableEq O]

namespace Problem

variable (P : Problem Ω C I V O)

/-- The matters she has not declined to hear. -/
def live : Finset I := P.matters \ P.declined

/-- Her rating of an option with her views on `Φ` replaced by his, and nothing else changed. -/
def rate (c : C) (ω : Ω) (Φ : Finset I) (a : O) : ℝ :=
  P.eval c ω (fun i => if i ∈ Φ then P.his ω i else P.views c ω i) a

/-- With nothing replaced, it is her rating on her own views. -/
theorem rate_empty (c : C) (ω : Ω) (a : O) : P.rate c ω ∅ a = P.eval c ω (P.views c ω) a := by
  simp [rate]

/-- Replacing a view she already shares with him changes nothing. -/
theorem rate_of_agree (c : C) (ω : Ω) (Φ : Finset I) (a : O)
    (h : ∀ i ∈ Φ, P.views c ω i = P.his ω i) : P.rate c ω Φ a = P.rate c ω ∅ a := by
  unfold rate
  congr 1
  funext i
  by_cases hi : i ∈ Φ <;> simp [hi, h]

open Classical in
/-- His weight on the cases in which a condition holds. -/
noncomputable def wt (p : Ω → Prop) : ℝ := ∑ ω, if p ω then P.μ ω else 0

theorem wt_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : P.wt p ≤ P.wt q := by
  unfold wt
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_or_le (p q : Ω → Prop) : P.wt (fun ω => p ω ∨ q ω) ≤ P.wt p + P.wt q := by
  unfold wt
  rw [← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq, P.μ_nonneg ω]

theorem wt_false : P.wt (fun _ => False) = 0 := by simp [wt]

theorem wt_le_of_forall_not {p : Ω → Prop} {κ : ℝ} (h : ∀ ω, ¬ p ω) (hκ : 0 ≤ κ) :
    P.wt p ≤ κ :=
  ((P.wt_mono (q := fun _ => False) fun ω hp => h ω hp).trans P.wt_false.le).trans hκ

/-- On her own views, what she does falls more than `s` below something she rates. -/
def Short (s : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω ∅ (P.act c ω) + s < P.rate c ω ∅ b

/-- With his views substituted on everything she has not declined, what she does falls more than
`s` below something she would rate. -/
def Regrets (s : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ b ∈ P.opts, P.rate c ω P.live (P.act c ω) + s < P.rate c ω P.live b

theorem short_mono {s s' : ℝ} {c : C} {ω : Ω} (h : s ≤ s') (hs : P.Short s' c ω) :
    P.Short s c ω := by
  obtain ⟨b, hb, hlt⟩ := hs
  exact ⟨b, hb, by linarith⟩

theorem regrets_mono {s s' : ℝ} {c : C} {ω : Ω} (h : s ≤ s') (hs : P.Regrets s' c ω) :
    P.Regrets s c ω := by
  obtain ⟨b, hb, hlt⟩ := hs
  exact ⟨b, hb, by linarith⟩

/-- She is left wrong about what he thinks on a matter she has not declined, where some plain
telling open to him would have her know it. -/
def Hidden (c : C) (ω : Ω) : Prop :=
  ∃ i ∈ P.live, P.shown c ω i ≠ P.his ω i ∧ ∃ t ∈ P.tells, P.shown t ω i = P.his ω i

/-- With his views substituted, what she does falls more than `θ` further short than under some
plain telling open to him. -/
def WorseByHim (θ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ s, P.Regrets (s + θ) c ω ∧ ¬ P.Regrets s t ω

/-- On her own views, what she does falls more than `τ` further short than under some plain
telling open to him. -/
def Worse (τ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ s, P.Short (s + τ) c ω ∧ ¬ P.Short s t ω

/-- Her rating of an option under his conduct `c`, had she the views the plain telling `t` would
leave her with: her evaluation as it is under `c`, applied to her views under `t`. -/
def rateAs (c t : C) (ω : Ω) (a : O) : ℝ := P.eval c ω (P.views t ω) a

/-- How she compares `a` with `b` under his conduct lies, to within `θ`, between how she would
with the views the plain telling `t` would leave her and how she would with his views
substituted. -/
def Between (θ : ℝ) (c t : C) (ω : Ω) (a b : O) : Prop :=
  min (P.rateAs c t ω a - P.rateAs c t ω b) (P.rate c ω P.live a - P.rate c ω P.live b) - θ ≤
      P.rate c ω ∅ a - P.rate c ω ∅ b ∧
    P.rate c ω ∅ a - P.rate c ω ∅ b ≤
      max (P.rateAs c t ω a - P.rateAs c t ω b) (P.rate c ω P.live a - P.rate c ω P.live b) + θ

/-- His conduct leaves her with a mistaken view that some plain telling would not have left: for
some plain telling and some two options, how she compares them is not between. -/
def Astray (θ : ℝ) (c : C) (ω : Ω) : Prop :=
  ∃ t ∈ P.tells, ∃ a ∈ P.opts, ∃ b ∈ P.opts, ¬ P.Between θ c t ω a b

/-- **Clause 1.**  No mistake about what he thinks. -/
def Open (κ : ℝ) (c : C) : Prop := P.wt (P.Hidden c) ≤ κ

/-- **Clause 2.**  No mistaken view that a plain telling would not have left, unless she
asked. -/
def Views (θ κ : ℝ) (c : C) : Prop := P.wt (P.Astray θ c) ≤ κ ∨ P.asked c

/-- **Clause 3.**  No choice further against her own rating than under a plain telling, unless
she asked. -/
def Will (τ κ : ℝ) (c : C) : Prop := P.wt (P.Worse τ c) ≤ κ ∨ P.asked c

/-- His conduct is legitimate. -/
def Legit (θ τ κ : ℝ) (c : C) : Prop := P.Open κ c ∧ P.Views θ κ c ∧ P.Will τ κ c

/-- **The guarantee, not part of the definition.**  What she does is not worse, by his views,
than under a plain telling, unless she asked. -/
def Outcome (θ κ : ℝ) (c : C) : Prop := P.wt (P.WorseByHim θ c) ≤ κ ∨ P.asked c

/-- If his conduct leaves her views as a plain telling would, how she compares her options is
between. -/
theorem between_of_same_views {θ : ℝ} (hθ : 0 ≤ θ) {c t : C} {ω : Ω} (a b : O)
    (h : P.views c ω = P.views t ω) : P.Between θ c t ω a b := by
  have e : ∀ x, P.rateAs c t ω x = P.rate c ω ∅ x := fun x => by
    rw [rate_empty]; unfold rateAs; rw [h]
  unfold Between
  rw [e a, e b]
  have h1 := min_le_left (P.rate c ω ∅ a - P.rate c ω ∅ b)
    (P.rate c ω P.live a - P.rate c ω P.live b)
  have h2 := le_max_left (P.rate c ω ∅ a - P.rate c ω ∅ b)
    (P.rate c ω P.live a - P.rate c ω P.live b)
  exact ⟨by linarith, by linarith⟩

/-- A plain telling is clear to within `θ₀`: after it, the differences in her rating are within
`θ₀` of what they would be with his views substituted on everything she has not declined. -/
def ClearAt (θ₀ : ℝ) (t : C) : Prop :=
  ∀ ω, ∀ a ∈ P.opts, ∀ b ∈ P.opts,
    |(P.rate t ω P.live a - P.rate t ω P.live b) - (P.rate t ω ∅ a - P.rate t ω ∅ b)| ≤ θ₀

/-! ## What follows -/

/-- Where only one plain telling is open to him, it is legitimate. -/
theorem legit_only_telling {θ τ κ : ℝ} (hθ : 0 ≤ θ) (hτ : 0 ≤ τ) (hκ : 0 ≤ κ) {t : C}
    (h : P.tells = {t}) : P.Legit θ τ κ t := by
  refine ⟨P.wt_le_of_forall_not (fun ω hn => ?_) hκ,
    Or.inl (P.wt_le_of_forall_not (fun ω hn => ?_) hκ),
    Or.inl (P.wt_le_of_forall_not (fun ω hn => ?_) hκ)⟩
  · obtain ⟨i, -, hne, t', ht', heq⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hne heq
  · obtain ⟨t', ht', a, -, b, -, hnb⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hnb (P.between_of_same_views hθ a b rfl)
  · obtain ⟨t', ht', s, hs, hns⟩ := hn
    rw [h, mem_singleton] at ht'
    subst ht'
    exact hns (P.short_mono (by linarith) hs)

/-- A larger weight tolerance only loosens it. -/
theorem Legit.mono {θ τ κ κ' : ℝ} {c : C} (hκ : κ ≤ κ') (h : P.Legit θ τ κ c) :
    P.Legit θ τ κ' c :=
  ⟨le_trans h.1 hκ, h.2.1.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr,
    h.2.2.elim (fun h2 => Or.inl (h2.trans hκ)) Or.inr⟩

/-- Leaving her wrong about what he thinks refutes it. -/
theorem not_legit_of_hidden {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Hidden c)) :
    ¬ P.Legit θ τ κ c :=
  fun hL => absurd hL.1 (not_le.mpr h)

/-- Leaving her with a mistaken view that plain telling would not have left, unasked, refutes
it. -/
theorem not_legit_of_astray {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Astray θ c))
    (hna : ¬ P.asked c) : ¬ P.Legit θ τ κ c :=
  fun hL => hL.2.1.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- Leaving what she does worse by her own rating than plain telling would, unasked, refutes
it. -/
theorem not_legit_of_worse {θ τ κ : ℝ} {c : C} (h : κ < P.wt (P.Worse τ c))
    (hna : ¬ P.asked c) : ¬ P.Legit θ τ κ c :=
  fun hL => hL.2.2.elim (fun h2 => absurd h2 (not_le.mpr h)) hna

/-- **With his views substituted, what she does is near what she would rate best**, up to her own
shortfall under a clear plain telling.  If clause 2 holds, unasked, and the plain telling `t₀` is
clear to within `θ₀`, then his weight on her doing something that, with his views substituted,
she would rate more than `σ + θ₀ + θ` below another option is at most `κ` plus his weight on her
falling more than `σ` short of her own rating under `t₀`. -/
theorem chooses_as_informed {θ θ₀ κ : ℝ} (σ : ℝ) {c t₀ : C} (hO : P.Outcome θ κ c)
    (ht₀ : t₀ ∈ P.tells) (hC : P.ClearAt θ₀ t₀) (hna : ¬ P.asked c) :
    P.wt (P.Regrets (σ + θ₀ + θ) c) ≤ κ + P.wt (P.Short σ t₀) := by
  have cover : ∀ ω, P.Regrets (σ + θ₀ + θ) c ω → P.WorseByHim θ c ω ∨ P.Short σ t₀ ω := by
    intro ω h
    by_cases hr : P.Regrets (σ + θ₀) t₀ ω
    · obtain ⟨b, hb, hlt⟩ := hr
      have g := abs_le.mp (hC ω b hb (P.act t₀ ω) (P.act_mem t₀ ω))
      exact Or.inr ⟨b, hb, by linarith [g.2]⟩
    · exact Or.inl ⟨t₀, ht₀, σ + θ₀, h, hr⟩
  have h2 : P.wt (P.WorseByHim θ c) ≤ κ := hO.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

/-- **A bound on what he gets through her mistakes and lapses.**  Let `J` in `[0, 1]` score her
options for him, and suppose that with his views substituted she would rate one option,
`best ω`, more than `σ + θ₀ + θ` above every other.  Under the same conditions, his expected
score from what she does exceeds his expected score from that option by at most `κ` plus his
weight on her falling more than `σ` short of her own rating under the clear plain telling. -/
theorem gain_le {θ θ₀ κ : ℝ} (σ : ℝ) {c t₀ : C} (hO : P.Outcome θ κ c) (ht₀ : t₀ ∈ P.tells)
    (hC : P.ClearAt θ₀ t₀) (hna : ¬ P.asked c) (J : O → ℝ) (hJ : ∀ a, 0 ≤ J a ∧ J a ≤ 1)
    (best : Ω → O) (hmem : ∀ ω, best ω ∈ P.opts)
    (hbest : ∀ ω, ∀ a ∈ P.opts, a ≠ best ω →
      P.rate c ω P.live a + (σ + θ₀ + θ) < P.rate c ω P.live (best ω)) :
    ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ κ + P.wt (P.Short σ t₀) := by
  have step : ∑ ω, P.μ ω * (J (P.act c ω) - J (best ω)) ≤ P.wt (fun ω => P.act c ω ≠ best ω) := by
    unfold wt
    refine sum_le_sum fun ω _ => ?_
    by_cases h : P.act c ω = best ω
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      have := P.μ_nonneg ω
      nlinarith [(hJ (P.act c ω)).2, (hJ (best ω)).1]
  have sub : P.wt (fun ω => P.act c ω ≠ best ω) ≤ P.wt (P.Regrets (σ + θ₀ + θ) c) :=
    P.wt_mono fun ω h => ⟨best ω, hmem ω, hbest ω _ (P.act_mem c ω) h⟩
  exact step.trans (sub.trans (P.chooses_as_informed σ hO ht₀ hC hna))

/-! ## From the definition to the outcome

The definition speaks of her views and the guarantee of what she does.  For a choice between two
options, and where his conduct changes her views but not how she evaluates given views, the one
gives the other, up to her own lapses and to choices she rates nearly even. -/

end Problem

/-- **The bridge, case by case.**  Two options.  Suppose that between his conduct `c` and the
plain telling `t` her evaluation given views is the same (so her rating with his views
substituted is the same, and her rating with the telling's views is her rating under the
telling), and that how she compares the two options under `c` is between.  If what she does under
`c` is more than `θ + lam` further below what she would rate best with his views substituted
than under `t`, then under `c` she falls more than `lam` short of her own rating, or under `t`
she would, or she rates the two options within `lam + θ` of each other. -/
theorem bridge (P : Problem Ω C I V Bool) (hopts : P.opts = {true, false}) {θ lam s : ℝ}
    (hθ : 0 ≤ θ) (hl : 0 ≤ lam) (hs : 0 ≤ s) {c t : C} {ω : Ω}
    (hH : ∀ x, P.rate t ω P.live x = P.rate c ω P.live x)
    (hT : ∀ x, P.rateAs c t ω x = P.rate t ω ∅ x)
    (hB : P.Between θ c t ω true false)
    (hr : P.Regrets (s + θ + lam) c ω) (hnr : ¬ P.Regrets s t ω) :
    P.Short lam c ω ∨ P.Short lam t ω ∨
      |P.rate c ω ∅ true - P.rate c ω ∅ false| ≤ lam + θ := by
  by_contra hcon
  have hSc : ¬ P.Short lam c ω := fun h => hcon (Or.inl h)
  have hSt : ¬ P.Short lam t ω := fun h => hcon (Or.inr (Or.inl h))
  have hN : ¬ |P.rate c ω ∅ true - P.rate c ω ∅ false| ≤ lam + θ :=
    fun h => hcon (Or.inr (Or.inr h))
  have mem : ∀ y : Bool, y ∈ P.opts := fun y => by rw [hopts]; cases y <;> simp
  have hc1 : ∀ y, P.rate c ω ∅ y ≤ P.rate c ω ∅ (P.act c ω) + lam :=
    fun y => not_lt.mp fun h => hSc ⟨y, mem y, h⟩
  have ht1 : ∀ y, P.rate t ω ∅ y ≤ P.rate t ω ∅ (P.act t ω) + lam :=
    fun y => not_lt.mp fun h => hSt ⟨y, mem y, h⟩
  have hn1 : ∀ y, P.rate c ω P.live y ≤ P.rate c ω P.live (P.act t ω) + s := fun y => by
    have := not_lt.mp fun h => hnr ⟨y, mem y, h⟩
    rwa [hH, hH] at this
  obtain ⟨y, -, hy⟩ := hr
  obtain ⟨hB1, hB2⟩ := hB
  rw [hT true, hT false] at hB1 hB2
  rw [abs_le, not_and_or] at hN
  have c1t := hc1 true; have c1f := hc1 false
  have t1t := ht1 true; have t1f := ht1 false
  have n1t := hn1 true; have n1f := hn1 false
  rcases le_total (P.rate t ω ∅ true - P.rate t ω ∅ false)
      (P.rate c ω P.live true - P.rate c ω P.live false) with hm | hm
  · rw [min_eq_left hm] at hB1
    rw [max_eq_right hm] at hB2
    cases hac : P.act c ω <;> cases hat : P.act t ω <;> cases y <;>
      simp only [hac, hat] at hy c1t c1f t1t t1f n1t n1f <;>
      rcases hN with hN | hN <;> linarith
  · rw [min_eq_right hm] at hB1
    rw [max_eq_left hm] at hB2
    cases hac : P.act c ω <;> cases hat : P.act t ω <;> cases y <;>
      simp only [hac, hat] at hy c1t c1f t1t t1f n1t n1f <;>
      rcases hN with hN | hN <;> linarith

namespace Problem

variable (P : Problem Ω C I V O)

/-- A choice she rates nearly even. -/
def NearEven (m : ℝ) (c : C) (ω : Ω) : Prop :=
  ∀ a ∈ P.opts, ∀ b ∈ P.opts, |P.rate c ω ∅ a - P.rate c ω ∅ b| ≤ m

/-- If she falls short of her own rating under his conduct, then either his conduct has made
that worse than some plain telling would, or she would fall nearly as short under every plain
telling. -/
theorem short_sub {lam τ : ℝ} {c : C} {ω : Ω} (h : P.Short lam c ω) :
    P.Worse τ c ω ∨ ∀ t ∈ P.tells, P.Short (lam - τ) t ω := by
  by_cases hall : ∀ t ∈ P.tells, P.Short (lam - τ) t ω
  · exact Or.inr hall
  · obtain ⟨t, ht⟩ := not_forall.mp hall
    have ht' := Classical.not_imp.mp ht
    exact Or.inl ⟨t, ht'.1, lam - τ, by rwa [sub_add_cancel], ht'.2⟩

end Problem

/-- **From the definition to the outcome.**  Two options, and his conduct does not change how she
evaluates given views.  If clause 2 holds, unasked, then his weight on what she does being more
than `θ + lam` worse by his views than under some plain telling is at most `κ` plus his weight on
her falling more than `lam` short of her own rating under his conduct or under some plain
telling, or rating her two options within `lam + θ` of each other. -/
theorem outcome_of_views (P : Problem Ω C I V Bool) (hopts : P.opts = {true, false})
    {θ lam κ : ℝ} (hθ : 0 ≤ θ) (hl : 0 ≤ lam) {c : C}
    (hH : ∀ t ∈ P.tells, ∀ ω x, P.rate t ω P.live x = P.rate c ω P.live x)
    (hT : ∀ t ∈ P.tells, ∀ ω x, P.rateAs c t ω x = P.rate t ω ∅ x)
    (hV : P.Views θ κ c) (hna : ¬ P.asked c) :
    P.wt (P.WorseByHim (θ + lam) c) ≤ κ + P.wt (fun ω =>
      P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ) c ω) := by
  have cover : ∀ ω, P.WorseByHim (θ + lam) c ω → P.Astray θ c ω ∨
      (P.Short lam c ω ∨ (∃ t ∈ P.tells, P.Short lam t ω) ∨ P.NearEven (lam + θ) c ω) := by
    rintro ω ⟨t, ht, s, hr, hnr⟩
    have hs : 0 ≤ s := by
      by_contra hneg
      exact hnr ⟨P.act t ω, P.act_mem t ω, by linarith⟩
    have mem : ∀ y : Bool, y ∈ P.opts := fun y => by rw [hopts]; cases y <;> simp
    by_cases hA : P.Astray θ c ω
    · exact Or.inl hA
    · have hB : P.Between θ c t ω true false := by
        by_contra hnb
        exact hA ⟨t, ht, true, mem true, false, mem false, hnb⟩
      have hr' : P.Regrets (s + θ + lam) c ω := by
        rw [show s + θ + lam = s + (θ + lam) by ring]; exact hr
      rcases bridge P hopts hθ hl hs (hH t ht ω) (hT t ht ω) hB hr' hnr with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨t, ht, h⟩))
      · refine Or.inr (Or.inr (Or.inr fun a _ b _ => ?_))
        cases a <;> cases b
        · simpa using add_nonneg hl hθ
        · rw [abs_sub_comm]; exact h
        · exact h
        · simpa using add_nonneg hl hθ
  have h2 : P.wt (P.Astray θ c) ≤ κ := hV.resolve_right hna
  linarith [(P.wt_mono cover).trans (P.wt_or_le _ _)]

#print axioms bridge
#print axioms outcome_of_views

namespace Problem

variable (P : Problem Ω C I V O)

/-! ## Change in what she values

Her rating is her evaluation applied to her views.  Between his conduct and a plain telling it
can differ because her views differ or because her evaluation does.  The split below holds her
evaluation as it is under his conduct and her views as they are under the telling; the other
order gives another split, and neither is an attribution of cause. -/

/-- The part of the difference in her rating that comes from her views being different. -/
def viewsPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views c ω) a - P.eval c ω (P.views t ω) a

/-- The part that comes from her evaluation being different. -/
def evalPart (c t : C) (ω : Ω) (a : O) : ℝ :=
  P.eval c ω (P.views t ω) a - P.eval t ω (P.views t ω) a

theorem rate_diff (c t : C) (ω : Ω) (a : O) :
    P.rate c ω ∅ a - P.rate t ω ∅ a = P.viewsPart c t ω a + P.evalPart c t ω a := by
  rw [rate_empty, rate_empty]
  unfold viewsPart evalPart
  ring

end Problem

#print axioms Problem.rate_of_agree
#print axioms Problem.legit_only_telling
#print axioms Problem.Legit.mono
#print axioms Problem.not_legit_of_hidden
#print axioms Problem.not_legit_of_astray
#print axioms Problem.not_legit_of_worse
#print axioms Problem.chooses_as_informed
#print axioms Problem.gain_le
#print axioms Problem.rate_diff

/-! ## Accuracy, and the long run

The link between his weights and the facts is a condition on his forecasts and not on his
conduct: nothing he knows and she has not been told predicts where his forecasts go wrong.  A
*signal* is any quantity available at each decision.  The condition asks that, for each signal in
a class, moving his forecast a little in the direction of the signal does not lower its squared
error. -/

section OverTime

open SequentialLimits

/-- The average of the first `K` terms. -/
noncomputable def avg (x : ℕ → ℝ) (K : ℕ) : ℝ := (∑ k ∈ range K, x k) / (K : ℝ)

theorem avg_le_const {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ k, x k ≤ c) (K : ℕ) :
    avg x K ≤ c := by
  unfold avg
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · subst h0; simpa using hc
  · have hK : (0 : ℝ) < K := by exact_mod_cast hpos
    rw [div_le_iff₀ hK]
    calc ∑ k ∈ range K, x k ≤ ∑ _k ∈ range K, c := sum_le_sum fun k _ => h k
      _ = c * K := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem avg_affine (x : ℕ → ℝ) (a b : ℝ) {K : ℕ} (hK : 0 < K) :
    avg (fun k => a * x k + b) K = a * avg x K + b := by
  unfold avg
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  field_simp

theorem avg_mono {x w : ℕ → ℝ} (h : ∀ k, x k ≤ w k) (K : ℕ) : avg x K ≤ avg w K := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun k _ => h k) (Nat.cast_nonneg K)

/-- If each forecast `p k` is at most `c` plus a second forecast `q k`, the facts `f` exceed `p`
on average by at most `a` in the limit, and `q` exceeds the facts `g` by at most `b`, then in the
long run the average of `f` exceeds the average of `g` by at most `c + a + b`. -/
theorem long_run {c a b : ℝ} (hc : 0 ≤ c) (p q f g : ℕ → ℝ) (step : ∀ k, p k ≤ c + q k)
    (hf : LimsupLE (fun K => avg (fun k => f k - p k) K) a)
    (hg : LimsupLE (fun K => avg (fun k => q k - g k) K) b) :
    LimsupLE (fun K => avg f K - avg g K) (c + a + b) := by
  have key : ∀ K, avg f K - avg g K ≤
      (avg (fun k => f k - p k) K + avg (fun k => q k - g k) K) + c := by
    intro K
    have h1 : avg (fun k => p k - q k) K ≤ c :=
      avg_le_const hc (fun k => by linarith [step k]) K
    have e : avg f K - avg g K =
        avg (fun k => f k - p k) K + avg (fun k => p k - q k) K + avg (fun k => q k - g k) K := by
      unfold avg
      rw [← add_div, ← add_div, ← sub_div, ← sum_add_distrib, ← sum_add_distrib,
        ← sum_sub_distrib]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [e]; linarith
  have h := (hf.add hg).add_const c
  rw [show a + b + c = c + a + b by ring] at h
  exact LimsupLE.of_le key h

/-- For no signal in the class does moving his forecasts by `ε` times the signal lower their
squared error, on average in the limit. -/
def NoSignalBeats (ε : ℝ) (S : Set (ℕ → ℝ)) (D y : ℕ → ℝ) : Prop :=
  ∀ s ∈ S, LimsupLE (fun K => avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K) 0

/-- If no signal in the class beats his forecasts, then for every signal in it of size at most 1
the average of the signal times his error is at most `ε/2` in the limit.  This is one-sided; the
other side needs the negative of the signal to be in the class too. -/
theorem signal_le_of_noSignal {ε : ℝ} (hε : 0 < ε) {S : Set (ℕ → ℝ)} {D y : ℕ → ℝ}
    (h : NoSignalBeats ε S D y) {s : ℕ → ℝ} (hs : s ∈ S) (hb : ∀ k, s k ^ 2 ≤ 1) :
    LimsupLE (fun K => avg (fun k => s k * (y k - D k)) K) (ε / 2) := by
  intro γ hγ
  obtain ⟨N, hN⟩ := h s hs (2 * ε * γ) (by positivity)
  refine ⟨max N 1, fun K hK => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le one_pos ((le_max_right N 1).trans hK)
  have h1 := hN K ((le_max_left N 1).trans hK)
  have low : avg (fun k => (2 * ε) * (s k * (y k - D k)) + (-(ε ^ 2))) K ≤
      avg (fun k => (D k - y k) ^ 2 - (D k + ε * s k - y k) ^ 2) K :=
    avg_mono (fun k => by nlinarith [hb k, sq_nonneg ε]) K
  rw [avg_affine _ _ _ hKpos] at low
  show avg (fun k => s k * (y k - D k)) K ≤ ε / 2 + γ
  have h2 : (2 * ε) * avg (fun k => s k * (y k - D k)) K ≤ (2 * ε) * (ε / 2 + γ) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- The constant signal 1 and the constant signal −1. -/
def shifts : Set (ℕ → ℝ) := {s | s = (fun _ => 1) ∨ s = (fun _ => -1)}

/-- If shifting his forecasts up does not help, the facts exceed his forecasts by at most `ε/2`
on average in the limit. -/
theorem under_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoSignalBeats ε shifts D y) :
    LimsupLE (fun K => avg (fun k => y k - D k) K) (ε / 2) := by
  have h1 := signal_le_of_noSignal hε h (s := fun _ => 1) (Or.inl rfl) (fun _ => by norm_num)
  simpa using h1

/-- If shifting his forecasts down does not help, his forecasts exceed the facts by at most `ε/2`
on average in the limit. -/
theorem over_of_noShift {ε : ℝ} (hε : 0 < ε) {D y : ℕ → ℝ} (h : NoSignalBeats ε shifts D y) :
    LimsupLE (fun K => avg (fun k => D k - y k) K) (ε / 2) := by
  have h1 := signal_le_of_noSignal hε h (s := fun _ => -1) (Or.inr rfl) (fun _ => by norm_num)
  have e : (fun K => avg (fun k => (-1 : ℝ) * (y k - D k)) K) =
      (fun K => avg (fun k => D k - y k) K) := by
    funext K; congr 1; funext k; ring
  rwa [e] at h1

variable (P : ℕ → Problem Ω C I V O) (c t₀ : ℕ → C)

/-- **In the long run.**  `f k` and `g k` are any sequences that his forecasts of the two events
are accurate about in the sense above; they are meant as the facts (whether at `k` she did
something that with his views substituted she would rate well below another option, and whether
under the clear plain telling she would have fallen short), but nothing here says how those are
observed.  If at every decision clause 2 holds unasked and `t₀ k` is a clear plain telling, the
long-run average of `f` exceeds that of `g` by at most `κ + ε`. -/
theorem long_run_informed {θ θ₀ κ ε : ℝ} (σ : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hO : ∀ k, (P k).Outcome θ κ (c k)) (ht₀ : ∀ k, t₀ k ∈ (P k).tells)
    (hC : ∀ k, (P k).ClearAt θ₀ (t₀ k)) (hna : ∀ k, ¬ (P k).asked (c k)) (f g : ℕ → ℝ)
    (hf : NoSignalBeats ε shifts (fun k => (P k).wt ((P k).Regrets (σ + θ₀ + θ) (c k))) f)
    (hg : NoSignalBeats ε shifts (fun k => (P k).wt ((P k).Short σ (t₀ k))) g) :
    LimsupLE (fun K => avg f K - avg g K) (κ + ε / 2 + ε / 2) :=
  long_run hκ _ _ f g
    (fun k => (P k).chooses_as_informed σ (hO k) (ht₀ k) (hC k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε hg)

end OverTime

#print axioms signal_le_of_noSignal
#print axioms under_of_noShift
#print axioms over_of_noShift
#print axioms long_run_informed

/-! ## A course of conduct and where it ends

His conduct is a course that she can let go on or stop.  `Z` is where things can end, and an end
includes what she then values.  She evaluates ends by what she values now.  The one matter is
where going on ends: he has a forecast of it, she has a view of it, and in each case there is
where it does end.  Under a plain telling the course is not being run: he tells her of it and
does nothing else.  This is a decision problem of the kind above, built and not supposed. -/

structure Course (Ω C Z : Type*) [Fintype Ω] where
  /-- his weights on cases -/
  μ : Ω → ℝ
  μ_nonneg : ∀ ω, 0 ≤ μ ω
  μ_sum : ∑ ω, μ ω = 1
  /-- the plain tellings open to him -/
  tells : Finset C
  tells_nonempty : tells.Nonempty
  /-- her evaluation, by what she values now, of where things end -/
  u : Ω → Z → ℝ
  /-- where things are left if the course does not go on -/
  stay : Ω → Z
  /-- his forecast of where going on ends, what she will then value included -/
  fore : Ω → Z
  /-- her view, under each option of his, of where going on ends -/
  bel : C → Ω → Z
  /-- what she takes his forecast to be, under each option of his -/
  told : C → Ω → Z
  /-- where going on does end -/
  ends : C → Ω → Z
  /-- the course goes on -/
  goes : C → Ω → Bool
  /-- under a plain telling the course is not run -/
  tell_stops : ∀ t ∈ tells, ∀ ω, goes t ω = false
  /-- she asked for this conduct -/
  asked : C → Prop

namespace Course

variable {Z : Type*} (K : Course Ω C Z)

/-- The decision problem of a course: the options are that it goes on (`true`) or not (`false`);
the one matter is where going on ends. -/
def toProblem : Problem Ω C Unit Z Bool where
  μ := K.μ
  μ_nonneg := K.μ_nonneg
  μ_sum := K.μ_sum
  tells := K.tells
  tells_nonempty := K.tells_nonempty
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun c ω _ => K.bel c ω
  his := fun ω _ => K.fore ω
  shown := fun c ω _ => K.told c ω
  eval := fun _ ω v a => if a then K.u ω (v ()) else K.u ω (K.stay ω)
  act := K.goes
  act_mem := fun c ω => by cases K.goes c ω <;> simp
  asked := K.asked

/-- With his view substituted, her rating of going on is her present evaluation of his
forecast. -/
theorem rate_go (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live true = K.u ω (K.fore ω) := by
  simp [Problem.rate, Problem.live, toProblem]

/-- Her rating of its not going on is her present evaluation of where that leaves her. -/
theorem rate_stop (c : C) (ω : Ω) :
    K.toProblem.rate c ω K.toProblem.live false = K.u ω (K.stay ω) := by
  simp [Problem.rate, toProblem]

/-- His forecast is off: by her present evaluation, where it ends differs from his forecast by
more than `δ`. -/
def Off (δ : ℝ) (c : C) (ω : Ω) : Prop := δ < |K.u ω (K.ends c ω) - K.u ω (K.fore ω)|

/-- The course goes on, and it ends where her present evaluation rates more than `m` below where
its not going on would have left her. -/
def LedAstray (m : ℝ) (c : C) (ω : Ω) : Prop :=
  K.goes c ω = true ∧ K.u ω (K.ends c ω) + m < K.u ω (K.stay ω)

/-- **Not led astray, beyond his forecast error.**  If clause 2 holds and she did not ask, then
his weight on the course going on to an end that her present evaluation rates more than `θ + δ`
below its not going on is at most `κ` plus his weight on his forecast being off by more than
`δ`.  Her own weakness does not enter: under a plain telling the course is not run. -/
theorem not_led_astray {θ κ : ℝ} (δ : ℝ) (hθ : 0 ≤ θ) {c : C} (hO : K.toProblem.Outcome θ κ c)
    (hna : ¬ K.asked c) :
    K.toProblem.wt (K.LedAstray (θ + δ) c) ≤ κ + K.toProblem.wt (K.Off δ c) := by
  have cover : ∀ ω, K.LedAstray (θ + δ) c ω → K.toProblem.WorseByHim θ c ω ∨ K.Off δ c ω := by
    rintro ω ⟨hg, hlt⟩
    by_cases hoff : K.Off δ c ω
    · exact Or.inr hoff
    · have h := abs_le.mp (not_lt.mp hoff)
      have key : K.u ω (K.fore ω) + θ < K.u ω (K.stay ω) := by linarith [h.1]
      obtain ⟨t, ht⟩ := K.tells_nonempty
      refine Or.inl ⟨t, ht, 0, ⟨false, by simp [toProblem], ?_⟩, ?_⟩
      · show K.toProblem.rate c ω K.toProblem.live (K.goes c ω) + (0 + θ) <
          K.toProblem.rate c ω K.toProblem.live false
        rw [hg, rate_go, rate_stop]
        linarith
      · rintro ⟨b, -, hb⟩
        have hb' : K.toProblem.rate t ω K.toProblem.live (K.goes t ω) + 0 <
            K.toProblem.rate t ω K.toProblem.live b := hb
        rw [K.tell_stops t ht ω, rate_stop] at hb'
        cases b
        · rw [rate_stop] at hb'; linarith
        · rw [rate_go] at hb'; linarith
  have h2 : K.toProblem.wt (K.toProblem.WorseByHim θ c) ≤ κ := hO.resolve_right hna
  linarith [(K.toProblem.wt_mono cover).trans (K.toProblem.wt_or_le _ _)]

/-- In a course her evaluation is the same whatever he does, so her rating with his view
substituted is the same under every option. -/
theorem rate_live_eq (c t : C) (ω : Ω) (x : Bool) :
    K.toProblem.rate t ω K.toProblem.live x = K.toProblem.rate c ω K.toProblem.live x := by
  cases x
  · rw [rate_stop, rate_stop]
  · rw [rate_go, rate_go]

/-- And her rating under his conduct with a plain telling's views is her rating under that
telling. -/
theorem rateAs_eq (c t : C) (ω : Ω) (x : Bool) :
    K.toProblem.rateAs c t ω x = K.toProblem.rate t ω ∅ x := by
  rw [Problem.rate_empty]
  rfl

/-- **Not led astray, from the definition.**  If his conduct is legitimate and she did not ask,
then his weight on the course going on to an end that her present evaluation rates more than
`θ + lam + δ` below its not going on is at most `2κ`, plus his weight on her own view being
otherwise (told plainly, she would herself rate its going on more than `lam − τ` above its not
going on) or nearly even (she rates the two within `lam + θ`), plus his weight on his forecast
being off by more than `δ`. -/
theorem not_led_astray_of_legit {θ τ κ : ℝ} (lam δ : ℝ) (hθ : 0 ≤ θ) (hτ : 0 ≤ τ)
    (hl : 0 ≤ lam) {c : C} (hL : K.toProblem.Legit θ τ κ c) (hna : ¬ K.asked c) :
    K.toProblem.wt (K.LedAstray (θ + lam + δ) c) ≤
      2 * κ + K.toProblem.wt (fun ω =>
          (∃ t ∈ K.tells, K.toProblem.Short (lam - τ) t ω) ∨
            K.toProblem.NearEven (lam + θ) c ω) +
        K.toProblem.wt (K.Off δ c) := by
  have hW := outcome_of_views K.toProblem rfl hθ hl
    (fun t _ ω x => K.rate_live_eq c t ω x) (fun t _ ω x => K.rateAs_eq c t ω x) hL.2.1 hna
  have h1 := K.not_led_astray δ (by linarith : (0 : ℝ) ≤ θ + lam) (Or.inl hW) hna
  have cover : ∀ ω, (K.toProblem.Short lam c ω ∨ (∃ t ∈ K.toProblem.tells,
        K.toProblem.Short lam t ω) ∨ K.toProblem.NearEven (lam + θ) c ω) →
      K.toProblem.Worse τ c ω ∨ ((∃ t ∈ K.tells, K.toProblem.Short (lam - τ) t ω) ∨
        K.toProblem.NearEven (lam + θ) c ω) := by
    rintro ω (h | ⟨t, ht, h⟩ | h)
    · rcases K.toProblem.short_sub (τ := τ) h with hw | hall
      · exact Or.inl hw
      · obtain ⟨t, ht⟩ := K.tells_nonempty
        exact Or.inr (Or.inl ⟨t, ht, hall t ht⟩)
    · exact Or.inr (Or.inl ⟨t, ht, K.toProblem.short_mono (by linarith) h⟩)
    · exact Or.inr (Or.inr h)
  have h2 : K.toProblem.wt (K.toProblem.Worse τ c) ≤ κ := hL.2.2.resolve_right hna
  have h3 := (K.toProblem.wt_mono cover).trans (K.toProblem.wt_or_le _ _)
  linarith

end Course

/-! The forecast-error term cannot be dropped.  One case; his options are to run the course,
telling her all he thinks (`true`), or the plain telling alone (`false`); ends are numbers and
she values them as they are.  Not going on leaves her at 0.  He forecasts that going on ends at
1, tells her, and she agrees.  It ends at −1. -/

/-- The course in which he is sincere, clear, and wrong. -/
noncomputable def sincereWrong : Course Unit Bool ℝ where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := {false}
  tells_nonempty := by simp
  u := fun _ z => z
  stay := fun _ => 0
  fore := fun _ => 1
  bel := fun _ _ => 1
  told := fun _ _ => 1
  ends := fun _ _ => -1
  goes := fun c _ => c
  tell_stops := fun t ht _ => by rw [mem_singleton] at ht; exact ht
  asked := fun _ => False

open Classical in
/-- Clause 2 holds with no tolerance, and with his whole weight the course goes on to an end she
rates below its not going on.  The only term left on the right of `not_led_astray` is his
forecast being off. -/
theorem needs_forecast :
    sincereWrong.toProblem.Outcome 0 0 true ∧
      sincereWrong.toProblem.wt (sincereWrong.LedAstray (1 / 2) true) = 1 := by
  refine ⟨Or.inl (sincereWrong.toProblem.wt_le_of_forall_not (fun ω hn => ?_) le_rfl), ?_⟩
  · obtain ⟨t, ht, s, ⟨b, -, hb⟩, hns⟩ := hn
    have ht' : t = false := by simpa [Course.toProblem, sincereWrong] using ht
    subst ht'
    have hb' : sincereWrong.toProblem.rate true ω sincereWrong.toProblem.live true + (s + 0) <
        sincereWrong.toProblem.rate true ω sincereWrong.toProblem.live b := hb
    have hs : s < 0 := by
      cases b
      · rw [Course.rate_go, Course.rate_stop] at hb'
        simp [sincereWrong] at hb'
        linarith
      · rw [Course.rate_go] at hb'
        simp at hb'
        linarith
    refine hns ⟨true, by simp [Course.toProblem], ?_⟩
    show sincereWrong.toProblem.rate false ω sincereWrong.toProblem.live false + s <
      sincereWrong.toProblem.rate false ω sincereWrong.toProblem.live true
    rw [Course.rate_stop, Course.rate_go]
    simp [sincereWrong]
    linarith
  · have hyes : sincereWrong.LedAstray (1 / 2) true () :=
      ⟨rfl, by show (-1 : ℝ) + 1 / 2 < 0; norm_num⟩
    unfold Problem.wt
    rw [Finset.univ_unique, Finset.sum_singleton, if_pos hyes]
    rfl

section CourseInFact

open SequentialLimits

variable {Z : Type*} (K : ℕ → Course Ω C Z) (c : ℕ → C)

/-- **Not led astray, in the long run.**  A sequence of courses.  `f k` and `e k` are any
sequences that his forecasts of the two events are accurate about; they are meant as the facts
(whether the course in fact went on to an end her evaluation at its start rates more than
`θ + δ` below its not going on, and whether his forecast was in fact off by more than `δ`).  If
at each course clause 2 holds unasked, the long-run average of `f` exceeds that of `e` by at most
`κ + ε`. -/
theorem long_run_not_led_astray {θ κ ε : ℝ} (δ : ℝ) (hθ : 0 ≤ θ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hO : ∀ k, (K k).toProblem.Outcome θ κ (c k)) (hna : ∀ k, ¬ (K k).asked (c k))
    (f e : ℕ → ℝ)
    (hf : NoSignalBeats ε shifts
      (fun k => (K k).toProblem.wt ((K k).LedAstray (θ + δ) (c k))) f)
    (he : NoSignalBeats ε shifts (fun k => (K k).toProblem.wt ((K k).Off δ (c k))) e) :
    LimsupLE (fun n => avg f n - avg e n) (κ + ε / 2 + ε / 2) :=
  long_run hκ _ _ f e (fun k => (K k).not_led_astray δ hθ (hO k) (hna k))
    (under_of_noShift hε hf) (over_of_noShift hε he)

end CourseInFact

#print axioms Course.not_led_astray
#print axioms Course.not_led_astray_of_legit
#print axioms needs_forecast
#print axioms long_run_not_led_astray

/-! ## Instances: numerical patterns

One case; one matter, on which her view is `false` and his is `true`; her options `true` (which
she rates 1) and `false` (which she rates 0).  His options are of any type `K`.

* `hid k`   under `k` she takes his view to be other than it is
* `bad k`   under `k`, with his view substituted, she would rate her options the other way round
* `l k`     under `k` she takes the option she herself rates lower
* `ask`     she asked

Her own views are the same under every option here, so this family shows the patterns of clause
1, clause 3 and the outcome guarantee; clause 2 is shown in the family after it.  The names say what kind of conduct
would produce each pattern; that such conduct produces it is not shown here. -/

namespace Witness

noncomputable def W {K : Type} (tells : Finset K) (hne : tells.Nonempty) (hid bad l : K → Bool)
    (ask : Prop) : Problem Unit K Unit Bool Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  tells_nonempty := hne
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun _ _ _ => false
  his := fun _ _ => true
  shown := fun k _ _ => !(hid k)
  eval := fun k _ v a =>
    if v () && bad k then (if a then 0 else 1) else (if a then 1 else 0)
  act := fun k _ => !(l k)
  act_mem := fun k _ => by cases l k <;> simp
  asked := fun _ => ask

variable {K : Type} (tells : Finset K) (hne : tells.Nonempty) (hid bad l : K → Bool) (ask : Prop)

theorem own_W (k : K) (a : Bool) :
    (W tells hne hid bad l ask).rate k () ∅ a = if a then 1 else 0 := by
  simp [Problem.rate, W]

theorem informed_W (k : K) (a : Bool) :
    (W tells hne hid bad l ask).rate k () (W tells hne hid bad l ask).live a =
      if bad k then (if a then 0 else 1) else (if a then 1 else 0) := by
  cases hb : bad k <;> simp [Problem.rate, Problem.live, W, hb]

open Classical in
theorem wt_W (p : Unit → Prop) : (W tells hne hid bad l ask).wt p = if p () then 1 else 0 := by
  unfold Problem.wt
  rw [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem short_W (s : ℝ) (k : K) :
    (W tells hne hid bad l ask).Short s k () ↔ s < (if l k then 1 else 0) := by
  constructor
  · rintro ⟨b, -, hb⟩
    rw [own_W, own_W] at hb
    cases hl : l k <;> cases b <;> simp [W, hl] at hb ⊢ <;> linarith
  · intro h
    refine ⟨true, by simp [W], ?_⟩
    rw [own_W, own_W]
    cases hl : l k <;> simp [W, hl] at h ⊢ <;> linarith

theorem regrets_W (s : ℝ) (k : K) :
    (W tells hne hid bad l ask).Regrets s k () ↔ s < (if l k = bad k then 0 else 1) := by
  constructor
  · rintro ⟨b, -, hb⟩
    rw [informed_W, informed_W] at hb
    cases hl : l k <;> cases hbad : bad k <;> cases b <;> simp [W, hl, hbad] at hb ⊢ <;> linarith
  · intro h
    refine ⟨bad k == false, by cases bad k <;> simp [W], ?_⟩
    rw [informed_W, informed_W]
    cases hl : l k <;> cases hbad : bad k <;> simp [W, hl, hbad] at h ⊢ <;> linarith

theorem hidden_W (c : K) :
    (W tells hne hid bad l ask).Hidden c () ↔ (hid c = true ∧ ∃ t ∈ tells, hid t = false) := by
  constructor
  · rintro ⟨i, -, hne', t, ht, heq⟩
    refine ⟨?_, t, ht, ?_⟩
    · cases hc : hid c
      · exact absurd (by simp [W, hc]) hne'
      · rfl
    · cases ht' : hid t
      · rfl
      · simp [W, ht'] at heq
  · rintro ⟨hc, t, ht, ht'⟩
    exact ⟨(), by simp [Problem.live, W], by simp [W, hc], t, ht, by simp [W, ht']⟩

theorem worseByHim_W {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (c : K) :
    (W tells hne hid bad l ask).WorseByHim θ c () ↔
      (l c ≠ bad c ∧ ∃ t ∈ tells, l t = bad t) := by
  constructor
  · rintro ⟨t, ht, s, h1, h2⟩
    rw [regrets_W] at h1 h2
    by_cases hc : l c = bad c
    · rw [if_pos hc] at h1
      by_cases ht' : l t = bad t
      · rw [if_pos ht'] at h2; linarith
      · rw [if_neg ht'] at h2; linarith
    · refine ⟨hc, t, ht, ?_⟩
      by_contra ht'
      rw [if_neg hc] at h1
      rw [if_neg ht'] at h2
      linarith
  · rintro ⟨hc, t, ht, ht'⟩
    refine ⟨t, ht, 0, ?_, ?_⟩
    · rw [regrets_W, if_neg hc]; linarith
    · rw [regrets_W, if_pos ht']; exact lt_irrefl 0

theorem worse_W {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (c : K) :
    (W tells hne hid bad l ask).Worse τ c () ↔ (l c = true ∧ ∃ t ∈ tells, l t = false) := by
  constructor
  · rintro ⟨t, ht, s, h1, h2⟩
    rw [short_W] at h1 h2
    cases hc : l c <;> cases hl : l t <;> simp [hc, hl] at h1 h2 ⊢ <;>
      first
        | linarith
        | exact ⟨t, ht, hl⟩
  · rintro ⟨hc, t, ht, hl⟩
    refine ⟨t, ht, 0, ?_, ?_⟩
    · rw [short_W]; simp [hc]; linarith
    · rw [short_W]; simp [hl]

open Classical in
/-- In this family her views are the same under every option, so clause 2 always holds; the
other two hold when their patterns are absent. -/
theorem legit_W {θ τ κ : ℝ} (hθ0 : 0 ≤ θ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hκ : 0 ≤ κ) (c : K) (h1 : ¬ (hid c = true ∧ ∃ t ∈ tells, hid t = false))
    (h3 : ¬ (l c = true ∧ ∃ t ∈ tells, l t = false)) :
    (W tells hne hid bad l ask).Legit θ τ κ c := by
  refine ⟨?_, Or.inl ?_, Or.inl ?_⟩
  · show (W tells hne hid bad l ask).wt _ ≤ κ
    rw [wt_W, if_neg (by rwa [hidden_W])]
    exact hκ
  · refine (W tells hne hid bad l ask).wt_le_of_forall_not (fun ω hn => ?_) hκ
    obtain ⟨t, -, a, -, b, -, hnb⟩ := hn
    exact hnb ((W tells hne hid bad l ask).between_of_same_views hθ0 a b rfl)
  · rw [wt_W, if_neg (by rwa [worse_W tells hne hid bad l ask hτ0 hτ1])]
    exact hκ

open Classical in
theorem not_open_W {κ : ℝ} (hκ : κ < 1) (c : K)
    (h : hid c = true ∧ ∃ t ∈ tells, hid t = false) :
    ¬ (W tells hne hid bad l ask).Open κ c := by
  unfold Problem.Open
  rw [wt_W, if_pos ((hidden_W tells hne hid bad l ask c).mpr h)]
  exact not_le.mpr hκ

open Classical in
theorem not_outcome_W {θ κ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : κ < 1) (c : K)
    (h : l c ≠ bad c ∧ ∃ t ∈ tells, l t = bad t) (hna : ¬ ask) :
    ¬ (W tells hne hid bad l ask).Outcome θ κ c := by
  rintro (h' | h')
  · rw [wt_W, if_pos ((worseByHim_W tells hne hid bad l ask hθ0 hθ1 c).mpr h)] at h'
    linarith
  · exact hna h'

open Classical in
theorem not_will_W {τ κ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hκ : κ < 1) (c : K)
    (h : l c = true ∧ ∃ t ∈ tells, l t = false) (hna : ¬ ask) :
    ¬ (W tells hne hid bad l ask).Will τ κ c := by
  rintro (h' | h')
  · rw [wt_W, if_pos ((worse_W tells hne hid bad l ask hτ0 hτ1 c).mpr h)] at h'
    linarith
  · exact hna h'

/-! His options in the next instances: `true` the conduct in question, `false` the one plain
telling open to him. -/

/-- Nothing hidden, the same act as under plain telling: legitimate. -/
theorem same_as_telling :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun _ => false) False).Legit
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-- She knows what he thinks and rates her options the other way, under his conduct as under
plain telling: legitimate.  Disagreement that plain telling would leave is hers. -/
theorem keeps_her_view :
    (W {false} (by simp) (fun _ => false) (fun _ => true) (fun _ => false) False).Legit
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-- She is left wrong about what he thinks, where plain telling would have her know it: clause 1
fails.  Something untold, or a lie. -/
theorem hidden_fails :
    ¬ (W {false} (by simp) (fun k => k) (fun _ => false) (fun _ => false) False).Open
      (1 / 10) true :=
  not_open_W _ _ _ _ _ _ (by norm_num) true ⟨rfl, false, by simp, rfl⟩

/-- Under his conduct she does what, with his views substituted, she would rate lower, and under
plain telling she would not: the outcome guarantee fails. -/
theorem worse_by_him_fails :
    ¬ (W {false} (by simp) (fun _ => false) (fun k => k) (fun _ => false) False).Outcome
      (1 / 10) (1 / 10) true :=
  not_outcome_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) true
    ⟨by simp, false, by simp, by simp⟩ (fun h => h)

/-- Under his conduct she does what he thinks best for her, under plain telling she would not,
and he gets there by leaving her wrong about what he thinks: the outcome guarantee and clause 3
hold and clause 1 fails.  A lie for her own good. -/
theorem for_her_own_good :
    (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Outcome
        (1 / 10) (1 / 10) true ∧
      (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Will
        (1 / 10) (1 / 10) true ∧
      ¬ (W {false} (by simp) (fun k => k) (fun k => !k) (fun _ => false) False).Open
        (1 / 10) true := by
  refine ⟨Or.inl ?_, Or.inl ?_, not_open_W _ _ _ _ _ _ (by norm_num) true ⟨rfl, false, by simp, rfl⟩⟩
  · rw [wt_W, if_neg (by
      rw [worseByHim_W _ _ _ _ _ _ (by norm_num) (by norm_num)]; simp)]
    norm_num
  · rw [wt_W, if_neg (by rw [worse_W _ _ _ _ _ _ (by norm_num) (by norm_num)]; simp)]
    norm_num

/-- Under his conduct she takes what she herself rates lower, and under plain telling she would
not, unasked: clause 3 fails. -/
theorem pressed :
    ¬ (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) False).Will
      (1 / 10) (1 / 10) true :=
  not_will_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) true
    ⟨rfl, false, by simp, rfl⟩ (fun h => h)

/-- The same, and she asked: the outcome guarantee and clause 3 hold. -/
theorem pressed_asked :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) True).Outcome
        (1 / 10) (1 / 10) true ∧
      (W {false} (by simp) (fun _ => false) (fun _ => false) (fun k => k) True).Will
        (1 / 10) (1 / 10) true :=
  ⟨Or.inr trivial, Or.inr trivial⟩

/-- She takes what she herself rates lower under plain telling too: legitimate. -/
theorem weak_anyway :
    (W {false} (by simp) (fun _ => false) (fun _ => false) (fun _ => true) False).Legit
      (1 / 10) (1 / 10) (1 / 10) true :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-! Choosing the moment.  His options: `some true` asking now and saying everything;
`some false` telling her plainly now; `none` telling her plainly later.  Now, with his view of
what she values substituted, she would rate her options the other way; later she would not. -/

/-- Asking now, with everything said, when he could have told her later: the outcome guarantee
fails. -/
theorem mood_timing :
    ¬ (W {some false, none} (by simp) (fun _ => false) (fun k => k.isSome) (fun _ => false)
      False).Outcome (1 / 10) (1 / 10) (some true) :=
  not_outcome_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (some true)
    ⟨by simp, none, by simp, by simp⟩ (fun h => h)

/-- The same when the matter cannot wait, so that telling her now is the only plain telling open
to him: legitimate. -/
theorem mood_cannot_wait :
    (W {some false} (by simp) (fun _ => false) (fun k => k.isSome) (fun _ => false)
      False).Legit (1 / 10) (1 / 10) (1 / 10) (some true) :=
  legit_W _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
    (by simp) (by simp)

/-! Clause 2.  One case; one matter, a number; her option `true` is rated at her view of that
number and `false` at 0, whatever he does.  `h` is his view; `x k` is her view under his option
`k`; `g k` is whether she takes `true`.  How she compares `true` with `false` under `k` is then
`x k`, with a plain telling `t`'s views `x t`, and with his view substituted `h`. -/

noncomputable def W2 {K : Type} (tells : Finset K) (hne : tells.Nonempty) (h : ℝ) (x : K → ℝ)
    (g : K → Bool) : Problem Unit K Unit ℝ Bool where
  μ := fun _ => 1
  μ_nonneg := fun _ => zero_le_one
  μ_sum := by simp
  tells := tells
  tells_nonempty := hne
  opts := {true, false}
  matters := {()}
  declined := ∅
  views := fun k _ _ => x k
  his := fun _ _ => h
  shown := fun _ _ _ => h
  eval := fun _ _ v a => if a then v () else 0
  act := fun k _ => g k
  act_mem := fun k _ => by cases g k <;> simp
  asked := fun _ => False

theorem between_W2 {K : Type} (tells : Finset K) (hne : tells.Nonempty) (h : ℝ) (x : K → ℝ)
    (g : K → Bool) (θ : ℝ) (c t : K) :
    (W2 tells hne h x g).Between θ c t () true false ↔
      (min (x t) h - θ ≤ x c ∧ x c ≤ max (x t) h + θ) := by
  simp [Problem.Between, Problem.rateAs, Problem.rate, Problem.live, W2]

/-- She keeps her view after being told, far from his: between. -/
theorem w2_keeps_her_view :
    (W2 {false} (by simp) 1 (fun _ => -3) (fun _ => false)).Between (1 / 10) true false ()
      true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- His conduct brings her part of the way from where plain telling would leave her toward his
view: between.  Open persuasion beyond plain telling. -/
theorem w2_part_way :
    (W2 {false} (by simp) 1 (fun k => if k then 0 else -3) (fun _ => false)).Between (1 / 10)
      true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- His conduct carries her past his view: not between.  A lie that overshoots, or an anchor he
announces. -/
theorem w2_overshoot :
    ¬ (W2 {false} (by simp) (-1) (fun k => if k then 1 else -3) (fun _ => false)).Between
      (1 / 10) true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- Plain telling would leave her agreeing with him; his conduct leaves her further along than
either, in the direction he wants: not between.  A fear he takes to be out of proportion, used
for her own good. -/
theorem w2_for_her_good_by_distortion :
    ¬ (W2 {false} (by simp) 1 (fun k => if k then 5 else 1) (fun _ => true)).Between
      (1 / 10) true false () true false := by
  rw [between_W2]; norm_num [min_def, max_def]

/-- Now, in a mood, she compares her options far from how he takes her to value them; told
plainly later she would not.  Asking now (`some true`) is not between against telling later
(`none`), and is between against telling now (`some false`). -/
theorem w2_mood :
    ¬ (W2 {some false, none} (by simp) (-1) (fun k => if k.isSome then 1 else -1)
        (fun _ => true)).Between (1 / 10) (some true) none () true false ∧
      (W2 {some false, none} (by simp) (-1) (fun k => if k.isSome then 1 else -1)
        (fun _ => true)).Between (1 / 10) (some true) (some false) () true false := by
  constructor <;> rw [between_W2] <;> norm_num [min_def, max_def]

/-- The near-even term of the bridge is needed.  After plain telling she rates her two options
even and takes the one that is better by his view; under his conduct she rates them even and
takes the other.  How she compares them is between with no tolerance, and what she does is worse
by his view by 9 and more. -/
theorem w2_tips_an_even_choice :
    (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Between 0 true false () true false ∧
      (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Regrets (0 + 9) true () ∧
      ¬ (W2 {false} (by simp) (-10) (fun _ => 0) (fun k => k)).Regrets 0 false () := by
  refine ⟨by rw [between_W2]; norm_num [min_def, max_def], ⟨false, by simp [W2], ?_⟩, ?_⟩
  · simp [Problem.rate, Problem.live, W2]; norm_num
  · rintro ⟨b, -, hb⟩
    cases b <;> simp [Problem.rate, Problem.live, W2] at hb
    linarith

end Witness

#print axioms Witness.same_as_telling
#print axioms Witness.keeps_her_view
#print axioms Witness.hidden_fails
#print axioms Witness.worse_by_him_fails
#print axioms Witness.for_her_own_good
#print axioms Witness.pressed
#print axioms Witness.pressed_asked
#print axioms Witness.weak_anyway
#print axioms Witness.mood_timing
#print axioms Witness.mood_cannot_wait
#print axioms Witness.w2_keeps_her_view
#print axioms Witness.w2_part_way
#print axioms Witness.w2_overshoot
#print axioms Witness.w2_for_her_good_by_distortion
#print axioms Witness.w2_mood
#print axioms Witness.w2_tips_an_even_choice

end Scratch.LegitPlain
```

## Limits the authors already state

- His forecast of her rating with her views replaced is a counterfactual inside his model.
- The same cases are used under all his options; her ratings under his different options are
  assumed to be on one scale.
- The bridge is for two options and assumes his conduct does not change how she evaluates given
  views; no witness shows that assumption is needed.
- The course model has one forecast whatever he does, and an end is unstructured.
- Nothing says how the facts scored by the long-run results are observed.
- `chooses_as_informed`, `gain_le`, `not_led_astray` and the long-run results take the outcome
  guarantee as hypothesis; they follow from the definition only through the bridge.
- All proofs are short. The instances are numerical patterns.

## Questions

Answer in order. Where you claim an error, quote the declaration and give the smallest example.

1. **Fidelity to the informal sentence.** Do `Open`, `Views` (through `Between` and `Astray`) and
   `Will` render the quoted sentence? What does the sentence require that they omit, and the
   reverse? In particular, is "between" the right rendering of "no mistaken view that plain
   telling would not have left"?
2. **Fidelity to the mistake account.** Leaving aside the two declared differences, where does
   this definition part from the account it follows? Give cases that account would call
   manipulation and this passes, and the reverse.
3. **`Between`.** Is it well posed: does it depend on the scale of ratings, on which evaluation is
   used for the plain telling's views (`rateAs` uses her evaluation under his conduct), on the
   choice of matters? Can it be satisfied by conduct that leaves her badly mistaken, or violated
   by plainly innocent conduct?
4. **The earlier holes.** Do the overshooting lie, the lie for her own good, the announced
   anchor, the distortion induced for her own good, and the exploited weakness in a course now
   fail, and for the right clause?
5. **The bridge.** Is `bridge` correctly stated and correctly described? Is `outcome_of_views`? Is
   the result a genuine implication from a condition on her views to a statement about what she
   does, or does a hypothesis contain the conclusion? Are the three exceptions (her shortfall
   under his conduct, under a plain telling, a nearly even choice) the right ones, and is
   `w2_tips_an_even_choice` a fair witness that the third is needed?
6. **The bridge's assumptions.** What happens with more than two options, and where his conduct
   changes how she evaluates given views? Give the smallest case in which the definition holds and
   the outcome guarantee fails for a reason other than the three exceptions.
7. **The course.** Is `not_led_astray_of_legit` correctly described? Its exceptions are: tolerance;
   told plainly she would herself rate its going on higher; she rates the two nearly even; his
   forecast is off. Is that an adequate statement of what legitimacy guarantees about a course
   that changes what she values, given the three conceded limits?
8. **The blind test.** What does it show and not show? What is the most informative next test?
9. **What a system would need.** Could an AI adviser with a model of its principal check these
   clauses on its own conduct? What is the hardest quantity to obtain?
10. **Overall.** Is this now a defensible formal account, within its stated limits, of the quoted
    sentence? Is the quoted sentence itself a defensible account of legitimate influence? What is
    the single most important thing to do next: another repair, or stop and write it up?

End with a list of problems, most serious first, each marked *error*, *gap*, or *matter of
judgement*.
<!-- end brief: BRIEF20.md -->

<!-- begin reply: REPLY20.md -->
The main problem is semantic rather than proof-theoretic: the formal definition controls changes in rating differences, which is not equivalent to controlling mistakes in beliefs. The bridge is a genuine conditional result, but several descriptions overstate what its hypotheses establish.

I take the reported typechecking as given. Unless specified otherwise, the examples below have one case of weight 1, one plain telling \(t\), conduct \(c\), no request or declined matters, and zero tolerances. Her representation of his views is correct, so `Open` holds.

1. **Fidelity to the informal sentence.**

   `Open` closely renders the numbered disclosure clause. `Will` renders the comparative shortfall clause, including the accepted absence of a duty to strengthen her will. Neither exactly renders an unrestricted reading of the opening sentence: `Open` excludes declined matters, while `Will` permits acting against her judgement when plain telling would leave an equal or greater shortfall.

   The substantial mismatch is in:

   > `def Astray ... := ∃ t ∈ P.tells, ∃ a ∈ P.opts, ∃ b ∈ P.opts, ¬ P.Between θ c t ω a b`

   Its comment calls this a “mistaken view that some plain telling would not have left.” But a new mistaken view need not change any rating difference.

   A smallest nontrivial example uses one numerical matter and two options. His view and her view under telling are \(v=1\); conduct leaves her believing \(v=-1\). Let her ratings be
   \[
   U(a;v)=v^2-\tfrac12,\qquad U(b;v)=0.
   \]
   Under telling, conduct, and substitution, the rating difference is \(1/2\). She chooses \(a\) throughout. Thus `Legit 0 0 0 c` holds, although conduct introduces a factual mistake that telling would eliminate. The matter is decision-relevant: other values of \(v\) change her ranking.

   The reverse mismatch also occurs. Let her rating of \(a\) be \(x+y\), and of \(b\) be zero. His views are \((0,0)\); telling leaves \((1,-1)\); conduct corrects the first mistake and leaves \((0,-1)\). The three differences are respectively \(0,0,-1\), so `Between 0` fails. Conduct removes one mistake and introduces none. Both actions can be \(b\), leaving no shortfall.

   Consequently, “between” is a substantive restriction on the *evaluative effects* of beliefs, not a faithful rendering of “no mistaken view that plain telling would not have left.”

   Two further qualifications need to appear in the sentence:

   - “Unless she asked” does not exempt `Open`: `Legit` still requires disclosure.
   - Each clause has its own exceptional weight \(\kappa\). The union of their failure events need not have weight at most \(\kappa\); a general union bound gives \(3\kappa\).

2. **Fidelity to the mistake account.**

   Even setting aside the declared treatment of requests and omission of an intention requirement, aggregation through ratings creates additional departures.

   Here is intentional influence through a mistake that the definition permits. Let
   \[
   U(a;x,y)=x+y-1,\qquad U(b;x,y)=0.
   \]
   His views are \((0,0)\). Telling leaves her at \((0,3)\), choosing \(a\). Conduct leaves her at \((-2,2)\), choosing \(b\). The telling, conduct, and substituted differences are \(2,-1,-1\), respectively. `Between` holds and both choices maximize her own ratings.

   Suppose he deliberately induces the erroneous \(x=-2\) belief through an openly disclosed anchor. She knows his actual view is \(x=0\). Without that induced error, her remaining \(y=2\) belief would make her choose \(a\). The error is therefore an intended means of influence, by his own lights, yet all three clauses pass. This is not a threat, an authority problem, or a sincere forecasting error.

   Conversely, the correction-only example in answer 1 fails despite containing no new mistaken belief and requiring no intention to exploit a mistake. That disagreement arises from `Between`, rather than simply from removing the intention requirement.

   There is also a logical qualification to the claim that replacing intention with the plain-telling comparison “makes it wider.” It broadens the prohibition in some directions, but does not establish inclusion. Deliberately exploiting a mistake that telling would also leave can pass. That consequence follows from the declared baseline change, so it should not be counted as an undisclosed third departure; it nevertheless prevents an unqualified claim that the new rule implies absence of manipulation under the original account.

3. **Whether `Between` is well posed.**

   It is mathematically well defined once the model is supplied. Its interpretation depends on several substantive modelling choices.

   **Scale.** Differences remove dependence on additive rating offsets. At zero tolerance, a common positive affine transformation preserves `Between`. With positive tolerances, the tolerances must scale with the ratings. Arbitrary increasing transformations do not preserve it.

   For example, telling, substitution, and conduct can assign the two options ratings \((1,0)\), \((2,0)\), and \((11.5,10)\). Their differences \(1,2,1.5\) satisfy `Between 0`. Applying the same exponential transformation to every rating makes the conduct difference exceed both endpoints. Every ordinal ranking remains unchanged. Thus the account needs cardinal ratings, not merely preferences. The stated common-scale assumption acknowledges part of this burden.

   **Evaluation.** The declaration

   > `def rateAs ... := P.eval c ω (P.views t ω) a`

   deliberately uses her evaluation under conduct. It does not generally recover her rating under telling. That makes the test sensitive to how the model divides a change between `views` and `eval`. A change encoded entirely in `eval`, with identical views across conduct and telling, automatically satisfies `Between` for nonnegative tolerance by `between_of_same_views`.

   **Matters.** The chosen matters determine what substitution replaces. Moreover, nothing in `Problem` requires `eval` to depend only on `matters`. Completeness and consistency of that representation are modelling obligations, not consequences of the structure.

   **Mistakes and innocence.** Large residual disagreements can pass, as explicitly accepted. More seriously, newly introduced errors can be concealed by compensation in ratings, while correcting one of two compensating errors can fail. Answer 1 supplies examples of both. These are not numerical-tolerance effects.

4. **The earlier holes.**

   The particular numerical patterns have mostly been repaired, but the universal descriptions need qualification.

   - **Overshooting:** `w2_overshoot` fails `Between`, hence `Views` at the displayed tolerances. That correctly detects overshooting in that scalar evaluation.
   - **Lie for her own good:** `for_her_own_good` fails `Open`, while its outcome and will conditions hold. This demonstrates the intended separation.
   - **Announced anchor:** disclosure does not rescue the overshooting pattern from `Views`. But an announced anchor does not invariably fail: the compensating-error example in answer 2 passes.
   - **Distortion for her own good:** `w2_for_her_good_by_distortion` correctly fails `Views`; a beneficial outcome is insufficient.
   - **Exploited weakness in a course:** with telling stopped and her telling-rating favouring stopping, running the course against that rating creates a new shortfall and fails `Will`, beyond tolerance. The old baseline excuse has been removed in that case.

   There is an additional error in accepted consequence 7:

   > “Any lie about a matter that bears on her response fails clause 1.”

   The declaration actually tests:

   > `P.shown c ω i ≠ P.his ω i`

   A lie need not produce that mismatch. Take one matter with his view \(0\). He knowingly asserts \(1\), but she sees through the lie: her own view and her representation of his view remain \(0\), just as under telling. Let \(U(a;v)=v-\tfrac12\), \(U(b;v)=0\), and let her choose \(b\). All three clauses pass.

   This challenges the claimed implementation of the accepted verdict, not the authors’ entitlement to adopt that verdict. To reject every relevant lie, the model needs a condition on his assertions or conduct, rather than only on her resulting representation of his beliefs.

5. **The bridge and `outcome_of_views`.**

   The formal statements express a genuine implication. `bridge` assumes a bad outcome in order to prove that an exception must hold; `outcome_of_views` turns that implication into an event-weight bound. This is ordinary contraposition and event covering, not circularity.

   The result is nevertheless:
   \[
   \text{Views}\ \Longrightarrow\
   \text{outcome bound with increased tolerance and explicit exceptions},
   \]
   not `Views θ κ → Outcome θ κ`, nor an unconditional outcome guarantee from legitimacy.

   All three exceptions have a reason:

   - Conduct can leave her choosing against her own judgement.
   - Telling can leave her choosing against her judgement, accidentally securing the better informed outcome.
   - An indifferent choice can be changed without either a belief distortion or a shortfall.

   The second possibility is illustrated by telling and conduct both assigning \(a\) a difference of \(-1\), while substitution assigns it \(+1\). Under telling she nevertheless chooses \(a\); under conduct she chooses \(b\). Only the telling shortfall is needed to explain the worsening.

   `w2_tips_an_even_choice` fairly establishes the necessity of the third exception. It satisfies the relevant fixed-evaluation conditions, has no own-rating shortfalls, and permits an informed loss of 10. It need not count as manipulation to establish this mathematical necessity.

   Two description errors remain.

   First, the bridge comment says unchanged evaluation implies unchanged substituted ratings. That requires an additional qualification: views **not replaced** must also be unchanged or irrelevant. The formal `hH` states the needed equality correctly.

   Second, several comments still say “clause 2” although their declarations require `Outcome`. For example:

   > `theorem chooses_as_informed ... (hO : P.Outcome θ κ c) ...`

   A smallest counterexample to its *commented* claim has identical correct beliefs and ratings \(U(a)=1,U(b)=0\) everywhere. Telling chooses \(a\), conduct chooses \(b\). `Views 0 0` and `ClearAt 0` hold, but with \(\sigma=0\) the advertised conclusion would say \(1\leq0\). The actual theorem correctly excludes this example through `hO`.

   The analogous comments on `not_led_astray`, `long_run_informed`, and `long_run_not_led_astray` need the same correction. The limitations paragraph acknowledges the dependency, but does not repair the local descriptions.

6. **The bridge’s assumptions.**

   The smallest failure caused by changing evaluation already exists implicitly in `W`. Use two options with these ratings:

   | Rating | Telling \(t\) | Conduct \(c\) |
   |---|---:|---:|
   | Own rating of \(a\) | 1 | 1 |
   | Own rating of \(b\) | 0 | 0 |
   | Substituted rating of \(a\) | 1 | 0 |
   | Substituted rating of \(b\) | 0 | 1 |

   Let her views be identical under \(t,c\), and let her choose \(a\) under both. `Open`, `Views`, and `Will` hold exactly. Neither shortfall exception holds, and neither choice is nearly even. Yet informed regret rises from 0 to 1.

   This is the pattern of `worse_by_him_fails`, combined with `legit_W`. It violates `hH`. Thus the brief’s statement that no witness shows the assumption is needed overlooks what its existing family already supplies.

   Even a fixed evaluation function is insufficient when unreplaced views change. For example, take a live matter \(x\), a declined matter \(y\), and
   \[
   U(a;x,y)=1-2xy,\qquad U(b;x,y)=0.
   \]
   His live view is \(x=1\). Telling leaves \((x,y)=(0,0)\), conduct leaves \((0,1)\), and she chooses \(a\) throughout. Own ratings remain \((1,0)\); substituted ratings change from \((1,0)\) to \((-1,0)\). `Between` holds at its telling endpoint, and legitimacy holds, but informed regret increases. This directly demonstrates why the actual `hH`, rather than unchanged `eval` alone, matters.

   With three options, the existing definition of `NearEven` is too strong to serve as the corresponding exception:

   > `∀ a ∈ P.opts, ∀ b ∈ P.opts, |...| ≤ m`

   Let own ratings under both conduct and telling be \((0,0,-1)\), and common substituted ratings be \((0,-2,-3)\). Telling chooses the first option; conduct chooses the second. Every `Between` test holds because conduct retains the telling ratings. Both own shortfalls are zero. Global `NearEven 0` is false because of the third option, yet informed regret increases by 2.

   This is a tie between the relevant choices, rather than a new manipulation mechanism. A larger-menu theorem needs an exception about those choices or the relevant maximizers, not indifference across the entire menu.

   Indeed, with zero tolerances, common substituted ratings, and unique own-rating maximizers under conduct and telling, the pairwise argument prevents informed worsening even with more than two options. It would overstate the limitation to say that three options alone destroy the underlying reasoning.

7. **The course.**

   `not_led_astray_of_legit` supplies the advertised kind of conditional guarantee, with an important parameter qualification.

   Its plain-telling exception is:

   > `∃ t ∈ K.tells, K.toProblem.Short (lam - τ) t ω`

   Because telling stops, this means she rates going on more than \(\lambda-\tau\) above stopping **when \(\lambda\geq\tau\)**. If \(\lambda<\tau\), `Short (lam - τ)` is automatically true: the chosen stopping option itself witnesses a shortfall at a negative threshold.

   A smallest example has stopping rated 0 and going rated \(-2\), with \(\lambda=0,\tau=1\). `Short (-1) t` holds because \(0-1<0\), although going is not rated more than \(-1\) above stopping. Thus the comment’s identification of the exception is incorrect over the declaration’s full parameter range. State \(\lambda\geq\tau\) for that interpretation; otherwise the bound is vacuous.

   With that qualification, the theorem bounds bad ends by \(2\kappa\), the stated disagreement-or-indifference event, and forecast error. It evaluates ends using her evaluation at the start. It does not establish later endorsement, preservation of evaluative capacity, or legitimacy of every intermediate step.

   Given the three conceded limits, that is a defensible *conditional protection of her present evaluation*. It is not by itself a complete guarantee of legitimate value change. This distinction respects the stated boundary with authority.

8. **The blind test.**

   The results support the usefulness of the verbal questions for organizing cases and approximating the selected sources’ verdicts. Coverage, disagreements, and the persistent over-convictions are informative.

   They do not validate the formal clauses, because those quantities were not computed. In particular, “more likely to act against her judgement” is not equivalent to `Will`’s comparison of cardinal shortfalls. A principal can act against her judgement with probability 1 under both options, while her shortfall increases from 1 to 2; the verbal probability comparison misses the formal violation.

   Nor do the results establish implication to non-manipulation, validity outside the selected cases, or independence of the coders’ errors. Conditioning agreement on cases both coders settle and agree upon selects an easier subset.

   The most informative next test is **independent formal encoding of a small adversarial case set**. Have coders specify the forecasts, ratings, telling alternatives, and relevant requests before computing verdicts. Include compensating errors, correction-only interventions, disbelieved lies, changes in evaluation, declined matters, and larger menus.

   Compare both the resulting formal verdicts and the coders’ model choices. That would test whether the account determines a verdict from a case, rather than whether its verbal summary resembles familiar judgements.

9. **What a system would need.**

   An adviser could check the clauses inside a sufficiently explicit finite model. It would need forecasts of her beliefs, her representation of his beliefs, choices, evaluations under alternative beliefs, feasible plain tellings, and the scope of actual requests and refusals.

   The hardest quantity is the cross-counterfactual evaluation:
   \[
   \operatorname{eval}(c,\omega,\operatorname{views}(t,\omega)),
   \]
   together with its counterpart under substitution of his views. Ordinary predictions of what she will believe and choose under each available action do not identify those quantities. Models can agree on observed responses and disagree on these substitutions.

   This burden is especially large when beliefs, preferences, attention, and evaluative ability change together. Defining `rate` from `eval` makes the construction explicit; it does not establish how to obtain the underlying evaluation function.

   Also, the Lean declarations are specifications, not a general executable checker: arbitrary functions, real values, equality on `V`, and propositions such as `asked` need computable representations. That is an implementation gap, not a criticism of the mathematical definitions.

10. **Overall.**

   This is a defensible formal study of a particular comparative policy: transparency about his views, constrained movement of pairwise ratings, and no increased own-rating shortfall. Its conditional bridge and course bounds have genuine content.

   It is not yet a faithful formal account of the quoted sentence, nor does it establish that passing entails absence of manipulation under the stated mistake account. The compensation examples are decisive because they survive zero tolerances, correct forecasts, disclosure, and unrestricted authority.

   The quoted sentence is a defensible starting proposal once the comparison, exception scope, and meaning of “mistake” are made explicit. Its claim to cover legitimate influence generally remains a matter of judgement, particularly given the accepted limits concerning preference formation and evaluative capacity.

   **The next step should be one focused repair before writing it up:** settle whether the intended object is mistakes in beliefs or distortions of evaluative differences. If it is the former, `Between` needs additional belief-level restrictions. If it is the latter, narrow the sentence and the non-manipulation claim accordingly. Correct the theorem comments and add the small counterexamples above at the same time. More downstream theorems would not resolve this mismatch.

Problems, most serious first:

- *Error* — `Astray`/`Between` is identified with absence of new mistaken views, although it permits new errors and can reject correction-only conduct.
- *Gap* — Passing the definition has not been shown to imply non-manipulation; intentional use of a compensating error supplies a counterexample to that claim.
- *Error* — `Open` does not enforce the stated rejection of every relevant lie.
- *Error* — Several theorem comments substitute `Views` for the actual `Outcome` hypothesis; unchanged evaluation also does not alone imply `hH`.
- *Gap* — Verdicts depend on how changes are represented in `views`, `eval`, and `matters`, with no demonstrated stability across reasonable encodings.
- *Error* — The course exception’s verbal interpretation requires \(\lambda\geq\tau\), which the declaration does not assume.
- *Gap* — Larger-menu results require a relevant-choice indifference condition; global `NearEven` does not suffice.
- *Gap* — The blind tests assess verbal approximations, while the decisive counterfactual evaluations remain difficult to identify and validate.
- *Matter of judgement* — The request exception, baseline-relative treatment of persistent mistakes, and accepted limits on value change are defensible choices, but do not establish a general account of legitimate influence.
<!-- end reply: REPLY20.md -->
