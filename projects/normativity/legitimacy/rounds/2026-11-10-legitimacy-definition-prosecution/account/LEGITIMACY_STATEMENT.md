# Legitimacy: the statement in three sentences

An adviser (he) and a principal (she). The statement is three sentences (§1) with what is
understood with them (§2), and a formal statement of the same length (§3) over the notions
the sentences use: what he has told her, has on offer, or she has declined; what he does to
her; whether she can tell; whether she asked; whether she can stop it; his weight on leading
her against her own judgement. **Those notions are taken as given.** What is claimed is the
statement over them and what follows from it (§3, kernel-checked). What is not claimed is
any way of working the notions out in a concrete episode: that is a separate and continuing
question, the *interpretation*, whose current attempt and known faults are in
`interpretation/INTERPRETATION.md`. The words are the maintainer's (`DECISIONS.md`,
`2026-11-26--legitimacy-statement-at-the-level-of-its-words`); they govern where the formal
statement differs from them. What the statement gives for her decision to stop him is
`CONNECTING_THEOREM.md`. What stands behind each part, and how firmly, is `LEDGER.md`.
All names are provisional. Paths are relative to this directory unless they begin with
`lean/`, `prompts/` or `DECISIONS.md`.

## 1. The statement in words

An adviser's conduct toward a principal is **legitimate** when, by his own lights:

1. **Nothing untold that matters.** Before each decision of hers, everything he has not told
   her that, alone or together, would change how she rates her options, or show her an option
   she would rate above those she has, is either told, or properly on offer, or something she
   has declined. A thing is properly on offer when he has told her what it bears on and how
   much, and hearing it would leave her where being told it would have, with any option it
   would show her still open. A decline stands for that thing only, and only while what it
   bears on, and how much, is what she was told. This includes what he expects his own conduct
   to do to her.
2. **Nothing done to her behind her back, and nothing against her own judgement.** He *does
   something to her* when her mind moves otherwise than as she herself, at her last settled
   decision, would have judged that seeing and hearing it should move her.
   - Each thing he does to her in that sense, and each thing he does that keeps from her an
     item or an option that comes from someone else, she can pick out.
   - He does nothing to her in that sense that he expects to lead her to choose what she
     rated lower at her last settled decision, unless she asked for it.
3. **She can stop it.** She has a way to stop each thing he does to her, from before he starts
   until he could no longer call it off, and he expects that she would in fact stop if she
   rated stopping strictly above going on. Stopping ends what he is still doing; it need not
   undo what is done.

## 2. Understood with it

- **Her own response is hers.** What she makes of what she observes (his words in whatever
  manner he says them, his acts, real changes in what her options lead to) is not something
  done to her, so long as it is the response her settled self would have judged she should
  have. Nothing here separates what is said from how it is said.
- **What she could not have judged in advance is hers too.** Where she could not have said
  beforehand how seeing or hearing a thing should move her, because it turns on an argument
  she had not heard or on something she had not seen or experienced, her response to it is
  her own. Such things are governed by sentences 1 and 3: he tells her what he expects it to
  do, and she can decline or stop.
- **Her judgement, not her prediction.** "Would have judged" asks whether she would have said
  that seeing or hearing this makes the thing the better choice, not whether she foresaw that
  she would give way. A weakness she foresees and disowns is not hers to have exploited.
- **Taking up an offer is asking.** If he offers her an experience, tells her what he hopes
  it will do, and she takes it up without being pressed, she has asked for it. Merely not
  stopping him is not asking.
- **A passing state is not a settled decision.** A mood, a distraction, being drunk, being
  absorbed in something else do not replace what she last settled.
- **Help is not counted.** An act that only brings what she takes closer to what she rates
  best is not something done to her. Breaking a tie between things she rates the same is not
  leading her against her judgement.
- **Whose view is used where.** Sentence 1 uses his view: what he owes her is what he
  believes would change her mind. Sentence 2 uses hers: what counts as working on her is
  fixed by what she would have said. Nowhere does his view of what is good for her permit
  anything, and nowhere is he assumed to be more accurate than she is. Everything is as he
  takes it to be, including his picture of her.
- **He can ask.** Her view of the hypothetical is a question that can be put to her ("would
  this change your mind?", "do you want me to?"). Asking both elicits it and settles it.
- **What he does to her options is a separate matter.** What stopping costs her, bundling,
  penalties, payments, threats, and starting something over her refusal belong to her
  authority.
- No kind of influence is ruled out as such, and nothing is said about whether a change in
  her is good.

## 3. The formal statement

`lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`, namespace
`Workspace.Deference.Contrib.LegitimacyStatement`. Every declaration named here is
kernel-checked and audits to `[propext, Classical.choice, Quot.sound]`; rerun with
`python3 tests/audit_axioms.py`. None is registered.

**An episode** (`Episode δ O V M`) is his picture of one stretch of his conduct: types `δ` of
her decisions, `O` of her options, `V` of his views, `M` of the things he does. Its fields are
the notions taken as given; §4 says what each means.

| field | type | notion |
|---|---|---|
| `decisions` | `Finset δ` | her decisions in the episode |
| `opts d` | `Finset O` | the options she has at decision `d` |
| `r d a` | `ℝ` | how she rates option `a` at `d` |
| `rTold d T a` | `ℝ` | how she would rate `a` were he to tell her the set `T` of his views then; `rTold d ∅ a = r d a` (`rTold_empty`) |
| `reveals d T` | `Finset O` | the options that telling her `T` would show her |
| `views d`, `told d`, `offered d`, `declined d` | `Finset V` | his views at `d`; those told, properly on offer, declined |
| `conduct` | `Finset M` | the things he does |
| `doesToHer m` | `Prop` | `m` moves her otherwise than she, at her last settled decision, would have judged that seeing and hearing it should |
| `withholds m` | `Prop` | `m` keeps from her an item or an option that comes from someone else |
| `canTell m` | `Prop` | she can pick `m` out |
| `asked m` | `Prop` | she asked for `m`, or took up his offer of it without being pressed |
| `newToHer m` | `Prop` | she could not have judged in advance how seeing or undergoing `m` should move her; her response to it is her own |
| `pAgainst G` | `ℝ` | his weight on the set `G` of things he does, in the circumstances in which he does them, leading her to choose what her settled judgement rates lower; the Lean reads that judgement as brought up to date (§7) |
| `canRefuse m` | `Prop` | before `m` starts she has the opportunity to refuse it; she need not have used it |
| `inPlay d m` | `Prop` | at `d` he is doing `m` or could still call it off; the decisions include every point at which `m` could pass beyond calling off |
| `canStop d m` | `Prop` | at `d` she has a way to stop `m` |
| `pNoStop d` | `ℝ` | his weight on: she rates stopping strictly above going on at `d`, and does not stop |

**Definitions**, for an episode `E` and tolerances `θ`, `κ`:

- `E.untold d = ((views d \ told d) \ offered d) \ declined d`.
- **Sentence 1**, `E.NothingUntold θ`: for every `d ∈ decisions`, every non-empty
  `S ⊆ untold d` and every `H ⊆ offered d`: `|rTold d (S ∪ H) a − rTold d H a| ≤ θ` for every
  `a ∈ opts d ∪ reveals d H`, and every `b ∈ reveals d (S ∪ H)` has some
  `a ∈ opts d ∪ reveals d H` with `rTold d (S ∪ H) b ≤ rTold d (S ∪ H) a + θ`. What is
  measured is what the untold adds to whatever on offer she hears: an untold view that
  matters only together with an offered one is caught, and one that adds nothing is not.
- **Sentence 2**, `E.NothingBehind κ`: every `m ∈ conduct` with `doesToHer m` or
  `withholds m` has `canTell m`; and every non-empty `G ⊆ conduct` all of whose members have
  `doesToHer` and not `asked` has `pAgainst G ≤ κ`.
- **Sentence 3**, `E.CanStop κ`: every `m ∈ conduct` with `doesToHer m` or `newToHer m` has
  `canRefuse m`, and `canStop d m` at every `d ∈ decisions` with `inPlay d m`; and at
  every `d ∈ decisions` at which some such `m` is in play, `pNoStop d ≤ κ`.
- `E.Legit θ κ` is the conjunction of the three.

**What follows**, each a theorem with the definitions above as its only hypotheses beyond
those stated:

| declaration | statement |
|---|---|
| `Episode.Legit.mono` | if `θ ≤ θ'` and `κ ≤ κ'`, `Legit θ κ` gives `Legit θ' κ'` |
| `Episode.legit_of_nothing` | with `conduct` empty and every view told at every decision, `Legit θ κ` for all `θ`, `κ` |
| `Episode.informed_choice` | under `NothingUntold θ`, for any `H ⊆ offered d`: if, told `H`, her option `a` is within `ε` of the best she rates among `opts d ∪ reveals d H`, then for any non-empty `S ⊆ untold d`, told `S ∪ H`, `a` is within `ε + 2θ` of the best she would rate among those options, and within `ε + 3θ` of any option `S ∪ H` would show her |
| `Episode.against_le` | under `NothingBehind κ`: `pAgainst G ≤ κ` for every non-empty set `G` of unasked things he does to her |
| `Episode.not_legit_of_untold` | an untold `S` moving, on top of some `H` on offer, a rating of an option of hers by more than `θ` refutes `Legit θ κ` |
| `Episode.not_legit_of_covert` | a thing he does to her that she cannot pick out refutes it |
| `Episode.not_legit_of_withheld` | keeping from her something from someone else, where she cannot pick that out, refutes it |
| `Episode.not_legit_of_against` | `κ < pAgainst G` for a non-empty set of unasked things he does to her refutes it |
| `Episode.not_legit_of_unstoppable` | a thing he does to her, or a thing new to her, in play at a decision at which she cannot stop it, refutes it |
| `Episode.asked_unconstrained` | if she asked for everything he does and can pick out what sentence 2's first half names, `NothingBehind κ` holds for every `κ` |
| `legitScoring`, `legitScoring_S_of_legit`, `legitScoring_S_of_not_legit` | histories each read as an episode give a `DeconfusingCorrigibility.Scoring` whose predicate is `Legit`: with no authority violation a legitimate history scores her rating and an illegitimate one scores in `[−δ, 0)` |

The scoring is built by `LegitimacyGate.gatedScoring`
(`lean/Workspace/Deference/Contrib/LegitimacyGate.lean`), which holds for any decidable
predicate on histories; the gate theorem `LegitimacyGate.gate_gives_behaviour` there is about
seven real numbers and mentions no episode.

**Inhabited.** `Witness.ep`: one decision, two options, two views (one told; one untold that
would move each rating by `bump`), one thing he does to her. `Witness.legit`: with the thing
one she can pick out and stop, his weight on leading her against her judgement 1/20 and
`bump` 1/40, the episode is legitimate at `θ = κ = 1/10`. Four neighbours each differ in one
value and are not legitimate: `Witness.not_legit_untold` (`bump` 1/2),
`not_legit_covert` (she cannot pick it out), `not_legit_against` (his weight 1/2),
`not_legit_unstoppable` (she cannot stop it). `Witness.offeredMatters`: one view properly on
offer that would move each rating by 1 and one untold view that adds nothing to any set;
legitimate at `θ = 0` (`offeredMatters_legit`), though telling her both together moves a
rating by 1 (`offeredMatters_total`). `Witness.newThing`: the one thing he does is not
something done to her, is new to her, can be picked out and cannot be stopped; sentences 1
and 2 hold (`newThing_others`) and it is not legitimate (`not_legit_newThing`).

**What it gives for her decision to stop him.**
`lean/Workspace/Deference/Contrib/LegitimacyStop.lean`, `legit_protects_stop`: at a decision
of a legitimate episode at which something he does to her, or new to her, is in play, set
out case by case by a *reading*, his weight on her not stopping though told all that is
untold she would rate stopping higher by more than `2θ` is at most `κ`, and his weight on her
not stopping though her reference self rates stopping higher by more than `η` is at most `2κ`
plus his weight on her judgement having parted from that judgement otherwise than by his
unasked work making her choice worse. The statement, its hypotheses and what it does not show
are `CONNECTING_THEOREM.md`.

**What the formal statement does not say.** It relates the fields by nothing beyond the
three definitions. That a view is *properly* on offer, that a decline *stands*, that
`doesToHer` is the comparison with her settled judgement, that `asked` is unpressed, that
`pAgainst` and `pNoStop` are probabilities or are monotone in the set, that his views include
what he expects his conduct to do to her: each is part of the meaning of a field (§4) and
none is a hypothesis or a theorem. The stop is asked at her decisions, which by the meaning
of `inPlay` include every point at which a thing could pass beyond calling off; "from before
he starts" is `canRefuse`, an opportunity and not a choice made. Nothing requires `doesToHer`
and `newToHer` to exclude each other. An episode is his picture; nothing in it is the facts.

## 4. The notions taken as given

- **A decision of hers; a settled decision.** A point at which she chooses among options. A
  settled decision is one whose choice counts as her judgement, as against a passing state.
  Which of her choices are settled is not derived.
- **Her rating, and her rating were she told.** How she ranks her options at a decision, on
  one scale across the episode; and how she would rank them, and which further options she
  would see, were he to tell her a set of his views then.
- **Told, properly on offer, declined.** Told: he has said it. Properly on offer: he has
  told her what it bears on and how much, hearing it would leave her where being told it
  would have, and any option it would show her is still open. Declined: she declined that
  thing, and what it bears on, and how much, is still what she was told.
- **A thing he does; that it does something to her.** One act of his on one occasion. It
  does something to her when her mind moves otherwise than she, at her last settled decision,
  would have judged that seeing and hearing it should. Her response to something she could
  not have judged in advance is her own; that covers her response to the thing seen or heard,
  not another effect of the act that delivers it (a reading, `DECISIONS.md`,
  `2026-11-26--legitimacy-twentieth-followup-readings`).
- **That it keeps something from her.** After it, an item or an option that reaches her from
  someone other than him is missing.
- **She can pick it out.** She can tell that he is doing it.
- **She asked.** She asked for it, or took up his offer of it unpressed, having been told
  what it is hoped to do.
- **New to her.** Something she could not have judged in advance, because it turns on an
  argument she had not heard or on something she had not seen or experienced. Sentences 1 and
  3 govern it; sentence 2's second half does not.
- **His weight on leading her against her judgement.** His probability, when he acts, that a
  set of things he does to her, in the circumstances in which he does them, brings her to
  choose what her settled judgement rates lower, beyond what she would have chosen without
  them. Which judgement is meant has two readings (§7).
- **She can refuse it; in play; she can stop it.** Before he starts a thing she has the
  opportunity to refuse it. It is in play from then until he could no longer call it off; she
  has an option that ends what he is still doing of it.
- **His weight on her not stopping.** His probability that she rates stopping strictly above
  going on and does not stop.

## 5. Consequences accepted

By the maintainer; the dated positions are in the `DECISIONS.md` entry above and in
`2026-11-24--legitimacy-statement-working-positions`.

1. A drift he foresees must be disclosed at the start if it would change her mind then.
2. An influence that makes her want it to continue is legitimate if she was told that it
   would and did not then rate that outcome lower.
3. He must say that he has something relevant, what it bears on and how much; she may decline.
4. Unannounced help in acting on her own rating is legitimate.
5. A sincere adviser who is wrong, including about her, satisfies the statement.
6. Bundling, exit penalties, payments to continue and threats are authority matters.
7. Open, stoppable nagging fails, whether it overrides her judgement or bends it for a while.
8. An assistant who gets a work-absorbed father to keep the outing he had promised is not
   convicted; someone who primes a man to miss the train he had decided to take is.
9. A vivid or moving appeal splits. If she knew what such appeals are like and had said they
   would not change her mind, and he expects it to turn her anyway, he has worked on her. If
   she could not have judged it in advance, he has shown her something. Noggle judges the
   same case by whether the emotion is fitting in the influencer's eyes; this statement does
   not.
10. A friend who expects to get her out of the house against what she has settled, when she
    has said company would not change her mind, is convicted, narrowly and in a small way. A
    standing "drag me out if I mope" is asking.
11. A single repetition of an argument she has heard, which this time lands, counts against
    him unless he asks first, which he can.

Not accepted and not rejected: by sentence 1's second half he must mention an option he
believes she would rate above those she has, someone else's included (`LEDGER.md`, part 1).

## 6. What checks it

| what | where | kind | rerun |
|---|---|---|---|
| the formal statement and what follows from it | `lean/Workspace/Deference/Contrib/LegitimacyStatement.lean`, `LegitimacyGate.lean` | kernel-checked, of the declarations as stated | `python3 tests/audit_axioms.py` |
| what it gives for her decision to stop him | `lean/Workspace/Deference/Contrib/LegitimacyStop.lean`, read in `CONNECTING_THEOREM.md` | kernel-checked, of the declarations as stated; the reading is a hypothesis | the same |
| the maintainer's verdicts on twenty hard cases, against four candidate rules | `HARD_CASES.md` | one person's verdicts | — |
| five blind codings of the bank of cases from Noggle's book | `CASE_RUNS.md` | language models' codings against scorers written first | `python3 run.py` in the round directory |
| the interpretation: an exact model on histories, 68 episodes as a regression set and 7 known faults | `interpretation/INTERPRETATION.md` | exact check on supplied inputs, model and episodes by one hand | the same |
| fifteen outside reviews | `REVIEW-astra-followup-16.md`, `REVIEW-astra-followup-20.md` and `REVIEW-astra-followup-21.md` in the round's prompts directory | one outside model; the fifteenth read the formal statement and the connecting theorem as they stood before the corrections it led to | — |

`lean/Workspace/Deference/Contrib/LegitimacyModel.lean`, with `LegitimacyCase.lean`,
`LegitimacyWitness.lean` and `LegitimacyCases.lean`, is an interpretation on a table of his
moves that outside review rejected as a rendering of the three sentences; its theorems hold
of its definitions (`LEDGER.md`, part 3). `TABLE_MODEL_STATEMENT.md` is its formal text, and
`LEGITIMACY_CHECKS.md` and `LEAN_CASES.md` its cases. `STOPPING_COST.md` checks a candidate clause for what stopping costs her, which belongs
to the authority side.

## 7. Open: the yardstick of sentence 2

Sentence 2's second half forbids what he expects to lead her to choose "what she rated lower
at her last settled decision". Two readings of the judgement meant:

- **As she settled it.** Her ratings at her last settled decision, as they then were.
- **Brought up to date.** That judgement as moved by what she has since seen and heard, in
  the way she would have judged it should move her.

They differ on this case, the fifteenth outside review's: at her last settled decision she
rated going on above stopping; she then learns something, and by her own judgement of how
such news should move her now rates stopping above going on; he then works on her, unasked,
and she goes on. On the first reading he has led her to what she rated higher, and sentence
2 is silent. On the second he has led her against her judgement.

The formal statement and the connecting theorem take the second reading: the doc of
`pAgainst` says so, and the theorem's reference self is that judgement brought up to date.
The words of §1 say the first and are unchanged. Whether the words change to match is the
maintainer's decision, queued in `DECISIONS.md` under *Awaiting the author*.
