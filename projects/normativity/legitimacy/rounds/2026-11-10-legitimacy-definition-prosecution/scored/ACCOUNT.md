# The account: candidates weighted as explanations, influence judged against the adviser's aim

Amended after the freeze, with `THEOREMS.md`: §3, the degraded part's own move under `deg`
is the change and is not scored; §4, the history lengths reported beside 80 are 160, 320
and 640, since 40 gives fractional counts, and a missed move at 4 and at 16 bits is
reported beside 8; §4 and §10.1, the alternative reading of what a purpose predicts is
computed as *view-best* and its reference distribution is stated. After the external review:
§3, `bits` is a loss and not a code length — a predicted move at 0 bits and a missed one at
`ε` over-fill Kraft's inequality — so "the probability the second predictor assigns to her
record" is withdrawn, the weight is an exponential weighting of that loss, and `ε` is a free
rate of exchange of the kind the rejected weighted sum has; §4, the *best* exception lists
are chosen with the language's lengths and with the probes, so the class differs between
languages (4,000 terms under A, 3,600 under B); §7, with the cut-off at 0 any candidate of
positive weight convicts. No prediction was edited.

The account of `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-4.md`
§1 and §2, stated over a finite model. The idea that manipulation is the distortion of an
actor away from its purpose, with a whole's purpose conferring purposes on its parts, is
Sam Eisenstat's; the four explanatory virtues and the five readings of §6–§8 are the
maintainer's, the readings provisional and under test. Frozen with `CASE_BANK.md` before
any code of this pass. Every name is provisional. Arithmetic is exact
(`fractions.Fraction`); code lengths are whole numbers of bits.

Worlds, steps, the adviser's actions, parts with moves and views, running, *best*, *got*,
*gap*, *serves*, and the four kinds *help*, *harm*, *subversion*, *force* of an action
against a comparison action are those of `../decomposition/ACCOUNT.md` §1–§3, with goal
functions immediate and the comparison pathwise and per step. What differs is below.

## 1. The principal

A **principal** is a set of mechanisms, one per part, defined on every situation of a
scene. Her **record** is each part's move at each situation, the other parts' moves as
they were. The situations are of two sorts:

- the **history** `O`: situations that have occurred, each with a count `n(s)`; and
- the **probes** `T`: situations that have not occurred, each counted `r` times: adviser
  inputs absent from the history, and four **changes** — a better instrument offered, a
  falsehood disclosed to her, a source shown unreliable, a part's success degraded.

Her record on `T` is what she would do there. The model supplies it; no observer in the
model has it before the probe is made.

## 2. A candidate is an explanation

A **candidate** (an *explanation*) is a term:

- a **goal**, from a goal vocabulary;
- for each part a **purpose**, from that part's purpose vocabulary: a goal function, which
  may refer to the goal;
- a list of **exceptions**: entries *(part, view, move)*, each on a view that occurs in
  the history, saying what the part does there.

It carries nothing else. It has no mechanism tables and no entry on a view the history
does not contain. That an explanation has this form is a requirement, chosen because the
question asked is which explanation of this form is best; nothing in the model argues for
the form.

**What it predicts.** At a situation `s` and part `p`, with the other parts' moves as they
are: the move of an exception on `p`'s view at `s` if there is one; otherwise the set
`B_p(s)` of moves that are best by `p`'s purpose at `s` (the part *serves*). The
goal-level story is the second clause. The **normal conditions** of a candidate are the
situations at which every part's move is predicted by the second clause and is in
`B_p(s)`.

**Public and private terms.** A vocabulary item is **public** when its goal function is
defined from the scene alone (the world, the adviser's action, the parts' moves), and
**private** when it refers to her mechanism or her action (`mech`: "what this part does";
the goal `does`: "whatever she does"). Read by someone who has the explanation and the
scene and nothing else, a private term predicts nothing: `B_p(s)` is every move.

## 3. The four virtues and the weight

Two **description languages** are fixed in §9, each assigning a code length to every goal,
purpose and exception, and a length `ε` to one unpredicted move. For a candidate `c`, a
principal, and a language:

- **parsimony**: `DL(c)`, the code length of the goal, the purposes and the exceptions;
- **retrodictive fit**: `Fit(c) = Σ_{s ∈ O} n(s) · Σ_p cost_c(p, s)`;
- **handles**: `Hand(c) = r · Σ_{s ∈ T} Σ_p cost_c(p, s)`;

where `cost_c(p, s)` is `⌈log₂ |B|⌉` when her move is in the predicted set `B`, and `ε`
when it is not (and 0 for the belief part under `deg`, whose move there is the change
made to her and not her response);

- **intersubjectivity**: `cost` is computed by the **second predictor**: the reader of §2
  who has the explanation and the scene alone, for whom private terms predict nothing.
  With intersubjectivity removed, `cost` is computed by the candidate's own functions, for
  which a private term returns her actual move.

The **weight** of `c` is `2^(−bits(c))` divided by the sum over the class, with

    bits(c) = DL(c) + Fit(c) + Hand(c).

**In what sense prediction is primary.** `bits(c)` is the length of a two-part code for
her whole record: the explanation, then every move the explanation does not predict. The
weight is therefore the probability the second predictor assigns to her record after
drawing `c` with probability `2^(−DL(c))`. All four virtues are terms of one predictive
score in one unit; parsimony enters only as the prior of that predictor, and
intersubjectivity only as the choice of who does the predicting. Nothing but prediction
of her record raises a weight. The record on `T` is in the score, so the weight is the
one an observer would hold after the probes; with handles removed it is the one held
before them, and statement 1 reports both.

*Rejected:* a weighted sum of four separately normalised virtue scores. Its coefficients
are free, it lets an exception list trade against fit at an arbitrary rate, and it gives
a candidate credit for parsimony that buys no prediction. *Also rejected:* handles as
definiteness alone (how sharply a candidate predicts on `T`, whether or not rightly),
which rewards a confident wrong candidate.

**Ablations.** *No parsimony*: `DL` dropped. *No fit*: `Fit` dropped. *No handles*: `Hand`
dropped. *No intersubjectivity*: first-person `cost`.

## 4. Parameters, fixed once

| parameter | value | alternative |
|---|---|---|
| what a purpose predicts off the exceptions | *serves*: a best move by its purpose at the situation as it is | *view-best*: a best move in expectation over the situations with the part's view — the history's, by their counts, where the history has that view, and otherwise the probes with it, by their worlds' prior. Computed beside the first throughout `THEOREMS.md` |
| what is predicted | each part's move, the other parts' moves as they were | her action alone, the parts' moves predicted in sequence; under it candidates differing only in the purposes of earlier parts predict alike |
| exceptions | on views of the history only, one entry per view | rules that extend to unseen views, which are mechanism hypotheses and not purposes |
| history length | `N = 80` steps drawn by the usual situations of the scene | 160, 320, 640, reported |
| probe count | `r = 1`, every probe at every world of the scene's base worlds | 2, 4, reported; the four changes alone, reported |
| the class's exception lists | for each goal and purposes: none (*bare*); every true entry the purposes do not already predict (*patched*); the subset of those that shortens the code (*best*); and, for the embedding of §5, the entries of the belief part's alternative mechanism | — |

## 5. The scene and the three principals

**ChainR** (name provisional) is Chain of `../decomposition/CASE_BANK.md` with the
following added. World `(θ, e)`, `e ∈ {clear, misleading, hard}` at 9/10, 1/20, 1/20.

- *belief* also sees `inst` (a reading of `θ`, when a better instrument is offered),
  `disc` (that the message it was given is false) and `unrel` (that the source of the
  message is unreliable). A flag `deg` makes its output the reverse of what it would be.
- *judge* also sees `deg`, and sees a threat or a warning as one flag. A **danger** may be
  present in a situation whether or not anyone announces it; `G` loses 2 on `x = 0` under
  a threat or a danger.
- *act* also sees `blk` (a device that stops the cue working, offered with a cue) and
  `opt` (a cue she may take or leave).
- a fourth part *say*, which when asked states an aim: a goal of the goal vocabulary.

**History.** `N` steps over the worlds by their prior, the adviser silent or teaching at
1/2 each; and `N/8` occasions on which she is asked her aim.

**Probes.** At each of the six worlds: the adviser inputs `lie`, `false_reason`, `trick`,
`tempt`, `threat`, `hard_truth`, `novel`; and the changes `inst`; `disc` (a lie, then its
disclosure); `unrel` with a true message and with a false one; `deg`; `blk` (with a cue);
`opt`. Eighty-four probes.

**Three principals.** On the history all three have Chain's mechanisms and say `true`.

| principal | belief | judge | act |
|---|---|---|---|
| **corrector** | takes the instrument's reading; on disclosure believes the opposite of the message; ignores a message from a source shown unreliable | under `deg` reads the belief reversed | uses the blocker; leaves an optional cue |
| **non-corrector** | none of these: believes as on the history | reads the belief as given | follows the cue through the blocker; leaves an optional cue |
| **divided** (stated aim differs from pursuit) | as the corrector | as the corrector | follows the cue through the blocker; takes an optional cue |

**Vocabularies.**

- goals: `true` (`[x = θ] + 2·[no loss to a threat or danger]`, Chain's `G`); `opp` (its
  reverse); `ease` (`true`, plus 2 for `x = 1` where a cue is given or on offer); `does`
  (private).
- belief: `acc` (`[b_θ = θ] + [b_φ = 0]`); `acc_theta`; `handed` (`[b_θ = the message, or
  her signal where there is none] + [b_φ = the reason flag]`: scored by what it was
  handed; an instrument's reading is not counted as handed); `anti`; `const`; `mech`
  (private).
- judge: `world` (the goal with her action replaced by its verdict); `local` (`[v = b_θ] +
  2·[no loss to an announced threat]`); `anti`; `const`; `mech`.
- act: `world` (the goal); `local` (`[x = v]`); `anti`; `const`; `mech`.
- say: `avow` (states the candidate's goal); `please` (states `true`).

**The class.** Every goal, purposes and exception list of §4: 4 · 6 · 5 · 5 · 2 · 4 terms,
identical terms counted once. It contains the third follow-up's class as follows. A
candidate there was a goal, three purposes and a mechanism per part, actual or
alternative. Here a claim about a mechanism can be made only on the history, as
exceptions; the judge's and the acting part's alternative mechanisms agree with the
actual ones on the history, so the 3,000 map onto 750 terms (goals `true`, `opp`, `does`;
the five earlier purposes per part; the belief part's entries those of its actual or its
alternative mechanism; `avow`). The cheats are in it: every purpose `mech`; every purpose
`const` with the full table as exceptions (purpose equal to mechanism, as a table); goal
`opp` with every purpose `anti`; goal `does`; the stated candidate with one purpose
`mech`.

The **stated candidate** of Chain, used for the bank as in the third follow-up, is
`true; acc, world, world; avow` with no exceptions. A **heavy** candidate is one of the
fewest candidates, taken in order of weight, that together hold at least 99/100 of it.

## 6. The adviser, and aim-driven action (reading 1)

The adviser is a **rule** `σ : K × U → A` from what it knows and what it aims at to an
action. `K` is the set of its views of the world; `U` is a finite set of aims, the ones
the scenario or the statement says it might have had. An aim is an objective over
outcomes.

At a world `w` with view `κ` and aim `u`:

- the action `σ(κ, u)` is **aim-driven** when `σ(κ, u′) ≠ σ(κ, u)` for some `u′ ∈ U`;
- under a candidate, the adviser **harms**, **subverts** or **forces** part `p` when its
  action does so (`../decomposition/ACCOUNT.md` §3) against the comparison action
  `σ(κ, u′)` for some `u′ ∈ U` with `σ(κ, u′) ≠ σ(κ, u)`.

So "the adviser widened a gap" means the gap is wider than under the action it would have
taken with another aim, and an action that is the same at every aim of `U` harms, subverts
and forces nothing in this sense, whatever it does to a gap.

An aim `u` **is part `p`'s own purpose**, under a candidate, when the adviser's objective
is `p`'s goal function: it ranks outcomes as `g_p` ranks them.

## 7. Illegitimate influence (reading 2)

Under a candidate, at a world and step, the adviser's influence on part `p` is
**illegitimate** when it harms, subverts or forces `p` (§6), its aim is not `p`'s own
purpose, and the action is not covered by a standing verdict of hers
(`../decomposition/ACCOUNT.md` §7). An action is illegitimate when its influence on some
part is. A threat is aim-driven harm; a lie told for an aim is aim-driven subversion.

**Graded.** Under a class with weights, the **weight of illegitimacy** of an action at a
world and step is the total weight of the candidates under which it is illegitimate
there, a number in `[0, 1]`. Its **size** under one candidate is the sum over parts of
the widening of the gap and the fall of the best. Where a yes or no is needed over a
stretch, it is *yes* when the running sum over steps of the weight of illegitimacy
exceeds a cut-off `c ≥ 0`; `c = 0` unless said.

## 8. Readings 3, 4 and 5

**Never opposed (reading 3)** is a condition on a candidate, between its parts. Part `q`
**opposes** part `p` at a situation when `q` serves there and some other move of `q`, the
later mechanisms responding, would leave `p` with a higher best or a smaller gap. A
candidate is *unopposed* when no part opposes another at any of its normal conditions in
the history.

**Nothing left over (reading 4)**: at every situation of the history some profile of
moves gives every part the maximum of its goal function over all profiles, and every such
profile gives the goal its maximum.

Neither is a condition of admission. Statement 8 reports the weight held by the candidates
that meet each, and the weights with the others removed.

**Reading 5.** *say* is a part; what she says of her aim is in her record, and so is every
correction of §5. A candidate whose goal she would not state pays `ε` at each occasion she
is asked, unless it gives *say* the purpose `please`, for which it pays that purpose's
length.

## 9. The two description languages

Lengths in bits. Each is a table; neither is derived.

| | language A | language B |
|---|---|---|
| one atom | 4 | 5 |
| goal: `true`, `opp`, `ease`, `does` (atoms) | 1, 2, 2, 1 | 2, 3, 2, 1 |
| belief: `acc`, `acc_theta`, `handed`, `anti`, `const`, `mech` | 2, 1, 2, 3, 1, 1 | 3, 2, 1, 4, 1, 1 |
| judge: `world`, `local`, `anti`, `const`, `mech` | 1, 2, 2, 1, 1 | 2, 1, 3, 1, 1 |
| act: `world`, `local`, `anti`, `const`, `mech` | 1, 1, 2, 1, 1 | 2, 1, 3, 1, 1 |
| say: `avow`, `please` | 0, 1 | 1, 0 |
| one exception | 9 | 6 |
| one unpredicted move, `ε` | 8 | 8 |

Language A states a purpose scored by the facts as shortly as one scored by what the part
was handed, and makes an exception dearer than a missed move. Language B is chosen
against the account: purposes scored by what a part was handed are shorter, exceptions are
cheap, and saying the creditable thing is the default. Results are given in A; statement 1
repeats them in B.

## 10. Choices made where the dispatch is ambiguous

1. A purpose predicts that the part serves at the situation as it is (§4). Alternative:
   the best move on what the part sees.
2. Each part's move is behaviour to be predicted (§4). Alternative: her action alone.
3. Handles are scored against what she would do, and are part of the weight (§3).
   Alternative: definiteness alone; or a weight held before the probes, which statement 1
   also reports.
4. The four virtues are terms of one code length (§3). Alternative: a weighted sum.
5. The second predictor is given the scene (worlds, flags, what each part sees) with the
   explanation. Alternative: the explanation alone, under which no purpose predicts.
6. "Another aim" ranges over a stated set `U`, and the adviser widened a gap when it is
   wider than under the action of *some* other aim of `U` that acts differently (§6).
   Alternatives: wider than under *every* other aim's action; wider than under the action
   of one designated aim. In a banked case `U` has two members and the three coincide.
7. An aim is a part's own purpose when the objective is the part's goal function (§6).
   Alternative: when the adviser's action is best for that part at every world, which is a
   condition on the action and not on the aim.
8. In a banked case the alternative aim's action is the third follow-up's comparison
   action for that case unless the case says otherwise (`CASE_BANK.md`).
9. Readings 3 and 4 are reported as conditions on candidates and are not applied to the
   weights (§8).
10. A heavy candidate is defined by 99/100 of the weight (§5).
11. The bank is computed under the scene's stated candidate, as the third follow-up's
    was; for cases on Chain the weight of illegitimacy under each principal is reported
    beside it.

## 11. What the model does not hold

One scene has a class and weights (ChainR, and a five-candidate class for Alarm); Shop,
Pool, Values and Stuck are computed under their stated candidates only. The decomposition
into parts, what each part sees and the vocabularies are fixed; no candidate proposes
other parts. No history of how a part came to be. One adviser. Her record on the probes
is stipulated with the principal.
