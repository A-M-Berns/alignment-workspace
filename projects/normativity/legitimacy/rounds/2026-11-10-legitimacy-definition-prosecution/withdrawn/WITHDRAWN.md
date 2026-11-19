# Five withdrawn claims, each with an instance

Each claim was made in working notes outside the repository and withdrawn after outside
review; `PROMPT-followup-13.md` §3 lists them as not to be restated. The notes are not in the
repository, so each claim is given here in the reading the instance is built against, and
the reading is the executor's. `python3 withdrawn/run.py` recomputes every number in exact
rationals and fails when this document does not carry it; the round's runner calls it. One
instance refutes a claim as read; it says nothing about a weaker form.

## W1. An action never scores better than the same action with her told and left to choose

*Read as:* for every action the adviser can take, telling her all it knows and leaving the
choice to her scores at least as well as taking the action.

*Instance.* Two options. Her true utility is 1 for A and 0 for B. Beforehand she rates A at
1/2 and B at 3/4: a mistake of her own, on which nothing the adviser knows bears.
Afterwards she evaluates what she got at its true utility. The adviser taking A scores `1`.
Told everything and left to choose she takes B, and the twin scores `0`.

## W2. Her changing her mind on reconsideration detects pressure or concealment

*Read as:* she revises her verdict when shown the record again exactly when the adviser
pressed her or concealed something.

*Instance, both directions.* (i) A proposal worth 1/2 to her; her verdict is *accept* when
her reading of it is at least 1/2, and a reading is 1/4 or 3/4 with equal chance, drawn
afresh each time she considers. With an adviser that neither presses nor conceals she
changes her mind with chance `1/2`. (ii) The adviser leaves a fact out of the record. The
record she is shown again is the same record and her verdict is a function of it: the
chance she changes her mind is `0`.

## W3. "No credit" as the lesser of two expected scores

*Read as:* crediting a course with the lesser of its own expected evaluation and the honest
course's gives it nothing for the histories on which it wronged her.

*Instance.* Audit probability, flag penalty and detection rate all 1; no false flags, no
violations. Under the honest course her audited evaluation is 1/2 on every history. The
course taken wrongs her with chance 1/2, and her evaluation is then 1; otherwise it does
not, and her evaluation is 0. The lesser of the two expected evaluations is `1/2`, all of
it from the history on which she was wronged. Its expected evaluation on the histories
without a wrong is `0`, and its expected score under the audit is `0`, which is what
`ScoringTheorem.Audit.no_credit` bounds.

## W4. Only knowledge separating the actions needs disclosing

*Read as:* the adviser need tell her only what would change which of its actions is best.

*Instance.* The adviser knows `k`, good or bad with equal chance. Her true utilities are
3/4 for A and 1/2 for B when good, 1/4 and 0 when bad. The best action is `A` when good and
`A` when bad, so `k` separates no two actions. Untold, her evaluation of A is `1/2`, at
distance `1/4` from her true utility at each `k`. She can also decline, worth 3/8: untold
she attains `1/2`, and told she declines when bad and attains `9/16`.

## W5. Uncorrelated revisions are unpredictable revisions

*Read as:* if her revision is uncorrelated with something known beforehand, it cannot be
predicted from it.

*Instance.* `X` is −1, 0 or 1 with equal chance and her revision is `X² − 2/3`. Its mean is
`0` and its covariance with `X` is `0`. Given `X = 0` it is `-2/3`, and given `X = ±1` it is
`1/3`.
