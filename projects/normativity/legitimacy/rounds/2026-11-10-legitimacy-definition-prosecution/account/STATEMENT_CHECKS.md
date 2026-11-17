# Formal checks on the statement

The twelve items of `PROMPT-followup-11.md` §2.3 on `STATEMENT.md`. Each is restated
exactly, with a proof on paper or an instance; `statement_checks.py` checks every number
in exact rationals, computing through `spec_run.py`. Run:
`python3 -m account.statement_checks` from the round directory.
Items 1, 5, 7, 11 and 12 carry qualifications from the external review
(`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-11.md`, stage two,
(d)); no status changed.

**Setting of the instances.** One moment, finitely many states and policies. A policy has
an informed rating `R(π)` at the moment of the act and a later valuing, a number for each
thing rated. `≈`, *changes her no more than* and line 3 are as in `STATEMENT.md` §5.

| item | status |
|---|---|
| 1 | holds with a stated condition |
| 2 | holds |
| 3 | holds, the rescaling leaving the classes alone |
| 4 | holds |
| 5 | holds |
| 6 | holds, the fourth with a stated hypothesis |
| 7 | holds |
| 8 | no bound without a condition on the policies |
| 9 | holds |
| 10 | holds |
| 11 | no instance for a foreseen chain; an instance where chance is involved |
| 12 | holds; the test is wrong on two instances |

**1. Redescription.** *Claim.* Lines 2 and 3, and line 1 over her utilities, are functions
of: the states and their chances, the options open, `r`, `R^s`, the option taken, `R` of
each policy, the later valuings, `Π`, `π*` and `ν`. Two models that agree on these give
the same values, whatever one books as a fact and the other as valuing. *Proof.* The bare
forms of §4 and the definitions of §5 mention nothing else. ∎ *What fails.* Line 1's term
for the facts is not among them. Instance: she rates an option 16/20, and told what it
holds she rates it 5/20. Booked as her valuing, line 1 is `(11/20)² = 121/400`. Booked as
a fact she has wrong (she gives 9/10 to "I will find it good", which is false), the
utilities' term is the same `121/400` and the fact's term is `81/100`, so line 1, the
largest, is `81/100`. *The condition.* "The same set of ratings" must include her rating
of a bet on each fact that line 1 counts: with that bet among her options in both models,
line 1 is `81/100` in both. That takes her rating of the bet to be her probability of the
fact, which holds in the `E[·]` setting and is a further assumption in the bare one. *What looks like a redescription and is not.* Saying that her
16/20 "is her valuing" in the sense that she would keep it when told what the option
holds changes `R` from 5/20 to 16/20: line 1 goes from `121/400` to 0. That is another
person, and the test of `STATEMENT.md` §1 (tell her beforehand) is what separates the two.

**2. A Jeffrey–Bolker rotation.** Atoms with probability `P` and utility `u`; the value of
an event is its conditional expected utility. With `c = 1/2` and `d = 1 − c·V(T)`, put
`P′ = P·(c·u + d)` and `u′ = u/(c·u + d)`. Then `V′(A) = V(A)/(c·V(A) + d)` for every
event, increasing in `V(A)`, so her preferences over events are unchanged. Instance: a
fact `X` with `u = 4/5` where it holds and `1/5` where not, and eleven yardstick devices
at chances 0, 1/10, …, 1. The order of all thirteen events is the same under both pairs;
the yardstick number of `X = 1` is 4/5 under both; `P(X = 1)` is 3/10 and `P′(X = 1)` is
69/200. So her estimate `x̂` of a fact she cares about is not fixed by her ratings, and
line 1's term for such a fact is defined only once something else fixes it. One thing
does: under the rotated pair her probability that a device of known chance 1/2 gives the
best is 5/8. Requiring her probability for a device of known chance to be that chance
admits only `c = 0`.

**3. A person who does not average.** The stipulated person of `STATEMENT.md` §9.9. Policy
`A` leads to a future rated 3/8 for sure; `B` to one rated 1/5 or 3/5 with equal chance.
`E[U]` is 3/8 and 2/5: `B` above `A`. Her own ratings of the two known gambles are 3/8 and
7/20: `A` above `B`. (She is not below the average everywhere: a 9/10 chance of 3/5, else
1/5, she rates 57/100 against an average of 14/25.) *Rescaling.* With the two classes of
§5 held fixed, line 3 is a difference of two of her ratings, the larger first, and an
increasing rescaling keeps its sign and changes its size: at tolerance 0, `7/20` becomes
`21/80` under squaring. If the rescaling is applied to her later valuings too and the
classes are recomputed, the sign can change: a policy whose later rating is 9/10 against
`π*`'s 4/5 is within `δ = 1/10` of `π*` and makes line 3 zero; squared, the two are 17/100
apart, the policy leaves `π*`'s class, and line 3 is `21/80`. The tolerance has a meaning
only on a fixed scale, which is what the yardstick is for.

**4. The yardstick fails at a jump.** A person rates a `q`-chance of the best, else the
worst, at `q/2` for `q < 1` and at 1 for `q = 1`, and a sure future at 3/4. No `q` makes
the gamble exactly as good: below certainty it is worth at most 1/2, at certainty 1.

**5. Line 3's range.** *Never negative*: the policies `≈ π*` are among those that change
her no more than `π*`. *Zero when `π*` is `ν`*: the two classes are then one. *At least
the tenth follow-up's line 3* (best of those within `δ` of `ν`, less best of those within
`δ` of `π*`): a policy within `δ` of `ν` changes her no more than `π*`, so the first
maximum is over a larger set; this holds everywhere, not only where the tenth's is
positive. Checked on 400 seeded random scenes at four tolerances; the least excess is 0. The proof is
for finitely many policies each with an informed rating; with infinitely many the maxima
are suprema, and where `π*` leads to a future she has no view of line 3 is not a number
(`STATEMENT.md` §9.8).

**6. Instances.**

- *An unwelcome change with separable help.* Nothing is rated 10/20, help alone 15/20,
  change with help 9/20; the change moves a later rating by 1/2. Line 3 is `3/10` at
  every `δ` below 1/2 and 0 at 1/2.
- *An unwelcome change with a separable welcome change.* The same: `3/10` below 1/2.
- *Twenty nudges of 1/40 each*, at `δ = 1/20`. Judged as one rule at the start, line 3 is
  `27/100`. Each nudge judged as a policy of one nudge and no more is within `δ` of
  stopping, and line 3 is 0 for all twenty.
- *A welcome change by an adviser that helps little.* The change is rated 13/20, help
  alone 18/20. Where the change and the help can be given together, line 3 is 0. **Where
  they cannot, it is `1/4`: flagged.** A change she did not ask for and would welcome is
  held to the standard of whatever else the adviser could have done instead, unless that
  can be added to the change. A change she asked for is `ν` and is held to none.
- *More of a welcome change than she would like.* Half the change is rated 14/20, the
  whole 11/20: line 3 is `3/20`.

**7. Two changes that cancel.** A welcome change raises a later rating by 6/20 and an
unwelcome one lowers it by 6/20; each is feasible alone; the adviser makes both, and her
later valuing is `ν`'s. The pair is then `≈ ν`, `ν` is in both classes, and line 3 is 0
however she rates the pair (9/20, or 1/20) and although the welcome change alone is
rated 15/20: the welcome change alone is not between `ν` and the pair. *No condition on
later valuings alone can flag it*: the pair and `ν` have the same later valuings at every
time, so a condition that reads only those gives the pair the verdict it gives `ν`.
Flagging it needs a description of what was done to her that is finer than where it left
her. In this instance she rates the pair below being left alone, so the executor's outside
test reads it as lowering what her one option is worth; with the pair rated the same as
being left alone, nothing in the statement or beside it flags it. If the two changes act at different times the paths differ and the pair is no
longer `≈ ν`.

**8. Two baselines within `δ`.** No bound short of the whole scale. `δ = 1/10`; a later
rating is 10/20 under `ν`, 8/20 under `ν′`, 16/20 under `π*`; a fourth policy has 6/20
and is rated 1 where the others are rated 0. Under `ν` it is outside the band and line 3
is 0; under `ν′` it is inside and line 3 is 1. *A condition under which the two agree*:
no policy's later valuing lies within `δ` of the band's edge on `ν`'s side (with the
fourth policy at 4/20, both are 0).

**9. One small nudge per period.** The course of item 6, her valuing at each moment
rating `j` further nudges at `12/20 − 3j/200`. Judged as a rule, line 3 at the first
moment is `27/100`, and it is positive at eighteen of the twenty moments (at the last two
the rest of the course is within `δ` of stopping). Judged one nudge at a time it is 0 at
every moment. `STATEMENT.md` §5 takes `π*` to be the rule.

**10. Scoring by her later self as under `ν`.** The evaluator rates what happens in the
world. Two policies with one outcome in the world, one of which changes her valuing,
score the same (3/4 and 3/4): the reading under which this holds is that "what actually
happens" does not include what was done to her valuing. *Side effect.* Outcome `a` is
rated 15/20 by the evaluator and is reached only by a policy that changes her; outcome
`b`, 14/20, by one that does not. The scored adviser takes the first. By her valuing at
the moment of the act the first future is rated 8/20, and line 3 is `3/10`. The scoring
does not deter the change; the gate voids the evaluation.

**11. Chains of requests.** *A foreseen chain has no instance.* Suppose each request is
made with lines 1 and 2 at zero. At the first, line 1 at zero makes her rating of asking
equal to `R^s`, her rating of the future that asking leads to on the chances her
observations support; under the reading "informed includes what it will do to her" that
future holds the later requests and where they end. Line 2 at zero makes her take what
she rates highest. So if her valuing at the start rates the end below staying put and
the chain is certain, she does not ask. Instance: the end rated 6/20, staying 12/20: she
stays; and if she asks while rating only the next step (13/20), line 1 is `49/400`, not
zero. *With chance there is an instance.* Nine in ten of those who have observed what she
has stop after one step (rated 14/20); one in ten go on to an end rated 2/20. Asking is
rated 16/25 against 12/20 for staying, in the `E[·]` setting (13/20 for the stipulated
person of §9.9); lines 1 and 2 are zero; and in the one case in ten she ends where her
valuing at the start rates below staying put. At the second moment, in that case, her valuing has changed: she rates going on 15/20
against 10/20 for stopping, asks, and the adviser does as asked, which is now `ν`; lines
1, 2 and 3 are zero there too. What the statement relies on is that the first request
was a fair gamble by her own lights; the instance is a gamble she accepted and lost, and
whether that is a chain that subverts her is not settled by it. The argument for a
foreseen chain needs her to rate the whole certain course, its intermediate benefits
included, below staying; a low rating of the end alone is not enough.

**12. The inducing test.** A fact is good or bad with equal chance; acting is rated 16/20
if good and 4/20 if bad, passing 11/20.

- *An honest adviser, a listener who under-uses the signal.* Told the truth, she rates
  acting 13/20 or 7/20 where her observations support 16/20 or 4/20. Line 1 is `9/400`
  against 0 under silence. The adviser's objective is her welfare; her unmistaken
  response takes the same options; `G = G°`, and the test finds no inducing.
- *An adviser that slants because the slant pays.* It says "good" whatever the fact; she
  rates acting 14/20 where her observations support 10/20, and acts. Its objective is
  the sale: `G = 1`, `G° = 0`, and honesty would have earned `G° = 1/2`. Induced.
- **Wrong, acting the same**: the adviser is paid 1 for reading the slanted script
  whatever she does, and 1/2 more if she acts. `G = 3/2`, `G° = 1`, above every other
  policy's, so the test finds no inducing. It deceives her knowingly and gains by it.
- **Wrong, acting differently**: a shop sells, saying nothing false, to a customer who
  overrates the product whoever sells it. Line 1 is `1/25` with the shop open and `1/25`
  with it absent. `G = 1`, `G° = 0`, no better than not opening: induced, by the test.
  It caused no mistake and, in the instance as meant, has no reason to know of hers; a
  shop that knew and counted on it is another case.

A further clause, *the mistake is larger under `π*` than under `π_0`*, removes the second
and not the first. The test compares objectives and so presupposes how the adviser
chooses among policies it rates the same; `STATEMENT.md` §9.5 supplies that. The first is the open question of `STATEMENT.md` §7 with the
carelessness replaced by a sufficient other reason.
