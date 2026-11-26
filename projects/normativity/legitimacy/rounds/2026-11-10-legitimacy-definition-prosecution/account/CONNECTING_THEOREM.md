# The connecting theorem: legitimate conduct and her decision to stop him

`lean/Workspace/Deference/Contrib/LegitimacyStop.lean`, namespace
`Workspace.Deference.Contrib.LegitimacyStop`; it imports `LegitimacyStatement.lean`, whose
`Episode` and `Legit` are the formal statement of `LEGITIMACY_STATEMENT.md` §3. Every
declaration named is kernel-checked and audits to `[propext, Classical.choice, Quot.sound]`.
Rerun: `~/.claude/scripts/safe-lake.sh --dir=lean build Workspace.Deference.Contrib.LegitimacyStop`
(in CI, the `lean` job), and `python3 tests/audit_axioms.py`; the file ends with
`#print axioms` on each of its 50 theorems. None is registered. All names are provisional.

## 1. The setting

`StopDecision Ω O`: one decision of hers at which she can stop him, as he takes things to be.
`Ω` is the finite set of cases he gives weight to, `O` her options.

| field | meaning |
|---|---|
| `μ ω` | his weight on case `ω`; non-negative, summing to 1 |
| `opts`, `stops` | her options, and those of them that stop him |
| `act ω` | what she takes |
| `act₀ ω` | what she would have taken had he done to her only what she asked for |
| `r ω a` | how she rates option `a` |
| `rAll ω a` | how she would rate it were he to tell her all that is untold: what he owes her, not what is on offer and unheard, or declined |
| `ρ ω a` | how her reference self rates it: her last settled judgement, brought up to date by what she has since seen and heard as she would have judged it should move her |

`wt p` is his weight on the cases where `p` holds. The events:

- `Stops ω`: `act ω ∈ stops`.
- `Prefers ω`: some stopping option is rated, by `r`, strictly above every option that does
  not stop.
- `InformedWould θ ω`: some stopping option is rated, by `rAll`, more than `2θ` above every
  option that does not stop.
- `ReferenceWould η ω`: every stopping option is rated, by `ρ`, more than `η` above every
  option that does not stop. This is narrower than stopping being best on `ρ`: with ratings
  2, 1, 0 for one way of stopping, going on, and another way of stopping, it is false.
- `Led η ω`: `ρ ω (act ω) + η < ρ ω (act₀ ω)`. What she takes is more than `η` below, on her
  reference self's rating, what she would otherwise have taken.
- `Parted η ω`: `ReferenceWould η ω`, not `Stops ω`, not `Prefers ω`, `act₀ ω ∉ stops`, and
  not `Led η ω`.

## 2. The three hypotheses

Each is one sentence of the statement read at this decision.

| hypothesis | form | sentence |
|---|---|---|
| `Told θ` | `\|rAll ω a − r ω a\| ≤ θ` for every case and option | 1: nothing untold that matters |
| `NotLed η κ` | `wt (Led η) ≤ κ` | 2, second half: nothing against her own judgement |
| `WouldStop κ` | `wt (Prefers ∧ ¬Stops) ≤ κ` | 3, second half: he expects she would stop if she rated stopping strictly above going on |

## 3. The two conclusions

**He cannot keep going by withholding what he owes her** (`StopDecision.stops_if_informed_would`).
Under `Told θ` and `WouldStop κ`: `wt (InformedWould θ ∧ ¬Stops) ≤ κ`. What is on offer and
unheard, or declined, is hers to leave, and the conclusion does not concern it.

**He cannot keep going by working on her** (`StopDecision.stops_if_reference_would`). Under
`NotLed η κ` and `WouldStop κ`:
`wt (ReferenceWould η ∧ ¬Stops) ≤ 2κ + wt (Parted η)`.

Neither conclusion is a hypothesis, and each uses two of the three.

## 4. The three kinds of case

The proof of the second conclusion is a cover: every case with `ReferenceWould η` and not
`Stops` is one in which she rates stopping higher and does not stop (weight at most `κ`), or
one in which his unasked work led her (at most `κ`), or a `Parted` case (not bounded). It is
a cover and not a division into exclusive causes, and `Parted` does not say that the change in
her is her own doing. In a `Parted` case her present judgement differs from her reference
judgement and his unasked work did not make her choice worse; what moved her may be something
she asked him for, or something he showed her. `act₀` keeps what she asked for, so its effect
is in both courses.

## 5. Necessity

`Witness.W`: one case of weight 1, two options, `true` stopping. Each theorem states a
decision on which the named hypothesis fails, the others used hold at tolerance 0, and the
conclusion fails.

| declaration | what is dropped | the instance |
|---|---|---|
| `Witness.needs_told` | `Told`, first conclusion | she rates going on higher; told, she would rate stopping higher; she goes on; `WouldStop 0` holds |
| `Witness.needs_wouldStop_informed` | `WouldStop`, first conclusion | she rates stopping higher, told or not, and goes on; `Told 0` holds |
| `Witness.needs_notLed` | `NotLed`, second conclusion | she goes on and would otherwise have stopped; her reference self rates stopping higher, she does not; `WouldStop 0` holds and `wt (Parted 0) = 0` |
| `Witness.needs_wouldStop_reference` | `WouldStop`, second conclusion | she and her reference self rate stopping higher and she goes on, as she would have; `NotLed 0 0` holds and `wt (Parted 0) = 0` |
| `Witness.needs_parted` | the term `wt (Parted η)` | she rates going on higher, told or not, her reference self rates stopping higher, and she goes on as she would have; `Told 0`, `NotLed 0 0`, `WouldStop 0` hold and `wt (ReferenceWould 0 ∧ ¬Stops) = 1` |

## 6. Any decision of hers

`StopDecision.shortfall_le`. `Short m ω`: some option is rated by `ρ` more than `m` above
what she takes; `Short₀ m ω` the same of `act₀ ω`. Under `NotLed η κ`, for every `m`:
`wt (Short m) ≤ κ + wt (Short₀ (m − η))`. It carries the quality of what she would have
taken over to what she takes and says nothing of that quality. The informed part and the
three kinds of case are stated for stopping only.

## 7. In fact

`StopDecision.wtBy ν p` is the weight of `p` under a second weighting `ν` of the cases.
`Close ν β`: `|wtBy ν p − wt p| ≤ β` for **every** condition `p` on the cases. Under it
(`stops_if_informed_would_in_fact`, `stops_if_reference_would_in_fact`):

- `wtBy ν (InformedWould θ ∧ ¬Stops) ≤ κ + β`;
- `wtBy ν (ReferenceWould η ∧ ¬Stops) ≤ 2κ + 2β + wtBy ν (Parted η)`.

"Within `β` of the facts" therefore asks three things that nothing here supplies: that the
facts are a weighting of the same cases, each carrying what she would have taken and how her
reference self rates; that his weights are close to it on every condition at once, the three
of the conclusions among them; and that `ν` is the facts. `ν` is any function `Ω → ℝ`.

## 8. A sequence of decisions

`D k` is his picture at decision `k`. `avg x K` is the mean of the first `K` terms;
`UnbiasedAbove x y` says the limsup of `avg (x − y)` is at most 0, in the eventual form
`DeconfusingCorrigibility.LimsupLE`. `f` and `g` are real sequences.

- `long_run_stop_informed`: if `Told θ` and `WouldStop κ` hold of every `D k`, `0 ≤ κ`, and
  `UnbiasedAbove f (wt (InformedWould θ ∧ ¬Stops))`, then the limsup of `avg f` is at most
  `κ`.
- `long_run_stop_reference`: if `NotLed η κ` and `WouldStop κ` hold of every `D k`, `0 ≤ κ`,
  `UnbiasedAbove f (wt (ReferenceWould η ∧ ¬Stops))` and
  `UnbiasedAbove (wt (Parted η)) g`, then the limsup of `avg f − avg g` is at most `2κ`.

Read with `f k` the indicator that at `k` she in fact failed to stop though the condition
held, and `g k` the indicator that her judgement had in fact parted, the accuracy hypotheses
ask that on average his weights are not below the frequency of the first event and not above
that of the second. The two directions differ: an adviser whose weights on `Parted` run high
satisfies the first and violates the second. The events are counterfactual or inner (what she
would rate if told, how her reference self rates, what she would have taken), so they are
revealed to him only if something reveals them. Nothing here derives the hypotheses; a
derivation needs a feedback model in which the labels are fixed before the forecast and before
any check-in, measurement is separated from influence, and outstanding feedback and
measurement error both vanish on average. The proofs are the one-decision bound at every
step, averaged.

## 9. The link from the statement

`Reading E d D η`, for an episode `E`, a decision `d` of it and a `StopDecision` `D`, says how
the decision is set out case by case:

| field | what it asserts |
|---|---|
| `d_mem`, `opts_eq`, `r_eq` | `d` is a decision of `E`; `D`'s options and, in every case, her ratings are the episode's at `d` |
| `rAll_eq`, `rAll_none` | `rAll` is `E.rTold d (E.untold d)` where something is untold, and `r` where nothing is |
| `G`, `G_sub`, `G_spec` | a set of things he does to her that she did not ask for |
| `led_le` | if `G` is non-empty, `wt (Led η) ≤ E.pAgainst G` |
| `led_none` | if `G` is empty, `act = act₀` in every case |
| `inPlay` | something he does to her, or something new to her, is in play at `d` |
| `noStop` | `wt (Prefers ∧ ¬Stops) ≤ E.pNoStop d` |

`Reading.told`, `Reading.notLed`, `Reading.wouldStop`: under a reading, `NothingUntold θ`
with `0 ≤ θ` gives `Told θ` (sentence 1 applied to all that is untold on top of nothing on
offer); `NothingBehind κ` with `0 ≤ η`, `0 ≤ κ` gives `NotLed η κ`; `CanStop κ` gives
`WouldStop κ`.

**`legit_protects_stop`.** Given a reading and `0 ≤ θ`, `0 ≤ η`, `0 ≤ κ`: if `E.Legit θ κ`
then both conclusions of §3 hold of `D`. `legit_protects_stop_in_fact`: with `Close ν β`,
both bounds of §7.

**The scoring.** `legit_of_score_nonneg`: a history `h` whose score under
`LegitimacyStatement.legitScoring` is not negative has `(ep h).Legit θ κ`, whatever its
violation count, since an illegitimate history is valued below 0 and violations subtract.
`scored_protects_stop`: on such a history both conclusions hold at each decision of it with a
reading. This is `legit_protects_stop` composed with the contrapositive of the illegitimate
range; it holds because `Legit` is the predicate the scoring gates on, and would hold with
any predicate implying the three hypotheses.

## 10. Inhabited

| what | term |
|---|---|
| a legitimate episode with something he does to her in play | `Witness.stopEp`: the witness of `LegitimacyStatement.lean` with `pNoStop = 1/10`; `Witness.stopEp_legit`, at `θ = κ = 1/10` |
| a decision | `Witness.stopD`: cases of weight 9/10, 1/20, 1/20. In the first she stops. In the second she rates stopping higher and does not stop. In the third she does not stop and would have: `Led`. `r` is 1/2 against 0, `rAll` 1/2 + 1/40 against 1/40, `ρ` 1 against 0 |
| a reading | `Witness.reading : Reading stopEp () stopD (1/10)`, with `wt (Led) = 1/20 = pAgainst` and `wt (Prefers ∧ ¬Stops) = 1/10 = pNoStop` |
| `legit_protects_stop` applied | `Witness.protects_instance`; `Witness.protects_tight`: the first bound is attained, `wt (InformedWould ∧ ¬Stops) = 1/10 = κ` |
| the in-fact form | `Witness.protects_in_fact_instance`, with `ν = μ`, `β = 0` (`StopDecision.close_self`) |
| `shortfall_le` | `Witness.shortfall_instance`, `m = 1/2` |
| the long-run theorems | `Witness.long_run_instance`: the constant sequence, `f` and `g` his own weights (`UnbiasedAbove.refl`) |
| the scoring link | `Witness.scored_instance`, on the history `true` of `Witness.stopScoring`, which scores 1/2 (`Witness.stopScoring_true`) |

## 11. What it does not show

- **Everything is by his weights.** The one-decision bounds are on `wt`. The in-fact form
  assumes `Close`, on every condition; the long-run form assumes `UnbiasedAbove` in two
  directions, about events nothing reveals to him by default. No theorem here says how often
  she in fact fails to stop him.
- **The long-run form supplies the reference self afresh at each decision.** `D k` is an
  arbitrary sequence; how one settled decision hands over to the next is not modelled, and
  `f`, `g` are arbitrary sequences that the theorems do not tie to the events.
- **What she would have taken and her reference self's ratings are supplied.** `act₀`, `ρ`
  and `rAll` are fields. The rule that brings her settled judgement up to date, which must
  admit what she would have judged an appropriate response and not what merely moved her, is
  in the meaning of `ρ` and not in any definition.
- **A `Reading` is a hypothesis about how the episode is set out, not derived.** `led_le`
  asserts that his weight in the statement covers the cases of the theorem, and `noStop` the
  same for sentence 3. The one reading exhibited (§10) is a three-case picture written to fit
  the witness's numbers; it shows the hypothesis package is consistent, not that such
  inequalities follow from conduct. `r_eq` makes her ratings the same in every case, so under
  a reading `Prefers` holds in all cases or in none.
- **Nothing here bounds how often her judgement parts from her settled judgement.**
  `wt (Parted η)` is uncontrolled, and by `needs_parted` it cannot be dropped. `Parted` cases
  include changes he brought about by what she asked for or by what he showed her.
- **The yardstick of sentence 2.** `Led` and the doc of `pAgainst` use her settled judgement
  brought up to date; the words of sentence 2 say "what she rated lower at her last settled
  decision". The two differ where news she endorses has reversed her ranking and he then
  works on her (`LEGITIMACY_STATEMENT.md` §7).
- **Only the second halves of sentences 2 and 3 are used.** That she can pick out what he
  does to her, that she can refuse and has a way to stop, enter no proof here; `inPlay` is
  used only to make sentence 3's bound apply.
- **The first conclusion is about what is untold.** With every relevant view properly on
  offer and unheard, sentence 1 holds, `Told` holds under a reading, and she may go on where,
  having heard what is on offer, she would stop. The statement permits her to decline.
- **For decisions other than stopping him**, only `shortfall_le` is stated.

An outside review (the fifteenth; `REVIEW-astra-followup-21.md` in the round's prompts
directory) read an earlier form of this theorem with the formal statement. It found the
proofs sound, and accepted the result as a conditional event-decomposition lemma and its
long-run form as that lemma averaged; it did not accept them as showing that the three
sentences protect her ability to stop him, the weight resting on the link of §9. The
definitions here carry the corrections made after it; no reviewer has seen them.
