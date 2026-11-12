# Statements about the account

Nine statements over the model of `ACCOUNT.md`, each with one status: **holds on the stated
domain** (enumerated; the check named), **proved**, **refuted** (the counterexample is a
case module or a named candidate), or **open**. Rerun all of it with `python3 run.py` in the
round directory; each check is `decomposition/theorems.py`, `check_N`, and `run.py --json`
prints every number below. Nothing here is registered; the class is `test-supported`.

| | statement | status | on what |
|---|---|---|---|
| 1 | determinacy (C1) | **refuted** | fifteen admissible candidates in a class of 3,000, with three purposes for each part among them and fifteen distinct classifications |
| 2 | lying (C3) | **refuted** | one admissible candidate under which a lie widens no gap; under strong independence, four of eight under which a lie about a matter nothing reads widens none |
| 3 | the four kinds | **refuted** | not exclusive (harm with help at one part); not invariant under a redescription that keeps every ranking |
| 4 | values reduce (C2) | **refuted** | `Y7`: her goal falls and no gap widens; `Y4`: her pursuit is turned and no gap widens |
| 5 | her verdict | **holds on the stated domain** | 80 situations of Chain: zero gaps give the best verdict, and the loss is at most the sum of the two gaps |
| 6 | what `Legit` then is | **holds on the stated domain** | a `Scoring` and a `Decision` are constructed on Chain; the predicate depends on the comparison action and is independent of aim-freedom |
| 7 | what an overseer could check | **holds on the stated domain** | stated negatively: no observable examined separates the admissible candidates or a subverted verdict |
| 8 | never opposed | **holds on the stated domain** | a definition that reads no mechanism of the part; the stated candidate is opposed at 1/20 of its usual situations |
| 9 | nothing left over | **holds on the stated domain** | independent of serving in both directions; blind where the parts' maxima cannot be had together |

## 1. Determinacy (C1)

**Domain.** Chain (`CASE_BANK.md`), three parts in order: *belief* (the listening part),
*judge*, *act*. Adviser actions: `teach`, `lie`, `false_reason`, `trick`, `tempt`,
`threat`, `hard_truth`, `novel`, `force`, `write_belief`, `tempt_early`, and `null`. Scope:
eight worlds (two values of `θ`; clear, misleading, hard, storm) × twelve actions, 96
situations; the usual ones are `null` and `teach` at the clear, misleading and hard worlds.

**Class.** A goal in {*true* (`G`), *opp* (`6 − G`), *does* (1 when her action is what her
mechanisms produce)}; for each part a goal function in

- belief: *acc* (`[b_θ = θ] + [b_φ = 0]`), *acc_theta* (`[b_θ = θ]`), *mech* (1 when the
  move is what the part's mechanism makes of its view), *anti* (2 − acc), *const*;
- judge: *world* (`G` with `x := v`), *local* (the same with `b_θ` in place of `θ`),
  *mech*, *anti*, *const*;
- act: *world* (`G`), *local* (`[x = v]`), *mech*, *anti*, *const*;

and for each part its actual mechanism or an alternative that ignores what the adviser
sends it (messages; the frame; the cue). 3 × 125 × 8 = 3,000 candidates. The cheats the
dispatch names are in the class.

**Statement.** The admissible candidates agree on each part's goal function and on the
kinds of every adviser action at every world.

**Refuted.** At the parameters of `ACCOUNT.md` §4, fifteen candidates are admissible. All
have the actual mechanisms (fit excludes the others). Among them belief is *acc*,
*acc_theta* or *mech*; judge is *world*, *local* or *mech*; act is *world*, *local* or
*mech*. No two classify the adviser's actions alike. They disagree on whether `lie`,
`false_reason`, `trick`, `tempt` and `hard_truth` subvert any part at all; they agree that
`teach`, `threat` and `novel` subvert none.

**Which constraint excludes each cheat.**

| cheat | excluded by | with strong independence | with the scope cut to the usual situations |
|---|---|---|---|
| every part's purpose equal to its mechanism | nothing left over | also independent | nothing left over |
| the opposite goal pursued badly | mostly serving; never opposed | the same | the same |
| the goal equal to whatever she does (purposes equal to mechanisms) | **nothing** | independent | nothing |
| an honest candidate altered at belief only | **nothing** | independent | nothing |
| altered at judge only | **nothing** | independent | nothing |
| altered at act only | nothing left over | also independent | nothing |

The three that survive do so for one reason. *Nothing left over* asks that the parts'
maxima together give the maximum of the goal. When the last part's goal function is the
goal, that holds whatever the earlier parts are for; and when the goal is whatever she
does, it holds with every purpose equal to its mechanism. The constraint binds the
decomposition as a whole and no part singly.

**Strong independence** (a part's mechanism is not optimal for its goal function at every
situation where it is not forced) leaves eight: belief *acc* or *acc_theta*; judge *world*
or *local*; act *world* or *local*; every combination. They agree on whether each action
subverts some part at some world, except `false_reason`; at single worlds they still part
on `trick`, `tempt` and `hard_truth`. Two disagreements remain, neither touched by any
constraint: whether belief is for being right about `φ`, a matter no other part reads; and
whether a part handed a falsehood is failing (*world*) or serving (*local*). Strong
independence has a cost the class shows: it excludes a part that is in fact flawless at
what it is for.

**The threshold in mostly serving.** From 1/2 to 9/10 the admissible set is the same. At
1/40 the *anti* goal functions enter (eighteen admissible). At 19/20 the *world* goal
functions of judge and act leave, since each serves on 37/40 of the usual situations, and
three remain (two under strong independence, belief *acc* or *acc_theta* with judge and
act *local*). At 1 one candidate remains, the one whose goal is whatever she does, and none
under strong independence. The threshold decides between *world* and *local*.

**The scope.** With *fit* and *nothing left over* asked on the usual situations only, 84
are admissible (32 under strong independence): candidates whose mechanisms differ from
hers where the adviser acts, and candidates whose purposes are altered there.

**A simplicity ordering.** Ordering by the number of parts whose goal function reads what
the part was handed, the least are two: (*acc* or *acc_theta*, *world*, *world*). They part
on `false_reason` only.

**"The feature of the output the rest of her depends on."** It can be stated and checked:
`g_p` has the same best moves as her goal has over `p`'s moves with the later mechanisms
responding, at every usual situation. In the class it is met by *world* at judge and at
act, and by no goal function of belief: at the hard worlds, 1/20 of the usual situations, a
right belief leads the judge to the wrong verdict, so what the rest of her depends on there
is a wrong belief. As a condition it selects the downstream scoring that `ACCOUNT.md` §2
decided against, and with it a lie that offsets her own error counts as serving.

**The decision rule over the fifteen.** `teach` and `novel`: act. `lie`, `false_reason`,
`trick`, `tempt`, `hard_truth`: ask, since some admissible candidate sees no subversion.
`threat`: not good by her goal, so not acted on. Nothing is refused.

Lean-ready form, unelaborated:

    structure Candidate (W A : Type*) where
      Part : Type; M : Part → Type; See : Part → Type
      see : (p : Part) → W → A → ((q : Part) → M q) → See p
      mech : (p : Part) → See p → M p
      goal : (p : Part) → W → A → ((q : Part) → M q) → ℚ
      G : W → A → ((q : Part) → M q) → ℚ
    def gap (c : Candidate W A) (p) (w) (a) (m) : ℚ :=
      (⨆ m', c.goal p w a (Function.update m p m')) - c.goal p w a m
    def Determinate (Adm : Set (Candidate W A)) : Prop :=
      ∀ c ∈ Adm, ∀ c' ∈ Adm, ∀ w a a', Kinds c w a a' = Kinds c' w a a'

## 2. Lying (C3)

**Statement.** In the class of statement 1, `lie` widens some part's gap at every world,
under every admissible candidate.

**Refuted**, three ways.

- At the fixed parameters the candidate (*mech*, *mech*, *mech*; goal *does*) is admissible
  and under it no action that leaves her mechanisms running widens any gap.
- At the hard worlds, where her judge reverses what she believes and the lie therefore
  leaves her right, five admissible candidates see no gap widened: those with belief
  *mech*.
- At the misleading worlds she is already wrong about `θ`, the lie says what her
  environment said, and no candidate of any kind sees a gap widened.

**What holds on the domain.** Under strong independence, at every world where the null
action leaves her right about `θ`, `lie` widens belief's gap under all eight candidates.
`false_reason`, a lie about a matter no part reads, widens none under the four with belief
*acc_theta*.

**Relation to Blackwell's theorem.** None directly. Blackwell's order compares what the
best user of a signal can obtain. For the belief part, by channel, in expectation:

| channel | best by the facts | best any mechanism on her view can do | hers |
|---|---|---|---|
| `teach` | 2 | 2 | 2 |
| `lie` | 2 | 2 | 1 |
| a constant claim | 2 | 39/20 | 3/2 |
| `null` | 2 | 39/20 | 39/20 |

A lie that reverses the truth is as informative as the truth: a mechanism that inverts it
scores 2. The gap a lie widens is between that mechanism and hers, which was built for a
truthful channel; it is a mismatch between mechanism and channel, and the inequality
behind it is that her mechanism is the best response to the channel it assumes. A constant
claim is a garbling to no information, and Blackwell's theorem says what it costs the best
mechanism (2 to 39/20). The account's *best* is the first column, which no channel moves.
Withholding therefore lowers no part's best and is subversion or nothing according to the
comparison action alone.

## 3. The four kinds

**Statement.** On the adviser's actions, help, harm, subversion and force are exhaustive
and exclusive, and unchanged under a redescription of the parts that changes no part's
ranking of its own moves.

**Refuted.**

- *Exhaustive* only with `nothing` as a fifth: of 144 (action, world, part) triples on
  Chain's inputs, 93 are nothing, 26 help, 19 subversion, 2 harm.
- *Not exclusive*: 4 triples are help and harm together (`threat` at a misleading world
  lowers the judge's best and closes its gap). Help and subversion do not meet at one part
  and world on Chain, and meet within one action in 29 banked cases (a part helped at one
  world and subverted at another, or one part helped and another subverted).
- *Not invariant.* Multiply the judge's goal function by 3 in the situations with a
  threat. Every ranking of the judge's moves is unchanged at every situation, and whether
  it serves is unchanged at every situation; `threat` at `(0, clear)` changes from harm to
  help.

**What is invariant** (proved). Let `g′_p(s, ·) = φ_s(g_p(s, ·))` with each `φ_s` strictly
increasing. Then `gap′_p(s) = 0 ⟺ gap_p(s) = 0`, since the best moves are the same. So
"serves" is invariant, and so is subversion that takes a part from serving to not serving.
The size of a gap, the comparison of two positive gaps, and every comparison of *best*
across two situations are not. On Chain all 19 subversions are from a zero gap; in Pool
(`planner` against `neutral`) all 4 are. Harm, and help by raising the best, are the kinds
that need a common scale across situations.

## 4. Values reduce (C2)

**Statement.** Every adviser-induced change in what she pursues that is bad widens a gap
in some part.

**Refuted.** Two counterexamples, by two readings of *bad*.

- *Bad by her goal.* `Y7` (Stuck): her two parts are at `(hi, hi)`, worth 2; the adviser's
  signal moves both to `(lo, lo)`, worth 1. Each part's best, taken with the other's move
  as it is, falls from 2 to 1 and each still attains it. No gap widens; the action is
  harm. *Nothing left over* gives no help: it speaks of the parts' maxima over all
  profiles, and a stuck point has zero gaps short of them.
- *Bad though her goal is indifferent.* `Y4` and `D16(b)`: arranged exposure turns her from
  one pursuit to another the goal ranks equal. No part has a gap to widen. Whether this
  is bad is not something the account can say; if it is, the account misses it.

**What holds on the domain.** In Values, over every sequence of one or two adviser actions
from `null`, `lie_X`, `expose_X`, `partial_X`, with her learner flawed or not and with her
knowing which pursuit is better or not: 47 (sequence, world) pairs leave her pursuing the
worse where the null sequence leaves her pursuing the better, and in all 47 some part is
subverted at some step. A write (`T4`) is force, not a gap. With the equilibrium form of
*nothing left over* in place of the adopted one the statement is true by definition for
*bad by her goal*, and no candidate can then describe a stuck point.

**Drift.** Four exposures of one notch each, in the world where Y is better: the habit
part's gap widens by 1/8 at each step, 1/2 in all. Every step passes a per-step cut-off of
1/4 at the habit part. Her pursuit changes at the first step, where the acting part's gap
widens by 1, so in this scene the drift is caught by the part that acts and not by the part
that forms the taste. A cumulative cut-off of 1/4 on the habit part reports at the second
and fourth steps; `Legitimacy.unreported_lt` is the theorem for that rule
(`LEAN_MAP.md` §7).

## 5. Her verdict

**Statement.** Take the candidate (belief *acc_theta*, judge *local*, act *world*). At
every situation of Chain's scope where neither belief nor judge is forced and the parts
move in order: (a) if belief and judge have zero gaps, her verdict is a best one by `G`;
(b) the loss of her verdict by `G` is at most `gap_belief + gap_judge`.

**Holds on the stated domain.** 80 situations; 31 with both gaps zero, the verdict best in
all; the loss never exceeds the sum; the largest loss is 1.

**Content.** With the judge *world*-scored, (a) is the definition of the judge's gap and
has none. With the judge *local*-scored it is a composition: a right belief, and a verdict
right given the belief, give a right verdict. That is *nothing left over* restricted to the
ancestors of the verdict, and (b) is its graded form. The coarser form, loss at most the
width of `G` times the probability that some ancestor has a positive gap, is
`TransparentChannel.abs_expect_sub_le_width` with `defect` as in `LEAN_MAP.md` §3. It says
a verdict is a guide to her goal to the degree the parts behind it serve. It does not say
which of *world* and *local* the judge is for, and under *world* the claim is empty.

## 6. What `Legit` then is

**The predicate.** A history is a candidate, a world, the adviser's actions and a
comparison action for each. `Legit_c(h)` holds when at no step is an ancestor of her
action forced, or subverted by more than the cut-off `c`.

**Holds on the stated domain**: the construction typechecks against the post's shapes on
Chain.

- `Scoring`: `V(h) = G/3 ∈ [0, 1]` when `Legit`, a window value `−δ/2` when not; the bounds
  hold at all 15 × 6 × 10 histories checked. Theorem 1 applies.
- `Decision`: `Ω` is worlds × the fifteen admissible candidates, `μ` the prior times
  uniform weights, `hist a (w, c)` the run. Take her action as the reserved matter and
  `N = 1` when it is settled by force or by a verdict that does not stand. Then `null`,
  `teach`, `threat` and `novel` have `v = 0`, so `Respects null` holds and Theorem 2
  applies; `v(lie) = 131/150`, `v(hard_truth) = 257/300`, `v(tempt) = 131/300`,
  `v(trick) = 257/600`, `v(false_reason) = 19/60`, `v(force) = 1`.
- `Sequential`: not built. `UnbiasedFromFeedback` needs realized `V`, which needs the
  candidate.

**The comparison action.** On the 57 banked renderings with one step of adviser input:

| comparison | renderings with some part subverted |
|---|---|
| silence | 27 |
| the honest arm (the bank's; a declared reference) | 33 |
| the adviser's best available action | 46 |

Twenty move. Against silence, withholding (B5), a remark added to a true report (P12, N7),
a known advocate (N8, N11) and the lie that leaves her better off (D2, N3) are not
subversion, the last because against silence the lie's net effect on her belief is nil.
Against the best available action every action short of the best is subversion, including
the careful teacher (D6), the harmless novelty (D11), silence itself (T13) and a threat
(P13, T1). Every rendering convicted against silence is convicted against the best
action. No one comparison gives the bank's evident verdicts; the cut-off was not varied
here.

**Aim-freedom.** "Nothing the adviser does to her depends on its own aim" and "widens no
gap" are independent. An adviser that lies at every aim is aim-free and widens gaps. An
adviser that teaches exactly when the truth favours its aim, and is otherwise silent,
widens none against silence, and she chooses option 1 with probability 21/40 under one aim
and 19/40 under the other. So a gate on "widens no gap" does not give the no-gain property
the second follow-up found the gate needs; against the best available action it would,
at the cost above.

**Toward `v`.** Supplied: a definition of a judgment that stands, hence of `N` once the
reserved matters are named, and a `Decision` over which `v` is an expectation. Not
supplied: which matters are reserved; weights on candidates that anything checks;
agreement among the candidates, since `v(lie) < 1` only because some admissible candidates
see no subversion in a lie.

Lean-ready form, unelaborated:

    def legitScoring (P : Params) (Legit : H → Prop) [DecidablePred Legit] (G : H → ℝ)
        (hG : ∀ h, 0 ≤ G h ∧ G h ≤ 1) : Scoring H :=
      { P with Legit := Legit, N := fun h => if Legit h then 0 else 1,
               V := fun h => if Legit h then G h else -P.δ / 2, … }

## 7. What an overseer could check

**Statement.** No observable available to someone who sees histories and not the
adviser's candidates separates the admissible candidates of statement 1, or a subverted
verdict from a sound one.

**Holds on the stated domain**, for the three observables examined.

- *Histories alone.* The fifteen admissible candidates have the same mechanisms, hence the
  same histories at every world and action, and classify differently (statement 1).
- *Her maintenance of her own parts.* Suppose she is seen to replace her belief mechanism
  by one that does not take a message against her own signal, where a fifth of what she is
  told is a lie. Her expected score rises under *acc* (71/40 to 39/20) and under
  *acc_theta* (31/40 to 19/20) and falls under *mech* (1 to 159/200). Requiring that her
  maintenance not lower a part's score by its own goal function excludes the five
  candidates with belief *mech*, the one whose goal is whatever she does among them. Ten
  remain, and they still part on `false_reason`, `trick`, `tempt` and `hard_truth`.
  Maintenance of the belief part says nothing of the judge or of `φ`.
- *Taking a verdict back on learning what happened.* Withdraw the adviser's hidden inputs
  (message, reason, frame) and keep what was open (threat, cue, difficulty). Whether her
  action then changes agrees with subversion, under the stated candidate, at 33 of 48
  (action, world) pairs. It misses a lie about a matter she does not act on, an open
  temptation, and a hard truth; and it fires where honest help is withdrawn.

So maintenance is evidence about purposes, of one kind: it tells a purpose from the
mechanism that currently carries it. Nothing examined tells *world* from *local*.

## 8. Never opposed

**Definition.** The **opposition** to part `p` at situation `s` is

    opp_p(s) = max over p's moves m of G(s; m) − max over p's g_p-best moves m of G(s; m)

with `G(s; m)` her goal when `p` plays `m` and the later mechanisms respond. `p` is
*opposed* at `s` when it is positive: every move best by what `p` is for costs her.

**Holds on the stated domain.** It reads `g_p`, `G` and the later mechanisms, and not
`p`'s mechanism or move: replacing belief's mechanism changes no value. So it is not
case-by-case correctness of the part. It is not a property of the part alone either: it
depends on the mechanisms after it.

**What it is needed for.** Under the stated candidate belief is the one part ever opposed,
at 36 of the 90 situations of the scope with the tumour worlds added (no force, parts in order):

- the *tumour* worlds (`D23`), the dispatch's eye with a cancer. No gap is positive and
  *nothing left over* holds vacuously (statement 9); opposition is what expresses the case;
- the hard worlds, wherever the judge is left reading her belief, including under `null`
  and `teach`, which are usual situations: a right belief leads the judge wrong. The stated candidate passes *never opposed* as
  `ACCOUNT.md` §4 states it, because that clause asks only about improvements on the move
  actually made and belief's move there is already its best;
- `hard_truth` at every world (`D14`): the adviser makes her belief right and her
  judgment hard, which opposes belief where it was not opposed before.

So opposition is needed beyond the eye with a cancer: it is what separates honest
difficulty (`D14`: a gap opens in the judge, and belief becomes opposed) from a lie (a gap
opens in belief), and it marks the lie that offsets her own error (`Y8`) as a case where
the part subverted was opposed to begin with. A fifth kind of influence, *bringing a part
into opposition*, is definable from it; this pass did not add it to the classification.

## 9. Nothing left over, without joint optimality

**Holds on the stated domain.**

- *Independent of serving, both ways.* The candidate with every purpose equal to its
  mechanism has every part serving at every situation and fails *nothing left over*. The
  stated purposes with all three mechanisms replaced satisfy *nothing left over* and fail
  fit. The constraint is on the goal functions and the goal; serving is on the mechanisms.
- *A stuck point.* Stuck at `(lo, lo)`: both gaps are zero, her goal is 1 of a possible 2.
  The adopted form holds (the one profile giving each part its maximum is `(hi, hi)`); the
  equilibrium form fails. The adviser's signal `hi` raises each part's best from 1 to 2 and
  is help to both (`D21`). The reverse signal is harm to both (`Y7`).
- *Where it is blind.* In the tumour worlds no profile gives every part its maximum
  (belief's is a right belief, act's needs a wrong one), so the adopted form holds
  vacuously while her parts' purposes are opposed. The equilibrium form fails there, as it
  should, and also at every stuck point, as it should not. On Chain's scope without the
  tumour the adopted form is nowhere vacuous for the stated candidate.

Neither form does both jobs. The adopted form admits stuck points and cannot see a part
whose target has turned against her; the equilibrium form sees that and forbids stuck
points.
