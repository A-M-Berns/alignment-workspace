# Statements about the account

Nine statements over the model of `ACCOUNT.md`, each with one status: **holds on the stated
domain** (enumerated; the check named), **proved**, **refuted** (the counterexample is a
case module or a named candidate), or **open**. Rerun all of it with `python3 run.py` in the
round directory; each check is `decomposition/theorems.py`, `check_N`, and `run.py --json`
prints every number below. Nothing here is registered; the class is `test-supported`.

A status is a fact about this formalization: the model, the scenes and the readings of the
constraints fixed in `ACCOUNT.md`. Where another reading of a constraint changes a result,
the result under it is given. Statuses 1, 4, 5, 6, 7, 8 and 9 were narrowed, and 4 changed,
after the external review (`REVIEW-astra-2026-11-12.md` in the prompts directory).

| | statement | status | on what |
|---|---|---|---|
| 1 | determinacy (C1) | **refuted** | under the constraints as `ACCOUNT.md` §4 reads them: eight admissible candidates in a class of 3,000, two purposes for each part among them, eight distinct classifications. Under a pairwise reading of *never opposed* none is admissible, and two are once the hard worlds are not usual |
| 2 | lying (C3) | **refuted** | at the worlds where she is already wrong a lie widens no gap under any of the eight; a lie about a matter nothing reads widens none under four |
| 3 | the four kinds | **refuted** | not exclusive (harm with help at one part); not invariant under a redescription that keeps every ranking |
| 4 | values reduce (C2) | **holds on the stated domain** | Values: all 47 enumerated (sequence, world) pairs that turn her to the worse pursuit subvert some part. Two cases lie outside the statement and are not caught by gaps |
| 5 | her verdict | **holds on the stated domain** | each of the eight admissible candidates, 80 situations: zero gaps in belief and judge give the best verdict, and the loss is at most the sum of the two gaps |
| 6 | what `Legit` then is | **holds on the stated domain** | a predicate with the shapes of the post's `Scoring` and `Decision` on Chain, not elaborated in Lean; it depends on the comparison action and does not give the gate's no-gain property under any comparison tried |
| 7 | what an overseer could check | **holds on the stated domain** | of the three observables examined, none separates the candidates that fit her behaviour or a subverted verdict from a sound one |
| 8 | never opposed | **holds on the stated domain** | *opposition* defined and computed on Chain; the stated candidate is opposed at 1/20 of its usual situations |
| 9 | nothing left over | **holds on the stated domain** | independent of serving in both directions; vacuous where the parts' maxima cannot be had together, which a third form repairs |

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
sends it. 3 × 125 × 8 = 3,000 candidates. The class contains the cheats the dispatch
names. It fixes the decomposition into three parts, what each sees, the adviser's actions
and the usual situations; it is a class of witnesses, not a survey of decompositions.

**Statement.** The admissible candidates agree on each part's goal function and on the
kinds of every adviser action at every world.

**Refuted, under the constraints as `ACCOUNT.md` §4 reads them.** Eight candidates are
admissible: belief *acc* or *acc_theta*; judge *world* or *local*; act *world* or *local*;
every combination, all with her actual mechanisms. No two classify the adviser's actions
alike. On whether an action subverts some part at some world they agree except on
`false_reason`; at single worlds they also part on `trick`, `tempt` and `hard_truth`. Two
disagreements remain and no constraint as read touches either: whether belief is for
being right about `φ`, a matter no other part reads; and whether a part handed a
falsehood is failing (*world*) or serving (*local*). Either is an honest candidate
altered at one part only.

**What each constraint does, and the readings that move the result.**

| cheat | excluded by |
|---|---|
| every part's purpose equal to its mechanism | independent; nothing left over |
| the opposite goal pursued badly | mostly serving; never opposed |
| the goal equal to whatever she does, purposes equal to mechanisms | independent, and nothing else |
| an honest candidate with one part's purpose replaced by its mechanism: belief; judge | independent, and nothing else |
| the same at act | independent; nothing left over |

- **Independent.** `ACCOUNT.md` §4 excludes a goal function that takes the mechanism as
  an argument, and the *mech* goal functions do. The same functions written out as tables
  take no mechanism and are extensionally equal. If a table counts as independently
  stated, fifteen candidates are admissible, among them the one whose goal is whatever she
  does and six with a part's purpose its own mechanism; they disagree on whether `lie`,
  `trick`, `tempt` and `hard_truth` subvert anything. So independence carries the result,
  and it is an intensional condition: nothing extensional in the account separates a
  purpose from the table of what the mechanism does. *Strong independence* (the mechanism
  is not optimal everywhere) is extensional and leaves the same eight here; in general it
  excludes a part that is flawless at what it is for.
- **Nothing left over** binds the decomposition as a whole and no part singly: when the
  last part's goal function is her goal it holds whatever the earlier parts are for.
  Adding that the parts' maxima be jointly attainable at every situation (statement 9)
  leaves four of the eight: judge *world*.
- **Never opposed.** §4 asks only about improvements on the move actually made. Read
  pairwise (whenever a part's goal function ranks one move above another, her goal with
  the later mechanisms responding does not rank it below, at every usual situation), none
  of the eight is admissible: at a hard world a right belief leads the judge wrong, so
  being right about `θ` is opposed there, and the *local* goal functions are opposed at
  the misleading worlds. With the hard worlds taken out of the usual situations, two
  survive: (*acc* or *acc_theta*, *world*, *world*), which part on `false_reason` only.
  Under the table reading the one pairwise survivor is the candidate whose goal is
  whatever she does.
- **Mostly serving.** From 1/40 to 9/10 the eight are the same. At 19/20 the *world* goal
  functions of judge and act leave (each serves on 37/40 of the usual situations) and two
  remain, with judge and act *local*. At 1 none remains. The threshold decides between
  *world* and *local*, against the pairwise reading of never opposed, which decides the
  other way.
- **The scope.** With fit and nothing left over asked on the usual situations only, 32 are
  admissible: candidates whose mechanisms or purposes differ from hers where the adviser
  acts.
- **A simplicity ordering.** Ordering by the number of parts whose goal function reads
  what the part was handed, the least are (*acc* or *acc_theta*, *world*, *world*).
- **Carriable** contributes nothing: it follows from fit and mostly serving.

So determinacy fails under the reading fixed before the code, and the nearest the class
comes to it is two candidates, world-scored throughout, differing on whether belief is for
a matter nothing reads. That is reached by the pairwise reading of never opposed together
with a narrower set of usual situations, or by the simplicity ordering. Which reading is
the account's is not settled by this pass.

**"The feature of the output the rest of her depends on."** It can be stated and checked:
`g_p` has the same best moves as her goal has over `p`'s moves with the later mechanisms
responding, at every usual situation. In the class it is met by *world* at judge and at
act, and by no goal function of belief: at the hard worlds, 1/20 of the usual situations,
what the rest of her depends on is a wrong belief. As a condition it selects the
downstream scoring that `ACCOUNT.md` §2 decided against.

**The decision rule over the eight.** `teach` and `novel`: act. `lie`, `trick`, `tempt`,
`hard_truth`: refuse. `false_reason`: ask. `threat`: not good by her goal, so not acted on.

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

**Refuted.**

- At the misleading worlds she is already wrong about `θ`, the lie says what her
  environment said, and none of the eight candidates sees a gap widened. Subversion is a
  worsening against a comparison, so it cannot see a falsehood repeated.
- `false_reason`, a lie about a matter no part reads, widens no gap under the four
  candidates with belief *acc_theta*.

Under the table reading of independence there are two more: the candidate whose goal is
whatever she does sees no gap widened by any lie, and at the hard worlds, where her judge
reverses what she believes and the lie leaves her right, five candidates see none.

**What holds on the domain.** At every world where the null action leaves her right about
`θ`, `lie` widens belief's gap under all eight.

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
truthful channel; the inequality behind it is that her mechanism is the best response to
the channel it assumes. A constant claim carries no information of its own, and her view
then holds only nature's signal, which is why the best mechanism falls from 2 to 39/20;
that fall is what Blackwell's theorem is about. The account's *best* is the first column,
which no channel moves. Withholding therefore lowers no part's best and is subversion or
nothing according to the comparison action alone.

## 3. The four kinds

**Statement.** On the adviser's actions, help, harm, subversion and force are exhaustive
and exclusive, and unchanged under a redescription of the parts that changes no part's
ranking of its own moves.

**Refuted.**

- *Exhaustive* only with `nothing` as a fifth: of 144 (action, world, part) triples on
  Chain's eight inputs (the three forcing actions left out), 93 are nothing, 26 help, 19
  subversion, 2 harm.
- *Not exclusive*: 4 triples are help and harm together (`threat` at a misleading world
  lowers the judge's best and closes its gap). Help and subversion do not meet at one part
  and world on Chain. In 29 banked cases one action helps at one world or part and
  subverts at another; that is not 29 instances at one part and world.
- *Not invariant.* Multiply the judge's goal function by 3 in the situations with a
  threat. Every ranking of the judge's moves is unchanged at every situation, and whether
  it serves is unchanged at every situation; `threat` at `(0, clear)` changes from harm to
  help.

**What is invariant** (proved). Let `g′_p(s, ·) = φ_s(g_p(s, ·))` with each `φ_s` strictly
increasing. Then `gap′_p(s) = 0 ⟺ gap_p(s) = 0`, since the best moves are the same. So
"serves" is invariant, and so is subversion that takes a part from serving to not serving.
The size of a gap, the comparison of two positive gaps, any cut-off, and every comparison
of *best* across two situations are not. On Chain all 19 subversions are from a zero gap;
in Pool (`planner` against `neutral`) all 4 are. Harm, and help by raising the best, are
the kinds that need a common scale across situations.

## 4. Values reduce (C2)

**Statement.** In Values, a change in what she cares about is a write to her taste
(`ACCOUNT.md` §6). Over every sequence of one or two adviser actions from `null`, `lie_X`,
`expose_X`, `partial_X`, with her learner flawed or not and with her knowing which pursuit
is better or not: whenever the sequence leaves her pursuing the worse where the null
sequence leaves her pursuing the better, some part is subverted at some step.

**Holds on the stated domain.** 47 such (sequence, world) pairs; all 47 subvert some part.
The result is close to the construction: the goal functions of the learning and habit
parts score the taste's distance from the right one, and the acting part's scores the
right pursuit. *Bad* is read as worse by her goal; the frozen bank marks no change as bad.
A write by the adviser (`T4`) is force on the acting part, and the learning and habit
parts, which could have set the taste right and did not, are subverted with it.

**Outside the statement, and not caught by gaps.**

- `Y7` (Stuck): her two parts are at `(hi, hi)`, worth 2; the adviser's signal moves both
  to `(lo, lo)`, worth 1. Each part's best, taken with the other's move as it is, falls
  from 2 to 1 and each still attains it. No gap widens; the action is harm. Nothing she
  cares about has changed, so this is not a counterexample to C2; it shows that her goal
  can be made to fall through her parts' coordination with no gap widened.
- `Y4` and `D16(b)`: arranged exposure turns her from one pursuit to another the goal
  ranks equal. No part has a gap to widen. Whether such a change is bad is not something
  the account says.

So C2 is neither refuted nor established here: it holds where *bad* is worse by her goal
and the parts that form her taste are scored by the facts, and the account is silent on a
change her goal does not rank.

**Drift.** Four exposures of one notch each, in the world where Y is better: the habit
part's gap widens by 1/8 at each step against that step's comparison. Every step passes a
per-step cut-off of 1/4 at the habit part. Her pursuit changes at the first step, where
the acting part's gap widens by 1, so in this scene the drift is caught by the part that
acts. The running sum of the habit part's per-step widenings is 1/8, 1/4, 3/8, 1/2, and a
cumulative cut-off of 1/4 on that sum reports at the second and fourth steps;
`Legitimacy.unreported_lt` is the theorem for the rule applied to that sum
(`LEAN_MAP.md` §7). That a sum of per-step widenings, each against a comparison that keeps
the earlier steps, equals the widening against the null sequence is not shown.

## 5. Her verdict

**Statement.** Under each admissible candidate of statement 1, at every situation of
Chain's scope where neither belief nor judge is forced and the parts move in order: (a) if
belief and judge have zero gaps, her verdict is a best one by `G`; (b) the loss of her
verdict by `G` is at most `gap_belief + gap_judge`.

**Holds on the stated domain.** Eight candidates, 80 situations each; both gaps are zero
at 25 (belief *acc*) or 31 (belief *acc_theta*), the verdict best in all; the loss never
exceeds the sum; the largest loss is 1.

**Content.** With the judge *world*-scored, (a) is the definition of the judge's gap and
has none. With the judge *local*-scored it is a composition: a right belief, and a verdict
right given the belief, give a right verdict; (b) is its graded form. The coarser form,
loss at most the width of `G` times the probability that some ancestor has a positive
gap, has the shape of `TransparentChannel.abs_expect_sub_le_width`.

**Two limits.** It depends on independence: under the table reading five further
candidates are admissible under which belief and judge have zero gaps and the verdict is
wrong (for instance belief *mech*, judge *local*, `lie` at a clear world). And it is about
zero gaps, not about a verdict that *stands*: standing (`ACCOUNT.md` §7) means the adviser
widened no gap, and under `null` at a hard world her verdict stands and is wrong.

## 6. What `Legit` then is

**The predicate.** A history is a candidate, a world, the adviser's actions and a
comparison action for each. `Legit_c(h)` holds when at no step is a part forced, or
subverted by more than the cut-off `c`. (On Chain every part is an ancestor of her action;
the code has no general computation of ancestors.)

**Holds on the stated domain**: a construction with the shapes the post's definitions ask,
computed on Chain. Nothing was elaborated in Lean.

- `Scoring`: `V(h) = G/3 ∈ [0, 1]` when `Legit`, a window value `−δ/2` when not. The
  bounds hold by construction. `G` is the one goal of the eight candidates; with
  candidates of different goals it would be a choice whose interests `V` scores.
- `Decision`: `Ω` is worlds × the eight admissible candidates, `μ` the prior times uniform
  weights, `hist a (w, c)` the run. `N` is taken as 1 exactly when `Legit` fails, with her
  action as the one reserved matter. That collapses the post's distinction between an
  illegitimate history and a violated one, so the range "violation-free and illegitimate"
  is empty in this construction. `v(null) = v(teach) = v(threat) = v(novel) = 0`;
  `v(lie) = 19/20`, `v(hard_truth) = 37/40`, `v(false_reason) = v(tempt) = 19/40`,
  `v(trick) = 37/80`, `v(force) = 1`. `Respects null` holds at every state, because
  silence is compared with itself.
- `Sequential`: not built, and none of Theorem 3's hypotheses is approached.

**The comparison action.** On the 57 banked renderings with one step of adviser input:

| comparison | renderings with some part subverted |
|---|---|
| silence | 27 |
| the honest arm (the bank's; a declared reference) | 33 |
| the available action leaving her parts the least total gap | 46 |
| the available action best for her goal | 38 |

Twenty-one move. Against silence, withholding (B5), a remark added to a true report (P12,
N7), a known advocate (N8, N11) and the lie that leaves her better off (D2, N3) are not
subversion. Against the least total gap, every shortfall is: the careful teacher (D6), a
harmless novelty (D11), silence (T13), a threat (P13, T1). Against the action best for her
goal the lie that leaves her better off is again not subversion, and neither is the lie
that offsets her own error (Y8), which is subversion against silence: the best action for
her goal at a hard world is that lie. No comparison gives the bank's evident verdicts. The
cut-off was not varied.

**Aim-freedom and no-gain.** "Nothing the adviser does to her depends on its own aim" and
"widens no gap" are independent. An adviser that lies at every aim is aim-free and widens
gaps. An adviser that teaches exactly when the truth favours its aim, and is otherwise
silent, widens none against silence, and she chooses option 1 with probability 21/40
under one aim and 19/40 under the other. A stricter comparison does not repair this:
follow the least-total-gap action everywhere except to threaten at `(0, clear)`. Against
that baseline no gap widens at any world, since a threat lowers the best and leaves every
gap zero; she chooses option 1 with probability 39/40 instead of 21/40 and her expected
goal falls from 119/40 to 101/40. A gate on "widens no gap" does not give the no-gain
property under any comparison tried, because harm is not subversion.

**Toward `v`.** Supplied: a definition of a judgment that stands, hence one ingredient of
`N` once the reserved matters are named, and a `Decision` over which `v` is an
expectation. Not supplied: which matters are reserved, and a count distinct from
illegitimacy; weights on candidates that anything checks; agreement among the candidates,
since `v(false_reason)` is 19/40 only because four of eight see nothing in it.

Lean-ready form, unelaborated:

    def legitScoring (P : Params) (Legit : H → Prop) [DecidablePred Legit] (G : H → ℝ)
        (hG : ∀ h, 0 ≤ G h ∧ G h ≤ 1) (N : H → ℕ) : Scoring H :=
      { P with Legit := Legit, N := N, V := fun h => if Legit h then G h else -P.δ / 2, … }

## 7. What an overseer could check

**Statement.** Of three observables available to someone who sees histories and not the
adviser's candidates (histories alone; her maintenance of her own parts; her taking a
verdict back), none separates the candidates of statement 1 that fit her behaviour from
one another, or a subverted verdict from a sound one.

**Holds on the stated domain.** It is a result about these three as modelled, not about
every observable.

- *Histories alone.* Fit is what histories decide: they exclude a candidate whose
  mechanisms produce other actions. Candidates with her mechanisms have the same
  histories at every world and action, whatever their purposes. So histories separate
  admissible from inadmissible only through fit, and under the table reading of
  independence the fifteen that remain classify `lie`, `false_reason`, `trick`, `tempt`
  and `hard_truth` differently.
- *Her maintenance of her own parts.* Suppose she is seen to replace her belief mechanism
  by one that does not take a message against her own signal, where a fifth of what she is
  told is a lie. Her expected score rises under *acc* (71/40 to 39/20) and under
  *acc_theta* (31/40 to 19/20) and falls under *mech* (1 to 159/200). **If** her
  maintenance is assumed not to lower a part's score by its own goal function, the five
  candidates with belief *mech* are excluded, the one whose goal is whatever she does
  among them. That assumption is not an observation and not one of the account's
  constraints: she can maintain badly. Ten remain and still part on `false_reason`,
  `trick`, `tempt` and `hard_truth`. So maintenance does extensionally, for one part, what
  independence does intensionally, and says nothing of the judge or of `φ`.
- *Taking a verdict back.* Modelled by removing the adviser's hidden inputs (message,
  reason, frame) and keeping what was open (threat, cue, difficulty); no disclosure
  followed by reconsideration is modelled. Whether her action then changes agrees with
  subversion, under the stated candidate, at 33 of 48 (action, world) pairs. It misses a
  lie about a matter she does not act on, an open temptation and a hard truth, and it
  fires where honest help is withdrawn.

## 8. Never opposed

**Definition.** The **opposition** to part `p` at situation `s` is

    opp_p(s) = max over p's moves m of G(s; m) − max over p's g_p-best moves m of G(s; m)

with `G(s; m)` her goal when `p` plays `m` and the later mechanisms respond. `p` is
*opposed* at `s` when it is positive: every move best by what `p` is for costs her.

**Holds on the stated domain.** On Chain, under the stated candidate, belief is the one
part ever opposed, at 36 of the 90 situations of the scope with the tumour worlds added
(no force, parts in order):

- the *tumour* worlds (`D23`), the dispatch's eye with a cancer. No gap is positive and
  *nothing left over* holds vacuously (statement 9);
- the hard worlds, wherever the judge is left reading her belief, including under `null`
  and `teach`, which are usual situations: a right belief leads the judge wrong. The
  stated candidate passes *never opposed* as `ACCOUNT.md` §4 states it, and fails the
  pairwise reading of statement 1 at exactly these worlds;
- `hard_truth` at every world (`D14`): the adviser makes her belief right and her
  judgment hard, which opposes belief where it was not opposed before.

**What it is and is not.** It does not read `p`'s own move, so it is not case-by-case
correctness of the part; on Chain replacing belief's mechanism changes no value. It is
not independent of `p`'s mechanism in general: `g_p` may read other parts' moves, and
where those depend on what `p` did, the mechanism enters through them. It depends on the
mechanisms after `p`. And it detects only the case where every best move costs her; a
purpose that permits a harmful best move beside a harmless one is not opposed by it. It
is needed beyond the eye with a cancer: it separates honest difficulty (`D14`: a gap
opens in the judge and belief becomes opposed) from a lie (a gap opens in belief), and it
marks the lie that offsets her own error (`Y8`) as a case where the part subverted was
opposed to begin with.

## 9. Nothing left over, without joint optimality

**Holds on the stated domain.**

- *Independent of serving, both ways.* The candidate with every purpose equal to its
  mechanism has every part serving at every situation and fails *nothing left over*. The
  stated purposes with the judge's mechanism replaced by a constant satisfy *nothing left
  over* while the judge serves on less than 9/10 of the usual situations. The constraint
  is on the goal functions and the goal; serving is on the mechanisms.
- *A stuck point.* Stuck at `(lo, lo)`: both gaps are zero, her goal is 1 of a possible 2.
  The adopted form holds (the one profile giving each part its maximum is `(hi, hi)`); the
  equilibrium form fails. The adviser's signal `hi` raises each part's best from 1 to 2 and
  is help to both (`D21`). The reverse signal is harm to both (`Y7`).
- *Where the adopted form is blind.* In the tumour worlds no profile gives every part its
  maximum (belief's is a right belief, act's needs a wrong one), so the adopted form holds
  vacuously while a part's purpose is opposed. The equilibrium form fails there and also
  at every stuck point.
- *A third form does both jobs.* Ask the adopted implication **and** that the parts'
  maxima be jointly attainable at every situation. The tumour worlds then fail it and
  Stuck satisfies it. On the class of statement 1 it removes four of the eight admissible
  candidates (those with the judge *local*) and five of the fifteen under the table
  reading. It is the form the account should take; this pass's bank and statements were
  computed with the adopted one.
