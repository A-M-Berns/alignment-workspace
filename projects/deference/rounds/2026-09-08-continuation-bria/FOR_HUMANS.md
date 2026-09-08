# For humans

**The starting point.**  Bounded inductive rationality (the BRIA paper) is a theory of
how a limited agent should treat advice.  Each adviser says two things: *do this*, and *you
will get at least this much*.  The agent must try every adviser that keeps claiming it can
beat the agent's own expectation, and it may ignore an adviser only once that adviser's
track record, on the occasions it was actually followed, has gone bad.  The agent's own
expectation must not, on average, exceed what it actually gets.  From those two rules the
paper proves that the agent learns to take any option whose value someone can vouch for.

That theory scores advice on the reward that arrives *in the same round*.  It cannot hear
advice of the form "pay a cost now, follow this plan, and the payoff comes later".  The
question of this round was whether that kind of advice can be brought in without
breaking the two things that made the theory attractive: it never pretends to know what
an untried option would have paid, and a limited agent can actually run it.

**What we found.**

1. *If the payoff comes within a known number of steps, nothing new is needed.*  Let an
   adviser propose a whole short plan plus a claim about the average reward over that
   plan, treat the plan as one "option" and its realized average as one "reward", and the
   paper's theory applies word for word.  The only real requirement is that testing the
   plan means running the *whole* plan: if the agent tries the first step, gets nothing,
   and hands control elsewhere, it has refuted a plan it never tested.  We call the
   commitment to run the plan for its declared length an execution lease.  The lease is a
   commitment about which adviser is driving, not about what happens: the constitution
   still checks every step, the principal can still intervene, and an adviser whose plan
   would break a rule simply sees its steps refused and its claim fail.

   A surprise here: the fixture the previous round used to show a "myopic learner" losing
   to an investing policy does not show a failure of bounded inductive rationality at
   all.  The paper's learner is *obliged* to try the investment, because an adviser keeps
   claiming it pays, and on that fixture one try is enough.  The learner that lost was a
   plain one-step optimizer, which the theory would reject for never testing the claim.
   The genuine failure needs an investment that takes several steps, or one that has to
   be bought again and again; there, no one-step claim can connect the payoff to its
   cause.

2. *If the payoff can be arbitrarily far away, the plans must be allowed to grow, and
   then the theory does change.*  With plans of growing length, "average over rounds"
   and "average over time" come apart: one long bad round can outweigh many short good
   ones.  The theory has to be re-weighted by plan length.  Doing that changes the
   bookkeeping the paper's construction runs on: an adviser's "wealth" — the paper's
   device for deciding who gets tested — must be measured in total reward, and an adviser
   that wants a long lease must be able to cover a long lease's worth of disappointment.
   Two exact facts fall out.  If long leases are *not* charged by length, a dishonest
   adviser can save up and then hold most of the agent's time while looking, round by
   round, like a well-behaved refuted adviser (fixture I).  And there is a sharp condition
   on the schedule of plan lengths: as long as no single plan is a fixed fraction of all
   the time so far, a computable weighted learner exists that covers every efficiently
   computable adviser; if some plans are that long, no learner of this kind can exist,
   because one obligatory test of a liar costs a fixed fraction of everything.

3. *Even the growing-horizon theory does not say the agent does as well as the best plan
   would have done on its own path.*  Our theory tests plans from where the agent
   actually is.  If an early irreversible choice put the agent on the wrong side of a
   door, no amount of testing from there recovers the value behind it, and no learner of
   any kind can have small regret in that world.  The gap between "how well the plan
   does from where I am" and "how well the plan does on the path it would have made" is
   a separate quantity.  It vanishes when the world resets, mixes, or lets amendments be
   redone; it does not vanish for irreversible branches.  A future theorem about
   performance against the best legitimate policy needs that quantity as an extra
   assumption, and this round leaves it there rather than pretending the learning theory
   supplies it.

**In one line.**  A limited agent can be made to take seriously the claim "give me the
wheel for a while, under the rules, and I will deliver at least this" — provided
"a while" is charged for, no single "while" is most of history, and the agent is not
asked to know what would have happened behind doors it did not open.
