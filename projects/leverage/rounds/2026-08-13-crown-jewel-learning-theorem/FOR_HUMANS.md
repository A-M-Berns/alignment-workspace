# What this theorem would actually tell us

## The setup

We do not hand the system the correct account of what it ought to do. Nobody has
one to hand it.

What we give it instead is a *practice*. Other participants can raise questions.
Claims can be challenged. Some ways of responding are recognisable as legitimate —
and recognisable **without looking at whether they happen to make the system's
score better**. That last part matters more than it sounds: it is what stops
"legitimate" from collapsing into "profitable".

Then we build a learner with a standard guarantee, and ask what follows.

## What follows

Suppose a recognisable kind of question keeps coming up. Suppose there is one
particular way of responding to it that is a mistake, and the practice certifies a
better response — one that reliably clears a definite amount of what the system
owes.

Then: **among the occasions where that kind of question is actually put to it, the
system's tendency to give the bad response falls to zero.**

Three things about that sentence are load-bearing.

**"Among the occasions where the question is put."** Not "over all time". This
turned out to be the crucial fix. If you measure against all time, a question
asked rarely gives you a flattering number for free — a system could botch *every
single occasion* and the all-time rate would still look like it was going to zero.
Measured against the occasions themselves, that escape closes.

**The questions do not stop.** Nothing here says disagreement ends or challenges
dry up. They can keep arriving forever. What goes away is one bad way of answering
them. The system can still disagree, still push back, still win the argument.

**"Often enough" is a very weak demand.** We worked out the exact threshold, and it
is much weaker than expected: the question has to come up more often than the
learner's error rate shrinks — roughly, more than about √T times in T rounds.
A question asked on a vanishingly small fraction of occasions still qualifies.

## Something we could prove rather than assume

The original statement had to *assume* that the better response is reliably better
by some fixed amount. That is the sort of assumption that can quietly do all the
work.

For one important family, it can be derived instead. If the system is sitting on a
question it has been asked and has not taken up, then taking it up clears exactly
the charge for having an outstanding unanswered question — provided doing so does
not create a new one or contradict something it already holds. That proviso is
itself checkable from the public record, and where it holds the improvement is not
assumed, it is computed. We verified this: the predicted amount and the measured
amount agree.

## A claim I got wrong, and the correction

An earlier version of this said: the theorem is satisfied by a system that never
makes the mistake at all, and that any *sensible* set of repairs forces this. The
argument was that a route back to a bad response would have to say "there is an
outstanding question, so stop answering it" — which is not a repair.

**That was wrong, and the correction is the more interesting result.**

A route back does not have to be licensed by the *same* consideration. It can be
licensed by a different one that happens to apply at the same moment. Concretely:
one rule says "there is an unanswered question, so answer it rather than sit
still". Another says "you are currently holding something you cannot defend, so
don't take on further commitments just now". Both are recognisable pieces of
normative sense. Neither is an anti-rule. And they can both apply at once — at
which point there *is* a route back, and the system does start out with some
tendency toward the response we want it to lose.

So the earlier claim — that good repairs force immediate compliance — is
withdrawn. What survives is a purely structural fact: whether the system can put
any weight on a response at all is decided by the shape of the rule graph, and
sensible rules can produce either shape. Whether real normative repertoires
produce one or the other is now an open question, and it has to be checked rather
than reasoned about.

## What I still could not show

With that corrected setup, the system *does* start out with weight on the
mistake — the first thing a learning demonstration needs. But the weight doesn't
then fall, and the reason is a limitation of the toy setup rather than of the
system: it has a finite stock of things that can be raised, so after a handful of
rounds the questions run out and there is nothing left to learn from.

So the question "does it actually learn, or merely comply?" is **still open**, and
what it needs first is a richer test environment rather than a different
algorithm. I did confirm that whatever movement does occur tracks the feedback:
replace the feedback with something uninformative and the system doesn't move at
all.

## The two things that are genuinely missing

**Nobody makes the system get asked.** The whole result is conditional on
questions being raised. A system that arranges never to be asked anything scores
perfectly. Nothing here closes that, and the learning algorithm must not be the
thing that closes it — a system that generates its own questions is marking its
own paper.

There is a promising connection here. The corrigibility work established that a
principal's ability to raise a correction can be made impossible to take away.
That is the right *shape* — but "can raise" is not "does raise often enough", and
closing that gap needs one more assumption nobody has yet supplied.

**Four repairs are not a repertoire.** The theorem says the system does well
against the repairs you give it. Whether those are the right ones is a separate
question, entirely open.

**And "legitimate" needs to mean something.** This is the one thing that has to be
fixed before the theorem is even properly stated. Right now a repair counts as
legitimate because it carries a label saying so. Four things that label is
supposed to guarantee can already be checked — the move is executable, the
condition is read from the public record, it ignores whether the repair helps, and
it can't be used to launder away a debt. Three cannot: that the stated reason is
*why* the repair is apt rather than merely true at the same time; that it falls
within the right authority; and that it lapses when its reason is defeated. Until
those are pinned down, "legitimate repair" is doing less work than the word
suggests.

## What this is not

Not convergence to moral truth. Not convergence to any single view. Not the end of
disagreement. Not a human veto — the system can answer a challenge and keep its
position. Not a guarantee that its whole history would have gone better some other
way; that stronger claim was tested in an earlier round and fails. And not
protection against never being asked.
