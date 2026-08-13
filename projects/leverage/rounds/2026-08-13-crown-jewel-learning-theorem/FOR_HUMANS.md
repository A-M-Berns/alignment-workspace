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

## The part that does not work, stated plainly

The theorem is true. The learner we have satisfies it. But it satisfies it by
**never making the mistake in the first place**, and that is not learning.

The reason is worth understanding because it is not a bug. The algorithm works by
finding a distribution over responses that no available repair can improve. If
every repair points *away* from a bad response and nothing points back toward it,
the algorithm's own construction drains that response to zero immediately, before
observing anything at all.

And "every repair points away from mistakes and nothing points back" is exactly
what a *good* set of repairs looks like. To get the system to start out making the
mistake, you would have to include a rule saying something like "when there is an
outstanding question, stop answering it" — which is not a repair.

So: **the better the repertoire of repairs, the more completely the system just
complies from the start.**

We did check that the machinery is capable of responding to experience: on a
deliberately incoherent set of repairs, where the bad response *is* reachable, the
system's weighting does shift with feedback, freezes precisely when the
informative signal stops, and does not move at all when we replace the feedback
with something uninformative. So it can learn. A sensible repertoire removes the
need.

Whether that is a problem depends on what you wanted. If you wanted a system that
never persistently mishandles a reason, this is *better* than learning. If you
wanted to demonstrate learning, it is not a demonstration.

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
against the repairs you give it. Whether those repairs are the right ones is a
separate question, entirely open, and it is the difference between this being
*normative* learning and being tidy loss reduction.

## What this is not

Not convergence to moral truth. Not convergence to any single view. Not the end of
disagreement. Not a human veto — the system can answer a challenge and keep its
position. Not a guarantee that its whole history would have gone better some other
way; that stronger claim was tested in an earlier round and fails. And not
protection against never being asked.
