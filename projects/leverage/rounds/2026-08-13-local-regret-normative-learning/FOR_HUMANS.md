# What this round did, in plain terms

## The question

The previous round ended on a negative. It had been trying to show that a learner
which does well by a certain local measure would also have done better *over its
whole history* had it always applied a given repair. That second thing turned out
to be false, and the learning line was written down as blocked.

This round asks whether that was the right thing to have been trying to show.

## The distinction the whole round turns on

There are two different questions you can ask about a repair.

**"Would I have been better off if I had always done this?"** — compare the life I
had against the life I would have had. This requires imagining a whole alternative
history, and it is what broke.

**"On the occasions I actually faced, was there a standing better response I kept
not taking?"** — no alternative history. Just: here is what happened, here is what
each available response would have cost at that moment, and here is how often I
kept choosing the worse one.

The second is weaker. The claim is that it is also the one we actually want, and
that the standard theorem the project has been building on delivers exactly it.

## Reading the source rather than the summary

I went back to the 2007 Blum–Mansour paper instead of the repository's notes, and
three things settle it.

The theorem lets a repair rule depend on the whole history — the paper says so in
the definition. It lets the trigger for a repair depend on the history too — a
footnote says so. And, decisively, when it scores what the repair would have done,
**it scores it against the loss that actually occurred on that date.** It never
builds the alternative history at all.

So the thing that broke last round was not a hypothesis of the theorem. It was a
different quantity that the repository had come to treat as the theorem's meaning.

One correction falls out of this. The repository had been carrying a note that the
environment must be "frozen" for the theorem to apply. That is not a condition of
the theorem — it is a condition for the two quantities above to coincide. The
theorem itself is fine with a world that changes in response to what the learner
does, and its proof is a piece of algebra that holds for whatever sequence of
events actually happened.

## What had to be fixed to use it

One thing, and it matters.

A repair that changes several responses at once is useless for this argument, because
its gain on the mistake you care about can be paid for by a loss somewhere else,
and the two cancel before you can conclude anything. So the repairs here are
**surgical**: each one changes exactly one response, in exactly one kind of
situation, and leaves everything else alone.

That is not a workaround. It is the shape the original paper's own central example
already has.

With that shape the arithmetic is clean, and it comes out as an exact equality
rather than an inequality: over 4, 8, 16 and 32 rounds, the measured quantity is
precisely the size of the improvement times how often the mistake was made.

## The answer

**Yes, conditionally.** If a recognisable kind of situation keeps arising, and
there is a fixed publicly-justified better response to one particular mistake in
it, and that better response reliably saves a definite amount, then a learner with
the standard guarantee cannot keep making that mistake at a steady rate. It has to
stop.

And crucially: *the situations do not go away*. Challenges keep arriving. What
disappears is a bad way of answering them. That is the distinction the whole
architecture was built for, and it is what this result actually delivers.

I also checked the two quantities side by side on the very same run: the
alternative-history comparison diverges, growing far faster, while the local
quantity sits exactly on its bound. Both facts, one run. The divergence is real
and it does not touch the result.

## Three honest problems

**The learner never made the mistake.** I plugged in the project's existing
algorithm, and it satisfies the bound — by putting zero weight on the bad response
from the very first round. There is a structural reason: the construction is
designed so that no repair can ever gain, so it starves exactly those responses
immediately. So the inequality holds in the strongest possible way and demonstrates
no *learning at all*. I tried to build a case where the learner starts out wrong
and improves, and could not.

**A learner nobody questions has nothing to answer for.** Only burdens that have
actually been raised count. That was a deliberate fix from last round — otherwise
you would be charging an agent for every consequence of everything it ever said,
which is a demand for omniscience. But it leaves an obvious hole: an agent that
arranges never to be asked anything scores perfectly. Nothing here closes that,
and nothing here pretends to. It is the single biggest missing piece.

**Four repairs are not a repertoire.** The result says the learner does well
against the repairs you give it. It says nothing about whether those repairs cover
what a real practice would need. Of the four here, one never applies in the main
run and one is legitimate but actually makes things slightly worse — which is at
least honest, since it shows that "this repair is justified" and "this repair helps"
are genuinely separate judgements in the model.

## So is it normative learning?

The mathematics works. Whether it deserves that name is not settled here, and I
have not pretended otherwise.

The case for: what vanishes is not "an action with a lower score existed" but a
recurring failure to take a specific, publicly justified response — one whose
justification is checked without ever looking at what it earns, and whose
occasions are generated by someone else, not by the learner.

The case against: it is still a statement about single moves on the path actually
taken. What would make it genuinely *normative* learning is that the repertoire of
repairs is normatively adequate — and four hand-picked rules do not show that.

So the verdict is split: the mathematical path is open, and the interpretation
rests on a question about repertoire and about inquiry that this round leaves
open and names precisely.
