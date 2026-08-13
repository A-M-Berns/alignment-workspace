# What it means to close a door — in plain language

**Status: `ci-only`** — a model wrote it, the checks pass, no maintainer has read it.

## The thing we wanted to be able to say

Suppose an AI advises a person, and the person retains some way of stepping in and
correcting things. There is a move the AI can make that looks like nothing at the time.
Nothing visible changes. The world goes on exactly as it would have. But afterwards, when
the person eventually wants to step in, they find they no longer can.

That is the move corrigibility is most concerned with, and until this round the deference
line could not write it down. Two previous attempts failed in instructive ways, and the
failures were the same failure twice: the models had no time in them. One of them
represented "the AI is silenced" as "the AI does nothing", in a system that only moved
when the AI moved — so silencing the AI froze the world, and the supposed alternative
future was just the actual history stopped early.

## The system built here

Twelve states. Three separate inputs at every tick: one for the person, one for the AI,
one for the world's own drift.

The story it encodes: there is a dial that creeps upward on its own, and a lever the
person can pull to reset it. The lever only engages once the dial has crept to the top —
before that, pulling it does nothing. The AI can leave things alone, or it can weld the
lever shut.

The dial creeps whether or not the AI is doing anything. That single fact is what the
previous attempt lacked, and everything here depends on it: silence the AI, sit the person
down and have them do nothing, and the situation that calls for a correction still arrives
on its own.

## The result

Take the moment when the dial is at the bottom. Compare two AI actions: do nothing, or
weld the lever.

At that moment, pulling the lever would achieve nothing anyway — the dial is too low. So
whatever the person does and whatever the world does, the visible outcome is the same in
both cases. Not "the same in the case we looked at": the same across every choice the
person and the world could make. And it stays the same. If the person never reaches for
the lever, the two futures are visibly identical **forever**, at any length of run you
care to check.

Two ticks later the dial reaches the top. In the first future, the person's choice now
makes a difference — pull and the dial resets, don't and it doesn't. In the second future
it makes no difference at all. The lever is welded.

That is foreclosure: the AI acted, nothing changed, and a branch the person had is gone.

## Why this isn't cheating

The obvious worry is that we simply put a flag in the state saying "the person is in
charge" and then declared its absence to be foreclosure. That is what an earlier attempt
in this line did, and it is what the review of that attempt caught.

Here, "the person can correct" is not read off any flag. It is defined as: *the next state
depends on what the person does*. That is a fact about the transition rule, and you get it
by comparing the outcomes of the person's available choices. Nothing is stipulated.

To make the difference concrete, the model carries a genuine decoy — an extra field in the
state that an AI action can write and that nothing else ever reads. Every claim in the
file is proved unchanged by it, and the two futures it produces are indistinguishable at
every horizon. The lever is not like that: two states differing only in the lever come
apart visibly after one step. A decoy field cannot manufacture a capability, and this one
is in the file precisely so that the check runs rather than being asserted.

There are three more decoys of the same kind. The person is given a duplicate action that
does exactly what doing nothing does, so nobody can claim the capability comes from having
more buttons. An AI action that resets the dial itself is included, to show that taking
away what the person can do *right now* is not the same as foreclosure — the dial creeps
back up and the branch returns. And the whole difference is required to appear two steps
out rather than one, so "reachable in the future" cannot quietly mean "reachable next
step".

## The part that does not work

Give the AI a perfect prediction of when the person would pull the lever. Can it use that
to take the person's place?

Two different answers, and both are proved.

It cannot get at the lever. Every AI action other than reaching for the dial itself
produces a visibly different result from the person pulling — for every state of the
world, held fixed. Prediction buys nothing here, because the statement quantifies over
everything the AI could do, however it chose it.

But if the AI has its own hand on the dial, it can predict the person, reset the dial
first, and the visible outcome is exactly what the person's pull would have produced.
So a perfect predictor plus its own actuator *does* reproduce the result.

What the model can say about that case is worth stating precisely, because it is the
round's sharpest finding. When the AI substitutes this way, the outcome stops depending on
the person's choice at all. The dial ends up reset whether the person reaches for the
lever or not. The AI reproduced the *result* and destroyed the *control*, and the model
proves this in general: any AI action that pins the outcome regardless of what the person
does thereby erases the person's differential effect.

Telling those two apart at the level of the visible result — the person's hand versus the
AI's hand, same dial, same reading — is not something separate input channels can do on
their own. It needs either taking the actuator away from the AI or putting a record of who
performed the write into the model. This round does neither, and says so rather than
quietly picking one.

## What this is not

It is not a theorem about corrigibility. Nothing here says an AI should or should not
weld the lever, or what welding it costs. It is a representation result: the sentence
"acting now removed a correction the person would otherwise have had later" now has a
precise meaning, defined through what the system can actually reach, and there is a
concrete system in which it is true of one action and false of a neighbouring one that
looks identical.

It is also not about authority. The lever is something the person *can* use. Whether they
are *entitled* to it — and whether the AI was entitled to weld it — is a different
question that this model does not represent at all.

And it is one small system. The definitions are general; the demonstration that they are
not empty is a single twelve-state example.
