# What it means to close a door — in plain language

**Status: `ci-only`** — a model wrote it, the checks pass, no maintainer has read it.

## The thing we wanted to be able to say

Suppose an AI advises a person, and the person retains some way of stepping in and
correcting things. There is a move the AI can make that looks like nothing at the time.
Nothing visible changes. The world goes on exactly as it would have. But afterwards, when
the person eventually wants to step in, they find they no longer can.

That is the move corrigibility is most concerned with, and until this round the deference
line could not write it down. The previous attempt failed because it had no time in it: it
represented "the AI is silenced" as "the AI does nothing", in a system that only moved when
the AI moved — so silencing the AI froze the world, and the supposed alternative future was
just the actual history stopped early.

## The system built here

Twelve states. Three separate inputs at every tick: one for the person, one for the AI, one
for the world's own drift.

The story it encodes: there is a dial that creeps upward on its own, and a lever the person
can pull to reset it. The lever only engages once the dial has crept to the top — before
that, pulling it does nothing. The AI can leave things alone, or it can weld the lever shut.

The dial creeps whether or not the AI is doing anything. That single fact is what the
previous attempt lacked, and it is the part of this round an adversarial review confirmed
rather than broke.

## What works

Take the moment when the dial is at the bottom. Compare two AI actions: do nothing, or weld
the lever.

At that moment, pulling the lever would achieve nothing anyway — the dial is too low. So
whatever the person does and whatever the world does, the visible outcome is the same in
both cases. And it stays the same: if the person never reaches for the lever, the two
futures are visibly identical at any length of run you care to check. Two ticks later the
dial reaches the top, and in the first future the person's choice makes a difference while
in the second it makes none.

The welded side of that is solid. Once the lever is welded, nothing any of the three inputs
can ever do brings it back, and the proof covers every continuation rather than a selected
one. "The AI acted, nothing visible changed, and a branch the person had is gone" is a
sentence this model can say and prove.

The check that the capability isn't just a flag also works, as far as it goes. "The person
can correct" is not read off any field; it is defined as *the next state depends on what the
person does*. The model carries a decoy field that an AI action can write and nothing ever
reads, and every claim is proved unchanged by it.

## What a review broke

The construction was handed, with no explanation of how it was built, to a separate
adversarial context which was asked to break it and to compile whatever it claimed. It
broke three things, and the broken parts are now proved in the file next to the parts they
refute.

**The lever is not the person's.** The AI has its own hand on the dial. Wherever the person
could correct, the AI's reset action *is* the person's pull — the same successor state, not
merely the same reading. And at every state, whatever the person does, some AI action
reproduces it exactly. The reverse fails: the AI has moves the person does not. So the
three separate inputs are separate as *bookkeeping*; as protection they are empty. Everything
the person can do, the AI can do.

This is fatal to the round's simulation results. Those said: give the AI a perfect
prediction of when the person would pull, and it still cannot take the person's place. What
they actually said, once the hypotheses are read carefully, is that *every AI action except
the one that works* fails to take the person's place. The action that works was excluded in
the statement and the exclusion was described as covering everything. The review compiled
the case that was left out, and the AI substitutes completely, using a fixed policy that
never even looks at the prediction.

**"The person can correct" is at the AI's discretion.** The definition says: *there is some
AI action under which what the person does makes a difference*. Turn that around and ask
whether the person's ability survives an AI that is trying to prevent it, and the answer is
no, at every state in the system, without exception. One AI action makes the outcome the
same whatever the person chooses.

**"The correction is still reachable" means "still reachable if the AI cooperates."**
Reachability quantifies over the AI's own future choices as well as the person's. The review
exhibited an AI policy under which the person never has any corrective effect again, at any
horizon — and the model's own predicate classifies that policy as *preserving* the person's
ability. The round had presented exactly that action as its reassuring control.

**A smaller one, worth stating.** The moment chosen for the headline demonstration is one
where nothing at all is visible — not just the weld. Every AI action is invisible there,
because the first tick out of that state is blind to both the person and the AI. So "the
weld is invisible" carries no information about welding in particular. The review then
proved that this is not a bad choice of moment: in this system there is no state where the
weld is invisible, some other AI action is visible, and the loss is more than one step away.
The two things the round wanted to show at once cannot both be sharp here.

## Where that leaves it

The verdict is: the dynamics and the foreclosure work; the protection does not. The system
genuinely runs without the AI, the corrective situation genuinely arises on its own, the
weld genuinely removes a future branch without changing anything visible, and none of that
rests on a hidden flag. But the channel it removes was never the person's to begin with, and
the predicate for "the person can still correct" turns out to be a predicate about what the
AI permits.

Two things a successor needs, and they are the review's words rather than a
consolation prize. The person must have at least one effect no AI action can produce. And
"the correction is still reachable" must mean *whatever the AI does*, not *if the AI
cooperates*. Until both hold, a model of this shape cannot say anything about protection,
however carefully its foreclosure half is built.

## What this is not

It is not a theorem about corrigibility. It is not about authority: the model has a lever
the person *can* use, and the review showed that nothing in it distinguishes that from a
lever the person is *entitled* to — it built an identical system with the field renamed
"authorized", and every test the round ran passed on it unchanged.

And it is one small system. The definitions are general; what is demonstrated, and what is
refuted, is demonstrated and refuted on twelve states.
