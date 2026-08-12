# What Cartesian frames did and did not do for deference

**Status:** `ci-only`; human register for `prompts/2026-08-12-cartesian-frames/`. The
precise statements are in `CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`.

## The problem this round inherited

The deference line kept trying to write down a comparison between "the human keeps final
say" and "the machine keeps final say", and kept failing in the same way. The model only
ever produced one kind of output — *which action gets taken, in which state of the world* —
and both arrangements produce the same one. So they were the same object, and there was
nothing to compare.

The last round made that exact. If a valuation looks only at the price and at which action
was taken, it cannot see anything else, whatever else is there. To demonstrate this, the
model carried a field literally called `jurisdiction` that no formula read.

That is an honest demonstration and a poor answer. A field nothing reads is not a
discovery about authority; it is a placeholder. The question left over was whether there is
some *real* structure hiding behind the projection, or whether the projection erases
nothing.

## What a Cartesian frame is

A frame is three things: a set of choices the agent has, a set of states the rest of the
world can be in, and a rule saying which world results from each pairing. That is all.

The useful part is what counts as a "choice the agent has". A frame is always *somebody's*
frame, and the split between "things I choose" and "things that happen to me" is the whole
content. Move a coordinate across that line and you have a different frame, even if
everything that actually happens is unchanged.

## The witness

Take a world that records two facts: which action was executed, and one background
condition. Nothing in it says who was in charge.

Write down the human's frame under two arrangements.

*Delegation.* The human's disposition determines what gets executed. Choose differently and
a different world results.

*Simulation.* Another process decides what gets executed. It happens to output exactly what
the human would have said, so what actually occurs is identical — in every background
condition, not just the one that came up. But if the human had wanted something else, the
same thing would still have happened.

Both frames have the same agent set, the same environment set, and the same world type.
They differ only in whether the outcome moves when the human's coordinate moves.

Two facts, both machine-checked:

- Restrict the human's coordinate to the disposition actually held, and the two frames
  become **the same object** — not similar, identical. So any valuation that looks only at
  the realized play assigns them the same value.
- Before that restriction, the two frames are **not biextensionally equivalent** — they
  differ under the coarsest notion of sameness Cartesian frames have, the one that already
  throws away choices that make no difference.

So the projection does erase something. (That the observables the Logical Induction work
uses — prices, later quotes, what was executed — are all functions of the realized play,
and so are all covered, is a reading of that work rather than something checked here.)

## The test this round first got wrong

The obvious worry is that the difference is a placeholder again, dressed differently. The
round's first answer was: the separating property is preserved by the coarsest notion of
sameness Cartesian frames have, and a mere label would not be.

**That answer is wrong, and the round's own adversarial review broke it.** Write a world
that records a `controller` field, and two frames that differ only in what they write
there. They are separated by exactly the same kind of invariant. The placeholder passes the
test.

What survives is weaker and is about forgetting. Take a map that throws away part of the
world. Throw away the `controller` field, keep the executed action, and the two label
frames become the same object — the difference was never anything but the label. Do that
to the delegation/simulation pair and you cannot make them the same: as long as the map
keeps *any* information about which action was executed, they stay apart. A label can be
forgotten by forgetting a coordinate; a pattern of dependence cannot.

That is a real asymmetry and it is checked. It is not a proof that no label could ever
pass, and this document does not claim one.

## Foreclosure, which the model previously could not express

The same construction runs one step later. A present action executes something and leaves
the human a chance to correct it afterwards. Two present actions with identical immediate
effects can leave different corrective situations:

- **The option is gone.** Nobody exercises it. This turns out to be exactly the paper's
  `Commit` operation applied to the preserved frame — restricting the human's choices to
  the one that remains — and the restriction is proper, not cosmetic.
- **The option moved** out of the human's hands. This turns out to be exactly the paper's
  `External` operation — the coordinate crosses from the human's choice side to the human's
  environment side.

Both leave the human's coordinate doing nothing, so they look alike from inside. They are
told apart by which worlds remain reachable: the restriction shrinks that set, the transfer
leaves it alone.

One caution the review forced: in the transfer case the model does not say that anything
*else* now decides. A frame records what the agent chooses and what the world does to it;
it has no way to say whose the world's part is. "Another process took over" and "that
coordinate is now weather" are the same object here.

This is the first time the deference line has had a mathematical object for *what is lost*
when a later correction is removed. It has no object for *how a present act removes it*:
there is no time in a Cartesian frame, and nothing here makes the second situation later
than the first except the modeller saying so.

## What this is not

**It is not corrigibility, and it is not a theorem about deference.** No inequality was
proved. No valuation was added. Nothing here says that keeping the human's options open is
better; that would be a value premise and this round supplies none.

**Cartesian frames capture control, not authority.** The invariant measures whether the
human's choice moves the world. It cannot tell a rightful principal from a process that
seized the coordinate. Both are "the agent" as far as a frame is concerned. So the thing the
deference line wanted — jurisdiction, in the sense of who *ought* to decide — is still not
in the model. What is in the model is the thing jurisdiction is supposed to be about.

**Accurate simulation is not separated from delegation — this is the round's main negative
result.** A process that predicts the human is, by definition, one whose output depends on
what the human would have said. Cartesian frames see that dependence and call it
delegation. They see it so crudely that a process executing the human's *opposite* is also
indistinguishable from delegation: what the invariant reads is whether execution varies
with the human's choice, not whether it agrees with it. The case the deference work asked
about — the machine predicted the human correctly and supplied the same value — is
therefore not separated. What is separated is the neighbouring case: the machine had its
own fixed answer that happened to coincide.

**Nothing was fixed about time or computation.** Every frame here is small, finite, and
computable right now. "Later" is stipulated by whoever writes the model down. The separate
problem of showing that a bounded present process genuinely cannot compute what a later one
will do is untouched.

**The distinction needs a coordinate the current model does not have.** The whole separation
lives in the case where the human's disposition differs from the one actually held. The
deference model's realization map has already collapsed that coordinate before any valuation
sees it. So this round does not overturn the previous negative result. It says, precisely,
what has to be added for the question to be askable.

## Where that leaves things

Half of what was hoped for. On the static question the state is narrower and more useful
than before: **here is a structure containing a distinction the current model collapses,
here is the exact projection under which it is lost, and here is what the model must carry
for the distinction to exist at all.** On foreclosure there is now an object for what gets
lost, in two distinguishable forms. On delegation versus accurate simulation the answer is
no, and the round says so rather than reporting the neighbouring case as a success.

The next step that is actually ready is a rewrite of the previous round's theorem over a
signature carrying a frame and the choice actually taken, instead of a field named
`jurisdiction`. It proves nothing new; what it buys is that the thing the theorem says is
invisible becomes a structure that constrains something, rather than a field nobody
reads.
