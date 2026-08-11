# For humans

A standalone account. No symbols, no identifiers, no prior reading assumed.

## The problem

A system that reasons about the world has to get information from the world
somehow. Everything else it believes can be argued with: you can challenge its
evidence, its inferences, its standards, its decisions. But at some point
something has to come in from outside and just *be the case* — the thermometer
read fourteen degrees, the theorem was proved. That input cannot be argued with,
because there is nobody to argue with. The world does not answer objections.

This creates a hole in an otherwise accountable system. Every other thing the
system says is staked, challengeable, and revisable. This one kind of thing
enters exempt. If the exempt channel is wrong, or manipulable, or slow, the
accountability of everything downstream is worth less than it looks.

The work here is about that hole: making it as small as possible, saying exactly
what is being assumed about what is left, and proving what follows.

## The design principle

**Minimize the unanswerable.** Whatever the exempt voice does not strictly need
to say gets said in the answerable layer instead, where the system's ordinary
machinery applies.

The main trick: what settles is never "it is fourteen degrees". What settles is
"*this thermometer, run at this time, returned fourteen*". The step from the
reading to the temperature is a *bridge* — endorsed, defeasible, and fully
challengeable. So the unanswerable part is as thin as it can be, and everything
interesting about reliability, calibration, and interpretation stays arguable.

A nice consequence: two thermometers that disagree are not a crisis. They are two
different procedures, so two different facts about what was returned, and both
are true. Their disagreement lives entirely in the arguable layer, where the two
bridges pull against each other and the system's ordinary conflict machinery
handles it. Nothing in the settled record ever contradicts itself.

## The interface

Rather than build one world-channel and prove things about it, the work
specifies what *any* world-channel has to provide, and proves everything over
that specification. A channel supplies three things: **reports** — what it
writes down; **timing** — when; and **enforcement** — the weight standing behind
what it writes.

The specification is about eighteen clauses. The important structural point is
that each clause is one of two kinds. Most are **checkable**: you can run a
program over the record and it will tell you whether the clause holds, and if
not, why not. A few are **declared**: nobody can check them from a finite
record, so they are written down as explicit assumptions carrying their own
text. When the system reports that a channel meets the specification, it also
prints the list of things nobody checked. That printed list is the honesty
mechanism, and it is the part of this design I would defend hardest.

## Three things that went differently than expected

**A clause everyone thought was assumed turned out to be computable.** One clause
asks the channel to certify that it holds its positions with some minimum
conviction. This had been carried as a single open assumption. Writing the
condition out geometrically showed it is *linear* in one variable, which means
"does this hold right now?" is a small computation with an exact answer. What
stays open is only whether it keeps holding as more gets settled. One open
assumption became a program plus a strictly smaller assumption.

**A clause everyone thought was fine turned out to be unsatisfiable.** The same
condition had been stated against the whole space of possible belief states. But
once anything is settled, the space of live belief states is thinner — settling a
fact rules out a whole slab of them. The condition asks a full-thickness object
to fit inside a thinner one, which cannot happen. Not "hard": impossible, for
every setting of the parameter, from the first settled fact onward. The fix is to
read the condition against the *remaining* space, which is what a reader would
have meant anyway. The failing version is kept in the monograph, displayed
failing, because that is the clearest possible statement of why the current
version is written as it is.

**A measurement was being taken against the wrong thing.** One clause limits how
incoherent a channel's prices may be. It turns out to matter enormously whether
you measure that against *logic plus what has been settled* or against *logic
plus what has been settled plus what the system itself has committed to*. Measure
it the second way and a system whose own commitments are contradictory gets
recorded as a channel failure — which pauses the clocks, forgives the system, and
charges nobody. Measure it the first way and the same situation is recorded as
the system's own problem, which is what it is. Same arithmetic, opposite
verdicts about who pays.

## What is actually proved

The main result takes the earlier work's guarantee — a limit on how much can be
extracted from a system whose commitments move around — and restates it over
*any* channel meeting the specification, rather than over one hand-built
example. It is honest about being a substitution: no new mathematics, and the
statement says so. What it buys is that the assumption is now something you
evaluate rather than something you hope.

There is a discipline in how it is stated that is worth noticing. The
antecedent has thirteen separate assumptions. If any one is missing, the result
reports **no bound at all** and names the missing assumption. It never quietly
reports a weaker number. Every one of the thirteen is checked to be genuinely
load-bearing by removing them one at a time.

## What is not proved

The specification is a definition, and a definition cannot be true.

There is exactly one piece of evidence in this package about whether any
*serious* system meets the specification, and it is the weakest kind: somebody
read that system's published description clause by clause and wrote down what
matched. That is a **reading audit**. It is labelled as such everywhere it
appears, including in the row of the ledger that records it. It is kept because
it is the only such evidence that exists, not because it is strong.

Two things are assumed outright and named: that the channel's reports depend
only on the procedure and the world, and not secretly on what the system
believes or who paid; and that the proof checker is sound. The work argues these
cannot be checked from inside the record. It does not prove them, and it does
not pretend to.

And two mathematical questions are open, one of them in both directions — nobody
knows whether the thing exists, and nobody knows whether it is impossible.

## The one-line version

The world cannot be held accountable, so the work makes the unaccountable part
as small and as explicitly labelled as possible, proves what follows from it, and
prints the list of everything it had to take on faith.
