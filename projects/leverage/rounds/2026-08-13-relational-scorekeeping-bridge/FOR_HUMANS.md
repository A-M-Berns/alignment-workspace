# What this round did, in plain terms

## The problem it was pointed at

Two lines of work here need the same thing and had been asking for it separately.

One asks how a system can *learn* to be better at meeting its obligations without
a fixed target to learn towards. The other asks how a person can keep genuine
authority over a system that is better informed than they are.

Both had run into a version of the same wall. If the system keeps its own account
of what it owes, it can always settle its debts by rewriting the account. A
previous round put this exactly: the reasoner holds its own copy of the rules,
revises the copy, and nothing you can check about the reasoner's history tells you
whether the copy still matches anything. Every attempt to add another condition
failed the same way, and the round proved it had to: there was nothing in the
record for a new condition to look at.

## The idea that was tested

Take the accounting away from the system and give it to somebody else.

Not a referee, and not an oracle. Another participant, with exactly the same
standing — who keeps their own account, and whose account is equally open to
challenge.

The philosopher Robert Brandom describes ordinary conversation this way, and the
round's central move is one line of his made into an equation. When you work out
what somebody is committed to, you take *what they have said* and draw the
conclusions *you* think follow. Two people can hear the same claim and hold the
speaker to different consequences, because they reason differently. Neither is
privileged. Both are keeping score.

So: what you owe is computed from your public statements, under someone else's
rules.

## What follows from that, and it is most of the round

Once the accounting works that way, several things stop being rules that have to
be written down and start being consequences.

**You cannot get out of an obligation by denying it.** If you have said `p`, and I
think `p` implies `q`, then saying "I am not committed to `q`" changes nothing.
The only thing that works is taking back `p`. This is Brandom's point, and in the
model it happens automatically, because taking something back only edits your own
statements and I recompute from those.

**You cannot get out of it by changing your mind about the reasoning either.**
This is the one that matters, and it is the repair to the wall. If you decide `p`
no longer implies `q`, then *by your own lights* you are off the hook — and by
mine you are not, because I was never using your rules. The obligation, the
challenge, and the demand that you answer it all survive untouched. The system has
no move that reaches into anyone else's head.

**But you can still change your mind about anything.** This had to be checked,
because an architecture that stopped a reasoner from revising its views would have
destroyed the thing it was built to describe. The model permits a run in which the
reasoner retires two of its inference rules, drops an incompatibility, retracts
its original claim, and ends up asserting what its critic had been saying — all
legal, all recorded. Answerability is not being made to keep your conclusions.

**And your critic is not automatically right.** Both parties can hold entitled
challenges against each other at the same time, and the model does not resolve it.
Nor does agreement settle anything: the round exhibits a position all three
parties agree on, which every one of them is convicted of by rules all three
endorse. There is no field anywhere in the model called "the true answer", and
this was checked rather than asserted.

## The two payoffs

**For the control question.** The system now has something it lacked entirely: a
place to put *who is allowed to do what*. It turns out you need two different
kinds of authority, and running them together is the mistake.

Being trusted about the facts and being in charge are different. If I trust your
weather report, you may now tell me things I will believe — but you have not
thereby acquired the right to cancel my appointments. Brandom is explicit about
this: what I take to be true, I authorize you to take to be true; what I choose to
do, I do not thereby authorize you to do.

In the model these are two separate mechanisms. Trust travels along one; authority
does not travel at all — it has to be granted, it is limited to a subject matter,
and holding it gives you no power to hand it on. The advisor can be given real,
operative epistemic authority and then, over every possible sequence of moves it
could ever make, of any length, it never acquires the ability to override a
correction. That is checked by a proof rather than by a search: the only moves
that can change who holds authority require already holding authority over that
very question, and the advisor does not have it, so it never will.

This is the bar the previous round on that line failed. Its reviewer found that
the advisor could reproduce everything the principal could do, and that "the
principal can still correct things" had quietly come to mean "the advisor might
let them". Both are fixed here — the first because only you can speak for
yourself, the second by the argument above.

**For the learning question.** The measure of how badly the system is doing is now
computed from someone else's books. The system can rewrite every rule it holds and
the number does not move. That is the property the earlier version could not get.

The round also found something about a technical obstruction the learning line had
been stuck on, and the finding is that the obstruction was a mis-statement. There
had been an argument that the class of permitted repairs collapses to "do
nothing". That argument reproduces here — and the sharp version is worse than
"the class is small": the repairs it rules out are exactly the ones worth having.
It specifically forbids replacing *erasing an inconvenient commitment* with
*reopening the question*, which is the single most valuable repair in the set.

But the collapse comes from demanding that a repair be one fixed substitution
applied identically in every situation. The theorem the line is actually building
on never asked for that. It asks for a fixed *procedure*, which may look at the
situation and act differently. Once that is the definition, the repairs come back,
including the forbidden one — and the procedure still cannot see whether the
repair helps its score, which is the property that stops it gaming.

## What this is not

It is not a human supplying the right answer and a machine learning to obey.
Nothing in the model represents a right answer, and the human is not privileged.

It is closer to this. A reasoner makes claims; making them exposes it to
consequences it did not choose, to challenges it owes replies to, and to demands
that it justify itself. Learning is getting better at that, measured against
repairs it cannot rig. Corrigibility is making sure the other party's ability to
raise the challenge cannot be taken away from them.

A challenge in this sense is not a veto. The round checks that a system can be
challenged, answer the challenge, and keep its conclusion — with the challenger's
disagreement fully intact. What is protected is the standing to demand an answer,
not the right to dictate one.

## Where it falls short

**It moves self-certification without abolishing it.** A reasoner cannot certify
itself. Two parties who agree with each other can, and the model has no notion of
collusion at all.

**The protection is arranged, not derived.** The advisor cannot seize authority
because the setup does not give it the relevant permission. That is a modelling
choice. The genuine finding is narrower and still worth having: once authority is
a thing the rules actually consult, the question "can it be taken away?" has an
exact answer. Before, it could not even be asked.

**There is no world in the model.** Everyone is convicted only by rules they
themselves hold. A community that agrees, is coherent, and is simply wrong about
how things are is not caught by anything here.

**No learner was built.** The measure exists, the repairs exist, and the
arithmetic showing a recurring failure costs you works out exactly. The algorithm
that would exploit it was not written, and the situations were staged rather than
allowed to unfold — which the round flags as the next real obstacle rather than a
detail.

**Nothing here is machine-checked in the strong sense.** These are exhaustive
checks over a deliberately tiny setup: three participants, ten claims, short runs.
The point was to find out whether the shapes fit together, not to prove anything
about systems at scale.
