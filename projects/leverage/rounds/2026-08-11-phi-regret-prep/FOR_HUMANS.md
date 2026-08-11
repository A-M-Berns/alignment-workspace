# In plain language

## The question behind the machinery

Suppose a system has to make judgment calls, and suppose we want it to get better
at them over time. The usual way to say "better" is to compare it against a
target: here is the right answer, how close did you come. That move is not
available here, because the whole point of the programme is that there is no
fixed external standard of normative correctness to compare against.

So the comparison has to be internal. Not *you should have said X, because X is
right*, but *you should have said X, because your own record already contained
the reasons for X, and you had them at the time.* A system that repeatedly fails
to do the thing its own commitments licensed is failing in a way that can be
pointed at without anyone claiming to know the truth.

Making that precise is what this round did. It did not show that any system
achieves it.

## What "lawful edit" means

Take a moment in the system's history where it declined to rule on a question and
let a clock run up charges. Ask: could it have ruled, given what was on its record
at that moment?

That is a question with a checkable answer, and the check has nine parts. The
grounds it would have relied on must have been on the record *then* — not filed
later. They must actually bear on the thing being changed. They must not have
been undercut. They must license the specific change and not just some change in
that direction. The edit must not quietly delete an obligation to make the books
look better. And — the part everything else rests on — the check must not be
allowed to notice that the edit would have been cheaper.

That last one is enforced by construction rather than by care. The checking code
runs behind a reader that has a declared list of things it is allowed to look at,
and the cost table is not on the list. Asking for it throws an error. There is a
test that writes a rule which tries to peek at costs, and asserts that the whole
run crashes rather than quietly producing an answer. That is the difference
between a principle and a mechanism.

## What was built

A small finite world: questions arriving over time, a record of what was known
when, three ways to respond, and an exact accounting of what each response costs
in the charges the existing theory already defines. Then thirteen experiments,
each a specific thing that had to be true or the whole framing would be wrong.

Five of them are about refusing edits that would have paid:

- an edit that would save money but that the record doesn't support — refused;
- an edit justified by something only established later — refused twice over,
  once because the later fact is literally invisible to a check standing at the
  earlier moment, and once because "we later decided this was right" is not a
  reason it was right;
- an edit that claims a delay of four days when the recorded obstacle accounts
  for two — left *unresolved* rather than refused, because whether a reason for
  going in a direction ever licenses going all the way is a real open question
  and pretending to have answered it would have been the easy lie;
- the same edit lawful before an objection lands against its grounds and unlawful
  after;
- an edit that lowers the bill by striking the obligation off the books —
  refused, and the test checks that striking it really would have zeroed the
  bill, because a refusal of something harmless proves nothing.

Three are about edits that do count, and how much they are worth. The important
one is a system that keeps declining a question its record clearly answers, over
and over. The lawful repair saves the same amount every time, so the shortfall
grows in a straight line with the length of the run — two-thirds of a unit per
question, at every horizon tested. That is the shape a learning result would have
to rule out, and having it as a running example rather than a description is most
of what this round is for.

## The finding that was not expected

The interesting question was how far one small change can reach. If changing one
decision can change everything that follows, then comparing runs is hopeless.

The expectation going in was that keeping accounts separate — one budget per
stream, so trouble in one does not spill into another — would be enough. It is
not, and the reason is worth stating.

Money is not the mechanism. Running out of budget is: a stream that exhausts its
reserve loses the ability to rule on things properly, so every later question in
it gets declined and charged. So one edit at the very start can be the difference
between a stream that stays solvent and one that does not, and that difference
plays out over every question the stream ever sees. Separate accounts do not help
if the account is big.

Same history, four configurations, exact numbers: with the edited decision alone
in its own account, the change is 2 whatever the horizon. With everything in one
account — separated from the rest of the world, but internally shared — the
change is 24 at horizon 12 and 48 at horizon 24. Pooled, the same. Turn off the
budget-exhaustion rule and it drops back to 2.

So the condition that makes the comparison work is not separation. It is that
nothing about one decision can change whether a later decision is *possible*. The
next round gets to make that assumption explicitly, and gets told in writing that
it is an assumption, and that another proved result in the same body of work
says the rule it switches off is doing real work elsewhere.

## What this is not

It is not a learning result. Nothing here shows any system achieves low regret;
the target is written down, the environment for testing it is built, the numbers
a failure would produce are exhibited, and that is all.

It is not a theory of reasons. Three of the nine checks bottom out in relations
this round declines to settle, and they are named functions in one place, so a
later commitment shows up as a change to code rather than as a change of tone in
a document.

And it is not coverage. The system is only measured against repairs someone has
already written down. A failure nobody thought to represent generates no pressure
at all, however costly and however obviously repairable. That gap is the honest
distance between "does not persist in a mistake it can see" and "does not persist
in a mistake", and closing it is somebody else's round.
