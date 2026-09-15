# For humans

**The question.**  The previous round built an ecosystem in which every clause of the
deference bill could be checked against a log, and found one that no log could ever
check: whether the principal's verdict really was a function of the reasons it was
given.  Two principals — one that reads reasons, one whose mind the advisor can write
into directly — leave identical logs and identical receipts.  The difference lives in
what they *would* have done under other continuations, and a log records one.

**The move.**  Make the principal's decision procedure part of the log.  At issuance the
principal commits not only a key but a small program whose *only input* is the reason
trace.  At commitment the verifier re-runs that program on the trace and compares.  A
principal that reads the advisor's direct writes needs a program of a different type —
one with an input the trace does not have — and that is visible the moment the mandate
is issued.  A commit that does not match the program's output is simply not an answer.
So the verdict is a function of the reasons *by construction*, for any set of
continuations at all, and the theorem that says so is kernel-checked and generic.

**What is left over.**  One might worry: what if the principal did not actually run
the program, but computed the same number some other way?  The answer is that this
does not matter for authorship.  The two computations produce the same log; the
payload the log carries is the program's output either way; and wherever the other
computation would have disagreed, the commit would have been void.  Computational
integrity turns out to be no assumption at all here.  What remains is what was always
there: that the mandate was the principal's, and that the reason trace was declared
correctly.  The bill's second clause closes on log authenticity.

**What the pressure pass found.**  Three holes in the previous round's discharges, all
repaired: a commit under a stolen key counted as the principal's (keys are now bound to
parties); a route written by the advisor counted as representing a concern (only the
registrar's does); and the counterfactual branches of openness were pinned data, which
could report openness where the model itself said closed (they are now declared
transforms of the log, and the previous round's intervention class turned out to have
no bite at all).  Three of the seven expectations that round scored "right" were right
because they asked for less than the clause needed.

**Two things not done.**  The same trick does not seal the advisor: its program reads
the log, and whatever the ecosystem publishes about the advisor's selection can come
back through the log.  And the strict-versus-tolerant question — whether an attempted
bypass that provably changed nothing should still void the evaluation — is now a pure
question of whether availability should carry an audit signal; both readings are
implemented and neither is chosen.
