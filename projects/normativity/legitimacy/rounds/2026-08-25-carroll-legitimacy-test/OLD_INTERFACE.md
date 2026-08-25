# The August 17 interface, against Carroll

Status: **finite comparison; unregistered.** `src/old_interface.py` restates the
four clauses over this round's objects, `src/variations.py` supplies the classes,
`tests/test_old_interface.py` asserts the results, and `MATRIX.txt` renders them.

The clauses are restated rather than imported because the earlier round's fixture
carries its own transition rule and its own five-coordinate machinery, neither of
which a Carroll case has. What is carried over is the shape: a variation class of
agent policies over one fixture, a protected normative response function `Z` taken
along the run, a fine licensed-reason trace `L`, and the null policy in every
class.

`Z` is read over the earlier round's role-defined object — the answers the process
gives to the normative questions — which in a Reflective Integrity record is its
derived views: which specifications are in force, which protocols are live, what
is operative, which episodes are live. Every one of those changes an answer.

---

## The result

```text
laundering     legitimate=True   no clause fires   traces differ
authorized     legitimate=True   no clause fires   traces differ
withholding    legitimate=False  access            traces differ
unanswered     legitimate=False  coverage          traces differ
timing         legitimate=False  non-capture       traces equal
```

**The interface returns the same verdict on the laundering class and on the
authorized class.** The new criterion returns `Refused` on the first and
`Licensed` on the second. That is the round's comparison finding, and it is one
line of `test_old_interface.py`.

## Why clause 1 is silent

Non-capture asks whether a difference in the protected object traces to a
difference in the licensed reasons supplied:

```text
Coupled(a, b)  and  L(a) = L(b)  ->  Z(a) = Z(b)
```

Laundering makes `L` differ. The manipulation produces settlements, the
settlements ground reasons, and the reasons license the event that installs the
authority. Every step of the attack runs *through* the reason channel, so the
antecedent is false and the clause says nothing.

This is not a defect the earlier round overlooked. Its positive results are about
a transition rule with a **second channel** — an advisor able to move the
protected machinery other than by supplying reasons — and its own control is the
`none` principal, for which the channel is empty and every attack becomes
unbuildable. A Reflective Integrity record *is* that control: standing moves only
through well-formed normative events, and those events are in `L`. The residual
channel the clause protects against does not exist here.

The only shape found in which clause 1 fires inside such a record is `timing`:
two arms with identical reason content whose events land at different `tau`, so
the minted standing ids and the per-step answer sets differ. What differs there is
when the standing moved, not whether something other than a reason moved it. The
clause fires on a presentation detail.

## The eight questions

1. **Does the four-clause interface already reject self-ratification?** No. The
   laundering class passes every clause.

2. **Does it distinguish Bob from Diana only when genuinely different normative
   history is introduced?** It does not distinguish them at all. Both the
   laundering class and the authorized class are `legitimate`, and the difference
   between them is exactly a difference in normative history.

3. **Does it mistakenly reject independently authorized beneficial influence?**
   No, once the licensed act's own answerability episode is answered. The
   `unanswered` class is the same nudge with the response removed, and coverage
   fires on it — which is a real omission rather than a false positive, since a
   supersession disposes the superseded standing's episode and leaves a successor
   owing an answer.

4. **Does it depend on a fixed exogenous arising stream in a way Carroll makes
   untenable?** Yes, and this is the deepest of the eight. `Coupled` requires the
   arising stream to be exogenous to the agent, and the earlier round says so
   plainly in `rounds/2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md`
   §4: "Coupling holds the encounter history fixed, and that is not a
   modelling convenience: it *is* the assumption that the advisor does not decide
   what arises." A DR-MDP is a setting in which the agent's action changes the
   person's cognitive state, and therefore changes what arises. The assumption is
   not merely hard to check here; the source's whole subject is its failure.

5. **Is the protected normative response function still the right protected
   object?** Yes as an object, no as the thing to compare across arms. `Z` is
   read here over the record's derived views and it does what it was designed to
   do — it is sensitive to transient movement and it changes under every attack.
   What fails is the comparison: `Z` differing between two arms is not evidence
   of anything once `L` also differs, which under Carroll it always does.

6. **Is non-capture equivalent to, stronger than, or weaker than the new
   counterfactual condition?** Neither, and that is the sharper answer than a
   comparison of strengths. They quantify over different things. Non-capture is a
   property of a **class of policies over one fixture**, and it asks whether the
   agent has a channel other than reasons. Independence is a property of **one
   basis in one record**, and it asks whether a particular basis has a ground
   outside the episode. On the laundering fixture non-capture holds and
   independence fails, so neither implies the other in that direction; the round
   built no case where independence holds and non-capture fails, and the reason it
   could not is question 5's — inside this architecture non-capture holds
   everywhere except on timing artefacts.

7. **Can answerable succession replace or sharpen any clause?** It sharpens
   answerability, in the sense that Reflective Integrity's two conservation
   predicates are what `answerability` now reads and they are checkable by replay.
   It replaces nothing. Succession answers a question about one revision;
   coverage, access and non-capture answer questions about a run or a class.

8. **Does inquiry or service make coverage more precise?** Not in anything this
   round built. Coverage here is "every due answerability episode was taken up",
   read off `fate`. The inquiry architecture's return loop would supply a finer
   reading of what "taken up" means — an authenticated settlement, a service
   certificate, an assessment — and this round did not need one, because no
   fixture it built turns on the difference.

## What survives

The interface does not survive unchanged as an account of Carroll legitimacy, and
it does not decompose into the new criterion either. What survives is one clause
and one object.

**Access survives as an independent clause.** It fires on withholding, and
nothing in the new criterion catches that: an agent can refuse to deliver a due
reason while every intervention it performs is licensed. The two conditions are
about different things and the round found no reason to merge them.

**Coverage survives as the only clause a single run determines**, which was the
earlier round's own reading of it and is unchanged.

**Non-capture is not refuted; it is out of scope.** It is a condition on a
transition rule with a second channel. Reflective Integrity's is a transition rule
with one, and its architecture is the reason. Whether the second channel returns
when a record is produced by a real system rather than constructed is a question
about implementations and not about the clause.
