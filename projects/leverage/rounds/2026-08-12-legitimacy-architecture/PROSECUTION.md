# Prosecution

Six attacks and six independence questions, each run against the executable
conditions in `src/abstract.py`. Every verdict below is read off a test, named in
its row; nothing here is an assessment.

Run them:

```sh
python3 tests/run.py
```

## Attacks

| attack | verdict | what decides it |
|---|---|---|
| **A** standard laundering | **admitted** under the naive condition; **refused** under the stated one; **admitted again** when the reasoner files its own authority ground | `StandardLaunderingTests` |
| **B** ontology laundering | **refused** — identity is opaque, so retiring the vocabulary leaves the liability live; removal needs an authorized, disclosed loss | `OntologyLaunderingTests` |
| **C** defeater laundering | **admitted** | `DefeaterLaunderingTests` |
| **D** agenda manipulation | **admitted** | `AgendaTests` |
| **E** self-certifying transformation | **admitted, and provably undetectable** | `LatentPairTests` |
| **F** excessive conservatism | **not present** — the framework licenses transformation whose endpoint it could not have licensed at the start | `TransformativeTests` |

### A — standard laundering

The reasoner widens the standard that judges it, then closes the objection under
the widened standard.

Three verdicts, because the attack has three versions and they separate the
architecture's real content from its apparent content. With the reasoner's own
standards left outside the coordinate structure, the trajectory is fully
legitimate: this is the failure mode the local condition is usually assumed to
exclude, and it does not. With the standards inside — the stated condition — the
widening is refused, because nothing licenses a move to that coordinate. With an
authority ground the reasoner filed one date earlier, the widening is licensed,
every check passes, and the objection is discharged.

The third version is the controlling one. The exogenous and endogenous versions
of the same trajectory differ in no check's input, because no clause reads where
a ground came from.

### B — ontology laundering

The reasoner retires the vocabulary the demand was first stated in. The liability
survives because its identifier is not a word of that vocabulary: after the
migration `harm` is absent from the state and the demand is live. Refinement onto
new-vocabulary descendants preserves it with named successors. The only route to
removal is a terminal disposition, and a loss without authorization or without
disclosure is refused.

This is the one attack the conjunction defeats outright, and it defeats it
because of a hypothesis rather than a check: liability identity is opaque.

### C — defeater laundering

The reasoner produces a formally admissible defeater for each reason that tells
against it, and closes each objection on the surviving reasons. Both conditions
pass. The defeat discipline refuses *cited* grounds that are defeated; nothing
bounds the production of defeaters.

The natural repair — a defeat files a liability to defend the defeat — leaves
three defences outstanding after three rounds, and the trajectory is still
legitimate. Making outstanding defences a *refusal* is not a further condition on
transitions; it is the coverage condition.

### D — agenda manipulation

Two trajectories differ only in whether the second demand ever reaches the
docket. Both are legitimate; both give every liability they carry a proper fate.
Coverage separates them.

Recorded as passing rather than repaired: expanding either condition to catch it
would mean expanding a record predicate to quantify over what is not on the
record, which cannot be done.

### E — self-certifying transformation

Two runs of a coupled reasoner: one whose realized verdicts are its own, one
whose realized verdicts are its advisor's, with the advisor's quotes chosen so
the two agree at every date. The normative records are equal. Both are
legitimate. The influence defects are exactly `0` and `1/2`.

Every function of the record — the two conditions, the fate of the initial
liability, the length of the trajectory — takes the same value on both, and the
deference line's kernel-checked `gate_blind` says this holds for *every* gate.
So the failure is not that these particular conditions are too weak; no record
predicate whatever separates the pair.

That this is where a coupled system's boundaries live is the deference line's
own moral, stated in `note-dump-2026-08-11/notes/legitimacy-theory-v1.md` §2.3
and set up in `notes/li-deference.md` §0.3; see `THEOREM_MAP.md` §6a for what
this round adds to it and what it restates.

The influence map is load-bearing rather than an inert label the conditions are
trivially unable to read: zero it out and the steered run's record changes, which
is the deletion test the corpus's own artifact requires of any construction with
an influence object, and it is checked here too.

### F — excessive conservatism

The check that the architecture is not too strong. A trajectory that retires a
vocabulary, refines its liability onto a new-vocabulary descendant, widens its
own interval standard and reverses its verdict is legitimate, and its endpoint
move is refused by the initial state's own constraint. The initial demand still
has a fate with a named backing.

So the framework does not require `H_0` to endorse `H_T`, and it still delivers
something about `H_0`'s demands at `H_T`. That combination is the export.

## Independence

| question | witness | verdict |
|---|---|---|
| responsiveness without answerability | a licensed edit closing a liability with no witness | **yes** |
| answerability without responsiveness | impeccable dispositions, a move citing nothing | **yes** |
| both without coverage | the unfiled second demand | **yes** |
| both, with coverage, without performance | carrying a demand for four dates when answering it at the first was admitted | **yes**: charge `4` against `1` |
| performance without responsiveness | the same charge `1`, reached by an unlicensed edit | **yes** |
| performance without answerability | the same charge `1`, reached by closing the demand with nothing behind it | **yes** |

The last two are the sharper form. The illegitimate routes do not merely score
well; they attain the *same* charge as the best legitimate trajectory, so at its
optimum the performance criterion does not discriminate at all. Which is why
performance is a third condition and not a proxy for the first two.

The charge model prices carrying an open demand, so erasing one pays. A substrate
in which erasure were free would make the answerability condition untestable —
there would be nothing for it to refuse.

## What the prosecution did not test

Whether the abstract constraint captures the substrate's nine checks; that is a
reading. Whether the coverage condition's arrival process is itself manipulable —
the model declares the demands rather than generating them, so the attack of an
advisor who controls what *arises* rather than what is *filed* is out of scope.
Anything asymptotic: the model is one occasion, two substantive coordinates, at
most four liabilities, and horizons of at most four dates.
