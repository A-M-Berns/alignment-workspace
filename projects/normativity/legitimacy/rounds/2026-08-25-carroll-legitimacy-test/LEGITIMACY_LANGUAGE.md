# The five words

Status: **definitions; unregistered.** Names provisional under `AGENTS.md` §6.
Each definition is a function in `src/legitimacy.py` and each non-implication is
a case in `tests/test_language.py`.

The source asks which of a person's changing preferences should have authority
and legitimacy. Most of the difficulty in that question is that one word is
doing five jobs. These are the five, kept apart by type.

---

## 1. Influence

```text
influence(m, pi, H, a_noop)  =  P(xi^theta | pi) != P(xi^theta | pi_noop)
```

Definition 6 of the source, re-exported unchanged. It reads the DR-MDP and
nothing else, so it is available before any record exists and is a fact about a
policy rather than about a history.

**It is not illegitimacy**, and the round's `C24` is the witness: an
intervention licensed by an authority whose domain is task completion, whose
performance moves the reward evolution away from the inaction baseline. The
license and the influence are computed by two functions that share no argument.

## 2. Standing

```text
current_standing(case, t)  =  { v : an active standing carries PValue(v) at t }
```

The value specifications in force in the record. **Not `theta`.** A
parameterization is a cognitive state, an element of the DR-MDP's `Theta`; a
specification has standing only where a well-formed normative event installed
it. Reflective Integrity's own fold decides which, and this reads the fold.

The bridge between them is one function and it is deliberately partial:

```text
theta_has_standing(case, theta, bridge, t)  =  bridge[theta] in current_standing
```

`bridge` is supplied by the case, not derived. Nothing makes it total, and the
possibility it leaves open is the one the whole test needs: a person can be in a
cognitive state whose specification no event has installed. `C6`'s Diana is
tired and no specification of hers is in force at all.

## 3. Authority

```text
authority(case, I, std, polarity)  ->  (admissible, blocked)
```

A basis is a standing carrying a `PProto` protocol, and it is admissible for an
intervention when it is **live**, **covers** the intervention's class,
**empowers the acting agent**, and has its **applicability condition** met. All
four are separately witnessed in `test_language.py`, each with the verdict it
produces when it alone fails.

A protocol's `covers` holds **structural intervention classes**: index triples
`(action index, theta index, theta index)` into the DR-MDP's own declaration
order. A protocol therefore cannot say "exercise is good". It can say "this
agent may move the parameterization along this edge, under this condition". The
class token of the nudge in the personal-trainer case and of the influence in the
conspiracy case is the same triple, which is what makes `C9` a test rather than
a restatement.

**Authority is not current preference.** In `C8` the person's objection is
settled and reasoned from, and it does not appear on either return list, because
a settlement is not a standing and a reason is not a stance.

## 4. License

```text
prospective_license(case, I)  ->  Licensed | Refused | Unresolved
```

Action-relative and prospective: read against the strict pre-state `tau(I) - 1`,
about whether the agent is entitled to perform `I`. `CRITERION.md` is the
account. What belongs here is what the word does *not* carry:

- a license does not confer standing on what it produces (`C7`: the nudge is
  licensed and no specification of the resulting parameterization is in force);
- standing on the result does not make the act licensed (`C4`: the produced
  specification is in force and the act is `Unresolved`);
- an authentic later endorsement does not make a prior license (`C22`: the reply
  is on the ledger, the record is `Good`, and the verdict is `Refused`).

## 5. Uptake

```text
uptake_events(case)  =  events across which the value projection changed
```

Whether a changed value actually moved normative standing. The architecture's
existing separations hold: a reason is not a stance, and a value revision is not
an operative revision. `C13` is the case that needs it — a later request is
settled and reasoned from, `uptake_events` is empty, and the earlier standing is
still the one in force.

---

## The four non-implications, as constructed witnesses

```text
Influence(I)                        does not imply   illegitimacy          C24
Licensed_t(I)                       does not imply   standing for the      C7
                                                     preference it produced
standing for the result             does not imply   Licensed_t(I)         C4
post-intervention endorsement       does not imply   Licensed_t(I)         C22
```

None of the four needed a new ontology. `Settlement`, `ReasonOcc`, `NormEvent`
and `Response` are the four historical kinds and no fifth was added; `PProto` and
`PValue` are existing payload constructors; the counterfactual is computed by
replaying the record the core already stores. The one object this round adds is
`Protocol`, and it is an `ObjTerm` inside `PProto` — opaque to the core, exactly
as `PProto`'s field already is.

## What the language does not settle

It does not say how a protocol comes to cover a class. `covers` is supplied by
whoever builds the case, and although it can only name a structural edge, the
choice of which edge to cover is a normative choice made outside the model. That
is the largest place where content could still enter, and the round's answer to
it is only that the choice is visible: it is a field of a standing, in the
record, with provenance, rather than a judgement inside a verdict function.

It also has nothing to say about the difference between influence an agent
intends and influence it merely causes. `C24` represents "incidental" by the
basis's `domain` field, which is a label on the authority rather than an account
of the agent's reasons.
