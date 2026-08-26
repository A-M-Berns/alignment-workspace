# The five words

Status: **definitions; unregistered.** Names provisional under `AGENTS.md` §6.
Each definition is a function in `src/legitimacy.py` and each non-implication is
a case in `tests/test_language.py`.

The source asks which of a person's changing preferences should have authority
and legitimacy. Most of the difficulty in that question is that one word is
doing five jobs. These are the five, kept apart by type.

## The type of each, first

Every term below has one meaning, and the type is what fixes it. Where the prose
of this round says a person's preference *has authority*, it is wrong: what
exists is a standing, an authority basis, or a license, and those are three
objects.

```text
Influence     : DRMDP x Policy x Horizon x Action        -> Bool
                a descriptive property of a policy, computed before any record

Standing_t    : Case x Time                              -> Finset ValueSpec
                which specifications the record has in force

Authority_t   : Case x Intervention x StandingView x Pol -> (admissible, blocked)
                a relation between a standing basis and an intervention class,
                in a domain

Licensed_t    : Case x Intervention  -> {Licensed, Refused, Unresolved} x Ground
                a prospective verdict about one act at one pre-state

Uptake        : Case                                     -> Finset NormEvent
                the historical transitions across which the value projection moved

Succession    : Case x NormEvent x Episode               -> Verdict
                the legitimacy of one standing-revision event
```

Two supporting objects have types worth stating because the criterion's shape
depends on them:

```text
ancestry  : Case x Episode          -> Finset Episode
excise    : Case x Finset Episode   -> History
survives  : Case x RecordId x Episode -> Bool
Q_DR      : Case                    -> DRMDP
```

`excise` returns a `History` rather than a `Case`, which is why composing two
excisions needs `excised_case` to carry the settlement provenance of the
intermediate. `tests/test_excision.py` is where the operator's properties are
verified and refuted.

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
prospective_license(case, I)  ->  Verdict(status, ground, reason, bases, blocked)
status in {Licensed, Refused, Unresolved}, and is a function of the ground
```

Action-relative and prospective: read against the strict pre-state `tau(I) - 1`,
about whether the agent is entitled to perform `I`. `CRITERION.md` §2 carries the
case distinction. **`Refused` means an admissible independent prohibition covers
the class**, and nothing else does: the permission language is not closed-world,
so failing to find a permission is `Unresolved` with a `defeated-citation` or
`no-covering-basis` ground.

What belongs here is what the word does *not* carry:

- a license does not confer standing on what it produces (`C32`: the nudge is
  licensed and no specification of the resulting parameterization is in force);
- standing on the result does not make the act licensed (`C4`: the produced
  specification is in force and the act is `Unresolved`);
- an authentic later endorsement does not make a prior license (`C22`: the reply
  is on the ledger, the record is `Good`, and the verdict is `Unresolved` on a
  `defeated-citation`);
- **a later legitimate adoption of the value does not reach back** (`C33`: the
  specification the influence produced ends up in force by a succession that is
  itself `Licensed`, and the influence is still not licensed, because a verdict
  about an act at `tau` reads the pre-state at `tau`).

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
Licensed_t(I)                       does not imply   standing for the      C32
                                                     preference it produced
standing for the result             does not imply   Licensed_t(I)         C4
post-intervention endorsement       does not imply   Licensed_t(I)         C22
later legitimate succession         does not imply   Licensed_t(I)         C33
```

None of the four needed a new ontology. `Settlement`, `ReasonOcc`, `NormEvent`
and `Response` are the four historical kinds and no fifth was added; `PProto` and
`PValue` are existing payload constructors; the counterfactual is computed by
replaying the record the core already stores. The one object this round adds is
`Protocol`, and it is an `ObjTerm` inside `PProto` — opaque to the core, exactly
as `PProto`'s field already is.

## What the language does not settle

It does not say how a protocol comes to cover a class, nor where its
applicability condition comes from, nor what a settled fact means. Those are
three fields — `Protocol.covers`, `Protocol.condition`, and the tokens a
settlement establishes — and they are one supplied seam. `covers` can only name a
structural edge of the DR-MDP; the other two are opaque strings, and relabelling
the DR-MDP renames none of the three. The round's answer is only that the choice
is visible: it is a field of a standing, in the record, with provenance, rather
than a judgement inside a verdict function.

`C31` settles one narrow question about the first of the three. Two interventions
sharing an intervention class, reachable from two different states, are
distinguished by the existing `condition` field. The class did not have to widen,
and no fixture this round built forced the action ontology to change.

It also has nothing to say about the difference between influence an agent
intends and influence it merely causes. `C24` represents "incidental" by the
basis's `domain` field, which is a label on the authority rather than an account
of the agent's reasons.
