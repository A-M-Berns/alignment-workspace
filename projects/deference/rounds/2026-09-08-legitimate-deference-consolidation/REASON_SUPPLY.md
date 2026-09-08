# Reason supply: protected reason coverage

**Status:** `ci-only`.  Lean: `lean/Workspace/Deference/Contrib/ReasonCoverage.lean`.

## 1. The channel

Reason mediation closes bypass: the advisor cannot move the verdict except through the
reason trace.  It leaves open *supply*: the advisor controls which reasons reach the
trace.  The narrow, scope-relative answer: **a certified evaluation may not omit a
protected live concern.**  The protected scope `Γ_eval` is declared and
history-relative; it is not the set of all decision-relevant truths.

## 2. Vocabulary, reused

From `NonCaptureCertificate.CovState`: `Active(c)` (anchored applicability), `Rep(c)`
(represented), `live(c) := Active ∧ ¬Rep`, and `Covered`: a live concern has an adequate
route.  `ReasonCoverage.CoverageData` carries `active`, `rep`, and one new field per
concern and world: `inTrace`, membership in the declared reason trace `R_{n:m}` at
commitment.  That field is the only bridge from the coverage semantics to the
authorship semantics, and it is the thinnest one: an encoding of a concern as a
trace element, declared by the application (**EXT**).

## 3. The two clauses and the theorem

```
RepFaithful(Γ_eval) :  Rep(c) ⇒ InTrace(c)              for c ∈ Γ_eval        (the bridge)
NoBindLive(Γ_eval)  :  C = 1 ⇒ ¬ live(c)                for c ∈ Γ_eval        (the barrier)
```

**Reason-coverage soundness** (`covered_of_barrier`, **LEAN**):

```
NoBindLive ∧ RepFaithful   ⟹   C = 1 ⇒ ∀ c ∈ Γ_eval. Active(c) ⇒ InTrace(c)
```

and its contrapositive (`void_of_omitted`, **LEAN**): a protected active concern missing
from the trace forces `C = 0`.  Suppression does not produce a conveniently
manipulated authoritative `V`; it produces authority failure.

**Void-mass bound** (`covFail_mass_le`, **LEAN**): under soundness, with `π ≥ 0`,

```
P(∃ c ∈ Γ_eval. Active(c) ∧ ¬InTrace(c))  ≤  𝔼[1 − C]  ≤  η .
```

High availability therefore bounds the credence of protected-reason-suppression
worlds — *relative to the declared scope*.  It does not say `Γ_eval` was complete.

## 4. Where Robust Openness sits — three things kept apart

| | statement | supplied by | label |
|---|---|---|---|
| **A. Soundness / barrier** | `C = 1 ⇒` protected reasons covered | `NoBindLive + RepFaithful`; needs nothing from RO | LEAN |
| **B. Route availability** | a live protected concern has an adequate route by which it can become represented | `RobustOpenActual` at the snapshot: `CovState.Covered` on the actual branch and every declared intervention (`route_of_live`) | LEAN (it is the current type) |
| **C. Liveness / availability** | the route is exercised, the concern becomes represented, the evaluation certifies | **not** RO; not any theorem in this stack | OPEN |

A imposed alone gives soundness with possibly vacuous availability (fixture **H**: every
route destroyed, the concern stays live, `C = 0` forever, `η = 1`).  B alone gives a
route and no coverage (fixture **G**: the evaluator commits before representation).
B with A is the composition the stack offers: if the barrier is imposed and openness
holds, then a protected concern that is live has a route, and certification waits on
its representation.  What closes C — that routes are exercised in time — is the
serviceability question; the answerability/service results on `main` are about
obligations in the accounted state and are **not imported** here, since a concern's
representation is not typed as an obligation in this stack.  The residue is named in
`PRIORITIES.md` item 87, not solved.

## 5. Fixtures

`COUNTERMODELS.md` F–L; Lean `Witness.route_without_barrier`,
`Witness.barrier_without_route`, `Witness.unfaithful`, `Witness.unprotected_omission`,
`Witness.consideration_not_agreement`.  The last is the point of "coverage":
consideration, not agreement — the protected objection favouring `b` is represented
and in the trace, the principal still chooses `a`, and nothing in coverage reads the
verdict.

## 6. What is not established

- That any declared `Γ_eval` is the right scope, or that any concern's trace encoding
  is faithful (EXT).
- That routes are exercised (OPEN); that `C` is ever `1` (OPEN).
- Anything about facts outside `Γ_eval` (fixture **J**: withholding an unprotected fact
  is not a violation of this theorem).
