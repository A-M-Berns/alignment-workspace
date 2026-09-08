# Diachronic authorship

**Status:** `ci-only`.  Lean: `lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean`
(the #93 module, extended here: `selPairs`, `selectionBlind_iff_blind`,
`selectionBlind_of_blind`, `Witness.earlyWrite`, `Witness.diachronic_learning`,
`Witness.transient`).

## 1. The issuance-rooted frame

```
β_n : Q_n^A → Z_n^P → Ω_n
```

- `q ∈ Q_n^A`: the advisor's **whole contingent continuation** from the issuance prefix
  `h_n` through the evaluation's commitment at `m = f(n)` — every session input, every
  early intervention, every disposition it might attempt.
- `z ∈ Z_n^P`: the principal-side / exterior **response policy** fixed at `h_n`.  Not
  realized actions: the principal's realized cognition and actions differ across `q`
  because the delivered reasons differ, and that is the permitted influence.
- `β_n(q, z)`: the resulting continuation.

This is the Cartesian-frame shape (`CartesianFrameBridge.Frame.outcome`) at a different
instantiation of the types; `ReasonMediatedAuthorship.lean` is polymorphic in `Q`, `Z`,
`Ω`, so **no new Lean object is needed**.  The session-local reading of #93 — `q` one
session's inputs, `z` the policy at session start, `R` the reasons held at commitment —
is the same predicate at the session instantiation.

## 2. The reason trace

```
R_{n:m} : Ω_n → ℛ_{n:m}
```

The **admitted deliberative inputs encountered by the principal over the interval**:
settled facts, proofs, arguments, authenticated reports, protected objections, and
their admissions, withdrawals and dispositions.  It is not the principal's posterior,
not the final vector, not the whole world, not the advisor policy.

**Why a trace and not a final reason state.**  A legitimate transient argument may
move the principal and later leave the current view.  Under a final-state view two
continuations — never argue, argue-then-withdraw — have equal reasons and different
verdicts, so the honest influence reads as a bypass; under the trace they differ.
`Witness.transient` (**LEAN**): final-state mediation fails, trace mediation holds.

## 3. Diachronic reason mediation

```
∀ q q' ∈ D.  R_{n:m}(β_n(q, z)) = R_{n:m}(β_n(q', z))  →  V_m(β_n(q, z)) = V_m(β_n(q', z))
```

equivalently `V_m ∘ β_n(·, z) = F_z ∘ R_{n:m} ∘ β_n(·, z)` on `D`
(`reasonMediated_iff_factor`, **LEAN**).  Any mediation relation on continuations
reduces to its equivalence closure (`invariant_iff_eqvGen`), so the trace with equality
is the general form.

**Is it stronger than the session-local theorem?**  Yes, as an instantiation: it
quantifies over whole continuations, so an early intervention that leaves no trace is
a member of `D` and is constrained.  The session-local theorem quantifies only over the
terminal session's inputs at a policy that already incorporates whatever happened
before.  `Witness.earlyWrite` (**LEAN**; fixture **D**): with continuations
`(early, late) ∈ {none, write} × {argue, silent}`, trace = the terminal argument, verdict
= whether the early write occurred — session-local mediation holds at *both* session
policies (the write is inside `z_s`), issuance-rooted mediation fails.  That is the
reason to adopt the diachronic scope.  Legitimate diachronic learning survives
(`Witness.diachronic_learning`; fixture **E**): an early proof enters the trace, moves
the verdict, and mediation holds.

**What is still outside.**  A change of the principal role's *holder* by authorized
succession within the interval.  That is Legitimate Evolution's business (the role
identity is anchored; its holder is a `LocalLaw`), not authorship's.

## 4. Channel blindness carries the content

`Blind β R P z` (**LEAN**): the trace reads the same on every declared pair of
continuations differing only through a prohibited channel.  Then

```
Blind R P  ∧  ReasonMediated   ⟹   Blind V P                     (blind_of_mediated, LEAN)
```

The declared `P` — direct disposition writes, coercion, side channels — is where the
normative content sits, and its correctness is **EXT**.  The two failure modes of the
declaration are unchanged from #93: an injective trace makes mediation vacuous
(`reasonMediated_of_injOn`); a constant trace is the isolated-principal reading
(`reasonMediated_const_iff`), which is the no-AI reference evaluator recovered as the
coarsest trace.

## 5. Selection blindness is an instance

`selPairs qpol := {(qpol σ, qpol σ')}` is the pair class induced by changing the
advisor's selection for this occurrence across its whole continuation, and

```
SelectionBlind V qpol  ↔  Blind V (selPairs qpol)                (selectionBlind_iff_blind, LEAN)
Blind R (selPairs qpol) ∧ ReasonMediated  ⟹  SelectionBlind V    (selectionBlind_of_blind, LEAN)
```

`SelectionBlind` is kept as a derived name for the Value theorem's scope condition; it
is not a second primitive.  Literal no-preview — the principal never reads the
selection coordinate — is `Blind R` for the *coordinate* pairs only, which is weaker
than `Blind R (selPairs qpol)` when the advisor's other inputs depend on its selection
(`Witness.leak`; fixture **K**): every mediation clause holds, the principal never sees
the selection, and the payload depends on it through the leaked input.  So the
application must certify blindness to `P_sel` for the **whole selection-conditioned
continuation**, and authorship alone does not supply it: with the selection inside the
trace, mediation holds and Value's domain condition can fail.

## 6. Exclusive binding

`ExclusiveBind β author D z`: on every audited continuation the binding event is the
principal's.  In the account it is the receipt's `warrant` being the principal role's
binding warrant with `Authorized` holding only for principal-produced events — an
existing field plus the standing semantic-authentication input.  Both conjuncts are
needed (`Witness.bind_not_mediated`, `Witness.mediated_not_bind`).

## 7. Stochastic principal

Unchanged from #93 §3: the per-seed deterministic form with the seed inside `z` is the
theorem; the kernel form `Law(V | R = r, do(q))` invariant in `q` is its corollary under
seed privacy (EXT); the converse fails.  No stochastic Lean.

## 8. Quantitative form

`χ` and `regretU_perturb` unchanged from #93 §5; the link between the counterfactual sup
and per-world perturbation remains **OPEN**.
