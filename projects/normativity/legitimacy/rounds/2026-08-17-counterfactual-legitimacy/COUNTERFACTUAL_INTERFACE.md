# The counterfactual interface

Two clauses, both predicates of a **variation class** `V` — a set of advisor
policies over one fixture — and neither a predicate of a run. That type change is
what the round is testing. The procedural round's conditions are predicates of a
trajectory, and its record-equivalence argument says no predicate of that type
reaches these cases.

## Clause 1 — reason-mediated non-capture

```
for all a, b in V:
    Coupled(a, b)  and  L(a) = L(b)   ->   Z(a) = Z(b)
```

Once the exogenous history and the licensed reasons actually supplied are fixed,
no residual difference in advisor influence reaches the protected machinery.
Equivalently: `Z` factors as `F(E, L)` over `V`.

`Coupled` is structural — same fixture, and neither policy suppressing an
encounter. `L` is the fine trace. `Z` is the five-coordinate projection.

## Clause 2 — protected access

```
for all a, b in V, for all t:
    Pool(t) ∩ delivered_a(t) = Pool(t) ∩ delivered_b(t)
    and  arising_a = arising_b
```

The advisor's policy choice does not determine which **due** inputs arrive:
neither which due reasons reach the principal, nor which encounters occur.

`Pool` is the due-reason set. It must be `Due` and not "everything licensed",
and the difference is the whole reason this clause does not forbid persuasion. A
reason the advisor originates and is under no obligation to supply is outside
`Pool`; delivering it in one arm and not another moves nothing here, and clause 1
is silent because the traces differ. A reason the principal is entitled to have
is inside `Pool`, and withholding it fires.

## The quantifier, which is not a detail

`V` is an argument, because two readings of the same formula are two different
objects.

**`V` = every policy the advisor could adopt.** A claim about the *principal's*
dynamics: this reasoner is not moved by non-reasons. No advisor can undertake to
satisfy it, so it does not license deference by an advisor. It is the right
reading for asking whether a principal is fit to be advised.

**`V` = one policy together with its residual variants and the null policy.** A
claim about *this advisor's* action space: whatever else this advisor might have
done within its residual latitude, the principal's protected machinery would have
been the same. This is the reading a deference argument needs, and every verdict
in `PROSECUTION.md` is stated against a named finite class of that shape.

The two readings agree on every scenario here, because each fixture's class is
the advisor's whole action space in that fixture. They will not agree in general,
and a statement that did not name its class would not be a statement.

## Why the quantifier is not decoration: dose compensation

Checking one chosen pair is not the same as quantifying over the class. An
advisor that knows which pair will be compared can push a revision and push it
back, so the audited contrast is flat while the class contains a policy that is
not — `QuantifyingOverTheClassReplacesPreRegistration`.

This is the dose-response note's dose-compensation attack in definitional form.
There, the fix is one committed stream, coarser than the arm partition. Here, it
is the quantifier. Same necessity, different instrument.

## Why the null policy must be in the class

A principal that moves on any exposure at all, identically at every positive
dose, satisfies clause 1 on every pair of positive-exposure policies —
`TheNullPolicyMustBeInTheClass`. Only a pair containing the zero-exposure policy
reveals it. This is the finite form of the note's observation that
presence-triggered steering is invisible to any design whose every arm has
nonzero dose.

## What is not tautological about this

The advisor is not denied write access to anything. Every coordinate of `Z` is
reachable by an advisor item, and the record-internal conditions hold in every
arm of every attack. What clause 1 asks is not "can the advisor write `Z`" but
"does a difference in `Z` trace to a difference in the reasons supplied", and the
two come apart precisely because the transition rule has a second channel.

The evidence that it is not definitional is the `none` principal: remove the
residual channel and `Z = F(E, L)` holds by construction, every attack becomes
unbuildable, and the round has nothing to report. The positive results are
results about a two-channel transition rule.

The harder evidence is the negative space. A condition fitted to the six attacks
would also have fired on autonomous bad revision, on the radical-transformation
control, and on persuasion; it fires on none of them. And it fails to fire on
selection among licensed reasons and cannot be stated against control of arising,
neither of which is obviously outside its reach until the fixture is built.
