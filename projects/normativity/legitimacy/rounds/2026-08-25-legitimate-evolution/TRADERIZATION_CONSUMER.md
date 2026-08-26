# The second consumer: which norms are entitled to continued enforcement

Status: **prosecution record and a prospective theorem shape; unregistered.**
Cited by path against this branch's base. No liability mathematics is invented
here; what is new is the legitimacy side of the interface and the identification
of the one theorem that is missing.

---

## 1. The question

The enforcement pipeline compiles active `PForce` standing into a constraint
region and hands it to a trader. The projection it reads is `O_t`, a fold over
the normative view — **everything in force**, whether or not any of it is
entitled to be. A manufactured injunction compiles exactly like an earned one.

The consumer question is therefore:

> Can the legitimacy interface identify exactly which norms are entitled to
> continued enforcement, so that an enforcement guarantee can be stated over a
> norm's legitimate lifetime rather than over its mere presence?

## 2. What the legitimacy interface exports

Two objects, and neither mentions a normative event.

```text
NormView_s   =  project(F^leg_s, classify, "norm")
lifetime(n)  =  { s : n in NormView_s }
```

`cases.force_bearing` is the record where this is a real set rather than an
assertion: one injunction issued under a seeded authority, legitimately
superseded by a successor saying something else, and a third issued inside an
influence episode.

```text
live at the end        the successor and the manufactured one
NormView at the end    the successor alone
NormView at tau = 3    the first injunction, before its supersession
```

So the interface distinguishes *live* from *legitimately live*, which is the
distinction the operative projection cannot make, and it does so without the
consumer knowing what a `PForce` payload is — `classify` is supplied by the
consumer and the frame does not know what a norm is.

Two theorems make `lifetime` usable rather than decorative.

**T4** gives *persistent until legitimately changed*: a norm stays in the
frontier until an exercise acts on it. So a lifetime is not a per-date recomputation
that might silently drop a norm nobody touched.

**T4'** gives the second exit: a new challenge can remove a norm from the
frontier with nothing acting on it. **The enforcement target must therefore be
allowed to move**, and a consumer that cached `K^leg` would be wrong. This is the
answer to *once legitimate, enforced forever* — it is not what the interface
says.

## 3. The prospective theorem

```text
PersistentLegitimateEnforcement                                (prospective)

  L         a legitimacy interface with coverage against a stated Xi
  interpret  a consumer-supplied reading of a norm as a constraint
  K^leg_s   = intersection of interpret(n, s) over n in NormView_s
  feasibility  K^leg_s intersect K^D_s is non-empty, with a witness
  bounded-lifetime liability  for each n, the charge allocated to n over
                              lifetime(n) is at most an allowance attached to n
                              at issuance, and the allowances are summable
  ------------------------------------------------------------------
  on every date of every norm's legitimate lifetime the account funds the
  charge, force is emitted, and  dist(P_s, K^leg_s) <= delta_s
```

The conformance half — `dist(P_s, K^leg_s) <= delta_s` — is the traderization
theorem's own conclusion and is not this round's to state. What this round
contributes is that `K^leg_s` is now a well-defined object with a legitimacy
warrant behind each conjunct, where the pipeline previously had `K^N_s` with
nothing behind it.

## 4. What the liability theory already supplies, and what it does not

**Supplied.** The charged branch runs: `force_api.compile_safe_force` computes
`outflow.LiveDeficitCertificate.by_enumeration` from the region it is about to
enforce, charges `q_t = (eps_t + M_t) * D_t / delta_t`, debits, and only then
constructs the position. The answerability scout's Level-I result telescopes a
one-step inequality into

```text
sum_t c_t  +  Phi_T  <=  Phi_0  +  sum_t eta_t
```

under four local laws checkable at one event, with `sum_t c_t <= Phi_0`
unconditionally when there are no grants.

**Not supplied, and this is the gap.** Level I bounds the **total** charge across
all norms and all time. It does not say that a **particular** norm's allowance
covers **its own** lifetime. Between the two sits the allocation `alloc_t(i)` —
each force-bearing standing's own rows over the joint support, which the scout
shows is a real `ForceRequest` and covers `c_t` subadditively — and nothing
bounds `sum over lifetime(n) of alloc_s(n)` by anything attached to `n`.

So the missing theorem is exactly:

> **Bounded-lifetime liability.** For a norm `n` whose issuance attaches an
> allowance `B(n)`, the charge allocated to `n` over `lifetime(n)` is at most
> `B(n)`; and the allowances attached over a trajectory are summable.

Three things it would need, all of which have a place to attach and none of which
exists. An allowance minted **with** the norm — the scout names `MINT` as the
seam where a number attaches to an episode, and `Phi_0` is currently a seed fact
rather than a per-norm one. Charging against the norm's own episode — the scout's
L1. And either a finite lifetime or a decaying allocation, since `D_t` provably
does **not** fall with increasing settlement: a frozen injunction over `Expect(X)`
recompiles at each day's mesh and a free day becomes a charged day with nothing
unsettled.

## 5. A legitimate norm can be unenforceable, and the architecture already says so

This is the round's answer to whether legitimacy should absorb serviceability,
and it is not a stipulation — it is the behaviour of the existing API. Under the
default `quarantine` policy, an account that cannot fund the charge emits no
force and produces no price, and `force_api.compile_safe_force`'s own docstring
records what happens to the norm: *"force is withheld, nothing is spent, the
endorsement keeps its normative standing, and the answerability deadline it would
otherwise miss is tolled."*

Keeping its normative standing is exactly the legitimate-but-unenforceable case.
And it is not a corner: the inertness dichotomy says an injunction that changes
the price region at all falls outside the unconditional traderization theorem's
hypothesis, so **every** norm this consumer cares about is in the charged branch
and needs the liability hypothesis. No normative source in the repository is
shown to have summable enforcement liability.

So the three interfaces come apart, and the round recommends keeping them apart:

```text
legitimate    entitled                    G |- n, under coverage
accountable   answerable                  the account layer, L7-L8 and T5
serviceable   sustainably enforceable     bounded-lifetime liability
```

A norm can be the first without the third, and the enforcement consumer needs
both. Folding serviceability into legitimacy would make an insolvent norm
*illegitimate*, which is the wrong verdict — being unable to afford enforcement
is not a defect in one's entitlement — and it would make the legitimacy calculus
read a price, which the abstract layer must not do.

**A norm can also be the first without the second**, which is §6 of
`COUNTERMODELS.md`. The three are independent and the consumer picks.

## 6. What this consumer needs that the deference consumer does not

The deference consumer reads `AuthorityView` and needs one authority at a time:
the process whose later judgment is to be deferred to. The enforcement consumer
reads `NormView` and needs the **whole set at each index**, because the
constraint it enforces is an intersection, and it needs the set to **move
correctly through time**, because a superseded norm must stop being enforced.

That is what made the lifecycle a required addition rather than a nicety. A
provenance calculus answering only `G |- y` tells the enforcement consumer
nothing about when to stop.

## 7. What this document does not establish

No theorem is proved. `PersistentLegitimateEnforcement` is a shape with a named
missing hypothesis, and the hypothesis is not one this round is entitled to
assume.

`interpret` is consumer-supplied and unconstrained here. Whether the compilation
of a legitimate norm is faithful to what the norm says is the vertical slice's
`K1` and is not a legitimacy question.

The frame exports no liability field and this round did not add one — the
modularity of §5 is a design decision with a witness, not a theorem that
liability could not have been folded in.

Nothing here addresses whether a legitimacy verdict can be computed at
enforcement time. The stability judgments behind `NormView` cost a replay in this
realization, and an enforcement pipeline running per date is exactly the setting
where that cost would bind.
