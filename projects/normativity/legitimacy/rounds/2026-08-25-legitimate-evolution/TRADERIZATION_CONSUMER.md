# The second consumer: which norms are entitled to continued enforcement

Status: **prosecution record and a prospective theorem shape; unregistered.** No
liability mathematics is invented here.

---

## 1. The question, and why the previous answer failed it

The enforcement pipeline compiles active `PForce` standing into a constraint
region. Its projection reads **everything in force**, entitled or not.

The previous pass offered `NormView = live ∩ Derivable`. `office.rogue_revocation`
is why that is not usable: an act with no legitimate authority revokes a norm,
the raw lifecycle drops it, and the enforcement target loses a norm nobody was
entitled to remove. For this consumer that is the whole ballgame — an attacker
who cannot add to the target could still subtract from it.

## 2. What the interface exports now

```text
NormView(alpha, t)  =  Norm(L(alpha, t))
lifetime(o)         =  { t : o in NormView(alpha, t) }
```

`cases.force_bearing` is the record where this is a real set: one injunction
issued under a seeded authority, legitimately superseded by a successor saying
something else, and a third issued inside an influence episode.

```text
alpha:trusting   successor and the manufactured one
alpha:audited    the successor alone
before tau 6     the first injunction
```

Three properties the enforcement consumer actually needs, and now has.

**G5 — persistence until a valid edit.** The target does not move because
something moved it; it moves because something *entitled* moved it.

**Legitimate supersession moves the target.** Not *once legitimate, enforced
forever*: when the successor is enacted the predecessor leaves.

**A revised audit context revises the target.** And in both directions —
tightening `alpha` can remove a norm whose lineage is now doubted, and can
**restore** one whose repeal is now doubted (`office.audit_restores`). A consumer
that cached `K^leg` would be wrong.

## 3. The prospective theorem

```text
PersistentLegitimateEnforcement                                (prospective)

  a process satisfying H1-H6, with Pi and Xi stated
  interpret     a consumer-supplied reading of a norm occurrence as a constraint
  K^leg_t       = intersection of interpret(o, t) over o in NormView(alpha, t)
  feasibility   K^leg_t meets the deductive region, with a witness
  bounded-lifetime liability
  ------------------------------------------------------------------
  on every date of every norm's legitimate lifetime the account funds the
  charge, force is emitted, and  dist(P_t, K^leg_t) <= delta_t
```

The conformance half is the traderization theorem's own conclusion. What this
round contributes is that `K^leg_t` is a well-defined object with a grounding
tree behind each conjunct, where the pipeline previously had a fold over
everything in force.

## 4. What the liability theory supplies, and the one theorem missing

**Supplied.** `force_api.compile_safe_force` computes
`outflow.LiveDeficitCertificate.by_enumeration` from the region it is about to
enforce, charges `q_t = (eps_t + M_t) * D_t / delta_t`, debits, then constructs
the position. The answerability scout telescopes a one-step inequality into
`sum_t c_t + Phi_T <= Phi_0 + sum_t eta_t`, with `sum_t c_t <= Phi_0` when there
are no grants.

**Missing, and unchanged by this pass.** Level I bounds the **total** charge
across all norms and all time. Nothing bounds a **particular** norm's charge over
**its own** lifetime.

> **Bounded-lifetime liability.** For a norm occurrence `o` whose issuance
> attaches an allowance `B(o)`, the charge allocated to `o` over `lifetime(o)` is
> at most `B(o)`; and the allowances attached over a trajectory are summable.

Three things it needs: an allowance minted with the occurrence — and occurrence
identity now gives it something unambiguous to attach to, which is a small gain
from this pass; charging against that occurrence; and either a finite lifetime or
a decaying allocation, since the per-date deficit provably does not fall with
increasing settlement.

`PRIORITIES.md` item 69.

## 5. A legitimate norm can be unenforceable

Not a stipulation. Under the default `quarantine` policy an account that cannot
fund the charge emits no force and produces no price, and
`force_api.compile_safe_force`'s own docstring records what happens to the norm:
*"force is withheld, nothing is spent, the endorsement keeps its normative
standing, and the answerability deadline it would otherwise miss is tolled."*

And it is not a corner: the inertness dichotomy puts every contentful injunction
in the charged branch, and no normative source in the repository is shown to have
summable liability.

```text
legitimate    entitled                  o in NormView(alpha, t)
accountable   answerable                the account layer
serviceable   sustainably enforceable   bounded-lifetime liability
```

Independent. Folding serviceability into legitimacy would make an insolvent norm
*illegitimate*, which is the wrong verdict, and would make the abstract layer read
a price.

## 6. What this consumer needs that the other does not

**The whole set at each index**, because the constraint is an intersection, and
the set must move correctly through time.

**Verifier completeness on disposals.** This is the sharpest asymmetry the pass
found. A sound but incomplete checker under-approximates: it misses valid edits.
For the recognition consumer that is conservative — it declines to recognize
things it should have. For enforcement it is a hazard in one direction only: a
missed valid *repeal* leaves an obsolete norm in the target, and force is then
applied without entitlement. `office.repealable` runs both cases and
`missed_disposals` is the quantity enforcement must watch.

So the two consumers can share an interface and cannot share a checker.

## 7. What this document does not establish

No theorem is proved. `PersistentLegitimateEnforcement` is a shape with a named
missing hypothesis.

`interpret` is consumer-supplied and unconstrained here; whether the compilation
of a legitimate norm is faithful to what the norm says is the vertical slice's
`K1`.

The process carries no liability field and this round did not add one — the
modularity of §5 is a design decision with a witness, not a theorem that
liability could not have been folded in.

Nothing here addresses whether a legitimacy verdict can be computed at
enforcement time. `ProvOK` on declared inputs is cheaper than the previous
replay, and an enforcement pipeline running per date is still where that cost
would bind.
