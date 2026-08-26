# The second consumer: which norms are entitled to continued enforcement

Status: **prosecution record and a prospective theorem shape; unregistered.** No
liability mathematics is invented here.

---

## 1. What it consumes

Unambiguously the current state:

```text
NormView_t  =  { o in L_t : not Auth(o) }
```

Enforcement is about what is in force now, so this consumer needs `Live`, never
`Grounded`. That was already true and the previous pass stated it; what changed is
that the *other* consumer turns out to need `Live` too, so the asymmetry between
them is withdrawn.

`cases.force_bearing` is the record where the projection is a real set: one
injunction issued, legitimately superseded, and a third issued inside a doubted
episode. At `alpha:audited` the target is the successor alone.

## 2. The four cases

| | target |
|---|---|
| unauthorized repeal | the norm **stays** — a rejected edit is a no-op |
| valid repeal | the norm leaves |
| missed valid repeal | the norm **wrongly stays**, and the checker is at fault |
| audit-invalidated repeal | the norm **returns** |

The first is `office.rogue_revocation` and is the attack that replaced the
previous object. The fourth is `office.audit_restores` and is why a consumer that
cached the target would be wrong.

The third is now a checker question with an exact answer: agreement along the
trace. The previous pass had a weaker condition here and it does not hold up —
`COUNTERMODELS.md` §3.

## 3. The prospective theorem

```text
PersistentLegitimateEnforcement                                (prospective)

  a process satisfying S1 and S2, with its semantics stated
  interpret     a consumer-supplied reading of a norm occurrence as a constraint
  K^leg_t       = intersection of interpret(o, t) over o in NormView_t
  feasibility   K^leg_t meets the deductive region, with a witness
  bounded-lifetime liability
  ------------------------------------------------------------------
  on every date of every norm's legitimate lifetime the account funds the
  charge, force is emitted, and  dist(P_t, K^leg_t) <= delta_t
```

## 4. The one theorem still missing

**Supplied.** `force_api.compile_safe_force` computes
`outflow.LiveDeficitCertificate.by_enumeration` from the region it is about to
enforce, charges, debits, then constructs the position. The answerability scout
telescopes a one-step inequality into `sum_t c_t + Phi_T <= Phi_0 + sum_t eta_t`.

**Missing, unchanged.** Level I bounds the **total** charge across all norms and
all time. Nothing bounds a **particular** norm's charge over **its own** lifetime.

> **Bounded-lifetime liability.** For a norm occurrence `o` with an allowance
> attached at issuance, the charge allocated to `o` over its lifetime is at most
> that allowance, and the allowances are summable.

Occurrence identity gives it something unambiguous to attach to, and the lifetime
is now well defined at a fixed audit context. `PRIORITIES.md` item 69.

**Narrowed by the answerability pass**, in two ways, both in `ANSWERABILITY.md`
§4. First, the bound cannot be a structural theorem: four constitutions transfer
every obligation to a named successor, satisfy both structural premises and the
continuity theorem, and shrink the total burden — `diluted_to_nothing` to zero. So
it must be sought as a hypothesis on the succession semantics, in the same shape
as the monotone-reach conditional. Second, it must be stated in **total**
accounting. Per-parent accounting is not a weaker form of the same law; a merge of
two obligations of weight 1 into one of weight 1.5 passes per-parent while the
total falls, so the per-parent statement is false and would look proved.

## 5. Legitimate but unenforceable

Unchanged and not a stipulation: under the default exhaustion policy force is
withheld and *"the endorsement keeps its normative standing, and the answerability
deadline it would otherwise miss is tolled"*. Every contentful injunction is in
the charged branch by the inertness dichotomy, and no normative source in the
repository is shown to have summable liability.

```text
legitimate    entitled                  o in NormView_t
accountable   answerable                a separate interface
serviceable   sustainably enforceable   bounded-lifetime liability
```

## 6. What this does not establish

No theorem is proved. `interpret` is consumer-supplied and unconstrained.

Whether a legitimacy verdict can be computed at enforcement time is still open,
and this pass makes the cost more precise rather than smaller: the target is
`L_t`, and `L_t` is a replay.
