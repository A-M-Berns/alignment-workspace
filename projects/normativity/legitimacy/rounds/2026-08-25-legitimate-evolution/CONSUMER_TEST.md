# The first consumer: the deference machinery

Status: **prosecution record; unregistered.** Cited by path against this branch's
base. `TRADERIZATION_CONSUMER.md` is the second consumer.

---

## 1. The consumer, unchanged

| statement | where | what it needs |
|---|---|---|
| `delegation_bridge` | `lean/Workspace/Deference/Contrib/DelegationBridge.lean:71` | `GradeTrust EX W eta`, `hp`, `J` pointwise grade-maximal |
| `GradeTrust EX W eta` | same file, line 52 | `forall x pi. abs (EX x pi - W x pi) <= eta` |
| `canCorrectFuture_iff`, `forecloses_iff` | `ReachableCorrectiveControl.lean:306,313` | a finite transition system with three input coordinates |

`DelegationBridge.lean`'s docstring: grade trust "is the source's substantive
hypothesis and it is imported, not derived". `FUTURE_AGENT_SPEC.md`'s status
block: "**The cause is the signature, not the parameterisation.** ... **the
authorisation relation has to be in the type.**" And: "Value drift is
deliberately excluded."

## 2. The substitution, against the compressed interface

`W : C -> P -> Q` carries no index. The re-typing is the same one the previous
pass found, and the object filling it is now sharper:

```text
                     W : Occ -> C -> P -> Q
                     W_o  for o in Auth(L(alpha, t))
```

```text
CertifiedDelegation                                            (prospective)

  Recognizes_A(G), Pi, Xi, alpha            what A accepts
  B proposes a process satisfying H1-H6
  o in Auth(L(alpha, t))                    the legitimacy premise
  (W-index)  W_o is a function of the authority in force
  GradeTrust EX W_o eta
  hp, and J pointwise W_o-maximal
  -----------------------------------------------------------------
  valuation p EX sel + gradeMargin p W_o J sel
      - 2 * eta * disagreementMass p J sel   <=   valuation p EX J
```

**The legitimacy fact is `o in Auth(L(alpha, t))`**, and its job is unchanged: to
make `GradeTrust` a proposition the advisor did not select. Four things changed
about what it is worth.

**It is a fact about a reconstructed state, not a filtered one.** The previous
premise could be defeated by an attacker with no authority, because the raw
process's lifecycle was a conjunct. It cannot now: an unauthorized revocation is
a no-op.

**It rules out the exercise and not just the provenance.** `Permit` is a conjunct
of `Valid`, so an authority used outside its jurisdiction issues nothing. The
previous premise did not carry that.

**It is indexed by an audit context**, so a recognizer that learns of an
influence revises its premise rather than being stuck with a verdict taken once.

**It does not require the future authority to have survived a counterfactual**,
so a principal who was argued into a revision still has one.

**(W-index) is substantive.** It is the August 17 interface's `H5` sharpened, and
`grade_reads_outside` is that round's witness of a grade reading a field the
protected object does not cover.

## 3. What this buys over challenge-stability

The comparison with the August 17 non-capture clause is unchanged and is in the
previous pass's record. The comparison worth making now is with the round's own
previous premise.

**Checkability improved again.** The old premise needed a stability judgment per
edge, each costing a replay of the record under a voided episode, and the
operator was neither monotone nor composable. The new one needs `ProvOK` on each
edit's declared input — evaluable by the recognizer from the declared data.

**Coverage did not improve.** `ProvOK`'s adequacy to `Xi` is still an axiom.

## 4. Corrigibility

```text
CorrigibleDeference                                            (prospective)

  Recognizes_A(G), Pi, Xi, alpha
  o in Auth(L(alpha, t)) under B
  Trust:              GradeTrust EX W_o eta, (W-index)
  EffectiveAuthority: the principal's corrective capability is preserved
                      under every advisor policy in scope
  -----------------------------------------------------------------
  A has no strictly dominant preemption on the protected domain
```

Statable and not provable, and the missing hypothesis is unchanged:
`ReachableCorrectiveControl`'s registered refutations mean there is no formal
object standing for `EffectiveAuthority`. Legitimacy does not supply it.

## 5. The negative test: pretend Reflective Integrity does not exist

**Can the consumer theorem be stated?** Yes. Every hypothesis is a condition on
the process, and a constitution and its gazette satisfy them.

**Can the legitimacy premise be checked in principle?** Yes, and more cheaply
than before. A grounding tree is finite; `Valid` at each node is `grounds`,
`Permit` and `ProvOK`.

**Does `A` need `B`'s internal representation?** For the interface, no. **And now
substantially less for the realization** — `ProvOK` reads declared inputs rather
than replaying the record. `A` still needs the declared data, which is not
nothing, and route 3 of `CROSS_PROCESS_INTERFACE.md` §3 remains a trust
assumption when `A` will not hold it.

**Does `A` need to endorse the content?** No.

Three of four cleanly, and the third improved from *no for the interface, yes for
our oracle* to *no for the interface, and the realization now needs declared data
rather than the whole record*.

## 6. What the deference line would have to change

Unchanged, and still one field and one hypothesis: index `W` by the authority in
force, and state that the grade is a function of it. Neither revises a registered
statement.

## 7. What this test does not establish

That `W` tracks anything worth tracking — `FINITE_MODEL_SKELETON.md` §8.5
declares "**The relation between `v⁺` and `X`** — none".

That the re-typing is enough; whether the resulting theorem is worth proving
depends on the grade-to-quantity link, which is `PRIORITIES.md` Q2.

That `A` can come to be entitled to the provenance judgments, as against a
theorem consuming them.
