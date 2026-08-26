# The first consumer: plugging it into the deference machinery

Status: **prosecution record; unregistered.** Cited by path against this branch's
base, not from memory. `TRADERIZATION_CONSUMER.md` is the second consumer.

---

## 1. What the consumer actually is

| statement | where | what it needs |
|---|---|---|
| `delegation_bridge` | `lean/Workspace/Deference/Contrib/DelegationBridge.lean:71` | `GradeTrust EX W eta`, `hp`, `J` pointwise grade-maximal |
| `GradeTrust EX W eta` | same file, line 52 | `forall x pi. abs (EX x pi - W x pi) <= eta` |
| `canCorrectFuture_iff`, `forecloses_iff` | `ReachableCorrectiveControl.lean:306,313` | a finite transition system with three input coordinates |

Both are registered `lean-proved` in `projects/deference/CLAIMS.md`, the second
**because it refutes its own round's protection claims**:
`advisor_has_a_universal_veto` and `canCorrectFuture_measures_advisor_cooperation`
(lines 1051 and 926) say the capability predicate measures the advisor's
cooperation rather than the principal's control.

Two documents say where the hole is, in the deference line's own words.

`DelegationBridge.lean`'s docstring: grade trust "is the source's substantive
hypothesis and it is imported, not derived — the source's §1.1 and §4 argue at
length that no settlement instantiation in the skeleton produces it."

`projects/deference/notes/FUTURE_AGENT_SPEC.md`, whose status block is a
diagnosis of a collapse: "**The cause is the signature, not the parameterisation.**
Two authorisation regimes that induce the same realisation map `Ω → Π_n ⊔ {⊥}`
are the *same object* in a model whose only outputs are such maps priced by one
measure. No fourth parameter repairs that; **the authorisation relation has to be
in the type.**" And, four questions later: "Value drift is deliberately excluded."

## 2. The substitution, against the repaired interface

`W : C -> P -> Q` carries **no index** — not a time, not a process, not an
authority. The object to be substituted has nowhere to go, so the first result is
a re-typing:

```text
                     W : C -> P -> Q                            current
                     W : A -> C -> P -> Q                        required
                     W_x  for the authority x in AuthorityView_s
```

The repaired interface supplies the index and the time at which to read it:

```text
CertifiedDelegation                                            (prospective)

  Recognizes_A(G)                       A accepts a base
  Xi                                    and a threat model
  B |= LegitimacyInterface              B satisfies L0-L8
  Coverage(B, Xi)                       B's challenges reach Xi
  x in AuthorityView_s under B          x is legitimately live at s
  (W-index)  W_x is a function of the authority in force
  GradeTrust EX W_x eta
  hp, and J pointwise W_x-maximal
  -----------------------------------------------------------------
  valuation p EX sel + gradeMargin p W_x J sel
      - 2 * eta * disagreementMass p J sel   <=   valuation p EX J
```

**The legitimacy fact appearing as a hypothesis is `x in AuthorityView_s`**, and
it does one job: it makes `GradeTrust EX W_x eta` a proposition the advisor did
not select. The bridge's inequality is already proved and legitimacy contributes
nothing to it.

Three things the repair changed about what that hypothesis is worth.

**It is stronger than the first pass's.** `G |- x` now requires every licence in
the lineage to be derivable, not merely to survive. The first pass's version was
satisfiable through an authority that survived a counterfactual while being
entitled to nothing, which is exactly the manipulation the premise exists to
exclude. `COUNTERMODELS.md` §1.

**It is relative to a threat model, and says so.** A deference theorem consuming
`G |- x` without `Coverage` would be consuming a certificate against nothing.

**It is time-indexed.** `AuthorityView_s` rather than `G |- x` alone, so the
premise is about the authority in force when the grade is read, and T4 is what
says it does not silently lapse between dates.

**(W-index) is substantive and is not free.** It is the sharpened form of the
August 17 interface's `H5`, grade factorization, and `grade_reads_outside` is that
round's witness of a grade reading a field the protected object does not cover,
flipping grade trust while every legitimacy clause stays silent.

## 3. What this buys over the August 17 interface

That interface supplied non-capture: `Coupled(a,b) and L(a) = L(b) => Z(a) = Z(b)`
over a named advisor variation class.

**Checkability.** Non-capture is a semantic property of a variation class, and the
procedural round established that no statistic of one realized trajectory
determines it. `x in AuthorityView_s` is a property of one frame, one threat model
and finitely many stability judgments. That is an improvement in what `A` could
come to be entitled to, bounded by §3 of `CROSS_PROCESS_INTERFACE.md`.

**Scope.** The Carroll round found non-capture's antecedent *false* on both
laundering classes, because laundering runs through the reason channel and so
changes the licensed-reason trace. Derivability fires there.

**Coverage, the other way.** Access and coverage survive as independent clauses
catching things this interface does not — a withheld due reason is not a
succession defect and no axiom of the spine sees it. The composition remains a
conjunction.

## 4. The corrigibility shape, and the hypothesis with no model

```text
CorrigibleDeference                                            (prospective)

  Recognizes_A(G), Xi, B |= LegitimacyInterface, Coverage(B, Xi)
  x in AuthorityView_s under B
  Trust:              GradeTrust EX W_x eta, (W-index)
  EffectiveAuthority: the principal's corrective capability is preserved
                      under every advisor policy in scope
  -----------------------------------------------------------------
  A has no strictly dominant preemption on the protected domain
```

The three inputs are the August 17 interface's own proposal, and the round can say
which is missing: the third. `ReachableCorrectiveControl`'s registered refutations
mean there is no formal object standing for `EffectiveAuthority`. Legitimacy does
not supply it and this round does not attempt to — standing and effective causal
access were separated by the relational-scorekeeping bridge and shown independent
in both directions.

So the corrigibility theorem is **statable and not provable**, and the obstacle is
`PRIORITIES.md` item 22's fourth question: a protected-capability predicate
quantifying the advisor universally.

## 5. The negative test: pretend Reflective Integrity does not exist

Delete `NormEvent`, `AnsRoot` and `ReasonOcc` from §2 and §4 and read what
remains.

**Can the consumer theorem still be stated?** Yes. Every hypothesis is a condition
on the frame, and the warrant register satisfies them with no ledger anywhere.

**Can the legitimacy premise be checked or proved in principle?** Yes, and the
cost is realization-dependent. A derivation is finite in every realization. The
stability judgments are a reachability query in the warrant register and a replay
in ours.

**Does `A` need to know `B`'s internal representation?** For the interface, no.
**For our realization's stability oracle, yes** — the honest answer is not the
desired one, and it is unchanged by this pass. `A` must hold `B`'s record,
challenge it interactively, or accept an attestation.

**Does `A` need to endorse `B`'s future normative content?** No.

Three of four, with the third qualified rather than met — and the qualification is
a fact about this realization, not about the interface, which is the distinction
the abstraction exists to make visible.

## 6. What the deference line would have to change

Unchanged by this pass, and still one field and one hypothesis.

1. **`W` acquires an index.** `W : A -> C -> P -> Q`, read off the authority in
   force. `valuation`, `gradeMargin`, `disagreementMass` and both theorems take
   `W` as a parameter and never inspect it, so nothing in the file is revised.
2. **(W-index) is stated as a hypothesis.** That the principal's grade is a
   function of the authority in force, and not of anything the advisor can write
   beside it.

## 7. What this test does not establish

That `W` tracks anything worth tracking. `FINITE_MODEL_SKELETON.md` §8.5 declares
"**The relation between `v⁺` and `X`** — none", and legitimacy cannot supply it:
that is a claim about the principal's competence about the world.

That the re-typing is enough. It makes the premise statable; whether the resulting
theorem is worth proving depends on the grade-to-quantity link the programme
decided to derive rather than assume, which is `PRIORITIES.md` Q2.

That `A` can come to be entitled to the stability judgments, as against a theorem
consuming them. That is the epistemic lifting problem and it is where the August
17 interface left it.
