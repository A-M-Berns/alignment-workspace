# Plugging it into the deference machinery

Status: **prosecution record; unregistered.** Cited by path against this
branch's base, not from memory.

---

## 1. What the consumer actually is

| statement | where | what it needs |
|---|---|---|
| `delegation_bridge` | `lean/Workspace/Deference/Contrib/DelegationBridge.lean:71` | `GradeTrust EX W η`, `hp`, and `J` pointwise grade-maximal |
| `GradeTrust EX W η` | same file, line 52 | `forall x pi. abs (EX x pi - W x pi) <= eta` |
| `delegation_bridge_unconditional` | same file, line 97 | nothing, and it concludes a `2B` deficit |
| `canCorrectFuture_iff`, `forecloses_iff` | `lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean:306,313` | a finite transition system with three input coordinates |

Both bodies are registered `lean-proved` in `projects/deference/CLAIMS.md`. The
first is the deference target and the second is the corrigibility target, and
the second is registered **because it refutes its own round's protection
claims**: `advisor_has_a_universal_veto` and
`canCorrectFuture_measures_advisor_cooperation` say the capability predicate
measures the advisor's cooperation rather than the principal's control.

Two documents say where the hole is, in the deference line's own words.

`DelegationBridge.lean`'s docstring: grade trust "is the source's substantive
hypothesis and it is imported, not derived — the source's §1.1 and §4 argue at
length that no settlement instantiation in the skeleton produces it."

`projects/deference/notes/FUTURE_AGENT_SPEC.md`, whose whole status block is a
diagnosis of a collapse: "**The cause is the signature, not the parameterisation.**
Two authorisation regimes that induce the same realisation map `Ω → Π_n ⊔ {⊥}`
are the *same object* in a model whose only outputs are such maps priced by one
measure. No fourth parameter repairs that; **the authorisation relation has to be
in the type.**" And, four questions later: "Value drift is deliberately
excluded."

## 2. The substitution, attempted

`W : C -> P -> Q` is the principal's grade. It carries **no index** — not a time,
not a process, not a standing. So the object the round was asked to substitute
into has nowhere to go, and the first result of the test is a re-typing rather
than a substitution:

```text
                     W : C -> P -> Q                          current
                     W : A -> C -> P -> Q                      required
                     W_x := W x   for the authority x in force
```

With that index the bridge restates:

```text
CertifiedDelegation                                            (prospective)

  Recognizes_A(G)                       A accepts a base
  B |= LegitimacyInterface              B satisfies L0-L4
  G |-_B x                              x is certified from that base in B
  (W-index)  W_x is a function of the authority in force at x
  GradeTrust EX W_x eta
  hp, and J pointwise W_x-maximal
  -----------------------------------------------------------------
  valuation p EX sel + gradeMargin p W_x J sel
      - 2 * eta * disagreementMass p J sel   <=   valuation p EX J
```

**The legitimacy fact that appears as a hypothesis is `G |-_B x`, and it does
exactly one job: it is what makes `GradeTrust EX W_x eta` a proposition the
advisor did not select.** The bridge's inequality is already proved and
legitimacy contributes nothing to it. What legitimacy contributes is that `W_x`
is not something the advisor arranged, and the arrangement it excludes is
precise: by **T3**, no authority anywhere in `x`'s provenance was issued by an
exercise the challenge challenges.

**(W-index) is new and substantive.** It is the sharpened form of the August 17
interface's H5, *grade factorization*, and it is not free: `grade_reads_outside`
is that round's witness of a grade reading a field the protected object does not
cover, flipping grade trust while every legitimacy clause stays silent. Here the
protected object is not a coordinate list but the authority in force, and
(W-index) is the requirement that the principal's grade be a function of it.

## 3. What this buys over the August 17 interface

That interface supplied non-capture: `Coupled(a,b) and L(a) = L(b) => Z(a) = Z(b)`
over a named advisor variation class. Three differences, and one of them is not
in this round's favour.

**Checkability.** Non-capture is a semantic property of a variation class, and
the procedural round established that no statistic of one realized trajectory
determines it. `G |-_B x` is a property of one record and one challenge and is
decided by finitely many stability judgments. That is a real improvement in what
`A` could come to be entitled to, and it is bounded by §3 of
`CROSS_PROCESS_INTERFACE.md`: in this realization each judgment costs a replay.

**Scope.** The Carroll round already found that non-capture's antecedent is
*false* on both laundering classes, because laundering runs through the reason
channel and so changes the licensed-reason trace. Derivability fires there.

**Coverage, in the other direction.** Access and coverage survive as independent
clauses catching things this interface does not — a withheld due reason is not a
succession defect and no axiom of the spine sees it. The composition remains a
conjunction.

## 4. The corrigibility shape, and the hypothesis it has no model for

```text
CorrigibleDeference                                            (prospective)

  Recognizes_A(G)  and  B |= LegitimacyInterface  and  G |-_B x
  Trust:            GradeTrust EX W_x eta,  (W-index)
  EffectiveAuthority: the principal's corrective capability is
                      preserved under every advisor policy in scope
  -----------------------------------------------------------------
  A has no strictly dominant preemption on the protected domain
```

The three inputs are the August 17 interface's own proposal —
`Legit + Trust + EffectiveAuthority => NoPreemption` — and the round can now say
which one is missing. It is the third. `ReachableCorrectiveControl`'s registered
refutations are that its capability predicate is satisfied by the advisor's
*leave* rather than against its opposition, so there is presently no formal
object standing for `EffectiveAuthority`. Legitimacy does not supply it and this
round does not attempt to: standing and effective causal access were separated by
the relational-scorekeeping bridge and shown independent in both directions.

So the corrigibility theorem is **statable and not provable**, and the obstacle
is named: a protected-capability predicate quantifying the advisor universally.
That is `PRIORITIES.md` item 22's fourth question, unchanged by this round.

## 5. The negative test: pretend Reflective Integrity does not exist

Delete `NormEvent`, `AnsRoot` and `ReasonOcc` from §2 and §4 and read what
remains.

**Can the consumer theorem still be stated?** Yes. `B |= LegitimacyInterface` and
`G |-_B x` are conditions on `(A, T, src, tgt, lic, rank, Chal, |=)`, and the
warrant register satisfies them with no ledger anywhere. Nothing in
`CertifiedDelegation` or `CorrigibleDeference` names an internal representation.

**Can the legitimacy premise be checked or proved in principle?** Yes, and the
cost is realization-dependent. A derivation is finite and canonical in every
realization. The stability judgments are a reachability query in the warrant
register and a replay in ours.

**Does `A` need to know `B`'s internal representation?** For the interface, no.
**For our realization's stability oracle, yes** — the honest answer is not the
desired one. A certificate's derivation compresses and its stability half does
not, because the challenge operator is neither monotone nor composable. `A` must
either hold `B`'s record, or challenge and be answered, or accept an attestation
and record that as trust.

**Does `A` need to endorse `B`'s future normative content?** No. The frame has no
content field, relabelling leaves derivability fixed, and `C11`, `C14` and `C33`
are records where recognition transports across a content change.

Three of the four desired answers, and the third qualified rather than met. The
qualification is a fact about *this* realization and not about the interface,
which is precisely the distinction the abstraction was built to make visible.

## 6. What the deference line would have to change

One field and one hypothesis, both small and both real.

1. **`W` acquires an index.** `W : A -> C -> P -> Q`, with `W_x` read off the
   authority in force. Everything else in `DelegationBridge.lean` is untouched:
   `valuation`, `gradeMargin`, `disagreementMass` and the two theorems take `W`
   as a parameter and never inspect it.
2. **(W-index) is stated as a hypothesis.** That the principal's grade is a
   function of the authority in force, and not of anything the advisor can write
   beside it.

Neither is a change to a registered statement — `delegation_bridge` is proved for
every `W` — so this is an addition rather than a revision, and it is the whole
of what stands between the interface and an actual consumption.

## 7. What this test does not establish

That `W` tracks anything worth tracking. `FINITE_MODEL_SKELETON.md` §8.5 declares
"**The relation between `v⁺` and `X`** — none", and legitimacy cannot supply it:
that is a claim about the principal's competence about the world. The round
leaves it exactly where the August 17 interface left it.

That the re-typing is enough. It makes the premise statable; whether the
resulting theorem is worth proving depends on the grade-to-quantity link the
programme decided to derive rather than assume, which is `PRIORITIES.md` Q2.
