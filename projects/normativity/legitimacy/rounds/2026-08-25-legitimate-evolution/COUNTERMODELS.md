# Prosecuting the hypotheses

Status: **prosecution record; unregistered.** Every entry names the process that
decides it and the test that runs it.

The first five sections each replaced something the round had already shipped and
tested. Three of them were decided by a constitution and its gazette rather than
by a record, because Reflective Integrity's admission preconditions make the
alternatives indistinguishable inside our own architecture.

---

## 1. The legitimate state cannot be the raw lifecycle filtered

**`office.rogue_revocation`.** A norm is issued cleanly. A doubted act grants a
rogue authority. An act under that rogue authority revokes the norm.

```text
the rogue authority   never legitimate          — correctly refused
the raw process       has removed the norm
raw ∩ derivable       has removed the norm      — wrong
legitimate replay     keeps the norm            — right
```

The previous object was `F^leg = live[s] ∩ Derivable`, and it lost the norm
because *something* in the raw process removed it. Its persistence theorem
reported no violation while this happened, because the theorem's hypothesis was
"no exercise acts on it" and an exercise did — one with no legitimate authority
at all.

So the previous branch established **persistent until something changes it**, not
*persistent until legitimately changed*, and for the enforcement consumer that is
the difference between a target and a suggestion: an attacker with no authority
could remove a norm from what gets enforced.

The repair is to reconstruct rather than filter. A rejected edit is a **no-op**,
so a revocation nobody was entitled to make does not remove anything.

## 2. A grounded authority is not an authorized exercise

**`office.unauthorized_scope`.** `w:fiscal` is granted cleanly and holds only over
fiscal matters. The act using it to legislate on safety has impeccable grounds
and impeccable provenance.

```text
grounds ⊆ Auth(L)     true
ProvOK                true
Permit                false
```

The previous calculus admitted it. It required an exercise's licence to be
derivable and never asked what the licence was *for*, so it established authority
provenance and not legitimacy of the particular exercise.

`Permit(L, B, I, e)` is the narrowest repair: a parameter the interface requires
be consulted, able to express jurisdiction, scope, consent conditions, amendment
rules and procedural conditions, and saying nothing itself about what any of them
should be.

**Where this bites the realization.** Reflective Integrity's `PAuth` carries a
`SchemaCode` and no domain, so `permit` is the identity on a record whose
authority is a bare `PAuth`. That is a gap in the architecture the abstraction
exposes, and `LEGITIMATE_EVOLUTION.md` §8 names it rather than letting H4 look
discharged.

## 3. Legitimate influence does not require outcome survival

**`office.persuasion`.** Alice has authority to revise policy. Bob argues. Alice
revises, relying on the argument. Remove the argument and the edit does not
happen.

Under challenge survival that counts against the edit. Under the local judgment
it counts for nothing: the question is whether prior legitimate authority
permitted this exact edit given this declared input, and it did.

This is a **strict reduction in what the theory refuses**, and it is the one the
Carroll round predicted when it called its criterion "conservative in the
direction of refusing". A legitimacy theory that cannot let an agent be persuaded
is not describing the learning the programme exists to describe.

**What it costs.** A counterfactual test can in principle notice a dependence the
record does not declare; a declared-input test cannot. **H5** is the hypothesis
that makes that safe, and §6 is where it fails.

## 4. Rejected authority never rehabilitates, and identical content is not poisoned

**`office.laundering`.** A doubted grant used downstream three times. Nothing is
accepted; the legitimate state is the base.

**`office.readoption`.** The same policy content proposed twice — once under the
doubted grant, once by the charter on a clean finding. The first occurrence is
never legitimate; the second is; the content is untouched.

```text
illicit occurrence   n1.0    rejected
clean occurrence     n2.0    legitimate
same content         n:P     both
```

This is why the ontology is occurrences. A theory tracking contents would have to
either poison `n:P` globally — refusing later independent adoption, which is the
learning case again — or let downstream use rehabilitate it.

## 5. Unique issuance dissolves

The previous branch spent a section on whether lineage existence needs unique
issuance, built a two-chancery register to separate existence from canonicity,
and restated the no-bootstrap theorem over derivations to avoid it.

Under occurrence identity there is nothing to separate: an occurrence carries the
index of the edit that issued it, so two edits cannot issue one occurrence and no
axiom says so. **H2** reports any attempt, and
`TestTheCompressionIsNotDefinitional` breaks freshness deliberately to check that
it is doing work.

The earlier register has no analogue to build, which is the cleanest evidence
that the earlier question was an artefact of the earlier object.

## 6. Factorization, and the two ways it fails

**Admission.** `office.hidden_admission_pair` — one gazette, two constitutions,
a hidden variable the gazette does not report and the validity rules consult. The
declared views agree at every step and one replay admits the act while the other
refuses it.

**Effect.** `cases.partial_effect_pair` — two records of the same length, same
`tau`s, same authority, same witness, same cited reason, same cited settlement.
They differ only in an **uncited** settlement, and the minting schema reads it, so
one issued occurrence carries a different payload.

```text
declared views       identical at every step
verdicts             identical
effects              differ
```

Both are refused by **H5**, and the positive control `office.clean_pair` passes.

**This is the general form of the pre-state condition.** The previous branch
concluded that pre-state-blindness was required under either exercise identity
and treated it as a fact about schemas. It is not about the pre-state: the defect
is reading state the record does not **declare**. A schema may read the whole
pre-state provided the edit declares what it read; a schema reading one uncited
settlement breaks the theorem. That reformulation is what makes the hypothesis
falsifiable rather than a coding standard.

## 7. Two failures of provenance that are not one

**`office.forged_input`** — the declared information is a forgery. `InputOK`
fails, `ExerciseOK` holds.

**`office.coerced_exercise`** — the information is authentic and the act was made
under duress. `ExerciseOK` fails, `InputOK` holds.

Both are refused and they fail different clauses. The interface fixes neither
answer: a constitution may declare that coercion does not invalidate, and the
theorem accepts it. What is required is that whatever the rules treat as relevant
to authentic exercise crosses the interface.

## 8. Coverage is still a hypothesis nobody discharges

**`office.laundering` at a context that doubts nothing** accepts everything and
certifies the manufactured permit. The threat model refuses it:

```text
Xi = { xi:campaign -> the edits it produced }
H6 adequacy   uncovered influence
```

and the audited context covers it.

A record's own declared episodes generate a threat model its provenance covers by
construction. That is the ceiling on self-certification, and it is unchanged by
this pass: nothing here computes `depends`, and a recognizer worried about an
influence the record does not record must supply its own threat class, against
which the record may simply fail.

## 9. Soundness is not enough for one of the two consumers

**`office.repealable`** with a checker that declines one valid edit.

```text
missed a valid issuance    the norm is absent   — conservative, and safe
missed a valid repeal      the norm is present  — an obsolete norm is enforced
```

So the consumers have different requirements. Recognition can run on a sound
under-approximation: it will refuse to recognize things it should have
recognized, which is a cost and not a hazard. Enforcement cannot: the
under-approximation *keeps* things in the target, and a missed repeal is force
applied without entitlement.

**`Valid` is semantic and `Verify` is a checker**, and the interface keeps them
apart for exactly this reason. `verifier_sound` and `verifier_complete` are
separate functions and `missed_disposals` is the one enforcement must watch.

## 10. What no entry above claims

That the hypotheses are correct. Each is a condition the round wrote, and the
substantive normative content sits in `Permit` and `ProvOK`, which are parameters
the interface does not constrain.

That the theorems are deep. G3 is a short induction whose work was done by
choosing occurrences over contents; G5 is two lines. The defence is that they
were *false or missing* in the previous object, that each fails when its
hypothesis is dropped — checked — and that G1 and G4 are genuine inductions over
the edit history.

That coverage is solved. §8 is the largest remaining hole and it survives every
reformulation this round has tried.

That the account layer has been re-examined. It left the headline in the previous
pass and this pass did not put it back or test it further.
