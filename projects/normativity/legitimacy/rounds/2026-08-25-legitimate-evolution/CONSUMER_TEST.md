# The first consumer: the deference machinery

Status: **prosecution record; unregistered.** Cited by path against this branch's
base.

---

## 1. The consumer

| statement | where | what it needs |
|---|---|---|
| `delegation_bridge` | `lean/Workspace/Deference/Contrib/DelegationBridge.lean:71` | `GradeTrust EX W eta`, `hp`, `J` pointwise grade-maximal |
| `GradeTrust EX W eta` | same file, line 52 | `forall x pi. abs (EX x pi - W x pi) <= eta` |
| `canCorrectFuture_iff` | `ReachableCorrectiveControl.lean:306` | a finite transition system |

`FUTURE_AGENT_SPEC.md`: "**the authorisation relation has to be in the type.**"

## 2. Which statement the bridge actually needs

This is the question this pass forced, and the answer changed the substitution.

```text
Grounded(o)    o was legitimately issued
Live_t(o)      o is in force at t
```

The grade `W_o` is the judgment `A` is deferring to **now**. An authority that was
legitimately created and has since been validly revoked is not one whose later
judgment `A` should treat as authoritative. So the premise is `Live_t(o)`, not
`Grounded(o)`.

That matters because they have different costs. `Grounded(o)` has a finite
certificate — a grounding tree. `Live_t(o)` does not: it is history-sensitive and
`A` must replay the prefix, hold a commitment-and-delta proof, or accept an
attestation. `CROSS_PROCESS_INTERFACE.md` §3.

**The previous pass had this wrong in two ways at once**: it offered a tree as the
certificate and it said a sound checker sufficed. A tree does not establish
currentness, and a sound checker can retain a revoked authority.

```text
CertifiedDelegation                                            (prospective)

  Recognizes_A(G), and A accepts (Auth, Valid, alpha)
  B's process satisfies S1 and S2
  o in Auth(L_t)                            the legitimacy premise
  (W-index)  W_o is a function of the authority in force
  GradeTrust EX W_o eta
  hp, and J pointwise W_o-maximal
  -----------------------------------------------------------------
  valuation p EX sel + gradeMargin p W_o J sel
      - 2 * eta * disagreementMass p J sel   <=   valuation p EX J
```

## 3. What the premise does and does not buy

**Does.** It makes `GradeTrust` a proposition the advisor did not select: by the
theorem, `o`'s whole lineage is grounded in a base `A` accepts, and by Corollary 2
nothing a rejected edit proposed is in it.

**Does not.** It says nothing about `W_o` tracking anything worth tracking —
`FINITE_MODEL_SKELETON.md` §8.5 declares "**The relation between `v⁺` and `X`** —
none".

**Costs more than the previous pass thought.** `A` must either replay `B`'s prefix
or accept an attestation of currentness. The compression made the *lineage* half
cheaper and made the *currentness* half visible; the previous formulation hid the
second inside the first.

## 4. Corrigibility

```text
CorrigibleDeference                                            (prospective)

  o in Auth(L_t) under B
  Trust:              GradeTrust EX W_o eta, (W-index)
  EffectiveAuthority: the principal's corrective capability is preserved
                      under every advisor policy in scope
  -----------------------------------------------------------------
  A has no strictly dominant preemption on the protected domain
```

Statable, not provable, and the missing hypothesis is unchanged:
`ReachableCorrectiveControl`'s registered refutations mean there is no formal
object standing for `EffectiveAuthority`.

## 5. The negative test: pretend Reflective Integrity does not exist

**Can the theorem be stated?** Yes. Every hypothesis is a condition on a frame,
and a constitution satisfies them.

**Can the premise be checked in principle?** The lineage half, cheaply and
finitely. The currentness half, only by replay or by a commitment scheme nobody
has built.

**Does `A` need `B`'s internal representation?** No for the interface. For the
currentness half `A` needs `B`'s trace and semantics, which is more than the
previous pass claimed and is the honest position.

**Does `A` need to endorse the content?** No. The kernel never inspects content;
`Permit` may, and that is `B`'s semantics, not `A`'s endorsement.

## 6. What the deference line would have to change

Unchanged: index `W` by the authority in force, and state that the grade is a
function of it. Neither revises a registered statement.

## 7. What this does not establish

That currentness is affordable. It is the open interface question and this pass
sharpened it rather than solving it.

That `W` tracks the quantity that matters, or that the resulting theorem is worth
proving — `PRIORITIES.md` Q2.

---

## What the Due bridge adds, and what it still does not

Added by this pass. The package can now state the thing deference actually wants:
a successor process is not merely genealogically descended from a legitimate one,
but any represented reason **it itself** recognizes as demanding treatment is in
its answerability dynamics, and can leave only along a resolution path. That is
D1 composed with the continuity theorem, and the previous package could not say
it -- a process satisfying every premise could recognize an obligation by its own
semantics and never enter it.

Unchanged. Deference needs *current* authority and a grounding tree certifies
origin, so the current-state certificate is still missing and this pass did no
work on it.

Not obtained, and worth saying plainly: D1 is a premise, and Reflective Integrity
cannot discharge it. A deference consumer reading an RI record gets the continuity
half and not the realization half.
