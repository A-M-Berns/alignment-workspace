# Report — legitimate evolution and cross-process recognition

**Verdict: LEGITIMACY-THEOREM-COMPRESSED.**

Superseding `LEGITIMATE-EVOLUTION-TWO-CONSUMER-READY`. The succession calculus
was the scaffold: it found the right questions and the object underneath is
smaller. All ten conditions of the compressed verdict are met, and each of the
three attacks the dispatch named landed.

Deliverables are at
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/`.

---

## Deviations from the prompt

**One canonical theorem document, not a new one.** §24 offered
`LEGITIMATE_REPLAY.md` or `NO_LAUNDERING.md` and preferred compression;
`LEGITIMATE_EVOLUTION.md` was rewritten instead.

**`src/frame.py` and `src/warrant.py` are deleted rather than kept for
comparison.** §24 asks that rejected rules be preserved where informative. The
rejected *registers* are preserved and now run against the new theory; the
rejected *rules* are described in `COUNTERMODELS.md` with the process that killed
each. Keeping two live formulations of the same object would have violated the
present-ontology rule and doubled the surface for no evidential gain.

**§14's theorem numbering is not followed.** `T2 Legitimate Grounding` and `T3
Global No-Bootstrap` are one theorem plus a corollary here, because grounding is
the replay's own definition and the content is in no-laundering. §9's
*groundedness* is a definition, not a theorem, and is labelled one.

**§9's list of frontier exits is incomplete and the round adds a second.**
Tightening the audit context can remove an occurrence with nothing acting on it —
and can also **restore** one. That second direction is new this pass.

**The two-issuer question is dropped rather than answered.** §4 of the previous
dispatch had it; occurrence identity dissolves it, and the register has no
analogue to build.

---

## The final questions

**1. Was the stable-but-illegitimate-license counterexample valid?** That was the
previous pass and yes. This pass's first attack also landed:
`F^leg = raw_live ∩ Derivable` fails under illegitimate revocation, and worse than
suspected — the persistence theorem reported **no violation** while it happened,
because its hypothesis was "no exercise acts on it" and an exercise did. An
attacker with no legitimate authority could subtract from the enforcement target.

**2. What replaces it.** A legitimate replay:

```text
L(alpha, 0) = G
L(alpha, s+1) = apply(L(alpha,s), e_s) if Valid_alpha(L(alpha,s), e_s) else L(alpha,s)
```

A rejected edit is a no-op, so an unauthorized revocation removes nothing.

**3. One replay or a family?** A family, `L(alpha, s)`, on two independent
indices. Historical time is when the act happened; the audit context is what is
currently believed about whether its conditions were met. Changing the first is
normative revision; changing the second is a revised assessment of a revision.

**4. The local judgment.**

```text
Valid_alpha(L, e)  =>  grounds(e) subset Auth(L)      H3
                   =>  Permit(L, grounds(e), input(e), e)   H4
                   =>  ProvOK_alpha(e)                H6
```

`Valid` is a **parameter**; those are hypotheses on it, each with a countermodel.

**5. Does a grounded licence suffice?** No. `office.unauthorized_scope` is a
fiscal warrant legislating on safety with impeccable grounds and provenance, and
the previous calculus admitted it. `Permit` is required.

**6. `InputOK` versus `ExerciseOK`.** Whether the declared information is
authentic, versus whether this was an authentic exercise. A forgery fails the
first; duress fails the second; `office.forged_input` and
`office.coerced_exercise` fail different clauses. The interface fixes neither
answer — a constitution may declare that coercion does not invalidate.

**7. Does the theorem still need challenge survival?** No. It is gone from the
headline and Carroll excision realizes `ProvOK` if a realization wants it.

**8. What becomes of L3 and L3'?** Retired. They were conditions on a
challenge-stability relation that no longer appears. Their anti-laundering work is
done by `ProvOK` refusing the edit at issuance plus freshness; their pathologies —
non-monotonicity, non-composability — go with them, and reappear as the
intelligible fact that invalidating a repeal restores its target.

**9. The dependency-factorization law.** Two proposals with the same declared view
have the same verdicts. `office.hidden_admission_pair` refutes it for a
realization whose validity rules read a hidden variable.

**10. The effect-factorization law.** The same, for effects.
`cases.partial_effect_pair` is two records of equal length, same `tau`s, same
authority, same witness, same cited reason and settlement, differing only in an
**uncited** settlement that the schema reads. **This generalizes the previous
pass's pre-state condition**: the defect is not reading the pre-state, it is
reading state the record does not declare. A schema may read the whole pre-state
if the edit declares what it read.

**11. The adequacy hypothesis.** Every influence in `Xi` is one `ProvOK` can
refuse. Undischarged, and now the only hole of its kind.

**12. Is `Valid` semantic or verifier-relative?** Both, at two layers, and keeping
them apart is what §10 of the dispatch was right to press. `Valid` is semantic;
`Verify` is a checker; `verifier_sound` and `verifier_complete` are separate.

**13. Do consumers require completeness?** Asymmetrically, and this is the
sharpest new finding. A sound incomplete checker misses valid edits. Missing an
**issuance** is conservative — recognition declines something it should have
recognized. Missing a **disposal** is a hazard — an obsolete norm stays in the
enforcement target and force is applied without entitlement. So the two consumers
can share an interface and cannot share a checker.

**14. Finite grounding.** Every legitimate occurrence has a finite tree, leaves in
`G`, internal nodes accepted edits, historical index strictly decreasing.
Induction on the index from H3 and H2. Fails when H3 is dropped — checked.

**15. No laundering.** An occurrence a rejected edit proposed never becomes
legitimate, however often it is used downstream. Freshness plus the no-op. The
work is done by choosing occurrences over contents, and the pairing that makes it
substantive is `office.readoption`: the same content, adopted later by a clean
act, is legitimate.

**16. Noninterference.** Same declared view, same legitimate state, by induction
from H5. Raw histories may differ arbitrarily outside the view; an influence that
changes the declared input changes the view and is permitted to change the
outcome.

**17. Persistence at fixed audit context.** `o in L(alpha,s)` and no accepted edit
in `(s,u]` disposing `o` gives `o in L(alpha,u)`. This is the property the
previous object did not have.

**18. How later audit information retracts.** By replaying at a stricter `alpha`:
the invalidated edit becomes a no-op and everything grounded in what it issued
falls with it. No historical rule changes.

**19. Readoption versus laundering.** Occurrence identity. The rejected act's
occurrence and the clean act's occurrence are different objects with the same
content, and only the second is in the state.

**20. What deference consumes.** `o in Auth(L(alpha,t))`, plus the four things the
recognizer must accept. Its job is unchanged: to make `GradeTrust` a proposition
the advisor did not select. The kernel still cannot state it — `W` has no index.

**21. What traderization consumes.** `Norm(L(alpha,t))` and the lifetime it
induces.

**22. Which axioms survived unchanged?** In substance, two: strict-prestate
grounding, and base recognition — the latter now folded into "the replay starts at
`G`". Everything else was replaced, retired or dissolved.

**23. Which became realization-specific?** Challenge survival in both its forms;
the challenge set and its coverage predicate as a *frame* field (adequacy remains
abstract, the operator does not); unique issuance; the lifecycle entry and exit
axioms, which are now consequences of the replay rather than conditions on a
supplied view; and the account layer's two axioms, which are outside this object
entirely.

**24. Is pre-state-blindness still required?** Not as stated. It is a sufficient
condition for the real hypothesis, which is that the effect and the verdict factor
through what the edit declares. That is strictly weaker and strictly more
intelligible, and it is falsifiable in a way "the schema reads the pre-state"
never was.

**25. Is the theorem non-definitional?** Partly, and the honest breakdown is:
`G1` and `G4` are genuine inductions and each fails when its hypothesis is
dropped — checked. `G3` and `G5` are short, and the ontology did their work; their
defence is that they were false or missing in the previous object. `G2` is a
corollary and `G6` is true by the type. The substantive normative content is
entirely in `Permit` and `ProvOK`, which are parameters, and the round says so
rather than claiming the theorem settles what legitimacy requires.

**26. Short enough to be the compression target for the line?** Yes. Two types,
one fold, six hypotheses, six theorems, no challenge operator and no ledger.

**27. Stable enough for a Lean port?** Yes, and it is now the recommended next
step. Three passes were needed to get here and each found a false or missing
statement in the one before, which is the argument for having done them first.

---

## What this pass does not establish

No Lean and no registered claim, deliberately.

Adequacy is undischarged and has now survived three surrounding theories. Nothing
here computes the map from an influence to the edits it produced.

Neither consumer theorem is provable. Deference lacks an index on the grade and a
protected-capability predicate; enforcement lacks bounded-lifetime liability.

`Permit` and `ProvOK` are opaque parameters. The interface requires they be
consulted and constrains neither, so a constitution with a permissive `Permit` is
accepted by every theorem here.

Reflective Integrity has no jurisdiction on an authority, so H4 is vacuous on a
record whose authority is a bare `PAuth`. That is a gap the abstraction exposed
and this round did not fix.

The account layer left the headline in the previous pass and was not re-examined
here.

---

## Outstanding maintainer actions

1. **Rule on whether the deference kernel's grade acquires an index.** In
   `DECISIONS.md`'s *Awaiting the author* since the first pass; unchanged, and the
   premise it would attach to is now stronger. *Turns on:* whether the deference
   line is being restarted, and what a paper needs.

2. **No other item is reserved.** The three forks this pass faced it adopted, as
   dated `DECISIONS.md` entries marked agent-decided and reversible: the
   legitimate state is replayed rather than filtered; legitimacy is judged locally
   rather than by outcome survival; grounding an authority is not authorizing an
   exercise.

---

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; four dispatches — the round, an addendum sent mid-round, a repair pass, and this compression pass |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-25 |
