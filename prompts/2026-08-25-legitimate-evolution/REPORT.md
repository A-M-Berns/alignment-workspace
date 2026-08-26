# Report — Grounded Replay

**Verdict: GROUNDED-REPLAY-KERNEL-STABLE.**

Superseding `LEGITIMACY-THEOREM-COMPRESSED`. The replay object survived; four of
the things built on it did not.

Deliverables are at
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/`.

---

## Deviations from the prompt

**No separate `EditId`.** §2 offered `Occ = (issuer, slot)` with time beside it.
The trace is a list, so position is identity and order at once and the second
index buys nothing. The hole §2 identified was real; the repair is smaller than
proposed.

**`Xi` is not a field of anything.** §12 asked for a structural theorem
mentioning no threat class and §7 for coverage to remain explicit. Coverage is a
boolean the extraction must justify (`ProvComplete`), and the threat class it is
relative to is named in prose rather than modelled — the round could not state an
adequacy condition worth modelling, which §7 permits.

**`office.py` carries the semantics as well as the non-record realization.** §20's
decomposition wants them separate. They are separate *layers* and one file, since
the semantic definition and the constitution that instantiates it are read
together; `replay.py` is the boundary that matters and it is clean.

**Three earlier verdicts are now withdrawn in the record**, not just superseded:
`LEGITIMATE-EVOLUTION-CONSUMABLE`, `TWO-CONSUMER-READY` and one substantive claim
of `COMPRESSED` (§3 below).

---

## The final questions

**1. Is G1 false because empty ground sets are allowed?** Yes. `office.ex_nihilo`:
prior grounding holds vacuously, the edit is accepted, and the occurrence it
issues has no tree with leaves in the base. The conclusion is false on a frame
satisfying every stated hypothesis.

**2. The minimal repair.** `S2`: an accepted edit that *changes the state* has a
non-empty ground set. Not "every valid edit" — a no-op needs no authority. The
two halves are consumed separately: grounding needs it of edits that issue,
persistence of edits that dispose.

**3. Was historical time being used as identity?** Yes, and it was a free field,
so two edits at one time issued the same occurrence and the replay applied the
first twice.

**4. The freshness property required.** Unique **birth**: no two edits issue one
occurrence. Not unique issuance of a content — `office.readoption` issues one
content twice and must. Now definitional, since positions in a list are unique.

**5. Does sound under-approximation preserve `AuthorityView`?** **No.** A checker
that misses a valid revocation keeps the revoked authority. It does not
under-approximate the state; a missed disposal makes it strictly larger.

**6. Does it preserve `NormView`?** No, for the same reason, and the stale
authority then admits a norm the semantics never did.

**7. The weakest sufficient checker relation.** Agreement along the trace:
`Check(L_t, e_t) ⟺ Valid(L_t, e_t)` at the states the **semantic** replay
reaches. Weaker than global extensional equality — a checker wrong at every
unvisited state still simulates, and there is a test for that — and strictly
stronger than either one-sided condition. It gives `Lhat = L` by induction, hence
both projections. A projection-specific weakening exists and needs `Permit` to
factor through the projection; stated, not claimed.

**8. What a grounding tree certifies.** That the occurrence was legitimately
issued: a finite lineage of accepted edits back to the base, positions strictly
descending.

**9. What it fails to certify.** That the occurrence is in force. A tree is built
from grounds and disposals are not grounds, so it structurally cannot name the
revocation that would defeat it.

**10. Is a current-state certificate history-sensitive?** Yes, necessarily.
Replay the prefix, or hold a state commitment plus a proof of the delta, or accept
an attestation. Nothing here builds the second.

**11. Should `Valid` be defined?** Yes. Keeping it primitive left it free to
reject a grounded, permitted, provenance-adequate edit, and nothing needed that.

**12. The definition.**

```text
Valid_alpha(L,e) := grounds(e) ⊆ Auth(L)
                  ∧ (changes(L,e) → grounds(e) ≠ ∅)
                  ∧ ProvComplete_alpha(e)
                  ∧ Permit(L, e, ProvView_alpha(e))
```

**13. What descriptive provenance does.** Records what happened: which findings
entered, whether a signature was forged, whether the actor was coerced.

**14. What `Permit` does.** Decides what those facts mean, plus jurisdiction and
scope. The split is what lets persuasion be **recorded and permitted**; the
previous provenance predicate could only refuse an influence.

**15. What remains open in completeness.** The whole of it. The round tried to
state an adequacy condition that is non-circular, not "refuse every influence",
compatible with permitted persuasion, and falsifiable by the existing fixtures,
and did not find one. It is an explicit epistemic assumption on the extraction and
is not a premise of the kernel.

**16. Should the edit contain its frozen effect?** Yes. `apply` is then a function
and the fold is deterministic.

**17. What becomes of hidden-effect factorization?** It moves below the boundary.
Noninterference is extraction factorization composed with fold determinism; the
second is definitional. A record whose effect reads an uncited settlement produces
a different **trace**, which is a conformance failure, not a legitimacy premise.

**18. Is H5 a legitimacy hypothesis?** No — a realization theorem, and it can fail
two ways: a different trace, or a different validity relation.

**19. Is G6 false or vacuous?** Both. The check replayed the unchanged process, and
permission reads content once a live policy can ban a scope. Deleted, replaced by
a no-conservativity statement that follows from the kernel never inspecting
content.

**20. Must `Auth` and `Norm` be a partition?** No. The kernel needs one predicate;
the enforcement projection lives in the realizations; nothing requires them
disjoint or exhaustive, and a norm can bear on a permission judgment without being
an authority.

**21. The minimal structural premises.** Two: prior grounding, and no ex nihilo.
Each has a countermodel where the theorem's conclusion fails, and they fail on
different frames.

**22. Should the theorem range over live or admitted?** **Admitted.** An
occurrence validly issued and validly disposed keeps its lineage and stops being
in force.

**23. Grounded, admitted, live.** `Live ⊆ Admitted`, strictly. On a fixed trace
`Grounded = Admitted` — a lineage is built from that trace's accepted edits, so
having one and having been issued by one coincide. The independent distinction is
admitted against live.

**24. Which does deference consume?** `Live`. The grade is the judgment being
deferred to now, and an authority since revoked is not one. So deference does
**not** get a finite certificate, which is a change from the previous pass.

**25. Which does traderization consume?** `Live`, unchanged.

**26. What remains of H1-H6?** H1 and H2 are definitional under the new types; H3
and H4 became `S1` and part of the semantic definition; H5 is extraction; H6 is
`ProvComplete`, an assumption. Two premises remain.

**27. What remains of G1-G6?** One theorem and three corollaries. G4 is
extraction plus fold determinism; G6 is withdrawn.

**28. Stable enough for a Lean port?** Yes. Two types, one fold, two premises, one
induction, three corollaries; every premise prosecuted; the semantic,
realization and computational layers separate and each with its own failures.

---

## What this pass does not establish

No Lean and no registered claim, deliberately.

Provenance completeness is undischarged and has now survived four surrounding
theories, which is the best evidence available that it is not an artefact of any
of them.

`Permit` is opaque. A constitution with a permissive one satisfies every theorem
here, and every substantive normative question lives in it.

A current-state certificate does not exist. Both consumers need one and the round
sharpened the problem rather than solving it.

Reflective Integrity has no jurisdiction on an authority, so the permit clause is
nearly vacuous on a record. `PRIORITIES.md` item 67, deliberately not repaired.

The theorem is short. An induction over a list; two corollaries are two lines. The
contribution is the object, the exact premises, and four formulations' worth of
evidence about what fails.

---

## Outstanding maintainer actions

1. **Rule on whether the deference kernel's grade acquires an index.** In
   `DECISIONS.md`'s *Awaiting the author* since the first pass. This pass sharpens
   what it would attach to: the premise is `Live_t(o)`, and supplying it needs a
   replay or an attestation rather than a certificate. *Turns on:* whether the
   deference line is being restarted, and what a paper needs.

2. **No other item is reserved.** The three forks this pass faced it adopted, as
   dated `DECISIONS.md` entries marked agent-decided and reversible: occurrence
   identity is trace position; semantic validity is defined rather than
   constrained; a grounding certificate is about origin rather than currentness.

---

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; five dispatches |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-25 to 2026-08-26 |
