# Report — legitimate evolution and cross-process recognition

**Verdict: LEGITIMATE-EVOLUTION-TWO-CONSUMER-READY.**

Superseding the first pass's `LEGITIMATE-EVOLUTION-CONSUMABLE`, which the repair
pass withdrew: the headline theorem it shipped was **false**, not merely
under-proved, and `warrant.stable_but_illegitimate_register` is the frame that
shows it.

All seven conditions of the verdict are met. The licence-grounding defect is
repaired; the no-bootstrap theorem holds over derivations rather than
provenances; lineage existence is free of unique issuance and a two-issuer
register proves the separation; challenge coverage is a typed hypothesis with a
countermodel; exercise identity is prosecuted and the answer is that it relocates
the pre-state condition rather than removing it; the interface exports a
legitimately live frontier with two projections; and both consumers can read it
with no Reflective Integrity vocabulary.

Deliverables are at
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/`.

---

## Deviations from the prompt

**The theorem numbering is not §14's.** `T2 Legitimate Grounding` and `T3 Global
No-Bootstrap` collapse into one result, because the grounding claim is the
derivability relation's own definition and the content is entirely in the
no-bootstrap conclusion; retaining both would have been the padding §14 warns
against. `T6` remains an axiom plus two theorems and `T7` is a document.

**§9's *groundedness* is not proved and cannot be.** `x in F^leg_t -> G |- x` is
true by the definition of the frontier as `live ∩ Derivable`. It is listed as a
definition rather than dressed as a theorem.

**§9's list of exits is incomplete and the round adds one.** A norm can leave the
legitimate frontier with nothing acting on it, by the arrival of a challenge that
reaches its lineage. That is `T4'` and it is a consequence of quantifying over
challenges, not a defect.

**The first pass's `LegitCert(x0, x)` is over a base set and now also carries a
coverage claim.** A certificate that does not name what it is a certificate
against is not a weaker certificate, so `certify` returns nothing when coverage
fails.

**Two `DECISIONS.md` entries from the first pass are re-ruled**, not amended in
place: legitimacy parents are not the objects an exercise acts on, and an
exercise is individuated by what it does. A third is added for keeping liability
out of legitimacy.

---

## The final questions

**1. Was the stable-but-illegitimate-license counterexample valid?** Yes, and it
is stronger than the review supposed. It is not a proof gap: on
`warrant.stable_but_illegitimate_register` the spine holds, `w:y` is derivable,
and `w:tainted` — issued by a challenged exercise — sits in `w:y`'s provenance.
So the **conclusion** of the no-bootstrap theorem was false. The invalid step was
"each such `z` is itself derivable", which was unavailable for a licence:
derivability recursed only through parents while provenance ran through licences
too.

**2. The repaired definition.**

```text
G |-_q y   :=   y in G,  or
                exists t.  parents(t) union {lic(t)}  subset  { z : G |-_q z }
                       and y in tgt(t)
                       and q |= t
```

One clause *fewer* than the old rule, not one more: stability of the licence is
now a consequence of `T2a` rather than a hypothesis.

**3. Are licences recursively required to be legitimately grounded?** Yes.
`grounds(t) = parents(t) ∪ {lic(t)}` and all of it must be derivable, so the
requirement recurses to the base.

**4. The role of `src` after prosecution.** It was doing two jobs and is now two
fields. `affected(t)` is what the exercise acts on and constrains nothing;
`parents(t)` is what its issue inherits entitlement from and must be derivable,
all of it. `warrant.cleanup_register` decides it: a regulator revoking a
fraudulent warrant and granting a proper one inherits from its charter, and the
old rule made the replacement illegitimate. In a record a cleanup is a revocation
plus a separate creation, and the creation inherits from its licence alone.

**5. Does the theorem follow now?** Yes. Every `z` in a certified derivation's
ancestry is derivable by construction of the repaired rule, so `T2a` gives
`q |= z`, `L3'` gives a stable issuer and `L4` puts it outside `Chal(q)`. Checked
on eight frames, with the rejected rule failing the same standard on the frame
that separates them.

**6. Does lineage existence require unique issuance?** No. `provenance` closes
over every issuer, `minted_by` returns the first rather than raising, and
`thm_finite_lineage` is clean on a register where `L2'` fails. `L2'` is out of the
checked spine.

**7. What unique issuance buys.** Canonicity, and only that: the provenance is
determined by the target, so a process cannot present a flattering route. Without
it a certificate exhibits *a* route and the recipient learns that this route is
clean, not that every route is — which is the correct thing to learn, since on
`warrant.two_issuers_register` a challenged issuer sits in the route-blind
provenance while the authority is perfectly legitimate by the clean route. That
register is also why the no-bootstrap theorem had to move from provenances to
derivations.

**8. The right abstract identity of an exercise.** Effect-sensitive: an act that
does something else is not the same act. Chosen on semantics, because the
prosecution shows it does not buy a free hypothesis.

**9. Does the realization still need pre-state-blind schemas?** Yes, and this is
the pass's most surprising finding. The hypothesis **moves rather than
vanishing**:

| | L3 | L3' |
|---|---|---|
| event identity | needs pre-state-blindness | free |
| effect identity | free | needs pre-state-blindness |

`C28` alone would have said otherwise — it fails L3 under event identity and
satisfies the whole spine under effect identity. `cases.partial_effect` is the
general case: one `Create`, two payloads, only the second reading the pre-state,
so the effect changes while one issued authority does not. Failure condition D is
therefore answered negatively: pre-state-blindness is not an artefact of a coarse
map, it is what makes the challenge operator's action on effects determinate.

**10. The coverage hypothesis.**

```text
ThreatModel = (Xi, depends : Xi -> Pfin(T))
Coverage    :  forall xi in Xi. exists q in Q. depends(xi) subset Chal(q)
```

`certified_against` returns the empty set when it fails and `certify` returns no
certificate at all.

**11. What the theorem is relative to.** A supplied threat class. `depends` is a
fact about the world and about a process's provenance discipline, and nothing
here computes it. A record's own declared episodes generate a threat model it
covers by construction, which is the ceiling on self-certification and is not a
solution to provenance completeness.

**12. The frontier.** `F^leg_s = live[s] ∩ Derivable`, with `live` supplied by
the realization under two axioms — nothing comes into force without an act,
nothing falls out of force on its own.

**13. Persistent until legitimately changed.** `T4`, from the exit axiom:
derivability does not move with the lifecycle index, so only the live view can
change, and it changes only through an exercise acting on the authority. With
`T4'` those are the only two exits.

**14. What the deference consumer receives.** `x in AuthorityView_s` — the
authority legitimately in force when the grade is read — under a stated threat
model. Its job is to make `GradeTrust` a proposition the advisor did not select.
The kernel still cannot state it: `W` carries no index, and the required change is
one field plus one hypothesis, neither revising a registered statement.

**15. What the traderization consumer receives.** `NormView_s` and the lifetime it
induces, under a consumer-supplied classifier. `cases.force_bearing` is the record
where that is a real set: one injunction legitimately superseded, one manufactured
beside it, and the frontier holds the successor while the manufactured one is live
and outside it. That distinction is precisely what a projection of `Std_t` cannot
make.

**16. The missing liability theorem.** Bounded-lifetime liability: that the charge
allocated to one norm over its own legitimate lifetime is bounded by an allowance
attached to it at issuance, and that such allowances are summable. Level I bounds
the **total** across all norms and all time; nothing bounds a particular norm's
own lifetime. It needs an allowance minted with the norm at the `MINT` seam,
charging against the norm's own episode, and either a finite lifetime or a
decaying allocation — the per-date deficit provably does not fall with increasing
settlement. Filed as `PRIORITIES.md` item 69.

**17. Is answerability part of legitimacy?** No, and the pass did not reverse the
first pass's finding — it strengthened the evidence by realizing the same shape in
a register with no record. A delegation nobody answers for has a clean spine, a
derivable authority and an account outstanding forever. It is a separate
consumer-visible refinement, and it earns two constructors the authority graph
cannot express plus the one clause that can fail with the authority side clean.

**18. Can a norm be legitimate but unenforceable?** Yes, and the architecture
already says so rather than this round stipulating it. Under the default
exhaustion policy `compile_safe_force` withholds force and "the endorsement keeps
its normative standing". It is not a corner case: the inertness dichotomy puts
every contentful injunction in the charged branch, and no normative source in the
repository is shown to have summable liability.

**19. Can both consumers quantify over external implementations?** Yes for the
interface — every hypothesis is a condition on the frame, and a register of
offices satisfies them with no ledger. **No for our realization's stability
oracle**, unchanged by this pass: `A` must hold `B`'s record, challenge it
interactively, or accept an attestation.

**20. Stable enough for a Lean port?** Yes, and that is now the recommended next
step — `PRIORITIES.md` item 66, restated. The repair pass is what makes it
dispatchable: porting the first pass's rule would have formalized a false
statement. The remaining open items are consumer-side or acknowledged-external and
none of them changes a type in the spine.

---

## What this pass does not establish

No Lean and no registered claim, deliberately. The realization theorem is a paper
argument from Reflective Integrity's own statements, checked on finite records,
and those statements are themselves unregistered.

Coverage is explicit and undischarged. An external process satisfying every axiom
with a challenge set naming almost nothing is certified, and the Carroll round's
unlinked-episode witness is now a coverage failure with a type rather than a
prose caveat. Nothing here says how a process comes by an adequate challenge set.

Neither consumer theorem is provable. Deference lacks an index on the grade and a
protected-capability predicate; enforcement lacks bounded-lifetime liability. Both
are named, both sit on the consumers' side of the boundary, and neither is a
defect in the interface.

The account layer's abstraction is the weakest part of the interface.
`warrant.py` realizes it, but the realization was written to match rather than
found independently, so it is the one component not tested by a system with its
own reasons for the same shape.

The spine is not shown minimal. `L2'` is out; `L5`-`L8` are four bookkeeping
axioms a better factorization might do with two.

---

## Outstanding maintainer actions

1. **Rule on whether the deference kernel's grade acquires an index.** Already in
   `DECISIONS.md`'s *Awaiting the author* from the first pass; unchanged by this
   one, and the repair makes the premise it would attach to stronger rather than
   different. *Turns on:* whether the deference line is being restarted, and what
   a paper needs.

2. **No other item is reserved.** The three forks this pass faced it adopted, as
   dated `DECISIONS.md` entries marked agent-decided and reversible: legitimacy
   parents are not the objects acted on; an exercise is individuated by what it
   does; legitimacy does not mention liability.

---

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; three dispatches — the round, an addendum sent mid-round, and this repair pass |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-25 |
