# Report — traderized enforcement, reconciliation pass

**Prompt author model:** GPT-5.6 Sol (OpenAI). **Executor model:** Claude Opus 5
(Anthropic). **Date:** 2026-08-17. Dispatch: `PROMPT-reconciliation.md`.

Two claims of the second pass are withdrawn against review counterexamples, both
reproduced exactly and both kept as regressions. The abstract safety theorem is
unchanged. The reconciliation finds one hole in the paper's intended architecture,
and it is not small.

## Verdicts

**Paper-fit verdict: the force channel fits; the semantic channel has a hole.**
Nine of the fourteen intended spine steps survive, two survive restated, one is
strengthened, one is weakened and case-split, and three are open. The one that
blocks the narrative is Coverage.

**Force verdict: unchanged and intact.** The compiler, the enforcement inequality,
the conformance modulus with an adaptive intensity rule, and the totality
asymmetry against a directly constrained market maker all stand.

**Safety verdict: `B < ∞ ⟹ non-exploitation with bound 1 + B`, unchanged.** The
*sufficient conditions* for bounding `B` are weaker than claimed: the surviving
per-date bound is `(ε_t + C_t)·‖d_t(W)‖₁/δ_t`, in which the intensity does not
cancel and a tighter promised tolerance raises the ceiling.

**Exactness verdict: case-split by geometry, and not by interior versus empty
interior.** Available for regions with an interior *and* for regions sitting on a
cube face — settlement pinning is the easy case. Unavailable for a region strictly
inside the open cube with empty interior, where a coherence relation lands. The
proved theorem is one-dimensional; *face-solidity* is the conjecture.

**Deductive recovery verdict: clean.** `Ω_t^live = PC(D_t)` for the
coherence-polytope constraint, hence the generalized criterion is `LIC_D`. What is
recovered is the semantics; `D` remains in `Budgeter` and in the definition of
exploitation, and the paper should say traderization generalizes deduction's
**operative-force role**.

**CL verdict: Liability settled, Coverage missing.** Liability is the force-side
condition the algebraic proof consumes, and it is proved sufficient. Coverage's
job is *not* to make that proof go through — it is to stop the assessment set
being chosen to satisfy it. Its statement is what this pass could not produce.

**Editorial verdict: one paper, with force as a self-contained module.** By
theorem dependency: the force results mention no criterion, no assessment set and
no deductive process, so they are liftable; the safety result composes `lem:mm`
and `lem:tfdom` with an assessment set, and that coupling is the paper.

## Corrections made

**Withdrawn: the intensity-free liability ceiling** `L_t(W) ≤ C_t · max_j d_j(W)`,
and Corollary 12's summability condition built on it.

The failed step is the one review named: *"at equilibrium the enforcement position
offsets the ordinary one, so its size is `C_t` whatever the intensity."* That
holds only where the contract forces the aggregate to vanish. Positive slack does
not force it — the contract bounds the aggregate's cube maximum gain, leaving
residual enforcement demand nothing cancels. The counterexample reproduces
exactly, with the ordinary position at **zero**: `C = 1/100`, `ε = 1/8`,
`δ = 1/10`, intensity `27/2`; at `P = 51/100` the violation is `1/100`, the
position is `27/200` short, `max_gain = 1377/20000 ≤ 1/8`, conformance holds, and
the liability is `1323/20000` against a ceiling of `1/200`.

Replaced by `L_t(W) ≤ ∑_j β_j g_j d_j(W) ≤ (ε_t + C_t)·‖d_t(W)‖₁/δ_t`. The
pointwise form gives `27/400` on the counterexample against an actual `1323/20000`
— tight. **The direction reverses**: conformance and liability are traded against
each other, so the second pass's correction of the first pass was itself wrong,
and the first pass's instinct was closer.

**The safe non-world-inclusive trajectory survives.** Under the corrected bound
its cumulative liability is bounded by `20 + 5/3` rather than `2`. Convergence is
what the safety theorem needs, and it converges.

**Withdrawn: exactness impossibility for every empty-interior region**, and with
it the claim that settlement equalities are generically unenforceable.

The proved theorem hypothesises `K ⊆ (0,1)`, and that hypothesis is load-bearing.
`K = {0}` is enforced exactly by the constant strategy `ζ_E ≡ −λ` for any
`λ > C`: at a zero price a short position costs the disturbance nothing to leave,
so the contract charges zero there, and at every `P > 0` the aggregate stays short
by at least `λ − C` and the cube maximum gain is `(λ−C)P > 0`. Symmetrically for
`K = {1}`, which is settlement to probability one, and for a settlement face in
two dimensions. **Settlement is the easy case.**

The case the generalization got right is isolated and kept: a coherence relation
cuts a segment through the open cube, lying in no proper face, and a cancellable
band of half-width `C/(2β)` survives every intensity.

**Withdrawn: the responsibility table's assignment of bounded liability wholly to
the source.** With the intensity in the bound, both layers contribute — the source
sets the depth, the mechanism sets the tolerance.

**Also corrected:** `contract.volume_times_depth` is retained but documented as
*not a bound*, so the withdrawn quantity cannot be recomputed as one.

## New theorem map

`THEOREM_MAP.md` carries the full table. What changed:

| result | before | now |
|---|---|---|
| liability ceiling `C_t·max_j d_j` | test-supported | **withdrawn**, counterexample pinned |
| declared-quantity bound | — | `derived` |
| exactness impossibility | derived, stated generally | `derived`, restricted to `K ⊆ (0,1)` in one dimension |
| empty interior ⟹ impossible | test-supported | **withdrawn** |
| settlement faces enforced exactly | — | `witness`, one and two dimensions |
| coherence segment still hard | — | `witness`, exact band |
| face-solidity | — | `conjecture` |
| `Ω^live = PC(D_t)` | — | `derived`, `test-supported` on a fragment |
| live-world lift | — | `derived`, three hypotheses named |
| derived live worlds launder liability | — | `witness` |

Nothing is registered. The five Lean results are unchanged and unaffected by
either retraction: both withdrawn claims were downstream of the kernel-checked
identity, not instances of it.

## Paper reconciliation

`PAPER_RECONCILIATION.md`. In outline: Models A and B are the **same algorithm
under different criteria**, not different algorithms; the source construction
lifts to any **nested, effectively presented, nonempty** live-world process, with
`lem:budgeter`.2's induction being the step that needs nestedness; the deductive
recovery is clean; and the two-channel split is defensible on three independent
grounds, the sharpest being that the collapsed mechanism can fail to exist.

Then the hole. Under Model B the live worlds are read off `S_t = Π_t ∩ K_t`, and
the enforcement position is the violation-weighted combination of `K_t`'s own row
normals — so by the enforcement inequality it is worth at least zero at every live
world. **Liability is identically zero and the safety theorem is satisfied by
construction.** The region Model A convicts at `−5/8`, Model B reports clean.

A constraint source can therefore discharge its own safety obligation by declaring
the worlds it loses money in inadmissible, and no condition stated over the
derived set can see it, because the set is chosen by the party the condition
binds.

## Remaining blockers

Two, at theorem level.

1. **Item 44, the assessment-set anchor.** What makes the generalized criterion
   non-vacuous. Three candidates named, none proved; the deductive floor keeps `D`
   in a role the generalization meant to remove, and eventual vindication makes a
   normative constraint a prediction, which costs `Licensed` its
   performance-independence.
2. **Item 43, a compiler both exact and safe** — or a proof there is none.

Items 39–42 are unchanged and are of ordinary size.

## The seven sentences

Six are precise and are stated in `PAPER_RECONCILIATION.md` §9. The sixth —
*what additional condition prevents the generalized semantics from laundering
losses* — is the one that fails, and the reason is structural rather than a gap in
effort: the object that defines force and the object that defines loss are the
same object, and nothing inside the generalized framework separates them.

## Maintainer decisions

Appended to `DECISIONS.md`'s *Awaiting the author*, on top of the four already
there:

5. **Whether the two-channel semantics/force distinction is the paper
   architecture.** The round recommends adopting it and gives three independent
   obstructions supporting it.
6. **Whether Coverage–Liability stays the terminology.** Liability's job is
   settled; Coverage's job is now known to be non-vacuity rather than
   proof-support, which is a different role from the one the name was chosen for.
7. **Whether traderized force is a module or a section.** The round recommends
   one paper with force as a liftable module, on theorem dependency.

## What this pass does not establish

That face-solidity is the right condition — it is a conjecture with witnesses on
both sides and a one-dimensional theorem. That the surviving liability bound is
tight. That any of the three anchors works. That the live-world lift is correct as
more than a reading of the source proofs; it is not formalized. And nothing about
whether a normative source can meet any of these conditions, which is item 39 and
was open before this pass.

## Deviations from the dispatch

**The wiki was softened rather than extended.** §X permits a wiki update only if
the surviving conceptual picture is genuinely stable. It is not — the central
condition is missing — so the existing section had its two withdrawn claims
removed and gained one paragraph naming the open question. No new page.

**No living specification note**, per §X and unchanged from the second pass.
