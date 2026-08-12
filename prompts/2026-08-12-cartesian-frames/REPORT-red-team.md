# Adversarial review — Cartesian frames × deference

**Reviewer:** Claude Opus 5 (Anthropic), in a **separate context** with no access to the
round's reasoning, per the dispatch's §XV independence requirement. Instructed to break the
claims, not to summarise them.

**Reviewed:** the round's first version, before any of the repairs below landed. All
citations are to that version; where a defect was already fixed independently, this is
noted.

**Verdict of the review.** The Lean is sound and the mirror is faithful. The defects are in
the inferences drawn from it, and one of them was the round's headline claim.

## What the review confirmed

Findings are listed at the severity the reviewer assigned. Every one is accepted; the
disposition column says what changed.

| # | finding | disposition |
|---|---|---|
| C1 | **The "not a label" argument proves too much.** `image` is a `≃ᵇ`-invariant, so a controller label moved from the architecture record into the *world* type is separated by a `≃ᵇ`-invariant too. The reviewer built the adversary: two agent-active frames differing only in a `controller` coordinate, separated at `≃ᵇ`, blind-equal under the round's own projection. `≃ᵇ`-invariance does not certify a separation as structural. | **Accepted; the argument was replaced.** The adversary is now in both Lean surfaces (`labelledHuman`, `labelledAgent`, `labelledHuman_not_biextEquiv_labelledAgent`). The surviving argument is the world-map asymmetry — `mapWorlds_forgetLabel` deletes the label separation, `mapWorlds_delegated_not_biextEquiv_simulated` shows nothing deletes the control separation — and it is labelled a structural argument, not a proof. Bridge §4b, N1 row of §5. |
| C2 | **Accurate simulation is not modelled.** `simulated h₀` is a constant, not a predictor. N3 was graded "survives" on a construction outside its scope. | **Accepted; the obstruction row is now `no`.** Bridge §4c, §6. |
| C3 | **`≃ᵇ` cannot tell "tracks" from "inverts".** A process executing the principal's disposition *negated* is biextensionally equivalent to delegation. The invariant reads dependence, not agreement. Separately, `simulatedReading_eq_delegated` was a tautology of definitions the round wrote itself. | **Accepted.** `simulatedReading` is deleted; the `simRead f` family replaces it, with `simRead_id_eq_delegated`, `simRead_const_eq_simulated` and `simRead_not_biextEquiv_delegated` on both surfaces. "Tracks" is corrected to "varies with" throughout. |
| C4 | **No present index, action or transition exists in the formalization**, while the prose said "two present actions" and "induce". | **Partly pre-empted, partly accepted.** `PresentAction`, `presentStage` and `futureFrame` were added before the review returned, which supplies the two-stage statement. The deeper half stands: there is no transition and no time coordinate, so Q3's *depth* hole is untouched. The PRIORITIES claim that this "is what the depth question wanted" was wrong and is retracted; bridge §7.8 is new. |
| C5 | **The subagency claims are universally-true schemas.** `Commit^B(C) ◁₊ C` and `External^{/s}(C) ◁ₓ C` hold of every frame at every argument, and Theorem 24's factorization is trivial when the subagency is already `◁₊` or `◁ₓ`. The externalization route is eliminable — the reviewer proved `MultSubagent transfer preserve` in six lines without `External`. | **Accepted.** Bridge §4d now separates the universal half from the content, which is the `≃ᵇ` identifications plus the properness. The Theorem 24 sentence is retained only with its triviality stated. |
| C6 | **"Still exercised, but by something else" is unsupported.** `transfer` is equivalent to a frame with a one-point agent whose executed coordinate is exogenous; a frame has no notion of *whose* environment state a coordinate is. | **Accepted.** `transfer_biextEquiv_exogenous` added to both surfaces. Bridge §4e and the human register now say the holder is not represented. |
| C7 | **H1 is not confirmed as stated.** The dispatch's H1 is over a coarse world map alone; the reviewer proved it *fails* on this pair for every map retaining any information about the executed action. What was confirmed uses `mapWorlds p ∘ pin`. | **Accepted, and it became load-bearing.** The negative is now `mapWorlds_delegated_not_biextEquiv_simulated`, and it is what carries the repaired N1 argument. Recorded as a negative result in §8. |
| C8 | **Evidence-class mislabel in the human register**: the extension from "every functional of this two-bit world" to "every observable the Logical Induction work uses" is architectural interpretation presented under "machine-checked". | **Accepted.** Split in the human register; added to the §8 evidence table. |
| C9 | **The §9 target is a re-instantiation, not a theorem.** It is `value_eq_of_price_realization_eq` at a new instantiation with `commitment_view_blind` as witness; both already proved. | **Accepted.** §9 now says so, and says the reason to do it is the witness rather than the theorem. |
| C10 | "Every result below holds on both surfaces" is false in both directions. | **Accepted.** §2 enumerates what each surface uniquely carries. |
| C11 | `commitment_view_blind` is `congrArg` on definitionally equal terms, so calling it the Cartesian-frame form of the Stage-V theorem misstates its kind — it is the inhabitation witness. | **Accepted.** §4a corrected. |
| C12 | The mirror header's justification for its weaker `Iso` was wrong; the conclusion survives because collapses are biextensional, which the mirror does not prove. | **Independently fixed before the review returned**, in the direction the reviewer confirms: the mirrored `Iso` constrains only the agent components, so the mirrored `BiextEquiv` is weaker and every `¬ BiextEquiv` correspondingly stronger. Direction-safe either way. |
| C13 | Provenance: the upstream commit had moved; `REPORT-red-team.md` was listed as produced and did not exist; a line count disagreed between two files. | **Accepted.** The upstream library moved twice during the round and then merged to `main`; every reference now names `e13dc5b`, which is where the cross-check is verified. This file exists. Counts reconciled. |

## What the review probed and found sound

Reported here because a review that only lists defects hides how much was tested.

- **Mirror faithfulness, definition by definition.** `Frame`, `image`, `Hom`, `Hom.id`,
  `Homotopic`, `HomotopyEquiv`, `agentSetoid`, `envSetoid`, `collapse`, `BiextEquiv`,
  `commit`, `mapWorlds`, `partitionSections`, `externalQuot` match the authoritative
  definitions modulo namespacing; `Hom.comp` is correctly diagrammatic;
  `AddSubagent`/`MultSubagent` match Definitions 18/19 with the disclosed `HomotopyEquiv`
  substitution. **No mirrored definition is weaker in a direction that eases a
  separation.**
- **The `image` separator is not an artifact of the two-bit world.** The reviewer proved
  the general facts: `(C.externalQuot s).image = C.image` for every frame and every
  setoid, and the commit inclusion. One caveat accepted into §4e: shrinkage is a fact about
  the set committed to, not about `Commit`.
- **`externalQuot` at the one-cell partition is not vacuous.** `foreclose d₀ ◁ₓ preserve`
  is false, so `◁ₓ` and `◁₊` do separate here. The degeneracy is C5's, not vacuity.
- **No value premise is smuggled.** Nothing in the Lean assigns a preference; the
  evaluative pull is carried by provisional names and is disclosed as provisional.
- **Stage V is genuinely untouched and the round says so.**
- **Axiom hygiene and gating** are as claimed, on both surfaces.

## Effect on the verdict

The round was written up as *representation-positive, corrigibility-open*. C2 and C3
together mean the delegation-versus-simulation target **fails** on the case the dispatch
posed, which no qualification of a positive verdict covers honestly. The verdict is
**mixed**, with the split stated in the bridge document's opening.

## What the review did not settle

The reviewer did not have, and did not need, an opinion on whether the control reading of
delegation — a faithful predictor is a channel through which the principal controls
execution — is the one the deference line wants. That remains open, and it is the question
C2 and C3 hand back to the line.
