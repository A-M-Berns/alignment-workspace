# Stage-II integration verification of Track M

**This is not Track M's report.** Track M's executor did not persist report-shaped
output, and no draft of its prose exists anywhere in the repository or in the round
directory — only its Lean, its `PROVENANCE.md` row block, and the commit message of
`f4d9849`. Rather than reconstruct prose and present it as the original agent's, this
document is an **independent verification of Track M's committed artifacts**, authored
by the Stage-II closure pass. Where it states a finding, the finding is mine and was
obtained by running the checks named below; where it reports Track M's intent, the
source is the committed code, its docstrings, or `f4d9849`'s message, cited as such.

| field | value |
|---|---|
| original track | Phase II Track M, `prompts/2026-08-11-phase-ii-promotion/PROMPT.md` |
| original executor | Claude Opus 5 (Anthropic); prompt author GPT-5.6 Sol (OpenAI) |
| original delivery | `f4d9849`, Lean + provenance only; no report persisted |
| this document's author | Claude Opus 5 (Anthropic), Stage-II closure pass, 2026-08-11 |
| review status | `ci-only` |

## 1. What was inspected

Four Lean modules under `lean/Workspace/Deference/Contrib/`, added by `f4d9849`:
`CertificateBounds.lean`, `DelegationBridge.lean`, `ExposureGeometry.lean`,
`SubstitutionSeparation.lean`; the `PROVENANCE.md` rows added for them; and the four
wave-1 reports they cite as sources.

## 2. Commands run, and their exact output

At `HEAD = 8c71ef9`, branch `round/2026-08-11-deference-corrigibility`, tree clean.

| command | result |
|---|---|
| `lake build` (in `lean/`) | exit 0, **1843 jobs** |
| `python3 tests/audit_axioms.py` | exit 0, **142 results across 10 files**, all within `[propext, Classical.choice, Quot.sound]` |
| `python3 tests/run.py` | `ALL GREEN (2 projects)`; sorry gate clean over 10 files; conservativity: 3 spec files, no axioms, shape unchanged |

The build count confirms the library glob is doing its job: `lean/lakefile.toml`
carries `globs = ["Workspace.+"]`, so every module under the library is reached by the
default target without an import edit in the specification root. I verified the glob is
present and unmodified rather than taking the count on trust.

## 3. Theorem counts

Counted as `^(theorem|lemma) ` declarations, and independently as `#print axioms`
lines, which agree exactly per module.

| module | theorems | `#print axioms` |
|---|---|---|
| `CertificateBounds.lean` | 28 | 28 |
| `DelegationBridge.lean` | 15 | 15 |
| `ExposureGeometry.lean` | 19 | 19 |
| `SubstitutionSeparation.lean` | 21 | 21 |
| **total** | **83** | **83** |

The claim of 83 theorems across four modules is confirmed. Library-wide the figure is
155 theorems across 10 files, the balance being the three modules from earlier rounds.

## 4. Sorry status

Zero. `grep -rn sorry` over the library returns nothing, and `tests/run.py`'s sorry
gate reports clean over 10 files. No `axiom` declaration appears in any contributed
module; the conservativity gate confirms the specification shape is unchanged.

## 5. Targets reached

Against the recommended set in the dispatch:

| source | recommended | landed as |
|---|---|---|
| finite-kernel §1.2 | delegation bridge + two corollaries | `delegation_bridge` (T1), `delegation_bridge_unconditional` (T1′), `gradeTrust_of_refinement` (T1″) |
| certificates §1.2–§1.3 | L1, L2, L3, L7, Theorem C′ | `margin_forces_agreement` / `selection_eq_of_margin` (L1), `override_bound` (L2), `defect_bound` (L3), `advantage_estimate` (L7), `gradeRegister_strict` (C′) |
| densification §1 | Lemma 1 piercing duality, Theorem 2 exposure–harvest identity | `greedy_duality`, `exposure_harvest_bound`, `exposure_harvest_attained` |
| channel §1.2 | Propositions 1, 2, 6, 7 | `extensional_admits_both`, `sim_depends_only_on_inducedChoice`, `separation_requires_disagreement`, `unpredictability_separates` |

**Not reached:** Track E's Theorem 6 and Corollary 4. `f4d9849` records these as not
attempted for a statement-level reason (the nondecreasing-delay hypothesis had to
appear in the statement rather than a comment) rather than left as holes. I confirm
they are absent and that no `sorry` stands in for them.

## 6. Exclusions, and why they now matter more than they did

Two results were deliberately excluded, and `CertificateBounds.lean`'s header records
the exclusion in the file itself:

> Theorem C's V-register comparator clause and the `2M` delegation bridge (source L4,
> L5, L6) rest on the movement hypothesis (MV-M), the uniform grade-to-quantity
> relation this phase exists to replace.

I verified L4, L5 and L6 are absent from the Lean, and that the `delegation_bridge`
that *was* ported is the local form under a named `GradeTrust` hypothesis, not the
uniform `2M` form.

**This exclusion is what kept the promoted set intact.** Track L subsequently refuted
the settlement-loaded branch of L4 under a protecting execution layer, with 1443
enumerated counterexamples. Had L4 been ported, the kernel would now hold a theorem
whose intended reading is false in the architecture the phase moved to. The exclusion
was made on the grounds that the hypothesis shape was expected to change; the
justification that arrived is stronger than the one given.

## 7. What this verification does not establish

1. **That the transcriptions are faithful to their sources.** I confirmed each ported
   theorem cites a source by path and section and that the cited sections exist and
   state results of the same shape. I did not re-derive the hand proofs in the four
   wave-1 reports, so "the Lean says what the report said" rests on reading, not on a
   check. `f4d9849` claims the sources' constants were recomputed inside the kernel and
   all match; I confirm such constant lemmas exist (`defect_eq`, `advantage_hat`,
   `advantage_true`, `override_mass`, `TR`, `bridge_at_E1`, `bound_attained`) but did
   not independently recompute them from the reports.
2. **That the statements are the ones we meant.** The kernel certifies bodies against
   statements. Every statement here is `ci-only`; no maintainer has read them.
3. **Nonvacuity beyond what ships.** Each ported theorem ships an inhabitation witness
   and the `*_nonvacuous` declarations typecheck. Two declarations elsewhere in the
   library remain `unverified-nonvacuous` — `FaithfulAcceleration.weight_not_divergent`
   and `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd` — and neither is Track
   M's.
4. **Registration.** Nothing is registered. `projects/deference/CLAIMS.md` does not
   exist, so no promoted theorem is `workspace-established` regardless of its kernel
   status.

## 8. Proposed registry entries

None proposed here. Registration is a maintainer act under demand-gating, and the
prerequisite — creating `CLAIMS.md` — is a specification-layer change that no track has
been authorized to make. The 83 theorems are `lean-proved` in the sense of surviving
the kernel and the axiom audit, and unregistered, which are different things.

## 9. Provenance

Track M's Lean and its `PROVENANCE.md` rows are committed and correctly attributed:
generator `prompts/2026-08-11-phase-ii-promotion/`, executor Claude Opus 5 (Anthropic),
prompt author GPT-5.6 Sol (OpenAI), review status `ci-only`, dated 2026-08-11. This
verification document adds no new code and claims no new result.

---

## Outstanding maintainer actions

1. **Decide whether this substitute register is acceptable**, or whether Track M should
   be re-dispatched to produce its own report. The Lean is verified either way; what is
   missing is the executor's own account of its reasoning, which cannot be recovered.
2. **Note that the dual-register requirement is not met for Track M.** `AGENTS.md`
   requires both a verification and a human register per substantive deliverable. This
   document is the verification register; the human register for Track M's content is
   folded into the Stage II parent report rather than written separately, because
   writing a plain-language account of another agent's reasoning that it never recorded
   would be invention.
