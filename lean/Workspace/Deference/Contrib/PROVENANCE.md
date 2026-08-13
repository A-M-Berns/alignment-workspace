# Provenance — `Workspace.Deference.Contrib`

| file | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `InheritedAlgebra.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |
| `FaithfulAcceleration.lean` | `prompts/2026-08-11-faithful-acceleration/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-faithful-acceleration/` | — |
| `MagnitudePrediction.lean` | `prompts/2026-08-11-phase-ii-prediction/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-prediction/` | — |
| `DelegationBridge.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `CertificateBounds.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `SubstitutionSeparation.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `ExposureGeometry.lean` | `prompts/2026-08-11-phase-ii-promotion/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-phase-ii-promotion/` | — |
| `EnvelopeDominance.lean` | `prompts/2026-08-11-stage-iii-fud/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-stage-iii-fud/` | — |
| `StaticViewFactorization.lean` | `prompts/2026-08-11-stage-v-li-native/` (executor: GPT-5 Codex, OpenAI; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-11 | `prompts/2026-08-11-stage-v-li-native/` | — |
| `CartesianFrameBridge.lean` | `prompts/2026-08-12-cartesian-frames/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-12 | `prompts/2026-08-12-cartesian-frames/` | — |

`InheritedAlgebra.lean` transcribes statements from
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean`; per-declaration
attribution to the inherited source is in each docstring.

`FaithfulAcceleration.lean` transcribes its Layer-1 statements from
`projects/deference/note-dump-2026-06-27/lean/FaithfulAcceleration.lean`; its Layer 2 is new
in this round.

Neither file's `weight_not_divergent` is promotable to `CLAIMS.md`: it ships no term
inhabiting its full hypothesis package. See the round report, §4.

`DelegationBridge.lean`, `CertificateBounds.lean`, `SubstitutionSeparation.lean` and
`ExposureGeometry.lean` port hand proofs from four wave-1 round reports, cited by path and
section in each docstring: `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2,
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2–§1.3,
`prompts/2026-08-11-deference-channel/REPORT.md` §1.2–§1.3, and
`prompts/2026-08-11-deference-densification/REPORT.md` §1. Every declaration in the four is
hypothesis-complete and every ported theorem ships a typechecking term inhabiting its full
hypothesis package.

`EnvelopeDominance.lean` is new in its round. It states that a per-cell maximiser of
conditional value dominates any cell-measurable selection, decomposes the gap into per-cell
regrets, and bounds that gap under a gated calibration hypothesis. Every declaration is
hypothesis-complete, and both the dominance statement and the gated bound ship inhabitation
witnesses at a non-degenerate instance where the two selections disagree.

**Read its header before citing it.** The module was written for a fully-updated-deference
comparison and does not deliver one: its maximiser is built from the evaluating agent's own
credence and objective, so it is computable before the later information arrives and
represents no distinct future agent. The dominance statement carries no fairness hypothesis
and is `sum of maxima >= sum of anything`; the regret decomposition is distributivity. The
round's report records this as the round's central defect, and the module is named for what
it proves rather than for what it was written for.

`MagnitudePrediction.lean` is new in its round. Its
`squaredError_bdd_of_sharpness_bdd` is likewise not promotable — it carries an undischarged
`EfficientlyComputable` certificate and ships no term inhabiting its full hypothesis
package. Every other declaration in that file is hypothesis-complete and ships a witness.

Stage V adds `unitTrader_ec` and `signed_bddAbove_of_bddBelow_rpn` to
`MagnitudePrediction.lean`. The first constructs the actual FAF efficient-emission
certificate; the second invokes actual `IsLogicalInductor.noExploit` and retains only the
substantive bounded-downside premise. The constant-tautology declarations inhabit that
premise. `StaticViewFactorization.lean` answers item 28's conditional core with a
polymorphic factorization theorem and a worked architecture pair whose toy jurisdiction
label differs while its static view agrees. It does not establish unrestricted
jurisdiction invisibility.

`CartesianFrameBridge.lean` is new in its round. **Its §1 mirrors fourteen definitions and three
claims of the Cartesian Frames formalization** in Formalized-Agent-Foundations, at
commit `e13dc5bd0117486b1947fbb5643045e14743e98d` — which
is not the commit `lean/lakefile.toml` pins, so the fragment is copied rather than imported.
The file header carries the name-by-name correspondence and the two places the rendering
differs from the authoritative one: composition is written in diagrammatic order, and `Iso`
constrains only the agent components, which makes the mirrored `BiextEquiv` **weaker** than
the authoritative `≃ᵇ` and every `¬ BiextEquiv` in the file correspondingly **stronger**.
Only one direction of Claim 39 is mirrored, so the
file's positive results are stated as homotopy equivalences; under the full Claim 39 they
read as biextensional equivalences, and that reading is a citation.

**Every result in it is compiled a second time against the authoritative definitions**, in
`prompts/2026-08-12-cartesian-frames/artifacts/CFCrossCheck.lean`, where the real `≃ᵇ`,
`◁`, `◁₊`, `◁ₓ`, `commit`, `externalQuot` and `image` are used and the positive results are
genuine biextensional equivalences. That file imports a library this repository does not
pin, so it is outside `lean/Workspace/` and outside the `lean` gate; the round's report
carries the re-verification command. Nothing in `CartesianFrameBridge.lean` depends on it.

Every declaration in the file is hypothesis-complete, and the constructed frames inhabit
every statement. None is promotable to `CLAIMS.md` as it stands: the deference line has no
registry, which is the standing friction entry rather than a defect of this file.

## `TimeIndexedCapability.lean`

Generated by Claude Opus 5 (Anthropic), `ci-only`, 2026-08-12, round
`prompts/2026-08-12-time-indexed-corrective-capability/` (prompt author GPT-5.6 Sol,
OpenAI). 18 declarations, `sorry`-free, each auditing to `propext` alone.

**Read §10 before citing anything above it.** An independent adversarial review, run in a
separate context, refuted two of the file's three intended results, and §10 carries the
refutations as theorems rather than the round answering them in prose:
`cutRun_eq_run_min` shows the cut family collapses onto the actual trajectory, so the
construction has no counterfactual continuations; `forecloses_iff_one_step` shows
`Forecloses` is a two-frame statement on one run; and `spurFrame_agentInert_iff` shows the
file's frame certification passes equally for a field designated as an inert label. The
docstrings above §10 were corrected to match, and the round's verdict is `Mixed`.

`exercise` and `Actor` are a **stipulated channel monopoly**, not a result: nothing in
`step`, `run`, `cutRun` or `Forecloses` reads them.

What survives review: the endpoint/capability orthogonality witnesses, the shared-history
lemmas, and `honest_prevention`. Nothing is registered; the line has no registry.
