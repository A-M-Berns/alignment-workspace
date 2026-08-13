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
| `ReachableCorrectiveControl.lean` | `prompts/2026-08-12-reachable-corrective-control/` (executor: Claude Opus 5, Anthropic; prompt author: GPT-5.6 Sol, OpenAI) | `ci-only` | 2026-08-13 | `prompts/2026-08-12-reachable-corrective-control/` | — |

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

`ReachableCorrectiveControl.lean` is new in its round and has **no imports**: it elaborates
against the pinned toolchain alone, which is why nothing in it depends on the
Cartesian-frames mirror above. It is a twelve-state transition system with separate
principal, advisor and environment input coordinates, and it defines corrective capability,
reachable corrective capability and foreclosure by quantifying over the transition relation
rather than by reading a state field; the field-level characterizations `canCorrect_iff`,
`canCorrectFuture_iff` and `forecloses_iff` are conclusions. Every declaration is
hypothesis-complete and every witness is a concrete state of the model, so nothing in the
file is vacuous. None is promotable to `CLAIMS.md`: the deference line has no registry.

**Its §12 is an adversarial review's refutations, reproved in place, and it breaks the
file's protection claims. Read it before citing anything in §9 or §10.** There is no
protected coordinate: `principal_has_no_exclusive_effect` shows the advisor reproduces the
principal's entire successor state at every state, and
`advisor_reset_is_principal_pull_where_capable` that wherever the principal can correct the
advisor's actuator *is* the principal's correction. `CanCorrect` and `CanCorrectFuture`
quantify the advisor existentially, so neither is a statement about the principal's control
— `advisor_has_a_universal_veto`, `no_advisor_robust_capability`, and
`canCorrectFuture_measures_advisor_cooperation`, which exhibits an advisor policy that
destroys the capability at every horizon while `Preserves` certifies it. `AuthLabel` builds
an isomorphic system whose gating field is named `authorized` and which passes every test in
§10, so §10 excludes inert coordinates and nothing more. `EnvBlame` shows `Forecloses`
attributes nothing. The Cartesian-frame correspondence stated in the round's register is
prose: no declaration in this file checks it.

What the review attacked and did not break: the autonomy (the system evolves without the
advisor, and the environment alone creates the corrective situation), the absorbing-severed
argument and the foreclosing arm, the fairness of `obs`, the quantifiers of `SameImmediate`,
and the inert-field results.
