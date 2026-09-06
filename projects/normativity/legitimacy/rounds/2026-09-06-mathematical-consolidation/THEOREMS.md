# Theorem ledger

Every Lean declaration below is sorry-free and audits to a subset of
`[propext, Classical.choice, Quot.sound]`. Nothing is registered by this round.

## `Workspace.Normativity.Contrib.OccurrenceIntegrity` (new)

| declaration | statement | class |
|---|---|---|
| `Program.evaluate_subst` | `(t.subst hab ρ).evaluate v = t.evaluate (fun p => (ρ p).evaluate v)` | lean-proved |
| `Program.exists_fate`, `fates_ne_zero` | every account has a fate | lean-proved |
| `Program.terminals_subst` | `(t.subst hab ρ).terminals = t.terminals + Σ_{p ∈ t.livePorts} (ρ p).terminals` | lean-proved |
| `Program.livePorts_subst` | `(t.subst hab ρ).livePorts = Σ_{p ∈ t.livePorts} (ρ p).livePorts` | lean-proved |
| `Program.terminals_le_subst` | `t.terminals ≤ (t.subst hab ρ).terminals` | lean-proved |
| `Step.prefix` | a step's source history is a prefix of its target's | lean-proved |
| `Segment.propagate_trans` | `(l.trans r).propagate a = r.propagate (l.propagate a)` | lean-proved |
| `Segment.complete_accounting` | `Segment A B → Initial A → Accounted B` | lean-proved (a definition; its content is the type) |
| `Segment.exposure_mono` | `A.exposed ⊆ B.exposed` along a segment | lean-proved |
| `Segment.denote` | every exposed occurrence's account denotes `Evidence (anchor o)` | lean-proved (definition) |
| `LocalLaw.feasibility` | inhabitation of parent and successors' evidence is equivalent | lean-proved |
| `Witness.first_answered`, `second_live`, `distinct_fates` | two occurrences with one anchor: fates `{answered}` and `{live}` after one step | lean-proved; nonvacuity witness for `complete_accounting` and the multiplicity claim |

Necessity: the constructor-level blocks in `CONSOLIDATION.md` §2 are by typing; no
separate necessity witness is claimed for each protocol predicate. PR85's
`IntegrityAdversary` countermodels remain the necessity evidence for the record-layer
conditions and are unchanged.

## `Workspace.Normativity.Contrib.NonCaptureCertificate` (extended)

| declaration | statement | class |
|---|---|---|
| `Scenario.certPlus_iff_robustOpen` | `CoverageActual W → ((S ∧ R+ ∧ P) ↔ RobustOpen)` | lean-proved |
| `Scenario.robustOpen_of_persistence` | `CoverageActual W → S → Ra W → Rb W → Rc W → P → RobustOpen` | lean-proved |
| `Witness.persistence_not_necessary` | `RobustOpen ∧ CoverageActual W0 ∧ ¬ ClauseR W0` on a two-route scenario | lean-proved; exact witness |

Consequence: the `(S, R+, P)` bill is the conclusion factored by a case split, not a
sufficient condition of independent content; the componentwise persistence bill is
the substantive external certificate and is strictly stronger.

## `Workspace.Normativity.Contrib.NormativeInductorComposition` (repaired)

| declaration | statement | class |
|---|---|---|
| `edge_progress_bound` | `T,d ≥ 0`; `PracticalCert` on positive edges; `Σ_e T M ≤ Γ ν` ⇒ `Σ T Λ + D r ≤ Γ Σ ν d + Σ T ε + D r` | lean-proved (Codex worker, `PROGRESS.md`) |
| `edge_progress_bound_quadratic` | with `ν = λ/Σλ`, `λ d² ≤ ρ`, `Γ ≥ 0`: first term `Γ √(Σρ/Σλ)` | lean-proved (Codex worker) |
| `edge_progress_witness` | all hypotheses inhabited, all three terms positive | lean-proved (Codex worker) |
| `edge_headline_separation` | average edge loss `1/2 < 1` headline | lean-proved (Codex worker); separates the endpoints |
| `progress_bound`, `progress_bound_quadratic` | exposure-headline form | lean-proved (PR85); reclassified as optional corollary |
| `EndToEndHypotheses`, `end_to_end` | removed | its conclusion returned six opaque premises unchanged |

## `Workspace.Normativity.Contrib.NormativeInductionInterface` (new)

| declaration | statement | class |
|---|---|---|
| `Evaluation.residual_bounds` | `0 ≤ residual ≤ 1` from `μ_prob`, `T_row`, `T_nonneg` | lean-proved |
| `Evaluation.progress_bound` | `PracticalUptake market → progress market ≤ modulus + error + D·residual` | lean-proved |
| `Evaluation.conditional_normative_inductor` | bounded liability ∧ computable market ∧ `PracticalUptake` ⇒ `IsLogicalInductor` ∧ residual bounds ∧ Progress bound | lean-proved; unverified-nonvacuous on the LI hypotheses |
| `Evaluation.deductive_normative_inductor` | registered effective end-to-end hypotheses ∧ `DefectDominated` ∧ edge certificates ∧ amplification ⇒ `IsLogicalInductor` ∧ Progress bound, with `λ d² ≤ ρ` derived from conformance | lean-proved; inhabitation of `DeductiveProcessComputation` inherited from the registered theorem's own status |
| `Witness.uptake`, `Witness.bound` | `PracticalUptake` inhabited on the Integrity witness boundary; bound holds; all three terms positive | lean-proved; nonvacuity for the certificate half |

## `Workspace.Normativity.Contrib.HistoryIntegrity` (CI repair)

The `#print axioms` block moved outside the namespace in which `Classical` is open,
so the audit reads `Classical.choice` rather than `choice`. No declaration changed.

## Verification

From `lean/`: `lake build` (green, 2983 jobs) and `python3 ../tests/audit_axioms.py`.
From the repository root: `python3 tests/run.py`.
