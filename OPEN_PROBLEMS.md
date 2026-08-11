# Open problems

**The contribution funnel, and the source of truth.** GitHub issues mirror this
file; this file does not mirror them. Each item states the problem precisely,
points at the context, says what a solution must ship, and carries a difficulty
tag.

What a solution must ship is set by `CONTRIBUTING.md` and is the same for
everyone: a theorem ships as statement + implementation + test + a necessity
witness per hypothesis where feasible; Lean ships building and auditing clean; a
witness ships as the exact instance and the check that verifies it.

**Every item is a self-contained round specification** an arbitrary agent could
execute: a precise statement, the deliverable shape, an acceptance check stated
as something CI runs, a context pointer with exact paths, and a difficulty tag.
Filing is a maintainer act — propose items as issues.

**Standing item family: Lean ports.** Every `test-supported` or
`enumeration-verified` registry entry is implicitly a port target; the maintainer
promotes selected ones to explicit items.

Difficulty tags: **[entry]** — self-contained, needs no new mathematics.
**[substantial]** — a real result, scoped. **[open]** — nobody knows, and it may
be impossible.

---

## Leverage line

Context for all six: `frozen/consolidation_aug9/`, whose `OPEN_PROBLEMS.md`
ranks them and whose theory parts state the surrounding results. Cite claims from
it by identifier.

### 1. Persistence of the certified core minimum — **[open]**

Containment of the core homothet is linear in the reference at fixed
coefficient, so whether a declared core minimum is satisfiable *at a date* is one
linear program (`NL-SI-A2`, `NL-SI-A3`). What is open is the infimum over dates:
whether a declared minimum keeps being satisfiable as settlement contracts the
region. `NL-SI-A4` shows no finite family of per-date checks decides it, and
`NL-SI-A7` shows both outcomes occur on small instances.

*Deliverable shape:* `lean-proved` in `Workstudio.Leverage.Contrib`, or `witness-checked` for the negative direction.
*Acceptance check:* The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property.

*Context:* `frozen/consolidation_aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.
*A solution ships:* either a proof that a positive minimum persists under stated
conditions, with necessity witnesses for those conditions; or a displayed
trajectory driving it to zero under conditions the interface permits.
*Why it matters:* it is the single hypothesis object separating the parametric
composite from an unconditional enforcement commitment.

### 2. A computable coherence modulus, or a proof there is none — **[open]**

Does a given engine admit a computable tolerance schedule tending to zero, with
its prices provably conforming at every finite date? Open **in both directions**.

**Do not cite the adjacent impossibility results as settling this.** Both the
source's own three-way impossibility and the cited four-way one turn on Gaifman
inductivity, a desideratum the candidate algorithm already fails, and which this
question does not mention.

*Deliverable shape:* `lean-proved`. Nothing weaker settles a question that is open in both directions.
*Acceptance check:* The Lean gate builds and audits clean.

*Context:* `frozen/consolidation_aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §3, §7.
*A solution ships:* a modulus with its conformance proof, or an impossibility
argument that does not route through Gaifman inductivity.

### 3. Registry completeness for the objection grammar — **[entry]**

The per-table ablation programme gives witnesses for the tables the displayed
grounds exercise, out of thirteen registered. Completeness — that no judge needs
a table the registry lacks — is not established. This is the one gap that would
make a footprint declaration **unsound** rather than merely coarse.

*Deliverable shape:* `enumeration-verified` — domain parameters for the house enumeration checker, covering all thirteen tables.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry.

*Context:* `frozen/consolidation_aug9/THEORY_7_OBJECTION_GRAMMAR.md` §4.
*A solution ships:* grounds exercising every registered table, the ablation run
over all thirteen, and the result either way.
*Why it is [entry]:* finite programme over a finite registry; no new mathematics.

### 4. Higher-dimensional sharpness for the movement cap — **[substantial]**

Everything verified numerically in the joint layer is the one-coordinate fixture.
The vertex formulation is stated for general finite regions but only the scalar
case is exercised, and no claim is made that the corrected retention predicate is
the weakest sound one.

*Deliverable shape:* `witness-checked` for the multi-coordinate instances; `lean-proved` for a sharpness result.
*Acceptance check:* The `witness` checker accepts each instance; or the Lean gate is green.

*Context:* `frozen/consolidation_aug9/THEORY_10_JOINT_COMPOSITION.md` §3, §6.
*A solution ships:* the multi-coordinate instances with exact witnesses, and
either a sharpness proof or a witness that the predicate is not weakest.

### 5. Constructing rather than reading the audited pair — **[substantial]**

The strongest evidence about a non-trivial engine in the leverage line is a
**reading audit** — a clause-by-clause reading of a published source, labelled as
the weakest evidence class in the package. Constructing a minimal instance of the
pair, enough of a market over a declared process to evaluate the interface
predicates against, would move that evidence from the weakest class to the
strongest.

*Deliverable shape:* A construction in `Workstudio.Leverage.Contrib` plus registry entries per clause it inhabits.
*Acceptance check:* The Lean gate is green and each clause entry names a declaration that exists.

*Context:* `frozen/consolidation_aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §7;
`VERIFICATION.md` §1.
*A solution ships:* the construction, the predicates evaluated against it, and an
honest statement of which clauses it does and does not inhabit.

### 6. Schema-level demand rates — **[substantial]**

How demand scales with the schema set rather than with the arrival stream. The
stream results are stated over arrivals.

*Deliverable shape:* `enumeration-verified` over a declared finite schema family, or `conjectured` with the statement made precise.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, or the registry records the class honestly as conjectured.

*Context:* `frozen/consolidation_aug9/THEORY_9_PRACTICAL_DEMAND.md`.

---

## Delegation line

Context for all three: `frozen/deference-note-dump-2026-06-27/`, in particular
`lean/AUDIT.md`, the development's own statement-level audit. Its §3 is titled
"The concerning gaps"; the three below are its own findings, quoted by section.

### 7. Model the market and the traders — **[substantial]**

The audit's §3.1 is "The market and traders are entirely unmodeled". The
development takes the Logical Induction theorems as named hypotheses and proves
what follows; the inference from the criterion to the forcing inequality is
nowhere in it, because the objects that inference is about are absent.

*Deliverable shape:* `lean-proved` in `Workstudio.Delegation.Contrib`, with an inhabitation witness for the hypothesis package.
*Acceptance check:* The Lean gate is green, the axiom audit is clean, and the nonvacuity witness typechecks.

*Context:* `frozen/deference-note-dump-2026-06-27/lean/AUDIT.md` §3.1.
*A solution ships:* a minimal market and trader model in
`Workstudio.Delegation.*`, enough that the criterion's application is a proof
rather than a hypothesis, with the axiom audit clean.
*Why it matters:* this is the same gap the leverage line and the pinned
dependency sit on the other side of. It is the most valuable single item in this
file.

### 8. The doubly-soft weight class — **[open]**

The audit's §3.2 is "The doubly-soft weight: one leak closed, the class still
open".

*Deliverable shape:* `lean-proved`, or `witness-checked` for a negative answer.
*Acceptance check:* The Lean gate is green; or the `witness` checker accepts the separating instance.

*Context:* `frozen/deference-note-dump-2026-06-27/lean/AUDIT.md` §3.2.
*A solution ships:* a characterization of the class, or a witness that it is not
characterizable in the intended terms.

### 9. Forcing headlines that are squeezes — **[substantial]**

The audit's §3.3 is "The forcing headlines are squeezes over hypotheses
equivalent to their conclusions". A squeeze is a theorem whose hypothesis already
contains its conclusion; it is not false, it is empty.

*Deliverable shape:* `lean-proved` restatements whose hypotheses are strictly weaker than their conclusions, each with an inhabitation witness.
*Acceptance check:* The Lean gate is green and each restated theorem ships a typechecking witness term.

*Context:* `frozen/deference-note-dump-2026-06-27/lean/AUDIT.md` §3.3, and §5's
severity ranking.
*A solution ships:* restated theorems whose hypotheses are strictly weaker than
their conclusions, with the gap displayed — or a demonstration that the squeeze
is unavoidable, which is itself a result.

---

## Infrastructure

### 10. Build the Lean in CI — **[entry]**

The Lean gate compiles in CI with a cached `.lake/`; if that cache proves too
slow or too large for the runner, the gate needs restructuring rather than
disabling. Anyone who improves the cache hit rate or the build time has
contributed.

*Deliverable shape:* A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue.
*Acceptance check:* The `lean` job's wall time falls, measured across two consecutive pushes that change neither the pin nor the toolchain.

*Context:* `.github/workflows/ci.yml`; `SETUP_REPORT.md` records the measured
times.

### 11. A dual-register presence check in CI — **[entry]**

`AGENTS.md` requires every substantive deliverable to ship both a verification
register and a human register, and leaves enforcement to review. A heuristic gate
— each new results directory contains both file kinds — is cheap once "results
directory" is defined, which needs the repository to have some.

*Deliverable shape:* A change to `.github/workflows/ci.yml` and a check script — **specification layer**.
*Acceptance check:* The check runs in CI, passes on a compliant directory and fails on one missing a register.

*Context:* `AGENTS.md`, dual-register section; `.github/workflows/ci.yml`.
*A solution ships:* the check, a passing case, and a failing case proving it bites.

### 12. A necessity witness for every hypothesis that lacks one — **[entry]**

Convention 2 asks for a necessity witness per hypothesis "where feasible". Rows
in the frozen ledger that lack one, and where one is feasible, are contributable
units: find the instance, display it, add the test.

*Deliverable shape:* `witness-checked` entries, one per hypothesis given a witness.
*Acceptance check:* The `witness` checker accepts each instance.

*Context:* `frozen/consolidation_aug9/LEDGER.md`, the necessity/sharpness column.


---

## Infrastructure, continued

### 13. Scaffolding self-verification — **[entry]** — *satisfied, kept open*

The repository's own machinery must be exercised by something real before any
research claim depends on it: the Lean chain must compile and audit, and the
checker harness, the claims registry and the CI job that runs them must all be
exercised end to end.

*Deliverable shape:* `lean-proved` entries for the dependency-chain smoke
results, and one `enumeration-verified` entry exercising the house enumeration
checker.
*Acceptance check:* the `lean` and `checkers` CI jobs both green, with the
registered entries adjudicated by them.
*Context:* `projects/leverage/CLAIMS.md`; `checkers/`; `.github/workflows/ci.yml`.
*Status:* satisfied by the scaffolding rounds. It stays filed because the
registry's demand rule means every entry must answer an item, including these —
and because a future change to the harness re-opens exactly this question.
