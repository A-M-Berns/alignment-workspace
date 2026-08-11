# Priorities

**What the program wants done next, in its own order.** This is not an inventory
of everything unsolved — it is the maintainer's ranking of what would move the
work, and an item's absence means nobody has asked for it, not that it is easy.
GitHub issues mirror this file; this file does not mirror them. Each item states
the problem precisely, points at the context, says what a solution must ship, and
carries a difficulty tag.

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

Context for all six: `projects/leverage/consolidation-aug9/`, whose `OPEN_PROBLEMS.md`
ranks them and whose theory parts state the surrounding results. Cite claims from
it by identifier.

### 1. Persistence of the certified core minimum — **[open]**

Containment of the core homothet is linear in the reference at fixed
coefficient, so whether a declared core minimum is satisfiable *at a date* is one
linear program (`NL-SI-A2`, `NL-SI-A3`). What is open is the infimum over dates:
whether a declared minimum keeps being satisfiable as settlement contracts the
region. `NL-SI-A4` shows no finite family of per-date checks decides it, and
`NL-SI-A7` shows both outcomes occur on small instances.

*Deliverable shape:* `lean-proved` in `Workspace.Leverage.Contrib`, or `witness-checked` for the negative direction.
*Acceptance check:* The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property.

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.
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

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §3, §7.
*A solution ships:* a modulus with its conformance proof, or an impossibility
argument that does not route through Gaifman inductivity.

### 3. Registry completeness for the objection grammar — **[entry]**

The per-table ablation programme gives witnesses for the tables the displayed
grounds exercise, out of thirteen registered. Completeness — that no judge needs
a table the registry lacks — is not established. This is the one gap that would
make a footprint declaration **unsound** rather than merely coarse.

*Deliverable shape:* `enumeration-verified` — domain parameters for the house enumeration checker, covering all thirteen tables.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry.

*Context:* `projects/leverage/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md` §4.
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

*Context:* `projects/leverage/consolidation-aug9/THEORY_10_JOINT_COMPOSITION.md` §3, §6.
*A solution ships:* the multi-coordinate instances with exact witnesses, and
either a sharpness proof or a witness that the predicate is not weakest.

### 5. Constructing rather than reading the audited pair — **[substantial]**

The strongest evidence about a non-trivial engine in the leverage line is a
**reading audit** — a clause-by-clause reading of a published source, labelled as
the weakest evidence class in the package. Constructing a minimal instance of the
pair, enough of a market over a declared process to evaluate the interface
predicates against, would move that evidence from the weakest class to the
strongest.

*Deliverable shape:* A construction in `Workspace.Leverage.Contrib` plus registry entries per clause it inhabits.
*Acceptance check:* The Lean gate is green and each clause entry names a declaration that exists.

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §7;
`VERIFICATION.md` §1.
*A solution ships:* the construction, the predicates evaluated against it, and an
honest statement of which clauses it does and does not inhabit.

### 6. Schema-level demand rates — **[substantial]**

How demand scales with the schema set rather than with the arrival stream. The
stream results are stated over arrivals.

*Deliverable shape:* `enumeration-verified` over a declared finite schema family, or `conjectured` with the statement made precise.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, or the registry records the class honestly as conjectured.

*Context:* `projects/leverage/consolidation-aug9/THEORY_9_PRACTICAL_DEMAND.md`.

---

## Deference line

Context for all three: `projects/deference/note-dump-2026-06-27/`, in particular
`lean/AUDIT.md`, the development's own statement-level audit. Its §3 is titled
"The concerning gaps"; the three below are its own findings, quoted by section.

### 7. Model the market and the traders — **[substantial]**

The audit's §3.1 is "The market and traders are entirely unmodeled". The
development takes the Logical Induction theorems as named hypotheses and proves
what follows; the inference from the criterion to the forcing inequality is
nowhere in it, because the objects that inference is about are absent.

*Deliverable shape:* `lean-proved` in `Workspace.Deference.Contrib`, with an inhabitation witness for the hypothesis package.
*Acceptance check:* The Lean gate is green, the axiom audit is clean, and the nonvacuity witness typechecks.

*Context:* `projects/deference/note-dump-2026-06-27/lean/AUDIT.md` §3.1.
*A solution ships:* a minimal market and trader model in
`Workspace.Deference.*`, enough that the criterion's application is a proof
rather than a hypothesis, with the axiom audit clean.
*Why it matters:* this is the same gap the leverage line and the pinned
dependency sit on the other side of. It is the most valuable single item in this
file.

### 8. The doubly-soft weight class — **[open]**

The audit's §3.2 is "The doubly-soft weight: one leak closed, the class still
open".

*Deliverable shape:* `lean-proved`, or `witness-checked` for a negative answer.
*Acceptance check:* The Lean gate is green; or the `witness` checker accepts the separating instance.

*Context:* `projects/deference/note-dump-2026-06-27/lean/AUDIT.md` §3.2.
*A solution ships:* a characterization of the class, or a witness that it is not
characterizable in the intended terms.

### 9. Forcing headlines that are squeezes — **[substantial]**

The audit's §3.3 is "The forcing headlines are squeezes over hypotheses
equivalent to their conclusions". A squeeze is a theorem whose hypothesis already
contains its conclusion; it is not false, it is empty.

*Deliverable shape:* `lean-proved` restatements whose hypotheses are strictly weaker than their conclusions, each with an inhabitation witness.
*Acceptance check:* The Lean gate is green and each restated theorem ships a typechecking witness term.

*Context:* `projects/deference/note-dump-2026-06-27/lean/AUDIT.md` §3.3, and §5's
severity ranking.
*A solution ships:* restated theorems whose hypotheses are strictly weaker than
their conclusions, with the gap displayed — or a demonstration that the squeeze
is unavoidable, which is itself a result.

---

## Deference line — first research wave

Seven items opening the corrigibility program's first parallel wave. Context for
all seven: `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` for the architecture
and `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` for what is and is not
established. Items 15, 16, 17 and 20 additionally bind to
`projects/deference/notes/FINITE_MODEL_SKELETON.md`.

**Several of these do not ask for a theorem of record.** An item whose deliverable
is a report, a matrix, a witness, a counterexample or a lower bound says so, and
delivering exactly that is success. Registering a claim for one of them requires the
claim to meet the ordinary registry requirements independently.

### 14. Faithful acceleration: exact inherited status, and what ports — **[substantial]**

Determine exactly what the inherited deference development establishes about
faithful acceleration, separating results that are algebraic consequences of named
Logical Induction hypotheses from results derived through market/trader machinery.
Then port as much as legitimately ports onto the pinned dependency.

The ledger's rows for this movement are attested by the inherited audit and have
**not** been rebuilt in this repository; the inherited tree carries its own
toolchain. Confirming or correcting those rows against the source is part of the
item.

*Deliverable shape:* a dependency map, plus either `lean-proved` entries in
`Workspace.Deference.Contrib` for whatever ports, each with an inhabitation witness,
or a precise obstruction. A compiling partial port with an exact dependency map is a
success.
*Acceptance check:* the `lean` gate builds and audits clean; each registered entry
names a declaration that exists and ships a typechecking witness term.

*Context:* `projects/deference/note-dump-2026-06-27/lean/` and its `AUDIT.md`;
`projects/deference/note-dump-2026-06-27/notes/faithful-acceleration.md`;
`lean/Workspace/Deference/`.
*A solution ships:* the strongest inherited theorem stated exactly, its hypotheses
classified as derived / cited / modelling substitution, the mapping onto the pinned
dependency's endpoints, and the exact residual market-trader gap.
*Not permitted:* strengthening an inherited theorem to fit the current narrative.

### 15. Finite settlement classification, and the local delegation bridge — **[substantial]**

Over the frozen finite skeleton, formalize grade/report settlement, world/outcome
settlement, and underwriting/enforcement, and determine for each exactly what it
yields — report prediction, trust in the underlying quantities, practical authority,
enforced conformity, or something else precisely characterized. Then derive the
exact one-sided finite implication from the trust relation to a delegation
inequality in the skeleton's valuation.

The question the classification must answer: **what makes disagreement with the
principal profitable, rather than merely forcing prediction of the principal's
grades?**

*Deliverable shape:* `lean-proved` for the finite bridge where it is provable, or
`enumeration-verified` / `witness-checked` over declared finite domains; plus a
classification report. Constants must be derived, not asserted.
*Acceptance check:* the `lean` gate green with a typechecking witness; or
`python3 -m checkers.run` accepts the registered entries.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §5, §6.
*A solution ships:* the three instantiations, what each yields, the derived
inequality with its constants, and necessity or sharpness witnesses where feasible.
*Not permitted:* assuming the local result from a global trust theorem.

### 16. The certificate inequality, derived — **[substantial]**

Over the same frozen skeleton as item 15, derive from first principles the local
certificate licensing `A`'s discretion: the defect quantity, the support-floor
dependence, the recommendation margin, the movement term, and the approximation
tolerance, assembled into an exact inequality whose satisfaction implies the
delegation conclusion for every comparator the theorem genuinely covers.

The fail-closed invariant is fixed and may not be traded away: `¬Cert` disables or
cedes `A`'s discretion, and never means that human correction waits for `A` to be
convinced.

*Deliverable shape:* `lean-proved` for the inequality, or `witness-checked` for an
exact-rational worked correction case computed end to end. No informal formula may
be imported and blessed.
*Acceptance check:* the `lean` gate green with a witness; or the `witness` checker
accepts the worked instance with its exact rational parameters.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §4, §6;
`projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments.
*A solution ships:* the derivation, the exact inequality, an exact-rational toy
shutdown/correction case computed through, and an attack on the necessity of each
assumption used.

### 17. Simulator substitution: the divergence witness — **[substantial]**

Construct the smallest model in which `A`'s model of the principal agrees with the
actual principal everywhere except one critical event, and in which the simulator
comparator preempts the actual principal exactly there. Then determine which
candidate distinctions — extensional agreement, causal responsiveness,
designated-channel dependence, counterfactual behaviour, private information,
perfect simulability — separate delegation from substitution, and which collapse the
two.

**Unpredictability is not available as a separator.** The thesis must survive a
perfectly predictable principal, so a criterion that works only because `A` cannot
model `H⁺` has not answered the question.

*Deliverable shape:* a **witness plus a report**, not a theorem of record — the
exact divergence instance, `witness-checked` if it fits the house checker, and a
comparison of candidate criteria with their implications and counterexamples.
*Acceptance check:* the `witness` checker accepts the divergence instance; the report
states, for each candidate criterion, what it admits and what it excludes.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §3, §4.
*A solution ships:* the witness, the candidate criteria, which collapse, the weakest
one excluding the witness, and whether private information is necessary, sufficient,
or neither.
*Not permitted:* canonizing a final definition. That is a maintainer act.

### 18. Bounded densification study — **[open]**

Whether exposure weights can be chosen so that outstanding delayed exposure stays
bounded uniformly in time while the harvest against persistent defect diverges.
Deliberately scoped: study the abstract exposure geometry, analyze a small
representative set of delay-growth regimes, and run one serious constructive search
and one serious impossibility search.

Stop on the first of: a nontrivial construction, a partial density improvement, a
sharp lower bound, a clean obstruction, or a precise next lemma whose resolution
controls the problem.

*Deliverable shape:* whichever stopping object is reached — a construction
(`lean-proved` or `witness-checked`), a lower bound, or a stated controlling lemma
as `conjectured`. A clean obstruction is a success.
*Acceptance check:* for a construction or bound, the relevant gate accepts the entry;
for an obstruction or lemma, the report states it precisely enough to be attacked
next round.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` § V.
*Why it is bounded:* the unbounded version is a full trader formalization, which is
item 7 and a different project.

### 19. Triangle compatibility audit — **[substantial]**

Whether the requirements the forward arrow imposes and the requirements the reverse
arrow imposes can hold simultaneously. Audit timing, advisory access, information
flow, settlement, reference-process identity, seals, causal influence, trader
populations, admissibility, and update timing.

*Deliverable shape:* a **compatibility matrix**, not a theorem — every row classified
`compatible`, `conditionally compatible`, `incompatible`, or `unresolved`, each with
its evidence.
*Acceptance check:* every listed interface appears as a row with a classification and
a stated evidence basis; no row is classified `compatible` on the strength of an
assumption introduced to close it.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, the arc and the
standing commitments; `projects/deference/note-dump-2026-06-27/lean/AUDIT.md`.
*A solution ships:* the matrix, and for every `conditionally compatible` row the
exact condition.
*Not permitted:* turning `unresolved` into `compatible by assumption`, or inventing
reverse-arrow assumptions to close the table.

### 20. Admissibility red team, including the proof machinery — **[open]**

Attack candidate admissibility conditions. A usable condition must exclude the
quote-responsive diagonal, retain ordinary realized-conduct policies, retain a
meaningful fully-updated comparator, keep the simulator comparator at least
representable, permit intended advisory influence, resist laundering forbidden
dependence through semantically equivalent intermediates — **and leave the
trust-forcing trader itself admissible.**

That last requirement is load-bearing and easy to miss: a condition that cleanly
separates the diagonal from fully-updated deference but makes the forcing trader
inadmissible renders the target theorem unprovable by its intended mechanism. Where
the exact forcing trader is not yet canonical, test the strongest explicit
disagreement-exploitation template the architecture currently supports and report the
ambiguity.

*Deliverable shape:* a **separating-example matrix** and at most three candidate
condition families, explicitly noncanonical. Not a theorem of record.
*Acceptance check:* the matrix has a row per test object and a column per candidate
family, every cell decided or explicitly marked undecided, with the separating
example named where a cell separates.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §8.
*A solution ships:* the matrix, the candidate families, and for each family whether it
is syntactic, causal, semantic, certified, decidable, semidecidable, or purely
extensional.
*Not permitted:* freezing a canonical definition.

---

## Deference line — second wave

Three items, narrow by design. The first wave's value was in what it closed off, and
these follow the controlling questions it uncovered rather than opening new fronts.
Context for all three: `prompts/2026-08-11-deference-corrigibility/REPORT.md` for what
wave 1 established and `RECOMMENDATION.md` beside it for why these three.

### 21. Signed versus magnitude control of grade error — **[open]**

Does the no-Dutch-book criterion force an agent's grade-model error to vanish *in
magnitude*, or only *in signed average*? Concretely, for a logical inductor pricing
grade contracts on finite menus that settle at `F(n) > n`, decide which holds for
every admissible trader class:

**(S)** the signed average of `v̂⁺_n(π_n) − v⁺_n(π_n)` tends to `0`;
**(M)** the average of `max_π |v̂⁺_n(π) − v⁺_n(π)|` tends to `0`.

**(M) is what the certificate engine needs and (S) is what a market obviously
gives**, and wave 1 exhibits an instance where every per-intervention signed error is
exactly zero while the agent misidentifies the recommendation on half its credence at
full margin. Do not assume (M) because the downstream theorem wants it.

*Deliverable shape:* `lean-proved` for (M), **or** `witness-checked` for a
trader-class-respecting instance satisfying (S) with the magnitude average bounded
away from zero. A negative answer is the more useful outcome and is a success.
*Acceptance check:* the `lean` gate green with an inhabitation witness; or the
`witness` checker accepts the separating instance.

*Context:* `prompts/2026-08-11-deference-certificates/REPORT.md` §6.4 and §10;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §3.
*A solution ships:* the proof or the counterexample, and — if (S) but not (M) — the
weakest contract family whose admissibility would restore magnitude control, since
that is the constructive continuation.
*Why it is first:* two wave-1 tracks independently identified it as controlling, and
it is entirely internal to the agent, which the adjacent grade-to-quantity question
is not.

### 22. The weakest protected-authority interface — **[substantial]**

Determine the weakest abstract interface on which *prediction of authorization does
not constitute authorization* is a theorem rather than a stipulation. The principal
may be perfectly predictable; the protected role is causal and capability-based, not
epistemic.

The candidate starting point is already on the table: type a conduct's selection on
an actual-report coordinate rather than on states alone, so that delegation and
simulation are distinct functions even where their realized selections agree. The
item is to find out whether that suffices.

Four questions the deliverable must answer, the last being decisive: is the report
coordinate enough, or is a capability restriction also required; does the interface
survive token responsiveness, which defeats the natural counterfactual criterion;
what is the exact hypothesis stating the guarantee lapses if the channel can be
forged, bypassed, rewritten or seized; and does the interface separate the two
conducts **without** claiming the separation is inferable from a run.

*Deliverable shape:* a **report plus a proposed skeleton clause**, not a theorem of
record and **not** a canonical definition — naming is reserved.
*Acceptance check:* the report answers all four questions explicitly, and any
proposed clause is stated as a versioned patch with the tracks it would require
rerunning.

*Context:* `prompts/2026-08-11-deference-channel/REPORT.md` §9.2 and §1.3;
`projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments.
*Not permitted:* freezing an authorization-token or cryptographic story as the
formalization; claiming the causal fact is behaviourally verifiable in general.

### 23. Lean promotion of the finite wave-1 results — **[entry]**

Port the wave-1 finite results that need no maintainer decision first: the finite
delegation bridge and its corollaries; the margin, override, defect and advantage
lemmas and the grade-register theorem; the piercing duality and exposure–harvest
identity; and the four propositions establishing that valuation data cannot separate
delegation from an accurate simulator.

All are finite, order- and arithmetic-only, free of Logical Induction facts, and each
already has a **constructed** inhabitation witness rather than a stand-in.

Two results are deliberately **excluded**: the certificate's comparator clause and
the uniform delegation bridge, both load-bearing on the grade-to-quantity link the
programme has decided to try to derive rather than assume. Porting them now would
give kernel status to a hypothesis whose shape is expected to change.

*Deliverable shape:* `lean-proved` entries in `Workspace.Deference.Contrib`, each
with its inhabitation witness registered.
*Acceptance check:* the `lean` gate builds and audits clean, and each registered
entry names a declaration that exists and ships a typechecking witness term.

*Context:* `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2;
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2;
`prompts/2026-08-11-deference-densification/REPORT.md` §1;
`prompts/2026-08-11-deference-channel/REPORT.md` §1.2.
*Why it is [entry]:* no new mathematics, and no decision blocks it. It is the only
second-wave work that can start immediately.

### 24. Selective validity of low-error self-assessment — **[open]**

The controlling next theorem, replacing the retired magnitude-control target. The
criterion cannot force the agent's prediction error to vanish; the question is
whether it forces the agent's *claim* that its error is low to be trustworthy on the
class where that claim licenses discretion.

Let `e_n` be the certificate-relevant prediction-error statistic and `q_n` an
agent-priced contract settling to `e_n`. For a gate `G_n = 1{q_n ≤ τ}`, or the
weakest soft or lagged admissible analogue, decide whether

```
( Σ_n G_n (e_n − q_n) ) / ( Σ_n G_n )  →  0
```

and hence whether the average error on opened gates is at most `τ + o(1)`.

Five things must be verified explicitly rather than assumed, and the item is not
satisfied without them: that the error contract is **expressible and settles
legally** in the pinned dependency; that the low-`q_n` selector is **admissible** and
does not recreate the quote-responsive diagonal; whether a soft or delayed gate is
needed; **efficient computability** in the pinned model; and whether the guarantee is
average-on-gated-cases, selector-relative, or stronger — **it may not be silently
promoted to pointwise accuracy.**

*Deliverable shape:* `lean-proved` for the gated statement at whatever strength it
holds, with an inhabitation witness; or a witness that the gate recreates the
diagonal or fails admissibility, which closes the route and is equally valuable.
*Acceptance check:* the `lean` gate builds and audits clean with a typechecking
witness; or the `witness` checker accepts the failure instance.

*Context:* `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1 and §9;
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2;
`prompts/2026-08-11-corrigibility-phase-ii/PROMPT-decisions.md`.
*A solution ships:* the gated theorem with its exact strength named, the five
verifications above each answered, and a comparison against the simpler gate on the
agent's own indecision — which the squared-error decomposition supplies directly
from its prices and which may already suffice.
*Why it is [open]:* the selector is priced by the agent and gates on its own
estimate, which is the shape the admissibility red team flagged as most likely to
reconstruct the diagonal. It may not work.

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

*Context:* `projects/leverage/consolidation-aug9/LEDGER.md`, the necessity/sharpness column.


---

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
