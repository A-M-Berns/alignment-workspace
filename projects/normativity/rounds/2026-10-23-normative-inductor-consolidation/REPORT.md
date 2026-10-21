# Report — PR #129: final Normative Inductor consolidation

| | |
|---|---|
| Prompt author | the maintainer (`prompts/2026-10-23-normative-inductor-consolidation/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Base | the branch of PR #129 at `c43e7fbe` |
| Date | 2026-10-23 (the branch's round sequence; the machine's calendar date was 2026-10-20) |

## Corrections and deviations (`AGENTS.md` §8)

The dispatch's description of the branch is accurate: `Admission` carried provenance only,
`compileAt` returned the empty bundle on a failed check, the witness's strength occurrence was
gone before its consequent was refuted, and the wiki described conformance as a distance. One
deviation: the dispatch did not name a round directory; this round is dated 2026-10-23 to
continue the branch's sequence (10-20, 10-21, 10-22) rather than by the calendar.

## 1. Admission, entitlement, authorization

Four roles, now four objects. **Provenance** is `WarrantInductor.Origin`: the exposed
obligation occurrence a warrant realizes — the former `Admission`, renamed because provenance
was its only content. **Entitlement** is `WarrantInductor.Entitlement O G Expresses`, extending
`Origin` with three conditions: the origin is admitted by the protocol at the boundary's
history (`Protocol.Admitted`), its account carries a live leaf (`Fate.live ∈ fates`), and the
form expresses the origin's anchor under the declared relation `Expresses`. **Verdict
licensing** is `NormState.Licensed`, unchanged, and is not a prerequisite of enforcement: no
substantive reason was found to make a licence to select a verdict into authority to introduce
a constraint, and the two are different authorities over different objects (a verdict value;
a row). **Operative enforcement** is survival under the docket and the settlement plus an
enforced compile outcome.

What is proved: `warrant_inductor`'s provenance conclusion now says every held substantive
row is an *entitled* survivor's (`Entitlement.Entitled`: exposed, admitted, live, expressed),
so the compiler enforces only entitled warrants. What is typed: `Protocol.Admitted` is the
protocol's and `Expresses` the application's; nothing derives that the obligation was
legitimately incurred — that remains the obligation state's, through the Integrity segment
that produced it (item 128, narrowed). What the account supplies with content: liveness. In
the fixture's `state₁`, where the first obligation is answered, no entitlement under any
`Expresses` relation may trace an occurrence to it (`WarrantInductorWitness.answered_not_entitled`);
the runs are entitled in `state₀`, where both accounts are live (`account_live`). The fixture's
protocol is the trivial one, so `Admitted` and `Expresses` are not exercised there; item 128
asks for the first protocol at which they are.

The liveness reading — discharge retires the warrant — is agent-decided and queued for the
maintainer (`DECISIONS.md`, *Awaiting the author*), since whether a reason outlives the debt
that incurred it is taste the mathematics does not decide.

## 2. Accountable compilation

`compileAt` now takes the compiler's `CompileResult` (a witness, a Farkas conflict certificate,
or `unknown`) and its `outcome` is one of three: `idle` (the state has no rows), `enforced B`
(the witness checks into the region; every row held), `withheld B res` (rows present, no checked
witness; the result carried). The four desiderata:

- **Conservation.** `outcome_obligations`: the obligations present are the state's bundle
  whatever the result; `Outcome` has no field that drops, renames or reweights an occurrence,
  and the survivors and the accounted state are not inputs of the compile.
- **Transparency.** `outcome_idle_iff` (idle iff no rows); `withheld_of_not_check` (a supplied
  witness outside the region withholds — nothing is known about feasibility);
  `conflict_withheld` and `conflict_region_empty` (a conflict certificate over allowed rows
  refutes the region — the system is infeasible, by the composition module's `conflict_sound`);
  `unknown_withheld` (no result, nothing known). No second conflict theory.
- **Evaluation.** `AdapterProtocol.restrict served` cuts the services to the served dates and
  `residual_restrict` says the residual grows by exactly the dropped services' transport mass,
  which the Progress bound charges at `D`. Scenario B uses it: the date-9 service is declared,
  its certificates fail, and the restricted protocol's residual is `1/2` against the declared
  `1/4` (`residual_restricted`).
- **Preservation.** `WarrantSchedule.day_value_eq_zero_of_bundle_nil`: a date with no held
  rows has day value zero at every world, so the account's net worth and the liability bound
  are unchanged across withheld dates, and `isLogicalInductor` is indifferent to them.

The theorem's hypothesis `hcheck` became `henf : Enforced (N s) (res s)` at the service dates,
and its conformance conclusion is stated at enforced dates (`Enforced N res ↔ N.bundle = [] ∨
∃ w, res = compiled w ∧ check`, `enforced_iff`). A withheld date carries no conformance claim;
the docstring says so.

## 3. The dynamic witness: two scenarios

**Scenario A** (`WarrantInductorWitness`, kept) adds `undercut_summary`: at the undercut the
applicability and the strength leave, the premise and `Z` stay; the region loses `P(X∧A) ≥ 3/4`
and `P(X∧A∧Y) ≥ 1/2` — at date 5 it admits the point pricing both at `0` — and keeps `P(Z) ≥
3/4`; with `exclusion_lapses`, the certified guidance on the principal matter is lost and
nothing replaces it while the independent warrant's guidance is untouched.

**Scenario B** (`WarrantInductorRebuttal`, new): the same grounds, settlement, coherence rows,
tolerance and deductive process, with a quiet docket.

1. `operative_before`: the strength is a survivor and its row is held at every date before 8.
2. `antecedent_open`: at 8 the settlement pins `Y` and `X∧A∧Y` false and leaves `X∧A` open; the
   date-9 region contains `(1,1,0,0,1)` and forces `P(X∧A) ≥ 3/4`.
3. `withdrawn`: from 8 the strength's outcome is `rebutted` and it is not a survivor.
4. `contraposition_blocked`: the date-9 bundle with the specialized strength row appended —
   `2/3·P(X∧A) ≤ 0` — has empty region, against the applicability row's `P(X∧A) ≥ 3/4`.
5. `enforced`, `inductor`: every date is enforced and every held row conforms within `1/400`.
6. `liability`: `−72` at every plausible world at every date, with the all-true world slack
   before the refutation and the world `X, A, Z` true, `Y` false after it; the applicability row
   is now among the rows the second world dominates (`dom_wAY'`).

**The same question before and after.** `P₁` (act on the conclusion or refrain; adequate set
*act*) at dates 4 and 9, with the four levels the dispatch asked to keep apart:

- constraints: `withdrawn`;
- region: `region_flips` — refraining at most `1/3` at date 4, at least `3/4` at date 9;
- guarantees: `no_certificate_after` — no `Excludes` and no `Margins` certificate for `P₁`
  exists on the date-9 bundle, so the adapter theorem cannot be applied to this question there;
  the former recommendation is no longer warranted by anything the construction certifies;
- behavior: `same_question` — at the realized market the gate's mass on acting is at least
  `24/25` at date 4 and exactly `0` at date 9, because the enforced pin holds `P(X∧A∧Y) ≤ 1/400
  < τ` and the enforced applicability row holds `P(X∧A) ≥ 3/4 − 1/400`.

The behavioral reversal is not a normative reversal: the adequate set is not re-declared, the
gate follows the pinned price of the refuted conclusion, and whether refraining is adequate
after the refutation is not answered. The actual-market results of Scenario A are retained;
nothing is stipulated.

## 4. The exposition

`THEOREM_STORY.md` §G, `wiki/Normative-Inductor.md` (new sections *Entitlement, not licence*
and *The interface: a public defect and certified bounds*; the consolidated theorem under *The
conditional theorems*), `wiki/Normative-Induction.md` (the decision-interface status),
`wiki/Theorem-Spine.md` (Theorem 7.6; the duplicated 7.3 renumbered) and `THEOREM.md` tell one
story: the Normative Inductor is an *interface* — a nonnegative public defect per service, a
certified bound on each response-relevant functional in terms of it, the work relation and
amplification, which `Evaluation.progress_bound` consumes through `PracticalUptake` — and the
projection enforcer (distance defect, vertex representation, distance conformance) and the
rowwise enforcer (per-row tolerance, certificate-mass transport, displayed inadequate excess)
are two realizations of it. Neither is retired: neither guarantee implies the other without a
Hoffman-type constant (item 125). The two claims are separated on every page: *warrants
constrain the prices* (conformance, from an enforced outcome and the liability bound) and
*warrants produce warranted guidance about the adapter* (the adapter conclusion and Progress,
conditional on the adequacy semantics and the certificates); neither says the warrants are
correct.

## 5. Audit of the flagship theorem

- *Is the admission hypothesis substantive?* It was a labelling. It is now `Entitlement`, with
  one condition of content read off the account (liveness), one of the protocol's
  (`Admitted`) and one declared (`Expresses`); the fixture exercises the first.
- *Same state and market?* Yes: the certificates cite `(N s).bundle = W.bundle s` (by
  `henf`), the gate reads `W.market DP s (F.ι j)`, the enforcer's realized strategy is
  `enforcementStrategy (W.realizedPres DP n) n` by `rfl`.
- *Temporally unconstrained states?* Yes, and the docstring now says so: the theorem is
  pointwise in `n` over an externally supplied state process.
- *Conformance conditional on compilation?* Yes: stated at enforced dates only; a withheld date
  trades nothing and keeps its obligations.
- *Liability versus computability?* Separate hypotheses (`B`, `hliab` against `process`, `hE`),
  separately discharged in both runs.
- *`Excludes`, `Margins`?* Checkable geometric conditions on the bundle (decidable given the
  citations); their normative meaning enters only through `A`, `A₁` and `lam`.
- *Progress informative in the witness?* `progress_le`: `≤ 37/100` against the trivial `1`;
  the gate realizes the adequate response with mass at least `24/25` and `99/100`; the adequate
  response costs `1/10`; the unserved quarter is the largest term.
- *Restated assumptions?* The provenance half of conclusion 2 is soundness of the compile (an
  entitled survivor's row and nothing else reaches the market), stated as such; it is not an
  inequality. No other conclusion restates a hypothesis.

The signature changed shape (`ent`, `res`, `henf` for `adm`, `wit`, `hcheck`) and gained no
hypothesis and no conclusion.

## What this round does not establish

- That any entitlement is legitimate: `Admitted` and `Expresses` are typed; the fixture's
  protocol makes both trivial (item 128).
- That a warrant should lose standing when its obligation is answered: adopted, queued.
- Distance-to-region conformance for the rowwise realization (item 125); the bankroll beyond
  one reopening (item 126); the `defeaters` attack reading (item 127) — all unchanged.
- Whether refraining is adequate after the refutation in Scenario B: not a mathematical
  question, and not answered.
- A full-protocol Progress theorem that keeps unserved services in the statement rather than
  restricting to the served ones: `residual_restrict` is the accounting; the restriction is
  the construction.

## Verification

- `lake build` of the whole library: `Build completed successfully (4095 jobs)`.
- `python3 tests/audit_axioms.py`: `AXIOM AUDIT: 3390 results across 108 files, all within
  ['Classical.choice', 'Quot.sound', 'propext']`.
- `python3 projects/normativity/rounds/2026-10-23-normative-inductor-consolidation/tests/run.py`:
  `Ran 13 tests … OK`.
- `python3 -m checkers.run`: `73 entries, 1 adjudicated here` for the normativity registry,
  both registries ok; `python3 -m checkers.workspace_state --check`: `WORKSPACE STATE: valid —
  6 projects, 178 modern claims, … 125 rounds`; wiki bindings clean (3 verified); wiki links
  clean.
- `python3 tests/run.py` at the root: `ALL GREEN (80 project(s))`.

Claims whose status changed: none. `inductor.warrant-inductor` and `inductor.witness` keep
class and declaration under the revised hypotheses; `inductor.rebuttal-run` and
`inductor.contraposition-blocked` are added, both `lean-proved`.

## Merge recommendation

**Ready.** The result the dispatch names is now exactly what the mathematics says: a system of
defeasible warrants, admitted under a stated interface (entitlement, with its typed parts
named), revised by defeat and settlement (the grounded rule, rebuttal), compiled into enforced
rows with a typed outcome that conserves what it withholds; under enforced and affordable
dates the market is a logical inductor, every held row conforms within the tolerance, and with
certified exclusion and margins the adapter's inadequate mass and the Progress statistic are
bounded. Two runs exhibit the two revisions, and in the second the same question's guidance is
withdrawn and the adapter follows the market. The two reservations of the integration round
remain as mathematics, not as defects: conformance is rowwise and the distance reading is a
different realization's (now said on every page), and the `defeaters` reading is
agent-decided. The remaining open questions — legitimate admission, warrant learning, repeated
reopenings — are the ones the dispatch names as not required to merge.

## Items

Narrowed: 35 (third instance), 128 (entitlement landed; the nontrivial protocol, the
`authorized`–account relation and the segment reading remain). None filed.

## Registrations

`inductor.rebuttal-run` (`WarrantInductorRebuttal.inductor`, item 35);
`inductor.contraposition-blocked` (`WarrantInductorRebuttal.contraposition_blocked`, item 113).
Notes updated on `inductor.warrant-inductor` and `inductor.witness`. Listed and not registered:
every other declaration of the three files.

## Names, provisional

*origin*, *entitlement*, *entitled*, *expresses*; *compile outcome*, *idle*, *enforced*,
*withheld*, *obligations present*; *served protocol*; *Scenario A*, *Scenario B*, *same
question*.

## Outstanding maintainer actions

1. **Rule on entitlement's liveness condition** — does discharge of the obligation retire the
   warrant (landed) or only the debt: `DECISIONS.md`, *Awaiting the author*, the 2026-10-23
   entry.
2. The actions of the three earlier rounds stand: the reading of `defeaters` (item 127); M1,
   M2, M5 and the reopened bankroll (`DECISIONS.md`, *Awaiting the author*); close PRs #102 and
   #103; merge PR #129, which carries four rounds.
