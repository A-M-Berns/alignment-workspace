# Report — Normative Induction: end-to-end integration and theorem consolidation

Dispatch: `prompts/2026-10-22-normative-inductor-integration/PROMPT.md`, on the branch of
PR #129 at `b1c17d30`. Prompt author: the maintainer. Executor: Claude Fable 5.1 (Anthropic).
Date: 2026-10-22.

| | |
|---|---|
| Lean | `OddsBankroll.lean` (22 declarations), `WarrantForce.lean` (67), `WarrantInductor.lean` (57), `WarrantInductorWitness.lean` (111), new; `WarrantEntitlement.lean` (315, revised), `EndToEndWitness.lean` (127, revised) |
| Exact rationals | `src/inductor.py`, 22 checks under `tests/` |
| Documents | `HANDOFFS.md` (the audit of the arrows), `THEOREM_STORY.md` (the paper-facing account, §§A–F with the learning claim) |
| Registered | `inductor.grounded-survivors` (112), `inductor.conformance` (39), `inductor.certificate-transport` (124), `inductor.warrant-inductor` and `inductor.witness` (35), all `lean-proved` |
| Items | 124–128 filed; 35, 39, 112, 115, 116, 118, 121 narrowed |

## Corrections to the prompt (`AGENTS.md` §8)

1. §3 states that occurrence 3 "cites applicability occurrence 2 and carries `{2}` as a
   defeater, yet occurrence 3 survives when occurrence 2 is undercut." Confirmed, and it was a
   defect of the rule, not of the fixture: `Grounds.survivors` consumed the occurrence's own
   port and `settleOutcome`, retired one step along `cites`, and read `defeaters` not at all.
   The fixture's later refutation of `Y` hid it exactly as the dispatch suspected. Repaired by
   the grounded rule (§P0 below); the two earlier rounds' documents carry dated notes where
   they describe the strength occurrence as surviving until `n_E`.
2. §4 anticipates "a potential architectural mismatch between the older projection-based
   Normative Inductor and the rowwise violation-proportional trader." The mismatch is real but
   lies elsewhere than the trader's shape: the projection enforcer and every computability
   theorem run on the *deductive* market (`DeductiveEnforcement.history DP`), while PR #129's
   rowwise trader and its bankroll ran on the *assessment* market
   (`EnforcementPreservation.history L`), and no theorem relates the two firms. This round runs
   the rowwise trader on the deductive market; the assessment-market bankroll becomes an
   instance of the same abstract account. The two enforcer shapes are not bridged
   (`HANDOFFS.md`, the market arrow; item 125).
3. §5 asks for the practical certificate to be derived from "the existing adequacy-set,
   soft-gate, Lipschitz adapter" results. The soft-gate theorems are stated at a *region point*
   (`Region u A τ`, `Margin u A τ δ`, `Within b u d`), which rowwise conformance does not supply.
   The derivation goes through a displayed-margin route instead (certified bounds transported
   to the displayed price, then `softGate_massOff_le_displayed` with a synthetic region point);
   `Within` is never established at the real market. Not a deviation from the ask, but the
   route the dispatch names is not the one that works.
4. §1 writes the target conformance as `d_t(P_t, K_t) ≤ δ_t`. What is proved is rowwise:
   every row's excess at the displayed price is at most `tol_t`. The conversion to a distance
   is not established and is filed (item 125); the certificate transport is the conversion that
   is established, to the bounds a licence certifies and an adapter reads.

## P0 — the canonical semantics

**The grounded rule** (`WarrantEntitlement.lean`). An occurrence is *undercut* when its own
port or a port of its defeat set is defeated; *live given* an identity set `S` when not
undercut, kept by `settleOutcome`, and citing into `S`; the **active identities** are the least
fixed point of `activeStep` from `∅`, reached in `G.length` steps (`activeIds_fixed`, by the
chain of iterates and a cardinality argument); the **survivors** are the occurrences live given
the active identities. `mem_survivors` is the characterization: in the grounds, not undercut,
kept, citing a survivor. Antitone in the settlement (`survivors_anti`, as before) and in the
docket (`survivors_anti_docket`, new). The one-step retirement, `citesRetired` and `retiredIds`
are gone; propagation along citation chains of any length needs no closure on the settlement
(item 121 answered). A dangling or cyclic citation is inactive.

`defeaters` is read as *ports whose defeat also undercuts the occurrence* — the reading the
2026-10-20 ruling describes ("a warrant's forms share one defeat condition") and the fixture
used. The alternative reading, undercutting *occurrences* that defeat when themselves active,
needs the grounded extension with attacks and is filed (item 127).

**One bundle, four views** (`WarrantInductor.lean`, `NormState`). The normative state is the
record state with the structural rows. Its bundle is `forcedBundle` of the seed whose items are
the survivors', with the live structural rows and the pins. `region_iff` reads it by
occurrence; `bundle_eq_settledBundle` says it is the settled bundle when there are no
structural rows; `interval` is `forcedInterval` on the same seed; the enforcer's rows are its
rows through `toForceRow`; `Supported` and `Licensed` are `SupportedOn` this bundle. The
record's `Licensed` (`WarrantEntitlement`) is the same predicate on the settled bundle, and
`Admissible`, `Supported`, the record's position (`trace`) and `positionOf_eq_zero_of_region`
all now read the settled bundle rather than the port-only one.

**Acceptance criterion.** Given a state, `NormState.bundle` is the one answer to which rows
are enforced; `warrant_inductor`'s third conclusion is that every enforced row is a survivor's
row under its citation, a live structural row, or a pin (`mem_compileAt`).

**Well-formedness and admission.** `Grounds.WellFormed`: identities unique, citations resolve;
then a survivor's citation names exactly one survivor (`cited_unique`). `Admission O G`: every
occurrence realizes an exposed obligation occurrence — a typed link to the accounted state,
distinct from the record's authorized verdict-selection events.

## P1 — the integrated theorem

**The affordability interface** (`OddsBankroll.lean`). `Account`: a trader playing
`enforcementStrategy (pres n) n` against a history with rational quotes, assessed at live
worlds, capped there. The odds bankroll `−cap·ρ` and the reopened bankroll `−cap·ρ(2+ρ)` are
proved once; the assessment market (`WarrantEntitlement.assessmentAccount`) and the deductive
market (`WarrantForce.WarrantSchedule.account`) are its instances at cap `3`, the second from
the source firm's own floor `tradingFirmTrader_netWorth_floor`.

**The enforcer on the deductive market** (`WarrantForce.lean`). `WarrantSchedule`: fragment
map, compiled bundle per date, tolerance. `enforcer : EffectiveEnforcer` holds the bundle's
rows at the calibrated intensity `(ε_n + A_n)/tol_n²`; `market` is the augmented deductive
market; `isLogicalInductor` from a liability bound and `EffectiveEnforcerComputation`, the
latter proved for finite-phase schedules (`computation`: the trade map is a fixed syntax tree
in the date and the intensity, `tradesOf_primrec`, `tradesOf_stepBundle_primrec`).

**Conformance at the realized market.** `rowViolation_le_tol`: with a rational cube point in
the day's region, every row's violation at the displayed price is at most `tol_n`. The slack
and volume terms of `weighted_square_le_pair` are discharged by `marketMaker_day_value_le_cube`
and `Strategy.abs_value_le`; the calibrated intensity closes with
`rowViolation_le_of_intensity_ge`. `excess_le_tol_of_admitted` extends it to every row a
certificate may cite (bundle rows and cube faces).

**Transport.** `FunctionalCert` (multipliers on rows summing to a functional), `value`,
`mass`; `le_of_excess`: `ℓ·p ≤ value + mass·δ` where every positively weighted row's excess is
at most `δ`. `BoundCert.transport`, `bracket_at_market` (a supported verdict's bracket at the
displayed price, widened by `mass·tol` on each side), `functional_at_market`.

**The adapter** (`WarrantInductor.Problem`). Scores are affine functionals of the fragment's
prices; the gate is `GatedChoice.softGate` on them; the public defect `defectOf` is the
displayed inadequate excess; `Excludes` and `Margins` are certificate conditions on the bundle.
`scoreR_le`, `scoreR_ge` at the market; `massOff_le`: inadequate mass at most
`κ·defectOf`; `defectOf_le`: at most `massCap·tol`; `practicalCert`. `AdapterProtocol.uptake`
derives `PracticalUptake`.

**The theorem.** `warrant_inductor` — signature and interpretation in `THEOREM_STORY.md` §D;
`warrant_inductor_of_slack` is the one-slack-world form. Its assumptions, sorted:

| kind | hypothesis | status |
|---|---|---|
| semantic | `Admission`, the adequacy losses `lam`, `εad`, `D` | imported, typed |
| normative state | `WellFormed`, checked witnesses, `Excludes`, `Margins` | checkable on the state; discharged at the fixture |
| protocol | `lamS`, `ρ` (budgets), `Γ` (amplification), `μ`, `T` | declared, as in `deductive_normative_inductor` |
| affordability | `−B ≤ netWorth` | discharged by `liability` / `liability_reopened` |
| computability | `DeductiveProcessComputation DP`; `EffectiveEnforcerComputation` | the first is the process's; the second discharged by `computation` |

Conclusions: Logical Induction over the deductive process; rowwise conformance at every
checked date and the provenance of every enforced row; the adapter's inadequate-mass bound and
the defect's bound; the Progress bound. Compared with PR #129's `warrant_normative_inductor`
and `inductor_run`: `ComputableMarket` and `PracticalUptake` were hypotheses there; both are
derived here, and the enforcer, the licence and the elimination read one bundle.

## P2 — the witness

`WarrantInductorWitness.inductor`: `warrant_inductor` at a five-sentence fixture with no
computability and no liability hypothesis. What is constructed, what happens to the warrants,
what the market guarantees and what the adapter does: `THEOREM_STORY.md` §E. The behavioral
statements: `gate_bounds` (`1/25`, `1/100`), `gate_nonconstant`, `exclusion_lapses`,
`bracket`, `liability` (`−72`), `intensity_pos`.

Coherence: three structural rows `X∧A ≤ X`, `X∧A∧Y ≤ X∧A`, `X∧A∧Y ≤ Y` (the dispatch's missing
relation included) as declared `StrItem`s of the state. `clearing` in `EndToEndWitness` stays
what it was — a stipulated price path, now documented as such — and nothing in this round's
witness is a stipulated price: the gate and the bracket are read at `W.market DP`, whose
values are not computed.

## Repairs to PR #129

- **Survivor semantics.** The one-step rule replaced by the grounded rule; `Fixture.survivors_eq`,
  `Fixture.rowsRebutted`, `EndToEndWitness.Run.survivors_eq`, `firstWarrantAt`, `rows5`,
  `regionRAt_iff` recomputed: the strength occurrence leaves at `n₀`. `Fixture.liability_rebutted`
  (registered `rebuttal.liability-rebutted`) keeps its statement with the recomputed schedule;
  `interval_XA`, `interval_XAY`, `hullMass_run` are unchanged in value.
- **Licensing.** `Admissible`, `Supported`, `Licensed` on the settled bundle (`SupportedOn` a
  bundle, generally); the countermodels re-proved; `EndToEndWitness.Run.licensed_at_entry`,
  `undercut_licences` on the settled bundle.
- **Records.** `trace` carries the position on the settled bundle.
- **Force.** The bankroll theorems are instances of `OddsBankroll.Account`; the warrant round's
  constant-intensity enforcer and assessment market are kept as that instance, and the
  deductive market carries the calibrated enforcer.
- **Workspace.** `PRIORITIES.md` had two `## Workspace friction` headings, the first introduced
  by the rebuttal round when it filed items 121–123; the duplicate is removed and the items sit
  before the friction section.

## What this round does not establish

- Distance-to-region conformance for the rowwise enforcer (item 125); the public defect is the
  displayed excess and the enforcer's guarantee is per row.
- Market computability beyond finite-phase bundle schedules and computable deductive
  processes; `DeductiveProcessComputation` remains an input of the general theorem.
- The bankroll for more than one reopening (item 126), or the sharp constant across one
  (item 123, unchanged).
- Legitimacy of admission: `Admission` is a typed map (item 128); the authorized events are the
  record's data.
- Soundness of any warrant, or adequacy of any declared adequate set; `Excludes` and `Margins`
  are sufficient conditions, and their completeness (whether every region-excluded response
  has a certificate) is item 118's LP-duality question.
- The undercutter-occurrence reading of `defeaters` (item 127).
- The two enforcer architectures (projection, rowwise) are not bridged; both are retained, on
  the same deductive market.

## Open problems, ranked

*Preventing the conditional Normative Inductor as stated:* none; the theorem is proved and
run.

*Preventing a general repeated-revision construction:* item 126 (repeated reopenings); item
123 (the sharp one-reopening constant and the cushion exploit against the pinned maker); item
125 (distance conformance, needed before the rowwise and projection enforcers can share one
public defect).

*Preventing the stronger normative-learning agenda:* item 128 (admission from the account);
item 118 (certificate completeness, which decides when the adapter's conditions are checkable
rather than supplied); item 127 (defeaters as occurrences); item 117 (strength selection), which
this round does not touch — strengths are declared and never learned.

## Verification

- `lake build` of the whole library: `Build completed successfully (4094 jobs)`.
- `python3 tests/audit_axioms.py`: `AXIOM AUDIT: 3320 results across 107 files, all within
  ['Classical.choice', 'Quot.sound', 'propext']`.
- `python3 projects/normativity/rounds/2026-10-22-normative-inductor-integration/tests/run.py`:
  `Ran 22 tests … OK`.
- `python3 tests/run.py` at the root: `ALL GREEN (79 project(s))`; `python3 -m checkers.run`:
  `71 entries, 1 adjudicated here` for the normativity registry, both registries ok;
  `python3 -m checkers.workspace_state --check`: `WORKSPACE STATE: valid — 6 projects, 176
  modern claims, … 124 rounds`.

Claims whose status changed: `rebuttal.liability-rebutted` keeps class and declaration with a
recomputed force schedule (the strength row leaves at `n₀`); `warrant.licence-chain`,
`warrant.supported-admissible`, `warrant.admissible-not-supported`,
`warrant.supported-not-licensed` keep class and declaration with `Supported` now on the settled
bundle. Five entries added, all `lean-proved`.

## Merge recommendation

**Ready, with two reservations stated as mathematics.** The three conclusions are proved on
one market for one normative state process, and the run discharges every hypothesis that a
theorem in the repository can discharge. The reservations: (i) conformance is rowwise, and the
reading "prices within `δ` of the region" that the wiki's Normative-Inductor page and the
projection theorems use is not what this construction proves — a reader comparing the two
should be told which guarantee is meant (item 125); (ii) the maintainer's open rulings from the
two earlier rounds (M1, M2, M5, the reopened bankroll) are unchanged by this round and the
grounded rule is agent-decided; if the undercutter-occurrence reading of `defeaters` is the
intended one, `undercut` changes and the survivors' fixed point becomes the grounded extension
(item 127).

## Items filed

124 (certified bounds at the displayed price — filed answered), 125 (distance conformance for
the rowwise enforcer), 126 (the bankroll across repeated reopenings), 127 (defeaters as
undercutting occurrences), 128 (admission from the accounted state). Narrowed: 35 (second
instance; computability and liability discharged), 39 (conformance registered), 112 (answered
by the grounded rule), 115 (the licence on the canonical bundle; transport across record
transitions remains), 116 (part (c) closed on 2026-10-21), 118 (completeness also for the
adapter's certificates), 121 (answered).

## Registrations

`inductor.grounded-survivors` (`WarrantEntitlement.mem_survivors`, item 112);
`inductor.conformance` (`WarrantForce.WarrantSchedule.excess_le_tol`, item 39);
`inductor.certificate-transport` (`WarrantForce.WarrantSchedule.bracket_at_market`, item 124);
`inductor.warrant-inductor` (`WarrantInductor.warrant_inductor`, item 35);
`inductor.witness` (`WarrantInductorWitness.inductor`, item 35). Listed and not registered:
`OddsBankroll.Account.netWorth_ge_neg_odds_reopened`, `WarrantSchedule.computation`,
`WarrantSchedule.isLogicalInductor`, and every other declaration of the four new files.

## Names, provisional

*grounded rule*, *active identities*, *undercut*, *live given*; *normative state*, *canonical
bundle*; *withholding compile*; *enforcement account*, *capital*; *warrant schedule*,
*calibrated warrant enforcer*; *functional certificate*, *mass*, *transport*; *excludes*,
*margins*, *public defect* (the displayed inadequate excess); *adapter protocol*; *warrant
Normative Inductor*.

## Outstanding maintainer actions

1. **Rule on the reading of `defeaters`** — shared defeat ports (landed, agent-decided) or
   undercutting occurrences (item 127): `DECISIONS.md`, the 2026-10-22 entry's first
   rejected alternative. The fixture is unchanged either way.
2. **The wiki's Normative-Inductor and Normative-Induction pages** describe conformance as
   distance to the region and `PracticalUptake` as a typed input; this round's status note on
   `Normative-Inductor.md` is one paragraph. The synthesis (which construction the page
   presents, and in what terms) is the maintainer's.
3. The actions of the two earlier rounds stand: M1, M2, M5, the reopened bankroll
   (`DECISIONS.md`, *Awaiting the author*); close PRs #102 and #103; merge PR #129, which now
   carries three rounds.
