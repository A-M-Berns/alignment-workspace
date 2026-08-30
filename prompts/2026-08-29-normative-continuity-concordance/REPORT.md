# Normative Continuity concordance and Lean spine — report

**Verdicts:** concordance `CONCORDANT WITH LOCAL REPAIRS`; formalization
`FORMALIZATION SURVIVES`. The checkpoint stays `AGENT-CONSOLIDATED`.

## Phase I — canonicalized artifact inventory

`projects/normativity/legitimacy/rounds/2026-08-29-normative-continuity-concordance/`:

| path | sha256 | role |
|---|---|---|
| `NORMATIVE_CONTINUITY.tex` | `644fb6a9…6524c` | source (Downloads `normative_continuity_refined (freeze).tex`, mtime 23:16) |
| `NORMATIVE_CONTINUITY.pdf` | `b3d74f12…9d665` | render of that source (tectonic, 14 pp.) |
| `PROOF_PASS.md` | `616818cf…4ef8` | the hostile proof-pass report |
| `src/fixtures.py` | `33db0094…d920` | the proof pass's fixtures, unchanged |

Full digests in the round's `ORIGIN.md`, recomputed by `tests/test_fixtures.py`. The three
older `.tex` files in Downloads (14:42, 16:57, and the pre-repair `(freeze).tex`) are
byte-identical to each other and predate the PDF; content features (single
wait-responsiveness assumption, `M_n`/`β(m)`, reach gate, expanded Step 2, `L_n^+`
freshness, qualified route-extinction lemma, Requirement 8 and `Met`-persistence cited in
the proof, adjacent-work paragraph, `agent-consolidated` note) identify the 23:16/23:17
pair as the checkpoint. Status gloss and the non-meanings are in `ORIGIN.md` and `README.md`.
No frozen Legitimate Evolution file was touched.

## Phase II — concordance

`CONCORDANCE.md` maps every substantial object to its source with quotations, commit
hashes, and a change classification, and carries the non-supersession map. Findings that
matter:

1. **No theorem conflict.** Every trace the synthesis admits satisfies the frozen LE carry
   law (`S ≠ ∅ → S ⊆ O_{t+1}`) and no-silent-loss; Grounded Replay is LE's theorem
   restricted from `Adm_t` to `L_n`.
2. **Undeclared reversals of frozen LE decisions**, inherited through the unfrozen
   Answerable Process page: successor freshness (LE A5/A11 withdrew it), same-batch
   open-and-resolve (LE A17 allowed it), `Due` read at the strict prefix (LE A34 read
   descriptive material from the current event), resolution gated by `κ_q` alone (LE
   A21/A22 gated it by `Permit`). Errata E1–E4.
3. **The no-rewiring rule is not new.** AP §6 Discipline is a *stronger* ancestor; Req 12
   is a deliberate weakening that the Lean proof shows still suffices. Erratum E5; the
   synthesis's §Scope sentence is corrected in the concordance, not in the checkpoint.
4. Smaller: S1 scope, `Met` semantics for internal routes, attention-budget grain, a dead
   `\Ext` macro (E6–E9).

The Answerable Process one-pager the synthesis consolidates is a Downloads artifact, not a
repository round, and not frozen by the workspace's convention; the concordance says so.

## Phase III — Lean

`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` (1042 lines, Mathlib only).
Built in this tree with `lake build Workspace.Normativity.Contrib.NormativeContinuity`
(726 jobs, "Build completed successfully"); every `#print axioms` line reports
`[propext, Classical.choice, Quot.sound]`.

Lean-verified, under the stated abstract hypotheses: **Persistent-Wait**
(`IssueTrace.persistent_wait`), **Persistent Opportunity**
(`persistent_opportunity`, parametric in `WaitResponsive`), **No Structural
Abandonment** (`no_structural_abandonment`, parametric in `NonStarving`), **Grounded
Replay** (`StandingTrace.grounded_replay`), the standing-at-opening bridge
(`anchor_grounded`), the repaired route-extinction lemma
(`routes_empty_persistent`), matter continuity (`live_empty_persistent`), and the
Step-2 lemmas as separate declarations (`live_succ_eq`, `pre_succ_subset`,
`routes_succ_eq`, `reach_succ_subset`). Fixture A in both directions
(`fixA_live_gate_holds`, `fixA_persistent_wait_fails`, `fixA_reach_gate_fails`,
`fixA_other_requirements`), fixture B (`fixB_routes`), fixture E (`fixE_cycle_is_work`).

**Dependency report.** Lean hypotheses match the proof-pass table exactly
(`THEOREM_MAP.md`): Persistent-Wait consumes Requirements 4, 5, 7, 8, 9, 10, 12 and the
list-bookkeeping facts (unique birth, born-before-outstanding, `Res ⊆ O`, matters are
prior issues that persist); nothing else in the file. Two things Lean made visible that
the paper leaves implicit: `M` enters abstractly (two fields the paper's construction
satisfies; proving that is an obligation), and the freshness clause of Requirement 1 is
stated (`StandingTrace.Fresh`) and not consumed by Grounded Replay — it buys uniqueness
of the entry, not existence of the tree. `born_not_out` is a stated field no proof uses.

No countermodel and no missing premise surfaced. `AGENT-CONSOLIDATED` remains valid.

## Deviations from the prompt

- Fixtures C, D and F are Python-tested but not translated to Lean. C and D are instances
  of the general lemmas (`routes_empty_persistent` covers D), and F exercises bookkeeping
  the structure fields state directly; translating them would have added definitions
  without a claim they check. The prompt asked for A–F "before attempting Persistent-Wait";
  A, B and E were done, Persistent-Wait was proved, and C/D/F were judged not to earn a
  Lean statement. Reversible.
- The prompt's §1 summary says the standing-freshness repair was needed so that "the
  change through which it entered" is unambiguous. The Lean proof shows the tree exists
  without freshness; the concordance records freshness as LE conformance, not as a
  hypothesis of the theorem.
- The concordance research was delegated to a read-only subagent; its quotations were
  checked against the files before use.
- Local builds used a bootstrapped `lean/.lake` (packages symlinked from the
  maintainer's Formalized-Agent-Foundations checkout at the same Mathlib rev). The
  repository's full `tests/audit_axioms.py` was not run locally because it re-elaborates
  every Contrib file, several of which import `LogicalInduction` modules that are not
  built in that bootstrap; CI's `lean` job runs it.

## What is not shown

Wait responsiveness and non-starvation are hypotheses, not results. The eight semantic
judgments have no realization here. The concordance's classifications are readings.
Nothing is registered; the wiki is untouched.

## Friction

None new. `tests/round_records.py`'s requirement that a landed round's `prompts/<round>/`
appear in the root `PROVENANCE.md` table is met by the added row.

## Outstanding maintainer actions

1. Decide the reserved entry in `DECISIONS.md` *Awaiting the author*: whether successor
   freshness (Req 5) supersedes LE A11 for the continuity line, or Req 5 is weakened to
   `S ⊆ Q⁺_n ∪ O_{n+1}` with an explicit acyclicity requirement (`CONCORDANCE.md` §8).
2. Apply errata E1–E9 (`CONCORDANCE.md` §7) at the next revision of the synthesis source,
   which will change its digest and therefore needs a new `ORIGIN.md` entry.
3. Merge the pull request from `round/2026-08-29-normative-continuity-concordance`
   (auto-merge not enabled).

## Model attribution

Prompt author: the maintainer, drafted with GPT-5.6 Sol (OpenAI). Executor: Claude Fable 5
(Anthropic), 2026-08-29. Subagent for concordance research: Claude Fable 5 (Anthropic).
