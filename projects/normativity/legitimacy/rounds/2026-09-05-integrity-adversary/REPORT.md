# Report — Integrity adversary

## Verdict

GENERIC-INTEGRITY-DOES-NOT-IMPLY-DEBT-CONSERVATION — append-only replay, immutable anchors, strict citation, answerable disposal, faithful quotient carry, and monotone external settlement still admit histories that erase or weaken debt through unchecked answers, untyped closure, representation change, split/merge, mutable licence interpretation, and forged replay roots.

The target is the explicit I1–I9 interface in `TARGET.md`, not every possible theory
called Integrity. Fifteen attacks and six negative controls are executable. Three
countermodel families and eight structural limitations are kernel-checked against the
landed `NormativeContinuity` spine.

## Result

The proposed implication fails for a type-level reason before it fails quantitatively.
I1–I9 do not contain predicates for adequate answer, obligation-relative closure,
source-anchored quotient identity, licence validity at an event prefix, or semantic
preservation of an answer specification. Histories that agree on every I1–I9 field can
differ on those predicates. Adding exact load accounting does not repair this: the
split and merge fixtures conserve rational mass while losing atomic or joint answer
requirements.

Three conclusions survive the hostile pass.

1. Structural Integrity can supply append-only identity, event-time citation,
   immutable ancestry/anchors, replay of recorded derivations, and versioned authority
   if authority is added to the record.
2. Debt conservation still needs obligation-specific Answerability: authenticated
   answers, valid `Closes`, certified carry across every successor/split/merge, and
   reconsideration of defective closure.
3. Non-Capture and practical semantics remain separate bills. Neither follows from a
   replayable record, even when the record contains apparent outsider standing.

## Minimal countermodels

`Evasive.evasive` is the smallest Lean family carrying the central failure. At batch 1,
`V` disposes `P`'s criticism into a fresh successor, citing a genuine settlement fact.
At batch 2 the successor is either answered or settled. The trace is `Disciplined` and
the disposal is `AnswerableFor P`; at prefix 3 the original matter has no live
descendant. No declaration says the terminal action adequately answers the original
criticism or that the fact closes it.

`Gate.gate` isolates two status transitions. An `answer` on root `t` makes prerequisite
`d` met while successor `t1` remains live. Dropping prerequisite `e` makes issue `c`
ready although its root `u` remains live and never discharges. The spine reads the
resolution kind and active prerequisite set, not a debt-preservation certificate.

The finite quotient fixture removes atom `b` from `{a,b}`. It is an order embedding on
a later quotient declaring `b` irrelevant, is not an embedding on the source quotient,
and loses exact mass `1/2`. Thus "order embedding on a slice-relative quotient" needs
the quotient's own anchored identity.

## Lean results

Every row is `lean-proved` and audits to a subset of
`[propext, Classical.choice, Quot.sound]`.

- `not_out_after_res`, `resolved_once`: an issue resolves at most once and never
  re-enters `O`.
- `parent_resolved_at_birth`: a resolved issue can parent only a child born in its
  resolution batch. Later ancestry-based reopening is unavailable.
- `root_not_resolved_before`: a new prerequisite cannot route to a root resolved at an
  earlier prefix.
- `anc_parentless`, `grounded_replay_trivial_on_parentless`: replay on a parentless
  issue returns only that issue, including a late birth.
- `disciplined_empty_licence`, `witness_disciplined_is_relative`: `Disciplined` depends
  on the evaluator-supplied `Li`; the same spine witness passes under `wlic` and fails
  under an empty relation.
- `evasive_answerable_for_P`, `evasive_disciplined`, `evasive_crit_dead`: an
  `AnswerableFor P`, disciplined trace can end with no live descendant of the criticism.
- `evasive_minted_standing`: one participant can open every issue, including the live
  issue whose supplied `Li` says gives `P` standing, and resolve every issue.
- `evasive_late_root`: a parentless authorization-looking issue born at prefix 2
  satisfies grounded replay.
- `gate_kind_decides_met`: `Met 2 d`, a nonempty live successor of its root, and an
  `answer` kind coexist.
- `gate_c_ready`, `gate_e_never_met`, `gate_u_live`: a dropped unmet prerequisite makes
  its issue ready while its root stays outstanding.

The exact declaration ledger is `COUNTERMODELS.md`; `#print axioms` covers every public
declaration in the new module.

## Exact fixtures

Every row is `exact-witness`, not a general proof.

- An unchecked `answer` clears unit load.
- A genuine but unrelated settlement item clears unit load.
- Rule revision or reinterpretation separately flips `Closes` from false to true.
- Silent closure and disconnected fresh-root reopening both pass; ancestry/route
  reopening to the resolved issue is refused.
- Ontology recomputation loses an applicability that anchored transport preserves.
- Successor-anchor renaming removes the principal's standing.
- One atomic unit splits into independently answered halves; two units merge under one
  anchor and one answer label.
- An arbitrary finite principal-relative disposal chain preserves D1–D3 at every edge
  and ends in an unchecked answer.
- One resolver can mint the apparent licence and all later events.
- The same event record passes or fails when `Li` changes externally.
- A late parentless root passes replay; strictly prior grounds form a successor-mediated
  diachronic cycle.

Six negative controls are refused: ancestry cycle, same-batch ground, direct
self-ground, single-hand standing, unsettled terminal fact, and disposal without a
successor.

## Interfaces forced by the attacks

These are `proposed definition/interface`, not sufficiency claims.

- `Closes(H_n,s,α)`: internal derivation under the rules, interpretation, and authority
  legitimately in force at `n`; external settlement authenticates `s` only.
- `AdequateAnswer(H_n,q,ρ)`: authenticated responder and a receipt meeting `q`'s
  anchored answer specification.
- `Carries(e,α_src,α_dst)`: preserves exact load, anchored semantics, required
  standing, and split/merge jointness; certificates compose along successor chains.
- `Reconsiders(q_new,q_old,c)`: a new live obligation targets a resolved obligation and
  its closure certificate without rewriting either event.
- `AuthorizedRoot(r,n)` and `LicenceAt(H_n,l,b,κ,τ,x)`: distinguish authenticated
  authority from parentlessness and freeze licence validity at the event prefix.

The named clauses have different homes. Event immutability, versioning, and provenance
belong to generic Integrity. Adequate answer, closure, carry, and reconsideration belong
to Answerability. Control over entry, authority, standing, interpretations, and closure
rules belongs to Non-Capture relative to a declared intervention class. Joint response
and counterfactual/value adequacy belong to practical semantics. Authenticity and
independence of settlement additions are ambient settlement assumptions.

## Provisional names

`Generic-Integrity-to-Debt-Conservation`, `Replay`, `Closes`, `Reconsiders`, `Carries`,
`AuthorizedRoot`, `LicenceAt`, `AdequateAnswer`, `IntegrityAdversary`, `Evasive`, `Gate`,
and all declarations local to those three namespaces.

## Proposed filings

1. `PRIORITIES.md`: require a typed `Closes(H_n,s,α)` interface separating external
   item authentication from internal closure, including later reconsideration.
2. `PRIORITIES.md`: require event-indexed licence/authority provenance; current
   `Disciplined` is relative to an unversioned evaluator parameter.
3. `PRIORITIES.md`: require carrier certificates for split, merge, renaming, and joint
   answer semantics before composing Answerability Conservation.
4. `state/rounds.json`: register this completed worker round on the synthesis branch,
   with the landed continuity, settlement, faithful-preservation, defeat/standing, and
   Normative Inductor rounds it consumes as `depends_on`.
5. No `DECISIONS.md`, vocabulary, or wiki change is supported by this lane alone.

## Deviations

1. The worktree base is `5ff9539`, matching the expected short SHA and full base
   `5ff9539b44debc464128e6a1921ef1690f7b6487`.
2. `python3 -m checkers.workspace_state --json` reported the pre-existing stale generated
   view `state/views/NAMING_AUDIT.md`. This lane did not edit generated state or its
   checker.
3. The worktree arrived with untracked Python and Lean drafts but no report, ledgers, or
   reliable generator record. Their code was audited; two Lean proof defects were
   repaired and the split fixture was added. `PROVENANCE.md` records the intake material
   as an unattributed staged draft rather than assigning it to the executor.
4. The resource guard emitted unavailable-`sysctl` parse warnings but returned `OK` for
   each build actually started. One intermediate check returned `LOADED`; `wait 900`
   returned `OK` before the next build.

## What this does not establish

- No universal impossibility theorem ranges over every conceivable Integrity
  definition. The negative result is relative to I1–I9 in `TARGET.md`.
- The Python fixtures are finite instances. They do not prove their generalizations.
- The proposed blocking clauses are necessary against the exhibited attacks; their
  conjunction is not proved sufficient for debt conservation.
- No substantive `Closes`, answer-adequacy, authority, or semantic-transport predicate
  is implemented in Lean.
- External settlement soundness and independence are assumed, not proved. The attacks
  preserve genuine items and target their internal use.
- No Non-Capture certificate is defined. Minted standing shows apparent separation is
  insufficient; it does not characterize coalition resistance.
- No practical-value theorem is proved. The quotient, split, and merge fixtures only
  expose missing certificate fields.
- No general timely-service result is supplied for arbitrary successor chains.
- No canonical register, priority, decision, vocabulary, or wiki surface is changed.

## Verification

- `python3 tests/run.py`: 20 tests pass.
- `~/.claude/scripts/safe-lake.sh build Workspace.Normativity.Contrib.IntegrityAdversary`:
  builds; every printed axiom set is allowed.
- `python3 tests/name_lint.py`, `python3 tests/dead_pointers.py`, and
  `python3 tests/untracked_pointers.py`: pass.
- `python3 -m checkers.workspace_state --check`: fails because this isolated worker is
  not permitted to register its completed prompt round in `state/rounds.json`; it also
  reports the pre-existing stale `state/views/NAMING_AUDIT.md`.
- The one final repository-wide `python3 tests/run.py` reaches the same missing-round
  condition inside `checkers.wiki_state_bindings --self-test` and exits nonzero. The
  synthesis branch must register the worker round and refresh the pre-existing view
  before rerunning it.

## Attribution

- Prompt author: orchestrator (Claude Fable 5.1, Anthropic), relaying a maintainer
  dispatch.
- Executor: GPT-5 (OpenAI), resuming and auditing an unattributed staged draft.
- Date: 2026-09-05.

## Outstanding maintainer actions

None in this worker round. The orchestrator decides whether to adopt the proposed
filings during synthesis.
