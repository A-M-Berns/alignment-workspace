# Normative Continuity settlement — report

**Verdict: `NORMATIVE-CONTINUITY-MATH-SETTLED`.** Gloss as dispatched: the structural
mathematical specification, its principal modeling choices, theorem dependencies,
satisfiability, and Lean theorem spine have been settled. This does not assert Coverage,
Progress, substantive normative correctness, Proper Exercise, or realization by a
concrete reasoner. The legitimacy project is not called settled.

Deliverables are in `projects/normativity/legitimacy/rounds/2026-08-30-normative-continuity-settlement/`:
revision 2 of the specification (`NORMATIVE_CONTINUITY.tex/.pdf`), `SETTLEMENT.md`
(the decisions and the red team), `THEOREM_MAP.md`, `src/settled_model.py` (the whole
specification as one checker with witness `W`), `tests/`, and §4 of
`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`. The `AGENT-CONSOLIDATED`
checkpoint of 2026-08-29 is byte-unchanged.

## Resolutions (§§1, 2, 6, 7 of the dispatch)

- **Successor freshness: fresh successors (A).** Static existing-successor ancestry (B)
  is incoherent: a resolution written at `n` would change `Live_k(m)` and `o_k(m)` for
  `k < n`, so opportunity would not be prefix-determined; acyclicity does not touch this.
  Time-stamped edges (C) are coherent but doubly time-index every ancestry-dependent
  definition and buy nothing needed: consolidation into an existing issue is a
  prerequisite routed to it, which keeps matter identity, reach and attention. The
  dispatch's hypothesis is vindicated; LE A5/A11 are superseded with that reason.
- **Same-batch open-and-resolve: forbidden.** Every judgment about `q` reads a prefix at
  which `q` is outstanding; allowing it needs a birth-state semantics and lets Req 3 be
  discharged by an issue outstanding at no prefix. Supersedes A17.
- **Due timing: uniformly strict prefix.** One position lost, the descriptive/normative
  split gone. Supersedes A34.
- **Resolution gating: `Resolve` sufficient alone;** `Permit` readable inside. A second
  gate does no structural work. Supersedes A21.
- **Standing grounds:** constrained only for records that change standing; S1's
  constraint on no-op edits has no structural content.
- **Wait responsiveness:** primitive is `∀ d N0, ∃ n ≥ N0, d ∉ NoRoute_n(m)`; the
  eventually-met form is equivalent (both directions in Lean) and kept as the
  mechanism-naming sufficient condition. No `External(d)`.
- **Grounded Replay:** stated over admitted occurrences `Adm_n`, live form as
  corollary (Lean: `grounded_replay_admitted`, `grounded_replay_live`). No model
  complication; `Adm` is derived.

## Matters (§3)

`IssueTraceCore.mattersOf` is the paper's construction; `mattersOf_mono`,
`mattersOf_prior` are proved from the single side condition `Desig_n ⊆ O_n ∪ Q⁺_n`;
`IssueTraceCore.toIssueTrace` is the realization. Prospective-only matterhood
(`mem_mattersOf_succ`, `mattersOf_not_mem_of_lt`), merge and split
(`anc_of_parent`, `mem_live_succ_of_parent`). **No extra property was needed.** The
theorems stay generic over abstract `M`, as the dispatch expected; the paper gains
Lemma "matter bookkeeping" stating the same two facts.

## Satisfiability (§4)

`src/settled_model.py` checks Requirements 1–12, compatibility, fresh standing
occurrences, and the matter-grain budget with positive shares, on witness `W`: standing
gain and loss with authorized grounds; an issue anchored to `P` outliving `P`'s standing
and resolving under it; `Due` rising twice for one pair; co-opened route root;
withdrawal then a fresh semantically identical occurrence; route extinction; reach-gated
additions passing; split/merge; a designated descendant matter overlapping its ancestor
under the budget. In Lean, `Fixtures.fixE_issueTrace` inhabits the issue-trace
specification and `shareAttention_sum_le_one` / `shareAttention_nonStarving` are the
attention witness for any injective birth index and any number of matters (no problem
from infinitely many matters over time: each `M_n` is finite and the shares sum below
one for any finite set).

## Dependencies (§5) and red team (§9)

Unchanged: Persistent-Wait from Requirements 4, 5, 7, 8, 9, 10, 12 + bookkeeping;
Persistent Opportunity = + wait responsiveness (also from the primitive form,
`persistent_opportunity'`); No Structural Abandonment = + non-starvation; Grounded
Replay from Requirement 1, bridged by Requirement 2. No settled choice altered a
definition a theorem reads, so nothing moved. Fixtures rerun: rotating prerequisite
(Lean, both ways), co-opened route root (Lean), waiting cycle (Lean), split/merge/
designation (Python + Lean lemmas), standing loss with a live anchored issue (witness
`W`). The red team (`SETTLEMENT.md` §9) found no theorem violation and no inconsistent
requirement pair.

## Checks

`lake build Workspace.Normativity.Contrib.NormativeContinuity` in this tree: success; 28
`#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`. Round tests: 15
pass. Repo runner: see the commit's CI.

## Deviations from the prompt

- The revision's requirement numbers are unchanged, but lemma numbers shifted by one
  after Lemma 1 (the matter-bookkeeping lemma is Lemma 2); the prompt refers to lemmas
  by name, not number, so nothing it says is affected.
- Fixtures C, D, F remain Python-only, as in the concordance round.
- `SETTLEMENT.md` §1's incoherence argument for model B is a paper argument; the
  prompt asked to "pressure-test whether this is actually coherent", which is answered,
  but no Lean statement of B's failure was made because B has no well-formed definition
  of `o_k` to state it against.

## What is not shown

Wait responsiveness and non-starvation are assumptions; the attention witness shows
non-starvation is satisfiable, not that any given process satisfies it. The eight
judgments have no realization. Coverage, Progress, Proper Exercise, checkers, liability
are untouched.

## Outstanding maintainer actions

1. Merge the pull request from `round/2026-08-30-normative-continuity-settlement`
   (auto-merge not enabled).
2. Honor or reject the status: if honored, this layer is closed until a downstream
   consumer exposes a missing capability; the one candidate named is time-stamped
   consolidation (`SETTLEMENT.md` §1, model C).

## Model attribution

Prompt author: the maintainer, drafted with GPT-5.6 Sol (OpenAI). Executor: Claude
Fable 5 (Anthropic), 2026-08-30.
