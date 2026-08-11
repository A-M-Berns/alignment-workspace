# Workspace integration pass

## Graph and accounting

| object | commit / status |
|---|---|
| current `main` at intake | `e8be7ae158c6b0d9bf271c98affd11ac81765d8d`, merged PR #16 |
| refinement branch before integration | `d6a39a82506affe682759e4184724fa422e6dff4`, merged PR #17 |
| PR #17 base | `9e37c4ff32b343c4f54e31a9edd28826542330c3` |
| PR #16 | merged; its Stage V content is on current `main` |

**Current main contains:** the Stage V actual-FAF trader and criterion chain,
static-view factorization, temporal quotation/self-trust boundary, the current
review-versus-adoption semantics, and the maintainer-owned root README updates.

**PR #17 adds:** the φ-regret preparation environment and exact-rational suite,
the deck snapshot and provenance, items 29–31, F4, deck path protection, and
the leverage learning-track state.

**PR #17 branch is stale with respect to:** Stage V deference state, current item
7 and item 28 status, and current review-versus-adoption semantics.

**Potential conflicts:** `DECISIONS.md`, `PRIORITIES.md`, `PROVENANCE.md`, and
`RESEARCH_STATE.md`. They were synthesized against current `main`; no shared file
was taken wholesale from the stale branch.

## Integration result

The integration branch starts at current `main` and applies PR #17's merge commit
without its stale shared-state account. The leverage artifacts, tests, deck,
path-gate entry, priorities, and genuinely unresolved maintainer actions are
preserved. Current Stage V deference documents and their status remain governing.

No theorem, regret bound, FUD comparator, futurity construction, or foreclosure
model was sought in this pass.

## State consistency

| topic | RESEARCH_STATE | PRIORITIES | DECISIONS | line docs |
|---|---|---|---|---|
| deference item 7 | partial actual-FAF closure | partial, residue named | Stage V review queue | LI-native register |
| item 28 | conditional static-view theorem | answered core, unregistered | Stage V review queue | factorization module/register |
| computational futurity | resource separation absent | Q4 | Stage V review queue | LI-native register |
| foreclosure | no native type | Q3, ingenuity-level | Stage V review queue | LI-native register |
| competence | separate leakage debt | item 25 | no new ruling | roadmap/ledger |
| learning substrate | constructed environment, no regret result | learning-track context | none | φ-prep register |
| item 29 | next controlling question | substantial applicability test | none | online-learning map |
| item 30 | downstream and unproved | open learner test | none | test specification |
| item 31 | finite audit pending | entry | none | remediable-failures register |
| fencing/locality | fencing alone insufficient | item 30 context | none | counterfactual-influence register |
| F4 | adapter debt noted | friction report | maintainer choice queued | φ-prep current state |

## One additional filing

The current priorities had no explicit ingenuity question for the Stage V
resource-separation boundary. This pass adds Q4, `What certifies
resource-separated computational futurity?`, without proposing an implementation
or claiming a result.

## What was not shown

- No φ-regret bound or Blum–Mansour instantiation result.
- No new leverage theorem beyond the imported PR #17 material.
- No resource-separated future computation, authority model, or foreclosure theorem.
- No adoption of the deck or its research claims from its qualified review status.

## Outstanding maintainer actions

1. Rule on the Stage V review surface: item 28's narrow boundary, item 7 partial
   closure, and Q3's status.
2. Confirm or revert the deck path-gate entry.
3. Confirm the deck's qualified review status without treating it as adoption.
4. Decide F4's durable answerability-code location.

## Next dispatches

- **Deference:** a resource-indexed quotation boundary coupled only with the
  minimum two-time continuation/capability semantics needed to state corrective
  reachability. This is conceptually central and model-heavy.
- **Leverage:** item 29, testing whether the Blum–Mansour reduction survives the
  guarded, prefix-dependent, varying-action-set comparator substrate. This is the
  cheaper immediate test and gates item 30.

## Verification

| command / check | result |
|---|---|
| `python3 tests/run.py` | green; 3 leverage projects, including φ-prep |
| φ-prep runner | 25 exact-rational tests green over fifteen fixtures |
| `WORKSPACE_LEAN=1 python3 tests/run.py` | green; Lean build and all house gates |
| axiom audit | 175 results across 12 files, within the three-axiom allowance |
| sorry gate | clean over 12 files |
| path gate | 14 self-tests green, including deck protection and round proof-layer status |
| `git diff --check` | clean |
| root README | no diff |

## Attribution

```
Maintainer:           A. M. Berns
Prompt-author-model:  GPT-5.6 Sol (OpenAI)
Executor:             GPT-5 Codex (OpenAI)
Date:                 2026-08-11
```

PR: https://github.com/A-M-Berns/alignment-workspace/pull/18
