# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MEMO.md` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-reason-representation/` | — |
| `src/reason_state.py`, `tests/` | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-reason-representation/` | — |
| `wiki/Normative-Record-and-Inquiry.md`, `wiki/Reasons-Answerability-and-the-Score.md`, `wiki/Sources.md`, `wiki/Roadmap.md` (edits) | Claude Fable 5 (Anthropic) | `ci-only` | 2026-08-23 | `prompts/2026-08-23-reason-representation/` | — |

The executor worked from live `origin/main` at
`6ad03a9be2073917576b016975db98b83598cd7c`, the merge commit for the
afoundational-inquiry round.

## External sources inspected

- Jon Doyle, “A Truth Maintenance System,” *Artificial Intelligence* 12
  (1979), 231–272. The primary PDF was inspected for the node/justification
  data structures, SL-justification inlist/outlist validity, in/out statuses
  and their distinction from truth values, well-founded support, truth
  maintenance, non-monotonic justifications and assumptions, and
  dependency-directed backtracking (pp. 236–239).
- Johan de Kleer, “An Assumption-based TMS,” *Artificial Intelligence* 28
  (1986), 127–162. The primary PDF was inspected for assumption labels,
  minimal environments, multiple simultaneous contexts, nogood recording, the
  problem-solver/TMS division of control, and the catalogue of JTMS
  limitations (pp. 130–133, 138–139). The companion “Problem Solving with the
  ATMS” PDF was available and not relied on for any claim.
- John F. Horty, *Reasons as Defaults*, draft #2 of August 16, 2006. The
  draft PDF was inspected for scenarios and generated belief sets, triggered/
  conflicted/defeated definitions, reasons as premises of triggered defaults,
  the rebutting-only scope of its defeat notion with undercutting deferred,
  and variable-priority default theories with priority statements in the
  object language (pp. 10–14, 21–22).

The stateless-substrate reading, the policy-relativity of nogoods under
learnable incompatibility, and the reified staged applicability treatment of
undercutting are this round's constructions, not claims attributed to those
sources.
