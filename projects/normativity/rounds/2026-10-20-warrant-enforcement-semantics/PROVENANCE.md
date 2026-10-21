# Provenance

| artifact | generator | review status | date | originating round |
| --- | --- | --- | --- | --- |
| `README.md`, `REPORT.md`, `LICENCE_CHAIN.md`, `SETTLEMENT_FORK.md`, `RECORD.md`, `COUNTERMODELS.md`, `PROVENANCE.md` | Claude Fable 5.1 (Anthropic); the prompt by the maintainer, relayed verbatim | `ci-only` | 2026-10-20 | `prompts/2026-10-20-warrant-enforcement-semantics/` |
| `src/fixture.py`, `src/licence.py`, `src/record.py`, `tests/run.py`, `tests/test_fixture.py` | Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-10-20 | `prompts/2026-10-20-warrant-enforcement-semantics/` |
| `lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean` | Claude Fable 5.1 (Anthropic); Part 0 ported from `round/2026-09-16-seed-statics` (`SeedStatics.lean`, that round's executor Claude Fable 5.1, Anthropic) | `ci-only` | 2026-10-20 | `prompts/2026-10-20-warrant-enforcement-semantics/`; row in `lean/Workspace/Normativity/Contrib/PROVENANCE.md` |

The Lean is adjudicated by the kernel and the axiom audit: every declaration carries
`#print axioms` and audits to `[propext, Classical.choice, Quot.sound]` or a subset. The
Python is exact `fractions.Fraction` throughout; its two market exhibits use a
one-coordinate market maker that zeroes the aggregate, one valid selection under the maker's
contract and not the pinned dependency's `MarketMaker`, and are `test-supported`.
