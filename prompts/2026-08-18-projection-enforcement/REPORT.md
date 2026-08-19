# Report — projection enforcement closure pass

The deliverables live in
`projects/normativity/rounds/2026-08-18-projection-enforcement/`:

1. `DECISION_MEMO.md` — read first. Every question of the dispatch graded
   *proved* / *proved conditional on a named standard theorem* / *likely but
   unresolved* / *false*, leading with whether the projection trader survives.
2. `PAPER_CLOSURE.md` — the recommended theorem chain, what strengthens, what stays
   conditional, the cleanest trader-budget statement, computational cost, remaining
   holes, and the ruling on `DistanceComplete`.
3. `PAPER_AUDIT.md` — the rest of the paper, split into *wrong*, *under-justified*,
   *improvable*, plus notation.
4. `COMPARISON.md`, `COMPUTABILITY.md`, `THEOREM_MAP.md`, `README.md`.

Lean: `lean/Workspace/Normativity/Contrib/Projection{Force,Market,Compiler,Budget}.lean`
— no `sorry`, no `axiom`, axioms `[propext, Classical.choice, Quot.sound]` only.

Python: `src/projection.py`, `tests/test_projection.py` — exact `Fraction` arithmetic,
twelve tests.

The paper itself was not rewritten, per the dispatch.

## Model attribution

- **Prompt-author-model:** unrecorded — the dispatch was written outside this session.
- **Model:** Claude Opus 5 (Anthropic) — the executor.
- **Dates:** 2026-08-18.
