# The legitimacy architecture round

**Verdict: partial success.** The decomposition is real and one part of it is a
proved conservation law that already existed under another description. The
conjunction under test is **not sufficient**, and the round exhibits what is
missing. The online-learning target is **worse off than it looked**: the
comparator class the abstraction suggests is provably trivial on any trajectory
whose constraint responds to the record.

- `../../notes/LEGITIMACY_ARCHITECTURE.md` — the consolidated view, and the entry
  point for a reader who has read nothing else in this line.
- `THEOREM_MAP.md` — the verification register: statements, derivations, scopes,
  and what is not established.
- `PROSECUTION.md` — the six attacks and the independence matrix, with the test
  that decides each.
- `MAPPING.md` — which existing artifact holds which part, and the vocabulary
  correspondence.
- `FOR_HUMANS.md` — the round's human register.
- `src/` — the abstract conditions, the fixtures, the conservation sweep, the
  comparator analysis.

```sh
python3 tests/run.py
```

Nothing here is registered in `CLAIMS.md` and nothing is in Lean. The four
statements worth porting are named in `THEOREM_MAP.md` and filed as items 35–39
in `PRIORITIES.md`.
