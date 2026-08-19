# Provenance

Every file in this directory:

- **generator** — `prompts/2026-08-19-deductive-region/`, executed by Claude Opus 5
  (Anthropic); the dispatch's author model is unrecorded
- **review status** — `ci-only`
- **date** — 2026-08-19

| path | notes |
|---|---|
| `README.md` | the round record; its verdict line is registered in `state/rounds.json` |

The round's deliverable is Lean, not documents: `lean/Workspace/Normativity/Contrib/DeductiveRegion.lean`,
generator and review status as above, adjudicated by the Lean kernel and the axiom
audit. Every public result there carries `#print axioms` and audits to
`[propext, Classical.choice, Quot.sound]` or a subset.
