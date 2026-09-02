# Origin — revision 2 of Normative Continuity (the settled specification)

Derived on 2026-08-30 from the `AGENT-CONSOLIDATED` checkpoint
`../2026-08-29-normative-continuity-concordance/NORMATIVE_CONTINUITY.tex`
(`sha256:644fb6a9b4d6aeb3873683d456c205e8220a2846815353eaeafb745d4de6524c`), which is
unchanged. Every difference is a settlement decision or an erratum of that round's
`CONCORDANCE.md` §7, listed in the revision's own "Revision 2" paragraph and argued in
`SETTLEMENT.md`; no definition read by a theorem changed.

| file | digest | what it is |
|---|---|---|
| `NORMATIVE_CONTINUITY.tex` | `sha256:1f5303ecadc3c00287c6e4f9c6b7cc07c814e8602868ebbb89d12b7386e82ddb` | revision 2, the settled specification |
| `NORMATIVE_CONTINUITY.pdf` | `sha256:24cd56cf8d84738067c83e818f8a21f22c45bf0e7d46a34f40a7fc1e5f88f170` | its render (tectonic, 16 pages) |
| `src/settled_model.py` | `sha256:5a646c86506aa327964e35d18ad9b7380f7cfbb2a647fcce5f6e3de1151389db` | the whole specification as one checker, with the witness trace `W` |
| `src/fixtures.py` | `sha256:33db009406a896beb343c05bcdba4563bbb53965e16253ed11093875a55cd920` | the proof pass's fixtures, unchanged (same bytes as the checkpoint's) |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` | `sha256:a27fe04721b1a076a8c5b5509d52e7c3e62e2169e8c85c2d8d18a6778a92ac78` | the Lean spine with the settlement additions (§4 of the file); ordinary contributed source, may move — **and it has moved, see below** |

## The Lean spine has moved since intake, 2026-09-02

The row above is the only digest in this table that has changed, and its "may move"
note is why it is a detector rather than a prohibition. The settled artifacts —
`NORMATIVE_CONTINUITY.tex` revision 2, its render, `src/settled_model.py` and
`src/fixtures.py` — are **unchanged**, and so is the specification they carry.

What changed, by
`projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/`:
§5 was added, and §2 (`StandingTrace`, `Licensing`, the inductive `Grounded`) and §4.2
(`grounded_replay_admitted`, `grounded_replay_live`, `Adm`) were **deleted as
primitives** and re-derived on a unified trace. Digest before
`sha256:3eab58f4…`, after `sha256:a27fe047…`.

**Every theorem of this round's specification still elaborates**, which was the
condition on the surgery: the `IssueTrace` layer is byte-identical, `DefeatTrace`
extends it, and the module builds sorry-free with all 35 declarations auditing to
`[propext, Classical.choice, Quot.sound]`. Two requirements of the *standing* layer did
not survive as consequences — the `Auth` filter on grounds and the nonemptiness of a
standing change's grounds — and are carried as side conditions rather than dropped;
`GROUNDS.md` §3 of that round states them.

Status: **`NORMATIVE-CONTINUITY-MATH-SETTLED`** — the structural mathematical
specification, its principal modeling choices, theorem dependencies, satisfiability, and
Lean theorem spine have been settled. This does not assert Coverage, Progress,
substantive normative correctness, Proper Exercise, or realization by a concrete
reasoner. `AGENT-CONSOLIDATED` remains the status of the checkpoint this descends from.
Not `FROZEN`, not `CANONICAL`, not registered.
