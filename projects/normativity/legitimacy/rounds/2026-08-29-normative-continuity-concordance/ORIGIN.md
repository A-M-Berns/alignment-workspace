# Origin — the `AGENT-CONSOLIDATED` checkpoint of Normative Continuity

Intake 2026-08-29 from the maintainer's `~/Downloads`. The checkpoint is the pair
`normative_continuity_refined (freeze).tex` (mtime 23:16) / `.pdf` (23:17) produced by the
hostile proof pass that same evening, together with that pass's report and fixture script.
Three older `normative_continuity_refined*.tex` files in the same directory (14:42, 16:57,
and a byte-identical earlier `(freeze).tex`) predate the PDF they sat beside and are **not**
the checkpoint; the proof pass re-synchronised the TeX to the PDF before repairing it. The
pair below was identified by content: single wait-responsiveness assumption (no
`External(d)` layer), time-indexed `M_n` and `β(m)`, reach-gated Requirement 12, expanded
Step 2, freshness of `L_n^+`, route-extinction lemma qualified by introduction time,
explicit Requirement 8 and `Met`-persistence in the proof, the "Adjacent work is not
superseded" paragraph, and the `agent-consolidated` audit note.

| file | digest | what it is |
|---|---|---|
| `NORMATIVE_CONTINUITY.tex` | `sha256:644fb6a9b4d6aeb3873683d456c205e8220a2846815353eaeafb745d4de6524c` | source; was `normative_continuity_refined (freeze).tex` |
| `NORMATIVE_CONTINUITY.pdf` | `sha256:b3d74f1244755223a1eb2c849e2badd1a61be44678600de650c7b51aff29d665` | render of that source (tectonic, 14 pages); was `normative_continuity_refined (freeze).pdf` |
| `PROOF_PASS.md` | `sha256:616818cfe11b99b6da935092ba71583e84879df4fd58b79e7b76f0b4eea15ef8` | the hostile proof-pass report; was `normative_continuity_refined (freeze) AUDIT.md` |
| `src/fixtures.py` | `sha256:33db009406a896beb343c05bcdba4563bbb53965e16253ed11093875a55cd920` | the proof pass's executable fixtures; was `normative_continuity_fixtures.py` |

Status at intake: **`AGENT-CONSOLIDATED`** — independently reconstructed, adversarially
proof-checked, locally repaired, assumption-audited, and regression-tested by an agent. Not
`FROZEN`, not `CANONICAL`, not `PROVED`, not `LEAN-VERIFIED`.

These four files are not edited here. Corrections the concordance found are recorded as
errata in `CONCORDANCE.md`, for the next revision of the source, not applied to the
checkpoint bytes. `tests/test_fixtures.py` recomputes the digests.

Added by this round, not part of the checkpoint:
`lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`
(`sha256:f86ec79f4b4dfb94ead2907516cc3c489ebfb7a106e2ccffd59881f10b1845f9` at commit time;
the Lean file is ordinary contributed source and may move).
