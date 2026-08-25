# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `CARROLL_CORE.md`, `LEGITIMACY_LANGUAGE.md`, `CRITERION.md`, `PROSECUTION.md`, `OLD_INTERFACE.md`, `THEOREM_MAP.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-carroll-legitimacy-test/` | — |
| `src/`, `tests/`, `MATRIX.txt` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-carroll-legitimacy-test/` | — |

The prompt was authored outside this repository and is committed verbatim at
`prompts/2026-08-25-carroll-legitimacy-test/PROMPT.md`. `MATRIX.txt` is generated
by `python3 src/report.py MATRIX.txt` and `tests/test_adversarial.py` checks the
committed file against a fresh render.

## Sources

**External, and the round's subject.** *AI Alignment with Changing and
Influenceable Reward Functions*, Proceedings of the 41st International Conference
on Machine Learning, PMLR 235 (2024), `arXiv:2405.17713`. Read as the arXiv PDF
and the arXiv LaTeX source, figures included. Definitions 1 to 11, Tables 1 to 5,
Figures 1, 2, 4, 6 and 8, Appendices A.5, A.7, A.8, A.9, B.1 to B.4 and C.1 to
C.3 were read directly; the finite specifications come from Table 3 and from the
figures it names rather than from any prose summary. Every transcription decision
is listed in `carroll_cases.DEPARTURES` and argued in `CARROLL_CORE.md` §§3-5.

**In-repository, imported and run unmodified.** The Reflective Integrity core at
`../2026-08-24-reflective-integrity-core/src/ri_core.py` — its four historical
record kinds, `PAuth`, `PProto`, the standing-effect interpreter, freshness,
answerability roots, fates, custody and both conservation predicates. The
vertical slice at `../2026-08-25-end-to-end-vertical-slice/src/standing.py`, for
`PValue` and `values_projection`.

**In-repository, read and prosecuted rather than imported.** The counterfactual
legitimacy round at `../2026-08-17-counterfactual-legitimacy/` —
`LEGITIMACY_INTERFACE.md`, `COUNTERFACTUAL_INTERFACE.md`, `MODEL.md`,
`PROSECUTION.md`. Its four clauses are restated over this round's objects in
`src/old_interface.py`, for the reason `OLD_INTERFACE.md` gives; its `src/` is not
imported. The vertical slice's `ARCHITECTURE.md` and `INQUIRY_INTEGRATION.md`
were read for the division into parameters, historical occurrences, bounded
resource and derived views, and for the three separate graphs; nothing in this
round adds a historical event kind or reopens Reflective Integrity.

**Not used.** No Logical Induction object, no traderization result, no charged
enforcement path. The round's dependency on
`../2026-08-16-traderized-enforcement/src` is a path on `tests/run.py`'s
`sys.path`, inherited through the vertical slice's import chain, and no claim
here rests on anything in it.
