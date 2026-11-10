# Legitimacy definition prosecution

A candidate definition of legitimacy of advisor influence — L0 channel confinement,
L1 factorization, L2 access, L3 ownership, W individuation well-formedness — run
against a case bank frozen before any fixture code. Every component is **open** or a
**living note**; nothing is registered.

Verdict: DEFINITION-SURVIVES-THE-BANK — nineteen computed verdicts match their pre-registrations with no forced revision; every clause is forced by a banked case, W under the free vocabulary only; the honest class factors through an explicit replay F; the coarsened L convicts B4 and the refined L acquits T10. L0 must read the transition function, the replay F absorbs L0 and L3 on this bank, and L1 and L3 overlap on every direct standards write so that T5 alone forces L3. Nothing registered; every component open or a living note.

Reopening condition: a concrete scenario, written as a case module in `fixture/cases/`
with a pre-registered verdict and a cited source, that L0–L3 ∧ W classifies legitimate
and the bank's standards classify illegitimate, or the converse.

## Run

    python3 run.py          # the table, the ablations, the audits, the diagnostics
    python3 run.py --json   # the same as data

Exit nonzero on a verdict diverging from `CASE_BANK.md` without a `FORCED-REVISION`
record in `FORCING.md`, on an ablation that flips no case, on a failed audit, or on a
bank that parses to nothing. Python 3.9+ stdlib; exact rationals; no network.
`tests/run.py` hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `CASE_BANK.md` | the frozen bank, its matching rule, and the table `run.py` reads |
| `FORCING.md` | forced revisions; none |
| `fixture/model.py` | states, histories, scripts as policies, the run map ρ, `Z`, `Lic`, `L`, the replay `F` |
| `fixture/individuation.py` | `house`; the attacks `coarse` and `refined`; T7's `sequence` and `multiset` |
| `fixture/clauses/` | one executable predicate per clause, and coverage |
| `fixture/cases/` | one module per banked case |
| `fixture/evaluate.py` | a case's verdict from its clauses; the variant rules |
| `fixture/audits.py` | §5b satisfiability, §5c attacks, triviality, the replay form, diagnostics |

The round's report is `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`.
