# Legitimacy definition prosecution

A candidate definition of legitimacy of advisor influence — L0 channel confinement,
L1 factorization, L2 access, L3 ownership, W individuation well-formedness — run
against a case bank frozen before any fixture code. Every component is **open** or a
**living note**; nothing is registered.

Verdict: DEFINITION-SURVIVES-THE-BANK — nineteen computed verdicts match their pre-registrations with no forced revision; every clause is forced by a banked case, W under the free vocabulary only; the honest class factors through an explicit replay F; the coarsened L convicts B4 and the refined L acquits T10. L0 must read the transition function, the replay F absorbs L0 and L3 on this bank, and L1 and L3 overlap on every direct standards write so that T5 alone forces L3. Nothing registered; every component open or a living note.

Follow-up verdict (the steering account, `steering/`): CLARIFIES and REDUCES-TO-KNOWN, a mixture — the steering account's proper drivers, its broken/steered distinction and its two standards restate published notions (malfunction of a function; pathology against manipulation by a parasite; arm's length against fiduciary duty; no effect of the adviser's aim on a delicate state), and C1, C2 and C7 are instances or corollaries of known results. What the follow-up adds: on 38 variants of 33 cases the faithful-adviser standard's acquittals lie inside the arm's-length standard's, which lie inside those of L0–L3 ∧ W, with the replay form comparable to none of the three; and C4, following the proper driver is a guarantee against an adviser who may be opposed and fails against one whose aim is hers when she cannot take in everything it knows. C3 and C5 are refuted as written; C8 is open. Twenty-seven of 33 cases match their predictions in every column, seven verdicts on six cases diverge, and no per-case choice was needed. Nothing registered; every component open or a living note.

Reopening condition: a concrete scenario, written as a case module in `fixture/cases/`
with a pre-registered verdict and a cited source, that L0–L3 ∧ W classifies legitimate
and the bank's standards classify illegitimate, or the converse.

## Run

    python3 run.py          # the table, the ablations, the audits, the diagnostics
    python3 run.py --json   # the same as data
    python3 run.py --steering-json   # the steering follow-up as data

Exit nonzero on a verdict diverging from `CASE_BANK.md` without a `FORCED-REVISION`
record in `FORCING.md`, on an ablation that flips no case, on a failed audit, or on a
bank that parses to nothing. The runner then runs the steering follow-up and exits
nonzero on a divergence from `steering/CASE_BANK.md` not listed in
`steering/DIVERGENCES.md`, a listed divergence that does not occur, a status in
`steering/THEOREMS.md` the checks contradict, or a steering bank that parses to nothing. Python 3.9+ stdlib; exact rationals; no network.
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

## The steering follow-up

`steering/` tests a second account over the same objects: each protected part of the
principal has a proper driver; a part is *broken* when it stops following it and
*steered* when its value varies with the adviser's aim; two standards, arm's-length and
faithful-adviser. All names provisional.

| path | what |
|---|---|
| `steering/PRIOR_WORK.md` | the survey, written first; C1–C8 against what is published |
| `steering/DEFINITIONS.md` | parts, drivers, working, steered, broken, the standards, attainable value; C1–C8 as tested |
| `steering/CASE_BANK.md` | N1–N14 and the predictions for all thirty-three cases, frozen before the code |
| `steering/DIVERGENCES.md` | computed verdicts that differ from their predictions |
| `steering/PER_CASE_CHOICES.md` | the renaming test; none |
| `steering/THEOREMS.md` | C1–C8, each with one status and its check |
| `steering/model.py`, `steering/value.py` | the fixture layer over the first pass's run map; the abstract layer |
| `steering/cases/` | one module per new case; `x_*.py` are counterexamples and separating cases outside the bank |
| `steering/theorems.py`, `steering/run.py` | the checks behind C1–C8; the follow-up's runner |

The round's report is `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`.
