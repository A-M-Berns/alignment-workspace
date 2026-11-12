# Removed

Removed from this directory on 2026-11-11 by the second follow-up
(`prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-2.md`, §2), under the
ruling `2026-11-11--legitimacy-purpose-first-direction` in `DECISIONS.md`. Each file is in
git history at commit `28ce3220`. What these files computed is recorded in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`.

| removed | reason |
|---|---|
| `FORCING.md` | the record of forced revisions to L0–L3 ∧ W; it held none, and nothing run here reads it |
| `fixture/model.py` | the first pass's principal, run map, license predicate and replay `F`; serves only L0–L3 ∧ W |
| `fixture/individuation.py` | the individuations of the licensed trace `L`; serves only clause W |
| `fixture/clauses/` (`l0.py`, `l1.py`, `l2.py`, `l3.py`, `w.py`, `coverage.py`, `__init__.py`) | one predicate per clause of L0–L3 ∧ W |
| `fixture/cases/` (`b1.py`–`b6.py`, `t1.py`–`t13.py`, `__init__.py`) | the nineteen cases as scripts over the first pass's objects; the cases themselves stay in `CASE_BANK.md` |
| `fixture/case.py`, `fixture/bank.py`, `fixture/evaluate.py`, `fixture/audits.py`, `fixture/__init__.py` | the case record, the bank parser, the verdict rule and the ablation and vocabulary audits of L0–L3 ∧ W |
| `steering/DEFINITIONS.md` | the steering account's parts, drivers and two standards, and its statements C1–C8 as tested |
| `steering/THEOREMS.md` | the statuses of C1–C8 |
| `steering/PER_CASE_CHOICES.md` | the renaming test's record; it held none |
| `steering/model.py`, `steering/value.py` | the arm's-length and faithful-adviser predicates over the first pass's run map, and the attainable-value layer |
| `steering/theorems.py`, `steering/run.py`, `steering/__init__.py` | the checks behind C1–C8 and the follow-up's runner |
| `steering/cases/` (`n1.py`–`n14.py`, `shop.py`, `x_gift.py`, `x_threat_welcome.py`, `x_common_fault.py`, `__init__.py`) | N1–N14 as scripts over the first pass's objects, and three counterexample modules for C3 and C6; the cases themselves stay in `steering/CASE_BANK.md` |

`run.py` is rewritten, not removed: it ran the clauses, ablations and audits above and now
reads the two banks.

## Left in place

| kept | why it could not be removed |
|---|---|
| `steering/DIVERGENCES.md` | it records divergences from the two standards' predictions and nothing run here reads it, but `DECISIONS.md`, *Awaiting the author* (the entry of 2026-11-10 on the faithful-adviser standard) cites it by path, and `tests/dead_pointers.py` fails on a pointer in `DECISIONS.md` that does not resolve |
