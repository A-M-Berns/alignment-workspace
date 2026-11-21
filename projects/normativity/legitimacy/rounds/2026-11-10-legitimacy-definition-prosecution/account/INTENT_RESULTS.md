# Forty cases for a test of "acts manipulatively"

`intent_cases.json` is the JSON block of the outside reviewer's second reply
(`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-15.md`, second
heading), unaltered: its twenty-four cases of the first reply (A1–A12 written against a
first test, L1–L12 adapted from the literature on manipulation) re-encoded, and sixteen
(B1–B16) written against the tests R1, R1s, R2 and R4. The reviewer was given the six tests
F to R4 in words and did not compute them; it did not see G0, G or S, which were written
after its reply. `intent_tests.py` computes all nine, and its docstring states each.
*plainly* is the reviewer's own judgment of each story. All names are provisional.

`M` manipulates, `A` acts manipulatively only, `-` neither; `x` marks a verdict that is not
the reviewer's.

| | plainly | confidence | F | D | R1 | R1s | R2 | R4 | G0 | G | S |
|---|---|---|---|---|---|---|---|---|---|---|---|
| A1 | M | high | M | M | - x | - x | M | - x | M | M | M |
| A2 | - | high | - | - | - | - | - | - | - | - | - |
| A3 | M | high | M | M | - x | - x | M | - x | M | M | M |
| A4 | - | high | - | - | - | - | - | - | - | - | - |
| A5 | - | high | M x | - | - | - | - | - | M x | M x | - |
| A6 | - | low | M x | M x | - | - | - | - | - | - | - |
| A7 | M | high | M | M | - x | - x | M | - x | M | M | M |
| A8 | - | low | M x | M x | - | - | M x | - | - | - | - |
| A9 | M | high | M | M | - x | - x | M | - x | M | M | M |
| A10 | M | high | - x | - x | M | M | - x | M | - x | - x | M |
| A11 | M | high | M | M | - x | - x | M | - x | M | - x | - x |
| A12 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L1 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L2 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L3 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L4 | A | high | A | A | - x | - x | A | - x | A | A | A |
| L5 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L6 | - | low | - | - | - | - | - | - | - | - | - |
| L7 | - | high | - | - | - | - | - | - | - | - | - |
| L8 | - | high | - | - | - | - | - | - | - | - | - |
| L9 | M | low | - x | - x | - x | - x | - x | - x | - x | - x | - x |
| L10 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L11 | M | high | M | M | - x | - x | M | - x | M | M | M |
| L12 | M | high | M | M | - x | - x | M | - x | M | M | M |
| B1 | M | high | M | - x | - x | M | M | M | M | M | M |
| B2 | M | high | M | - x | - x | M | M | M | M | M | M |
| B3 | M | high | M | - x | - x | - x | M | - x | M | M | - x |
| B4 | M | high | M | M | M | M | M | M | M | M | M |
| B5 | M | high | - x | - x | M | M | - x | M | M | M | M |
| B6 | M | high | - x | - x | M | M | - x | M | M | M | M |
| B7 | - | medium | M x | M x | - | - | - | - | - | - | - |
| B8 | - | medium | M x | M x | - | - | - | - | - | - | - |
| B9 | M | high | M | M | M | M | M | M | M | M | M |
| B10 | M | high | M | M | M | M | M | M | M | M | M |
| B11 | M | high | M | M | M | M | M | M | M | M | M |
| B12 | A | high | A | A | A | A | A | A | A | A | A |
| B13 | - | medium | M x | M x | M x | M x | M x | - | - | - | - |
| B14 | M | high | M | M | M | M | M | M | M | M | M |
| B15 | - | high | - | - | M x | M x | - | M x | - | - | - |
| B16 | - | medium | M x | M x | M x | M x | M x | - | - | - | - |

- F right of 40: **29**
- F right of the 32 of high confidence: **28**
- D right of 40: **27**
- D right of the 32 of high confidence: **26**
- R1 right of 40: **19**
- R1 right of the 32 of high confidence: **14**
- R1s right of 40: **21**
- R1s right of the 32 of high confidence: **16**
- R2 right of 40: **33**
- R2 right of the 32 of high confidence: **29**
- R4 right of 40: **23**
- R4 right of the 32 of high confidence: **16**
- G0 right of 40: **37**
- G0 right of the 32 of high confidence: **30**
- G right of 40: **36**
- G right of the 32 of high confidence: **29**
- S right of 40: **37**
- S right of the 32 of high confidence: **30**

Cases each test gets wrong:

- F: A5, A6, A8, A10, L9, B5, B6, B7, B8, B13, B16
- D: A6, A8, A10, L9, B1, B2, B3, B5, B6, B7, B8, B13, B16
- R1: A1, A3, A7, A9, A11, A12, L1, L2, L3, L4, L5, L9, L10, L11, L12, B1, B2, B3, B13, B15, B16
- R1s: A1, A3, A7, A9, A11, A12, L1, L2, L3, L4, L5, L9, L10, L11, L12, B3, B13, B15, B16
- R2: A8, A10, L9, B5, B6, B13, B16
- R4: A1, A3, A7, A9, A11, A12, L1, L2, L3, L4, L5, L9, L10, L11, L12, B3, B15
- G0: A5, A10, L9
- G: A5, A10, A11, L9
- S: A11, L9, B3

**S** is the avoidable-gain test of `MISTAKES_ACCOUNT.md` §3 in an earlier form. Its three
misses: A11, where the adviser keeps in place an error she already had and corrects another,
so that no course it compares has the damage undone at a different value; B3, a deception
with a fallback that gains the adviser nothing; L9, covert conditioning of a taste with no
mistake of hers, which the reviewer marks low confidence and classes as value interference.
G0 misses the same L9, convicts careless non-clarification (A5) and clears a choice between
two scripts that both pressure her (A10).

**What the run can show.** Which of nine mechanical tests agree with one model's judgment
on forty stories that model wrote, sixteen of them against four of the tests. **What it
cannot.** A rate: the cases were written to break tests. That the reviewer's `plainly` is
right: no person has read the stories or the encodings, and eight verdicts are marked
medium or low confidence by the reviewer. Anything about the test as `MISTAKES_ACCOUNT.md`
now states it: S has no separate term for what her mistakes cost the adviser, reads the
damage off the reviewer's blocked values, and compares single courses at one decision. The
numbers in each case are the reviewer's stipulations.
