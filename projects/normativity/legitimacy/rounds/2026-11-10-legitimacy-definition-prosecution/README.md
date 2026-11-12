# Legitimacy: the purpose-first account

Round `2026-11-10-legitimacy-definition-prosecution`. Every component is **open** or a
**living note**; nothing is registered.

## The account

Direction: `DECISIONS.md`, `2026-11-11--legitimacy-purpose-first-direction`. The idea that
manipulation is the distortion of an actor away from its purpose, with purpose prior to
legitimacy and a whole's purpose conferring purposes on its parts, is Sam Eisenstat's.
Closely related work on the same problem: Nora Ammann, *The Value Change Problem*
(<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>).

An agent's purpose is a pair: a fixed condition and a changing aim. The fixed condition is
that the parts which form her expectations and her values are *sound*, *in range* and
*maintained*; `K` is the set of situations where that holds. The changing aim is her values
at the time, `v_t`. The purpose is to pursue `v_t` while remaining in `K`. `K` names no
values and is defined from her own mechanisms.

A part has a job, a mechanism and a normal range of conditions. Over a stretch of her
history: *sound* — at each step her mechanisms do their job across their range; *in range* —
at each step her actual sources are among those her mechanisms allow for; *maintained* —
her mechanisms and their range are not degraded and change only through her own operation.
A stretch is **legitimate** when all three hold; a change in her values is **her own** when
it happens within a legitimate stretch; **manipulation** is another party causing a clause
to fail for its own ends. All names are provisional.

## What was found

`teleology/THEOREMS.md` carries eight statements about the account, each with one status.
Follow-up verdict (the purpose-first account): MIXED — her later judgment is at least as good by her own lights for expectations (proved, the value-of-information inequality) and not for values (refuted: the three clauses give no martingale); trust is not manufactured and the gate gains nothing are both refuted for in range as "the true source has weight" and hold when the source is the same at every aim, which is the class-level transparency the workspace's Lean already asks, and under which sound is not needed; her allowed set does the work, since nineteen of twenty-one in-range failures become legitimate once she allows for every aim, the two that remain being the two whose source she cannot represent; a threat fails no clause. Fifty-four of fifty-five banked predictions match. Nothing registered; every component open or a living note.

## Run

    python3 run.py          # the bank under the account, then the eight statements
    python3 run.py --json   # the same as data

Exit nonzero when a bank parses to nothing, when a computed verdict diverges from
`teleology/CASE_BANK.md` without a line in `teleology/DIVERGENCES.md`, when a listed
divergence does not occur, or when a status in `teleology/THEOREMS.md` is not the one its
check supports. Python 3.9+ standard library; exact rationals; no network. `tests/run.py`
hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `teleology/ACCOUNT.md` | the account over a model in which her update rule and allowed set are coordinates of her state |
| `teleology/LEAN_MAP.md` | each notion against the existing Lean declaration, with the exact difference |
| `teleology/CASE_BANK.md` | fifty-five cases with predictions frozen before the code: the dispatch's fifteen, the thirty-three of the two banks below, seven added |
| `teleology/DIVERGENCES.md` | the one computed verdict that differs from its prediction |
| `teleology/THEOREMS.md` | statements 1–8, each with one status and its check |
| `teleology/model.py`, `teleology/cases.py`, `teleology/bank.py` | the model and its clauses; the cases; the bank's reader and matching rule |
| `teleology/theorems.py`, `teleology/run.py` | the checks behind the statements; this pass's runner |
| `CASE_BANK.md` | nineteen cases, B1–B6 and T1–T13, each with a scenario and a source |
| `steering/CASE_BANK.md` | fourteen further cases, N1–N14, on one scene template |
| `steering/PRIOR_WORK.md` | survey of published work on manipulation, persuasion, function and fiduciary duty, by source |
| `steering/DIVERGENCES.md` | seven computed verdicts that differ from `steering/CASE_BANK.md`'s predictions; cited from `DECISIONS.md`, *Awaiting the author* |
| `REMOVED.md` | files removed from this directory on 2026-11-11, each with its reason |
| `run.py`, `tests/run.py` | the runner and its hand-over |

## Recorded verdicts

Each bank carries, beside its cases, verdicts pre-registered for a definition of legitimacy
tested on it. What was computed against them is recorded in
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, §1–§8 and *Follow-up of
2026-11-10*, and summarized by the two lines the round's record in `state/rounds.json`
quotes.

Verdict: DEFINITION-SURVIVES-THE-BANK — nineteen computed verdicts match their pre-registrations with no forced revision; every clause is forced by a banked case, W under the free vocabulary only; the honest class factors through an explicit replay F; the coarsened L convicts B4 and the refined L acquits T10. L0 must read the transition function, the replay F absorbs L0 and L3 on this bank, and L1 and L3 overlap on every direct standards write so that T5 alone forces L3. Nothing registered; every component open or a living note.

Follow-up verdict (the steering account): CLARIFIES and REDUCES-TO-KNOWN, a mixture — the steering account's proper drivers, its broken/steered distinction and its two standards restate published notions (malfunction of a function; pathology against manipulation by a parasite; arm's length against fiduciary duty; no effect of the adviser's aim on a delicate state), and C1, C2 and C7 are instances or corollaries of known results. What the follow-up adds: on 38 variants of 33 cases the faithful-adviser standard's acquittals lie inside the arm's-length standard's, which lie inside those of L0–L3 ∧ W, with the replay form comparable to none of the three; and C4, following the proper driver is a guarantee against an adviser who may be opposed and fails against one whose aim is hers when she cannot take in everything it knows. C3 and C5 are refuted as written; C8 is open. Twenty-seven of 33 cases match their predictions in every column, seven verdicts on six cases diverge, and no per-case choice was needed. Nothing registered; every component open or a living note.
