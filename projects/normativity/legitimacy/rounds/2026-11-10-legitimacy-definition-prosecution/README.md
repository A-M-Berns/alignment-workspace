# Legitimacy: purpose as a goal pursued through parts

Round `2026-11-10-legitimacy-definition-prosecution`. Every component is **open** or a
**living note**; nothing is registered.

## The account

Direction: `DECISIONS.md`, `2026-11-11--legitimacy-purpose-first-direction`. The idea that
manipulation is the distortion of an actor away from its purpose, with a whole's purpose
conferring purposes on its parts, is Sam Eisenstat's; the development below is the
maintainer's and the prompt author's. Closely related work on the same problem: Nora
Ammann, *The Value Change Problem* (<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>).
`decomposition/ACCOUNT.md` is the current statement.

The principal's purpose is an overall goal together with a description of how she pursues
it through parts. A **candidate** description has a goal; parts, each with its own moves,
a small view, a **mechanism** (what it does) and a **goal function** (what it is for,
scored by how things are); a rule fixing her action from the parts' moves; and moves that
alter mechanisms, which is how what she cares about changes. In a situation a part's
**best** is the most its goal function could obtain from any of its moves, its **got**
what its mechanism's move obtains, and the **gap** the shortfall; it **serves** when the
gap is zero. An adviser's action is **help** when it raises a part's best or narrows its
gap, **harm** when it lowers the best, **subversion** when it widens the gap with the
mechanism still running, **force** when it replaces a part's move. Manipulation is
subversion. A candidate is **admissible** when its mechanisms fit what she does, its
purposes **add up** (*nothing left over*, *never opposed*), its parts are **mostly
serving**, and each part's purpose is stated independently of its mechanism and is one a
part seeing little could carry. All names are provisional.

## What was found

`decomposition/THEOREMS.md` carries nine statements with a status each; the report's
section *Follow-up of 2026-11-12* carries the external review and what was done with it.

Follow-up verdict (purpose as a goal pursued through parts): MIXED — of nine statements, four are refuted and five hold on a stated domain. The constraints do not fix purposes: in a class of 3,000 candidates over a three-part chain fifteen are admissible, no two classifying the adviser's actions alike, and a candidate whose goal is whatever she does is among them; a stronger reading of independence leaves eight that agree on every action but a lie about a matter nothing reads. A lie widens no gap under one admissible candidate, and none at worlds where she was already wrong. The four kinds are not exclusive and only the step from serving to not serving survives redescription. Her goal can fall with no gap widened. A legitimacy predicate built from gaps fits the post's scoring and decision shapes, depends on the comparison action (27, 33 or 46 of 57 renderings convicted) and is independent of aim-freedom. Eighty-eight of eighty-nine banked predictions match, which is fit. Nothing registered; every component open or a living note.

## Run

    python3 run.py          # both accounts: bank, statements, and the addenda's facts
    python3 run.py --json   # the same as data

About two minutes. Exit nonzero when a bank parses to nothing, when a computed verdict
diverges from its bank without a line in that pass's `DIVERGENCES.md`, when a listed
divergence does not occur, or when a status in either `THEOREMS.md` is not the one its
check supports. Python 3.9+ standard library; exact rationals; no network. `tests/run.py`
hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `decomposition/ACCOUNT.md` | the account over a finite model, with each choice and its alternative |
| `decomposition/LEAN_MAP.md` | each notion against the existing Lean declaration, with the exact difference |
| `decomposition/CASE_BANK.md` | eighty-nine cases with predictions frozen before the code: the dispatch's twenty-four, the fifty-five of the three banks below, ten added |
| `decomposition/DIVERGENCES.md` | the one computed verdict that differs from its prediction |
| `decomposition/THEOREMS.md` | statements 1–9, each with one status and its check |
| `decomposition/TWO_DECOMPOSITIONS.md` | a many-to-many relation between mechanisms and subgoals, tried on the difficulties found |
| `decomposition/ADVISER_AS_PART.md` | the adviser taken as one of her parts, against the same difficulties |
| `decomposition/model.py`, `scenes.py`, `cases.py`, `bank.py` | the model; the scenes; the cases; the bank's reader and matching rule |
| `decomposition/theorems.py`, `extensions.py`, `run.py` | the checks behind the statements; the addenda's computations; this pass's runner |
| `teleology/` | an earlier statement of the purpose-first account (a fixed condition `K` with clauses *sound*, *in range*, *maintained*), its bank of fifty-five cases, its eight statements and what runs them; superseded as the statement of the account by `decomposition/ACCOUNT.md` |
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
2026-11-10*, and summarized by the lines the round's record in `state/rounds.json` quotes.

Verdict: DEFINITION-SURVIVES-THE-BANK — nineteen computed verdicts match their pre-registrations with no forced revision; every clause is forced by a banked case, W under the free vocabulary only; the honest class factors through an explicit replay F; the coarsened L convicts B4 and the refined L acquits T10. L0 must read the transition function, the replay F absorbs L0 and L3 on this bank, and L1 and L3 overlap on every direct standards write so that T5 alone forces L3. Nothing registered; every component open or a living note.

Follow-up verdict (the steering account): CLARIFIES and REDUCES-TO-KNOWN, a mixture — the steering account's proper drivers, its broken/steered distinction and its two standards restate published notions (malfunction of a function; pathology against manipulation by a parasite; arm's length against fiduciary duty; no effect of the adviser's aim on a delicate state), and C1, C2 and C7 are instances or corollaries of known results. What the follow-up adds: on 38 variants of 33 cases the faithful-adviser standard's acquittals lie inside the arm's-length standard's, which lie inside those of L0–L3 ∧ W, with the replay form comparable to none of the three; and C4, following the proper driver is a guarantee against an adviser who may be opposed and fails against one whose aim is hers when she cannot take in everything it knows. C3 and C5 are refuted as written; C8 is open. Twenty-seven of 33 cases match their predictions in every column, seven verdicts on six cases diverge, and no per-case choice was needed. Nothing registered; every component open or a living note.

Follow-up verdict (the purpose-first account): MIXED — of nine statuses on eight statements about the account, two are proved, two hold on a stated domain, four are refuted and one is open. Her later judgment is at least as good by her own lights for expectations (the value-of-information inequality, which needs her values fixed) and not for values. That trust is not manufactured, and that the gate gains nothing, are refuted for in range as the account states it, and for an adviser whose aim she knows when her evaluation is a verdict; they hold when nothing the adviser does to her depends on its aim, which is close to the class-level transparency the workspace's Lean already asks. A departure of small probability costs the gated score a fixed amount. The verdicts follow the allowed set a case is given: nineteen of twenty-one in-range failures become legitimate once she allows for every aim, the other two being the two whose source she cannot represent. A threat fails no clause. Fifty-four of fifty-five banked predictions match, which is fit. Nothing registered; every component open or a living note.
