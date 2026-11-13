# Legitimacy: candidates weighted as explanations, influence judged against the adviser's aim

Round `2026-11-10-legitimacy-definition-prosecution`. Every component is **open** or a
**living note**; nothing is registered.

## The account

Direction: `DECISIONS.md`, `2026-11-11--legitimacy-purpose-first-direction`. The idea that
manipulation is the distortion of an actor away from its purpose, with a whole's purpose
conferring purposes on its parts, is Sam Eisenstat's; the development below is the
maintainer's and the prompt author's. Closely related work on the same problem: Nora
Ammann, *The Value Change Problem* (<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>).
`scored/ACCOUNT.md` is the current statement; `decomposition/ACCOUNT.md` and
`teleology/ACCOUNT.md` are the two earlier ones.

The principal pursues a goal through **parts**, each with moves, a small view and a
mechanism. A **candidate** is an explanation of her: a goal; for each part a **purpose**, a
goal function saying what the part is for; and **exceptions**, entries saying what a part
does on a view her history contains. At a situation it predicts, for each part with the
other parts' moves as they were, the exception's move if one applies and otherwise the
moves best by the part's purpose. Its **weight** is `2^(−bits)` normalised, where `bits`
is one sum: the length of the explanation (**parsimony**), a cost for every move on her
history it does not predict (**retrodictive fit**), and the same for every move it does
not predict on probes — adviser inputs she has not met, a better instrument, a falsehood
disclosed, a source shown unreliable, a part degraded (**handles**) — as read by a second
predictor who has the explanation and the scene and for whom a term naming her own
mechanism predicts nothing (**intersubjectivity**). In a situation a part's **best** is
the most its purpose could obtain from any move, its **got** what its move obtains, the
**gap** the shortfall. The adviser is a rule from what it knows and what it aims at to an
action. Its action is **aim-driven** where another aim would have acted differently; it
**harms** a part when the best is lower than under that other action, **subverts** it when
the gap is wider, **forces** it when it sets the part's move or mechanism; and the
influence is **illegitimate** when it harms, subverts or forces a part, its aim is not
that part's own purpose, and no standing verdict of hers covers it. All names are
provisional.

## What was found

`scored/THEOREMS.md` carries nine statements with a status each; the report's section
*Fourth follow-up* carries the external review and what was done with each of its points.

Follow-up verdict (candidates weighted, influence judged against the adviser's aim): MIXED — of nine statements about the account, five are refuted and four hold on a stated domain, each a conditional calculation in one formalization: a small scene, three stipulated principals, two tabulated description languages, one cost for a missed move. Scoring candidates by parsimony, fit and handles, read by a second predictor, concentrates the weight in mass (the ten heaviest of 4,000 hold 0.84 to 0.98) and not on agreeing candidates: at 0.95 or more of the weight her judging part is given no purpose or one naming its own mechanism, its behaviour carried as a table of her history, and the heavy candidates split on which adviser inputs are illegitimate; a purpose equal to its mechanism is charged as a rule by intersubjectivity and is not removed as a table; the score is a loss, not a code length. Read as the best move on what a part sees, a purpose for the belief part follows her corrections and the judging part's does not. Judged against the adviser's aim under stated candidates and assigned aim structures, 77 of 89 cases match their evident character against 66 by a changed standard, and a threat is illegitimate; a lie told at every aim passes, and the weights do not favour the stated candidates. Between actions that harm, subvert and force nothing against each other her choice is the same under the stated candidate and not under the candidates tied at the top for two principals; no maximizing adviser was analysed. The condition is strictly weaker than aim-freedom of the adviser's whole intervention, to whose guarantee the decomposition adds nothing; it adds a rule for which aim-dependent variation to permit. Eighty-nine of ninety-three banked rows match, which is fit. Nothing registered; every component open or a living note.

## Run

    python3 run.py          # the three accounts: banks, statements, the addenda's facts
    python3 run.py --json   # the same as data

About three minutes. Exit nonzero when a bank parses to nothing, when a computed verdict
diverges from its bank without a line in that pass's `DIVERGENCES.md`, when a listed
divergence does not occur, or when a status in any `THEOREMS.md` is not the one its
check supports. Python 3.9+ standard library; exact rationals; no network. `tests/run.py`
hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `scored/ACCOUNT.md` | the account over a finite model, with each choice and its alternative |
| `scored/CASE_BANK.md` | ninety-four cases, eighty-nine with predictions frozen before the code and five to be reported: the eighty-nine of `decomposition/CASE_BANK.md` with an aim structure each, five added |
| `scored/DIVERGENCES.md` | the four rows, on three cases, whose computed verdict differs from its prediction |
| `scored/THEOREMS.md` | statements 1–9, each with one status and its check |
| `scored/scene.py`, `weights.py`, `cases.py`, `bank.py`, `theorems.py`, `run.py` | the scene and the three principals; explanations, code lengths and weights; the cases; the bank's reader; the checks; this pass's runner |
| `decomposition/` | the account as a goal pursued through parts with yes-or-no constraints on candidates (`ACCOUNT.md`), its Lean map, its bank of eighty-nine cases, its nine statements, two addenda (`TWO_DECOMPOSITIONS.md`, `ADVISER_AS_PART.md`) and what runs them; `scored/` builds on its model and scenes |
| `teleology/` | an earlier statement of the purpose-first account (a fixed condition `K` with clauses *sound*, *in range*, *maintained*), its bank of fifty-five cases, its eight statements and what runs them; an earlier statement than `decomposition/ACCOUNT.md` |
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

Follow-up verdict (purpose as a goal pursued through parts): MIXED — of nine statements about the account, four are refuted and five hold on a stated domain, each as a fact about one formalization. The constraints do not fix purposes in it: in a class of 3,000 candidates over a three-part chain eight are admissible, no two classifying the adviser's actions alike, and a candidate whose goal is whatever she does is excluded only by a condition no extensional test captures (fifteen are admissible without it). Read pairwise, never opposed excludes all eight, and leaves two once the situations where her own judging part reverses a right belief are not counted usual. A lie widens no gap where she was already wrong, and none under four of the eight where it concerns a matter nothing reads. The four kinds are not exclusive, and only the step from serving to not serving survives redescription. That every bad change in what she cares about widens a gap holds in the one scene enumerated, close to by construction; her goal can fall through her parts' coordination with no gap widened. A legitimacy predicate built from gaps has the shapes of the post's scoring and decision, depends on the comparison action (27, 33, 46 or 38 of 57 renderings convicted), and under none gives the gate's no-gain property, since harm is not subversion. Eighty-four of eighty-five banked predictions match, which is fit. Nothing registered; every component open or a living note.
