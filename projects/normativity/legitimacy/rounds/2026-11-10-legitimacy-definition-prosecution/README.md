# Legitimacy: a part as a mechanism and a purpose on the world

Round `2026-11-10-legitimacy-definition-prosecution`. Every component is **open** or a
**living note**; nothing is registered.

## The account

Direction: `DECISIONS.md`, `2026-11-11--legitimacy-purpose-first-direction`. The idea that
manipulation is the distortion of an actor away from its purpose, with a whole's purpose
conferring purposes on its parts, is Sam Eisenstat's; the development below is the
maintainer's and the prompt author's. Closely related work on the same problem: Nora
Ammann, *The Value Change Problem* (<https://www.alignmentforum.org/s/3QXNgNKXoLrdXJwWE>).
`blocks/SETTING.md` is the current statement; `scored/ACCOUNT.md`,
`decomposition/ACCOUNT.md` and `teleology/ACCOUNT.md` are earlier ones.

A world is a finite set of states with a prior. The adviser knows something of the state,
has an aim, and by a rule takes an action with four components: a **signal**, a
**consequence** for her moves, a **force** on a part's move, an **alteration** of a part's
mechanism. The **actual condition** is the law of state and action under its rule; the
**null condition** is the law with no action. The principal is **parts**, each with moves,
a **mechanism** from the world state to a move, and a utility on the world and the move,
which is what the part is for and is given, not recovered. No view is given: a part sees
what its move distinguishes. A part is **in range** at a grain when no re-reading of its
own move, allowed to use the grain, does better by its utility, and its **gap** is what
the best re-reading would gain; for a part that estimates a quantity this is calibration.
The adviser **subverts** a part whose gap is wider than under the null condition, **harms**
a choosing part when its consequence lowers the most the part could obtain, and its
influence is **illegitimate** when it subverts or harms a part, forces or alters one that
no part of hers in range asked it to, or lets its aim decide between options every part
of hers ranks equally. Her verdict is **legitimate** when every part behind it is in
range. An **end** is a part for what it values at the time; an **end-revising part**
replaces one end and is for the **fit** of the replacement with her other ends at that
time, what they then attain less what they would lose if the replacement got its best; a
**maintaining part** alters a mechanism and is for what that part is for. All names are
provisional.

## What was found

`blocks/RESULTS.md` carries thirty-two statements with a status each, by the dispatch's
seven questions, and the verdict on each case with its reason; the report's section
*Fifth follow-up* carries the external review and what was done with each of its points.

Follow-up verdict (a part as a mechanism and a purpose on the world): MIXED — with purposes given and not recovered, range and gap are stated and used once a grain is fixed, and the four kinds of influence are not: they need the adviser's null action as a comparison, typed actions, a move that carries confidence, her verdict as one part's move, the rule at other aims for ties, and a menu for each revising part. Of the dispatch's twenty-seven cases with a prediction twenty-six have the predicted verdict under renderings the executor wrote, a check of consistency and not a test; an advocate for an undisclosed side diverges because the null comparison runs her mechanism in the adviser's absence. Of thirty-two statements nine are proved on paper, eighteen hold on a stated example and five are refuted, each a fact about one formalization. Conditioning on the step catches a lie targeted in time; a lie targeted at a state is caught only by a move that carries confidence, at a size second order in the lie's probability, and none of four grains computed separates it from honest difficulty when the move is two-valued. A foreseeable shift in her verdict equals the shift in what the verdict is for up to the roots of the verdict part's two gaps, and a maintaining part in range with a menu closed under re-reading installs a mechanism in range; that every shift traces to something out of range or to the adviser is refuted, and whose a gap is rests on a stipulated comparison. A threat is told from an offer and a true warning with no aim read, and from a warning of the adviser's own standing practice only by a supplied fact about the branch not taken. Fit among her ends gives a revising part a purpose with no fixed final end, never excludes dropping an end, and does not say which of two opposed ends yields: a chain of two steps each in range carries her from the outcome her starting ends value most to the one they value least, and the rule on ties stops an aim choosing between equally fitting replacements only when the parts that later tell them apart are left out. Parts in range do not give a verdict in range unless the aggregation is itself calibrated. The post's calibration hypothesis is implied in probability, for a bounded score, by the range condition at the grain of the history of the part that estimates the score, and one existing Lean theorem applies to advisers whose signal does not vary with their aim. The decomposition adds permission and a rule of attribution and no protection. Nothing registered; every component open or a living note.

## Run

    python3 run.py          # the four accounts: banks, statements, the addenda's facts
    python3 run.py --json   # the same as data

About two minutes. Exit nonzero when a bank parses to nothing, when a computed verdict
diverges from its bank without a line in that pass's `DIVERGENCES.md`, when a listed
divergence does not occur, or when a status in any `THEOREMS.md` or in `blocks/RESULTS.md`
is not the one its check supports. Python 3.9+ standard library; exact rationals; no
network. `tests/run.py` hands over to `run.py` so the repository-level runner finds it.

## Layout

| path | what |
|---|---|
| `blocks/SETTING.md` | the position, the model, each choice with its alternative, and the devices the model needed |
| `blocks/CASE_BANK.md` | thirty-seven rows frozen before the code: the dispatch's twenty-eight cases with its predictions, and eight added |
| `blocks/RESULTS.md` | statements by question, each with one status and its proof or example; the verdict on each case |
| `blocks/DIVERGENCES.md` | the one row whose computed verdict differs from its prediction |
| `blocks/model.py`, `cases.py`, `bank.py`, `results.py`, `run.py` | the model; the cases as scenes; the bank's reader; the checks; this pass's runner |
| `scored/` | the account with candidates weighted as explanations and influence judged against the adviser's aim (`ACCOUNT.md`), its bank of ninety-four cases, its nine statements and what runs them |
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

Follow-up verdict (candidates weighted, influence judged against the adviser's aim): MIXED — of nine statements about the account, five are refuted and four hold on a stated domain, each a conditional calculation in one formalization: a small scene, three stipulated principals, two tabulated description languages, one cost for a missed move. Scoring candidates by parsimony, fit and handles, read by a second predictor, concentrates the weight in mass (the ten heaviest of 4,000 hold 0.84 to 0.98) and not on agreeing candidates: at 0.95 or more of the weight her judging part is given no purpose or one naming its own mechanism, its behaviour carried as a table of her history, and the heavy candidates split on which adviser inputs are illegitimate; a purpose equal to its mechanism is charged as a rule by intersubjectivity and is not removed as a table; the score is a loss, not a code length. Read as the best move on what a part sees, a purpose for the belief part follows her corrections and the judging part's does not. Judged against the adviser's aim under stated candidates and assigned aim structures, 77 of 89 cases match their evident character against 66 by a changed standard, and a threat is illegitimate; a lie told at every aim passes, and the weights do not favour the stated candidates. Between actions that harm, subvert and force nothing against each other her choice is the same under the stated candidate and not under the candidates tied at the top for two principals; no maximizing adviser was analysed. The condition is strictly weaker than aim-freedom of the adviser's whole intervention, to whose guarantee the decomposition adds nothing; it adds a rule for which aim-dependent variation to permit. Eighty-nine of ninety-three banked rows match, which is fit. Nothing registered; every component open or a living note.
