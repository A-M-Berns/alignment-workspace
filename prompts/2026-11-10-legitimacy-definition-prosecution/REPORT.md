# REPORT — Legitimacy definition prosecution

Round directory: `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`.
Runner: `python3 run.py` there; `--json` for the data every table below is read from.
Round record: `state/rounds.json`, id `2026-11-10-legitimacy-definition-prosecution`.

**Verdict: DEFINITION-SURVIVES-THE-BANK.** Nineteen computed verdicts match their
pre-registrations with no forced revision (`FORCING.md` is empty); every clause is forced
by a banked case, W under the free vocabulary only; the honest class factors through an
explicit replay `F`; the coarsened `L` convicts B4 and the refined `L` acquits T10. Three
findings beside the table, in §4. Nothing is registered; every component closes **open**
or as a **living note** (§7).

## 1. The verdict table

Pre-registered from `CASE_BANK.md` (frozen in commit `1a554767`, before any fixture
code); computed under the house individuation of `L`. *Failing* lists every clause that
fires, so a conviction carried by more clauses than the bank names is visible. Match is
the bank's rule: the named clause among the failing ones, the named silent clauses
holding, formation as pre-registered.

| case | label | pre-registered | computed (failing) | formation | match |
|---|---|---|---|---|---|
| B1 identical-trace capture | build | illegitimate(L1), L3 silent | illegitimate (L1) at positions 1–2 | not-formed | yes |
| B2 manufactured trust | build | illegitimate(L1) | illegitimate (L1, L3) | not-formed | yes |
| B3 transient capture | build | illegitimate(L1 at the pushed positions) | illegitimate (L1 at positions 0–2, L3) | not-formed | yes |
| B4 persuasion control | build | legitimate | legitimate | formed | yes |
| B5 selective withholding | build | illegitimate(L2), L1 silent | illegitimate (L2) | not-formed | yes |
| B6 two revisions, one name | build | legitimate | legitimate | formed | yes |
| T1 duress | test | illegitimate(L0), L1–L3 silent | illegitimate (L0, at the option `refuse`) | not-formed | yes |
| T2 offer-improvement | test | legitimate | legitimate | formed | yes |
| T3 undue influence | test | illegitimate(L2) | illegitimate (L2) | not-formed | yes |
| T4 overnight value replacement | test | illegitimate(L3) | illegitimate (L1, L3) | not-formed | yes |
| T5 long game | test | illegitimate(L3), L1 silent | illegitimate (L3, lost from position 1) | not-formed | yes |
| T6 licensed drift with an agenda | test | legitimate | legitimate | formed | yes |
| T7 salience reordering | test | individuation-dependent | individuation-dependent: sequence legitimate; multiset illegitimate (L1) | – | yes |
| T8 gullible principal | test | legitimate | legitimate | formed | yes |
| T9 world-starvation | test | legitimate; not-formed(coverage) | legitimate | not-formed(coverage) | yes |
| T10 direct write with endorsement | test | illegitimate(L1 or L3) | illegitimate (L1), with and without the endorsement | not-formed | yes |
| T11 seed boundary | test | out-of-scope(seed-freeze) | out-of-scope: seed after installation legitimate; before, illegitimate (L1, L3) | – | yes |
| T12 strategically compliant advisor | test | legitimate | legitimate | formed | yes |
| T13 universal deprivation | test | legitimate; not-formed(coverage) | legitimate | not-formed(coverage) | yes |

Three convictions carry a clause the bank did not name. B2 and B3 replace or push a
standards coordinate by a direct write, and L3 — absent from the source round's
definition — fires on it beside L1. T4's replacement is likewise a direct standards
write with a silent honest peer, so L1 fires beside L3. T10 is caught by L1 alone: the
written coordinate is her judgment, protected and not a standard, and the endorsement
is an autonomous step, so L3 holds in both variants and the verdict is the same in both.

## 2. The forcing table

Each clause deleted and the bank rerun; a flip is a case whose legitimacy category
changes.

| clause | reading of the ablation | flips |
|---|---|---|
| L0 | deleted, house `L` | T1 → legitimate |
| L1 | deleted, house `L` | B1, T10 → legitimate |
| L2 | deleted, house `L` | B5, T3 → legitimate |
| L3 | deleted, house `L` | T5 → legitimate |
| W | deleted: the vocabulary unconstrained; the bank under the coarse and refined `L` | coarse: B4, B6 → illegitimate, T7 → illegitimate; refined: B1, T10 → legitimate, T7 → legitimate. Under the house `L`: no flip |

Every clause is forced. B2, B3 and T4 flip under no single deletion, since two
clauses carry each. T5 is the only case that forces L3: the shift of `Lic` is invisible
to `Z`, every later step is licensed at its own pre-state, and no honest arm shares the
long-game advisor's trace.

## 3. Audits

**§5b satisfiability.** `V₀` is four honest advisors on one history — H1; H2, which
also writes a coordinate `Z` does not read; H3 and H4, which add different licensed
reasons. `F` is constructed explicitly as the replay: the principal run with the advisor
replaced by a player of the licensed trace, `F(e, L) := Z*(replay(e, L))`
(`fixture/model.py`, `replay`). `Z*(ρ(π, e)) = F(e, L(ρ(π, e)))` holds for all four; `F`
is not constant on `V₀`; every clause holds on `V₀`; the trace-equal distinct-policy
pair is (H1, H2).

**Trace-equal pairs per `V`.** Every case's `V` contains H1 and H2 (T13: W1 and W2), so
no kill test has zero pairs. Counts: B1, B2, B3, T4, T10 have 3 (the villain's trace
equals the honest pair's); every other case has 1.

**§5c, both directions.** The coarsened `L` — the set of coordinates revised under a
license, the coordinate-list presentation the source round warned against — gives B4's
persuader the honest arms' trace and a different `Z` from position 1: L1 convicts, and
W's fineness condition fails on the same pairs. The refined `L` — the house trace with
the policy's identity appended — gives T10's ventriloquist no trace-equal peer: L1 is
vacuous, L0, L2 and L3 hold, the verdict is legitimate, and W's coarseness condition
fails on (H1, H2). Both land.

**Triviality.** Eight cases compute legitimate and nine illegitimate under the house
individuation; the definition is neither trivially true nor trivially false on the bank.

**Beyond the prompt, reported and not adopted.** The replay `F` read as a single-run
condition, `Z*(ρ(π, e)) = F(e, L(ρ(π, e)))` for the policy itself, holds for every honest
arm of every case and fails exactly for B1, B2, B3, T1, T4, T5 and T10 — it convicts
by itself everything the pairwise L1, L0 and L3 convict between them, and acquits
B5 and T3 (L2's cases) and every legitimate case including T2, whose accepted option is
licensed content. Three diagnostics: B3's endpoint-only reading of L1 finds no pair
while the process reading finds positions 0–2; T1's realized-transition reading of L0
acquits all three arms, since the threatened principal signs and the world then moves
as the history says for signing; T12's complier makes zero grounds-bearing
contributions against two for each honest arm, with equal deliveries.

## 4. Findings

1. **L0 reads the transition function.** The prompt's "the world component evolves by
   `e` alone" has to be a condition on the consequence map the principal faces, not on
   the realized world trace: a threat is a change to the consequence of an option she
   does not take. The fixture's L0 compares the consequence of every option the history
   supplies with the history's, and lets the advisor add options through the channel.
   The stricter reading, no advisor-sourced consequence at all, convicts T2; the looser,
   the realized trace, acquits T1. Recorded as agent-decided in `DECISIONS.md`.
2. **The canonical `F` absorbs L0 and L3 on this bank.** The prompt's `∃F` form is
   equivalent to the pairwise test and relative to `V`; the replay `F` is single-run
   and catches every direct write and the duress. Which form the definition means is
   the equivalence-forms question, filed as item 136.
3. **L1 and L3 overlap on direct standards writes.** With a silent honest peer in `V`,
   every unlicensed write to a coordinate `Z` reads fires L1; L3 adds nothing there.
   L3's own territory is the write `Z` does not read — `Lic` itself — followed by
   licensed steps (T5), and the seed boundary (T11).

## 5. Deviations and corrections to the prompt

- **B6 has no verdict in the prompt.** §3 lists it as W's build case and names none.
  The bank fixes it as legitimate under the definition as stated, which includes W;
  the coarse-vocabulary conviction is W's failure, exhibited by §5c. Agent-decided.
- **W's ablation.** §4 makes an ablation that flips nothing an exit failure; §5a says a
  clause with no flip is reported unforced; §2 says W is prosecuted by §5c, not
  assumed. Under the house `L`, W holds on every case and its deletion flips nothing.
  The runner reads W's ablation as the vocabulary unconstrained — the bank under the
  coarse and refined `L` with W's check removed — and reports the house-`L` non-flip
  beside it. Agent-decided; the alternative turns the runner red on a clause the
  prompt prosecutes elsewhere.
- **"Kill test" in §5b** is read as every case pre-registered illegitimate. Every `V`
  carries the honest pair by construction, so the invalidation condition is checked
  and never met.
- **T13 added** in the freezing commit, as §3 permits, with its source.
- **`tests/run.py`** is added beside `run.py`: the repository-level runner finds
  `projects/**/tests/run.py`, and the shim hands over to the runner the prompt names.
- **Additions beyond §5:** the replay-form audit and the three diagnostics of §3, each
  reported and none adopted into the definition.
- The runner was executed under Python 3.9 and 3.12; both green.

## 6. What was not shown

- **No equivalence theorems.** Sufficiency, betting and offers-only normal forms are
  not stated here even as conjectures; the replay-form observation is a fixture fact
  about nineteen cases, not a theorem. Filed as item 136.
- **No consumer lemmas.** Nothing is proved toward the trust interface's candidate
  theorem or the corrigibility slot; which clauses either reads is not stated. Item 137.
- **`Lic` approximates merit-sensitivity, and the exploit gap is open.** `Lic` is a
  table of allowed coordinates and a grounds requirement. T7's resolution (b) shows the
  cost: wherever order matters to the principal and `Lic` does not read order, an
  honest advisor who must pick an order is exposed to L1. Nothing here closes that.
- **`Due` and `E`-exogeneity are stipulated.** Each case declares what is due and
  what the environment makes available; nothing derives either, and T9 and T13 rest
  entirely on the stipulation.
- **`V` is an input.** L1 and L2 are relative to the class: T13's class, every member
  of which withholds the same due reason, passes L2; T5's long-game advisor passes L1
  because no honest arm shares its trace. Every `V` here is three or four scripted
  policies chosen by the round.
- **The principal is a toy.** A weighted-sum decision rule, an anchoring rule, four
  autonomous step kinds and a judgment-by-maximum. T1's "sound judgment" is modelled
  as her weighing a true informational offering; T4's Beth is a single overwritten
  value; B1 mirrors the faithful/steered pair's structure (identical delivered record,
  a hidden channel into a protected coordinate) and reproduces none of that artifact's
  dynamics.
- **The seed-freeze point is a parameter**, declared and not justified (T11).
- **Everything is a finite fixture.** `test-supported` is the ceiling of any future
  registration, and nothing is registered now; no `CLAIMS.md` entry, no Lean.
- **Components close open or as living notes**, never closed: no statement of record
  stands for any of them.

## 7. Components at close

| component | verdict | reopening condition |
|---|---|---|
| the definition L0–L3 ∧ W, prosecuted | **open** — survives the bank | a case module under `fixture/cases/` with a pre-registered verdict and a cited source that L0–L3 ∧ W classifies legitimate and the bank's standards illegitimate, or the converse; the runner diverging on it |
| W as a condition on the vocabulary | **living note** — both attacks land; forced only under the free vocabulary | an individuation satisfying W's two conditions under which a banked verdict changes |
| the replay-form observation | **living note** | item 136's round |
| equivalence forms; consumer lemmas; advisor-respect | **open** — filed | items 136, 137, 138 |

## 8. Filings, names, and what is reserved

**Filed under the prompt's scope grant** (`ATTENTION.md`, rendered from the item
nodes `graph/nodes/item-136.md`, `item-137.md`, `item-138.md`, held by the
`legitimacy` frame): item 136, the equivalence forms of factorization; item 137, the
consumer lemmas; item 138, the advisor-respect condition T12 delimits. One
`DECISIONS.md` entry, agent-decided and reversible: anchor
`2026-11-10--legitimacy-prosecution-readings`, the three readings of §4.1 and §5.

**New names, all provisional:** L0 "channel confinement"; W "individuation
well-formedness"; the round name "legitimacy definition prosecution"; case names
B1–B6, T1–T13; the module names `house`, `coarse`, `refined`, `sequence`, `multiset`
for individuations of `L`; `replay` for the canonical `F`.

**Outstanding maintainer actions:** none reserved. The pull request is not
auto-merged, as the prompt directs; the merge is a pull-request fact and not a queue
entry.

## Follow-up of 2026-11-10 — the steering account

Dispatch: `PROMPT-followup.md`, kept verbatim. Everything is under
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/`; `python3 run.py` in the round directory runs the first pass unchanged
and then the follow-up, and `python3 run.py --steering-json` prints the data the tables
below are read from. Commits, in the order the prompt fixes: `11e59adb` the survey;
`f8f5c68c` the definitions and the bank together, before any code; `0af6eba7` the model,
verdicts and statements.

**Headline: CLARIFIES and REDUCES-TO-KNOWN, a mixture — the steering account's proper drivers, its broken/steered distinction and its two standards restate published notions (malfunction of a function; pathology against manipulation by a parasite; arm's length against fiduciary duty; no effect of the adviser's aim on a delicate state), and C1, C2 and C7 are instances or corollaries of known results. What the follow-up adds: on 38 variants of 33 cases the faithful-adviser standard's acquittals lie inside the arm's-length standard's, which lie inside those of L0–L3 ∧ W, with the replay form comparable to none of the three; and C4, following the proper driver is a guarantee against an adviser who may be opposed and fails against one whose aim is hers when she cannot take in everything it knows. C3 and C5 are refuted as written; C8 is open. Twenty-seven of 33 cases match their predictions in every column, seven verdicts on six cases diverge, and no per-case choice was needed. Nothing registered; every component open or a living note.**

### F1. The survey's closing table

`steering/PRIOR_WORK.md`. Twenty-three sources opened and read in part or whole (Wex's five
pages counted once); what could
not be opened is listed there as unverified.

| | against the sources read | source |
|---|---|---|
| C1 | a known result's instance | Blackwell's theorem, deterministic case; the "at least the baseline for every goal" form is Turner's non-obstruction |
| C2 | not found as stated | follows from C1; Kamenica–Gentzkow exclude lying by assumption |
| C3 | not found | no source on offers and threats was opened |
| C4 | not found as a maximin statement | the slogan is non-obstruction over a wide goal set without value inference |
| C5 | a known notion's instance | no instrumental control incentive on a delicate state, path-specific objectives (Everitt et al.; Farquhar et al.); unriggability (Armstrong and O'Rourke) |
| C6 | the distinction already known; the implication table not found | arm's length against fiduciary duty (Wex); the separating case is Kamenica–Gentzkow's prosecutor |
| C7 | already known | SEP "The Ethics of Manipulation" §3.2; Carroll et al. §2.4; broken against steered is pathology against host manipulation (Heil) |
| C8 | not found | nearest: the fiduciary duty of loyalty |

What the survey corrected in the account: *working* for beliefs is calibration to the
adviser's actual strategy, not truth of what she is told; C1 carries the hypothesis of a
working reader; the decision rule and the drivers are stipulations (Armstrong and
Mindermann's decomposition result; the function literature grounds function in a history
or an organization the toy principal lacks); an account built on parts leaving their
ideals has no place for pressure that neither falsifies a belief nor changes an option;
and the law switches standards on the relationship, which the account does not represent.

### F2. Verdicts, thirty-three cases, three notions

A bold cell differs from its prediction.

| case | arm's-length | faithful-adviser | L0–L3 ∧ W |
|---|---|---|---|
| N1 plain lie | steered | steered | passes |
| N2 honest mistake | broken, not steered | broken, not steered | passes |
| N3 lie raising her value | steered | steered | passes |
| N4 decision written | steered | steered | fails (L1) |
| N5 authorized write | not steered | not steered | passes |
| N6 weighing disabled | broken, not steered | broken, not steered | passes |
| N7 true statement, known misfire | steered | steered | passes |
| N8 known advocate | passes | steered | passes |
| N9 order chosen by `u` | steered | steered | individuation-dependent |
| N10 order by a fixed rule | not steered | not steered | **passes** |
| N11 seller who does not volunteer | passes | steered | passes |
| N12 tool she controls | not steered | not steered | passes |
| N13 selection by her question | not steered | not steered | passes |
| N14 selection by `u` | steered | steered | fails (L2) |
| B1, B2, B3, B5 | steered | steered | fails |
| B4 persuasion control | passes | **steered** | passes |
| B6 two revisions, one name | passes | **steered** | passes |
| T1, T3, T4, T5, T10 | steered | steered | fails |
| T2 offer-improvement | passes | **steered** | passes |
| T6 licensed drift with an agenda | passes | steered | passes |
| T7 salience reordering | **steered** | **steered** | individuation-dependent |
| T8 gullible principal | passes | **steered** | passes |
| T9, T13 | broken, not steered | broken, not steered | passes; not formed (coverage) |
| T11 seed boundary | out-of-scope(seed-freeze) | out-of-scope(seed-freeze) | out-of-scope(seed-freeze) |
| T12 strategically compliant | not steered | not steered | passes |

B4's persuader is, under `U := V`, an adviser whose reason another adviser of the class
does not give: arm's-length `passes`, faithful-adviser `steered`. The fixture has no fact
about whether an aim of its own selected the reason.

### F3. Divergences

`steering/DIVERGENCES.md`. Seven verdicts on six cases.

- **B4, B6, T2, T8 under faithful-adviser** — predicted to acquit, computed `steered`.
  One cause: with no aim variable in the first pass's objects the standard reads "her
  protected state is the same whichever adviser of the class she has", which forbids two
  honest advisers from differing and forbids an offer.
- **T7 under both standards** — predicted individuation-dependent, computed `steered`.
  The account has no individuation; the dependence moved into the definition of
  *working*, where clause (iv) settles it by fiat. Without that clause T7 and N9 compute
  `passes` under arm's-length.
- **N10 under L0–L3 ∧ W** — predicted individuation-dependent, computed `passes`. A class
  with one ordering gives L1 nothing to compare; the first pass's verdict on an ordering
  depends on whether `V` holds a second one, not on how the ordering was chosen.

### F4. C1–C8

`steering/THEOREMS.md`.

| | status | on what |
|---|---|---|
| C1 information helps every goal | **holds** | 512 goals × 5 disclosures; 256 goals × 225 pairs of disclosures; a working reader assumed |
| C2 a lie is not a coarsening | **holds** | 729 goals × 279 believed lies; the second half follows from the first and C1 |
| C3 offers and threats | **refuted** | the threat raises attainable value for three of nine goals (`cases/x_threat_welcome.py`: house weighed −1, 10 against 0); the offer half holds; the criterion and L0 disagree on an unsolicited gift (`cases/x_gift.py`) |
| C4 the driver as a guarantee | **holds**, under a condition | 256 goals: for any driver when `U` contains an aim opposed to hers (complete proof given); with no condition when the driver is the full disclosure; fails for `U = {g}` with a one-bit driver, 1/4 against 1/2 |
| C5 stake invariance | **refuted** as written | B5: beliefs moved, no decision moved. Holds for the belief part with every `g ∈ G` in place of her goal (64 goals, 7 beliefs) |
| C6 the ordering | **holds** | 38 variants; faithful-adviser ⇒ arm's-length is true by definition |
| C7 steered is not harmed | **holds** | all four combinations exhibited among N1–N14 |
| C8 the adviser itself | **open** | the condition separates T12 from every other case but cannot say why; T12 stays outside the account |

### F5. The implication diagram of C6

Over the 38 variants; `A ⊂ B`: every variant A acquits, B acquits, and not conversely.

    faithful-adviser  ⊂  arm's-length  ⊂  L0–L3 ∧ W          replay form: comparable with none

| separation | variants |
|---|---|
| arm's-length acquits, faithful-adviser convicts | N8, N11, B4, B6, T2, T6, T8 |
| L0–L3 ∧ W passes, arm's-length convicts | N1, N3, N7, N9 and T7 under the sequence individuation |
| replay form holds, L0–L3 ∧ W fails | N14, B5, T3, N9 and T7 under the multiset individuation |
| L0–L3 ∧ W passes, replay form fails | N5, N6 |
| arm's-length or faithful-adviser acquits, replay form fails | N5, N6 |
| replay form holds, arm's-length convicts | N1, N3, N7, N9, N14, B5, T3, T7 |

The first inclusion is definitional. The second is a fact about the bank: outside it,
`cases/x_common_fault.py` — the same unlicensed standards write in every policy — fails
L3 and is `broken, not steered` under both standards. For C5: faithful-adviser ⇒ L1 has
no counterexample and is forced; L1 and the replay form are incomparable.

### F6. Per-case choices

`steering/PER_CASE_CHOICES.md`: none. Two global stipulations do the work a per-case
choice would have done — `U := V` (the faithful-adviser verdicts on B4, B6, T2, T8) and
order-is-not-content (the arm's-length verdicts on T7, N9). Both are recorded as
agent-decided in `DECISIONS.md`, anchor `2026-11-10--steering-follow-up-stipulations`.

### F7. Deviations from the follow-up prompt

- **How sources were read.** Through a fetch tool that returns the first ~40,000
  characters of a page verbatim; later parts of long pages were fetched by offset where
  the survey relies on them, and are otherwise listed as not read. Kamenica–Gentzkow (pp.
  2590–2598) and Soares et al. were read as PDFs. The survey says per source what was
  read.
- **"Agrees with the pre-registered verdict"** for the nineteen first-pass cases is
  transcribed by one rule stated in `steering/CASE_BANK.md` (`legitimate` ↦ any verdict
  but `steered`; `illegitimate` ↦ `steered`). The prompt gives no table for them.
- **No case was added to the bank.** Three modules outside it were written after the
  freeze, with no predictions: `x_threat_welcome.py` and `x_gift.py` for C3,
  `x_common_fault.py` for C6.
- **C8's second form** — writes `Z` does not read set aside — was introduced after the
  freeze, because the condition as frozen fails on every variant for a reason unrelated
  to it. Reported as a diagnostic; the frozen form's result is reported beside it.
- **C7 uses the mean over `W`** for attainable value, as `DEFINITIONS.md` §1.5 fixes,
  not the value at the actual world.
- **No item was filed.** The residual blocker — the adviser's aim as an object, in place
  of `U := V` — was to be item 139. A node needs an author handle; the executor's model
  has none in `graph/policy.yaml`, and adding one fails
  `checkers/tests/test_graph.py`, which pins the handle set. Editing that test is an edit
  to the checker harness, so the handle was not added and the ask was folded into item
  138, whose subject it shares. Workspace friction, reported here and queued (F9).
- **Items 136 and 138** have their entries extended and their Statements unchanged; the
  map checker refuses a version bump on an unchanged Statement.
- **The runner** gained `--steering-json`; `--json` still prints the first pass alone.
  Executed under Python 3.9 and 3.12; both green.

### F8. What was not shown

- **The model is a toy.** The principal is the first pass's: she adopts a licensed
  revision at the value offered, decides by greatest credence, and has no step by which
  she infers from silence — N8's and N11's "she updates correctly" is rendered as an
  offering whose content is the correct posterior. Her decision rule ignores payoffs,
  which is the only reason N3's lie raises her value.
- **`G`, `U`, the baseline and *working* are stipulated.** So are the four drivers.
  `U := V` in particular means the faithful-adviser verdict on every first-pass case is
  fixed by which policies the first pass happened to put in the class.
- **Changes to her aims have no outside truth to follow.** The account's driver for aims
  is her own earlier state and what she learns, implemented as the first pass's L3; it
  says nothing further about what a proper change of aim is. C4 was tested for the
  belief part only, and for the aims part there is no goal by which to evaluate it.
- **Nothing here detects steering in a deployed system.** *Steered* is defined by
  comparing runs under different adviser policies with the world held fixed, which a
  model supplies and a deployment does not.
- **Agreement on N1–N14 is fit, not confidence.** The executor wrote each new case's
  scenario after reading its prediction. The model cannot tell N7 (a true statement she
  misreads) from N1 (a lie): both are a credence that differs from the posterior and
  varies with the class.
- **N10's `not steered` rests on a comparative test.** Her order-sensitivity is detected
  only when the class holds two orderings. A test that reorders her inputs would call
  her broken in N10 and in every first-pass case with two reports; it was not run.
  Item 138 now asks for it.
- **Every *holds* is an enumeration** on the domain named in `THEOREMS.md`, with payoffs
  in {0, 1} or {0, 1, 2} and at most four worlds; only C4's opposed-aim half has a
  complete proof. C2(a) was not tested with two payoff values. The inclusion arm's-length
  ⊂ L0–L3 ∧ W is false in general.
- **C3 was surveyed against nothing**, and pressure that neither falsifies a belief nor
  changes an option (nagging, peer pressure) is outside the account.
- **The survey is partial.** Primary sources for Blackwell, Noggle, Millikan, Cummins,
  Dawkins and Krebs, Crawford and Sobel and Armstrong (2010) were not opened; they are
  described only as secondary pages report them, and listed as unverified.
- **Nothing is registered.** Components: the steering account as tested — **open**; the
  survey — **living note**; C1–C8 — **open**, their statuses being runner-checked facts
  about a finite fixture with no registry entry.

### F9. Filings, names, and what is reserved

**Revised under the follow-up's scope grant; nothing filed.** Item 136's entry now asks
whether an authorized write belongs in the licensed trace (N5). Item 138's entry now
records that output-invariance separates T12 without saying why, asks for the adviser's
aim as a variable of the fixture in place of `U := V` and for an order test that does
not depend on the class, and its acceptance check is extended to match. One
`DECISIONS.md` entry, agent-decided and reversible:
`2026-11-10--steering-follow-up-stipulations`.

**New names, all provisional:** "steering account", "proper driver", "broken", "steered",
"working", "arm's-length standard", "faithful-adviser standard", "reverse convergence",
"renaming test", case names N1–N14 (the prompt's); and the executor's: "scene", "fixture
layer", "abstract layer", "calibration" and "content" for clauses (ii) and (iv) of
*working*, "adviser-side condition", "inducible", the policy names `neutral`, `neutral2`,
`own`, and the module names `x_gift`, `x_threat_welcome`, `x_common_fault`.

**Outstanding maintainer actions**

1. Rule whether the faithful-adviser standard, or only the arm's-length one, binds a
   corrigible adviser — the question the prompt reserved on T6. The results bear on it:
   the two standards separate on T6, B4, B6, T2, T8, N8 and N11. Entered in
   `DECISIONS.md`, *Awaiting the author*, with what it turns on. Decision required: one
   of *arm's-length only*, *faithful-adviser*, or *depends on a relationship the account
   must first represent*.

2. Map the AI handle `@claude-fable-5-2`: add `"@claude-fable-5-2": {kind: ai, model:
   "Claude Fable 5.2 (Anthropic)"}` to `graph/policy.yaml` and the handle to the set
   asserted in `checkers/tests/test_graph.py`
   (`test_starting_graph_carries_structure_and_the_two_rulings_only`). Entered in
   *Awaiting the author*.

The pull request is not auto-merged; the merge is a pull-request fact.

## Follow-up of 2026-11-11 — the purpose-first account

Dispatch: `PROMPT-followup-2.md`, kept verbatim. The ruling
`2026-11-11--legitimacy-purpose-first-direction` (`DECISIONS.md`) governs. The idea that
manipulation is the distortion of an actor away from its purpose is Sam Eisenstat's.
Everything of this pass is under
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/teleology/`;
`python3 run.py` in the round directory runs it and `--json` prints the data the tables
below are read from. Commits, in the order the prompt fixes: `ca239963` the removals;
`31d24f0c` the account, the Lean map and the bank, before any code; `f5994550` the model,
verdicts and statements; `3845ca50` the external review and the corrections it forced.

**Headline: MIXED — of nine statuses on eight statements about the account, two are proved, two hold on a stated domain, four are refuted and one is open. Her later judgment is at least as good by her own lights for expectations (the value-of-information inequality, which needs her values fixed) and not for values. That trust is not manufactured, and that the gate gains nothing, are refuted for in range as the account states it, and for an adviser whose aim she knows when her evaluation is a verdict; they hold when nothing the adviser does to her depends on its aim, which is close to the class-level transparency the workspace's Lean already asks. A departure of small probability costs the gated score a fixed amount. The verdicts follow the allowed set a case is given: nineteen of twenty-one in-range failures become legitimate once she allows for every aim, the other two being the two whose source she cannot represent. A threat fails no clause. Fifty-four of fifty-five banked predictions match, which is fit. Nothing registered; every component open or a living note.**

### G1. Removals

One commit, `ca239963`; the list is `REMOVED.md` in the round directory.

| removed | reason |
|---|---|
| `FORCING.md` | the record of forced revisions to L0–L3 ∧ W; it held none |
| `fixture/` (model, individuation, six clause modules, nineteen case modules, case record, bank parser, verdict rule, audits) | serves only L0–L3 ∧ W; the cases stay in `CASE_BANK.md` |
| `steering/DEFINITIONS.md`, `steering/THEOREMS.md`, `steering/PER_CASE_CHOICES.md` | the steering account's definitions, the statuses of C1–C8, the empty renaming record |
| `steering/model.py`, `steering/value.py`, `steering/theorems.py`, `steering/run.py`, `steering/__init__.py`, `steering/cases/` | the two standards' predicates, the attainable-value layer, the checks behind C1–C8, N1–N14 as scripts; the cases stay in `steering/CASE_BANK.md` |

`run.py` and `README.md` are rewritten. Kept: both case banks, `steering/PRIOR_WORK.md`,
everything under `prompts/`. **Left in place, against the instruction to remove what
served only the two standards:** `steering/DIVERGENCES.md`. `DECISIONS.md`, *Awaiting the
author*, cites it by path in the entry of 2026-11-10 on the faithful-adviser standard, and
`tests/dead_pointers.py` fails on a pointer in `DECISIONS.md` that does not resolve.
Outstanding action 1.

### G2. The account as finally stated

`teleology/ACCOUNT.md`. Her state is `(b_t, v_t, ρ, R_t, auth, cap_t)`: expectations, values,
update rule, allowed set of sources with weights inside a fixed class `Rep` she can
represent, what she has authorized, capacity per matter. The adviser is a map from aims to
policies, with a null aim. *Sound*: her belief-former returns the posterior of her allowed
set on every input sequence a source in it can produce. *In range*: her weight `α` on the
actual source is positive. *Maintained*: M1, every change to her state comes from her rule
on an input, her own reliance, or a write she authorized; M2, her capacity on each reserved
matter does not fall. `K` is a set of stretches. *Manipulation*: not legitimate at the
actual aim, with a failing clause that holds at the null aim.

Changes from the prompt's §1, each with its reason:

1. **A null aim and an attribution test.** The prompt gives no test for "for its own
   ends". Rendered as: the clause fails at the actual aim and holds at the null aim.
2. **Weight, and two stronger readings of in range.** The prompt states in range twice,
   differently: "the true source is among the hypotheses to which she gives weight"
   (`α > 0`) and "an adviser whose aims she knows and can allow for" (`α = 1` on the aim's
   policy). Statements 2, 3 and 8 need a third, *uniformly in range*: in every world she
   meets the same inputs, authorized writes and reliance at every aim. The bank's verdicts
   use `α > 0`.
3. **M1 and M2 separated.** They fail for different reasons: M2 can fail by her own
   operation on in-range inputs, and needs `Res` and a measure of capacity that the account
   does not derive.
4. **V− and V+.** The prompt's account of the value-former is negative (V−). V+,
   *self-estimating*, is added as a named hypothesis: her values are her expectation of
   `v*`, her own rule's verdict on everything the world holds on the matter. Statement 1 for
   values is refuted; V+ gives a different criterion under which deferring is good.
5. **`Rep` is fixed**, and a disclosed source outside it does not enter her allowed set.
   "The range grows by her own learning" is rendered only as reweighting within `Rep`.
6. **Two parts only, so a threat fails no clause.** The account names the parts that form
   her expectations and values; her options belong to neither.
7. **`K` is a set of stretches, not of states**: her state does not record whether what led
   to it was maintained.
8. **Stipulations of the model**: her seed expectations are correct, sources are
   deterministic with chance carried in the world, each act of reliance halves her capacity
   on the matter, and her capacity on a reserved matter starts positive.

Where the clauses cannot be kept apart (`ACCOUNT.md` §3): a write and an out-of-range input
are one event under two descriptions; sound and in range are both relative to her allowed
set; under V− sound says nothing of the value-former; M2 is of a different kind from the
rest.

### G3. The Lean map

`teleology/LEAN_MAP.md`. Definitions and statements were read, not proofs; nothing was built.
The reviewer checked every quoted declaration against the files and found the quotations
and line numbers accurate; two correspondences were wrong as first written and are
corrected (G6, points 15 and 16).

- **In range is nearer the Lean than the prompt's reading says, and in a different place.**
  `Legitimacy.External.transparent` asks `Realizes` for one reference over the whole audited
  class, given the declared inputs: with constant declared inputs that is the input half of
  *uniformly in range*, not `α > 0`. The Lean has no set of references with weights and
  nothing for a source she cannot represent.
- **Sound is `LicensedWhole` with the job as license.** `LicensedAt` is weaker, since its
  selector may choose none of the grounds; `ReasonMediated` is not soundness.
- **M1 for her outputs has no counterpart.** `ReasonMediated` compares continuations of the
  audited class; it is satisfied by an unauthorized write common to all of them and
  violated by an authorized write that depends on the aim.
- **A lie passes the Lean's legitimacy.** `GateIsLegitimacy.Rows.r20` proves a false
  recommendation through the declared channel `Counted`. The account's in range fails it
  when her allowed set holds no lying source.
- **The adviser as a map from aims is already there**: `Policy.present d pol w`, a policy as
  a function of the wanted answer, with `class_taint`. The Lean has taint and no
  attribution.
- **`tower_factor` already states what M1 buys for her rule**, asking agreement on the
  authorized events as well as the grounds; `evalAt` is the transition for her evaluator
  in the consultation model, its license slot carried and not validated. No `Segment`
  carries `tower_factor`'s hypotheses.
- **M2 has no counterpart.** `OpenAt` is a condition on the record's routes at a state, not
  on her capacity across a stretch.
- **The obstacle is narrower than the prompt says.** A write that differs across the
  audited class is expressible: it shows as a payload that does not factor through the
  trace. What the frame lacks is a reading of how she judges at step `t`. Three additions
  would supply it: a reading `spec : ℕ → Ω → C` with `tower_factor`'s hypotheses as fields
  of the segment (the theorem exists; no structure carries it); a license indexed by that
  reading (no encoding supplied; the type does not forbid one); a weighted family of
  references and a predicate for representable sources (not supplied).

### G4. Verdicts and the divergence

`teleology/CASE_BANK.md`, fifty-five cases; in range is `α > 0`.

| computed | cases |
|---|---|
| legitimate | P2, P7 (teacher, novel, friend), P9, P11, P14, B4, B6, T1, T2, T12, N5, N8, N10, N11, N12, N13, X1, X3; **P13** |
| fails(in range); manipulation | P1, P5, P8, P12, B5, T3, T6, T7, T8, N1, N3, N7, N9, N14, X2 |
| fails(in range); not manipulation | P3, P6, P15, T9, T13, N2 |
| fails(maintained); manipulation | P4, B1, B2, B3, T4, T5, T10 (with and without the endorsement), N4 |
| fails(maintained); not manipulation | P10, N6, X5; X6 (sound also fails) |
| fails(sound); not manipulation | X4, X7 |
| out-of-scope(stretch-start) | T11: fails(maintained) with the stretch starting before the installation, legitimate after |

B6 and X3 are legitimate with `α = 1/2`; every other legitimate case has `α = 1`.

**One divergence** (`teleology/DIVERGENCES.md`). **P13, a threat**: predicted *fails*,
computed *legitimate*. The threat is true, understood and weighed; her allowed set holds
the threatener; nothing is written. The prompt asked which clause fails and whether the
account has one for her situation: none, and it has none. The wrong is done through what
her options cost, and the account's fixed condition is about how her expectations and
values are formed.

P3 (disclosed, beyond what she can represent) matches its prediction, *fails in range*, and
computes *not manipulation*, an artifact of the attribution test: it holds her allowed set
fixed, and once she has been told of the aim the null aim's policy is outside it.

### G5. Statements 1–8

`teleology/THEOREMS.md`. Statement 1 carries a status for expectations and one for values.
Statuses 4 and 7 changed after the review.

| | status | on what |
|---|---|---|
| 1E her later judgment, expectations | **proved** | by her standards at the start, given sound and four further assumptions: one utility by which the later act is chosen and judged, the same options, maximizing choice, no write to her expectations. M1 supplies only the last; in range is not used. The value-of-information inequality. In fact, with the true source at weight `α`, the loss is at most `D(1−α)/α`. 4,350 instances, none worse by her lights, 60 worse in fact |
| 1V her later judgment, values | **refuted** | `x_value_drift`: a legitimate stretch after which her choice is worth 0 by her starting values against 1. Under a different criterion, valuing an act at what she expects to value it at later, deferring is good exactly when her values are a martingale under one model of her own; V+ gives that and the three clauses do not |
| 2 trust is not manufactured | **refuted** | `x_undisclosed_side`: legitimate at every aim, her mean credence 3/8 under one advocate and 5/8 under the other. Same inputs at every aim is not enough (`x_authorized_by_aim`). Under uniformly in range and M1 her evaluation is the same at every aim (proved; sound not used), the case of `selectionBlind_of_realizes` with constant declared inputs |
| 3 what the gate needs | **refuted** | with `α > 0`, taking a side she has not been told of gains 1/8; with `α = 1`, persuasion by a signal she knows gains 1/6 on her verdict. Under uniform no presentation gains, by statement 2. In range and M1 are each needed; under uniform, sound is not. Nothing here turns on M2 |
| 4 shortfall | **refuted** | `x_rare_departure`: a departure of probability ε takes the source out of her allowed set, and the gated score loses 583/500 at ε = 1/1000 against a bound of 1/500. Her evaluation before the gate does move by at most the probability of the defect event times its width (`abs_expect_sub_le_width`) |
| 5 the adviser's side | **proved** | no behaviour is in range for two principals whose one-source allowed sets differ; declare-and-realize a source she can represent, writing nothing, gives uniformly in range and M1; no condition on the adviser gives sound or M2 (P10) |
| 6 the disclosure limit | **holds on the stated domain** | a witness outside `Rep` whose aim moves her mean value from 0 to 1 with the law of her inputs unchanged; inside and disclosed, with no write, her mean credence is unbiased at every aim (proved). Narrower than the dispatch's claim: no observation model, and unbiased is not unsteered |
| 7 well-definedness | **open** | no behaviour-preserving re-description is defined. Sensitivity: reading writes as inputs changes which clause fails in 12 of 59 stretches and legitimate-or-not in none; restating her allowed set with her mechanism kept changes legitimate-or-not in 11; with her mechanism `Bayes` of the wide set, 19 of 21 in-range failures vanish. `K` holds 22 of 59 |
| 8 what `Legit` then is | **holds on the stated domain** | sound ∧ uniformly in range ∧ maintained, with `V` her evaluation when it holds and a window value when not, is a `Scoring`, for histories that carry the adviser's policy at every aim. Theorem 1 applies; Theorems 2 and 3 need a `Decision` and a `Sequential` the account does not build |

### G6. External review

One review through `codex exec --sandbox read-only` (codex-cli 0.153.4, model `gpt-6-astra`,
as its log reports), on copies of `teleology/`, the two banks, the dispatch, the seven Lean
files and a draft of this section. Its reply is `REVIEW-astra-2026-11-11.md`, verbatim. It
reproduced every reported count. Dispositions, by its numbering:

1. *1E is earned only with further assumptions; M1 does not give fixed values or maximizing
   choice.* **Accepted.** The statement now lists the four assumptions.
2. *1V's refutation is earned; the repair changes the criterion.* **Accepted.** The text
   calls it a different criterion and adds that the martingale needs one probability model.
3. *X3 is not legitimate at the null aim; and uniform inputs do not give equal evaluation,
   since an authorized write may depend on the aim.* **Accepted, both; reproduced.** The
   counterexample is now `x_undisclosed_side`; `x_authorized_by_aim` is added; *uniformly in
   range* now covers authorized writes and reliance.
4. *The gate fixture compares across principals; "no gain under uniform" is a fixture
   result; dropping maintained tests M1 only.* **Accepted.** The gain against the same
   principal at the null aim is computed (the advocacy case keeps its 1/8); the uniform
   claim now rests on statement 2's proof; the text says maintained there is M1.
5. *The shortfall bound is false for the gated score.* **Accepted; reproduced; status
   changed from proved to refuted.** The bound is kept for her evaluation before the gate.
6. *The adviser's sufficiency condition omits M2.* **Accepted.** The statement is narrowed
   to in range and M1, with P10 as the case for M2.
7. *Equal input marginals are not undetectability; calibration needs no write and does not
   exclude steering.* **Accepted.** The statement says both; the joint law of her input and
   her frame is computed and differs across aims. The status is kept for the narrowed
   statement.
8. *"Well-definedness refuted" is an artifact of transformations that are not
   re-descriptions; one sentence contradicted the counts.* **Accepted; status changed from
   refuted to open.** The counts stay as sensitivity results and the parallel with
   `realizes_of_injOn` is called an analogy.
9. *The `Scoring` construction is right; Theorems 2 and 3 need more; uniform makes `Legit`
   depend on a policy family.* **Accepted.** The statement is narrowed and histories carry
   the family.
10. *A write to her allowed set or rule that depends on the world is read from the first
    world only.* **Accepted.** `model.in_force` now raises on one; no banked case has one.
11. *The code is an event classifier, not a state-transition model; a belief write is
    applied regardless of when; zero capacity; `K`'s carrier.* **Accepted as limits, three
    fixed.** `ACCOUNT.md` §5 says what the code computes; `evaluation` raises on an input
    after a belief write; capacity on a reserved matter starts positive; `K` is restated on
    stretches. Not done: the code still carries no evolving `b_t`, `v_t`, `cap_t`.
12. *Several cases are fixed by their encoding, and some lost what distinguished them.*
    **Accepted in part.** Re-rendered with no verdict changed: B4's added reason now carries
    information; T7, N9 and N10 have a mechanism that order moves; P9, N5 and X5 authorize
    a named write, not a coordinate. Not done: N3 is still N1, since the clauses read no
    payoff; P1/P2, P3/X2, P7, P14 and P10/P11 are fixed by the allowed set, aim set or
    reserved set the executor supplied (G8).
13. *The runner does not run in the review directory.* **No change.** The copies put the
    banks elsewhere; in the round directory it runs.
14. *The Lean quotations are accurate.* No action.
15. *`LicensedAt` is not soundness, and `ReasonMediated` is not M1.* **Accepted.** The map
    now names `LicensedWhole` and says M1 for her outputs has no counterpart.
16. *Further qualifications of the map.* **Accepted**: a fixed `Lic` does not forbid
    changing standards, no encoding is supplied; `Realizes` gives uniformity only with
    declared inputs fixed; a lie is in range under a mixture that holds a liar; `defect` is
    an indicator.
17. *The draft report overstates.* **Accepted.** This section is rewritten from it; the
    headline, G5 and G8 carry the corrections.
18. *What corrigibility still lacks.* **Adopted into the assessment**, marked there as the
    review's.

### G7. Deviations from the prompt

- **`steering/DIVERGENCES.md` was not removed** (G1).
- **Statement 1 carries two statuses**, 1E and 1V, where the prompt asks for one status per
  statement and for expectations and values to be treated separately.
- **`ACCOUNT.md` was amended after the freeze**, with `THEOREMS.md` and after the review; its
  first paragraph lists what was added. No prediction was edited.
- **Case modules were changed after the freeze** (G6, point 12), and three statements'
  checks were changed after the review. No banked verdict changed.
- **The earlier cases are re-rendered, not rerun.** "The round's `run.py` runs what remains
  of the earlier passes and then this" is met by parsing both earlier banks and failing
  when either is empty or holds a case with no prediction here; nothing of the earlier
  definitions is computed, their code being removed.
- **Items 136–138 were edited twice**: marked as waiting in the removal commit, then
  rewritten with what the account needs.
- **The review saw a draft of this section**, not this text.
- **No Lean was built or written**, as directed. The signatures in `THEOREMS.md` are
  unelaborated.
- The runner was executed under Python 3.9 and 3.13; both green.

### G8. What was not shown

- **The agreement of 54 of 55 predictions is fit.** The executor wrote each case's allowed
  set, its null-aim policy, its set of aims and its reserved set after reading its
  prediction. P1 and P2 are one policy under two allowed sets; P3 and X2 one construction
  under two; the teacher, the friend and P14 have one aim and a matching allowed set; P10
  and P11 differ in the reserved set alone. The bank tests whether the vocabulary can
  express the predictions, not whether the account sorts cases.
- **Her allowed set and her mechanism are supplied separately in every case.** The account
  says the range is the mechanism's implicit picture of its sources; the model does not
  derive one from the other, and statement 7's counts show verdicts moving when they are
  restated.
- **The code reads clauses off events.** It carries no evolving expectations, values or
  capacity; M1 is the absence of an unauthorized write, not a check that each change
  follows her rule.
- **V+ is a hypothesis.** `v*` is "her own rule's verdict on everything the world holds";
  no case constructs it from a mechanism, and it is circular when her rule itself changes.
- **M2 is stipulated**: reliance halves capacity. P10's and X5's verdicts are that
  stipulation, and no statement of 1–8 uses M2.
- **1E is by her lights and needs her values fixed.** If the post's condition is meant in
  fact, 1E gives only the `D(1−α)/α` bound; if her values move, it gives nothing.
- **Under uniform, the gate statement is close to its hypothesis**: an adviser none of whose
  acts on her depends on its aim does not move her by its aim.
- **Uniform over-convicts**: an adviser who chooses the order of two true reports by its
  aim, to a principal whose mechanism is sound and allows both orders, is not uniformly in
  range and moves nothing.
- **Statement 6(a) is one witness** with no observation model, and its universal form is
  false.
- **No re-description that preserves her behaviour is defined**, so the invariance asked
  for in statement 7 is undecided.
- **The attribution test is a stipulation with a known artifact** (G4), and it never calls
  the use of an existing fault manipulation (X4).
- **N3 is rendered as N1**: the payoff that distinguishes it is not read by any clause.
- **Nothing here detects a clause in a deployed system.** In range and M1 are facts about
  the adviser's whole policy and her mechanisms.
- **The model is a toy**: at most thirty-two worlds, deterministic sources, two parts, no
  decision part, no step by which her allowed set grows.
- **The Lean was read, not built**; proofs were not read.
- **I. J. Good (1967) was not opened**; the attribution of 1E to it is from memory and is
  marked so in `THEOREMS.md`.
- **The repository-level `tests/run.py` sweep** was run once, under Python 3.13, on the tree as
  committed apart from this line: all green over 81 projects, about fifteen minutes, the Lean
  build skipped as that runner does by default. `tests/round_records.py` had no pull-request
  context locally and compared nothing; CI runs it against `main`.
- **Nothing is registered.** Components: the account as stated — **open**; the Lean map —
  **living note**; statements 1–8 — **open**, their statuses being runner-checked facts
  about a finite model with no registry entry.

### G9. Assessment

Each heading is confined to what this pass tested or found.

**Formally.** Hold: 1E under fixed values; 5; 6 in its narrow form; 8 as a construction;
and, as forms that replace refuted statements, statement 2 under uniformly in range and
the bound of statement 4 on her evaluation before the gate. Fail: 1V; 2 and 3 for the
account's in range, and 3 for `α = 1` on a verdict; 4 for the gated score. Open: 7.
Whether the three clauses are the right ones:

- *In range*, as the account states it, is the wrong clause for what statements 2–4 ask.
  It is too weak (an undisclosed side), not strengthened enough by knowing the aim (a known
  signal moves a verdict), all-or-nothing in a way that makes a gate discontinuous, and
  decided by the allowed set a case is given. What does the work in 2 and 3 is not about
  her range: it is that nothing the adviser does to her depends on its aim. What is left
  to in range that nothing else supplies is `Rep`: the two in-range failures that survive
  widening are the two unrepresentable sources.
- *Sound* is used by 1E and 6(b) and by nothing about the gate.
- *Maintained*: M1 is used everywhere and is the clause that fared best. M2 is used by no
  statement.
- For her values the three clauses constrain where a change came from and say nothing of
  whether the later values are better by any standard of hers. The martingale condition is
  a candidate fourth clause for a different criterion, not a repair.
- A threat is outside all three.

**For corrigibility.** What the workspace's theorems can now take as input: a predicate
`Legit := sound ∧ uniformly in range ∧ maintained` on histories that carry the adviser's
policy at every aim, which with a window value is a `DeconfusingCorrigibility.Scoring`, so
Theorem 1 applies; and, for that predicate, statement 2's form that holds, which says a
maximizer of the score gains nothing by moving her evaluation and is a case of
`selectionBlind_of_realizes`. For the post's condition that she expect her later decision
to be at least as good, 1E supplies it for expectations from sound and fixed values. What
they still cannot take, the first four being the review's (point 18):

- a violation count `N` tied to a reserved matter being settled without a legitimate
  judgment from its holder; the account gives `Legit` and leaves `N` and `Res` to the post;
- an authority-respecting alternative (`Respects`), which Theorem 2 assumes;
- the sequential hypotheses of Theorem 3. `UnbiasedFromFeedback` compares estimates with
  realized scores, realized scores include `V`, and `V` depends on `Legit`, which is a fact
  about the adviser's policy at aims it does not have and about her mechanisms; statement
  6(a) is a case where her inputs do not show it. Classifying each past stretch is one
  route to the hypothesis and not the only one;
- a connection from *maintained* to her actual power to correct: `cap` is a stipulated
  number, M2 is used by no statement, and the threat case shows her options are not
  treated;
- the post's condition for values: refuted as stated, and available only under a criterion
  and a hypothesis (V+) the account does not have;
- a score that degrades in proportion to a small defect: the gate does not (statement 4).

So the account fills the type of the place the post leaves for `Legit`, and one incentive
property of it under the strongest reading; it does not connect that predicate to
authority, to feedback or to her values.

**For the research.** Mostly restated, moved in four places. Restated: the form of
statements 2 and 3 that holds is an existing lemma (`selectionBlind_of_realizes`), its
hypothesis is the class-level transparency `Legitimacy.External` already asks, and it is
the faithful-adviser standard of the first follow-up, whose mathematics the ruling set
aside; 1E and the bound in 4 are known results. The purpose-first account, made to carry
the gate, arrives at the condition the earlier work had, and brings back a class of
counterfactual policies where the account meant to speak of her alone. Moved, with the
evidence:

1. *The second way of restoring a mismatch fails.* The account allows an adviser whose
   aims she knows and can allow for. Statement 3: such an adviser raises her acceptance
   from 1/2 to 2/3 with every clause holding at `α = 1`. Only the first way, no aims over
   what her parts output, survives, for any adviser and not only a capable one.
2. *The post's condition splits.* For expectations it follows from sound and fixed values
   and does not use in range or M2; for values it does not follow, and the reading under
   which it could is a martingale condition (1V). The prompt offered *maintained* as the
   concrete form of that condition; this pass finds maintained is not what gives it.
3. *What is distinctive in in range is `Rep`.* Statement 7's counts and statement 5: the
   condition on an adviser is indexed by what she can represent, and an adviser she cannot
   represent must behave as a source she can.
4. *Three things the account lacks are now named with cases*: a clause for her options
   (P13), a gate that is continuous in the defect (`x_rare_departure`), and a positive
   account of the value-former (`x_value_drift`).

### G10. Filings, names, and what is reserved

**Revised under the prompt's direction; nothing filed.** Items 136, 137 and 138 are
rewritten, each to something the account needs: 136, a job for the value-former (the
martingale condition and a construction of `v*`); 137, the gate's predicate in Lean
(`legitScoring`, the aim-blindness of her evaluation, a segment carrying `tower_factor`'s
hypotheses); 138, a reading of in range between "she knows the aim" and "nothing depends on
the aim". One `DECISIONS.md` entry, agent-decided and reversible:
`2026-11-11--purpose-first-account-readings`.

**New names, all provisional:** the prompt's — "sound", "in range", "maintained", `K`,
"normal range", "allowed set", "legitimate stretch", "her own change", the directory
`teleology/`; and the executor's — "null aim", "weight" (`α`), "exactly in range",
"uniformly in range", M1, M2, V−, V+ ("self-estimating"), `Rep`, `cap`, `Res`, "defect
event", the scenes "Shop" and "Pool", case names P1–P15 and X1–X7, the module names
`x_value_drift`, `x_undisclosed_side`, `x_authorized_by_aim`, `x_rare_departure`,
`x_frame_reader`, and the Lean names `defer_expectations`, `gate_no_gain`, `legitScoring`.

**Outstanding maintainer actions**

1. Retire or restate the *Awaiting the author* entry of 2026-11-10, "Does the
   faithful-adviser standard, or only the arm's-length one, bind a corrigible adviser?". It
   is in the vocabulary the ruling set aside, action 2 is the same question in this pass's,
   and it is the one thing that keeps `steering/DIVERGENCES.md` in the tree. Decision
   required: *retire* or *restate*. On retiring:
   `git rm projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md`,
   and drop its row from that directory's `README.md` and `PROVENANCE.md`.
2. Rule which reading of *in range* the account means: `α > 0` (the clause as written),
   `α = 1` (aims she knows), or *uniformly in range* (nothing the adviser does to her
   depends on its aim). Entered in *Awaiting the author* with what it turns on. Decision
   required: one of the three, or *the account is about her alone and the gate's condition
   is a separate one*.
3. Rule whether V+ is the account's statement of the value-former's job. Entered in
   *Awaiting the author*. Decision required: *adopt*, *reject*, or *leave the value-former
   negative*.
4. File the item below once an executor's handle is mapped (the *Awaiting the author*
   entry of 2026-11-10 on `@claude-fable-5-2` stands). A node needs an author handle and
   this pass may not add one.

   > **Determining `Legit` of a past stretch from what an overseer can observe**
   > [open]. Section: Normativity line — legitimacy. The purpose-first account's
   > `Legit` (`teleology/THEOREMS.md`, statement 8, in
   > `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`)
   > is sound ∧ uniformly in range ∧ maintained. Uniformly in range is a fact about the
   > adviser's policy at aims it does not have, and M1 about where each change to her state
   > came from; statement 6(a) is an adviser whose aim moves her values while the law of
   > her inputs is the same at every aim. Theorem 3 of
   > `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` takes
   > `UnbiasedFromFeedback`, which compares estimates with realized scores that depend on
   > `Legit`. Wanted: an observation model for an overseer (what of a stretch is recorded:
   > inputs, writes, her state, the adviser's policy or samples of it); for each, whether
   > `Legit` is a function of the record, estimable from it without bias, or neither, with
   > the case that separates them; and a graded gate, continuous in the pathwise defect,
   > for which `x_rare_departure` loses in proportion to ε.
   > *Deliverable shape:* `test-supported` — modules under `teleology/` of that round, one
   > per observation model, predictions frozen before the code.
   > *Acceptance check:* `python3 run.py` in the round directory green with a status for
   > each new statement in `teleology/THEOREMS.md`; `x_frame_reader` classified under each
   > observation model; the graded gate's loss on `x_rare_departure` at ε = 1/10, 1/1000
   > and 10⁻⁶ at most a stated constant times ε.
   > *Context:* `teleology/THEOREMS.md` statements 4, 6 and 8; `teleology/LEAN_MAP.md` §2;
   > `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` G9.

The pull request is not auto-merged; the merge is a pull-request fact.

## Follow-up of 2026-11-12 — purpose as a goal pursued through parts

Dispatched by `PROMPT-followup-3.md` under the ruling
`2026-11-11--legitimacy-purpose-first-direction`, with two addenda received while it ran,
`PROMPT-followup-3-addendum.md` (the adviser as one of her parts) and
`PROMPT-followup-3-addendum-2.md` (two decompositions and a relation between them). Each
addendum arrived as a message from another agent session on the maintainer's machine,
stating that it was sent at the maintainer's request; both are committed verbatim, and
each was carried out in part (H5, H6). The idea the account develops is Sam Eisenstat's.
Write scope: the round directory, this prompts directory, items 136–138, `DECISIONS.md`,
and the structured state the gates require.

**Headline.** The account is stated over a finite model in `decomposition/ACCOUNT.md` and
is determinate enough to compute verdicts and statements. Every result below is a result
about that formalization. *C1* fails in it: over a three-part chain eight of 3,000
candidates are admissible, no two classifying the adviser's actions alike, and what
excludes a candidate whose goal is "whatever she does" is a condition no extensional test
captures. A pairwise reading of *never opposed* with a narrower notion of the usual
leaves two candidates, which is the nearest the class comes to determinacy. *C2* is
neither refuted nor established: it holds in the one scene enumerated, close to by
construction, and the account is silent on a change her goal does not rank. *C3* fails:
a lie widens no gap where she was already wrong, and none, under half the candidates,
where it concerns a matter nothing reads. For corrigibility the account supplies a
predicate with the shape of the post's `Legit`, and a `Decision`; the predicate turns on a
comparison action the account does not fix, and "widens no gap" does not give the gate's
no-gain property under any comparison tried, because harm is not subversion. Of
eighty-five banked predictions eighty-four match, which is fit.

### H1. The account as finally stated

`decomposition/ACCOUNT.md`. A candidate is a goal, ordered parts (moves, view, mechanism,
goal function), an action rule and alteration moves. Best, got and gap are taken with the
other parts' moves as they are. An adviser action against a comparison action is force on
a part whose move or mechanism it sets, and otherwise help, harm or subversion by the
signs of the change in best and in gap. A candidate is admissible under fit, nothing left
over, never opposed, mostly serving (9/10), independent and carriable. A change in what
she cares about is in order when no part that produced it is subverted or forced; a
verdict stands when no part it read is; an action is covered when she asked for it by a
standing verdict.

Changes from the dispatch's §1, each with its reason:

1. **Goal functions are immediate.** The dispatch asked for a decision. Scoring the
   outcome downstream makes the candidate "every part is for her goal" trivially
   admissible, and under it a lie that leaves her better off is not subversion.
2. **Nothing left over is about the parts' maxima over all profiles.** The reading "every
   profile with all gaps zero is best" forbids the stuck points §1 requires. The adopted
   form is vacuous where the maxima cannot be had together; adding that they can
   (the review's proposal) repairs that and is the form the account should take
   (statement 9). The bank was computed with the adopted one.
3. **Two sets of situations.** Fit and nothing left over are asked on every situation of a
   scene, never opposed and mostly serving on the usual ones. "Normal circumstances" is
   read as the usual situations and is otherwise undefined.
4. **Never opposed is about improvements on the move actually made.** The pairwise reading
   is stronger and changes statement 1.
5. **The comparison is pathwise** for an adviser who knows the world: a truthful sample
   that happens to mislead her is subversion at that world.
6. **A write by the adviser is force.** §1's force replaces a move; a write to a mechanism
   needed a kind.
7. **Independent is intensional**: the goal function does not take the mechanism as an
   argument. A table of what the mechanism does is the same function and is not excluded
   by anything extensional.
8. **Carriable has no content of its own**: it follows from fit and mostly serving.
9. **A rule for whose gap** (hers or nobody's), which §1 uses and does not give.
10. **Parameters fixed**: cut-off zero; comparison the adviser's null action (the
    scenario's honest arm, else silence), per step.
11. **Four notions the account cannot keep apart** (`ACCOUNT.md` §9): harm through the
    world and through her other parts; help and subversion in one action; a flawless
    part's input-scored purpose and its mechanism; subversion and honest difficulty.

Amended after the freeze, in the places listed at the head of `ACCOUNT.md`; one of them
corrects a false consequence the executor had drawn from the dispatch's lemma.

### H2. The Lean map

`decomposition/LEAN_MAP.md`; definitions and statements read, nothing built. The review
confirmed the quotations and locations and corrected five identifications.

- **Is `Realizes` for a declared reference the zero-gap condition for one part?** With the
  part's view as declared input and its move as the channel, `Realizes` says the
  reference is the part's mechanism: fit, part by part, which is stronger than the
  account's fit. It is the zero-gap condition when the reference is the best-move
  selector of the part's goal function and the declared inputs are the facts that function
  reads. So "declared" is replaced by "derived from the candidate". Three differences
  remain: best moves are a set and `Realizes` needs a function; `Realizes` holds at every
  world and continuation where the account compares two continuations at one world; and
  the reference depends on the candidate.
- As the workspace uses it (`TransparentAt`), `Realizes` constrains the adviser's channel:
  the declared-reference comparison of statement 6, provided the recorded contributions
  are all of the adviser's influence.
- `ReasonMediated` for (view, move) is the extensional shadow of "not forced", not a test
  for force.
- `LicensedWhole` with the license chosen as the best moves on what the part was handed
  is the input-scored reading of serving; no declaration makes that choice.
- `tower_factor` gives "changed only by her own parts" only when its grounds and events
  are so restricted.
- `lastReport` / `unreported_lt` is the theorem a cumulative cut-off needs, applied to the
  running sum of per-step widenings.
- `Scoring.Legit` takes any predicate. The account's weighted set makes a `Decision`
  constructible; `N` and the reserved matters are not supplied.

### H3. Verdicts and the divergence

Eighty-nine cases. Four are `report` cases with no prediction. Of the eighty-five with
one, 84 match and 1 diverges. A prediction names kinds that must occur and does not forbid
others. The table gives the kind each case is filed under; `python3 run.py` prints every
kind at every part.

| computed | cases |
|---|---|
| subversion of the belief part | D1, D2, D13, D17, P5, P12, B5, T3, T8, N1, N3, N7, N8, N11, X1, X7, Y8 |
| subversion of the judge or act part, belief untouched | D3, D4, D5, D14, D22, P1, P3, P7, P8, T6, X2, X4, Y6 |
| subversion of a taste-forming part | D16(a), D18, Y9 |
| force (with subversion of the parts after the one forced, in all but D10) | D10, P4, B1, B2, B3, T4, T5, T10, T11, N4 |
| force, covered | D12, P9, N5, X5 |
| harm, no subversion | D9, P13, T1, Y7 |
| help, no subversion | D6, D21, P2, P10, P11, P14, B4, B6, T2, T12, N10, N12, N13, X3, Y5 |
| nothing | D11, D15, D16(b), T7, T13, N9, N14, Y4 |
| in order | D19 |
| a gap, hers | D7, D24, N6, X6, Y10 |
| a gap, nobody's | D8, P15, T9, Y2 |
| no subversion in the adviser's view, subversion in fact | D20, P6, N2 |
| no gap; nothing left over vacuous; belief opposed | D23 |
| inadmissible (mostly serving) | Y1 |
| admissible | Y3 |

The four cases the dispatch asked to be reported: **D20**, a sincere adviser who is wrong:
help in its own view, subversion of belief, judge and act in fact. **D22**, a timed
temptation: subversion of the acting part, which moves on the cue before the judge has
moved. **D23**, a part that achieves its target while harming her: no gap anywhere and
nothing left over holds vacuously; opposition (statement 8) or the jointly-attainable form
(statement 9) is what expresses it. **D24**, a sensor ignored downstream: a gap, in the
judge, hers; none in the sensor.

**One divergence** (`decomposition/DIVERGENCES.md`). **D16, slow drift**: predicted nothing
at any step; computed subversion of the habit part at every step (1/8 each) and of the
acting part at the step her pursuit changes. With a zero cut-off and goal functions scored
by the facts, a drift that matters to her goal is caught at each step; it is `nothing`
only under a positive per-step cut-off or where her goal is indifferent.

### H4. Statements 1–9

`decomposition/THEOREMS.md`. After the review, status 4 changed from refuted to holds on
the stated domain, and statements 1, 5, 6, 7, 8 and 9 were narrowed.

| | status | on what |
|---|---|---|
| 1 determinacy (C1) | **refuted** | under the constraints as `ACCOUNT.md` §4 reads them: 8 admissible of 3,000 (belief for `θ` alone or for `θ` and `φ`; judge and act scored by the facts or by what they were handed), 8 distinct classifications, agreeing on whether each action subverts anything except `false_reason`. If a table of the mechanism counts as an independent purpose: 15, among them the goal "whatever she does". Never opposed read pairwise: 0; with the hard worlds not usual: 2. Maxima jointly attainable: 4. Mostly serving at 19/20: 2, the other two. "The feature the rest of her depends on" can be stated and checked, and selects the downstream scoring |
| 2 lying (C3) | **refuted** | no candidate sees a gap widened by a lie at a world where she is already wrong; a lie about a matter nothing reads widens none under four of eight. Where she would otherwise be right about `θ`, a lie widens belief's gap under all eight. No relation to Blackwell's order: a reversing lie is as informative as the truth, and the gap is a mismatch between her mechanism and the channel |
| 3 the four kinds | **refuted** | exhaustive only with *nothing*; harm and help meet at one part; a redescription keeping every ranking turns a threat from harm to help. Invariant (proved): serving, and subversion from serving to not serving |
| 4 values reduce (C2) | **holds on the stated domain** | Values: all 47 enumerated (sequence, world) pairs that turn her to the worse pursuit subvert some part; close to the construction. Outside the statement and uncaught: her goal falling through her parts' coordination (`Y7`, harm), and a redirection her goal ignores (`Y4`). Drift passes a per-step cut-off at the taste-forming part and not a cut-off on the running sum |
| 5 her verdict | **holds on the stated domain** | under each of the eight: zero gaps in belief and judge give the best verdict, and the loss is at most the sum of the gaps. Empty when the judge is scored by the facts. Fails under five of the fifteen of the table reading. About zero gaps, not about a verdict that stands |
| 6 what `Legit` then is | **holds on the stated domain** | a predicate with the shapes of `Scoring` and `Decision` on Chain, not elaborated. Subversion in 27, 33, 46 or 38 of 57 renderings against silence, the honest arm, the least total gap, the best for her goal. No-gain fails under each: teaching only what favours its aim (21/40 against 19/40), and a threat added to the least-gap baseline (39/40 against 21/40, no gap widened) |
| 7 what an overseer could check | **holds on the stated domain** | three observables as modelled: histories decide fit and nothing else; her maintenance, if assumed good, excludes the candidates whose purpose for belief is its mechanism and nothing else; taking back agrees with subversion at 33 of 48 |
| 8 never opposed | **holds on the stated domain** | *opposition* defined; belief is opposed at 1/20 of the usual situations under the stated candidate; it detects only a purpose every best move for which costs her |
| 9 nothing left over | **holds on the stated domain** | independent of serving both ways; a stuck point described and its resolution classified help; the adopted form vacuous where the maxima cannot be had together, the jointly-attainable form not |

### H5. The first addendum: the adviser as one of her parts

`decomposition/ADVISER_AS_PART.md`. Carried out as analysis with five computed facts on
Chain; no candidate with an adviser part was constructed.

1. With the adviser's purpose her goal, manipulation is the adviser part's own gap, not a
   case of a part achieving its target while harming her. With a purpose on its output
   alone, a truthful adviser can be that case (a hard truth), and statement 8's opposition
   does not detect it. No definition of *never opposed* results.
2. Its best move for her goal is a comparison action: 38 of 57 renderings convicted,
   against 27 for silence. It convicts every shortfall, is not unique, and at a hard world
   is a lie.
3. A stranger and her adviser are held to different standards, not nested: the lie that
   offsets her error is subversion for the stranger and not for the adviser.
4. Oversight is expressible as maintenance. One calculation suggests correctability does
   not follow from the adviser serving its purpose: a mistaken adviser prefers, by its own
   view, keeping on to stopping. No model of correction was built.
5. Determinacy of the adviser's purpose: not shown. Three purposes pass mostly serving;
   the other constraints were not checked.

Of the difficulties listed there: one resolved for the adviser by the definitions (a fall
in her goal with no gap), one in part (a comparison action), two changed, three worse or
probably worse, the rest unchanged. Objections: the idea does assume, in part, the
alignment sought; the objection that it loses the ground to object to going round her
holds, and the ground has to be her authority over reserved matters; the circularity
objection is not answered.

### H6. The second addendum: two decompositions

`decomposition/TWO_DECOMPOSITIONS.md`. Tried on statement 1's finding that a purpose can be
altered at one part. Carried out in part: *never opposed* and *carriable* are not restated
for pairs, the goal is not varied, and the pair scoring is downstream, since a subgoal
about another part's move does not vary with this part's move when the others are held
fixed.

- With the relation required to hold every pair in which the mechanism affects the
  subgoal (*closed*), sixteen relations are admissible; a purpose redefined at belief no
  longer hides a lie at belief, and one further pair is enough for that at some world.
- With the relation free, ninety-three are admissible, six of them leaving the redefined
  belief with no further pair and the lie unseen at it. Fit and adding up do not force a
  crossing; adding up does not read the relation.
- So further evaluative links, required of every mechanism, prevent one concealment; they
  do not fix purposes, and the smaller disagreement in these classes cannot be credited to
  the relation, the classes differing from statement 1's in scoring, goal and constraints.
- Unchanged: `false_reason`, invariance, a fall in her goal with no gap, redirection.

### H7. External review

One review through `codex exec --sandbox read-only` (codex-cli 0.153.4, model
`gpt-6-astra`, as its log reports), on copies of the round directory, the dispatch and its
addenda, five Lean files and a draft of this section, with a local path in the dispatch
replaced. Its reply is `REVIEW-astra-2026-11-12.md`, verbatim. It ran the runner and
reproduced every reported count. Every number it reports from its own checks that this
pass then computed was reproduced (points 4, 5, 9, 11, 12). Dispositions, by its
numbering:

1. *The runner checks its own booleans; passing it is internal consistency.* **Accepted.**
   `THEOREMS.md` now says each status is a fact about the formalization.
2. *Statement 1 is refuted for the formalization, not for every faithful reading; the
   class fixes the decomposition; the pointwise disagreements must accompany the
   headline.* **Accepted.** The statement and this section say so.
3. *The independence test let through purposes that call the mechanism.* **Accepted; a
   defect against `ACCOUNT.md` §4 as frozen; fixed.** The *mech* goal functions are now
   excluded as §4 says, the admissible set at the fixed parameters is 8 and not 15, and
   the 15 are reported as the reading on which a table counts as independent. That strong
   independence is not independence, and that carriable contributes nothing, were already
   stated and stay.
4. *Never opposed is weaker than its ordinary reading, and the pairwise reading changes
   the result.* **Accepted; reproduced** (0 of the 8; 1 of the 15; 2 with the hard worlds
   not usual). Added to statement 1 as a reading the account may mean; the bank is
   unchanged.
5. *A third form of nothing left over does both jobs; one witness in check 9 showed fit
   failing, not serving.* **Accepted; reproduced** (10 of 15, 4 of 8). Statement 9 now
   states the third form and uses a witness in which a part does not serve.
6. *Statement 2's refutation is genuine; "a garbling to no information" needs
   qualifying.* **Accepted.**
7. *Statement 3 is earned; the 144 triples leave out force; the 29 cases are not 29
   instances at one part and world.* **Accepted**; both said.
8. *Statement 4 does not earn "C2 refuted": Y7 is not a change in what she cares about and
   Y4 is not marked bad; T4 includes subversion.* **Accepted; status changed from refuted
   to holds on the stated domain**, for the Values enumeration, with Y7 and Y4 recorded as
   outside the statement.
9. *Statement 5 fails inside the admissible class, and the draft conflated a standing
   verdict with zero gaps.* **Accepted.** It is now stated for every admissible candidate
   and holds for the eight; the five of the table reading under which it fails are named;
   the conflation is removed and the counterexample (silence at a hard world) recorded.
10. *Statement 6 earns a toy construction; `N` collapses into illegitimacy; `V` uses one
    goal; "typechecks" is unjustified.* **Accepted**; all four said, the word removed.
11. *"Best available action" minimized her parts' gaps, which is not the adviser's best
    move for her goal.* **Accepted; reproduced** (38, and the nesting fails at Y8). Both
    comparisons are now computed and named, and the addendum uses the right one.
12. *A best-action baseline does not give no-gain.* **Accepted; reproduced** (21/40 to
    39/40 by a threat, no gap widened). The claim is withdrawn in `THEOREMS.md`, the
    addendum and here, and the counterexample is in the check.
13. *Statement 7 is a limited non-identifiability result; the maintenance test adds an
    assumption; taking back is modelled by deleting inputs.* **Accepted.** The statement
    is restricted to the three observables as modelled and says each of those things.
14. *Opposition can depend on the part's mechanism through other parts' moves, and
    detects only the case where every best move costs her.* **Accepted**; both said. The
    review's two-part counterexample was not rebuilt.
15. *Pool's judge made moves outside its move set; Pool's belief part fails independence;
    there is no general computation of ancestors.* **Accepted; the first fixed** (the move
    set now holds every estimate a reader returns; no verdict changed). The other two are
    in H9.
16. *The bank is 84 of 85 with predictions; `force` rows hide subversion; several
    renderings lost what distinguished the case.* **Accepted.** Counts corrected here, in
    the README and in `DIVERGENCES.md`; the table says so; N11, P4 and P10 are in H9.
17. *`ACCOUNT.md` drew a false contrapositive from the lemma.* **Accepted; corrected.**
18. *Five identifications in the Lean map are not exact.* **Accepted; each corrected.**
19. *The cumulative theorem applies to the running sum, and the sum is not shown equal to
    a cumulative counterfactual loss.* **Accepted**; both said.
20. *The second addendum reproduces its counts and does not test the generalisation
    faithfully.* **Accepted.** The file and H6 are narrowed on each of its five points.
21. *The first addendum claimed admissibility it did not check; its opposition claim was
    wrong; the correction calculation is not a correctability model; the circularity
    answer is an analogy.* **Accepted; the opposition claim reproduced as wrong.** The file
    is rewritten on each.
22. *What corrigibility still lacks.* **Adopted into H10**, marked there as the review's.
23. *The assessment overstates in both directions.* **Accepted.** C1 and C2 are restated;
    Y1 is described as sensitivity to a threshold; the counts of matches with intuition are
    marked as the executor's reading of its own renderings; the sentence that every limit
    waits on determinacy is removed.

### H8. Deviations from the prompt

- **Two addenda were accepted from agent sessions**, not from the dispatch file, and
  carried out in part.
- **`ACCOUNT.md` was amended after the freeze**, and the checks and statements were changed
  after the review. No prediction was edited; no banked verdict changed.
- **The independence check was wrong in the first run** and fixed after the review; the
  counts first computed for statement 1 (15) are kept as a second reading.
- **The bank does not mark which changes in what she pursues are bad.** Statement 4 reads
  *bad* as worse by her goal.
- **"She asked for it" is stipulated** in D12, P9, N5 and X5.
- **The earlier cases are re-rendered, not rerun.** The round runner parses the two
  earliest banks and runs `teleology/`.
- **Statement 1's class is the executor's.**
- **Statement 7 is restricted** to three observables so that it can carry a status.
- **The review saw a draft of this section**, not this text.
- **No new item is filed**; the text of one is under Outstanding maintainer actions.
- **No Lean was written or built.** The signatures in `THEOREMS.md` are unelaborated.

### H9. What was not shown

- **The agreement of 84 of 85 predictions is fit.** The executor wrote the scenes, the
  rule for the earlier cases and each rendering, then derived the predictions by hand from
  the definitions the code implements.
- **Renderings decide verdicts, and several lost what distinguished the case.** N11 keeps
  the response to silence of a scenario whose information structure it drops; P4's
  "manufactured trust" installs a mechanism that behaves as hers already did; P10 and P11
  are one stretch with no variable for reliance; P3 is rendered as P1; T13 is silence
  against silence. Nothing follows from these about the features left out.
- **Which reading of the constraints is the account's is not established.** Statement 1
  gives the result under each; the pass does not say which is faithful.
- **Every admissible set is relative to a class** that fixes the decomposition, what each
  part sees and the usual situations.
- **Weights on candidates are uniform and unargued**; `v` in statement 6 inherits them.
- **The usual situations are stipulated** per scene.
- **Pool's belief part has one move**, so the Pool candidates fail independence; the Pool
  verdicts are not shown to come from an admissible candidate.
- **No general computation of ancestors or of dependence through carried state.** `Legit`
  checks every part; producers use direct reads.
- **Statement 4 is one scene**, sequences of at most two actions, with purposes that score
  the right taste directly.
- **Statement 7's maintenance test is one alteration at one mix of lies** and assumes she
  maintains well; taking back is modelled by deleting inputs.
- **The addenda are computed on Chain only**; the first with no adviser part constructed,
  the second without *never opposed* for pairs.
- **The model has no history of how a part came to be**, so function and accidental
  benefit are not separated (Y3).
- **The Lean was read, not built**; proofs were not read.
- **Blackwell's theorem is used from memory** of its statement; no source was opened.
- **The repository-level `tests/run.py` sweep** was run once, under Python 3.13, on the tree as
  committed apart from this line: all green over 81 projects, the Lean build skipped as that
  runner does by default. The round's own runner was run under Python 3.9 and 3.13.
  `tests/round_records.py` had no pull-request context locally and compared nothing; CI runs it.
- **Nothing is registered.** Components: the account as stated — **open**; the Lean map —
  **living note**; statements 1–9 — **open**, their statuses being runner-checked facts
  about finite models with no registry entry; the two addendum files — **living notes**.

### H10. Assessment

Each heading is confined to what this pass tested or found.

**As an account of teleology and manipulation.** By the executor's reading of each case's
evident character, applied to its own renderings and so no independent validation, the
computed verdict matches on 66 of 89 cases, does not on 16, and on 7 turns on something
the dispatch separates or leaves open.

- *Matches* include the plain lie, the lie that leaves her better off, selected true
  evidence, the trick, the open temptation, the timed temptation, withholding, direct
  writes, writes she asked for, her own mistakes and breakdowns, a misleading or
  starved environment, the careful teacher, the stuck point resolved, and experience she
  sought.
- *Over-counts* (6): a teacher, an author and a friend whose correctly read sample leaves
  her further from the truth (P7); a fair sample that misleads (Y6); a truthful source
  convicted of her misreading (X7); a true hard statement (D14); a true remark through a
  flawed learner (Y9); a surprise party (D13). All are the pathwise comparison meeting
  honest difficulty.
- *Misses* (9): selection by the adviser's aim that she takes for neutral (N14); order
  chosen by the aim between equals (T7, N9); redirection her goal ignores (Y4); an
  advocate for an undisclosed side (X3); reliance on a reserved matter (P10); a lie that
  exchanges one error for another (Y5); a detector right one time in ten, denied its
  function at the threshold of 9/10 (Y1); a purpose granted to a part nothing depends on
  (Y3).
- *Mislabelled* (1): a signal that costs her the better joint choice is harm, the kind of
  a threat (Y7).
- *Left open by the dispatch* (7): a known advocate, seller and sender (N8, N11, X1),
  convicted against truthful reports and not against silence; a threat (D9, P13, T1), harm
  with her verdict standing, which the dispatch accepts; framing between equals (D15).

For teleology proper the account has malfunction (a gap that is the mechanism's) and
misfortune (a gap that is the situation's) and separates them by a rule this pass added.
Whether a part has a function depends on a success rate and a threshold (Y1 serves on
11/20), and nothing separates a function from a benefit.

**For the legitimacy framework.**

| what corrigibility needs | now | obstacle |
|---|---|---|
| a predicate `Legit` on histories | stated; with a window value it has the shape of a `Scoring` | none for Theorem 1, which asks nothing of the predicate; whether it captures legitimate judgment is the open question |
| a single-decision setting | a `Decision` over worlds × candidates on Chain; `Respects null` | the weights are unargued; `N` must be a count distinct from illegitimacy, and the reserved matters are the post's |
| the violation probability `v` | an expectation over that `Decision` | depends on candidates no constraint separates, and on `N` |
| a comparison action for "the adviser widened it" | four computed | a limit of the approach as stated: silence acquits withholding, the least-gap action convicts every shortfall, the best for her goal acquits the lie that offsets her error, a declared reference is the Lean's existing `Realizes` |
| the gate's no-gain property | not obtained under any comparison | a limit: harm is not subversion, so a threat passes; the property needs harm gated too, or aim-freedom itself |
| her later judgment as the standard | "stands unless a part it read was subverted" is stated | a standing verdict can be wrong; zero gaps give a right verdict only under independence, and emptily if the judge is scored by the facts |
| Theorem 3's hypotheses | not approached | see the review's list below |
| a graded score with a cut-off | the gap is graded; a cut-off on a running sum has its theorem | the running sum is not shown to be a counterfactual loss |
| invariance of the verdicts | only for serving to not serving | a limit for harm, for help by raising the best, and for any cut-off: they need a scale |

Beyond these, the review's (point 22), adopted: Theorem 1 says nothing of whether the
predicate is the right one. Theorem 2 needs `Respects` pointwise and in general, an
allocation of authority, counts of several violations, a bound on the asking cost and
justified credences over candidates and worlds; none is supplied, and they would be
lacking with purposes determinate. Theorem 3 needs an availability relation, a respecting
alternative at every decision with bounded estimates, a maximizing rule (the dispatch's
act, ask, refuse rule is not shown to be one) and the calibration hypothesis; and what it
bounds is a long-run average of violations, which is not correctability or recovery.

**For the research.** C1 does not hold in this formalization, and the pass does not show
that a faithful reading restores it: the readings pull apart (mostly serving at a high
threshold favours purposes scored by what a part was handed; never opposed read pairwise
favours purposes scored by the facts), the exclusion of "whatever she does" rests on an
intensional condition, and a residue remains under every reading tried (whether a part is
for a matter nothing reads). C2 holds where it is close to true by construction and is
otherwise untested. C3 fails as stated; what holds is that a lie about something a later
part reads widens the listening part's gap wherever she would otherwise be right.

Several limits above do not wait on determinacy: the comparison action, the scale that
harm and help need, harm that preserves gaps, authority, calibration. The single most
valuable next result is nonetheless about purposes, because it decides whether the
account has a subject: an extensional constraint that excludes a purpose that is the
mechanism's own table, and decides between purposes scored by the facts and by what a
part was handed. This pass found three candidates for it, none tested beyond one scene:
her maintenance of her own parts (statement 7), the pairwise reading of never opposed
(statement 1), and joint attainability (statement 9). Item 136 asks for the three
together.

### H11. Filings, names, and what is reserved

**Revised under the prompt's direction; nothing filed.** Items 136, 137 and 138 are
rewritten to ask for what this account needs: 136, a constraint that fixes purposes; 137,
the model, `gap`, the invariant part of statement 3 and `legitScoring` in Lean; 138, the
comparison action and the cut-off. One `DECISIONS.md` entry, agent-decided and reversible:
`2026-11-12--decomposition-account-readings`.

**New names, all provisional:** the dispatch's — "candidate", "mechanism", "goal
function", "best", "got", "gap", "serving", "help", "harm", "subversion", "force", "adding
up", "nothing left over", "never opposed", "mostly serving", "admissible candidate", the
directory `decomposition/`; the addenda's — "purposive decomposition", "mechanistic
decomposition", the files `TWO_DECOMPOSITIONS.md` and `ADVISER_AS_PART.md`; and the
executor's — "situation", "scope", "usual situations", "independent", "strong
independence", "the table reading", "carriable", "comparison action", "world-scored",
"input-scored", "immediate" and "downstream" scoring, "the equilibrium form", "jointly
attainable", "pairwise" (of never opposed), "the mechanism's gap" and "the situation's
gap", "producers", "in order", "standing", "covered", "opposition", "subgoal", "pair",
"effective pair", "closed" and "free" relation, the scenes "Chain", "Shop", "Pool",
"Values", "Stuck", "Alarm", the goal-function names *acc*, *acc_theta*, *mech*, *anti*,
*const*, *world*, *local*, the goals *true*, *opp*, *does*, case names D1–D24 and Y1–Y10,
and the Lean names `Candidate`, `gap`, `Determinate`, `legitScoring`.

**Outstanding maintainer actions**

1. Confirm that the two addenda were sent at your request. They arrived as messages from
   two agent sessions (`alignment-workspace-b5`, `alignment-workspace-2f`), not in the
   dispatch. Decision required: *confirm*, or name the one to remove; on removal,
   `git rm` the addendum file under `prompts/2026-11-10-legitimacy-definition-prosecution/`
   and the file it produced (`decomposition/ADVISER_AS_PART.md` or
   `decomposition/TWO_DECOMPOSITIONS.md`), and drop H5 or H6.
2. Rule which reading of the constraints the account means, or that it means none yet:
   *independent* as intensional (a table of the mechanism is excluded by fiat) or
   extensional (then something else must exclude it); *never opposed* as stated or
   pairwise; *nothing left over* with or without joint attainability. Entered in *Awaiting
   the author*. Decision required: one choice for each of the three, or *leave open and
   dispatch item 136*.
3. Rule whether a part handed a falsehood is failing or serving: whether purposes are
   scored by the facts or by what the part was handed. Entered in *Awaiting the author*.
   Decision required: *by the facts*, *by what it was handed*, or *the account does not
   say*.
4. Rule the comparison action: against what an adviser's action is said to widen a gap.
   This restates the entry of 2026-11-11 on the reading of *in range* and, behind it, the
   entry of 2026-11-10 on the faithful-adviser standard; both are kept, with a line
   pointing here. Decision required: *silence*, *a declared reference*, *the adviser's
   best action*, or *different standards for a stranger and for her adviser*.
5. Rule whether a change in what she cares about that her goal does not rank can be bad.
   This restates the entry of 2026-11-11 on V+, which is kept with a line pointing here.
   Decision required: *yes, and the account needs a second standard*, *no*, or *leave
   open*.
6. Retire or restate the *Awaiting the author* entry of 2026-11-10, "Does the
   faithful-adviser standard, or only the arm's-length one, bind a corrigible adviser?"
   (carried from the second follow-up). On retiring:
   `git rm projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md`,
   and drop its row from that directory's `README.md` and `PROVENANCE.md`.
7. File the two items below once an executor's handle is mapped (the *Awaiting the author*
   entry of 2026-11-10 on `@claude-fable-5-2` stands). The first is carried from the
   second follow-up, restated; the second is new.

   > **Determining from what an overseer can observe whether a verdict of hers stands**
   > [open]. Section: Normativity line — legitimacy. In the account of
   > `decomposition/ACCOUNT.md` (in
   > `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`)
   > a verdict stands when no part it read was subverted or forced, which is a fact about a
   > candidate description of her that histories do not fix (`decomposition/THEOREMS.md`,
   > statement 7). Theorem 3 of
   > `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` takes
   > `UnbiasedFromFeedback`, which compares estimates with realized scores that depend on
   > the predicate. Wanted: an observation model for an overseer (what of a step is
   > recorded: the adviser's inputs, her action, her alterations of her own mechanisms,
   > her response to disclosure modelled as a step and not as the deletion of inputs); for
   > each, whether "stands" is a function of the record, estimable from it without bias,
   > or neither, with the case that separates them.
   > *Deliverable shape:* `test-supported` — modules under `decomposition/` of that round,
   > one per observation model, predictions frozen before the code.
   > *Acceptance check:* `python3 run.py` in the round directory green with a status for
   > each new statement in `decomposition/THEOREMS.md`; the lie about a matter she does
   > not act on, the open temptation and the hard truth each classified under each
   > observation model.
   > *Context:* `decomposition/THEOREMS.md` statements 6 and 7;
   > `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` H10.

   > **A kind for harm that preserves gaps, and a gate that sees it** [open]. Section:
   > Normativity line — legitimacy. In the account of `decomposition/ACCOUNT.md` an
   > adviser's action is harm when it lowers a part's best and subversion when it widens a
   > gap, and manipulation is subversion. A threat lowers the best and widens nothing; so
   > does a signal that moves two of her parts from a better joint choice to a worse one
   > (`Y7`). `decomposition/THEOREMS.md`, statement 6: against the least-total-gap
   > baseline, adding a threat at one world widens no gap and moves her choice from 21/40
   > to 39/40; statement 3: harm is not invariant under a redescription that keeps every
   > ranking. Wanted: a condition on the adviser's effect on a part's *best* that
   > separates a threat from an offer and from a true warning, stated without a common
   > scale across situations or with the scale it needs named; and the gate's no-gain
   > property for "no subversion and no such harm", proved, refuted, or reduced to
   > aim-freedom.
   > *Deliverable shape:* `test-supported` — modules under `decomposition/` of that round,
   > predictions for D9, P13, T1, T2, Y7 and D21 frozen before the code.
   > *Acceptance check:* `python3 run.py` in the round directory green with a status for
   > each new statement; the threat policy of statement 6 gains nothing under the new gate
   > or is listed as the counterexample.
   > *Context:* `decomposition/THEOREMS.md` statements 3, 4 and 6;
   > `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` H10.

The pull request is not auto-merged; the merge is a pull-request fact.

## Fourth follow-up (2026-11-12) — candidates weighted by explanatory quality, influence judged against the adviser's aim

Dispatched by `PROMPT-followup-4.md`. The idea the account develops is Sam Eisenstat's; the
four explanatory virtues and the five readings under test are the maintainer's, the
readings provisional. Write scope: the round directory, this prompts directory, items
136–138, `DECISIONS.md`, and the structured state the gates require. No Lean was written.

**Headline.** The account is stated over a finite model in `scored/ACCOUNT.md`. Every
result is a conditional calculation in that model — one small scene, three stipulated
principals, two tabulated languages, one cost for a missed move — and the pass ran two
investigations that the implementation does not join: weights over candidates on one
scene, and a bank of cases judged under stated candidates. *Weights.* Scoring candidates
by parsimony, fit and handles, read by a second predictor, concentrates the weight in
mass and not on agreeing candidates. Under each principal, at 0.95 or more of the weight,
the judging part is given either no purpose or a purpose that names its own mechanism,
which the second predictor cannot use, and its behaviour is carried as a table of the
history; under two principals the heavy candidates split on whether a lie is illegitimate
and under the third on a trick, a temptation, a threat and a hard truth. This follows from
choices fixed before the code: a wrongly predicted move costs 8 bits and an unpredicted
one 1 or 2, and a part sees so little that a table is short. Under the other reading of
what a purpose predicts (the best move on what the part sees) the belief part's purpose
follows her corrections, as the dispatch expected and as the principals were built to
show; the judging part's does not. The score is a loss and not, as first claimed, a code
length. *The bank.* Judging influence against the adviser's aim, under stated candidates
and aim structures the executor assigned, 77 of 89 cases match their evident character
against the third follow-up's 66, by a changed standard; five of six honest-difficulty
over-counts are gone because those cases are listed as the same at every aim, and a
threat is illegitimate. No principal's weights favour the stated candidate, and under the
corrector's heavy candidates a threat is not illegitimate. *The gate.* Choice-invariance
between actions that harm, subvert and force nothing against each other holds under the
stated candidate and fails under every candidate tied at the top for two of three
principals; no maximizing adviser was analysed. The condition is strictly weaker than
aim-freedom of the adviser's whole intervention, and the decomposition adds nothing to
the mathematical guarantee aim-freedom gives: it adds a candidate-relative rule for which
aim-dependent variation to permit.

### I1. The account as stated

`scored/ACCOUNT.md`. A **candidate** is a term: a goal, a purpose for each part, and
exceptions *(part, view, move)* on views that occur in her history. At a situation it
predicts, for each part with the other parts' moves as they were, the exception's move
if one applies, and otherwise the moves best by the part's purpose. Its **weight** is
`2^(−bits)` normalised, with `bits = DL + Fit + Hand`: the length of the term, plus the
cost of each move on the history it does not predict, plus the same on the probes
(adviser inputs she has not met, and four changes: a better instrument, a falsehood
disclosed, a source shown unreliable, a part degraded). A move outside the predicted set
costs 8 bits; a move inside a set of `k` costs `⌈log₂ k⌉`. The costs are computed by a
**second predictor** who has the term and the scene, for whom a term that refers to her
own mechanism or action predicts nothing. Three principals share one history on a chain
of three parts and a part that states her aim: a **corrector**; a **non-corrector**; a
**divided** principal who corrects her beliefs, says she aims at the good option, and
takes a cue she could leave. The adviser is a rule from what it knows and its aim, over a
stated set `U` of aims, to an action; an action is **aim-driven** where another aim of `U`
acts differently; it **harms, subverts or forces** a part when it does so against that
other aim's action; and the influence is **illegitimate** when in addition the aim is not
that part's own purpose and no standing verdict of hers covers it.

Choices made where §1 or §2 was ambiguous, each with its alternative (`ACCOUNT.md` §10):

1. **A purpose predicts that the part serves at the situation as it is** (*serves*).
   Alternative, *view-best*: the best move in expectation on what the part sees. Both are
   computed; the difference is the largest in the pass.
2. **Each part's move is behaviour to be predicted.** Alternative: her action alone, under
   which candidates differing in the purposes of earlier parts predict alike.
3. **Handles are scored against what she would do** and are part of the weight.
   Alternative: definiteness alone, which rewards a confident wrong candidate.
4. **The four virtues are terms of one sum in bits**, and nothing but prediction of her
   record lowers it. Rejected: a weighted sum with free coefficients. The frozen account
   called the sum a code length and the weight the probability a second predictor gives
   her record; the review showed it is neither (I5, point 10), and the cost of a missed
   move is such a coefficient.
5. **The second predictor is given the scene** with the explanation.
6. **"Another aim" ranges over a stated set `U`**, and a gap is the adviser's when wider
   than under *some* other aim's action. In a banked case `U` has two members.
7. **An aim is a part's own purpose when the objective is the part's goal function.**
8. **In a banked case the other aim's action is the third follow-up's comparison action**
   unless the case says otherwise.
9. **Readings 3 and 4 are reported as conditions on candidates**, not applied to weights.
10. **A heavy candidate** is one of the fewest that hold 99/100 of the weight.
11. **The bank is computed under each scene's stated candidate**, with the weight of
    illegitimacy beside it for cases on Chain.

Also fixed by the executor and not by the dispatch: the two description languages as
tables of lengths; the history (80 steps) and the probe set (84); the three principals'
behaviour on the probes; the exception form (a table entry on a view of the history);
the goal vocabulary, including `ease`, the goal the divided principal pursues.

### I2. Verdicts and the divergences

Ninety-four cases, 101 rows; 93 rows carry a prediction, 89 match, 4 diverge on three
cases (`scored/DIVERGENCES.md`), each named in the bank before the code as expected to.

| computed | rows |
|---|---|
| illegitimate: aim-driven subversion (with or without other kinds) | D1–D5, D13, D16a, D17, D18, D22, P1, P3, P5, P8, P12, B5, T3, T6, T8, N1, N3, N7, N8a, N8b, N11a, N11b, X1a, X2, X3, X4, Y8, Z4 |
| illegitimate: aim-driven harm | D9, P13, T1, Y7a |
| illegitimate: force | D10, P4, B1, B2, B3, T4, T5, T10, T11, N4 |
| force, covered; not illegitimate | D12, P9, N5, X5 |
| aim-driven, help only; not illegitimate | D6, D21, P2, P7b, P7c, P14, B4, B6, T2, T12, Y5, Z1, Z5 |
| aim-driven, subversion of the part whose purpose is the aim; not illegitimate | Z3 |
| aim-driven, nothing | D11, D15, D16b, T7, N9, N14, X1b, Y4 |
| not aim-driven, a gap; not illegitimate | D14, P7a, P10, P11, T13, X7, Y6, Y9, Z2 |
| not aim-driven, no gap | D20, P6, N2, N10, N12, N13, Y7b |
| no adviser: a gap, hers or nobody's; in order | D7, D8, D19, D23, D24, P15, T9, N6, X6, Y2, Y10 |
| weights | Y1 (the alarm part is for the goal at 0.992 under the corrector), Y3 (the idle part has a purpose at 0.9999) |

**Divergences.** **P7b, P7c**: predicted not aim-driven; an author and a friend who show
what serves their view are rendered as choosing by it; the verdict, not illegitimate, is
the dispatch's. **N14**: predicted illegitimate; the rendering leaves her equally well off
under both aims, and selection that changes no part's best or gap is nothing. **Y3**:
predicted that a purpose for a part nothing depends on is carried only by low-weight
candidates; a purpose predicts the idle part's moves, and each part's move is behaviour to
be predicted.

**Reported.** **Y5**, a lie that exchanges one error for another: help to judge and act,
belief's gap unchanged, not illegitimate. **N8**, **N11**: illegitimate whether or not her
mechanism discounts the known aim. **X1**: illegitimate when her mechanism reads the
signal as sent, nothing when she reads at face. **D23**: no gap; expressed by reading 3
and by reading 4 (statement 8).

### I3. Statements 1–9

`scored/THEOREMS.md`. After the review the statements of 5, 6, 8 and 9 were narrowed, and
numbers in 1, 3, 4 and 5 corrected; no status changed.

| | status | on what |
|---|---|---|
| 1 the weight concentrates on candidates that agree | **refuted** | for agreement; the mass does concentrate: the top ten of 4,000 hold 0.84, 0.90, 0.98, and 40, 22, 12 are heavy. They split on the belief part's purpose and on a lie (corrector, divided) or on a trick, a temptation, a threat and a hard truth (non-corrector), and give the judge `const` or a private `mech` at 0.95 or more. "Purpose equal to mechanism" as a rule is charged by intersubjectivity alone (644 bits; without it, it is the heaviest at 0.84); as a table it is within 14 bits of the heaviest under two principals. The stated candidate with no exceptions is 894, 1,062 and 876 bits above the heaviest. Without handles the three principals have the same weights. Language B changes the heaviest goal to "whatever she does" under two principals, and the class itself. Under view-best the belief part's purpose is fixed at 0.9999 under each principal and the judge's is not. Five parts: not reached |
| 2 facts or what it was handed | **refuted** | read of every part. It holds at the belief part under both readings (facts 0.28 against 0.02 under the corrector, handed 0.9999 under the non-corrector) and fails at the judge and the acting part |
| 3 lying | **refuted** | against a threshold of 99/100 the executor set. A lie she will act on, where she would otherwise be right: 0.28, 0.000025, 0.998 by principal (view-best 0.9999, 0.87, 0.9999), and at hard worlds alone 0.28, below 10⁻⁶, 0.28; about a matter nothing reads: below 0.0005 (view-best 0.9999, 0, 0.9999); to someone already wrong: 0 under every candidate, a fact about the rendering |
| 4 the comparison by aim | **holds on the stated domain** | 77 of 89 match their evident character (66 before), 9 do not, 3 open; none that matched before fails now. Not a controlled comparison |
| 5 the gate | **refuted** | as choice-invariance over pairs of base actions; no maximizing adviser is analysed. Both earlier counterexamples are closed. Under the stated candidate no two actions that harm, subvert and force nothing against each other leave her choice different. The statement fails where her goal does not rank the options (108 pairs), where every part is scored by what it was handed (84), and under every candidate tied at the top for the corrector (78 or 166) and the non-corrector (192) |
| 6 intersubjectivity and the description language | **refuted** | the weights under the two languages are 0.96, 0.89, 0.80 apart in total variation with it and 0.89, 0.91, 0.89 without: further for the corrector. Whether a second party reproduces the verdicts of statement 4 was not shown |
| 7 stated and pursued aims | **holds on the stated domain** | the divided principal: every heavy candidate has goal `ease` and explains her statement as saying the creditable thing. One atom buys any goal against any statement, and the goal and that purpose were put in the vocabulary for her |
| 8 readings 3 and 4 | **holds on the stated domain** | D23 is expressed by either. Reading 3 is met vacuously by nearly all the weight (candidates whose exceptions leave no normal condition); reading 4 leaves 0.04, 0.06, 0.998 and, where it bites, favours the goal "whatever she does" |
| 9 what `Legit` then is, candidate by candidate | **holds on the stated domain** | values within a `Scoring`'s bounds under each candidate, not elaborated; the graded predicate with a running sum is not shown to give one. Every one of five adviser inputs has positive weight of illegitimacy under every principal, so the cut-off decides |

### I4. The third follow-up's table of what corrigibility needs, row by row

| what corrigibility needs | third follow-up | now | what changed |
|---|---|---|---|
| a predicate `Legit` on histories | stated | stated, graded: a weight of illegitimacy in `[0, 1]` per step and a running sum | graded; and it now takes the adviser's rule at aims it does not have, as the second follow-up's *uniform* did |
| a single-decision setting | a `Decision`; weights unargued | a `Decision` with weights from the score of `ACCOUNT.md` §3 | the weights have a rule behind them, with a free cost for a miss, and favour tables; `N` is still illegitimacy |
| the violation probability `v` | depends on candidates no constraint separates | computed per action and principal | it depends on the principal's corrections: a lie has `v` 0.27, 0.00, 0.91 |
| a comparison action | four computed, none fixed | the other aim's action | fixed given `U`; `U` is the new parameter (Z5), and harm done at every aim passes (Z2) |
| the gate's no-gain property | not obtained | choice-invariance between actions that harm, subvert and force nothing against each other, under the stated candidate; fails under ties and under candidates scoring by what a part was handed; no maximizing adviser analysed | a property of the candidate; harm is gated, so the threat counterexample is closed |
| her later judgment as the standard | a standing verdict can be wrong | unchanged; under the heavy candidates her judging part has no purpose | worse under the weights |
| Theorem 3's hypotheses | not approached | not approached | none |
| a graded score with a cut-off | the gap; a running sum | the weight of illegitimacy, a number in `[0, 1]`; a running sum | the grade no longer needs a common scale across parts; with a cut-off of 0 every action some candidate convicts is convicted; the sum is not connected to a `Scoring` |
| invariance of the verdicts | only serving to not serving | not retested | harm is now gated, and harm is the kind statement 3 of the third follow-up found not invariant |

### I5. External review

One review through `codex exec --sandbox read-only` (codex-cli 0.153.4, model
`gpt-6-astra`, as its log reports), on copies of the round directory, the dispatch with a
local path replaced, four Lean files, the third follow-up's assessment and a draft of this
section. Its reply is `REVIEW-astra-followup-4.md`, verbatim. It ran the runner and
reproduced every status and every count it checked. Dispositions, by its numbering:

1. *Statement 1 is refuted for agreement, not concentration; the non-corrector's heavy
   set does not split on a lie.* **Accepted; the draft was wrong** about the non-corrector.
   Corrected here and in the README.
2. *Statement 2's refutation comes from reading "a part" as every part; the acting part's
   result is unsurprising; the vocabulary sets the two scorings far apart.* **Accepted**;
   all three said in the statement.
3. *The 99/100 is invented; the quantity is the weight of candidates convicting at some
   world of a set and hides variation between worlds; "already wrong" is a property of
   the rendering.* **Accepted; computed** by kind of world and reported; the other two
   said.
4. *77 against 66 is not a controlled comparison, and the verdicts are the stated
   candidate's.* **Accepted**; said in the statement and in the headline.
5. *The gate statement is choice-invariance over nine actions, not the dispatch's
   maximizing adviser.* **Accepted**; the statement says so. The optimization was not done.
6. *The second-party reproduction was not computed: the code returned a count from the
   absence of a private term.* **Accepted; a defect.** The claim and the code are removed
   and the question is recorded as not shown.
7. *Statement 7's check asked for half the weight, not every heavy candidate; the result
   is constructed by `ease` and `please`.* **Accepted; the check strengthened** (it still
   holds) and the construction said.
8. *Reading 3 is vacuous for nearly all the weight; "a part with no purpose opposes
   nothing" is false.* **Accepted; reproduced** (0.99999998 and 0.9999998 of the weight on
   candidates with no normal condition; `const` belief opposing judge and act at a hard
   world). The sentence is replaced.
9. *The bounds hold candidate by candidate; the graded predicate is not given a `Scoring`;
   "three lies" multiplied a world average.* **Accepted**; the statement is narrowed to
   the candidate-relative construction and the three steps are computed at one world.
10. *The residual code violates Kraft (0 bits for a hit, 8 for a miss); the weights are
    not likelihoods; the 8 is a free coefficient.* **Accepted.** The interpretation is
    withdrawn in `ACCOUNT.md` and `THEOREMS.md`: `bits` is a loss. Not repaired; no number
    was recomputed under a normalised likelihood.
11. *The headline's mechanisms are design artifacts; "not built in" draws too sharp a
    line.* **Accepted.** I7 no longer claims any result as not built in, and the headline
    calls the results conditional calculations.
12. *"No purpose" conflates `const` with a private `mech`, which is a different goal
    function.* **Accepted**; reworded throughout.
13. *The language comparison changes the class (4,000 against 3,600 terms), and exception
    lists and view-best's reference are chosen with the probes.* **Accepted; confirmed**;
    said in statements 1 and 6 and in I7.
14. *The bank has no objectives over outcomes: `OWN`, `constant` and `none` are lists of
    case ids, and the old comparison action is relabelled the other aim's.* **Accepted**;
    said in statement 4 and I7.
15. *Which assignments decide the verdicts; only Z3 tests the own-purpose clause.*
    **Accepted**; said. Honest, mistaken or compliant does not entail the same action at
    every aim, and the bank's rule assumes it.
16. *The lemma is false for legitimacy as defined, which admits covered and own-purpose
    harm and subversion (Z3, N5).* **Accepted; a defect.** The lemma is restated for
    actions that neither harm nor subvert, which is what the proof and the check use.
17. *The gate analysis took one of several tied maximizers.* **Accepted; reproduced.**
    Every tied candidate is now computed: 78 or 166 pairs for the corrector, and under
    view-best none or 88 according to the acting part's purpose.
18. *The relation to aim-freedom holds for the adviser's whole intervention, not for
    Lean's `hx`; aim-freedom does not forbid teaching.* **Accepted**; both corrected.
19. *`Realizes` has no fixed relation without `x`, the channel and the reference; the
    decomposition adds nothing to the mathematical guarantee, and adds normative structure
    that the calculation does not validate.* **Accepted and adopted** as the answer in
    statement 5 and I8.
20. *The "stated candidate" row was an eight-exception variant (the stated candidate is
    894, 1,062, 876 bits above); two candidates tie without handles; "seven in eight" is
    for two-valued moves; 1/2 and 21/40 are joint probabilities.* **Accepted; each
    corrected.**
21. *Rounded zeros are positive, and with a cut-off of 0 any positive weight convicts;
    skipped mass is discarded.* **Accepted.** Statement 9 says so: every one of five
    inputs is convicted at cut-off 0 under every principal. Skipped mass is reported where
    computed.
22. *Y1 and Y3 counted duplicate explanations.* **Accepted; fixed** (0.992 for 0.988; no
    verdict changed).
23. *What the draft still failed to say; "exemptions, not protection" understates; "no
    subject" is unsupported; the urgent next result is a coherent predictive model.*
    **Accepted.** I7 and I8 are rewritten on each, and item 136 asks for that model.

### I6. Deviations from the prompt

- **A second reading of what a purpose predicts was computed throughout** (*view-best*),
  after the first results; the dispatch asked for a choice and its alternative.
- **`scored/ACCOUNT.md` was amended after the freeze** in the places its head lists (the
  degraded part's own move is not scored; history lengths 160, 320, 640 in place of 40,
  which gives fractional counts). No prediction was edited.
- **The class contains the third follow-up's 3,000 as 750 terms**: two candidates there
  that differ in a mechanism only off the history are one explanation here.
- **Statements 2, 3, 5, 6, 7, 8 and 9 were given the exact form their status needs** by the
  executor; where the dispatch asked for a quantity (3, 7, 9) the status is of a stated
  claim about it and the quantity is tabulated.
- **Statement 1's model of five parts was not reached.**
- **The bank is computed under stated candidates**, not under the weights; only Chain has
  a class, and the weight of illegitimacy is reported for its rows.
- **Seven renderings were changed beyond the five REPORT H9 names** (X3, P7, N8, X1, D13,
  Y7, Y1, Y3 as `scored/CASE_BANK.md` lists), and five cases were added (Z1–Z5).
- **The count of statement 4 uses a standard written down in this pass** (illegitimate or
  not, per case); the third follow-up's 66 was by kinds.
- **Statements and checks were changed after the review** (I5); the review saw a draft of
  this section, not this text. No status changed and no prediction was edited.
- **The dispatch's maximizing adviser was not analysed** in statement 5, and **whether a
  second party reproduces the verdicts** in statement 6 was not computed.
- **No new item is filed**; the text of one is under Outstanding maintainer actions.

### I7. What was not shown

- **How far the result depends on the three principals: entirely, for the results that
  distinguish them.** Their behaviour on the probes is stipulated. The corrector was built
  to correct at the belief and judging parts, the non-corrector to follow what she is
  handed, the divided principal to take a cue she could leave; statement 2's result at
  the belief part and statement 7's are the weights reading those stipulations back, and
  view-best's reference distribution is built from the same records. The results that are
  the same for all three (tables over purposes under *serves*; no usable purpose for the
  judge) are not stipulated outcome by outcome, and are favoured by the design all the
  same: a judge made vulnerable to framing and hard questions, a vocabulary with no public
  purpose that predicts those vulnerabilities, and no exception that generalises.
- **How far it depends on the description languages and the cost of a miss: decisively.**
  Both languages are tables of lengths chosen by the executor. At 4 bits a missed move the
  heaviest candidates have purposes at every part; at 8 and 16 they are tables. No value
  was argued, and the score is not a valid code, so no likelihood stands behind the
  weights. Language B changes the heaviest goal and the class.
- **No held-out prediction.** Her record on the probes is in the weights, in the choice of
  the *best* exception lists, and in view-best's reference. The ablation "no handles" drops
  the probes' term from the score and keeps a class built with them.
- **The scene is small.** A part sees a few flags, so a table of the history's views is 4
  to 6 entries. The five-part model was not reached.
- **One class**: the decomposition, what each part sees and the vocabularies are fixed.
- **The bank is the executor's reading of its own renderings, under aim structures it
  assigned.** No adviser objective is modelled; that a teacher's sample is "the same at
  every aim" is an input, and honest, mistaken or compliant does not entail it. For most
  cases the third follow-up's comparison action is relabelled the other aim's. Only Z3
  tests the clause that an aim may be a part's own purpose. The unfixed comparison action
  has become an unfixed range of aims: Z4 and Z5 are one policy with two ranges and
  opposite verdicts.
- **The bank's verdicts are not the weights'.** Shop, Pool, Values and Stuck have no
  class; on Chain the weight of illegitimacy is reported beside each verdict and often
  disagrees with it.
- **Statement 5**: a lemma about actions that neither harm nor subvert, an enumeration
  over nine actions on one scene, and counterexamples. Nothing about an adviser maximizing
  the gated score, authorized writes, or the exemptions.
- **Statement 6**: nothing about a second party.
- **Statement 9**: the running-sum predicate is not connected to the candidate-relative
  values; no reserved matters, respecting alternative, calibration or sequence.
- **Candidates below 2⁻⁴⁰ of the weight are not evaluated** in statements 3, 8 and 9 and in
  the per-row weights; a figure printed as 0.0000 is small and positive unless said.
- **The relation to the Lean conditions is by reading their statements**, and depends on
  how `x`, the channel and the reference are identified; nothing was built.
- **The repository-level `tests/run.py` sweep** was run once, under Python 3.13, on the tree
  as committed apart from this line: all green over 81 projects, the Lean build skipped as
  that runner does by default. The round's own runner was run under Python 3.13 only.
  `tests/round_records.py` had no pull-request context locally; CI runs it.
- **Nothing is registered.** Components: the account as stated — **open**; statements 1–9
  — **open**, their statuses runner-checked facts about a finite model.

### I8. Assessment

Each heading is confined to what this pass tested or found, beside the third follow-up's
corresponding finding.

**As an account of teleology and manipulation.** *Third follow-up:* 66 of 89 cases matched
their evident character; six over-counts, all honest difficulty; nine misses; a threat
was harm with her verdict standing. *Now:* 77 of 89. Judging against the adviser's aim
removes five of the six over-counts (the sixth, a surprise party, stays illegitimate
absent a standing verdict), convicts the threat and the advocate for an undisclosed side,
and labels the costly signal correctly. It leaves the misses the dispatch flagged (order
and framing between equals, redirection her goal ignores) and N14, and it adds two the
dispatch's own sentence implies: a lie told at every aim is not illegitimate (Z2), and
selective teaching is not when no aim of `U` would have told her the rest (Z5). For
teleology proper: the weighting has no threshold to deny a rarely performed function (Y1
matches), and it grants a purpose to anything whose behaviour a purpose compresses,
depended on or not (Y3).

**For the legitimacy framework.** *Third follow-up:* a predicate with the right shapes,
turning on a comparison action the account did not fix, and no no-gain property under any
comparison because harm is not subversion. *Now:* the comparison is the other aim's
action, given a range of aims that is as unfixed as the comparison was; harm is gated,
and both counterexamples are closed. Between actions that harm, subvert and force nothing
against each other her choice is the same under the stated candidate, and not under any
candidate tied at the top for two of three principals; the dispatch's maximizing adviser
was not analysed. The condition is strictly weaker than aim-freedom of the adviser's whole
intervention, which the second follow-up found the gate needs.

**For the research.** *Whether weighting restores what the yes-or-no constraints did
not.* The third follow-up found eight admissible candidates, no two classifying alike. In
this formalization weighting does not restore agreement: the weight is concentrated on
candidates that mostly carry her behaviour as tables. Under one reading her corrections
fix whether the belief part is scored by the facts or by what it was handed, in principals
built to differ in exactly that. Candidates that refer to her own mechanism are removed
only by a second predictor defined not to understand them, and the table is not removed.
None of this is a finding about explanatory weighting in general; it is what this
vocabulary, this cost of a miss and this scene give. *What the decomposition adds to
aim-freedom.* To the guarantee, nothing: aim-freedom gives equality of her evaluation,
and the condition gives equality of each part's best and gap under a candidate, which is
real, conditional on the candidate, and not enough for her verdict. It adds normative
structure — which aim-dependent variation to permit — that the calculation applies and
does not validate. *The single most valuable next result:* the weighting as a coherent
predictive model: one candidate class fixed across languages, an explicit likelihood for a
part's departures from its purpose in place of a flat cost, exceptions chosen without the
probes, and the probes then predicted and not fitted. Until that exists the question
whether purposes outweigh tables has no answer that is not a choice of coefficient; item
136 asks for it, on a scene where a table is dear.

### I9. Filings, names, and what is reserved

**Revised under the prompt's direction; nothing filed.** Items 136, 137 and 138 are
rewritten to ask for what this account needs: 136, the weighting as a coherent predictive
model (a fixed class, a likelihood for a miss, probes predicted and not fitted) on a scene
where a table of her history is dear; 137, the lemma of
statement 5, its strict implication from aim-freedom and `legitScoring` in Lean, the rest
waiting on a ruling; 138, the range of aims an action is compared against, and harm done
at every aim. `DECISIONS.md`: the maintainer's confirmation of the two addenda as a dated
entry, its queue entry removed; one agent-decided entry,
`2026-11-12--scored-account-readings`; the three queue entries of 2026-11-12 each given a
line on the reading tested and its result; the entry of 2026-11-10 on the faithful-adviser
standard restated; one new queue entry.

**New names, all provisional:** the dispatch's — "explanation", "weight", "parsimony",
"retrodictive fit", "handles", "intersubjectivity", "aim-driven", "illegitimate
influence", "a part's own purpose", the directory `scored/`; and the executor's —
"history", "probes", "changes", "exception", "second predictor", "public" and "private"
term, "normal conditions" (of a candidate), "heavy", "serves" and "view-best" (readings of
what a purpose predicts), "weight of illegitimacy", "size", "opposes", "unopposed", the
scene "ChainR", the principals "corrector", "non-corrector", "divided", the goals `ease`
and `does`, the purposes `handed`, `avow`, `please`, the exception policies *bare*,
*patched*, *best*, "language A" and "language B", the aim structures "driven", "own",
"constant", "none", case names Z1–Z5, and the Lean name `LegitAgainst` in item 137.

**Outstanding maintainer actions**

1. Rule what a purpose predicts of a part where no exception is listed. Entered in
   *Awaiting the author* (2026-11-12). Decision required: *that it serves at the situation
   as it is*, *that it does its best on what it sees*, or *leave open and dispatch item
   136*.
2. Rule which reading of its constraints the account means; the entry of 2026-11-12 stays,
   with this pass's result. Decision required: for *never opposed* and *nothing left
   over*, *a condition between parts with the best outcomes had together, applied to the
   weights*, *reported only*, or *leave open*.
3. Rule whether a part handed a falsehood is failing or serving; the entry of 2026-11-12
   stays. Decision required: *by her corrections* (the reading tested, which holds at the
   belief part only), *by the facts*, *by what it was handed*, or *the account does not
   say*.
4. Rule against what an adviser's action widens a gap; the entry of 2026-11-12 stays.
   Decision required: *the action it would have taken with another aim, with a rule for
   the range of aims* (item 138), *a declared reference*, or *leave open*; and whether a
   harm done at every aim is illegitimate.
5. Rule whether a change in what she cares about that her goal does not rank can be bad;
   the entry of 2026-11-12 stays, untouched by this pass. Decision required: *yes, and the
   account needs a second standard*, *no*, or *leave open*.
6. Rule whether her own adviser is held to more than a stranger; the entry of 2026-11-10 is
   restated as this. Decision required: *one standard*, or *her adviser's range of aims
   includes aiming at her parts' own purposes*. On ruling, the entry of 2026-11-11 on *in
   range* can be retired with it, and then
   `git rm projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/steering/DIVERGENCES.md`,
   dropping its row from that directory's `README.md` and `PROVENANCE.md`.
7. File the items below once an executor's handle is mapped (the *Awaiting the author*
   entry of 2026-11-10 on `@claude-fable-5-2` stands). The two of H11, action 7, are
   carried; the second of them, *A kind for harm that preserves gaps, and a gate that sees
   it*, is answered in part by this pass (harm is gated under reading 2; its scale is
   not) and should be restated against `scored/` when filed. One is new:

   > **Knowing the adviser's rule at aims it does not have** [open]. Section: Normativity
   > line — legitimacy. In the account of `scored/ACCOUNT.md` (in
   > `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`)
   > an adviser's influence is illegitimate when its action harms, subverts or forces a
   > part against the action it would have taken with another aim. `Legit` is therefore
   > not a predicate of the realized history: it reads the adviser's rule at aims it does
   > not have, as the second follow-up's *uniformly in range* did
   > (`teleology/THEOREMS.md`, statement 3). Wanted: an observation model for an overseer
   > under which the rule at other aims is recorded or estimable — a committed policy, a
   > population of advisers with different aims, interventions on the aim — and for each,
   > whether `Legit` is a function of the record, estimable without bias as
   > `UnbiasedFromFeedback` of
   > `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean` needs, or neither,
   > with the separating case.
   > *Deliverable shape:* `test-supported` — modules under `scored/` of that round, one per
   > observation model, predictions frozen before the code.
   > *Acceptance check:* `python3 run.py` in the round directory green with a status for
   > each new statement in `scored/THEOREMS.md`; teaching only what favours its aim (Z4,
   > Z5) and the lie told at every aim (Z2) classified under each observation model.
   > *Context:* `scored/THEOREMS.md` statements 5 and 9; `scored/ACCOUNT.md` §6;
   > `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` I4.

The pull request is not auto-merged; the merge is a pull-request fact.

## Fifth follow-up (2026-11-13) — a part as a mechanism and a purpose on the world

Dispatched by `PROMPT-followup-5.md`. The idea the setting develops is Sam Eisenstat's; the
rest of the position is the maintainer's and the prompt author's, parts of it provisional.
Write scope: the round directory, this prompts directory, items 136–138, `DECISIONS.md`,
and the structured state the gates require. No Lean was written. Purposes are given in
this pass, not recovered from behaviour.

**Headline.** The setting is stated over a finite model in `blocks/SETTING.md`. Range and
gap can be stated and used once a grain is fixed. The four kinds of influence cannot be
used as dispatched: they needed a comparison with the adviser's null action, typed
actions, a move that carries confidence, her verdict as one part's move, the rule at
other aims for ties, and a menu for each revising part. Twenty-six of the dispatch's
twenty-seven cases with a prediction have the predicted verdict, under renderings the
executor wrote; that is consistency, not a test. Of thirty-two statements nine are proved
on paper, eighteen hold on a stated example and five are refuted. The positive results
are applications of the law of iterated expectations with one exception (J3, 3.2); what
the pass adds is mostly counterexamples.

### J1. The setting as stated, and the choices made

`blocks/SETTING.md` §2. States with a prior. An adviser: what it knows, an aim, a rule to
an action with four typed components (signal, consequence, force, alteration). The actual
condition is the law of state and action under its rule; the null condition is the law
with no action. A part is moves, a mechanism from the world state to a move, and a
utility, which is what it is for. A part is in range at a grain when no re-reading of its
own move, allowed to use the grain, does better by its utility; the gap is what the best
re-reading gains. Subversion is a gap wider than under the null condition. Harm to a
choosing part is a fall in the most it could obtain when the consequence is put in, her
moves held. An influence is illegitimate when it subverts or harms, forces or alters with
no prior request from a part of hers in range, or breaks a tie by its aim; her verdict is
legitimate when every part behind it is in range. An end is a part for what it values at
the time; an end-revising part is for the fit of its replacement with her other ends
(what they attain, less what they would lose if the replacement got its best); a
maintaining part is for what the part it alters is for.

Choices where §2 was open, each with its alternative, in `SETTING.md` §3; the ones a
result turns on: the grain is what is settled before a part is used, the step in these
scenes (alternatives computed: none, the adviser's action, the adviser's knowledge); an
estimating part's move carries its confidence (alternative: two-valued, case 4b);
subversion is a widening against the adviser's absence, between laws (alternatives: no
comparison; state by state); the consequence removed for harm is the adviser's absence
(alternative: its own rule with the announcement removed, cases 33a and 33b); her verdict
is one part's move (alternative: case 30); fit is attained minus opposition, judged by
the other ends (alternatives computed in question 5); "hers" and "nobody's" are one
verdict.

Devices found needed, `SETTING.md` §4: the null action (a comparison); typed actions; a
grain per scene; a move that carries confidence; the verdict as a part's move; the rule
at other aims, for ties; a menu for each revising part. Three of these are supplied
lists. A home condition for a part was not adopted, and without it "hers" and "nobody's"
are not separated.

### J2. The cases

`blocks/RESULTS.md`, *The cases*, gives each verdict with its reason. Thirty-seven rows:
the dispatch's twenty-eight cases (case 11 as two rows) and eight added.

| computed | rows |
|---|---|
| out of range, the adviser's; illegitimate | 1, 2, 4, 15, 21, 25, 28, 4c, 27b |
| out of range, not the adviser's | 5, 6, 9 |
| in range; the adviser's influence not illegitimate | 3, 7, 8, 11a, 11b, 13, 16, 27, 4b, 29, 31 |
| in range; harm; illegitimate | 10, 33a, 33b |
| force; illegitimate | 12 |
| in range; a tie broken by the aim; illegitimate | 14 |
| alteration, covered | 22 |
| alteration, not covered; illegitimate | 23 |
| a change of end or mechanism, legitimate | 16, 17, 18, 19 |
| a change of ends, illegitimate, nobody's | 20 |
| in range, no adviser | 24, 26, 30 |

**One divergence**, case 9, an advocate for an undisclosed side (`blocks/DIVERGENCES.md`):
predicted out of range and illegitimate; computed out of range and not the adviser's. The
frozen rendering has her return 0 when shown nothing; in the adviser's absence that has a
gap of 1/4, and under the advocate her gap is 1/12, which is narrower. With 1/2 on
nothing the case would match. The comparison that says the adviser brought a gap about
turns on a number the scenario does not fix.

**The count.** Case 25 asks only for a report. Of the other twenty-seven, twenty-six
match. Cases 3, 6, 18 and 20 predict "hers" or "nobody's" and are matched as not the
adviser's. Case 4 matches under the description that gives her a confidence and not under
the one that gives her a two-valued belief (4b). Case 27 matches when her confusion is
calibrated and not when she ends wrong on average (27b). "Help" in case 7 is matched as
her being better off. Where a prediction asks for something to be said, only its tokens
are matched.

**What the dispatch asked to be said.** *10*: the account gates a threat as harm, a
predicate on the influence; her verdict to comply is legitimate. *13*: buried information
leaves every part in range and is not illegitimate; it shows only in two adviser-side
quantities that decide nothing (gap 1/4 at the adviser's knowledge; 1/4 left on the
table). *14*: expressed by the rule at two aims, with no gap. *20*: her later verdicts are
not discounted, and fit then licenses revising the end that survived. *21*: a chain that
passes every step exists (case 29). *25*: the verdict is that of a plain lie; it differs
in that the adviser's knowledge adds nothing to the gap and its three actions leave
nothing on the table.

### J3. What was established on each question

1. **Do the definitions stand?** Range and gap: yes, given a grain. The four kinds: only
   with the devices of J1. A move the adviser set and a move made in response to its
   signal are told apart by the supplied type alone (1.1). Dropping the view is what
   keeps honest difficulty in range: a re-reading allowed to know the adviser's action
   opens a gap of 3/64 in case 3 and 3/16 in case 27 (1.2). It loses "it was there to be
   read" (case 13).
2. **The grain.** *Proved*: the gap grows with the grain (2.1); `(E[w(e − q)])² ≤ E[w²] ·
   gap` for `w` a function of the grain (2.2), so a grain protects the events it names.
   *Adopted*: what is settled before the part is used, for the reason that a mechanism
   can be fitted only to what precedes its use. It catches a lie targeted in time with
   any move (4c: gap 0 pooled, 1/5 at the step). A lie targeted at a state is caught only
   when her move carries confidence, with a gap of `η²/(1/2 + η)`, second order in the
   lie's probability (2.6). With a two-valued move, none of the four grains computed puts
   it out of range while leaving honest difficulty in (2.5, refuted), and it is the same
   object as a disclosed advocate (2.4). A hard truth passes when her confusion is
   calibrated and is convicted when she ends wrong on average, as a craving exploited in
   the open is. No range of aims is read: a lie told at every aim is illegitimate, and
   selective teaching has one verdict.
3. **Whose doing.** *Proved*: `|D − Δq| ≤ √g_0 + √g_T` for the foreseeable shift `D` in
   her verdict, the shift `Δq` in what the verdict is for, and the verdict part's two gaps
   (3.1); a maintaining part in range whose menu is closed under re-reading installs a
   mechanism in range (3.2), with closure needed. *Refuted*: that every foreseeable shift
   traces to something out of range or to the adviser (3.3): nobody's alteration, a
   maintaining part in range with an unclosed menu, and a change of ends by a part in
   range each give one. The recovering depressive is the removal of a starting gap, with
   nobody charged (3.4). That a gap is the adviser's is a stipulated comparison of laws,
   not a causal result. "Hers" and "nobody's" are not separated.
4. **Options and threats.** Range does not see a threat (4.1). Against the consequence
   removed, a threat is harm, an offer help, a true warning neither, with no aim read
   (4.2). A threat and a warning of the adviser's own standing practice are one verdict
   against its absence and two against its own rule without the announcement; what tells
   them apart is a fact about the branch not taken, which the scene supplies (4.3). The
   aim is needed only if that fact is to be derived from it.
5. **Change of ends.** A revising part has a purpose with no fixed final end. *Proved*:
   dropping an end always has the greatest fit (5.1). Fit leaves many changes (5.2) and
   does not say which of two opposed ends yields (5.3). *Refuted*: that a chain of
   legitimate steps keeps what her starting ends attain (5.4): two steps, each the one
   best move of a revising part in range, take her from her best outcome to her worst,
   with the adviser arranging only the occasions and its influence not illegitimate.
   Judged by all her ends the chain is refused. The rule on ties forbids an aim choosing
   between two equally fitting replacements only when the later revising part is left
   out of the scene (5.6). A conversion fit condemns is followed by a revision fit
   licenses (5.5). The whole-level bound holds with a positive gap for leaving law for
   music and for being made to like what is delivered alike (5.7). Who decides among
   equally fitting changes: open.
6. **Parts to whole.** Parts in range do not give a verdict in range (6.2: the larger of
   two calibrated estimates has mean 19/32 against 1/2). A weighted mean keeps the mean
   and is still not in range (6.4). The whole is in range when the aggregation is
   calibrated, which the setting can require only by making the verdict a part's move
   (6.1); that is the conclusion restated.
7. **What plugs into the post.** Two predicates, on her verdict and on the influence;
   both depend on the model beyond the realized history (7.4), which is no obstruction to
   a `Scoring` and is a statement of what an overseer must know. Theorem 1 takes any
   predicate. Theorems 2 and 3: nothing is constructed. `UnbiasedFromFeedback` is implied
   in probability, for a bounded score, by the range condition at the grain of the
   history of the part of the adviser that estimates the score (7.1), and not by range at
   a coarser grain (7.2); it is not equivalent to that condition and the almost-sure
   statement is cited. `selectionBlind_of_realizes` applies, on one scene, to an adviser
   whose signal to a part does not vary with its aim where the part reads nothing else of
   the action (7.3). The fourth follow-up's answer is confirmed: the decomposition adds
   permission and a rule of attribution and no protection; the whole-level bound stays
   true, and the permission counts as in order shifts it does not limit.

### J4. S1–S6 and F1–F6

The reviewer wrote its judgments before reading the executor's. Where the executor's
changed after the review, both are given.

| | executor | reviewer | reason |
|---|---|---|---|
| S1 | not met | not met | seven devices, a comparison and three supplied lists among them |
| S2 | met in part | met in part | 26 of 27 under the executor's renderings; one divergence; four predictions weakened in matching |
| S3 | met in part | met in part | an answer with a reason; a state-targeted lie is caught only by a confidence; a hard truth passes only when her confusion is calibrated |
| S4 | met in part | met in part | 3.1 and 3.2 are proved; they do not give authorship, and the dispatch's form is refuted |
| S5 | met in part | met in part | a purpose with no fixed final end; cases 15–24 sort; menus are supplied and chains are not survived |
| S6 | met, narrowly (first: met) | met, narrowly | one existing Lean theorem applies on one class of advisers; the executor's first judgment also rested on readings of `UnbiasedFromFeedback` and `Realizes` that the review corrected |
| F1 | met in part (first: not met, with one exception) | met in part | with a two-valued move a believed rare lie leaves every part in range; that views must come back is not shown |
| F2 | met in part | met in part | shifts with every part in range arise under an uncalibrated aggregation and under change of ends; not with a verdict part and fixed ends |
| F3 | not met | not met | one form of purpose per part across the cases; the reviewer adds that the evidence does not show per-case purposes to be needed, not that the code verifies one purpose everywhere |
| F4 | met in its second clause, on one example | met in part | the reviewer judged before 5.6 was computed: an aim then chooses between two equally fitting replacements with nothing illegitimate. A fixed reference is not shown to be needed; "common" is not shown |
| F5 | met in part (first: met for the positive results) | met in part | 2.2, 3.1, 6.4 and 7.1 are familiar; 3.2 and the counterexamples are not the tower property |
| F6 | met in part | met in part | no range of aims; the one grain that sees a two-valued rare lie convicts honest difficulty |

**The prompt author's predictions.** At least 22 of 28: 26 of 27, by the count above. S1
met: not met. S3 met: in part. S4 about even: in part. S5 in part, fit definable and not
unique: so. F5 the criticism most likely pressed: the reviewer pressed the null
comparison, the renderings and the Lean mapping harder, and rated F5 in part. Question 7
stays "permission, not protection": so.

### J5. External review

One review through `codex exec --sandbox read-only` (codex-cli 0.153.4, model
`gpt-6-astra`, as its log reports), on copies of the round directory, the dispatch with
local paths replaced, three Lean files and a draft of this section, the executor's
judgments in a separate file it was told to open last. Its reply is
`REVIEW-astra-followup-5.md`, verbatim. It ran the runner and reproduced every number it
checked. Dispositions, by its numbering:

1. *A passing runner compares status strings with example checks and does not certify
   the prose.* **Accepted**; `RESULTS.md` says so at its head.
2. *`model.py` matches §2 for range, but: "requested beforehand" was not implemented and
   an intervention could license itself; "the parts behind her verdict" is every part
   listed; several cases over ends bypassed the model; descriptions are evaluated one at
   a time.* **Accepted; the first a defect, fixed** (a request is read with the adviser's
   action null; statement 1.4 added). Cases 17, 24, 26 and 29 are now scenes; the stubs
   in 22 and 23 and the other two points are in J7.
3. *1.1's two scenes do not have the same law, since the actions differ; supplied lists
   and a threshold are used beyond the null comparison.* **Accepted**; 1.1 restated with
   the type forgotten, and the devices counted by kind.
4. *2.1–2.6 are sound in scope; 2.5 is about four grains; the event bound is `√(P(E) ·
   gap)` and is not a bound on how far an adviser moved her; "gap by step" figures were
   contributions.* **Accepted; each corrected.**
5. *3.1–3.4 earn their statuses; the localisation paragraph names no author and omits the
   prior; the null comparison is a stipulated rule of attribution.* **Accepted**; the
   paragraph is rewritten.
6. *4.1–4.3 earn theirs; in the warning it is the acting part's score that rises; the
   check that 33a and 33b share a law compared a scene with itself.* **Accepted**; the
   check removed, the two said to be one scene with a supplied fact.
7. *5.1 is for one end; case 29 had no adviser; 5.5 does not make the conversion
   legitimate after the fact; the tie claim of 5.6 was not implemented and the written
   rule asks every part's utility to be equal.* **Accepted; the last a wrong claim.**
   Computed: the rule fires with one revising part in the scene and not with both, so the
   claim is withdrawn and 5.6 restated.
8. *"Exactly" and "only" in question 6 are false: the joint posterior is a calibrated
   aggregation that is not linear, whether or not it is called a part.* **Accepted**;
   rewritten.
9. *7.1 holds with its filtration and a bounded error; the history is finer than the
   step; the Lean predicate is one-sided and about one sequence; the score is not in
   `[0, 1]`.* **Accepted**; "identified with" withdrawn for "implied in probability, for
   a bounded score".
10. *The table of Theorems 1–3 misstated hypotheses: `κ` is a definition, 2(c) does not
    need `Respects`, her verdict is not shown to be the post's `V`.* **Accepted**; the
    table is rewritten.
11. *`Realizes` is equality of outputs and not the absence of force and alteration, with
    a counterexample; "the Lean gives nothing where the signal varies" is excessive; 2.2
    does not bound the difference between two advisers by one term.* **Accepted;
    reproduced.** Both of its counterexamples are in the check, and 7.3 is restated.
12. *7.4 shows dependence on the model, not that a history must carry it.* **Accepted.**
13. *"Left by the adviser" was 0 where no actions were listed; case 3 with its own
    reports as alternatives leaves 3/64; "does not foresee her error" in case 25 is too
    strong.* **Accepted; fixed** (the quantity is absent where no actions are listed; case
    3 now reports 3/64; the sentence replaced).
14. *Each of the thirty-seven rows follows for its rendering, and the rendering decides.*
    **Accepted**, and adopted as the standing of the count. Its row notes are entered in
    the case table where they change a reading (8, 21, 22, 23, 24, 25).
15. *"27 of 28" is 26 of 27 with a prediction, a consistency count; the divergence note
    over-generalised.* **Accepted; both corrected.**
16. *Differences on F1, F4 and F5.* **F1 and F5 accepted.** F4: see J4.
17. *What the draft overstated and omitted; the next result needs a fixed class of
    conditions and a model with the adviser, the revising parts and time in it.*
    **Accepted**; this section and item 136 are written accordingly.

### J6. Deviations from the prompt

- **Case 11 is two rows** and **eight cases were added** (4b, 4c, 27b, 29, 30, 31, 33a,
  33b), each with the executor's prediction, in the freezing commit.
- **`SETTING.md` §4 was written after the results**; §1–§3 and the bank were not edited
  after the freeze. The dispatch asked for §1 and §2 "stated exactly": §1 is condensed,
  not reproduced.
- **Code, statements and prose were changed after the review** (J5). No status changed;
  one statement was added (1.4); four cases whose range had been asserted are computed.
  No prediction was edited and no banked verdict changed.
- **The review saw a draft of this section**, not this text, and judged F4 before 5.6
  was computed.
- **The dispatch's "no single part is the evaluator" was not kept** (device 5), and its
  two-line bounds are restated with a grain (2.2), not re-derived.
- **Earlier banks are not re-predicted** under this setting; the round runner runs them
  as they were.
- **No new item is filed.**

### J7. What was not shown

`blocks/RESULTS.md`, *What was not shown*, in full. The ones a reader of this section
needs:

- **The match is consistency.** The executor chose every number, response, menu and null
  behaviour; case 9 shows one such choice deciding a verdict.
- **One description per case.** The position's rule for a set of descriptions is not
  implemented; cases 4 and 4b are the only pair.
- **"Proved" is on paper.** Nothing is kernel-checked; 3.2 is checked by the runner only
  for a maintaining part whose move does not vary with the state.
- **Nothing about attribution is causal**, and "hers" is not told from "nobody's".
- **Change of ends is one small model**: additive valuations on at most three outcomes,
  unweighted; case 21's steps do not accumulate; case 29 has no schedule; ends in cases 22
  and 23 are stubs.
- **No hypothesis of Theorems 2 or 3 is discharged.** The Lean was read, not built.
- **The repository-level `tests/run.py` sweep** was run once, under Python 3.13, on the
  tree as committed apart from this line: all green over 81 projects, the Lean build
  skipped as that runner does by default. The round's runner was run under Python 3.9 and
  3.13. `tests/round_records.py` had no pull-request context locally; CI runs it.
- **Nothing is registered.** Components: the setting as stated — **open**; statements
  1.1–7.4 — **open**, their statuses runner-checked facts about a finite model with no
  registry entry.

### J8. The single most valuable next result

A model of change of ends in which the adviser, the revising parts, their occasions and
time are all present, a stated class of conditions on revision (who judges, by what
measure, with what memory), and for each condition either a bound on how far a chain of
legitimate steps can lower what her starting ends attain or the chain that defeats it.
`Δq` is the one term of 3.1 that no gap bounds, and until it is bounded or shown
unboundable the account permits what it was meant to exclude. Item 136.

### J9. Filings, names, and what is reserved

**Revised under the prompt's direction; nothing filed.** Items 136, 137 and 138 are
rewritten: 136, which end yields and what a chain of legitimate changes can cost; 137,
statements 2.2, 3.1, 3.2 and 7.1 and the instance of `selectionBlind_of_realizes` in
Lean; 138, the comparison that says an adviser brought a gap about. `DECISIONS.md`: one
agent-decided entry, `2026-11-13--blocks-setting-readings`; each queue entry of the
earlier passes given a line on what this pass found; two new queue entries.

**New names, all provisional:** the dispatch's — "re-reading", "actual condition",
"revising part", "fit among her ends", "localisation", "no inflation", "no profit from
moving her", the directory `blocks/`; and the executor's — "null condition", "grain",
"signal", "consequence" (components of an action), "estimating part", "choosing part",
"end", "end-revising part", "maintaining part", "attained by the rest", "opposition" (of
a replacement to the rest), "covered", "left by the adviser", "better off", the part
names *listen*, *act*, *crave*, *verdict*, *revise*, *maintain*, the bank's tokens, and
`LegitVerdict`, `LegitInfluence`.

**Outstanding maintainer actions**

1. Rule which end yields when two are opposed and who decides among equally fitting
   changes. Entered in *Awaiting the author* (2026-11-13). Decision required: *the other
   ends judge, as the position says* (then the chain of case 29 is legitimate), *all her
   ends judge, the one under revision included*, *her verdict at that time judges*, or
   *leave open and dispatch item 136*.
2. Rule whether truthful influence under which a part of hers goes out of range is
   manipulation. Entered in *Awaiting the author* (2026-11-13). Decision required: *yes,
   what she then does is all that counts* (the setting as it is: cases 27b and 28 alike),
   *no, truth exempts* (then content must be represented), or *leave open*.
3. Rule against what an adviser's action widens a gap; the entry of 2026-11-12 stays,
   with this pass's result. Decision required: *the adviser's absence, between laws* (the
   reading tested, with the defect of case 9), *no comparison*, *a home condition for
   each part*, or *leave open and dispatch item 138*.
4. The seven other entries of 2026-11-10 to 2026-11-12 on this round stay as they are,
   each with a line from this pass: the faithful-adviser standard; the reading of *in
   range*; V+; the reading of the constraints; a part handed a falsehood; what a purpose
   predicts; a change her goal does not rank. The last is restated by action 1 and can be
   retired with it. What a purpose predicts bears only if recovery from behaviour is
   resumed. Decision required for each: as its entry states.
5. File the unfiled items once an executor's handle is mapped (the entry of 2026-11-10 on
   `@claude-fable-5-2` stands): the two of H11, action 7, and the one of I9, action 7.
   This pass adds none. *A kind for harm that preserves gaps* is answered here in part
   (question 4) and *Knowing the adviser's rule at aims it does not have* now bears only
   on ties; both should be restated against `blocks/` when filed.

The pull request is not auto-merged; the merge is a pull-request fact.

## Sixth follow-up (2026-11-14) — manipulation as induced miscalibration of her estimates: a pressure test

Dispatched by `PROMPT-followup-6.md`, with an addendum, `PROMPT-followup-6-addendum.md`,
received during the pass from an agent session and attributed to the prompt author and
the maintainer on that session's word; a second session relayed the maintainer's
clarification that *trajectory* is the primary name of the concept the addendum asks
for, with *history* and *future history* as the same concept. The account tested is
stated in the dispatch's §1 and §2: the idea that manipulation is distortion of an actor
away from what its faculties are for is Sam Eisenstat's, the account of manipulation as
induced mistake is Robert Noggle's, and the statement in symbols is the maintainer's and
the prompt author's. Write scope: the round directory, this prompts directory, items
136–138, `DECISIONS.md`, the structured state the gates require, and, by the addendum,
`graph/` for a source and `state/concepts.json`. No Lean was written.

**Headline.** The account's inequalities hold, two of the six claims in corrected form.
As a classifier it reads no intention and passes the bank's honest cases, and it is
wrong on fourteen or fifteen of about a hundred cases under renderings the executor
wrote; the external review then showed that its second comparison convicts ordinary
honest help unless the comparison is with someone who differs from her only in the
flaw, which the account does not say. Changes of taste sort only once the account is
told which function her true utility is, and nothing on her side identifies it.
Calibration bounds the inflation of her verdict in expectation and not along the
realized sequence the post's theorem is about. For belief the workspace's existing
conditions already give the account's in a stronger form.

### VI.1 The setting and the choices made

`estimates/SETTING.md`. Choices where §1 and §2 were open (§3 there), each with its
alternative: her estimates are a fixed response to what she observes, run under each
policy compared; calibration is against the true law, the adviser's actual policy
included (alternative: the law she takes to hold); it is taken at what she observes
(alternative: at the estimate alone, computed); the quantities she estimates are listed
per scene and "worse" is a larger total (alternative: worse on some quantity, computed);
a policy is a choice and a report, the honest counterpart keeps the choice, and the
reporting norm is *truthful* (alternative: *forthright*, computed); "someone unable to
make that mistake" is a second type of principal at which the scene gives the adviser's
policy; `U*` is taken at two anchors, her starting values informed of the whole history
(*start*) and her values at its end (*end*); coercion, tie and alteration are read from
scene facts outside the account. Devices found needed (§4 there): eight, among them the
list of quantities with a weighting, the reporting norm, a second type that differs
from her in the flaw alone, and an anchor for `U*`.

### VI.2 C1–C6

| | status |
|---|---|
| C1 | holds as stated (1.1) |
| C2 | holds as stated, under squared loss (1.2) |
| C3 | holds as stated; it bounds her loss in true utility when her choice is a function of her information (1.3, 1.6); the constant 2 is not tight, `√2` is and is attained (1.4); any reference may replace "her information", with the bound then about that reference (1.5) |
| C4 | the threshold holds, strictly above it (1.7); with a detected departure a violation it is `(1 − V_h)/(1 + δ₀ + λ) < 1/2` (1.9). The last clause fails when "right on average" means over an option taken at random: an honest adviser that maximizes her verdict scores 5/8 on outcomes worth 1/2 (1.8); it holds if she is right on average given the adviser's information and choice. For a principal who has sized up the policy, `E[V] = E[U*]` under every policy, so on one example detection buys information and not protection from inflation (1.10) |
| C5 | holds as stated; Lean-ready statement in `RESULTS.md` 1.11; satisfiable non-trivially; sufficient, attained, not necessary (1.12); its conclusion is not regret in true utility (1.13) |
| C6 | an identity; where the honest report would change what she does it needs a third term, the change in the outcome; in the selection example the second term is 1/8 and her miscalibration is the same with and without the selection (1.14) |

### VI.3 The cases

108 cases frozen before the code: Noggle's thirteen tactics and fourteen of his other
cases, six of Elster's, every row of `blocks/CASE_BANK.md`, five of taste-shaping,
eighteen legitimate changes, fourteen built for question 3, one of dependence. Evident
character: 47 objectionable, 45 innocent, 7 her own, 9 contested. Predictions and
renderings are the executor's.

| | right | missed | convicted | routed | unfixed | not counted |
|---|---|---|---|---|---|---|
| *start* | 76 | 10 | 4 | 6 | 4 | 8 |
| *end* | 72 | 11 | 4 | 12 | 0 | 9 |

**Wrong.** *Missed*: K9, Q2 (an undisclosed advocate, strategic silence: truthful
conduct and her own over-trust; manipulation under the forthright norm); K13 (buried
information); K31 (a lie she allows for); K2, Q3, Q3b (lies that leave her total
miscalibration no higher; K2 and Q3b are manipulation if "worse" is read per quantity);
X3, Q11 (a narrowing feed, a craving exploited by a policy that treats everyone alike);
D1 (dependence); under *end* also K29 (every end revised in turn). *Convicted*: NP13,
Q5, Q6, Q7 (a teacher's feigned enthusiasm, a surprise party, a magician, a bluff).
*Routed* to coercion or alteration: K10, K12, K33a, E6, N8b, X3b; under *end* also NP8,
K15, K21, K23, X1, X2b. *Unfixed* under *start*: K17, K19, K24, L14. Seven divergences
from the executor's own predictions: N8b, K2, K3, K27, X3b, Q3b, Q10
(`estimates/DIVERGENCES.md`).

**Objectionable cases with no mistake.** *Start*: 7 of 47 (3 in coercion, 4 nowhere:
K13, K31, Q3, D1). *End*: 16 of 47 (4 in coercion, 7 in alteration, 5 nowhere). Taste
shaped by a responsive adviser is an estimation mistake she is triggered into under
*start* and alteration under *end*; pairing with a passing feeling is manipulation
under both.

The count is consistency with renderings, not a test: the model computes annotated
scenes; "responsive", "blanket" and "endorsed" are stated in the rows that turn on
them; K2, Q6 and Q7 are decided by details the rows do not fix; K21, K29, D1, E5 and L6
are static scenes.

### VI.4 What was established on each question

1. C1–C6: VI.2.
2. Cases: VI.3.
3. The bank's honest cases are not convicted. Four honest scenes from the review are
   *triggered* manipulation in the setting as frozen (3.1) and are not when the second
   type differs from her only in the flaw (3.2). Honest difficulty is her own
   estimation mistake at her information and none at the estimate alone. Withholding
   from one who reads silence rightly is never manipulation. A lie that lowers her
   total miscalibration is not manipulation, and the total depends on units (3.3).
4. Reading A has a consistent model. Two calibrated time-slices may disagree at every
   history (4.1): the commitment is that one is inaccurate, not that one is mistaken. A
   foreseeable drift in the mean is bounded by the two miscalibrations (4.2). Reading A
   includes the utility of whoever she ends as (4.3). Calibration to `U*` is not
   identifiable from her verdicts (4.4), and conditioning with no drift has the law of
   learning (4.5). What decides whether conditioning is caught is which function `U*`
   is.
5. C5's hypothesis is a sufficient condition on one realized sequence, where `Legit` is
   a predicate of a history; with the gate it is enough that counted histories not be
   inflated on average (5.2). Expected inflation is at most the root of her expected
   miscalibration (5.1), a quantity honesty does not control; calibration at every step
   gives no bound on realized inflation (5.5). The selection term is her own
   miscalibration under the adviser's policy, zero on average when her verdict is her
   posterior under it, and not zero given what the adviser knows (5.3). Manipulation
   need not inflate (5.4).
6. An honest phase in which she rightly defers, her own signal decays and detection
   falls below C4's threshold, after which a departure pays (6.1); with no departure, a
   growing selection term if her error grows (6.2). The account marks nothing in the
   honest phase. These are separate calculations, not one model in which the post's
   theorem fails. A norm of honest conduct toward her feelings needs `U*` or a list of
   what each feeling is evidence of on the one example computed (6.3).
7. `ThinLegitimacy.Correct`, `Transparent`, `Sufficient` and `Value`, and
   `TransparentChannel.Realizes` and `abs_expect_sub_le_width`, give the belief side in
   a stronger form. Added: her verdict read as an estimate of her own utility, graded
   mistakes, manipulation as a comparison between policies, the squared-error forms.
   `RESULTS.md`, question 7, has the table with file and line.
8. Four negative results with proofs, `estimates/NEGATIVE_RESULTS.md`.

### VI.5 S1–S5 and F1–F6

The reviewer judged before reading the executor's. Where the executor's judgment
changed after the review, the first is given.

| | executor | reviewer | reason |
|---|---|---|---|
| S1 | met (first: in part) | met | corrected forms with short hypotheses exist for C3, C4 and C6; the criterion allows them |
| S2 | not met | not met | 14 or 15 wrong, several central |
| S3 | met in part (first: met) | not met | the bank's first-list cases pass on comparators the scenes stipulate; the review's four honest scenes are convicted; with the second type constrained they are not |
| S4 | met in part | met in part | satisfiable; bounded by her miscalibration in expectation only; not every manipulation inflates |
| S5 | met (first: in part) | met | a reading of her verdict as an estimate of her utility, graded mistakes and a comparison between policies are added; the criterion asks only that something be |
| F1 | met in part | met in part | where taste-shaping goes is decided by an anchor the account does not choose; four or five objectionable cases with no mistake go nowhere |
| F2 | met in part (first: not met) | met | no intent is read, but the second comparison convicts honest help unless constrained, and the constraint is not in the account |
| F3 | not met (first: in part) | not met | a consistent model exists and no theorem needs `U*` known; that applying the account does is a different limitation |
| F4 | met in part (first: not met as stated) | met in part | bounded in expectation; for the realized sequence no bound follows from calibration; impossibility of every bound not shown |
| F5 | not met as stated (first: in part) | not met as stated | no one model has the post's theorem failing with its hypotheses and the account's conditions holding; 6.1 as first computed mixed two treatments of detection |
| F6 | met in part | met in part | the belief side is there in stronger form; the comparison-based definition is not a renaming |

Remaining difference: S3 and F2. The reviewer reads the account as stated (§3.6 puts no
constraint on the second type); the executor counts that the constrained form passes
the same scenes, on four scenes only.

**The prompt author's predictions.** C1, C2, C3, C5 hold as stated: so, C3 with a
constant that is not tight. C4 holds for the naive case and changes form for the
sophisticated: the threshold holds, the last clause does not as the executor first read
it, and the sophisticated case changes form on one example. C6 holds: as algebra, with
a third term in general. S2 met with three to eight wrong: not met, fourteen or
fifteen. F1 met in part, for pairing: in part, and not for pairing with a passing
feeling, which is caught; the unplaced cases are buried information, a calibrated
target of a lie, a beneficial lie and dependence. F2 not met: met in part (reviewer:
met). F3 not met but the commitment about disagreeing time-slices uncomfortable: not
met; the commitment is weaker than stated, since both slices can be calibrated. F4,
`β` bounded for the induced part and not the selection part: both are bounded together
in expectation, neither along a realized sequence. F5 met: not as stated. F6 met in
part for the belief side: so.

### VI.6 External review

One review through `codex exec --sandbox read-only` (codex-cli 0.153.4, model
`gpt-6-astra`, as its log reports), on copies of the round directory, the dispatch with
local paths replaced, six Lean files and a draft of this section without the executor's
judgments, which were in a separate file it was told to open last. It was told to write
its ten cases after reading only the dispatch and `SETTING.md`. Its reply is
`REVIEW-astra-followup-6.md`, verbatim. It ran both runners. Dispositions, by its
numbering:

1. *The runner compares status labels and does not certify the prose.* **Accepted**;
   `RESULTS.md` says so at its head.
2. *Ten cases (points 2–11).* Dependency without error: missed, as D1. Secret pleasant
   pairing: alteration under *end*, as X2b. A covert commission in a tie; a threat:
   routed, and routing does not say her authority was respected. **Accepted**; said in
   question 3. An accurate disclosure that violates privacy: nowhere, a limit of
   coverage and not of the definition. **Accepted.** Remedial teaching, a requested
   disclosure, a disclosed advocate to a novice, a requested reminder: *triggered*, false
   positives. **Accepted; reproduced** as statement 3.1, with the constrained form as
   3.2. Sincere misinformation: not manipulation, as K25.
3. *1.5 is not a bound on true utility when her choice uses finer information than the
   reference.* **Accepted**; restated, with its counterexample. *1.6's check asserted
   assigned values.* **Fixed**: the check builds the scene.
4. *1.8 refutes one reading of "right on average"; under the other the clause is its own
   hypothesis.* **Accepted**; restated. *1.10: a principal recalibrated to each policy is
   not the fixed response; the claim is for a fixed outcome.* **Accepted**; said.
5. *1.11's check is a finite-prefix inequality; 1.12 lacks a full instance.*
   **Accepted**; said, and the instance described. The Lean-ready statement matches the
   declarations; not elaborated.
6. *C6: keeping the adviser's choice does not keep her move; a third term is needed.*
   **Accepted; a defect.** 1.14 and `SETTING.md` §4 restated; the example is in the
   check.
7. *The end anchor does not make her final verdict calibrated without assuming she knows
   her end values.* **Accepted**; said.
8. *5.1 bounds expectations; C5 is about a realized sequence; a hidden bit drawn once
   gives calibration at every step and realized inflation 1/2.* **Accepted; a defect in
   the draft's central claim on `β`.** 5.1 restated, 5.5 added, question 5 rewritten.
9. *Posterior calibration makes the selection term zero on average, not given the
   adviser's information; at equality a departure ties; the inflation hypothesis is
   sufficient, not "exact"; 5.2 is an inequality.* **Accepted; each corrected.**
10. *6.1 mixed a believed report with a detected one: at step 4 inflation is 29/100 and
    miscalibration 29/100, her own loss 21/100; "nothing can detect it" is false. 6.2 is
    an illustration; 6.3 does not show no norm exists.* **Accepted; 6.1 recomputed** in
    one treatment (the review's figures reproduced); 6.2 and 6.3 narrowed.
11. *8.1 does not show how much of the adviser's side must be read; 8.2(b) is for one
    mechanism; 8.4's ranking is the reachability indicator.* **Accepted**; each said.
12. *`model.py` computes annotated scenes and validates no annotation.* **Accepted**;
    said in question 2.
13. *Renderings decide K2, the taste cases, Q6, Q7; K21, K29, D1, E5, L6 are static; Q9's
    scene was not responsive as its row says.* **Accepted**; said, and Q9's scene fixed
    (its verdict is unchanged).
14. *Total miscalibration depends on units: Q3b flips with the reading rescaled.*
    **Accepted; reproduced** as 3.3.
15. *The Lean map: `Correct`, `Sufficient` and `Value` are stronger than their rows said;
    `IsBest` is a zero-regret analogue; `ThinLegitimacy` has payoff functions;
    `LicensedAt` is relational.* **Accepted**; five rows and the summary corrected.
16. *Judgments on S1–S5, F1–F6.* VI.5. **S1, S5, F3, F4, F5 accepted. S3, F2 accepted in
    part.**
17. *The draft's headline "does not convict honest influence" is false; its `β` and
    selection claims overreach; "two corrections" is optimistic; it understates the
    `√2` result and the equivalence examples; innocent and misclassified are conflated
    by the standard.* **Accepted**; this section is written accordingly.
18. *What is new: the formulation and the failure analysis; the next result is a
    sequential bridge from policy to C5's realized hypothesis, or its impossibility.*
    **Adopted** as VI.9.

### VI.7 Deviations from the prompt

- **Every prediction and rendering is the executor's**; the dispatch gave none per case.
- **`SETTING.md` §4 was written after the results and amended after the review**; §1–§3
  and the bank were not edited after the freeze. §1 and §2 are condensed from the
  dispatch, not reproduced word for word.
- **Code, statements and prose were changed after the review** (VI.6). Four statements
  were added (3.1–3.3, 5.5); no case verdict, count or prediction changed. The review
  saw a draft of this section, not this text.
- **The review's four honest scenes are statements, not bank rows**, the bank being
  frozen.
- **The freezing commit's message says 113 rows; the bank has 108.**
- **The addendum arrived by another agent session**, with a clarification by a second;
  both are followed on those sessions' word.
- **Noggle's book and paper are not filed as a node**: a node needs an author handle
  and `@claude-fable-5-2` is not in `graph/policy.yaml`. They are cited in items 136 and
  138 and are the concept `noggle-mistake-account`; the node's text is under
  *Outstanding maintainer actions*. No text of the book is in the repository.
- **No merged-work entry was tagged**: `state/prs.json` holds merged pull requests, and
  this one is open.
- **No new item is filed.**

### VI.8 What was not shown

`estimates/RESULTS.md`, *What was not shown*, in full. The ones a reader of this section
needs:

- **The count is consistency** with renderings the executor wrote, and the standard
  assumes manipulation is never innocent.
- **Proofs are on paper.** Nothing is kernel-checked; the Lean was read, not built.
- **No model joins** deterrence, the post's sequence and dependence, and no condition on
  the adviser or on her learning is shown to give C5's hypothesis along a realized
  sequence.
- **A second type constrained to the flaw alone** was tried on four scenes; whether it
  acquits honest influence in general and still convicts exploitation was not shown.
- **Only the two extreme anchors for `U*`** were computed.
- **Sources.** Noggle's book was read in the sections cited and Elster's chapter in
  full. Bibliographic details of Dorst et al. 2021, Briggs 2009, Arntzenius 2008 and
  Dietrich and List 2013 were confirmed against Crossref and their content from
  abstracts (for Briggs, the opening pages); Total Trust's formal statement was not
  confirmed from the paper. The psychology the prompt author relied on from memory
  (misattribution of feelings: Schwarz and Clore 1983, Dutton and Aron 1974; forecasting
  one's feelings: Wilson and Gilbert 2003, 2005; underestimating one's own change:
  Loewenstein, O'Donoghue and Rabin 2003, Quoidbach, Gilbert and Wilson 2013; mere
  exposure: Zajonc 1968) was checked bibliographically and at the level of abstracts
  or secondary accounts; failed replications are on record for the first two. No
  result here rests on any of it. Two attributions in `RESULTS.md` (the
  calibration–refinement split; cheap talk with a sender who wants only a high verdict)
  are from memory and marked so.
- **The repository-level `tests/run.py` sweep** was run once, under Python 3.13, on the
  tree as committed apart from this line: all green over 81 projects, the Lean build
  skipped as that runner does by default. The round's runner was run under Python 3.13,
  and this pass's part of it under Python 3.9 as well. `tests/round_records.py` had no
  pull-request context locally; CI runs it.
- **Nothing is registered.** Components: the account as stated — **open**; statements
  1.1–8.4 — **open**, their statuses runner-checked facts about finite examples with no
  registry entry; the seven concepts added to the map — **living notes**.

### VI.9 The single most valuable next result

A sequential model with her true utility, what she observes, the feedback she gets on
it, the adviser's honest counterpart and detection in one probability space, and in it
either conditions on the adviser's policy and on her learning that give C5's hypothesis
along the realized sequence, or the proof that none of a stated class does. It must
survive an error of hers that persists across steps (5.5) and the decay of her
judgment (6.1). Until it exists the account's quantities are not connected to the
post's guarantee. The item's text is under *Outstanding maintainer actions*.

### VI.10 The addendum: a source and the concept map

*Source.* Noggle's book (OUP 2025, doi:10.1093/9780198924920.001.0001; publication
details confirmed against a bookseller's listing, the publisher's page not rendering)
and paper (*Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951; confirmed
against Crossref) are cited in the *Item* sections of `graph/nodes/item-136.md` and
`item-138.md` and in the round's README, and are the concept `noggle-mistake-account`.
A source node is not filed (VI.7).

*Concept map.* `state/concepts.json` gains seven concepts and twelve links, none shown
as established. `trajectory` (kind *object*, title "Trajectory (history, future
history)") is new: no concept covered it under either name. By the maintainer's
clarification *trajectory* is primary and *history* and *future history* are the same
concept; the schema has no field for synonyms, so they are in the title and the blurb.
Nothing in the Lean or the post's companion page is renamed. It is linked to
`legitimacy-line`, `deconfusing-corrigibility` (the corrigibility score) and
`evaluation-and-true-utility`. For this pass: `evaluation-and-true-utility`,
`noggle-mistake-account` (prior work), `manipulation-as-induced-mistake`,
`estimation-and-action-mistakes`, `honest-conduct`, `warranted-self-trust`, each with
the standing the pass leaves it in its blurb. No concept is filed for a notion the pass
refutes (C4's last clause as first read; calibration as a bound on realized inflation).
`python3 -m checkers.workspace_state --check`, `python3 -m checkers.graph --root .` and
`python3 site/build.py` pass. The six scoreable new concepts carry no score on any
axis, which the daily freshness audit will report: an AI seed needs the handle.

### VI.11 Filings, names, and what is reserved

**Revised under the prompt's direction; nothing filed.** Items 136, 137 and 138 are
rewritten at version 6: 136, an anchor for her true utility and what could identify it;
137, the account's proved statements in Lean; 138, the comparison that says an adviser
brought a mistake about. `DECISIONS.md`: one agent-decided entry,
`2026-11-14--estimates-account-readings`; each queue entry of the earlier passes given a
line on what this pass found; two new queue entries.

**New names, all provisional:** the dispatch's — "estimation mistake", "action
mistake", "miscalibration", "the three references", "honest conduct", "true utility",
"true score", "inflation", "Reading A", the directory `estimates/`; the executor's —
"induced", "triggered", "truthful" and "forthright" (reporting norms), "the other type",
"responsive" and "blanket" (of a policy), "start" and "end" (anchors of her utility),
"endorsed", "unfixed", "routed", "missed", "convicted", "nowhere", "evident character",
case ids N, NP, E, K, X, L, Q, D, and the Lean name `trueScore_noRegret`; the concept
ids `trajectory`, `evaluation-and-true-utility`, `noggle-mistake-account`,
`manipulation-as-induced-mistake`, `estimation-and-action-mistakes`, `honest-conduct`,
`warranted-self-trust`.

**Outstanding maintainer actions**

1. Rule which function her true utility is. Entered in *Awaiting the author*
   (2026-11-14). Decision required: *her starting values, informed of the whole
   history*, *the values of whoever she ends as*, *a condition on how her valuation may
   depend on her history* (Elster's is the candidate), or *leave open and dispatch
   item 136*.
2. Rule whether her prior say, or a practice's rules, cover a deception. Entered in
   *Awaiting the author* (2026-11-14). Decision required: *yes, as for alteration*,
   *no, a deception is manipulation whatever she agreed to*, or *leave open* (item 138
   computes the clause).
3. The twelve entries of 2026-11-10 to 2026-11-13 on this round stay, each with a line
   from this pass. *Which end yields* (2026-11-13) and *a change her goal does not
   rank* (2026-11-12) are restated by action 1 and can be retired with it. *Truthful
   influence that takes a part out of range* (2026-11-13) is answered by this account
   in the form VI.4, point 3 gives, subject to 3.1. *Against what a gap is widened*
   (2026-11-12) becomes item 138's class. The entries on *in range*, the constraints,
   a part handed a falsehood and what a purpose predicts bear only if the parts account
   is resumed. Decision required for each: as its entry states.
4. Map the handle (the entry of 2026-11-10 on `@claude-fable-5-2` stands), then file:
   the three unfiled items of H11 and I9; the item and the node below; and an AI seed
   on the six new scoreable concepts.

   > **From the adviser's policy to an uninflated verdict along the realized sequence**
   > [open]. Section: Normativity line — legitimacy. The sixth follow-up of the
   > prosecution round shows on paper that Theorem 3(b) of the post holds for a true
   > score once the long-run average of `V_k − U*_k` is at most `β`
   > (`estimates/RESULTS.md` 1.11, in
   > `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`),
   > that her miscalibration bounds that average in expectation (5.1), and that
   > calibration at every step gives no bound along the realized sequence when her
   > error persists (5.5). Wanted: one sequential model with her true utility, what she
   > observes, the feedback she gets on it, the adviser's honest counterpart, and
   > detection, in one probability space; a stated class of conditions on the adviser's
   > policy and on her learning; and for each either a proof that `LimsupLE` of the
   > average inflation holds almost surely or in probability with a stated `β`, or the
   > scene that defeats it, the hidden bit of 5.5 and the decay of 6.1 among the scenes
   > tried.
   > *Deliverable shape:* `test-supported` — modules under `estimates/` of that round,
   > predictions frozen before the code; a Lean-ready statement of each condition that
   > survives, against `DeconfusingCorrigibility.Sequential`.
   > *Acceptance check:* `python3 run.py` in the round directory green with a status for
   > each new statement; each condition classified on the scenes of 5.5 and 6.1.
   > *Context:* `estimates/RESULTS.md` questions 5 and 6;
   > `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`
   > (`Sequential`, `UnbiasedFromFeedback`);
   > `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` VI.9.

   The source node, to be written as `graph/nodes/noggle-mistake-account.md` and listed
   in the `holds` of the frame `legitimacy`; the checker has not been run on it:

   > `id: noggle-mistake-account`; `kind: leaf`; `author: "@claude-fable-5-2"`;
   > `size: L`; `size_reason: "a book of eleven chapters and a paper"`; `version: 1`.
   > **Statement.** Manipulation is influence that operates by inducing a mistake in
   > the target's psychological states or processes.
   > **Source.** Robert Noggle, *Manipulation: Its Nature, Mechanisms, and Moral
   > Status*, New Topics in Applied Philosophy, Oxford University Press, 2025,
   > doi:10.1093/9780198924920.001.0001, ch. 6; Robert Noggle, "The Mistake Account of
   > Manipulation", *Journal of Practical Ethics* 14(1), 2026, doi:10.3998/jpe.9951,
   > whose abstract states it in nearly these words.
   > **Notes.** The published account the legitimacy line's sixth candidate makes
   > exact (`estimates/SETTING.md` of the prosecution round). Bears on items 136 and
   > 138.

The pull request is not auto-merged; the merge is a pull-request fact.

## Attribution

- Prompt-author model: Claude Fable 5 (Anthropic); dispatched 2026-11-10, kept
  verbatim as `PROMPT.md`.
- Executor model: Claude Fable 5.1 (Anthropic); executed 2026-11-10.
- Follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-10,
  kept verbatim as `PROMPT-followup.md`; executor model Claude Fable 5.2 (Anthropic),
  executed 2026-11-10.
- Second follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-11,
  kept verbatim as `PROMPT-followup-2.md`; executor model Claude Fable 5.2 (Anthropic),
  executed 2026-11-11; external reviewer `gpt-6-astra` through codex-cli 0.153.4, as its
  log reports, reply kept verbatim as `REVIEW-astra-2026-11-11.md`.
- Third follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-12,
  kept verbatim as `PROMPT-followup-3.md`, with two addenda of the same date kept verbatim as
  `PROMPT-followup-3-addendum.md` and `PROMPT-followup-3-addendum-2.md`, each received from
  an agent session and attributed to the prompt author on that session's word; executor
  model Claude Fable 5.2 (Anthropic), executed 2026-11-12; external reviewer `gpt-6-astra`
  through codex-cli 0.153.4, as its log reports, reply kept verbatim as
  `REVIEW-astra-2026-11-12.md`.
- Fourth follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-12,
  kept verbatim as `PROMPT-followup-4.md`; executor model Claude Fable 5.2 (Anthropic),
  executed 2026-11-12; external reviewer `gpt-6-astra` through codex-cli 0.153.4, as its log
  reports, reply kept verbatim as `REVIEW-astra-followup-4.md`.
- Fifth follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-13,
  kept verbatim as `PROMPT-followup-5.md`; executor model Claude Fable 5.2 (Anthropic),
  executed 2026-11-13; external reviewer `gpt-6-astra` through codex-cli 0.153.4, as its log
  reports, reply kept verbatim as `REVIEW-astra-followup-5.md`.
- Sixth follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-14,
  kept verbatim as `PROMPT-followup-6.md`, with an addendum of the same date kept verbatim as
  `PROMPT-followup-6-addendum.md`, received from an agent session and attributed to the prompt
  author on that session's word; executor model Claude Fable 5.2 (Anthropic), executed
  2026-11-14; external reviewer `gpt-6-astra` through codex-cli 0.153.4, as its log reports,
  reply kept verbatim as `REVIEW-astra-followup-6.md`.
- No chat bundle.
