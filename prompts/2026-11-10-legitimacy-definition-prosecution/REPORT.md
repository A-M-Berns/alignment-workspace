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
- No chat bundle.
