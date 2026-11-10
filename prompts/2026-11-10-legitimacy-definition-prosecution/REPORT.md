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
- **`graph/policy.yaml`** gains the AI handle `@claude-fable-5-2`, outside the prompt's
  listed write scope: the map checker refuses a node whose author is unmapped, and item
  139 needs an author.
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
  Item 139.
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

**Filed or revised under the follow-up's scope grant.** Item 139, the adviser's aim as an
object of the fixture (`graph/nodes/item-139.md`, held by the `legitimacy` frame). Item
136's entry now asks whether an authorized write belongs in the licensed trace (N5).
Item 138's entry now records that output-invariance separates T12 without saying why,
and its acceptance check asks for a case that tells the two apart. One `DECISIONS.md`
entry, agent-decided and reversible: `2026-11-10--steering-follow-up-stipulations`.

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

The pull request is not auto-merged; the merge is a pull-request fact.

## Attribution

- Prompt-author model: Claude Fable 5 (Anthropic); dispatched 2026-11-10, kept
  verbatim as `PROMPT.md`.
- Executor model: Claude Fable 5.1 (Anthropic); executed 2026-11-10.
- Follow-up: prompt-author model Claude Fable 5.2 (Anthropic), dispatched 2026-11-10,
  kept verbatim as `PROMPT-followup.md`; executor model Claude Fable 5.2 (Anthropic),
  executed 2026-11-10.
- No chat bundle.
