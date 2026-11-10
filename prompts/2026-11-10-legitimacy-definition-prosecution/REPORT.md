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

## Attribution

- Prompt-author model: Claude Fable 5 (Anthropic); dispatched 2026-11-10, kept
  verbatim as `PROMPT.md`.
- Executor model: Claude Fable 5.1 (Anthropic); executed 2026-11-10.
- No chat bundle.
