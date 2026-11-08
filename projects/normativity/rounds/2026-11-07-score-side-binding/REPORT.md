# Report — where obligations bind: the score-side test, solvency as soundness, admission by standing

| | |
|---|---|
| Prompt author | Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-07 (`prompts/2026-11-07-score-side-binding/PROMPT.md`, verbatim); the follow-up of 2026-11-08 by the maintainer (`PROMPT-followup.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code; both runs |
| Base | `origin/main` at `73edb7de` |
| Dates | 2026-11-07; follow-up 2026-11-08 |

## Corrections and deviations (`AGENTS.md` §8)

- The dispatch places the eight-world model in `ThinLegitimacy.lean`. That file's §11 mentions
  an eight-world fixture in prose and exposes no world type or measure for it; the Lean
  witnesses there are two-world. The model is stated locally in `RobustWarrant.lean` with exact
  rationals, as the dispatch permits.
- The dispatch's `python3` is 3.9 on this machine, which cannot parse `checkers/graph.py`; every
  checker was run with `python3.12`, the version CI uses.
- The dispatch asks the round to "file the round's node". The map protocol has no node kind for
  a round: a round appears only as `work` pointers of kind `round` on the nodes standing for
  its results and items. The round filed those pointers and no node of its own, and the gap is
  item F10.
- The dispatch names `DecisionComponent.permWeight` / `cgate`, or `BRIACorrigibility.evalOf`,
  as the decision component for the charge. The score-side gate is `GatedChoice.softGate` on
  the charged scores with the run's own `P₁.pref`, `τ`, `δ`. Reason: the question is whether the
  *same* reversal obtains, and the run's gate is `P₁.gate = softGate (P₁.scoreR ·)`; `cgate`
  gates through a permission ramp with its own thresholds `θlo`, `θhi` and would change the
  gate's form, so the comparison would no longer be against the run's gate, and `evalOf` is a
  scalar evaluation (a bid less `ϖ` per priced event) with no menu or gate. Its shape — the
  priced event subtracted from the score — is what the charge takes, inside the run's gate.
- The follow-up changed the statements relative to the first run: `same_question_two_realizations`,
  `before` and `after` take the hypothesis `Assessed` and conclude also that acting is assessed
  a shortfall at the dates in question; the statement of record of `robust.eight-world-strengths`
  is `robustStrength_both` (the first run registered `robustStrength_all` and the bridge credited
  it with both strengths); the short name of `solvency.conflict-names-suspects` is narrowed; item
  128 is open, not closed. No class changed.

## 1. The score-side test

**Classification.** Every row the October bundles enforce, by what settles it:

| row | source | what settles the sentence | class | about |
|---|---|---|---|---|
| `P(X) ≥ 4/5` | `occP`, premise | the deductive process pins `X` (date 3) | deductive | credence |
| `P(X∧A) ≥ 3/4 · P(X)` | `occA`, applicability | the process could pin `X∧A`; it does not in the fixture | deductive | credence |
| `P(X∧A∧Y) ≥ 2/3 · P(X∧A)` | `occS`, strength | the process pins `X∧A∧Y` false (date 8); rebuttal | deductive | credence |
| `P(Z) ≥ 3/4` | `occZ`, premise | the process could pin `Z`; it does not | deductive | credence |
| `P(X∧A) ≤ P(X)`, `P(X∧A∧Y) ≤ P(X∧A)`, `P(X∧A∧Y) ≤ P(Y)` | `coh₁..₃` | consequences of the logic | deductive | credence |
| pins on `X`, `Y`, `X∧A∧Y` | the settlement | the process | deductive | credence |
| `SeedStatics.Form` as a type: `premise`, `applicability`, `strength` | — | a form names sentences of the fragment, which the process settles | deductive | credence |

No row is about conduct, and no row is assessed: the forms have no constructor for either.
The obligation added — **refrain while live**: acting on the conclusion is a shortfall at any
date at which the originating obligation's account carries a live leaf — is of class *assessed*
and about conduct. `ShortfallAt n` reads the fate off the state accounted at `n`
(`stateAt n`, which is `state₀` at every date of the run); `shortfall_assessed`: live
throughout. The obligation carries one shortfall sentence per date (`RefrainWhileLive`), and
the hypothesis `Assessed O v` says the valuation `v` settling those sentences makes
`O.shortfall n` true iff `ShortfallAt n`. `Assessed` is typed: nothing derives it.

**The two realizations on the same market.** `scoreSide O ϖ` stores the rebuttal run's
schedule with the obligation and a charge `ϖ`; its gate is `GatedChoice.softGate` on `P₁`'s
scores less `ϖ` times the market's price of the date's shortfall sentence on the acting option
(`chargedScore`, `scoreGate`). Proved:

- `bundle_unchanged`, `market_unchanged`: the bundle is `(NB n).bundle` and the market is
  `WB.market DP` — by construction, since `scoreSide` stores `WB`; `market_unchanged` is `rfl`,
  a design fact (the charge adds no trader) and not a result. `no_conduct_row`: the one row
  *refrain* was compiled to, `P(X∧A∧Y) ≤ 1/3`, is held at no date, by the constants of the
  held rows (`−4/5, 1/5, 0, −3/4` for the sub rows, `0` for coherence, `0, ±1` for pins). It is
  not a classification of every row on conduct.
- `after`: under `Assessed`, at date 9, for every `ϖ ≥ 0`, acting is assessed a shortfall and
  the gate refrains with certainty — the charge only lowers an acting score the pin already
  holds below `τ`.
- `before`: under `Assessed`, at date 4, with `ϖ · price(shortfall 4) ≤ 19/240`, acting is
  assessed a shortfall and the gate acts with mass at least `24/25`. The enforced strength and
  applicability rows hold `P(X∧A∧Y) ≥ 1/2 − 1/240`, which leaves `19/240` above `τ + δ = 5/12`;
  the refraining score is at most `1/3 + 1/400`. The obligation binds through the charge and
  nothing else.
- `override`: when `ϖ · price` reaches the acting score's room above `τ`, the act's weight is
  `0` — and no price has moved.
- `same_question_two_realizations`: the run's `same_question`, `before` and `after` together.
- `strength_row_necessary`: `p₀ = (1, 3/4, 0, 0, 3/4)` lies in the cube, satisfies every date-4
  row except the specialized strength row, violates that one, and at `p₀` the charged gate puts
  mass `0` on acting and `1` on refraining for every `κ ≥ 0`; `scoreGate_eq_gateAt` says the
  gate at a price vector is the realized gate's form. The witness that `before` cannot drop the
  strength row: the bundle without it is satisfied by a point at which the decision differs.
- `conduct_on_prices_conflicts`: the conduct row appended to the date-4 bundle leaves an empty
  region, by the three-row certificate `conductCert` (strength row, `2/3` of the applicability
  row, conduct row; constant `−1/6`) through `conflict_sound`; a compiler returning it withholds
  the date. `conduct_on_prices_idle`: at date 9 every region point satisfies the conduct row.
  This is the chosen compilation of *refrain*; other compilations are not examined.

**Verdict: (b), as a conditional sufficiency result with a necessity witness.** Under `Assessed`
and the charge bound, the reversal obtains with no row on conduct enforced; it needs the
strength row (`strength_row_necessary`); the practical part is score-side and the belief part
is an epistemic warrant on prices. What (c) would have cost is proved beside it: on prices the
chosen row either collapses the date or adds nothing. The charge bound is satisfiable at every
market, since prices lie in `[0, 1]`: every `0 ≤ ϖ ≤ 19/240` meets it.

## 2. Solvency as soundness

**(a) The instantiation.** `WarrantSolvency.Schema`: a strength and, per instance, whether it is
undefeated and the settled truth of its consequent. `held t` is the strength on an undefeated
instance, `realized t` the consequent's truth. `Schema.bounded_iff_frequency`:
`(∀ n, −B ≤ liability realized held n) ↔ ∀ n, c · U_n − T_n ≤ B`, with `U_n` the undefeated
count and `T_n` the true consequents among them. The reduction of `WarrantForce`'s calibrated
day value to one unit per instance is the hypothesis `UnitPosition`, named on `solvent_iff` and
not derived; the calibrated enforcer's positions vanish when a row is satisfied, so the
hypothesis is not generally true of it. Witnesses: a consequent always true (bounded at
`B = 0`), always false (unbounded, through `systematic_outperformance_unbounded` with gap `3/4`).
**This is a renaming of the deference result**, `bounded_iff_not_outperformed` with
`h := realized`, `g := held`, plus the counting identity `outperformance_eq`; no new mathematics.

**(b) The conflict audit.** `exists_violated_suspect`: for any `FarkasCert` and any price
vector, some positively weighted row is violated. `no_conflict_of_sound`: rows all valid at one
point admit no valid certificate. `suspect_in_bundle`: against a bundle, at every cube point
some positively weighted *bundle* row is violated there, the cube rows holding in the cube —
the row may differ from point to point, and no single row is shown violated everywhere; also on
a `NormState` (`suspect_in_normState`). `unique_suspect`: all suspects but one holding at a point
convicts the one there. What excludes a conflict certificate is validity of all its rows at one
point, not solvency: two contradictory rows each enforced on one instance have bounded cumulative
liability. Reading a conflict as a mis-admission needs the premise that admission demands
validity at the point in question; the theorems do not supply it.

**(c) The eight-world fixture.** `RobustWarrant`: worlds `(q, s, ch)`, `μ` the product measure.
`valid_at_signal`: the row at `3/4` holds at the record `⊤` (`Pr(Y | A) = 3/4`, `posterior_signal`).
`invalid_at_contrary`: at the record `C` it fails (`Pr(Y | A ∧ C) = 3/5`; `3/4 · 5/12 > 1/4`). On
the three-coordinate embedding (`A`, `A∧Y`, `C`) the settlement recording the challenge pins
neither antecedent nor consequent, so `settleOutcome` keeps the form and `settleForm`
contributes the specialized row (`kept_under_challenge`); the quiet docket undercuts nothing
(`not_undercut`); the repository's grounded survivor rule `Grounds.survivors` applied to the
warrant's grounds `[occ]` at that record keeps it (`survives_challenge`); and the contributed row
is violated by her posterior (`contributed_row_invalid`). The opposing warrant at `2/3` makes the
rows infeasible (`naiveCert`, `naive_conflict`) although `3/5` is determinate. **The robust
reading** (`Robust`, provisional): `Pr(Y | A ∧ E) ≥ c` for every `E` in a declared extension set
`U`; `robust_sound` is its soundness lemma. `robustStrength_both`, the statement of record:
`3/5` over `Uall = {⊤, C, ¬C}` and `3/4` over `Udef = {⊤, ¬C}`. The extension sets are declared
inputs; no theorem derives them from `Grounds.survivors` or any defeat mechanism.
`against_robust_iff`: the opposing warrant's robust strength is `2/5`; `robust_meet`: the robust
rows for and against meet at `3/5`.

This bears on the queue entries on M1 and M2 and does not reopen them; a sentence is added to
each. Item 113 (closed) and item 127 carry a note each; the `Form`-level rule is item 133.

## 3. Admission by standing

The types meet without adaptation. `AdmissionByStanding.admittedByStanding allocAt matter issuer`
has the protocol's `Admitted` signature: an occurrence is admitted at history `h` when
`((allocAt h).entry (matter o)).holder = issuer o`; `withStanding` replaces the one field. The
fixture is the witness's `state₀` rebuilt over the protocol with standing under `J₀` — two
matters, the first the principal's and the second (the `Z` warrant's origin) the reasoner's own
— and `entitlementS n` inhabits `Entitlement stateS (N n).grounds (fun _ _ => True)` at every
date with the admission clause discharged by the allocation (`admitted_by_allocation`,
`first_person_admitted`). Under `J₁ = J₀.withHolder 0 agent` the first obligation is not admitted
at any history (`reallocated_not_admitted`) and `reallocated_entitles_nothing`: over any
obligation state of that protocol no entitlement of the grounds traces an occurrence to it.

**The hypothesis package is inhabited.** `Initial` admits every exposed occurrence, and under
`J₁` obligation `0` is admitted at no history, so an initial exposure over `protocolS₁` can
expose only obligation `1`: `start₁` exposes it alone on one port, `initialS₁` and `stateS₁`
build the state, and `entitlementS₁ : Entitlement stateS₁ grounds (fun _ _ => True)` traces
every occurrence to obligation `1` — admitted under `J₁`, account live, `Expresses` total.
`witness_origin` applies the registered theorem to it; its conclusion there reads `1 ≠ 0`.

Of entitlement's four conditions at this fixture: **exposure** is content-free at `stateS`
(`start` exposes everything) and selects at `stateS₁`; **admission** carries content (the
allocation can withdraw it); **liveness** carries content (as before, `answered_not_entitled`);
**`Expresses`** remains typed and total. The allocation is constant in the history at the
fixture; the definition takes a history-indexed one. Of item 128's clause (a), the admission
half landed and the `Expresses` half did not; the item is open.

## The eight questions, per registered theorem

**`same_question_two_realizations`.** *Hypotheses:* `Assessed O v`; `0 ≤ ϖ`;
`ϖ · WB.market DP 4 (O.shortfall 4) ≤ 19/240`; the run's enforced dates. *Inhabited by:* any
`O` and any `v` making every `O.shortfall n` true (then `Assessed O v` holds, since
`ShortfallAt n` holds at every date), with `ϖ = 0`; and every `0 ≤ ϖ ≤ 19/240`, since prices lie
in `[0, 1]`. *Typed:* `Assessed`; the shortfall sentences' generability; whether the market
prices them well. *At the fixture:* act `≥ 24/25` at 4, refrain with certainty at 9, in both
realizations; acting assessed a shortfall at both dates. *Vacuous if:* `Assessed` had no model
— it has the one above. *Same theorem elsewhere:* the run's `same_question` is its first
conjunct. *Not shown:* that acting is adequate at date 4 under the obligation (the adequate set
is declared); that the sentences are generable; anything about a market other than `WB`.
*Reopens:* a change to `P₁`, the tolerance, or the rebuttal rule.

**`conduct_on_prices_conflicts`.** *Hypotheses:* none beyond the fixture. *Inhabited by:* the
date-4 bundle. *Typed:* which row *refrain* compiles to; `P(X∧A∧Y) ≤ τ` is the choice.
*At the fixture:* empty region, certificate constant `−1/6`. *Vacuous if:* the conduct row were
chosen weaker than the strength row's lower bound. *Same elsewhere:* `contraposition_blocked`
is the same shape at date 9 with the strength row kept. *Not shown:* that no other compile of
the obligation onto prices is consistent. *Reopens:* a different compile of *refrain*.

**`Schema.bounded_iff_frequency`.** *Hypotheses:* none beyond the schema. *Inhabited by:*
`Witness.alwaysTrue`, `alwaysFalse`. *Typed:* `UnitPosition`, the relation to the calibrated
trade. *At the fixture:* `−0 ≤ liability` for always-true; unbounded for always-false. *Vacuous
if:* no instance is ever undefeated (`U_n = 0`: both sides are `0 ≤ B`). *Same elsewhere:*
`DecisionComponent.bounded_iff_not_outperformed`; this is it renamed. *Not shown:* the
summability condition of item 61 over the compiled force request and the live-world deficit;
anything about the calibrated trader's actual day value. *Reopens:* a proof or refutation that
the calibrated trader's day value is a unit position.

**`suspect_in_bundle`.** *Hypotheses:* the certificate's rows are allowed; `x` in the cube.
*Inhabited by:* `conductCert` against the date-4 bundle with the conduct row. *Typed:* which
point is the true posterior; whether admission demands validity there. *At the fixture:* at
`wit 4` the violated suspect is the conduct row. *Vacuous if:* `m = 0` — excluded, since
`const_sum` needs a negative sum. *Same elsewhere:* `conflict_sound` is its contrapositive
without the suspect. *Not shown:* one row violated at every point; which suspect was
mis-admitted. *Reopens:* a change to `Bundle.Allowed`.

**`robustStrength_both`.** *Hypotheses:* none beyond the model. *Inhabited by:* the model.
*Typed:* the extension sets `Uall`, `Udef`, declared. *At the fixture:* `3/5` and `3/4`.
*Vacuous if:* an extension set were empty, excluded by `Uall_nonempty`, `Udef_nonempty`. *Same
elsewhere:* none in Lean. *Not shown:* a `Form`-level rule; that `Uall` or `Udef` is what any
defeat mechanism generates; agreement with `settleForm`; anything beyond eight worlds.
*Reopens:* item 133.

**`reallocated_entitles_nothing`.** *Hypotheses:* an entitlement's own fields over the protocol
under `J₁`. *Inhabited by:* `entitlementS₁` over `stateS₁`; `entitlementS` inhabits the positive
side at `J₀`. *Typed:* `Expresses`; the history-indexed allocation (constant at the fixture).
*At the fixture:* `origin o ≠ 0` for every `o ∈ grounds`; at the witness, `1 ≠ 0`. *Vacuous if:*
no obligation state of `protocolS₁` existed — `stateS₁` is one, and none exposes obligation `0`.
*Same elsewhere:* `answered_not_entitled`, with the allocation for the account. *Not shown:*
`authorized` against the account (128(b)); entitlement along an evolution (128(c)); that the
grounds could be entitled through origin `1` under an `Expresses` with content. *Reopens:* a
ruling that admission reads the receipts rather than the allocation.

## What this round does not establish

- The assessment interpretation of the shortfall sentences: `Assessed` is a hypothesis.
  Nothing shows that the market prices the sentences well or that they are generable (items 90,
  101 of the decision component), and no assessment process settles them in Lean.
- The strength row's necessity beyond the price-vector level: `p₀` conforms to the weakened
  bundle and reverses the decision, but no second market history realized by a logical inductor
  is built at it.
- That the calibrated warrant enforcer's day value is a unit position per instance:
  `UnitPosition` is a hypothesis; 2(a) is the deference identity under a name.
- Item 61's summability condition over the compiled force request and `D_t`: untouched.
- Any defeat semantics: `Uall` and `Udef` are declared, and `survives_challenge` says only that
  `Grounds.survivors` keeps the warrant on the grounds `[occ]` at the challenge record; no
  theorem relates the extension sets to that rule (item 133).
- Which suspect a conflict convicts, or one row violated everywhere: only that some positively
  weighted bundle row is violated at each cube point. That a conflict is a mis-admission needs
  admission to demand validity at that point.
- The reallocated witness exposes obligation `1` alone, which is the only shape an `Initial`
  over `protocolS₁` can take; the theorem's content at the fixture is that every entitlement
  that exists there traces to obligation `1`. Nothing about `authorized`, or about entitlement
  along an evolution.
- Whether acting is *adequate* at date 4 under the added obligation: the adequate set is
  declared, and the charge is a parameter.
- The exposure rule: a proposal on the wiki and in the queue, not a result.

## External review

GPT-6 Astra (OpenAI), via `codex`, reviewed pull request #140 at `d3d3542e` on 2026-11-08;
its text is `prompts/2026-11-07-score-side-binding/REVIEW-astra-2026-11-08.md`, verbatim. The
maintainer checked its findings against the Lean source and fixed the dispositions in
`PROMPT-followup.md`.

| finding | disposition |
|---|---|
| Outcome (b) promoted without a strength-necessity witness | fixed, `f7e76b44`: `strength_row_necessary`, `scoreGate_eq_gateAt` |
| The shortfall sentence formally disconnected from assessment; `ShortfallAt` ignores its date | fixed, `f7e76b44`: one sentence per date, `stateAt`, `Assessed`; the theorems take it and conclude the assessment |
| `market_unchanged` is `rfl` and not a result; `no_conduct_row` shows the chosen row absent, not every conduct row | fixed, `f7e76b44`: docstrings, report and wiki say so |
| The charge bound omitted from the categorical verdict and the wiki; the "vacuity" scenario impossible | fixed, `f7e76b44`: the `19/240` bound travels with the `24/25` figure; the scenario is cut |
| `conduct_on_prices_conflicts` is for the chosen compilation only | fixed, `f7e76b44`: stated in the docstring and above |
| `UnitPosition` not generally plausible for the calibrated enforcer | already declared as a hypothesis; the report now says why it is not generally true |
| "A conflict among solvent rows cannot occur" is false; `suspect_in_bundle` is every-point-some-row; mis-admission needs an admission standard | fixed, `a3a50cc2`: wiki, registry short name and note, result nodes, item 133, Lean docstrings |
| No theorem applies `Grounds.survivors` to the eight-world fixture | fixed, `a3a50cc2`: `survives_challenge` |
| Declaring the challenge a defeater is a deletion no repository mechanism performs | the extension sets are declared inputs; said in the Lean header, the registry note, the spine and above |
| The robust bridge credits both strengths to a declaration proving `3/5` | fixed, `a3a50cc2`: `robustStrength_both` is the statement of record |
| `standing.reallocated-entitles-nothing` lacks a hypothesis-package witness | fixed, `49fd21ad`: `start₁`, `initialS₁`, `stateS₁`, `entitlementS₁`, `witness_origin` |
| Item 128 `closed` while only the admission half of (a) landed | fixed, `49fd21ad`: open, the note narrowed, the render regenerated |
| Report limitations omit the four gaps above | fixed, this commit: *What this round does not establish* |
| The `softGate` construction is an undeclared deviation from the named decision component | **disputed** as to novelty — `softGate` is the consolidation round's existing machinery, the run's own gate; the deviation from the named functions is declared above under §8 |
| `REPORT.md` corrects a `PRIORITIES.md` reference the dispatch does not contain | fixed, this commit: the correction is removed; the others were checked against the committed `PROMPT.md` |
| The exposition inventory and merge recommendation repeat earlier material | fixed, this commit: both cut |
| Commits omit the `Prompt-author-model:` trailer | **disputed** — `AGENTS.md` requires that trailer only where prompt author and executor differ; both are Claude Fable 5.1 here, and the `Model:` trailer and the pull request's attribution section carry it |

## Verification

First run, 2026-11-07, at `2733e03b`: `safe-lake.sh build Workspace` built `4099 jobs`;
`tests/audit_axioms.py` audited `3492 results across 112 files`; `tests/run.py` `ALL GREEN (80
project(s))`; `checkers.run` `79 entries, 1 adjudicated here`; `workspace_state --check` valid;
`wiki_state_bindings`, `wiki_links`, `wiki_refs`, `attention_render --check` clean; `checkers.graph`
`OK 2494 nodes, 2603 events, 2094 ranked units`. CI at `2733e03b`: all seven required checks
passed.

Second run, 2026-11-08, after the follow-up:

- `~/.claude/scripts/safe-lake.sh build Workspace`: `Build completed successfully (4099 jobs)`; the four revised modules compile with no `sorry`.
- `python3.12 tests/audit_axioms.py`: `AXIOM AUDIT: 3511 results across 112 files, all within ['Classical.choice', 'Quot.sound', 'propext']`.
- `python3.12 tests/run.py` (with `lean/.lake` set aside and the new files added): `ALL GREEN (80 project(s))`; `LEAN BUILD SKIPPED` as documented, the build above being the Lean verification.
- `python3.12 -m checkers.run`: `79 entries, 1 adjudicated here`; the six entries of this round `lean-proved`, adjudicated by the Lean gate, `robust.eight-world-strengths` now against `robustStrength_both`.
- `python3.12 -m checkers.workspace_state --check`: `WORKSPACE STATE: valid — 7 projects, 184 modern claims, 1 foundations, 180 foundation claims, 131 rounds, 52 terms, 144 priorities, 10 interface objects`, after `--write-handoff` regenerated the two views the verdict change had made stale.
- `python3.12 -m checkers.wiki_state_bindings`: `WIKI STATE BINDINGS: clean over 35 page(s); 3 binding(s) verified against the state emission`.
- `python3.12 -m checkers.wiki_links`: `WIKI LINKS: clean over 33 page(s) (links resolve; repository links are commit-pinned)`.
- `python3.12 -m checkers.wiki_refs`: `WIKI REFS: clean over 35 page(s); 327 reference(s) resolve`.
- `python3.12 -m checkers.attention_render --check`: `ATTENTION RENDER: the committed file equals the render (144 items)`.
- `python3.12 -m checkers.graph`: `OK 2494 nodes, 2603 events, 2094 ranked units; research first: the decision term (printed, not applied) favours vet hull-condition-total-trust (ranked unit 43), D 0.00016`; the same two warnings as the first run, neither this round's. Five result nodes whose Statement changed carry `version: 2`.

CI on pull request #140 after the follow-up: CI-SECOND-RUN

Claims whose status changed: none. Six claims registered, all `lean-proved`; the statement of
record of `robust.eight-world-strengths` is `robustStrength_both`.

## Items

Narrowed: 35 (fourth instance), 61, 128 (the admission half of clause (a); open). Noted: 113
(closed; the non-linear form it names), 127. Filed: 133 (the robust reading as a `Form`-level
rule), F10 (a research round has no node of its own on the map; `AGENTS.md` §14).

## Registrations

`scoreside.same-question-two-realizations`, `scoreside.conduct-on-prices-conflicts` (item 35);
`solvency.bounded-iff-frequency` (item 61); `solvency.conflict-names-suspects`,
`robust.eight-world-strengths` (item 133); `standing.reallocated-entitles-nothing` (item 128).
Listed and not registered: every other declaration of the four modules.

## Names, provisional

*refrain while live*, *shortfall sentence*, *assessed* (the hypothesis `Assessed`),
*score-side realization*, *charged score*, *score-side gate*, *conduct row*; *schema* (warrant
schema with timely-settling instances), *unit position*, *undefeated count*, *true count*;
*suspects*; *robust* (the robust reading), *robust strength*, *row valid at a record*;
*admission by standing*, *with standing*.

## Outstanding maintainer actions

1. **Rule on the exposure rule, or leave it a proposal** — `DECISIONS.md`, *Awaiting the
   author*, the 2026-11-07 entry (`open--exposure-rule-proposal`).
2. **Merge or decline the pull request**; auto-merge is off and the merge is the maintainer's.
3. The queue entries on M1, M2 and the entitlement liveness reading stand as before; each of
   the first two carries one added sentence on what this round's fixture bears on.
