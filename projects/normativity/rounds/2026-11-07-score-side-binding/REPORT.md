# Report — where obligations bind: the score-side test, solvency as soundness, admission by standing

| | |
|---|---|
| Prompt author | Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-07 (`prompts/2026-11-07-score-side-binding/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Base | `origin/main` at `73edb7de` |
| Date | 2026-11-07 |

## Corrections and deviations (`AGENTS.md` §8)

- The dispatch places the eight-world model in `ThinLegitimacy.lean`. That file's §11 mentions
  an eight-world fixture in prose and exposes no world type or measure for it; the Lean
  witnesses there are two-world. The model is stated locally in `RobustWarrant.lean` with exact
  rationals, as the dispatch permits.
- The dispatch cites `PRIORITIES.md` for the item ledger and for *Workspace friction*. The ledger
  is `ATTENTION.md`, rendered from the item nodes under `graph/nodes/` since 2026-11-05; items
  were narrowed by editing their nodes and the render regenerated.
- The dispatch's `python3` is 3.9 on this machine, which cannot parse `checkers/graph.py`; every
  checker was run with `python3.12`, the version CI uses.
- The dispatch asks the round to "file the round's node". The map protocol has no node kind for
  a round: a round appears only as `work` pointers of kind `round` on the nodes standing for
  its results and items. The round filed those pointers and no node of its own, and the gap is
  item F10.
- The rebuttal run's fixture has no obligation on conduct, so the smallest one was added as the
  dispatch instructs; the fixture otherwise is the run's, imported, not copied.

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
date at which the originating obligation's account carries a live leaf, assessed by that
account's fate — is of class *assessed* and about conduct (`WarrantInductorScoreSide.ShortfallAt`;
`shortfall_assessed`: live at every date of `state₀`).

**The two realizations on the same market.** The score-side realization (`scoreSide σ ϖ`) is the
rebuttal run's schedule, untouched, with the obligation and a charge `ϖ`; its gate is the soft
gate on `P₁`'s scores less `ϖ` times the market's price of the shortfall sentence `σ` on the
acting option (`chargedScore`, `scoreGate`; the shape of `BRIACorrigibility.evalOf`). Proved:

- `bundle_unchanged`: the enforcer's bundle is `(NB n).bundle` at every date;
  `market_unchanged`: the market is `WB.market DP`, by `rfl`; `no_conduct_row`: no held row
  equals the conduct row `P(X∧A∧Y) ≤ 1/3`, by the constants of the held rows
  (`−4/5, 1/5, 0, −3/4` for the sub rows, `0` for coherence, `0, ±1` for pins).
- `after`: at date 9, for every `ϖ ≥ 0` and every `σ`, the gate refrains with certainty — the
  charge only lowers an acting score the pin already holds below `τ`.
- `before`: at date 4, with `ϖ · price(σ) ≤ 19/240`, the gate acts with mass at least `24/25`.
  The enforced strength and applicability rows hold `P(X∧A∧Y) ≥ 1/2 − 1/240`, which leaves
  `19/240` above `τ + δ = 5/12`; the refraining score is at most `1/3 + 1/400`.
- `override`: when `ϖ · price(σ)` reaches the acting score's room above `τ`, the act's weight
  is `0` — and no price has moved.
- `same_question_two_realizations`: the run's `same_question` and `before`/`after` together.
- `conduct_on_prices_conflicts`: the conduct row appended to the date-4 bundle leaves an empty
  region, by the three-row certificate `conductCert` (strength row, `2/3` of the applicability
  row, conduct row; constant `−1/6`) through `conflict_sound`; a compiler returning it withholds
  the date. `conduct_on_prices_idle`: at date 9 every region point satisfies the conduct row.

**Verdict: (b).** The reversal obtains with no row on conduct enforced, and it needs the
epistemic strength row: without it the date-4 region admits `P(X∧A∧Y) = 0` and nothing
certifies acting. The practical part is score-side — the obligation binds through `ϖ` and the
priced assessment, and can override the act without touching a belief — and the belief part is
an epistemic warrant on prices. What (c) would have cost is proved beside it: on prices the
obligation either collapses the date or adds nothing.

## 2. Solvency as soundness

**(a) The instantiation.** `WarrantSolvency.Schema`: a strength and, per instance, whether it is
undefeated and the settled truth of its consequent — timeliness is the shape of the data.
`held t` is the strength on an undefeated instance, `realized t` the consequent's truth.
`Schema.bounded_iff_frequency`: `(∀ n, −B ≤ liability realized held n) ↔ ∀ n, c · U_n − T_n ≤ B`,
with `U_n` the undefeated count and `T_n` the true consequents among them. The reduction of
`WarrantForce`'s calibrated day value to one unit per instance is the hypothesis
`UnitPosition`, named on `solvent_iff` and not derived. Witnesses: a consequent always true
(bounded at `B = 0`), always false (unbounded, through `systematic_outperformance_unbounded`
with gap `3/4`). **This is a renaming of the deference result**, `bounded_iff_not_outperformed`
with `h := realized`, `g := held`, plus the counting identity `outperformance_eq`; no new
mathematics.

**(b) The conflict audit.** `exists_violated_suspect`: for any `FarkasCert` and any price
vector, some positively weighted row is violated (the weighted sum argument of `farkas_sound`,
restricted to the positive multipliers). `no_conflict_of_sound`: if every weighted row holds at
a point, no such certificate exists. `suspect_in_bundle`: against a bundle, at any cube point,
the violated suspect is a row of the bundle, since the cube rows hold in the cube; also on a
`NormState` (`suspect_in_normState`). `unique_suspect`: all suspects but one holding at a point
convicts the one. Read at the true posterior: sound rows cannot conflict, and a valid conflict
certificate proves a mis-admission among the rows it weights.

**(c) The eight-world fixture.** `RobustWarrant`: worlds `(q, s, ch)`, `μ` the product measure.
`valid_at_signal`: the row at `3/4` holds at the record with the signal alone, with equality
(`Pr(Y | A) = 3/4`). `invalid_at_contrary`: at the record with the contrary challenge it fails
(`Pr(Y | A ∧ C) = 3/5`; `3/4 · 5/12 > 1/4`). On the three-coordinate embedding
(`A`, `A∧Y`, `C`), the settlement recording the challenge pins neither antecedent nor
consequent, so `settleOutcome` keeps the form and `settleForm` contributes the specialized row
(`kept_under_challenge`), the quiet docket undercuts nothing (`not_undercut`), and the
contributed row is violated by her posterior (`contributed_row_invalid`). The opposing warrant
at `2/3` makes the rows infeasible (`naiveCert`, `naive_conflict`) although `3/5` is
determinate. **The robust reading** (`Robust`, provisional): `Pr(Y | A ∧ E) ≥ c` for every
undefeated extension `E`; `robust_sound` is its one-line soundness lemma. `robustStrength_all`:
`3/5` over the three extensions; `robustStrength_defeated`: `3/4` with the contrary challenge a
defeater; `against_robust_iff`: the opposing warrant's robust strength is `2/5`; `robust_meet`:
the robust rows for and against meet at `3/5`. No general defeat semantics is built.

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

Of entitlement's four conditions at this fixture: **exposure** is content-free (`start` exposes
everything); **admission** carries content (the allocation can withdraw it); **liveness** carries
content (as before, `answered_not_entitled`); **`Expresses`** remains typed and total. The
allocation is constant in the history at the fixture; the definition takes a history-indexed
one.

## 4. Exposition

`wiki/Normative-Inductor.md`: the architecture line carries the adapter's charge and a sentence
saying obligations on conduct enter there, not the enforcer; *Where each kind of obligation
binds* under the architecture; *Entitlement, not licence* gains admission by standing; *What
remains* gains the robust reading and item 133. `wiki/Normativity.md`: *Current status* gains
the three kinds of settlement, force as finite-time binding on settling matters, solvency as the
discipline, and the exposure rule marked as a proposal; *What a norm has to promise* and *Force,
and what force costs* gain the solvency statement and the finite-date paragraph.
`wiki/Theorem-Spine.md`: Theorems 7.7–7.10. Established labels name only the six registered
claims. *Warrants constrain prices* and *warrants produce warranted guidance* are kept apart on
each page.

## The eight questions, per registered theorem

**`same_question_two_realizations`.** *Hypotheses:* `0 ≤ ϖ`; `ϖ · WB.market DP 4 σ ≤ 19/240`;
the run's enforced dates. *Inhabited by:* any `σ`, `ϖ = 0`. *Typed:* the shortfall sentence
and its generability; whether the market prices the assessment well. *At the fixture:* act
`≥ 24/25` at 4, refrain with certainty at 9, in both realizations. *Vacuous if:* the date-4
price of `σ` leaves no `ϖ > 0` under the bound — then it reduces to the run's theorem;
`override` covers that regime. *Same theorem elsewhere:* the run's `same_question` is its first
conjunct. *Not shown:* that acting is adequate at date 4 under the obligation (the adequate set
is declared); that `σ` is generable. *Reopens:* a change to `P₁`, the tolerance, or the
rebuttal rule.

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
point is the true posterior. *At the fixture:* at `wit 4` the violated suspect is the conduct
row. *Vacuous if:* `m = 0` — excluded, since `const_sum` needs a negative sum. *Same
elsewhere:* `conflict_sound` is its contrapositive without the suspect. *Not shown:* which
suspect is the mis-admission; only that one is. *Reopens:* a change to `Bundle.Allowed`.

**`robustStrength_all`.** *Hypotheses:* none beyond the model. *Inhabited by:* the model.
*Typed:* the undefeated extension set `U`. *At the fixture:* `3/5`; `3/4` with the challenge a
defeater. *Vacuous if:* `U` empty, excluded. *Same elsewhere:* none in Lean. *Not shown:* a
`Form`-level rule; agreement with `settleForm`; anything beyond eight worlds. *Reopens:* item 133.

**`reallocated_entitles_nothing`.** *Hypotheses:* an entitlement's own fields over the protocol
under `J₁`. *Inhabited by:* vacuously at `J₁` (no `Initial` exists exposing obligation 0);
`entitlementS` inhabits the positive side at `J₀`. *Typed:* `Expresses`; the history-indexed
allocation (constant at the fixture). *At the fixture:* `origin o ≠ 0` for every `o ∈ grounds`.
*Vacuous if:* no obligation state of `protocolS₁` exists — one does with only obligation 1
exposed; the theorem is stated for all. *Same elsewhere:* `answered_not_entitled`, with the
allocation for the account. *Not shown:* `authorized` against the account (128(b)); entitlement
along an evolution (128(c)). *Reopens:* a ruling that admission reads the receipts rather than
the allocation.

## What this round does not establish

- That the shortfall sentence is generable or that the market prices the assessment well: both
  typed (items 90, 101 of the decision component).
- That the calibrated warrant enforcer's day value is a unit position per instance: `UnitPosition`
  is a hypothesis; 2(a) is the deference identity under a name.
- Item 61's summability condition over the compiled force request and `D_t`: untouched.
- A `Form`-level rule or compile of the robust reading; any defeat semantics (item 133).
- Which suspect a conflict convicts: only that some weighted bundle row is false at every
  cube point.
- Anything about `authorized` against the account, or entitlement along an evolution.
- Whether acting is *adequate* at date 4 under the added obligation: the adequate set is
  declared, and the charge is a parameter.
- The exposure rule: a proposal on the wiki and in the queue, not a result.

## Verification

- `~/.claude/scripts/safe-lake.sh build Workspace`: VERIFICATION-BUILD
- `python3 tests/audit_axioms.py` (run as `python3.12`): VERIFICATION-AUDIT
- `python3 tests/run.py`: VERIFICATION-TESTS
- `python3 -m checkers.run`: VERIFICATION-CHECKERS
- `python3 -m checkers.workspace_state --check`: VERIFICATION-STATE
- `python3 -m checkers.wiki_state_bindings`: VERIFICATION-BINDINGS
- `python3 -m checkers.wiki_links`: VERIFICATION-LINKS
- `python3 -m checkers.wiki_refs`: VERIFICATION-REFS
- `python3 -m checkers.attention_render --check`: VERIFICATION-ATTENTION
- `python3 -m checkers.graph`: VERIFICATION-GRAPH

Claims whose status changed: none. Six claims added, all `lean-proved`.

## Items

Narrowed: 35 (fourth instance), 61, 128 (clause (a) landed). Noted: 113 (closed; the
non-linear form it names), 127. Filed: 133 (the robust reading as a `Form`-level rule), F10
(a research round has no node of its own on the map; `AGENTS.md` §14).

## Registrations

`scoreside.same-question-two-realizations`, `scoreside.conduct-on-prices-conflicts` (item 35);
`solvency.bounded-iff-frequency` (item 61); `solvency.conflict-names-suspects`,
`robust.eight-world-strengths` (item 133); `standing.reallocated-entitles-nothing` (item 128).
Listed and not registered: every other declaration of the four modules.

## Names, provisional

*refrain while live*, *shortfall sentence*, *score-side realization*, *charged score*,
*score-side gate*, *conduct row*; *schema* (warrant schema with timely-settling instances),
*unit position*, *undefeated count*, *true count*; *suspects*; *robust* (the robust reading),
*robust strength*, *row valid at a record*; *admission by standing*, *with standing*.

## Merge recommendation

**Ready, with one reading to confirm.** The mathematics is small and does what the dispatch
asked: the score-side test discriminates the three outcomes and lands on (b) with the cost of
(c) proved beside it; the solvency statement is the deference identity renamed and says so; the
conflict audit is in the certificate type's generality; the eight-world fixture shows the row
failing while both mechanisms stay silent and the robust reading repairing it at `3/5`; the
admission predicate now has content from the allocation. The one reading the maintainer owns is
the exposure rule, queued as a proposal. The two things that could make the round smaller than
it looks are named: the unit-position hypothesis stands between 2(a) and the calibrated
enforcer, and the shortfall sentence's generability stands between the score-side charge and a
deployable chooser.

## Outstanding maintainer actions

1. **Rule on the exposure rule, or leave it a proposal** — `DECISIONS.md`, *Awaiting the
   author*, the 2026-11-07 entry (`open--exposure-rule-proposal`).
2. **Merge or decline the pull request**; auto-merge is off and the merge is the maintainer's.
3. The queue entries on M1, M2 and the entitlement liveness reading stand as before; each of
   the first two carries one added sentence on what this round's fixture bears on.
