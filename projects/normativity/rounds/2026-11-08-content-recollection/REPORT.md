# Report — content recollection: four tools for a notion of content that survives change

| | |
|---|---|
| Prompt author | Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-08 (`prompts/2026-11-08-content-recollection/PROMPT.md`, verbatim) |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code |
| Base | `origin/main` at `fca35075` |
| Date | 2026-11-08 |

Lean, all under `lean/Workspace/Normativity/Contrib/`: `RowAlternative.lean` (the shared
duality), `Conservativity.lean` (matter 1), `IncompatibilitySemantics.lean` and
`ExpressesByRole.lean` (matter 2), `Recollection.lean` (matter 3), `PrecedentConstraint.lean`
(matter 4). `THEOREM.md` carries the registered statements with their hypothesis packages. No
Python in this round is theorem-bearing.

## Corrections and deviations

- **The Farkas lemma comes from `EconCSLib`, not Mathlib.** The dispatch asks whether the
  pinned Mathlib supplies the form completeness needs. It does not: Mathlib has the
  closed-cone form over real inner product spaces. The pinned `EconCSLib`
  (`lean/lake-manifest.json`, inherited through Formalized-Agent-Foundations) proves the
  theorem of the alternative and the affine Farkas lemma over any linearly ordered field
  (`EconCSLib.LinearAlgebra.theorem_of_alternative`, `farkas_lemma`). `RowAlternative.lean`
  imports `EconCSLib.Math.LinearAlgebra.Farkas` and reads both into `Row`. This is the first
  `Workspace` import of an `EconCSLib` module; no pin changed, and both results audit to the
  three allowed axioms. So completeness is proved, and both of item 118's theorems are
  shipped rather than the item narrowed.
- **Completeness needs no nonemptiness hypothesis.** The dispatch expects completeness "where
  the region is nonempty". Relative to the cube it holds everywhere: against an infeasible list
  a scaled conflict certificate added to a cube certificate derives every row
  (`certEntails_of_incompatible`).
- **Matter 1 is proved for linear translations, of which a coordinate map is the `0/1` case.**
  The dispatch asks for an embedding of old coordinates into new. The theorems take each old
  coordinate as a rational linear form in the new ones (`Translation`); `Translation.ofMap e`
  is the coordinate map, and injectivity of `e` is used nowhere. Reason: matter 3's stochastic
  map is a translation on world-distribution coordinates, so one theorem serves both.
- **Matter 4 registers against item 117**, which the dispatch's candidate list (118, 128, 113,
  133, 115) does not name. Item 117 is the filed request for a precedent object on the docket.
  Nothing registers against item 115.
- **One new item is filed, not two**: item 134. What matter 4 found missing is added to item
  117 as a note, because that item already asks for the object.
- **The site.** `state/prs.json` gains this pull request's digest and no digest for #140. Open
  pull request #141 already writes #140's; a second copy here would give one path two entries
  once both land. The digest's `merged` field is empty: the pull request is unmerged and the
  contract on `main` does not say what the field holds before a merge. Both edits append at
  the end of the same list, so whichever of #141 and this pull request merges second needs that
  hunk resolved by keeping both. `state/concepts.json` is untouched: the contract does not call
  for an entry for anything here.
- **The system `python3`** is 3.9; every checker was run with `python3.12`.

## 1. Conservativity

A vocabulary change is given by a **translation**: each old coordinate as a rational linear
form in the new coordinates. An old row pulls back to a new row, valid at a new point iff the
old row is valid at the induced old point (`pull_sat_iff`). Against an old region `R` and a new
region `R'`:

- the new **refines** the old when the pullback of every row `R` forces is forced by `R'`;
- the new **adds nothing** when every old row whose pullback `R'` forces was forced by `R`;
- **conservative** is both.

Both definitions quantify over rows of one vocabulary and mention no point of the other.
Proved, for bundle regions:

- `refines_iff`: refinement iff the image of `R'` lies in `R`;
- `addsNothing_iff`: adding nothing iff `R` lies in the image of `R'`. A point outside the
  image is cut off by an old row whose pullback is a nonnegative combination of the new
  bundle's rows (`separating_row`), by the rational alternative;
- `conservative_iff`: conservative iff the image equals the old region.

For seeds, `extend e S sub' str'` relabels every old item along the coordinate map and adds the
new items; the projection of the new forced region is `y ∘ e`. An extension always refines
(`extend_refines`), so it is conservative iff every old forced point lifts
(`extend_conservative_iff`).

**`seed_independence_strict` is not an instance.** With the identity map it says that a
nonempty strict layer adds no *pin* (`strict_layer_adds_no_pin`). A strict layer does add rows:
over the cube on one coordinate, `x < 1/2` forces `x ≤ 1/2` (`strict_layer_adds_rows`). It is
conservativity restricted to consequences of the form `x φ = p`.

**Fixtures.** `ext₁`: over `P(X) ≥ 1/2`, a new coordinate `X∧A` with `P(X∧A) ≥ 3/4 · P(X)` and
`P(X∧A) ≤ P(X)` is conservative (`ext₁_conservative`). `ext₂`, the bad concept: over
`P(X) ≥ 1/2` on `(X, Y)`, a new term `T` with introduction row `P(T) ≥ 4/5 · P(X)` and
elimination row `P(Y) ≥ 3/4 · P(T)`. The extension forces `P(Y) ≥ 3/10` (`bad_forces_lower`),
by the certificate `badCert` — `3/5` of the premise row, `3/4` of the introduction row, the
elimination row, summing to `−P(Y) ≤ −3/10` — attained at `(1/2, 3/10, 2/5)`
(`bad_lower_attained`); the old seed admits `(1/2, 0)` (`old_not_forces_lower`); so the
extension refines and is not conservative (`bad_not_conservative`). With the elimination row's
port defeated it is conservative again (`bad_conservative_when_defeated`).

The tool **checks** a proposed vocabulary change and chooses none. Declared inputs: the
translation, the new seed, and that the new settlement agrees with the old on the old
coordinates.

**Verdict: fits.**

## 2. Incompatibility semantics and `Expresses`

**Incompatibility** of a list of rows is a Farkas certificate over the list's rows and the cube
rows — a valid `conflict` result of the compiler (`incompatible_iff_conflict`). It holds
exactly when the rows have no common cube point (`incompatible_iff_not_feasible`).
**Incompatibility entailment**: `Γ` entails `g` when every list incompatible with `g` is
incompatible with `Γ`. **Certificate entailment**: `g` is a nonnegative combination of rows
allowed against `Γ`, with slack (`EntailCert`); a `BoundCert` is the case `s · x φ ≤ v`. The
two coincide, and both are validity on the cube points of `Γ`
(`incEntails_iff_certEntails`, `incEntails_iff_sem`, `certEntails_iff_sem`).

**Item 118.** Its two theorems: every valid lower or upper bound on a forced region has a
bound certificate over the forced bundle's allowed rows (`lowerBound_certified`,
`upperBound_certified`), and the pair `forcedInterval` computes inhabits `IsForcedInterval`
(`forcedInterval_isForcedInterval`), by `exists_rat_of_real`: a rational system feasible over
`ℝ` is feasible over `ℚ`. Both hypothesis packages are inhabited on `widenSeed`.

**The Form language alone is degenerate.** The all-ones point satisfies every form of strength
at most one, so no list of such forms is incompatible and, restricted to form contexts, every
form entails every other (`humble_forms_feasible`, `formIncEntails_total`); on rows
`P(X) ≥ 1/2` does not entail `P(X) ≥ 3/4` (`form_role_needs_rows`). A form has a role only
among rows — structural rows, pins, the rows of other vocabularies.

**`Expresses`.** The anchored requirement is a defeasible warrant: events `A`, `Y`, a strength
`c`, undefeated extensions `U`. It **denotes its models**, the nonnegative measures satisfying
`RobustWarrant.Robust`. A form is read as a **content** — the rows it contributes at each
record — under the `plain` rule (its specialized row at every record) or the `settled` rule
(its specialized row where `settleOutcome` keeps it). An interpretation sends coordinates to
events; a model prices the fragment by its posterior at a record. A list of rows is
incompatible with the requirement at a record when no model's posterior there satisfies it.

- **Demands no more**: every list incompatible with the content at a record is incompatible
  with the requirement there. Equivalently every model of the requirement satisfies the
  content's rows at every record of positive mass (`demandsNoMore_iff`).
- **Same role**, relative to a declared background: the two incompatibility relations agree.

General results. A model of a requirement of positive strength gives the antecedent mass zero
on an undefeated extension where the consequent is false (`models_null_at_rebuttal`): a
satisfiable defeasible warrant cannot count its own rebuttal as undefeated. The kept row
demands no more than a requirement of at least its strength whose undefeated extensions
include every record the rule keeps it at (`settled_demandsNoMore`). The plain row demands more
wherever a model gives the antecedent positive posterior at a record settling the consequent
false (`plain_demandsMore`).

On the eight-world model with the fragment `(A, A∧Y, C)`:

1. `entitlementW` inhabits `Entitlement` under `ExpressesNoMore ι settled`, for the strength
   row at `3/5` against the requirement at `3/5` over the kept extensions, with admission by
   standing and a live account. The eight-world measure is a model of that requirement
   (`μ_models_kept`).
2. The plain row is not expressed (`plain_not_expresses`). At the record settling `A∧Y` false
   the row reads `3/5 · P(A) ≤ 0`; the eight-world measure prices `A` at `1/5` there. So
   `P(A) ≥ 1/5` is incompatible with the row, by the certificate `contraCert`, and compatible
   with the requirement (`contraposition_as_expression`). No entitlement exists under the plain
   rule (`no_entitlement_plain`).
3. The kept row passes (`settled_expresses`).

And one thing the dispatch did not ask for: the row at `3/4` has no entitlement over this state
(`no_entitlement_at_three_quarters`). Against the requirement at `3/5` it is too strong.
Against the requirement at `3/4` with the contrary challenge a declared defeater, the rebuttal
rule keeps the row at the challenge record, where the measure — a model of that requirement —
violates it (`defeater_not_expressed`). That is item 133's phenomenon as a failure of
expression: the rule's kept records are not among the requirement's undefeated extensions.
`entitlement_discriminates` collects the three cases.

The row at `1/2` demands no more than the requirement at `3/5` and does not have the same role
(`weaker_noMore_not_same`). Whether the row at `3/5` has the same role is not proved.

The tool **checks** a proposed pairing of requirement, form and rule. Declared inputs: the
requirement's events, strength and undefeated extensions; the interpretation of coordinates as
events; the background.

**Verdict: fits.**

## 3. Recollection as a map between world spaces

**Level: world distributions.** A recollection is a stochastic map from new worlds to old
(`Recollection`; `ofMap` for a function). On the coordinates "probability of a world" it is a
translation, so matter 1 applies unchanged and the pullback of a row is always a row. At the
level of sentence prices an old sentence pulls back to `w' ↦ Σ_{w ∈ S} k w' w`, a row over new
world coordinates and a new sentence only when `0/1`-valued.

- **Pullback and soundness**: `pull_sound`; the excess of a row is carried exactly
  (`excess_pull`).
- **Composition**: `comp`, `push_comp`, `pull_comp`. A recollection is a transport step with
  constant `1` and slack `0` (`recollection_step`); two compose through
  `affine_transport_compose` to `(1 · 1, 0 + 1 · 0)` (`recollection_chain`).
- **Approximate version**: two recollections that agree off a set `B` of new worlds move a
  row's excess by at most the row's oscillation times the new credence's mass on `B`
  (`approx_step`) — the slack is the mass on which the map fails, attained in `partial_slack`.
- **`ThinLegitimacy`**: a process to the new worlds followed by a recollection is a garbling of
  that process in the file's own terms, the recollection cast to the reals being the stochastic
  matrix (`garbling_of_recollection`). The mismatch: `ThinLegitimacy`'s kernels are real-valued
  and run from one common world type to record spaces, so the statement needs a declared common
  process; a recollection alone has none. `Sufficient` adds the earlier record beside the
  baseline's, which needs the file's Integrity clause and is not derived here.
- **Broken commitments**: rows the old region forces whose pullback the new region does not
  (`Broken`). None is broken iff the new region pushes forward into the old (`no_broken_iff`).

**Integrity's faithful transport.** In Lean it is
`OpenIntegrityEvolution.Conservation.faithful`: there is a map `transport` from resolutions of
the later boundary's ports to resolutions of the earlier boundary's ports such that, for every
occurrence exposed earlier, the later account evaluated at `v` equals the earlier account
evaluated at `transport v`. Each step supplies it by substitution (`Conservation.ofStep`). It
is a pullback along a deterministic map from later to earlier — the same shape as a
recollection — on a different carrier: resolution witnesses of accounts, with the anchor fixed
by type. It constrains no row and no credence. A recollection neither supplies it nor follows
from it. "No broken commitment" would be a further condition on content, one that Integrity
does not state.

**Fixtures.** *Split*: `(S, ¬S)` retold from `(S₁, S₂, neither)`. `P(S) ≥ c` pulls back to
`P(S₁) + P(S₂) ≥ c` (`split_pull`). With `P(S₁) ≥ 2/5`, `P(S₂) ≥ 1/5` nothing is broken and
`P(S) ≥ 3/5` is added (`split_refines`, `split_adds`); with `1/5` and `1/5`, `P(S) ≥ 1/2` is
broken (`split_broken`). *Abandonment*: each new world retells as a mixture, `S` with weight
`1/4` or `3/4`. The old sentence has no exact image (`abandon_no_sentence`); `P(S) ≥ 9/10` is
broken at every new credence (`abandon_broken_everywhere`); `P(S) ≥ 1/2` becomes the constraint
that the second new world has probability at least `1/2` (`abandon_half`).

**What the formalism reports under abandonment.** Given a map, it reports which old rows the
new credence breaks, exactly. Given the uninformative map — every new world retold as one fixed
old credence — every old row is kept or broken at every new credence alike
(`const_pull_sat`): it reports whether that fixed credence satisfied the row and nothing about
the new view. Given no map, it reports nothing. It does not say which map is right.

Two limits. The pullback of a leverage form along a translation that is not a coordinate map
is a row and not a form, so a recollected commitment enters a new seed as a structural row,
which no docket port defeats. And nothing here ties a recollection to a step of an Integrity
evolution.

The tool **checks** a proposed recollection and chooses none. Declared inputs: the map, and for
the garbling a common process.

**Verdict: fits in part.**

## 4. Precedent as the constraint on continuation

The constraint: past decisions induce a priority among reasons, and a new decision is allowed
only if one consistent priority still rationalizes every decision. The dispatch attributes it
to John Horty; the attribution is unverified here.

The model, in Lean. A reason is a leverage form: its kind is the form with the strength
erased, its weight is the strength. A **case** is read off the record: the forms of the
occurrences that survive under a docket and a settlement prevailed, and the forms of the
occurrences the docket undercuts were outweighed (`caseOf`). `V` covers `W` when each form of
`W` has a form of `V` of its kind and at least its strength. A case says that anything
covering its winners beats anything its losers cover. A case base is **consistent** when no
two reason sets beat each other, which is the existence of an asymmetric relation containing
every case's decision (`consistent_iff_order`) and a pairwise check on cases
(`consistent_iff_pairwise`). A continuation is **permitted** when the base stays consistent
with it; permission only shrinks (`permitted_antitone`).

Fixtures on `(X, ¬X, D)`. The precedent: `P(X) ≥ 3/4` prevailed over `P(¬X) ≥ 1/2`.
*Forbidden*: `P(¬X) ≥ 2/5` prevailing over `P(X) ≥ 4/5` (`forbidden_not_permitted`).
*Permitted by distinguishing*: deciding against `P(X) ≥ 3/4` with a ground of a new kind
present (`permitted_distinguished`), or with the opposing strength at `3/5`, above the
precedent's (`permitted_stronger`).

**Better, or only allowed?** Only allowed. In the distinguished situation both decisions are
permitted and they are not jointly permitted (`both_permitted`); the model has nothing that
orders them.

**The survivor rule.** The constraint sits beside it, upstream. It reads the rule's output to
form a case and constrains the docket, which is the rule's input; the rule is unchanged. An
occurrence removed by rebuttal is on neither side of a case
(`rebuttal_sets_no_precedent`).

**What does not fit.** The record carries no decision. `DocketState.defeated` is a set of
ports; nothing says which conflict a defeat resolved or what prevailed, so `caseOf` reads every
undercut as an outweighing, and an undercut that attacks applicability is counted as a lost
contest. A case also drops the grounds that were present and neither prevailed nor were
undercut. For the model to fit, the docket would carry a decision occurrence naming the
grounds weighed and the ground that prevailed. Item 117 asks for a docket object of that kind;
the gap is recorded there.

The tool **checks** a proposed continuation against the cases and chooses none. Declared
inputs: the docket states, and the reading of undercut as outweighed.

**Verdict: fits in part.**

## What this round does not establish

- **The reading.** Nothing here shows that a later stage *recollects* an earlier one in the
  sense under test. Matters 1 and 3 say when a change keeps old commitments and what it adds;
  none of the four tools explains an old error, and none selects a translation.
- **Same role for the exact row.** `ExpressesSame` is defined and refuted for a weaker row; for
  the row at the requirement's own strength it needs every cube point of the kept row's region
  to be the posterior of some model, which is not built.
- **The undefeated extensions.** `U` is declared. `keptExtensions` is the set under which the
  rebuttal rule is sound, not a derivation of defeat; the item-133 rule on `Form` is not
  written.
- **Models over one world type.** `DemandsNoMore` quantifies over nonnegative measures on a
  fixed finite world type with a fixed interpretation.
- **Computing the image.** `conservative_iff` characterizes conservativity; no procedure here
  computes the image of a region, and `SeedStatics.project` is not connected to it.
- **The adapter's certificates.** That `Excludes` and `Margins` certificates of
  `WarrantInductor.Problem` exist whenever the region excludes or marks is not derived from
  `certEntails_iff_sem`.
- **The fixtures are small**: at most three coordinates, eight worlds, three cases.
- **Matter 3 beyond fixtures.** No theory at the level of sentence prices; no recollection
  attached to an accounted state.
- **Matter 4's source.** The reason model is stated from the dispatch's description; no text of
  the attributed author was consulted.
- **The dependency.** Completeness rests on `EconCSLib`'s proofs, kernel-checked and unread by
  a maintainer.

## External review

*Filled after the review.*

## Verification

*Filled after the runs.*

## Items

Both of item 118's theorems are registered; its status is the maintainer's word (ruling G3)
and is left `open`. Narrowed: 128 (the `Expresses` half of clause (a)), 133 (the
kept row against a declared defeater; soundness of the kept row where the rule's kept records
are undefeated), 122 (its Lean half), 117 (a constraint in place of a lock; what the docket
lacks). Noted: 113 (closed; the contraposition as a statement about expression), 79 (conflict
and entailment certificates complete on the row schema). Filed: 134 (content across a
vocabulary change, on the accounted state).

## Registrations

Against 118: `rows.incompatibility-entailment`, `seed.bound-certified`,
`seed.forced-interval-rational`. Against 128: `expresses.kept-row-demands-no-more`,
`expresses.entitlement-discriminates`. Against 113: `expresses.plain-row-demands-more`. Against
134: `content.conservative-iff-image`. Against 117: `precedent.consistent-iff-pairwise`. All
`lean-proved`. Listed and not registered: every other declaration of the six modules, matter
3's among them.

## Names, provisional

*weights*, *the alternative*; *translation*, *pullback*, *image*, *projection*, *forces*,
*refines*, *adds nothing*, *conservative*, *extension* (of a seed); *incompatible*, *feasible*,
*incompatibility entailment*, *entailment certificate*, *certificate entailment*; *content*,
*plain* and *settled* (readings of a form), *record event*, *posterior prices*, *requirement*,
*models*, *demands no more*, *same role*, *kept extensions*; *recollection*, *push*, *excess*,
*broken commitment*; *kind* (of a reason), *covers*, *case*, *beats*, *consistent* (case base),
*permitted*.

## Outstanding maintainer actions

1. **Merge or decline the pull request.** Auto-merge is off.
2. **Resolve `state/prs.json` against pull request #141**, whichever merges second: keep both
   appended hunks, and set this pull request's `merged` date.
3. **Rule on whether a broken commitment bars a change or is accounted** — `DECISIONS.md`,
   *Awaiting the author*, the 2026-11-08 entry (`open--broken-commitment-bars-or-accounts`).
4. **Close item 118, or name what remains**: set `item_status` in
   `graph/nodes/item-118.md` and run `python3.12 -m checkers.attention_render --write`.
