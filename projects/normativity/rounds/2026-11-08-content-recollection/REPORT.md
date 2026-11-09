# Report — content recollection: four tools for a notion of content that survives change

| | |
|---|---|
| Prompt author | Claude Fable 5.1 (Anthropic), drafted in conversation with the maintainer on 2026-11-08 (`prompts/2026-11-08-content-recollection/PROMPT.md`, verbatim); the follow-up dispatch of 2026-11-09 (`PROMPT-followup.md`, verbatim) names no author model: unrecorded |
| Executor | Claude Fable 5.1 (Anthropic), in Claude Code; both passes |
| Base | `origin/main` at `fca35075`; the follow-up on the pull request's branch, `main` merged in at `e20498c3` and `eb98367e` |
| Dates | 2026-11-08; follow-up 2026-11-09 |

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
  133, 115) does not name. Item 117 is the filed request for a precedent object on the docket;
  the result bears on it and delivers neither its canonical joint rule nor its lock. Nothing
  registers against item 115.
- **Matter 1 registers against a new item**, 134, where the dispatch asks for an existing one.
  No filed item asks for a criterion on vocabulary change; item 122 asks only for the row
  transport, which is a lemma here.
- **One new item is filed, not two**: item 134. What matter 4 found missing is added to item
  117 as a note, because that item already asks for the object.
- **The site.** `state/prs.json` gains this pull request's digest and no digest for #140:
  pull request #141 wrote #140's and merged on 2026-11-09 while this round ran, and `main` at
  `e20498c3` is merged into this branch with both. The digest's `merged` field is `2026-11-09`,
  the day the pull request opened (the ruling of 2026-11-08 on digests; set by the follow-up).
  `state/concepts.json` is untouched: the contract does not call for an entry for anything
  here.
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
new items; the projection of the new forced region is `y ∘ e`. Under the same docket, the old
warrants relabelled, and a new settlement agreeing with the old on the old coordinates, an
extension refines (`extend_refines`), so it is conservative iff every old forced point lifts
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
exactly when the rows have no common cube point (`incompatible_iff_not_feasible`); this is
existence of a certificate, and no procedure here finds one.
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
warrant that counts its own rebuttal as undefeated is satisfied only by measures on which the
antecedent cannot occur there. The kept row
demands no more than a requirement of at least its strength whose undefeated extensions
include every record the rule keeps it at (`settled_demandsNoMore`). The plain row demands more
wherever a model gives the antecedent positive posterior at a record settling the consequent
false (`plain_demandsMore`). The condition on the extensions in `settled_demandsNoMore` is
sufficient; no converse is proved, and its necessity is shown only at the fixture.

On the eight-world model with the fragment `(A, A∧Y, C)`:

1. `entitlementW` inhabits `Entitlement` under `ExpressesNoMore ι settled`, for the strength
   row at `3/5` against the requirement at `3/5` over the kept extensions. The eight-world
   measure is a model of that requirement (`μ_models_kept`). Exposure, admission by standing
   and liveness hold for both obligations by construction — the protocol's other predicates
   are `True` — so at this fixture expression is the one condition that discriminates.
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
  `affine_transport_compose` to `(1 · 1, 0 + 1 · 0)` (`recollection_chain`). Both are the
  equality `excess_pull` written as an inequality: the transported quantity is a row's excess,
  and no defect measure of the program's is involved.
- **Approximate version**: two recollections that agree off a set `B` of new worlds move a
  row's excess by at most the row's oscillation times the new credence's mass on `B`
  (`approx_step`). For a row of oscillation one the slack is the mass on which the map fails,
  attained in `partial_slack`.
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
covering its winners beats anything its losers cover. A case base is **rationalizable** when
one strict order on reason sets, irreflexive and transitive, contains every case's decision.
That holds iff the graph on cases — an edge from a case to each case whose winners its losers
cover — has no cycle (`rationalizable_iff_acyclic`). The pairwise check, that no two reason
sets beat each other (`consistent_iff_pairwise`), is necessary and not sufficient: three cases
in a cycle pass it and have no order (`cycle_not_rationalizable`). A continuation is
**permitted** when the base stays rationalizable with it; permission only shrinks
(`permitted_antitone`). The model has no sides: any reason set may be compared with any
other.

Fixtures on `(X, ¬X, D)`. The precedent: `P(X) ≥ 3/4` prevailed over `P(¬X) ≥ 1/2`.
*Forbidden*: `P(¬X) ≥ 2/5` prevailing over `P(X) ≥ 4/5` (`forbidden_not_permitted`).
*Permitted by distinguishing*: deciding against `P(X) ≥ 3/4` with a ground of a new kind
present (`permitted_distinguished`), or with the opposing strength at `3/5`, above the
precedent's (`permitted_stronger`).

**Better, or only allowed?** Only allowed. In the distinguished situation both decisions are
permitted and they are not jointly permitted (`both_permitted`); the model has nothing that
orders them.

**The survivor rule.** The constraint sits beside it, upstream. It reads the rule's output to
form a case and constrains the docket, which is the rule's input; the rule is unchanged. On
the quiet docket an occurrence removed by rebuttal is on neither side of a case
(`rebuttal_sets_no_precedent`); `caseOf` counts every undercut occurrence a loser, whatever
the settlement.

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
  rebuttal rule is sound: choosing it builds the rule's compatibility into the requirement and
  validates no defeat semantics. No converse says which `U` a kept row needs. The item-133 rule
  on `Form` is not written.
- **The entitlement's other three conditions.** At `stateW` exposure, admission and liveness
  hold by construction; the fixture shows expression deciding entitlement, not four conditions
  each deciding it.
- **Certificates exist; none is computed.** Completeness is existence of a conflict or
  entailment certificate. No procedure here produces one.
- **Transport.** `recollection_step` restates an equality; no defect, loss or distance of the
  program's is transported.
- **The interpretation across a translation.** An interpretation `Fin d → Finset W` composes
  with a coordinate map and not with a stochastic translation, whose pullback of an event is a
  `[0,1]`-valued function. Item 134 carries this.
- **The precedent model has no sides.** Reasons are not sorted by the verdict they favour, and
  whether the attributed model orders reasons transitively was not checked against any text.
- **Models over one world type.** `DemandsNoMore` quantifies over nonnegative measures on a
  fixed finite world type with a fixed interpretation.
- **Computing the image.** `conservative_iff` characterizes conservativity. The image is
  computed for one dropped coordinate (`Forgetting.forget_region`, follow-up §F3) and for no
  other translation.
- **The adapter's certificates.** Derived below a rational threshold and at tolerance `0`
  (`AdapterCertificates`, follow-up §F5); not at a positive tolerance.
- **The fixtures are small**: at most three coordinates, eight worlds, three cases.
- **Matter 3 beyond fixtures.** No theory at the level of sentence prices; no recollection
  attached to an accounted state.
- **Matter 4's source.** The reason model is stated from the dispatch's description; no text of
  the attributed author was consulted.
- **The dependency.** Completeness rests on `EconCSLib`'s proofs, kernel-checked and unread by
  a maintainer.

## External review

GPT-6 Astra (OpenAI), via `codex`, reviewed pull request #142 at `5a421912` on 2026-11-08,
read-only; its text is `prompts/2026-11-08-content-recollection/REVIEW-astra-2026-11-08.md`,
verbatim. Its merge word: **fix-then-merge**. It found no mathematical defect in matters 1 and
2. One review pass and one fix pass; the fixes are in the commit that adds this section.

| finding | disposition |
|---|---|
| **Blocking.** `Consistent` requires asymmetry only; three cases in a cycle pass the pairwise check and no order rationalizes them, so "one consistent priority" was overstated | fixed: `Rationalizable` (an irreflexive transitive relation containing every case's decision), `rationalizable_iff_acyclic`, `rationalizable_of_rank`; `Permitted` is now rationalizability; the reviewer's three-cycle is `cycle_not_rationalizable`; the registered statement is `precedent.rationalizable-iff-acyclic` |
| The pull request says the kept row expresses the warrant "exactly when" kept records equal undefeated extensions; the theorem gives a sufficient condition | fixed: the description says *whenever*; §2 and the limitations say no converse is proved |
| Item 134 is not type-correct: a stochastic translation does not compose with an event-valued interpretation, and no broken row does not preserve admission or liveness | fixed: the item asks for the coordinate-map case with its hypotheses stated or a counterexample, and separately for the carrier a general translation needs |
| "A satisfiable warrant cannot count its rebuttal as undefeated" overstates `models_null_at_rebuttal` | fixed: §2 states the conclusion, zero antecedent mass |
| The queue entry says refinement bars every change away from a concept with no exact image; `abandon_half` shows otherwise | fixed: the entry names the commitment `P(S) ≥ 9/10` along that map |
| "A rebutted occurrence is on neither side" holds on the quiet docket only; `caseOf` counts every undercut occurrence a loser | fixed: §4, the Lean header and the registry note |
| Slack equals the failing mass only for a row of oscillation one | fixed: §3, the verdict line, the digest and the Lean header keep the factor |
| The verification and review sections were placeholders | fixed: filled below and above |
| The report calls item 113 closed although its status is open | **disputed**: `graph/nodes/item-113.md` carries `item_status: closed`; the `[open]` in the rendered heading is the difficulty tag. *Items* now says so |
| Registering conservativity against the new item 134 is an undeclared deviation | fixed: declared above |
| `entitlementW`'s exposure, admission and liveness hold by construction | fixed: §2 and the limitations say expression is the one condition that discriminates there |
| `recollection_step` repackages an equality | fixed: §3 and the limitations say so |
| "An extension always refines" needs its qualifications | fixed: §1 states them |
| The description's "the all-ones point satisfies them all" drops the strength restriction | fixed in the description |
| `incompatible_iff_conflict` is existence of a valid result, not a compiler's execution | fixed: §2 and the limitations |
| The digest's empty `merged` field must be resolved before publication; preserve #141's digest of #140 when reconciling | #141 merged during the fix pass and `main` is merged into this branch with its digests intact; the date is reserved, outstanding action 2, since it is not known before the merge |

## Verification

Local, Python 3.12, on the tree after the fix pass.

- `~/.claude/scripts/safe-lake.sh build Workspace`: `Build completed successfully (4108 jobs)`;
  the build compiles two `EconCSLib` modules it did not compile before
  (`Math.LinearAlgebra.FourierMotzkin`, `Math.LinearAlgebra.Farkas`).
- `python3.12 tests/audit_axioms.py`: all within
  `['Classical.choice', 'Quot.sound', 'propext']`, `3757 results across 118 files`. The script
  outlasts this session's limit on one command, so its own `main` was run over the sorted
  source list in four slices before the fix pass (633, 965, 966 and 1185 results; 3749) and
  again over the six new modules after it (246 results, 238 before). No slice reported a
  failure.
- `python3.12 tests/run.py`, with `lean/.lake` set aside and the new files added:
  `ALL GREEN (80 project(s))`, before and after the fix pass; `LEAN SORRY GATE: clean over 118
  files`; `SITE DOM GATE: app boots, 73 capsules, 151 edges, cards open, fragments present, no
  overlaps`; `LEAN BUILD SKIPPED`, the build above being the Lean verification.
- `python3.12 -m checkers.run`: `87 entries, 1 adjudicated here`; the eight entries of this
  round `lean-proved`, adjudicated by the Lean gate.
- `python3.12 -m checkers.workspace_state --check`: `WORKSPACE STATE: valid — 7 projects, 192
  modern claims, 1 foundations, 180 foundation claims, 133 rounds, 52 terms, 145 priorities, 10
  interface objects`, after `--write-handoff` and with `main` merged in.
- `python3.12 -m checkers.wiki_state_bindings`: `clean over 35 page(s); 3 binding(s) verified
  against the state emission`, after the registered-claims count on `wiki/Normativity.md` moved
  from 70 to 78 — the one wiki edit.
- `python3.12 -m checkers.wiki_links`: `clean over 33 page(s)`. `python3.12 -m
  checkers.wiki_refs`: `clean over 35 page(s); 327 reference(s) resolve`.
- `python3.12 -m checkers.attention_render --check`: `the committed file equals the render (145
  items)`.
- `python3.12 -m checkers.graph`: `OK 2527 nodes, 2603 events, 2094 ranked units`, with the
  standing warning on decision anchors without a node.

`main` at `e20498c3` (pull request #141: digests, a workflow schedule, governance text; no
Lean) was merged into the branch after the runs above. On the merged tree the build was not
repeated; `checkers.graph`, `checkers.workspace_state --check`, `checkers.run`,
`checkers.attention_render --check`, `checkers.wiki_state_bindings`, `tests/site_build.py`,
`tests/dead_pointers.py`, `tests/untracked_pointers.py` and `tests/freshness.py --self-test`
were re-run and are clean, and the full `tests/run.py` sweep on the merged tree is CI's.

CI on pull request #142: all seven required checks passed at `5a421912`, the head the review
read. Later heads are recorded on the pull request.

## Items

Both of item 118's theorems are registered; its status is the maintainer's word (ruling G3)
and is left `open`. Narrowed: 128 (the `Expresses` half of clause (a)), 133 (the
kept row against a declared defeater; soundness of the kept row where the rule's kept records
are undefeated), 122 (its Lean half), 117 (a constraint in place of a lock; what the docket
lacks). Noted: 113 (closed; the contraposition as a statement about expression), 79 (conflict
and entailment certificates complete on the row schema). Filed: 134 (content across a
vocabulary change, on the accounted state). Item 113's node carries `item_status: closed`;
the bracket in its `ATTENTION.md` heading is the difficulty tag.

## Registrations

Against 118: `rows.incompatibility-entailment`, `seed.bound-certified`,
`seed.forced-interval-rational`. Against 128: `expresses.kept-row-demands-no-more`,
`expresses.entitlement-discriminates`. Against 113: `expresses.plain-row-demands-more`. Against
134: `content.conservative-iff-image`. Against 117: `precedent.rationalizable-iff-acyclic`. All
`lean-proved`. Listed and not registered: every other declaration of the six modules, matter
3's among them.

## Names, provisional

*weights*, *the alternative*; *translation*, *pullback*, *image*, *projection*, *forces*,
*refines*, *adds nothing*, *conservative*, *extension* (of a seed); *incompatible*, *feasible*,
*incompatibility entailment*, *entailment certificate*, *certificate entailment*; *content*,
*plain* and *settled* (readings of a form), *record event*, *posterior prices*, *requirement*,
*models*, *demands no more*, *same role*, *kept extensions*; *recollection*, *push*, *excess*,
*broken commitment*; *kind* (of a reason), *covers*, *case*, *beats*, *dominates*, *rationalizable*, *consistent* (the pairwise
condition), *permitted*.

## Follow-up of 2026-11-09 — finite memory, decisions on the record, change as an answerable act

Dispatch: `prompts/2026-11-08-content-recollection/PROMPT-followup.md`, verbatim. Lean, under
`lean/Workspace/Normativity/Contrib/`: `PrecedentHolding.lean` (F1), `AssessedConduct.lean`
(F2), `Forgetting.lean` (F3), `VocabularyAct.lean` (F4), `AdapterCertificates.lean` (F5). No
existing module was changed.

### Corrections and deviations

- **`main` was merged into the branch at `eb98367e`** (pull request #139), which conflicted
  with it. The dispatch says to add commits without rebase or squash; the merge is a commit.
- **`main` carried conflict markers.** At `eb98367e`, `DECISIONS.md` has three merge-conflict
  marker lines around two entries of 2026-11-09 and one of 2026-11-08, with every required
  check green. The merge here keeps every entry, in date order, without the three lines. No
  gate reads for them; filed as friction item F11.
- **Two items are filed where the dispatch allows one**: item 135, and the friction item F11
  just named. F11 is filed rather than fixed here, though a new gate is within the contained
  fixes a round may take: a gate under `tests/` sits on the trust chain, and the maintainer is
  asked to merge this pull request on its research; a gate added to it would be merged on those
  grounds, not read on its own.
- **The first pass's text is changed in four places**: the header table (dates, the follow-up
  dispatch); the deviation on the digest's `merged` field; the lines *Computing the image* and
  *The adapter's certificates* of *What this round does not establish*; and *Outstanding
  maintainer actions*, where setting the digest's date is no longer an action.
- **The first pass's notes on items 79 and 118** said the adapter's certificates were not
  derived; they now state what is derived. Item 134's clause (d) is rewritten around what is
  proved and a clause (e) added.
- **F1's normal form is not the one the dispatch suggests.** It suggests a threshold per kind
  or an antichain of minimal winners and maximal losers. What is proved is the reach restricted
  to a finite set of reason sets. The antichain is not built: `staircase_irredundant` is an
  antichain of `n` cases over one pair of kinds, so over `ℚ` it is not finitely bounded either.
- **F2's adapter is slight.** `ActCertificate` is generic in its entry type, so at
  `Ent := Form d` its grounds are a reason set with no conversion.
- **F3(a) connects through the step, and then through `project`.** The theorem is proved for
  one step of `FourierMotzkin.elim`, the step `SeedStatics.project` iterates;
  `project_iff_projection` is the statement for `project` itself.
- **F4's readings take liveness as a declared predicate** on rows. Nothing reads it off the
  docket.
- **Nothing registers against item 119.** The merged-discord fixtures are noted there.
- **One wiki edit**: the bound count of registered claims on `wiki/Normativity.md`, 78 to 88,
  which `checkers.wiki_state_bindings` requires.
- **The follow-up dispatch names no author model.** The attribution block records it as
  unrecorded.

### F1. The holding (C1)

The **holding** of a case base is the transitive closure of `Dominates` on reason sets
(`Holding`). Its **reach** adds covering: `Reach Γ V U` is `Covers V U ∨ Holding Γ V U`, a
preorder.

- `holding_cons`: the holding of `c :: Γ` relates `V` to `U` iff the holding of `Γ` does, or
  the reach of `Γ` puts `V` at or above `c`'s winners and `c`'s losers at or above `U`.
- `permitted_iff`: `Permitted Γ c` iff `Γ` is rationalizable and the reach of `Γ` does not put
  `c.losers` at or above `c.winners`. Permission reads the reach at one pair.
- `permitted_congr`, `permitted_append_congr`: two case bases with the same holding permit the
  same continuations, and still do after any further continuations. **The cases may be
  forgotten and the holding kept.**
- `permission_eq_iff_reach_eq`: among rationalizable bases, same permissions iff same reach.
  The holding is finer than that: a case whose winners cover its losers enters the holding and
  changes no permission (`holding_not_minimal`).

**Size.** The holding relates all reason sets. Restricted to a set `R` that contains the
winners and losers of every continuation, the reach on `R × R` together with whether the base
is rationalizable is closed under continuation (`agreeOn_cons`). For finite `R` it is a subset
of `R × R`, it only grows (`reach_mono`), and along any sequence of continuations it is
eventually constant (`reachSet_eventually_const`, by `SeedStatics.eventually_const_of_finite`),
after which permission over `R` is constant (`permission_eventually_const`). A finite set `Φ`
of forms — finitely many kinds at finitely many strengths — supplies such an `R`: a reason set
drawn from `Φ` covers and is covered by its list of distinct forms (`normal`, `covers_normal`),
of which there are at most `2 ^ |Φ|` (`reasonSets`, `card_reasonSets_le`); the holding does not
distinguish reason sets that cover each other (`holding_congr_covers`); so along any sequence
of continuations — drawn from `Φ` or not — the holding on all reason sets drawn from `Φ` is
eventually constant (`holding_eventually_const_of_finite_forms`), and so is permission for
every continuation drawn from `Φ` (`permission_eventually_const_of_finite_forms`). The theorems
bound what the holding can say on `Φ` and when it stops changing; they do not bound the stage
at which it stops, nor the size of any representation of it. Without finitely many strengths
there is no finite representation: over one pair of kinds, no case of a staircase of `n` cases
at `n` increasing strengths is redundant (`staircase_irredundant`), and two staircases over
one scale with the same holding have the same steps (`stairs_holding_injective`), so `n`
strengths carry a different holding for each of the `2 ^ n` sets of steps, at strengths inside
`(0,1)` (`humbleScale_spec`). The count `2 ^ n` is read off the injectivity and is not itself
formalized.

**Merging.** The union of two case bases is rationalizable iff the union of their holdings has
no cycle (`rationalizable_append_iff`): merging reads the holdings. Two rationalizable bases
whose union is not: the precedent and its reverse (`merged_discord`); and the first two cases
of the three-cycle against the third, where every pair of cases is compatible
(`merged_discord_hidden`).

**Against item 119's hidden discord: it resembles it.** There, bundles of rows are each
feasible, pass a coordinate-wise check and are jointly infeasible. Here, case bases are each
rationalizable, pass the pairwise check and are jointly unrationalizable. Both are merges whose
failure no pairwise test sees. They are not shown to be one phenomenon: what is merged here is
an order on reason sets and its failure is a cycle, not an empty region of a declared fragment.
A reduction would be that a base is rationalizable iff ranks on its cases satisfy a system of
difference constraints, a cycle being that system's Farkas certificate; only one direction is
proved (`rationalizable_of_rank`), and its coordinates would be the cases, not sentences.

**Verdict: fits in part.** The holding is a sufficient statistic; it is finitely bounded only
over a finite set of reason sets.

### F2. Decisions on the record (C6)

An **assessed act** (`AssessedAct`) carries the grounds the act was taken on, the surviving
grounds against it, and a verdict, `adequate` or `shortfall`. Its **proposal** is the case the
chooser acted on, its grounds over the grounds against. Its **case** is set by the verdict: the
proposal if adequate, the reverse if a shortfall. The precedent is the assessor's.

**The adapter.** `ofCertificate cert against v` builds one from a
`DecisionComponent.ActCertificate (Form d) M Ob`. The certificate supplies the grounds. It has
no field for the grounds against the act or for an assessment; both are supplied beside it. Its
licence and lineage are not read. `WarrantInductorScoreSide.ShortfallAt` is a proposition of
the kind that would supply the verdict, and nothing here connects them.

**Consistency of conduct** (`ConsistentConduct`): each choice is permitted by the case base of
the assessed acts before it. By `permitted_iff` that is: the assessed past is rationalizable
and its reach does not put the grounds against the act at or above its grounds
(`consistentConduct_cons_iff`).

Fixtures on `(X, ¬X, D)`. The first act, on `P(X) ≥ 3/4` against `P(¬X) ≥ 1/2`, is assessed a
shortfall. *Forbidden*: a later choice on `P(X) ≥ 7/10` against `P(¬X) ≥ 3/5`
(`repeat_forbidden`); it would be permitted had the act's own proposal been the precedent
(`assessor_sets_precedent`). *Permitted by distinguishing*: a later choice on `P(X) ≥ 3/4` with
the ground `P(X) ≥ 9/10 · P(D)` beside it (`distinguished_consistent`).

**Better, or only allowed?** Still only allowed. A choice the holding backs has its reverse
forbidden (`backed_reverse_forbidden`), and making it sets no new precedent
(`reach_cons_of_backed`). Where a choice and its reverse are both permitted, the reach relates
their reason sets in neither direction (`permitted_both_silent`): between a permitted choice
and its permitted reverse the assessed past is silent. (Two permitted choices against a common
opponent may still have their grounds compared by the holding; nothing here reads that as a
ranking.) What the assessor's verdicts add is the order after the fact, and a price on the
assessor's side: a shortfall verdict on a choice the reach backs leaves the assessed case base
unrationalizable, after which nothing is permitted (`shortfall_of_backed_not_rationalizable`,
`assessor_bound`) — a consequence of the verdict, not a mechanism that prevents it. An order among reasons does accumulate — the holding grows and is a strict
order while the base is rationalizable — and it sorts continuations into permitted and
forbidden, with no degree between.

**Verdict: fits in part.**

### F3. Forgetting (C2, C3, C4)

**(a) Projection is computed.** `eliminate k L` is one Fourier–Motzkin step on the rows of `L`
with coordinate `k` moved last. Its rational solutions are exactly the restrictions of the
rational solutions of `L` to the other coordinates (`eliminate_sat_iff`); the rational witness
is by `RowAlternative.exists_rat_of_real`. For a bundle, `forget k B` has as its region the
projection of `B`'s region along the coordinate map that drops `k` (`forget_region`), and
`SeedStatics.project` on a bundle's system is the projection onto one coordinate
(`project_iff_projection`). **Exactness**: a row over the retained coordinates is forced by the
full bundle iff by the forgotten one (`forget_exact`); it has an entailment certificate against
one iff against the other (`forget_certified`); the change is conservative
(`forget_conservative`). The rows are computed. The certificates are shown to exist.

**(b) What may be forgotten.**

*A settled coordinate.* With `k` settled at `F`, the rows specialized at `F` and restricted to
the other coordinates give the projection of the forced region under every docket state and
every later settlement (`forget_settled`). What is read afterwards: those rows with their ports
and ids, the docket state, and the later settlement on the retained coordinates.

*A closed account.* `OpenIntegrityEvolution.Conservation` asks three things of an exposed
occurrence: that it stay exposed, that its receipts (`terminals`) not shrink, and that its
later account evaluate to what its earlier account evaluates to under a transport of
resolutions. An account with no live port evaluates to one resolution whatever the ports
resolve to (`closed_evaluate_const`), and every later substitution leaves its receipts, its
having no live port and that resolution unchanged (`closed_subst`). So the data `Conservation`
reads of it are the occurrence's identity, its multiset of receipts, and one resolution. Two
limits: `ObligationState` stores the whole account, so no state type holds less; and a receipt's
`Authority` stores the history prefix it was issued at.

*A live coordinate.* It is not safe in general: over `(X, Y)` with the one item
`P(Y) ≥ 3/4 · P(X)`, forgetting `X` before it settles leaves the whole cube on `Y`, exactly, by
(a). Once `X` settles true the full
record forces `P(Y) ∈ [3/4, 1]`; the reasoner that forgot holds `[0, 1]`. Forgetting `X` after
it has settled keeps `P(Y) ≥ 3/4` (`live_forget_cost`). The cost is `3/4` at the lower endpoint
and is no slack at the time of forgetting.

**(c) Loss as slack.** For forgetting steps `K t` that agree with reference steps `K₀ t` off
sets `B t` of worlds, a row with coefficients in `[lo, hi]` has, at every stage `T`, excess at
the held credence at most its excess under the reference schedule plus `(hi − lo)` times the
sum over `t < T` of the mass the credence held at stage `t` places on `B t` (`schedule_slack`,
by induction from `approx_step`). The reference is exact forgetting when its steps are maps of
worlds; the theorem compares two stochastic schedules and asks nothing of the reference. Where those masses are bounded by a sequence with bounded
partial sums, or a summable one, the bound is uniform in `T` (`schedule_bounded`,
`schedule_summable`).

**(d) Selective forgetting.** Two records over `(φ, A, B)`: the one obligation on `φ`,
`P(φ) ≥ 3/4 · P(a)`, runs through `A` in the first and `B` in the second. One of `A`, `B` must
be dropped; both then settle true. The choice made after seeing the record — drop the
coordinate the obligation runs through — leaves `φ ∈ [0, 1]` on both records. Dropping `A`
whatever the record leaves `[3/4, 1]` on the second, and dropping `B` leaves `[3/4, 1]` on the
first. The full record forces `[3/4, 1]` on both (`selective_forgetting`).

*The omission result.* It is `ReasonSupply.adverse_union`, restated as
`TransparentChain.omission_le_adverse`: for an extensional program `F` on sets of reasons with
adverse sensitivity `A`, the gain from omitting the reasons `s` is at most `Σ_{r ∈ s} A r`. The
fixture has that form — forgetting the coordinate removes exactly one row's effect, and the
gain, `3/4` at the lower endpoint, equals that row's adverse sensitivity. It is not shown to be
an instance, and in general it is not one: elimination replaces the rows through the dropped
coordinate by their combinations, which is not an omission from a set of rows; and the omission
bound holds whoever chose the omission, so it does not separate a fixed from an adaptive
choice, which is what the fixture exhibits. The instantiation is not made in Lean.

**What a bounded reasoner may retain, on these results.** A sufficient retained state, piece
by piece, each piece exact by one theorem above and the composition unproved: the docket state,
since defeat and withdrawal act through ports and ids; for every item of the seed and every
warrant — not only those live now, since `forget_settled` selects the live rows at the docket
state queried — its row specialized at the current settlement and restricted to the unsettled
coordinates, with its port or id, the settled coordinates and their pin rows going; every
unsettled coordinate; the holding of its case base on the reason sets it may meet, in place of
the cases; for each account with no live port, its receipts and the resolution it denotes; for
each live account, the account. Nothing here shows any of this necessary, and dropping an
unsettled coordinate is not always a loss — one fixture shows it can be. Not known: a space
bound — one elimination step can square the number of rows, `n` strengths carry `2 ^ n`
holdings, and a receipt carries a history prefix; whether these pieces compose into one
retained state (item 135); and what the market or the inductor must retain, which is out of
scope.

**Verdict: fits.**

### F4. A vocabulary change as an act (C5)

A **vocabulary change** (`VocabularyAct.VocabularyChange`) is an occurrence: its owner, the
translation, the old and new commitments as rows, and a declared protected fragment of old
rows.

- **Licence** (`Licensed`): for each protected row and each old cube row, an entailment
  certificate of its pullback against the new commitments. It exists iff the change refines the
  fragment (`licensed_iff_refines`).
- **Challenge** (`Challenge`): a row, an entailment certificate of it against a list of old
  rows, and a point of the new vocabulary. It is valid when the certificate weights only
  allowed rows, the point is a cube point of the new commitments, and the row's pullback fails
  there; validity is decidable (`Challenge.Valid`). A valid challenge is a broken commitment
  and every broken commitment has one (`Challenge.sound`, `challenge_complete`).
- **A licensed change admits no valid challenge on the protected fragment**
  (`licensed_no_challenge`); an unlicensed one admits one (`unlicensed_has_challenge`).
- Neither the licence nor that theorem reads the old commitments. `FragmentOfOld` — every
  protected row has an entailment certificate against the old commitments — is the relation
  that ties the fragment to them; under it a valid challenge on the fragment is a broken
  commitment of the old (`challenge_on_fragment_breaks_old`), and the split fixture satisfies
  it (`split_fragmentOfOld`). The occurrence is data on rows; nothing makes it a step of
  `OpenIntegrityEvolution`, and its licence is a statement about the old commitments at issue.
- For a change that adds one coordinate, adding nothing is one entailment certificate per row
  that elimination leaves (`addsNothing_certified`). For other translations a conservativity
  licence has no finite form here.

On the split fixture, the change protecting the two credence rows is licensed
(`split_licensed`), and the commitment `P(S) ≥ 1/2`, outside the fragment, is validly
challenged by the row itself and the credence `(1/5, 1/5, 3/5)` (`splitChallenge_valid`).

**Who may issue one is not determined.** `AuthorityModule.AuthAlloc` allocates matters to the
principal or the agent, and an act is licensed by a reference to a matter the agent holds
(`DecisionComponent.LicenseRef.Valid`; none on a reserved matter, `no_license_on_reserved`).
The module names no matter for vocabulary, and `Seed.con.protectedClass` is declared data that
nothing computes from. The `owner` field is carried and read by nothing.

**Three readings of a broken commitment**, as predicates on a recollection, a list of old
commitments and a new region; none is adopted. `Bars`: every commitment is kept. `Accounted`:
each is relaxed by a nonnegative charge. `Split`: a live commitment must be kept, any other is
relaxed by its charge. A commitment's **charge** is the largest excess of its pullback over the
new region (`Charge`), and each reading's verdict on one commitment is a function of it
(`readings_of_charge`).

| fixture | charge | bars | accounted | split, live | split, not live |
|---|---|---|---|---|---|
| split: `P(S) ≥ 1/2` against `P(S₁), P(S₂) ≥ 1/5` | `1/10` | refuses | admits, `1/10` | refuses | admits, `1/10` |
| abandonment: `P(S) ≥ 9/10` | `13/20`; at least `3/20` everywhere | refuses | admits, `13/20` | refuses | admits, `13/20` |
| `P(X∧Y) ≥ 3/4 · P(X)`, `X` unsettled, dropped and retold as a fair coin | `3/8` | refuses | admits, `3/8` | refuses | admits, `3/8` |
| the same, `X` retold as false | `0` | admits | admits, `0` | admits | admits |

(`split_charge`, `abandon_charge`, `half_charge`, `zero_charge`, with `readings_of_pos_charge`
and `readings_of_zero_charge`.) In the last row nothing is broken and all three readings admit
the change at no charge (`zero_admitted`), though the obligation is shed. Once `X` settles true
the pin `P(X) ≥ 1` is broken at every new credence, charged `1`, and `1/2` under the fair coin
(`zero_pin_charge`, `half_pin_charge`). A reading applied once, when the change is made, does
not see the shedding; a challenge raised later does. The queue entry
`open--broken-commitment-bars-or-accounts` carries this comparison and stays queued.

**Verdict: fits in part.** The licence and the challenge fit, as data beside the record; the
issuer is not determined and no reading of a broken commitment registers the fourth row.

### F5. Refinements

- **The adapter's certificates.** Every valid upper bound on a rational functional over a
  bundle's region has a cited functional certificate (`exists_citedFunctional`, from
  `certEntails_iff_sem`). So `Excludes` certificates exist where every inadequate response
  scores at most a rational `t ≤ τ` on the region (`excludes_of_region`), and `Margins`
  certificates at tolerance `0` where every margin witness scores at least a rational
  `t ≥ τ + δ` (`margins_of_region`). In the way of the rest: `τ` is real, and a threshold with
  no rational between it and the region's supremum needs that supremum rational and attained,
  which is not proved; and at a positive tolerance `Margins` multiplies the tolerance by the
  certificate's mass, which validity on the region does not bound.
- **The row logic** is stated once in `THEOREM.md`.
- **The digest.** `state/prs.json`, entry 142: `merged` is `2026-11-09`; the summary and
  `state_after` cover both passes, the latter stating the separate results and their limits.

**Verdict: fits in part.** The adapter's certificates exist below a rational threshold and at
tolerance `0`; the other two refinements are done as stated.

### The conjectures

| | conjecture | outcome | by |
|---|---|---|---|
| C1 | a holding is a sufficient statistic, bounded by the vocabulary of reasons | **narrowed**: sufficiency proved; over a finite set of forms the holding is eventually constant and permission with it, with no bound on the stage or on a representation's size; over the kinds of reasons alone there is no finite representation | `permitted_append_congr`, `holding_eventually_const_of_finite_forms`, `stairs_holding_injective` |
| C2 | forgetting is projection, exact on the retained fragment; settled sentences and closed accounts are safe, a live obligation is not | **proved**, the closed account as far as `Conservation` reads it | `forget_exact`, `forget_settled`, `closed_subst`, `live_forget_cost` |
| C3 | loss composes as slack; summable slack loses a bounded amount | **proved**, as a comparison of two stochastic schedules differing on sets of worlds | `schedule_slack`, `schedule_summable` |
| C4 | choosing what to forget is steering | **proved**, at one fixture, against choices of a fixed coordinate | `selective_forgetting` |
| C5 | a vocabulary change should be an owned, licensed, challengeable act | **narrowed**: the occurrence, licence and challenge are defined and the two theorems proved; the owner is not determined, and a licence at issue does not cover what the record gains later | `licensed_no_challenge`, `challenge_complete`, `zero_pin_charge` |
| C6 | decisions belong on the record; conduct held to its assessed past; an order among reasons accumulates | **narrowed**: all three hold at the fixtures; the order sorts continuations into permitted and forbidden and ranks none | `assessor_sets_precedent`, `permitted_both_silent`, `holding_mono` |

### What the follow-up does not establish

- **No retained state.** The pieces of F3's closing paragraph are separate theorems. Item 135.
- **No space bound.** The canonical reason sets over a finite set `Φ` of forms number at most
  `2 ^ |Φ|`; nothing bounds the stage at which the holding stops changing, and no theorem
  gives a least set of generators of a holding — the staircase's `2 ^ n` is an injectivity read
  as a count.
- **No necessary retention rule.** The retained state of F3's closing paragraph is sufficient
  piece by piece; nothing shows any piece necessary, and `live_forget_cost` shows that dropping
  an unsettled coordinate can lose, not that it must.
- **The fragment and the old commitments** are related only by `FragmentOfOld`, a declared
  relation the licence does not read.
- **The recollection.** Forgetting by projection is a retelling that is computed. For an
  unsettled coordinate the retelling is still chosen — as a fair coin or as false — and nothing
  here chooses. No stage is shown to recollect an earlier one.
- **C2's cost is not C3's slack.** `schedule_slack` bounds a schedule against the exact
  schedule, which may itself forget. The loss of `live_forget_cost` occurs under an exact step
  and is not bounded by it.
- **C4 is one fixture**: two records, one obligation, and the fixed choices are choices of a
  coordinate. A rule fixed in advance that names the coordinate by its role — drop the one the
  obligation runs through — reproduces the adaptive result; no theorem compares classes of
  policies, and nothing connects the fixture to the Logical Induction non-capture chain.
- **The assessed act is beside the docket.** `DocketState` is unchanged, `caseOf` is not
  replaced, the grounds against an act are not computed from `Grounds.survivors`, and the
  verdict is not tied to `Assessed`.
- **A rank characterization.** That a rationalizable base has a rank on its cases is not
  proved, nor that cycles of every length are minimal.
- **Several coordinates at once.** `forget_settled` and `forget_region` drop one coordinate;
  iteration is by `projection_comp`, with no theorem for a set.
- **Ports after forgetting.** The retained rows keep their ports and ids. Nothing shows when a
  port may be forgotten.
- **A licence over time.** `Licensed` is a statement about the old commitments at issue.
- **Charges.** One commitment at a time; no total, no budget. Liveness is declared.
- **Who may issue a vocabulary change.**
- **The adapter** at an irrational threshold or a positive tolerance.
- **The literature.** Le Cam's deficiency, the reason model of precedent, and Hegel's and
  Brandom's recollection are named in the dispatches and were not consulted. Nothing is cited.

### External review

GPT-6 Astra (OpenAI), via `codex`, reviewed the follow-up on pull request #142 at `8a5b591f` on
2026-11-09, read-only; its text is `prompts/2026-11-08-content-recollection/REVIEW-astra-followup.md`,
verbatim. Its merge word: **fix-then-merge**. It found the theorem statements supporting the
restricted results and the registry and digest promoting stronger ones. One review pass and one
fix pass; the fixes are in the commits that add this section.

| finding | disposition |
|---|---|
| **Blocking.** The size claims overreach: a finite set of kinds and strengths does not make `R` finite without canonical representatives and an invariance theorem; the staircase proves deletion-irredundance, not a representation-size bound; the registry's "number of cases a holding needs" exceeds its statement | fixed: `holding_congr_covers`, `normal`, `reasonSets` (at most `2 ^ |Φ|`), `holding_eventually_const_of_finite_forms`, `permission_eventually_const_of_finite_forms`; `stairs_permitted_iff`, `stairs_holding_injective` (two staircases with the same holding have the same steps, so `n` strengths carry `2 ^ n` holdings); §F1, the registry notes of `precedent.permitted-iff-reach` and `precedent.staircase-irredundant`, `THEOREM.md`, item 117, the 2026-11-09 holding entry, the README and the digest reworded; that neither the stage nor a representation's size is bounded is stated |
| **Blocking.** The digest's `state_after` claims a combined bounded-memory result the report leaves open, and reads a closed account as receipts alone | fixed: rewritten as the four separate results and their limits, the closed account as receipts and the resolution it denotes |
| "The assessed past never ranks two permitted alternatives" overgeneralizes `permitted_both_silent`, which concerns a choice and its reverse | fixed: §F2 says so, and names the case it does not cover |
| `shortfall_of_backed_not_rationalizable` is a consequence of a verdict, not a mechanism enforcing compliance | fixed: §F2 and the README |
| The retention paragraph should be a sufficient proposal, not a necessity rule; retaining only rows live now is not justified, since `forget_settled` selects live rows at the queried docket state | fixed: §F3's closing paragraph says what is sufficient, piece by piece, that nothing is shown necessary, and that every item's row is retained; the registry note of `content.forget-settled` and `THEOREM.md` say what the theorem reads |
| `live_forget_cost` shows that forgetting an unsettled coordinate can lose, not that it must | fixed: §F3, the README, the digest and the 2026-11-09 forgetting entry say *can* |
| `K₀` is a reference schedule; nothing certifies it as exact forgetting | fixed: *reference* throughout — the Lean header and docstrings of `Forgetting.lean`, `THEOREM.md`, the registry entry, §F3 and the conjecture table |
| Nothing relates `fragment` to `old`; the licence never reads `old` | fixed: `FragmentOfOld`, `challenge_on_fragment_breaks_old`, `split_fragmentOfOld`; §F4, the registry note, `THEOREM.md`, the 2026-11-09 vocabulary entry and *What the follow-up does not establish* say the relation is declared |
| The occurrence is data, not a docket occurrence checked by the account system | fixed: §F4, item 134 and the registry note say so |
| Abandonment's "every change" holds for nonempty regions of credences | fixed: the queue table says *whatever the new credences* |
| F11 is filed where the contained-fix rule would let the round take it; the deferral is unexplained | fixed: the deviation states the reason |
| F5 has no fit verdict | fixed: *fits in part* |
| Living-document residue: item 79's "as open as before", the README's "the case the docket lacked" | fixed |
| Item 118's body still says rational attainment is absent | **disputed**: the Item section is the request as filed, its heading note states what is proved, and its status is the maintainer's word (ruling G3; outstanding action 3) |
| The README repeats the report at length and mixes present and past | **disputed in part**: the verdict line is the round record's verdict, which `state/rounds.json` carries by `verdict_source`; its follow-up sentences are reworded where the review found the residue |
| C4 should keep its fixed-coordinate qualification | fixed: §F3, the conjecture table, the registry note, *What the follow-up does not establish* |
| *What the follow-up does not establish* should name normalization and minimum-generator bounds, the fragment relation, and the absence of a necessary retention rule | fixed: three entries added |
| The PR description and auto-merge setting could not be read (GitHub's API was unavailable to the reviewer) | the description is updated with this pass and carries the attribution section; auto-merge is off |

### Verification

Local, Python 3.12, on the tree with `main` merged in at `eb98367e`, each long gate run once
before the external review and once after the fix pass.

- `~/.claude/scripts/safe-lake.sh build Workspace`: `Build completed successfully (4113 jobs)`.
- `python3.12 tests/audit_axioms.py`, one run after the fix pass: `AXIOM AUDIT: 3963 results
  across 123 files, all within ['Classical.choice', 'Quot.sound', 'propext']` (3945 before it).
- `python3.12 tests/run.py`, one run: `ALL GREEN (80 project(s))`; `LEAN SORRY GATE: clean over
  123 files`; `SITE DOM GATE: app boots, 73 capsules, 151 edges, cards open, fragments present,
  no overlaps`; `LEAN BUILD SKIPPED`, the build above being the Lean verification.
- `python3.12 -m checkers.run`: `97 entries, 1 adjudicated here`; the ten entries of the
  follow-up `lean-proved`, adjudicated by the Lean gate.
- `python3.12 -m checkers.workspace_state --check`: `WORKSPACE STATE: valid — 7 projects, 202
  modern claims, 1 foundations, 180 foundation claims, 134 rounds, 52 terms, 147 priorities, 10
  interface objects`, after `--write-handoff`.
- `python3.12 -m checkers.wiki_state_bindings`: `clean over 35 page(s); 3 binding(s) verified
  against the state emission`.
- `python3.12 -m checkers.wiki_links`: `clean over 33 page(s)`.
- `python3.12 -m checkers.attention_render --check`: `the committed file equals the render (147
  items)`.
- `python3.12 -m checkers.graph --root .`: `OK 2569 nodes, 2603 events, 2094 ranked units`, with
  the standing warning on decision anchors without a node.
- `python3.12 tests/freshness.py`: exit status 1 with two findings, both `main`'s: merged pull request #139 has no
  digest in `state/prs.json`, and the round `2026-11-09-github-sign-in` appears in no digest.
  Neither is this pull request's to write; the audit calls each work for a round and not a
  merge blocker.

CI on pull request #142: all seven required checks passed at `0ac5aaa1` (before the review) and
at `d6df8a9b` (after the fix pass): `checkers` 5m, `lean` 13m, `python` 16m, the rest seconds.

### Registrations, items, names

Against 117: `precedent.permitted-iff-reach`, `precedent.staircase-irredundant`,
`precedent.assessor-sets-precedent`. Against 134: `content.forget-region-is-projection`,
`content.forget-settled`, `content.licensed-no-challenge`. Against 135:
`memory.live-forget-cost`, `memory.schedule-slack`, `memory.selective-forgetting`. Against 118:
`seed.adapter-certificates-exist`. All `lean-proved`. Listed and not registered: every other
declaration of the five modules.

Filed: 135 (the retained state of a forgetting reasoner); F11 (no gate refuses committed
conflict markers). Narrowed: 134 (clause (d) for one coordinate; the occurrence on rows).
Noted: 117, 118, 119, 79.

Names, provisional: *holding*, *reach*, *agree on*, *staircase*, *step*, *against*, *humble
scale*, *merged discord*; *assessed act*, *verdict*, *proposal*, *case* (of an assessed act),
*consistent conduct*, *backed*; *eliminate*, *forget*, *drop coordinate*, *drop settlement*,
*chain*, *schedule loss*, *interval* (of a region), *after forget*; *vocabulary change* (the
occurrence), *licensed*, *challenge*, *broken along*, *region of*, *relax*, *bars*,
*accounted*, *split* (the reading), *charge*.

## Outstanding maintainer actions

1. **Merge or decline the pull request.** Auto-merge is off.
2. **Rule on whether a broken commitment bars a change or is accounted** — `DECISIONS.md`,
   *Awaiting the author*, the 2026-11-08 entry (`open--broken-commitment-bars-or-accounts`),
   which now carries the three readings compared on four fixtures.
3. **Close item 118, or name what remains**: set `item_status` in
   `graph/nodes/item-118.md` and run `python3.12 -m checkers.attention_render --write`.
