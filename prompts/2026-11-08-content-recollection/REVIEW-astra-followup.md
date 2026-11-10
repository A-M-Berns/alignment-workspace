Reviewed head `8a5b591f`, after fetching `origin/main`. No Lean build or tests run. GitHub’s API was unavailable, so I could not verify the current PR description or auto-merge setting.

**1. Holding, C1.**

The sufficiency result is supported. [PrecedentHolding.lean:113](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/PrecedentHolding.lean:113) states:

```lean
Holding (c :: Γ) V U ↔
  Holding Γ V U ∨ (Reach Γ V c.winners ∧ Reach Γ c.losers U)
```

The forward induction separates old edges from uses of the new case; repeated uses need only the first entrance and last exit. The converse inserts the new case between those two reaches. Both directions work without assuming rationalizability.

At lines 159–170:

```lean
Permitted Γ c ↔ Rationalizable Γ ∧ ¬ Reach Γ c.losers c.winners
```

The forward direction excludes both an existing cycle and a cycle through `c`; the reverse decomposes any purported cycle using `holding_cons`. `Reach` is necessary: even an empty base forbids a case whose losers cover its winners, although its holding is empty.

Lines 193–202 give the advertised continuation and minimality comparisons:

```lean
Permitted (cs ++ Γ) c ↔ Permitted (cs ++ Γ') c

(∀ c, Permitted Γ c ↔ Permitted Γ' c) ↔
  ∀ V U, Reach Γ V U ↔ Reach Γ' V U
```

The first assumes equal holdings; the second assumes both bases rationalizable. `holding_not_minimal`, lines 233–245, supplies equal permissions and reach but unequal holdings. Thus holding is sufficient and strictly finer than immediate permission observes.

**The size claims overreach.** At [lines 256–294](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/PrecedentHolding.lean:256), `agreeOn_cons` requires the continuation’s winners and losers to belong to `R`; stabilization states:

```lean
∃ N, ∀ n, N ≤ n → reachSet R (Γ n) = reachSet R (Γ N)
```

Here `R : Finset (List (Form d))`. This bounds the restricted relation by `|R|²` possible pairs, with a rationalizability bit for continuation. It does not bound the stabilization date, the full holding, or its representation size. Permission stabilization additionally assumes an initially rationalizable base and permitted continuations.

This is **not yet the finite-strength-grid result**. Lists over even one available form have unbounded length through repetition. The report’s assertion that finite kinds and strengths make `R` finite ([REPORT.md:493](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md:493)) needs canonical representatives and an invariance theorem—naturally, maximal strength per kind.

The staircase statement is exactly:

```lean
¬ Permitted (staircase s n) (against s i) ∧
  Permitted ((staircase s n).filter fun c => c ≠ step s i) (against s i)
```

under `StrictMono s` and `i < n` ([line 324](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/PrecedentHolding.lean:324)). It proves arbitrarily large deletion-irredundant bases. It does **not** quantify over alternative generators of the same holding or establish a representation-size lower bound. Consequently the registry’s “number of cases a holding … needs” is stronger than its statement of record.

Accumulation is only partly delivered: `holding_mono` proves growth under inclusion, even without permission; eventual constancy is proved for **restricted reach and permissions**, not stated for the whole holding over a finite vocabulary. C1 **narrowed** is appropriate, but the claimed size refutation needs narrowing too.

The merged-discord fixtures match their descriptions. Their conclusions are respectively:

```lean
Rationalizable [precedent] ∧ Rationalizable [forbidden] ∧
  ¬ Rationalizable ([precedent] ++ [forbidden])

Rationalizable cycleHead ∧ Rationalizable cycleLast ∧
  Consistent (cycleHead ++ cycleLast) ∧
  ¬ Rationalizable (cycleHead ++ cycleLast)
```

([lines 428–451](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/PrecedentHolding.lean:428)). “Resembles” item 119, with the rank/difference-constraint reduction unproved, is the correct qualification.

**2. Assessed conduct, C6.**

[AssessedConduct.lean:56–98](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/AssessedConduct.lean:56) implements the requested abstract reading:

```lean
| .adequate => ⟨a.grounds, a.against⟩
| .shortfall => ⟨a.against, a.grounds⟩
```

`against` is supplied data, not proven surviving grounds. `ofCertificate` genuinely needs only `⟨cert.grounds, against, v⟩` at `Ent := Form d`. [ActCertificate:1027](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Deference/Contrib/DecisionComponent.lean:1027) has grounds, licence and lineage, but neither opposition nor assessment. No connection to `WarrantInductorScoreSide.Assessed` is made; the report says so.

With newest acts first:

```lean
ConsistentConduct (a :: past) =
  (Permitted (caseBase past) a.proposal ∧ ConsistentConduct past)
```

This expresses consistency against the supplied assessed history; ownership of that history is an interpretation, not another checked field.

The fixtures meet the request:

```lean
¬ Permitted [first.case] (again v).proposal ∧
  Permitted [first.proposal] (again v).proposal

¬ ConsistentConduct [again v, first]
ConsistentConduct [distinguishedAct, first]
```

([lines 165–182](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/AssessedConduct.lean:165)).

“Still only allowed” is accurate about the absence of a continuation-ranking mechanism. But [REPORT.md:544](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/projects/normativity/rounds/2026-11-08-content-recollection/REPORT.md:544), “the assessed past never ranks two permitted alternatives,” overgeneralizes:

```lean
(h₁ : Permitted Γ ⟨V, U⟩) (h₂ : Permitted Γ ⟨U, V⟩) :
  ¬ Reach Γ V U ∧ ¬ Reach Γ U V
```

This concerns a choice **and its reverse**. A base asserting `V > W`, with three distinct singleton kinds `V,W,U`, can permit both `V > U` and `W > U` while its holding still compares `V` with `W`.

The backed-choice results and assessor warning are correctly described:

```lean
¬ Permitted Γ ⟨c.losers, c.winners⟩
Reach (c :: Γ) V U ↔ Reach Γ V U
¬ Rationalizable (caseBase (a :: past))
```

The last requires a shortfall verdict and prior reach from grounds to opposition; it establishes a consequence of assessment, not a mechanism enforcing assessor compliance.

**3. Forgetting, C2–C4.**

Projection is correctly connected and exact. [Forgetting.lean:139](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:139) states:

```lean
SatAll (eliminate k L) x ↔ projection k.succAbove (SatAll L) x
```

`toLast_sat` correctly moves `k` last; `ofLin_satR` requires non-strictness, which elimination preserves. `elim_sat_iff` supplies the real extension. Crucially, `fixRows` pins **both bounds** of every retained rational coordinate before `exists_rat_of_real` is applied, so rationalization preserves the requested `x`.

The bundle and consequence statements are:

```lean
(forget k B).Region x ↔ projection k.succAbove B.Region x

Forces B.Region (Conservativity.pull (Translation.ofMap k.succAbove) r) ↔
  Forces (forget k B).Region r
```

([lines 182–209](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:182)). `project_iff_projection`, lines 246–264, separately connects the actual iterated `SeedStatics.project` to rational one-coordinate projection. The computation produces rows; certificate existence is a further theorem.

For settled forgetting, [lines 287–293](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:287) require `F.val k = some b` and `F.le F'` and conclude:

```lean
projection k.succAbove (forcedRegion S W st F') x ↔
  InCube x ∧ (dropSettlement k F').Pinned x ∧
  (∀ it ∈ S.liveSub st ++ W, (dropCoord k (specialize F it.form.row)).Sat x) ∧
  (∀ it ∈ S.liveStr st, (dropCoord k (specialize F it.row)).Sat x)
```

“Every docket state and later settlement” matches these quantifiers, for the supplied `S,W`. It does not establish an evolving compressed state. In particular, retaining only rows live **now** is not justified for arbitrary future docket states: the theorem selects live rows from the original seed at the queried `st`.

For closed accounts, the conclusions are:

```lean
t.evaluate v = t.evaluate v'

(t.subst hab replacement).terminals = t.terminals ∧
  (t.subst hab replacement).livePorts = 0 ∧
  ∀ v v₀, (t.subst hab replacement).evaluate v = t.evaluate v₀
```

under `t.livePorts = 0` ([lines 747–777](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:747)). Identity/exposure, terminal receipts and denotation describe what `Conservation` observes of a closed account. This is not a minimality theorem or a replacement-state construction. Both reported limits are real: accounts remain programs, and receipts contain historical authority data.

The live fixture is nonempty and exact: its three conjuncts give the initial projection `↔ InCube x`, the attained interval

```lean
IsForcedInterval liveSeed [] DocketState.quiet settledX 1 (3/4) 1
```

and the settled projection `↔ InCube x ∧ 3/4 ≤ x 0` ([line 352](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:352)). It shows that unsettled forgetting **can** lose later constraints, not that every unsettled coordinate necessarily does.

The schedule induction is sound. Its statement is:

```lean
excess r ((chain K T).push q) ≤
  excess r ((chain K₀ T).push q) + (hi - lo) * scheduleLoss K B q T
```

([lines 441–464](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:441)). Composition applies `K T` after the preceding chain. The induction pulls the terminal row through `K₀ T`, preserves its coefficient bounds, then adds the current `approx_step` error. `schedule_summable` replaces accumulated mass by `∑' t, (ε t : ℝ)`.

This bounds signed row-excess discrepancy between two stochastic schedules. `K₀` is a reference schedule; no hypothesis independently certifies it as exact forgetting. It bounds neither interval loss nor retained-state size. The report correctly separates this slack from C2’s cost.

Selective forgetting proves the six advertised interval conjuncts ([lines 726–733](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/Forgetting.lean:726)):

```lean
(IsInterval (afterForget 1 1 later) 0 0 1 ∧
 IsInterval (afterForget 2 2 later) 0 0 1) ∧
(IsInterval (afterForget 2 1 later) 0 (3/4) 1 ∧
 IsInterval (afterForget 1 2 later) 0 (3/4) 1) ∧
(IsForcedInterval (recOn 1) [] DocketState.quiet bothTrue 0 (3/4) 1 ∧
 IsForcedInterval (recOn 2) [] DocketState.quiet bothTrue 0 (3/4) 1)
```

It is not empty: endpoints are attained, and each comparison uses the same record and restricted later settlement. It separates adaptive coordinate choice from a **constant coordinate choice** across two records. A policy fixed beforehand that says “drop the coordinate carrying the obligation” reproduces the adaptive result; the theorem does not separate general policy classes. The report’s explicit limitation acknowledges this.

The omission attribution is accurate:

```lean
F actual - F ref ≤ ∑ r ∈ ref \ actual, A r
```

under `Adverse F A` and `actual ⊆ ref` ([TransparentChain.lean:72](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Deference/Contrib/TransparentChain.lean:72)). The claimed `3/4` sensitivity is an informal singleton interpretation, not an instantiated theorem. Elimination generally combines rows, so declining the general omission instantiation is justified.

The closing retention paragraph should be phrased as a conservative proposal. Neither necessity of retaining every mentioned unsettled coordinate nor sufficiency of keeping only currently live items is proved.

**4. Vocabulary acts, C5.**

[VocabularyAct.lean:82](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/VocabularyAct.lean:82) supplies owner, translation, old/new rows and fragment. Licence is a separate property; challenge is a separate structure. That arrangement supports the static theorems, but it is not yet a docket occurrence checked by the existing account system.

Another unstated limitation: nothing requires `fragment` to be contained in, or entailed by, `old`. The licence and protected-fragment theorem never read `old`.

The substantive claims are supported:

```lean
Licensed V ↔ Refines V.T (regionOf V.fragment) (regionOf V.new)

(h : Licensed V) (c : Challenge d d') : ¬ c.Valid V V.fragment

(h : BrokenAlong V.T (regionOf Γ) (regionOf V.new) r) :
  ∃ c : Challenge d d', c.Valid V Γ ∧ c.row = r
```

([lines 98–157](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/VocabularyAct.lean:98)). Validity checks finite certificate-row membership, a rational cube point satisfying new rows, and failure of the pulled row. Its `Decidable` instance is computational. `BrokenAlong` generalizes `Broken`; for `K.toTranslation` their equivalence is literally `Iff.rfl`.

The authority limitation is fair: `LicenseRef.Valid` reads a delegated matter, and no vocabulary matter or owner-to-allocation connection is supplied.

The readings are accurately represented by [lines 301–304](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/VocabularyAct.lean:301):

```lean
(Bars K [r] R' ↔ s ≤ 0) ∧
(Accounted K [r] R' t ↔ 0 ≤ t r ∧ s ≤ t r) ∧
(Split K [r] R' live t ↔ (live r → s ≤ 0) ∧ 0 ≤ t r ∧ s ≤ t r)
```

The six charge statements give `1/10`, `13/20`, `3/8`, `0`, `1/2`, and `1`, respectively; abandonment additionally gives excess at least `3/20` everywhere. Thus every report/queue table entry follows, with abandonment’s “every change” restricted to nonempty regions of normalized credences.

The fourth row is correctly admitted even when declared live:

```lean
Bars zeroK [liveRow] simplex2 ∧
  Accounted zeroK [liveRow] simplex2 (fun _ => 0) ∧
  ∀ live : Row 4 → Prop, Split zeroK [liveRow] simplex2 live fun _ => 0
```

([line 422](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/VocabularyAct.lean:422)). Liveness affects positive-charge split verdicts; it cannot affect zero charge. Calling this a live obligation relies on the declared reading—there is no docket obligation here. Later pin failure is proved statically; a persistent challenge process is not. No reading is adopted.

**5. Refinements and digest.**

[AdapterCertificates.lean:45](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/lean/Workspace/Normativity/Contrib/AdapterCertificates.lean:45) proves:

```lean
(h : ∀ y, B.Region y → ∑ j, ℓ j * y j ≤ v) :
  ∃ c : CitedFunctional d ℓ, c.CitesLive B ∧ c.cert.value ≤ v
```

The conversion from entailment certificates preserves coefficients and supplies valid citations, including cube rows. The refinements conclude:

```lean
∃ upper, ({ P with upper := upper } : Problem d Q).Excludes B
∃ lower, ({ P with lower := lower } : Problem d Q).Margins B 0
```

They require a separating rational threshold in the stated direction. They replace the certificate fields; they do not validate arbitrary existing certificates. The report correctly identifies the remaining rational-optimum argument and the positive-tolerance certificate-mass issue.

The row-logic section matches the definitions, including cube-relative semantics and completeness without nonemptiness:

```lean
CertEntails Γ g ↔ SemEntails Γ g
IncEntails Γ g ↔ CertEntails Γ g
```

The predicates table is accurate subject to the fragment qualification above.

[The digest:2311](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/state/prs.json:2311) has the requested date and extended fields. **Its `state_after` at line 2328 is materially overstated:** “the record need not grow” and “forgetting any of these is computed and exact” claim a combined memory result the report expressly leaves open. Closed accounts also require denotation, not receipts alone. Replace this with the separate established results and their limits.

**6. Registry and filed items.**

All ten records point to genuine theorem declarations, not definitions. Their hypothesis packages have concrete inhabitants; none depends solely on an impossible premise.

| Claim | Inhabitation evidence | Scope assessment |
|---|---|---|
| `precedent.permitted-iff-reach` | No proof assumptions; permitted/forbidden fixtures | Accurate; item 117 is relevant |
| `precedent.staircase-irredundant` | `humbleScale_spec`, `staircase_witness` | **Size inference exceeds theorem** |
| `precedent.assessor-sets-precedent` | Concrete acts; either `Verdict` | Accurate fixture; item 117 |
| `content.forget-region-is-projection` | No proof assumptions; live-seed regions | Accurate; item 134 |
| `content.forget-settled` | `forget_settled_witness` | Accurate for supplied seed and warrants |
| `content.licensed-no-challenge` | `split_licensed` | Accurate on independently declared fragment |
| `memory.live-forget-cost` | Closed fixture with attained endpoints | Accurate fixture; item 135 |
| `memory.schedule-slack` | `schedule_slack_witness` | Accurate comparison bound; “exact” is interpretive |
| `memory.selective-forgetting` | Closed, attained interval fixtures | Accurate for fixed coordinates |
| `seed.adapter-certificates-exist` | `citedFunctional_witness` | Accurate; item 118 |

The named witnesses are documented in [THEOREM.md:147–254](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/projects/normativity/rounds/2026-11-08-content-recollection/THEOREM.md:147). The sampled formal-result nodes distinguish record, bridge and completeness; they do not cure the staircase’s overbroad registered reading.

[Item 135](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-08-content-recollection/graph/nodes/item-135.md:38) is a self-contained exploratory specification with deliverables, acceptance criteria and consumers. Its filing is within scope. F11 is a second item, exceeding the literal cap; this is declared, and friction reporting is independently required by AGENTS.md.

**7. Outcomes.**

C1 narrowed is earned after correcting its size claims. C2 is proved at the stated projection/substitution level, with a counterexample to generally safe unsettled forgetting; it does not prove a necessary retention rule. C3 is proved as the explicitly restricted stochastic comparison theorem. C4 is proved for the two-record/fixed-coordinate fixture. C5 and C6 narrowed are appropriate, with the additional missing fragment-to-old invariant and the F2 overstatement identified above.

The four fit verdicts are defensible at those scopes. F5 lacks the per-matter fit verdict requested by the dispatch. “What the follow-up does not establish” should additionally name normalization/minimum-generator bounds, the unchecked fragment relationship, and the absence of a necessary retention characterization.

**8. Standards and mechanics.**

The first-pass report edits match the declared correction locations. The inherited site decisions are not this round’s work. The merge retained them and removed the three actual markers present in `eb98367e`; I found no grounds to treat that as a covert ruling change.

Names are marked provisional; literature is explicitly unconsulted rather than cited through remembered identifiers. Follow-up provenance consistently says Claude Fable 5.1, `ci-only`, with prompt-author model unrecorded; commit trailers agree. PR-level attribution remains unverified because the API read failed.

The wiki count edit and second item are declared departures. F11’s deferral should explain why the contained-fix rule was not applied. Living-document cleanup remains: item 79’s “as open as before,” the README’s “case the docket lacked,” and item 118’s body still asserting that rational attainment is absent. The long README repeats the report and preserves incompatible present/past descriptions. The queue comparison itself retains a live unresolved decision rather than adopting a reading.

Ranked defects:

1. **Blocking — unsupported size claims:** correct the finite-grid assertion and staircase minimum-size inference in the report, registry, map and derived status text, or supply the missing normalization/lower-bound results.
2. **Blocking — premature current-state claim:** rewrite `state/prs.json:2328`; no combined bounded-memory construction or computed account/holding compression is established.
3. **Should-fix — overbroad interpretation:** restrict F2’s “never ranks” to reversed choices; present the retention paragraph as sufficient guidance with assumptions, not a proved necessity rule.
4. **Should-fix — incomplete vocabulary contract:** disclose or enforce the relationship between `fragment` and `old`; describe the object as proposed occurrence data pending docket integration.
5. **Note — scope and editorial record:** explain F11’s deferral, add F5’s verdict, and remove stale living-document prose. Preserve the fixed-coordinate qualification for C4.

The most important thing the follow-up’s own report oversells is **C1’s size conclusion**: deletion-irredundance and stabilization on a supplied finite universe are presented as settling representation bounds they do not establish.

**fix-then-merge**

The theorem statements support the restricted results, but the registry and current-state digest promote stronger conclusions. Correct those claims and the identified interpretation gaps before merging.