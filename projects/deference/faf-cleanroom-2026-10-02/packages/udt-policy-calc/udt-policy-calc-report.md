# udt-policy-calc report

Written 2026-09-29/30 by the formalizer agent of the faf-cleanroom run (Fable 5.1, [scrubbed]), against `udt-policy-calc-mandate`. Companion files: [udt-policy-calc-ledger](udt-policy-calc-ledger.md) (one row per headline), [udt-policy-calc-findings](udt-policy-calc-findings.md) (findings about the sources), `udt-policy-calc-open.txt` (empty: no open statements). Lean: `Cleanroom/Udt/UdtPolicyCalc/{Defs,LocalGlobal,Determination,Newcomb,TransparentNewcomb,Games,Tree,Simplification,Update,Toys,SelfSealing}.lean`, root module `Cleanroom/Udt/UdtPolicyCalc.lean`, namespace `Cleanroom.Udt.UdtPolicyCalc` (sub-namespaces `Opaque`, `Transparent`, `Tree`, `Simplification`, `SelfSealing`).

## State of the package

- **Every core target is proved; no open statements; gate PASS.** `scripts/wp-audit Cleanroom.Udt.UdtPolicyCalc` (and again naming all twelve modules) printed PASS after the last edit: axioms used are exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no custom syntax. Kernel replay is the consolidation phase's.
- **The five load-bearing headlines** (mandate §1) are `P`/`C` at grade (a) with N+ witnesses: (1) `Transparent.edt_ne_udt_transparent` with `edt_ne_udt_uniform_witness`; (2) `exists_localOptimum_not_optimal` (T3) and `Separable.isOptimal_of_isLocalOptimum` + `sup'_eq_sum_sup'_of_separable` (T4) with `separable_of_rtest`/`Separable.exists_rtest`, `weighted_sum_sup'_eq_sup'_sum`; (3) `Tree.isNashEquilibrium_iff_isLocalOptimum_V` over EconCSLib's `IsNashEquilibrium` on FAF's `(instanceGame _).toStrategic`, and `Tree.exists_env_of_policyUtility`; (4) `Simplification.rhs_argmax_ne_lhs_argmax` and `rhs_eq_lhs_of_concentrated`; (5) `Tree.score_eq_V` with `t14_witness` and the policy-dependent failure `cm_score_ne_V`.
- **Definitions of record** shipped first (`Defs`, committed 2026-09-29): `Policy`, `Function.update` as modification, `IsOptimal`, `IsLocallyOptimal`, `IsLocalOptimum`, `IsArgmax`, `IsStrictArgmax`, `LocalGlobal`, `Separable`, `CrossSituationDependence`, `RTest`, `FSADependence`, `OrdSep`, `FinDist`, `mass`, `condExpJunk`, `condProbJunk`, `event`. No definition of record was renamed after its first commit. Later files added `instanceGame`/`directGame` (Games), `Tree.Leaf/Node/Pol/Env/runLaw/V` (Tree), `Tree.ActionEnv/liftEnv/score` (Update), and the `Transparent.*` model.
- **Stretch done**: T14's policy-dependent failure witness (`cm_score_ne_V`), T15(a)'s series (`mean_correction_time`), T15(b) exact stationary law and (c) `perEpisodeValue`; the §5 extension in full (`Separable ⊊ OrdSep ⊊ LocalGlobal`); udt-rep-2-020's three toy problems; `edt_oneBoxes_opaque` for 2-031(b). Not attempted: the "flip then update" order of T15(b) as Lean (recorded in the findings), and the mandate's optional OPEN question on the decidability of `LocalGlobal` below `|A|^{|S|}` enumeration (a question, not a claim; not listed as an open *statement*).
- **Mandate deviations, disclosed**: (i) T14 is stated for *action* environments `e₀ : Node → A → FinDist O` lifted by `e π h := e₀ h (π h)`, not the mandate's "policy-independent `e : Node → FinDist O` lifted by ignoring `π`", which would make `V e U` constant in `π` and the theorem vacuous ([udt-policy-calc-findings](udt-policy-calc-findings.md) §12); the mandate's "`pH` independent of `π`" is proved in its correct form `pH_eq_of_agreesOff`. (ii) `runLaw` is the closed product `∏ k, (e π (prefixOf l k)).w (l k)` as the mandate asks; `runLaw_sum_one` is proved through a downward induction on the prefix length (`sum_suffixLaw`) rather than `Fintype.prod_sum`, because the factors depend on the prefix, not only on the coordinate. (iii) T9's threshold theorem is the non-strict `IsOptimal (V ε) (one,two) ↔ ε ≤ 999/1999` (ties allowed in `IsOptimal`), with strict uniqueness as a separate theorem for `0 < ε < 999/1999`. (iv) T15(b) fixes the order "update then flip"; the other order is a findings paragraph.
- **Hypothesis provenance**: every hypothesis of every headline is grade (a) — derived, or an explicit scope variable (a full-support prior, `0 < ε < 999/1999`, `0 ≤ W ≤ 1`, `AgreesOff π π' h`) — except T6's `PolicyDetermined`, disclosed as **(c)** in every docstring and ledger row. There is no (b).
- **Contamination: none.** Nothing under `research/faf-lab/`, no transcript, no unfiltered git history was read. `research/README.md` and the inventories mention the earlier run; those links were not followed.
- Size: eleven files, about 4,200 lines of Lean; 752 declarations audited by the gate.

## Representation of record, and why

Carriers `S`, `A` are arbitrary `Type`s with `Fintype`/`DecidableEq` where a statement needs them (`Nonempty A` only where a `sup'` needs it); `Policy S A := S → A` is an `abbrev`. Modification is `Function.update`; the source's hand-rolled `modify` is kept only for `modify_eq_update`. Utilities are `ℝ`-valued with `ℚ` witnesses cast in, so `norm_num` closes every numeric cell. Probabilities are `FinDist` weight functions (non-negative, sum one) — not `PMF`, not `Measure` — and every conditional expectation is `condExpJunk w f E j` with the junk value `j` explicit; the C&T convention is `j = −1` throughout. Argmax is the predicate `IsArgmax` (ties allowed); headline verdicts are strict inequalities between named candidates or `IsStrictArgmax`. Games: `instanceGame U : SafeParetoImprovements.Game S (fun _ => A)` (FAF's object) with Nash being EconCSLib's `IsNashEquilibrium` on `(instanceGame U).toStrategic`; the direct form `directGame U : StrategicGame S ℝ` is what proofs compute with, and `isNashEquilibrium_instanceGame_iff_directGame` identifies the two. Post 1's tree: `Leaf O n := Fin n → O`, `Node O n := Σ k : Fin n, (Fin k → O)`, `Pol := Node → A`, `Env := Pol → Node → FinDist O`, `runLaw e π l := ∏ k, (e π (prefixOf l k)).w (l k)`, `V e U π := ∑ l, runLaw e π l * U l`. Not a bridge package: no bridge to `dp-core-tree`, `udt-bli-core` or `udt-harmony-bargain` (plan §0.4 rule 10); the one bridge inside the package — abstract `U : (S → A) → ℝ` versus Post 1's `V e U` — is T12(c).

Two-situation witnesses use a table `tbl v00 v01 v10 v11 : (Fin 2 → Fin 2) → ℝ` with `forall_policy2` (quantification over the four policies) and `policy2_sum`; the transparent-Newcomb model uses `Transparent.mk af ae` with `forall_tpolicy` and `tpolicy_sum`. Depth-two environments use `Tree.mkEnv2` (root law and depth-one law) with `V_two`, `pH_two`, `contVal_two`, `offMass_two`.

## Targets

Each section: the claim, the Lean, Kind, status, hypothesis provenance, witness and grade, and what resisted.

### T1 — Definitions of record (`core`, D)

`Policy`, `modify_eq_update` (L: the source's `π[o ↦ a]` is `Function.update`; its `modify_self`/`modify_at`/`modify_other` are `update_eq_self`/`update_self`/`update_of_ne`), `IsOptimal`, `IsLocallyOptimal` (the source's three-argument shape), `IsLocalOptimum`, `isLocalOptimum_iff` (L), `IsArgmax`, `IsStrictArgmax`, `LocalGlobal`. One copy; no `inArgmax` ([udt-policy-calc-findings](udt-policy-calc-findings.md) §10). Status proved.

### T2 — Global ⟹ local (`core`, T)

`isLocalOptimum_of_isOptimal : IsOptimal U π → IsLocalOptimum U π`. Kind T (a ledger row for the record); the docstring says the corpus calls this "the UDT formula" and that the identification with `argmax_a E[U | π(s) = a]` is T13's business and fails in general. Hyps (a). Status proved.

### T3 — Local ⇏ global: Coordinated Buttons (`core`, P + N+; load-bearing 2)

`coordButtons := tbl 5 0 0 10`; `coordButtons_localOptimum : IsLocalOptimum coordButtons ![0,0]`, `coordButtons_not_optimal`, headline `exists_localOptimum_not_optimal`. N+: `coordButtons_not_separable : CrossSituationDependence coordButtons` (the exchange identity `U π + U π' = U (π[1 ↦ π' 1]) + U (π'[1 ↦ π 1])` of separable utilities would force `5 + 10 = 0 + 0`) and `coordButtons_localOptimum_one` (two genuine local optima). The source's `Theorem.lean` sets up `diffObs`/`modify_reduces_diff` "for a converse" and stops; the docstring says so. Hyps (a). Status proved.

### T4 — Separability (`core`, D + P; load-bearing 2)

(a) `Separable`, `CrossSituationDependence := ¬ Separable`, `RTest`; `separable_of_weighted` (the corpus's weight `P s` absorbed into `u`); `separable_of_rtest : RTest R → Separable (fun π => ∑ s, R s π)` and `Separable.exists_rtest` (a separable `U` admits an `RTest` presentation, `R s π := u s (π s)`). They are equivalent only given a presentation of `U` as a sum of per-situation rewards; the docstring and findings §5 say so. Status proved.

(b) `FSADependence` (the literal [formal-single-agent](../../sources/udt-representation-theorem/formal-single-agent.md) predicate) and `fsaDependence_iff_nonconstant : (∃ s₀ ≠ s₁) → (FSADependence U ↔ ∃ π π', U π ≠ U π')` — sharper than the mandate's instance: on `|S| ≥ 2` the definition *is* non-constancy. Instance `fsaDependence_sepIndicator` (the separable `sepIndicator := tbl 0 1 1 2` satisfies it). Ledger: `refuted` as a definition, with the sentence quoted, the literal reading, and the survivor `CrossSituationDependence`. Status refuted (proved).

(c) Lookup-table identity, in weighted form for any non-negative weights (so that (d)'s `max = Σ max` is the unit-weight instance): `weighted_sum_le_sum_sup'` (i) and `weighted_sum_sup'_eq_sup'_sum` (ii), with the `FinDist` instances `FinDist.exp_le_exp_sup'`, `FinDist.exp_sup'_eq_sup'_exp`. `sup'` over `Finset.univ` with `[Nonempty Y]`; no `⨆`. Kind P. Status proved.

(d) `Separable.isOptimal_of_isLocalOptimum` (P: local optimality at `s` pins `u s (π s) ≥ u s a` via `sum_update_eq`, then `Finset.sum_le_sum`), `Separable.localGlobal` (L), `sup'_eq_sum_sup'_of_separable` (C: derived from (c)(ii) with unit weights, not re-proved). Witness N+: `sepIndicator_localOptimum` / `sepIndicator_optimal` with `sepIndicator_nonconstant`; the failure without the hypothesis is T3. Findings §15 records 2-031(a). Status proved.

### T5 — Extension: is separability necessary for local ⟹ global? (`extension`, P)

`Separable.ordSep` (P), `OrdSep.localGlobal` (P; induction on the number of disagreeing coordinates, transporting local optimality by `OrdSep`; `Function.update_idem` does the bookkeeping the source's orphan `modify_reduces_diff` was for), `exists_localGlobal_not_separable` via `U5a := tbl 0 1 1 3` (`localGlobal_U5a`, `U5a_not_separable`, and `U5a_ordSep` so `U5a` separates `Separable` from `OrdSep`), `exists_localGlobal_not_ordSep` via `U5b := tbl 0 (−1) 1 2` (`localGlobal_U5b`, `U5b_not_ordSep`). So `Separable ⊊ OrdSep ⊊ LocalGlobal` on finite situation sets, all three inclusions witnessed. The exact characterization is recorded as the tautology `localGlobal_iff_nash_optimal` (Games). The mandate's optional OPEN (decidability of `LocalGlobal` below full enumeration) is not stated: it is a question about an algorithm class, not a Lean statement with a precise `sorry`. Status proved.

### T6 — Deterministic decision-determination with a mechanism coordinate (`core`, D + L, Hyps (c))

`PolicyDetermined behaviour W := ∀ m₁ m₂, behaviour m₁ = behaviour m₂ → W m₁ = W m₂`; `derivedPolicyUtility` via `Function.surjInv`; `derivedPolicyUtility_spec`, `exists_policyUtility` (`∃ U, ∀ m, W m = U (behaviour m)`), `policyDetermined_of_eq_comp`, `policyDetermined_iff_factors` (an iff for surjective behaviour maps). Hyps: **(c)** — the deterministic, mechanism-only caricature of C&T's decision-determination (`udt-comm-trust` owns the C&T notion); nothing here is claimed for it. Witnesses: `W2_witness` (N+: `Mech2 := (Fin 2 → Fin 2) × Bool`, `behav2 := Prod.fst`, `W2 := coordButtons ∘ fst` — policy-determined, non-constant, two distinct mechanisms sharing a behaviour) and `W2bad_not_policyDetermined` (Counterexample 2). `hasCrossSituationDependence := True` dropped (findings §4). Status proved.

### T7 — "Optimal predictor ⟹ DD" recorded as a squeeze (`core`, S row / L lemma)

`policyDetermined_of_factors` (three lines). Ledger row under the source's name `optimal_predictor_gives_dd`: Kind S, Status `flagged: "optimal" is defined as "factors through the policy" (OptimalPredictor.lean:119); the theorem assumes Gap 1`; pointer to `udt-condense-dd`. Status proved (as L), flagged (as S).

### T8 — Opaque Newcomb: CDT ≠ UDT, re-founded (`core`, P + N+)

`Opaque`: `Pred`, `World := Pred × BoxAct`, `predict`, `utility`, `predictorAccurate`, `consistent`, `consistentWorld`; **derived**: `consistent_unique : ∀ π, ∃! w, consistent π w`, `policyUtility π := utility (consistentWorld π)`, `policyUtility_spec`. Theorems `cdt_prefers_twoBox` (∀ p, `cdtUtility p one < cdtUtility p two`), `oneBox_beats_twoBox`, `oneBox_optimal : IsOptimal policyUtility oneBoxPolicy`, headline `cdt_udt_differ`; all by `simp`/`norm_num` (no `native_decide`). N+: `predictor_matters` (the world where a one-boxer is mispredicted scores `0 ≠ 10⁶` and is inconsistent). Extra: `edtScore` (condition on the action under a prior over the policy, junk `−1`) and `edt_oneBoxes_opaque` — EDT one-boxes here (findings §1, 2-031(b)). Status proved.

### T9 — Transparent Newcomb with predictor error ε (`core`, P + N+)

`Transparent`: `TObs`, `mk`, `flip`, `prediction π c`, `obs`, `act`, `u`, `payoff`, `coinW ε`, `coin`, `V ε π := ∑ c, coinW ε c * payoff π c` (derived, `V_eq_exp`). Closed forms `V_oneTwo`, `V_twoTwo`, `V_oneOne`, `V_twoOne`, `V_oneTwo_sub_twoTwo` (`= 999000(1−ε) − 10⁶ε`); `isOptimal_oneTwo_iff (0 ≤ ε ≤ 1) : IsOptimal (V ε) (mk one two) ↔ ε ≤ 999/1999` (exact rational); `oneTwo_strictArgmax (0 < ε < 999/1999)`. T11(b) is the docstring sentence. Status proved.

### T10 — EDT ≠ UDT in transparent Newcomb (`core`, P + N+; load-bearing 1)

Joint carrier `TPolicy × Bool` with `jointW μ ε (π, c) := μ.w π * coinW ε c` (a `FinDist`, `joint`), `obsΩ`, `actΩ`, `payoffΩ`; **EDT rule** `edtScore μ ε o a := condExpJunk (jointW μ ε) payoffΩ (event {O = o ∧ A = a}) (−1)`; `edtScore_eq_of_pos` (on a positive event the score is `u o a`, computed from the joint, not typed in).

(a) `edt_rule_twoBoxes_on_full_of_pos_support` (`10⁶ < 1001000`), `edt_rule_twoBoxes_on_empty_of_pos_support` (`0 < 1000`), headline `edt_ne_udt_transparent (hμ : ∀ π, 0 < μ.w π) (0 < ε) (ε < 999/1999) : (∀ o, IsStrictArgmax (edtScore μ ε o) two) ∧ IsStrictArgmax (V ε) (mk one two) ∧ mk two two full ≠ mk one two full ∧ 0 < V ε (one,two) − V ε (two,two)`. The divergence is on the full branch (docstring). Hyps (a): the prior is a variable with the support hypothesis explicit, `ε` a variable. Witness N+ `edt_ne_udt_uniform_witness` (uniform prior, `ε = 1/10`: all four EDT scores computed, `10⁶`, `1001000`, `0`, `1000`, and the strict UDT argmax).

(b) `separation_vanishes_of_null_event` (null `{full, two}` ⟹ score `−1`), `mass_full_two_eq_zero_of_eps_zero`, `mass_full_two_eq_zero_of_prior_null`, headline `edt_rule_oneBoxes_on_full_of_eps_zero`. Findings §7 carries the `j = 2` remark.

(c) `ctScore μ ε o a := condExpJunk (jointW μ ε) payoffΩ (event {Π o = a}) (−1)`; `ctScore_eq` (the C&T rule is the prior-average of `V ε` over `{π o = a}`); `ctRule_oneBoxes_on_full_of_lt (full support) (0 ≤ ε ≤ 1) (ε < 999/2000)`; `ctRule_disagrees_with_udt11_on_empty` (`halfPrior := ½δ_{(one,one)} + ½δ_{(two,two)}`, `ε = 1/10`: `E[U | Π empty = one] = 900000 > 101000 = E[U | Π empty = two]`, while `(one, two)` is UDT1.1-optimal with `two` at `empty`).

(d) `condProb_empty_given_full_one : P(empty | Π full = one) = ε`, `condProb_empty_given_full_two : = 1 − ε` (given positive mass of the conditioning set). Status: all proved.

### T11 — "Why ain't'cha rich" (`core`, records)

(b) is `isOptimal_oneTwo_iff`'s docstring; (c) is findings §14 (punishing a *procedure* needs a non-policy-determined environment, T6's failure witness). No new declaration.

### T12 — Post 1's policy-selection setup and the Nash reading (`core`, D + P + N+; load-bearing 3)

(a) `Tree.Leaf`, `Node`, `Pol`, `Env`, `prefixOf'`, `prefixOf`, `pathLaw F l := ∏ k, F (prefixOf l k) (l k)`, `suffixLaw F m l` (the product from depth `m`), `RowStochastic`, `envKernel e π`, `runLaw e π := pathLaw (envKernel e π)`, `runLaw_nonneg`, `runLaw_sum_one`, `runDist`, `V e U π`. The key lemma `sum_suffixLaw (hF : RowStochastic F) : ∀ d m, m + d = n → ∀ p : Fin m → O, ∑_{l : prefixOf' l m = p} suffixLaw F m l = 1` by induction on `d` (downward in `m`): the fibre decomposition `filter_prefix_succ` (leaves extending `p` with next observation `o` are the leaves extending `snoc p o`), `suffixLaw_succ` (peel the depth-`m` factor), `Finset.sum_fiberwise`. What resisted: the `Sigma`-typed nodes make `Fin (k : Fin n).val` appear in binder types, so several `rfl`-level facts (`(prefixOf l k).1 = k`, `Fin.castLE _ i` values) had to be exposed by `show` before `omega`/`exact` would see them; the higher-order unification in `Finset.sum_fiberwise` timed out until its arguments were given explicitly.

(b) `isNashEquilibrium_iff_isLocalOptimum_V`, `isNashEquilibrium_of_isOptimal_V` (Tree), over `Games`'s `isNashEquilibrium_instanceGame_iff` (the FAF form: FAF's `ofStrategicProfile_deviate` pushes the subtype coercion through `Function.update`) and `isNashEquilibrium_directGame_iff` (the direct form, `simp only [IsNashEquilibrium, IsBestResponse, deviate]`). Kind P; the docstring says the content is the coercion plumbing plus T2. Non-optimal Nash: `coordButtons_nash_not_optimal` (abstract) and `exists_nash_not_optimal_policySelection` (in a policy-selection environment: Coordinated Buttons on the two depth-one nodes of the depth-two binary tree, scaled into `[0,1]` and realized through (c)).

(c) `realizeEnv W hW0 hW1 o₀ o₁` (root: `bern (W π)` on `o₀`/`o₁`; later nodes `delta o₀`), `realizeU hn o₀ := [l 0 = o₀]`, `V_realize`, headline `exists_env_of_policyUtility (0 < n) (o₀ ≠ o₁) (W) (0 ≤ W) (W ≤ 1) : ∃ e U, ∀ π, V e U π = W π`. Proof: only the constant-`o₀` leaf carries mass and utility (`Finset.sum_eq_single`, `Finset.prod_eq_single`). Findings §8 corrects the inventory's encoding remark.

(d) `perverse_V : ∃ e U, ∀ π, V e U π = if π = π₀ then 1 else 0` (N+). (e) `card_node`, `card_node_geom` (`Nat.geomSum_eq`), `card_pol`. Status: all proved.

### T13 — The unjustified "simplification" (`core`, P + P; load-bearing 4)

`Simplification.lhs U π* s a := U (π*[s ↦ a])`, `rhs μ U s a := condExpJunk μ.w U (event {π s = a}) (−1)`. Refutation `rhs_argmax_ne_lhs_argmax : IsOptimal U13 ![1,1] ∧ IsStrictArgmax (lhs U13 ![1,1] 0) 1 ∧ IsStrictArgmax (rhs μ13 U13 0) 0`, with `U13 := tbl 1 0 0 2`, `μ13` weights `(3/10, 1/20, 6/10, 1/20)`, `rhs13_one : rhs 0 1 = 2/13`, `rhs13_zero : rhs 0 0 = 6/7`. Sufficient condition `rhs_eq_lhs_of_concentrated (hconc : ∀ π, π s = a → π ≠ π*[s ↦ a] → μ.w π = 0) (hpos : 0 < μ.w (π*[s ↦ a])) : rhs μ U s a = lhs U π* s a`; point-mass corollaries `rhs_delta_eq` (equality at `a = π* s`) and `rhs_delta_junk` (`−1` at every other action). Witness N+ `concentrated_witness` (`½δ_{(0,1)} + ½δ_{(1,1)}`, both actions, `U13` non-constant). The reading is ATTRIBUTION-UNVETTED (docstrings, ledger). Status: refuted / proved.

### T14 — Vanessa's dynamically consistent update, Bayesian case (`core`, D + P + N+; load-bearing 5)

`Tree.ActionEnv O A n := Node → A → FinDist O`, `liftEnv e₀ π h := e₀ h (π h)`; `LeafExt h l` (decidable), `NodeExt h m`, `AgreesOff π π' h := ∀ m, ¬ NodeExt h m → π m = π' m`, `AgreesOff.update`; `pH e π h := ∑_{l ⊇ h} runLaw e π l`, `contVal e U h π' := ∑_{l ⊇ h} suffixLaw (envKernel e π') |h| l * U l` (`E_{π'⋈(e|h)}[U]`, an expectation because `sum_suffixLaw_leafExt` gives suffix mass one), `offMass e U π h := ∑_{l ⊉ h} runLaw e π l * U l` (`P(¬h)·E[U | ¬h]`, multiplicative), `score e U π h π' := pH * contVal π' + offMass`. **Headline** `score_eq_V (e₀) (U) (π π') (h) (hag : AgreesOff π π' h) : score (liftEnv e₀) U π h π' = V (liftEnv e₀) U π'`. Proof: off `h` the leaf law does not see the continuation (`runLaw_eq_of_agreesOff_of_not_leafExt`: every prefix of a non-extending leaf is a non-extending node); on the leaves extending `h`, `pathLaw = suffixLaw · prefixLaw` (`Finset.prod_filter_mul_prod_filter_not`), the prefix law is one number for all such leaves and for both policies (`prefixLaw_eq_of_leafExt`), so `pH · contVal π'` expands by `Finset.sum_mul_sum` and `Finset.sum_comm` into `∑_{l'} (∑_l suffixLaw π l) · runLaw π' l' · U l'` with the inner sum one; then `Finset.sum_filter_add_sum_filter_not`. Corollary `score_argmax_iff`; `pH_eq_prefixLaw`, `pH_eq_of_agreesOff`. Witness N+ `Toys.t14_witness` (`coinActEnv := mkActEnv2 fairCoin (fun _ a => delta a)`, `h = tails`, `pay` vs `refuse-at-tails`: `AgreesOff`, distinct, values `45 ≠ 50`, identity holds). Fidelity exact for the Bayesian specialization; ATTRIBUTION-UNVETTED "Vanessa's rule as rendered by Diffractor"; the InfraBayes original is out of scope. The mandate's "policy-independent environment" is replaced by action environments (findings §12). **Stretch, done**: `Toys.cm_score_ne_V` — counterfactual mugging as a policy-selection environment (the heads branch reads the policy's tails action): with reference `pay` and `h = tails`, `S_h refuse = 50 ≠ 0 = V refuse` while `S_h pay = 45 = V pay`, and `AgreesOff pay refuse-at-tails tails`. Status proved.

### T15 — Self-sealing verdicts (`core` (a); `stretch` (b), (c))

`SelfSealing`: `Verdict`, `step ε` (1B absorbing; 2B corrected w.p. `ε`), `dist ε v₀ t`; `oneB_absorbing`, `uncorrected_eq : dist ε 2B t 2B = (1−ε)^t`, `corrected_eq`; `mean_correction_time (0 < ε < 1) : ∑' k, (k+1)·ε·(1−ε)^k = 1/ε` (Mathlib `tsum_coe_mul_geometric_of_norm_lt_one`, `tsum_geometric_of_lt_one`). (b) `stepDecay ε ρ` for the order "update then flip w.p. ρ", `statDecay` with `π(2B) = ρ/(2ρ + ε − 2ερ)`, `statDecay_stationary (0 < ε < 1) (0 < ρ)`, `statDecay_sum`; the other order in findings §9. (c) `perEpisodeValue`, `perEpisodeValue_eq`. Status proved.

### T16 — Records (findings only)

Findings §13 maps the eleven prose "representation theorems" to T2 (plus T4(d) where separability is invoked and T6 where fairness is), §15 the retracted formula, §11 the build graph, §14 T11(c).

### udt-rep-2-020 — the toy problems (N+ rows)

`Toys.cm_pay_sub_refuse : V pay − V refuse = 45`, `parfit_pay_sub_refuse (L) : = L − 10000`, `xor_V_pay = −199`, `xor_V_refuse = −100`, `xor_refuse_beats_pay`; each a depth-two policy-selection environment (`mkEnv2`) with the source's numbers, evaluated by `V_two` and `norm_num`. The mugging environment `cmEnv` doubles as T14's failure witness.

## What resisted, and how it was resolved

- **Constructor disequalities under `simp only`.** `BoxAct.one = BoxAct.two` is not reduced by `simp only` or `norm_num`; the `one_eq_two_iff`/`two_eq_one_iff` simp lemmas (proved by full `simp`) fixed the transparent-Newcomb numerics.
- **`Fin.val` of `Fin`-valued lengths.** Node depths are `k : Fin n`, so second components live in `Fin (k : ℕ) → O`; goals then show `Fin ↑(prefixOf l k).fst` or `Fin ↑1`, which `fin_cases`, `Fin.forall_fin_one` and `omega` do not see through. `show` with the reduced type, `Nat.one_pos`/`Nat.lt_one_iff` and `lt_of_lt_of_le i.isLt hk` resolved each case.
- **`Finset.sum_fiberwise` unification.** With implicit arguments it hit the heartbeat limit; explicit `s`, `g`, `f` elaborate instantly.
- **FAF's `toStrategic` bridge.** Unfolding `instanceGame` before rewriting turned `toStrategic.payoff` into a lambda that FAF's `ofStrategicProfile_deviate` no longer matched; rewriting with FAF's three lemmas first, then closing by definitional unfolding, is the working order (as the mandate's §9 probe predicted: one lemma of plumbing).
- **`field_simp` on the stationary law** left inverses in place; `linear_combination c * mul_inv_cancel₀ hD` with the right coefficient (`±ρ`, `−10⁶(1−ε)`) closes each identity directly.

## Requests to FAF and to other packages

- FAF API: none needed; `SafeParetoImprovements.Game.ofStrategicProfile_deviate` and `_toStrategicProfile` were exactly the lemmas the bridge required.
- `udt-ct-examples`: identify its C&T-structure conditional expectation with `condExpJunk … (−1)` and cite `Transparent.ctScore_eq`, `ctRule_oneBoxes_on_full_of_lt`, `ctRule_disagrees_with_udt11_on_empty` for udt-rep-090's bridge finding.
- `udt-comm-trust`: `PolicyDetermined` is a (c) placeholder for its decision-determination; `exists_policyUtility` is the deterministic shadow of the factoring it should prove.
- `udt-influence-101`: import `Tree.Leaf/Node/Pol/Env/runLaw/V` and `instanceGame`.
