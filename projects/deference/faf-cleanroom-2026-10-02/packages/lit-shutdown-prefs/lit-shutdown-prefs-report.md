# lit-shutdown-prefs — report

*Written 2026-09-29 by the formalizer agent (Claude Fable 5.1, [scrubbed]); § Repair round 1 added 2026-09-30 by the repairer after the round-1 audits (`lit-shutdown-prefs-audit-r1-fidelity.md`, `…-adversarial.md`). Package key `lit-shutdown-prefs`, area `lit`, namespace `Cleanroom.Lit.LitShutdownPrefs`, directory `Cleanroom/Lit/LitShutdownPrefs/`, root module `Cleanroom/Lit/LitShutdownPrefs.lean`. Mandate: `lit-shutdown-prefs-mandate`. Findings: [lit-shutdown-prefs-findings](lit-shutdown-prefs-findings.md). Ledger: [lit-shutdown-prefs-ledger](lit-shutdown-prefs-ledger.md). Open list: `lit-shutdown-prefs-open.txt`.*

## State of the package

All fifteen core targets have Lean content; fourteen are done as the mandate asks (Target 13 fully since repair round 1: the closed form `F` is now derived from the enumerated meta-episode, `DrestDerivation.F_eq_metaReturn`), and one (Target 11) is done in the paper's own computation with the environment/policy data taken as given (`Dominated.lean`), now with the "small enough `δ`" supplied. Of the stretch targets, 23, 24 and 25 are done; 16–22 are not attempted (see the section "Not done"); extensions 26 and 28 are not attempted. One deliberately open statement (`PostConsistency.posl_ilpacs_nontrivial_model_open`, listed in `lit-shutdown-prefs-open.txt`, direction unknown); no other `sorry`.

**Gate**: `scripts/wp-audit` on the root module and all eighteen submodules printed **PASS** — 19 modules, 749 declarations, axioms `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` in the one listed open statement only — after the last edit of repair round 1 (2026-09-30). (Formalization round: 17 modules, 640 declarations, PASS.)

| File | Contents |
|---|---|
| `Lottery.lean` | carrier: `Lottery`, `wsum`, `expect`, product-form `mass`/`condSum`, `dirac`, `mix`, `map`, `condOn`, decomposition lemmas |
| `Comb.lean` | finite convex combinations `comb` |
| `Traj.lean` | `Traj`, `len`, `sumTotal`, `lengths`, `condLen` (proof-carrying), length decomposition, `discSum` |
| `Weak.lean` | framework W, Sen's corollaries, six conditions, IBIL lift, `euLe` lemmas (Targets 1, 2, 24) |
| `Strict.lean` | framework S, the 2024 simple theorem (kind S), the W↔S bridge (Target 5(c)) |
| `SIS.lean` | the state, Lemma 1, Lemma 2, First Theorem (Targets 2, 3) |
| `SISWitnesses.lean` | N+ witnesses, gap non-degeneracy, Thorstad refuted (Targets 3, 4) |
| `ThreeTheorems.lean` | Second Theorem, thin classes, Third Theorem, price lemma (Targets 5(a)(b), 6) |
| `Post.lean` | definitions of record and the chain (Targets 7, 8(a)(b)) |
| `PostAppendix.lean` | App. C.1 Theorems 1–2 (Theorem 2 under `RichnessOn tableTraj`), POST not idle, package witnesses (Target 10) |
| `PostConsistency.lean` | POSL ∧ ILPACS inconsistent with expected-sum-total single-length preferences; trivial model; repeated-parts consequence; the open model question (repair round 1) |
| `TimestepDominance.lean` | `TimestepDominates`, kind-S theorem, TD satisfies POSL/Neutrality, violates ILPACS, witnesses (Targets 7, 8(c), 9) |
| `CostModel.lean` | the cost model, byproduct witness, 2-006 (b)(c) (Targets 9, 23, 25) |
| `Unanimity.lean` | POST as unanimity; fails Neutrality and POSL (Target 14) |
| `Drest.lean` | usefulness/neutrality, `F`, usefulness proved, neutrality refuted (closed form and joint `(p, ρ)` form), repair (Targets 12, 13, 27) |
| `DrestDerivation.lean` | `F` derived from the enumerated meta-episode; the refutations restated for the enumerated return (Target 13, first part; repair round 1) |
| `Dominated.lean` | App. C.4 dominated policy (Target 11) |
| `Turner.lean` | the Fact (Target 15) |

## Contamination disclosure

None. Nothing under `research/faf-lab/`, no transcripts, no unfiltered git history was read. Sources read: the transcriptions the mandate cites (grep-then-window), `research/lean-deference/AUDIT.md` §0.2 and §3, `research/corrigibility/workflow-2026-09-13/{positive,critique}/thornley.md` windows, and Mathlib/FAF declaration files.

## Carrier and conventions (as built)

- `Lottery T` (`Lottery.lean`): `structure` with `p : T →₀ ℝ`, `nonneg`, `sum_one : ∑ t ∈ p.support, p t = 1`; `@[ext]` on `p`. Every quantity is `expect X g = ∑_{t ∈ supp X} X t · g t` (`wsum` at the finsupp level, with additivity/homogeneity/push-forward/filter lemmas).
- Product-form conditioning: `mass X q`, `condSum X q φ`; `condOn X q h` is the sublottery and takes the positivity proof `h : 0 < mass X q` as an argument — no junk value. Ratio forms are lemmas (`expect_condOn`, `mass_mul_expect_condOn`).
- `mix a ha X Y` carries the proof `ha : a ∈ [0,1]` explicitly (no clamping). `map φ X` is the push-forward; `map_mix`, `map_dirac`.
- Decomposition: `p_eq_decomp` / `eq_mix_condOn` (`X = mix (mass X q) (condOn X q) (condOn X ¬q)`), `condOn_point`, `support_condOn`, `mass_pos_of_mem`.
- Framework W (`Weak.lean`): `le` primitive; `lt`, `indiff`, `gap`, `lacks` derived; `Transitive`, `Complete`; Sen's four corollaries `pp_trans`, `ii_trans`, `pi_trans`, `ip_trans` from `Transitive` alone; `lacks_iff`, `lacks_iff_indiff_of_complete`, `trichotomy_of_complete`.
- Conditions on `le`: `IABM` (on `Act × R`), `IBILsub` (definition of record; ATTRIBUTION-UNVETTED reading of the sublottery schema), `BetterChances` (iff), `StrictMonotone` (one direction, strict), `Monotonicity` (Thorstad's weak one-direction). `strictMonotone_of_betterChances`.
- IBIL lemmas: `indiff_mix_mix_of_indiff` (the paper's `0.1X+0.4Y+0.5Z ~ 0.3X+0.2Y+0.5Z` example as nested mixtures, needs Transitive) and the **pointwise lift** `indiff_map_of_pointwise` (strong induction on the support, peeling one point with `eq_mix_condOn` + `condOn_point`; injectivity of `φ` is not needed, so the lemma is stronger than the mandate's).
- EU relation `euLe u X Y := E_Y[u] ≤ E_X[u]`: `euLe_lt_iff`, `euLe_indiff_iff`, transitive, complete, Better Chances, Strict Monotonicity, Monotonicity, IBILsub, and `euLe_iabm_iff` (IABM iff label-blind). The mandate's `IsEU u le` is not a separate predicate: witnesses take `le := euLe u` literally, so no transfer lemma is needed.

## Targets

### Target 1 — carrier and Sen's corollaries (core, D/L) — done

Declarations: `Lottery`, `Lottery.expect`, `Lottery.mass`, `Lottery.condSum`, `Lottery.dirac`, `Lottery.mix`, `Lottery.map`, `Lottery.condOn`, `Lottery.eq_mix_condOn`; `Weak.lt/indiff/gap/lacks/Transitive/Complete`, `Weak.pp_trans/ii_trans/pi_trans/ip_trans`, `Weak.euLe` with the lemma cluster above. Kind D/L, status proved. Hypotheses: none beyond `Transitive` for Sen's corollaries (a).

### Target 2 — the shutdown-influencing state and the six conditions (core, D) — done

`SIS.lean`: `Act` (`Leave | Prevent | Cause`), `SIS R` (`f g h`, `0 ≤ f < g < h ≤ 1`, base lotteries `P₀ U₀ : Lottery R`), `SIS.P a = P₀.map (a, ·)`, `SIS.U a = U₀.map (a, ·)`, `SIS.prob`, `SIS.act a = mix (prob a) (P a) (U a)` (Backward Induction definitional), `ShutdownAverse`, `ShutdownSeeking` (preference statements; "deterministically chooses" is the behavioural reading, l. 592). The label `a` is kept in `P a`/`U a`, so IABM and Lemma 1 have content (the mandate's trap). Conditions are in `Weak.lean`. Status: proved (definitions of record).

Note on IBIL: the definition of record is `IBILsub`; the 2025 §12 iff-form restricted to a shared length distribution is a different predicate, to be defined separately for Target 16 (`IBIL2025`).

### Target 3 — the First Theorem (core, kind C) — done

`SIS.lemma1_P`, `SIS.lemma1_U` (all `P a` / all `U a` mutually indifferent; from IABM + IBILsub + Transitive through the pointwise lift and the relabelling identity `P_map : (P a).map (a', ·.2) = P a'`), `SIS.lemma1_mix` (the stored fact, for any `c ∈ [0,1]` and any `a b` — stronger than the paper's `c = f`), `SIS.lemma2_lt_UP/lt_PU/indiff/gap` (Lemma 2, all four relations, via the weak-preference transfers `lemma2_le_UP/PU` and Transitivity), and the theorem:

- `SIS.first_theorem_averse : Transitive le → IABM le → IBILsub le → StrictMonotone le → (∃ a, lt le (U a) (P a)) → S.ShutdownAverse le`
- `SIS.first_theorem_seeking : … → (∃ a, lt le (P a) (U a)) → S.ShutdownSeeking le`
- `first_theorem_averse_bc`, `first_theorem_seeking_bc`: the same under `BetterChances`, via `strictMonotone_of_betterChances`.

Proof shape (kind C): Lemma 2 moves the preference to the Leave (resp. Cause) pair; StrictMonotone with `(1−f) > (1−g)` (resp. `h > g`) compares the two mixtures of the *same* pair; Lemma 1's stored fact identifies `act Prevent` with the `f`-mixture of the Leave pair; IP-transitivity closes. Exactly A3/A4. Hypotheses all (a): the four are the paper's antecedents (OSI and Backward Induction are definitional: `Fidelity: variant`). No `f > 0` or `h < 1` is assumed.

Witnesses (`SISWitnesses.lean`): `witness f g h …` over `Fin 2` (`0` unpressed, `1` pressed) with `P₀ = dirac 1`, `U₀ = dirac 0`, any `0 ≤ f < g < h ≤ 1`. `witness_averse` (N+): for `euLe uUnpressed`, all four hypotheses, `U a ≻ P a` for every `a`, and `ShutdownAverse` checked *directly* by `1 − g < 1 − f`, `1 − h < 1 − f` (not through the theorem). `witness_seeking` (N+) dually. Non-degeneracy (rebuilt in repair round 1): `witness_gap` over `R = Fin 3` (`witness3`, third state valued by neither criterion) — the two-criterion dominance relation `domLe crit0 crit1` (`[r = 0]`, `[r = 1]`) satisfies the four conditions, has genuine strict preferences (`(a, 0) ≻ (a, 2)`), a gap between every `U a` and `P a`, the three actions pairwise incomparable (criterion vectors `(1 − prob a, prob a)` with `f < g < h`), and the state is neither averse nor seeking; so the theorem's antecedent is not idle, and the gap case is exactly what the Second Theorem closes under Completeness. The original `Fin 2` construction is kept as `witness_gap_fin2` (N−): there the two label-blind criteria sum to `1`, the relation is the equivalence "equal unpressed mass" and has no strict preferences (`domLe_fin2_lt_empty`) — both round-1 audits caught this.

### Target 4 — Thorstad's Monotonicity restatement refuted (core, refuted + P) — done

`SIS.thorstad_monotonicity_restatement_refuted : ¬ ∀ S le, Transitive le → Complete le → IABM le → IBILsub le → Monotonicity le → (∃ a, lt le (U a) (P a)) → S.ShutdownAverse le` over `Fin 2`. Counter-model `clsLe X Y :⇔ posInd (m Y) ≤ posInd (m X)`, `m` the unpressed mass, `posInd s = [s > 0]`: `clsLe_transitive`, `clsLe_complete`, `clsLe_iabm`, `clsLe_ibilSub` (via `pos_mix_iff`), `clsLe_monotonicity`, `clsLe_lt_UP`, and `clsLe_not_averse` (Prevent and Leave both have unpressed mass `1 − f`, `1 − g > 0`; `g < 1` is forced by `g < h ≤ 1`). Witness state `(1/4, 1/2, 3/4)`. Mandate-writer claims checked: the refutation holds; `f = 0` does **not** rescue it (`thorstad_refuted_f_zero` on `(0, 1/2, 1)`). Deviation from the mandate: the two-level class function suffices for every admissible `(f, g, h)`; the three-level `cls` was not needed. Surviving neighbour: `first_theorem_averse` under `StrictMonotone`. Severity: local error in Thorstad.

### Target 5 — Second Theorem, thin classes, 2024 simple theorem, W↔S bridge (core) — done

(a) `second_theorem` (`ThreeTheorems.lean`): `Transitive → Complete → lacks X Y → four clauses`, kind L (Completeness turns the lack into indifference, PI/IP finish). (b) `lacks_chain_card_le_one`: along a strict chain `l : Fin n → Lottery T`, `(univ.filter (lacks s (l ·))).card ≤ 1` — the content of "at most 6 of 36". (c) `Strict.simple_theorem_2024` (kind S, as pre-labelled) and `simple_theorem_2024_chain`; bridge `Strict.indiff_of_weak_indiff`, `weak_gap_of_gap` (Transitive only), `weak_indiff_iff_indiff`, `weak_gap_iff_gap` (Transitive + `DomainRich`, the footnote's condition as a named hypothesis). All hypotheses (a).

### Target 6 — Third Theorem (core, kind L) and the price lemma (stretch) — done

`Patience`, `MinimalPatience`, `third_theorem` (trichotomy + PP/PP/PI; `e > 0` not needed for the step), `third_theorem_minimal`; witness `third_theorem_witness` (N+): `δ = 1/2` discounted sum, `a = b = c = []`, `i = j = 0`, `e = 1`, `k = l = 3`; Patience holds and the realised disjunct is the first, checked directly. The comparative-statics remark is not stated (findings F6). Price lemma: `SIS.price_lemma : lt (euLe (chargePrevent u₀ c)) (act Prevent) (act Leave) ↔ c < (g − f) · (E_{U₀} u₀ − E_{P₀} u₀)` and `chargePrevent_iabm_iff` (IABM iff `c = 0`). The mandate wrote the left side as `lt (act Leave) (act Prevent)`; that is a sign slip (findings F6). The TD counterpart is Target 9's cost model. The thesis-side reading is ATTRIBUTION-UNVETTED and not formalized.

### Target 7 — definitions of record (core, D) — done

`Post.lean`: `SameLength`, `PartShared`, `DifferentLength`, `POST` (clause (2)), `POSL`, `ILPACS` (exactly as displayed; `X.p = ∑ i, p i • (Xs i).p`), `NeutralityAntecedents`, `Neutrality`, `ReSIC` (over `Finset (Lottery Traj)` with a `resists` predicate), `Maximal`. `Traj.lean`: `condLen X l h` takes the membership proof (no junk value). `TimestepDominance.lean`: `condSumGE`, `condSumGT` (product form), `TimestepDominates` (footnoted version, condition (0) as clause 1), `TDPrinciple`, `NRATDR`. Stable since the ledger row was written.

### Target 8 — the chain and ILPACS vs TD (core) — done

(a) `neutrality_of_posl_ilpacs` (kind L): the length decomposition `Lottery.p_eq_sum_condLen` (a sum over `lengths X`'s attached finset, converted to a `Fin`-indexed decomposition by `Finset.equivFin`), pairwise lacks from POSL + `lengths_condLen`, weights in `(0,1)` from `mass_lt_one_of_ne`, the single-length case by `condLen_eq_self` (a gap in the paper's proof, findings F6). Neutrality is ILPACS specialised to the length decomposition (ledger). **Its hypothesis package** (repair round 1, `PostConsistency.lean`): no non-trivial model is exhibited; POSL ∧ ILPACS is inconsistent with expected-sum-total single-length preferences (`posl_ilpacs_inconsistent`, findings F7); the only exhibited model is the empty relation; whether any asymmetric relation with a strict preference satisfies it is open (`posl_ilpacs_nontrivial_model_open`, see § Repair round 1). (b) `not_maximal_of_resists` (one line). (c) `posl_TD`, `neutrality_TD` (through `condSumGE_condLen_iff`/`condSumGT_condLen_iff` and `TD_single_iff`; behavioural indifference of single-length lotteries forces equal conditional sums), and `not_ilpacs_TD` with the mandate's eight rationals — all mandate-writer claims held. Consequence recorded in findings F3.

### Target 9 — TD witnesses, the never-resist theorem, the cost model (core) — done

Witnesses `TD_leave_block` (with `E Block = 1.8 > 1.2 = E Leave`), `TD_steal_work` (truncated; `E Work = 2.98 > 2.02 = E Steal`), `spend_invest_incomparable` (three lengths, uniform shutdown time). `never_resist_TD` (kind S; NRATDR classified (c)). Cost model (`CostModel.lean`): `charge c` (cost at timestep 1), `reweight B w` (`p' = (w(len)/Z) · B`, `Z = E_B[w ∘ len]`), `opt B c w = (reweight B w).map (charge c)`; `mass_opt`, `condSum_opt`, `lengths_opt`; **`TD_cost`** (kind P): the `c = 0` option timestep-dominates every `c > 0` option for any positive reweightings, given no empty trajectory in `B`'s support; `nratdr_costModel` (any finite family of options with a free one satisfies NRATDR, with `resists := "is a costly option"` — well defined because dominance is irreflexive, `opt_ne_of_cost_pos`); `never_resist_costModel` (the chain, grade (a) inside the model). `byproduct_witness` (Target 25). What was not done: no comparison of the cost model with the Third Theorem's price lemma beyond the two statements themselves.

### Target 10 — App. C.1 (core) — done, with a named richness hypothesis

`PostAppendix.lean`: `prospectLottery`, `NegativeDominance`, `Acyclic` (no `List.IsChain` returning to its start), `NonArbitrarinessWith lt ε`, `NonArbitrariness`, `Richness`, and (repair round 1) `RichnessOn T` with `tableTraj` (the ten trajectories of Figure 11). Theorem 1: `lacks_of_differentLength` (kind L). Theorem 2 for `ε > 1/3`: `lacks_of_partShared` (kind P) via the six prospects `pA … pF` on three equiprobable states and the step lemmas `step_AB … step_FA` (each: two same-length states where the table's ranking gives the preference and Acyclicity gives asymmetry, one cross-length state where POST gives no dispreference; mass `2/3 ≥ 1 − ε`), under `RichnessOn tableTraj` — exactly the preferences the cycle uses; `lacks_of_partShared_of_richness` is the corollary under full `Richness`. The paper's statement lists POST, Acyclicity and Non-Arbitrariness; its proof uses the money-making agent's same-length preferences (findings F6, which now also records that the general claim is open for POST agents too sparse to rank the table). Squeeze check: `post_not_idle` — the expected sum-total agent satisfies Acyclicity, Non-Arbitrariness for every `ε ∈ (0,1)`, Richness, has a part-shared preference and violates POST; so POST is load-bearing. Non-vacuity: `partShared_package_satisfiable`, `differentLength_package_satisfiable` (repair round 1; from the adversarial probes). General `ε` (Target 28) not attempted.

### Target 11 — App. C.4 (core, kind P) — done in the paper's computation

`Dominated.lean`: `induced r s X Y Xs Z a b` (the induced mass function), `DominatedRep` (the paper's Dominated Policy, including the preference condition (1) and — since repair round 1 — the well-formedness clauses `dᵢ ∈ [0,1]`, `dᵢ + eᵢ ≤ 1`, remainder `≥ 0` the paper leaves implicit), `perturbed` (`aᵢ + s δ (qᵢ − pᵢ)/r`), `sum_perturbed`. **`dominated_of_ilpacs_violation`**: given the ILPACS data, `r, s > 0`, `r + s < 1`, `aᵢ > 0` summing to one, `0 ≤ b < 1`, and any `δ > 0` with `b + δ ≤ 1` and the perturbed probabilities positive, the perturbed policy sums to one and its induced mass function dominates the original's, with `cᵢ = r aᵢ + s b pᵢ + s(1−b) qᵢ`, `dᵢ = (r aᵢ + s b pᵢ)/cᵢ`, `eᵢ = s δ qᵢ/cᵢ` — the paper's own values; `cᵢ < 1` uses `r + s < 1`. `exists_delta` (repair round 1): `δ = min (1 − b) (r ∏ aᵢ / 2s)` is positive, keeps `b + δ ≤ 1` and every perturbed probability positive; `dominated_of_ilpacs_violation_exists` combines the two. `dominated_full_witness` (N+, repair round 1, from the adversarial probe) inhabits the theorem's *full* hypothesis package with the `not_ilpacs_TD` data (`lt := TimestepDominates`, `Xs = (X₁, X₂)`, `Ys = (X₁, Y₂)`, `r = s = 1/4`, `a = (1/2,1/2)`, `b = 1/2`, `δ = 1/10`); it replaces `numeric_delta_witness`, which inhabited only the arithmetic side conditions. Hypotheses: (c) the two-situation environment and the Maximality-dictated policy data (`aᵢ > 0` from stochastic choice among pairwise-lacking options, `b < 1` from `¬ X ≻ Y`) taken as given rather than derived from a formal Maximality.

### Target 12 — DReST definitions (core, D) — done

`Drest.usefulness p ρ = ∑ p l ρ l` (ratio primitive; `0/0` excluded), `neutrality p = ∑ negMulLog (p l)` (nats; `(c)` for `measureEntropy`/`log₂`), `uniform`, `MaxNeutral`; `neutrality_le_uniform` and `neutrality_eq_uniform_iff` by Jensen on `Real.strictConcaveOn_negMulLog` (`ConcaveOn.le_map_sum`, `StrictConcaveOn.map_sum_eq_iff_of_pos`).

### Target 13 — Theorem 5.1: usefulness proved, neutrality refuted (core) — done (derivation added in repair round 1)

`Drest.F n lam mu p ρ = ∑_{i<n} mu^i ∑_l p l ρ l (1 − (1−lam) p l)^i` with `mu = lam^{−1/k}` kept as a separate parameter so that all arithmetic is rational. **Derivation** (`DrestDerivation.lean`, repair round 1): `countBefore seq i` (DReST's `N_{e_i}(l)`), `seqReturn lam mu ρ i₀ c seq` (the return of a length sequence with initial index and counts), `seqProb p seq = ∏ p (seq j)` (i.i.d. lengths), `metaReturn n lam mu p ρ = ∑_{seq : Fin n → Fin k} seqProb · seqReturn 0 0` (**the enumerated expected return**), and the backward recursion `R lam mu p ρ (n+1) i₀ c = ∑ₐ p a (mu^{i₀} ρ a lam^{c a} + R n (i₀+1) (c + eₐ))`. `sum_seqProb_seqReturn`: enumeration = recursion, by induction on `n` peeling the first mini-episode (`Fin.consEquiv`, `countBefore_cons_succ`); `R_eq_closed`: the recursion has the closed form, by induction with the one-step binomial factor `∑ₐ p a lam^{[a = b]} = 1 − (1−lam) p b` (`sum_p_lam_ite`); **`F_eq_metaReturn`**: `F = metaReturn` for every `n` and every `p` with `∑ p = 1`. Hence `lemma_D2_false_enumerated` and `theorem_5_1_neutrality_false_enumerated`: the refutations hold for DReST's own Def D.2 enumerated over all `2^8` length sequences, not only for the closed form. The (c) on `F` is discharged; the remaining (c) is the `(p, ρ)` model. `theorem_5_1_neutrality_false_joint` (repair round 1): the theorem's own quantifier over policies `(p, ρ)` — no joint maximiser over simplex × `[0,1]^2` is uniform (`F_eq_of_rho_one` reduces a joint maximiser to the `ρ ≡ 1` slice). Usefulness half: `F_strictMono_rho`, `usefulness_eq_one_of_isMaxOn` (kind P). Neutrality half: `lemma_D2_false` (`n = 8`: `13191189/4194304`), `lemma_D2_false_seven` (`36351/262144`) — both mandate-writer numbers verified by exact arithmetic (Python `Fraction` and `norm_num`); `theorem_5_1_neutrality_false`: a maximiser of `F 8 (1/4) 2 · 1` on the compact simplex exists (`isCompact_stdSimplex`, `IsCompact.exists_isMaxOn`, `fun_prop` for continuity) and none is uniform. Findings F2. Target 27 (repair): `G`, `φ`, `φ_eq` (geometric sum), `convexOn_pow_affine`, `φ_concaveOn`, **`repaired_return_le_uniform`** (Jensen); strictness for `n ≥ 2` and the clipped-reward variant not done.

### Target 14 — POST as unanimity (core) — done

`Unanimity.lean`: `V u k t = u t + k · len t`, `leUL`, `ltUL`, `meanLen`; `leUL_iff` (`E len` equal ∧ `E u` ordered; the `k ↦ ±∞` argument done by choosing `k = (E_X u − E_Y u + 1)/(E_Y len − E_X len)`), `ltUL_dirac_iff_of_len_eq`, `lacks_dirac_of_len_ne`, **`post_unanimity`** (for every `u`; the non-triviality witness `[1] ≻ [0]` for `u = sumTotal` is `unanimity_nontrivial`, split off in repair round 1), `not_neutrality_unanimity` (Allow/Resist: antecedents hold, lotteries incomparable since mean lengths `1.1 ≠ 1.9`), `not_posl_unanimity` (mandate-writer claim held). The open conjecture is recorded (findings), not stated.

### Target 15 — Turner (core, L) — done

`Turner.lean`: `WeakCorrigibleTo R x := ∀ y, R y ≤ R x`, `StrictCorrigibleTo R x := ∀ y, R y < R x`, `not_strictCorrigibleTo`, **`weakCorrigibleTo_all_iff`** (the Fact), `exists_weakCorrigibleTo`. Findings F6 records the scope of the title claim. Target 20 not done.

### Stretch and extension targets

Done: 23 (`TD_dodge_comply`, `maximal_congr_menu`), 24 (`Weak.euLe_*`, `euLe_iabm_iff`), 25 (`byproduct_witness`). Not attempted: 16 (Neutrality+: needs the per-length affine utilities, the Ramsey yardstick and the 2025 IBIL as separate definitions plus the rebalancing induction), 17 (CCD: needs comparability classes as an equivalence relation), 18 (Petersen Prop. 1: strong acyclicity vs forcing pumps — short, not reached), 19 (Thorstad's enriched state and Krakovna–Kramar Theorem 2), 20 (permutation bound via `Equiv.Perm.decomposeFin`), 21 (the author's generalized objectives; Hahn–Banach separation), 22 (geometric aggregation), 26, 28. None of these blocks a core target.

## Mandate-writer claims: which held

- Target 4 counter-model: held; `f = 0` does not rescue; the two-level class function suffices (three-level not needed).
- Target 8(c): TD satisfies POSL and Neutrality: held. TD violates ILPACS with the given eight rationals: held.
- Target 13 numbers `36351/262144` (n = 7) and `13191189/4194304` (n = 8): held (exact arithmetic).
- Target 14: unanimity violates POSL with `dirac [0,0]` vs `½[1] + ½[0,0,0]`: held (with `Y ≻ X` for `u = sumTotal`).
- Target 6 price lemma: the stated direction was a sign slip; corrected.
- Target 10 squeeze check: POST is not idle (proved by a non-POST witness).

## Deviations from the mandate's shapes

1. `mix a ha X Y` carries the membership proof; `condLen X l h` carries the membership proof — no junk values anywhere.
2. `IsEU u le` is not a predicate; witnesses use `euLe u` directly.
3. `Acyclic` is stated with `List.IsChain` (Mathlib deprecated `List.Chain`), as "no chain returning to its start".
4. `Richness` is an explicit hypothesis of Theorem 2 (App. C.1) — the paper's proof uses it; the statement does not name it.
5. `NRATDR` and `ReSIC` take the situation as a `Finset (Lottery Traj)` and a `resists` predicate; in the cost model `resists` is defined through the option index and shown well defined.
6. DReST's `mu = lam^{−1/k}` is a separate real parameter (no `Real.rpow`).

## Repair round 1 (2026-09-30)

Audits read: `lit-shutdown-prefs-audit-r1-fidelity.md` (blocking B1, B2; non-blocking 1–10) and `lit-shutdown-prefs-audit-r1-adversarial.md` (blocking B1–B4; non-blocking N1–N8). The two audits overlap on the gap witness and the `Drest.F` docstring. Contamination: none (nothing under `research/faf-lab/`, no transcripts, no unfiltered git history; the only new sources read were the two audits and their probes under `audit-r1-probes/`).

**Gate after the last edit**: `scripts/wp-audit` on all 19 modules — PASS, 749 declarations, axioms `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` in the one listed open statement. Commits `363d5606`, `0e4bb74c` (Lean) and the docs commit that follows.

### Blocking issues

| Issue | Verdict | What changed |
|---|---|---|
| Fidelity B1 / adversarial B4 — `SIS.witness_gap` labelled N+ but its relation has no strict preferences (on `Fin 2` the two label-blind criteria sum to `1`) | **fixed** (the auditors' fix (ii)) | New `witness_gap` over `R = Fin 3` (`SISWitnesses.lean`): `witness3` with a third rest-trajectory, criteria `crit0 = [r = 0]`, `crit1 = [r = 1]`; the statement now *includes* the existence of strict preferences (`lt (dirac (a,0)) (dirac (a,2))` for every `a`) and the pairwise incomparability of the three actions (`witness3_domLe_act_iff`: `act a ≽ act b ↔ prob a = prob b`), besides the four conditions, the `U a`/`P a` gap and ¬averse ∧ ¬seeking. The `Fin 2` construction is kept, renamed `witness_gap_fin2` and regraded N−, with the degeneracy mechanized (`domLe_fin2_iff`, `domLe_fin2_lt_empty`, from the fidelity probe). Ledger row of `first_theorem_averse` updated. |
| Fidelity B2 / adversarial B3 — `Drest.F`'s docstring and the module header claimed a derivation in a file that did not exist | **fixed, and the file now exists** | First the two lines were corrected to say the derivation was not in Lean and `F` a (c). Then the derivation was done: `DrestDerivation.lean` (`F_eq_metaReturn`, see Target 13 above), so the docstring now points to a real derivation and `F`'s fidelity is `exact (given i.i.d. lengths)`; the ledger's D row no longer carries the closed-form (c). The header's "(strictly for `n ≥ 2`)" on the repair was removed (not proved). |
| Adversarial B1 — the hypothesis package of `neutrality_of_posl_ilpacs` (POSL ∧ ILPACS) is inconsistent with expected-sum-total single-length preferences; the ledger cited a witness (`TD_leave_block`) that does not satisfy ILPACS; the findings missed it | **fixed** (all four parts of the auditor's fix) | (i) The probe's two theorems are in the package as headlines: `PostConsistency.posl_ilpacs_two_cycle` (P) and `posl_ilpacs_inconsistent` (C), with a ledger row, status *refuted* for "POSL ∧ ILPACS is satisfiable by expected-sum-total agents". (ii) The Witness cell of `neutrality_of_posl_ilpacs` now says: none non-trivial; the only exhibited model is the empty relation (`posl_ilpacs_trivial_model`, N−); inconsistent with expected-sum-total single-length preferences. (iii) Findings F7 added (blocking for 2025 §7's chain as applied to any agent ranking same-length lotteries by expected sum-total; the theorem is true, its antecedent is empty), and F3's register corrected. (iv) `posl_ilpacs_nontrivial_model_open` stated as OPEN and listed in `lit-shutdown-prefs-open.txt`; see "The open question" below for what was tried. Also added: `ilpacs_lt_mix_of_lt` (ILPACS with a repeated part gives `A ≻ qB + (1−q)A`; findings F7). |
| Adversarial B2 — `Dominated.numeric_delta_witness` labelled N+ but inhabited only the arithmetic side conditions | **fixed** | Replaced by `dominated_full_witness` (N+): relation `TimestepDominates`, the `not_ilpacs_TD` lotteries, all ILPACS antecedents, environment, policy and `δ`; `TD_ilX₂_ilY₂` exported from `TimestepDominance.lean` (and reused inside `not_ilpacs_TD`). Both ledger rows updated. |

Nothing disputed.

### Non-blocking issues handled

- Adversarial N1 — `DominatedRep` junk values: the definition now requires `dᵢ ∈ [0,1]`, `dᵢ + eᵢ ≤ 1` and a nonnegative remainder; `dominated_of_ilpacs_violation` proves them (`dᵢ + eᵢ ≤ 1 ⟺ δ ≤ 1 − b`). Fidelity `exact (well-formedness made explicit)`.
- Adversarial N2 — witnesses for the full hypothesis packages of `lacks_of_partShared` and `lacks_of_differentLength`: `partShared_package_satisfiable` (`sameLenSumLt`; POST, Acyclic, Richness, `RichnessOn tableTraj`, NA for every `ε`, `[1] ≻ [0]`; NA vacuous, inherent) and `differentLength_package_satisfiable` (`diracLt`), from the probes; ledger Witness cells updated.
- Fidelity 1 / adversarial N3 — `Richness` much stronger than used: `RichnessOn tableTraj` (the money-making ranking on the ten trajectories of Figure 11 only) is now the hypothesis of `lacks_of_partShared`; `lacks_of_partShared_of_richness` is the corollary under `Richness`; findings F6 records that the general claim is open for sparse POST agents.
- Fidelity 2 — the paper's proof gap at single-length lotteries: findings F6.
- Fidelity 3 / adversarial N8 — Thorstad refutation's robustness (any reading of IBIL; "some … some" vs "corresponding"; Completeness added): recorded in the docstring of `thorstad_monotonicity_restatement_refuted`; regraded N+ per adversarial N4 (the counter-model is complete, transitive, with genuine strict preferences).
- Fidelity 4 — `SIS`'s fidelity line now `variant` (the label-only difference is built into the carrier).
- Fidelity 5 — the mandate's reversed Third Theorem disjuncts and swapped `F`/`G` in Non-Arbitrariness: recorded in findings F6.
- Fidelity 6 — `exists_delta` and `dominated_of_ilpacs_violation_exists`; the `eᵢ` presentation note in findings F6 and the module header.
- Fidelity 7 — `theorem_5_1_neutrality_false_joint` (no joint `(p, ρ)` maximiser is uniform) via `F_eq_of_rho_one`.
- Fidelity 8 — `post_unanimity` split: `post_unanimity u : POST (ltUL u)` and `unanimity_nontrivial`.
- Adversarial N5 — `Patience` docstring says why `0 < e` is not part of the schematic condition.
- Fidelity 9, 10 and adversarial N6, N7 — ledger kinds/cells and F3's register as requested. `price_lemma`'s kind left at P (one `nlinarith` after unfolding; a stretch item, not a headline the mandate weighs).

### Pushed further

- **Target 13, first part, done**: `DrestDerivation.lean` derives the closed form from the enumerated meta-episode for every `n` (the plan the formalization report had sketched — backward recursion with an initial-counts accumulator — worked as sketched; `Fin.consEquiv` does the peeling). The DReST refutation now rests only on the `(p, ρ)` model.
- `ilpacs_lt_mix_of_lt`: a consequence of the ILPACS display's formal shape (repeated parts are allowed because a lottery lacks a preference with itself).

### The open question (`posl_ilpacs_nontrivial_model_open`) — what was tried, hand analysis only, nothing below is in Lean beyond what is named

Question: is there an asymmetric `lt` with some `A ≻ B` satisfying POSL ∧ ILPACS? Stated in the existence direction because the analysis leans that way, but the direction is unknown; a proof either way is a finding about Thornley 2025 §7 (a model: ILPACS is consistent but only with non-EU within-length preferences; impossibility: the 2025 chain is vacuous for every agent).

1. Any model has preferences between multi-length lotteries: from `A ≻ B` (same length set `S`) and any `D` with a different length set, POSL makes `A`, `D` lack a preference and ILPACS gives `pA + (1−p)D ≻ qB + (1−q)D` for all `p, q ∈ (0,1)`. So "preferences only among single-length lotteries" is not a model.
2. Every *cardinal* candidate fails. Unconditional expected sum-total fails on the probe's pair (`E X = 1.9 < 8.2 = E Y` while ILPACS demands `X ≻ Y`); conditional (per-length) expected sum-total is the probe's `hEU` itself; the mass potential `m₁₀ − m₉` and the odds `m₁₀/m₉` survive every two-part decomposition (`p + q + (q − p)φ(D) ≥ 2 min(p,q) > 0`) but fail a three-part one with decoupled weights — parts `([10], E, F)` vs `([9], E, F)` with `E = [1,1]`, `F = 0.9[9] + 0.1[1,1]`, weights `p = (0.05, 0.05, 0.9)`, `q = (0.05, 0.9, 0.05)`: ILPACS demands `X ≻ Y`, the potentials say the opposite.
3. Support-based (ordinal) candidates: leximax over the set of support values fails because `D = ½[10] + ½[1,1]` forces `{10, 2} ≻ {10, 9, 2}` (an extra worse outcome must count as *bad*) while `D' = ½[9] + ½[1,1]` forces `{10, 9, 2} ≻ {9, 2}`; "leximax with absence as `+∞`" survives those two but ties on `D'' = ¼[10] + ¼[9] + ½[1,1]` (equal supports, strict preference demanded), and breaking the tie by conditional probabilities is defeated by the three-part decomposition of item 2 again.
4. The ILPACS-closure of the single preference `[10] ≻ [9]` (least relation containing it and closed under the display) was explored by hand: with repeated parts it contains `[10] ≻ q[9] + (1−q)[10]` (`ilpacs_lt_mix_of_lt`), every derived winner contains `[10]` in its support and every loser `[9]`, and the derivations tried produced only chains (e.g. `X_p ≻ M ≻ Y'_q` with `M = ⅓[10] + ⅓[9] + ⅓[1,1]`), never a cycle; whether the closure is asymmetric was not settled. Behavioural indifference is nearly trivial in the closure (most lacking pairs have a gap), so `≽` there is essentially `≻ ∨ =`.

What would settle it: a Lean proof that the closure of item 4 is asymmetric (a model), or a derivation of a two-cycle from `A ≻ B` alone using only POSL and the display (impossibility). Either is a natural next round's stretch item.

### Deliverables touched

`Cleanroom/Lit/LitShutdownPrefs/{SISWitnesses, Dominated, TimestepDominance, PostAppendix, PostConsistency (new), Drest, DrestDerivation (new), Unanimity, SIS, ThreeTheorems}.lean`, the root module, `lit-shutdown-prefs-open.txt` (one entry), the ledger (rows marked **[r1]**), the findings (F2, F3, F6, new F7), this section. The audit files were not edited.
