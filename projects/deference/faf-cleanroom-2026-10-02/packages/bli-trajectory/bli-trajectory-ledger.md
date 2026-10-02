# `bli-trajectory` — ledger

One row per headline ([STANDARDS](../../STANDARDS.md) §6). Kinds: P proved · C composition · S squeeze · T trivial stub · N+/N− non-vacuity witness · L plumbing · D definition of record · OPEN. Every declaration is in namespace `Cleanroom.Bli.BliTrajectory`. "Hyps (b)/(c)" lists non-(a) hypotheses; "—" means all hypotheses are (a) or there are none. Status `proved` means the declaration is sorry-free and the gate (`scripts/wp-audit`) passed on its module after the last edit (see [bli-trajectory-report](bli-trajectory-report.md) §Gate). **F8 rows are `L`/`D` by design** (program §7 item 1): they are what `bliPrice` means. Witnesses over `smallIndex` are proved from theorems, never evaluated.

## D1–D4 — definitions of record (`Defs.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `smallIndex` | bli-program §2.1; mandate D1 | the index of record is `bli-found`'s `smallSet` | D | exact | — | — | proved |
| `StateCoding` (`code`, `inj`, `large`), `decode`, `states`, `tableVal`, `exists_stateCoding` | bli-program §2.3; mandate D1 | codes for grid tables, injective on the grid, large; decoding (junk zero table off the image); table values (junk `0` off `smallSet m`); a coding exists (N+, noncomputable) | D/N+ | variant: parameter with a largeness field (F-10) | — | `exists_stateCoding` (`Finset.equivFin` + offset `4^{sizeBound}`) | proved |
| `bliStateSystem` | bli-program §2.3/§2.5; mandate D1 | candidates = codes of the grid, `val` = decoded table, `actual` = code of the rounded actual table | D | exact (junk values disclosed) | — | — | proved |
| `hasFutureAtom`, `NoFutureState`, `futureStateAtom`, `combine`, `parse`, `latestEntry`, `Consistent`, `SmallPart`, `tierA` | bli-program §2.5; mandate D2 | the coding-aware Tier-A parser: future candidate atoms, conjunction trees split at `⋏`, `⊤` neutral as chain tail, disjunctions/implications Tier B | D | variant: coding-aware, made precise (F-10, F-16) | — | the parses in `Parser.lean` | proved |
| `chainProbH`, `chainMass`, `smallFactor`, `tierAPrice` | bli-program §2.5; bli-soto-a-035; mandate D2 | the forward chain probability (chain rule built in), the chain mass to the latest day, the Tier-A price (inconsistent chain → `0`; latest day's table prices the small part) | D | variant: forward recursion in place of a `trajGrid` sum (F-15) | — | — | proved |
| `bliPrice`, `bliHistory`, `ratHistory` | bli-program §2.5; mandate D2 | small → base, Tier A → trajectory prior from the **unrounded** actual table, Tier B → base | D | exact | — | — | proved |
| `pointMass`, `extendZero`, `degStep`, `degLaw`, `degIter`, `degAt`, `b0Price`, `b0History` | Appendix B `main.tex:447`; mandate D3 | B0: the point-mass law at the next-day rounding extended by zero (not a `Kernel`), the deterministic continuation, B0's history built directly | D | exact (new-coordinate convention `0`, disclosed) | — | — | proved |
| `marginalMass`, `marginalJoint`, `FaithMarginal`, `BayesRatio`, `TB_on`, `KernelLip` | bli-slides-015; mandate D4/M6 | the event "`𝐐_m(φ) = x`" as a partition sum; faith in the marginal; the ratio form under positivity (Lean's `/`, never `conditionalQuote`); `TB` restricted; ℓ¹-modulus of a skeleton | D | variant: (c) event as a partition sum (B1 prices no disjunction) | (c) partition-sum event | — | proved |
| `E2xScoped`, `E3Scoped`, `E3finScoped`, `FaithMarginalScoped`, `IsBLI_RomanScoped` | mandate M1; Known issue 1 | `bli-found`'s faith predicates with the scope restricted by `NoFutureState c n φ` | D | weaker: scope minus sentences mentioning a candidate atom of a day in `(n, m)` (F-1) | — | — | proved |

## M1 — F8: the constraint lemmas of `𝐏` (`Lemmas.lean`; all definitional)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bli_small` | Appendix B (1) exact; bli-slides-017 (1) | `E1x (ratHistory Q) 𝐏` — definitional | L | exact (`E1x`, not `E1r`) | — | — | proved |
| `bliPrice_state`, `bli_state` | bli-program §2.5 | the superbelief of a grid table's code is the kernel entry at the unrounded actual table — definitional (uses `large`) | L | exact | — | — | proved |
| `bli_cond2_scoped` | Appendix B (2); bli-slides-017 (2) | `E2xScoped c S 𝐏` — definitional | L | weaker: scope (F-1) | — | — | proved |
| `bli_cond3_scoped`, `bli_cond3fin_scoped` | Appendix B (3) | `E3Scoped`, `E3finScoped` — the later table prices the small part; definitional | L | weaker: scope (F-1) | — | — | proved |
| `bli_balance` | Appendix B (4); bli-slides-017 (4) | `E4 S 𝐏` from `Kernel.balanced` at the unrounded actual table | L | exact (bli-slides-017's scope) | — | — | proved |
| `bli_partition` | bli-slides-017 (5) | `E5 S 𝐏`: masses sum to one (`Kernel.sum_law`), same-day pairs inconsistent → `0` | L | exact | — | — | proved |
| `bli_update_small` | Appendix B `main.tex:440`; bli-slides-004 | product-form update on every day-`n` small `φ`, gap `≤ (1/(2 d_{n+1})) 𝐏_n(σ)` | L | weaker: up to the mesh; exact on the denominator grid | — | — | proved |
| `bliHistory_mem_Icc` | bli-program §2.5 | every price in `[0,1]` | L | exact | — | — | proved |
| `bli_E1r_of_grid` | Appendix B (1) rounded; Known issue 4 | `E1r` holds on the denominator grid | L | weaker: needs the grid hypothesis | — | — | proved |

## M3 — the bundle and the tent instance (`Lemmas.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bliHistory_isBLI_scoped` | bli-slides-017; bli-program §3.5 (i) | `IsBLI_RomanScoped c S (ratHistory Q) 𝐏` over any skeleton | C | weaker: scoped faith | — | tent instance | proved |
| `bliHistory_tent_nonDegenerate` | bli-program §3.4; bli-slides-018 | with the tent skeleton every superbelief charges the whole product face | L | exact | — | — | proved |
| `bliHistory_tent_two_states` | bli-program §3.4; mandate M3 | from an interior day-`n` price, two distinct day-`(n+1)` candidates have positive superbelief (not a point mass) | **N+** | n/a (no `d ≥ 2` needed) | — | face points sending `φ` to `0`/`1`, proved from `tentLaw_pos_iff` (not evaluated); **concrete instance** `bliHistory_tent_two_states_halfBase` (`Refutations.lean`: base `halfBase`, `φ := ⊥`, any mesh and coding — `halfBase` is incoherent, which is what makes `⊥` interior; the row's own hypothesis is any interior small price) | proved |
| **`chainProbH_sum_states`** (`Parser.lean`) | bli-program §3.5 (i); mandate M3 | additivity over a day's codes: for `n < m ≤ n + H`, `∑_{q ∈ states m} chainProbH ((m,q) :: l) n t H = chainProbH l n t H` — the marginal over day `m` is the sum over its codes (the horizon condition is necessary: beyond it the entry is inert) | P | exact (with the horizon condition stated) | — | — | proved (repair round 1; was "not landed") |
| **`bli_stateAlgebra_additive`** (`Lemmas.lean`) | bli-program §3.5 (i); mandate M3 | for every `n < m`, `∑_{q ∈ states m} 𝐏_n(⌜𝑸_m = q⌝) = 1` — every future day's candidates carry total mass one, not only the next day's (`bli_partition`) | C | exact | — | — | proved (repair round 1) |
| `Traj.cons`/`first`/`tail`, `sum_trajGrid_cons`, `trajLaw_cons`, `chainEvent_cons` (`Marginals.lean`) | mandate D2 ("prove they agree") | the front decomposition of a trajectory (a bijection `grid (n+1) × trajGrid (n+1) k ≃ trajGrid n (k+1)`); the trajectory law factors through it | D/L/P | exact | — | — | proved |
| **`chainProbH_eq_trajMass`** (`Marginals.lean`) | mandate D2 ("prove they agree") | the forward chain probability **equals** the mass `trajLaw` gives the chain's event (`trajMass`) — the deviation F-15 is cosmetic | P | exact | — | — | proved |

## M2 — B0, the degenerate solution (`Degenerate.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `degLaw_balanced_iff` | Appendix B `main.tex:447`; bli-soto-a-006 (ii) | the point-mass law is balanced at `t` iff every coordinate of `t` is a next-day grid value | P | variant: next-day grid values (the true condition; the mandate's `t ∈ grid m` is the case `d (m+1) = d m`, F-5) | — | — | proved |
| `degLaw_balanced_of_mem_grid` | bli-soto-a-006 (ii) | nested grids: a day-`m` grid table is balanced | L | exact | — | — | proved |
| `degLaw_not_kernel` | mandate D3 | no `Kernel` has the point-mass law once the day has a sentence | P | exact | — | the table `1/(2 d_{m+1})` | proved |
| `pointMass_not_nonDegenerate` | bli-slides-018/021 | a point mass is never non-degenerate at an interior table | P | exact (no `d ≥ 2` needed) | — | two face points | proved |
| `b0_small`, `b0_cond2_scoped`, `b0_cond3_scoped`, `b0_partition` | Appendix B (1)–(3), (5) | B0 satisfies `E1x`, the scoped faith predicates and `E5` — definitional | L | scoped (F-1) | — | — | proved |
| `b0_balance` | Appendix B (4) | `E4` for B0 on the denominator grid | L | weaker: denominator grid | — | — | proved |
| `b0_isBLI_scoped` | Appendix B `main.tex:447` | the degenerate solution passes the (scoped) constraints on the denominator grid | C | weaker: scoped, grid | — | — | proved |
| `b0_pos_iff` | bli-slides-005; bli-paper-043 (finite half) | the realized next state has positive B0-mass iff the rounded prices did not move — including that every *new* day-`(n+1)` small sentence rounds to `0` (the `extendZero` convention, D3; audit r1 N7) | P | exact (rounded to the day-`(n+1)` grid, F-17) | — | — | proved |
| `b0_unique_state` | Appendix B `main.tex:447` | exactly one candidate has positive superbelief | **N−** | n/a (the degenerate witness the sources exhibit; the N+ is the tent) | — | itself | proved |
| `faithMarginalScoped_of_e2xScoped` | bli-slides-015 (a) | scoped `E2x` ⟹ scoped `FaithMarginal` | L | exact | — | — | proved |
| `b0_simplified_bli` | bli-slides-015 (c); mandate M7 (iv) | B0 satisfies `E1x ∧ FaithMarginalScoped ∧ E3Scoped ∧ E4 ∧ E5` on the denominator grid | C | weaker: scoped, grid (F-14) | — | — | proved |

## M4 — constraint 4 is the partition axiom (`Partition.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `e4_iff_partition_mass` | bli-soto-a-006 (i)/(iii); Appendix B `main.tex:434–435`, `444–445`; bli-found F-11 | under a FAF world mixture on the day-`n`/day-`(n+1)` algebra, exclusivity and constraint 2 on `smallSet n`: `E4` at `n` ⟺ the day-`(n+1)` masses sum to one (`1 ≤ n` for ⇒; ⇐ holds at `n = 0` too, not split out) | C | exact (abstract; `1 ≤ n` for ⇒, F-11) | — | **`PartitionWitness.partition_package_inhabited`** (repair round 2, from audit r2's adversarial probe; was "none shipped", audit r1 fidelity N2): `pwHistory n` (weights `½` on `cohWorld n 0`, `cohWorld n 3`) with `pwSystem` (tables = those worlds' payouts) satisfies coherence on `pcpAtoms`, exclusivity and constraint 2 on **all** of `smallSet n` — **N+**: two charged states (`½` each) with *different* tables (`cohAtom ↦ 1` vs `0`), market `½` on `cohAtom`; `e4_at_witness` exercises the (⇐) direction. B1 itself still satisfies only the *conclusion* outright (`bli_e4_and_partition_mass`; F-11 (ii)) | proved |
| `partition_package_inhabited`, `e4_at_witness` (`PartitionWitness.lean`) | audit r2 adversarial N1; mandate M4 | the hypothesis package of `e4_iff_partition_mass` is inhabited at every `n`, with the N+ certificate; constraint 4 at `n ≥ 1` follows at the witness from partition mass `1` | N+ / C | exact | — | itself | proved (repair round 2) |
| `bli_e4_and_partition_mass` | bli-soto-a-006 (i) | in B1 both hold outright (kernel fields) | C | exact | — | — | proved |

## M5 — the small-sentence update (`Update.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bli_update_small_ratio` | Appendix B `main.tex:440`; bli-slides-004 | under positivity, `|𝐏_{n+1}(φ) − 𝐏_n(φ ⋏ σ)/𝐏_n(σ)| ≤ 1/(2 d_{n+1})` on `smallSet n` | C | weaker: up to the mesh; positivity explicit | — | — | proved |
| `bli_update_small_exact_iff` | bli-slides-004 | the ratio equals `𝐏_{n+1}(φ)` iff `Q_{n+1}(φ)` is a grid value | C | exact | — | — | proved |
| `bli_bayesRatio_small_of_grid` | bli-slides-004 | `BayesRatio` on small sentences on the denominator grid | C | exact | — | — | proved |
| `b0_update_small_exact` | bli-slides-005; bli-paper-043 | B0's ratio form is exact on the days its prices did not move **and** `Q_{n+1}(φ)` is a grid value (`hgrid`; the ratio is the *rounded* price — the true pair is `b0_pos_iff` + `bli_update_small_exact_iff`) | C | exact | — | — | proved |

## M6 — the total update on the state algebra (`Update.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `bliPrice_update_tierA_exact`, `bli_update_tierA_exact` | Appendix B `main.tex:440`; bli-program §3.5 (iii) | on the denominator grid, for Tier-A `ψ` (small part mentioning no day-`(n+1)` atom): `𝐏_{n+1}(ψ) · 𝐏_n(σ) = 𝐏_n(ψ ⋏ σ)` — restart from the conditioned table | C (regraded from P, audit r1 N4: definitional in the forward recursion; the work is the day shift + the restart identity) | exact (grid; F-18's day-shift restriction) | — | `tierAUpdatable_stateAtom` (every day-`(n+2)` candidate atom is `TierAUpdatable` at day `n`) | proved |
| `bli_update_tierA_ratio` | Appendix B `main.tex:440` | ratio form under positivity | C | exact | — | — | proved |
| `bli_TB_on_tierA` | bli-slides-048 | `TB_on (TierAUpdatable c)` when every actual table is a grid table | C | weaker: Tier A, grid | — | `tierAUpdatable_stateAtom` | proved |
| `chainProbH_lipschitz`, `bli_update_tierA_modulus` | bli-program §3.5 (iii); mandate M6 (modulus) | under `KernelLip sk L`: `|𝐏_{n+1}(ψ) 𝐏_n(σ) − 𝐏_n(ψ ⋏ σ)| ≤ 𝐏_n(σ) · L_{n+1}/(2 d_{n+1})` (sharper than the mandate's bound by the factor `𝐏_n(σ) ≤ 1`) | P | exact (abstract skeleton; instantiated at the tent in `TentModulus.lean`) | — | **`TentModulus.kernelLip_tent`** (repair round 2, from audit r2's adversarial probe): the tent skeleton has ℓ¹-modulus `4·|S m|` by `bli-superbelief`'s `tentLaw_l1_le` (the program's `2|S|` is refuted there, `tentLaw_l1_two_witness`); `bli_update_tierA_modulus_tent` is this row at the tent with `hQ` alone. The row cannot collapse to an exact update through a trivial `L` (`L m = 0` is unsatisfiable by any `Kernel` over `smallIndex`) | proved; instantiated in `TentModulus.lean`, which is gated but **not imported by the root** (cross-package import of `bli-superbelief`'s `Modulus` — `flagged: the import is the orchestrator's call at consolidation`) |

## M7 — what constraints 1–4 do not imply (`Refutations.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `recipeHistory`, `recipe_E1x/E2x/E3/E4/E5`, `recipe_isBLI_Roman` | mandate M7 | a hand-built history satisfying the **full-scope** Roman bundle (abstract system with large candidates) | D/L/C | exact (full scope) | — | `threeSystem`, `twoSystem` | proved |
| `constraints_not_imply_update` | bli-soto-a-005; `main.tex:440` | two `IsBLI_Roman` histories, equal on day `n₀`, different superbeliefs on day `n₀+1` | P (refutation) | exact | — | `threeSystem` (tables `0, ½, 1`), masses `(¼,½,¼)` vs `(⅓,⅓,⅓)`: N+ on the coordinate that matters; **incoherent constant scaffold** elsewhere (the base prices `⊥` at `½`, two of the three tables price `⊥` at `½`/`1`; audit r1 probe `RefutationDirect.threeSystem_incoherent`) | refuted (the implication); surviving neighbour: `bli_update_tierA_exact`. The sharper direct form (`P₁` alone violates the product-form update at positive conditioning mass `¼`) is `constraints_not_imply_update_direct` |
| `faithMarginal_of_e2x` | bli-slides-015 (a) | `E2x ⟹ FaithMarginal` | L | exact | — | — | proved |
| `faithMarginal_not_imp_e2x` | bli-slides-015 (b); bli-soto-a-009 | `FaithMarginal ∧ E1x ∧ E4 ∧ E5` without `E2x` | P (refutation) | variant: **two codes, one table** (audit r2 adversarial N3) — refutes bli-slides-015 (b)'s "may vary across `Q`" for `bli-found`'s abstract `StateSystem`, not across distinct price-lists: with two *distinct* additive tables the converse holds (`Pinning.two_state_pinning_scope`), and the distinct-table refutation needs three states (`TriState`); for the Notion's claim see the next two rows | — | `twoSystem p`, conditionals `p ± δ`, masses `½`: N+ on the conditional coordinate, identical tables by design; **incoherent constant scaffold** (base and tables price `⊥` at `p`; audit r1 probe `CoherentBase.twoWitness_not_coherent`) | refuted (the converse); surviving neighbour: refinement-invariant trust = `E2x` |
| **`faithMarginal_coherent_not_imp_e2x`** (`Coherent.lean`), with `cohHistory`, `cohSystem`, `cohHistory_coherent`, `cohHistory_faithMarginal`, `cohHistory_not_E2x`, `cohWeight_pos` | Notion ll. 215–225 (bli-paper-060; the coherence horn of M7 (iii), F-13) | a market that is a FAF world mixture on every day (`CoherentOn ∅ A (𝐏_n)` for every `n`, `A` — market, base and every candidate table), with `E1x ∧ E3 ∧ E4 ∧ E5 ∧ FaithMarginal` on the **full** scope, and `¬ E2x` | P (refutation) | **weaker: (c)** propositional coherence over the state-atom encoding (`CoherentOn ∅`: every atom set, *empty* stage — the weakest) in place of "propositional plus LUV coherence"; the state system is **non-injective** (two codes, one table). The injective version is the next row | (c) `CoherentOn ∅` for "LUV coherence"; two codes for one table | four `PCWorld`s per day (`cohAtom = atom 0` true/false × which of two candidates holds), weights `(p+δ)/2, (1−p−δ)/2, (p−δ)/2, (1−p+δ)/2`, all positive under `0 < δ < p`, `p + δ < 1` (`cohWeight_pos`, the N+); tables copy the day-`n` market (coherent, **identical** — what the `¬E2x` uses); `E2x` fails at `(0, 1, c₁, cohAtom)`: `(p+δ)/2 ≠ p/2` (needs only `δ ≠ 0`; the headline's bounds serve the N+). Scaffold, disclosed: the day-`n` mixture gives mass `0` to every state of a day `≥ n+2` (F-19) | refuted for `bli-found`'s abstract `StateSystem` under `CoherentOn ∅` (audit r2 adversarial B1); the Notion's claim under the injective reading is refuted by the `TriState` row below; surviving neighbours: `Pinning.two_state_pinning`/`_scope` (two distinct tables are pinned), refinement-invariant trust = `E2x` |
| **`Pinning.two_state_pinning`**, **`Pinning.two_state_pinning_scope`** (with `two_state_faith_cases`, `pin_and_of_pin`) | audit r2 adversarial B1 (probe `Pinning.lean`, adopted and extended); bli-slides-015 (b); mandate M7 (ii)/(iii) | **two distinct tables are pinned**: over a two-state system with distinct, finitely additive and commutative tables, the market a FAF world mixture, and faith in the marginal on a `⋏`/`∼`-closed family `Γ`, constraint 2 holds at every sentence of `Γ` for both states (the probe's instance: tables deciding a `ψ` oppositely, faith at `ψ` and `φ ⋏ ψ`) | P | exact (abstract; the Boolean laws and the scope are explicit hypotheses, all supplied by `CoherentOn ∅` on a `⋏`/`∼`-closed family) | — | n/a (a positive result; its hypotheses are met by any two-state world-mixture system with distinct tables, e.g. `PartitionWitness.pwSystem`'s two worlds at `(n, n+1)` on the cell algebra) | proved (repair round 2) |
| **`TriState.faithMarginal_coherent_distinct_not_imp_e2x`** (`TriState.lean`), with `triHistory`, `triSystem`, `triWorld_unique_state`, `triTableVal_ne`, `triHistory_coherent`, `triTableVal_coherent`, `triHistory_faithMarginal`, `triLevel`, `triHistory_not_E2x`, `triSystem_large`, `triCond_pos` | Notion ll. 215–225 (bli-paper-060; the coherence horn of M7 (iii) under the **injective** reading, F-13/F-20) | a market that is a FAF world mixture on every day in which **every world holds exactly one next-day candidate** (`triWorld_unique_state`), over **three pairwise distinct coherent tables** (`triTableVal_ne`, `triTableVal_coherent`), with `E1x ∧ E3 ∧ E4 ∧ E5 ∧ FaithMarginal` on the **full** scope, and `¬ E2x` | P (refutation) | exact (refutation; coherence relative to the empty stage on every atom set; the partition and injectivity readings of "LUV coherence" built into the witness; the scaffold as in `Coherent`) | — | nine `PCWorld`s per day (next-day candidate `i` × cell `j` of the two atoms `atom 0`, `atom 1`: `{a,b}`, `{a}`, `{b}`), weights `⅓·c_{ij}(ε)`, all positive for `0 < ε < ¼` (`triCond_pos`); tables `t₁ = (½,¼,¼)`, `t₂ = (¼,½,¼)`, `t₃ = (¼,¼,½)` over the cells; conditionals = tables + the 3-cycle `ε·(0,1,−1), (−1,0,1), (1,−1,0)` (deviations vanish on every level set of every event, `triLevel`, eight events exhaustively); `E2x` fails at `(0, 1, triCode 1 0, cohAtom)`: `⅓(¾ + ε) ≠ ¾·⅓`. N+ on the coordinate that matters: three positive-mass states with distinct interior tables. Scaffold, disclosed: mass `0` two days ahead (F-19); the tables' values on the day-`m` state atoms are junk the sources never read | refuted (the Notion's implication under the `FaithMarginal` + partition/injective reading of LUV coherence); surviving neighbours: `Pinning.two_state_pinning_scope` (two states go the Notion's way), refinement-invariant trust = `E2x`; stronger readings of LUV coherence that FAF cannot state are not touched (F-20) |
| `b0_simplified_bli` (M7 iv) | bli-slides-015 (c) | see M2 | C | scoped (F-14) | — | — | proved |

## M8 — response-conditioning (the journal response argument) (`JournalResponse.lean`)

(Named after notes in the author's 2023 journal; it is not Scott Garrabrant's or Benja Fallenstein's proposal — theirs were specific and technical, and the author's notes do not record them accurately.)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Reflection`, `journalResponse_forced`, `TruthResponse`, `journalResponse_truth` | bli-journal-2023-09-11 ll. 852–870 (ATTRIBUTION-UNVETTED) | a response settled on every state forces `𝐏_n(φ)`; a truth response collapses the market to the truth — **the tautological half** of the email's argument (substitute the constant response into the reflection identity; one `Finset.sum_congr`); the incompatibility with an inductor that does not yet know the digits is not formalized | D/L (regraded from C, audit r1 adversarial B1) | weaker: the tautological half only (abstract response) | (c) `TruthResponse` as "traders compute the digits" | — | proved |
| `eisenstat_form_consistent`, `eisenstat_response_unsettled` | same | Eisenstat's response (the state's own table) leaves `½` over two certain, opposite states; it is not settled | **N+** | n/a | — | `sbSystem` (two charged certain states) on the constant-`½` scaffold market `fun _ _ => ½` — not a BLI, and incoherent (prices `⊥` at `½`); the N+ is on the two-state coordinate only (audit r2 fidelity N5) | proved |

## M9 — Known issue 1 as a theorem (`Refutations.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `e2x_full_scope_fails` | Appendix B `main.tex:432`; `bli-found` `E2x`; Notion scope | for the tent instance from **any** base with day-`n` prices in the unit cube (coherent bases included) and `2 ≤ d_{n+1}`, `¬ E2x S 𝐏` (full scope). Repair round 1: the round-0 statement asked for *interior* day-`n` prices, which excluded every base pricing `⊥` at `0` — i.e. every `D_PC` base and B3's premise (audit r1 fidelity N3 / adversarial N2); kept by name as the corollary `e2x_full_scope_fails_of_interior` | P (refutation) | exact | — | `q'` = code of the day-`(n+1)` **face table** of `t` (`faceTable`: copies `t`'s `0/1` coordinates, `1/d_j` elsewhere), `m = max (n+2) (tokenSize σ')`, `q` = code of the day-`m` face table with `σ'` zeroed (`zeroAt`); positivity by path, each table in the product face of the previous one (`tentLaw_pos_iff`, `faceTable_mem_faceProd_self/_succ`, `zeroAt_faceTable_mem_faceProd`); concrete instance `e2x_full_scope_fails_halfBase` (incoherent base; the theorem covers coherent ones) | refuted (full-scope predicate); surviving neighbour: `bli_cond2_scoped`; **no OPEN inhabitation row needed** |
| `e2x_full_scope_fails_of_interior`, `e2x_full_scope_fails_halfBase` | same | the round-0 form (every day-`n` small price strictly interior, hence excluding every `D_PC` base) as a corollary; the concrete instance at the constant-`½` base (incoherent) | C / N+ | weaker: interior prices (corollary); concrete instance at an incoherent base | — | `halfBase`; a coherent concrete instance was not built (audit r2 adversarial N4) | proved |
| `tb_refuted` (day-free), `tb_refuted_at` | bli-slides-048; `bli-found` `TB`; Known issue 2 | `TB` on every sentence fails for B1 at a Tier-B sentence | **N−** (refutation) | exact | — | constant-`½` base, `ψ = ∼stateAtom (n+2) q₀` (day `n` a parameter of the proof; `tb_refuted` takes `n = 0`) | refuted; surviving neighbours: `bli_TB_on_tierA`, `bli_update_small_ratio` |

## M10 — T6: smoothed self-trust in sum form (`SelfTrust.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `e2i_smoothed_self_trust` | bli-slides-042 (`Ind_δ` = FAF's `ctsInd`) | `E2i ε` gives `∑_q P_n(φ ⋏ σ_q) Ind_δ ≥ p ∑_q P_n(σ_q) Ind_δ − ε_m ∑_q P_n(σ_q) Ind_δ` over the partition (`0 < δ`, nonnegative superbeliefs) | C | variant: state-partition sums in place of the LUV expectation `𝔼_n`, and the state's table value `Q̂_q[φ]` in place of the LUV `P_m(φ)` (the (c)-flavoured identification disclosed for `marginalMass`; audit r1 N12/N5) | — | — | proved |
| `e2x_smoothed_self_trust` | bli-slides-042 | the exact (`ε = 0`) form under `E2x` | C | exact | — | — | proved |
| contrast row (no theorem) | FAF `lic_self_trust`; bli-soto-b-027 | FAF's self-trust is asymptotic over e.c. sequences; exact-from-day-one is `bli-exactness` X6's | — | — | — | — | recorded |

## Denominator mesh — the grid hypotheses as an instance (`DenominatorMesh.lean`, repair round 1)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `denominatorMesh` | bli-program §2.2 ("denominator grid"); audit r1 fidelity N6 | the mesh whose day-`n` denominator is the product of the denominators of every price `Q k φ`, `k ≤ n`, `φ ∈ smallSet k` (nested, positive) | D | exact | — | — | proved |
| `actualTable_mem_grid_denominatorMesh` | bli-program §2.2 | for a base in `[0, 1]`, every actual table is a grid table of its denominator mesh — the grid hypothesis of the grid rows, discharged | P | exact | — | — | proved |
| `actualState_eq_actualTable_denominator` | bli-program §2.2 | on the denominator mesh the actual state is the actual table (no rounding) | C | exact | — | — | proved |
| `bli_E1r_denominator`, `bli_TB_on_tierA_denominator` | Appendix B (1) rounded; bli-slides-048 | `E1r` and `TB_on` Tier A hold for `𝐏` at the denominator mesh with no grid hypothesis | C | exact (at the denominator mesh; Tier A for `TB_on`) | — | any coding of the mesh (`exists_stateCoding`) | proved |
| `b0_isBLI_scoped_denominator`, `b0_simplified_bli_denominator` | Appendix B `main.tex:447`; bli-slides-015 (c) | B0 passes the scoped constraints, and "simplified BLI", at the denominator mesh with no grid hypothesis | C | weaker: scoped (F-1/F-14); exact at the mesh | — | — | proved |
| not claimed | — | `2 ≤ d (n+1)` for the denominator mesh (an all-integer base gives `d ≡ 1`); only M9 needs it | — | — | — | — | recorded |

## Tent modulus — `KernelLip` at the tent (`TentModulus.lean`, repair round 2; **not imported by the root**)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `kernelLip_tent` | bli-program §3.4/§3.5 (iii) (constant corrected by `bli-superbelief` E2(a)); audit r2 adversarial N2 | the tent skeleton has ℓ¹-modulus `4·|S m|` (`bli-superbelief`'s `tentLaw_l1_le`; the program's `2|S|` is false there) | C | exact (constant `4|S m|`) | — | — | proved (repair round 2); the module imports `Cleanroom.Bli.BliSuperbelief.Modulus` (itself importing only `bli-finite` and Mathlib) — `flagged: cross-package import, the orchestrator's call` |
| `bli_update_tierA_modulus_tent` | mandate M6 (modulus form); audit r2 adversarial N2 | the modulus row at the tent instance with `hQ` alone: `|𝐏_{n+1}(ψ) 𝐏_n(σ) − 𝐏_n(ψ ⋏ σ)| ≤ 𝐏_n(σ) · 4|S_{n+1}| / (2 d_{n+1})` | C | exact | — | the tent itself (`tentLaw_pos_iff`-style, not evaluated) | proved (repair round 2) |

## Stretch (not attempted)

| Target | Status |
|---|---|
| M11 (T8, `Measure.lean`: the JS integral is `0`, disintegration repair) | not attempted; `Measure.lean` not created |
| M12 (T9, refute bli-soto-b-022) | not attempted |
| T1-infinite (Ionescu-Tulcea extension) | not attempted |
| Extension (the set of `TB`-values consistent with 1–4) | not attempted |
