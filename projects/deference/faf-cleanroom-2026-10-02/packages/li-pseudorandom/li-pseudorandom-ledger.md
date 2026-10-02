# li-pseudorandom — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Li.LiPseudorandom.` omitted. "Hyps (b)/(c)" lists only non-(a) hypotheses; "—" means every hypothesis is (a) or there is none. Witness column: the N+ instance in `Witnesses.lean` (or the real construction) that inhabits the row's hypothesis package. Status `proved` unless marked (definitions of record are `defined`); the T7 rows and the T9 cross-reading row are `open`; `truthStar_learned` is `partial: over OPEN computability (T7)` as the mandate requires. No `refuted`, no `flagged`. Written by the formalizer (Claude Fable 5.1, [scrubbed], 2026-09-29); **revised in repair round 1 (2026-09-30)** after the round-1 audits: the enumeration of record `genWeighting` is now explicit and primitive recursive (the round-1 blocking issue), the T4 witness is over a real market, kinds were regraded where the audits found them a notch high, and the union shape, the adaptive T1 witness and the T9 witness were added. **Revised in repair round 2 (2026-09-30)** after the round-2 audits: the T9 cross-reading form is proved (`truthStar₂` redefined over the disjoint union of the rule families, round-2 fidelity B1; new tables for `Lift.lean` and the countable-family stream), the market of record is shown to vary with the stream and T4's witness is over a certified inductor (`Market.lean`, round-2 adversarial items 1–2), `genWeighting_primrec` regraded L, `starDP` dropped, and the load-bearing-hypothesis witnesses adopted. The gate line is the last `scripts/wp-audit Cleanroom.Li.LiPseudorandom` result recorded in the report.*

## Definitions of record (`Defs.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `truthR` | mandate § Definitions | `Bool` stream → FAF's `truth : ℕ → ℝ` (`1`/`0`) | D | exact | — | — | defined |
| `CausalRule` | mandate § Definitions; T1 | strictly causal `[0,1]` weight rule (day `n` reads days `< n` only) | D | exact | — | `constRule`, `evenRule`, `prevRule` (stream-reading), `builderRule` | defined |
| `diag` (+ `diagStep`, `diagPrefix`, `tilt`, `mass`, `factor`, `mart`, `pot`) | mandate T1 | the diagonal sequence by day recursion on the finite potential; a `def`, not a `Classical.choose` | D | exact | — | `diag_not_eventuallyConst` | defined |
| `restrict`, `clamp`, `builderRule` | mandate T5 | the rule "clamp the day-`n` denotation of `W n` on the market built from the truth prefix"; strictly causal by construction | D | variant: the feature is evaluated on `B (restrict x n)`, not `B x`; equal under `CausalBuilder` (`builderRule_w_eq`) | — | — | defined |
| `CausalBuilder` | mandate T5 | market at days `≤ n` reads only truth values with `g j ≤ n` | D | exact | — | `liaHistory_atomDP_causal`, `liaHistory_union_atomDP_causal`, `toyBuilder_causal`; the strictness `∀ j, j < g j` is load-bearing: `omniscient_causalBuilder_id` / `omniscient_not_causalBuilder_succ` (repair round 2) | defined |
| `diagBuilder` | mandate T5/T6 | `diag` over the builder rules of an enumeration | D | variant: through `builderRule`; equal to the mandate's under `CausalBuilder` | — | — | defined |
| `atomFamily`, `literalOf`, `atomDP` | mandate T6; `bli-program` §3.2(b), §3.6(iii) | the process deciding literal atoms with delay profile `g` and placement `a` | D | exact | — | `atomDP_stage_ssubset` | defined |

## T1 — the diagonal theorem (`Diagonal.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `diag_pseudorandom` | mandate T1; anson-034 | for `p : ℕ → [0,1]` and countably many strictly causal rules, every rule with divergent realized sum on `diag R p` has weighted average of `truthR − p` tending to `0` | P (content in `Diagonal.lean`'s own lemmas; the final step composes `weightedAverage_tendsto_of_mart_le` and `mart_diag_le`) | stronger: day-varying target; all divergent rules at once (no patience) | — | `diag_not_eventuallyConst` (non-constancy), `diag_even_density` (a day-only second rule), `diag_prev_density` (a stream-reading rule: the adaptive clause), `diag_const_half_zero/one` (numerical sanity, L) | proved |
| `weightedAverage_tendsto_of_mart_le` | mandate T1 (proof) | the analytic core: bounded running products ⇒ the limit | P | exact | — | (as above) | proved |
| `diag_pseudorandom_const` | mandate T1; `def:pseudorandom` | constant `p`: weighted truth frequency `≈ₙ p` (a recentring of `diag_pseudorandom`) | L | exact over the class `R` | — | `diag_not_eventuallyConst`, `diag_prev_density` | proved |
| `diag_pseudorandom_of_surjective` | mandate T1 (corollary) | any rule family indexed by a type with a surjection `ℕ → ι` | L | exact | — | — | proved |

## T2 — countability and the enumeration of record (`Countable.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `pgenerable_countable` | mandate T2 | `Countable {W // PGenerableWeighting W}` (injection `W ↦ Nat.Partrec.Code` of its token stream) | C | exact | — | `instNonemptyPGenerable` (the degenerate constant member; L) | proved |
| `genWeighting` | mandate T2 (second form); T7 | **the enumeration of record**, explicit: index `j` = FAF machine description + polynomial clock; day `n` = the clocked run's digit output (`machineTokens j n`), `undigitize`d, `unRpn`'d, parsed by FAF's `efFromSerializedTokens`. Repair round 1: replaces a `Classical.choose`d surjection (round-1 B1 of both audits) | D | exact | — | — | defined |
| `genWeighting_primrec`, `genWeighting_computable` | mandate T2/T7 | the enumeration of record is primitive recursive (hence computable) in `(j, n)` — the computable presentation the first version lacked | L (a composition of four FAF `Primrec` lemmas; regraded from C in repair round 2, both round-2 audits) | exact | — | — | proved |
| `genWeighting_covers` (+ `genWeighting_surjective_subtype`) | mandate T2 | every P-generable weighting is enumerated, exactly (FAF's coverage bridge: the `FP` witness of `polySeg` is reproduced by a clocked index on every day; `unRpn` recovers the serialization; the decoder inverts it) | C | exact | — | — | proved |

*Dropped in repair round 1:* `genWeighting_pgenerable` (every enumerated progression is P-generable) — false for the explicit enumeration at garbage indices and used by nothing (T5 uses only coverage).

## T3 — rank locality (`Locality.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `EF.denote_congr_of_rank_le` (+ `denoteWith` form) | mandate T3 | a rank-`≤ n` feature denotes the same real on histories agreeing at days `≤ n` | L | exact | — | — | proved |
| `PGenerableWeighting.denote_congr` | mandate T3 | `(W n).denote P` depends on `P` at days `≤ n` only | L | exact | — | — | proved |

## T4 — fixed history (`Fixed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `diagBuilder_pseudorandom_of_history` | mandate T4; `def:pseudorandom` | every history `P` has a family (`diagBuilder (fun _ => P) gen p`) pseudorandom with frequency `p` over all P-generable weightings divergent on `P`; fixed history, not the inductor form | C | exact | — | `diagBuilder_liaHistory_certified` (N+, **the witness of record** since repair round 2: `P := liaHistory (atomDP a y succ)` for primitive recursive `a`, `y` is a *certified* logical inductor — `atomDP_succ_isLogicalInductor`, FAF's `LIA_is_logical_inductor` — with FAF's predicate for every `f` and a non-constant stream, `Market.lean`); `diagBuilder_liaHistory_not_eventuallyConst` (N+: any `a`, `y`, `g`, criterion not invoked; repair round 1, replacing the constant market `P ≡ ½`); `diagBuilder_history_not_eventuallyConst` (any `P`) | proved |
| `pseudorandomFrequency_of_history` | mandate T4; FAF `PseudorandomFrequency` | FAF's predicate for **every** `f` at once | C | stronger: all `f` | — | (as above) | proved |
| `exists_pseudorandom_of_history` | mandate T4 | existential packaging | L | weaker: ∃-form | — | — | proved |

## T5 — the causal-builder theorem (`Fixed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `diagBuilder_pseudorandom_of_causal` | mandate T5; `def:pseudorandom`; anson-034 | for a causal builder `B` (delay `g`, `j < g j`) and a covering enumeration, `x := diagBuilder B gen p` is pseudorandom with frequency `p` relative to `B x` over all P-generable divergent weightings | C | exact (relative to `B x`) | — | `liaHistory_atomDP_causal` (real), `toyBuilder_pseudorandom` (toy); `hcov` is not free (`trivial_enumeration_does_not_cover`) and `j < g j` is not decorative (`omniscient_not_causalBuilder_succ`), repair round 2 | proved |
| `pseudorandomFrequency_of_causal` | mandate T5; FAF `PseudorandomFrequency` | FAF's predicate relative to `B x` for **every** `f` | C | stronger: all `f` | — | (as above) | proved |
| `exists_pseudorandom_of_causal` | mandate T5 | existential packaging | L | weaker: ∃-form | — | — | proved |
| `variedPseudorandom_of_causal` | mandate T9 (varied form); FAF `VariedPseudorandom` | at a rational day-varying target `q`, `x := diagBuilder B gen q` is `q`-varied pseudorandom relative to `B x`, every `f` | C | stronger: all `f`; no generability of `q` needed | — | `truthStar₂_variedPseudorandom` + `truthStar₂_not_eventuallyConst` | proved |

## T6 — the process and the family of record (`AtomDP.lean`, `Family.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `atom_mem_atomDP_iff`, `neg_atom_mem_atomDP_iff` | mandate T6.1; `bli-program` §3.2(b), §3.6(iii) | `atom (a n) ∈ D m ↔ g n ≤ m ∧ x n` (and the negation form), under `Injective a`, `j < g j` | L | exact | — | — | proved |
| `atomDP_hworld` | mandate T6.1 | every stage has a consistent world (the atom world); a side condition derived from the stages (its non-vacuity role is a remark) | L | exact | — | `atomWorld` | proved |
| `atomDP_theoryTruth` | mandate T6.1; FAF `TheoryTruth` | `TheoryTruth (atomFamily a) (atomDP a x g) (truthR x)`, derived from the stages | L | exact | — | — | proved |
| `machineSentenceCodes_atomFamily_id` | FAF `machineSentenceCodes_atom` | `MachineSentenceCodes (atomFamily id)` | L | exact | — | — | proved |
| `liaStates_congr`, `liaHistory_congr` | mandate T6.2 | processes agreeing on stages `≤ n` have the same LIA state/prices at days `≤ n` | L | exact | — | — | proved |
| `liaHistory_atomDP_causal` | mandate T6.2 (corollary) | `x ↦ liaHistory (atomDP a x g)` is a causal builder for delay `g` (two lemma applications; content in `liaStates_congr`) | L | exact | — | (this is the real instance of `CausalBuilder`) | proved |
| `truthStar` | mandate T6.3 | the family of record, a `def` from `diag` over the explicit enumeration `genWeighting` | D | variant: rules evaluated on the prefix-built market; equal to the mandate's `truth⋆` under `CausalBuilder`, which `liaHistory_atomDP_causal` supplies | — | `truthStar_not_eventuallyConst` | defined |
| `truthStar_pseudorandom_all` | mandate T6.3; `def:pseudorandom` | the family of record is pseudorandom with frequency `p` relative to the LIA over its own deciding process, over all P-generable divergent weightings; hyps `0 ≤ p ≤ 1`, `j < g j` | C | exact | — | `truthStar_not_eventuallyConst` (N+: real LIA, non-constant stream — **certified through the constant P-generable weighting only**: no price-reading weighting is shown divergent on the LIA, which needs the LIA's prices on the undecided members, T7-level); `builder_not_const` (`Market.lean`, repair round 2: **the market of record varies with the stream** — at `a = id`, `g = succ` the all-`true` and all-`false` streams give different LIA histories, by FAF's criterion on the certified inductors `constDP_isLogicalInductor`); `atomDP_stage_ssubset` (process not trivial) | proved |
| `truthStar_pseudorandom` | mandate T6.3; FAF `PseudorandomFrequency` | FAF's predicate for the family of record at **every** `f`; all hypotheses (a); no `Injective a` needed (meaningful instances are injective) | C | stronger: all `f` | — | (as above) | proved |
| `truthStar_theoryTruth`, `truthStar_hworld` | mandate T6.3 (benford bundle) | the `thm:benford` side conditions for the family of record | L | exact | — | `atomWorld` | proved |
| `truthStar_learned` | mandate T6.3; FAF `thm:benford` | `liaHistory (atomDP …) n (atom (a n)) ≈ₙ p` under the instance `IsLogicalInductor (liaHistory (atomDP …)) (atomDP …)` and `MachineSentenceCodes (atomFamily a)` | C | exact | `IsLogicalInductor` instance: OPEN T7 — **not yet known to be inhabited for `truthStar` as defined** (its `processComputable` field is `starDP_computable`; uninhabited outright for non-computable `a`, so the meaningful instances are injective and computable `a`); `hcodes`: (a)-when-discharged parameter ((a) for `a = id`) | — | partial: over OPEN computability (T7); hypothesis not known satisfiable for the object of record until T7 lands |
| `truthStar_atom_mem_iff` | mandate T6.1/T6.3 | decided-with-delay for the family of record | L | exact | — | — | proved |

## The union shape (`Union.lean`; the plan's `paperDP T` instance shape)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `liaHistory_union_atomDP_causal` | mandate T5 (union case); plan `### li-pseudorandom`; round-1 adversarial audit, item 1 | `x ↦ liaHistory (DP₀.union (atomDP a x g))` is a causal builder for delay `g`, any fixed `DP₀` | L | exact | — | (instance of `CausalBuilder` over a real construction) | proved |
| `unionStar` | plan `### li-pseudorandom` | the diagonal family over the LIA of `DP₀.union (atomDP …)` | D | variant (as `truthStar`) | — | — | defined |
| `unionStar_pseudorandom_all`, `unionStar_pseudorandom` | plan `### li-pseudorandom`; mandate T5 | `unionStar DP₀ a g p` is pseudorandom with frequency `p` relative to the LIA over `DP₀.union (atomDP a (unionStar …) g)` (paper form; FAF's predicate for every `f`); with `DP₀ := paperDP T` the plan's stated instance, minus its `hworld` and inductor certificate (the dependent's) | C | exact / stronger: all `f` | — | `unionStar_not_eventuallyConst` (N+: real LIA over the union, non-constant stream; through the constant weighting only, same caveat as T6) | proved |
| `union_atomDP_theoryTruth`, `unionStar_theoryTruth` | mandate T6.1/T6.3 (benford bundle), union case | `TheoryTruth` for `DP₀.union (atomDP …)` from `atomDP`'s stages | L | exact | — | — | proved |

## T7 — computability (`Computable.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `truthStar_computable` | mandate T7; anson-034 | `Computable (truthStar a g q)` for computable `a`, `g`, rational `q`. Repair round 1: a genuine open step about a determined object (the enumeration is primrec); remaining obstacles: the LIA evaluator uniform in the process code (FAF API request; essentially the whole gap) and the commutation of the potential's operations with the rational cast (FAF's `EF.denote_eq_ratCast` covers the feature side; repair round 2, round-2 fidelity item 2) | OPEN | exact | — | — | open |
| `starDP_computable` | mandate T7 | `ComputableDeductiveProcess (atomDP a (truthStar a g q) g)` (the name survives the removal of the unused `def starDP` in repair round 2); reduces to `truthStar_computable` via a `Computable` analogue of FAF's `ofEncodePrim` plus `Computable` of `literalOf` and the filtered stage image — the `Primrec` version of exactly this reduction is `atomDP_succ_computable` (`Market.lean`) for fixed primitive recursive families | OPEN | exact | — | `atomDP_succ_computable` (the fixed-family case, proved) | open |
| `truthStar_isLogicalInductor` | mandate T7; FAF `LIA_is_logical_inductor` | the LIA over the process of record is a logical inductor | C | exact | rests on `starDP_computable` (OPEN T7) | — | open (rests on T7) |
| `truthStar_learned_of_computable` | mandate T6.3/T7 | `thm:benford` for the family of record with the certificate discharged from T7 | C | exact | rests on `starDP_computable` (OPEN T7); `hcodes` parameter | — | open (rests on T7) |

## T8 — `succDeferral` (`Deferral.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `deferralPatient_succDeferral_of_divergent` | mandate T8 | every divergent weighting is `succDeferral`-patient (window weight `≤ 2`) | L | exact | — | — | proved |
| `pseudorandomFrequency_succDeferral_iff` | mandate T8; `faf-map-li` §5 item 5 | `PseudorandomFrequency truth p succDeferral P` ↔ the paper's `def:pseudorandom` over all P-generable divergent weightings; `succDeferral` only, no monotonicity in `f` claimed | L | exact | — | — | proved |
| `pseudorandomFrequency_of_all` | mandate T8 | the paper's class implies FAF's predicate at every `f` (one direction) | L | exact | — | — | proved |

## T9's machinery — lifted rules and the disjoint union (`Lift.lean`; repair round 2)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Schedule` (+ `evenSched`, `oddSched`, `pairSched`) | mandate T9 | a strictly increasing placement `ι` of a subfamily's members among the days with an explicit left inverse `π` (no `Classical.choose`); instances `2m`, `2m+1`, `Nat.pair r m` | D | exact | — | the three instances | defined |
| `lift` | mandate T9; round-2 fidelity B1 (`EvenLift.lean`, generalized) | the lifted rule: on day `ι m`, `clamp ((W m).denote (B (restrict x (ι m))))`; `0` off the schedule; strictly causal by construction | D | variant: on the prefix-built market (as `builderRule`); realized weight `clamp ((W m).denote (B x))` under `CausalBuilder` (`lift_w_ι_eq`) | — | — | defined |
| `subfamily_of_lift` | mandate T9 (cross-reading clause) | for a causal builder, a schedule `S`, a target `q ∈ [0,1]` equal to `p` on `S`'s days, and a rule family containing `lift S B W` for a P-generable `W` divergent on `B (diag R q)`: the `W`-weighted truth frequency of `m ↦ truthR (diag R q) (ι m)` tends to `p`. T1 at the lift's index, the prefix sums reindexed along the schedule (`sum_lift`), the limit along the subsequence `ι n`; `W` is evaluated on the market over the whole stream | C | exact | — | `truthStar₂_even_not_eventuallyConst`, `truthStarω_family_not_eventuallyConst` (through the instances) | proved |
| `subfamily_pseudorandom_of_lift` | mandate T9; FAF `PseudorandomFrequency` | the subfamily inhabits FAF's predicate for every `f` when the family contains the lift of every P-generable weighting | C | stronger: all `f` | — | (as above) | proved |
| `unionRules` (+ `unionRules_pair`) | mandate T9 ("disjoint union of the rule families") | countably many rule families interleaved by `Nat.pair` | D | exact | — | `twoFamilyRules`, `omegaRules` | defined |
| `variedPseudorandom_of_builderRule_mem`, `pseudorandom_all_of_builderRule_mem` | mandate T9 (varied form); `def:pseudorandom` | the combined-stream statements (`variedPseudorandom_of_causal`, `diagBuilder_pseudorandom_of_causal`) for any rule family that *contains* the builder rule of every P-generable weighting — enlarging the family by lifts loses nothing | C | stronger: all `f` / exact | — | `truthStar₂_variedPseudorandom`, `truthStarω_variedPseudorandom` | proved |

## T9 — jointly pseudorandom families (`Joint.lean`, `Fixed.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `twoFamilyRules`, `truthStar₂` | mandate T9 | the two-family stream of record: `diag` over the disjoint union of the builder rules, their even lifts and their odd lifts, at the LIA of record and the enumeration of record, alternating target. **Repair round 2: redefined** (was: over the builder rules only, round-2 fidelity B1); not a definition of record (mandate § Definitions of record), so `Family.lean`'s exports are untouched | D | variant (as `truthStar`) | — | `truthStar₂_not_eventuallyConst` | defined |
| `truthStar₂_variedPseudorandom` | mandate T9 (varied form) | the two-family stream is `pairTarget p₁ p₂`-varied pseudorandom relative to the LIA over the process deciding both families, every `f`; statement unchanged by the redefinition | C | stronger: all `f` | — | `truthStar₂_not_eventuallyConst` (N+: at `p₁, p₂ ∈ (0,1)` the combined stream is not eventually constant, through the constant weighting on the LIA of record; repair round 1, proof unchanged) | proved |
| `truthStar₂_even_pseudorandom`, `truthStar₂_odd_pseudorandom` (+ `…_all` paper forms) | mandate T9 (cross-reading clause); anson-050; `def-dose-response` | the even subfamily inhabits FAF's `PseudorandomFrequency` with frequency `p₁`, the odd subfamily with frequency `p₂`, relative to the LIA over the process deciding both subfamilies, for every `f`; the weightings quantified over are all P-generable weightings on that market, so they may read the other family's decided atoms. **Was OPEN; proved in repair round 2** | C | stronger: all `f` | — | `truthStar₂_even_not_eventuallyConst`, `truthStar₂_odd_not_eventuallyConst` (N+: the subfamily's plain density is its target, through the constant weighting on the LIA of record; the same "constant weighting only" caveat as T6 — no *cross-reading* weighting is shown divergent, which needs the LIA's prices on decided atoms and is T7-level) | proved |
| `omegaTarget`, `omegaRules`, `truthStarω` | mandate T9 ("countably many families at once") | member `m` of family `r` on day `Nat.pair r m`; `diag` over the disjoint union of the builder rules and the lifts of every family; target `q r` on family `r` | D | variant (as `truthStar`) | — | `truthStarω_family_not_eventuallyConst` | defined |
| `truthStarω_pseudorandom` (+ `truthStarω_pseudorandom_all`) | mandate T9 ("countably many families at once … each is pseudorandom against weightings that read the other families' truth values"); anson-050 | every family `r` of `truthStarω a g q` inhabits FAF's predicate with frequency `q r` relative to the LIA over the process deciding all the families, for every `r` and every `f` | C | stronger: all `f` | — | `truthStarω_family_not_eventuallyConst` (N+, same caveat) | proved |
| `truthStarω_variedPseudorandom` | mandate T9 (varied form) | the combined countable-family stream is `omegaTarget q`-varied pseudorandom relative to that LIA, every `f` | C | stronger: all `f` | — | (as above) | proved |

## Witnesses (`Witnesses.lean`)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `not_eventuallyConst_of_average` | mandate T1/T6 (non-vacuity) | a `{0,1}` stream with plain density `p ∈ (0,1)` is not eventually constant | L | n/a | — | — | proved |
| `diag_not_eventuallyConst` | mandate T1 (witness) | with `R 0 = constRule`, `p ∈ (0,1)`: `diag R p` is not eventually constant | N+ | n/a | — | — | proved |
| `diag_even_density` | mandate T1 (witness) | with `R 1 = evenRule`: density on even days is `p` (a day-only rule) | N+ | n/a | — | — | proved |
| `prevRule`, `diag_prev_density` | mandate T1 (witness); round-1 adversarial audit, item 2 | a strictly causal, stream-reading rule (weight `1` after a `true` day); with `R 0 = constRule`, `R 1 = prevRule`, `p ∈ (0,1)`: its realized sum on the diagonal diverges and the truth frequency on the days after a `true` day tends to `p` — N+ for the adaptive clause of T1 | D / N+ | n/a | — | — | proved |
| `diag_const_half_zero`, `diag_const_half_one` | mandate T1 (numerical sanity) | at `p = 1/2` over constant rules the first two values are `false, true`, by hand-evaluating the finite potential (no `native_decide`); sanity computations, not non-vacuity witnesses | L | n/a | — | — | proved |
| `diagBuilder_history_not_eventuallyConst` | mandate T4 (witness) | over **any** history `P`, `p ∈ (0,1)`: the fixed-history family is not eventually constant (repair round 1: generalized from `P ≡ ½`) | N+ (stream) | n/a | — | — | proved |
| `diagBuilder_liaHistory_not_eventuallyConst` | mandate T4 (witness); [STANDARDS](../../STANDARDS.md) §3 | the same over `P := liaHistory (atomDP a y g)`, a real inductor construction over a fixed decided family: T4's package with a non-trivial market | N+ | n/a | — | — | proved |
| `toyBuilder_causal`, `toyBuilder_nonconst`, `toyBuilder_pseudorandom` | mandate T5 (witness) | a cheap non-constant causal builder and T5 on it | N+ | n/a | — | — | proved |
| `truthStar_not_eventuallyConst` | mandate T6.3 (non-vacuity) | the family of record at `p ∈ (0,1)` is not eventually constant (through the constant P-generable weighting on the LIA) | N+ | n/a | — | — | proved |
| `atomDP_stage_ssubset` | mandate T6.3 (non-vacuity of the process) | every stage of `atomDP` is strictly contained in a later one (stages grow without bound) | N+ | n/a | — | — | proved |
| `not_eventuallyConst_of_varied_average` | mandate T9 (non-vacuity) | a `{0,1}` stream whose plain average of `truthR − q` tends to `0`, for `q` valued in `[lo, hi] ⊂ (0,1)`, is not eventually constant | L | n/a | — | — | proved |
| `truthStar₂_not_eventuallyConst` | mandate T9 (non-vacuity); round-1 fidelity audit, item 5 | the two-family stream of record at `p₁, p₂ ∈ (0,1)` is not eventually constant | N+ | n/a | — | — | proved |
| `truthStar₂_even_not_eventuallyConst`, `truthStar₂_odd_not_eventuallyConst` | mandate T9 (non-vacuity); repair round 2 | the even (odd) subfamily of the two-family stream is not eventually constant when its target is in `(0,1)` | N+ | n/a | — | — | proved |
| `truthStarω_family_not_eventuallyConst` | mandate T9 (non-vacuity, countably many families); repair round 2 | every family `r` with `q r ∈ (0,1)` of the countable-family stream is not eventually constant | N+ | n/a | — | — | proved |
| `unionStar_not_eventuallyConst` | plan `### li-pseudorandom`; mandate T6.3 (non-vacuity) | the family inside `DP₀.union (atomDP …)` at `p ∈ (0,1)` is not eventually constant | N+ | n/a | — | — | proved |
| `omniscient`, `omniscient_causalBuilder_id`, `omniscient_not_causalBuilder_succ` | mandate § Context 1, T5 trap (i); round-2 adversarial audit, item 6 | the omniscient builder (day `m` prices everything at `truthR x m`) is a `CausalBuilder` for the non-strict profile `g = id` and not for delay one: the strictness `∀ j, j < g j` of T5/T6 is load-bearing | D / N+ | n/a | — | — | proved |
| `trivial_enumeration_does_not_cover` | mandate T5; round-2 adversarial audit, item 7 | the constant enumeration `EF.const 0` misses the constant-`1` P-generable weighting: T5's `hcov` is not free | N+ | n/a | — | — | proved |

## The market of record (`Market.lean`; repair round 2)

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `atomDP_succ_computable` | mandate T6/T7 (fixed-family case); FAF `encode_stage_prim_of_list`, `ofEncodePrim`; round-2 adversarial audit, item 2 | for primitive recursive `a`, `x`: `ComputableDeductiveProcess (atomDP a x succ)` (stage `n` is the list of the first `n` literals) | C | exact | — | `constDP_computable` | proved |
| `atomDP_succ_isLogicalInductor` | FAF `LIA_is_logical_inductor` (`thm:lia`) | the LIA over `atomDP a x succ` is a logical inductor for primitive recursive `a`, `x` | C | exact | — | `constDP_isLogicalInductor` | proved |
| `liaHistory_atomDP_ne`, `builder_not_const` | mandate T6 (non-vacuity of the market of record); round-1 audits' T6 caveat; round-2 adversarial audit, item 1 | the LIA over `atomDP id x succ` differs between the all-`true` and all-`false` streams (`lic_disprovable_tendsto_zero` vs `lic_exists_limit_pos` on `atom 0`): the builder of record is not a constant map | N+ | n/a | — | — | proved |
| `diagBuilder_liaHistory_certified` | mandate T4 (witness); [STANDARDS](../../STANDARDS.md) §3; round-2 adversarial audit, item 2 | T4's package over the LIA of a fixed primitive recursive family, with the inductor certificate, FAF's predicate for every `f`, and non-constancy, in one statement — the T4 witness of record | N+ | n/a | — | — | proved |
