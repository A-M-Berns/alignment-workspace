# udt-comm-trust — report

Formalizer report for work package `udt-comm-trust` (Communication & Trust: decision structures, decision-determination, self-trust, advice-following). Mandate: `udt-comm-trust-mandate`. Binding: `00-common`, [STANDARDS](../../STANDARDS.md). Written in sections as the work progressed, 2026-09-30.

**Provenance note.** A first formalizer session committed `Factor.lean`, `FfsBridge.lean`, `Condense.lean`, `Prob.lean`, `Structure.lean` and left `Determination.lean` uncommitted (its last proof step failed), with no report, ledger or handoff. This session (launched as a fresh formalizer, not a continuation) kept all of that work, fixed the one failing step, added `polE_apply_of_DIB_eq`/`polE_eq_of` to `Structure.lean` and the witness-side criteria to `Factor.lean`, and wrote everything from `Concrete.lean` on. No definition of record was renamed.

## State of the package

- Modules (`Cleanroom/Udt/UdtCommTrust/`): `Factor` (T1(a)), `FfsBridge` (T1(b),(c)), `Condense` (T2(a),(b)), `Prob` (junk conventions, total expectation), `Structure` (T3, T4(a)), `Determination` (T5(a)–(c), T6, T7), `Concrete` (T8, T9, T12), `SelfTrust` (T10, T11, T17), `Advice` (T13, T14(b)), `Construct` (T4(b), repair round 1), `Count` (witness counting), `Witness`, `WitnessSmall`, `WitnessDet` (W2, the small witnesses, and the round-1 witnesses). Root module `Cleanroom/Udt/UdtCommTrust.lean`.
- Gate: **PASS** after repair round 1 (`scripts/wp-audit Cleanroom.Udt.UdtCommTrust`; see §Repair round 1 for the counts).
- The five load-bearing items: T11 (`selfTrust_printed` T row + `selfTrust_repaired` P) proved; T13 (`adviceFollowing_R` termwise, `adviceFollowing_Pi`, `faithful_of_nonsilent`, `aE_follows_R_of_udtRuleAt` per world, `polE_follows_R` as printed — the last two re-derived in repair round 1 after audit r1 found the r0 corollary vacuous) proved; T5+T6 (`DecisionDetermined`, `DetDD`, `detDD_of_uniqueFix`, `DynamicsCI`, `condExp_DIB_eq_policyUtility`) proved, with one reversal of the mandate's expectation (T5(c), below); T2 (`ct_not_unique` refutation, `CTCondensation.unique_given`) proved; T7 (`decomposition` with `Π* ⊑ D_{I,B}`) proved. Witness status per target below.
- Representation departures from the mandate, all disclosed in docstrings: (i) `ConcreteDS` carries `s`, `p` only; the instance factorizations are the predicate `InstanceFactored`, not fields (§T8); (ii) `s ö`, `p ö` read the whole `Ô`/`Ǒ`; (iii) `MinMod`/`HasCA` quantify over *attained* actions (the paper's `range A_ö`); (iv) two hypotheses the paper's proofs use silently are explicit: `R ⊑ D_{I,B}` (T10/T11) and `FactorsAsFam R` (T13).

## T1 — "Factors as" and the FFS bridge (`core`)

- Definitions (`Factor.lean`, kind D): `IsSubvariable` (dependence form, decidable; `isSubvariable_iff_exists` recovers the paper's `Y = f ∘ X` with `[Nonempty W]`), `IsSubvariable.proj` (``·`_Y`, `Classical.choose`, junk off-range disclosed), `FactorsAs` (support independence; clause 1 definitional, docstring says so), `factorsAs_iff` (decidable form), `FactorsAsFam` (restriction map = identity, recorded as presentation), `factorsAsFam_iff`, `factorsAsFam_bool_iff`, `CommonInfo`, `commonInfo_of_step`, `commonInfo_of_chain`, `commonInfo_exists` (P: common information always exists on a finite carrier as the equivalence closure of "same `X` or same `Y`" — the paper's "in our discrete setting it will exist" is true in the partition sense; the Gács–Körner point is about entropy, findings item 10). Witness-side: `factorsAs_of_fun`, `factorsAsFam_of_fun`.
- Bridge (`FfsBridge.lean`, previous session): `factorsAs_iff_isFactorization` (P): under `TwoValued Yv`, `TwoValued Zv`, `FactorsAs Yv Zv ↔ bY ≠ bZ ∧ IsFactorization {bY, bZ}` on `prodRange`; `bY_ne_bZ`; `orthogonal_bY_bZ` (T1(c), P); `orthogonal_not_isFactorization` (N−: orthogonality of two partitions does not give a factorization; three-point witness with `⊥, ⊤`). Hyps: (a). The unconditional (no two-value hypothesis) form and the family form of the bridge were not done (`stretch`).
- Witness for (b): the mandate's `Fin 4` witness (`(· / 2)`, `(· % 2)`) is not in `FfsBridge.lean`; `W2`'s factorization fields are `FactorsAs` witnesses of the definition. Status: (a) proved; (b) proved under two-valuedness; (c) proved; N+ for the bridge itself missing (partial).

## T2 — The translation's condensation variable (`core` (a),(b); `stretch` (c))

- `CTCondensation μ X Y V` (`Condense.lean`, D): clauses (1), (2) `FactorsAs`, (3′) `V ⊑ (X, Y)` ∧ `IndepLaw μ V Y`. Docstring says "the translation's definition" and never "C&T defines" (2-008(a)).
- `ct_not_unique` (P, refuted): quotes `topics/dynamics-and-condensation` line 76, reading literal with "function of" on the support (ATTRIBUTION-UNVETTED that the author meant "given `Y`"); XOR witness on four uniform points (`ct_snd`, `ct_xor`, N+); `¬ IsSubvariable snd xor` by `decide`. Surviving neighbour `CTCondensation.unique_given` (P): two condensation variables are functions of each other given `Y`.
- `CTCondensation.indepLaw` (L): udt-rep-011's corollary, read off (3′).
- (c) the entropy clause: not attempted (OPEN, listed in `udt-comm-trust-open.txt` as a statement in prose only — no Lean file with `sorry` was written, so the gate has nothing to list; see the open file's note). Status: (a),(b) proved; (c) open.

## T3 — The abstract decision structure (`core`)

- `AbstractDS` (`Structure.lean`, D): `μ`, `pos` (support), nine primitive variables, `polS` (`Π*` as a field: the paper's assumption), `U`, `U_mem`, six subvariable clauses, `IB_common`, `BE_common` (fields), six `FactorsAs` fields plus `IB_det` (clause 1 of the agent-dynamic constraint). Compound variables `I, O, A, B, E, DIB, IB` are defined as products. The finite-support `(c)` is disclosed in the structure docstring.
- Restriction maps: `projOf` (explicit junk `Y ω₀`), `rho`, `rho_spec`, `polOf` (``d`_Π̈`), `polE` (`Π̈`), `polD` (`Π†`), `projA/projAE/projAI/projOE`. Determination lemmas (L): `polE_sub` (`Π̈ ⊑ D_{I,B}`, udt-rep-2-001's sentence), `polD_sub`, `oI_sub_oE_DIB`, `polE_apply_oE`, `polD_apply_O`, `polE_apply_of_DIB_eq`, `polE_eq_of` (computable description of `Π̈` for witnesses).
- Witness: `W2.absDS` (`Witness.lean`), every field discharged (see the witness section). Status: proved.

## T4 — Policy types and the UDT rule (`core` (a); (b) not done)

- (a) `evS` (`{Π*(ȯ,ö) = a}`), `score` (junk `−1`), `UdtRuleAt`, `UdtRule` (pointwise reading, ATTRIBUTION-UNVETTED in the docstring), `evS_self_nonempty`, `score_lt_of_empty`, `evS_nonempty_of_isArgmax` (an argmax is attained). Status: proved.
- (b) the construction of `Π*` from `D_B` and a neutral side-channel value: **done in repair round 1** (`Construct.lean`). `SemChanSplit` (`Ȯ ⊑ (Ô, Ǒ)`), `Neutral`, `NeutralCompatible` (weaker than the mandate's `FactorsAs Ô Ǒ`; `neutralCompatible_of_factorsAs`), `neutralize` (`ȯ⟨Ǒ := ǒ₀⟩`, with `neutralize_spec`/`neutralize_eq`), `polSC` (`Π*_c`), (i) `polSC_sub` / `polSC_sub_DIB` (P), (ii) `polD_eq_polSC_of_oC` (P, at worlds whose side channel is at the neutral value) and `polD_eq_polSC_iff_inert` (L: on the mandate's unforced event (ii) *is* the inertness assumption `SideChannelInert`, i.e. `hlink` — findings 4′), (iii) `polD_eq_polSC_of_modProb_zero` (C), `withPolSC`/`withPolSC_hlink`/`withPolSC_polS_sub` (the structure with `Π* := Π*_c`, on which T7/T10/T11's `Π* ⊑ D_{I,B}` and T13(c)'s `hlink` are discharged). Witnesses: `W2.polSC_eq_polS` (N−: the side channel is constant, `Π*_c = Π*`), `W2m.not_factorsAs_oH_oC` with `W2m.neutralCompatible` (N−: the linked-coordinates failure case for the mandate's precondition, on which the construction is nevertheless available). `Π*` stays a field of `AbstractDS` (the paper's assumption) for structures without the preconditions.

## T5 — Decision-determination (`core` (a)–(c); `stretch` (d))

- (a) `DecisionDetermined` (`Determination.lean`, D): clause (1) `U ⊑ E`, clause (2) division-free CI of `E` and `D_{I,B}` given `Π̈`, over the support; `decisionDetermined_ratio` (L) is the paper's displayed ratio on positive-mass atoms.
- (b) `DetDD` (D), `E_fixed_point` (L: `E(ω) = (Π̈(ω)(`E(ω)`_Ö), D_E(ω))`), `UniqueFix` (D), `detDD_of_uniqueFix` (P: D1 automatic under uniqueness), `not_detDD_of_two_worlds` (L, the failure criterion). Witness for failure: `two-world` structure in `Witness.lean` (see there).
- (c) `DynamicsCI` (D). **Reversal:** `dynamicsCI_of_decisionDetermined` (P) — DD implies `D_E ⊥ D_{I,B} ∣ Π̈`, because `D_E ⊑ E`; so the mandate's expected witness of `DecisionDetermined ∧ ¬ DynamicsCI` cannot exist ("`ε` ignores a coordinate of `D_E`" is impossible under the environment-dynamic factorization). `dd2_of_dynamicsCI` (P): under `DetDD`, `DynamicsCI` gives clause (2); so under `DetDD` the two are equivalent. Findings item 11.
- The four corpus variants of (a) (`I(E;D|Π)`, `I(U;D|Π)`, `I(E;D_B|Π)`, `Π̈`-form) as definitions with the two implications: **not done** (`L`/`N+` rows dropped for budget).
- (d) entropy form: not attempted (OPEN, prose statement in the open file).

## T6 — DD ⟹ expected utility factors through `Π̈` (`core`, load-bearing 3)

- `policyUtility` (D), `condExp_DIB_eq_policyUtility` (P): for realized `d`, `E[U ∣ D_{I,B} = d] = E[U ∣ Π̈ = `d`_Π̈]`; derived from clause (1) (`U = u ∘ E`) and the atom identity of clause (2) summed with weight `u(e)`. Quantified over realized `d` (docstring explains why the identity is false off the range). `condExp_DIB_eq_policyUtility_polE` (C). `condExp_eq_policyUtility_of_measurable` (P, infrastructure). Hyps: (a); §3 (c).
- Witness: `W2` has DD (non-trivially: `(m,k) ↦ Π̈` is 16-to-4) and `policyUtility` takes two distinct values (`W2.policyUtility_lt`: `policyUtility id < policyUtility (fun _ => 0)`; the r0 text's `3/4`/`1/4` were the 48-world design's numbers and are withdrawn), so the theorem is not `c = c` there. Status: proved; witness in `Witness.lean` (see that section for what was checked).

## T7 — The decomposition needs `Π* ⊑ D_{I,B}` (`core`, load-bearing 5)

- `decomposition` (P): under DD and `IsSubvariable S.DIB S.polS`, for non-empty `{Π*(ȯ,ö) = a}`, `E[U ∣ Π*(ȯ,ö) = a] = ∑_{π̈ ∈ range Π̈} E[U ∣ Π̈ = π̈] · P(Π̈ = π̈ ∣ Π*(ȯ,ö) = a)`; division-free proof through `condExpJunk_total` and T6. Docstring names the silent hypothesis and where the original takes it (line ~345). `decomposition_of_measurable` (`SelfTrust.lean`) is the general form on any non-empty `D_{I,B}`-measurable event.
- Witness of necessity (`Π*` not a function of `D_{I,B}`, display fails by a computed rational): designed (four worlds `(k, j)`, `Π* = j`, `U = j`, `D_{I,B} = k`; display gives `0 ≠ 1/2`) — **Lean status in the witness section**.

## T8 — The concrete decision structure (`core`)

- `ConcreteDS extends AbstractDS` with `s : OE → OH → Option AE`, `p : OE → OC → Option AE` (`Concrete.lean`, D). Derived: `projOH`, `projOC`, `R` (`R_eq_projOH`, `R_sub`), `P` (`P_sub`), `Follows`, `evFollowsR` (`{Π̈ = R}`, udt-rep-017's reading), `evFollowsR_eq_univ_iff` (`P(Π̈ = R) = 1 ↔ {Π̈ = R} = Ω`), `IsModified`, `evMod`, `modProb` (junk `0`), `modS`.
- Departures (findings, T8): the instance factorizations are the predicate `InstanceFactored` (Π*, Π† families), not fields — no theorem uses them, so the theorems are stronger without them; the families for `B, Ȧ, Ä, A, Ȯ` are not representable on the realized-instance reading (`Ä = Π̈(Ö)` is one action). `ConcreteDS.ofTables` (a small-arity constructor) was not written; `W2` shows the pattern the examples package can copy (structure literal + `decide +kernel`).

## T9 — Minimally modifying actions and communicative alternatives (`core`)

- `MinMod` (over attained actions, D), `IsCA` (D), `HasCA` (over attained `a`, D). `isCA_nonempty` (L, T9(i): junk `0` forces `{c} ∩ {Π̈ = R} ≠ ∅`), `isCA_self_of_minMod` (L, T9(ii)). Status: proved.

## T10 — Communicative Expectation (`core`)

- `commExp_proof` (P): DD, `Π* ⊑ D_{I,B}`, `R ⊑ D_{I,B}`, `IsCA a c`, `a` attained ⟹ `E[U ∣ a] = E[U ∣ c, Π̈ = R]` — the proof's statement. **New silent hypothesis found:** decomposing `E[U ∣ c, Π̈ = R]` over `Π̈` by DD needs `{Π̈ = R}` to be `D_{I,B}`-measurable; `R ⊑ Ȯ` and `Ȯ ⊑ (Ö, D_{I,B})` do not give it (the recommendation may depend on the focal observation), so `R ⊑ D_{I,B}` is taken as a hypothesis (findings item 2′).
- `commExp_printed` (P): with `P(Π̈ = R) = 1`, `E[U ∣ a] = E[U ∣ c]` — the printed lemma. Status: both proved. Hyps: (a) throughout, with the two silent hypotheses named.

## T11 — Self-Trust (`core`, load-bearing 1)

- `selfTrust_printed` (T, `proved`): the printed display with the paper's three conditions and the min-clause as *unused* binders; proof `Finset.le_sup'` at `a' = a`. The quote and reading are in the docstring; severity: local error in the statement of the main theorem, in the original and the translation alike (2-008(b)).
- `selfTrust_repaired` (P): DD, `Π* ⊑ D_{I,B}`, `R ⊑ D_{I,B}`, `HasCA`, `P(Π̈ = R) = 1` ⟹ at every input the UDT argmax contains a minimally modifying action. `selfTrust_sup_eq` (C): the sup over minimally modifying actions equals the sup over all.
- Witness (`W2m`, four worlds, in `Witness.lean`): designed so that `HasCA`, DD (non-trivial), `P(Π̈ = R) = 1`, a modifying action `(0, m'+1)` of positive mass with `m = 1 > 0 = m(follow)`, and a tie `E[U ∣ a₁] = E[U ∣ a₀] = 1/2`. **Lean status in the witness section.**

## T12 — Stability and internally-driven recommendations (`core`)

- `evFollowsMinus` (`[Π̈ = r]_{−ö}`), `evToldMinus` (`{R_{−ö} = r_{−ö}}`), `evR`, `Stable` (Π-form, `ȯ_ö` quantified over the observations producing `r ö`), `StableR` (told form, the original's contrasted reading, 2-008(d)), `InternallyDriven`. Lemmas: `internallyDriven_nonempty` (L: junk `0` forces the `(ȧ, ä)`-events to be all empty or all non-empty), `stable_nonempty` (L: junk `−1` forces the `(ȧ, r ö)`-events non-empty). Status: proved.

## T13 — Advice-Following (`core`, load-bearing 2)

- `adviceFollowing_R` (P): `InternallyDriven`, `∀ r ∈ range R, StableR r`, `FactorsAsFam R`, `ȯ ∈ range Ȯ`, `s ö `ȯ`_Ô = some ä₀`, `{Π*(ȯ,ö) = (ȧ, ä₀)}` attained ⟹ `∀ ä ≠ ä₀, E[U ∣ (ȧ, ä)] < E[U ∣ (ȧ, ä₀)]`, for each `ȧ`. Proof exactly as the mandate prescribes (law of total expectation over `R_{−ö}`, weights equal by internal drive summed over compatible `r` — `condProb_Rminus_eq_sum` — termwise `StableR` at the combined recommendation, strict average `sum_mul_lt_sum_mul`). **Finding:** the combined recommendation (`ä₀` here, the fibre's values elsewhere) must be *realized* for "stable with probability one" to apply to it; this is the instance factorization of `Ȯ` (the paper's Instance Structure), used silently by the proof — hence `FactorsAsFam R` as a hypothesis. Without it the theorem still holds under the stronger reading "stable for every `r`" (not formalized separately; noted).
- `Faithful` (D), `evToldMinus_subset_evFollowsMinus` (L), `stableR_of_stable` (L), `adviceFollowing_Pi` (C), `faithful_of_nonsilent` (P).
- (c) **rewritten in repair round 1** (audit r1, B1). `aE_follows_R_of_udtRuleAt` (P, per world): `UdtRuleAt ω Ȯ(ω) Ö(ω)`, no simultaneous recommendation and modification, `hlink` (the prose meaning of `Π*`: effective = chosen where the realized instance is unforced), AF-R's hypotheses ⟹ `R(ω)(Ö(ω)) = some a → Ä(ω) = a`; the attainment of `(ȧ*, a)` that the r0 proof took from junk internal drive now comes from told-form stability (`stableR_nonempty`). `polE_follows_R` (C, the printed clause): the pointwise rule + `R ⊑ D_{I,B}` + the same ⟹ for every world and realized `ö`, via the world with the same dynamics observing `ö`. The `argmax` over pairs is where the paper's `argmax_ä max_ȧ` belongs. Internal drive is the guarded `InternallyDriven` in both; with the r0 unguarded form the package was contradictory (`udtRule_internallyDrivenJunk_stableR_inconsistent`, P, finding 7).
- Witness `W2` for (a): `internallyDriven` (via the junk form), `stableR` on `range R`, `R_fam`, strict gap `1/2 > 7/16` at both instances with both events non-empty (the r0 text's `3/8` and `32/64 vs 12/32` were the 48-world numbers; withdrawn). For (c): `UdtRule` fails on `W2` (`not_udtRule`, scores `1/2` vs `7/16`), and under unguarded internal drive no nondegenerate structure could satisfy the pointwise package at all; the per-world form has the N+ witness `W2.aE_follows_at_follow_world` (rule at the following world by the computed gap; a deviating world of positive mass at the same input, `W2.deviating_world`), and the printed form has the deterministic N− witness `Det` (`WitnessDet.lean`: constant following `Π*`, rule by `udtRule_of_const`, stability strict through the junk `−1`, conclusion true by construction `Det.follows_direct`).
- `Faithful` failure witness (T13(d)): not done (OPEN, prose).

## T14 — Self-reference (`core` (b))

- `AbstractDS.udtRule_of_const` (P, repair round 1): on any structure a *constant* `Π*` satisfies `UdtRule` (the chosen action's event is `Ω`, every other action's event is empty and scores `−1`), so "no `Π*` satisfies the rule" is false while `Π*` is a free field; the content is that a *nondegenerate* prior need not be a fixed point (`W2.not_udtRule`) and, under unguarded internal drive with stability, cannot be (`tie_of_udtRule_internallyDrivenJunk`). Status: (b) proved; (a) open.

## T15 — Fairness conjunction (`stretch` (a))

- **Positive half proved in repair round 1** (`Fairness.lean`): `followsR_of_hasCA_const` (P) — with a *constant* recommendation, communicative alternatives at one input force `P(Π̈ = R) = 1` (the CA identity gives a non-following `Π̈` conditional probability `0` given every attained action; the attained events cover `Ω`); `followsR_of_fairness_const` (C) states it for the fairness conjunction with DD, stability and the rule as unused binders. Negative half (design only, unverified): with a two-valued `R`, an eight-world structure has DD, `HasCA` (each action is its own CA), `∀ r ∈ range R, Stable r` (strict via junk on the deviating event), `UdtRule` (utility independent of the agent) and `P(Π̈ = R) = 1/2`. Recorded in the findings; not built.

## T16 — Translation-fidelity ledger

In [udt-comm-trust-findings](udt-comm-trust-findings.md) §T16.

## T17 — Extension

- `minMod_of_isStrictArgmax` (C): a strict argmax is minimally modifying (ceiling (ii)). `no_modification_cost` (L): under DD a modification cost invisible to `E` cannot exist (finding (i)). The tie witness is `W2m` (T11).

## Witnesses (`Count.lean`, `Witness.lean`)

- `Count.lean`: `IntWeights` (positive natural weights, total `N`), `cnt`, `dist`, `mass_eq_cnt`, and the transfer lemmas `mass_mul_eq_of_cnt`, `condProbJunk_eq_of_cnt`, `condExpJunk_indicator`, `condExpJunk_indicator_lt/eq`, `mass_eq_of_cnt`, `mass_eq_one_of_cnt`, `event_congr`. Every numeric fact about a witness is a natural-number count identity proved by `decide +kernel` and lifted once. No `native_decide`.
- `W2` (64 worlds `((m, k), (ö, a))`; the r0 text said 48, the earlier design): `absDS : AbstractDS` with every field discharged (mixing functions + `decide +kernel`; `IB_common` by hand; `BE_common` by a two-step chain), `S : ConcreteDS`. Design constraints that the abstract structure forces are recorded in the module docstring and findings item T8′.
- Checks on `W2` and the other witnesses: see the final section.

## Final section — gate, witness checks, what remains

**Gate: PASS.** `scripts/wp-audit Cleanroom.Udt.UdtCommTrust` (the root module, which pulls in all twelve modules) after the last edit, 2026-09-30: 652 declarations audited, axioms used `propext`, `Classical.choice`, `Quot.sound` only, no `sorry`, no lint failure. Every module `lean-build` clean. `udt-comm-trust-open.txt` lists no declaration (nothing uses `sorry`); the open items are recorded there in prose.

**Witness checks (all elaborated and built).**
- `W2` (64 worlds, `Witness.lean`): `absDS`/`S` inhabit every field; `decisionDetermined` (96 count identities; DD non-trivial, `(m, k) ↦ Π̈` is 16-to-4); `polS_sub`, `R_sub_DIB`; `internallyDriven` (288 identities); `stableR` for every realized recommendation with both events non-empty and the strict gap `1/2 > 7/16`; `R_fam` (the recommendation factors by instance); `instanceFactored` (both policy families); `policyUtility_lt` (T6 not `c = c`); `score_lt` (the Advice-Following gap at one input); `not_udtRule` (the nondegenerate prior is not a fixed point). Lean time about ten minutes at 2.5 GB in the slice; all enumerations by `decide +kernel`.
- `W2m` (four worlds, `WitnessSmall.lean`): `followsR` (`P(Π̈ = R) = 1`), `decisionDetermined` (non-trivial), `polS_sub`, `R_sub_DIB`, `modS_values` (`m = 1` for the flipping action, `0` for following), `minMod_follow`, `hasCA`, `score_tie` (`1/2 = 1/2`), `both_argmax` — so `selfTrust_repaired`'s full hypothesis package is inhabited with a non-minimally-modifying action of positive mass, and the T17 tie is exhibited: **N+ for the hypothesis package and for T17; N− for `selfTrust_repaired`'s conclusion** (audit r1, B2: with two actions the CA identity forces the tie, so every action is an argmax and the conclusion follows from `minMod_follow` alone; a witness exercising the `IsArgmax` conjunct needs three attained external actions with two score levels — open file, T11(c)+). The r0 sentence "DD non-trivially … N+" overstated this.
- `Two` (two worlds): `not_detDD`, `not_uniqueFix` (T5(b) failure). N+.
- `NoSub` (four worlds): `decisionDetermined`, `not_polS_sub`, `decomposition_fails` (`0 ≠ 1/2`; T7 necessity). N+.

**Witness status by target (updated in repair round 1).** T3 ✓ (`W2`). T4(b) ✓ (`W2`, N−; `W2m` for the precondition). T5(b) ✓ (`Two`). T6 ✓ (`W2`). T7 ✓ (`NoSub`). T10/T17 ✓ (`W2m`); T11(b) hypothesis package ✓ (`W2m`), conclusion N−. T13(a) ✓ (`W2`: internal drive, told-form stability, `R` factoring, strict gap). T13(b): `adviceFollowing_Pi`'s package not separately inhabited (needs `P(Π̈ = R) = 1` with two instances; not done). T13(c) ✓ per world N+ (`W2.aE_follows_at_follow_world`), as printed N− (`Det`). T14(b) ✓ (`Det.udtRule`). T1(b) bridge: no `Fin 4` witness. T2(b) ✓ (XOR).

**What remains** (priority order, see `udt-comm-trust-handoff`): the three-action `W2m` variant (T11(c)+); the `Fin 4` bridge witness; T15(a) in Lean (both designs in the findings); the T13(b) witness and the T13(d) `Faithful` failure; the four corpus DD variants (T5(a)); `ConcreteDS.ofTables`; the strict witness for `DynamicsCI ∧ ¬DD(2)` (T5(c)); `UniqueFix` restricted to `range E` (audit r1 §3.5, flagged in the ledger); the `Entropy.lean` stretch items (T2(c), T5(d)); T14(a).

## Repair round 1

Repairer: a fresh-context agent (Fable 5.1, [scrubbed], 2026-09-30) that did not write the package. Audits read: `udt-comm-trust-audit-r1-fidelity`, `udt-comm-trust-audit-r1-adversarial` and their probes (`audit-r1-probes/`, elaborated by the auditors; their theorems were re-derived inside the package, see below). Nothing from the earlier formalization run was seen.

**Gate after the last edit: PASS** — `scripts/wp-audit Cleanroom.Udt.UdtCommTrust` (the root module, all modules), 771 declarations (r0: 652), axioms `propext`, `Classical.choice`, `Quot.sound` only, no `sorry`, no lint failure; run after `Construct.lean`, `WitnessDet.lean` and the `Advice`/`Concrete`/`Witness` changes were built (the final run of the round, after `Fairness.lean`, is recorded at the end of this section).

### Blocking issues

- **B1 (both lenses): `polE_follows_R` vacuous — fixed.** Cause confirmed: the unguarded junk-`0` `InternallyDriven` forces all `(ȧ, ä)` attained once one is, the pointwise rule then forces universal ties, and AF-R forces a strict preference; the package had no non-trivial model. Changes: (1) `ConcreteDS.InternallyDriven` is now the **guarded** identity (where both conditional probabilities are defined, i.e. among attained actions) — the fidelity auditor's fix (a); the old form is `InternallyDrivenJunk` with `InternallyDrivenJunk.toInternallyDriven` and `internallyDrivenJunk_nonempty` (was `internallyDriven_nonempty`). (2) `adviceFollowing_R` takes the guarded form; its proof gains one case split (an unattained competitor scores `−1`, `score_lt_of_empty`). (3) `stableR_nonempty` (mirror of `stable_nonempty`). (4) The corollary is split: `aE_follows_R_of_udtRuleAt` (P, per world: the rule at `ω`'s realized input only; attainment of the recommended action from `stableR_nonempty`) — the adversarial auditor's fix 1 — and `polE_follows_R` (C, the printed clause from it via the agent-dynamic factorization and `R ⊑ D_{I,B}`). (5) The auditors' probe theorems live in the package as `tie_of_udtRule_internallyDrivenJunk` (L) and `udtRule_internallyDrivenJunk_stableR_inconsistent` (P, finding 7). (6) Witnesses (`WitnessDet.lean`): `Det`, eight worlds with a constant following `Π*`, inhabits the **full** package of `polE_follows_R` (`Det.polE_follows_R`; N−, `Det.follows_direct` shows the conclusion is by construction); `W2.aE_follows_at_follow_world` inhabits the per-world package on the nondegenerate `W2` (N+: `W2.udtRuleAt_follow` from the computed gap, `W2.deviating_world` for non-degeneracy). (7) `W2.internallyDriven` is derived from `W2.internallyDrivenJunk` (the 288 identities are unchanged). Ledger, findings (items 7, 9, §C) and this report corrected accordingly.
- **B2 (adversarial): `W2m` N− on the conclusion side — fixed by relabelling** (the minimal fix the auditor offered). Ledger cell and the witness section now say: N+ for the hypothesis package and T17, N− for `selfTrust_repaired`'s conclusion (two actions, forced tie). The three-action variant is recorded in the open file (`T11(c)+`) with the auditor's design constraint; not built (budget went to B1 and T4(b)).
- **B2 (fidelity) / B3 (adversarial): T4(b) skipped — fixed.** `Construct.lean`: the construction `polSC` with (i) `polSC_sub`/`polSC_sub_DIB` (P), (ii) `polD_eq_polSC_of_oC` (P, at neutral-side-channel worlds) and `polD_eq_polSC_iff_inert` (L — on the mandate's unforced event (ii) is exactly the inertness assumption; finding 4′), (iii) `polD_eq_polSC_of_modProb_zero` (C), and `withPolSC` with `withPolSC_hlink`, `withPolSC_polS_sub` discharging T13(c)'s `hlink` and T7/T10/T11's `Π* ⊑ D_{I,B}` for the constructed policy. Precondition weakened from `FactorsAs Ô Ǒ` to `NeutralCompatible` (`neutralCompatible_of_factorsAs`). Witnesses `W2.polSC_eq_polS`, `W2.sideChannelInert` (N−), `W2m.semChanSplit`/`neutral`/`neutralCompatible`/`not_factorsAs_oH_oC` (the failure case, N−). The "T7 one-liner" the fidelity audit missed is `withPolSC_polS_sub`.
- **Open items as `sorry` statements (both lenses, part of B2/B3): not done**, recorded in the open file's header with the reason (entropy items need imports not attempted; the witness items are existence claims over structures). Non-blocking for the stretch items per the fidelity audit; disclosed.

### Non-blocking issues

Fixed: N1/§3.1 (`adviceFollowing_Pi` witness cell → none); §3.3 (`StableR` attribution: Source line and docstring now point at the proof's decomposition, O ~536; T16(d) corrected); §3.4/N3/N4/N5 (quantifier-over-value-types and junk-at-unrealized caveats: `Concrete.lean` module docstring, `Stable`/`StableR` docstrings and Fidelity lines, ledger header); §3.6/N2 (`MinMod` docstring: `a` unrestricted; "attained by some chosen policy" is a choice); §3.8/N6 T14(b) (`udtRule_of_const`, P); §3.9 (findings §C rewritten); §3.10 (report numbers: 64 worlds, `7/16`, `policyUtility_lt`); §3.11 (`unique_given` → L); N7 (AF-R squeeze caveat in the docstring and ledger). Not fixed, flagged: §3.5 `UniqueFix` off-range junk (ledger Status `flagged`; the definition sits in `Determination.lean` and its change was not worth a second full rebuild this round); §3.7 the strict `DynamicsCI ∧ ¬DD(2)` witness; §3.8's other items (`ofTables`, the `Fin 4` bridge witness, T5(a) variants, T13(d), T15(a) Lean); §3.12/N-open (open items as `sorry`).

### Pushing further

`udtRule_of_const` (T14(b), P), the per-world/printed split of "`Π̈ = R` in fact", and `Fairness.lean` (T15(a), positive half: `followsR_of_hasCA_const`, P — the findings' constant-`R` design verified and strengthened to CA at one input with no DD/stability/rule) are the round's additions beyond the repairs. The two-valued refutation design of T15(a) and the three-action `W2m` variant remain open.

**Final gate of the round: PASS** — `scripts/wp-audit Cleanroom.Udt.UdtCommTrust` after the last edit (`Fairness.lean` added to the root module): 773 declarations, axioms `propext`, `Classical.choice`, `Quot.sound` only, no `sorry`, no lint failure. Every module `lean-build` clean (`Witness.lean` fully rebuilt with the renamed `internallyDrivenJunk`). Commits: `1b67e842` (the repairs) and the following one (T15(a), root import, these lines).
