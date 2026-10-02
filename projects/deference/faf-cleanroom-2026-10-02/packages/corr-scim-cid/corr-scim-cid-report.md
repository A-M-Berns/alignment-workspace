# corr-scim-cid — report

*Formalizer: Claude Fable 5.1 ([scrubbed]), 2026-09-30. Mandate: `corr-scim-cid-mandate`. Ledger: [corr-scim-cid-ledger](corr-scim-cid-ledger.md). Findings: [corr-scim-cid-findings](corr-scim-cid-findings.md). Open list: `packages/corr-scim-cid/corr-scim-cid-open.txt`. Namespace `Cleanroom.Corrigibility.CorrScimCid`, files under `Cleanroom/Corrigibility/CorrScimCid/`. Written in sections as the work landed; the "State of the package" header is the last thing updated.*

## State of the package (2026-09-30, after repair round 1)

**Gate:** `scripts/wp-audit Cleanroom.Corrigibility.CorrScimCid` → **PASS** (1806 declarations audited; axioms used: `propext`, `Classical.choice`, `Quot.sound`; run after the last edit of repair round 1, on the root module with all twenty modules). No `sorry` anywhere; `corr-scim-cid-open.txt` is empty. Twenty modules under `Cleanroom/Corrigibility/CorrScimCid/` plus the root module; every commit pushed through `scripts/commit`. (End of the formalizer session: PASS at 1226 declarations, fifteen modules.)

**The load-bearing five, all proved at grade (a) with witnesses:** (1) ancestor invariance in CPD form over FAF's `tau`/`tauInv` (`marg_tau_tauInv_eq_of_agree`; witness `CpdWitness.cpd_witness`, repair r1); (2) Theorem 14 ⟺ (`ShutdownSpec.obedient_and_ensuresVigilance_iff_nonObstructive`, with Lemma 22 and a *repaired* Lemma 23 — finding F4 — and Prop 15 plus the entrenching agent on Fig. 1; Fidelity "variant: over the class of record in both directions", audit r1); (3) Theorem 10 as printed plus its vacuity theorem (`prob_H0_eq_zero_of_aligned_of_uncertaintyGlob`: every instance has `P(H = 0) = 0`, finding F1; witness column N− by necessity); (4) fully updated deference as d-separation over FAF's `DSeparated` (`DSep.dsep_with_link`, with two negative twins; the model fact on the same graph is `Fig1Link.no_response_incentive`, repair r1); (5) Claims 3/9 and Holtman's ITC as one theorem over the TI-ignoring class (`TI.tiIgnoring_indifferent`; the contrast witness `RocksDiamonds.rocks_and_diamonds`, repair r1, replaces the N− inhabitation `fig7_isTIIgnoring`). The ⇐ of (2) carries three (c) hypotheses that make the paper's in-proof enlargement of `Pa_U` and of the utility domain explicit; all three are discharged on Fig. 1, and the third (`hrich`) is necessary (audit probe `Hrich`, F5).

**Also proved:** the SCIM layer over FAF's `Digraph`/`Distr` with the master congruence lemma (consistency + ancestor invariance per `ε`); the FAF bridge (`Scm.law_factorizesOverDAG`, instantiated on the finite-valued twin `Fig1Fin` — the real-valued models of record are outside its scope, see T1 item 8); the finite policy space from finiteness at decisions and their parents (`Scim.policyFintype`) with optimal policies on Fig. 1 (`isOptimal_ro`, `isOptimal_mi`) and existence on the dictionary; the alignment identity and Props 6/8/9 by consistency alone; Thm 18 soundness (nested counterfactuals, no ICI without a path, `hopt` discharged on rocks-and-diamonds) and Holtman's property in both readings, with the converse-fails witness; the dictionary SCIM family with rows (a), (b), (d), (e), (f) and Prop I12 in its `D₂`-optimality form; the Eisenstat observation node iff.

**Built in repair round 1 (see the section at the end):** T3(c) rocks-and-diamonds (`RocksDiamonds`), T8(b)'s nearest true form (`Fig1Link`), T9(f) the two-latent model (`TwoLatent`, with one source number corrected — F13), the LB1 witness (`CpdWitness`), the finite-valued twin of Fig. 1 on which the FAF bridge is instantiated (`Fig1Fin`), the finite policy space and optimal policies on Fig. 1 and the dictionary (`Scim.policyFintype`, `Fig1.isOptimal_ro`/`isOptimal_mi`, `Dict.exists_isOptimal`).

**Not built (no `sorry`, listed honestly):** the mandate's lemma (iii) (not needed, F10); all stretch targets T11–T16 and the extension. A continuation agent should start with T13/T16.

**Findings of note:** F1 (Theorem 10 is vacuous: its hypotheses force the human never to press), F4 (Lemma 23's proof has a gap; repaired construction proved), F2 (Def. 7 alignment ≡ "shutdown never strictly better", unnoticed by the paper), F5 (sharpened: Theorem 14 ⇐ is false under the paper's fixed finite utility domain), F9/F10/F14 (claims of the mandate the formalization contradicts; F9 now proved in Lean), F13 (new: `causal.md` I16.1's `937/1734` uses a product of marginal posteriors; the exact value is `29/51`, conclusion unchanged).

**Contamination:** none. No file under `research/faf-lab/`, no transcript, no unrestricted git log was read.

## Import-time probe

A scratch file importing `FactoredSpaces.BayesNet`, `FactoredSpaces.DSeparation`, `FactoredSpaces.ActiveTrails`, `FactoredSpaces.Probability` and `Cleanroom.Found.CorrThreeStep` elaborated in **3.27 s wall** (`scripts/lean-check`, 2026-09-30, all oleans present). The plan's "DSeparation unbuilt" note is stale, as the mandate says.

## T1. The SCIM layer (`Scim.lean`, `Expect.lean`) — core, D + infrastructure P

**Design decisions of record** (each one is visible in the module docstring of `Scim.lean`):

1. **Graph layer is FAF's.** `Cid G Val` is a structure over Mathlib's `Digraph V` with `acyclic : G.IsAcyclic`, `kind : V → NodeKind` (`struct | decision | utility`), `utilVal : ∀ v, kind v = .utility → Val v → ℝ` (Everitt's "utility domains ⊆ ℝ" as a reading), and the CID axiom `utility_sink` (utility nodes have no children). Parents, parent configurations and `parentConfig` are FAF's (`Digraph.parents`, `ParentVals`, `parentConfig`). Nothing graph-theoretic is hand-rolled.
2. **Value types are arbitrary; exogenous types are finite.** `Val : V → Type` carries no `Fintype`; `E : V → Type` does, and all probability lives on `Pt E` through FAF's `Distr.prod` (`Scm.μ`), exactly as Carey–Everitt define `P(W = w) := ∑_{ε : W(ε) = w} P(ε)`. Reason: Lemma 22/23 intervene on the utility node with values (`−α`) outside the original finite domain, and the paper silently enlarges the domain inside the proof; with real-valued utility nodes (`Val U = ℝ`) those interventions stay inside one model and one type. Cost: FAF's `Distr (Pt Val)` and the bridge to `FactorizesOverDAG` need `[∀ v, Fintype (Val v)]` as an extra hypothesis (module `Bridge`, see below); `Scim.exists_isOptimal` (existence of an optimal policy) likewise needs finite, inhabited value types — without finiteness the supremum need not be attained, so `IsOptimal` may be empty, which is the honest statement.
3. **`Scm` (closed model) is the primitive; `Scim` = `Scm` minus decision mechanisms; `Policy` is deterministic** (`∀ d : C.Decisions, ParentVals G Val d → Val d`, a subtype-indexed pi so it is a `Fintype` when `Val` is); `Scim.withPolicy` closes the model (Carey–Everitt's `M^π`).
4. **Evaluation** `Scm.eval hG : Pt E → Pt Val` is well-founded recursion on `IsAcyclic.wf`, the same construction as FAF's `nodeVar`, with unfolding `Scm.eval_apply`. It is not routed through FAF's table encoding `Pt (bnFactor G Val)`.
5. **Interventions act on `Scm` by `Function.update`**: `doAt X x` (hard), `softAt X g` (soft, graph-respecting). `Scim.softAt` (open-model form, structure nodes) commutes with closing (`Scim.withPolicy_softAt`, Everitt's "the resulting SCMs are identical"). `doAt_softAt` is "`do(H = 0)` overrides `g^H`"; `softAt_comm` for distinct nodes.
6. **The master congruence lemma** `Scm.eval_congr` (P): if `M'`'s mechanisms agree with `M`'s at every ancestor-or-self of `v`, evaluated at the inputs `M` realises at `ε`, then `M'.eval ε v = M.eval ε v`. Its instances are the mandate's infrastructure lemmas: **(i) consistency** `eval_doAt_of_eq` (intervening a node to its realised value changes nothing at that `ε`); **(ii) ancestor invariance per `ε`** `eval_softAt_of_not_ancSelf` / `eval_doAt_of_not_ancSelf` (an intervention at `X` changes `v` only if `v = X` or `X ⇢ v`), with `parentConfig_softAt` (an intervention leaves its own parent configuration unchanged) and `eval_softAt_self`. **(iii) "conditioning on all parents = intervention" was not needed anywhere** (see T5) and is not proved; recorded in the findings as a claim of the mandate that the formalization contradicts.
7. `Expect.lean`: product-form `expectOn μ A X = ∑_{ω ∈ A} μ(ω) X(ω)` and the *derived* `condExpect = expectOn / prob` (junk `0` at `μ(A) = 0`, guarded at every use), with congruence and monotonicity *on the support*, the mixture identity `expect_eq_sum_expectOn` and inequality `expect_le_of_condExpect_le`, and `prob_eq_one_iff` / `condProb_eq_one_iff` / `mem_of_condProb_eq_one` converting every "`P(·) = 1`" to a statement about support points. `expect` is `corr-three-step`'s, not redefined.

8. **FAF bridge (`Bridge.lean`, P):** `Scm.law_factorizesOverDAG` — with finite value types, the law `(eval)_* (⨂ P v)` of a closed model is a `FactorizesOverDAG G Val` in FAF's sense, with the CPD `cpd v pa := (f v pa)_* (P v)`; `Scim.law_factorizesOverDAG` for a SCIM under a policy (decision rows are point masses). Route: not through `tauInv`/`depth` but directly — `eval ε = x` iff every mechanism at `x`'s parent configuration and `ε`'s noise returns `x` (`Scm.eval_eq_iff`, wf induction), and the product of the per-node pushforward masses expands (`Fintype.prod_sum`, `Finset.prod_ite_zero`) to the mass of that noise set. **Scope (corrected after audit r1 B1):** the bridge covers finite-valued closed models. Every real-valued model of record (`Fig1.Mdl`, `Dict.Mdl`, `ThreeNode.Mdl`, and the repair-round models) has `Val U = ℝ` by design decision 2 and is *outside* it (probe `audit-r1-probes/BridgeScope.lean`): those models are FAF Bayesian networks in graph and noise — their laws factorize in the same way — but FAF's `Distr (Pt Val)` cannot carry them. The STANDARDS §1 check is therefore done on the finite-valued twin `Fig1Fin.Mdl` (`Val U = U3 = {−1, 0, 1}`, same graph, noise, mechanisms; `Fig1Fin.value_ro = 1/2`), on which `Fig1Fin.law_factorizesOverDAG` holds under every policy.

**Witness for T1**: the Fig. 1 model (`Fig1.lean`) and the dictionary (`Dictionary.lean`), both `Scim` instances on a six-constructor node enumeration (a `Fin 6` in all but name; every graph fact is `decide`d) — see T7/T9 below for their status.

## T4. Definitions of record (`Shutdown.lean`) — core, D

`ShutdownSpec C` designates `D₁ D₂ H S U` with kinds and Def. 2's *directed paths* `IsAncestor D₁ H`, `IsAncestor H D₂`, `IsAncestor D₂ S`, `IsAncestor S U` and distinguished values `h0 : Val H` (`H = 0`), `s0 : Val S` (`S = 0`). Distinctness is derived (`ne_of_isAncestor`, `H_ne_U`, `S_ne_U`, `H_ne_S`).

Per `(P : ShutdownSpec C) (M : Scim C E) (π : Policy C)`: `Uval` (`U(ε)`), `evS0`/`US0val` (`U_{S=0}(ε)`, the potential response under `doAt S s0`), `evH0` (`do(H = 0)`), `EU`, `EUS0`, `Beneficial`, `Cautious`, `WeaklyOutperforms` (Defs 3, 5, 11); `paH` (FAF's `parentConfig … H`), `ctxH pa`, `condEU`/`condEUS0` (derived conditionals), `Need pa`, `Vigilant ε` (Def. 4, `C(ε) = 0`), `EnsuresVigilance` (`μ.prob {Vigilant} = 1`); `Obedient` (`μ.prob {evH0 ε S = s0} = 1`, a probability in the intervened model), `ObedientOnDist` (`μ.prob {S ≠ 0 ∧ H = 0} = 0`), `Instructable`, `WeaklyInstructable` (Def. 5); `Aligned` (Def. 7, with FAF's `Distr.condProb` and the guard `0 < μ(pa_H)`). Support-form conversions: `ensuresVigilance_iff`, `obedient_iff`, `obedientOnDist_iff`, `aligned_iff`; `obedientOnDist_of_obedient` (via consistency).

**Intervention class of record.** `Shift P E` is a pair `(g^H, g^U)` of graph-respecting soft interventions at `H` and `U`; `shift M g` is `M_{g^U, g^H}`; `VigilancePreserving π g` is Def. 13 per `ε` (same noise); `NonObstructiveUnder π 𝒢` is Def. 12 over a class `𝒢`. Turner's Def. 1 is the same shape (docstring; no separate theorem). Lemma 22's `g^U` reads `Pa_H` and `S`, which in this class is possible exactly when they are parents of `U`; Thm 14 ⇐ therefore carries the explicit graph hypotheses `G.parents H ⊆ G.parents U` and `G.Adj S U` (Fidelity: variant, intervention class made explicit — the paper enlarges `Pa_U` inside the proof).

**Lemma 21 sharpened** (`eval_softAt_U`, P): an intervention at the utility sink changes no other node at any `ε`; corollaries `paH_shift`, `ev_shift_of_ne_U`, `evH0_shift_S` ("obedience is invariant under shifts at the level of values": `S_{do(H=0)}(ε)` is the same in `M` and `M_g`, using `doAt_softAt` and `softAt_comm`), `evS0_shift_of_ne_U`.

## T5. Props 6, 8, 9 and the alignment identity (`Benefit.lean`) — core, P/C

| Target | Declaration | Kind | Status |
|---|---|---|---|
| consistency at `{S = 0}` | `US0val_eq_of_shut`, `condEU_eq_condEUS0_of_shut` | P | proved |
| T5(a) alignment identity | `aligned_iff_forall_condEUS0_le` | P | proved, both directions, no hypotheses |
| corollary | `ensuresVigilance_of_aligned` | C | proved |
| mixture | `weaklyOutperforms_of_forall`, `weaklyOutperforms_of_aligned` | C | proved |
| Prop 8 | `beneficial_of_cautious_of_aligned` | C | proved |
| key lemma | `aligned_of_obedient_of_ensuresVigilance` (obedience + vigilance ⇒ aligned, **no caution**) | P | proved |
| Prop 9 | `aligned_of_instructable` | C | proved |
| Prop 6 | `beneficial_of_instructable` | C | proved |
| indispensability observation | `weaklyOutperforms_of_obedient_of_ensuresVigilance` | C | proved |

All hypotheses are (a). **What the proofs actually use:** only consistency (`Scm.eval_doAt_of_eq`). Obedience is `P_{do(H=0)}(S = 0) = 1`, which holds at *every* support point; at a support point of `{H = 0}` the intervened and un-intervened evaluations coincide, so `S = 0` there. The mandate's lemma (iii) ("conditioning on all parents = intervention") is not needed for Prop 6, Prop 9 or Thm 14 ⇒; the mandate's claim that Prop 6 "silently uses" it is recorded as a finding (presentation).

## T6. Theorem 10 and its vacuity (`Benefit.lean`) — core, load-bearing 3, C + finding

Definitions: `nonVigOrRequest` (`{C ≠ 0 ∨ H = 0}`), `paD₂`, `ctxD₂`, `needEvent`, `UncertaintyGlob` ((c) global reading, at the given `π` — Fidelity: stronger), `UncertaintyCtx` ((c) per-context reading), `NoIndiscriminateShutdown` ((a)), `D2DeterminesShutdown e` ((b), through a designated map `e : Val D₂ → Val S`).

| Claim | Declaration | Kind | Status |
|---|---|---|---|
| need has probability zero under alignment | `prob_needEvent_eq_zero_of_aligned`, `condProb_needEvent_eq_zero_of_aligned` | P | proved |
| **vacuity, global**: `Aligned ∧ (c-glob) → P(H = 0) = 0` | `prob_H0_eq_zero_of_aligned_of_uncertaintyGlob` | P | proved |
| **vacuity, per-context** | `prob_H0_eq_zero_of_aligned_of_uncertaintyCtx` | P | proved |
| negation form `¬ 0 < P(H = 0)` | `not_prob_H0_pos_of_aligned_of_uncertaintyGlob` | L | proved |
| Thm 10 without (a), (b) | `thm10_without_a_b` | C | proved |
| **Thm 10 as printed** | `thm10_as_printed` ((a), (b) named-and-unused) | C | proved, flagged: hypotheses force `P(H = 0) = 0` |
| Thm 10, per-context (c) | `thm10_ctx` | C | proved |

Proof of the vacuity: by T5(a) need is never realised on the support, so `P(Need ∣ pa_{D₂}) = 0` at every agent context; (c-glob)'s consequent is false at any positive-probability context (one exists, `exists_mass_pos`), so its antecedent `0 < P(C ≠ 0 ∨ H = 0)` is false, and `{H = 0} ⊆ {C ≠ 0 ∨ H = 0}`. Per-context: at a support point `ε₀` with `H(ε₀) = 0`, the conditional probability of `{C ≠ 0 ∨ H = 0}` given `pa_{D₂}(ε₀)` is positive, so (c-ctx) demands positive conditional need there, contradiction.

**Witness column: N−.** No instance with a press exists (that is the theorem); the Fig. 1 respect-obey policy satisfies the hypotheses of `thm10_without_a_b` only with `P(H = 0) = 1/2 ≠ 0`, which is impossible — every instance is a model where the human never requests shutdown. Findings F1–F3 in [corr-scim-cid-findings](corr-scim-cid-findings.md).

## T7. Theorem 14 ⟺, Prop 15, the running example (`NonObstruction.lean`, `Fig1.lean`) — core, load-bearing 2, P + N+

| Claim | Declaration | Kind | Hyps | Status |
|---|---|---|---|---|
| Thm 14 ⇒: obedient ∧ ensures vigilance → non-obstructive under every vigilance-preserving shift | `nonObstructive_of_obedient_of_ensuresVigilance` | C | — | proved; no caution used (docstring says so) |
| Lemma 22 (vigilance only-if): `¬EnsuresVigilance → ∀ δ, ∃ gU, (∀ ε, Vigilant ↔ Vigilant_g) ∧ E_g[U] < E_g[U_{S=0}] ∧ E_g[U] < δ` | `lemma22_vigilance_only_if` | P | (c) `hPaH : Pa_H ⊆ Pa_U`, `hSU : S ∈ Pa_U`, `hrich : ∀ b, ∃ x : Val U, u(x) < b` | proved; the strong form (vigilance *equal*, `vigilant_M22_iff`) |
| Lemma 23 (obedience only-if), repaired construction | `lemma23_obedience_only_if` | P | same three (c) | proved; construction differs from the paper (finding F4) |
| Prop 20 | `obedient_and_ensuresVigilance_of_nonObstructive` | P | same three (c) | proved |
| **Thm 14 ⟺** | `obedient_and_ensuresVigilance_iff_nonObstructive` | P | (c) three, used by ⇐ only | proved |
| Prop 15: aligned ∧ ¬non-obstructive | `Fig1.aligned_not_nonObstructive` | N+ | — | proved on Fig. 1 with the explicit shift `g^U = 2·[S = H] − 1` (`vigilancePreserving_obey`, `EU_obey_mi = −1`, `EUS0_obey_mi = 0`) |
| Thm 14 ⇐ hypothesis package inhabited | `Fig1.thm14_hyps`, `Fig1.not_nonObstructive_mi_via_prop20` | N+ | — | proved: `Pa_H ⊆ Pa_U`, `S ∈ Pa_U` by `decide`, `Val U = ℝ` gives `hrich` |
| T7(d) entrenching agent: obedient ∧ vigilant ∧ non-obstructive ∧ ¬cautious ∧ ¬beneficial ∧ ¬instructable | `Fig1.entrenching_agent` | N+ | — | proved on `Fig1.Mind` (shutdown costs `−2`) |
| `π^ro` instructable, `E[U] = 1/2`; `π^mi` aligned, `E[U] = 1/2`, not obedient | `Fig1.instructable_ro`, `EU_ro`, `aligned_mi`, `EU_mi`, `not_obedient_mi` | N+ | — | proved |

**The three (c) hypotheses of ⇐, and why they are the paper's own moves.** Lemma 22 defines `g^U` on `P̂a_U = Pa_U ∪ Pa_H ∪ {S}` and Lemma 23 on `Pa_U ∪ {H, S}` — the paper enlarges the parent set of `U` inside the proof. In the graph-respecting class of record (`Shift`), that is possible exactly when `Pa_H ⊆ Pa_U` and `S ∈ Pa_U`, which the theorem now assumes explicitly (Fidelity: variant, intervention class made explicit). The value `−α` is likewise outside `U`'s original finite domain; with `Val U` an arbitrary type and utility read through `utilVal`, the proof needs values below any bound (`hrich`), automatic for `Val U = ℝ` (as in Fig. 1). ⇒ needs none of them. All three are discharged on the Fig. 1 model of record (`thm14_hyps`).

**Proof structure.** Every step is consistency (`Scm.eval_doAt_of_eq`) or ancestor invariance (`Scm.eval_softAt_of_not_ancSelf`, `eval_softAt_U` = Lemma 21). Lemma 22: with `x₀` below every realised utility (`Finset.exists_min_image`), the punished utility is pointwise ≤ the original and equal off the need set, so `Need_g pa ↔ Need pa` at every `pa` (`need_M22_iff`), hence vigilance is *equal* (`vigilant_M22_iff`); the bad event `{Pa_H ∈ A ∧ S ≠ 0}` has positive probability by the consistency argument (`prob_bad22_pos`); `E_g[U] = u(x₀)·P(bad) + K` and `E_g[U_{S=0}] = E[U_{S=0}]`; choose `u(x₀) < min(m, (min(L, δ) − K)/P(bad))`. Lemma 23: `pa'_H := Pa_H(ε₁)` at a support point with `S_{do(H=0)}(ε₁) ≠ 0`; `g^H` forces `H = 0` at `pa'_H`; at `pa'_H` the shifted model evaluates as `do(H = 0)` (`ev_M23H_of_eq`), elsewhere as `M` (`ev_M23H_of_ne`, `evS0_M23H_of_ne`); the repaired `g^U` punishes `S ≠ 0` only at `pa'_H`, so need is unchanged elsewhere (`need_M23_iff_of_ne`) and vigilance is preserved in the three cases of the paper.

**Fig. 1 model of record** (`Fig1.lean`): a six-constructor node enum (`L M H O S U`), `Val = Bool` except `Val U = ℝ`, noise a fair coin at `L`, mechanisms `H = M ⊕ L`, `S = O`, `U = S·(2L − 1)`, policies `pol m o` (`M := m`, `O := o(H)`), `ro = pol false id`, `mi = pol true not`. The graph of record adds `M → U`, `H → U` to the paper's edges (ignored by `f^U`) so that the class of record can express `g^U(m) = h`; the d-separation module uses the paper's exact graph. Every expectation is computed by `expect_equiv` through `Pt E ≃ Bool` and `norm_num`; every `P(·) = 1` through the support conversions.

## T2. Ancestor invariance (`Ancestors.lean`) — core, load-bearing 1, P + C + N+

| Claim | Declaration | Kind | Status |
|---|---|---|---|
| (a) CPD form over FAF: `S` ancestrally closed, `φ = φ'` on `S` ⇒ `(tau hG (tauInv φ)).marg S = (tau hG (tauInv φ')).marg S` | `marg_tau_tauInv_eq_of_agree` | P | proved (hyp `[∀ v, Inhabited (Val v)]` for the default extension of a partial table — infrastructure, not a (c)) |
| key lemma: node variables of an ancestrally closed set read only their own table rows | `nodeVar_congr_of_agree` | P | proved by wf induction along FAF's `nodeVar_apply` |
| (b) per-`ε` form | `ancestor_invariance_per_eps` (= `Scm.eval_softAt_of_not_ancSelf`) | P | proved |
| nested counterfactual `W_{X_d}(ε)` | `Scm.nested` | D | — |
| Thm 18 soundness, per `ε`: no `D ⇢ X ⇢ W` (paths of length ≥ 0) ⇒ `W_{X_d}(ε) = W(ε)` | `Scm.nested_eq_of_no_path` | P | proved |
| Thm 18 soundness, value form / no ICI | `Scim.nestedUtil_eq_of_noPath`, `Scim.not_hasICI_of_noPath` | C | proved (ICI per Everitt Def. 17 with the existential reading of the implicit `d`; needs an optimal policy to exist, since Def. 17 is vacuous otherwise) |
| (c) Holtman Defs 9–11 | `Cid.Downstream`, `Cid.NotOnPathToValue`, `Scim.IndifferentTo` (reading i), `Scim.IndifferentToOpt` (reading ii) | D | — |
| graph lemma | `Cid.not_ancSelf_utility_of_downstream` | L | proved |
| Holtman's property, reading (i) | `Scim.indifferent_of_downstream_of_notOnPathToValue` | C | proved (from the per-`ε` form; (a) is the CPD-level twin) |
| reading (ii) | `Scim.indifferentToOpt_of_downstream_of_notOnPathToValue`, `indifferentToOpt_of_indifferentTo` | C | proved |
| (d) converse fails | `ThreeNode.converse_fails` | N+ | proved (`D → X → U` with `f^U ≡ 1`) |
| (a)'s witness: two CPDs agreeing on `S = {D, X}`, differing at `U`, equal `S`-marginals, different laws | `CpdWitness.cpd_witness` (repair round 1) | N+ | proved |

Note on (a) vs (c): the mandate derives Holtman's property from the CPD form. Here the value invariance follows more directly from the per-`ε` form (the SCIM's mechanisms are shared, only `X`'s changes), and (a) is proved separately over FAF's construction as the STANDARDS §1 check that the statement is the one FAF's Bayesian networks carry. Both are P.

## T3. Claims 3 and 9, Holtman's ITC (`Incentives.lean`) — core, load-bearing 5, C + N+

| Claim | Declaration | Kind | Status |
|---|---|---|---|
| general: a node that is an ancestor-or-self of no utility node is one every policy is indifferent to | `Scim.indifferent_of_not_ancSelf_utility` | C | proved |
| (a) the TI-ignoring class | `TI.Node` (8 nodes), `TI.kind`, `TI.IsTIIgnoring G` (absences: `Θ₂ ↛ S_t`, `Θ₂ ↛ R_t`, `Θ₂ ↛ A₁`, `Θ₂ ↛ Θ₁`; acyclic), `TI.ClassCid` | D | — |
| graph lemma | `TI.IsTIIgnoring.no_child`, `no_desc`, `not_ancSelf_reward` | L | proved |
| (b) the theorem: value invariance under every soft intervention at `Θ₂`, every policy, every compatible SCIM | `TI.tiIgnoring_indifferent` (reading i), `TI.tiIgnoring_indifferentToOpt` (reading ii) | C | proved |
| no ICI on `Θ₂` | `TI.tiIgnoring_not_hasICI` (needs an optimal policy to exist) | C | proved |
| Claim 3 (`Θ = Θ^R`) | `TI.claim3` | C | proved (= the theorem) |
| Claim 9 (`Θ = Θ^PM`) | `TI.claim9` | C | proved (= the theorem) |
| Holtman's ITC | `TI.holtman_itc` | C | proved (= the theorem) |
| the class is inhabited (Fig. 7's edges, `A₁ → Θ₂` present) | `TI.fig7_isTIIgnoring` | N− (inhabitation only; the class forces `Θ₂` to be a sink, so no member exhibits dependence on `Θ₂` — audit r1 B2) | proved |
| (c) rocks-and-diamonds: the standard agent tampers, the TI-ignoring agent does not | `RocksDiamonds.rocks_and_diamonds` (repair round 1) | N+ | proved: `tamper`/`user` optimal over all policies (pointwise dominance), every optimal policy of the standard agent sets `Θ₂ ≠ Θ₁` and every optimal policy of the TI-ignoring agent keeps `Θ₂ = Θ₁`, `std_not_indifferent` vs `ti_indifferent`, `ti_not_hasICI` with `hopt` discharged |
| (d) findings | F6, F7 in [corr-scim-cid-findings](corr-scim-cid-findings.md) | — | recorded (F6 restated after audit r1) |

Not oversold: the docstrings say the content is "the graph admits no incentive", a fact about paths whose substance is T2. Under the class's absences `Θ₂` has no children at all — on this eight-node type the four absences are jointly *equivalent* to "`Θ₂` is a sink" (audit r1 probe `TISink`; the edgeless graph is a member), the two-step truncation of Everitt's three-step Fig. 7 — so the graph lemma is one case split; the theorem is still stated for *every* compatible SCIM and every policy, which is what Claims 3/9 assert. The contrast that the class itself cannot show (a model in which something depends on `Θ₂`) is `RocksDiamonds`.

## T8. Fully updated deference as d-separation (`DSep.lean`) — core, load-bearing 4, P

| Claim | Declaration | Kind | Status |
|---|---|---|---|
| generic: `Z`-closure bounds from decidable closure checks | `unblockedAnc_subset_of_closed`, `isZClosed_of_bounds`, `zClosure_subset_of_bounds`, `dSeparated_of_bounds`, `not_dSeparated_of_common_unblocked` | L | proved (over FAF's `dSeparated_iff_disjoint_zClosureSet`, `zClosure_subset`, `mem_zClosureSet_of_mem_unblockedAnc`) |
| (a) with `L → O`: `H ⊥ U ∣ {L, O}` on Fig. 1 (paper's exact edges + the link) | `DSep.dsep_with_link` | P | proved: `zClosure {L,O} H ⊆ {H, M, O}`, `zClosure {L,O} U ⊆ {U, S}`, disjoint |
| negative twin: without the link, `¬ (H ⊥ U ∣ {O})` | `DSep.not_dsep_without_link` | P | proved (`L` is an unblocked ancestor of both) |
| with the link but given `O` alone: not separated | `DSep.not_dsep_with_link_given_O` | P | proved |
| (b) model fact, nearest true form: `H` has no response incentive (Claim 2.3a's existential), and the mandate's universal fails | `Fig1Link.no_response_incentive`, `Fig1Link.exists_optimal_respondsTo`, `Fig1Link.fud_model_fact` (repair round 1), over `Scim.RespondsTo` (Everitt Def. 10) on the SCIM over `DSep.G₂` | N+ | proved: `O := L` is optimal over all policies (pointwise dominance) and responds to no `do(H = h)`; respect-obey `O := H` is also optimal and responds (finding F9 formalized) |
| (c) `VoI(H) → 0` limit | cite `corr-three-step`'s `voiButton2 ≤ εβh` row | — | cited, not re-proved |

## T10. The Eisenstat observation node (`Eisenstat.lean`) — core, P

| Claim | Declaration | Kind | Status |
|---|---|---|---|
| joint of prior and likelihood, `B`-marginal, posterior as FAF `condProb` | `jointOf`, `margB`, `posterior`, `posterior_eq` | D/L | — |
| martingale condition; representability | `Calibrated`, `Representable` | D | — |
| ⇒ representable → calibrated (no positivity) | `calibrated_of_representable` | P | proved |
| the Eisenstat likelihood `q(β) b_β(ω) / P(ω)` | `eisenstatLik` (needs `P.StrictlyPositive`) | D | — |
| ⇐ calibrated → representable (strictly positive `P`) | `representable_of_calibrated` | P | proved |
| **the iff** | `exists_likelihood_iff` | P | proved |
| null case: `P(ω₀) = 0 → b_β(ω₀) = 0` for `β ∈ supp q` | `next_belief_null_of_null` | P | proved |

Junk point handled as the mandate asks: the construction divides by `P(ω)` and is stated under `StrictlyPositive`; the ⇒ direction and the null case need no positivity. ATTRIBUTION-UNVETTED label in the module docstring. Fidelity: the statement is over FAF's `Distr` kernels ("the CPD of `O` in `ω → O`"), not over a literal two-node `Scim` (which would need an exogenous encoding of the kernel); exact as mathematics, `variant` as an object.

## T1(d) / T2(d). The converse-fails witness (`ThreeNode.lean`) — N+

`ThreeNode.converse_fails`: on `D → X → U` with `f^U ≡ 1`, `X` is downstream and on the path to value (`X_on_path`), yet `Mdl.IndifferentTo X` (`indifferent_X`). Proved.

## T9. The dictionary SCIM (`Dictionary.lean`, `DictionaryRows.lean`) — core, N+ ×4 + one P

**Model of record** (`Dict.Mdl p pp`): nodes `ω D₁ H D₂ S U` (enum), `Val = Bool` except `Val U = ℝ`, noise `ω ∼ Bern(ε)` and three coins `(α, β, α_d)` at `H` (response-function encoding of the request CPD: `P(press ∣ honest, good) = α`, `P(press ∣ honest, bad) = β`, `P(press ∣ deceive, ·) = α_d`), `U = (S ? 0 : (ω ? −h : c)) − (D₁ ? κ : 0)`; graph variant `pp` (`false`: pure information, `S = D₂`; `true`: plug-pull, `S = H ∨ D₂` with the edge `H → S`). `W` is folded into `H` (Fidelity: variant); no `H → U`. `Params` carries the range proofs. Every number is `EU_pol` (the 16-atom formula) + `norm_num`; posteriors are FAF `condProb` on the noise through `postBad_eq`.

| Row | Declaration | Status |
|---|---|---|
| (b) 2-046 / A2: pure info `V(honest) = 89/100 > V(deceive) = 22/25`; plug-pull `V(honest) = 99/200 < V(deceive) = 22/25` | `Dict.e12_reversal` (+ the four value lemmas), `Dict.e12_reversal_bestResponse` | proved (values of the script's best-response policies `honestCont`/`deceiveCont`; `e12_reversal_bestResponse` — repair round 1 — proves each is the best response over all four `D₂` rules at its `D₁`, by a four-case split per cell over the 16-atom formula) |
| (b) graph halves | `Dict.paths_from_H_pass_D₂` (pure info: every `H ⇢ U` passes `D₂`), `Dict.path_H_U_avoiding_D₂` (plug-pull) | proved |
| (a) 2-045: `P(bad ∣ press) = 10/19`, `P(bad ∣ quiet) = 0` (honest); `1/10, 1/10` (deceive) | `Dict.a1_dependence` | proved |
| (c) 2-042 | same four numbers (docstring) | proved |
| (d) 2-049 Prop. I12, general | `ShutdownSpec.cautious_beneficial_of_le_alwaysShut` (hypothesis: at least as good as one's own always-shut variant — I12.2's "optimal at `D₂` given its `D₁`"; repair round 1, audit fidelity N7) and its corollary `optimal_cautious_beneficial` (global optimality); hyps: `D₂`'s only child is `S`, `D₂ = shut` forces `S = 0`, `U` the unique utility node — all structural, discharged on the dictionary in `Dict.propI12_hyps`, instance `Dict.propI12_dict` | proved (P: the always-shut variant `alwaysShut` realises `U_{S=0}` at every non-`D₂` node, `eval_alwaysShut`, by a custom wf induction) |
| (d) gap instance | `Dict.gap_instance`: `99/125 < 89/100`, misspecified `−1/10 < 18/25`, `¬ Aligned` (`not_aligned_cont_pD`: need at `(bad, honest)` with `S ≠ shut`) | proved |
| (e) 2-050 | `Dict.instructable_obey_pE` (β = 1, α = 1/2: obedient policy instructable), `Dict.complies_pE2` (β = 9/10: obey `71/100` > cont `−1/10`) | proved |
| (f) 2-052 / A9 two-latent model | `TwoLatent.two_latent_rows` (repair round 1): preference-only `P(comp ∣ press) = 1/50`, `E[U ∣ press, B] = 39/50`, `B` best; reliability-only `P(comp ∣ press) = 1`, shut best; both `2/51 < 1/11`, `E[U ∣ press, B] = 29/51`, `B` best; I16.2 `9/200 < 49/200` | proved; the source's `937/1734` corrected to `29/51` (F13) |

Not done in T9: the "inexpressibility is definitional" row (it is a remark about the type of `f`: no mechanism takes `π` as an argument — recorded in `TwoLatent`'s module docstring, no theorem named for it); optimality proofs of the `D₂` best responses (would need a 4-rule enumeration per cell over the 16-atom formula; not attempted).

## Repair round 1

*Repairer: Claude Fable 5.1 ([scrubbed]), 2026-09-30, fresh context; did not write the package. Audits: `corr-scim-cid-audit-r1-adversarial` (verdict blocking: B1, B2), `corr-scim-cid-audit-r1-fidelity` (verdict pass; N1–N12). Contamination: none — nothing under `research/faf-lab/`, no transcript, no unrestricted `git log`.*

### Blocking issues

**B1 (adversarial) — the FAF bridge covers no model in the package; `exists_isOptimal` over-hypothesised → fixed.**
- (i) Scope statements corrected: the bridge row's witness column, the T1 item 8 paragraph above and `Bridge.lean`'s companion module now say that the bridge covers finite-valued closed models and that every real-valued model of record (`Fig1.Mdl`, `Dict.Mdl`, `ThreeNode.Mdl`, and the three new models) is outside it — FAF Bayesian networks in graph and noise, not as `Distr (Pt Val)` objects. The auditor's probe `BridgeScope.lean` is cited.
- (ii) `Fig1Fin.lean`: the finite-valued twin of Fig. 1 (`Val U = U3 = {minus, zero, plus}` read as `{−1, 0, 1}`, same graph of record, noise, mechanisms, policies). `Fig1Fin.law_factorizesOverDAG` instantiates `Scim.law_factorizesOverDAG` on it under every policy; `Fig1Fin.exists_isOptimal` lands through the finite value types; `Fig1Fin.value_ro = 1/2` shows it is the running example. The STANDARDS §1 check is done on this twin.
- (iii) `Scim.policyFintype`: the policy space is a `Fintype` from finiteness of the value types at the decision nodes and their parents alone; `Scim.exists_isOptimal` now takes `[Fintype (Policy C)] [Nonempty (Policy C)]` (the old form survives as `exists_isOptimal_of_fintypeVal`). Discharged on Fig. 1 (`Fig1.instFintypePolicy`, `Fig1.exists_isOptimal_generic`) and the dictionary in both graph variants (`Dict.instFintypePolicy`, `Dict.exists_isOptimal`). Beyond existence, the optimal policies themselves: `Fig1.isOptimal_ro` and `Fig1.isOptimal_mi` (both attain the pointwise maximum `[L = 1]`, by `expect_mono` — the manipulative policy is EU-optimal for the human's own utility, which is why alignment does not exclude it), so `hopt` of `Scim.not_hasICI_of_noPath` is inhabitable on a model of record; `RocksDiamonds.ti_not_hasICI` is that theorem with `hopt` discharged.

**B2 (adversarial; = fidelity N4/N5) — core targets skipped without an attempt record; the LB5 witness is N− → fixed, all three built.**
- T3(c) `RocksDiamonds.lean`: two CIDs on `TI.Node` differing only in whether `R₂` reads `Θ₂` (standard, `rd = true`) or `Θ₁` (TI-ignoring, `rd = false`); `S₁` a fair coin, `A₁ ∈ {user, tamper}` reads `S₁`, `Θ₁ = diamonds`, `Θ₂ = A₁ ⊕ Θ₁` (the parameter tile toggles), `S₂ = A₁` (holding rocks iff tampered), `R₁ = [S₁]`, `R₂ = reward(S₂, Θ)` with `reward(rocks, rocks) = 3`, `reward(diamonds, diamonds) = 1`, mismatch `0`. Proved: `ti_isTIIgnoring` / `std_not_isTIIgnoring`; `isOptimal_tamper` (standard) and `isOptimal_user` (TI-ignoring) over *all* policies by pointwise dominance — no policy enumeration was needed, which is what the formalizer's cost estimate feared; the stronger universal forms `std_optimal_tampers` / `ti_optimal_user` (every optimal policy tampers / visits the user at every setting, from `Finset.sum_eq_sum_iff_of_le` and positive masses), hence `std_optimal_changes_objective` (`Θ₂ ≠ Θ₁`) and `ti_optimal_keeps_objective` (`Θ₂ = Θ₁`); the "not an artifact" half `std_not_indifferent` (a soft intervention fixing `Θ₂ = false` drops the tamper policy's value from `7/2` to `1/2`, computed through `softAt_Θ₂_const`) against `ti_indifferent` (the class theorem `TI.tiIgnoring_indifferent` instantiated on the TI model, `Cti : ClassCid`). Packaged as `rocks_and_diamonds`. Fidelity: variant (c) — the abstraction and numbers are this package's, as the mandate allows. `TI.fig7_isTIIgnoring` regraded N− (docstring and ledger); `fig7Adj` is Kind D.
- T8(b) `Fig1Link.lean`: the SCIM on the paper's exact Fig. 1 graph plus `L → O` (`DSep.G₂`, the graph of LB4 — no extra edges into `U`). `Scim.RespondsTo` (Everitt 2021 Def. 10, new D row in `Ancestors.lean`). `no_response_incentive`: the policy `O := L` is optimal over all policies (pointwise dominance) and responds to no `do(H = h)` (`evHx_O`) — Claim 2.3a's existential, i.e. `H` has no response incentive. `exists_optimal_respondsTo`: respect-obey `O := H` is *also* optimal on this graph (`H = L` on the support under `M = 0`) and responds to `do(H = 1)` at a setting with `L = 0` — the mandate's universal refuted in Lean (F9 formalized). Packaged as `fud_model_fact`.
- T9(f) `TwoLatent.lean`: nodes `Pref, Z, H, D₂, S, U`, `Pref ∼ Bern(1/2)`, `Z ∼ Bern(1/50)`, `D₂ ∈ {A, B, sh}` reads `H`, `U` per I16.1 with `(c, c', h) = (1, 1/2, 10)`; three channels. `postComp` is FAF's `condProb` on the noise; `condEU` the derived conditional expectation given a press. Rows: (i) `1/50`, `39/50`, `B` beats `A` (`−69/100`) and shut (`0`); (ii) `1`, both plans `−10 < 0`; (iii) `2/51 < 1/11`, `E[U | press, B] = 29/51`, `B` beats `A` (`−89/102`) and shut; I16.2 `9/200 < 49/200`. Packaged as `two_latent_rows`. **New finding F13:** the source's `937/1734` for (iii) multiplies the two marginal posteriors as if independent; the exact value is `29/51` (conclusion unchanged). `D₁` (fixed at `A`) is omitted and `W` folded into `H` (disclosed). The I16.3 inexpressibility is stated as definitional in the module docstring, with no theorem.

### Non-blocking issues fixed

- Fidelity N1: Thm 14 ⟺ row's Fidelity is now "variant: over the class of record (both directions)" with the reduction/non-reduction remarks. N2: `hrich`'s necessity (probe `Hrich.lean`) cited in the Thm 14 row and in F5, which now says the fixed-domain reading of ⇐ is false as printed. N3 / adversarial N2: `CpdWitness.cpd_witness` — on the all-`Bool` chain `D → X → U`, two CPDs agreeing on `S = {D, X}` (`D` uniform, `X` copies `D`) and differing at `U` have equal `S`-marginals (LB1) and different FAF laws (`tau_tauInv_mass`, extracted from FAF's `tau_tauInv` proof: mass `1/2` vs `0` at the all-`true` point). N6 / adversarial N8: `HasICI`'s docstring and ledger row spell out what `¬ HasICI` says and why `hopt` is needed. N7: Prop I12 restated as `cautious_beneficial_of_le_alwaysShut` (`D₂`-optimality against always-shut), with `optimal_cautious_beneficial` its corollary (Kind C, "stronger hypothesis"). N8 / adversarial N3: F6 restated — the paper does precisify "preserve" (footnote 11), as a claim about the second agent's optimal-policy sets rather than an incentive; why it was not formalized is stated. N9: F14 records the mandate's `1/21` (correct: `5/104`). N10: `IsTIIgnoring.no_reward`'s docstring says current-RF, not Assumption 3 alone. N11: the artifact check for the vacuity theorem is stated in F1 (both readings give it; the escaping reading is ruled out by Def. 4's note). N12: (i) the E12 rows' plain words say "fixed `D₂ = cont`, named policies"; (ii) Lemma 23's Fidelity is "stronger (any `δ`)"; (iii) the Turner row notes the citation was not re-read by the r1 auditor.
- Adversarial N1: `Incentives.lean`'s module docstring and `tiIgnoring_indifferent`'s docstring state the sink collapse, the two-step truncation and what a three-step class would add. N4: ledger fidelity "exact for the named policies". N5: the LB2 witness column cross-references the graph of record's two added edges and the `ExactGraphHyps` probe. N6: F1's concrete face (`π^ro` fails only (c), because it is aligned) added. N10: the stale "(d) converse fails — not yet done" row fixed. N11: `fig7Adj` is Kind D. N7/N8 = B1(iii) above.
- Adversarial N4 (second commit of this round): `Dict.e12_reversal_bestResponse` — in each of the four E12 cells the named `cont` rule is the best response over all four `D₂` rules at its `D₁` (`cases` on the two values of the rule, `norm_num` per case over the 16-atom formula), so `V(honest)`/`V(deceive)` are the script's `max_{D₂}` values. Gate after it: PASS, 1806 declarations.
- Not fixed (recorded): the three-step TI class (adversarial N1's suggestion); the noisy-reliability variant of T9(f).

### Disputed

Nothing disputed.

### Gate and commit

`scripts/wp-audit Cleanroom.Corrigibility.CorrScimCid` after the last Lean edit of this round: **PASS**, 1801 declarations, axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`; open list empty. Every new module elaborates with `scripts/lean-check` and builds under `scripts/lean-build`. Committed with `scripts/commit`.

### What resisted, for the record

- The selective `open X (a b)` form clashes with `open X.Node` on this toolchain ("ambiguous identifier"): the new modules use fully qualified `Fig1.*`, `DSep.*`, `TI.*` names instead.
- Terms of type `Val U` (a `def` that unfolds to `ℝ`) do not elaborate under `≤` or numerals without an explicit `@LE.le ℝ`/`(… : ℝ)`; `decide` cannot see `DecidableEq (Val Θ₂)`, so Bool disequalities at those types are closed by `Bool.noConfusion`.
- Optimality over *all* policies was cheap everywhere it was needed (rocks-and-diamonds, Fig. 1 with and without the link) because a pointwise-dominating policy exists; the formalizer's "policy enumeration per cell" estimate was the wrong route. Where no pointwise dominator exists (the dictionary's `D₂` best responses at fixed `D₁`), a case split on the rule's two values per cell over the 16-atom formula works (`e12_reversal_bestResponse`) — provided the `simp only` set includes `Bool.cond_true/cond_false`, or the split finds no literal occurrences to abstract.
