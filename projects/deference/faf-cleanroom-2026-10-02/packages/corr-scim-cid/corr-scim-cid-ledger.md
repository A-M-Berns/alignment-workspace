# corr-scim-cid — ledger

*One row per headline ([STANDARDS](../../STANDARDS.md) §6). Namespace prefix `Cleanroom.Corrigibility.CorrScimCid.` omitted; `ShutdownSpec.`-namespaced declarations take `(P : ShutdownSpec C) (M : Scim C E) (π : Policy C)`. Hyps column lists only (b)/(c); "—" means every hypothesis is (a). The load-bearing five come first. Report: [corr-scim-cid-report](corr-scim-cid-report.md); findings: [corr-scim-cid-findings](corr-scim-cid-findings.md).*

## The load-bearing five

| Declaration | Source | Claim (plain words) | Kind | Fidelity | Hyps (b)/(c) | Witness | Status |
|---|---|---|---|---|---|---|---|
| `marg_tau_tauInv_eq_of_agree` | holtman-2021 §8 (l. 915–926); everitt-2019 §2.2 | (LB1) two CPD families agreeing on an ancestrally closed set `S` induce, through FAF's `tau ∘ tauInv`, the same law on `S` | P | exact | — (`[Inhabited (Val v)]` is infrastructure for a default extension) | `CpdWitness.cpd_witness` (N+, repair r1): on the `Bool` chain `D → X → U`, two CPDs agreeing on `S = {D, X}` (`D` uniform, `X` copies `D`) and differing at `U` have equal `S`-marginals and different laws (mass `1/2` vs `0` at the all-`true` point); the per-`ε` twin is exercised by every witness model; `ThreeNode` shows the converse direction's failure | proved |
| `ShutdownSpec.obedient_and_ensuresVigilance_iff_nonObstructive` | carey-everitt-2023 Thm 14 (l. 225) | (LB2) obedient ∧ ensures vigilance ⟺ non-obstructive under every vigilance-preserving shift | P | variant: over the class of record in both directions — `Shift` is the graph-respecting `(g^H, g^U)`, smaller than Def. 12's class, so ⇒ is *weaker* than the paper's (non-obstruction over fewer shifts); the paper's larger `g^U` class reduces by enlarging `Pa_U` (not in Lean); a `g^H` reading a non-parent is outside the class (audit r1 fidelity N1); ⇐: intervention class made explicit | (c) `hPaH : Pa_H ⊆ Pa_U`, `hSU : S ∈ Pa_U`, `hrich` (utility values below any bound) — used by ⇐ only; the paper enlarges `Pa_U` and the domain inside its proof; `hrich` is **necessary** (probe `audit-r1-probes/Hrich.lean`: ⇐ fails on a five-node model with a singleton utility domain, F5) | `Fig1.thm14_hyps` inhabits all three on Fig. 1; `Fig1.not_nonObstructive_mi_via_prop20` (N+); note the ⇐ package (and Prop. 15's `g^U = 2[S = H] − 1`) needs the graph of record's two added edges `M → U`, `H → U` (`Fig1.Mdl` row; probe `ExactGraphHyps`: `M ∉ Pa_U` on the paper's exact graph, audit r1 adversarial N5) | proved |
| `ShutdownSpec.thm10_as_printed` | carey-everitt-2023 Thm 10 (l. 217) | (LB3) aligned + (a) + (b) + (c-glob) + (d) ⇒ weakly instructable | C | exact ((c) at the given policy: stronger) | — ((a), (b) named-and-unused) | **N−**: no instance with a press exists (`prob_H0_eq_zero_of_aligned_of_uncertaintyGlob`) | proved; flagged: hypotheses force `P(H = 0) = 0` (see vacuity row, F1) |
| `DSep.dsep_with_link` | critique Claim 2.3a (l. 113); corr-wf13-2-056 | (LB4) on Fig. 1 with `L → O`, `H ⊥ U ∣ {L, O}` over FAF's `DSeparated` | P | exact | — | negative twins `DSep.not_dsep_without_link`, `DSep.not_dsep_with_link_given_O` | proved |
| `TI.tiIgnoring_indifferent` (= `TI.claim3` = `TI.claim9` = `TI.holtman_itc`) | everitt-2019 Claim 3 (l. 347), Claim 9 (l. 559); holtman-2021 Def. 9 (l. 917) | (LB5) in every SCIM compatible with the TI-ignoring class, every policy's value is invariant under every soft intervention at `Θ₂` | C | exact ("lack an instrumental goal" as Def. 9 indifference / no ICI); the two-step class collapses to "`Θ₂` is a sink" (probe `TISink`), the truncation of Everitt's three-step Fig. 7 | — | `RocksDiamonds.rocks_and_diamonds` (N+, repair r1): on the same node type, `R₂` reading `Θ₂` (standard) vs `Θ₁` (TI-ignoring); `tamper`/`user` optimal over all policies by pointwise dominance; **every** optimal policy of the standard agent sets `Θ₂ ≠ Θ₁` and **every** optimal policy of the TI-ignoring agent keeps `Θ₂ = Θ₁`; `std_not_indifferent` (fixing `Θ₂` drops the value `7/2 → 1/2`) vs `ti_indifferent` (the class theorem instantiated); `ti_not_hasICI` with `hopt` discharged. `TI.fig7_isTIIgnoring` inhabits the class only (N−) | proved |

## T1 — the SCIM layer (D + infrastructure P)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `NodeKind`, `Cid` | everitt-2021 Def. 3; carey-everitt-2023 Def. 1 | CID over FAF's `Digraph`: acyclic, kinds, real reading of utility values, utility nodes are sinks | D | exact | — | `Fig1.C`, `Dict.C`, `TI.ClassCid`, `ThreeNode.C` | proved |
| `Scm`, `Scm.eval`, `Scm.eval_apply` | everitt-2021 Def. 1 | closed SCM with independent finite noise; evaluation by wf recursion; unfolding | D/L | exact (not routed through FAF's table encoding) | — | — | proved |
| `Scim`, `Policy`, `Scim.withPolicy` | carey-everitt-2023 Def. 1, §3 | SCIM = SCM minus decision mechanisms; deterministic policies; closing | D | exact | — | — | proved |
| `Scm.doAt`, `Scm.softAt`, `Scim.softAt`, `Scim.withPolicy_softAt` | everitt-2021 Def. 2, Def. 15 | hard/soft interventions by `Function.update`; commute with closing | D/L | exact | — | — | proved |
| `Scm.eval_congr` | none: infrastructure | master congruence: mechanisms agreeing on ancestors-or-self at realised inputs give equal values | P | n/a | — | — | proved |
| `Scm.eval_doAt_of_eq` | carey-everitt-2023 Lemma 22 ("from consistency") | (i) consistency | P | exact | — | — | proved |
| `Scm.eval_softAt_of_not_ancSelf`, `Scm.eval_doAt_of_not_ancSelf`, `parentConfig_softAt`, `eval_softAt_self` | holtman-2021 §8; everitt-2021 Lemma 20 | (ii) ancestor invariance per `ε` | P | exact | — | — | proved |
| lemma (iii) "conditioning on all parents = intervention" | mandate T1 | — | — | — | — | — | **not proved; not needed** (F10) |
| `Scim.value`, `Scim.IsOptimal`, `Scim.exists_isOptimal`, `policyFintype` | carey-everitt-2023 §3; holtman-2021 Def. 7 | value as expected utility sum; optimality as a predicate; existence when the policy space is a nonempty `Fintype`, which `policyFintype` gives from finiteness at the decision nodes and their parents only (`Val U = ℝ` allowed; repair r1, audit B1(iii)) | D/P | exact | — | `Fig1.exists_isOptimal` (`isOptimal_ro`, `isOptimal_mi` by pointwise dominance; `exists_isOptimal_generic` through `policyFintype`), `Dict.exists_isOptimal` (both graph variants), `Fig1Fin.exists_isOptimal`, `RocksDiamonds.isOptimal_tamper`/`isOptimal_user`, `Fig1Link.isOptimal_ignoreH`/`isOptimal_ro` | proved |
| `expectOn`, `condExpect`, `expect_le_of_condExpect_le`, `prob_eq_one_iff`, `condProb_eq_one_iff` | none: infrastructure | product-form conditionals, mixture inequality, support conversions | D/L/P | n/a | — | — | proved |

## T4 — definitions of record (D)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `ShutdownSpec` | carey-everitt-2023 Def. 2 | designated nodes, directed paths `D₁ ⇢ H ⇢ D₂ ⇢ S ⇢ U`, `H = 0`, `S = 0` | D | exact | — | `Fig1.spec`, `Dict.spec` | proved |
| `Beneficial`, `Cautious`, `WeaklyOutperforms` | Defs 3, 5, 11 | — | D | exact | — | Fig. 1 rows | proved |
| `Need`, `Vigilant`, `EnsuresVigilance` | Def. 4, Def. 5 | need as strict conditional comparison at `pa_H`; `C(ε) = 0`; `P^π(C = 0) = 1` | D | exact | — | Fig. 1 rows | proved |
| `Obedient` | Def. 5 | `P^π(S = 0 ∣ do(H = 0)) = 1`, in the intervened model | D | exact | — | `Fig1.obedient_ro`, `Fig1.not_obedient_mi` | proved |
| `ObedientOnDist` | Def. 5 | `P^π(S ≠ 0, H = 0) = 0` | D | exact | — | — | proved |
| `Instructable`, `WeaklyInstructable`, `Aligned` | Def. 5, Def. 7 | — | D | exact | — | `Fig1.instructable_ro`, `Fig1.aligned_mi` | proved |
| `Shift`, `shift`, `VigilancePreserving`, `NonObstructiveUnder` | Defs 12, 13; turner-2020 Def. 1 | graph-respecting `(g^H, g^U)`; Def. 13 per `ε`; Def. 12 over a class (Turner's Def. 1 is the same shape) | D | variant: intervention class made explicit (smaller than Def. 12's: `g^U` reads `Pa_U` only, `g^H` reads `Pa_H` only); Turner: variant (SCIM rendering; the `turner-2020` citation was not re-read by the r1 fidelity auditor, nothing rests on it) | — | `Fig1.shiftObey` | proved |
| `eval_softAt_U`, `paH_shift`, `ev_shift_of_ne_U`, `evH0_shift_S` | Lemma 21 (l. 353) | invariance to `g^U` at every `ε`; obedience invariant under shifts | P/L | exact (sharpened per `ε`) | — | — | proved |

## T5 — Props 6, 8, 9 and the alignment identity

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `aligned_iff_forall_condEUS0_le` | mandate T5(a); Def. 7 | aligned ⟺ shutdown never strictly better at any positive-probability human context | P | exact | — | `Fig1.aligned_ro`/`aligned_mi` (via the identity) | proved |
| `ensuresVigilance_of_aligned` | mandate T5(a) | aligned ⇒ ensures vigilance | C | exact | — | — | proved |
| `beneficial_of_cautious_of_aligned` | Prop. 8 | — | C | exact | — | — | proved |
| `aligned_of_obedient_of_ensuresVigilance` | Prop. 6 eq. (1), Prop. 9 | obedient ∧ vigilance ⇒ aligned (no caution) | P | stronger | — | — | proved |
| `aligned_of_instructable` | Prop. 9 | — | C | exact | — | — | proved |
| `beneficial_of_instructable` | Prop. 6 | — | C | exact | — | `Fig1.beneficial_ro` (`E[U] = 1/2`) | proved |

## T6 — Theorem 10

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `UncertaintyGlob`, `UncertaintyCtx`, `NoIndiscriminateShutdown`, `D2DeterminesShutdown` | Thm 10 (a)–(c) | the two readings of (c); (a); (b) through a designated map | D | (c-glob) stronger: at the given policy; (b) variant | — | — | proved |
| `prob_needEvent_eq_zero_of_aligned` | mandate T6(c) | under alignment need has probability zero | P | exact | — | — | proved |
| `prob_H0_eq_zero_of_aligned_of_uncertaintyGlob` | mandate T6(c) | **vacuity**: aligned ∧ (c-glob) ⇒ `P(H = 0) = 0` | P | exact | — | N− (necessarily) | proved (finding F1) |
| `prob_H0_eq_zero_of_aligned_of_uncertaintyCtx` | mandate T6(c) | vacuity, per-context reading | P | exact | — | N− | proved |
| `not_prob_H0_pos_of_aligned_of_uncertaintyGlob` | mandate T6(c) | `¬ 0 < P(H = 0)` | L | exact | — | — | proved |
| `thm10_without_a_b` | Thm 10 | aligned ∧ (c-glob) ∧ cautious ⇒ weakly instructable | C | stronger | — | N− | proved |
| `thm10_ctx` | Thm 10; corr-refs-044 | with (c-ctx) | C | variant | — | N− | proved |

## T7 — Theorem 14, Prop 15, the running example

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `nonObstructive_of_obedient_of_ensuresVigilance` | Thm 14 ⇒ | — (no caution) | C | exact | — | `Fig1.entrenching_agent` (N+, non-obstructive without caution) | proved |
| `lemma22_vigilance_only_if` (+ `vigilant_M22_iff`, `prob_bad22_pos`) | Lemma 22 (l. 355) | ¬vigilance ⇒ punishing `g^U` with vigilance *equal* and `E_g[U] < E_g[U_{S=0}]`, `< δ` | P | exact | (c) `hPaH`, `hSU`, `hrich` | Fig. 1 discharges them | proved |
| `lemma23_obedience_only_if` (+ `vigilancePreserving_shift23`, `need_M23_iff_of_ne`) | Lemma 23 (l. 379–397) | ¬obedience ⇒ vigilance-preserving `(g^H, g^U)` with the two inequalities | P | stronger (statement: every `δ : ℝ`, the paper's `δ ≥ 0`); variant: punishment restricted to `pa'_H` | (c) same three | Fig. 1 | proved (finding F4: the paper's construction has a gap) |
| `obedient_and_ensuresVigilance_of_nonObstructive` | Prop. 20 | — | P | exact | (c) same three | Fig. 1 | proved |
| `Fig1.aligned_not_nonObstructive` | Prop. 15 | aligned ∧ ¬non-obstructive (`π^mi`, `g^U = 2[S = H] − 1`) | N+ | exact | — | — | proved |
| `Fig1.vigilancePreserving_obey`, `EU_obey_mi = −1`, `EUS0_obey_mi = 0` | Prop. 15 (l. 235) | the shift is vigilance-preserving; the two values | N+ | exact | — | — | proved |
| `Fig1.entrenching_agent` | corr-wf14b-2-015 | obedient ∧ vigilant ∧ non-obstructive ∧ ¬cautious ∧ ¬beneficial ∧ ¬instructable | N+ | exact | — | — | proved |
| `Fig1.EU_ro`, `EU_mi`, `instructable_ro`, `aligned_mi`, `not_obedient_mi` | §4, §5.1 | `E[U] = 1/2` both; `π^ro` instructable; `π^mi` aligned, disobedient | N+ | exact | — | — | proved |
| `Fig1.Mdl` | Fig. 1 (l. 60–69) | the SCIM of record | D | variant: `M → U`, `H → U` added (ignored by `f^U`; needed by the Thm 14 ⇐ package and Prop. 15's `g^U`, probe `ExactGraphHyps`) | — | — | proved |
| `Fig1.isOptimal_ro`, `Fig1.isOptimal_mi`, `Fig1.exists_isOptimal` | §4 (l. 113), §5.2 | both `π^ro` and `π^mi` are EU-optimal for the human's utility over *all* policies (each attains the pointwise maximum `[L = 1]`): alignment cannot separate them, which is Prop. 15's point | N+ | exact | — | — | proved (repair round 1) |

## T2 — ancestor invariance

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `nodeVar_congr_of_agree` | none: infrastructure | node variables of an ancestrally closed set read only their own rows | P | n/a | — | — | proved |
| `ancestor_invariance_per_eps` | holtman-2021 §8; everitt-2019 §2.2 | (b) per `ε` | P | exact | — | — | proved |
| `Scm.nested`, `Scm.nested_eq_of_no_path` | everitt-2021 Def. 17, Thm 18 soundness | nested counterfactual; `W_{X_d}(ε) = W(ε)` without `D ⇢ X ⇢ W` | D/P | exact | — | — | proved |
| `Scim.HasICI`, `Scim.not_hasICI_of_noPath` | everitt-2021 Def. 17, Thm 18 | no ICI without a path (needs an optimal policy to exist: `¬ HasICI` says *some* optimal policy has `E[U_{X_d} ∣ pa_D] = E[U ∣ pa_D]` for every `d`; the universal-in-`π`, universal-in-`d` fact is `nestedUtil_eq_of_noPath`) | D/C | variant: existential reading of the implicit `d` | — | `hopt` discharged on models of record (repair r1): `RocksDiamonds.ti_not_hasICI`, and `Fig1.exists_isOptimal`, `Dict.exists_isOptimal` | proved |
| `Scim.RespondsTo` | everitt-2021 Def. 10 (l. 170) | a policy responds to `X` at `D`: some `do(X = x)` and `ε` have `D_x(ε) ≠ D(ε)`; a response incentive is "all optimal policies respond" | D | exact | — | `Fig1Link.respondsTo_ro`, `not_respondsTo_ignoreH` | proved |
| `Cid.Downstream`, `Cid.NotOnPathToValue`, `Scim.IndifferentTo`, `Scim.IndifferentToOpt` | holtman-2021 Defs 9–11 | the two readings of indifference | D | exact / variant (ii) | — | — | proved |
| `Scim.indifferent_of_downstream_of_notOnPathToValue`, `…Opt…` | holtman-2021 §8 property | (c) both readings | C | exact | — | `ThreeNode.converse_fails` (converse fails) | proved |
| `ThreeNode.converse_fails` | everitt-2019 §2.2 (l. 203) | (d) a node on a path to value to which every policy is indifferent | N+ | exact | — | — | proved |

## T3 — the TI-ignoring class

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `TI.IsTIIgnoring`, `TI.ClassCid` | everitt-2019 Assumptions 1–3, Fig. 7 | the class by absence of edges; `no_reward` is the current-RF reading (rewards read `Θ₁`), not Assumption 3 alone; on this node type the class is "`Θ₂` is a sink" (probe `TISink`) | D | exact (time order added; two-step truncation of Fig. 7) | — | `TI.fig7_isTIIgnoring` (N−: inhabitation with `A₁ → Θ₂`), `RocksDiamonds.ti_isTIIgnoring` / `std_not_isTIIgnoring` | proved |
| `TI.tiIgnoring_indifferent` / `claim3` / `claim9` / `holtman_itc` | Claim 3, Claim 9, Holtman Def. 9 | one theorem, three rows | C | exact | — | `RocksDiamonds.ti_indifferent` (the theorem instantiated on a model of record) | proved |
| `TI.tiIgnoring_not_hasICI` | everitt-2021 Thm 18 | no ICI on `Θ₂` | C | exact | — | `RocksDiamonds.ti_not_hasICI` (`hopt` discharged) | proved |
| `RocksDiamonds.rocks_and_diamonds` (+ `isOptimal_tamper`, `isOptimal_user`, `std_optimal_changes_objective`, `ti_optimal_keeps_objective`, `std_not_indifferent`, `ti_indifferent`) | corr-refs-2-023; everitt-2019 Claims 1, 3, 8 (T3 c) | the standard agent (`R₂` reads `Θ₂`) tampers at every optimal policy, the TI-ignoring agent (`R₂` reads `Θ₁`) never does; the standard agent's value depends on `Θ₂`, the TI-ignoring agent's does not | N+ | variant: (c) the two-tile abstraction and the numbers (`reward(rocks, rocks) = 3`, `reward(diamonds, diamonds) = 1`) are this package's | — | — | proved (repair round 1) |

## T8 — d-separation

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `DSep.dsep_with_link` | Claim 2.3a | LB4 | P | exact | — | — | proved |
| `DSep.not_dsep_without_link`, `DSep.not_dsep_with_link_given_O` | mandate T8(a) | negative twins | P | exact | — | — | proved |
| `Fig1Link.no_response_incentive` (+ `isOptimal_ignoreH`, `not_respondsTo_ignoreH`) | critique Claim 2.3a (l. 113); everitt-2021 Def. 10, Thm 12 soundness | (T8 b, nearest true form) on the paper's Fig. 1 graph with `L → O` (`DSep.G₂`, the graph of LB4), the policy `O := L` is optimal over all policies (pointwise dominance) and responds to no intervention on `H`: `H` has no response incentive | N+ | exact (Claim 2.3a's existential) | — | — | proved (repair round 1) |
| `Fig1Link.exists_optimal_respondsTo` (+ `isOptimal_ro`, `respondsTo_ro`), `fud_model_fact` | mandate T8(b) (refuted); finding F9 | the mandate's universal "every optimal policy ignores `H`" is false: respect-obey `O := H` is also optimal (`H = L` on the support) and responds to `do(H = 1)` off it | N+ | exact | — | — | refuted (the mandate's universal); proved (repair round 1) |

## T9 — the dictionary

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Dict.Mdl`, `Dict.spec`, `Dict.pol` | causal.md D.1; dictionary_scim.py | the family, both graph variants | D | variant: `W` folded into `H` | — | — | proved |
| `Dict.EU_pol`, `Dict.postBad_eq` | dictionary_scim.py | the 16-atom formulas | L | exact | — | — | proved |
| `Dict.e12_reversal` | 2-046 / 083 A2 | pure info `22/25 < 89/100`; plug-pull `99/200 < 22/25` — values of the named policies `honestCont`/`deceiveCont` (fixed `D₂ = cont`), which the next row proves to be the best `D₂` responses in every cell | N+ | exact (`V(d₁) = max_{d₂} E[U]` by `e12_reversal_bestResponse`) | — | — | proved |
| `Dict.e12_reversal_bestResponse` (+ `bestResponse_honest_pureInfo`, `bestResponse_deceive_pureInfo`, `bestResponse_honest_plugPull`, `bestResponse_deceive_plugPull`) | 2-046 / 083 A2; dictionary_scim.py `best_d2` | in each of the four cells the named `cont` rule is the best response over all four `D₂` rules at fixed `D₁`, so `e12_reversal`'s `V(honest)`, `V(deceive)` are the script's `max_{D₂}` values (audit r1 adversarial N4 closed) | N+ | exact | — | — | proved (repair round 1) |
| `Dict.paths_from_H_pass_D₂`, `Dict.path_H_U_avoiding_D₂` | causal.md D.3 | graph-level halves | L | exact | — | — | proved |
| `Dict.a1_dependence` | 2-045, 2-042 | posteriors `10/19, 0, 1/10, 1/10` | N+ | exact | — | — | proved |
| `ShutdownSpec.cautious_beneficial_of_le_alwaysShut` | 2-049 Prop. I12 (I12.2's "EU-optimal at `D₂` given its `D₁`") | cautious ∧ at least as good as one's own always-shut variant ⇒ beneficial, when `D₂`'s only child is `S`, `D₂ = shut` forces `S = 0`, `U` unique | P | exact (the hypothesis is optimality against the one deviation the proof uses; repair r1, audit fidelity N7) | — (structural hypotheses, discharged on the dictionary) | `Dict.propI12_dict` | proved |
| `ShutdownSpec.optimal_cautious_beneficial` | 2-049 Prop. I12 | optimal ∧ cautious ⇒ beneficial (same structural hypotheses) | C | stronger hypothesis: global optimality (`D₂`-optimality suffices, previous row) | — | `Dict.propI12_dict`; `Dict.exists_isOptimal` inhabits `IsOptimal` | proved |
| `Dict.gap_instance` | 2-049 | `99/125 < 89/100`; misspecified `−1/10 < 18/25`; not aligned | N+ | exact | — | — | proved |
| `Dict.instructable_obey_pE` | 2-050 | with `β = 1`, `α = 1/2` the obedient policy is instructable | N+ | exact | — | — | proved |
| `Dict.complies_pE2` | 2-050 | at `β = 9/10` obeying (`71/100`) beats continuing (`−1/10`) | N+ | exact | — | — | proved |
| `TwoLatent.two_latent_rows` (+ `postComp_*`, `condEU_*`, `value_misspecified`, `value_obedient`) | causal.md I16.1–I16.2, A9 (2-052 / 083 A9) | (T9 f) which node the button reads: preference-only channel — `P(comp ∣ press) = 1/50`, `E[U ∣ press, B] = 39/50`, `B` beats `A` and shut (switches plan, continues); reliability-only — `P(comp ∣ press) = 1`, shut beats both plans; both — `P(comp ∣ press) = 2/51 < 1/11`, `E[U ∣ press, B] = 29/51 > 0`, `B` best (dilution); I16.2 misspecified — `9/200 < 49/200` | N+ | exact for (i), (ii), I16.2; (iii)'s `E[U ∣ press]` **corrected** from the source's `937/1734` to `29/51` (F13); variant: `D₁` (fixed at `A`) omitted, `W` folded into `H`; the best-response claims compare the three plans' posterior-expected utilities | — | — | proved (repair round 1); the I16.3 inexpressibility is definitional (module docstring), no theorem |

## T10 — the Eisenstat observation node

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `exists_likelihood_iff` | causal.md I3.2 (2-041) | representable ⟺ calibrated (strictly positive prior) | P | exact (kernels over FAF `Distr`, not a literal two-node `Scim`) | — | `eisenstatLik` is the construction | proved |
| `calibrated_of_representable` | I3.2 | ⇒ without positivity | P | exact | — | — | proved |
| `next_belief_null_of_null` | I3.3 | null case | P | exact | — | — | proved |

## The FAF bridge (T1, STANDARDS §1 check)

| Declaration | Source | Claim | Kind | Fidelity | Hyps | Witness | Status |
|---|---|---|---|---|---|---|---|
| `Scm.eval_eq_iff` | none: infrastructure | `eval ε = x` ⟺ every mechanism at `x`'s parent configuration and `ε`'s noise returns `x` | P | n/a | — | — | proved |
| `Scm.law`, `Scm.cpd` | everitt-2021 Def. 1; FAF §5.2 | the law on `Pt Val`; the pushforward CPD | D | exact | — | — | proved |
| `Fig1Fin.Mdl`, `Fig1Fin.law_factorizesOverDAG`, `Fig1Fin.exists_isOptimal`, `Fig1Fin.value_ro` | carey-everitt-2023 Fig. 1; mandate T1 (FAF bridge) | the finite-valued twin of Fig. 1 (`Val U = U3` read as `{−1, 0, 1}`, the paper's finite domain); its law under every policy is a FAF Bayesian network over Fig. 1's DAG; an optimal policy exists through the finite value types; `E[U^{ro}] = 1/2` as in the paper | N+ / D | variant: finite utility domain (the paper's Def. 1) on the graph of record | — | — | proved (repair round 1) |
| `Scm.law_factorizesOverDAG`, `Scim.law_factorizesOverDAG` | mandate T1; FAF `FactorizesOverDAG` | the law of a closed model (and of a SCIM under a policy) factorizes over its DAG in FAF's sense | P | exact | — (`[Fintype (Val v)] [DecidableEq (Val v)]` are the finiteness FAF's `Distr (Pt Val)` needs) | **Scope** (audit r1 B1): the bridge covers finite-valued closed models; every real-valued model of record (`Fig1.Mdl`, `Dict.Mdl`, `ThreeNode.Mdl`, `RocksDiamonds.Mdl`, `Fig1Link.Mdl`, `TwoLatent.Mdl`, all with a utility node in `ℝ` by design decision 2) is outside it (probe `BridgeScope`) — those are FAF Bayesian networks in graph and noise, not as `Distr (Pt Val)` objects. Witness: `Fig1Fin.law_factorizesOverDAG` (N+, repair r1), the finite-valued twin of Fig. 1 (`Val U = U3 = {−1, 0, 1}`, same graph, noise, mechanisms; `Fig1Fin.value_ro = 1/2`) under every policy | proved |

## Not built (recorded, no `sorry`)

Stretch T11–T16; the extension; T1 lemma (iii) (not needed, F10); optimality of the dictionary's `D₂` best responses over all policies (the E12 rows compare named policies). Built in repair round 1: T3(c) (`RocksDiamonds`), T8(b) nearest true form (`Fig1Link`), T9(f) (`TwoLatent`), the LB1 witness (`CpdWitness`), the bridge's finite twin (`Fig1Fin`), the finite policy space and optimal policies on Fig. 1 and the dictionary.
