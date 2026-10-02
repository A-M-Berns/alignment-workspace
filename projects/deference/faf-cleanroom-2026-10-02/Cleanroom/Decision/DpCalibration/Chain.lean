import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCalibration.Limit

/-!
# The implication diagram among the senses (T10) and Proposition 1 (T4)

**The diagram** (each arrow a theorem, each crossed arrow a named witness; `H_d` := coverage,
a.s. subtree-veridicality at every `d`-node, and almost-fairness):

| implication | theorem / witness |
|---|---|
| limit ⟹ strict | `limitOCAt_imp_strictOCAt` (`Limit.lean`) |
| strict ⟹̸ limit | `toldYouSo` (`ToldYouSo.lean`) |
| prior + Jeffrey ⟹ strict | `priorCalibrated_jeffrey_strictOC` (below; Proposition 1) |
| strict ⟺ per-run under `H_d` | `perRunSSCAt_iff_strictOCAt` (`Bridge.lean`; Proposition 3) |
| per-run ⟺ per-occurrence under almost-fairness | `perRunSSCAt_iff_perOccSSCAt_of_almostFair` (below) |
| limit ⟹̸ per-run off "realized" | `a1_limitOCAt` + `a1_not_perRunSSCAt` (`Witnesses.lean`) |
| strict ⟹̸ per-run | `tnV2_observation1` (`Examples.lean`; Observation 1) |
| per-run ⟹̸ strict | `mug1_perRun_not_strict` (`Mugging.lean`) |
| per-run ⟹̸ per-occurrence under nesting | `amd_perRun_not_perOcc` (below) |
| strict ⟹ masked at recorded points with full-support strict action credences | `maskedOCAt_of_strict_fullSupport` (`Recording.lean`) |
| strict ⟹̸ masked | `coinQuery_strict_not_masked` (below) |
| masked ⟹̸ strict | `mug1_masked_not_strict` (`Mugging.lean`) |

`H_d` is stated over `dp-core-tree`'s predicates (`Covers`, `SubtreeVeridicalAS`, `AlmostFair`),
never over "strongly fair" (`dp-fairness-reloc`'s word).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## Proposition 1 -/

section prop1

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Proposition 1**: if a prior state `s°` is prior-calibrated for `C` on `B` and every queried
state whose observation is `s°`-positive is the Jeffrey conditioning of `s°` at that
observation, then `B` is strictly observation-calibrated for `C`. Both clauses of Definition 11
are used: clause 2 is what makes the `V`-side true (v2 change-log 13). The Jeffrey hypothesis is
demanded only where `P_{s°}(O_d) > 0` (repair round 1: the earlier `∃ h` form asserted
`P_{s°}(O_d) > 0` at *every* queried point, which no tree with a null queried observation — e.g.
`toldYouSo` under `C₀` at `d₁₀` — could satisfy, although Definition 8 leaves such points free).
Source: [[decision-problems-v2]] §3.1 Proposition 1
Kind: C
Fidelity: exact
Hyps: (a) `PriorCalibrated C B s°`, (a) `s d = jeffreyCond s° (O_d)` at every queried `d` with
`P_{s°}(O_d) > 0` -/
theorem priorCalibrated_jeffrey_strictOC (s : ι → State Ω K) (s₀ : State Ω K)
    (hprior : PriorCalibrated C B s₀)
    (hs : ∀ d ∈ queried B, ∀ h : 0 < s₀.pr (obs d), s d = jeffreyCond s₀ (obs d) h) :
    StrictOC s obs C B := by
  intro d hd hpos
  have h : 0 < s₀.pr (obs d) := by rw [hprior.1]; exact hpos
  have hsd := hs d hd h
  refine ⟨fun X => ?_, fun X _ hXO => ?_⟩
  · rw [hsd, jeffreyCond_pr]
    simp only [State.pr, hprior.1]
    exact div_mul_cancel₀ _ hpos.ne'
  · rw [hsd, jeffreyCond_V]
    exact hprior.2 _ hXO

end prop1

/-! ## Per-run versus per-occurrence under almost-fairness -/

section almostFair

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- On an almost-fair tree `#_d ∈ {0, 1}`, so `𝔼[#_d 1_X] = μ({λ⊨X} ∩ occ(d))`.
Source: `zoo.md` ZO-3 ("on almost-fair trees `#_d ≤ 1` makes Def 13's two equations identical")
Kind: L -/
theorem countMass_eq_of_almostFair (hAF : AlmostFair B) (d : ι) (X : Finset Ω) :
    countMass C B d X = mass C B (worldEv B X ∩ occ d B) := by
  unfold countMass mass
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := hAF d ℓ
  rcases Nat.lt_or_ge 0 (count d B ℓ) with hpos | hzero
  · have h1 : count d B ℓ = 1 := by omega
    have hmem : ℓ ∈ occ d B := (mem_occ d B ℓ).mpr hpos
    rw [if_pos hmem, h1]; simp
  · have h0 : count d B ℓ = 0 := by omega
    have hmem : ℓ ∉ occ d B := fun hc => by rw [mem_occ] at hc; omega
    rw [if_neg hmem, h0]; simp

/-- On an almost-fair tree `𝔼[#_d r 1_X] = ∑_{{λ⊨X} ∩ occ(d)} μ r`.
Source: `zoo.md` ZO-3
Kind: L -/
theorem countPay_eq_of_almostFair (hAF : AlmostFair B) (d : ι) (X : Finset Ω) :
    countPay C B d X = ∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ := by
  unfold countPay
  rw [← Finset.sum_ite_mem]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have h := hAF d ℓ
  rcases Nat.lt_or_ge 0 (count d B ℓ) with hpos | hzero
  · have h1 : count d B ℓ = 1 := by omega
    have hmem : ℓ ∈ occ d B := (mem_occ d B ℓ).mpr hpos
    rw [if_pos hmem, h1]; simp
  · have h0 : count d B ℓ = 0 := by omega
    have hmem : ℓ ∉ occ d B := fun hc => by rw [mem_occ] at hc; omega
    rw [if_neg hmem, h0]; simp

/-- **Per-run SSC ⟺ per-occurrence SSC on almost-fair trees**, clause form.
Source: `zoo.md` ZO-2 ("FR-1(i) (no nesting) gives per-run = per-occurrence"); ZO-3
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B` -/
theorem perRunClausesAt_iff_perOccClausesAt_of_almostFair (hAF : AlmostFair B)
    (s : ι → State Ω K) (d : ι) : PerRunClausesAt s C B d ↔ PerOccClausesAt s C B d := by
  unfold PerRunClausesAt PerOccClausesAt PerRunClause1At PerRunClause2At
  simp only [countMass_eq_of_almostFair C B hAF, countPay_eq_of_almostFair C B hAF, worldEv_univ,
    Finset.univ_inter]

/-- **Per-run SSC ⟺ per-occurrence SSC on almost-fair trees** (guards coincide:
`𝔼[#_d] = μ(occ(d))`).
Source: `zoo.md` ZO-2; mandate T10 (`perRun_iff_perOcc_of_almostFair`)
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B` -/
theorem perRunSSCAt_iff_perOccSSCAt_of_almostFair (hAF : AlmostFair B) (s : ι → State Ω K)
    (d : ι) : PerRunSSCAt s C B d ↔ PerOccSSCAt s C B d := by
  unfold PerRunSSCAt PerOccSSCAt
  rw [countMass_eq_of_almostFair C B hAF, worldEv_univ, Finset.univ_inter,
    perRunClausesAt_iff_perOccClausesAt_of_almostFair C B hAF]

/-- **ZO-2's chain at a point** over `dp-core-tree`'s predicates: under coverage, a.s.
subtree-veridicality at every `d`-node and almost-fairness, limit ⟹ strict ⟺ per-run ⟺
per-occurrence at `d`.
Source: `cf-workflow/phase2-notes/repair/zoo.md` ZO-2 (the coincidence theorem, stated here over
`Covers`/`SubtreeVeridicalAS`/`AlmostFair` rather than "strongly fair, FRec, pruned, realized")
Kind: C
Fidelity: variant: hypotheses are `dp-core-tree`'s `H_d` (the derivation from strong fairness +
FRec + realized is `dp-fairness-reloc`/`dp-edt-udt-fair`'s)
Hyps: (a) `H_d`, (a) `AlmostFair B` -/
theorem zo2_chain_at [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω) (s : ι → State Ω K) {d : ι}
    (hcov : Covers obs C B d) (hver : ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q)
    (hAF : AlmostFair B) :
    (LimitOCAt s obs C B d → StrictOCAt s obs C B d) ∧
    (StrictOCAt s obs C B d ↔ PerRunSSCAt s C B d) ∧
    (PerRunSSCAt s C B d ↔ PerOccSSCAt s C B d) :=
  ⟨limitOCAt_imp_strictOCAt s obs C B d, (perRunSSCAt_iff_strictOCAt obs C B s hcov hver).symm,
    perRunSSCAt_iff_perOccSSCAt_of_almostFair C B hAF s d⟩

/-- **ZO-2's chain, package level**: with `H_d` at every queried point and almost-fairness,
`LimitOC → StrictOC`, `StrictOC ↔ PerRunSSC`, `PerRunSSC ↔ PerOccSSC`.
Source: `zoo.md` ZO-2
Kind: C
Fidelity: variant: hypotheses are `dp-core-tree`'s `H_d`
Hyps: (a) `H_d` at every queried `d`, (a) `AlmostFair B` -/
theorem zo2_chain [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω) (s : ι → State Ω K)
    (hH : ∀ d ∈ queried B, Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q)
    (hAF : AlmostFair B) :
    (LimitOC s obs C B → StrictOC s obs C B) ∧
    (StrictOC s obs C B ↔ PerRunSSC s C B) ∧
    (PerRunSSC s C B ↔ PerOccSSC s C B) := by
  refine ⟨limitOC_imp_strictOC s obs C B, (perRunSSC_iff_strictOC obs C B s hH).symm, ?_⟩
  unfold PerRunSSC PerOccSSC
  constructor
  · intro h d hd; exact (perRunSSCAt_iff_perOccSSCAt_of_almostFair C B hAF s d).mp (h d hd)
  · intro h d hd; exact (perRunSSCAt_iff_perOccSSCAt_of_almostFair C B hAF s d).mpr (h d hd)

end almostFair

/-! ## Witnesses -/

section witnesses

/-- **Proposition 1's hypothesis package inhabited on `B₁`** (N+): the prior state
`s° := (ν, 𝔼[r | ·])` is prior-calibrated, `P_{s°}(O_T) = ½ > 0`, and the Jeffrey-conditioned
state at `O_T` is then strictly calibrated (by Proposition 1).
Source: mandate T4 ("N+: `mug1 x y` with `s° :=` the state `(ν, 𝔼[r|·])`")
Kind: N+ -/
theorem mug1_prop1_instance (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    ∃ (s₀ : State MugW ℚ) (h : 0 < s₀.pr (mugObs ())), PriorCalibrated C (mug1 x y) s₀ ∧
      StrictOC (fun _ => jeffreyCond s₀ (mugObs ()) h) mugObs C (mug1 x y) := by
  refine ⟨calibratedState C (mug1 x y) Finset.univ (nu_univ_pos _ _), ?_, ?_, ?_⟩
  · rw [calibratedState_pr, Finset.inter_univ, nu_univ, div_one, mug1_nu_obs]; norm_num
  · exact priorCalibrated_calibratedState_univ C (mug1 x y) _
  · apply priorCalibrated_jeffrey_strictOC mugObs C (mug1 x y) _ _
      (priorCalibrated_calibratedState_univ C (mug1 x y) _)
    intro d _ _
    cases d
    rfl

/-- `𝔼[r · 1_X]` on `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_paySum (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug1 x y) X =
      (if MugW.tPay ∈ X then -((1/2 : ℚ) * (C ()).w .a * x) else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .a * y else 0) := by
  rw [paySum_eq_sum_ite, mug1_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  ring

/-- The prior state with correct beliefs (`P = ν`) and arbitrary stakes (`V ≡ 0`) on `B₁`.
Source: [[decision-problems-v2]] Proposition 1 proof (the "half-true" version)
Kind: D -/
noncomputable def mugPriorNoStakes (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : State MugW ℚ :=
  State.ofConst (nuCondDistr (procQ q h0 h1) (mug1 x y) Finset.univ
    (nu_univ_pos (procQ q h0 h1) (mug1 x y))) 0

/-- **Clause 2 of Definition 11 is necessary for Proposition 1** (N−, v2 change-log 13): with
`P_{s°} = ν` but `V_{s°} ≡ 0`, the Jeffrey-conditioned state on `B₁` fails clause 2 of strict OC
at `d` (for `x ≠ 0` and `q > 0`).
Source: [[decision-problems-v2]] Proposition 1 proof ("without which the value side would be
unconstrained, so the prior-state upgrade of Definition 11 is what makes the proposition true
rather than half-true")
Kind: N− (the counter-state: correct beliefs, arbitrary stakes)
Fidelity: exact — on `B₁` rather than the mandate's `coinQuery`, whose payoffs are all `0` (there
`V ≡ 0` happens to be correct and no counter-state exists) -/
theorem mug1_prop1_clause2_necessary (x y q : ℚ) (hx : x ≠ 0) (h0 : 0 < q) (h1 : q ≤ 1) :
    (∀ X, (mugPriorNoStakes x y q h0.le h1).pr X = nu (procQ q h0.le h1) (mug1 x y) X) ∧
    ∃ h : 0 < (mugPriorNoStakes x y q h0.le h1).pr (mugObs ()),
      ¬ StrictOCAt (fun _ => jeffreyCond (mugPriorNoStakes x y q h0.le h1) (mugObs ()) h) mugObs
        (procQ q h0.le h1) (mug1 x y) () := by
  have hP : ∀ X, (mugPriorNoStakes x y q h0.le h1).pr X = nu (procQ q h0.le h1) (mug1 x y) X := by
    intro X
    simp only [mugPriorNoStakes, State.pr, State.ofConst_P, probOf_nuCondDistr, Finset.inter_univ,
      nu_univ, div_one]
  refine ⟨hP, ?_⟩
  have hO : 0 < (mugPriorNoStakes x y q h0.le h1).pr (mugObs ()) := by
    rw [hP, mug1_nu_obs]; norm_num
  refine ⟨hO, fun h => ?_⟩
  have hpos : 0 < nu (procQ q h0.le h1) (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
  have hXO : nu (procQ q h0.le h1) (mug1 x y) ({.tPay} ∩ mugObs ()) = q / 2 := by
    rw [mug1_nu]; simp [mugObs, procQ]; ring
  have hpay : 0 < (jeffreyCond (mugPriorNoStakes x y q h0.le h1) (mugObs ()) hO).pr {.tPay} := by
    rw [jeffreyCond_pr, hP, hP, hXO, mug1_nu_obs]
    positivity
  have := (h hpos).2 {.tPay} hpay (by rw [hXO]; positivity)
  rw [jeffreyCond_V, hXO, mug1_paySum] at this
  simp only [mugPriorNoStakes, State.ofConst_V, zero_mul, mugObs, Finset.mem_inter,
    Finset.mem_singleton, Finset.mem_insert, procQ, FinDistr.act2_a] at this
  simp at this
  rcases this with h1' | h2'
  · exact h0.ne' h1'
  · exact hx h2'

/-- The strict state of `procQ r` on `coinQuery` believes `a` with probability `r`.
Source: none: infrastructure (self-transparency at a recorded point)
Kind: L -/
theorem cqStrictState_pr_a (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (cqStrictState r hr0 hr1).pr (cqActEv () .a) = r := by
  have := selfTransparent_of_recordsFor_strict cqObs cqActEv (procQ r hr0 hr1) coinQuery
    (fun _ => cqStrictState r hr0 hr1) (coinQuery_recordsFor _)
    (by rw [coinQuery_nu_obs]; exact one_pos)
    (strictOCAt_calibratedState cqObs (procQ r hr0 hr1) coinQuery _ () _ rfl) .a
  simpa [procQ] using this

/-- **Strict ⟹̸ masked** (`coinQuery`): the self-certain strict state of the deterministic `δ_a`
at a recorded subtree-veridical node is strictly calibrated and not masked-calibrated — no
full-support self-model gives `P(a) = 1`.
Source: mandate T10 ("strict ⇏ masked (a self-certain strict state under deterministic `C` at a
recorded subtree-veridical node, `coinQuery`: no full-support `m` gives `P(a) = 1`)"); v2 Remark
3.7 ("at a subtree-veridical node, full support forces `P_{s_d}(a) > 0` for every action")
Kind: N+ -/
theorem coinQuery_strict_not_masked :
    StrictOCAt (fun _ => cqStrictState 1 zero_le_one le_rfl) cqObs (procQ 1 zero_le_one le_rfl)
      coinQuery () ∧
    ¬ MaskedOCAt (fun _ => cqStrictState 1 zero_le_one le_rfl) cqObs (procQ 1 zero_le_one le_rfl)
      coinQuery () := by
  refine ⟨(coinQuery_prop7_instance 1 zero_le_one le_rfl).2.2, ?_⟩
  rintro (⟨C', ⟨m, hm, rfl⟩, hpos, hcl⟩ | ⟨-, hnull⟩)
  · have h1 := hcl.1 (cqActEv () .a)
    rw [cqStrictState_pr_a, coinQuery_nu_obs, mul_one,
      nu_actEv_inter_obs_of_recordsFor cqObs cqActEv _ coinQuery (coinQuery_recordsFor _),
      coinQuery_nu_obs, mul_one, Proc.deviate_same] at h1
    have hb := hm .b
    have hsum := m.sum_one
    rw [Act2.sum_univ] at hsum
    linarith
  · have := hnull (procQ (1/2) (by norm_num) (by norm_num))
      ⟨FinDistr.act2 (1/2) (by norm_num) (by norm_num),
        fun a => by cases a <;> norm_num [FinDistr.act2_a, FinDistr.act2_b], by rw [deviate_unit]; rfl⟩
    rw [coinQuery_nu_obs] at this
    exact one_ne_zero this

/-- A sum over the leaves of the AMD as three terms. Source: none: infrastructure. Kind: L -/
theorem amd_sum (f : amd.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩ := by
  unfold amd at f ⊢
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  ring

/-- `occ(d)` on the AMD is every run. Source: none: infrastructure. Kind: L -/
theorem amd_occ : occ () amd = Finset.univ := by
  ext ℓ; unfold amd at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a <;> simp [count_decision]

/-- `𝔼[#_d 1_X]` on the AMD: the two-node leaves count twice.
Source: `zoo.md` ZO-3 ("counts `1, 2, 2`")
Kind: L -/
theorem amd_countMass (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset AmdW) :
    countMass C amd () X =
      (if AmdW.sa ∈ X then (C ()).w .a else 0) +
      (if AmdW.sba ∈ X then (C ()).w .b * (C ()).w .a * 2 else 0) +
      (if AmdW.sbb ∈ X then (C ()).w .b * (C ()).w .b * 2 else 0) := by
  have e : countMass C amd () X =
      ∑ ℓ, if world amd ℓ ∈ X then leafLaw C amd ℓ * (count () amd ℓ : ℚ) else 0 := by
    unfold countMass worldEv; rw [Finset.sum_filter]
  rw [e, amd_sum]
  simp [amd, leafLaw_decision, world_decision, count_decision]

/-- `ν` on the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset AmdW) :
    nu C amd X =
      (if AmdW.sa ∈ X then (C ()).w .a else 0) +
      (if AmdW.sba ∈ X then (C ()).w .b * (C ()).w .a else 0) +
      (if AmdW.sbb ∈ X then (C ()).w .b * (C ()).w .b else 0) := by
  rw [nu_eq_sum, amd_sum]
  simp [amd, leafLaw_decision, world_decision]

/-- The per-run state of `procQ ¼` on the AMD: `(¼, 3/16, 9/16)` over `(sa, sba, sbb)`.
Source: `zoo.md` ZO-3
Kind: D -/
noncomputable def amdPerRunState : State AmdW ℚ :=
  calibratedState (procQ (1/4) (by norm_num) (by norm_num)) amd Finset.univ
    (nu_univ_pos (procQ (1/4) (by norm_num) (by norm_num)) amd)

/-- **Per-run ⟹̸ per-occurrence under nesting** (the AMD at `q = ¼`, ZO-3's numbers): the
per-run state `(¼, 3/16, 9/16)` over `(sa, sba, sbb)` satisfies the per-run clauses at `d` (it
is the prior-calibrated state; `occ(d)` is every run) and violates the per-occurrence clause 1:
`P(sa) · 𝔼[#_d] = ¼ · 7/4 ≠ ¼ = 𝔼[#_d 1_{sa}]` (the per-occurrence state would be
`(1/7, 3/14, 9/14)`). The almost-fairness hypothesis of the chain is necessary.
Source: `cf-workflow/phase2-notes/repair/zoo.md` ZO-3 ("per-run SSC state
`(¼, 3/16, 9/16)`; per-occurrence SSC state `(1/7, 3/14, 9/14)`")
Kind: N+ -/
theorem amd_perRun_not_perOcc :
    PerRunClausesAt (fun _ => amdPerRunState) (procQ (1/4) (by norm_num) (by norm_num)) amd () ∧
    amdPerRunState.pr {.sa} = 1/4 ∧ amdPerRunState.pr {.sba} = 3/16 ∧
    amdPerRunState.pr {.sbb} = 9/16 ∧
    ¬ PerOccClausesAt (fun _ => amdPerRunState) (procQ (1/4) (by norm_num) (by norm_num)) amd () := by
  have hpr : ∀ X, amdPerRunState.pr X = nu (procQ (1/4) (by norm_num) (by norm_num)) amd X := by
    intro X
    simp only [amdPerRunState, State.pr, calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
  refine ⟨perRunClausesAt_of_priorCalibrated_of_occ_univ _ amd _ amd_occ
      (priorCalibrated_calibratedState_univ _ amd _), ?_, ?_, ?_, ?_⟩
  · rw [hpr, amd_nu]; simp [procQ]
  · rw [hpr, amd_nu]; simp [procQ]; norm_num
  · rw [hpr, amd_nu]; simp [procQ]; norm_num
  · rintro ⟨h1, -⟩
    have := h1 {.sa}
    rw [hpr, amd_nu, amd_countMass, amd_countMass] at this
    simp [procQ] at this
    norm_num at this

/-- The guarded forms of the AMD row: `μ(occ(d)) = 1 > 0` and `𝔼[#_d] = 7/4 > 0`, so the
per-run state is per-run SSC at `d` and not per-occurrence SSC at `d` (the guards are positive,
not merely the clauses; repair round 1, audit N2).
Source: `cf-workflow/phase2-notes/repair/zoo.md` ZO-3
Kind: N+ -/
theorem amd_perRunSSC_not_perOccSSC :
    PerRunSSCAt (fun _ => amdPerRunState) (procQ (1/4) (by norm_num) (by norm_num)) amd () ∧
    0 < countMass (procQ (1/4) (by norm_num) (by norm_num)) amd () Finset.univ ∧
    ¬ PerOccSSCAt (fun _ => amdPerRunState) (procQ (1/4) (by norm_num) (by norm_num)) amd () := by
  obtain ⟨hpr, -, -, -, hnot⟩ := amd_perRun_not_perOcc
  have hcount : 0 < countMass (procQ (1/4) (by norm_num) (by norm_num)) amd () Finset.univ := by
    rw [amd_countMass]; simp [procQ]; norm_num
  exact ⟨fun _ => hpr, hcount, fun h => hnot (h hcount)⟩

end witnesses

end Cleanroom.Decision.DpCalibration
