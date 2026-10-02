import Cleanroom.Decision.DpReferentsCdt.C2A
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Found.DpCoreTree.Screening

/-!
# Counterfactual calibration's dividends: FA-25′(1′), Fusco's placement, the tiling identity,
Definition 20 as `T_EDT`'s criterion, Huttegger's manifold, and the (E) identity

* **T12(a)** — FA-25′(1′): strict OC + Definition 7 recording + counterfactual calibration of the `cf`
  slot to `refR1State`, `refR2Real` (with F3′ for `C`) or `refR3` on `A_d^+` gives Definition 20's
  evidential criterion (`evidentialCriterion_of_calibrated_refR1State`, `…_refR2Real`, `…_refR3`);
  the failure under F3′ alone is `OpaqueRows.lean`'s `newcomb34_evidentialCriterion_fails_refR1State`.
* **T12(b)** — at a self-certain act the criterion is one equation (`evidentialCriterion_iff_of_deterministic`).
* **T13(i)** — the averaging identity `V_{s_d}(⊤) = ∑_a P_{s_d}(a) V_{s_d}(a)` with the
  exhaustiveness `P(⋁_a a) = 1` *derived* from recording (`tiling_identity_of_recordsFor`) and, for
  T12(d), from F3′ with disjointness (`tiling_identity_of_actRecording`); **(ii)** causal
  self-consistency (`causal_self_consistency`); **(iv)** the identity fails without exhaustiveness
  on the mugging with `O_d = ⊤` (`mug1_nonexhaustive_identity_fails`); **(v)** P12-6's definitional
  equivalence (`tEdtAt_of_tCdtAt_evidentialCriterion`, `exists_cf_of_tEdtAt`).
* **T15** — Huttegger's Eells–Jeffrey manifold: under recording for the deviations and a pre-query
  `X` at every label, `P(X ∣ a) = P(X)` at every manifold point (`screening_manifold`).
* **T17** — the non-trivial (E) identity: the strict state conditioned on an act *is* the deviation's
  strict state, under recording for `C` alone (`jeffreyCond_calibratedState_agree_deviatePure`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## T12: FA-25′(1′) and Fusco's placement -/

section fa25

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **FA-25′(1′) for R1-state**: strict OC + Definition 7 recording + `cf` calibrated to `refR1State`
on `A_d^+` ⟹ Definition 20's evidential criterion (value half).
Source: `faithful.md` FA-25′(1′); dp-cf-110; mandate T12(a)
Kind: C
Fidelity: exact (value half)
Hyps: (a) `RecordsFor`, (a) `0 < ν_C(O_d)`, (a) strict OC, (a) `CfCalibratedAt cf d refR1State (· ∈ A_d^+)` -/
theorem evidentialCriterion_of_calibrated_refR1State {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) (cf : Cf ι acts K)
    (hcf : CfCalibratedAt cf d (refR1State obs C B d) (· ∈ APlus s actEv d)) :
    EvidentialCriterionAt s actEv cf d := by
  intro a ha
  rw [hcf a ha, (referents_agree_of_recordsFor s obs actEv C B h hpos hs ha).1]

/-- **FA-25′(1′) for R3**. Source: `faithful.md` FA-25′(1′); mandate T12(a). Kind: C
Fidelity: exact (value half)
Hyps: (a) as above with `refR3` -/
theorem evidentialCriterion_of_calibrated_refR3 {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) (cf : Cf ι acts K)
    (hcf : CfCalibratedAt cf d (refR3 obs actEv C B d) (· ∈ APlus s actEv d)) :
    EvidentialCriterionAt s actEv cf d := by
  intro a ha
  rw [hcf a ha, (referents_agree_of_recordsFor s obs actEv C B h hpos hs ha).2]

/-- **FA-25′(1′) for R2-real** (with F3′ for `C` and disjointness, which the forcing referent
needs). Source: `faithful.md` FA-25′(1′); mandate T12(a). Kind: C
Fidelity: exact (value half)
Hyps: (a) `ActRecording`, (a) disjointness, (a) `0 < ν_C(O_d)`, (a) strict OC,
(a) `CfCalibratedAt cf d refR2Real (· ∈ A_d^+)` -/
theorem evidentialCriterion_of_calibrated_refR2Real {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    (cf : Cf ι acts K)
    (hcf : CfCalibratedAt cf d (refR2Real actEv C B d) (· ∈ APlus s actEv d)) :
    EvidentialCriterionAt s actEv cf d := by
  intro a ha
  rw [hcf a ha, evStrict_eq_refR2Real_of_APlus s obs actEv C B h hdisj hpos hs ha]

/-- **Fusco's placement / "agents WILL know"**: at a deterministic recorded strictly calibrated point
`A_d^+ = {a*}`, so Definition 20's value half is the single equation `cf d a* = V_{s_d}(a*)` — the
criterion's content there, obtained from calibration by FA-25′(1′)'s route, never from success.
Source: dp-sl-068 (Fusco/TFT); dp-sl-2-040 ("agents WILL know", first half); mandate T12(b)(c)
Kind: L
Fidelity: exact -/
theorem evidentialCriterion_iff_of_deterministic {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀) (h : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) (cf : Cf ι acts K) :
    EvidentialCriterionAt s actEv cf d ↔ cf d a₀ = evStrict s actEv d a₀ := by
  unfold EvidentialCriterionAt
  rw [aPlus_eq_singleton_of_deterministic obs actEv C B s a₀ hC h hpos hs]
  simp

end fa25

/-! ## T13: the tiling identity and Definition 20 as `T_EDT`'s criterion -/

section tiling

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- A null event carries no payoff mass. Source: none: infrastructure. Kind: L -/
theorem paySum_eq_zero_of_nu_eq_zero {X : Finset Ω} (h : nu C B X = 0) : paySum C B X = 0 := by
  rw [nu_eq_sum] at h
  rw [paySum_eq_sum_ite]
  apply Finset.sum_eq_zero
  intro ℓ _
  split_ifs with hℓ
  · have hz : leafLaw C B ℓ = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ' _ => by
        split_ifs <;> [exact leafLaw_nonneg C B ℓ'; exact le_rfl])).mp h ℓ (Finset.mem_univ _)
      simpa [hℓ] using this
    rw [hz, zero_mul]
  · rfl

/-- The edge partition at a node: passing `q` is taking exactly one of its edges.
Source: none: infrastructure. Kind: L -/
theorem ite_isSome_eq_sum_edge (q : B.DecNode) (ℓ : B.Leaves) (f : K) :
    (if (edgeOf B q ℓ).isSome then f else 0) =
      ∑ b, if edgeOf B q ℓ = some b then f else 0 :=
  ite_eq_sum_of_unique Finset.univ _ _ f
    (fun h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      exact ⟨b, Finset.mem_univ _, hb⟩)
    (fun b _ hb => by rw [hb]; rfl)
    (fun b₁ _ b₂ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂))

/-- **The act partition of `O_d` under F3′ and disjointness**: `paySum_C(O_d) = ∑_b paySum_C(b ∧ O_d)`.
Source: [[decision-problems-v2]] Definition 7; mandate T13(i), T12(d)
Kind: P
Fidelity: exact
Hyps: (a) `ActRecording`, (a) `ActEvDisjoint` -/
theorem paySum_obs_eq_sum_actEv_of_actRecording {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) :
    paySum C B (obs d) = ∑ b, paySum C B (actEv d b ∩ obs d) := by
  have hL : paySum C B (obs d) =
      ∑ ℓ, if world B ℓ ∈ obs d then leafLaw C B ℓ * payoff B ℓ else 0 := paySum_eq_sum_ite C B _
  have hR : ∀ b, paySum C B (actEv d b ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d b ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * payoff B ℓ else 0 := by
    intro b
    rw [paySum_eq_sum_ite]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  simp only [hR]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [ite_obs_eq_sum_realFiber obs actEv C B h ℓ (payoff B ℓ),
    Finset.sum_congr rfl (fun b _ => ite_actEv_obs_eq_sum_realFiber obs actEv C B h hdisj b ℓ
      (payoff B ℓ)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpt, -⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  simp only [edgeS_eq_some_iff]
  exact ite_isSome_eq_sum_edge B q ℓ _

/-- The averaging identity from strict calibration and an act partition: the abstract core of
T13(i), with `P(⋁_a a) = 1` in the form `∑_b ν(b ∧ O_d) = ν(O_d)` and
`∑_b paySum(b ∧ O_d) = paySum(O_d)`.
Source: `sl-workflow/notes/lean/P08-tiling-identity.lean` (re-founded over the tree); P08-7′; mandate T13(i)
Kind: P -/
theorem tiling_identity_of_partition {d : ι} (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d)
    (hν : nu C B (obs d) = ∑ b, nu C B (actEv d b ∩ obs d))
    (hp : paySum C B (obs d) = ∑ b, paySum C B (actEv d b ∩ obs d)) :
    (s d).V Finset.univ = ∑ a, (s d).pr (actEv d a) * (s d).V (actEv d a) := by
  obtain ⟨h1, h2⟩ := hs hpos
  have hPtop : (s d).pr Finset.univ = 1 := by
    have := h1 Finset.univ
    rw [Finset.univ_inter] at this
    exact mul_right_cancel₀ hpos.ne' (by rw [this, one_mul])
  have hVtop : (s d).V Finset.univ * nu C B (obs d) = paySum C B (obs d) := by
    have := h2 Finset.univ (by rw [hPtop]; exact one_pos) (by rwa [Finset.univ_inter])
    rwa [Finset.univ_inter] at this
  have hterm : ∀ a, (s d).pr (actEv d a) * (s d).V (actEv d a) * nu C B (obs d) =
      paySum C B (actEv d a ∩ obs d) := by
    intro a
    have hPa := h1 (actEv d a)
    rcases (show 0 ≤ (s d).pr (actEv d a) from probOf_nonneg _ _).lt_or_eq with hP | hP
    · have hνa : 0 < nu C B (actEv d a ∩ obs d) := by rw [← hPa]; exact mul_pos hP hpos
      have := h2 (actEv d a) hP hνa
      calc (s d).pr (actEv d a) * (s d).V (actEv d a) * nu C B (obs d)
          = (s d).V (actEv d a) * ((s d).pr (actEv d a) * nu C B (obs d)) := by ring
        _ = (s d).V (actEv d a) * nu C B (actEv d a ∩ obs d) := by rw [hPa]
        _ = paySum C B (actEv d a ∩ obs d) := this
    · have hνa : nu C B (actEv d a ∩ obs d) = 0 := by rw [← hPa, ← hP, zero_mul]
      rw [← hP, paySum_eq_zero_of_nu_eq_zero C B hνa, zero_mul, zero_mul]
  apply mul_right_cancel₀ hpos.ne'
  rw [hVtop, hp, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => (hterm a).symm

/-- **T13(i), the tiling identity under Definition 7 recording**: `V_{s_d}(⊤) = ∑_a P_{s_d}(a)
V_{s_d}(a)` at a recorded strictly calibrated point — the exhaustiveness `P_{s_d}(⋁_a a) = 1` is
recording's dividend (clauses 3–4), not the averaging axiom's.
Source: `repair/P08.md` P08-7′ (LB-4: "the bare identity at any queried `d` … needs
`P_{s_d}(⋁ A_d) = 1`"); `P08-tiling-identity.lean`; dp-sl-048; mandate T13(i)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsFor`, (a) `0 < ν_C(O_d)`, (a) strict OC -/
theorem tiling_identity_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) :
    (s d).V Finset.univ = ∑ a, (s d).pr (actEv d a) * (s d).V (actEv d a) :=
  tiling_identity_of_partition s obs actEv C B hpos hs (nu_obs_eq_sum_actEv obs actEv C B h)
    (paySum_obs_eq_sum_actEv obs actEv C B h)

/-- **T12(d) / T13(i) under F3′**: the tiling identity with exhaustiveness derived from F3′ and
disjointness (C2-1 gives `∑_a P_{s_d}(a) = ∑_a C(d)(a) = 1`) — the (b)/(c) → (a) conversion
dp-sl-2-024 asks for.
Source: dp-sl-2-024 (P08 Open 9); mandate T12(d)
Kind: C
Fidelity: exact
Hyps: (a) `ActRecording`, (a) disjointness, (a) `0 < ν_C(O_d)`, (a) strict OC -/
theorem tiling_identity_of_actRecording {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) :
    (s d).V Finset.univ = ∑ a, (s d).pr (actEv d a) * (s d).V (actEv d a) := by
  refine tiling_identity_of_partition s obs actEv C B hpos hs ?_
    (paySum_obs_eq_sum_actEv_of_actRecording obs actEv C B h hdisj)
  rw [nu_obs_eq_realReach obs actEv C B h]
  simp only [nu_actEv_inter_obs_eq obs actEv C B h hdisj, ← Finset.sum_mul, (C d).sum_one, one_mul]

/-- **T13(ii), causal self-consistency (P08-7′)**: Definition 20's value half + `T_CDT` approval at a
recorded strictly calibrated point ⟹ `cf d a = V_{s_d}(⊤)` on `supp C(d)` (the common causal value
of the support is derived from `T_CDT`: every supported act is a maximiser).
Source: `repair/P08.md` P08-7′ ("strict OC + Definition 7 recording + Definition 20 on `A_d^+` +
`T_CDT` approval ⇒ causal self-consistency"); mandate T13(ii)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsFor`, (a) `0 < ν_C(O_d)`, (a) strict OC, (a) `EvidentialCriterionAt`, (a) `TCdtAt` -/
theorem causal_self_consistency {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) (cf : Cf ι acts K)
    (hev : EvidentialCriterionAt s actEv cf d) (hcdt : TCdtAt cf C d) :
    ∀ a, 0 < (C d).w a → cf d a = (s d).V Finset.univ := by
  intro a ha
  have hst := selfTransparent_of_recordsFor_strict obs actEv C B s h hpos hs
  have hmem : ∀ b, 0 < (C d).w b → b ∈ APlus s actEv d := fun b hb => by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hst b]; exact hb
  have hconst : ∀ b, 0 < (C d).w b → cf d b = cf d a :=
    fun b hb => le_antisymm (hcdt a ha b) (hcdt b hb a)
  rw [tiling_identity_of_recordsFor s obs actEv C B h hpos hs]
  have : ∀ b, (s d).pr (actEv d b) * (s d).V (actEv d b) = (C d).w b * cf d a := by
    intro b
    rw [hst b]
    rcases ((C d).nonneg b).lt_or_eq with hb | hb
    · rw [← hconst b hb, hev b (hmem b hb)]; rfl
    · rw [← hb, zero_mul, zero_mul]
  simp only [this, ← Finset.sum_mul, (C d).sum_one, one_mul]

/-- **T13(v), P12-6 (→)**: `T_CDT` approval with an evidentially calibrated `cf` (Definition 20's value
half) at a point where the support is subjectively possible gives `T_EDT` approval.
Source: `repair/P12.md` P12-6; mandate T13(v)
Kind: C
Fidelity: exact
Hyps: (a) `TCdtAt`, (a) `EvidentialCriterionAt`, (a) `supp C(d) ⊆ A_d^+` (derived from recording
or F3′ + strict OC by C2-1) -/
theorem tEdtAt_of_tCdtAt_evidentialCriterion {d : ι} (cf : Cf ι acts K) (hcdt : TCdtAt cf C d)
    (hev : EvidentialCriterionAt s actEv cf d) (hsupp : ∀ a, 0 < (C d).w a → a ∈ APlus s actEv d) :
    TEdtAt s actEv C d := by
  intro _ a ha
  rw [mem_argmaxPlus]
  refine ⟨hsupp a ha, fun b hb => ?_⟩
  show evStrict s actEv d b ≤ evStrict s actEv d a
  rw [← hev a (hsupp a ha), ← hev b hb]
  exact hcdt a ha b

/-- **T13(v), P12-6 (←)**: every `T_EDT`-approved procedure with a supported act is `T_CDT`-approved
for some evidentially calibrated `cf` (`V_{s_d}` on `A_d^+`, a supported act's value off it).
Source: `repair/P12.md` P12-6 ("conversely any `T_EDT`-approved `C` is `T_CDT`-approved for
`cf := evStrict` on `A_d^+`, `≤ max` off it"); mandate T13(v)
Kind: C
Fidelity: exact
Hyps: (a) `TEdtAt`, (a) a supported act, (a) `supp C(d) ⊆ A_d^+` -/
theorem exists_cf_of_tEdtAt {d : ι} (hedt : TEdtAt s actEv C d) (a₀ : acts d)
    (ha₀ : 0 < (C d).w a₀) (hsupp : ∀ a, 0 < (C d).w a → a ∈ APlus s actEv d) :
    ∃ cf : Cf ι acts K, TCdtAt cf C d ∧ EvidentialCriterionAt s actEv cf d := by
  classical
  refine ⟨fun d' b => if b ∈ APlus s actEv d' then evStrict s actEv d' b else
      if h : (APlus s actEv d').Nonempty then (APlus s actEv d').inf' h (evStrict s actEv d')
      else 0, ?_, ?_⟩
  · intro a ha b
    have hne : (APlus s actEv d).Nonempty := ⟨a₀, hsupp a₀ ha₀⟩
    have hamax := (mem_argmaxPlus s actEv d a).mp (hedt hne a ha)
    simp only [if_pos (hsupp a ha)]
    by_cases hb : b ∈ APlus s actEv d
    · rw [if_pos hb]; exact hamax.2 b hb
    · rw [if_neg hb, dif_pos hne]
      exact Finset.inf'_le _ (hsupp a ha)
  · intro a ha
    simp only [if_pos ha]

end tiling

/-! ## T13(iv): the identity fails without exhaustiveness -/

section mugging

/-- The mugging `B₁(1, 3)` with `O_d = ⊤`. Source: `repair/P08.md` LB-4 (§C′). Kind: D -/
def mug13 : Tree MugW Unit (fun _ => Act2) ℚ := mug1 1 3

/-- **T13(iv), the identity needs exhaustiveness**: on the mugging `B₁(1, 3)` with `O_d = ⊤` (not
recorded: the `H`-branch worlds lie in no action event), the calibrated state has
`P(pay) + P(refuse) = 1/2` and `V(⊤) − ∑_a P(a) V(a) = 3q/2 ≠ 0` for `0 < q < 1`.
Source: `repair/P08.md` LB-4 (§C′: "`P(⋁ A_d) = 1/2`, `V(⊤) = q(y−x)/2`, `∑ P(a)V(a) = −qx/2`,
difference `qy/2`"); mandate T13(iv)
Kind: N+ -/
theorem mug1_nonexhaustive_identity_fails (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    let s : State MugW ℚ :=
      calibratedState (procQ q h0.le h1.le) mug13 Finset.univ (nu_univ_pos _ _)
    s.pr (mugActEv () .a) + s.pr (mugActEv () .b) = 1/2 ∧
    s.V Finset.univ - (s.pr (mugActEv () .a) * s.V (mugActEv () .a) +
      s.pr (mugActEv () .b) * s.V (mugActEv () .b)) = 3 * q / 2 := by
  intro s
  have hb : (procQ q h0.le h1.le ()).w .b = 1 - q := by simp [procQ]
  have hpay : ∀ X, paySum (procQ q h0.le h1.le) mug13 X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * q * (-1) else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * q * 3 else 0) := by
    intro X
    rw [paySum_eq_sum_ite]
    unfold mug13
    rw [mug1_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin,
      procQ]
    ring
  simp only [s, calibratedState_pr, calibratedState_V, Finset.inter_univ, Finset.univ_inter,
    nu_univ, div_one, hpay]
  unfold mug13
  simp only [mug1_nu, mugActEv, hb, procQ, FinDistr.act2_a]
  simp
  have hq : q ≠ 0 := h0.ne'
  have hq' : 1 - q ≠ 0 := by linarith
  constructor
  · ring
  · field_simp
    ring

end mugging

/-! ## T15: Huttegger's Eells–Jeffrey manifold -/

section huttegger

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- **Huttegger's manifold**: under Definition 7 recording for every deviation `C[d ↦ m]` and a
pre-query event `X` at every label, `P(X ∣ a) = P(X)` at every manifold point — the screening
identity `ν(X ∧ a ∧ O_d) · ν(O_d) = ν(X ∧ O_d) · ν(a ∧ O_d)` for every label and act. Fails under the
shared seed (`OpaqueRows.lean`'s `newcomb34_seed_screening_fails`).
Source: dp-sl-2-047 (Huttegger's Eells–Jeffrey manifold); `dp-core-tree`'s Lemma 3′
(`screening_recorded`); mandate T15
Kind: C
Fidelity: exact (multiplicative form)
Hyps: (a) `RecordsForDeviations`, (a) `PreQuery` at every label -/
theorem screening_manifold {d : ι} (hdev : RecordsForDeviations obs actEv C B d) {X : Finset Ω}
    (hX : ∀ m, PreQuery obs (C.deviate d m) B d X) (m : FinDistr K (acts d)) (a : acts d) :
    nu (C.deviate d m) B (X ∩ actEv d a ∩ obs d) * nu (C.deviate d m) B (obs d) =
      nu (C.deviate d m) B (X ∩ obs d) * nu (C.deviate d m) B (actEv d a ∩ obs d) :=
  screening_recorded obs actEv (hdev m) (hX m) a

end huttegger

/-! ## T17: the (E) identity, non-trivial form -/

section eIdentity

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- The deviation-conditioning identity with an event inserted: under Definition 7 recording for `C`
and `C(d)(a) > 0`, `ν_{C[d↦a]}(X ∧ O_d) · C(d)(a) = ν_C(X ∧ a ∧ O_d)`.
Source: `faithful.md` FA-20′(ii); mandate T17
Kind: P -/
theorem nu_deviatePure_inter_obs_mul {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) (X : Finset Ω) :
    nu (C.deviatePure d a) B (X ∩ obs d) * (C d).w a = nu C B (X ∩ actEv d a ∩ obs d) := by
  rw [nu_eq_sum, nu_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have := ite_deviatePure_obs_mul obs actEv C B h ha ℓ (if world B ℓ ∈ X then 1 else 0)
  by_cases hX : world B ℓ ∈ X
  · simp [hX] at this
    simpa [hX, Finset.mem_inter] using this
  · simp [hX, Finset.mem_inter]

/-- The payoff version. Source: `faithful.md` FA-20′(ii); mandate T17. Kind: P -/
theorem paySum_deviatePure_inter_obs_mul {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) (X : Finset Ω) :
    paySum (C.deviatePure d a) B (X ∩ obs d) * (C d).w a = paySum C B (X ∩ actEv d a ∩ obs d) := by
  rw [paySum_eq_sum_ite, paySum_eq_sum_ite, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have := ite_deviatePure_obs_mul obs actEv C B h ha ℓ
    (if world B ℓ ∈ X then payoff B ℓ else 0)
  by_cases hX : world B ℓ ∈ X
  · simp [hX] at this
    simpa [hX, Finset.mem_inter] using this
  · simp [hX, Finset.mem_inter]

/-- Under Definition 7 recording for `C` and `C(d)(a) > 0`, the deviation `C[d ↦ a]` realizes `O_d`
with the same mass as `C`. Source: `faithful.md` FA-20′(ii); mandate T17. Kind: L -/
theorem nu_deviatePure_obs_eq_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) : nu (C.deviatePure d a) B (obs d) = nu C B (obs d) := by
  have := nu_deviatePure_obs_mul obs actEv C B h ha
  rw [nu_actEv_inter_obs_of_recordsFor obs actEv C B h a] at this
  exact mul_right_cancel₀ ha.ne' (by rw [this]; ring)

/-- **The (E) identity, non-trivial form**: under Definition 7 recording for `C` and `C(d)(a) > 0`,
the strict state of `C` Jeffrey-conditioned on the act `a` agrees (modulo junk `V`) with the strict
state of the deviation `C[d ↦ a]` — the conditioned state *is* the deviation's state. The trivial
"both sides one sum" form is dropped as a squeeze (dp-sl-2-056).
Source: dp-sl-2-056 ((E) identity); dp-sl-2-054; mandate T17
Kind: C
Fidelity: exact (`State.Agree`)
Hyps: (a) `RecordsFor`, (a) `0 < ν_C(O_d)`, (a) `0 < C(d)(a)` -/
theorem jeffreyCond_calibratedState_agree_deviatePure {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) {a : acts d} (ha : 0 < (C d).w a) :
    State.Agree
      (jeffreyCond (calibratedState C B (obs d) hpos) (actEv d a) (by
        rw [calibratedState_pr, nu_actEv_inter_obs_of_recordsFor obs actEv C B h a]
        exact div_pos (mul_pos ha hpos) hpos))
      (calibratedState (C.deviatePure d a) B (obs d)
        (by rw [nu_deviatePure_obs_eq_of_recordsFor obs actEv C B h ha]; exact hpos)) := by
  have hνa : nu C B (actEv d a ∩ obs d) = (C d).w a * nu C B (obs d) :=
    nu_actEv_inter_obs_of_recordsFor obs actEv C B h a
  have hν' : ∀ X, nu (C.deviatePure d a) B (X ∩ obs d) =
      nu C B (X ∩ actEv d a ∩ obs d) / (C d).w a := fun X => by
    rw [← nu_deviatePure_inter_obs_mul obs actEv C B h ha X, mul_div_cancel_right₀ _ ha.ne']
  have hp' : ∀ X, paySum (C.deviatePure d a) B (X ∩ obs d) =
      paySum C B (X ∩ actEv d a ∩ obs d) / (C d).w a := fun X => by
    rw [← paySum_deviatePure_inter_obs_mul obs actEv C B h ha X, mul_div_cancel_right₀ _ ha.ne']
  have hνO : nu (C.deviatePure d a) B (obs d) = nu C B (obs d) :=
    nu_deviatePure_obs_eq_of_recordsFor obs actEv C B h ha
  have hsing : ∀ ω, ω ∈ obs d →
      nu (C.deviatePure d a) B {ω} = nu C B ({ω} ∩ actEv d a ∩ obs d) / (C d).w a := by
    intro ω hω
    have := hν' {ω}
    rwa [Finset.singleton_inter_of_mem hω] at this
  constructor
  · apply FinDistr.ext'
    intro ω
    show (if ω ∈ actEv d a then (calibratedState C B (obs d) hpos).P.w ω /
        (calibratedState C B (obs d) hpos).pr (actEv d a) else 0) =
      (if ω ∈ obs d then nu (C.deviatePure d a) B {ω} / nu (C.deviatePure d a) B (obs d) else 0)
    have hL : (calibratedState C B (obs d) hpos).P.w ω =
        if ω ∈ obs d then nu C B {ω} / nu C B (obs d) else 0 := rfl
    rw [hL, calibratedState_pr, hνa, hνO, mul_div_assoc, div_self hpos.ne', mul_one]
    by_cases hω : ω ∈ obs d
    · simp only [if_pos hω, hsing ω hω]
      by_cases hωa : ω ∈ actEv d a
      · rw [if_pos hωa, Finset.singleton_inter_of_mem hωa, Finset.singleton_inter_of_mem hω]
        field_simp
      · rw [if_neg hωa, Finset.singleton_inter_of_notMem hωa, Finset.empty_inter, nu_empty,
          zero_div, zero_div]
    · simp only [if_neg hω]
      by_cases hωa : ω ∈ actEv d a
      · rw [if_pos hωa, zero_div]
      · rw [if_neg hωa]
  · intro X _
    show (calibratedState C B (obs d) hpos).V (X ∩ actEv d a) = _
    rw [calibratedState_V, calibratedState_V, hν', hp', div_div_div_cancel_right₀ ha.ne']

end eIdentity

end Cleanroom.Decision.DpReferentsCdt
