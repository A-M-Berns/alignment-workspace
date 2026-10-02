import Cleanroom.Decision.DpReferentsCdt.Defs
import Cleanroom.Decision.DpLocalOpt.Cells

/-!
# The structure of `O_d`-runs under F3′: the factorisation lemmas C2-L1/C2-L2 and C2-1

Under veridical act-recording (`ActRecording`, F3′) every positive `O_d`-run passes exactly one
node-action-veridical `d`-node, and with Definition 3's disjointness of the action events
(`ActEvDisjoint`) the runs with `λ ⊨ a ∧ O_d` are exactly the runs taking the `a`-edge at that
node. This file proves the pointwise identities and their consequences:

* `ite_obs_eq_sum_realFiber`, `ite_actEv_obs_eq_sum_realFiber` — the indicator of `O_d`
  (resp. `a ∧ O_d`) at a leaf is the sum over the real fiber of "the path passes `q`" (resp.
  "takes the `a`-edge at `q`");
* `nu_obs_eq_realReach` — `ν_C(O_d) = ∑_{q ∈ realFiber} R_q(C)`;
* `nu_actEv_inter_obs_eq`, `paySum_actEv_inter_obs_eq` — **Lemma C2-L2**:
  `ν_C(a ∧ O_d) = C(d)(a) · ∑_q R_q(C)` and `∑_{λ ⊨ a ∧ O_d} μ_C r = C(d)(a) · ∑_q R_q G_q(C, a)`,
  by `dp-core-tree`'s `mass_edge` and `dp-local-opt`'s `condDraw_eq_forced` at each node
  (**Lemma C2-L1**: Definition 6's independent draw at a node-action-veridical node);
* `condExp_actEv_inter_obs_eq_refR2Real` — the label factor cancels: `𝔼_C[r ∣ a ∧ O_d] = refR2Real a`
  for `C(d)(a) > 0`;
* `selfTransparent_of_actRecording_strict` — **C2-1**: strict calibration at an F3′ point gives
  `P_{s_d}(a) = C(d)(a)`, simulations upstream notwithstanding;
* the deviation-conditioning identities under Definition 7 recording
  (`nu_deviatePure_obs_mul`, `paySum_deviatePure_obs_mul`, `refR1State_eq_condExp_of_recordsFor`)
  and the act partition of `O_d` (`nu_obs_eq_sum_actEv`, `paySum_obs_eq_sum_actEv`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## A generic indicator identity -/

/-- An indicator equals the sum over a finite set of indicators of a predicate that has exactly
one witness in the set when the indicator is on, and none when it is off.
Source: none: infrastructure
Kind: L -/
theorem ite_eq_sum_of_unique {α M : Type} [AddCommMonoid M] (S : Finset α) (Q : α → Prop)
    [DecidablePred Q] (P : Prop) [Decidable P] (f : M)
    (hex : P → ∃ q ∈ S, Q q) (hQ : ∀ q ∈ S, Q q → P)
    (huniq : ∀ q₁ ∈ S, ∀ q₂ ∈ S, Q q₁ → Q q₂ → q₁ = q₂) :
    (if P then f else 0) = ∑ q ∈ S, if Q q then f else 0 := by
  by_cases hP : P
  · obtain ⟨q₀, hq₀, hQ₀⟩ := hex hP
    rw [if_pos hP, Finset.sum_eq_single q₀]
    · rw [if_pos hQ₀]
    · intro q hq hne
      rw [if_neg]
      intro hQq
      exact hne (huniq q hq q₀ hq₀ hQq hQ₀)
    · intro h; exact absurd hq₀ h
  · rw [if_neg hP]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    intro hQq
    exact hP (hQ q hq hQq)

/-! ## Positive leaves and their draws -/

section draws

variable (C : Proc ι acts K)

/-- Every draw on a positive-mass path has positive weight.
Source: none: infrastructure
Kind: L -/
theorem w_pos_of_leafLaw_pos :
    (B : Tree Ω ι acts K) → ∀ (ℓ : B.Leaves) {d : ι} {b : acts d},
      0 < leafLaw C B ℓ → (⟨d, b⟩ : Σ d, acts d) ∈ draws B ℓ → 0 < (C d).w b
  | leaf _ _, _, _, _, _, hmem => by simp at hmem
  | chance _ β child, ⟨i, ℓ⟩, d, b, hpos, hmem => by
      simp only [leafLaw_chance] at hpos
      simp only [draws_chance] at hmem
      have hrest : 0 < leafLaw C (child i) ℓ := by
        rcases (leafLaw_nonneg C (child i) ℓ).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      exact w_pos_of_leafLaw_pos (child i) ℓ hrest hmem
  | decision d' child, ⟨c, ℓ⟩, d, b, hpos, hmem => by
      simp only [leafLaw_decision] at hpos
      simp only [draws_decision, List.mem_cons] at hmem
      rcases hmem with h | h
      · obtain ⟨hd, hb⟩ := Sigma.mk.inj_iff.mp h
        subst hd
        rw [eq_of_heq hb]
        rcases ((C d).nonneg c).lt_or_eq with h' | h'
        · exact h'
        · rw [← h', zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · have hrest : 0 < leafLaw C (child c) ℓ := by
          rcases (leafLaw_nonneg C (child c) ℓ).lt_or_eq with h' | h'
          · exact h'
          · rw [← h', mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        exact w_pos_of_leafLaw_pos (child c) ℓ hrest h

/-- A leaf of mass zero under `C` has mass zero under `C[d ↦ a]` when `C(d)(a) > 0` (the vanishing
factor is a chance weight, a draw at another point, or a `d`-draw of an act other than `a`).
Source: mandate T5(iv) ("the `C[d ↦ a]`-positive `O_d`-runs are among `C`'s")
Kind: L -/
theorem leafLaw_deviatePure_eq_zero {d : ι} {a : acts d} (ha : 0 < (C d).w a) :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLaw C B ℓ = 0 → leafLaw (C.deviatePure d a) B ℓ = 0
  | leaf _ _, _, h => by simp at h
  | chance _ β child, ⟨i, ℓ⟩, h => by
      simp only [leafLaw_chance] at h ⊢
      rcases mul_eq_zero.mp h with h | h
      · rw [h, zero_mul]
      · rw [leafLaw_deviatePure_eq_zero ha (child i) ℓ h, mul_zero]
  | decision d' child, ⟨b, ℓ⟩, h => by
      simp only [leafLaw_decision] at h ⊢
      rcases mul_eq_zero.mp h with h | h
      · by_cases hd : d' = d
        · subst hd
          have hba : b ≠ a := by
            rintro rfl; rw [h] at ha; exact lt_irrefl 0 ha
          simp [Proc.deviatePure, hba]
        · rw [Proc.deviatePure, Proc.deviate_ne C _ hd, h, zero_mul]
      · rw [leafLaw_deviatePure_eq_zero ha (child b) ℓ h, mul_zero]

end draws

/-! ## The structure of positive `O_d`-runs under F3′ -/

section runStructure

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- (O1) Under F3′ a positive `O_d`-leaf passes a real-fiber node.
Source: `faithful.md` Definition F3′ clause (ii)
Kind: L -/
theorem exists_realFiber_of_obs {d : ι} (h : ActRecording obs actEv C B d) {ℓ : B.Leaves}
    (hpos : 0 < leafLaw C B ℓ) (hobs : world B ℓ ∈ obs d) :
    ∃ q ∈ realFiber actEv B d, (edgeOf B q ℓ).isSome := by
  obtain ⟨q, ⟨hq, hnav⟩, -⟩ := h.2 ℓ hpos hobs
  rw [mem_dNodesOn] at hq
  exact ⟨q, (mem_realFiber actEv B d q).mpr ⟨hq.1, hnav⟩, hq.2⟩

/-- (O2) Under F3′ every leaf below a real-fiber node has its world in `O_d` (clause (i):
node-action-veridical nodes are subtree-veridical).
Source: `faithful.md` Definition F3′ clause (i)
Kind: L -/
theorem obs_of_mem_realFiber {d : ι} (h : ActRecording obs actEv C B d) {q : B.DecNode}
    (hq : q ∈ realFiber actEv B d) {ℓ : B.Leaves} (he : (edgeOf B q ℓ).isSome) :
    world B ℓ ∈ obs d := by
  obtain ⟨hpt, hnav⟩ := (mem_realFiber actEv B d q).mp hq
  have := h.1 q hpt hnav ℓ ((mem_leavesBelow B q ℓ).mpr he)
  rwa [hpt] at this

/-- (O3) Under F3′ a positive leaf passes at most one real-fiber node.
Source: `faithful.md` Definition F3′ clause (ii) ("exactly one")
Kind: L -/
theorem realFiber_unique {d : ι} (h : ActRecording obs actEv C B d) {ℓ : B.Leaves}
    (hpos : 0 < leafLaw C B ℓ) {q₁ q₂ : B.DecNode} (h₁ : q₁ ∈ realFiber actEv B d)
    (h₂ : q₂ ∈ realFiber actEv B d) (e₁ : (edgeOf B q₁ ℓ).isSome)
    (e₂ : (edgeOf B q₂ ℓ).isSome) : q₁ = q₂ := by
  have hobs := obs_of_mem_realFiber obs actEv C B h h₁ e₁
  obtain ⟨q, -, huniq⟩ := h.2 ℓ hpos hobs
  have m₁ := (mem_realFiber actEv B d q₁).mp h₁
  have m₂ := (mem_realFiber actEv B d q₂).mp h₂
  have u₁ := huniq q₁ ⟨(mem_dNodesOn B d ℓ q₁).mpr ⟨m₁.1, e₁⟩, m₁.2⟩
  have u₂ := huniq q₂ ⟨(mem_dNodesOn B d ℓ q₂).mpr ⟨m₂.1, e₂⟩, m₂.2⟩
  rw [u₁, u₂]

/-- (S1) Under F3′ and disjointness, a positive leaf with `λ ⊨ a ∧ O_d` takes the `a`-edge at a
real-fiber node.
Source: `faithful.md` Definition F3′; [[decision-problems-v2]] Definition 3; mandate §7 trap 1
Kind: L -/
theorem exists_realFiber_edgeS {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) {ℓ : B.Leaves} (hpos : 0 < leafLaw C B ℓ) {a : acts d}
    (hact : world B ℓ ∈ actEv d a) (hobs : world B ℓ ∈ obs d) :
    ∃ q ∈ realFiber actEv B d, edgeS B q ℓ = some ⟨d, a⟩ := by
  obtain ⟨q, hq, he⟩ := exists_realFiber_of_obs obs actEv C B h hpos hobs
  refine ⟨q, hq, ?_⟩
  obtain ⟨hpt, hnav⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp he
  have hactb := hnav ℓ b hb
  have hab : a = b := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj a b hne) hact hactb
  subst hab
  exact (edgeS_eq_some_iff B q ℓ a).mpr hb

/-- (S2) Under F3′ a leaf taking the `a`-edge at a real-fiber node has `λ ⊨ a ∧ O_d`.
Source: `faithful.md` Definition F3′
Kind: L -/
theorem actEv_obs_of_edgeS {d : ι} (h : ActRecording obs actEv C B d) {q : B.DecNode}
    (hq : q ∈ realFiber actEv B d) {ℓ : B.Leaves} {a : acts d}
    (he : edgeS B q ℓ = some ⟨d, a⟩) :
    world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d := by
  have hobs := obs_of_mem_realFiber obs actEv C B h hq (isSome_of_edgeS B q ℓ he)
  refine ⟨?_, hobs⟩
  have hpt : pt B q = d := pt_eq_of_edgeS B q ℓ he
  obtain ⟨_, hnav⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  exact hnav ℓ a ((edgeS_eq_some_iff B q ℓ a).mp he)

/-- **The pointwise identity for the observation**: at every leaf, the `μ_C`-weighted indicator of
`λ ⊨ O_d` (times any `g`) is the sum over the real fiber of the indicator "the path passes `q`".
Source: `C2.md` Lemma C2-L2 (first identity); `faithful.md` FA-20′(i) ("the runs through
node-action-veridical `d`-nodes coincide a.s. with the `O_d`-runs")
Kind: P -/
theorem ite_obs_eq_sum_realFiber {d : ι} (h : ActRecording obs actEv C B d) (ℓ : B.Leaves)
    (g : K) :
    (if world B ℓ ∈ obs d then leafLaw C B ℓ * g else 0) =
      ∑ q ∈ realFiber actEv B d, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ * g else 0 := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · exact ite_eq_sum_of_unique _ _ _ _
      (fun hobs => exists_realFiber_of_obs obs actEv C B h hpos hobs)
      (fun q hq he => obs_of_mem_realFiber obs actEv C B h hq he)
      (fun q₁ h₁ q₂ h₂ e₁ e₂ => realFiber_unique obs actEv C B h hpos h₁ h₂ e₁ e₂)
  · rw [← hzero]; simp

/-- **The pointwise identity for an action event** (Lemma C2-L1's leaf-level content): at every
leaf, the `μ_C`-weighted indicator of `λ ⊨ a ∧ O_d` (times any `g`) is the sum over the real fiber
of the indicator "the path takes the `a`-edge at `q`". Needs Definition 3's disjointness.
Source: `C2.md` Lemma C2-L1 (factorisation), Lemma C2-L2; mandate §7 trap 1
Kind: P -/
theorem ite_actEv_obs_eq_sum_realFiber {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) (ℓ : B.Leaves) (g : K) :
    (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * g else 0) =
      ∑ q ∈ realFiber actEv B d, if edgeS B q ℓ = some ⟨d, a⟩ then leafLaw C B ℓ * g else 0 := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · exact ite_eq_sum_of_unique _ _ _ _
      (fun hc => exists_realFiber_edgeS obs actEv C B h hdisj hpos hc.1 hc.2)
      (fun q hq he => actEv_obs_of_edgeS obs actEv C B h hq he)
      (fun q₁ h₁ q₂ h₂ e₁ e₂ => realFiber_unique obs actEv C B h hpos h₁ h₂
        (isSome_of_edgeS B q₁ ℓ e₁) (isSome_of_edgeS B q₂ ℓ e₂))
  · rw [← hzero]; simp

end runStructure

/-! ## Lemma C2-L2: the sums -/

section sums

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The mass of the leaves below `q` is `R_q(C)`, as an indicator sum.
Source: [[decision-problems-v2]] §8 (`R_q(C) := μ_{B,C}(reach q)`)
Kind: L -/
theorem sum_ite_isSome_eq_reach (q : B.DecNode) :
    (∑ ℓ, if (edgeOf B q ℓ).isSome then leafLaw C B ℓ else 0) = reach C B q := by
  rw [reach_eq_mass_leavesBelow, leavesBelow, mass_filter]

/-- **`ν_C(O_d) = ∑_{q ∈ realFiber} R_q(C)`** under F3′ for `C`.
Source: `faithful.md` FA-20′(i); `C2.md` Lemma C2-L2
Kind: P
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C B d` -/
theorem nu_obs_eq_realReach {d : ι} (h : ActRecording obs actEv C B d) :
    nu C B (obs d) = realReach actEv C B d := by
  have hL : nu C B (obs d) = ∑ ℓ, if world B ℓ ∈ obs d then leafLaw C B ℓ * 1 else 0 := by
    rw [nu_eq_sum]; simp
  rw [hL, Finset.sum_congr rfl (fun ℓ _ => ite_obs_eq_sum_realFiber obs actEv C B h ℓ 1),
    Finset.sum_comm, realReach]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [mul_one]
  exact sum_ite_isSome_eq_reach C B q

/-- **Lemma C2-L2, first identity: `ν_C(a ∧ O_d) = C(d)(a) · ∑_{q ∈ realFiber} R_q(C)`** under F3′
for `C` and Definition 3's disjointness — the draw at the real node is the only act-specific
factor, whatever `d`-nodes lie upstream.
Source: `C2.md` line 48 (Lemma C2-L2, `ν(a ∣ O_d) = C(d)(a)`); mandate T3
Kind: P
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C B d`, (a) `ActEvDisjoint actEv d` (Definition 3) -/
theorem nu_actEv_inter_obs_eq {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) :
    nu C B (actEv d a ∩ obs d) = (C d).w a * realReach actEv C B d := by
  have hL : nu C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * 1 else 0 := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ite_actEv_obs_eq_sum_realFiber obs actEv C B h hdisj a ℓ 1),
    Finset.sum_comm, realReach, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpt, -⟩ := (mem_realFiber actEv B d q).mp hq
  simp only [mul_one]
  rw [mass_edgeS C B q hpt a, sum_ite_isSome_eq_reach C B q]

/-- **Lemma C2-L2, second identity: `∑_{λ ⊨ a ∧ O_d} μ_C(ℓ) r(ℓ) = C(d)(a) · ∑_{q ∈ realFiber}
R_q(C) G_q(C, a)`** (with `R_q G_q` rendered as `forcedBelow`): conditioning on `a ∧ O_d` is
forcing `a` at the node reached, by Definition 6's independent draw (`condDraw_eq_forced`).
Source: `C2.md` line 48 (Lemma C2-L2, `𝔼_μ[r ∣ a ∧ O_d] = v_d(a; C)`); `faithful.md` FA-20′(i)
Kind: P
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C B d`, (a) `ActEvDisjoint actEv d` -/
theorem paySum_actEv_inter_obs_eq {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) :
    paySum C B (actEv d a ∩ obs d) = (C d).w a * realForced actEv C B d a := by
  have hL : paySum C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d
        then leafLaw C B ℓ * payoff B ℓ else 0 := by
    rw [paySum_eq_sum_ite]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ite_actEv_obs_eq_sum_realFiber obs actEv C B h hdisj a ℓ (payoff B ℓ)),
    Finset.sum_comm, realForced, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpt, -⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  rw [dif_pos rfl]
  simp only [edgeS_eq_some_iff]
  exact condDraw_eq_forced C B q a

/-- **The label factor cancels**: for `C(d)(a) > 0` and `ν_C(O_d) > 0` under F3′ for `C`,
`𝔼_C[r ∣ a ∧ O_d] = refR2Real a`.
Source: `C2.md` line 48 (Lemma C2-L2, "the factor `C(d)(a)` cancels")
Kind: C
Fidelity: exact
Hyps: (a) `ActRecording`, (a) disjointness, (a) `0 < C(d)(a)`, (a) `0 < ν_C(O_d)` -/
theorem condExp_actEv_inter_obs_eq_refR2Real {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) {a : acts d} (ha : 0 < (C d).w a)
    (hpos : 0 < nu C B (obs d)) :
    condExp C B (actEv d a ∩ obs d) = refR2Real actEv C B d a := by
  unfold condExp refR2Real
  rw [paySum_actEv_inter_obs_eq obs actEv C B h hdisj a,
    nu_actEv_inter_obs_eq obs actEv C B h hdisj a]
  have hR : realReach actEv C B d ≠ 0 := by
    rw [← nu_obs_eq_realReach obs actEv C B h]; exact hpos.ne'
  field_simp

/-- Positivity of `a ∧ O_d` under F3′: `0 < C(d)(a)` and `0 < ν_C(O_d)` give `0 < ν_C(a ∧ O_d)`.
Source: none: infrastructure
Kind: L -/
theorem nu_actEv_inter_obs_pos {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) {a : acts d} (ha : 0 < (C d).w a)
    (hpos : 0 < nu C B (obs d)) : 0 < nu C B (actEv d a ∩ obs d) := by
  rw [nu_actEv_inter_obs_eq obs actEv C B h hdisj a, ← nu_obs_eq_realReach obs actEv C B h]
  exact mul_pos ha hpos

/-- **C2-1, the object of self-knowledge is the mixture**: strict observation calibration at an
F3′ point (with Definition 3's disjointness and `ν_C(O_d) > 0`) gives `P_{s_d}(a) = C(d)(a)` for
every `a`, even when further `d`-nodes (a predictor's simulations) lie above the real node and move
its reach weight. Generalises `dp-calibration`'s `selfTransparent_of_recordsFor_strict` (Definition
7) to F3′; the state knows the mixture, never the draw.
Source: `C2.md` line 46 (C2-1); `sl-synthesis.md` §2.2; dp-sl-024; mandate T2
Kind: C
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C B d`, (a) `ActEvDisjoint actEv d`, (a) `0 < ν_C(O_d)`,
(a) `StrictOCAt s obs C B d` -/
theorem selfTransparent_of_actRecording_strict (s : ι → State Ω K) {d : ι}
    (h : ActRecording obs actEv C B d) (hdisj : ActEvDisjoint actEv d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) :
    SelfTransparent s actEv C d := by
  intro a
  have h1 := (hs hpos).1 (actEv d a)
  rw [nu_actEv_inter_obs_eq obs actEv C B h hdisj a, ← nu_obs_eq_realReach obs actEv C B h] at h1
  exact mul_right_cancel₀ hpos.ne' h1

/-- Under F3′ and strict calibration, `A_d^+ = supp C(d)`.
Source: `C2.md` C2-1; mandate T3 (the domain `A_d^+` of `T_EDT`)
Kind: L -/
theorem mem_APlus_iff_of_actRecording_strict (s : ι → State Ω K) {d : ι}
    (h : ActRecording obs actEv C B d) (hdisj : ActEvDisjoint actEv d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) (a : acts d) :
    a ∈ APlus s actEv d ↔ 0 < (C d).w a := by
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [selfTransparent_of_actRecording_strict obs actEv C B s h hdisj hpos hs a]

end sums

/-! ## Deviation conditioning under Definition 7 recording -/

section deviation

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The pointwise deviation-conditioning identity**: under Definition 7 recording for `C` and
`C(d)(a) > 0`, at every leaf `μ_{C[d↦a]}(ℓ) 1[λ ⊨ O_d] · C(d)(a) = μ_C(ℓ) 1[λ ⊨ a ∧ O_d]`:
deviating all instances changes nothing on `O_d`-runs but the draw at the unique `d`-node.
Source: `faithful.md` FA-20′(ii) ("deviating all instances changes nothing on `O_d`-runs but the
draw at that node"); mandate T5(ii)(iv)
Kind: P -/
theorem ite_deviatePure_obs_mul {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) (ℓ : B.Leaves) (g : K) :
    (if world B ℓ ∈ obs d then leafLaw (C.deviatePure d a) B ℓ * g else 0) * (C d).w a =
      if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * g else 0 := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨h1, hnode⟩ := h ℓ hpos hobs
      -- the unique `d`-node and its edge
      have hcard := h1
      rw [count_eq_card_dNodesOn, Finset.card_eq_one] at hcard
      obtain ⟨q, hq⟩ := hcard
      have hmem : q ∈ dNodesOn B d ℓ := by rw [hq]; exact Finset.mem_singleton_self q
      rw [mem_dNodesOn] at hmem
      obtain ⟨hpt, hsome⟩ := hmem
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨-, hactb, huniq⟩ := hnode q hpt b hb
      have hbS : edgeS B q ℓ = some ⟨pt B q, b⟩ := (edgeS_eq_some_iff B q ℓ b).mpr hb
      have hdraw : (⟨d, hpt ▸ b⟩ : Σ d, acts d) ∈ draws B ℓ := by
        rw [mem_draws_iff_exists_edgeS]
        refine ⟨q, ?_⟩
        rw [hbS]; subst hpt; rfl
      have hoff : ∀ d', d' ≠ d → C d' = (C.deviatePure d a) d' := fun d' hd' =>
        (Proc.deviate_ne C _ hd').symm
      rw [leafLaw_eq_w_mul_offWeight B C h1 hdraw,
        leafLaw_eq_w_mul_offWeight B (C.deviatePure d a) h1 hdraw,
        ← offWeight_congr_off B d hoff ℓ, if_pos hobs]
      subst hpt
      simp only [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w]
      by_cases hba : b = a
      · subst hba
        rw [if_pos rfl, if_pos ⟨hactb, hobs⟩]; ring
      · rw [if_neg hba, if_neg]
        · ring
        · rintro ⟨hact, -⟩
          exact hba (huniq a hact).symm
    · simp [hobs]
  · rw [leafLaw_deviatePure_eq_zero C ha B ℓ hzero.symm, ← hzero]
    simp

/-- **`ν_{C[d↦a]}(O_d) · C(d)(a) = ν_C(a ∧ O_d)`** under Definition 7 recording for `C`.
Source: `faithful.md` FA-20′(ii); dp-sl-2-061(i); mandate T5(iv)
Kind: P
Fidelity: exact (cross-multiplied)
Hyps: (a) `RecordsFor obs actEv C B d`, (a) `0 < C(d)(a)` -/
theorem nu_deviatePure_obs_mul {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) :
    nu (C.deviatePure d a) B (obs d) * (C d).w a = nu C B (actEv d a ∩ obs d) := by
  rw [nu_eq_sum, nu_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have := ite_deviatePure_obs_mul obs actEv C B h ha ℓ 1
  simp only [mul_one] at this
  rw [this]
  simp [Finset.mem_inter]

/-- **`paySum_{C[d↦a]}(O_d) · C(d)(a) = paySum_C(a ∧ O_d)`** under Definition 7 recording for `C`.
Source: `faithful.md` FA-20′(ii); mandate T5(iv)
Kind: P
Fidelity: exact (cross-multiplied)
Hyps: (a) `RecordsFor obs actEv C B d`, (a) `0 < C(d)(a)` -/
theorem paySum_deviatePure_obs_mul {d : ι} (h : RecordsFor obs actEv C B d) {a : acts d}
    (ha : 0 < (C d).w a) :
    paySum (C.deviatePure d a) B (obs d) * (C d).w a = paySum C B (actEv d a ∩ obs d) := by
  rw [paySum_eq_sum_ite, paySum_eq_sum_ite, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [ite_deviatePure_obs_mul obs actEv C B h ha ℓ (payoff B ℓ)]
  simp [Finset.mem_inter]

/-- **R1-state is the strict act-conditional at a recorded point**: under Definition 7 recording
for `C`, `C(d)(a) > 0` and `ν_C(a ∧ O_d) > 0`, `refR1State a = 𝔼_C[r ∣ a ∧ O_d]`.
Source: `faithful.md` FA-20′(ii)(iii); dp-sl-2-061(i); mandate T5(iv)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsFor obs actEv C B d`, (a) `0 < C(d)(a)`, (a) `0 < ν_C(a ∧ O_d)` -/
theorem refR1State_eq_condExp_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d)
    {a : acts d} (ha : 0 < (C d).w a) (hpos : 0 < nu C B (actEv d a ∩ obs d)) :
    refR1State obs C B d a = condExp C B (actEv d a ∩ obs d) := by
  unfold refR1State condExp
  rw [← nu_deviatePure_obs_mul obs actEv C B h ha, ← paySum_deviatePure_obs_mul obs actEv C B h ha]
  have hν : nu (C.deviatePure d a) B (obs d) ≠ 0 := by
    intro h0
    rw [← nu_deviatePure_obs_mul obs actEv C B h ha, h0, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  field_simp

/-- **The act partition of `O_d` under Definition 7 recording**: every positive `O_d`-leaf lies in
exactly one action event (clauses 3 and 4), so `ν_C(O_d) = ∑_b ν_C(b ∧ O_d)` (pointwise, with any
weight `g`).
Source: [[decision-problems-v2]] Definition 7 clauses (3)–(4); mandate T13(i)
Kind: P -/
theorem ite_obs_eq_sum_actEv {d : ι} (h : RecordsFor obs actEv C B d) (ℓ : B.Leaves) (g : K) :
    (if world B ℓ ∈ obs d then leafLaw C B ℓ * g else 0) =
      ∑ b, if world B ℓ ∈ actEv d b ∧ world B ℓ ∈ obs d then leafLaw C B ℓ * g else 0 := by
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · by_cases hobs : world B ℓ ∈ obs d
    · obtain ⟨h1, hnode⟩ := h ℓ hpos hobs
      have hcard := h1
      rw [count_eq_card_dNodesOn, Finset.card_eq_one] at hcard
      obtain ⟨q, hq⟩ := hcard
      have hmem : q ∈ dNodesOn B d ℓ := by rw [hq]; exact Finset.mem_singleton_self q
      rw [mem_dNodesOn] at hmem
      obtain ⟨hpt, hsome⟩ := hmem
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨-, hactb, huniq⟩ := hnode q hpt b hb
      subst hpt
      exact ite_eq_sum_of_unique Finset.univ _ _ _
        (fun _ => ⟨b, Finset.mem_univ _, hactb, hobs⟩)
        (fun _ _ hc => hc.2)
        (fun b₁ _ b₂ _ h₁ h₂ => (huniq b₁ h₁.1).trans (huniq b₂ h₂.1).symm)
    · simp [hobs]
  · rw [← hzero]; simp

/-- `ν_C(O_d) = ∑_b ν_C(b ∧ O_d)` under Definition 7 recording.
Source: [[decision-problems-v2]] Definition 7; mandate T13(i) (the exhaustiveness `P(⋁_a a) = 1`)
Kind: P
Fidelity: exact
Hyps: (a) `RecordsFor obs actEv C B d` -/
theorem nu_obs_eq_sum_actEv {d : ι} (h : RecordsFor obs actEv C B d) :
    nu C B (obs d) = ∑ b, nu C B (actEv d b ∩ obs d) := by
  have hL : nu C B (obs d) = ∑ ℓ, if world B ℓ ∈ obs d then leafLaw C B ℓ * 1 else 0 := by
    rw [nu_eq_sum]; simp
  rw [hL, Finset.sum_congr rfl (fun ℓ _ => ite_obs_eq_sum_actEv obs actEv C B h ℓ 1),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [Finset.mem_inter]

/-- `paySum_C(O_d) = ∑_b paySum_C(b ∧ O_d)` under Definition 7 recording.
Source: [[decision-problems-v2]] Definition 7; mandate T13(i)
Kind: P
Fidelity: exact
Hyps: (a) `RecordsFor obs actEv C B d` -/
theorem paySum_obs_eq_sum_actEv {d : ι} (h : RecordsFor obs actEv C B d) :
    paySum C B (obs d) = ∑ b, paySum C B (actEv d b ∩ obs d) := by
  rw [paySum_eq_sum_ite,
    Finset.sum_congr rfl (fun ℓ _ => ite_obs_eq_sum_actEv obs actEv C B h ℓ (payoff B ℓ)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [paySum_eq_sum_ite]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp [Finset.mem_inter]

end deviation

end Cleanroom.Decision.DpReferentsCdt
