import Cleanroom.Found.LitDdbFrames.Cycle
import Cleanroom.Found.LitDdbFrames.SelfWeight
import Mathlib.Tactic.TFAE

/-!
# Lemma 7.5 (Weak Value → Value) and Theorem 7.6 = 2.2 = 4.1

Package `lit-ddb-frames`, Targets 16–17. Lemma 7.5 follows DDB's construction — replace each
option a recommended strategy `S` selects by a boosted copy paying `t_ρ` extra on `ρ`'s cell — with
the mandate's simplifications: `E_σ(S_ρ^t − S_ρ) = t · σ(P = ρ)`, so the intermediate-value step
is `t_ρ := δ / ρ(P = ρ)` (positive by Reflexivity), and the strict inequality (**) is
`SelfWeight.lean`'s `mass_cell_lt_selfMass_of_hull`.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Boosted options -/

/-- DDB's `S_i^t`: the option `S` selects at `w`, paying `δ / P_w(P = P_w)` extra on the cell of
`P_w` — so its expected gain under `P_w` is exactly `δ`.
Source: [[Deference Done Better]] App. B Lemma 7.5 l. 590
Kind: D
Fidelity: exact (with `t_i := δ / P_i(P = P_i)`, the mandate's closed form of DDB's IVT step) -/
def Frame.boost (F : Frame W) (S : W → (W → ℝ)) (δ : ℝ) (w : W) : W → ℝ :=
  S w + (δ / F.selfMass (F.P w)) • ind (F.cell (F.P w))

/-- Expectation of a boosted option: `E_σ(S_w^δ) = E_σ(S_w) + (δ / P_w(P = P_w)) · σ(P = P_w)`.
Source: [[Deference Done Better]] App. B Lemma 7.5 l. 592
Kind: L
Fidelity: n/a -/
theorem Frame.E_boost (F : Frame W) (S : W → (W → ℝ)) (δ : ℝ) (w : W) (σ : W → ℝ) :
    E σ (F.boost S δ w) = E σ (S w) + δ / F.selfMass (F.P w) * mass σ (F.cell (F.P w)) := by
  unfold Frame.boost
  rw [E_add_right, E_smul_right, E_ind]

/-- Boosting respects the cell constraint.
Source: none: infrastructure (Target 16)
Kind: L
Fidelity: n/a -/
theorem Frame.boost_cell (F : Frame W) {S : W → (W → ℝ)}
    (hcell : ∀ w v, F.P w = F.P v → S w = S v) (δ : ℝ) {w v : W} (e : F.P w = F.P v) :
    F.boost S δ w = F.boost S δ v := by
  unfold Frame.boost
  rw [hcell w v e, e]

/-! ## Lemma 7.5 -/

/-- **Target 16 (Lemma 7.5).** Weak Value implies Value. Given a menu, a recommended `S` and an
option `O` with `E_π(O) > E_π(S)`: by the cycle the hull condition holds, so every candidate has a
positive self-cell and strict self-cell dominance (**). Replace the options `S` selects by their
boosts with `δ := β · m / 2` (`β` the gap, `m` the least self-cell mass); each candidate's boost
is then its *unique* maximiser on the new menu, so every recommended strategy is the boosted
`S`, whose value exceeds `S`'s by at most `β / 2` — while `O` (or its boost) is still on the menu
and beats it. So Weak Value fails on the new menu.
Source: [[Deference Done Better]] App. B Lemma 7.5 l. 583
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem WeakValue.value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : WeakValue π F) : Value π F := by
  have hH := (h.totalTrust hπ).hullAndModestlyInformed hπ
  have hdec := hH.decompOver
  intro 𝒪 hne S hS o ho
  by_contra hlt
  push_neg at hlt
  set β := E π o - stratValue π S with hβ
  have hβpos : 0 < β := by linarith
  obtain ⟨ρ₀, hρ₀, hmin⟩ := (F.cands π).exists_min_image (fun ρ => F.selfMass ρ)
    (F.cands_nonempty hπ)
  set m := F.selfMass ρ₀ with hm
  have hmpos : 0 < m := F.selfMass_pos_of_hull hπ hH.1 hdec hρ₀
  set δ := β * m / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set 𝒪' : DecisionProblem W := (𝒪 \ (supp π).image S) ∪ (supp π).image (F.boost S δ) with h𝒪'
  have hne' : 𝒪'.Nonempty := by
    obtain ⟨w, hw⟩ := supp_nonempty hπ
    exact ⟨F.boost S δ w, mem_union_right _ (mem_image.2 ⟨w, hw, rfl⟩)⟩
  have hsm : ∀ w, 0 < π w → m ≤ F.selfMass (F.P w) := fun w hw => hmin _ (F.P_mem_cands hw)
  have hsmpos : ∀ w, 0 < π w → 0 < F.selfMass (F.P w) :=
    fun w hw => lt_of_lt_of_le hmpos (hsm w hw)
  -- each candidate's boost is the unique maximiser on the new menu
  have huniq : ∀ w, 0 < π w → ∀ o' ∈ 𝒪', o' ≠ F.boost S δ w →
      E (F.P w) o' < E (F.P w) (F.boost S δ w) := by
    intro w hw o' ho' hne''
    have hEw : E (F.P w) (F.boost S δ w) = E (F.P w) (S w) + δ := by
      rw [F.E_boost, ← Frame.selfMass, div_mul_cancel₀ _ (hsmpos w hw).ne']
    rcases mem_union.1 ho' with h1 | h1
    · have := hS.le w (mem_sdiff.1 h1).1
      rw [hEw]; linarith
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 h1
      have hvπ := mem_supp.1 hv
      have hPne : F.P w ≠ F.P v := fun e => hne'' (F.boost_cell hS.1.2 δ e.symm)
      have hlt' : mass (F.P w) (F.cell (F.P v)) < F.selfMass (F.P v) :=
        F.mass_cell_lt_selfMass_of_hull hπ hH (F.P_mem_cands hvπ) (F.P_mem_cands hw) hPne
      have h2 : δ / F.selfMass (F.P v) * mass (F.P w) (F.cell (F.P v)) < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (hsmpos v hvπ)]
        exact mul_lt_mul_of_pos_left hlt' hδpos
      have h3 := hS.le w (hS.mem v)
      rw [F.E_boost, hEw]
      linarith
  obtain ⟨S', hS', hval⟩ := h 𝒪' hne'
  have hS'eq : ∀ w, 0 < π w → S' w = F.boost S δ w := by
    intro w hw
    by_contra hne''
    have h1 := huniq w hw (S' w) (hS'.mem w) hne''
    have h2 := hS'.le w (o := F.boost S δ w)
      (mem_union_right _ (mem_image.2 ⟨w, mem_supp.2 hw, rfl⟩))
    linarith
  have hS'val : stratValue π S' ≤ stratValue π S + δ / m := by
    have e1 : stratValue π S' = stratValue π S + ∑ w, π w * (δ / F.selfMass (F.P w)) := by
      unfold stratValue
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro w _
      rcases (hπ.1 w).lt_or_eq with hw | hw
      · rw [hS'eq w hw]
        simp only [Frame.boost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ind, F.mem_cell_self,
          if_true, mul_one]
        ring
      · rw [← hw]; ring
    rw [e1]
    have e2 : ∑ w, π w * (δ / F.selfMass (F.P w)) ≤ ∑ w, π w * (δ / m) := by
      apply sum_le_sum
      intro w _
      rcases (hπ.1 w).lt_or_eq with hw | hw
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hδpos.le hmpos (hsm w hw)) hw.le
      · rw [← hw]; simp
    rw [← sum_mul, hπ.2, one_mul] at e2
    linarith
  have hm0 : m ≠ 0 := hmpos.ne'
  have hδm : δ / m = β / 2 := by
    rw [hδ, div_div, mul_div_mul_right β 2 hm0]
  rw [hδm] at hS'val
  -- `o` (or its boost) is on the new menu and beats `S'`
  have hcontra : E π o ≤ stratValue π S' := by
    by_cases hoS : o ∈ (supp π).image S
    · obtain ⟨v, hv, rfl⟩ := mem_image.1 hoS
      have h1 := hval (F.boost S δ v) (mem_union_right _ (mem_image.2 ⟨v, hv, rfl⟩))
      have h2 : E π (S v) ≤ E π (F.boost S δ v) := by
        rw [F.E_boost]
        have : 0 ≤ δ / F.selfMass (F.P v) * mass π (F.cell (F.P v)) :=
          mul_nonneg (div_nonneg hδpos.le (mass_nonneg (F.P_nonneg v) _)) (mass_nonneg hπ.1 _)
        linarith
      linarith
    · exact hval o (mem_union_left _ (mem_sdiff.2 ⟨ho, hoS⟩))
  linarith

/-! ## Theorem 7.6 = 2.2 = 4.1 -/

/-- **Target 17 (Theorem 7.6 = 2.2 = 4.1).** For a finite frame and a deferrer
`π ∈ stdSimplex ℝ W`, the following are equivalent: `π` values the frame (all nonempty finite
menus, all recommended strategies); `π` weakly values it; `π` totally trusts it (product form,
all `X`, all real thresholds); `π` lies in the convex hull of its candidates and every candidate
is modestly informed. The cycle is Lemmas 7.1–7.3, closed by 7.5; no DDB lemma is assumed and
the null-event convention is `totalTrust_iff_cond`.
Source: [[Deference Done Better]] §2 l. 186 (Thm 2.2), §4 l. 327 (Thm 4.1), App. B l. 625
(Thm 7.6)
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem tfae_value {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    List.TFAE [Value π F, WeakValue π F, TotalTrust π F, HullAndModestlyInformed π F] := by
  tfae_have 1 → 2 := Value.weakValue
  tfae_have 2 → 3 := WeakValue.totalTrust hπ
  tfae_have 3 → 4 := TotalTrust.hullAndModestlyInformed hπ
  tfae_have 4 → 2 := HullAndModestlyInformed.weakValue hπ
  tfae_have 2 → 1 := WeakValue.value hπ
  tfae_finish

/-- **Theorem 2.2.** `π` totally trusts the frame iff it values it.
Source: [[Deference Done Better]] §2 l. 186
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem value_iff_totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Value π F ↔ TotalTrust π F :=
  (tfae_value hπ F).out 0 2

/-- **Theorem 4.1.** `π` totally trusts the frame iff it lies in the convex hull of its
candidates and every candidate is modestly informed.
Source: [[Deference Done Better]] §4 l. 327
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem totalTrust_iff_hullAndModestlyInformed {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (F : Frame W) : TotalTrust π F ↔ HullAndModestlyInformed π F :=
  (tfae_value hπ F).out 2 3

/-- **Lemma 7.5 as an iff.** `π` values the frame iff it weakly values it.
Source: [[Deference Done Better]] App. B Lemma 7.5 l. 583
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem value_iff_weakValue {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    Value π F ↔ WeakValue π F :=
  (tfae_value hπ F).out 0 1

/-- **Corollary of 7.6.** Value on two-option menus `{X, const s}`, over all recommended
strategies, is equivalent to Total Trust — not by the witness identity alone (which gives ⇒)
but through the full cycle (⇐).
Source: [[Deference Done Better]] §2 l. 190; mandate Target 3
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem valueTwoOption_iff_totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) :
    ValueTwoOption π F ↔ TotalTrust π F :=
  ⟨ValueTwoOption.totalTrust hπ, fun h => ((value_iff_totalTrust hπ F).2 h).twoOption⟩

/-- **Fn 16 / fn 17 direction.** Total Trust implies New Reflection, hence so does Value.
Source: [[Deference Done Better]] §1 l. 133, fn 19
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem Value.newReflects {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} (h : Value π F) :
    NewReflects π F :=
  ((value_iff_totalTrust hπ F).1 h).newReflects hπ.1

end

end Cleanroom.Found.LitDdbFrames
