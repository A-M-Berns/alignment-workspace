import Cleanroom.Corrigibility.CorrLegitGeneral.Defs

/-!
# corr-legit-general — T8: mutual universal deference is agreement (mm I9.3)

Two immodest ("clear") frames `FA`, `FH` on one world space, an actual world `ω*`, and
non-dogmatism (each party's actual state gives positive probability to the other's actual
cell). If the agent's state totally trusts the humans' frame and the humans' state totally trusts
the agent's frame, the two states are equal; conversely equal states trust each other's frames.
Proof as the source's two steps, with the first step simplified: a positive-mass world `ω₁` of
`P^A` whose expert state `H_{ω₁}` leaks mass `q` outside `[ω*]_A` gives, with `X = 𝟙_{leak}`,
a below-zero term at `ω₁` in a sum all of whose terms are `≤ 0`. Witnesses: `WitnessesMutual.lean`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- An immodest frame's row vanishes off its own cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.Immodest.apply_eq_zero_of_not_mem_cell {F : Frame W} (hF : F.Immodest) {w v : W}
    (hv : v ∉ F.cell (F.P w)) : F.P w v = 0 := by
  have h1 := hF w
  unfold Frame.selfMass at h1
  have h2 : mass (F.P w) (F.cell (F.P w)) + mass (F.P w) (univ \ F.cell (F.P w)) = 1 := by
    have := mass_inter_add_mass_sdiff (F.P w) univ (F.cell (F.P w))
    rwa [univ_inter, mass_univ (F.P_mem w)] at this
  have h3 : mass (F.P w) (univ \ F.cell (F.P w)) = 0 := by linarith
  have h4 : v ∈ univ \ F.cell (F.P w) := mem_sdiff.2 ⟨mem_univ v, hv⟩
  have h5 := mass_pos_of_mem (F.P_mem w).1 h4
  by_contra hne
  have := h5 (lt_of_le_of_ne ((F.P_mem w).1 v) (Ne.symm hne))
  linarith

/-- A finite sum with all terms `≤ 0` and one term `< 0` is `< 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_neg_of_term_neg {f : W → ℝ} (hf : ∀ w, f w ≤ 0) {w₀ : W} (hw₀ : f w₀ < 0) :
    ∑ w, f w < 0 := by
  have := sum_lt_sum (s := (univ : Finset W)) (f := f) (g := fun _ => 0)
    (fun w _ => hf w) ⟨w₀, mem_univ w₀, hw₀⟩
  simpa using this

/-- **Step 1 of mm I9.3**: if `P^A := FA.P ω` totally trusts `FH` and `FH` is immodest, then the
expert state `H_{ω₁}` at every `P^A`-positive world `ω₁` vanishes outside `[ω]_A`.
Source: [[mm]] I9.3 l. 188 (Step 1)
Kind: P
Fidelity: exact
Hyps: (a) `FA.Immodest`, `TotalTrust (FA.P ω) FH`, `0 < FA.P ω ω₁` (the immodesty of `FH` is not
needed for this step) -/
theorem step1_supported {FA FH : Frame W} (hA : FA.Immodest) {ω : W}
    (hAH : TotalTrust (FA.P ω) FH) {ω₁ : W} (hω₁ : 0 < FA.P ω ω₁) :
    ∀ v, v ∉ FA.cell (FA.P ω) → FH.P ω₁ v = 0 := by
  intro v hv
  by_contra hne
  have hvpos : 0 < FH.P ω₁ v := lt_of_le_of_ne ((FH.P_mem ω₁).1 v) (Ne.symm hne)
  set S : Finset W := univ \ FA.cell (FA.P ω) with hS
  have hvS : v ∈ S := mem_sdiff.2 ⟨mem_univ v, hv⟩
  set q := mass (FH.P ω₁) S with hq
  have hqpos : 0 < q := mass_pos_of_mem (FH.P_mem ω₁).1 hvS hvpos
  have h := hAH (ind S) q
  -- every term is `≤ 0`: `P^A` lives on `[ω]_A`, where `𝟙_S = 0`
  have hterm : ∀ w, FA.P ω w * (ind S w - q) * (if q ≤ E (FH.P w) (ind S) then 1 else 0) ≤ 0 := by
    intro w
    rcases ((FA.P_mem ω).1 w).lt_or_eq with hw | hw
    · have hwcell : w ∈ FA.cell (FA.P ω) := by
        by_contra hc
        exact absurd (Frame.Immodest.apply_eq_zero_of_not_mem_cell hA hc) hw.ne'
      have hind : ind S w = 0 := by simp [ind, hS, hwcell]
      rw [hind]
      split_ifs
      · nlinarith
      · simp
    · rw [← hw]; simp
  have hω₁term : FA.P ω ω₁ * (ind S ω₁ - q) * (if q ≤ E (FH.P ω₁) (ind S) then 1 else 0) < 0 := by
    have hcell : ω₁ ∈ FA.cell (FA.P ω) := by
      by_contra hc
      exact absurd (Frame.Immodest.apply_eq_zero_of_not_mem_cell hA hc) hω₁.ne'
    have hind : ind S ω₁ = 0 := by simp [ind, hS, hcell]
    have hE : E (FH.P ω₁) (ind S) = q := by rw [E_ind]
    rw [hind, hE, if_pos le_rfl, mul_one]
    nlinarith
  have hsum : ∑ w, FA.P ω w * (ind S w - q) * (if q ≤ E (FH.P w) (ind S) then 1 else 0) < 0 :=
    sum_neg_of_term_neg hterm hω₁term
  linarith

/-- **mm I9.3, mutual Total Trust is agreement**: under clarity (immodesty of both frames) and
non-dogmatism, if `FA.P ω*` totally trusts `FH` and `FH.P ω*` totally trusts `FA`, then
`FA.P ω* = FH.P ω*`. Step 1 puts each party's actual state inside the other's actual cell;
on the intersection both frames are constant, so each state's expectation of every `X` is a
threshold the other reaches everywhere on the state's support, and Total Trust gives
`E_{P^H}(X) ≤ E_{P^A}(X)` and the reverse.
Source: [[mm]] I9.3 l. 188; corr-wf13-038
Kind: P
Fidelity: exact
Hyps: (a) `FA.Immodest`, `FH.Immodest`, non-dogmatism both ways, the two Total Trusts -/
theorem mutual_totalTrust_eq {FA FH : Frame W} (hA : FA.Immodest) (hH : FH.Immodest) (ω : W)
    (hndA : 0 < mass (FA.P ω) (FH.cell (FH.P ω))) (hndH : 0 < mass (FH.P ω) (FA.cell (FA.P ω)))
    (hAH : TotalTrust (FA.P ω) FH) (hHA : TotalTrust (FH.P ω) FA) : FA.P ω = FH.P ω := by
  -- `P^H` vanishes off `[ω]_A`, and `P^A` off `[ω]_H`
  obtain ⟨ω₁, hω₁cell, hω₁pos⟩ := (mass_pos_iff (FA.P_mem ω).1).1 hndA
  have hH_in_A : ∀ v, v ∉ FA.cell (FA.P ω) → FH.P ω v = 0 := by
    intro v hv
    have := step1_supported hA hAH hω₁pos v hv
    rwa [Frame.mem_cell.1 hω₁cell] at this
  obtain ⟨ω₂, hω₂cell, hω₂pos⟩ := (mass_pos_iff (FH.P_mem ω).1).1 hndH
  have hA_in_H : ∀ v, v ∉ FH.cell (FH.P ω) → FA.P ω v = 0 := by
    intro v hv
    have := step1_supported hH hHA hω₂pos v hv
    rwa [Frame.mem_cell.1 hω₂cell] at this
  -- Step 2: `E_{P^H}(X) ≤ E_{P^A}(X)` for every `X`
  have key : ∀ (GA GH : Frame W), GA.Immodest →
      (∀ v, v ∉ GH.cell (GH.P ω) → GA.P ω v = 0) → TotalTrust (GA.P ω) GH →
      ∀ X, E (GH.P ω) X ≤ E (GA.P ω) X := by
    intro GA GH hGA hAinH hT X
    have h := hT X (E (GH.P ω) X)
    have e : ∑ w, GA.P ω w * (X w - E (GH.P ω) X) *
        (if E (GH.P ω) X ≤ E (GH.P w) X then 1 else 0) =
        ∑ w, GA.P ω w * (X w - E (GH.P ω) X) := by
      apply sum_congr rfl
      intro w _
      rcases ((GA.P_mem ω).1 w).lt_or_eq with hw | hw
      · have hwH : w ∈ GH.cell (GH.P ω) := by
          by_contra hc
          exact absurd (hAinH w hc) hw.ne'
        rw [Frame.mem_cell.1 hwH, if_pos le_rfl, mul_one]
      · rw [← hw]; simp
    rw [e] at h
    have e2 : ∑ w, GA.P ω w * (X w - E (GH.P ω) X) = E (GA.P ω) X - E (GH.P ω) X := by
      simp only [E, mul_sub, sum_sub_distrib, ← sum_mul, (GA.P_mem ω).2, one_mul]
    linarith
  have h1 := key FA FH hA hA_in_H hAH
  have h2 := key FH FA hH hH_in_A hHA
  funext v
  have e1 := h1 (ind {v})
  have e2 := h2 (ind {v})
  simp only [E_ind, mass_singleton] at e1 e2
  exact le_antisymm e2 e1

/-- **mm I9.3, the converse**: equal actual states under clarity trust each other's frames
(non-dogmatism is not needed). With `Q := FA.P ω = FH.P ω`, `Q` lives on `[ω]_H`, where every
row of `FH` is `Q`, so every conditioning event is `Q`-full or `Q`-null.
Source: [[mm]] I9.3 l. 188 (Converse)
Kind: P
Fidelity: exact
Hyps: (a) `FA.Immodest`, `FH.Immodest`, `FA.P ω = FH.P ω` -/
theorem mutual_totalTrust_of_eq {FA FH : Frame W} (hA : FA.Immodest) (hH : FH.Immodest) (ω : W)
    (heq : FA.P ω = FH.P ω) : TotalTrust (FA.P ω) FH ∧ TotalTrust (FH.P ω) FA := by
  have key : ∀ (GA GH : Frame W), GH.Immodest → GA.P ω = GH.P ω → TotalTrust (GA.P ω) GH := by
    intro GA GH hGH hQ X s
    have e : ∑ w, GA.P ω w * (X w - s) * (if s ≤ E (GH.P w) X then 1 else 0) =
        (if s ≤ E (GH.P ω) X then 1 else 0) * ∑ w, GA.P ω w * (X w - s) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w _
      rcases ((GA.P_mem ω).1 w).lt_or_eq with hw | hw
      · have hwH : w ∈ GH.cell (GH.P ω) := by
          by_contra hc
          have := Frame.Immodest.apply_eq_zero_of_not_mem_cell hGH hc
          rw [← hQ] at this
          exact absurd this hw.ne'
        rw [Frame.mem_cell.1 hwH]; ring
      · rw [← hw]; simp
    rw [e]
    have e2 : ∑ w, GA.P ω w * (X w - s) = E (GH.P ω) X - s := by
      rw [hQ]
      simp only [E, mul_sub, sum_sub_distrib, ← sum_mul, (GH.P_mem ω).2, one_mul]
    rw [e2]
    split_ifs with hs
    · linarith
    · simp
  exact ⟨key FA FH hH heq, key FH FA hA heq.symm⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
