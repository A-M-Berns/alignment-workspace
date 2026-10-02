import Cleanroom.Decision.DpCausalConsist.TbThetaNR
import Cleanroom.Decision.DpCausalConsist.NRValueWeak
import Cleanroom.Decision.DpCausalConsist.Witness3

/-!
# `dp-causal-consist`: `NRAt` is inhabited where the Axiom-NR headlines apply (T8, repair round 2)

Audit r2 (both lenses, B1): after repair round 1 the headlines `tb_nrAt_V_cross`,
`nrcf_eq_deviation`, `nrcf_ne_forcing` (`TbTheta.lean`) and the general `nr_forces_kpart`,
`nr_forces_kpart_V`, `nr_evidential_at_recording` (`NR.lean`, `NRValue.lean`) quantify over an
arbitrary counterfactual component `t` with `NRAt t actEv exo`, and the package exhibited an
`NRAt` component only at the stay label of `TB(θ)` (`cfNR`, `TbThetaNR.lean`), where every one of
those theorems' guards fails. This file ships the inhabitants ([[STANDARDS]] §3 non-vacuity):

* **General** (`kPartCf`, `kPartCf_nrAt`): for a support-regular state `s` and an exogenous
  designation whose every cell meets every act event positively, the counterfactual component
  whose supposition of each act is the K-partition state `kPart s (actEv a) exo` satisfies Axiom
  NR — the K-partition state *is* an `NRAt` component on an act every cell meets. The clauses are
  `kPart_pr_self` (success), `kPart_pr_cell` (i), `kPart_pr_inter_cell` (ii), `kPart_V_sub` (iii).
* **`TB(θ)` at every mixed label** (`cfK`, `cfK_nrAt`): `cf(cross) := kPart` (both cells meet
  `cross` at `q > 0`), `cf(stay) := cfStay θ 0` (the `bot` cell does not meet `stay`, so `kPart`'s
  fallback would break success there; the two-point law with the zero fill serves), a point mass
  elsewhere. `cfK_V_cross`, `cfK_nrcf_eq_deviation` instantiate the three `TbTheta` headlines, and
  `nrAt_mixed_inhabited` states the inhabitation as an existential.
* **The recorded direct-effect point with `exo := ℓ`** (`cfKS1 := kPartCf (directState u) …`,
  `cfKS1_nrAt`): every lesion cell meets every act with mass `≥ 1/40 · 1/20`;
  `nr_evidential_cfKS1` instantiates `nr_evidential_at_recording`, so its hypothesis package is
  inhabited and its conclusion is a fact about a concrete component: `P^b(X) = P(X ∧ b)/P(b)`.

Both audit probes (`run/wp/dp-causal-consist/audit-r2-probes/NRAtWitness.lean`, `NRAtMixed.lean`)
built inhabitants; the general lemmas and `cfK` follow the adversarial probe, the fidelity probe's
`cfNRq` (the `cfNR` shape with fill `10` at every label) is an alternative not shipped.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree
  Cleanroom.Found.DpCoreTree.Catalogue Cleanroom.Decision.DpCalibration Finset

/-! ## The K-partition state satisfies Axiom NR's clauses on its own act -/

section general

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- Success of the K-partition state on an event every cell meets positively: `kPart(A) = 1`.
Source: none: infrastructure (Axiom NR's success clause for `kPart`)
Kind: L -/
theorem kPart_pr_self (s : State Ω K) (A : Finset Ω) (exo : Ω → E)
    (hpos : ∀ e, 0 < s.pr (A ∩ cell exo e)) : (kPart s A exo).pr A = 1 := by
  rw [kPart_pr_of_pos s A exo (fun e _ => hpos e)]
  have h : ∀ e, s.pr (A ∩ (A ∩ cell exo e)) / s.pr (A ∩ cell exo e) = 1 := by
    intro e
    rw [← Finset.inter_assoc, Finset.inter_self]
    exact div_self (hpos e).ne'
  simp_rw [h, mul_one]
  exact (cellDistr s exo).sum_one

/-- Clause (i) for `kPart`: it keeps every cell's probability.
Source: [[non-responsiveness]] "Axiom NR" clause (i), for the K-partition state
Kind: L -/
theorem kPart_pr_cell (s : State Ω K) (A : Finset Ω) (exo : Ω → E)
    (hpos : ∀ e, 0 < s.pr (A ∩ cell exo e)) (e : E) :
    (kPart s A exo).pr (cell exo e) = s.pr (cell exo e) := by
  rw [kPart_pr_of_pos s A exo (fun e _ => hpos e), Finset.sum_eq_single e]
  · have hset : cell exo e ∩ (A ∩ cell exo e) = A ∩ cell exo e := by
      ext ω; simp only [Finset.mem_inter]; tauto
    rw [hset, div_self (hpos e).ne', mul_one]
  · intro e' _ hne
    have hset : cell exo e ∩ (A ∩ cell exo e') = ∅ := by
      ext ω
      simp only [Finset.mem_inter, mem_cell, Finset.notMem_empty, iff_false, not_and]
      intro h1 _ h2; exact hne (h2.symm.trans h1)
    rw [hset]; simp [State.pr]
  · intro h; exact absurd (Finset.mem_univ e) h

/-- Clause (ii) for `kPart`, unnormalised: `kPart(X ∧ e) = P(e) · P(X ∧ A ∧ e)/P(A ∧ e)`.
Source: [[non-responsiveness]] "Axiom NR" clause (ii), for the K-partition state
Kind: L -/
theorem kPart_pr_inter_cell (s : State Ω K) (A : Finset Ω) (exo : Ω → E)
    (hpos : ∀ e, 0 < s.pr (A ∩ cell exo e)) (e : E) (X : Finset Ω) :
    (kPart s A exo).pr (X ∩ cell exo e)
      = s.pr (cell exo e) * (s.pr (X ∩ A ∩ cell exo e) / s.pr (A ∩ cell exo e)) := by
  rw [kPart_pr_of_pos s A exo (fun e _ => hpos e), Finset.sum_eq_single e]
  · have hset : X ∩ cell exo e ∩ (A ∩ cell exo e) = X ∩ A ∩ cell exo e := by
      ext ω; simp only [Finset.mem_inter]; tauto
    rw [hset]
  · intro e' _ hne
    have hset : X ∩ cell exo e ∩ (A ∩ cell exo e') = ∅ := by
      ext ω
      simp only [Finset.mem_inter, mem_cell, Finset.notMem_empty, iff_false, not_and]
      rintro ⟨_, h1⟩ _ h2; exact hne (h2.symm.trans h1)
    rw [hset]; simp [State.pr]
  · intro h; exact absurd (Finset.mem_univ e) h

/-- Clause (iii) for `kPart`: on a positive sub-event of `A ∧ e`, its desirability is the state's.
Source: [[non-responsiveness]] "Axiom NR" clause (iii), for the K-partition state
Kind: L -/
theorem kPart_V_sub (s : State Ω K) (hreg : SuppRegular s) (A : Finset Ω) (exo : Ω → E)
    (hpos : ∀ e, 0 < s.pr (A ∩ cell exo e)) (e : E) (Y : Finset Ω) (hY : Y ⊆ A ∩ cell exo e)
    (hYpos : 0 < s.pr Y) : (kPart s A exo).V Y = s.V Y := by
  rw [kPart_V_of_suppRegular s hreg]
  have hcomp : ∀ e', kPartComp s A exo e' = jeffreyCond s (A ∩ cell exo e') (hpos e') := by
    intro e'; unfold kPartComp; rw [dif_pos (hpos e')]
  have hzero : ∀ e', e' ≠ e → Y ∩ (A ∩ cell exo e') = ∅ := by
    intro e' hne
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ω hω
    rw [Finset.mem_inter, Finset.mem_inter] at hω
    have h1 := (Finset.mem_inter.mp (hY hω.1)).2
    rw [mem_cell] at h1
    have h2 := hω.2.2
    rw [mem_cell] at h2
    exact hne (h2.symm.trans h1)
  have hN : ∑ e', s.pr (cell exo e') * (kPartComp s A exo e').pr Y * (kPartComp s A exo e').V Y
      = s.pr (cell exo e) * (s.pr Y / s.pr (A ∩ cell exo e)) * s.V Y := by
    rw [Finset.sum_eq_single e]
    · rw [hcomp e, jeffreyCond_pr, jeffreyCond_V, Finset.inter_eq_left.mpr hY]
    · intro e' _ hne
      rw [hcomp e', jeffreyCond_pr, hzero e' hne]
      simp [State.pr]
    · intro h; exact absurd (Finset.mem_univ e) h
  have hD : ∑ e', s.pr (cell exo e') * (kPartComp s A exo e').pr Y
      = s.pr (cell exo e) * (s.pr Y / s.pr (A ∩ cell exo e)) := by
    rw [Finset.sum_eq_single e]
    · rw [hcomp e, jeffreyCond_pr, Finset.inter_eq_left.mpr hY]
    · intro e' _ hne
      rw [hcomp e', jeffreyCond_pr, hzero e' hne]
      simp [State.pr]
    · intro h; exact absurd (Finset.mem_univ e) h
  rw [hN, hD]
  have hne : s.pr (cell exo e) * (s.pr Y / s.pr (A ∩ cell exo e)) ≠ 0 := by
    apply mul_ne_zero
    · exact (lt_of_lt_of_le (hpos e) (probOf_mono _ Finset.inter_subset_right)).ne'
    · exact (div_pos hYpos (hpos e)).ne'
  exact mul_div_cancel_left₀ _ hne

open scoped Classical in
/-- **The K-partition counterfactual component**: the supposition of every act event is the
K-partition state `kPart s (actEv a) exo`; a point mass on any other event (NR reads only the act
events). Needs every cell to meet every act positively, for success.
Source: [[non-responsiveness]] "Axiom NR" ("Hence `P^a_s = ∑_e P_s(e) P_s(· | a, e)`" — read as a
construction); mandate T8 (the inhabitant of `NRAt`); audit r2 B1
Kind: D -/
noncomputable def kPartCf {A : Type} (s : State Ω K) (actEv : A → Finset Ω) (exo : Ω → E)
    (hpos : ∀ a e, 0 < s.pr (actEv a ∩ cell exo e)) : CfState Ω K where
  s := s
  cf B h := if hB : ∃ a, B = actEv a then kPart s B exo else State.dirac h.choose 0
  success B h := by
    split_ifs with hB
    · obtain ⟨a, rfl⟩ := hB
      exact kPart_pr_self _ _ _ (hpos a)
    · rw [State.dirac_pr, if_pos h.choose_spec]

/-- `kPartCf` on an act event is the K-partition state. Source: none: infrastructure. Kind: L -/
theorem kPartCf_cf {A : Type} (s : State Ω K) (actEv : A → Finset Ω) (exo : Ω → E)
    (hpos : ∀ a e, 0 < s.pr (actEv a ∩ cell exo e)) (a : A) (h : (actEv a).Nonempty) :
    (kPartCf s actEv exo hpos).cf (actEv a) h = kPart s (actEv a) exo := by
  unfold kPartCf
  simp only
  rw [dif_pos ⟨a, rfl⟩]

/-- **The K-partition state is an `NRAt` component** (T8, audit r2 B1): for a support-regular
state and a designation whose every cell meets every act positively, `kPartCf` satisfies Axiom
NR's clauses (i)–(iii) on every act — so the hypothesis packages of `nr_forces_kpart`,
`nr_forces_kpart_V` and (at a recorded point) `nr_evidential_at_recording` are inhabited wherever
their positivity guards hold.
Source: [[non-responsiveness]] "Axiom NR"; mandate T8; audit r2 B1
Kind: N+ (every support-regular state with positive act × cell table)
Fidelity: exact
Hyps: (a) `SuppRegular s`; (a) every cell meets every act positively -/
theorem kPartCf_nrAt {A : Type} (s : State Ω K) (hreg : SuppRegular s) (actEv : A → Finset Ω)
    (exo : Ω → E) (hpos : ∀ a e, 0 < s.pr (actEv a ∩ cell exo e)) :
    NRAt (kPartCf s actEv exo hpos) actEv exo := by
  intro a h
  rw [kPartCf_cf]
  refine ⟨fun e => kPart_pr_cell _ _ _ (hpos a) e, fun e X _ => ?_, fun e X hXpos => ?_⟩
  · show (kPart s (actEv a) exo).pr (X ∩ cell exo e) * s.pr (actEv a ∩ cell exo e)
        = (kPart s (actEv a) exo).pr (cell exo e) * s.pr (X ∩ actEv a ∩ cell exo e)
    rw [kPart_pr_inter_cell _ _ _ (hpos a) e X, kPart_pr_cell _ _ _ (hpos a) e, mul_assoc,
      div_mul_cancel₀ _ (hpos a e).ne']
  · exact kPart_V_sub _ hreg _ _ (hpos a) e _
      (Finset.inter_subset_inter Finset.inter_subset_right (Finset.Subset.refl _)) hXpos

end general

/-! ## `TB(θ)` at a mixed label -/

section tb

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- Both cells meet `cross` positively at a mixed label: `P(cross ∧ ¬bot) = (1−θ)q`,
`P(cross ∧ bot) = θ`. Source: none: infrastructure. Kind: L -/
theorem tb_cross_cells_pos (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    ∀ e, 0 < (tbState θ h0 h1 q q0 q1).pr (tbActEv () Act2.a ∩ cell exoBot e) := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := tb_mem_facts
  intro e
  cases e
  · rw [tbState_pr]; simp [m2, m3, m5, m7, m8, m9]; exact mul_pos (by linarith) hq
  · rw [tbState_pr]; simp [m1, m4, m6, m7, m8, m9]; exact hθ0

/-- **An `NRAt` component over `TB(θ)` at a mixed label**: `cf(cross) := kPart` (the K-partition
state on `cross`), `cf(stay) := cfStay θ 0` (the two-point law on the stay worlds with the zero
fill — `kPart` cannot serve there, since the `bot` cell does not meet `stay`), a point mass elsewhere.
Source: [[non-responsiveness]] "Axiom NR"; mandate T8; audit r2 B1
Kind: D -/
noncomputable def cfK (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) : CfState TbW ℚ where
  s := tbState θ h0 h1 q q0 q1
  cf A h :=
    if A = tbActEv () Act2.a then kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot
    else if A = tbActEv () Act2.b then cfStay θ h0 h1 0
    else State.dirac h.choose 0
  success A h := by
    split_ifs with hA hB
    · subst hA
      exact kPart_pr_self _ _ _ (tb_cross_cells_pos θ h0 h1 q q0 q1 hθ0 hθ1 hq)
    · subst hB
      rw [cfStay, stateOfU_pr, probOf_twoPt]
      simp [tbActEv]
    · rw [State.dirac_pr, if_pos h.choose_spec]

/-- `cfK` on the `cross` event. Source: none: infrastructure. Kind: L -/
theorem cfK_cf_cross (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (h : (tbActEv () Act2.a).Nonempty) :
    (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h
      = kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot := by
  unfold cfK; simp

/-- `cfK` on the `stay` event. Source: none: infrastructure. Kind: L -/
theorem cfK_cf_stay (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (h : (tbActEv () Act2.b).Nonempty) :
    (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.b) h = cfStay θ h0 h1 0 := by
  unfold cfK
  simp
  intro h'
  exact absurd h' (by decide)

/-- **`NRAt` is inhabited at every mixed label of `TB(θ)`** (T8, audit r2 B1): `cfK` satisfies
Axiom NR with `exo := bot` for `0 < θ < 1`, `0 < q`. The `cross` clauses are the K-partition
state's (`kPart_pr_cell`, `kPart_pr_inter_cell`, `kPart_V_sub`); the `stay` clauses are computed
on the two-point law (the `bot` cell is `stay`-null, so clauses (ii)–(iii) are silent there).
Source: [[non-responsiveness]] "Axiom NR"; mandate T8; audit r2 B1
Kind: N+ (mixed label: both cells positive, both meet `cross`)
Fidelity: exact
Hyps: (a) `0 < θ < 1`; (a) `0 < q` -/
theorem cfK_nrAt (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    NRAt (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq) (tbActEv ()) exoBot := by
  intro act h
  have hpos := tb_cross_cells_pos θ h0 h1 q q0 q1 hθ0 hθ1 hq
  have hreg : SuppRegular (tbState θ h0 h1 q q0 q1) := by
    unfold tbState; exact suppRegular_calibratedState _ _ _ _
  have hs : ∀ X, (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).s.pr X
      = (if (true, Act2.a) ∈ X then θ else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0)) :=
    tbState_pr θ h0 h1 q q0 q1
  have hsV : ∀ X, (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).s.V X
      = ((if (true, Act2.a) ∈ X then θ * (-10) else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q * 10 else 0)))
      / ((if (true, Act2.a) ∈ X then θ else 0) + (1 - θ) *
        ((if (false, Act2.a) ∈ X then q else 0) + (if (false, Act2.b) ∈ X then 1 - q else 0))) :=
    tbState_V θ h0 h1 q q0 q1
  cases act
  · -- cross: the K-partition state
    rw [cfK_cf_cross]
    refine ⟨fun e => kPart_pr_cell _ _ _ hpos e, fun e X _ => ?_, fun e X hXpos => ?_⟩
    · show (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).pr (X ∩ cell exoBot e)
          * (tbState θ h0 h1 q q0 q1).pr (tbActEv () Act2.a ∩ cell exoBot e)
        = (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).pr (cell exoBot e)
          * (tbState θ h0 h1 q q0 q1).pr (X ∩ tbActEv () Act2.a ∩ cell exoBot e)
      rw [kPart_pr_inter_cell _ _ _ hpos e X, kPart_pr_cell _ _ _ hpos e, mul_assoc,
        div_mul_cancel₀ _ (hpos e).ne']
    · exact kPart_V_sub _ hreg _ _ hpos e _
        (Finset.inter_subset_inter Finset.inter_subset_right (Finset.Subset.refl _)) hXpos
  · -- stay: the two-point law with the zero fill
    rw [cfK_cf_stay]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      rw [cfStay, stateOfU_pr, probOf_twoPt, hs]
      cases e <;> simp [cell, exoBot]
    · intro e X hpos'
      cases e
      · rw [cfStay, stateOfU_pr, stateOfU_pr, probOf_twoPt, probOf_twoPt, hs, hs]
        by_cases hX : (false, Act2.b) ∈ X <;> simp [cell, exoBot, tbActEv, hX]
      · exfalso
        rw [hs] at hpos'
        simp [tbActEv, cell, exoBot] at hpos'
    · intro e X hpos'
      cases e
      · have hmem : (false, Act2.b) ∈ X := by
          rw [hs] at hpos'
          by_contra hc
          simp [tbActEv, cell, exoBot, hc] at hpos'
        rw [cfStay, stateOfU_V, sum_twoPt_mul, probOf_twoPt, hsV]
        simp [cell, exoBot, tbActEv, hmem, uFill]
      · exfalso
        rw [hs] at hpos'
        simp [tbActEv, cell, exoBot] at hpos'

/-- `tb_nrAt_V_cross` instantiated: `cfK`'s NR-cf(cross) is `10 − 20θ`.
Source: [[non-responsiveness]] ("NR-cf(cross) `= 10 − 20θ`"); mandate T8; audit r2 B1
Kind: N+ (the shipped inhabitant of `tb_nrAt_V_cross`'s hypothesis package) -/
theorem cfK_V_cross (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (h : (tbActEv () Act2.a).Nonempty) :
    ((cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
      = 10 - 20 * θ :=
  tb_nrAt_V_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq _ rfl (cfK_nrAt θ h0 h1 q q0 q1 hθ0 hθ1 hq) h

/-- `nrcf_eq_deviation` instantiated: `cfK`'s NR-cf(cross) is the deviation
`V_B(C[d ↦ cross])`, and (`nrcf_ne_forcing`) not the forcing `G_q = 10`.
Source: [[non-responsiveness]] ("NR-cf `= V_B(C[d ↦ cross])` … `≠ G_q`"); mandate T8; audit r2 B1
Kind: N+ (the shipped inhabitant of `nrcf_eq_deviation`'s and `nrcf_ne_forcing`'s packages) -/
theorem cfK_nrcf_eq_deviation (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q)
    (h : (tbActEv () Act2.a).Nonempty) :
    ((cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
        = value ((procQ q q0 q1).deviatePure () Act2.a) (tbTheta θ h0 h1) ∧
    ((cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
        ≠ gNode (tbTheta θ h0 h1) (NodePolicy.ofProc (procQ q q0 q1) _) ⟨1, none⟩ Act2.a :=
  ⟨nrcf_eq_deviation θ h0 h1 q q0 q1 hθ0 hθ1 hq _ rfl (cfK_nrAt θ h0 h1 q q0 q1 hθ0 hθ1 hq) h,
    nrcf_ne_forcing θ h0 h1 q q0 q1 hθ0 hθ1 hq _ rfl (cfK_nrAt θ h0 h1 q q0 q1 hθ0 hθ1 hq) h⟩

/-- `cfK`'s supposition of `cross` is support-regular (it is a `kPart`, a mixture).
Source: none: infrastructure. Kind: L -/
theorem cfK_cross_suppRegular (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q)
    (h : (tbActEv () Act2.a).Nonempty) :
    SuppRegular ((cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h) := by
  rw [cfK_cf_cross]; exact suppRegular_kPart _ _ _

/-- `nr_forces_kpart_V'` (the weaker-guard `V`-forcing) instantiated on `cfK`: its full hypothesis
package — `NRAt`, positive cells meeting `cross`, `t.s` and `cf(cross)` support-regular — is
inhabited at every mixed label, and the conclusion is `cfK`'s NR-cf(cross) `=` the K-partition
state's value.
Source: mandate T8; audit r2 adv N3
Kind: N+ -/
theorem cfK_V_cross' (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) (h : (tbActEv () Act2.a).Nonempty) :
    ((cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq).cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a)
      = (kPart (tbState θ h0 h1 q q0 q1) (tbActEv () Act2.a) exoBot).V (tbActEv () Act2.a) := by
  have hreg : SuppRegular (tbState θ h0 h1 q q0 q1) := by
    unfold tbState; exact suppRegular_calibratedState _ _ _ _
  exact nr_forces_kpart_V' (cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq) (tbActEv ()) exoBot
    (cfK_nrAt θ h0 h1 q q0 q1 hθ0 hθ1 hq) hreg Act2.a h
    (cfK_cross_suppRegular θ h0 h1 q q0 q1 hθ0 hθ1 hq h)
    (fun e _ => tb_cross_cells_pos θ h0 h1 q q0 q1 hθ0 hθ1 hq e)

/-- **The hypothesis package of the mixed-label NR headlines is inhabited**, as an existential:
some counterfactual component over `tbState θ q` satisfies Axiom NR with `exo := bot` and
assigns `cross` the value `10 − 20θ`.
Source: mandate T8; audit r2 B1
Kind: N+ -/
theorem nrAt_mixed_inhabited (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq : 0 < q) :
    ∃ t : CfState TbW ℚ, t.s = tbState θ h0 h1 q q0 q1 ∧ NRAt t (tbActEv ()) exoBot ∧
      ∀ h, (t.cf (tbActEv () Act2.a) h).V (tbActEv () Act2.a) = 10 - 20 * θ :=
  ⟨cfK θ h0 h1 q q0 q1 hθ0 hθ1 hq, rfl, cfK_nrAt θ h0 h1 q q0 q1 hθ0 hθ1 hq,
    cfK_V_cross θ h0 h1 q q0 q1 hθ0 hθ1 hq⟩

end tb

/-! ## The recorded direct-effect point with `exo := ℓ` -/

section s1

/-- The lesion as the exogenous designation on `W3`. Source: mandate T8 (`exo := ℓ`). Kind: D -/
def exoL : W3 → Bool := fun x => x 0

/-- Every lesion cell meets every act positively at label `1/2`, `ρ = 1/10` (the point `(e, b, 1)`
has mass `≥ 1/40 · 1/20`). Source: none: infrastructure. Kind: L -/
theorem directState_act_cell_pos (u : W3 → ℚ) (b e : Bool) :
    0 < (directState u).pr (actEvCoord 1 b ∩ cell exoL e) := by
  have hsub : {pt3 e b true} ⊆ actEvCoord 1 b ∩ cell exoL e := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [actEvCoord, cell, exoL]
  refine lt_of_lt_of_le ?_ (probOf_mono _ hsub)
  rw [probOf_singleton, directState, s1State_w, s1Fam_nu_singleton]
  cases b <;> cases e <;> norm_num [procHalf, FinDistr.bool, dRateQ]

/-- **The K-partition component at the recorded direct-effect point** with `exo := ℓ`: `cf(b) :=
kPart (directState u) {m = b} ℓ` for both acts (`kPartCf`).
Source: mandate T8 (the inhabitant of `nr_evidential_at_recording`); audit r2 B1
Kind: D -/
noncomputable def cfKS1 (u : W3 → ℚ) : CfState W3 ℚ :=
  kPartCf (directState u) (s1ActEv ()) exoL (fun b e => directState_act_cell_pos u b e)

/-- `cfKS1` on an act event. Source: none: infrastructure. Kind: L -/
theorem cfKS1_cf (u : W3 → ℚ) (b : Bool) (h : (s1ActEv () b).Nonempty) :
    (cfKS1 u).cf (s1ActEv () b) h = kPart (directState u) (actEvCoord 1 b) exoL :=
  kPartCf_cf _ _ _ _ b h

/-- **`NRAt` is inhabited at the recorded direct-effect point with `exo := ℓ`** (audit r2 B1).
Source: [[non-responsiveness]] "Axiom NR"; mandate T8
Kind: N+ (label `1/2`, `ρ = 1/10`, every cell × act positive)
Fidelity: exact -/
theorem cfKS1_nrAt (u : W3 → ℚ) : NRAt (cfKS1 u) (s1ActEv ()) exoL :=
  kPartCf_nrAt _ (by unfold directState s1State; exact suppRegular_calibratedState _ _ _ _) _ _ _

/-- **`nr_evidential_at_recording` instantiated** on `cfKS1` (audit r2 B1): at the recorded
direct-effect point, for every act, `cfKS1`'s supposition of `b` has the act-conditional law
`P(X ∧ b)/P(b)` — the hypothesis package (recording, `ν(⊤) > 0`, clause 1, pre-query lesion
cells, `NRAt`, `b ∈ A_d^+`) is inhabited, and the theorem's conclusion is a fact about a concrete
component.
Source: [[non-responsiveness]] "Consistency with cf = conditional"; mandate T8; audit r2 B1
Kind: N+
Fidelity: exact -/
theorem nr_evidential_cfKS1 (u : W3 → ℚ) (b : Bool) (h : (s1ActEv () b).Nonempty)
    (X : Finset W3) :
    ((cfKS1 u).cf (s1ActEv () b) h).pr X
      = (directState u).pr (X ∩ s1ActEv () b) / (directState u).pr (s1ActEv () b) := by
  have hb : b ∈ APlus (fun _ => directState u) s1ActEv () := by
    rw [directState_aPlus]; exact Finset.mem_univ b
  rw [nr_evidential_at_recording s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf).1 exoL
    (fun e => s1Fam_preQuery_ell _ _ _ _ _ _ u procHalf e) (cfKS1 u) rfl (cfKS1_nrAt u) b hb h X,
    jeffreyCond_pr]

end s1

end Cleanroom.Decision.DpCausalConsist
