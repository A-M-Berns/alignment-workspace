import Cleanroom.Decision.DpCausalConsist.Mixture
import Cleanroom.Decision.DpCausalConsist.Witness3

/-!
# `dp-causal-consist`: `labCdt` and a literal instance of the mixture corollary (T5, repair round 2)

* `LabCdt π Γ Γ₀`: the prior is supported on the single structure `Γ₀` — the mandate's
  "`π = pure G*` where `G*` is the tree's mechanism graph". `mixState_pr_of_labCdt`,
  `mixState_V_of_labCdt`: the mixed supposition then *is* `cf^{Γ₀}` on every event (law and
  desirability; the desirability case needs the fact that `expState` has value `0` on a null
  event, `expState_V_of_pr_eq_zero`, since the mixture reads `0/0 = 0` there);
  `cdtpi_of_labCdt`: `CDT_π = argmax_a cf^{Γ₀}(a).V(a)`.
* `mechanismDAG := gColl`, `mechanismStructure := sColl`: the mechanism graph of the direct-effect
  tree (`ℓ` a root, `m` drawn from `C(d)` reading nothing, `k` reading `ℓ` and `m`), compatible
  with the calibrated law (`sColl_isFor`); `direct_cdtpi_labCdt` is the lab CDT on it.
* `direct_tcdt_mix_iff_tedt_LMK`: **a literal instance of `tcdt_mix_iff_tedt`** (`n = 1`, the point
  mass on the temporal structure `sLMK`, every hypothesis as in `direct_tcdt_iff_tedt_LMK`) — audit
  r2 adv N5 observed that no instance of the mixture theorems was shipped (the `n = 1` witness
  was "in substance" only, `mixState (pure 0) (fun _ => cfG sLMK …)` not being syntactically
  `cfG sLMK …`). The hypothesis package of the mixture theorems is now inhabited in Lean.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

section labCdt

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `expState` has value `0` on a null event (the quotient `0/0`). Source: none: infrastructure.
Kind: L -/
theorem expState_V_of_pr_eq_zero (Q : Distr Ω) (u : Ω → ℝ) (X : Finset Ω)
    (h : (expState Q u).pr X = 0) : (expState Q u).V X = 0 := by
  rw [expState_V]
  have h' : ∑ x ∈ X, Q.mass x = 0 := by simpa [State.pr, probOf, expState] using h
  rw [h', div_zero]

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]

/-- **`labCdt`**: the prior over structures is supported on the single structure `Γ₀` (the mandate's
"`π = pure G*`", with the indexing left free).
Source: [[learning-cdt-renderings]] Definition 26 context ("lab CDT: the prior is the point mass on
the tree's mechanism graph"); mandate T5 (`labCdt`)
Kind: D
Fidelity: exact (support condition in place of literal equality with `pure`) -/
def LabCdt {n : ℕ} (π : FinDistr ℝ (Fin n)) (Γ : Fin n → CausalStructure Val)
    (Γ₀ : CausalStructure Val) : Prop :=
  ∀ i, 0 < π.w i → Γ i = Γ₀

/-- Under `labCdt` the mixed supposition's law is `cf^{Γ₀}`'s. Source: none: infrastructure. Kind: L -/
theorem mixState_pr_of_labCdt {n : ℕ} (π : FinDistr ℝ (Fin n)) (Γ : Fin n → CausalStructure Val)
    (Γ₀ : CausalStructure Val) (h : LabCdt π Γ Γ₀) (m : V) (u : Pt Val → ℝ) (a : Val m)
    (X : Finset (Pt Val)) :
    (mixState π fun i => cfG (Γ i) m u a).pr X = (cfG Γ₀ m u a).pr X := by
  rw [mixState_pr]
  have hterm : ∀ i, π.w i * (cfG (Γ i) m u a).pr X = π.w i * (cfG Γ₀ m u a).pr X := by
    intro i
    rcases (π.nonneg i).lt_or_eq with hi | hi
    · rw [h i hi]
    · rw [← hi, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, π.sum_one, one_mul]

/-- Under `labCdt` the mixed supposition's desirability is `cf^{Γ₀}`'s on every event (on a null
event both are `0`). Source: none: infrastructure. Kind: L -/
theorem mixState_V_of_labCdt {n : ℕ} (π : FinDistr ℝ (Fin n)) (Γ : Fin n → CausalStructure Val)
    (Γ₀ : CausalStructure Val) (h : LabCdt π Γ Γ₀) (m : V) (u : Pt Val → ℝ) (a : Val m)
    (X : Finset (Pt Val)) :
    (mixState π fun i => cfG (Γ i) m u a).V X = (cfG Γ₀ m u a).V X := by
  rw [mixState_V_of_suppRegular π _ (fun i => by unfold cfG; exact expState_suppRegular _ _)]
  have hterm : ∀ i, π.w i * (cfG (Γ i) m u a).pr X * (cfG (Γ i) m u a).V X
      = π.w i * ((cfG Γ₀ m u a).pr X * (cfG Γ₀ m u a).V X) := by
    intro i
    rcases (π.nonneg i).lt_or_eq with hi | hi
    · rw [h i hi, mul_assoc]
    · rw [← hi, zero_mul, zero_mul, zero_mul]
  have hterm' : ∀ i, π.w i * (cfG (Γ i) m u a).pr X = π.w i * (cfG Γ₀ m u a).pr X := by
    intro i
    rcases (π.nonneg i).lt_or_eq with hi | hi
    · rw [h i hi]
    · rw [← hi, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_congr rfl fun i _ => hterm' i,
    ← Finset.sum_mul, ← Finset.sum_mul, π.sum_one, one_mul, one_mul]
  rcases eq_or_ne ((cfG Γ₀ m u a).pr X) 0 with hp | hp
  · rw [hp, zero_mul, zero_div]
    unfold cfG at hp ⊢
    exact (expState_V_of_pr_eq_zero _ _ _ hp).symm
  · exact mul_div_cancel_left₀ _ hp

/-- **The lab CDT**: under `labCdt`, `CDT_π` is the causal argmax of `cf^{Γ₀}` alone.
Source: [[learning-cdt-renderings]] Definition 26 (the point-mass prior); mandate T5 (`labCdt`)
Kind: C
Fidelity: exact
Hyps: (a) `LabCdt π Γ Γ₀` -/
theorem cdtpi_of_labCdt {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (π : FinDistr ℝ (Fin n))
    (Γ : Fin n → CausalStructure Val) (Γ₀ : CausalStructure Val) (h : LabCdt π Γ Γ₀) (m : V)
    (u : Pt Val → ℝ) (e : A → Val m) (actEv : A → Finset (Pt Val)) :
    CDTpi π Γ m u e actEv = argmaxAll fun a => (cfG Γ₀ m u (e a)).V (actEv a) := by
  unfold CDTpi
  congr 1
  funext a
  exact mixState_V_of_labCdt π Γ Γ₀ h m u (e a) (actEv a)

end labCdt

section direct

/-- **The mechanism graph of the direct-effect tree**: `ℓ` a root, `m` drawn from `C(d)` reading
nothing, `k` reading `ℓ` and `m` — `gColl` (`ℓ → k ← m`).
Source: mandate T5 ("`mechanismDAG` for `s1Tree`": the tree's own mechanism graph)
Kind: D
Fidelity: exact for the direct-effect member `directTree` (for the `τ = 0` member the edge `m → k`
carries a CPD constant in `m`, so the same graph is compatible) -/
def mechanismDAG : Digraph (Fin 3) := gColl

/-- The mechanism structure: `gColl` with the direct-effect CPD, compatible with the calibrated law
at label `1/2` (`sColl_isFor`). Source: mandate T5. Kind: D -/
noncomputable def mechanismStructure : CausalStructure (fun _ : Fin 3 => Bool) := sColl

/-- `mechanismStructure`'s graph is `mechanismDAG`. Source: none: infrastructure. Kind: L -/
theorem mechanismStructure_G : mechanismStructure.G = mechanismDAG := rfl

/-- **The lab CDT on the direct-effect tree** is the causal argmax of `cf^{sColl}`: `labCdt` holds
for the point mass on `sColl`, so `CDT_π` collapses to the single structure's argmax; by
`direct_tcdt_iff_tedt` its verdict then agrees with `T_EDT` under the proviso.
Source: mandate T5 (`labCdt`; "`direct_collapse` is its `n = 1` case")
Kind: C
Fidelity: exact -/
theorem direct_cdtpi_labCdt (u : W3 → ℚ) :
    CDTpi (FinDistr.pure (0 : Fin 1)) (fun _ => mechanismStructure) 1 (fun x => (u x : ℝ)) id
        (s1ActEv ())
      = argmaxAll fun a => (cfG sColl 1 (fun x => (u x : ℝ)) a).V (s1ActEv () a) :=
  cdtpi_of_labCdt _ _ _ (fun _ _ => rfl) _ _ _ _

/-- **A literal instance of `tcdt_mix_iff_tedt`** (audit r2 adv N5): on the direct-effect tree at
label `1/2`, with `n = 1` and the point mass on the temporal structure `sLMK` (parent cells the
lesion cells, discharged by `s1Fam_preQuery_ell`), `T_CDT` for the mixed supposition `↔ T_EDT` for
every supervenient payoff — the hypothesis package of the mixture corollary is inhabited.
Source: [[learning-cdt-renderings]] "Corollary 3.1 restated"; mandate T5; audit r2 adv N5
Kind: N+ (the `n = 1` instance; label `1/2`, `ρ = 1/10`, `γ = (1/20, 3/5)`, `τ = 1/5`)
Fidelity: exact -/
theorem direct_tcdt_mix_iff_tedt_LMK (u : W3 → ℚ) :
    TCdtAt (fun _ => directState u) s1ActEv procHalf ()
        (fun a => mixState (FinDistr.pure (0 : Fin 1))
          fun _ : Fin 1 => cfG sLMK 1 (fun x => (u x : ℝ)) (id a))
      ↔ TEdtAt (fun _ => directState u) s1ActEv procHalf () := by
  refine tcdt_mix_iff_tedt s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) (FinDistr.pure 0) (fun _ => sLMK)
    (fun _ => by rw [directTree_toDistr]; exact sLMK_isFor)
    (fun _ c => by
      rw [parentCell_sLMK c]
      exact s1Fam_preQuery_ell _ _ _ _ _ _ u procHalf _)
    u (s1Fam_payoff _ _ _ _ _ _ u) ?_
  rw [directState_aPlus, Finset.inter_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
    (fun a => (mixState (FinDistr.pure (0 : Fin 1))
      fun _ : Fin 1 => cfG sLMK 1 (fun x => (u x : ℝ)) (id a)).V (s1ActEv () a))
    Finset.univ_nonempty
  exact ⟨a, (mem_argmaxAll _ a).mpr fun b => ha b (Finset.mem_univ b)⟩

end direct

end Cleanroom.Decision.DpCausalConsist
