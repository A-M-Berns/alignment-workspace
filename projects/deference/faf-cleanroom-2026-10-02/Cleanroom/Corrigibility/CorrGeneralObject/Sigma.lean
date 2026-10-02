import Cleanroom.Corrigibility.CorrGeneralObject.Defs
import Cleanroom.Udt.UdtSupercondition.DZ
import Cleanroom.Udt.UdtSupercondition.Witnesses

/-!
# corr-general-object — T11: σ-algebra change through `udt-supercondition`'s repaired Thm 2.4

The theorem is `udt-supercondition`'s `commonInfo_condModel_iff` (SC Thm 2.4 **repaired**: a
compatible model exists iff bounded density **and** every `C`-positive point is in the range of
`c′`). Nothing is re-proved; the source's instance (S13, script (F)) is instantiated:

* **(a) no catch-all.** `Ω = Fin 3` (`o, s, *`) with `P = (1/2, 1/2, 0)`, `Ω' = Fin 4`
  (`o, s, θ', *'`) with `Q = (1/5, 1/5, 1/2, 1/10)`, `C = Fin 3`, `c = id`, `c' = (0, 1, 2, 2)`:
  `C₂ Q = (1/5, 1/5, 3/5)`, `C₁ P = (1/2, 1/2, 0)`, no bounded density, hence no compatible model
  (`no_catchAll_no_model`).
* **(b) catch-all `η = 1/10`.** `P = (9/20, 9/20, 1/10)`: density bound `6` (`3/5 ≤ 6 · 1/10`),
  the range clause holds, so a compatible model exists (`catchAll_model_exists`, the theorem's
  `⇐`).
* **(c) CE4.** The catch-all's *mass* moves under ordinary evidence: the likelihood
  `(1/10, 1/10, 9/10)` takes `η` from `1/10` to `1/2` (`catchAll_mass_moves`, `postPush`
  arithmetic); its *split* into `θ', *'` is not an event of `Ω` (docstring).

**Finding against S12** (recorded in the findings): "a `Ĉ`-compatible model iff `C' ≪ C` with
bounded density" omits the range clause the repair found necessary (`thm24_sufficiency_refuted`);
the source's own instances satisfy it (severity local).

Sources: [[general-object-final]] S12, S13, P6, (F), CE4; [[corr-wf14b-inventory]] 012;
`udt-supercondition` `commonInfo_condModel_iff`, `thm24_sufficiency_refuted`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Udt.UdtSupercondition
open Finset hiding expect
open scoped ENNReal
open Set

noncomputable section

/-- The no-catch-all prior `(1/2, 1/2, 0)` on `(o, s, *)`.
Source: [[general-object-final]] S13, script (F). Kind: D. Fidelity: exact -/
def sigP0 : PMF (Fin 3) :=
  pmfOfReal ![1/2, 1/2, 0] (fun i => by fin_cases i <;> norm_num) (by simp [Fin.sum_univ_three]; norm_num)

/-- The catch-all prior `(9/20, 9/20, 1/10)` on `(o, s, *)`.
Source: [[general-object-final]] S13, P6. Kind: D. Fidelity: exact -/
def sigP1 : PMF (Fin 3) :=
  pmfOfReal ![9/20, 9/20, 1/10] (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

/-- The expanded target `(1/5, 1/5, 1/2, 1/10)` on `(o, s, θ', *')`.
Source: [[general-object-final]] S13, P6. Kind: D. Fidelity: exact -/
def sigQ : PMF (Fin 4) :=
  pmfOfReal ![1/5, 1/5, 1/2, 1/10] (fun i => by fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)

/-- The common information: shared language `(o, s, *)`, `c = id`, `c' = (0, 1, 2, 2)` (both
new hypotheses refine the catch-all).
Source: [[general-object-final]] D12, S13 (reading (i): shared value cells)
Kind: D
Fidelity: exact -/
def sigCI : CommonInfo (Fin 3) (Fin 4) := { C := Fin 3, c := id, c' := ![0, 1, 2, 2] }

/-- `C₁ P = P` for `c = id`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sigCI_C₁ (P : PMF (Fin 3)) : sigCI.C₁ P = P := PMF.map_id P

/-- `C₂ Q` as a `PMF (Fin 3)` (the projection `sigCI.C` blocks numerals and `fin_cases`, so the
shared language is carried as `Fin 3` explicitly). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def sigC₂ : PMF (Fin 3) := sigQ.map (![0, 1, 2, 2] : Fin 4 → Fin 3)

/-- `C₂ Q` is `sigC₂`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sigCI_C₂_eq : sigCI.C₂ sigQ = sigC₂ := rfl

/-- `C₂ Q = (1/5, 1/5, 3/5)`. Source: [[general-object-final]] P6. Kind: L. Fidelity: exact -/
theorem sigC₂_apply (y : Fin 3) : sigC₂ y = ENNReal.ofReal (![1/5, 1/5, 3/5] y) := by
  unfold sigC₂
  rw [map_apply_eq_mass, mass_fintype, Fin.sum_univ_four]
  fin_cases y
  · simp [indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, sigQ, pmfOfReal_apply]
  · simp [indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, sigQ, pmfOfReal_apply]
  · simp only [indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Matrix.cons_val,
      Fin.isValue, Fin.reduceEq, ite_true, ite_false, sigQ, pmfOfReal_apply, zero_add, add_zero,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    exact ofReal_add_eq (by norm_num) (by norm_num) (by norm_num)

/-- **T11(a), N+ (impossibility instance): without a catch-all no compatible model exists** — the
shared cell `*` has `P`-mass `0` and `Q`-mass `3/5`, so no bounded density, so by the repaired
Thm 2.4 (its `⇒`, contrapositively) no `Ĉ`-compatible conditioning model. The genuine `⇐`
instance is `catchAll_model_exists`.
Source: [[general-object-final]] S13 (reading (i)), P6, script (F); `commonInfo_condModel_iff`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem no_catchAll_no_model : ¬ ∃ m : CondModel sigP0 sigQ, Compatible m sigCI := by
  rw [commonInfo_condModel_iff]
  rintro ⟨⟨B, _, hBD⟩, _⟩
  rw [sigCI_C₂_eq, sigCI_C₁] at hBD
  have key : @BoundedDensity (Fin 3) sigC₂ sigP0 B := hBD
  have h := key 2
  rw [sigC₂_apply] at h
  simp [sigP0, pmfOfReal_apply] at h <;> norm_num at h

/-- **T11(b), N+: with a catch-all of mass `1/10` a compatible model exists** — density bound `6`
(`1/5 ≤ 6 · 9/20`, `3/5 ≤ 6 · 1/10`) and every `C`-positive point is in the range of `c'`, so the
repaired theorem's `⇐` gives the model (the construction `diagModel` is `udt-supercondition`'s).
Source: [[general-object-final]] S13, P6 ("`B = 6`, constructed `L` has … posterior `Q`");
`commonInfo_condModel_iff`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem catchAll_model_exists : ∃ m : CondModel sigP1 sigQ, Compatible m sigCI := by
  rw [commonInfo_condModel_iff]
  refine ⟨⟨6, by simp, ?_⟩, ?_⟩
  · rw [sigCI_C₂_eq, sigCI_C₁]
    have key : @BoundedDensity (Fin 3) sigC₂ sigP1 6 := by
      intro y
      rw [sigC₂_apply]
      simp only [sigP1, pmfOfReal_apply]
      rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 from by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      fin_cases y <;> simp <;> norm_num
    exact key
  · have key : ∀ y : Fin 3, y ∈ Set.range sigCI.c' := by
      intro y
      fin_cases y
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    exact fun y _ => key y

/-- The catch-all prior as a FAF `Distr` (for the CE4 arithmetic).
Source: [[general-object-final]] CE4. Kind: D. Fidelity: exact -/
def ce4P : Distr (Fin 3) where
  mass := ![9/20, 9/20, 1/10]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- CE4's likelihood of the feedback "neither opiates nor stimulants": `(1/10, 1/10, 9/10)`.
Source: [[general-object-final]] CE4. Kind: D. Fidelity: exact -/
def ce4k : Fin 3 → ℝ := ![1/10, 1/10, 9/10]

/-- CE4's likelihood is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ce4k_nonneg : ∀ i, 0 ≤ ce4k i := fun i => by fin_cases i <;> norm_num [ce4k]

/-- CE4's feedback has push mass `9/50 > 0`. Source: [[general-object-final]] CE4. Kind: L.
Fidelity: exact -/
theorem ce4_pushMass : pushMass ce4P ce4k = 9/50 := by
  simp [pushMass, ce4P, ce4k, Fin.sum_univ_three]; norm_num

/-- The positivity guard for CE4's `postPush`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ce4_pushMass_pos : 0 < pushMass ce4P ce4k := by rw [ce4_pushMass]; norm_num

/-- **T11(c), CE4: the catch-all's mass moves under ordinary evidence** — the feedback takes
`η = P(*)` from `1/10` to `1/2`. What no evidence in `Ω` can do is *split* `*` into `θ', *'`:
the split is private to the new ontology and unjudged by `P_t` (no theorem; the split is not an
event of `Ω`).
Source: [[general-object-final]] S13, CE4, P6
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem catchAll_mass_moves :
    ce4P.mass 2 = 1/10 ∧ pushMass ce4P ce4k = 9/50 ∧
      (postPush ce4P ce4k ce4k_nonneg ce4_pushMass_pos).mass 2 = 1/2 := by
  refine ⟨by simp [ce4P], ce4_pushMass, ?_⟩
  rw [postPush_mass]
  simp [pushMass, ce4P, ce4k, Fin.sum_univ_three]; norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
