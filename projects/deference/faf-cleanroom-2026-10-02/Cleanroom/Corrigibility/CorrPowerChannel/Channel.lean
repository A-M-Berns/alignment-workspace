import Cleanroom.Corrigibility.CorrGeneralObject.Endorse
import Cleanroom.Corrigibility.CorrPowerChannel.Evpi

/-!
# `corr-power-channel` — T8: the Channel package — reach equals the anticipated set

* **Objects (D).** An `Anticipation Ω I` is a kernel `K : Ω → I → ℝ` (rows nonnegative, summing to
  one: exactly one datum "believe `ρ i`" is announced) with targets `ρ : I → Distr Ω`. The joint
  law is `corr-reflect-frames`' `pushJoint P.mass K`; function-form endorsement `(Mart)` is
  `ReflectiveFor P.mass K (fun i => (ρ i).mass)` (cited, not redefined). The push mass of a datum is
  `corr-general-object`'s `pushMass`, its conditional `postPush` under the guard
  `0 < pushMass` (a target of zero push mass has no conditional — the guard fails; no junk
  conditional is defined). **Reach through data** is the set of those conditionals.
* **(a) `dataReach_eq_anticipated`** (load-bearing 5): under `(Mart)`, the reach is exactly the set
  of anticipated targets of positive push mass — the datum "believe `ρ i`" lands on `ρ i`.
  Converse `exists_anticipation_of_barycentre`: every barycentric representation `P = ∑ m i • ρ i`
  is realised by an anticipation (imported from `corr-general-object`'s barycentre theorem, not
  re-proved). Witness R2 (`r2_reach`): `P = (1/2, 1/3, 1/6)`, three anticipated targets with
  masses `(1/5, 1/5, 3/5)`, each reached exactly; `(0, 1/2, 1/2)` not in the reach.
* **(b) Diaconis–Zabell per target** (`dz_two_target`): for `ρ ≪ P`, `ρ ≠ P`, the two-target
  family `{ρ, (P − λρ)/(1 − λ)}` with `λ = 1 / max_{supp ρ} (ρ/P) ∈ (0, 1)` is a valid anticipation
  satisfying `(Mart)` — one anticipation per target, not one reaching all of `Δ(Ω)` (S1's point).
* **(c) Grip, reach, erosion (D only)**: `SubstrateModel`, `reachSet`, `ErodesReach`, one N−
  witness. The landing probability `Γ` is T9's parameter (`Grip.lean`); `Γ(𝒬)` needs the joint
  process and is not defined here.

Sources: `research/corrigibility/workflow-2026-09-14b/develop/channel-final.md` (cited as
channel-final.md) D9–D11 (l. 41–45), S1 (l. 65), P1 (l. 99); `channel-scratch/repair_checks.py`
R2; corr-wf14b-027, 028 (028 duplicates corr-wf14b-003(ii): formalized once in
`corr-general-object`, cited here).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Cleanroom.Corrigibility.CorrGeneralObject (pushMass postPush postPush_mass Endorsed
  endorsed_iff_postPush_eq AbsCont exists_reflectiveFor_of_barycentre barycentre_of_reflectiveFor)
open Cleanroom.Corrigibility.CorrReflectFrames (ReflectiveFor pushJoint)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω I : Type} [Fintype Ω] [DecidableEq Ω] [Fintype I]

/-- **An anticipation**: a kernel `K ω i = P(E_{ρ i} | ω)` with nonnegative rows summing to one
(exactly one datum is announced) and the anticipated targets `ρ i`.
Source: channel-final.md D9 (l. 41, "a class `𝒬` of target credences"), P1 (l. 99)
Kind: D
Fidelity: exact (finite anticipated set, as P1) -/
structure Anticipation (Ω I : Type) [Fintype Ω] [Fintype I] where
  /-- the announcement kernel -/
  K : Ω → I → ℝ
  /-- the anticipated targets -/
  ρ : I → Distr Ω
  /-- rows are nonnegative -/
  K_nonneg : ∀ ω i, 0 ≤ K ω i
  /-- exactly one datum is announced -/
  K_sum : ∀ ω, ∑ i, K ω i = 1

namespace Anticipation

variable (𝒜 : Anticipation Ω I) (P : Distr Ω)

/-- The column `ω ↦ K ω i` of the kernel: the push toward target `i`.
Source: none: infrastructure. Kind: D. Fidelity: exact -/
abbrev col (i : I) : Ω → ℝ := fun ω => 𝒜.K ω i

/-- The push mass `P(E_{ρ i}) = ∑ ω, P ω K ω i` of datum `i` (`corr-general-object`'s
`pushMass`).
Source: channel-final.md P1 (l. 99, "`P_t(E_{ρ_k})`"). Kind: D. Fidelity: exact -/
abbrev pmass (i : I) : ℝ := pushMass P (𝒜.col i)

/-- **The joint law of the Channel**: `J(ω, i) = P ω · K ω i` (`corr-reflect-frames`' `pushJoint`).
Source: channel-final.md D9 (l. 41); [[corr-power-channel-mandate]] T8 ("the Channel as the joint
law")
Kind: D
Fidelity: exact -/
def joint : Ω → I → ℝ := pushJoint P.mass 𝒜.K

/-- **`(Mart)` with function-form endorsement**: `corr-reflect-frames`' `ReflectiveFor` — for every
datum of positive push mass, the conditional on it is its target (product form).
Source: channel-final.md S1 (l. 65, "(Mart) with function-form endorsement"), P1 (l. 99)
Kind: D
Fidelity: exact (cited: `ReflectiveFor`, not redefined) -/
def Mart : Prop := ReflectiveFor P.mass 𝒜.K (fun i => (𝒜.ρ i).mass)

/-- **Reach through data**: the credences the data channel can land on — the conditionals
`P(· | E_{ρ i})` of the data of positive push mass. A datum of zero push mass has no conditional
and contributes nothing (the guard `0 < pmass` is part of the definition).
Source: channel-final.md D9 (l. 41, "Their reach `M^H_t`"), S1 (l. 65)
Kind: D
Fidelity: exact (through-data form over a finite anticipation) -/
def dataReach : Set (Distr Ω) :=
  {Q | ∃ i, ∃ h : 0 < 𝒜.pmass P i, Q = postPush P (𝒜.col i) (fun ω => 𝒜.K_nonneg ω i) h}

/-- **The anticipated set** of positive push mass: `{ρ i | P(E_{ρ i}) > 0}`.
Source: channel-final.md S1 (l. 65, "iff `ρ` is anticipated")
Kind: D
Fidelity: exact -/
def anticipated : Set (Distr Ω) := {Q | ∃ i, 0 < 𝒜.pmass P i ∧ Q = 𝒜.ρ i}

/-- **S1: reach through data equals the anticipated set** (under `(Mart)`): the datum "believe
`ρ i`" lands exactly on `ρ i` for every anticipated target of positive push mass, and on nothing
else. The mechanism is `corr-general-object`'s `endorsed_iff_postPush_eq`: `(Mart)` at `i` *is*
`Endorsed P (col i) (ρ i)`, which under the guard says the conditional is `ρ i`. **Kind L** (repair
round 1): the proof is two applications of that imported iff, one per inclusion — the content is
`corr-general-object`'s; S1's "[derived]" sentence is a definitional unpacking of function-form
endorsement (F-17). This package's own contribution to S1 is `dz_two_target`.
Source: channel-final.md S1 (l. 65), P1 (l. 99); corr-wf14b-027
Kind: L
Fidelity: exact
Hyps: (a) `(Mart)`, named -/
theorem dataReach_eq_anticipated (h : 𝒜.Mart P) : 𝒜.dataReach P = 𝒜.anticipated P := by
  ext Q
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (endorsed_iff_postPush_eq P (fun ω => 𝒜.K_nonneg ω i) hi (𝒜.ρ i)).1
      (fun ω => h i hi ω)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, ((endorsed_iff_postPush_eq P (fun ω => 𝒜.K_nonneg ω i) hi (𝒜.ρ i)).1
      (fun ω => h i hi ω)).symm⟩

/-- Under `(Mart)`, `P` is the barycentre of the targets under the push masses
(`corr-general-object`'s `barycentre_of_reflectiveFor`).
Source: channel-final.md P1 (l. 99, "(Mart) `∑_k m_k ρ_k = P_t`")
Kind: L
Fidelity: exact
Hyps: (a) `(Mart)` -/
theorem barycentre_of_mart (h : 𝒜.Mart P) : ∀ ω, P.mass ω = ∑ i, 𝒜.pmass P i * (𝒜.ρ i).mass ω :=
  barycentre_of_reflectiveFor P 𝒜.K 𝒜.K_nonneg 𝒜.K_sum 𝒜.ρ h

end Anticipation

/-- **The converse construction (the barycentre theorem, `⇐`)**: for masses `m ≥ 0` with
`P = ∑ m i • ρ i`, there is an anticipation with targets `ρ`, push masses `m`, satisfying `(Mart)`;
its reach is `{ρ i | 0 < m i}`. Imported from `corr-general-object`
(`exists_reflectiveFor_of_barycentre`), not re-proved.
Source: channel-final.md P1 (l. 99, "put `P_t(E_{ρ_k} | ω) = m_k ρ_k(ω)/P_t(ω)`"); corr-wf14b-028
(duplicate of corr-wf14b-003(ii), `corr-general-object` T2)
Kind: C
Fidelity: exact
Hyps: (a) `m ≥ 0` and the barycentric identity -/
theorem exists_anticipation_of_barycentre (P : Distr Ω) (ρ : I → Distr Ω) (m : I → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hb : ∀ ω, P.mass ω = ∑ i, m i * (ρ i).mass ω) :
    ∃ 𝒜 : Anticipation Ω I, 𝒜.ρ = ρ ∧ (∀ i, 𝒜.pmass P i = m i) ∧ 𝒜.Mart P ∧
      𝒜.dataReach P = {Q | ∃ i, 0 < m i ∧ Q = ρ i} := by
  obtain ⟨K, hK0, hK1, hmass, hR⟩ := exists_reflectiveFor_of_barycentre P ρ m hm hb
  refine ⟨⟨K, ρ, hK0, hK1⟩, rfl, hmass, hR, ?_⟩
  rw [Anticipation.dataReach_eq_anticipated ⟨K, ρ, hK0, hK1⟩ P hR]
  ext Q
  simp only [Anticipation.anticipated, Set.mem_setOf_eq, Anticipation.pmass, Anticipation.col,
    pushMass, hmass]

/-! ## Witness R2 -/

/-- A `Distr (Fin 3)` from three nonnegative masses summing to one.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def distr3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) : Distr (Fin 3) where
  mass := ![a, b, c]
  nonneg := fun s => by
    fin_cases s
    · exact ha
    · exact hb
    · exact hc
  sum_eq_one := by simp [Fin.sum_univ_three, h]

/-- Mass of `distr3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem distr3_mass (a b c : ℝ) (ha hb hc h) : (distr3 a b c ha hb hc h).mass = ![a, b, c] := rfl

/-- R2's prior `P = (1/2, 1/3, 1/6)`. Source: `repair_checks.py` R2. Kind: D. Fidelity: n/a -/
def r2P : Distr (Fin 3) := distr3 (1 / 2) (1 / 3) (1 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- R2's targets `(3/4, 1/6, 1/12)`, `(1/4, 1/2, 1/4)`, `P`. Source: `repair_checks.py` R2.
Kind: D. Fidelity: n/a -/
def r2ρ : Fin 3 → Distr (Fin 3) :=
  ![distr3 (3 / 4) (1 / 6) (1 / 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    distr3 (1 / 4) (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num), r2P]

/-- R2's kernel `K ω i = m i ρ_i(ω)/P(ω)` with masses `(1/5, 1/5, 3/5)`: rows
`(3/10, 1/10, 3/5)`, `(1/10, 3/10, 3/5)`, `(1/10, 3/10, 3/5)`.
Source: `repair_checks.py` R2. Kind: D. Fidelity: n/a -/
def r2K : Fin 3 → Fin 3 → ℝ := ![![3 / 10, 1 / 10, 3 / 5], ![1 / 10, 3 / 10, 3 / 5], ![1 / 10, 3 / 10, 3 / 5]]

/-- R2's anticipation. Source: `repair_checks.py` R2. Kind: D. Fidelity: n/a -/
def r2A : Anticipation (Fin 3) (Fin 3) where
  K := r2K
  ρ := r2ρ
  K_nonneg := fun ω i => by fin_cases ω <;> fin_cases i <;> simp [r2K] <;> norm_num
  K_sum := fun ω => by fin_cases ω <;> simp [r2K, Fin.sum_univ_three] <;> norm_num

/-- The unanticipated target `(0, 1/2, 1/2)`. Source: `repair_checks.py` R2. Kind: D. Fidelity: n/a -/
def r2Out : Distr (Fin 3) := distr3 0 (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num) (by norm_num)

/-- **R2 (N+): reach equals the anticipated set, instantiated.** `(Mart)` holds for `r2A`; every
push mass is positive (`1/5, 1/5, 3/5`); so the reach is `{ρ₀, ρ₁, P}` — each target reached
exactly — and `(0, 1/2, 1/2)` is not in the reach (every reached credence is some `ρ i`, and all
three give `ω = 0` positive mass).
Source: channel-final.md S1 (l. 65, "R2: three anticipated targets each reached exactly;
`(0, 1/2, 1/2)` not"); `repair_checks.py` R2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem r2_reach :
    r2A.Mart r2P ∧ (∀ i, 0 < r2A.pmass r2P i) ∧
      r2A.dataReach r2P = {Q | ∃ i, Q = r2ρ i} ∧ r2Out ∉ r2A.dataReach r2P := by
  have hmass : ∀ i, r2A.pmass r2P i = (![1 / 5, 1 / 5, 3 / 5] : Fin 3 → ℝ) i := by
    intro i
    fin_cases i <;> simp [Anticipation.pmass, Anticipation.col, pushMass, r2A, r2K, r2P,
      Fin.sum_univ_three] <;> norm_num
  have hmart : r2A.Mart r2P := by
    intro i hi ω
    fin_cases i <;> fin_cases ω <;>
      simp [Anticipation.Mart, r2A, r2K, r2P, r2ρ, Fin.sum_univ_three] <;> norm_num
  have hpos : ∀ i, 0 < r2A.pmass r2P i := by
    intro i; rw [hmass]; fin_cases i <;> norm_num
  refine ⟨hmart, hpos, ?_, ?_⟩
  · rw [Anticipation.dataReach_eq_anticipated _ _ hmart]
    ext Q
    simp only [Anticipation.anticipated, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, hpos i, rfl⟩
  · rw [Anticipation.dataReach_eq_anticipated _ _ hmart]
    rintro ⟨i, _, hQ⟩
    have h0 := congrArg (fun R : Distr (Fin 3) => R.mass 0) hQ
    fin_cases i <;> simp [r2Out, r2A, r2ρ, r2P] at h0 <;> norm_num at h0

/-! ## (b) Diaconis–Zabell per target -/

/-- The support of `ρ` as a `Finset`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def suppF (ρ : Distr Ω) : Finset Ω := univ.filter (fun ω => 0 < ρ.mass ω)

/-- The support of a distribution is nonempty. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem suppF_nonempty (ρ : Distr Ω) : (suppF ρ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hall : ∀ ω, ρ.mass ω = 0 := by
    intro ω
    by_contra hne
    have hpos : 0 < ρ.mass ω := lt_of_le_of_ne (ρ.nonneg ω) (Ne.symm hne)
    have : ω ∈ suppF ρ := by simp [suppF, hpos]
    rw [h] at this
    simp at this
  have := ρ.sum_eq_one
  rw [sum_eq_zero (fun ω _ => hall ω)] at this
  exact zero_ne_one this

/-- `max_{supp ρ} ρ/P`, the sup of the density on the support.
Source: channel-final.md P1 (l. 99, "`λ = 1/‖dρ/dP_t‖_∞`"). Kind: D. Fidelity: exact -/
def densMax (ρ P : Distr Ω) : ℝ := (suppF ρ).sup' (suppF_nonempty ρ) (fun ω => ρ.mass ω / P.mass ω)

/-- Pointwise `ρ ≤ densMax · P` for `ρ ≪ P`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mass_le_densMax_mul (ρ P : Distr Ω) (hρP : AbsCont ρ P) (ω : Ω) :
    ρ.mass ω ≤ densMax ρ P * P.mass ω := by
  by_cases hω : 0 < ρ.mass ω
  · have hP : 0 < P.mass ω := by
      rcases lt_or_eq_of_le (P.nonneg ω) with h | h
      · exact h
      · exact absurd (hρP ω h.symm) hω.ne'
    have hle : ρ.mass ω / P.mass ω ≤ densMax ρ P :=
      le_sup' (fun ω => ρ.mass ω / P.mass ω) (by simp [suppF, hω])
    rwa [div_le_iff₀ hP] at hle
  · have h0 : ρ.mass ω = 0 := le_antisymm (not_lt.1 hω) (ρ.nonneg ω)
    rw [h0]
    apply mul_nonneg _ (P.nonneg ω)
    obtain ⟨ω₀, hω₀⟩ := suppF_nonempty ρ
    refine le_trans ?_ (le_sup' (fun ω => ρ.mass ω / P.mass ω) hω₀)
    exact div_nonneg (ρ.nonneg ω₀) (P.nonneg ω₀)

/-- `1 ≤ densMax` (both sum to one). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem one_le_densMax (ρ P : Distr Ω) (hρP : AbsCont ρ P) : 1 ≤ densMax ρ P := by
  have h := sum_le_sum fun ω (_ : ω ∈ univ) => mass_le_densMax_mul ρ P hρP ω
  rw [ρ.sum_eq_one, ← mul_sum, P.sum_eq_one, mul_one] at h
  exact h

/-- `densMax = 1` forces `ρ = P`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem eq_of_densMax_eq_one (ρ P : Distr Ω) (hρP : AbsCont ρ P) (h : densMax ρ P = 1) : ρ = P := by
  have hle : ∀ ω, ρ.mass ω ≤ P.mass ω := fun ω => by
    have := mass_le_densMax_mul ρ P hρP ω
    rwa [h, one_mul] at this
  ext ω
  by_contra hne
  have hlt : ρ.mass ω < P.mass ω := lt_of_le_of_ne (hle ω) hne
  have := sum_lt_sum (fun ω' (_ : ω' ∈ univ) => hle ω') ⟨ω, mem_univ ω, hlt⟩
  rw [ρ.sum_eq_one, P.sum_eq_one] at this
  exact lt_irrefl _ this

/-- **Diaconis–Zabell per target**: for `ρ ≪ P` with `ρ ≠ P`, `λ := 1/densMax ∈ (0, 1)` and the
two-target family `{ρ, ρ′}` with `ρ′ = (P − λρ)/(1 − λ)` and masses `(λ, 1 − λ)` is a valid
anticipation satisfying `(Mart)`, so `ρ` is reached by *some* anticipation. **One anticipation per
target** — not one anticipation reaching all of `Δ(Ω)` (S1).
Source: channel-final.md P1 (l. 99, "Diaconis–Zabell … `{ρ, (P_t − λρ)/(1 − λ)}` with
`λ = 1/‖dρ/dP_t‖_∞` satisfies (Mart)"); run 1 `radical` I3.1 (reported there)
Kind: P
Fidelity: exact (finite carrier)
Hyps: (a) `ρ ≪ P`, `ρ ≠ P` -/
theorem dz_two_target (ρ P : Distr Ω) (hρP : AbsCont ρ P) (hne : ρ ≠ P) :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ ∃ ρ' : Distr Ω,
      (∀ ω, P.mass ω = l * ρ.mass ω + (1 - l) * ρ'.mass ω) ∧
      ∃ 𝒜 : Anticipation Ω (Fin 2), 𝒜.ρ = ![ρ, ρ'] ∧ 𝒜.pmass P 0 = l ∧ 𝒜.pmass P 1 = 1 - l ∧
        𝒜.Mart P ∧ ρ ∈ 𝒜.dataReach P := by
  have hM1 : 1 ≤ densMax ρ P := one_le_densMax ρ P hρP
  have hMgt : 1 < densMax ρ P := by
    rcases lt_or_eq_of_le hM1 with h | h
    · exact h
    · exact absurd (eq_of_densMax_eq_one ρ P hρP h.symm) hne
  set l : ℝ := (densMax ρ P)⁻¹ with hl
  have hl0 : 0 < l := inv_pos.2 (by linarith)
  have hl1 : l < 1 := inv_lt_one_of_one_lt₀ hMgt
  have hlρ : ∀ ω, l * ρ.mass ω ≤ P.mass ω := fun ω => by
    have := mass_le_densMax_mul ρ P hρP ω
    rw [hl]
    calc (densMax ρ P)⁻¹ * ρ.mass ω ≤ (densMax ρ P)⁻¹ * (densMax ρ P * P.mass ω) :=
          mul_le_mul_of_nonneg_left this hl0.le
      _ = P.mass ω := by field_simp
  let ρ' : Distr Ω :=
    { mass := fun ω => (P.mass ω - l * ρ.mass ω) / (1 - l)
      nonneg := fun ω => div_nonneg (by linarith [hlρ ω]) (by linarith)
      sum_eq_one := by
        rw [← sum_div, sum_sub_distrib, ← mul_sum, P.sum_eq_one, ρ.sum_eq_one, mul_one]
        exact div_self (by linarith) }
  have hl1' : (1 - l) ≠ 0 := by linarith
  have hbary : ∀ ω, P.mass ω = l * ρ.mass ω + (1 - l) * ρ'.mass ω := fun ω => by
    show P.mass ω = l * ρ.mass ω + (1 - l) * ((P.mass ω - l * ρ.mass ω) / (1 - l))
    rw [mul_div_cancel₀ _ hl1']
    ring
  have hb : ∀ ω, P.mass ω = ∑ i : Fin 2, (![l, 1 - l] : Fin 2 → ℝ) i * ((![ρ, ρ'] : Fin 2 → Distr Ω) i).mass ω := by
    intro ω
    rw [Fin.sum_univ_two]
    simpa using hbary ω
  obtain ⟨𝒜, hρ, hmass, hmart, hreach⟩ := exists_anticipation_of_barycentre P ![ρ, ρ'] ![l, 1 - l]
    (fun i => by fin_cases i <;> simp <;> linarith) hb
  refine ⟨l, hl0, hl1, ρ', hbary, 𝒜, hρ, by simpa using hmass 0, by simpa using hmass 1, hmart, ?_⟩
  rw [hreach]
  exact ⟨0, by simpa using hl0, by simp⟩

/-! ## (c) Grip, reach, erosion — definitions only -/

/-- **A substrate model** (channel-final D9): substrate states `Sub`, the belief read off a state
`β`, and the effect `Φ ϑ e` of a physical influence `e` on a state.
Source: channel-final.md D9 (l. 41, "`M^H_t := {β(Φ(ϑ_t, e)) : e ∈ E^H_t}`")
Kind: D
Fidelity: variant: one-shot (no joint process) -/
structure SubstrateModel (Ω Sub E : Type) [Fintype Ω] where
  /-- the belief read off a substrate state -/
  β : Sub → Distr Ω
  /-- the effect of an influence on a state -/
  Φ : Sub → E → Sub

/-- **The humans' reach** `M^H = {β(Φ(ϑ, e)) : e ∈ E^H}` from state `ϑ` with influences `E^H`.
Source: channel-final.md D9 (l. 41)
Kind: D
Fidelity: variant: one-shot -/
def SubstrateModel.reachSet {Sub E : Type} (M : SubstrateModel Ω Sub E) (EH : Finset E) (ϑ : Sub) :
    Set (Distr Ω) :=
  (fun e => M.β (M.Φ ϑ e)) '' (↑EH : Set E)

/-- **Erosion of reach** (D10's reach clause): an option `a` erodes the reach if, from the state it
leaves, the humans' reach is a strict subset of the reach from the state the null option leaves.
`Γ`-erosion (the landing probability) is T9's parameter; `Γ(𝒬)` (target form) needs the joint
process and is not defined here. The inaction baseline is the source's O8 (a modelling choice).
Source: channel-final.md D10 (l. 43, "`M^H_{t+1}(a_t) ⊊ M^H_{t+1}(∅)`"), O8 (l. 160)
Kind: D
Fidelity: variant: one-shot, reach clause only -/
def ErodesReach {A Sub E : Type} (M : SubstrateModel Ω Sub E) (EH : Finset E) (after : A → Sub)
    (a nul : A) : Prop :=
  M.reachSet EH (after a) ⊂ M.reachSet EH (after nul)

/-- The two-state substrate: `true` = grip intact; the influence `true` acts only through an
intact grip; `β` reads `Q` off an acted-on state and `P₀` otherwise.
Source: none: infrastructure (N− witness). Kind: D. Fidelity: n/a -/
def toySubstrate (P₀ Q : Distr Ω) : SubstrateModel Ω Bool Bool where
  β := fun s => if s then Q else P₀
  Φ := fun ϑ e => ϑ && e

/-- **An N− witness of `ErodesReach`**: with the grip intact the humans reach `{P₀, Q}`; after an
option that breaks the grip they reach `{P₀}` only — a strict subset when `Q ≠ P₀`. Degenerate
(two states, two influences); it inhabits the definition and nothing more.
Source: channel-final.md D10 (l. 43)
Kind: N−
Fidelity: n/a
Hyps: (a) `Q ≠ P₀` -/
theorem toy_erodesReach (P₀ Q : Distr Ω) (hne : Q ≠ P₀) :
    ErodesReach (toySubstrate P₀ Q) univ (fun a : Bool => a) false true := by
  unfold ErodesReach SubstrateModel.reachSet toySubstrate
  simp only [coe_univ, Set.image_univ, Bool.false_and, Bool.true_and]
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · rintro _ ⟨e, rfl⟩
    exact ⟨false, by simp⟩
  · intro h
    have : Q ∈ Set.range (fun e : Bool => if e then Q else P₀) := ⟨true, by simp⟩
    rw [← h] at this
    obtain ⟨e, he⟩ := this
    simp at he
    exact hne he.symm

end

end Cleanroom.Corrigibility.CorrPowerChannel
