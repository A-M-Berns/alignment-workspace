import Cleanroom.Corrigibility.CorrGeneralObject.Support
import Cleanroom.Corrigibility.CorrReflectFrames.Clarity

/-!
# corr-general-object — T2: endorsement lives in the kernel; the barycentre theorem; T8

* **T2(i)** For `Q ≪ P` and `0 < λ`, the density kernel `k = λ · dQ/dP` (`densKernel`, `0` off
  `supp P`) is a kernel iff `λ Q ≤ P` pointwise (`densKernel_isKernel_iff`), has push mass `λ`
  and is endorsed (`endorsed_densKernel`); every `Q ≪ P` has an endorsing kernel
  (`exists_endorsing_kernel`); an endorsed kernel *is* the density kernel on `supp P`
  (`endorsed_iff_eq_densKernel`). Endorsement is `corr-reflect-frames`' `ReflectiveFor` at a
  one-point index (`reflectiveFor_unit_iff`).
* **T2(ii), the barycentre theorem (load-bearing).** For a kernel family `K` with rows in the
  simplex (exactly one target announced) and targets `ρ`, `ReflectiveFor P.mass K ρ` implies
  `P = ∑ᵢ P(E_{Qᵢ}) ρᵢ` (`barycentre_of_reflectiveFor`); conversely every barycentric
  representation `P = ∑ᵢ λᵢ ρᵢ` with `λ ≥ 0` is realised by a kernel family with rows in the
  simplex and push masses `λ` (`exists_reflectiveFor_of_barycentre`); together
  `exists_reflectiveFor_iff_barycentre`. The source's S1(b) states the iff for a *fixed* source
  ("has every announcement endorsed iff `P_t = ∑ᵢ P_t(E_{Qᵢ}) Qᵢ`"), and the mandate copied it;
  that sentence is false right-to-left — the barycentre condition under a source's own push
  masses does not make that source reflective (`barycentre_not_sufficient_fixed_law`: two
  worlds, `K ≡ 1/2`). What P2 proves, and what holds, is the existence form. Findings F-14.
* **T2(iii)** A family on one side of `P` along some `X` is not all endorsed
  (`not_reflectiveFor_of_one_sided`). N−: a one-target family with `ρ ≠ P`.
* **T8(a)** An endorsing kernel is silent where the target is null; a dogmatic target
  (`Q(S) = 1`) is literally adopted only by a kernel vanishing off `S` on `supp P`.

Witnesses: CE2 (`ce2_*`, both targets endorsed from `P = (1/2, 1/4, 1/4)`), Example A's two
kernels for `Endorsed` (`exA_*`, in `Witnesses.lean`), Example B (`exB_*`, `Witnesses.lean`).

Sources: [[general-object-final]] S1(a)(b), S4(b), S11, P2, P9, CE2, R5, R6;
[[corr-wf14b-inventory]] 003, 011.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrReflectFrames
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## T2(i): the density kernel -/

/-- The **density kernel** `k ω = λ · Q ω / P ω` on `supp P`, `0` off it — the only kernel shape
that endorses `Q` (S4(b)).
Source: [[general-object-final]] S4(b), P2 (`k(ω) = P_t(E_Q) Q(ω)/P_t(ω)`)
Kind: D
Fidelity: exact (the off-support value is immaterial: the push has no mass there) -/
def densKernel (P Q : Distr Ω) (l : ℝ) : Ω → ℝ :=
  fun ω => if P.mass ω = 0 then 0 else l * Q.mass ω / P.mass ω

/-- The density kernel at a support point. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem densKernel_of_pos (P Q : Distr Ω) (l : ℝ) {ω : Ω} (h : 0 < P.mass ω) :
    densKernel P Q l ω = l * Q.mass ω / P.mass ω := by
  simp [densKernel, h.ne']

/-- **Feasibility of the density kernel**: for `Q ≪ P` and `0 < λ`, `λ · dQ/dP ∈ [0, 1]` iff
`λ · Q ω ≤ P ω` for every `ω` (the multiplicative form of `λ ≤ 1/‖dQ/dP‖_∞`).
Source: [[general-object-final]] P2 ("feasibility `k ≤ 1` iff `P_t(E_Q) ≤ 1/‖dQ/dP_t‖_∞`")
Kind: L
Fidelity: exact (multiplicative form)
Hyps: (a) `AbsCont Q P`, `0 < λ` -/
theorem densKernel_isKernel_iff (P Q : Distr Ω) (hQP : AbsCont Q P) {l : ℝ} (hl : 0 < l) :
    IsKernel (densKernel P Q l) ↔ ∀ ω, l * Q.mass ω ≤ P.mass ω := by
  constructor
  · intro h ω
    by_cases hP : P.mass ω = 0
    · rw [hQP ω hP, hP]; simp
    · have hPpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP)
      have := (h ω).2
      rw [densKernel_of_pos P Q l hPpos, div_le_one hPpos] at this
      exact this
  · intro h ω
    by_cases hP : P.mass ω = 0
    · simp [densKernel, hP]
    · have hPpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP)
      rw [densKernel_of_pos P Q l hPpos]
      exact ⟨div_nonneg (mul_nonneg hl.le (Q.nonneg ω)) hPpos.le, (div_le_one hPpos).2 (h ω)⟩

/-- The push mass of the density kernel is `λ` (for `Q ≪ P`).
Source: [[general-object-final]] P2 ("and then `λ = P_t(E_Q)`")
Kind: L
Fidelity: exact
Hyps: (a) `AbsCont Q P` -/
theorem pushMass_densKernel (P Q : Distr Ω) (hQP : AbsCont Q P) (l : ℝ) :
    pushMass P (densKernel P Q l) = l := by
  unfold pushMass
  have : ∀ ω, P.mass ω * densKernel P Q l ω = l * Q.mass ω := by
    intro ω
    by_cases hP : P.mass ω = 0
    · simp [densKernel, hP, hQP ω hP]
    · rw [densKernel_of_pos P Q l (lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP))]
      field_simp
  simp only [this, ← mul_sum, Q.sum_eq_one, mul_one]

/-- **The density kernel endorses `Q`** (for `Q ≪ P`): `P ω · k ω = λ · Q ω = P(E_Q) · Q ω`.
Source: [[general-object-final]] S4(b), P2
Kind: P
Fidelity: exact
Hyps: (a) `AbsCont Q P` -/
theorem endorsed_densKernel (P Q : Distr Ω) (hQP : AbsCont Q P) (l : ℝ) :
    Endorsed P (densKernel P Q l) Q := by
  intro ω
  rw [pushMass_densKernel P Q hQP l]
  by_cases hP : P.mass ω = 0
  · simp [densKernel, hP, hQP ω hP]
  · rw [densKernel_of_pos P Q l (lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP))]
    field_simp

/-- **Every `Q ≪ P` has an endorsing kernel** of positive push mass: take
`λ := 1 / max 1 B` for a density bound `B` (`absCont_iff_exists_boundedDensity`); the bound is
stated multiplicatively, `λ · Q ≤ P`.
Source: [[general-object-final]] S1(a), P2 ("existence by taking equality")
Kind: P
Fidelity: exact
Hyps: (a) `AbsCont Q P` only -/
theorem exists_endorsing_kernel (P Q : Distr Ω) (hQP : AbsCont Q P) :
    ∃ (k : Ω → ℝ) (l : ℝ), 0 < l ∧ IsKernel k ∧ pushMass P k = l ∧ Endorsed P k Q ∧
      ∀ ω, l * Q.mass ω ≤ P.mass ω := by
  obtain ⟨B, hB⟩ := (absCont_iff_exists_boundedDensity Q P).1 hQP
  set B' := max 1 B with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hbound : ∀ ω, (1 / B') * Q.mass ω ≤ P.mass ω := by
    intro ω
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hB'pos]
    calc Q.mass ω ≤ B * P.mass ω := hB ω
      _ ≤ B' * P.mass ω := mul_le_mul_of_nonneg_right (le_max_right _ _) (P.nonneg ω)
      _ = P.mass ω * B' := mul_comm _ _
  refine ⟨densKernel P Q (1 / B'), 1 / B', by positivity,
    (densKernel_isKernel_iff P Q hQP (by positivity)).2 hbound, pushMass_densKernel P Q hQP _,
    endorsed_densKernel P Q hQP _, hbound⟩

/-- **An endorsing kernel is the density kernel on the support** (S4(b), the "only if"): under
`0 < pushMass` and `Q ≪ P`, `Endorsed P k Q ↔ ∀ ω, 0 < P ω → k ω = P(E_Q) · Q ω / P ω`.
Source: [[general-object-final]] S4(b), P2
Kind: L
Fidelity: exact
Hyps: (a) the guard and `AbsCont Q P` (the latter only for `⇐`, where the off-support values of
`k` are unconstrained) -/
theorem endorsed_iff_eq_densKernel (P Q : Distr Ω) {k : Ω → ℝ} (h : 0 < pushMass P k)
    (hQP : AbsCont Q P) :
    Endorsed P k Q ↔ ∀ ω, 0 < P.mass ω → k ω = pushMass P k * Q.mass ω / P.mass ω := by
  constructor
  · intro hE ω hP
    rw [eq_div_iff hP.ne', mul_comm, hE ω]
  · intro hk ω
    by_cases hP : P.mass ω = 0
    · rw [hP, hQP ω hP]; ring
    · have hPpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP)
      rw [hk ω hPpos]
      field_simp

/-- **Endorsement is `ReflectiveFor` at a one-point index**: `corr-reflect-frames`' predicate
for the constant family `K ω () = k ω`, `ρ () = Q`, unfolds to "`0 < pushMass → Endorsed`".
Source: [[general-object-final]] S4(a); radical I7.2 via `corr-reflect-frames`
Kind: L
Fidelity: exact -/
theorem reflectiveFor_unit_iff (P : Distr Ω) (k : Ω → ℝ) (Q : Distr Ω) :
    ReflectiveFor P.mass (fun ω (_ : Unit) => k ω) (fun _ => Q.mass) ↔
      (0 < pushMass P k → Endorsed P k Q) := by
  unfold ReflectiveFor Endorsed pushMass
  constructor
  · intro h hpos ω
    exact h () hpos ω
  · intro h _ hpos ω
    exact h hpos ω

/-! ## T2(ii): the barycentre theorem -/

/-- **Reflection for a family forces the barycentre condition** (load-bearing, `⇒`): for a kernel
family `K` with nonnegative rows summing to one (exactly one target announced) and targets `ρ`,
`ReflectiveFor P.mass K ρ` implies `P ω = ∑ᵢ P(E_{Qᵢ}) · ρᵢ ω` for every `ω` — `P` is the
barycentre of the announced targets under the announcement law.
Source: [[general-object-final]] S1(b), P2 ("summing gives `P_t = ∑ᵢ P_t(E_{Qᵢ}) Qᵢ`");
radical I3.3; [[corr-wf14b-inventory]] 003
Kind: C (the row normalisation `P ω = ∑ᵢ P ω K ω i`, then `ReflectiveFor` termwise, with the
zero-push-mass targets handled; re-graded from P at audit r2 adversarial 3.6 — the construction
is in `exists_reflectiveFor_of_barycentre`)
Fidelity: exact (`∑ᵢ K ω i = 1` is the content; without it `K = 0` endorses every family)
Hyps: (a) rows nonnegative and summing to one -/
theorem barycentre_of_reflectiveFor {I : Type} [Fintype I] (P : Distr Ω) (K : Ω → I → ℝ)
    (hK0 : ∀ ω i, 0 ≤ K ω i) (hK1 : ∀ ω, ∑ i, K ω i = 1) (ρ : I → Distr Ω)
    (h : ReflectiveFor P.mass K (fun i => (ρ i).mass)) :
    ∀ ω, P.mass ω = ∑ i, (∑ ω', P.mass ω' * K ω' i) * (ρ i).mass ω := by
  intro ω
  have e : P.mass ω = ∑ i, P.mass ω * K ω i := by rw [← mul_sum, hK1, mul_one]
  rw [e]
  apply sum_congr rfl
  intro i _
  by_cases hpos : 0 < ∑ ω', P.mass ω' * K ω' i
  · exact h i hpos ω
  · have hzero : ∑ ω', P.mass ω' * K ω' i = 0 :=
      le_antisymm (not_lt.1 hpos) (sum_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hK0 ω' i))
    have hall := (sum_eq_zero_iff_of_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hK0 ω' i)).1 hzero
    rw [hzero, zero_mul]
    exact hall ω (mem_univ ω)

/-- **Every barycentric representation is realised by a reflective kernel family** (`⇐`): given
`P = ∑ᵢ λᵢ ρᵢ` with `λ ≥ 0`, the kernels `K ω i = λᵢ ρᵢ ω / P ω` on `supp P` (rows `λ` off it)
are nonnegative, sum to one, have push masses `λ`, and are reflective.
Source: [[general-object-final]] P2 ("conversely, given `P_t = ∑ᵢ λᵢ Qᵢ` … the kernels
`kᵢ := λᵢ Qᵢ/P_t` are in `[0, 1]`, sum to one, and give `P_t(E_{Qᵢ}) = λᵢ`")
Kind: P
Fidelity: exact (`λ ≥ 0` rather than the source's `λ > 0`: a zero weight is a target never
announced, harmless)
Hyps: (a) `λ ≥ 0` and the barycentric identity -/
theorem exists_reflectiveFor_of_barycentre {I : Type} [Fintype I] (P : Distr Ω) (ρ : I → Distr Ω)
    (l : I → ℝ) (hl : ∀ i, 0 ≤ l i) (hb : ∀ ω, P.mass ω = ∑ i, l i * (ρ i).mass ω) :
    ∃ K : Ω → I → ℝ, (∀ ω i, 0 ≤ K ω i) ∧ (∀ ω, ∑ i, K ω i = 1) ∧
      (∀ i, ∑ ω, P.mass ω * K ω i = l i) ∧ ReflectiveFor P.mass K (fun i => (ρ i).mass) := by
  have hsum1 : ∑ i, l i = 1 := by
    have := P.sum_eq_one
    simp_rw [hb] at this
    rw [sum_comm] at this
    simpa [← mul_sum, (ρ _).sum_eq_one] using this
  -- the key pointwise fact: `l i * ρ i ω = 0` wherever `P ω = 0`
  have hnull : ∀ ω, P.mass ω = 0 → ∀ i, l i * (ρ i).mass ω = 0 := by
    intro ω hP i
    have h0 : ∑ j, l j * (ρ j).mass ω = 0 := by rw [← hb, hP]
    exact (sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hl j) ((ρ j).nonneg ω)).1 h0 i (mem_univ i)
  set K : Ω → I → ℝ := fun ω i => if P.mass ω = 0 then l i else l i * (ρ i).mass ω / P.mass ω with hK
  have hterm : ∀ ω i, P.mass ω * K ω i = l i * (ρ i).mass ω := by
    intro ω i
    by_cases hP : P.mass ω = 0
    · simp [hK, hP, hnull ω hP i]
    · simp only [hK, hP, if_false]
      field_simp
  have hmass : ∀ i, ∑ ω, P.mass ω * K ω i = l i := by
    intro i
    simp only [hterm, ← mul_sum, (ρ i).sum_eq_one, mul_one]
  refine ⟨K, ?_, ?_, hmass, ?_⟩
  · intro ω i
    by_cases hP : P.mass ω = 0
    · simp [hK, hP, hl i]
    · simp only [hK, hP, if_false]
      exact div_nonneg (mul_nonneg (hl i) ((ρ i).nonneg ω)) (P.nonneg ω)
  · intro ω
    by_cases hP : P.mass ω = 0
    · simp [hK, hP, hsum1]
    · simp only [hK, hP, if_false]
      rw [← sum_div, ← hb ω, div_self hP]
  · intro i _ ω
    rw [hterm, hmass]

/-- **The barycentre theorem, both directions**: a family of targets `ρ` is *all endorsed under
some announcement law* (a kernel family with nonnegative rows summing to one that is
`ReflectiveFor`) iff `P` is a nonnegative barycentre of the targets.
Source: [[general-object-final]] S1(b), P2; radical I3.3 (`exists_metaJoint_iff` is the PMF
form, `corr-reflect-frames` `MetaBelief`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_reflectiveFor_iff_barycentre {I : Type} [Fintype I] (P : Distr Ω)
    (ρ : I → Distr Ω) :
    (∃ K : Ω → I → ℝ, (∀ ω i, 0 ≤ K ω i) ∧ (∀ ω, ∑ i, K ω i = 1) ∧
        ReflectiveFor P.mass K (fun i => (ρ i).mass)) ↔
      ∃ l : I → ℝ, (∀ i, 0 ≤ l i) ∧ ∀ ω, P.mass ω = ∑ i, l i * (ρ i).mass ω := by
  constructor
  · rintro ⟨K, hK0, hK1, h⟩
    exact ⟨fun i => ∑ ω', P.mass ω' * K ω' i,
      fun i => sum_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hK0 ω' i),
      barycentre_of_reflectiveFor P K hK0 hK1 ρ h⟩
  · rintro ⟨l, hl, hb⟩
    obtain ⟨K, hK0, hK1, _, h⟩ := exists_reflectiveFor_of_barycentre P ρ l hl hb
    exact ⟨K, hK0, hK1, h⟩

/-! ### S1(b)'s fixed-source "iff" is false right-to-left (findings F-14)

S1(b): "a source that announces exactly one target from a family `{Qᵢ}` has *every* announcement
endorsed iff `P_t = ∑ᵢ P_t(E_{Qᵢ}) Qᵢ`" — an iff about a *fixed* source, whose push masses
`P_t(E_{Qᵢ})` appear on the right. Its `⇐` is false: two worlds, `P = (1/2, 1/2)`, targets
`δ₀, δ₁`, and the world-independent law `K ≡ 1/2`. The rows sum to one, the push masses are
`(1/2, 1/2)`, and `P = ½δ₀ + ½δ₁` — the barycentre condition holds under this source's own
masses — yet the source is not reflective (`P(1)·K(1, 0) = 1/4 ≠ ½·δ₀(1) = 0`). The source's
evidence for the direction (R5: 500 random families with `P_t` their barycentre, 0 failures)
builds its families by P2's construction `kᵢ := λᵢ Qᵢ/P_t`, so it never tests a different law
with the same masses. Instance from the round-1 adversarial audit
(`audit-r1-probes/FixedKBarycentre.lean`), landed at the round-2 fidelity audit's request. -/

/-- The two-world prior `(1/2, 1/2)` of the S1(b) refutation. Source: [[general-object-final]]
S1(b); audit r1 adversarial probe. Kind: D. Fidelity: exact -/
def s1bP : Distr (Fin 2) where
  mass := ![1/2, 1/2]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_two]; norm_num

/-- The two targets `δ₀, δ₁`. Source: audit r1 adversarial probe. Kind: D. Fidelity: exact -/
def s1bρ : Fin 2 → Distr (Fin 2) := ![Distr.delta 0, Distr.delta 1]

/-- The world-independent announcement law `K ≡ 1/2` (each target announced with probability
`1/2` in every world). Source: audit r1 adversarial probe. Kind: D. Fidelity: exact -/
def s1bK : Fin 2 → Fin 2 → ℝ := fun _ _ => 1/2

/-- **S1(b)'s fixed-source "iff" refuted right-to-left**: the law `K ≡ 1/2` has nonnegative rows
summing to one and push masses `(1/2, 1/2)`; `P = (1/2, 1/2)` *is* the barycentre
`∑ᵢ P(E_{Qᵢ}) ρᵢ` of the targets `δ₀, δ₁` under those masses; and `ReflectiveFor` fails. So the
barycentre condition under a source's own push masses does not make that source reflective: the
true statement is the existence form `exists_reflectiveFor_iff_barycentre`, which is what P2
proves.
Source: [[general-object-final]] S1(b) (the sentence "has every announcement endorsed iff
`P_t = ∑ᵢ P_t(E_{Qᵢ}) Qᵢ`"), copied by the mandate's T2(ii); audit r1 adversarial probe
`FixedKBarycentre.lean`; audit r2 fidelity B1
Kind: N+
Fidelity: exact (refutation of S1(b)'s `⇐` for a fixed source; both targets of positive push mass)
Hyps: (a) none -/
theorem barycentre_not_sufficient_fixed_law :
    (∀ ω i, 0 ≤ s1bK ω i) ∧ (∀ ω, ∑ i, s1bK ω i = 1) ∧
      (∀ i, ∑ ω, s1bP.mass ω * s1bK ω i = 1/2) ∧
      (∀ ω, s1bP.mass ω = ∑ i, (∑ ω', s1bP.mass ω' * s1bK ω' i) * (s1bρ i).mass ω) ∧
      ¬ ReflectiveFor s1bP.mass s1bK (fun i => (s1bρ i).mass) := by
  refine ⟨fun _ _ => by norm_num [s1bK], fun _ => by simp [s1bK], ?_, ?_, ?_⟩
  · intro i
    simp [s1bP, s1bK, Fin.sum_univ_two]; norm_num
  · intro ω
    fin_cases ω <;> simp [s1bP, s1bK, s1bρ, Distr.delta_mass, Fin.sum_univ_two] <;> norm_num
  · intro h
    have := h 0 (by simp [s1bP, s1bK, Fin.sum_univ_two] <;> norm_num) 1
    simp [s1bP, s1bK, s1bρ, Distr.delta_mass, Fin.sum_univ_two] at this

/-- Under reflection with rows summing to one, every expectation is the push-mass-weighted
average of the targets' expectations: `E_P[X] = ∑ᵢ P(E_{Qᵢ}) E_{ρᵢ}[X]`.
Source: [[general-object-final]] S1(b) (consequence)
Kind: L
Fidelity: exact -/
theorem expect_eq_sum_of_reflectiveFor {I : Type} [Fintype I] (P : Distr Ω) (K : Ω → I → ℝ)
    (hK0 : ∀ ω i, 0 ≤ K ω i) (hK1 : ∀ ω, ∑ i, K ω i = 1) (ρ : I → Distr Ω)
    (h : ReflectiveFor P.mass K (fun i => (ρ i).mass)) (X : Ω → ℝ) :
    expect P X = ∑ i, (∑ ω', P.mass ω' * K ω' i) * expect (ρ i) X := by
  unfold expect
  have hb := barycentre_of_reflectiveFor P K hK0 hK1 ρ h
  set l : I → ℝ := fun i => ∑ ω', P.mass ω' * K ω' i with hl
  calc ∑ ω, P.mass ω * X ω
      = ∑ ω, (∑ i, l i * (ρ i).mass ω) * X ω :=
        sum_congr rfl fun ω _ => by rw [← hb ω]
    _ = ∑ i, l i * ∑ ω, (ρ i).mass ω * X ω := by
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro ω _
        ring

/-- The push masses of a family with rows summing to one sum to one.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_pushMass_eq_one {I : Type} [Fintype I] (P : Distr Ω) (K : Ω → I → ℝ)
    (hK1 : ∀ ω, ∑ i, K ω i = 1) : ∑ i, ∑ ω', P.mass ω' * K ω' i = 1 := by
  rw [sum_comm]
  simp_rw [← mul_sum, hK1, mul_one, P.sum_eq_one]

/-- **T2(iii): a family lying on one side of `P` is not all endorsed** — if every target has
`E_P[X] < E_{ρᵢ}[X]` for some `X`, no announcement law (rows summing to one) is reflective.
Source: [[general-object-final]] S1(b) ("what no source can do is endorse a family whose
barycentre is not `P_t` — in particular a family lying on one side of `P_t`")
Kind: L
Fidelity: exact
Hyps: (a) none beyond the row normalisation -/
theorem not_reflectiveFor_of_one_sided {I : Type} [Fintype I] (P : Distr Ω) (K : Ω → I → ℝ)
    (hK0 : ∀ ω i, 0 ≤ K ω i) (hK1 : ∀ ω, ∑ i, K ω i = 1) (ρ : I → Distr Ω) (X : Ω → ℝ)
    (hX : ∀ i, expect P X < expect (ρ i) X) :
    ¬ ReflectiveFor P.mass K (fun i => (ρ i).mass) := by
  intro h
  have e := expect_eq_sum_of_reflectiveFor P K hK0 hK1 ρ h X
  set l : I → ℝ := fun i => ∑ ω', P.mass ω' * K ω' i with hl
  have hl0 : ∀ i, 0 ≤ l i := fun i => sum_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hK0 ω' i)
  have hl1 : ∑ i, l i = 1 := sum_pushMass_eq_one P K hK1
  have hex : ∃ i ∈ (univ : Finset I), 0 < l i := by
    by_contra hc
    push Not at hc
    have : ∑ i, l i ≤ 0 := sum_nonpos fun i hi => hc i hi
    linarith
  obtain ⟨i₀, _, hi₀⟩ := hex
  have hlt : ∑ i, l i * expect P X < ∑ i, l i * expect (ρ i) X := by
    apply sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hX i).le (hl0 i)
    · exact ⟨i₀, mem_univ _, mul_lt_mul_of_pos_left (hX i₀) hi₀⟩
  rw [← sum_mul, hl1, one_mul] at hlt
  linarith

/-- **N− for T2(iii)**: a one-target family with `ρ ≠ P` is never endorsed (the certain kernel
`K ≡ 1` forces `postPush = P`).
Source: mandate T2 (N−)
Kind: N−
Fidelity: exact (degenerate: one target, the certain kernel — the best available for the
one-sided corollary's *necessity*; the N+ is CE2)
Hyps: (a) none -/
theorem not_reflectiveFor_single_of_ne (P ρ : Distr Ω) (hne : ρ ≠ P) :
    ¬ ReflectiveFor P.mass (fun _ (_ : Unit) => (1 : ℝ)) (fun _ => ρ.mass) := by
  intro h
  have hb := barycentre_of_reflectiveFor P (fun _ (_ : Unit) => (1 : ℝ)) (fun _ _ => zero_le_one)
    (fun _ => by simp) (fun _ => ρ) h
  apply hne
  ext ω
  have := hb ω
  simp [P.sum_eq_one] at this
  exact this.symm

/-! ## CE2: two targets endorsed at once -/

/-- CE2's prior `P = (1/2, 1/4, 1/4)` (Example A's prior).
Source: [[general-object-final]] CE2, P2. Kind: D. Fidelity: exact -/
def ce2P : Distr (Fin 3) where
  mass := ![1/2, 1/4, 1/4]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- CE2's first target `Q₁ = (1/5, 3/5, 1/5)`. Source: [[general-object-final]] CE2. Kind: D. Fidelity: exact -/
def ce2Q1 : Distr (Fin 3) where
  mass := ![1/5, 3/5, 1/5]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- CE2's second target `Q₂ = (5/7, 0, 2/7)`. Source: [[general-object-final]] CE2. Kind: D. Fidelity: exact -/
def ce2Q2 : Distr (Fin 3) where
  mass := ![5/7, 0, 2/7]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_three]; norm_num

/-- CE2's target family. Source: [[general-object-final]] CE2. Kind: D. Fidelity: exact -/
def ce2ρ : Fin 2 → Distr (Fin 3) := ![ce2Q1, ce2Q2]

/-- CE2's announcement law `K = [(1/6, 5/6), (1, 0), (1/3, 2/3)]` (`k₁ + k₂ ≡ 1`).
Source: [[general-object-final]] CE2, P2. Kind: D. Fidelity: exact -/
def ce2K : Fin 3 → Fin 2 → ℝ := ![![1/6, 5/6], ![1, 0], ![1/3, 2/3]]

/-- CE2's rows are nonnegative and sum to one. Source: [[general-object-final]] CE2. Kind: N+. Fidelity: exact -/
theorem ce2K_rows : (∀ ω i, 0 ≤ ce2K ω i) ∧ ∀ ω, ∑ i, ce2K ω i = 1 := by
  refine ⟨fun ω i => ?_, fun ω => ?_⟩
  · fin_cases ω <;> fin_cases i <;> norm_num [ce2K]
  · fin_cases ω <;> simp [ce2K, Fin.sum_univ_two] <;> norm_num

/-- **N+ for T2 (CE2)**: both targets are endorsed under `K` — `ReflectiveFor` holds — with push
masses `λ = (5/12, 7/12)`, and the two targets are distinct.
Source: [[general-object-final]] CE2, P2, R5; [[corr-wf14b-inventory]] 003
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ce2_reflectiveFor :
    ReflectiveFor ce2P.mass ce2K (fun i => (ce2ρ i).mass) ∧
      (∑ ω, ce2P.mass ω * ce2K ω 0 = 5/12) ∧ (∑ ω, ce2P.mass ω * ce2K ω 1 = 7/12) ∧
      ce2ρ 0 ≠ ce2ρ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i _ ω
    fin_cases i <;> fin_cases ω <;>
      simp [ce2P, ce2ρ, ce2Q1, ce2Q2, ce2K, Fin.sum_univ_three] <;> norm_num
  · simp [ce2P, ce2K, Fin.sum_univ_three]; norm_num
  · simp [ce2P, ce2K, Fin.sum_univ_three]; norm_num
  · intro h
    have := congrArg (fun R : Distr (Fin 3) => R.mass 1) h
    simp [ce2ρ, ce2Q1, ce2Q2] at this

/-! ## T8(a): trust-structure edits on the meta-algebra -/

/-- **An endorsing kernel is silent where the target is null**: `Endorsed P k Q → Q ω = 0 →
P ω · k ω = 0`.
Source: [[general-object-final]] S11(ii), R6 ("equals `1` iff `α₂ = 0`")
Kind: L
Fidelity: exact -/
theorem endorsed_null_of_target_null (P : Distr Ω) {k : Ω → ℝ} {Q : Distr Ω}
    (hE : Endorsed P k Q) {ω : Ω} (hQ : Q.mass ω = 0) : P.mass ω * k ω = 0 := by
  rw [hE ω, hQ, mul_zero]

/-- **A dogmatic target is literally adopted only by a kernel silent off its support** (T8(a)):
if `Q(S) = 1` then an endorsing kernel vanishes at every `P`-positive world outside `S`
(`α₂ = 0`: the second-order sensor never fires on the worlds the target rules out). No
`0 < pushMass` guard is needed: at zero push mass `Endorsed` forces `P ω · k ω = 0` everywhere,
which is the conclusion. One `mul_eq_zero` on `endorsed_null_of_target_null`: kind L.
Source: [[general-object-final]] S11(ii) (non-dogmatism forbids literal adoption), R6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem endorsed_kernel_vanishes_off (P : Distr Ω) {k : Ω → ℝ} {Q : Distr Ω}
    (hE : Endorsed P k Q) {S : Finset Ω} (hQS : ∑ ω ∈ S, Q.mass ω = 1) :
    ∀ ω ∉ S, 0 < P.mass ω → k ω = 0 := by
  intro ω hω hP
  have hcompl : ∑ ω' ∈ Sᶜ, Q.mass ω' = 0 := by
    have := sum_add_sum_compl S Q.mass
    rw [hQS, Q.sum_eq_one] at this
    linarith
  have hQ : Q.mass ω = 0 :=
    (sum_eq_zero_iff_of_nonneg fun ω' _ => Q.nonneg ω').1 hcompl ω (mem_compl.2 hω)
  have := endorsed_null_of_target_null P hE hQ
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hP.ne'
  · exact h0

end

end Cleanroom.Corrigibility.CorrGeneralObject
