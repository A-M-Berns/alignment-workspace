import Cleanroom.Udt.UdtPolicyCalc.Defs
import Mathlib.Tactic.FieldSimp

/-!
# `Cleanroom.Udt.UdtCommTrust.Prob`: finite-probability plumbing on the support

Work package `udt-comm-trust`. Infrastructure over `udt-policy-calc`'s `FinDist`/`mass`/
`condExpJunk`/`condProbJunk`, specialised to a *fully supported* weight (`∀ ω, 0 < w ω`; mandate
§3: `Ω` is the support). Contents: the junk value `−1` sits strictly below every attained
conditional expectation of a `[0,1]`-valued `U` (`junk_lt_of_nonempty`); the law of total
expectation over the fibres of a random variable (`condExpJunk_total`); a conditional expectation
over a union of atoms on which the atom-wise conditional expectations agree (`condExpJunk_of_atoms`);
grouping a sum by the value of a variable (`sum_mul_comp_eq`); the total-probability sums for
`condProbJunk` (`sum_condProbJunk`); and a strict weighted-average inequality (`sum_mul_lt_sum_mul`).
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω : Type}

/-- Supporting lemma `mass_pos_of_nonempty`: under full support, a non-empty event has positive
mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_pos_of_nonempty {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) {E : Finset Ω} (h : E.Nonempty) :
    0 < mass w E :=
  mass_pos_of_mem (fun ω => (hw ω).le) h.choose_spec (hw _)

/-- Supporting lemma `mass_eq_zero_iff`: under full support, zero mass means the empty event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_zero_iff [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) {E : Finset Ω} :
    mass w E = 0 ↔ E = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact (mass_pos_of_nonempty hw (nonempty_iff_ne_empty.2 hne)).ne' h
  · rintro rfl
    simp [mass]

/-- Supporting lemma `mass_univ`: the mass of `univ` is one.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_univ [Fintype Ω] (μ : FinDist Ω) : mass μ.w univ = 1 := μ.sum_one

/-- Supporting lemma `event_inter_eq_filter`: `{P} ∩ F = F.filter P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem event_inter_eq_filter [Fintype Ω] [DecidableEq Ω] (P : Ω → Prop) [DecidablePred P] (F : Finset Ω) :
    event P ∩ F = F.filter P := by
  ext ω; simp [and_comm]

/-- Supporting lemma `condProbJunk_of_nonempty`: on a non-empty conditioning event the junk
conditional probability is the ratio.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_of_nonempty [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) {E F : Finset Ω}
    (hF : F.Nonempty) (j : ℝ) : condProbJunk w E F j = mass w (E ∩ F) / mass w F := by
  simp [condProbJunk, (mass_pos_of_nonempty hw hF).ne']

/-- Supporting lemma `condProbJunk_of_empty`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_of_empty [DecidableEq Ω] {w : Ω → ℝ} (E : Finset Ω) (j : ℝ) :
    condProbJunk w E ∅ j = j := by
  simp [condProbJunk, mass]

/-- Supporting lemma `condExpJunk_of_empty`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_of_empty {w f : Ω → ℝ} (j : ℝ) : condExpJunk w f ∅ j = j := by
  simp [condExpJunk, mass]

/-- **The junk value sits below every attained value**: for a `[0,1]`-valued `U` and a non-empty
event `E` (positive mass on the support), `−1 < E[U ∣ E]`. This is why the UDT argmax never selects
an unattained action, and why the theorems need no positivity side-conditions beyond non-emptiness.
Source: [[communication-trust-translated]] lines 265–270 (the `−1` convention); mandate §3
Kind: L
Fidelity: exact
Hyps: none -/
theorem junk_lt_of_nonempty {w U : Ω → ℝ} (hw : ∀ ω, 0 < w ω) (hU : ∀ ω, 0 ≤ U ω) {E : Finset Ω}
    (h : E.Nonempty) : (-1 : ℝ) < condExpJunk w U E (-1) :=
  lt_of_lt_of_le (by norm_num)
    (le_condExpJunk_of_le (fun ω => (hw ω).le) (mass_pos_of_nonempty hw h) fun ω _ => hU ω)

/-- Supporting lemma `condExpJunk_nonneg_of_nonempty`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_nonneg_of_nonempty {w U : Ω → ℝ} (hw : ∀ ω, 0 < w ω) (hU : ∀ ω, 0 ≤ U ω)
    {E : Finset Ω} (h : E.Nonempty) (j : ℝ) : 0 ≤ condExpJunk w U E j :=
  le_condExpJunk_of_le (fun ω => (hw ω).le) (mass_pos_of_nonempty hw h) fun ω _ => hU ω

/-- Supporting lemma `sum_mul_eq_of_condExpJunk_eq`: unnormalised form of a conditional
expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_mul_eq_of_condExpJunk_eq {w U : Ω → ℝ} {E : Finset Ω} (h : 0 < mass w E) {j c : ℝ}
    (hc : condExpJunk w U E j = c) : ∑ ω ∈ E, w ω * U ω = c * mass w E := by
  rw [condExpJunk_of_pos h] at hc
  rw [← hc, div_mul_cancel₀ _ h.ne']

/-- Supporting lemma `sum_mul_comp_eq`: a sum of `w · (u ∘ E)` grouped by the value of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_mul_comp_eq {K : Type} [Fintype K] [DecidableEq K] (w : Ω → ℝ) (u : K → ℝ)
    (E : Ω → K) (F : Finset Ω) :
    ∑ ω ∈ F, w ω * u (E ω) = ∑ e, u e * mass w (F.filter fun ω => E ω = e) := by
  rw [← Finset.sum_fiberwise F E]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.1 hω).2, mul_comm]

/-- **Law of total expectation over the fibres of `Z`**: for a non-empty `F`,
`E[U ∣ F] = ∑_z E[U ∣ F ∩ {Z = z}] · P(Z = z ∣ F)`; fibres missing from `F` contribute `0`
whatever the junk value.
Source: none: infrastructure (the decomposition step of every C&T proof)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_total [Fintype Ω] [DecidableEq Ω] {K : Type} [Fintype K] [DecidableEq K] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω)
    (U : Ω → ℝ) (Z : Ω → K) {F : Finset Ω} (hF : F.Nonempty) (j : ℝ) :
    condExpJunk w U F j =
      ∑ z, condExpJunk w U (F.filter fun ω => Z ω = z) j *
        condProbJunk w (event fun ω => Z ω = z) F 0 := by
  have hF' := mass_pos_of_nonempty hw hF
  have hterm : ∀ z, condExpJunk w U (F.filter fun ω => Z ω = z) j *
      condProbJunk w (event fun ω => Z ω = z) F 0 =
      (∑ ω ∈ F.filter (fun ω => Z ω = z), w ω * U ω) * (mass w F)⁻¹ := by
    intro z
    rw [condProbJunk_of_nonempty hw hF, event_inter_eq_filter]
    by_cases hz : (F.filter fun ω => Z ω = z).Nonempty
    · have hz' := mass_pos_of_nonempty hw hz
      rw [condExpJunk_of_pos hz']
      field_simp
    · rw [not_nonempty_iff_eq_empty] at hz
      rw [hz]
      simp [mass]
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.sum_mul, Finset.sum_fiberwise F Z,
    condExpJunk_of_pos hF', div_eq_mul_inv]

/-- **A conditional expectation over a `Z`-measurable union of atoms** on each of which the
atom-wise conditional expectation is `c` equals `c`.
Source: none: infrastructure (the "replace `U` by its `Π̈`-conditional mean" step)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_of_atoms [Fintype Ω] [DecidableEq Ω] {K : Type} [Fintype K] [DecidableEq K] {w : Ω → ℝ}
    (hw : ∀ ω, 0 < w ω) (U : Ω → ℝ) (Z : Ω → K) {G : Finset Ω} (hG : G.Nonempty)
    (hmeas : ∀ ω ∈ G, ∀ ω', Z ω' = Z ω → ω' ∈ G) {c j : ℝ}
    (hc : ∀ ω ∈ G, condExpJunk w U (event fun ω' => Z ω' = Z ω) j = c) :
    condExpJunk w U G j = c := by
  have hG' := mass_pos_of_nonempty hw hG
  rw [condExpJunk_of_pos hG', div_eq_iff hG'.ne']
  have hfib : ∀ z, ∑ ω ∈ G.filter (fun ω => Z ω = z), w ω * U ω =
      c * mass w (G.filter fun ω => Z ω = z) := by
    intro z
    by_cases hz : (G.filter fun ω => Z ω = z).Nonempty
    · obtain ⟨ω₀, hω₀⟩ := hz
      rw [Finset.mem_filter] at hω₀
      have hatom : (G.filter fun ω => Z ω = z) = event fun ω' => Z ω' = Z ω₀ := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2.trans hω₀.2.symm, fun h => ⟨hmeas ω₀ hω₀.1 ω h, h.trans hω₀.2⟩⟩
      rw [hatom]
      exact sum_mul_eq_of_condExpJunk_eq
        (mass_pos_of_nonempty hw ⟨ω₀, by simp⟩) (hc ω₀ hω₀.1)
    · rw [not_nonempty_iff_eq_empty] at hz
      rw [hz]
      simp [mass]
  rw [← Finset.sum_fiberwise G Z, Finset.sum_congr rfl fun z _ => hfib z, ← Finset.mul_sum]
  congr 1
  rw [mass, ← Finset.sum_fiberwise G Z]
  rfl

/-- **Total probability for `condProbJunk`**: the junk conditional probabilities of the fibres of
`Z` given `F` sum to `1` when `F` is non-empty and to `0` (the junk) when `F` is empty.
Source: none: infrastructure (T9(i), T12's "sum both sides" arguments)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_condProbJunk [Fintype Ω] [DecidableEq Ω] {K : Type} [Fintype K] [DecidableEq K] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω)
    (Z : Ω → K) (F : Finset Ω) :
    ∑ z, condProbJunk w (event fun ω => Z ω = z) F 0 = if F.Nonempty then 1 else 0 := by
  by_cases hF : F.Nonempty
  · rw [if_pos hF]
    have hF' := mass_pos_of_nonempty hw hF
    rw [Finset.sum_congr rfl fun z _ => by
      rw [condProbJunk_of_nonempty hw hF, event_inter_eq_filter, div_eq_mul_inv],
      ← Finset.sum_mul, ← div_eq_mul_inv, div_eq_one_iff_eq hF'.ne']
    rw [mass, ← Finset.sum_fiberwise F Z]
    rfl
  · rw [if_neg hF, not_nonempty_iff_eq_empty] at *
    subst hF
    simp [condProbJunk_of_empty]

/-- **A strict weighted average**: with non-negative weights summing to one, termwise strict
inequality on the positive-weight terms gives a strict inequality of the averages.
Source: none: infrastructure (T13's last step)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_mul_lt_sum_mul {K : Type} [Fintype K] (f g q : K → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hsum : ∑ k, q k = 1) (hlt : ∀ k, 0 < q k → f k < g k) :
    ∑ k, f k * q k < ∑ k, g k * q k := by
  have hex : ∃ k, 0 < q k := by
    by_contra hcon
    have hle : ∀ k, q k ≤ 0 := fun k => not_lt.1 fun h => hcon ⟨k, h⟩
    have : ∑ k, q k = 0 := Finset.sum_eq_zero fun k _ => le_antisymm (hle k) (hq k)
    linarith
  obtain ⟨k₀, hk₀⟩ := hex
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ _, ?_⟩
  · rcases (hq k).lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_right (hlt k h).le (hq k)
    · rw [← h]; simp
  · exact mul_lt_mul_of_pos_right (hlt k₀ hk₀) hk₀

end Cleanroom.Udt.UdtCommTrust
