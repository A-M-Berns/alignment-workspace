import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCommTrust.Concrete

/-!
# `Cleanroom.Udt.UdtCtExamples.CountExt`: rational-valued utilities and modification
probabilities through integer counts

Work package `udt-ct-examples`, infrastructure. The examples' utilities take the values
`0, 1/2, 1` (Coordinated Buttons) and `0, 1/4, 1/2, 1` (Third Button); `Count.lean` handles
`{0,1}`-valued indicators only. Here every utility is `u ω / m` for a natural-valued `u` and a
fixed denominator `m`, so a conditional expectation on a non-empty event is a ratio of naturals
`(∑ wt · u) / (m · cnt)` and every comparison is a cross-multiplied natural-number statement that
`decide +kernel` can settle. Also: junk conditional probabilities (`modProb`, `modS`) as ratios of
counts, and the structural lemma `aI_indep_of_dI` recording why the pre-instance's choice must
be an external action in this package (report §T1, findings F-1).
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The weighted sum `∑_{ω ∈ E} wt ω · u ω` of a natural-valued function over an event.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def csum (W : IntWeights Ω) (u : Ω → ℕ) (E : Finset Ω) : ℕ := ∑ ω ∈ E, W.wt ω * u ω

/-- The utility `u / m` as a real-valued function.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def natDiv (u : Ω → ℕ) (m : ℕ) (ω : Ω) : ℝ := (u ω : ℝ) / m

omit [Fintype Ω] [DecidableEq Ω] in
/-- Supporting lemma `natDiv_mem`: `u / m ∈ [0, 1]` when `u ≤ m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem natDiv_mem (u : Ω → ℕ) {m : ℕ} (hm : 0 < m) (hu : ∀ ω, u ω ≤ m) (ω : Ω) :
    natDiv u m ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold natDiv
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · positivity
  · rw [div_le_one hm']
    exact_mod_cast hu ω

/-- **A `u / m`-valued utility's conditional expectation is a ratio of counts**: on a non-empty
event, `E[u/m ∣ E] = (∑_E wt · u) / (m · cnt E)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_natDiv [Nonempty Ω] (W : IntWeights Ω) (u : Ω → ℕ) {m : ℕ} (hm : 0 < m)
    {E : Finset Ω} (hE : E.Nonempty) (j : ℝ) :
    condExpJunk W.w (natDiv u m) E j = (csum W u E : ℝ) / (m * W.cnt E) := by
  rw [condExpJunk_of_pos (mass_pos_of_nonempty W.w_pos hE), W.mass_eq_cnt]
  have hN : (W.N : ℝ) ≠ 0 := by exact_mod_cast W.N_pos.ne'
  have hc : (W.cnt E : ℝ) ≠ 0 := by exact_mod_cast W.cnt_ne_zero_of_nonempty hE
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : ∑ ω ∈ E, W.w ω * natDiv u m ω = (csum W u E : ℝ) / (W.N * m) := by
    unfold csum IntWeights.w natDiv
    rw [eq_div_iff (by positivity), Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    push_cast
    field_simp
  rw [h1]
  field_simp

/-- **Strict comparison of `u / m`-valued conditional expectations from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_natDiv_lt [Nonempty Ω] (W : IntWeights Ω) (u : Ω → ℕ) {m : ℕ} (hm : 0 < m)
    {E F : Finset Ω} (hE : E.Nonempty) (hF : F.Nonempty)
    (h : csum W u E * W.cnt F < csum W u F * W.cnt E) (j : ℝ) :
    condExpJunk W.w (natDiv u m) E j < condExpJunk W.w (natDiv u m) F j := by
  rw [condExpJunk_natDiv W u hm hE, condExpJunk_natDiv W u hm hF]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcE : (0 : ℝ) < W.cnt E := by exact_mod_cast (W.cnt_pos_iff E).2 hE
  have hcF : (0 : ℝ) < W.cnt F := by exact_mod_cast (W.cnt_pos_iff F).2 hF
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h' : (csum W u E : ℝ) * W.cnt F < csum W u F * W.cnt E := by exact_mod_cast h
  nlinarith

/-- **Equality of `u / m`-valued conditional expectations from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_natDiv_eq [Nonempty Ω] (W : IntWeights Ω) (u : Ω → ℕ) {m : ℕ} (hm : 0 < m)
    {E F : Finset Ω} (hE : E.Nonempty) (hF : F.Nonempty)
    (h : csum W u E * W.cnt F = csum W u F * W.cnt E) (j : ℝ) :
    condExpJunk W.w (natDiv u m) E j = condExpJunk W.w (natDiv u m) F j := by
  rw [condExpJunk_natDiv W u hm hE, condExpJunk_natDiv W u hm hF]
  have hcE : (W.cnt E : ℝ) ≠ 0 := by exact_mod_cast W.cnt_ne_zero_of_nonempty hE
  have hcF : (W.cnt F : ℝ) ≠ 0 := by exact_mod_cast W.cnt_ne_zero_of_nonempty hF
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have h' : (csum W u E : ℝ) * W.cnt F = csum W u F * W.cnt E := by exact_mod_cast h
  rw [mul_left_comm, h', mul_left_comm]

/-- **Non-strict comparison of `u / m`-valued conditional expectations from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExpJunk_natDiv_le [Nonempty Ω] (W : IntWeights Ω) (u : Ω → ℕ) {m : ℕ} (hm : 0 < m)
    {E F : Finset Ω} (hE : E.Nonempty) (hF : F.Nonempty)
    (h : csum W u E * W.cnt F ≤ csum W u F * W.cnt E) (j : ℝ) :
    condExpJunk W.w (natDiv u m) E j ≤ condExpJunk W.w (natDiv u m) F j := by
  rcases h.lt_or_eq with h | h
  · exact (condExpJunk_natDiv_lt W u hm hE hF h j).le
  · exact (condExpJunk_natDiv_eq W u hm hE hF h j).le

/-- **A junk conditional probability is a ratio of counts** on a non-empty conditioning event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_eq_cnt_div [Nonempty Ω] (W : IntWeights Ω) (E : Finset Ω) {F : Finset Ω}
    (hF : F.Nonempty) (j : ℝ) :
    condProbJunk W.w E F j = (W.cnt (E ∩ F) : ℝ) / W.cnt F := by
  rw [condProbJunk_of_nonempty W.w_pos hF, W.mass_eq_cnt, W.mass_eq_cnt,
    div_div_div_cancel_right₀ (by exact_mod_cast W.N_pos.ne')]

/-- **Comparison of junk conditional probabilities from counts** (both conditioning events
non-empty).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_le_of_cnt [Nonempty Ω] (W : IntWeights Ω) {E F E' F' : Finset Ω}
    (hF : F.Nonempty) (hF' : F'.Nonempty)
    (h : W.cnt (E ∩ F) * W.cnt F' ≤ W.cnt (E' ∩ F') * W.cnt F) :
    condProbJunk W.w E F 0 ≤ condProbJunk W.w E' F' 0 := by
  rw [condProbJunk_eq_cnt_div W E hF, condProbJunk_eq_cnt_div W E' hF',
    div_le_div_iff₀ (by exact_mod_cast (W.cnt_pos_iff F).2 hF)
      (by exact_mod_cast (W.cnt_pos_iff F').2 hF')]
  exact_mod_cast h

/-- **Strict comparison of junk conditional probabilities from counts.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_lt_of_cnt [Nonempty Ω] (W : IntWeights Ω) {E F E' F' : Finset Ω}
    (hF : F.Nonempty) (hF' : F'.Nonempty)
    (h : W.cnt (E ∩ F) * W.cnt F' < W.cnt (E' ∩ F') * W.cnt F) :
    condProbJunk W.w E F 0 < condProbJunk W.w E' F' 0 := by
  rw [condProbJunk_eq_cnt_div W E hF, condProbJunk_eq_cnt_div W E' hF',
    div_lt_div_iff₀ (by exact_mod_cast (W.cnt_pos_iff F).2 hF)
      (by exact_mod_cast (W.cnt_pos_iff F').2 hF')]
  exact_mod_cast h

omit [Fintype Ω] in
/-- **A junk conditional probability is `1`** when the conditioning event is non-empty and
contained in the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_eq_one_of_subset {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) {E F : Finset Ω}
    (hF : F.Nonempty) (h : F ⊆ E) (j : ℝ) : condProbJunk w E F j = 1 := by
  rw [condProbJunk_of_nonempty hw hF, Finset.inter_eq_right.2 h, div_self]
  exact (mass_pos_of_nonempty hw hF).ne'

omit [Fintype Ω] in
/-- **A junk conditional probability is `0`** when the conditioning event is non-empty and
disjoint from the event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condProbJunk_eq_zero_of_disjoint {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω) {E F : Finset Ω}
    (hF : F.Nonempty) (h : E ∩ F = ∅) (j : ℝ) : condProbJunk w E F j = 0 := by
  rw [condProbJunk_of_nonempty hw hF, h]
  simp [mass]

/-- Supporting lemma `fin2_cases`: case split on `Fin 2` that does not revert dependents.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- Supporting lemma `fin3_cases`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by revert x; decide

/-- Supporting lemma `forall_fun2`: a universal over `Fin 2 → α` is a universal over two values.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem forall_fun2 {α : Type} {P : (Fin 2 → α) → Prop}
    (h : ∀ x y, P fun e => if e = 0 then x else y) : ∀ π, P π := fun π => by
  have : π = fun e => if e = 0 then π 0 else π 1 := by
    funext e
    rcases fin2_cases e with rfl | rfl <;> rfl
  rw [this]
  exact h _ _

/-- Supporting lemma `forall_fun3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem forall_fun3 {α : Type} {P : (Fin 3 → α) → Prop}
    (h : ∀ x y z, P fun e => if e = 0 then x else if e = 1 then y else z) : ∀ π, P π := fun π => by
  have : π = fun e => if e = 0 then π 0 else if e = 1 then π 1 else π 2 := by
    funext e
    rcases fin3_cases e with rfl | rfl | rfl <;> rfl
  rw [this]
  exact h _ _ _

/-! ### The structural lemma behind the representation choice -/

omit [DecidableEq Ω] in
/-- **Any subvariable of `D_I` is support-independent of `Ȧ`** in every abstract decision
structure: for all `ω₁ ω₂` there is a world with `Ȧ = Ȧ(ω₁)` and `V = V(ω₂)` whenever `V ⊑ D_I`.
Two lines from the internal-dynamic factorization `I_fac`. Consequence used by this package
(report §T1): a side-channel value that the rooms read off `D_I` (which is where `Ǒ ⊑ Ȯ ⊑ (Ȧ, D_I)`
puts it when `Ȧ` is constant at the rooms) cannot be a function of the pre-instance's internal
action `Ȧ(pre)` — so the pill choice is rendered as the pre-instance's *external* action.
Source: [[communication-trust-translated]] line 343 (internal dynamic); mandate T1 (trap: "the pill is internal")
Kind: L
Fidelity: exact
Hyps: none -/
theorem aI_indep_of_dI {OI OE AI AE DI DE DB OH OC V : Type}
    (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC) {Vv : Ω → V} (hV : IsSubvariable S.dI Vv)
    (ω₁ ω₂ : Ω) : ∃ ω, S.aI ω = S.aI ω₁ ∧ Vv ω = Vv ω₂ := by
  obtain ⟨ω, h1, h2⟩ := (factorsAs_iff S.aI S.dI).1 S.I_fac ω₁ ω₂
  exact ⟨ω, h1, hV ω ω₂ h2⟩

end Cleanroom.Udt.UdtCtExamples
