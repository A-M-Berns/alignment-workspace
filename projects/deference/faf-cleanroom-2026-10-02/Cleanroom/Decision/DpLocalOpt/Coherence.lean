import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Ssa

/-!
# `dp-local-opt`: the three local conditions on almost-fair trees (T3(c), third clause)

When no path meets two `d`-nodes, Theorem 1's functional at `d` is the on-occurrence payoff mass
of the pure deviation `C[d ↦ a]` (`siaSum_eq_ssaNum_pure_of_count_le_one`), `V_B` is affine in
`C(d)` (`value_deviate_eq_sum_of_almostFair`, from `dp-core-tree`'s shared-seed affinity and the
agreement of the two semantics on almost-fair trees), and the three conditions coincide:
`Thm1At ⟺ CoherentAt ⟺ CoherentPureAt` (`thm1At_iff_coherentAt_of_almostFair`,
`coherentAt_iff_coherentPureAt_of_almostFair`). v2 comment (ii): "when no path contains two
`d`-nodes, `V_B` is affine in `C(d)` and they coincide".
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

section vanish

variable (C : Proc ι acts K) (d : ι)

/-- Theorem 1's functional vanishes on a subtree that never meets `d`.
Source: none: infrastructure (the "vacuous at `μ(occ(d)) = 0`" clause of `Thm1At`)
Kind: L -/
theorem siaSum_eq_zero_of_count_eq_zero :
    (B : Tree Ω ι acts K) → (∀ ℓ, count d B ℓ = 0) → ∀ a, siaSum C B d a = 0
  | leaf _ _, _, _ => rfl
  | chance _ β child, h, a => by
      rw [siaSum_chance]
      apply Finset.sum_eq_zero
      intro i _
      rw [siaSum_eq_zero_of_count_eq_zero (child i) (fun ℓ => by simpa using h ⟨i, ℓ⟩) a, mul_zero]
  | decision d' child, h, a => by
      haveI : ∀ e, Nonempty (acts e) := fun e => FinDistr.nonempty_of_finDistr (C e)
      have hd : d' ≠ d := by
        intro hd; subst hd
        obtain ⟨ℓ⟩ := leaves_nonempty (child (Classical.arbitrary (acts d')))
        have := h ⟨Classical.arbitrary (acts d'), ℓ⟩
        simp at this
      rw [siaSum_decision_ne C hd]
      apply Finset.sum_eq_zero
      intro b _
      rw [siaSum_eq_zero_of_count_eq_zero (child b) (fun ℓ => by
        have := h ⟨b, ℓ⟩
        simp only [count_decision, hd, if_false, zero_add] at this
        exact this) a, mul_zero]

end vanish

section almostFair

variable (C : Proc ι acts K) (d : ι)

/-- Pull a constant out of an indicator sum.
Source: none: infrastructure
Kind: L -/
theorem sum_ite_mul_left {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (c : K)
    (f : α → K) : (∑ x, if P x then c * f x else 0) = c * ∑ x, if P x then f x else 0 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp

/-- **On a tree meeting `d` at most once per path, Theorem 1's functional is the on-occurrence
payoff mass of the pure deviation**: `Φ_d(C, a) = ∑_{ℓ ∈ occ(d)} μ_{C[d↦a]}(ℓ) r(ℓ)`. (Each leaf of
`occ(d)` lies below exactly one `d`-node, where forcing `a` and deviating to `δ_a` agree.)
Source: [[decision-problems-v2]] §8 comment (ii) ("when no path contains two `d`-nodes, `V_B` is
affine in `C(d)` and they coincide"); mandate T3(c)
Kind: P
Fidelity: exact -/
theorem siaSum_eq_ssaNum_pure_of_count_le_one :
    (B : Tree Ω ι acts K) → (∀ ℓ, count d B ℓ ≤ 1) → ∀ a,
      siaSum C B d a = ∑ ℓ, if 0 < count d B ℓ then leafLaw (C.deviatePure d a) B ℓ * payoff B ℓ
        else 0
  | leaf _ _, _, a => by simp
  | chance _ β child, h, a => by
      rw [siaSum_chance, sum_leaves_chance]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [siaSum_eq_ssaNum_pure_of_count_le_one (child i) (fun ℓ => by simpa using h ⟨i, ℓ⟩) a]
      simp only [count_chance, leafLaw_chance, payoff_chance, mul_assoc]
      rw [sum_ite_mul_left]
  | decision d' child, h, a => by
      rw [sum_leaves_decision]
      by_cases hd : d' = d
      · subst hd
        rw [siaSum_decision_self]
        have hzero : ∀ b, siaSum C (child b) d' a = 0 := fun b =>
          siaSum_eq_zero_of_count_eq_zero C d' (child b) (fun ℓ => by
            have := h ⟨b, ℓ⟩
            simp only [count_decision, if_true] at this
            omega) a
        simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add]
        have hpos : ∀ (b : acts d') (ℓ : (child b).Leaves),
            0 < count d' (decision d' child) ⟨b, ℓ⟩ := fun b ℓ => by
          simp [count_decision]
        simp only [hpos, if_true, leafLaw_decision, payoff_decision, Proc.deviatePure,
          Proc.deviate_same, FinDistr.pure_w]
        rw [Finset.sum_eq_single a]
        · rw [value]
          simp only [if_true, one_mul]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [leafLaw_congr_off_of_count_zero C {d'} (fun e he => Proc.deviate_ne C _ (by simpa using he))
            (child a) ℓ (fun e he => by
              rw [Finset.mem_singleton] at he; subst he
              have := h ⟨a, ℓ⟩
              simp only [count_decision, if_true] at this
              omega)]
        · intro b _ hb
          simp [hb]
        · intro hna; exact absurd (Finset.mem_univ a) hna
      · rw [siaSum_decision_ne C hd]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [siaSum_eq_ssaNum_pure_of_count_le_one (child b) (fun ℓ => by
          have := h ⟨b, ℓ⟩
          simp only [count_decision, hd, if_false, zero_add] at this
          exact this) a]
        simp only [count_decision, hd, if_false, zero_add, leafLaw_decision, payoff_decision,
          Proc.deviatePure, Proc.deviate_ne C _ hd, mul_assoc]
        rw [sum_ite_mul_left]

/-- On a tree meeting `d` at most once per path, `Φ_d(C, a) = ssaNum(δ_a)`.
Source: mandate T3(c)
Kind: L -/
theorem siaSum_eq_ssaNum_pure (B : Tree Ω ι acts K) (h : ∀ ℓ, count d B ℓ ≤ 1) (a : acts d) :
    siaSum C B d a = ssaNum C B d (FinDistr.pure a) := by
  rw [siaSum_eq_ssaNum_pure_of_count_le_one C d B h a, ssaNum, occ, Finset.sum_filter]

/-- On a tree meeting `d` at most once per path, `V_B(C[d ↦ a]) = Φ_d(C, a) + offOcc`.
Source: mandate T3(c) ("`siaSum C B d a = value (C.deviatePure d a) B − offOcc C B d` when
`#_d ≤ 1`")
Kind: C -/
theorem value_deviatePure_eq_siaSum_add_offOcc (B : Tree Ω ι acts K) (h : ∀ ℓ, count d B ℓ ≤ 1)
    (a : acts d) :
    value (C.deviatePure d a) B = siaSum C B d a + offOcc C B d := by
  rw [Proc.deviatePure, value_deviate_eq_ssaNum_add_offOcc, siaSum_eq_ssaNum_pure C d B h a]

/-- Deviating twice at `d` is deviating once.
Source: none: infrastructure
Kind: L -/
theorem Proc.deviate_deviate (m m' : FinDistr K (acts d)) :
    (C.deviate d m).deviate d m' = C.deviate d m' := by
  unfold Proc.deviate; simp

/-- **Affinity of `V_B` in `C(d)` on almost-fair trees**: `V_B(C[d ↦ m]) = ∑_a m(a) V_B(C[d ↦ a])`
(from the shared-seed affinity `value'_deviate_sum` and the agreement of the two semantics on
almost-fair trees).
Source: [[decision-problems-v2]] §8 comment (ii); A30 ("When no path contains two `d`-nodes,
`V_B` is affine in `C(d)` and the two quantifications agree"); `seeds.md` SE-1(b), SE-2 Cor.
Kind: C -/
theorem value_deviate_eq_sum_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B)
    (m : FinDistr K (acts d)) :
    value (C.deviate d m) B = ∑ a, m.w a * value (C.deviatePure d a) B := by
  rw [h.value_eq_value', value'_deviate_sum _ B d]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Proc.deviate_same, Proc.deviatePure, Proc.deviate_deviate, ← Proc.deviatePure,
    h.value_eq_value']

/-- On almost-fair trees `V_B(C) = ∑_a C(d)(a) V_B(C[d ↦ a])`.
Source: [[decision-problems-v2]] §8 comment (ii)
Kind: L -/
theorem value_eq_sum_deviatePure_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B) :
    value C B = ∑ a, (C d).w a * value (C.deviatePure d a) B := by
  have := value_deviate_eq_sum_of_almostFair C d h (C d)
  have hself : C.deviate d (C d) = C := by
    funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  rwa [hself] at this

/-- **Affinity of `V_B` in `C(d)` when `#_d ≤ 1` on every path** — the per-point form of comment
(ii) (v2: "when no path contains two `d`-nodes"): `V_B(C[d ↦ m]) = ∑_a m(a) V_B(C[d ↦ a])`. By
structural recursion: below a `d`-node the path never meets `d` again, so the deviation is
invisible there (`leafLaw_congr_off_of_count_zero`); at every other node the identity passes
through the node's convex combination.
Source: [[decision-problems-v2]] §8 comment (ii); A30 ("When no path contains two `d`-nodes,
`V_B` is affine in `C(d)`"); audit r1 fidelity non-blocking 1 (per-point hypothesis)
Kind: P
Fidelity: exact (the comment's per-point hypothesis, not global almost-fairness) -/
theorem value_deviate_eq_sum_of_count_le_one :
    (B : Tree Ω ι acts K) → (∀ ℓ, count d B ℓ ≤ 1) → ∀ m : FinDistr K (acts d),
      value (C.deviate d m) B = ∑ a, m.w a * value (C.deviatePure d a) B
  | leaf _ _, _, m => by
      simp only [value_leaf, ← Finset.sum_mul, m.sum_one, one_mul]
  | chance _ β child, h, m => by
      have ih : ∀ i, value (C.deviate d m) (child i) =
          ∑ a, m.w a * value (C.deviatePure d a) (child i) := fun i =>
        value_deviate_eq_sum_of_count_le_one (child i) (fun ℓ => by simpa using h ⟨i, ℓ⟩) m
      simp only [value_chance, ih, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
  | decision d' child, h, m => by
      by_cases hd : d' = d
      · subst hd
        have hno : ∀ b (C' : Proc ι acts K), (∀ e, e ≠ d' → C' e = C e) →
            value C' (child b) = value C (child b) := fun b C' hC' => by
          unfold value
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [leafLaw_congr_off_of_count_zero C {d'} (fun e he => hC' e (by simpa using he))
            (child b) ℓ (fun e he => by
              rw [Finset.mem_singleton] at he; subst he
              have := h ⟨b, ℓ⟩
              simp only [count_decision, if_true] at this
              omega)]
        rw [value_decision, Proc.deviate_same]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hno b _ (fun e he => Proc.deviate_ne C _ he), value_decision, Proc.deviatePure,
          Proc.deviate_same, Finset.sum_eq_single b]
        · rw [hno b _ (fun e he => Proc.deviate_ne C _ he)]
          simp [FinDistr.pure_w]
        · intro c _ hc
          simp [FinDistr.pure_w, hc]
        · intro hnb; exact absurd (Finset.mem_univ b) hnb
      · have ih : ∀ b, value (C.deviate d m) (child b) =
            ∑ a, m.w a * value (C.deviatePure d a) (child b) := fun b =>
          value_deviate_eq_sum_of_count_le_one (child b) (fun ℓ => by
            have := h ⟨b, ℓ⟩
            simp only [count_decision, hd, if_false, zero_add] at this
            exact this) m
        simp only [value_decision, Proc.deviate_ne C _ hd, ih, Proc.deviatePure, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- When `#_d ≤ 1` on every path, `V_B(C) = ∑_a C(d)(a) V_B(C[d ↦ a])`.
Source: [[decision-problems-v2]] §8 comment (ii)
Kind: L -/
theorem value_eq_sum_deviatePure_of_count_le_one {B : Tree Ω ι acts K}
    (h : ∀ ℓ, count d B ℓ ≤ 1) :
    value C B = ∑ a, (C d).w a * value (C.deviatePure d a) B := by
  have := value_deviate_eq_sum_of_count_le_one C d B h (C d)
  have hself : C.deviate d (C d) = C := by
    funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  rwa [hself] at this

/-- **Per-point comment (ii): when no path contains two `d`-nodes, Theorem 1's condition at `d`,
mixed coherence at `d` and pure coherence at `d` coincide** — the hypothesis is the comment's own
(`#_d ≤ 1` on every path, for this `d` only), not global almost-fairness.
Source: [[decision-problems-v2]] §8 comment (ii) ("when no path contains two `d`-nodes … they
coincide") | A30 | A31 | dp-core-049; audit r1 fidelity non-blocking 1
Kind: C
Fidelity: exact
Hyps: (a) `∀ ℓ, #_d(ℓ) ≤ 1` (the comment's hypothesis) -/
theorem thm1At_iff_coherentAt_of_count_le_one {B : Tree Ω ι acts K}
    (h : ∀ ℓ, count d B ℓ ≤ 1) :
    (Thm1At C B d ↔ CoherentAt C B d) ∧ (CoherentAt C B d ↔ CoherentPureAt C B d) := by
  have hpm : CoherentPureAt C B d → CoherentAt C B d := by
    intro hc m
    rw [value_deviate_eq_sum_of_count_le_one C d B h m]
    calc ∑ a, m.w a * value (C.deviatePure d a) B ≤ ∑ a, m.w a * value C B :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hc a) (m.nonneg a)
      _ = value C B := by rw [← Finset.sum_mul, m.sum_one, one_mul]
  have htp : Thm1At C B d → CoherentPureAt C B d := by
    intro ht b
    rw [value_eq_sum_deviatePure_of_count_le_one C d h]
    have hle : ∀ a, 0 < (C d).w a →
        value (C.deviatePure d b) B ≤ value (C.deviatePure d a) B := by
      intro a ha
      rw [value_deviatePure_eq_siaSum_add_offOcc C d B h,
        value_deviatePure_eq_siaSum_add_offOcc C d B h]
      exact add_le_add (ht a ha b) le_rfl
    calc value (C.deviatePure d b) B = ∑ a, (C d).w a * value (C.deviatePure d b) B := by
          rw [← Finset.sum_mul, (C d).sum_one, one_mul]
      _ ≤ ∑ a, (C d).w a * value (C.deviatePure d a) B := by
          apply Finset.sum_le_sum
          intro a _
          rcases ((C d).nonneg a).lt_or_eq with ha | ha
          · exact mul_le_mul_of_nonneg_left (hle a ha) ha.le
          · rw [← ha]; simp
  exact ⟨⟨fun ht => hpm (htp ht), fun hc => thm1At_of_coherentAt C B d hc⟩,
    ⟨fun hc => CoherentAt.pure C B hc, hpm⟩⟩

/-- **On almost-fair trees pure coherence at `d` implies mixed coherence at `d`** (a mixed
deviation is a convex combination of pure ones).
Source: A30; mandate T3(a) ("on almost-fair trees pure ⟺ mixed")
Kind: C -/
theorem coherentAt_of_coherentPureAt_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B)
    (hc : CoherentPureAt C B d) : CoherentAt C B d := by
  intro m
  rw [value_deviate_eq_sum_of_almostFair C d h m]
  calc ∑ a, m.w a * value (C.deviatePure d a) B ≤ ∑ a, m.w a * value C B :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hc a) (m.nonneg a)
    _ = value C B := by rw [← Finset.sum_mul, m.sum_one, one_mul]

/-- **On almost-fair trees Theorem 1's condition at `d` implies pure coherence at `d`**: the
functional is `V_B(C[d ↦ ·]) − offOcc`, so the support of `C(d)` lies in
`argmax_a V_B(C[d ↦ a])`, and `V_B(C)` is the `C(d)`-average of those values.
Source: [[decision-problems-v2]] §8 comment (ii); mandate T3(c)
Kind: C -/
theorem coherentPureAt_of_thm1At_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B)
    (ht : Thm1At C B d) : CoherentPureAt C B d := by
  intro b
  have hcount : ∀ ℓ, count d B ℓ ≤ 1 := fun ℓ => h d ℓ
  rw [value_eq_sum_deviatePure_of_almostFair C d h]
  have hle : ∀ a, 0 < (C d).w a → value (C.deviatePure d b) B ≤ value (C.deviatePure d a) B := by
    intro a ha
    rw [value_deviatePure_eq_siaSum_add_offOcc C d B hcount,
      value_deviatePure_eq_siaSum_add_offOcc C d B hcount]
    exact add_le_add (ht a ha b) le_rfl
  calc value (C.deviatePure d b) B = ∑ a, (C d).w a * value (C.deviatePure d b) B := by
        rw [← Finset.sum_mul, (C d).sum_one, one_mul]
    _ ≤ ∑ a, (C d).w a * value (C.deviatePure d a) B := by
        apply Finset.sum_le_sum
        intro a _
        rcases ((C d).nonneg a).lt_or_eq with ha | ha
        · exact mul_le_mul_of_nonneg_left (hle a ha) ha.le
        · rw [← ha]; simp

/-- **Comment (ii): on almost-fair trees Theorem 1's condition and mixed coherence coincide.**
Source: [[decision-problems-v2]] §8 comment (ii) ("when no path contains two `d`-nodes … they
coincide") | A31 | dp-core-049
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B` (the comment's hypothesis) -/
theorem thm1At_iff_coherentAt_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B) :
    Thm1At C B d ↔ CoherentAt C B d :=
  ⟨fun ht => coherentAt_of_coherentPureAt_of_almostFair C d h
      (coherentPureAt_of_thm1At_of_almostFair C d h ht),
    fun hc => thm1At_of_coherentAt C B d hc⟩

/-- **A30's caveat: on almost-fair trees the pure and mixed forms of Definition 22 agree.**
Source: A30 ("When no path contains two `d`-nodes, `V_B` is affine in `C(d)` and the two
quantifications agree") | mandate T3(a)
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B` -/
theorem coherentAt_iff_coherentPureAt_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B) :
    CoherentAt C B d ↔ CoherentPureAt C B d :=
  ⟨fun hc => CoherentAt.pure C B hc, coherentAt_of_coherentPureAt_of_almostFair C d h⟩

/-- On almost-fair trees `Thm1 ⟺ Coherent ⟺ CoherentPure` at every queried point.
Source: [[decision-problems-v2]] §8 comment (ii); A30
Kind: C -/
theorem thm1_iff_coherent_of_almostFair {B : Tree Ω ι acts K} (h : AlmostFair B) :
    (Thm1 C B ↔ Coherent C B) ∧ (Coherent C B ↔ CoherentPure C B) := by
  refine ⟨?_, ?_⟩
  · unfold Thm1 Coherent
    exact forall₂_congr fun d _ => thm1At_iff_coherentAt_of_almostFair C d h
  · unfold Coherent CoherentPure
    exact forall₂_congr fun d _ => coherentAt_iff_coherentPureAt_of_almostFair C d h

end almostFair

/-! ### T16(ii): on a one-point tree mixed Definition 22 is literally optimality -/

section onePoint

variable {Ω : Type} {acts : Unit → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **On a one-point tree, mixed coherence at the point is optimality** (every procedure is a
point-deviation of `C`): Definition 22's sufficiency gap lives only across points.
Source: mandate T16(ii) ("on a one-point tree `CoherentAt` (mixed) is literally `IsOptimal`");
audit r1 fidelity non-blocking 8 (general one-point form)
Kind: L
Fidelity: exact (any action set, any field) -/
theorem coherentAt_iff_isOptimal_of_unit (C : Proc Unit acts K) (B : Tree Ω Unit acts K) :
    CoherentAt C B () ↔ IsOptimal C B := by
  have h : ∀ C' : Proc Unit acts K, C.deviate () (C' ()) = C' := fun C' => by
    funext u; cases u; simp
  constructor
  · intro hc C'; rw [← h C']; exact hc _
  · intro ho m; exact ho _

end onePoint

end Cleanroom.Decision.DpLocalOpt
