import Cleanroom.Fixpoint.FixOraclesCorresp.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fin.VecNotation

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Correlated`: the correlated lift

Target 7, first half (fixpoint-lit-009): for a relation `R` on a finite `X`, a **correlated fixed
point** is a probability measure `ν` on `X × X` supported on `R` whose two marginals agree. This is the
survey agent's precise version of both of Scott's examples (ATTRIBUTION-UNVETTED as a reading of Scott):
for negation on `Fin 2` the unique correlated fixed point puts mass `1/2` on `(0,1)` and `(1,0)` — "all
mass on 50 %" is literally true — and for the identity the correlated fixed points are exactly the
measures on the diagonal, with marginal map onto `Δ(X)`.

Existence for total relations is **Kakutani-free** (`exists_correlatedFixedPoint`): pick a selection
`f`, a periodic point of `f` (pigeonhole on the iterates), and put uniform mass on the cycle's edges
`(fᵏ x, fᵏ⁺¹ x)`; the two marginals agree because shifting the index along a cycle is a bijection.
Non-total relations can have none (`R = {(0,1)}`).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Correlated fixed point** of a relation `R` on `X`: `ν ∈ Δ(X × X)`, supported on `R`, with equal
marginals `∑ b, ν (a, b) = ∑ b, ν (b, a)` for every `a`.
Source: [[fixpoint-lit-inventory]] 009 (conversation-notes §4 "any relation at level `n` can be
represented as a convex relation at level `n+1`"; the survey agent's precise reading)
Kind: D
Fidelity: exact (for the survey's definition; the notes have no precise statement)
Hyps: n/a -/
def IsCorrelatedFixedPoint (R : X → X → Prop) (ν : X × X → ℝ) : Prop :=
  ν ∈ stdSimplex ℝ (X × X) ∧ (∀ a b, ν (a, b) ≠ 0 → R a b) ∧ ∀ a, ∑ b, ν (a, b) = ∑ b, ν (b, a)

omit [DecidableEq X] in
/-- **Periodic points exist on a finite type**: for any `f : X → X` there are `x` and `m > 0` with
`f^[m] x = x` (pigeonhole on the orbit of any point).
Source: [[fixpoint-lit-inventory]] 009 (i) ("a periodic orbit of `f` (exists on finite `X`)")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_periodic_point [Nonempty X] (f : X → X) : ∃ x : X, ∃ m : ℕ, 0 < m ∧ f^[m] x = x := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite fun n : ℕ => f^[n] (Classical.arbitrary X)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨f^[i] (Classical.arbitrary X), j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact h.symm
  · refine ⟨f^[j] (Classical.arbitrary X), i - j, Nat.sub_pos_of_lt hgt, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hgt.le]
    exact h

/-- The indicator of a single edge `e`, as a real-valued function on `X × X`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def edgeInd (e q : X × X) : ℝ := if q = e then 1 else 0

/-- Row-marginal of an edge indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_edgeInd_fst (c d a : X) : ∑ b, edgeInd (c, d) (a, b) = if a = c then 1 else 0 := by
  by_cases h : a = c
  · subst h; simp [edgeInd, Prod.ext_iff]
  · simp [edgeInd, Prod.ext_iff, h]

/-- Column-marginal of an edge indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_edgeInd_snd (c d a : X) : ∑ b, edgeInd (c, d) (b, a) = if a = d then 1 else 0 := by
  by_cases h : a = d
  · subst h; simp [edgeInd, Prod.ext_iff]
  · simp [edgeInd, Prod.ext_iff, h]

/-- Total mass of an edge indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_edgeInd (e : X × X) : ∑ q, edgeInd e q = 1 := by
  simp [edgeInd, Finset.sum_ite_eq']

/-- Shifting a sum along a cycle: if `g m = g 0` then `∑ k < m, g (k + 1) = ∑ k < m, g k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_range_shift (g : ℕ → ℝ) (m : ℕ) (h : g m = g 0) :
    ∑ k ∈ range m, g (k + 1) = ∑ k ∈ range m, g k := by
  have h1 := Finset.sum_range_succ' g m
  have h2 := Finset.sum_range_succ g m
  linarith

/-- **The cycle measure**: uniform mass on the `m` edges `(f^[k] x, f^[k+1] x)`, `k < m`.
Source: [[fixpoint-lit-inventory]] 009 (i) ("let `ν` be uniform on `{(x, f(x))}` along the orbit")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def cycleMeasure (f : X → X) (x : X) (m : ℕ) (q : X × X) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k ∈ range m, edgeInd (f^[k] x, f^[k + 1] x) q

/-- **Target 7 (i): total relations have correlated fixed points, Kakutani-free.** If every `a` has
some `b` with `R a b`, then a correlated fixed point of `R` exists: the cycle measure of a selection
along one of its periodic orbits.
Source: [[fixpoint-lit-inventory]] 009 (i)
Kind: P
Fidelity: exact
Hyps: (a) none (`Nonempty X` is needed: `Δ(∅ × ∅)` is empty) -/
theorem exists_correlatedFixedPoint [Nonempty X] (R : X → X → Prop) (htot : ∀ a, ∃ b, R a b) :
    ∃ ν, IsCorrelatedFixedPoint R ν := by
  choose f hf using htot
  obtain ⟨x, m, hm, hx⟩ := exists_periodic_point f
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨cycleMeasure f x m, ⟨fun q => ?_, ?_⟩, ?_, ?_⟩
  · unfold cycleMeasure
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ?_)
    unfold edgeInd; split_ifs <;> norm_num
  · unfold cycleMeasure
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [sum_edgeInd, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hm'
  · intro a b hab
    unfold cycleMeasure at hab
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hab)
    unfold edgeInd at hk
    split_ifs at hk with h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Function.iterate_succ_apply']
      exact hf _
    · exact absurd rfl hk
  · intro a
    unfold cycleMeasure
    simp only [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm, Finset.sum_comm (f := fun b k => edgeInd (f^[k] x, f^[k + 1] x) (b, a))]
    simp only [sum_edgeInd_fst, sum_edgeInd_snd]
    symm
    refine sum_range_shift (fun k => if a = f^[k] x then 1 else 0) m ?_
    simp only [hx, Function.iterate_zero_apply]
    by_cases h : a = x <;> simp [h]

/-! ### Instances on `Fin 2` -/

/-- Negation as a relation on `Fin 2`: `a ≠ b`.
Source: [[fixpoint-lit-inventory]] 009 (ii)
Kind: D
Fidelity: exact
Hyps: n/a -/
def negRel (a b : Fin 2) : Prop := a ≠ b

/-- The uniform measure on the two off-diagonal edges.
Source: [[fixpoint-lit-inventory]] 009 (ii)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def negFixed (q : Fin 2 × Fin 2) : ℝ := if q.1 = q.2 then 0 else 1 / 2

/-- **Target 7 (ii): the unique correlated fixed point of negation** puts mass `1/2` on `(0, 1)` and
`(1, 0)` — "negation's fixed point puts all mass on 50 %", literally.
Source: [[fixpoint-lit-inventory]] 009 (ii); README "negation ↦ mass on 50 %" (ATTRIBUTION-UNVETTED
that this is Scott's reading)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem isCorrelatedFixedPoint_negRel_iff (ν : Fin 2 × Fin 2 → ℝ) :
    IsCorrelatedFixedPoint negRel ν ↔ ν = negFixed := by
  constructor
  · rintro ⟨⟨hnn, hsum⟩, hsupp, hmarg⟩
    have h00 : ν (0, 0) = 0 := by
      by_contra h; exact hsupp 0 0 h rfl
    have h11 : ν (1, 1) = 0 := by
      by_contra h; exact hsupp 1 1 h rfl
    have hm := hmarg 0
    simp only [Fin.sum_univ_two] at hm hsum
    rw [Fintype.sum_prod_type] at hsum
    simp only [Fin.sum_univ_two] at hsum
    funext ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [negFixed] <;> linarith
  · rintro rfl
    refine ⟨⟨fun q => ?_, ?_⟩, ?_, ?_⟩
    · unfold negFixed; split_ifs <;> norm_num
    · rw [Fintype.sum_prod_type]; simp [Fin.sum_univ_two, negFixed]; norm_num
    · intro a b h
      unfold negFixed at h
      intro hab
      exact h (if_pos hab)
    · intro a
      fin_cases a <;> simp [Fin.sum_univ_two, negFixed]

/-- The marginal of negation's correlated fixed point is the uniform distribution `![1/2, 1/2]`.
Source: [[fixpoint-lit-inventory]] 009 (ii) ("with marginal `(½, ½)`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem negFixed_marginal : (fun a => ∑ b, negFixed (a, b)) = ![1 / 2, 1 / 2] := by
  funext a
  fin_cases a <;> simp [Fin.sum_univ_two, negFixed]

omit [DecidableEq X] in
/-- **Target 7 (iii): the correlated fixed points of the identity are exactly the measures on the
diagonal** (the marginal condition is automatic there).
Source: [[fixpoint-lit-inventory]] 009 (iii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isCorrelatedFixedPoint_eq_iff (ν : X × X → ℝ) :
    IsCorrelatedFixedPoint (fun a b => a = b) ν ↔
      ν ∈ stdSimplex ℝ (X × X) ∧ ∀ a b, ν (a, b) ≠ 0 → a = b := by
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, fun a => ?_⟩
    rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
    · intro b _ hb
      by_contra h
      exact hb (h2 b a h)
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      by_contra h
      exact hb (h2 a b h).symm
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The diagonal measure of `p ∈ Δ(X)`: `ν (a, b) = p a` if `a = b`, else `0`.
Source: [[fixpoint-lit-inventory]] 009 (iii) (`∑ p(x) δ_{(x,x)}`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def diagMeasure (p : X → ℝ) (q : X × X) : ℝ := if q.1 = q.2 then p q.1 else 0

/-- **Target 7 (iii), surjectivity**: every `p ∈ Δ(X)` is the marginal of a correlated fixed point of
the identity — "the identity spreads over all of `Δ(X)`", literally.
Source: [[fixpoint-lit-inventory]] 009 (iii); README "identity ↦ spread over all of Δ(X)"
(ATTRIBUTION-UNVETTED that this is Scott's reading)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exists_correlatedFixedPoint_eq_marginal {p : X → ℝ} (hp : p ∈ stdSimplex ℝ X) :
    ∃ ν, IsCorrelatedFixedPoint (fun a b => a = b) ν ∧ (fun a => ∑ b, ν (a, b)) = p := by
  refine ⟨diagMeasure p, (isCorrelatedFixedPoint_eq_iff _).2 ⟨⟨fun q => ?_, ?_⟩, ?_⟩, ?_⟩
  · unfold diagMeasure; split_ifs
    · exact hp.1 _
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    simp only [diagMeasure]
    simp [Finset.sum_ite_eq, hp.2]
  · intro a b h
    unfold diagMeasure at h
    by_contra hab
    exact h (if_neg hab)
  · funext a
    simp [diagMeasure, Finset.sum_ite_eq]

/-- **Target 7 (iv): a non-total relation can have no correlated fixed point**: `R = {(0, 1)}` on
`Fin 2` (the only admissible measure is `δ_{(0,1)}`, whose marginals differ).
Source: [[fixpoint-lit-inventory]] 009 (iv)
Kind: N-
Fidelity: exact
Hyps: (a) none -/
theorem not_exists_correlatedFixedPoint_single :
    ¬ ∃ ν, IsCorrelatedFixedPoint (fun a b : Fin 2 => a = 0 ∧ b = 1) ν := by
  rintro ⟨ν, ⟨-, hsum⟩, hsupp, hmarg⟩
  have h00 : ν (0, 0) = 0 := by
    by_contra h; exact absurd (hsupp 0 0 h).2 (by decide)
  have h10 : ν (1, 0) = 0 := by
    by_contra h; exact absurd (hsupp 1 0 h).1 (by decide)
  have h11 : ν (1, 1) = 0 := by
    by_contra h; exact absurd (hsupp 1 1 h).1 (by decide)
  have hm := hmarg 0
  rw [Fintype.sum_prod_type] at hsum
  simp only [Fin.sum_univ_two] at hm hsum
  linarith

end Cleanroom.Fixpoint.FixOraclesCorresp
