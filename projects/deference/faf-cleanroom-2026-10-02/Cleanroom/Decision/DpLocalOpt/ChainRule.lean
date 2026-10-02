import Cleanroom.Decision.DpLocalOpt.Sia

/-!
# `dp-local-opt`: the chain rule (T2) and mixed Definition 22 ⟹ Theorem 1 (T3(b))

v2 §8's proof of Theorem 1 differentiates `V_B` along the fiber of `d` ("applying the chain rule
over the fiber of `d`: `∂V/∂C(d)(a) = ∑_{q : d_q = d} R_q G_q(a)`"). Over a linearly ordered
field there is no derivative, so the chain rule is stated as a **finite-difference expansion**:
moving `C(d)` toward `m` by `ε ∈ [0,1]` changes `V_B` by `ε · ∑_a (m(a) − C(d)(a)) Φ_d(C, a)` plus
`ε²` times a remainder bounded on `[0,1]`. The proof is structural (mandate route A, in the
node-equation form): at a `d`-node the deviated weight `C(d)(b) + ε (m(b) − C(d)(b))` multiplies
the child's expansion, and the product's first-order coefficient is exactly `siaSum`'s recursion.

The consequence `thm1At_of_coherentAt` (ZO-6 / A31) is the package's central lemma: at a maximum
of `m ↦ V_B(C[d ↦ m])` over the simplex the first-order term toward every `δ_b` is `≤ 0`, so
every action in the support of `C(d)` attains `max_b Φ_d(C, b)`.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)]

/-! ### Convex interpolation of distributions -/

/-- The mixed action `(1 − ε) p + ε m` for `ε ∈ [0,1]`: the segment from `p` toward `m`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("first-order necessity … for all
`r ∈ Δ(A_d)`"); mandate T2 (`C_ε := C[d ↦ lerp ε (C d) m]`)
Kind: D -/
def FinDistr.lerp {α : Type} [Fintype α] (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (p m : FinDistr K α) : FinDistr K α where
  w a := (1 - ε) * p.w a + ε * m.w a
  nonneg a := add_nonneg (mul_nonneg (by linarith) (p.nonneg a)) (mul_nonneg h0 (m.nonneg a))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.sum_one, m.sum_one]; ring

/-- Weight of the interpolation.
Source: none: infrastructure
Kind: L -/
@[simp] theorem FinDistr.lerp_w {α : Type} [Fintype α] (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (p m : FinDistr K α) (a : α) :
    (FinDistr.lerp ε h0 h1 p m).w a = (1 - ε) * p.w a + ε * m.w a := rfl

/-! ### The first-order functional -/

section lin

variable [DecidableEq ι] (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d))

/-- The first-order coefficient of `V_B` along the direction `m − C(d)` at `d`:
`∑_a (m(a) − C(d)(a)) · Φ_d(C, a)` — v2's `∑_a (r_a − C(d)(a)) ∂V/∂C(d)(a)`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof
Kind: D -/
def lin (B : Tree Ω ι acts K) : K :=
  ∑ a, (m.w a - (C d).w a) * siaSum C B d a

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem lin_leaf (ω : Ω) (r : K) : lin C d m (leaf ω r : Tree Ω ι acts K) = 0 := by
  simp [lin]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem lin_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    lin C d m (chance n β child) = ∑ i, β.w i * lin C d m (child i) := by
  unfold lin
  simp only [siaSum_chance, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem lin_decision_self (child : acts d → Tree Ω ι acts K) :
    lin C d m (decision d child) =
      (∑ b, (C d).w b * lin C d m (child b)) + ∑ a, (m.w a - (C d).w a) * value C (child a) := by
  unfold lin
  simp only [siaSum_decision_self, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem lin_decision_ne {d' : ι} (h : d' ≠ d) (child : acts d' → Tree Ω ι acts K) :
    lin C d m (decision d' child) = ∑ b, (C d').w b * lin C d m (child b) := by
  unfold lin
  simp only [siaSum_decision_ne C h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- The first-order coefficient toward `δ_b` is `Φ_d(C, b) − ∑_a C(d)(a) Φ_d(C, a)`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof; mandate T3(b) ("read off …")
Kind: L -/
theorem lin_pure [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) (b : acts d) :
    lin C d (FinDistr.pure b) B = siaSum C B d b - ∑ a, (C d).w a * siaSum C B d a := by
  unfold lin
  simp only [FinDistr.pure_w, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end lin

/-! ### The chain rule -/

section chain

variable [DecidableEq ι] (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d))

/-- The deviated weight at `d` along the segment: `C(d)(b) + ε (m(b) − C(d)(b))`.
Source: none: infrastructure
Kind: L -/
theorem deviate_lerp_same (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (b : acts d) :
    (C.deviate d (FinDistr.lerp ε h0 h1 (C d) m) d).w b =
      (1 - ε) * (C d).w b + ε * m.w b := by
  rw [Proc.deviate_same, FinDistr.lerp_w]

/-- A difference of two weights in `[0,1]` has absolute value at most one.
Source: none: infrastructure
Kind: L -/
theorem abs_sub_w_le_one {α : Type} [Fintype α] (p m : FinDistr K α) (a : α) :
    |m.w a - p.w a| ≤ 1 := by
  have h1 := p.nonneg a; have h2 := p.w_le_one a
  have h3 := m.nonneg a; have h4 := m.w_le_one a
  rw [abs_le]; constructor <;> linarith

/-- **The chain rule (T2), finite-difference form.** For every tree `B` (self-succession
included), every `C`, `d`, `m ∈ Δ(A_d)`, there is a remainder `R` bounded on `[0,1]` with
`V_B(C[d ↦ (1−ε) C(d) + ε m]) = V_B(C) + ε · ∑_a (m(a) − C(d)(a)) Φ_d(C, a) + ε² · R(ε)` for all
`ε ∈ [0,1]`, where `Φ_d(C, a) = siaSum C B d a = ∑_{q : d_q = d} R_q(C) G_q(C, a)`
(`siaSum_eq_sum_fiber_forcedBelow`). Proved by structural recursion: at a `d`-node the weight
`C(d)(b) + ε(m(b) − C(d)(b))` multiplies the child's expansion.
Source: [[decision-problems-v2]] §8 Theorem 1 proof (line 268, the chain rule over the fiber);
dp-cf-051; dp-cf-2-046 ("the real lemma"); dp-cf-2-019
Kind: P
Fidelity: exact (finite-difference form of v2's derivative; remainder bounded, not
differentiable) | variant: payoffs in a linearly ordered field
Scope: Definition 6 (independent redraws); every tree, self-succession included
Hyps: (a) all -/
theorem value_lerp_deviate_eq :
    (B : Tree Ω ι acts K) →
      ∃ (R : K → K) (M : K), (∀ ε, 0 ≤ ε → ε ≤ 1 → |R ε| ≤ M) ∧
        ∀ ε (h0 : 0 ≤ ε) (h1 : ε ≤ 1),
          value (C.deviate d (FinDistr.lerp ε h0 h1 (C d) m)) B =
            value C B + ε * lin C d m B + ε ^ 2 * R ε
  | leaf ω r => ⟨fun _ => 0, 0, fun _ _ _ => by simp, fun ε _ _ => by simp⟩
  | chance n β child => by
      choose R M hM hR using fun i => value_lerp_deviate_eq (child i)
      refine ⟨fun ε => ∑ i, β.w i * R i ε, ∑ i, M i, ?_, ?_⟩
      · intro ε h0 h1
        calc |∑ i, β.w i * R i ε| ≤ ∑ i, |β.w i * R i ε| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, M i := Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_of_nonneg (β.nonneg i)]
              calc β.w i * |R i ε| ≤ 1 * |R i ε| :=
                    mul_le_mul_of_nonneg_right (β.w_le_one i) (abs_nonneg _)
                _ = |R i ε| := one_mul _
                _ ≤ M i := hM i ε h0 h1
      · intro ε h0 h1
        rw [value_chance, value_chance, lin_chance]
        simp only [hR _ ε h0 h1, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
  | decision d' child => by
      choose R M hM hR using fun b => value_lerp_deviate_eq (child b)
      by_cases hd : d' = d
      · subst hd
        refine ⟨fun ε => ∑ b, ((C d').w b * R b ε + (m.w b - (C d').w b) * lin C d' m (child b) +
            ε * (m.w b - (C d').w b) * R b ε), ∑ b, (2 * M b + |lin C d' m (child b)|), ?_, ?_⟩
        · intro ε h0 h1
          have hMnn : ∀ b, 0 ≤ M b := fun b => (abs_nonneg _).trans (hM b 0 le_rfl zero_le_one)
          calc |∑ b, ((C d').w b * R b ε + (m.w b - (C d').w b) * lin C d' m (child b) +
                ε * (m.w b - (C d').w b) * R b ε)|
              ≤ ∑ b, |(C d').w b * R b ε + (m.w b - (C d').w b) * lin C d' m (child b) +
                ε * (m.w b - (C d').w b) * R b ε| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ b, (2 * M b + |lin C d' m (child b)|) := Finset.sum_le_sum fun b _ => by
                have e1 : |(C d').w b * R b ε| ≤ M b := by
                  rw [abs_mul, abs_of_nonneg ((C d').nonneg b)]
                  calc (C d').w b * |R b ε| ≤ 1 * |R b ε| :=
                        mul_le_mul_of_nonneg_right ((C d').w_le_one b) (abs_nonneg _)
                    _ = |R b ε| := one_mul _
                    _ ≤ M b := hM b ε h0 h1
                have e2 : |(m.w b - (C d').w b) * lin C d' m (child b)| ≤ |lin C d' m (child b)| := by
                  rw [abs_mul]
                  calc |m.w b - (C d').w b| * |lin C d' m (child b)|
                      ≤ 1 * |lin C d' m (child b)| :=
                        mul_le_mul_of_nonneg_right (abs_sub_w_le_one _ _ _) (abs_nonneg _)
                    _ = _ := one_mul _
                have e3 : |ε * (m.w b - (C d').w b) * R b ε| ≤ M b := by
                  rw [abs_mul, abs_mul, abs_of_nonneg h0]
                  calc ε * |m.w b - (C d').w b| * |R b ε| ≤ 1 * 1 * |R b ε| := by
                        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                        exact mul_le_mul h1 (abs_sub_w_le_one _ _ _) (abs_nonneg _) zero_le_one
                    _ = |R b ε| := by ring
                    _ ≤ M b := hM b ε h0 h1
                calc |(C d').w b * R b ε + (m.w b - (C d').w b) * lin C d' m (child b) +
                      ε * (m.w b - (C d').w b) * R b ε|
                    ≤ |(C d').w b * R b ε + (m.w b - (C d').w b) * lin C d' m (child b)| +
                      |ε * (m.w b - (C d').w b) * R b ε| := abs_add_le _ _
                  _ ≤ (|(C d').w b * R b ε| + |(m.w b - (C d').w b) * lin C d' m (child b)|) +
                      |ε * (m.w b - (C d').w b) * R b ε| :=
                        add_le_add (abs_add_le _ _) le_rfl
                  _ ≤ (M b + |lin C d' m (child b)|) + M b := by gcongr
                  _ = 2 * M b + |lin C d' m (child b)| := by ring
        · intro ε h0 h1
          rw [value_decision, value_decision, lin_decision_self]
          simp only [deviate_lerp_same, hR _ ε h0 h1, mul_add, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring
      · refine ⟨fun ε => ∑ b, (C d').w b * R b ε, ∑ b, M b, ?_, ?_⟩
        · intro ε h0 h1
          calc |∑ b, (C d').w b * R b ε| ≤ ∑ b, |(C d').w b * R b ε| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ b, M b := Finset.sum_le_sum fun b _ => by
                rw [abs_mul, abs_of_nonneg ((C d').nonneg b)]
                calc (C d').w b * |R b ε| ≤ 1 * |R b ε| :=
                      mul_le_mul_of_nonneg_right ((C d').w_le_one b) (abs_nonneg _)
                  _ = |R b ε| := one_mul _
                  _ ≤ M b := hM b ε h0 h1
        · intro ε h0 h1
          rw [value_decision, value_decision, lin_decision_ne C d m hd]
          simp only [Proc.deviate_ne _ _ hd, hR _ ε h0 h1, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring

end chain

/-! ### Mixed Definition 22 implies Theorem 1's condition -/

section zo6

variable [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K) (B : Tree Ω ι acts K)
  (d : ι)

/-- **First-order necessity.** If no mixed point-deviation at `d` improves `V_B`, then for every
`b`, `Φ_d(C, b) ≤ ∑_a C(d)(a) Φ_d(C, a)`: moving toward `δ_b` cannot have a positive first-order
term, since a small step along the segment would then improve `V_B`.
Source: [[decision-problems-v2]] §8 Theorem 1 proof ("first-order necessity gives … for all
`r ∈ Δ(A_d)`"); A31; ZO-6
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem siaSum_le_avg_of_coherentAt (h : CoherentAt C B d) (b : acts d) :
    siaSum C B d b ≤ ∑ a, (C d).w a * siaSum C B d a := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  set L := siaSum C B d b - ∑ a, (C d).w a * siaSum C B d a with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  obtain ⟨R, M, hM, hR⟩ := value_lerp_deviate_eq C d (FinDistr.pure b) B
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl zero_le_one)
  set M' := M + 1 with hM'
  have hM'pos : 0 < M' := by rw [hM']; linarith
  -- the step size
  set ε := min 1 (L / (2 * M')) with hε
  have hε0 : 0 ≤ ε := le_min zero_le_one (div_nonneg hLpos.le (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεpos : 0 < ε := lt_min one_pos (div_pos hLpos (by linarith))
  have hεM : ε * M' ≤ L / 2 := by
    calc ε * M' ≤ L / (2 * M') * M' := mul_le_mul_of_nonneg_right (min_le_right _ _) hM'pos.le
      _ = L / 2 := by field_simp
  have hRε : -(M') ≤ R ε := by
    have := (abs_le.mp (hM ε hε0 hε1)).1
    linarith
  have key := hR ε hε0 hε1
  rw [lin_pure] at key
  have hcoh := h (FinDistr.lerp ε hε0 hε1 (C d) (FinDistr.pure b))
  rw [key] at hcoh
  -- `ε L + ε² R ≥ ε L − ε² M' ≥ ε (L − ε M') ≥ ε L / 2 > 0`
  have h1 : ε ^ 2 * R ε ≥ -(ε ^ 2 * M') := by nlinarith [sq_nonneg ε]
  have h2 : ε ^ 2 * M' ≤ ε * (L / 2) := by
    calc ε ^ 2 * M' = ε * (ε * M') := by ring
      _ ≤ ε * (L / 2) := mul_le_mul_of_nonneg_left hεM hε0
  have h3 : 0 < ε * L := mul_pos hεpos hLpos
  nlinarith

/-- **ZO-6 / A31 — mixed Definition 22 at `d` implies Theorem 1's condition at `d`, on every
finite tree** (self-succession included): if no point-deviation `C[d ↦ m]`, `m ∈ Δ(A_d)`,
improves `V_B`, then every action in the support of `C(d)` maximises
`Φ_d(C, ·) = ∑_{q : d_q = d} R_q(C) G_q(C, ·)`. First-order necessity toward each `δ_b`
(`siaSum_le_avg_of_coherentAt`) bounds every `Φ_d(C, b)` by the `C(d)`-average, and an action of
positive weight below that average would pull the average below itself.
Source: `cf-workflow/phase2-notes/final/v2-amendments.md` A31 ("The mixed form of Definition 22
implies Theorem 1's condition on every finite tree"); `repair/zoo.md` ZO-6; dp-core-051,
dp-cf-048, dp-cf-2-046
Kind: P
Fidelity: exact | variant: payoffs in a linearly ordered field
Scope: Definition 6; every tree, self-succession included; vacuous at `μ(occ(d)) = 0`
Hyps: (a) all -/
theorem thm1At_of_coherentAt (h : CoherentAt C B d) : Thm1At C B d := by
  intro a ha b
  have hle : ∀ b', siaSum C B d b' ≤ ∑ a', (C d).w a' * siaSum C B d a' :=
    siaSum_le_avg_of_coherentAt C B d h
  have hge : ∑ a', (C d).w a' * siaSum C B d a' ≤ siaSum C B d a := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have : ∑ a', (C d).w a' * siaSum C B d a' <
        ∑ a', (C d).w a' * ∑ a'', (C d).w a'' * siaSum C B d a'' := by
      apply Finset.sum_lt_sum
      · intro a' _
        exact mul_le_mul_of_nonneg_left (hle a') ((C d).nonneg a')
      · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left hlt ha⟩
    rw [← Finset.sum_mul, (C d).sum_one, one_mul] at this
    exact lt_irrefl _ this
  exact (hle b).trans hge

/-- **Coherent ⟹ Theorem 1** at every queried point.
Source: A31; ZO-6
Kind: C -/
theorem thm1_of_coherent (h : Coherent C B) : Thm1 C B :=
  fun d hd => thm1At_of_coherentAt C B d (h d hd)

/-- **Theorem 1 (global optimality implies CDT+SIA ratifiability)**: if `V_B(C) = max_{C'}
V_B(C')`, then at every queried `d`, `supp C(d) ⊆ argmax_a ∑_{q : d_q = d} R_q(C) G_q(C, a)`,
where `siaSum = ∑_q forcedBelow` by `siaSum_eq_sum_fiber_forcedBelow` and the SIA weights
`R_q / 𝔼[#_d]` are `sum_reach_fiber_eq_expCount`'s normalisation. Optimal ⟹ coherent
(`IsOptimal.coherent`) ⟹ Theorem 1's condition (`thm1_of_coherent`).
Source: [[decision-problems-v2]] §8 Theorem 1 (line 266) | dp-core-047 | dp-sl-057 | dp-cf-051
Kind: C
Fidelity: exact (finite-difference form of v2's derivative; `Φ_d = ∑_{q : d_q = d} R_q G_q` by
`siaSum_eq_sum_fiber_forcedBelow`) | variant: payoffs in a linearly ordered field
Scope: Definition 6 (independent redraws); every tree, self-succession included; vacuous at
`μ(occ(d)) = 0`
Hyps: (a) all -/
theorem thm1_of_isOptimal (h : IsOptimal C B) : Thm1 C B :=
  thm1_of_coherent C B (IsOptimal.coherent C B h)

end zo6

end Cleanroom.Decision.DpLocalOpt
