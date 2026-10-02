import Cleanroom.Bli.BliFinite.Kernel
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# `bli-exact-base` — bli-soto-b-026: convexity of the self-trust set

Over `bli-finite`'s finite objects: for a day-`m` table `t` and a pinned set of coordinates, the
**self-trust set** `selfTrustSet d pinned t` is the set of superbeliefs `μ` on the day-`m` grid
(`IsProb d μ`) whose mean on every pinned coordinate is `t` — exact self-trust
`∑_q μ q · q φ = t φ` as a linear constraint. It is **convex** (`selfTrustSet_convex`, Kind
`P`): `IsProb` is a convex condition and the mean is linear (`mean_add`, `mean_smul`).

Non-emptiness: the point mass on `t` when `t` is a grid table (`pointSb_mem`, N−); a member
charging two distinct tables when `t` is interior — the half/half mixture of the constant
tables `0` and `1` at `t ≡ 1/2` (`twoSb_mem`, `twoSb_two_charged`, N+).

**The wrong-weights finding** (presentation; findings F7). The source derives convexity from
`Q_k(φ | Q_{k+n}(φ) = p) = ∑_B P(B)·B(φ | …) = ∑_B P(B)·p = p`, but a mixture's conditional is the
mixture of conditionals with weights `P(B)·B(E)/P(E)`, not `P(B)`
(`wrong_weights_counterexample`: with weights `(1/2, 1/2)`, `B(E) = (1, 1/2)` and
`B(φ∧E) = (1, 0)` the source's formula gives `1/2`, the conditional is `2/3`). The conclusion
survives because every `B(φ | E) = p`: `P(φ ∧ E) = p · P(E)` holds under that hypothesis
(`mixture_cond_identity`, the identity the convexity proof actually uses). The inter-stage form
`∑_{p'} p' · P(Q_{k+2} = p' | Q_{k+1} = p) = p` is `bli-finite`'s `Kernel.balanced`
(`kernel_interstage`).
-/

namespace Cleanroom.Bli.BliExactBase.Convex

open Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex} {m : ℕ}

/-- **The self-trust set**: probabilities on the day-`m` grid whose mean agrees with `t` on the
pinned coordinates.
Source: bli-soto-b-026 (`𝒞`); mandate § 8
Kind: D
Fidelity: exact -/
def selfTrustSet (d : ℕ → ℕ) (pinned : Finset ↥(𝒮.S m)) (t : Table 𝒮 m) :
    Set (Superbelief 𝒮 m) :=
  {μ | IsProb d μ ∧ ∀ φ ∈ pinned, mean d μ φ = t φ}

/-- **bli-soto-b-026 — the self-trust set is convex.** `IsProb` (nonnegativity, support on the
grid, mass one) and the pinned-mean constraints are preserved by convex combination because the
mean is linear in the superbelief.
Source: bli-soto-b-026; mandate § 8 (judged item 5)
Kind: P
Fidelity: exact (over `ℚ`, the field of the superbeliefs; the mandate's `Convex ℝ` does not type)
Hyps: (a) -/
theorem selfTrustSet_convex (d : ℕ → ℕ) (pinned : Finset ↥(𝒮.S m)) (t : Table 𝒮 m) :
    Convex ℚ (selfTrustSet d pinned t) := by
  intro μ hμ ν hν a b ha hb hab
  obtain ⟨⟨hμ0, hμg, hμ1⟩, hμt⟩ := hμ
  obtain ⟨⟨hν0, hνg, hν1⟩, hνt⟩ := hν
  refine ⟨⟨fun q => ?_, fun q hq => ?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hμ0 q)) (mul_nonneg hb (hν0 q))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμg q hq, hνg q hq, mul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hμ1, hν1, mul_one, hab]
  · rw [mean_add, mean_smul, mean_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hμt φ hφ, hνt φ hφ]
    rw [← add_mul, hab, one_mul]

/-! ## Non-emptiness -/

open Classical in
/-- The point mass on a table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pointSb (t : Table 𝒮 m) : Superbelief 𝒮 m := fun q => if q = t then 1 else 0

open Classical in
/-- **N−**: the point mass on a grid table is in its own self-trust set (every pinned set).
Source: mandate § 8 ("nonempty when `t` is a grid table (the point mass; `N−`)")
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem pointSb_mem {d : ℕ → ℕ} (pinned : Finset ↥(𝒮.S m)) {t : Table 𝒮 m}
    (ht : t ∈ grid 𝒮 d m) : pointSb t ∈ selfTrustSet d pinned t := by
  refine ⟨⟨fun q => ?_, fun q hq => ?_, ?_⟩, fun φ _ => ?_⟩
  · unfold pointSb; split_ifs <;> norm_num
  · unfold pointSb
    rw [if_neg]
    rintro rfl
    exact hq ht
  · simp [pointSb, ht]
  · simp [mean, meanOn, pointSb, ite_mul, ht]

/-- The zero and one tables.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def zeroTable : Table 𝒮 m := fun _ => 0

/-- The one table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oneTable : Table 𝒮 m := fun _ => 1

/-- With a nonempty index the zero and one tables differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroTable_ne_oneTable (hne : (𝒮.S m).Nonempty) : (zeroTable : Table 𝒮 m) ≠ oneTable := by
  intro h
  obtain ⟨φ, hφ⟩ := hne
  have := congrFun h ⟨φ, hφ⟩
  simp [zeroTable, oneTable] at this

open Classical in
/-- The half/half mixture of the zero and one tables.
Source: mandate § 8 (the non-degenerate member)
Kind: D
Fidelity: n/a -/
noncomputable def twoSb : Superbelief 𝒮 m :=
  fun q => (if q = zeroTable then 1 / 2 else 0) + (if q = oneTable then 1 / 2 else 0)

open Classical in
/-- **N+**: at the interior table `t ≡ 1/2` the half/half mixture of the constant tables `0` and
`1` lies in the self-trust set (every pinned set, every positive denominator).
Source: mandate § 8 ("contains a non-degenerate member when `t` is interior")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem twoSb_mem {d : ℕ → ℕ} (hd : 0 < d m) (hne : (𝒮.S m).Nonempty)
    (pinned : Finset ↥(𝒮.S m)) :
    (twoSb : Superbelief 𝒮 m) ∈ selfTrustSet d pinned (fun _ => 1 / 2) := by
  have h0 : (zeroTable : Table 𝒮 m) ∈ grid 𝒮 d m :=
    mem_grid_iff.2 fun _ => zero_mem_gridVals _
  have h1 : (oneTable : Table 𝒮 m) ∈ grid 𝒮 d m :=
    mem_grid_iff.2 fun _ => one_mem_gridVals hd
  have hne' := zeroTable_ne_oneTable (𝒮 := 𝒮) (m := m) hne
  refine ⟨⟨fun q => ?_, fun q hq => ?_, ?_⟩, fun φ _ => ?_⟩
  · unfold twoSb; split_ifs <;> norm_num
  · have hz : q ≠ zeroTable := by rintro rfl; exact hq h0
    have ho : q ≠ oneTable := by rintro rfl; exact hq h1
    simp [twoSb, hz, ho]
  · simp [twoSb, Finset.sum_add_distrib, h0, h1]
    norm_num
  · simp [mean, meanOn, twoSb, add_mul, ite_mul, Finset.sum_add_distrib, h0, h1, zeroTable,
      oneTable]

open Classical in
/-- The mixture charges two distinct tables with mass `1/2` each: non-degenerate (not a point
mass).
Source: mandate § 8 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem twoSb_two_charged (hne : (𝒮.S m).Nonempty) :
    (zeroTable : Table 𝒮 m) ≠ oneTable ∧ (twoSb : Superbelief 𝒮 m) zeroTable = 1 / 2 ∧
      (twoSb : Superbelief 𝒮 m) oneTable = 1 / 2 := by
  have hne' := zeroTable_ne_oneTable (𝒮 := 𝒮) (m := m) hne
  refine ⟨hne', ?_, ?_⟩
  · simp [twoSb, hne']
  · simp [twoSb, hne'.symm]

/-! ## The wrong-weights finding -/

/-- **The identity the convexity argument needs**: if every component has `B(φ ∧ E) = p · B(E)`,
the mixture has `P(φ ∧ E) = p · P(E)` — linear in the weights, no conditioning required.
Source: bli-soto-b-026 (the surviving content of the displayed derivation); mandate § 8
Kind: L
Fidelity: n/a -/
theorem mixture_cond_identity {k : ℕ} (w B BE : Fin k → ℚ) (p : ℚ) (h : ∀ i, BE i = p * B i) :
    ∑ i, w i * BE i = p * ∑ i, w i * B i := by
  simp only [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The source's displayed weights are wrong**: `∑_B P(B)·B(φ|E)` is not `P(φ|E)` in general.
Two components with weights `1/2`, `B(E) = (1, 1/2)`, `B(φ∧E) = (1, 0)`: the source's formula
gives `1/2`, the mixture's conditional is `(1/2)/(3/4) = 2/3`.
Source: bli-soto-b-026 (inventory flag "wrong weights"); mandate § 8; findings F7
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem wrong_weights_counterexample :
    let w : Fin 2 → ℚ := ![1 / 2, 1 / 2]
    let B : Fin 2 → ℚ := ![1, 1 / 2]
    let BE : Fin 2 → ℚ := ![1, 0]
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, 0 < B i) ∧ (∀ i, 0 ≤ BE i ∧ BE i ≤ B i) ∧
      ∑ i, w i * (BE i / B i) ≠ (∑ i, w i * BE i) / ∑ i, w i * B i := by
  intro w B BE
  refine ⟨fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [w]
  · simp [w, Fin.sum_univ_two]; norm_num
  · fin_cases i <;> norm_num [B]
  · fin_cases i <;> norm_num [B, BE]
  · simp [w, B, BE, Fin.sum_univ_two]; norm_num

/-- **The inter-stage form** `∑_{p'} p' · P(Q_{k+2} = p' | Q_{k+1} = p) = p` is `bli-finite`'s
`Kernel.balanced`: the mean of the kernel's law at `t` restricts to `t`.
Source: bli-soto-b-026 (inter-stage marginalization); bli-finite `Kernel.balanced`
Kind: L
Fidelity: n/a -/
theorem kernel_interstage {d : ℕ → ℕ} (κ : Kernel 𝒮 d m) (t : Table 𝒮 m) (ht : t.InUnit)
    (φ : ↥(𝒮.S m)) : (mean d (κ.law t)).restrict φ = t φ :=
  κ.balanced t ht φ

end Cleanroom.Bli.BliExactBase.Convex
