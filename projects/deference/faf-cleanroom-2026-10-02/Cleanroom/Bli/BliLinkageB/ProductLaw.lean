import Cleanroom.Bli.BliLinkageB.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# bli-linkage, angle B — the product coupling (K5a/b, finite-probability core)

A superbelief on tables over `k` coordinates with `d` cells is a law on `Fin k → Fin d`. Given
per-coordinate marginal data `w i : Fin d → ℝ` (at the package level: `w i r = Q n (lit_{n+1, c_i, r})`
on the pinned coordinates and a balanced law of the user's choice on the rest), the **product
coupling** `productLaw w f := ∏ i, w i (f i)` is the projected kernel of record:

* a probability law when every `w i` is one (`productLaw_nonneg`, `sum_productLaw`);
* with the prescribed marginals (`marginal_productLaw`: the mass of the tables assigning `i₀`
  the cell `r₀` is `w i₀ r₀`) — by `Finset.prod_univ_sum` at the family of finsets that pins
  coordinate `i₀` to `{r₀}`;
* with the balance `∑_f μ f · rep (f i₀) = ∑_r rep r · w i₀ r` (`balance_productLaw`) — which is
  `Q n φ` exactly when `D_NNUcell` holds at the coordinate.

**K5a, abstract iff** (`exists_coupling_iff`): a law `μ` with marginals `w` and balances `b`
exists iff every `w i` is a probability vector and `b i = ∑_r rep r · w i r` for every `i`.
(⇒) is the regrouping of any such `μ` by the fibres of `f ↦ f i` (`balance_of_marginals`), no
coupling needed; (⇐) is the product coupling. **K5b** (`support_of_feasible`,
`productLaw_pos`): every feasible `μ` vanishes outside `supp⊗ := {f | ∀ i, 0 < w i (f i)}` (a
zero marginal kills the fibre), and the product coupling is positive on all of `supp⊗` — the
face statement, made directly (the constrained polytope is not a hull problem; contrast
`bli-superbelief`'s `faceGen`, cited in the report). The transport to the package's coded
tables and `cellMass` is `Existence.lean`.
-/

namespace Cleanroom.Bli.BliLinkageB

namespace Existence

open Finset

variable {k d : ℕ}

/-- **The product coupling** of the per-coordinate laws `w i`: the mass of the table `f` is
`∏_i w i (f i)`.
Source: mandate K5a (`productCoupling`, "the projected kernel of record"); [[bli-program]] §3.6(v); construction C6
Kind: D
Fidelity: exact (over function-tables `Fin k → Fin d`; coded tables in `Existence.lean`) -/
def productLaw (w : Fin k → Fin d → ℝ) (f : Fin k → Fin d) : ℝ := ∏ i, w i (f i)

/-- The product coupling is nonnegative when the marginal data is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem productLaw_nonneg {w : Fin k → Fin d → ℝ} (hw0 : ∀ i r, 0 ≤ w i r) (f : Fin k → Fin d) :
    0 ≤ productLaw w f :=
  Finset.prod_nonneg fun i _ => hw0 i (f i)

/-- **K5b, positivity**: the product coupling is positive on every table all of whose entries
have positive marginal mass.
Source: mandate K5b ("`productCoupling` is positive on all of `supp⊗`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem productLaw_pos {w : Fin k → Fin d → ℝ} {f : Fin k → Fin d} (hw : ∀ i, 0 < w i (f i)) :
    0 < productLaw w f :=
  Finset.prod_pos fun i _ => hw i

/-- The product coupling has total mass `1` when every `w i` sums to `1`.
Source: mandate K5a; Mathlib `Finset.prod_univ_sum`
Kind: L
Fidelity: n/a -/
theorem sum_productLaw {w : Fin k → Fin d → ℝ} (hw1 : ∀ i, ∑ r, w i r = 1) :
    ∑ f, productLaw w f = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin k => (univ : Finset (Fin d))) w
  rw [Fintype.piFinset_univ] at h
  unfold productLaw
  rw [← h]
  simp [hw1]

/-- The tables assigning `i₀` the cell `r₀` are the `piFinset` of the family pinning `i₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma piFinset_fix (i₀ : Fin k) (r₀ : Fin d) :
    Fintype.piFinset (fun i => if i = i₀ then ({r₀} : Finset (Fin d)) else univ) =
      univ.filter (fun f : Fin k → Fin d => f i₀ = r₀) := by
  ext f
  simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    simpa using h i₀
  · intro h i
    by_cases hi : i = i₀
    · subst hi
      simpa using h
    · simp [hi]

/-- **The product coupling has the prescribed marginals**: the mass of the tables assigning
`i₀` the cell `r₀` is `w i₀ r₀` (K5a (β) for the product coupling).
Source: mandate K5a ("(β) by marginalizing a product"); Mathlib `Finset.prod_univ_sum`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem marginal_productLaw {w : Fin k → Fin d → ℝ} (hw1 : ∀ i, ∑ r, w i r = 1) (i₀ : Fin k)
    (r₀ : Fin d) :
    ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i₀ = r₀), productLaw w f = w i₀ r₀ := by
  have h := Finset.prod_univ_sum (fun i => if i = i₀ then ({r₀} : Finset (Fin d)) else univ) w
  rw [piFinset_fix] at h
  unfold productLaw
  rw [← h, ← Finset.mul_prod_erase univ _ (mem_univ i₀)]
  simp only [if_true, sum_singleton]
  rw [Finset.prod_eq_one fun i hi => by rw [if_neg (ne_of_mem_erase hi)]; exact hw1 i, mul_one]

/-- **Any law's balance at a coordinate is determined by its marginals there**: regrouping the
tables by the cell they assign `i₀`, `∑_f μ f · rep (f i₀) = ∑_r rep r · (mass of the fibre)`.
This is K5a's (⇒): a feasible superbelief forces the balance to be the representative-weighted
marginal — the finite form of `D_NNUcell` at the coordinate.
Source: mandate K5a ("(⇒) is K2(c)"); Mathlib `Finset.sum_fiberwise`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem balance_of_marginals (μ : (Fin k → Fin d) → ℝ) (i₀ : Fin k) (rep : Fin d → ℝ) :
    ∑ f, μ f * rep (f i₀) =
      ∑ r, rep r * ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i₀ = r), μ f := by
  rw [← Finset.sum_fiberwise univ (fun f : Fin k → Fin d => f i₀)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f hf => by rw [(mem_filter.1 hf).2]; ring

/-- **The product coupling's balance** at every coordinate is the representative-weighted
marginal (K5a (α) for the product coupling, given `D_NNUcell` at the coordinate).
Source: mandate K5a ("(α) by `D_NNUcell`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem balance_productLaw {w : Fin k → Fin d → ℝ} (hw1 : ∀ i, ∑ r, w i r = 1) (i₀ : Fin k)
    (rep : Fin d → ℝ) :
    ∑ f, productLaw w f * rep (f i₀) = ∑ r, rep r * w i₀ r := by
  rw [balance_of_marginals]
  exact Finset.sum_congr rfl fun r _ => by rw [marginal_productLaw hw1 i₀ r]

/-- **K5b, the support of every feasible law**: a nonnegative `μ` with marginals `w` vanishes on
every table some entry of which has zero marginal mass — equivalently, `μ f ≠ 0` forces
`0 < w i (f i)` for every `i` (`f ∈ supp⊗`).
Source: mandate K5b ("every feasible `μ` is supported inside `supp⊗`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem support_of_feasible {μ : (Fin k → Fin d) → ℝ} (hμ0 : ∀ f, 0 ≤ μ f)
    {w : Fin k → Fin d → ℝ}
    (hmarg : ∀ i r, ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i = r), μ f = w i r)
    {f : Fin k → Fin d} (hf : μ f ≠ 0) : ∀ i, 0 < w i (f i) := by
  intro i
  rw [← hmarg i (f i)]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun g _ => hμ0 g) fun h => hf ?_
  exact (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hμ0 g).1 h.symm f
    (mem_filter.2 ⟨mem_univ _, rfl⟩)

/-- **K5a, the finite iff (abstract form).** A law `μ` on tables with marginals `w` and balances
`b` (at representatives `rep`) exists iff every `w i` is a probability vector and
`b i = ∑_r rep r · w i r` for every coordinate. (⇒): regroup any such `μ` (`balance_of_marginals`).
(⇐): the product coupling. At the package level the right-hand side is `D_NNUcell` at the
pinned coordinates with `w i r = Q n (lit_{n+1, c_i, r})` and `b i = Q n (sentenceOfCode c_i)`
(`Existence.lean`).
Source: mandate K5a; [[bli-program]] §3.6(v); bli-soto-b-044; bli-slides-010/011 (their "consistent demands" is the probability-vector clause, FB-9)
Kind: P
Fidelity: exact (abstract: function-tables, every coordinate treated alike; the pinned/unpinned split is the choice of `w` on the unpinned block)
Hyps: (a) -/
theorem exists_coupling_iff (w : Fin k → Fin d → ℝ) (rep : Fin d → ℝ) (b : Fin k → ℝ) :
    (∃ μ : (Fin k → Fin d) → ℝ, (∀ f, 0 ≤ μ f) ∧ ∑ f, μ f = 1 ∧
        (∀ i r, ∑ f ∈ univ.filter (fun f : Fin k → Fin d => f i = r), μ f = w i r) ∧
        (∀ i, ∑ f, μ f * rep (f i) = b i)) ↔
      (∀ i r, 0 ≤ w i r) ∧ (∀ i, ∑ r, w i r = 1) ∧ (∀ i, b i = ∑ r, rep r * w i r) := by
  constructor
  · rintro ⟨μ, hμ0, hμ1, hmarg, hbal⟩
    refine ⟨fun i r => ?_, fun i => ?_, fun i => ?_⟩
    · rw [← hmarg i r]
      exact Finset.sum_nonneg fun f _ => hμ0 f
    · rw [← hμ1, ← Finset.sum_fiberwise univ (fun f : Fin k → Fin d => f i)]
      exact Finset.sum_congr rfl fun r _ => (hmarg i r).symm
    · rw [← hbal i, balance_of_marginals]
      exact Finset.sum_congr rfl fun r _ => by rw [hmarg i r]
  · rintro ⟨hw0, hw1, hb⟩
    refine ⟨productLaw w, productLaw_nonneg hw0, sum_productLaw hw1,
      fun i r => marginal_productLaw hw1 i r, fun i => ?_⟩
    rw [balance_productLaw hw1 i rep, hb i]

end Existence

end Cleanroom.Bli.BliLinkageB
