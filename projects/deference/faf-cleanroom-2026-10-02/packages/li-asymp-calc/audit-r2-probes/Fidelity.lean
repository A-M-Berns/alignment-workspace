import Cleanroom.Found.LiAsympCalc

/-!
# li-asymp-calc — audit round 2, fidelity lens: probes

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for
one item of `li-asymp-calc-audit-r2-fidelity.md`:

1. `weightedApprox_trans_total`, `weightedApprox_add_total` — the same-weighting transitivity
   and additivity of `WeightedApprox` hold for **every** weighting, with no divergence
   hypothesis: FAF's `weightedAverage` is `0` at zero mass, so the additivity identity holds
   there too (both sides `0`). The package's `WeightedApprox.trans`/`.add` carry `hdiv`, which
   the mandate asked for and which is dispensable; the earlier Lean's `ApproxW.trans`
   (`StreamlinedSS.lean:150`) is unconditional for the same reason. Fidelity note, not a
   defect: the `hdiv` form is what every consumer has in scope anyway.
2. `gridLUV_mesh_determined_atomDP` — the shape of finding 9 sharpened. With the deductive
   process that reveals the atom `0` on every day, `DeterminedVia gridLUV DP 0` still holds on
   every day and the precision-`(n+1)` mesh of `ofLUV gridLUV` **is** exactly
   `AffineCombination.DeterminedViaTheory` — at the truth `1/(n+1)`, which differs from the
   mandate's grid-rounded truth `(n+1)⁻¹ · #{i < n+1 : i/(n+1) < 0} = 0` on every day. So the
   mandate's G3 (c) formula fails on the grid even for a deductive process that decides the
   threshold sentence, while the package's stronger "no truth stream at all"
   (`not_determined_mesh_ofLUV_onGrid`) is specific to the *undecided* atom (the empty
   deductive process). Both readings refute the mandate's claim; the finding should say which
   is which.
-/

namespace Cleanroom.Found.LiAsympCalc.AuditR2

open LogicalInduction Filter Topology Finset

/-! ### 1. Transitivity and additivity need no divergence hypothesis -/

/-- The additivity identity holds at every day, zero-mass days included. -/
theorem weightedAverage_sub_add_total (w x y z : ℕ → ℝ) (n : ℕ) :
    weightedAverage w (fun i => x i - z i) n =
      weightedAverage w (fun i => x i - y i) n + weightedAverage w (fun i => y i - z i) n := by
  by_cases h : prefixSum w n = 0
  · simp [weightedAverage, h]
  · rw [← weightedAverage_add w _ _ h]
    congr 1
    funext i
    ring

theorem weightedApprox_trans_total {w x y z : ℕ → ℝ}
    (hxy : WeightedApprox w x y) (hyz : WeightedApprox w y z) : WeightedApprox w x z := by
  unfold WeightedApprox at *
  have h := hxy.add hyz
  rw [add_zero] at h
  exact h.congr (fun n => (weightedAverage_sub_add_total w x y z n).symm)

theorem weightedApprox_add_total {w x y x' y' : ℕ → ℝ}
    (h₁ : WeightedApprox w x y) (h₂ : WeightedApprox w x' y') :
    WeightedApprox w (fun i => x i + x' i) (fun i => y i + y' i) := by
  unfold WeightedApprox at *
  have h := h₁.add h₂
  rw [add_zero] at h
  refine h.congr (fun n => ?_)
  by_cases hn : prefixSum w n = 0
  · simp [weightedAverage, hn]
  · rw [← weightedAverage_add w _ _ hn]
    congr 1
    funext i
    ring

/-! ### 2. On the grid with a deciding deductive process -/

/-- The deductive process that reveals the atom `0` on every day. -/
def atomDP : DeductiveProcess :=
  ⟨fun _ => {LO.Propositional.Formula.atom 0}, fun _ => Finset.Subset.refl _⟩

lemma holds_atom_of_consistent_atomDP {v : PCWorld} (hv : v.ConsistentWithTheory atomDP) :
    v.Holds (LO.Propositional.Formula.atom 0) :=
  hv 0 _ (Finset.mem_singleton_self _)

theorem gridLUV_mesh_determined_atomDP (P : History) :
    (∀ n : ℕ, LUV.DeterminedVia ((fun _ : ℕ => gridLUV) n) atomDP ((fun _ : ℕ => (0 : ℝ)) n)) ∧
    AffineCombination.DeterminedViaTheory
      (fun n : ℕ => (LUVCombination.ofLUV ((fun _ : ℕ => gridLUV) n)).meshAffine (n + 1)) P
      atomDP (fun n => 1 / ((n : ℝ) + 1)) ∧
    (∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≠
      (((n + 1 : ℕ) : ℝ))⁻¹ *
        ((Finset.range (n + 1)).filter
          (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) < (fun _ : ℕ => (0 : ℝ)) n)).card) := by
  refine ⟨fun _ v _ => gridLUV_valuesAt v, ?_, ?_⟩
  · intro n v hv
    simp only [meshAffine_ofLUV_value, LUV.expectApprox]
    rw [Finset.sum_range_succ']
    have h0 : gridLUV.gt (((0 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ)) = LO.Propositional.Formula.atom 0 := by
      simp [gridLUV]
    have hpos : ∀ i : ℕ, gridLUV.gt (((i + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ)) =
        LO.Propositional.Formula.falsum := by
      intro i
      have h1 : (0 : ℚ) < ((i : ℚ) + 1) / ((n : ℚ) + 1) := by positivity
      simp only [gridLUV]
      push_cast
      rw [if_neg (not_lt.2 h1.le), if_pos h1]
    have hzero : ∑ i ∈ range n,
        v.payout (gridLUV.gt (((i + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hpos i]
      unfold PCWorld.payout
      exact if_neg (fun h => h)
    rw [hzero, zero_add, h0]
    unfold PCWorld.payout
    rw [if_pos (holds_atom_of_consistent_atomDP hv)]
    push_cast
    ring
  · intro n
    have hempty : ((Finset.range (n + 1)).filter
        (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) < (fun _ : ℕ => (0 : ℝ)) n)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro i _
      exact not_lt.2 (by positivity)
    rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity

end Cleanroom.Found.LiAsympCalc.AuditR2
