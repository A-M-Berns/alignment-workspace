import Cleanroom.Bli.UdtBliCore.Basic

/-!
# `udt-bli-core` · NodeDescription: the node-description lemma and its converse (T11; bli-soto-a-064)

Finite form of Soto's PDF 09: if the sentence `S = (ϕ ∧ A = a) → (U = u)` has probability `1`,
then `μ(ϕ | A = a) = 1 → μ(U = u | A = a) = 1` (`node_description`, L). The inventory records an
**iff**; the source says "will happen if". The converse fails (`converse_fails`, N−): `U = u` can
hold for another reason while `ϕ` fails.
-/

namespace Cleanroom.Bli.UdtBliCore

open Finset

namespace NodeDesc

variable {Ω : Type} [Fintype Ω] (μ : Ω → ℚ)

/-- An event of probability one holds wherever `μ` is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_of_massOf_eq_one (hμ : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (S : Ω → Prop)
    [DecidablePred S] (hS : massOf μ S = 1) : ∀ ω, 0 < μ ω → S ω := by
  intro ω hω
  by_contra hnot
  have hsplit : ∑ ω, μ ω = massOf μ S + massOf μ (fun ω => ¬ S ω) := by
    unfold massOf
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω' _
    by_cases h : S ω' <;> simp [h]
  have hz : massOf μ (fun ω => ¬ S ω) = 0 := by linarith [hsplit, h1, hS]
  rw [massOf_eq_zero_iff μ hμ] at hz
  exact ne_of_gt hω (hz ω hnot)

/-- If `μ(ϕ | A) = 1` then `ϕ` holds wherever `A` holds with positive weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_of_condProb_eq_one (hμ : ∀ ω, 0 ≤ μ ω) (ϕ isA : Ω → Prop) [DecidablePred ϕ]
    [DecidablePred isA] (hpos : 0 < massOf μ isA)
    (h : massOf μ (fun ω => ϕ ω ∧ isA ω) / massOf μ isA = 1) :
    ∀ ω, 0 < μ ω → isA ω → ϕ ω := by
  intro ω hω hA
  by_contra hnot
  have heq : massOf μ (fun ω => ϕ ω ∧ isA ω) = massOf μ isA := by
    rw [div_eq_iff (ne_of_gt hpos), one_mul] at h; exact h
  have hsplit : massOf μ isA = massOf μ (fun ω => ϕ ω ∧ isA ω) +
      massOf μ (fun ω => ¬ ϕ ω ∧ isA ω) := by
    unfold massOf
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω' _
    by_cases h1 : ϕ ω' <;> by_cases h2 : isA ω' <;> simp [h1, h2]
  have hz : massOf μ (fun ω => ¬ ϕ ω ∧ isA ω) = 0 := by linarith [hsplit, heq]
  rw [massOf_eq_zero_iff μ hμ] at hz
  exact ne_of_gt hω (hz ω ⟨hnot, hA⟩)

/-- **The node-description lemma**: if `(ϕ ∧ A = a) → (U = u)` has probability one and
`μ(ϕ | A = a) = 1`, then `μ(U = u | A = a) = 1`.
Source: bli-soto-a-064 (Soto's PDF 09: "This will happen if `P(ϕ(D(i,j)) | S ∧ A(obs) = a) = 1`")
Kind: L
Fidelity: variant: `μ(S) = 1` in place of the source's conditioning on `S` (then conditioning on
`S` is a no-op), as the mandate asked; the source's "if" (the inventory's "iff" is refuted by
`converse_fails`)
Hyps: (a) `μ ≥ 0`, `∑ μ = 1`, `0 < μ(A)` -/
theorem node_description (hμ : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (ϕ isA isU : Ω → Prop)
    [DecidablePred ϕ] [DecidablePred isA] [DecidablePred isU]
    (hS : massOf μ (fun ω => ϕ ω ∧ isA ω → isU ω) = 1) (hpos : 0 < massOf μ isA)
    (hϕ : massOf μ (fun ω => ϕ ω ∧ isA ω) / massOf μ isA = 1) :
    massOf μ (fun ω => isU ω ∧ isA ω) / massOf μ isA = 1 := by
  rw [div_eq_iff (ne_of_gt hpos), one_mul]
  have hSw := holds_of_massOf_eq_one μ hμ h1 _ hS
  have hϕw := holds_of_condProb_eq_one μ hμ ϕ isA hpos hϕ
  unfold massOf
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : 0 < μ ω
  · by_cases hA : isA ω
    · have hU : isU ω := hSw ω hω ⟨hϕw ω hω hA, hA⟩
      simp [hA, hU]
    · simp [hA]
  · have hz : μ ω = 0 := le_antisymm (not_lt.mp hω) (hμ ω)
    simp [hz]

/-- **The converse fails** (N−): on the one-world space where `A` holds, `U = u` holds and `ϕ`
fails, `S` has probability one and `μ(U = u | A) = 1`, but `μ(ϕ | A) = 0`.
Source: bli-soto-a-064 (finding F-5: the inventory's "iff" is not in the source)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem converse_fails :
    massOf (fun _ : Unit => (1 : ℚ)) (fun _ => False ∧ True → True) = 1 ∧
      massOf (fun _ : Unit => (1 : ℚ)) (fun _ => True ∧ True) /
        massOf (fun _ : Unit => (1 : ℚ)) (fun _ => True) = 1 ∧
      massOf (fun _ : Unit => (1 : ℚ)) (fun _ => False ∧ True) /
        massOf (fun _ : Unit => (1 : ℚ)) (fun _ => True) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [massOf]

end NodeDesc

end Cleanroom.Bli.UdtBliCore
