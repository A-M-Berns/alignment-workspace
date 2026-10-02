import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T12(c) — per-run SSC with a self-model on `mug1` is prior calibration of `C[d ↦ m]` (stretch)

On Counterfactual Mugging `B₁` (`mug1`) the point `d` is queried on both branches of the coin, so
`occ(d)` is the set of all runs (`mug1_occ`). The per-run clauses of Definition 13 then coincide,
clause for clause, with the strict clauses of Definition 8 at `O_d = ⊤`
(`mug1_perRunClauses_iff_strict`, for every procedure and every state), and per-run SSC with a
full-support self-model (`PerRunSSCMaskedAt`, the "combined state" of P11 §A4) is exactly
Definition 9's masked calibration in the LF variant at `O_d = ⊤` — under either null-case
reading, since `ν(⊤) = 1` makes the vacuity disjunct impossible
(`mug1_perRunMasked_iff_maskedOC`). This is the `L` identity the mandate's T12(c) names; whether
the combined state is "v2-sanctioned" is a question about the source (UNREVIEWED there), not
settled here.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Every leaf of `mug1` meets `d` exactly once (both branches query it).
Source: [[decision-problems-v2]] Proposition 6 (`B₁`); mandate T12(c) ("`occ(d)` = all runs").
Kind: L -/
theorem mug1_count (x y : ℚ) (ℓ : (mug1 x y).Leaves) : count () (mug1 x y) ℓ = 1 := by
  unfold mug1 at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp [count]

/-- `occ(d)` on `mug1` is every run. Source: mandate T12(c). Kind: L -/
theorem mug1_occ (x y : ℚ) : occ () (mug1 x y) = Finset.univ := by
  ext ℓ; simp [occ, mug1_count]

/-- **On `mug1` the per-run clauses are the strict clauses at `O_d = ⊤`**, for every procedure
and every state: with `occ(d)` = all runs, `μ({λ ⊨ X} ∩ occ(d)) = ν(X)`, `μ(occ(d)) = 1 = ν(⊤)`,
and the payoff mass on `{λ ⊨ X} ∩ occ(d)` is `paySum X`, so Definition 13's two clauses read as
Definition 8's two clauses with `O_d = ⊤`.
Source: mandate T12(c) ("the combined state coincides with prior calibration of `C[d ↦ m]`
(`occ(d)` = all runs) — an `L` identity"); P11 §A4
Kind: L
Fidelity: exact on `mug1`
Hyps: none -/
theorem mug1_perRunClauses_iff_strict (x y : ℚ) (s : Unit → State MugW ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    PerRunClausesAt s C (mug1 x y) () ↔
      StrictClausesAt s (fun _ => Finset.univ) C (mug1 x y) () := by
  simp only [PerRunClausesAt, PerRunClause1At, PerRunClause2At, StrictClausesAt, StrictClause1At,
    StrictClause2At, mug1_occ, Finset.inter_univ, mass_univ, nu_univ, mul_one]
  simp only [nu, paySum]

/-- **T12(c): on `mug1`, per-run SSC with a full-support self-model is Definition 9 (LF) at
`O_d = ⊤`** — under either null-case reading, because `ν_{C'}(⊤) = 1` for every self-model, so
the vacuity disjunct is impossible and the letter disjunct is `PerRunSSCMaskedAt` through
`mug1_perRunClauses_iff_strict`. The combined state is prior calibration of `C[d ↦ m]`.
Source: mandate T12(c); P11 §A4 (the combined state); [[decision-problems-v2]] Definition 9
Kind: L
Fidelity: exact on `mug1`
Hyps: none -/
theorem mug1_perRunMasked_iff_maskedOC (x y : ℚ) (s : Unit → State MugW ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) (r : NullReading) :
    PerRunSSCMaskedAt C (mug1 x y) s () ↔
      MaskedOCAtV s (fun _ => Finset.univ) C (mug1 x y) .LF r () := by
  constructor
  · rintro ⟨m, hm, _, hcl⟩
    exact Or.inl ⟨C.deviate () m, ⟨m, hm, rfl⟩, nu_univ_pos _ _,
      (mug1_perRunClauses_iff_strict x y s _).1 hcl⟩
  · rintro (⟨C', ⟨m, hm, rfl⟩, _, hcl⟩ | ⟨_, hnull⟩)
    · exact ⟨m, hm, by rw [mug1_occ, mass_univ]; exact one_pos,
        (mug1_perRunClauses_iff_strict x y s _).2 hcl⟩
    · exfalso
      have h := hnull (C.deviate () (FinDistr.act2 (1/2) (by norm_num) (by norm_num)))
        ⟨_, fun z => by cases z <;> norm_num [FinDistr.act2], rfl⟩
      rw [nu_univ] at h
      exact one_ne_zero h

end Cleanroom.Decision.DpCalibLimits
