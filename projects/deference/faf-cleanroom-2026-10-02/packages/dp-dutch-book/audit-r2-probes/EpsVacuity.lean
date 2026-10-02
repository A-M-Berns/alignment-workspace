import Cleanroom.Decision.DpDutchBook.MiniatureR

/-!
Audit round 2, adversarial lens — probe 3: the vacuity envelope of `d2At_exists` /
`testSeq_exists`, and the grade of the new `ℝ` witnesses.

1. **Where `D2At` says nothing.** Definition 18's escape clause makes `D2At` hold for *every*
   procedure at every `ε` whenever no act is realized within `O_d` — e.g. when every observation
   event is empty — on any tree (round 1 showed the leaf-tree case; this is the general envelope).
   So `d2At_exists` and `testSeq_exists` carry content only through points with a realized act;
   that is the definition's structure (`dp-calibration`'s), disclosed in the docstrings, and the
   shipped witnesses are at such a point.
2. **The witnesses are what the ledger says.** `miniR_d2At_qStar`'s label `procStarR ε` has both
   acts strictly supported for `ε ∈ (0, ½]` (the docstring's "both acts supported" is not itself a
   theorem of the package), and `miniR_testSeq`'s sequence `procStarR (1/(n+2))` is non-constant:
   it never equals its limit `procR (2/3)`. Both are needed for the N+ grade the ledger claims.
Not imported by the library.
-/

namespace Cleanroom.Decision.DpDutchBook.AuditR2Adv

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDutchBook

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- `ν(∅) = 0`. -/
theorem nu_empty (C : Proc ι acts ℝ) (B : Tree Ω ι acts ℝ) : nu C B ∅ = 0 := by
  simp [nu, mass, worldEv]

/-- With every observation event empty, `D2At` holds for every procedure at every `ε`. -/
theorem d2At_of_obs_empty (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℝ)
    (C' : Proc ι acts ℝ) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    D2At (fun _ => ∅) actEv B C' ε h0 h1 := by
  intro d _ _ hb
  exfalso
  obtain ⟨b, hb⟩ := hb
  rw [Finset.inter_empty, nu_empty] at hb
  exact lt_irrefl _ hb

/-- Hence `TestSeqTrembleEdtConsistent` for every procedure, by the constant sequence. -/
theorem testSeq_of_obs_empty (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts ℝ)
    (C : Proc ι acts ℝ) :
    TestSeqTrembleEdtConsistent (fun _ => ∅) actEv C B := by
  refine ⟨fun n => 1 / ((n : ℝ) + 2), fun _ => C, fun n => epsSeq_mem n, ?_, ?_,
    fun n => d2At_of_obs_empty actEv B C _ (epsSeq_mem n).1 (epsSeq_mem n).2⟩
  · intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun n hn => ?_⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  · intro d a δ hδ
    exact ⟨0, fun n _ => by simpa using hδ⟩

/-- The `ℝ` witness's label has both acts strictly supported for `ε ∈ (0, ½]`. -/
theorem procStarR_both_supported (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    0 < (procStarR ε h0.le h1 ()).w .a ∧ 0 < (procStarR ε h0.le h1 ()).w .b := by
  have h23 := two_thirds_le_qStarR ε h0.le h1
  have hlt : qStarR ε < 1 := by
    unfold qStarR
    rw [div_lt_one (by linarith)]
    linarith
  constructor
  · simp only [procStarR, procR, act2R_a]; linarith
  · simp only [procStarR, procR, act2R_b]; linarith

/-- The test sequence is non-constant: `procStarR ε ≠ procR (2/3)` for every `ε ∈ (0, ½]`. -/
theorem procStarR_ne_limit (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    procStarR ε h0.le h1 ≠ procR (2 / 3) (by norm_num) (by norm_num) := by
  intro h
  have hw := congrArg (fun C => (C ()).w Act2.a) h
  simp only [procStarR, procR, act2R_a] at hw
  have := qStarR_sub_two_thirds ε h1
  have hpos : 0 < ε / (6 * (1 - ε)) := div_pos h0 (by linarith)
  linarith

end Cleanroom.Decision.DpDutchBook.AuditR2Adv
