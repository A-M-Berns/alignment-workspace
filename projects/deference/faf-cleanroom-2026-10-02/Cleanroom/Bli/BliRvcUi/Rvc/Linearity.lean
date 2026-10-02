import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import LogicalInduction.Construction.LUV.Endpoints

/-!
# `bli-rvc-ui` · Rvc/Linearity: real-value coherence (E) in the limit is FAF's linearity of expectation (T1.3)

**The claim.** Exact additivity `𝔼ₙ(X) + 𝔼ₙ(Y) ≈ₙ 𝔼ₙ(Z)` holds in the limit for every inductor,
under FAF's own premise package for `thm:loe` (`lic_linearity_of_expectation_seq`) at the
coefficients `a = b = 1`. This is the restatement the desiderata call D-RVC(E) "exact only in the
limit" (I9); the premises are FAF's `def:blcp` / `def:affthmval` interface and are carried as
disclosed (b) hypotheses — their discharge on a concrete family over `liaHistory (paperDP T)`
(stretch S2, FAF's `_ofSyntax` / `_arith` carriers) is not attempted here.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional

/-- **T1.3 — exact additivity of the day-`n` expectation in the limit** (FAF's `thm:loe` at
`a = b = 1`).
Source: `main.tex:349` (the expectation of `A + B`); [[bli-program-desiderata]] I9; FAF
`lic_linearity_of_expectation_seq`
Kind: C
Fidelity: exact (limit form; the finite-day form is T1.2's ε-form)
Hyps: (b) `h` (`def:blcp`: bounded, polynomially generated combination sequence), `hwv`
(`WorldValued`: every completed world values the LUVs), `hdet0` (`def:affthmval`: the combination
`X + Y − Z` is determined at `0` by the theory) — FAF's own interface for `thm:loe`, taken as
stated; (a) `hworld`. -/
theorem rvcE_limit {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (X Y Z : ℕ → LUV)
    (h : LUVCombination.BoundedSequence
      (linearityLUVComb (fun _ => .const 1) (fun _ => .const 1) X Y Z) P)
    (hwv : LUVCombination.WorldValued
      (linearityLUVComb (fun _ => .const 1) (fun _ => .const 1) X Y Z) DP)
    (hdet0 : LUVCombination.DeterminedViaTheory
      (linearityLUVComb (fun _ => .const 1) (fun _ => .const 1) X Y Z) P DP (fun _ => 0))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AsympEq (fun n => (X n).expect P n + (Y n).expect P n) (fun n => (Z n).expect P n) := by
  have hlin := lic_linearity_of_expectation_seq (fun _ => EF.const 1) (fun _ => EF.const 1) X Y Z
    h hwv hdet0 hworld
  simpa using hlin

end Cleanroom.Bli.BliRvcUi
