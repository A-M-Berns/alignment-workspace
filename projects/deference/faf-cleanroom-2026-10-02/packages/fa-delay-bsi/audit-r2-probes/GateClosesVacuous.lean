import Cleanroom.Fa.FaDelayBsi.Anticipated

/-!
# fa-delay-bsi · audit r2 (adversarial) · probe: E2 says nothing on an empty day-set

`gate_closes_of_realized_tendsto_zero` (`Anticipated.lean`, E2) takes a generable `{0,1}` day-set
`E` with no requirement that it fire infinitely often. On the empty day-set `E ≡ EF.const 0` the
filter `atTop ⊓ 𝓟 {n | (E n).denote A = 1}` is `⊥`, so the antecedent `hY` (realized credence
`→ 0` along `E`) holds for free and so does the conclusion — the theorem is vacuous there, and more
generally on every finite day-set. The same shape is inherited from `fa-theorem-a`'s `lemmaP`
(same `hE`, `hE01`, no divergence clause), so this is not a defect introduced here; it is recorded
so the ledger's "half the composition" is read with "on a day-set that fires infinitely often"
understood. Not imported by the library.
-/

namespace Cleanroom.Fa.FaDelayBsi.AuditR2

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Cleanroom.Fa.FaDelayBsi
open Filter Topology

/-- The day-set of `E ≡ EF.const 0` is empty. -/
theorem dayset_const_zero_empty (A : History) :
    {n : ℕ | ((fun _ : ℕ => EF.const (0 : ℚ)) n).denote A = 1} = ∅ := by
  ext n
  simp

/-- On `E ≡ EF.const 0` every hypothesis of E2 is met (the weighting is generable, `{0,1}`-valued,
and the along-`E` antecedent holds trivially) and its conclusion is a statement in the filter `⊥`. -/
theorem gate_closes_vacuous_on_empty_dayset {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (_pkg : CrossQuotePackage H DPA f X Y) (t δ : ℚ) :
    PGenerableWeighting (fun _ : ℕ => EF.const (0 : ℚ)) ∧
    (∀ n, ((fun _ : ℕ => EF.const (0 : ℚ)) n).denote A = 0 ∨
      ((fun _ : ℕ => EF.const (0 : ℚ)) n).denote A = 1) ∧
    Tendsto (realized H f X)
      (atTop ⊓ 𝓟 {n | ((fun _ : ℕ => EF.const (0 : ℚ)) n).denote A = 1}) (𝓝 0) ∧
    (∀ᶠ n in atTop ⊓ 𝓟 {n | ((fun _ : ℕ => EF.const (0 : ℚ)) n).denote A = 1},
      (quoteRampAbove Y t δ n).denote A = 0) := by
  refine ⟨pgenerableWeighting_const 0, fun n => Or.inl (by simp), ?_, ?_⟩
  · rw [dayset_const_zero_empty, Filter.principal_empty, inf_bot_eq]
    exact tendsto_bot
  · rw [dayset_const_zero_empty, Filter.principal_empty, inf_bot_eq]
    exact Filter.eventually_bot

end Cleanroom.Fa.FaDelayBsi.AuditR2

#print axioms Cleanroom.Fa.FaDelayBsi.AuditR2.gate_closes_vacuous_on_empty_dayset
