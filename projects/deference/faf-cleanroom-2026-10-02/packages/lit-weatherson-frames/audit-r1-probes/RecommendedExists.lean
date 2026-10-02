import Cleanroom.Lit.LitWeathersonFrames.Bentham

/-!
Audit round 1, adversarial lens — probe: the inner hypothesis package of the finite-menu Value
predicates (`ValueFinInt`, `ValueFinBdd`) is inhabited on **every** `CFrame`.

`ValueFinInt π F` quantifies over recommended strategies; if no strategy were ever recommended
the predicate would hold vacuously. It never does: for a finite nonempty menu an argmax exists at
every row, and choosing by the row (`S w := g (F.P w)`) satisfies the cell constraint by
construction. Instantiated on Bentham, whose recommendation clause at the null world `0` (row
`π`) is part of the hypothesis of `Bentham.valueFinInt`. Not imported by the library.
-/

namespace Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv

open Cleanroom.Lit.LitWeathersonFrames

/-- Every finite nonempty menu has a recommended strategy on every countable frame. -/
theorem exists_recommended {W : Type} (F : CFrame W) {ι : Type} [Fintype ι] [Nonempty ι]
    (o : ι → W → ℝ) : ∃ S, RecommendedC F o S := by
  classical
  have key : ∀ ρ : W → ℝ, ∃ i, ∀ j, Eℕ ρ (o j) ≤ Eℕ ρ (o i) := fun ρ =>
    Finite.exists_max (fun i => Eℕ ρ (o i))
  choose g hg using key
  exact ⟨fun w => g (F.P w), fun w v h => congrArg g h, fun w i => hg (F.P w) i⟩

/-- On Bentham in particular (recommendation at the null world included). -/
theorem bentham_exists_recommended {ι : Type} [Fintype ι] [Nonempty ι] (o : ι → ℕ → ℝ) :
    ∃ S, RecommendedC Bentham.frame o S :=
  exists_recommended Bentham.frame o

end Cleanroom.Lit.LitWeathersonFrames.AuditR1Adv
