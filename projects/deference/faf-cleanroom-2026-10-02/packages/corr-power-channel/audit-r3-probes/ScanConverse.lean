import Cleanroom.Corrigibility.CorrPowerChannel.Separable

/-!
Audit r3 (adversarial) probe for `voiExp_ofMap_eq_evpi_of_factors` (`Separable.lean`, repair round 2).

The theorem proves `VOI(ofMap f) = EVPI` **when** the value table on `B` factors through `f`. The
`Separable.lean` module header (and the round-2 adversarial audit that proposed the lemma) phrase it
as "a scan is worth `EVPI` *iff* it reveals everything decision-relevant". The report says only the
`⇐` direction is claimed. This file shows the converse — "worth `EVPI` ⟹ the table factors through
`f`" — is **false**, so the "iff" wording is an oversell and not a theorem waiting to be proved:

`Ω = Bool` uniform, two options, option `0` worth `1` under both hypotheses (dominant), option `1`
worth `1/2` under `true` and `0` under `false`; `f : Bool → Unit` constant (the trivial scan). Then
`VOI(ofMap f) = 0 = EVPI` (a dominant option makes every scan worthless), while the table on `univ`
does **not** factor through `f` (`V true 1 = 1/2 ≠ 0 = V false 1` with `f true = f false`).

So the condition "factors through `f`" is sufficient and not necessary for "worth `EVPI`"; the
"decision-relevant" reading of the condition is the right one in prose, but the Lean hypothesis is
the stronger pointwise-factoring one.

Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel.AuditR3

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrPowerChannel
open Finset hiding expect expect_const

noncomputable section

/-- The uniform mass on `Bool`. -/
theorem uniform_mass_bool (ω : Bool) : (Distr.uniform : Distr Bool).mass ω = 1 / 2 := by
  norm_num [Distr.uniform, Fintype.card_bool]

/-- Option `0` dominant (worth `1` everywhere); option `1` worth `1/2` under `true`, `0` under `false`. -/
def domV : Bool → Fin 2 → ℝ := fun ω => ![1, if ω then 1 / 2 else 0]

/-- The constant map: the trivial scan as an `ofMap`. -/
def constMap : Bool → Unit := fun _ => ()

/-- **The converse of `voiExp_ofMap_eq_evpi_of_factors` fails**: `VOI(ofMap constMap) = 0 = EVPI`,
yet the table does not factor through `constMap`. -/
theorem converse_fails :
    voiExp (Distr.uniform : Distr Bool) domV (ofMap constMap) univ univ_nonempty = 0 ∧
      evpi (Distr.uniform : Distr Bool) domV univ univ_nonempty = 0 ∧
      ¬ (∀ a ∈ (univ : Finset (Fin 2)), ∀ ω ω' : Bool,
          constMap ω = constMap ω' → domV ω a = domV ω' a) := by
  have hu2 : (univ : Finset (Fin 2)) = {0, 1} := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp [voiExp, bestMix, mixValue, expect, hu2, uniform_mass_bool, ofMap, constMap, domV]
  · simp [evpi, power, bestMix, attainable, mixValue, expect, hu2, uniform_mass_bool, domV]
    norm_num
  · intro h
    have := h 1 (mem_univ _) true false rfl
    simp [domV] at this

/-- The same two numbers read as the theorem's conclusion: the equation `VOI(ofMap f) = EVPI` holds
here although its hypothesis does not — the hypothesis is sufficient, not necessary. -/
theorem equation_holds_without_factoring :
    voiExp (Distr.uniform : Distr Bool) domV (ofMap constMap) univ univ_nonempty =
      evpi (Distr.uniform : Distr Bool) domV univ univ_nonempty := by
  rw [converse_fails.1, converse_fails.2.1]

end

end Cleanroom.Corrigibility.CorrPowerChannel.AuditR3
