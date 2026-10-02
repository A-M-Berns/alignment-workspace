import Cleanroom.Bli.BliFinite.Actual
import LogicalInduction.Construction.MarketMaker

/-!
# `bli-finite` · Bridge: rational belief states as rational histories (T8, bridge file)

**The only file of the package that imports `LogicalInduction.Construction.MarketMaker`**
(for `RationalBeliefState`); nothing else in the package imports this file. A sequence of
FAF rational belief states is a `RatHistory` through its exact rational `quote`, and the
real valuation FAF's markets denote is the cast of the actual table — the hook through which
`bli-found`/`bli-trajectory` bridge real histories via `ComputableMarket`'s rational quotes.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction

/-- The rational history of a sequence of FAF rational belief states: day `n`'s prices are the
exact rational quotes of `𝔹 n` (zero off its support).
Source: mandate T8 (bridge); FAF `Construction/MarketMaker.lean` `RationalBeliefState.quote`
Kind: D
Fidelity: exact -/
def ofBeliefStates (𝔹 : ℕ → RationalBeliefState) : RatHistory := fun n => (𝔹 n).quote

/-- Quotes of rational belief states lie in `[0,1]` (FAF's `quote_mem_Icc`), so every actual
table of `ofBeliefStates 𝔹` is in the unit cube.
Source: FAF `RationalBeliefState.quote_mem_Icc`
Kind: L
Fidelity: exact -/
lemma ofBeliefStates_inUnit (𝔹 : ℕ → RationalBeliefState) :
    ∀ n φ, 0 ≤ ofBeliefStates 𝔹 n φ ∧ ofBeliefStates 𝔹 n φ ≤ 1 :=
  fun n φ => (𝔹 n).quote_mem_Icc φ

/-- **The cast lemma**: the real valuation of `𝔹 m` at a small sentence is the cast of the actual
table's entry — definitionally.
Source: mandate T8 (bridge); FAF `RationalBeliefState.toValuation`
Kind: L
Fidelity: exact -/
lemma actualTable_ofBeliefStates_cast (𝒮 : SmallIndex) (𝔹 : ℕ → RationalBeliefState) (m : ℕ)
    (φ : ↥(𝒮.S m)) :
    ((actualTable 𝒮 (ofBeliefStates 𝔹) m φ : ℚ) : ℝ) = (𝔹 m).toValuation φ.1 := rfl

end Cleanroom.Bli.BliFinite
