import Cleanroom.Lit.LitWeathersonFrames.Coin

/-!
Audit r1 (fidelity) probe for `lit-weatherson-frames`. Not imported by the library.

The report's "Deviation 1" claims the mandate's convention `ValueBdd` with *per-option* bounds
(`∀ i, Bdd (o i)`) is false on Coin, which is why the package's `ValueBdd` quantifies over
uniformly bounded menus (`BddFam`). This probe compiles that claim: the per-option predicate,
spelled out exactly as the mandate words it, fails on `Coin.frame` through the paper's own menu
and strategy (each `O i` is bounded, `s` is recommended, its return is `0 < 1/2`).
-/

namespace Cleanroom.Lit.LitWeathersonFrames

/-- The mandate's per-option `ValueBdd`, verbatim. -/
def ValueBddPerOption {W : Type} (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) (o : ι → W → ℝ), (∀ i, Bdd (o i)) →
    ∀ S, RecommendedC F o S → ∀ i, Eℕ π (o i) ≤ stratValueC π o S

theorem probe_coin_not_valueBddPerOption : ¬ ValueBddPerOption Coin.π Coin.frame := by
  intro h
  have := h ℕ Coin.O Coin.O_bdd Coin.s Coin.s_recommended 0
  rw [Coin.E_prior_O, Coin.stratValue_s] at this
  norm_num at this

end Cleanroom.Lit.LitWeathersonFrames
