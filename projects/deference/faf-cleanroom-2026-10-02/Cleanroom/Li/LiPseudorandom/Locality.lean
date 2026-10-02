import LogicalInduction.Framework.Criterion
import LogicalInduction.Properties.Calibration

/-!
# `li-pseudorandom` — T3: rank locality of feature denotation

A feature of rank `≤ n` denotes the same real on two histories that agree on every day `≤ n`,
by induction on `EF` (`EF.rank`, `Framework/Criterion.lean`). Not in FAF (grep 2026-09-29: only the
`EFn` subring is graded by rank). Hence a `PGenerableWeighting` (`rank_le : ∀ n, (W n).rank ≤ n`)
reads the market at days `≤ n` only on day `n` — the fact that makes the builder rules of T5
strictly causal.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction

/-- **Rank locality of `denoteWith`.** If `e.rank ≤ n` and `P`, `P'` agree on all days `≤ n`,
then `e.denoteWith ρ P = e.denoteWith ρ P'` for every environment `ρ`.
Source: mandate T3; FAF `EF.rank` (`def:valfeature`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem EF.denoteWith_congr_of_rank_le (e : EF) {n : ℕ} (he : e.rank ≤ n)
    {P P' : History} (hPP' : ∀ m ≤ n, ∀ φ, P m φ = P' m φ) :
    ∀ ρ : List ℝ, e.denoteWith ρ P = e.denoteWith ρ P' := by
  induction e with
  | price φ m => intro ρ; simp only [EF.denoteWith_price]; exact hPP' m he φ
  | const q => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      simp only [EF.rank_add, Nat.max_le] at he
      simp only [EF.denoteWith_add, iha he.1 ρ, ihb he.2 ρ]
  | mul a b iha ihb =>
      intro ρ
      simp only [EF.rank_mul, Nat.max_le] at he
      simp only [EF.denoteWith_mul, iha he.1 ρ, ihb he.2 ρ]
  | max a b iha ihb =>
      intro ρ
      simp only [EF.rank_max, Nat.max_le] at he
      simp only [EF.denoteWith_max, iha he.1 ρ, ihb he.2 ρ]
  | safeRecip a iha =>
      intro ρ
      simp only [EF.rank_safeRecip] at he
      simp only [EF.denoteWith_safeRecip, iha he ρ]
  | var i => intro ρ; rfl
  | letE x body ihx ihbody =>
      intro ρ
      simp only [EF.rank_letE, Nat.max_le] at he
      simp only [EF.denoteWith_letE, ihx he.1 ρ, ihbody he.2 _]

/-- **Rank locality of `denote`.** A feature of rank `≤ n` denotes the same real on histories
agreeing on all days `≤ n`.
Source: mandate T3; FAF `EF.rank` (`def:valfeature`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem EF.denote_congr_of_rank_le (e : EF) {n : ℕ} (he : e.rank ≤ n)
    {P P' : History} (hPP' : ∀ m ≤ n, ∀ φ, P m φ = P' m φ) :
    e.denote P = e.denote P' :=
  EF.denoteWith_congr_of_rank_le e he hPP' []

/-- **A P-generable weighting is day-local**: `(W n).denote P` depends on `P` at days `≤ n` only.
Source: mandate T3; FAF `PGenerableWeighting.rank_le`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem PGenerableWeighting.denote_congr {W : ℕ → EF} (hW : PGenerableWeighting W) (n : ℕ)
    {P P' : History} (hPP' : ∀ m ≤ n, ∀ φ, P m φ = P' m φ) :
    (W n).denote P = (W n).denote P' :=
  EF.denote_congr_of_rank_le (W n) (hW.rank_le n) hPP'

end Cleanroom.Li.LiPseudorandom
