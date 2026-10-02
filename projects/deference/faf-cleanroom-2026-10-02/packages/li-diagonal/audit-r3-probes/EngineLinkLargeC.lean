import Cleanroom.Li.LiDiagonal.Engine

/-!
# `li-diagonal` · audit round 3 · adversarial lens · probe: where the engine's link is the conclusion

**Not imported by the library.** Evidence for `li-diagonal-audit-r3-adversarial.md`.

Repair round 2 added `link_of_asympEq` (the engine's conclusion implies its link `hlink` for any
`y`, `c`) and the ledger row for `pinning_engine` now says "the link is the *weaker* side … not a
squeeze". This probe sharpens that: the gap between the link and the conclusion is exactly the
room `y` has on either side of `t`. When `c` exceeds that room — here `c > 1` with `y`, `t` in
`[0, 1]` — both consequents of `hlink` are unsatisfiable, so `hlink` says directly that
`𝔼_n(Y_n)` is eventually within `ε` of `t`: the link *is* the conclusion and the engine is a
tautology in that regime. The regime with content is `c ≤` the spread of `y` on each side of `t`,
and the shipped witness `pinning_engine_diagonal` sits exactly at its edge: `y ∈ {0, 1}`,
`t = p`, `c = min p (1 − p)`, so the consequents `y ≤ p − c` and `p + c ≤ y` are satisfied by
`y = 0` and `y = 1` respectively and the link is a theorem (`thm:ei` + reflection), not the limit.
-/

namespace Cleanroom.Li.LiDiagonal.AuditR3Adv

open LogicalInduction Cleanroom.Found.LiAsympCalc Filter Topology

/-- **At `c > 1` the link is the conclusion.** With `y`, `t` in `[0, 1]`, both consequents of
`hlink` are impossible, so the link's two antecedents are eventually false: `|𝔼_n(Y_n) − t| ≤ ε`
eventually, for every `ε`. No inductor, no `hdet`, no `hworld` needed. -/
theorem link_is_conclusion_of_large_c (P : History) (Y : ℕ → LUV) (y : ℕ → ℝ)
    (hy : ∀ n, y n ∈ Set.Icc (0 : ℝ) 1) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : ℝ) (hc : 1 < c)
    (hlink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ((t : ℝ) + ε < (Y n).expect P n → y n ≤ t - c) ∧
      ((Y n).expect P n < (t : ℝ) - ε → (t : ℝ) + c ≤ y n)) :
    (fun n => (Y n).expect P n) ≈ₙ fun _ => (t : ℝ) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [hlink ε hε] with n hn
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have ht1R : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  obtain ⟨hy0, hy1⟩ := hy n
  rw [abs_le]
  constructor
  · by_contra h
    push Not at h
    have := hn.2 (by linarith)
    linarith
  · by_contra h
    push Not at h
    have := hn.1 (by linarith)
    linarith

/-- **The diagonal witness is at the edge of the regime with content**: at `t = p`,
`c = min p (1 − p)`, the link's consequents are satisfiable by the two truth values `0` and `1`
(so `hlink` there is a genuine constraint relating the price to the truth, not the limit). -/
theorem diagonal_link_consequents_satisfiable (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    (0 : ℝ) ≤ (p : ℝ) - min (p : ℝ) (1 - p) ∧ (p : ℝ) + min (p : ℝ) (1 - p) ≤ 1 := by
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  constructor
  · linarith [min_le_left (p : ℝ) (1 - p)]
  · linarith [min_le_right (p : ℝ) (1 - p)]

end Cleanroom.Li.LiDiagonal.AuditR3Adv
