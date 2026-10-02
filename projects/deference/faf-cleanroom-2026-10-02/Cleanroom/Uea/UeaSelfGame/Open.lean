import Cleanroom.Uea.UeaSelfGame.Repaired

/-!
# Open statements of `uea-self-game`

Precise statements with `sorry`, listed in `run/wp/uea-self-game/uea-self-game-open.txt`. A leaf module:
nothing in the library imports it.

* `inclusion_open` — [[uea-2-inventory]] 2-014/2-015's conjecture (1500/1500 instances): if some pure
  Herrmann fixed point exists then some pure extension fixed point exists. Not attempted beyond the
  statement; a proof would need to move from a Herrmann argmax (over available actions) to an argmax
  over all actions, which the `|S| = 1` witness (`Herrmann.lean`) shows cannot be the *same* policy.
* `floored_mixed_bound_open` — the corrected mixed bound for floored extension fixed points, with constant
  `2`: the `section_5` instance (`Floored.lean`) has gap `≈ 1.898 δ` and the mandate's parametric family
  approaches `2δ`, so no constant below `2` can work; whether `2δ/(1−δ)` suffices is open.

**Retired (proved).** `sup_limit_open` — the supremum half of the corrected tightness statement on
`δ ≤ 1/2` (for every `δ ∈ (0, 1/2]` and `ε > 0` a pure fixed point with the trust bound at every
situation and gap `≥ δ/(1−δ) − ε`) — was listed here through repair round 2, where it acquired the
hypothesis `δ ≤ 1/2` (adversarial audit B1: the gap is at most `1`, so the form over all `δ ∈ (0,1)` was
false, `Regimes.sup_limit_previous_form_false_above_half`). It is now the theorem `T3Family.sup_limit`,
with the statement unchanged, proved from the general `T3(n, θ, g)` family (`T3Family.lean`, the
continuation of repair round 2); the non-attainment half is `Attainment.theoremC_strict`, and above
`1/2` the gap `1` is attained for every `δ` (`T3Family.gap_one_attained_above_half`).

Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30; repair round 2, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSelfGame

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-- **OPEN (inclusion conjecture)**: a pure Herrmann fixed point implies a pure extension fixed point
(some pure policy, not necessarily the same one).
Source: [[uea-2-inventory]] 2-014, 2-015 ("if some pure Herrmann fixed point exists then some pure
extension fixed point exists", 1500/1500 random instances)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem inclusion_open (h : ∃ π, G.IsPureFP π) : ∃ π, G.IsFPext (pureMix π) := by
  sorry

/-- **OPEN (corrected mixed floored bound)**: every floored extension fixed point is within `2δ/(1−δ)` of
optimal. The constant `2` cannot be lowered: `FlooredFamily.constant_ge_two` (repair round 1) shows that
`U* − cδ/(1−δ) ≤ U(σ)` for all floored extension fixed points of `2 × 2` games with `δ ≤ 1/4` forces
`c ≥ 2` (whether `c = 2` itself works is this open statement), and `FlooredFamily.gap_le_open_bound` shows
that family is consistent with this statement (`Section5.gap_gt` is the earlier numerical lower bound
`3δ/2`). Content region: the conclusion is automatic for every mixed `σ` when `δ ≥ 1/3`
(`Regimes.floored_open_bound_trivial_of_third_le`), so the statement has content only for `δ < 1/3`.
Source: [[uea-self-game-mandate]] target 9 (f); [[updateless-self-game]] §7 (the false mixed claim)
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem floored_mixed_bound_open [Nonempty A] (σ : S → A → ℝ) (h : G.IsFlooredFPext σ) :
    G.Ustar - 2 * G.δ / (1 - G.δ) ≤ G.Umix σ := by
  sorry

end Game

end Cleanroom.Uea.UeaSelfGame
