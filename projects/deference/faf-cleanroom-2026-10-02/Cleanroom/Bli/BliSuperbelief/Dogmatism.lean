import Cleanroom.Bli.BliFinite.Actual
import Cleanroom.Bli.BliFinite.Superbelief

/-!
# `bli-superbelief` · Dogmatism: positive mass on the realized state iff the face condition (E6,
finite part)

The realized next state is the *rounded* day-`(m+1)` table `actualState V (m+1)`. Under any
balanced grid probability on day `m` it carries positive mass **only if** it lies on the product
face of the day-`m` table (`null_of_not_mem_faceProd` — `bli-finite`'s pinning lemma), and under
a non-degenerate one **iff** it does (`dogmatism`). The face condition unfolds to: *no small
sentence priced exactly `0` or `1` on day `m` has a different rounded price on day `m+1`*
(`actual_mem_faceProd_iff`). So a base that moves a `0/1` price makes the next state **null** —
conditioning on it divides by zero (bli-slides-018) — under *every* balanced superbelief,
non-degenerate or not (`null_of_zero_moved`). The FAF instance (a sentence entering the market
maker's support: day-`n` quote `0` off support, day-`(n+1)` quote above `1/(2d)`) is
`Paper.lean`'s `supportEntry_not_mem_faceProd`.

Rounding threshold: with `bli-finite`'s ties-down rounding, `roundVal d x > 0 ↔ 1/(2d) < x`
(`roundVal_pos_iff`); the mandate's `1/(2d) ≤ x` is off by the tie (see the findings).

Sources: bli-soto-a-034 (the support problem), bli-slides-018 (conditioning divides by zero);
[[bli-program]] §3.4 Dogmatism (`D:I7`, the withdrawal of `C:C2`'s "always positive"), §3.10 row
E6, §7 items 5, 11.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex} {d : ℕ → ℕ} {m : ℕ}

/-! ## The face condition on the realized state -/

/-- **E6(a).** The realized (rounded) day-`(m+1)` state is on the product face of the day-`m`
table iff no day-`m` small sentence priced exactly `0` or `1` has a different *rounded* price on
day `m+1`. Unconditional (no unit-cube hypothesis): the rounding clamps.
Source: [[bli-program]] §3.4 Dogmatism ("iff no small sentence priced exactly 0 or 1 on day `n`
has a different rounded price on day `n+1`")
Kind: L
Fidelity: exact -/
theorem actual_mem_faceProd_iff (V : RatHistory) (m : ℕ) :
    actualState 𝒮 d V (m + 1) ∈ faceProd 𝒮 d m (actualTable 𝒮 V m) ↔
      ∀ φ : ↥(𝒮.S m), (V m φ.1 = 0 ∨ V m φ.1 = 1) →
        roundVal (d (m + 1)) (V (m + 1) φ.1) = V m φ.1 := by
  rw [mem_faceProd_iff]
  constructor
  · rintro ⟨-, h⟩ φ hφ
    exact h φ hφ
  · intro h
    exact ⟨actualState_mem_grid, fun φ hφ => h φ hφ⟩

/-! ## Null off the face; positive on it under non-degeneracy -/

/-- **E6(b), the null direction.** Every balanced grid probability puts mass `0` on any table
outside the product face — `faceGen_subset_faceProd` plus the definitional
`mem_faceGen_of_pos` (`bli-finite`).
Source: bli-slides-021; [[bli-program]] §3.4
Kind: C
Fidelity: exact
Hyps: (a) none beyond `IsProb ∧ Balanced` -/
theorem null_of_not_mem_faceProd {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m} (hF : IsProb d F)
    (hb : Balanced d F t) {Q : Table 𝒮 (m + 1)} (hQ : Q ∉ faceProd 𝒮 d m t) : F Q = 0 := by
  by_contra h
  have hpos : 0 < F Q := lt_of_le_of_ne (hF.1 Q) (Ne.symm h)
  exact hQ (faceGen_subset_faceProd d t
    (mem_faceGen_of_pos hF (balanced_iff_restrict_meanOn_eq.mp hb) hpos))

/-- **E6(b), the converse under non-degeneracy**: `0 < F Q ↔ Q ∈ faceProd` — `bli-finite`'s
`nonDegenerate_iff_support_eq_faceProd`, cited.
Source: bli-slides-018 (`FS`); [[bli-program]] §2.4
Kind: C
Fidelity: exact
Hyps: (a) `NonDegenerate` -/
theorem pos_iff_mem_faceProd_of_nonDegenerate {F : Superbelief 𝒮 (m + 1)} {t : Table 𝒮 m}
    (hF : IsProb d F) (hb : Balanced d F t) (hnd : NonDegenerate d F t) (Q : Table 𝒮 (m + 1)) :
    0 < F Q ↔ Q ∈ faceProd 𝒮 d m t :=
  (nonDegenerate_iff_support_eq_faceProd hF hb).mp hnd Q

/-- **E6, the headline (finite part).** Under `IsProb ∧ Balanced ∧ NonDegenerate` at the day-`m`
actual table, the realized day-`(m+1)` state has positive mass **iff** the face condition holds:
no day-`m` small sentence priced exactly `0` or `1` has a different rounded price on day `m+1`.
The mathematics is `bli-finite`'s pinning lemma; this composes it with `actual_mem_faceProd_iff`.
Source: [[bli-program]] §3.4 Dogmatism (`D:I7`); bli-slides-018
Kind: C
Fidelity: exact
Hyps: (a) `IsProb`, `Balanced`, `NonDegenerate` at `actualTable V m` -/
theorem dogmatism (V : RatHistory) (m : ℕ) {F : Superbelief 𝒮 (m + 1)} (hF : IsProb d F)
    (hb : Balanced d F (actualTable 𝒮 V m)) (hnd : NonDegenerate d F (actualTable 𝒮 V m)) :
    0 < F (actualState 𝒮 d V (m + 1)) ↔
      ∀ φ : ↥(𝒮.S m), (V m φ.1 = 0 ∨ V m φ.1 = 1) →
        roundVal (d (m + 1)) (V (m + 1) φ.1) = V m φ.1 := by
  rw [pos_iff_mem_faceProd_of_nonDegenerate hF hb hnd, actual_mem_faceProd_iff]

/-! ## Rounding threshold -/

/-- The rounded value is positive iff the clamped value exceeds half a grid step (ties round
down, so `1/(2d)` itself rounds to `0`).
Source: bli-paper-033 (rounding); mandate E6(d) (corrected: `<`, not `≤`)
Kind: L
Fidelity: exact -/
lemma roundVal_pos_iff {d : ℕ} (hd : 0 < d) (x : ℚ) :
    0 < roundVal d x ↔ 1 / (2 * (d : ℚ)) < clamp01 x := by
  unfold roundVal
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_pos_iff_of_pos_right hdq, Int.cast_pos, Int.ceil_pos, sub_pos,
    div_lt_iff₀ (by positivity : (0 : ℚ) < 2 * d)]
  constructor <;> intro h <;> linarith

/-- The rounded value of a price in `[0,1]` is positive iff the price exceeds `1/(2d)`.
Source: bli-paper-033; mandate E6(d) (corrected threshold)
Kind: L
Fidelity: exact -/
lemma roundVal_pos_iff_of_mem {d : ℕ} (hd : 0 < d) {x : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) :
    0 < roundVal d x ↔ 1 / (2 * (d : ℚ)) < x := by
  rw [roundVal_pos_iff hd, clamp01_eq_self hx]

/-! ## A moved 0/1 price makes the realized state null -/

/-- If a day-`m` small sentence is priced exactly `0` and its day-`(m+1)` price rounds to something
positive, the realized day-`(m+1)` state is off the product face.
Source: [[bli-program]] §3.4 Dogmatism (the support-entry mechanism, finite part)
Kind: L
Fidelity: exact -/
theorem not_mem_faceProd_of_zero_moved (V : RatHistory) (m : ℕ) (φ : ↥(𝒮.S m))
    (h0 : V m φ.1 = 0) (hpos : 0 < roundVal (d (m + 1)) (V (m + 1) φ.1)) :
    actualState 𝒮 d V (m + 1) ∉ faceProd 𝒮 d m (actualTable 𝒮 V m) := by
  rw [actual_mem_faceProd_iff]
  intro h
  have := h φ (Or.inl h0)
  rw [h0] at this
  linarith

/-- Dually for a price exactly `1` whose day-`(m+1)` price rounds below `1`.
Source: [[bli-program]] §3.4 Dogmatism
Kind: L
Fidelity: exact -/
theorem not_mem_faceProd_of_one_moved (V : RatHistory) (m : ℕ) (φ : ↥(𝒮.S m))
    (h1 : V m φ.1 = 1) (hlt : roundVal (d (m + 1)) (V (m + 1) φ.1) < 1) :
    actualState 𝒮 d V (m + 1) ∉ faceProd 𝒮 d m (actualTable 𝒮 V m) := by
  rw [actual_mem_faceProd_iff]
  intro h
  have := h φ (Or.inr h1)
  rw [h1] at this
  linarith

/-- **The realized state is null under every balanced superbelief** — non-degenerate or not —
whenever the base moved a `0` price to a positively-rounding one: conditioning on the realized
state on such a day divides by zero. The hypotheses are three concrete facts about one day.
Source: bli-slides-018 (null conditioning); [[bli-program]] §3.4 Dogmatism, §7 item 5
Kind: C
Fidelity: exact
Hyps: (a) `IsProb ∧ Balanced` at `actualTable V m`; (a) the moved price -/
theorem null_of_zero_moved (V : RatHistory) (m : ℕ) (φ : ↥(𝒮.S m)) (h0 : V m φ.1 = 0)
    (hpos : 0 < roundVal (d (m + 1)) (V (m + 1) φ.1)) {F : Superbelief 𝒮 (m + 1)}
    (hF : IsProb d F) (hb : Balanced d F (actualTable 𝒮 V m)) :
    F (actualState 𝒮 d V (m + 1)) = 0 :=
  null_of_not_mem_faceProd hF hb (not_mem_faceProd_of_zero_moved V m φ h0 hpos)

end Cleanroom.Bli.BliSuperbelief
