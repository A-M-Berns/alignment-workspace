import LogicalInduction.Framework.Expectations
import Cleanroom.Bli.BliExtrapolation.Chain

/-!
# `bli-extrapolation` · Dyadic: the dyadic-interval LUV encoding over FAF's threshold
presentation (target 6)

PDF 07 "LUVs" / PIBBSS §4.2.2: for a `[0,1]`-LUV `X`, `D_X(m)` says "the value lies in the union
of the dyadic intervals of level `m` whose index has `m`-th digit `0`", and `X = Y` is rewritten
as `∀m (D_X(m) ↔ D_Y(m))`. Over FAF's `LUV` (`X.gt r = ⌜X > r⌝`) and `PCWorld.ValuesAt v X x`:
`dyadicSentence X n k := X.gt (k/2^n) ⋏ ∼X.gt ((k+1)/2^n)` for `0 < k`, and `∼X.gt (1/2^n)` for
`k = 0` (Soto's "`[0, 1/2^n]` when `k = 0`"); `digitSentence X m` is the disjunction over the
even-indexed cells.

**Boundary convention (a finding, F-14 in the findings file).** FAF's `ValuesAt v X x` fixes
`X.gt r` for `r < x` (true) and `r > x` (false) and leaves `X.gt x` **undetermined**. So a world
valuing `X` at a dyadic rational `x = k/2^n` holds exactly one of the two adjacent cells
`dyadicSentence X n (k-1)`, `dyadicSentence X n k`, according to its free verdict on `X.gt x`;
the source's half-open intervals `(k/2^n, (k+1)/2^n]` are not available as an exact
characterization. What is exact: the open-interval sufficiency (`holds_dyadic_of_mem_Ioo`), the
closed-interval necessity (`mem_Icc_of_holds_dyadic`), and the iff off the level-`n` grid
(`holds_dyadic_iff_of_notMem_grid`). The digit-level statements — `digitSentence_holds_iff`
(`D_X(m)` in terms of `⌊x·2^m⌋₊ % 2` off the grid) and the soundness of Soto's rewrite
`values_eq_of_digits` (equal digit sentences at every level force equal values, the boundary
freedom being consistent across levels because the threshold sentence `X.gt (k/2^n)` is the
*same* sentence at every level at which the rational `k/2^n` appears) — were `OPEN` after
round 1 and are proved in the repair round through the held-cell sequence `cellIdx` (last
section; the boundary analysis is in its header).

Not here: `LUV.expect`, real-value coherence (`bli-rvc-ui` X4/M8), and the partition-of-unity
corollary of bli-soto-a-051, which needs the valuation to be supported on threshold-monotone
worlds (the cells of one level are *not* propositionally exclusive: FAF's `X.gt r` are
independent atoms) — recorded in the findings (F-14), not stated.

Sources: PDF 07 p. 3 ("LUVs"); PIBBSS §4.2.2 and fn. 20; [[bli-soto-a-inventory]] 056, 051;
[[bli-soto-b-inventory]] 032.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional

/-- **The dyadic cell sentence**: "`X ∈ (k/2^n, (k+1)/2^n]`" for `0 < k`, "`X ∈ [0, 1/2^n]`" for
`k = 0`, over FAF's threshold sentences `X.gt r`.
Source: PDF 07 p. 3 ("LUVs"); PIBBSS §4.2.2; [[bli-soto-a-inventory]] 056
Kind: D
Fidelity: exact over FAF's threshold presentation (boundary convention: see the module docstring) -/
def dyadicSentence (X : LUV) (n k : ℕ) : Sentence :=
  if k = 0 then ∼X.gt (1 / 2 ^ n)
  else X.gt ((k : ℚ) / 2 ^ n) ⋏ ∼X.gt (((k : ℚ) + 1) / 2 ^ n)

/-- **Soto's `D_X(m)`**: the value lies in a level-`m` cell whose index is even (`m`-th binary
digit `0`).
Source: PDF 07 p. 3 (`D_X(m)`); PIBBSS §4.2.2
Kind: D
Fidelity: exact ("`m`-th digit of the index is `0`" read as `k % 2 = 0` for the cell index `k`) -/
def digitSentence (X : LUV) (m : ℕ) : Sentence :=
  sentenceDisjunction
    (((List.range (2 ^ m)).filter fun k => k % 2 = 0).map fun k => dyadicSentence X m k)

section

variable {v : PCWorld} {X : LUV} {x : ℝ}

/-- A world valuing `X` at `x` holds `X.gt r` whenever `r < x`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma ValuesAt.holds_gt (hv : v.ValuesAt X x) {r : ℚ} (hr : (r : ℝ) < x) : v.Holds (X.gt r) :=
  (hv.2.2 r).1 hr

/-- A world valuing `X` at `x` refutes `X.gt r` whenever `x < r`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma ValuesAt.not_holds_gt (hv : v.ValuesAt X x) {r : ℚ} (hr : x < (r : ℝ)) :
    ¬ v.Holds (X.gt r) :=
  (hv.2.2 r).2 hr

/-- If the world holds `X.gt r` then `r ≤ x` (contrapositive of `not_holds_gt`).
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma ValuesAt.le_of_holds_gt (hv : v.ValuesAt X x) {r : ℚ} (h : v.Holds (X.gt r)) :
    (r : ℝ) ≤ x :=
  le_of_not_gt fun hr => ValuesAt.not_holds_gt hv hr h

/-- If the world refutes `X.gt r` then `x ≤ r`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma ValuesAt.le_of_not_holds_gt (hv : v.ValuesAt X x) {r : ℚ} (h : ¬ v.Holds (X.gt r)) :
    x ≤ (r : ℝ) :=
  le_of_not_gt fun hr => h (ValuesAt.holds_gt hv hr)

/-- **Open-interval sufficiency**: a value strictly inside the level-`n` cell `k > 0` holds the
cell sentence.
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: exact
Hyps: (a) `ValuesAt`; (a) `0 < k`; (a) `x ∈ Ioo` -/
theorem holds_dyadic_of_mem_Ioo (hv : v.ValuesAt X x) {n k : ℕ} (hk : 0 < k)
    (hx : x ∈ Set.Ioo (((k : ℚ) / 2 ^ n : ℚ) : ℝ) ((((k : ℚ) + 1) / 2 ^ n : ℚ) : ℝ)) :
    v.Holds (dyadicSentence X n k) := by
  unfold dyadicSentence
  rw [if_neg hk.ne', PCWorld.holds_and, PCWorld.holds_neg]
  exact ⟨ValuesAt.holds_gt hv hx.1, ValuesAt.not_holds_gt hv hx.2⟩

/-- **The cell `0`**: a value strictly below `1/2^n` holds the cell-`0` sentence.
Source: PDF 07 p. 3 ("`[0, 1/2^n]` when `k = 0`")
Kind: P
Fidelity: exact -/
theorem holds_dyadic_zero_of_lt (hv : v.ValuesAt X x) {n : ℕ}
    (hx : x < (((1 : ℚ) / 2 ^ n : ℚ) : ℝ)) : v.Holds (dyadicSentence X n 0) := by
  unfold dyadicSentence
  rw [if_pos rfl, PCWorld.holds_neg]
  exact ValuesAt.not_holds_gt hv hx

/-- **Closed-interval necessity**: a world holding the level-`n` cell `k > 0` values `X` in the
closed cell.
Source: PDF 07 p. 3
Kind: P
Fidelity: exact -/
theorem mem_Icc_of_holds_dyadic (hv : v.ValuesAt X x) {n k : ℕ} (hk : 0 < k)
    (h : v.Holds (dyadicSentence X n k)) :
    x ∈ Set.Icc (((k : ℚ) / 2 ^ n : ℚ) : ℝ) ((((k : ℚ) + 1) / 2 ^ n : ℚ) : ℝ) := by
  unfold dyadicSentence at h
  rw [if_neg hk.ne', PCWorld.holds_and, PCWorld.holds_neg] at h
  exact ⟨ValuesAt.le_of_holds_gt hv h.1, ValuesAt.le_of_not_holds_gt hv h.2⟩

/-- A world holding the cell-`0` sentence values `X` at most `1/2^n`.
Source: PDF 07 p. 3
Kind: P
Fidelity: exact -/
theorem le_of_holds_dyadic_zero (hv : v.ValuesAt X x) {n : ℕ}
    (h : v.Holds (dyadicSentence X n 0)) : x ≤ (((1 : ℚ) / 2 ^ n : ℚ) : ℝ) := by
  unfold dyadicSentence at h
  rw [if_pos rfl, PCWorld.holds_neg] at h
  exact ValuesAt.le_of_not_holds_gt hv h

/-- **`dyadicSentence_holds_iff` off the grid**: for a value that is neither endpoint of the
level-`n` cell `k > 0`, the world holds the cell sentence iff the value lies in the (open = closed)
cell. On the grid the verdict is the world's free choice (module docstring).
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: weaker: off the level-`n` grid (FAF's `ValuesAt` leaves `X.gt x` undetermined)
Hyps: (a) `ValuesAt`; (a) `x` not an endpoint -/
theorem holds_dyadic_iff_of_notMem_grid (hv : v.ValuesAt X x) {n k : ℕ} (hk : 0 < k)
    (h1 : x ≠ (((k : ℚ) / 2 ^ n : ℚ) : ℝ)) (h2 : x ≠ ((((k : ℚ) + 1) / 2 ^ n : ℚ) : ℝ)) :
    v.Holds (dyadicSentence X n k) ↔
      x ∈ Set.Ioo (((k : ℚ) / 2 ^ n : ℚ) : ℝ) ((((k : ℚ) + 1) / 2 ^ n : ℚ) : ℝ) := by
  constructor
  · intro h
    obtain ⟨hl, hr⟩ := mem_Icc_of_holds_dyadic hv hk h
    exact ⟨lt_of_le_of_ne hl (Ne.symm h1), lt_of_le_of_ne hr h2⟩
  · exact holds_dyadic_of_mem_Ioo hv hk

/-- The cast of a level-`m` cell endpoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cast_dyadic (j m : ℕ) : ((((j : ℚ) / 2 ^ m : ℚ) : ℝ)) = (j : ℝ) / 2 ^ m := by simp

/-- The cast of a level-`m` cell's upper endpoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cast_dyadic_succ (j m : ℕ) :
    ((((j : ℚ) + 1) / 2 ^ m : ℚ) : ℝ) = ((j : ℝ) + 1) / 2 ^ m := by simp

/-- The cast of the cell-`0` endpoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cast_dyadic_one (m : ℕ) : (((1 : ℚ) / 2 ^ m : ℚ) : ℝ) = 1 / 2 ^ m := by simp

/-- **The unique cell off the grid**: if `x` is not a level-`m` grid point, the only level-`m`
cell a world valuing `X` at `x` can hold is `⌊x · 2^m⌋₊` (closed-interval necessity plus the two
grid exclusions make the cell's closed interval open at both ends).
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: exact off the grid
Hyps: (a) `ValuesAt`; (a) `x` off the level-`m` grid -/
theorem floor_eq_of_holds_dyadic (hv : v.ValuesAt X x) {m j : ℕ}
    (hgrid : ∀ i : ℕ, x ≠ (((i : ℚ) / 2 ^ m : ℚ) : ℝ))
    (h : v.Holds (dyadicSentence X m j)) : ⌊x * 2 ^ m⌋₊ = j := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have ht0 : 0 ≤ x * 2 ^ m := mul_nonneg hv.1 h2.le
  rw [Nat.floor_eq_iff ht0]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hle := le_of_holds_dyadic_zero hv h
    rw [cast_dyadic_one, le_div_iff₀ h2] at hle
    have hne : x * 2 ^ m ≠ 1 := by
      intro heq
      apply hgrid 1
      rw [cast_dyadic, Nat.cast_one, eq_div_iff h2.ne']
      exact heq
    refine ⟨by simpa using ht0, ?_⟩
    simpa using lt_of_le_of_ne hle hne
  · have hmem := mem_Icc_of_holds_dyadic hv hj h
    rw [cast_dyadic, cast_dyadic_succ] at hmem
    obtain ⟨hl, hr⟩ := hmem
    rw [div_le_iff₀ h2] at hl
    rw [le_div_iff₀ h2] at hr
    have hne : x * 2 ^ m ≠ (j : ℝ) + 1 := by
      intro heq
      apply hgrid (j + 1)
      rw [cast_dyadic, Nat.cast_succ, eq_div_iff h2.ne']
      exact heq
    exact ⟨hl, lt_of_le_of_ne hr hne⟩

/-- **`digitSentence_holds_iff`** (6): off the level-`m` grid, `D_X(m)` holds iff the `m`-th
binary digit of `x` is `0`, i.e. `⌊x · 2^m⌋₊ % 2 = 0`. Stated for `x < 1` and `x ∉ {j/2^m}`
(`0 ≤ x` is `ValuesAt`'s own bound): `x` then lies strictly inside the cell `k = ⌊x·2^m⌋₊ < 2^m`,
which it holds (`holds_dyadic_of_mem_Ioo`, or `holds_dyadic_zero_of_lt` for `k = 0`), and
`floor_eq_of_holds_dyadic` says no other cell can hold. On the grid the statement is false as an
iff for either reading of the digit: at `x = k/2^m` the world's free verdict on `X.gt x` selects
cell `k` or cell `k−1`, whose parities differ (F-14).
Source: PDF 07 p. 3 (`D_X(m)`); PIBBSS §4.2.2
Kind: P
Fidelity: weaker: off the level-`m` grid (on it, the digit is the world's free verdict)
Hyps: (a) `ValuesAt`; (a) `x < 1`; (a) `x` off the level-`m` grid -/
theorem digitSentence_holds_iff (hv : v.ValuesAt X x) {m : ℕ} (hx1 : x < 1)
    (hgrid : ∀ j : ℕ, x ≠ (((j : ℚ) / 2 ^ m : ℚ) : ℝ)) :
    v.Holds (digitSentence X m) ↔ ⌊x * 2 ^ m⌋₊ % 2 = 0 := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have ht0 : 0 ≤ x * 2 ^ m := mul_nonneg hv.1 h2.le
  unfold digitSentence
  rw [holds_sentenceDisjunction]
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j, ⟨_, hjeven⟩, rfl⟩, hj⟩
    rw [floor_eq_of_holds_dyadic hv hgrid hj]
    exact hjeven
  · intro heven
    have hkle : (⌊x * 2 ^ m⌋₊ : ℝ) ≤ x * 2 ^ m := Nat.floor_le ht0
    have hklt : x * 2 ^ m < ⌊x * 2 ^ m⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkne : (⌊x * 2 ^ m⌋₊ : ℝ) ≠ x * 2 ^ m := by
      intro heq
      apply hgrid ⌊x * 2 ^ m⌋₊
      rw [cast_dyadic, eq_div_iff h2.ne']
      exact heq.symm
    have hklt' : (⌊x * 2 ^ m⌋₊ : ℝ) < x * 2 ^ m := lt_of_le_of_ne hkle hkne
    have hk2 : ⌊x * 2 ^ m⌋₊ < 2 ^ m := by
      rw [Nat.floor_lt ht0]
      push_cast
      exact (mul_lt_iff_lt_one_left h2).mpr hx1
    refine ⟨dyadicSentence X m ⌊x * 2 ^ m⌋₊, ⟨⌊x * 2 ^ m⌋₊, ⟨hk2, heven⟩, rfl⟩, ?_⟩
    rcases Nat.eq_zero_or_pos ⌊x * 2 ^ m⌋₊ with hk0 | hkpos
    · rw [hk0]
      apply holds_dyadic_zero_of_lt hv
      rw [cast_dyadic_one, lt_div_iff₀ h2]
      rw [hk0] at hklt
      simpa using hklt
    · apply holds_dyadic_of_mem_Ioo hv hkpos
      rw [cast_dyadic, cast_dyadic_succ]
      exact ⟨(div_lt_iff₀ h2).mpr hklt', (lt_div_iff₀ h2).mpr hklt⟩

end

/-! ## The held-cell sequence and the soundness of Soto's rewrite

**Boundary analysis** (the content behind `values_eq_of_digits`; F-14). The statement needs
`ValuesAt`'s bounds `0 ≤ x ≤ 1`: without them it is false (`x = 1` with the free verdict `X.gt 1`
affirmed and any `y > 1` both make every `D(m)` false; `x = 0` and any `y < 0` both make every
`D(m)` true, cell `0` always holding). A world valuing `X` at `x` holds exactly one level-`m`
cell `cellIdx m ≤ 2^m`: existence through the first denied threshold (`firstDenied`,
`holds_cellIdx`), uniqueness because two held cells `j < j'` force `j' = j + 1` and opposite
verdicts on the same threshold sentence `X.gt ((j+1)/2^m)` (`cell_unique`); the cells nest,
`cellIdx (m+1) / 2 = cellIdx m` (`cell_nest`: the shared endpoints are the *same* rational,
hence the same threshold sentence, `thr_succ_double`, and the other endpoint follows by
antitonicity, `thr_anti`); `D_X(m)` holds iff `cellIdx m < 2^m` and `cellIdx m` is even
(`digitSentence_holds_iff_cellIdx`). The out-of-range cell `2^m` is held exactly by a world
affirming `X.gt 1` (then `x = 1`), at every level at once, and every `D_X(m)` fails there. Equal
digit sentences at every level give equal cell sequences by induction on `m`
(`c(m+1) = 2·c(m) + parity`, with the out-of-range case `c(m+1) = 2^{m+1}` forced exactly when
`c(m) = 2^m`), hence `|x − y| ≤ 2^{-m}` for every `m`, hence `x = y`. -/

section CellSequence

open Classical

variable {v : PCWorld} {X : LUV} {x : ℝ}

/-- The level-`m` threshold sentence `X.gt (k/2^m)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def thr (X : LUV) (m k : ℕ) : Sentence := X.gt ((k : ℚ) / 2 ^ m)

/-- A cell in threshold form: `k = 0` or the lower threshold, and not the upper one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_dyadic_iff_thr (v : PCWorld) (X : LUV) (m k : ℕ) :
    v.Holds (dyadicSentence X m k) ↔
      (k = 0 ∨ v.Holds (thr X m k)) ∧ ¬ v.Holds (thr X m (k + 1)) := by
  unfold dyadicSentence thr
  split_ifs with hk
  · subst hk
    rw [PCWorld.holds_neg]
    simp
  · rw [PCWorld.holds_and, PCWorld.holds_neg]
    simp [hk]

/-- Thresholds are antitone in the index (a world valuing `X` at `x` affirms every threshold
below an affirmed one).
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma thr_anti (hv : v.ValuesAt X x) {m k k' : ℕ} (hkk : k ≤ k') (h : v.Holds (thr X m k')) :
    v.Holds (thr X m k) := by
  rcases hkk.lt_or_eq with hlt | rfl
  · unfold thr at h ⊢
    apply ValuesAt.holds_gt hv
    calc (((k : ℚ) / 2 ^ m : ℚ) : ℝ) < (((k' : ℚ) / 2 ^ m : ℚ) : ℝ) := by
          rw [cast_dyadic, cast_dyadic]
          exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hlt)
      _ ≤ x := ValuesAt.le_of_holds_gt hv h
  · exact h

/-- The same rational at the next level: `thr (m+1) (2k) = thr m k` as sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thr_succ_double (X : LUV) (m k : ℕ) : thr X (m + 1) (2 * k) = thr X m k := by
  unfold thr
  congr 1
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  ring

/-- The threshold `(2^m + 1)/2^m > 1 ≥ x` is denied.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma not_thr_top (hv : v.ValuesAt X x) (m : ℕ) : ¬ v.Holds (thr X m (2 ^ m + 1)) := by
  unfold thr
  apply ValuesAt.not_holds_gt hv
  rw [cast_dyadic]
  push_cast
  rw [lt_div_iff₀ (by positivity)]
  have h1 : x * 2 ^ m ≤ 1 * 2 ^ m :=
    mul_le_mul_of_nonneg_right hv.2.1 (by positivity)
  linarith

/-- Some threshold is denied.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_not_thr (hv : v.ValuesAt X x) (m : ℕ) : ∃ k, ¬ v.Holds (thr X m k) :=
  ⟨2 ^ m + 1, not_thr_top hv m⟩

/-- **The first denied threshold** at level `m`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def firstDenied (hv : v.ValuesAt X x) (m : ℕ) : ℕ := Nat.find (exists_not_thr hv m)

/-- **The held cell** at level `m`: one below the first denied threshold (`0` if that is `0`).
Source: none: infrastructure (the cell-sequence proof plan of `values_eq_of_digits`)
Kind: D
Fidelity: n/a -/
noncomputable def cellIdx (hv : v.ValuesAt X x) (m : ℕ) : ℕ := firstDenied hv m - 1

/-- The first denied threshold is denied.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_thr_firstDenied (hv : v.ValuesAt X x) (m : ℕ) :
    ¬ v.Holds (thr X m (firstDenied hv m)) :=
  Nat.find_spec (exists_not_thr hv m)

/-- Thresholds below the first denied one are affirmed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma thr_of_lt_firstDenied (hv : v.ValuesAt X x) {m k : ℕ} (hk : k < firstDenied hv m) :
    v.Holds (thr X m k) := by
  have := Nat.find_min (exists_not_thr hv m) hk
  simpa using this

/-- The first denied threshold is at most `2^m + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma firstDenied_le (hv : v.ValuesAt X x) (m : ℕ) : firstDenied hv m ≤ 2 ^ m + 1 :=
  Nat.find_min' (exists_not_thr hv m) (not_thr_top hv m)

/-- **Existence**: the world holds the cell `cellIdx m` at every level.
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056 (the boundary analysis of F-14)
Kind: P
Fidelity: exact -/
theorem holds_cellIdx (hv : v.ValuesAt X x) (m : ℕ) :
    v.Holds (dyadicSentence X m (cellIdx hv m)) := by
  rw [holds_dyadic_iff_thr]
  unfold cellIdx
  rcases Nat.eq_zero_or_pos (firstDenied hv m) with h0 | hpos
  · refine ⟨Or.inl (by omega), ?_⟩
    intro h1
    apply not_thr_firstDenied hv m
    rw [h0]
    exact thr_anti hv (Nat.zero_le _) h1
  · refine ⟨Or.inr (thr_of_lt_firstDenied hv (by omega)), ?_⟩
    rw [Nat.sub_add_cancel hpos]
    exact not_thr_firstDenied hv m

/-- The held cell's index is at most `2^m` (the out-of-range cell `2^m` is held exactly by a
world affirming `X.gt 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellIdx_le (hv : v.ValuesAt X x) (m : ℕ) : cellIdx hv m ≤ 2 ^ m := by
  unfold cellIdx
  have := firstDenied_le hv m
  have h2 : 0 < 2 ^ m := by positivity
  omega

/-- **Uniqueness**: a world holds at most one cell per level (two held cells `j < j'` force
`j' = j + 1` and opposite verdicts on the threshold `X.gt ((j+1)/2^m)`).
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: exact -/
theorem cell_unique (hv : v.ValuesAt X x) {m j j' : ℕ} (hj : v.Holds (dyadicSentence X m j))
    (hj' : v.Holds (dyadicSentence X m j')) : j = j' := by
  rw [holds_dyadic_iff_thr] at hj hj'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hj'0 : j' ≠ 0 := by omega
    exact hj.2 (thr_anti hv (by omega : j + 1 ≤ j') (hj'.1.resolve_left hj'0))
  · have hj0 : j ≠ 0 := by omega
    exact hj'.2 (thr_anti hv (by omega : j' + 1 ≤ j) (hj.1.resolve_left hj0))

/-- **Nesting**: a held level-`(m+1)` cell `j` lies in the held level-`m` cell `j / 2` (the
shared endpoints are the same rational, hence the same threshold sentence; the others follow by
antitonicity).
Source: PDF 07 p. 3; [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: exact -/
theorem cell_nest (hv : v.ValuesAt X x) {m j : ℕ} (h : v.Holds (dyadicSentence X (m + 1) j)) :
    v.Holds (dyadicSentence X m (j / 2)) := by
  rw [holds_dyadic_iff_thr] at h ⊢
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (j / 2) with h0 | hpos
    · exact Or.inl h0
    · right
      have hj0 : j ≠ 0 := by omega
      rw [← thr_succ_double]
      exact thr_anti hv (Nat.mul_div_le j 2) (h.1.resolve_left hj0)
  · intro hthr
    apply h.2
    rw [← thr_succ_double] at hthr
    exact thr_anti hv (by omega : j + 1 ≤ 2 * (j / 2 + 1)) hthr

/-- The held-cell sequence nests: `cellIdx (m+1) / 2 = cellIdx m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellIdx_succ_div (hv : v.ValuesAt X x) (m : ℕ) : cellIdx hv (m + 1) / 2 = cellIdx hv m :=
  cell_unique hv (cell_nest hv (holds_cellIdx hv (m + 1))) (holds_cellIdx hv m)

/-- **`D_X(m)` reads the held cell**: it holds iff the held cell is in range and even.
Source: PDF 07 p. 3 (`D_X(m)`)
Kind: P
Fidelity: exact -/
theorem digitSentence_holds_iff_cellIdx (hv : v.ValuesAt X x) (m : ℕ) :
    v.Holds (digitSentence X m) ↔ cellIdx hv m < 2 ^ m ∧ cellIdx hv m % 2 = 0 := by
  unfold digitSentence
  rw [holds_sentenceDisjunction]
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨j, ⟨hjlt, hjeven⟩, rfl⟩, hj⟩
    rw [cell_unique hv (holds_cellIdx hv m) hj]
    exact ⟨hjlt, hjeven⟩
  · rintro ⟨hlt, heven⟩
    exact ⟨_, ⟨cellIdx hv m, ⟨hlt, heven⟩, rfl⟩, holds_cellIdx hv m⟩

/-- The value lies in the held cell's closed interval.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellIdx_bounds (hv : v.ValuesAt X x) (m : ℕ) :
    (cellIdx hv m : ℝ) / 2 ^ m ≤ x ∧ x ≤ ((cellIdx hv m : ℝ) + 1) / 2 ^ m := by
  have h := holds_cellIdx hv m
  rcases Nat.eq_zero_or_pos (cellIdx hv m) with h0 | hpos
  · rw [h0] at h ⊢
    refine ⟨by simpa using hv.1, ?_⟩
    have := le_of_holds_dyadic_zero hv h
    rw [cast_dyadic_one] at this
    simpa using this
  · have := mem_Icc_of_holds_dyadic hv hpos h
    rw [cast_dyadic, cast_dyadic_succ] at this
    exact this

/-- **`values_eq_of_digits`** (6): Soto's rewrite of `X = Y` as `∀m (D_X(m) ↔ D_Y(m))` is sound —
if a world values `X` at `x` and `Y` at `y` and holds `D_X(m) ↔ D_Y(m)` for every `m`, then
`x = y`. Proof: the held-cell sequences agree by induction on the level (`c(m+1) = 2·c(m) +
parity`, the parity read off `D(m+1)` when the cell is in range, and the out-of-range cell
`2^{m+1}` forced exactly when `c(m) = 2^m`), so `x` and `y` lie in the same closed cell of width
`2^{-m}` at every level. The bounds `0 ≤ x, y ≤ 1` of `ValuesAt` are used (without them the
statement is false: `x = 1` with `X.gt 1` affirmed and any `y > 1` make every `D` false).
Source: PDF 07 p. 3 ("we rewrite `X = Y` as `∀m(D_X(m) ↔ D_Y(m))`"); [[bli-soto-a-inventory]] 056
Kind: P
Fidelity: exact (the source's rewrite, soundness direction; boundary conventions are the
world's free verdicts, which the rewrite tolerates)
Hyps: (a) `ValuesAt` for `X` at `x` and for `Y` at `y`; (a) the digit equivalences at every level -/
theorem values_eq_of_digits {Y : LUV} {y : ℝ} (hx : v.ValuesAt X x) (hy : v.ValuesAt Y y)
    (h : ∀ m, v.Holds (digitSentence X m) ↔ v.Holds (digitSentence Y m)) : x = y := by
  have hD : ∀ m, (cellIdx hx m < 2 ^ m ∧ cellIdx hx m % 2 = 0) ↔
      (cellIdx hy m < 2 ^ m ∧ cellIdx hy m % 2 = 0) := by
    intro m
    rw [← digitSentence_holds_iff_cellIdx hx m, ← digitSentence_holds_iff_cellIdx hy m]
    exact h m
  have hc : ∀ m, cellIdx hx m = cellIdx hy m := by
    intro m
    induction m with
    | zero =>
        have hx0 := cellIdx_le hx 0
        have hy0 := cellIdx_le hy 0
        have hD0 := hD 0
        simp only [pow_zero] at hx0 hy0 hD0
        omega
    | succ m ih =>
        have hxle := cellIdx_le hx (m + 1)
        have hyle := cellIdx_le hy (m + 1)
        have hxd := cellIdx_succ_div hx m
        have hyd := cellIdx_succ_div hy m
        have hD' := hD (m + 1)
        have hxm := Nat.div_add_mod (cellIdx hx (m + 1)) 2
        have hym := Nat.div_add_mod (cellIdx hy (m + 1)) 2
        rw [pow_succ] at hxle hyle hD'
        rw [ih] at hxd
        generalize cellIdx hx (m + 1) = cx at hxle hxd hD' hxm ⊢
        generalize cellIdx hy (m + 1) = cy at hyle hyd hD' hym ⊢
        generalize cellIdx hy m = c at hxd hyd
        generalize 2 ^ m = P at hxle hyle hD'
        omega
  have hbound : ∀ m : ℕ, |x - y| ≤ 1 / 2 ^ m := by
    intro m
    obtain ⟨hx1, hx2⟩ := cellIdx_bounds hx m
    obtain ⟨hy1, hy2⟩ := cellIdx_bounds hy m
    rw [hc m] at hx1 hx2
    have e1 : (cellIdx hy m : ℝ) / 2 ^ m - ((cellIdx hy m : ℝ) + 1) / 2 ^ m = -(1 / 2 ^ m) := by
      ring
    have e2 : ((cellIdx hy m : ℝ) + 1) / 2 ^ m - (cellIdx hy m : ℝ) / 2 ^ m = 1 / 2 ^ m := by
      ring
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
  rw [one_div_pow] at hn
  linarith [hbound n]

end CellSequence

/-! ## The converse of `values_eq_of_digits` fails on the grid (F-14; audit r2 fidelity N3)

`values_eq_of_digits` is the soundness direction of Soto's rewrite of `X = Y` as
`∀m (D_X(m) ↔ D_Y(m))`. The converse is false over FAF's worlds: `ValuesAt v X x` leaves the
verdict on the threshold `X.gt x` free, so two LUVs valued at the same dyadic rational `½` can
disagree on the level-`1` cell `[0, ½]` — one world denies `X.gt ½` and affirms `Y.gt ½`, holding
`D_X(1)` and not `D_Y(1)`. Over threshold worlds the rewrite is therefore *strictly stronger* than
`X = Y` (it also asserts agreement of the two free verdicts on every dyadic threshold). -/

/-- The threshold LUV valued at `½` whose verdict at the threshold `½` itself is the atom `a`:
`⊤` below `½`, `∼⊤` above, `atom a` at `½`.
Source: audit r2 fidelity N3; FAF `PCWorld.ValuesAt`
Kind: D
Fidelity: n/a -/
def halfLUV (a : ℕ) : LUV where
  gt r := if r < 1 / 2 then ⊤ else if 1 / 2 < r then ∼(⊤ : Sentence) else Formula.atom a

/-- Every world values `halfLUV a` at `½`, whatever its verdict on `a`.
Source: FAF `PCWorld.ValuesAt`
Kind: L
Fidelity: n/a -/
lemma halfLUV_valuesAt (v : PCWorld) (a : ℕ) : v.ValuesAt (halfLUV a) ((1 / 2 : ℚ) : ℝ) := by
  refine ⟨by norm_num, by norm_num, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have h : r < 1 / 2 := Rat.cast_lt.mp hr
    simp only [halfLUV]
    rw [if_pos h]
    exact PCWorld.holds_top v
  · have h2 : (1 / 2 : ℚ) < r := Rat.cast_lt.mp hr
    have h1 : ¬ r < 1 / 2 := not_lt.mpr h2.le
    simp only [halfLUV]
    rw [if_neg h1, if_pos h2, PCWorld.holds_neg]
    exact fun h => h (PCWorld.holds_top v)

/-- **The converse of `values_eq_of_digits` fails on the grid** (F-14, sharp form): one world
values two LUVs at the same `x = ½` and holds Soto's `D_X(1)` for one but not for the other. The
world `v a := (a = 1)` denies `halfLUV 0`'s verdict atom `0` and affirms `halfLUV 1`'s atom `1`,
i.e. denies `X.gt ½` (holding the cell `[0, ½]`, so `D_X(1)`) and affirms `Y.gt ½` (holding the
cell `(½, 1]`, so not `D_Y(1)`), although both are valued at `½`.
Source: PDF 07 p. 3 (the rewrite of `X = Y`); audit r2 fidelity N3
Kind: N+
Fidelity: n/a (a counterexample to the converse direction)
Hyps: (a) none -/
theorem not_digits_of_values_eq :
    ∃ (v : PCWorld) (X Y : LUV) (x : ℝ), v.ValuesAt X x ∧ v.ValuesAt Y x ∧
      v.Holds (digitSentence X 1) ∧ ¬ v.Holds (digitSentence Y 1) := by
  refine ⟨fun a => a = 1, halfLUV 0, halfLUV 1, ((1 / 2 : ℚ) : ℝ), halfLUV_valuesAt _ 0,
    halfLUV_valuesAt _ 1, ?_, ?_⟩
  · unfold digitSentence
    rw [holds_sentenceDisjunction]
    refine ⟨dyadicSentence (halfLUV 0) 1 0, List.mem_map.mpr ⟨0, by decide, rfl⟩, ?_⟩
    norm_num [dyadicSentence, halfLUV]
  · unfold digitSentence
    rw [holds_sentenceDisjunction]
    rintro ⟨φ, hφ, hv⟩
    rw [List.mem_map] at hφ
    obtain ⟨k, hk, rfl⟩ := hφ
    rw [List.mem_filter, List.mem_range] at hk
    simp only [decide_eq_true_eq] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [dyadicSentence, halfLUV] at hv

end Cleanroom.Bli.BliExtrapolation
