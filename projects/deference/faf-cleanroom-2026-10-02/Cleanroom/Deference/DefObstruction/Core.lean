import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Li.LiDiagonal.Scope

/-!
# `def-obstruction` · Core: Lemma 2.1 and 2.1′ (T1)

The arithmetic core of obstruction 2a: the anti-inductive response `ρ(a) := 𝟙[a ≤ ½]` is at
distance at least `½` from every real `a`, with equality exactly at `a = ½`. Everything else in
the package is bookkeeping that installs `ρ` as the settlement of a sentence the reader's process
decides.

Three things to know about the statements here, against the source
([[self-referential-settlement-target]] §2.1):

* **No range hypothesis.** The source states Lemma 2.1 for `a ∈ [0,1]`; the bound `½ ≤ |a − ρ(a)|`
  holds for *every* real `a` (`defect_ge_half`), because `|a − ρ(a)| = max a (1 − a)`
  (`defect_eq_max`). The `[0,1]` form is the `IsGLB` statement `defect_isGLB`, where the range is
  the domain of the infimum. The rounding-robust form 2.1′ does use `a ∈ [0,1]`.
* **The `<` twin is proved, not asserted.** `rhoStrict a := 𝟙[a < ½]` has the same defect
  `max a (1 − a)` (`defect_strict_eq_max`); the two conventions differ only at `a = ½`, where
  both defects equal `½` (`defect_half`, `defect_strict_half`). The source's "the convention is
  irrelevant" is this pair of lemmas.
* **The bridge to `li-diagonal`.** `side a n = ρ(a n)` (`side_eq_rho`) and `invSide a n = ρ(a n)`
  (`invSide_eq_rho`, definitional), so T2 composes with `lemmaB` without a change of carrier.

Scope: single real number; no market. Source items: anson-001, root-deference-025,
lean-deference-012.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The anti-inductive response -/

/-- **The anti-inductive response** `ρ(a) := 𝟙[a ≤ ½]` of [[self-referential-settlement-target]]
§2.1 (Lemma 2.1), on all of `ℝ`. Ties at `½` give `1` — the ledger's polarity (`li-quote-lane`
disclosure (β)), which is what makes `side a n = ρ(a n)` (`side_eq_rho`) hold on the nose.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 (anson-001); [[no-timely-pointwise-tower]] §3
Kind: D
Fidelity: exact (the source's `ρ`, extended from `[0,1]` to `ℝ`)
Hyps: n/a -/
noncomputable def rho (a : ℝ) : ℝ := if a ≤ 1 / 2 then 1 else 0

/-- **The strict-convention twin** `𝟙[a < ½]`, the source's "the convention is irrelevant"
alternative. It differs from `rho` only at `a = ½` (`rho_eq_rhoStrict_of_ne`).
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 (the remark after Lemma 2.1)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def rhoStrict (a : ℝ) : ℝ := if a < 1 / 2 then 1 else 0

/-- `rho_eq_one_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rho_eq_one_iff (a : ℝ) : rho a = 1 ↔ a ≤ 1 / 2 := by
  unfold rho
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun h1 => absurd h1 h⟩

/-- `rho_eq_zero_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rho_eq_zero_iff (a : ℝ) : rho a = 0 ↔ 1 / 2 < a := by
  unfold rho
  split_ifs with h
  · exact ⟨fun h1 => absurd h1 one_ne_zero, fun hlt => absurd h (not_le.mpr hlt)⟩
  · exact ⟨fun _ => not_le.mp h, fun _ => rfl⟩

/-- `rho` takes values in `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rho_eq_zero_or_one (a : ℝ) : rho a = 0 ∨ rho a = 1 := by
  unfold rho; split_ifs <;> simp

/-- `rho` and `rhoStrict` agree off the tie `a = ½`.
Source: [[self-referential-settlement-target]] §2.1 ("the convention is irrelevant")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem rho_eq_rhoStrict_of_ne (a : ℝ) (h : a ≠ 1 / 2) : rho a = rhoStrict a := by
  unfold rho rhoStrict
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_pos hlt.le, if_pos hlt]
  · rw [if_neg (not_le.mpr hgt), if_neg (not_lt.mpr hgt.le)]

/-! ## B. The bridge to `li-diagonal`'s `side` and `invSide` -/

/-- **`li-diagonal`'s `side` is `ρ` of the published number**: `side a n = ρ(a n)` for every
rational table (the ledger's `≤` polarity is `ρ`'s).
Scope: one-way (a property of the published table).
Source: [[li-diagonal-mandate]] § Definitions of record (`side`); mandate T1 ("state over `side`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem side_eq_rho (a : ℕ → ℚ) (n : ℕ) : side a n = rho (a n) := by
  unfold side rho
  have hcast : ((a n : ℝ) ≤ 1 / 2) ↔ (a n ≤ 1 / 2) := by
    rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_le
  by_cases h : a n ≤ 1 / 2
  · rw [if_pos h, if_pos (hcast.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hcast.mp h'))]

/-- **`li-diagonal`'s `invSide` is `ρ` pointwise** (definitionally).
Scope: real sequences.
Source: [[li-diagonal-mandate]] T7 (`invSide`); mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem invSide_eq_rho (a : ℕ → ℝ) (n : ℕ) : invSide a n = rho (a n) := rfl

/-! ## C. Lemma 2.1 -/

/-- **The defect of the anti-inductive response is `max a (1 − a)`**, for every real `a`. This is
the one-line identity behind Lemma 2.1 and behind T6 (the defect is a *continuous* function of
the quote even though `ρ` is not).
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 (proof of Lemma 2.1, both cases)
Kind: P
Fidelity: stronger: an identity on all of `ℝ` in place of the source's bound on `[0,1]`
Hyps: (a) none -/
theorem defect_eq_max (a : ℝ) : |a - rho a| = max a (1 - a) := by
  unfold rho
  split_ifs with h
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
    ring
  · rw [not_le] at h
    rw [sub_zero, abs_of_pos (by linarith), max_eq_left (by linarith)]

/-- **Lemma 2.1 (no exact quote).** `½ ≤ |a − ρ(a)|` for **every** real `a` — no quote is within
`½` of the anti-inductive response to it. The source states it on `[0,1]`; the range is not
needed.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 Lemma 2.1 (anson-001); [[no-timely-pointwise-tower]] §3; [[deference-in-logical-induction-v6]] §4.3 line 453
Kind: P
Fidelity: stronger: all of `ℝ` in place of `[0,1]`
Hyps: (a) none -/
theorem defect_ge_half (a : ℝ) : 1 / 2 ≤ |a - rho a| := by
  rw [defect_eq_max]
  rcases le_or_gt a (1 / 2) with h | h
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h.le

/-- **Lemma 2.1, equality case.** The defect is exactly `½` iff `a = ½`.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 Lemma 2.1 ("attained only at `a = ½`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem defect_eq_half_iff (a : ℝ) : |a - rho a| = 1 / 2 ↔ a = 1 / 2 := by
  rw [defect_eq_max]
  constructor
  · intro h
    rcases le_total a (1 / 2) with h1 | h1
    · rw [max_eq_right (by linarith)] at h; linarith
    · rw [max_eq_left (by linarith)] at h; linarith
  · rintro rfl; norm_num

/-- The defect at the tie: `|½ − ρ(½)| = ½` (`ρ(½) = 1`).
Source: [[self-referential-settlement-target]] §2.3 ("`ρ(½) = 1 ≠ ½`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem defect_half : |(1 / 2 : ℝ) - rho (1 / 2)| = 1 / 2 := (defect_eq_half_iff _).2 rfl

/-- **Lemma 2.1 as an infimum**: `½` is the greatest lower bound of `{|a − ρ(a)| : a ∈ [0,1]}`
(attained at `a = ½`).
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 Lemma 2.1 (`inf_{a∈[0,1]} |a − ρ(a)| = ½`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem defect_isGLB : IsGLB ((fun a : ℝ => |a - rho a|) '' Set.Icc (0 : ℝ) 1) (1 / 2) := by
  constructor
  · rintro _ ⟨a, -, rfl⟩
    exact defect_ge_half a
  · intro b hb
    have h : b ≤ |(1 / 2 : ℝ) - rho (1 / 2)| := hb ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    rwa [defect_half] at h

/-- **Lemma 2.1′ (rounding-robust).** For `a ∈ [0,1]` and any real `r` (the recorded, possibly
rounded, quote), `½ − |r − a| ≤ |a − ρ(r)|`. Specialises to Lemma 2.1 at `r = a`. Over this run's
exact ledger (no rounding) only the `r = a` case is used; the lemma is kept for fidelity to the
source's `1/2n` grid.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 Lemma 2.1′ (`residual_lb`); anson-001
Kind: P
Fidelity: exact
Hyps: (a) none (`0 ≤ a ≤ 1` is the statement's own range) -/
theorem rounding_robust (a r : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    1 / 2 - |r - a| ≤ |a - rho r| := by
  unfold rho
  split_ifs with h
  · rw [abs_of_nonpos (show a - 1 ≤ 0 by linarith)]
    have h2 : a - r ≤ |r - a| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · rw [not_le] at h
    rw [sub_zero, abs_of_nonneg h0]
    have h2 : r - a ≤ |r - a| := le_abs_self _
    linarith

/-! ## D. The `<`-convention twin -/

/-- The strict twin has the same defect identity.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 (the convention remark)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem defect_strict_eq_max (a : ℝ) : |a - rhoStrict a| = max a (1 - a) := by
  unfold rhoStrict
  split_ifs with h
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
    ring
  · rw [not_lt] at h
    rw [sub_zero, abs_of_nonneg (by linarith), max_eq_left (by linarith)]

/-- **Lemma 2.1 in the `<` convention**: `½ ≤ |a − 𝟙[a < ½]|` for every real `a`.
Scope: single real.
Source: [[self-referential-settlement-target]] §2.1 (`no_exact_quote'`)
Kind: P
Fidelity: stronger: all of `ℝ`
Hyps: (a) none -/
theorem defect_strict_ge_half (a : ℝ) : 1 / 2 ≤ |a - rhoStrict a| := by
  rw [defect_strict_eq_max]
  rcases le_or_gt a (1 / 2) with h | h
  · exact le_max_of_le_right (by linarith)
  · exact le_max_of_le_left h.le

/-- The strict twin's defect at the tie: `|½ − 𝟙[½ < ½]| = ½` (now approached from below).
Source: [[self-referential-settlement-target]] §2.1 ("equality again `½`, now approached from below")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem defect_strict_half : |(1 / 2 : ℝ) - rhoStrict (1 / 2)| = 1 / 2 := by
  rw [defect_strict_eq_max]; norm_num

end Cleanroom.Deference.DefObstruction
