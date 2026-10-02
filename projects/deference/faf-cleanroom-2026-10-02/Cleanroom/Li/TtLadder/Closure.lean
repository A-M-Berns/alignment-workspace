import Cleanroom.Li.TtLadder.Arrows

/-!
# `tt-ladder`: full closure and δ-independence

Target 3 of [[tt-ladder-mandate]]. At the theorem's own quantification (every rational `t` and
`ε`), the whole family of "bounded ε-violation" readings collapses, *at each fixed width*
`δ > 0`, to one statement: `Dominates e a` (`li-asymp-calc`: `∀ c > 0, ∀ᶠ n, a n − c < e n`),
which for `[0,1]`-valued streams is `0 ≤ liminf (e − a)`. The compactness direction is
re-proved here at *fixed* `δ` — `li-asymp-calc`'s `dominates_of_tendsto_viol` instantiates
`δ := ε` and so cannot be cited for it. Over real sequences; not a theorem about inductors.

Squeeze discipline: the left sides below are the `Summable (viol …)` family and the `LCondSeq`
family *literally*; `Dominates` is never unfolded on both sides.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## The easy direction and the shared extraction -/

/-- `Dominates e a ⇒ T_full(δ)` for every width: `li-asymp-calc`'s `Dominates.summable_viol`,
instance-wise (no bounds needed).
Source: lean-deference-2-004 (ii); [[fa-positive-results-corrected-v3]] §5 Cor 3
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_of_dominates {a e : ℕ → ℝ} {δ : ℚ} (hδ : 0 < δ) (h : Dominates e a) :
    TFullSeq a e δ :=
  fun t _ hε => h.summable_viol t hε hδ

/-- The compactness extraction shared by both closure theorems: if `e` does not dominate `a`
and `a` is `[0,1]`-valued, there are `c > 0`, a limit `q`, and a strictly increasing `φ` with
`e (φ k) ≤ a (φ k) − c` for every `k` and `a ∘ φ → q`.
Source: none: infrastructure (lean-deference-2-004 (i), the subsequence step)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem exists_subseq_of_not_dominates {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (h : ¬ Dominates e a) :
    ∃ c : ℝ, 0 < c ∧ ∃ q : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k, e (φ k) ≤ a (φ k) - c) ∧ Tendsto (fun k => a (φ k)) atTop (𝓝 q) := by
  have hfreq : ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, e n ≤ a n - c := by
    by_contra hne
    apply h
    intro c hc
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    exact hne ⟨c, hc, hcon.mono (fun n hn => not_lt.1 hn)⟩
  obtain ⟨c, hc, hcon⟩ := hfreq
  obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨q, _, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq (fun k => ha (φ k))
  exact ⟨c, hc, q, φ ∘ ψ, hφ.comp hψ, fun k => hφv (ψ k), hlim⟩

/-! ## (i) `T_full(δ) ⇒ Dominates`, at fixed `δ` -/

/-- **Compactness at fixed width** (Prop B, `⟹`): if every rational-`(t, ε)` violation weight
at the *fixed* width `δ > 0` is summable and `a` is `[0,1]`-valued, then `e` dominates `a`.
Proof: otherwise `e ≤ a − c` along a subsequence with `a → q`; rational `t ∈ (q − c/2, q − c/4)`
and `ε ∈ (c/16, c/8)`; on a tail `a − t > 3c/16` and `(t − ε) − e > 5c/16`, so the weight is
`≥ min 1 (3c/(16δ)) · min 1 (5c/(16δ)) > 0` there and cannot tend to `0`. Bookkeeping: the
chat's `ε ≤ 3c/16` and lean-deference-044's `ε, δ ≤ c/8` are both replaced by `ε ∈ (c/16, c/8)`
with `δ` free. The bound `a ∈ [0,1]` is load-bearing: `a n = n`, `e n = n − 1` satisfy `T_full`
at every width and fail dominance (`closure_needs_quote_bound`, `Bounds.lean`). Over real
sequences; not a theorem about inductors.
Source: lean-deference-2-004 (i); lean-deference-044 (Cor 2's proof); root-fa-014
Kind: P
Fidelity: variant: sequence-level; stronger: at one fixed `δ` (the source quantifies over `δ` too)
Hyps: (a) none -/
theorem dominates_of_tFullSeq {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) (h : TFullSeq a e δ) : Dominates e a := by
  by_contra hnd
  obtain ⟨c, hc, q, φ, hφ, hφv, hlim⟩ := exists_subseq_of_not_dominates ha hnd
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show q - c / 2 < q - c / 4 by linarith)
  obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn (show c / 16 < c / 8 by linarith)
  have hεpos : 0 < ε := by
    have : (0 : ℝ) < ε := by linarith
    exact_mod_cast this
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hnear1 := hlim.eventually (gt_mem_nhds (show q < q + c / 16 by linarith))
  have hnear2 := hlim.eventually (lt_mem_nhds (show q - c / 16 < q by linarith))
  have hmpos : 0 < min 1 ((3 * c / 16) / δ) * min 1 ((5 * c / 16) / δ) :=
    mul_pos (lt_min one_pos (div_pos (by linarith) hδR))
      (lt_min one_pos (div_pos (by linarith) hδR))
  have hviol := (h t ε hεpos).tendsto_atTop_zero.comp hφ.tendsto_atTop
  have hsmall := hviol.eventually (gt_mem_nhds hmpos)
  obtain ⟨k, hk1, hk2, hk3⟩ := (hsmall.and (hnear1.and hnear2)).exists
  simp only [Function.comp] at hk1
  have hv := hφv k
  have hge : min 1 ((3 * c / 16) / δ) * min 1 ((5 * c / 16) / δ) ≤ viol e a t ε δ (φ k) := by
    rw [viol_eq_gateSeq_mul]
    refine mul_le_mul ?_ ?_ ?_ (gateSeq_nonneg _ _ _ _)
    · exact min_one_div_le_ctsInd hδ (by linarith)
    · exact min_one_div_le_ctsInd hδ (by linarith)
    · exact le_min zero_le_one (div_nonneg (by linarith) hδR.le)
  linarith

/-- **Prop B at fixed width**: `T_full(δ) ⟺ Dominates e a` for `[0,1]`-valued `a` and every
fixed `δ > 0`. The left side is the `Summable (viol …)` family literally. Over real sequences;
not a theorem about inductors.
Source: lean-deference-2-004 (i)+(ii); lean-deference-046 Prop B; root-fa-014
Kind: P
Fidelity: variant: sequence-level; stronger: at one fixed `δ`
Hyps: (a) none -/
theorem tFullSeq_iff_dominates {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) : TFullSeq a e δ ↔ Dominates e a :=
  ⟨dominates_of_tFullSeq ha hδ, tFullSeq_of_dominates hδ⟩

/-! ## (iii) `∀ t · L_cond(t) ⟺ Dominates` -/

/-- `Dominates e a ⇒ L_cond(t)` for every rational `t` (one line: on a gate-touched day
`t − c < a n − c < e n`).
Source: lean-deference-2-004 (iii), easy half
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lCondSeq_of_dominates {a e : ℕ → ℝ} (h : Dominates e a) (t : ℚ) : LCondSeq a e t := by
  intro c hc
  filter_upwards [h c hc] with n hn hg
  linarith

/-- `(∀ t, L_cond(t)) ⇒ Dominates e a` for `[0,1]`-valued `a`: the same compactness with
`t ∈ (q − 5c/8, q − c/8)` and the margin `c/4`. The bound `a ∈ [0,1]` is load-bearing:
`a n = n`, `e n = n − 1` satisfy `L_cond(t)` at every threshold and fail dominance
(`closure_needs_quote_bound`, `Bounds.lean`).
Source: lean-deference-2-004 (iii)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem dominates_of_lCondSeq_all {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ t : ℚ, LCondSeq a e t) : Dominates e a := by
  by_contra hnd
  obtain ⟨c, hc, q, φ, hφ, hφv, hlim⟩ := exists_subseq_of_not_dominates ha hnd
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show q - 5 * c / 8 < q - c / 8 by linarith)
  have hnear1 := hlim.eventually (gt_mem_nhds (show q < q + c / 16 by linarith))
  have hnear2 := hlim.eventually (lt_mem_nhds (show q - c / 16 < q by linarith))
  have hcond := hφ.tendsto_atTop.eventually (h t (c / 4) (by linarith))
  obtain ⟨k, hk1, hk2, hk3⟩ := (hcond.and (hnear1.and hnear2)).exists
  have hv := hφv k
  have hg : (t : ℝ) < a (φ k) := by linarith
  have := hk1 hg
  linarith

/-- **The conditional-limit closure**: `(∀ t, L_cond(t)) ⟺ Dominates e a` for `[0,1]`-valued
`a`. With `tFullSeq_iff_dominates` this is the equivalence the note's line 171 denies: at every
threshold, the per-day conditional limit *is* the theorem family. Over real sequences; not a
theorem about inductors.
Source: lean-deference-2-004 (iii); [[faithful-acceleration]] l.171 (refuted reading)
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lCondSeq_all_iff_dominates {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) :
    (∀ t : ℚ, LCondSeq a e t) ↔ Dominates e a :=
  ⟨dominates_of_lCondSeq_all ha, lCondSeq_of_dominates⟩

/-- `T_full(δ) ⟺ ∀ t · L_cond(t)` for `[0,1]`-valued `a`, `δ > 0`: the two full closures are
the same statement.
Source: lean-deference-2-004
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_iff_lCondSeq_all {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) : TFullSeq a e δ ↔ ∀ t : ℚ, LCondSeq a e t :=
  (tFullSeq_iff_dominates ha hδ).trans (lCondSeq_all_iff_dominates ha).symm

/-- **The fixed-`t` artifact, resolved side**: `T_full(δ) ⇒ L_cond(t₀)` at every fixed `t₀`
(for `[0,1]`-valued `a`). Its companion — `T_∀ε(t₀) ∧ ¬L_cond(t₀) ∧ ¬T_full` is satisfiable — is
`tAllEpsSeq_not_lCondSeq_not_tFullSeq` (`Witnesses.lean`, W2): the escape exists at a fixed
threshold and closes under the theorem's `∀ t`.
Source: lean-deference-2-005; lean-deference-2-004
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem lCondSeq_of_tFullSeq {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) (h : TFullSeq a e δ) (t₀ : ℚ) : LCondSeq a e t₀ :=
  lCondSeq_of_dominates (dominates_of_tFullSeq ha hδ h) t₀

/-- At the closure, every weight is eventually `0`: for `[0,1]`-valued `a`, `T_full(δ)` makes
`viol e a t ε δ` vanish eventually at every threshold and margin (through
`dominates_of_tFullSeq` and `li-asymp-calc`'s `Dominates.viol_eventually_zero`).
Source: [[tt-ladder-audit-r1-adversarial]] N-b (probe A2); lean-deference-2-004
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_eventually_zero {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) (h : TFullSeq a e δ) (t : ℚ) {ε : ℚ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, viol e a t ε δ n = 0 :=
  (dominates_of_tFullSeq ha hδ h).viol_eventually_zero t hε hδ

/-- **At the closure, "summable" is "eventually zero"**: for `[0,1]`-valued `a`, `T_full(δ)` is
equivalent to the finiteness of every violation set `{n ∣ viol e a t ε δ n ≠ 0}`. So the
"stronger: every weight eventually `0`" of the `L_cond ⇒ T_∀ε` row is stronger only at a fixed
`t`; at the theorem family's own quantification the summability formulation carries no content
beyond finiteness, and the residue above `T_full` (W7) is the residue of the margin-free `BV`.
Source: [[tt-ladder-audit-r1-adversarial]] N-b (probe A2); lean-deference-2-004
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_iff_eventually_zero {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ}
    (hδ : 0 < δ) :
    TFullSeq a e δ ↔ ∀ t ε : ℚ, 0 < ε → ∀ᶠ n in atTop, viol e a t ε δ n = 0 :=
  ⟨fun h t ε hε => tFullSeq_eventually_zero ha hδ h t hε, fun h t ε hε => by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h t ε hε)
    exact summable_of_ne_finset_zero (s := Finset.range N)
      (fun n hn => hN n (not_lt.1 (fun h' => hn (Finset.mem_range.2 h'))))⟩

/-! ## (iv) `∀ t · BV ⇒ T_full` -/

/-- `(∀ t, BV(t,δ)) ⇒ T_full(δ)`, instance-wise through `BV ⇒ T_∀ε`. Strict: W7
(`WitnessesLog.lean`, `tFullSeq_not_bvSeq`) satisfies `T_full` and fails `BV(½)`.
Source: lean-deference-2-004 (iv)
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_of_bvSeq_all {a e : ℕ → ℝ} {δ : ℚ} (hδ : 0 < δ) (h : ∀ t : ℚ, BVSeq a e t δ) :
    TFullSeq a e δ :=
  fun t ε hε => tAllEpsSeq_of_bvSeq hδ (h t) ε hε

/-! ## (v) δ-independence and the bridges -/

/-- **δ-independence**: for `[0,1]`-valued `a`, `T_full(δ) ⟺ T_full(δ')` for any two positive
widths — the closure does not depend on the ramp width (both are `Dominates e a`). Kind `L`: it
is `.trans` of two instances of `tFullSeq_iff_dominates`; the content is `dominates_of_tFullSeq`.
Source: lean-deference-2-004 (v)
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_iff_tFullSeq {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) {δ δ' : ℚ}
    (hδ : 0 < δ) (hδ' : 0 < δ') : TFullSeq a e δ ↔ TFullSeq a e δ' :=
  (tFullSeq_iff_dominates ha hδ).trans (tFullSeq_iff_dominates ha hδ').symm

/-- Bridge to `li-asymp-calc`'s all-`δ` packaging: `(∀ δ > 0, T_full(δ)) ⟺ Dominates e a`
(`summable_viol_iff_dominates` with its quantifiers regrouped).
Source: lean-deference-2-004 (v); [[fa-positive-results-corrected-v3]] §5
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_all_iff_dominates {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) :
    (∀ δ : ℚ, 0 < δ → TFullSeq a e δ) ↔ Dominates e a :=
  ⟨fun h => (summable_viol_iff_dominates ha).1 (fun t ε δ hε hδ => h δ hδ t ε hε),
    fun h δ hδ t ε hε => (summable_viol_iff_dominates ha).2 h t ε δ hε hδ⟩

/-- Bridge to the `liminf` form: for `[0,1]`-valued `a` and `e` and `δ > 0`,
`T_full(δ) ⟺ 0 ≤ liminf (e − a)` (`li-asymp-calc`'s `dominates_iff_liminf`).
Source: lean-deference-2-004; [[fa-positive-results-corrected-v2]] §5.5
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem tFullSeq_iff_liminf {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1) {δ : ℚ} (hδ : 0 < δ) :
    TFullSeq a e δ ↔ 0 ≤ liminf (fun n => e n - a n) atTop :=
  (tFullSeq_iff_dominates ha hδ).trans (dominates_iff_liminf ha he)

/-! ## Schedule form -/

/-- **Cor 2 along a schedule** (root-fa-2-005): for any `d : ℕ → ℕ` (no monotonicity needed),
`T_full(δ)` of the reindexed pair `(a ∘ d, e ∘ d)` is dominance along `d` — an instance of
`tFullSeq_iff_dominates`.
Source: root-fa-2-005 (Cor 2 along `d`); `li-asymp-calc` `tendsto_viol_iff_dominates_along`
Kind: L
Fidelity: variant: sequence-level; stronger: `d` need not be strictly increasing
Hyps: (a) none -/
theorem tFullSeq_comp_iff_dominates_comp {a e : ℕ → ℝ} (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℚ} (hδ : 0 < δ) (d : ℕ → ℕ) :
    TFullSeq (a ∘ d) (e ∘ d) δ ↔ Dominates (e ∘ d) (a ∘ d) :=
  tFullSeq_iff_dominates (fun k => ha (d k)) hδ

end Cleanroom.Li.TtLadder
