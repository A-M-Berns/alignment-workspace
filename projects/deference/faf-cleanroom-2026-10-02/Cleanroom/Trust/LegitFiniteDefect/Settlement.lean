import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Bounds.Basic

/-!
# Settlement continuity

Package `legit-finite-defect`, Target 11 (item 2-043). A self-referential settlement is a map
`s : ℝ → ℝ` sending `[0, 1]` into itself: the target the quote `a` must match is `s a`. The
pointwise **settlement gap** is `settleGap s a = |s a − a|` (not "defect": Target 1's word is
reserved for the weighted object).

* **Fixed point** (`exists_fixedPoint`): a continuous settlement has a quote with zero gap (IVT
  on `s a − a`), so a best-responding quoter achieves zero pointwise gap; contrapositively, a
  settlement with no fixed point is discontinuous (`not_continuousOn_of_no_fixedPoint`).
* **Computed infimum for the anti-indicator family** (`isGLB_settleGap_antiIndAt`): for
  `antiIndAt c a = 𝟙[a ≤ c]` and `c ∈ [0, 1]`, the greatest lower bound of the gap over `[0, 1]`
  is `min c (1 − c)`; at `c = 1/2` this re-proves lean-deference's `no_exact_quote` +
  `residual_half` (`research/lean-deference/SelfReferentialTarget.lean`; cited, grade (a)
  re-proof) as an instance.
* **Witnesses**: the affine flip `s a = 1 − a` (non-constant, continuous, self-mapping) has the
  unique fixed point `1/2` — the N+ witness of `exists_fixedPoint`, whose mechanism (IVT on
  `s a − a`, which changes sign from `+1` to `−1`) it exercises; the source's constant `s ≡ 1/2`
  is kept as an N− instance (a constant map's fixed point needs no continuity: audit round 1);
  `antiIndAt (1/2)` has gap `≥ 1/2` everywhere, attained at `1/2`, and no fixed point, hence is
  discontinuous.

**Trap, flagged and not shipped**: the scout's "(ii) if `inf |s(a) − a| ≥ J` then every quote has
gap `≥ J`" is the definition of an infimum, not a theorem. The interpretation "feedback is
legitimate iff the settlement responds continuously to the AI's output" is
ATTRIBUTION-UNVETTED and stays here in prose: the theorems are about fixed points and gaps of
real functions on `[0, 1]`.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.Settlement

open Set

noncomputable section

/-- The **settlement gap** of a quote `a` under the settlement `s`: `|s a − a|`.
Source: `run3/questions/scout-acceleration.md` Q6 (`legitimacy-continuity`); trust-lab-2-043
Kind: D
Fidelity: exact -/
def settleGap (s : ℝ → ℝ) (a : ℝ) : ℝ := |s a - a|

/-- Zero gap is a fixed point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem settleGap_eq_zero_iff (s : ℝ → ℝ) (a : ℝ) : settleGap s a = 0 ↔ s a = a := by
  unfold settleGap
  rw [abs_eq_zero, sub_eq_zero]

/-- **Fixed point.** A settlement continuous on `[0, 1]` and mapping `[0, 1]` into itself has a
quote `a ∈ [0, 1]` with `s a = a` — zero settlement gap. Intermediate value theorem on `s a − a`.
Source: trust-lab-2-043 (i) ("legitimate ⇒ calibratable"); `scout-acceleration.md` Q6 (i)
Kind: P
Fidelity: exact
Hyps: (a) continuity on `[0, 1]` and self-mapping, as stated -/
theorem exists_fixedPoint {s : ℝ → ℝ} (hc : ContinuousOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) : ∃ a ∈ Icc (0 : ℝ) 1, s a = a := by
  have hg : ContinuousOn (fun a => s a - a) (Icc 0 1) := hc.sub continuousOn_id
  have h0 : 0 ≤ s 0 := (hm (left_mem_Icc.2 zero_le_one)).1
  have h1 : s 1 ≤ 1 := (hm (right_mem_Icc.2 zero_le_one)).2
  have hsub := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hg
  obtain ⟨a, ha, hfa⟩ := hsub ⟨by show s 1 - 1 ≤ 0; linarith, by show 0 ≤ s 0 - 0; linarith⟩
  exact ⟨a, ha, by simpa [sub_eq_zero] using hfa⟩

/-- **Contrapositive**: a settlement of `[0, 1]` into itself with no fixed point (positive gap at
every quote) is not continuous on `[0, 1]`.
Source: trust-lab-2-043 (i′); mandate Target 11 (i′)
Kind: L
Fidelity: exact -/
theorem not_continuousOn_of_no_fixedPoint {s : ℝ → ℝ} (hm : MapsTo s (Icc 0 1) (Icc 0 1))
    (h : ∀ a ∈ Icc (0 : ℝ) 1, 0 < settleGap s a) : ¬ ContinuousOn s (Icc 0 1) := by
  intro hcont
  obtain ⟨a, ha, hfa⟩ := exists_fixedPoint hcont hm
  have := h a ha
  rw [(settleGap_eq_zero_iff s a).2 hfa] at this
  exact lt_irrefl _ this

/-! ## The anti-indicator family -/

/-- The anti-indicator settlement at level `c`: `s a = 1` if `a ≤ c`, else `0` (the inverting
step of the quote-referencing diagonal; `c = 1/2` is lean-deference's `antiInd`).
Source: `research/lean-deference/SelfReferentialTarget.lean` (`antiInd`), generalised in the level;
trust-lab-2-043 (ii)
Kind: D
Fidelity: exact (generalisation of `antiInd` to level `c`) -/
def antiIndAt (c : ℝ) (a : ℝ) : ℝ := if a ≤ c then 1 else 0

/-- The anti-indicator maps `[0, 1]` into itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem antiIndAt_mapsTo (c : ℝ) : MapsTo (antiIndAt c) (Icc 0 1) (Icc 0 1) := by
  intro a _
  unfold antiIndAt
  split_ifs <;> constructor <;> norm_num

/-- The gap of the anti-indicator at level `c` is at least `min c (1 − c)` on `[0, 1]` (for any
real `c`; the hypothesis `c ∈ [0, 1]` an earlier version carried was unused).
Source: trust-lab-2-043 (ii)
Kind: L
Fidelity: exact -/
theorem settleGap_antiIndAt_ge (c : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    min c (1 - c) ≤ settleGap (antiIndAt c) a := by
  unfold settleGap antiIndAt
  split_ifs with h
  · rw [abs_of_nonneg (by linarith [ha.2])]
    exact (min_le_right _ _).trans (by linarith)
  · rw [not_le] at h
    rw [abs_of_nonpos (by linarith [ha.1])]
    exact (min_le_left _ _).trans (by linarith)

/-- **Computed infimum.** For `c ∈ [0, 1]`, `min c (1 − c)` is the greatest lower bound of the
anti-indicator's gap over `[0, 1]`: below the level the gap is `1 − a ≥ 1 − c` (attained at
`a = c`); above it the gap is `a`, approaching `c` from above (not attained when `c < 1`).
At `c = 1/2` the infimum is `1/2`, which re-proves `no_exact_quote` + `residual_half` of
lean-deference's `SelfReferentialTarget` as the instance `c = 1/2`.
Source: trust-lab-2-043 (ii) ("for `s = antiInd` the infimum is `½` as a computed infimum");
`research/lean-deference/SelfReferentialTarget.lean` (`no_exact_quote`, `residual_half`)
Kind: P
Fidelity: exact (generalised in the level; the `c = 1/2` case is the cited result)
Hyps: (a) `c ∈ [0, 1]` -/
theorem isGLB_settleGap_antiIndAt {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IsGLB ((fun a => settleGap (antiIndAt c) a) '' Icc 0 1) (min c (1 - c)) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact settleGap_antiIndAt_ge c ha
  · intro b hb
    have h1 : b ≤ 1 - c := by
      have := hb (Set.mem_image_of_mem (fun a => settleGap (antiIndAt c) a) hc)
      simp only [settleGap, antiIndAt, le_refl, if_true] at this
      rwa [abs_of_nonneg (by linarith [hc.2])] at this
    have h2 : b ≤ c := by
      rcases hc.2.lt_or_eq with hlt | heq
      · by_contra hbc
        rw [not_le] at hbc
        have hmin : c < min b 1 := lt_min hbc hlt
        set a := (c + min b 1) / 2 with ha_def
        have hca : c < a := by rw [ha_def]; linarith
        have ha1 : a ≤ 1 := by
          rw [ha_def]
          have := min_le_right b 1
          linarith
        have hab : a < b := by
          rw [ha_def]
          have := min_le_left b 1
          linarith
        have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], ha1⟩
        have := hb (Set.mem_image_of_mem (fun a => settleGap (antiIndAt c) a) ha01)
        simp only [settleGap, antiIndAt, not_le.2 hca, if_false] at this
        rw [abs_of_nonpos (by linarith [hc.1])] at this
        linarith
      · rw [heq]
        rw [heq] at h1
        linarith
    exact le_min h2 h1

/-- **Attainment.** At the level itself the anti-indicator's gap is exactly `1 − c` (the lower
branch of the GLB is attained at `a = c`); at `c = 1/2` this is lean-deference's `residual_half`
(`|1/2 − antiInd (1/2)| = 1/2`), the attainment half of the cited result, which `IsGLB` alone
does not state.
Source: `research/lean-deference/SelfReferentialTarget.lean` (`residual_half`); audit round 1
(fidelity N5)
Kind: L
Fidelity: exact (generalised in the level)
Hyps: (a) `c ∈ [0, 1]` -/
theorem settleGap_antiIndAt_attained {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    settleGap (antiIndAt c) c = 1 - c := by
  unfold settleGap antiIndAt
  simp only [le_refl, if_true]
  exact abs_of_nonneg (by linarith [hc.2])

/-! ## Witnesses -/

/-- **Witness of `exists_fixedPoint` (N+).** The affine flip `s a = 1 − a` is continuous on
`[0, 1]`, maps it into itself, is non-constant (`s 0 = 1 ≠ 0 = s 1`), and has the *unique* fixed
point `1/2`: the settlement gap vanishes there and nowhere else on `[0, 1]`. It inhabits the
theorem's full hypothesis package and exercises its mechanism — `s a − a = 1 − 2a` changes sign
on `[0, 1]`, which is what the intermediate value theorem uses; a constant map (below) would not.
Source: mandate Target 11 (iii), replacing the constant witness after audit round 1 (adversarial
blocking 1)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem affine_flip_fixedPoint :
    ContinuousOn (fun a : ℝ => 1 - a) (Icc 0 1) ∧
      MapsTo (fun a : ℝ => 1 - a) (Icc 0 1) (Icc 0 1) ∧
      (fun a : ℝ => 1 - a) 0 ≠ (fun a : ℝ => 1 - a) 1 ∧
      settleGap (fun a => 1 - a) (1 / 2) = 0 ∧
      ∀ a ∈ Icc (0 : ℝ) 1, settleGap (fun a => 1 - a) a = 0 → a = 1 / 2 := by
  refine ⟨continuousOn_const.sub continuousOn_id,
    fun a ha => ⟨by linarith [ha.2], by linarith [ha.1]⟩, by norm_num, ?_, ?_⟩
  · unfold settleGap
    norm_num
  · intro a _ h
    rw [settleGap_eq_zero_iff] at h
    linarith

/-- `exists_fixedPoint` applied to the affine flip: the quote it produces is, by uniqueness, `1/2`.
Source: none: infrastructure (the theorem run on its N+ witness)
Kind: L
Fidelity: n/a -/
theorem affine_flip_exists_fixedPoint :
    ∃ a ∈ Icc (0 : ℝ) 1, (fun a : ℝ => 1 - a) a = a ∧ a = 1 / 2 := by
  obtain ⟨h1, h2, _, _, h5⟩ := affine_flip_fixedPoint
  obtain ⟨a, ha, hfa⟩ := exists_fixedPoint h1 h2
  exact ⟨a, ha, hfa, h5 a ha ((settleGap_eq_zero_iff _ a).2 hfa)⟩

/-- The source's constant settlement `s ≡ 1/2` (the price-level liar `χ`) has the fixed point
`1/2`: zero gap. **N−** as a witness of `exists_fixedPoint`: a constant map has a zero-gap quote
with no continuity and no intermediate value theorem involved (`constant_fixedPoint` below), so
it inhabits the hypotheses without exercising the mechanism. Kept because it is the source's
named instance; the N+ witness is `affine_flip_fixedPoint`.
Source: trust-lab-2-043 (iii); `scout-acceleration.md` Q6 (iii)
Kind: N-
Fidelity: exact
Hyps: (a) none -/
theorem const_half_fixedPoint :
    ContinuousOn (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 1) ∧
      MapsTo (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 1) (Icc 0 1) ∧
      settleGap (fun _ => (1 / 2 : ℝ)) (1 / 2) = 0 := by
  refine ⟨continuousOn_const, fun _ _ => ⟨by norm_num, by norm_num⟩, ?_⟩
  simp [settleGap]

/-- Why the constant witness is degenerate: *every* constant map has a zero-gap quote, with no
continuity hypothesis in sight.
Source: audit round 1 (adversarial probe P5)
Kind: L
Fidelity: n/a -/
theorem constant_fixedPoint (c : ℝ) : settleGap (fun _ => c) c = 0 := by
  simp [settleGap]

/-- The anti-indicator at level `1/2` has gap `≥ 1/2` at every quote in `[0, 1]`, has no fixed
point there, and is therefore discontinuous on `[0, 1]`.
Source: trust-lab-2-043 (iii); `research/lean-deference/SelfReferentialTarget.lean` (`residual_half`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem antiInd_half_gap :
    (∀ a ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ settleGap (antiIndAt (1 / 2)) a) ∧
      ¬ ContinuousOn (antiIndAt (1 / 2)) (Icc 0 1) := by
  have hge : ∀ a ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ settleGap (antiIndAt (1 / 2)) a := by
    intro a ha
    have := settleGap_antiIndAt_ge (1 / 2) ha
    rwa [show min (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 by norm_num] at this
  refine ⟨hge, not_continuousOn_of_no_fixedPoint (antiIndAt_mapsTo _) ?_⟩
  intro a ha
  linarith [hge a ha]

/-- The bound `1/2` of `antiInd_half_gap` is attained at the quote `1/2`: lean-deference's
`residual_half` as the `c = 1/2` instance of `settleGap_antiIndAt_attained`.
Source: `research/lean-deference/SelfReferentialTarget.lean` (`residual_half`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem antiInd_half_attained : settleGap (antiIndAt (1 / 2)) (1 / 2) = 1 / 2 := by
  rw [settleGap_antiIndAt_attained ⟨by norm_num, by norm_num⟩]
  norm_num

/-! ## Stretch: antitone settlements — the gap infimum at the crossing

The mandate's stretch: "for a nonincreasing `s` on `[0, 1]` without a fixed point, the gap
infimum equals the distance from the diagonal at the crossing (`min (s(c⁻) − c) (c − s(c⁺))`)".
That two-term formula is **wrong as stated**: the value of `s` *at* the crossing is a third
candidate, and a jump whose value at `c` lands near the diagonal makes the infimum smaller than
both one-sided terms (`Crossing.jump_counterexample`: one-sided limits `1` and `0` at `c = 1/2`,
so the two-term formula says `1/2`, but `s (1/2) = 5/8` gives gap `1/8`). The corrected theorem
(`Crossing.isGLB_settleGap_crossing`) has three terms, and the anti-indicator's `min c (1 − c)`
is recovered from it (`Crossing.antiIndAt_via_crossing`). -/

namespace Crossing

/-- The quotes strictly below the settlement: `{a ∈ [0, 1] | a < s a}`.
Source: mandate Target 11 (stretch); repair round 1
Kind: D
Fidelity: n/a -/
def below (s : ℝ → ℝ) : Set ℝ := {a | a ∈ Icc (0 : ℝ) 1 ∧ a < s a}

/-- The **crossing** of a settlement, `sSup {a ∈ [0, 1] | a < s a}`: where an antitone settlement
without a fixed point passes from above the diagonal to below it.
Source: mandate Target 11 (stretch: "the crossing"); repair round 1
Kind: D
Fidelity: exact -/
def crossing (s : ℝ → ℝ) : ℝ := sSup (below s)

/-- The left value at the crossing, `s(c⁻) := sInf (s '' [0, c))` — for an antitone `s` the
left limit; meaningful when `0 < c`.
Source: mandate Target 11 (stretch: `s(c⁻)`)
Kind: D
Fidelity: exact (as the value of the monotone one-sided limit) -/
def leftVal (s : ℝ → ℝ) : ℝ := sInf (s '' Ico 0 (crossing s))

/-- The right value at the crossing, `s(c⁺) := sSup (s '' (c, 1])` — for an antitone `s` the
right limit; meaningful when `c < 1`.
Source: mandate Target 11 (stretch: `s(c⁺)`)
Kind: D
Fidelity: exact (as the value of the monotone one-sided limit) -/
def rightVal (s : ℝ → ℝ) : ℝ := sSup (s '' Ioc (crossing s) 1)

/-- Without a fixed point, `0` is below the settlement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem zero_mem_below {s : ℝ → ℝ} (hm : MapsTo s (Icc 0 1) (Icc 0 1))
    (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a) : (0 : ℝ) ∈ below s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  exact ⟨h0, lt_of_le_of_ne (hm h0).1 (hnf 0 h0).symm⟩

/-- The below-set is bounded above by `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem below_bddAbove (s : ℝ → ℝ) : BddAbove (below s) := ⟨1, fun _ ha => ha.1.2⟩

/-- The crossing lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem crossing_mem {s : ℝ → ℝ} (hm : MapsTo s (Icc 0 1) (Icc 0 1))
    (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a) : crossing s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_csSup (below_bddAbove s) (zero_mem_below hm hnf),
    csSup_le ⟨0, zero_mem_below hm hnf⟩ fun _ ha => ha.1.2⟩

/-- Left of the crossing the settlement is above the diagonal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lt_of_lt_crossing {s : ℝ → ℝ} (hanti : AntitoneOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (h : a < crossing s) : a < s a := by
  obtain ⟨a', ha', hlt⟩ := exists_lt_of_lt_csSup ⟨0, zero_mem_below hm hnf⟩ h
  exact lt_of_lt_of_le (lt_trans hlt ha'.2) (hanti ha ha'.1 hlt.le)

/-- Right of the crossing the settlement is below the diagonal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lt_of_crossing_lt {s : ℝ → ℝ} (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (h : crossing s < a) : s a < a := by
  have hnot : ¬ a < s a := fun hlt =>
    absurd (le_csSup (below_bddAbove s) ⟨ha, hlt⟩) (not_le.2 h)
  exact lt_of_le_of_ne (not_lt.1 hnot) (hnf a ha)

/-- **The gap infimum of an antitone settlement without a fixed point**, with the crossing `c`
strictly inside `(0, 1)`: the greatest lower bound of `|s a − a|` over `[0, 1]` is the least of
**three** distances from the diagonal at the crossing — the gap at `c` itself, `|s c − c|`, the
left-limit term `s(c⁻) − c`, and the right-limit term `c − s(c⁺)`. (The mandate's two-term
formula omits the first; `jump_counterexample` shows it is needed.) The one-sided terms are
approached but in general not attained; the middle one is.
Source: mandate Target 11 (stretch: monotone settlement), corrected; repair round 1
Kind: P
Fidelity: variant: three terms where the mandate's formula has two (the two-term version is
false; see `jump_counterexample`); the crossing is restricted to the open interval, the boundary
cases being degenerate (`s ≡ 0` on `(0, 1]`, or `s ≡ 1` on `[0, 1)`)
Hyps: (a) `s` antitone on `[0, 1]`, self-mapping, fixed-point-free; `0 < c < 1` -/
theorem isGLB_settleGap_crossing {s : ℝ → ℝ} (hanti : AntitoneOn s (Icc 0 1))
    (hm : MapsTo s (Icc 0 1) (Icc 0 1)) (hnf : ∀ a ∈ Icc (0 : ℝ) 1, s a ≠ a)
    (hc0 : 0 < crossing s) (hc1 : crossing s < 1) :
    IsGLB (settleGap s '' Icc 0 1)
      (min (settleGap s (crossing s))
        (min (leftVal s - crossing s) (crossing s - rightVal s))) := by
  have hcmem : crossing s ∈ Icc (0 : ℝ) 1 := crossing_mem hm hnf
  have hbddL : BddBelow (s '' Ico 0 (crossing s)) :=
    ⟨0, by rintro _ ⟨a, ha, rfl⟩; exact (hm ⟨ha.1, ha.2.le.trans hcmem.2⟩).1⟩
  have hbddR : BddAbove (s '' Ioc (crossing s) 1) :=
    ⟨1, by rintro _ ⟨a, ha, rfl⟩; exact (hm ⟨hcmem.1.trans ha.1.le, ha.2⟩).2⟩
  have hneL : (s '' Ico 0 (crossing s)).Nonempty := ⟨s 0, 0, ⟨le_rfl, hc0⟩, rfl⟩
  have hneR : (s '' Ioc (crossing s) 1).Nonempty := ⟨s 1, 1, ⟨hc1, le_rfl⟩, rfl⟩
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    rcases lt_trichotomy a (crossing s) with h | h | h
    · have hlt := lt_of_lt_crossing hanti hm hnf ha h
      have hgap : settleGap s a = s a - a := by
        unfold settleGap; exact abs_of_pos (by linarith)
      have hL : leftVal s ≤ s a := csInf_le hbddL ⟨a, ⟨ha.1, h⟩, rfl⟩
      rw [hgap]
      calc min (settleGap s (crossing s)) (min (leftVal s - crossing s) (crossing s - rightVal s))
          ≤ leftVal s - crossing s := (min_le_right _ _).trans (min_le_left _ _)
        _ ≤ s a - a := by linarith
    · rw [h]; exact min_le_left _ _
    · have hlt := lt_of_crossing_lt hnf ha h
      have hgap : settleGap s a = a - s a := by
        unfold settleGap; rw [abs_of_neg (by linarith), neg_sub]
      have hR : s a ≤ rightVal s := le_csSup hbddR ⟨a, ⟨h, ha.2⟩, rfl⟩
      rw [hgap]
      calc min (settleGap s (crossing s)) (min (leftVal s - crossing s) (crossing s - rightVal s))
          ≤ crossing s - rightVal s := (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ a - s a := by linarith
  · intro b hb
    refine le_min (hb ⟨_, hcmem, rfl⟩) (le_min ?_ ?_)
    · by_contra hcon
      rw [not_le] at hcon
      have hlt : sInf (s '' Ico 0 (crossing s)) < b + crossing s := by
        unfold leftVal at hcon; linarith
      obtain ⟨_, ⟨a₀, ha₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hneL hlt
      -- a quote between `a₀` and the crossing, close enough to the crossing
      have hmem : max a₀ (crossing s - (b + crossing s - s a₀) / 2) ∈ Icc (0 : ℝ) 1 :=
        ⟨ha₀.1.trans (le_max_left _ _), (max_lt ha₀.2 (by linarith)).le.trans hcmem.2⟩
      have hac : max a₀ (crossing s - (b + crossing s - s a₀) / 2) < crossing s :=
        max_lt ha₀.2 (by linarith)
      have hsa : s (max a₀ (crossing s - (b + crossing s - s a₀) / 2)) ≤ s a₀ :=
        hanti ⟨ha₀.1, ha₀.2.le.trans hcmem.2⟩ hmem (le_max_left _ _)
      have hup := lt_of_lt_crossing hanti hm hnf hmem hac
      have hb' := hb ⟨_, hmem, rfl⟩
      unfold settleGap at hb'
      rw [abs_of_pos (by linarith)] at hb'
      have hge := le_max_right a₀ (crossing s - (b + crossing s - s a₀) / 2)
      linarith
    · by_contra hcon
      rw [not_le] at hcon
      have hlt : crossing s - b < sSup (s '' Ioc (crossing s) 1) := by
        unfold rightVal at hcon; linarith
      obtain ⟨_, ⟨a₀, ha₀, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hneR hlt
      have hca : crossing s < min a₀ (crossing s + (s a₀ - crossing s + b) / 2) :=
        lt_min ha₀.1 (by linarith)
      have hmem : min a₀ (crossing s + (s a₀ - crossing s + b) / 2) ∈ Icc (0 : ℝ) 1 :=
        ⟨hcmem.1.trans hca.le, (min_le_left _ _).trans ha₀.2⟩
      have hsa : s a₀ ≤ s (min a₀ (crossing s + (s a₀ - crossing s + b) / 2)) :=
        hanti hmem ⟨hcmem.1.trans ha₀.1.le, ha₀.2⟩ (min_le_left _ _)
      have hdown := lt_of_crossing_lt hnf hmem hca
      have hb' := hb ⟨_, hmem, rfl⟩
      unfold settleGap at hb'
      rw [abs_of_neg (by linarith), neg_sub] at hb'
      have hle := min_le_right a₀ (crossing s + (s a₀ - crossing s + b) / 2)
      linarith

/-! ### Instance: the anti-indicator, recovered from the crossing theorem -/

/-- The below-set of the anti-indicator at level `c < 1` is `[0, c]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem below_antiIndAt {c : ℝ} (hc1 : c < 1) : below (antiIndAt c) = Icc 0 c := by
  ext a
  simp only [below, antiIndAt, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, _⟩, hlt⟩
    split_ifs at hlt with h
    · exact ⟨h0, h⟩
    · exact absurd hlt (not_lt.2 h0)
  · rintro ⟨h0, hc⟩
    refine ⟨⟨h0, hc.trans hc1.le⟩, ?_⟩
    rw [if_pos hc]
    exact lt_of_le_of_lt hc hc1

/-- The crossing of the anti-indicator at level `c ∈ [0, 1)` is `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem crossing_antiIndAt {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) : crossing (antiIndAt c) = c := by
  unfold crossing
  rw [below_antiIndAt hc1]
  exact csSup_Icc hc0

/-- Left of the level the anti-indicator is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem image_Ico_antiIndAt {c : ℝ} (hc0 : 0 < c) : antiIndAt c '' Ico 0 c = {1} := by
  ext y
  simp only [Set.mem_image, Set.mem_Ico, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨_, hac⟩, rfl⟩
    simp [antiIndAt, hac.le]
  · rintro rfl
    exact ⟨0, ⟨le_rfl, hc0⟩, by simp [antiIndAt, hc0.le]⟩

/-- Right of the level the anti-indicator is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem image_Ioc_antiIndAt {c : ℝ} (hc1 : c < 1) : antiIndAt c '' Ioc c 1 = {0} := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨hca, _⟩, rfl⟩
    simp [antiIndAt, not_le.2 hca]
  · rintro rfl
    exact ⟨1, ⟨hc1, le_rfl⟩, by simp [antiIndAt, not_le.2 hc1]⟩

/-- The anti-indicator is antitone on `[0, 1]` and has no fixed point there.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem antiIndAt_antitoneOn_noFixed {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    AntitoneOn (antiIndAt c) (Icc 0 1) ∧ ∀ a ∈ Icc (0 : ℝ) 1, antiIndAt c a ≠ a := by
  constructor
  · intro a _ b _ hab
    unfold antiIndAt
    split_ifs with h1 h2 <;> norm_num
    exact absurd (hab.trans h1) h2
  · intro a _ h
    unfold antiIndAt at h
    split_ifs at h with hac
    · linarith
    · rw [not_le] at hac
      linarith

/-- **The anti-indicator's `min c (1 − c)`, recovered from the crossing theorem** for
`c ∈ (0, 1)`: its crossing is `c`, its one-sided values `1` and `0`, its gap at `c` is `1 − c`,
and `min (1 − c) (min (1 − c) c) = min c (1 − c)` — consistent with `isGLB_settleGap_antiIndAt`,
which the general theorem therefore subsumes on the open interval.
Source: trust-lab-2-043 (ii); mandate Target 11 (stretch); repair round 1
Kind: N+
Fidelity: exact (instance of `isGLB_settleGap_crossing`; `c ∈ (0, 1)`)
Hyps: (a) `0 < c < 1` -/
theorem antiIndAt_via_crossing {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    crossing (antiIndAt c) = c ∧ leftVal (antiIndAt c) = 1 ∧ rightVal (antiIndAt c) = 0 ∧
      IsGLB (settleGap (antiIndAt c) '' Icc 0 1) (min c (1 - c)) := by
  have hcr := crossing_antiIndAt hc0.le hc1
  have hL : leftVal (antiIndAt c) = 1 := by
    unfold leftVal
    rw [hcr, image_Ico_antiIndAt hc0]
    exact csInf_singleton 1
  have hR : rightVal (antiIndAt c) = 0 := by
    unfold rightVal
    rw [hcr, image_Ioc_antiIndAt hc1]
    exact csSup_singleton 0
  obtain ⟨hanti, hnf⟩ := antiIndAt_antitoneOn_noFixed hc0.le hc1
  have h := isGLB_settleGap_crossing hanti (antiIndAt_mapsTo c) hnf (by rw [hcr]; exact hc0)
    (by rw [hcr]; exact hc1)
  rw [hcr, hL, hR, settleGap_antiIndAt_attained ⟨hc0.le, hc1.le⟩, sub_zero] at h
  refine ⟨hcr, hL, hR, ?_⟩
  have e : min (1 - c) (min (1 - c) c) = min c (1 - c) := by
    rw [← min_assoc, min_self, min_comm]
  rwa [e] at h

/-! ### The jump counterexample to the two-term formula -/

/-- A settlement that jumps across the diagonal at `1/2` with its value *at* the crossing,
`5/8`, close to the diagonal: `1` below `1/2`, `5/8` at `1/2`, `0` above.
Source: repair round 1 (counterexample to the mandate's stretch formula)
Kind: D
Fidelity: n/a -/
def jump : ℝ → ℝ := fun a => if a < 1 / 2 then 1 else if 1 / 2 < a then 0 else 5 / 8

/-- **The two-term formula is false.** `jump` is antitone on `[0, 1]`, self-mapping and
fixed-point-free; its crossing is `1/2` with one-sided values `1` and `0`, so the mandate's
`min (s(c⁻) − c) (c − s(c⁺))` evaluates to `1/2`; but the gap at the crossing is `1/8`, and the
greatest lower bound of the gap over `[0, 1]` is `1/8`, not `1/2`. The three-term theorem gives
`min (1/8) (min (1/2) (1/2)) = 1/8`.
Source: mandate Target 11 (stretch formula), refuted; repair round 1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem jump_counterexample :
    AntitoneOn jump (Icc 0 1) ∧ MapsTo jump (Icc 0 1) (Icc 0 1) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, jump a ≠ a) ∧
      crossing jump = 1 / 2 ∧ leftVal jump = 1 ∧ rightVal jump = 0 ∧
      settleGap jump (1 / 2) = 1 / 8 ∧
      IsGLB (settleGap jump '' Icc 0 1) (1 / 8) ∧
      (1 / 8 : ℝ) < min (leftVal jump - crossing jump) (crossing jump - rightVal jump) := by
  have hanti : AntitoneOn jump (Icc 0 1) := by
    intro a _ b _ hab
    unfold jump
    split_ifs <;> (try norm_num) <;> (try simp only [not_lt] at *) <;> linarith
  have hm : MapsTo jump (Icc 0 1) (Icc 0 1) := by
    intro a _
    unfold jump
    split_ifs <;> constructor <;> norm_num
  have hnf : ∀ a ∈ Icc (0 : ℝ) 1, jump a ≠ a := by
    intro a _ h
    unfold jump at h
    split_ifs at h with h1 h2
    · linarith
    · linarith
    · rw [not_lt] at h1 h2
      linarith
  have hbelow : below jump = Icc 0 (1 / 2) := by
    ext a
    simp only [below, jump, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h0, _⟩, hlt⟩
      split_ifs at hlt with h1 h2
      · exact ⟨h0, h1.le⟩
      · exact absurd hlt (not_lt.2 h0)
      · rw [not_lt] at h1 h2
        exact ⟨h0, h2⟩
    · rintro ⟨h0, hc⟩
      refine ⟨⟨h0, by linarith⟩, ?_⟩
      split_ifs with h1 h2 <;> linarith
  have hcr : crossing jump = 1 / 2 := by
    unfold crossing
    rw [hbelow]
    exact csSup_Icc (by norm_num)
  have hL : leftVal jump = 1 := by
    unfold leftVal
    rw [hcr]
    have : jump '' Ico 0 (1 / 2) = {1} := by
      ext y
      simp only [Set.mem_image, Set.mem_Ico, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, ⟨_, hac⟩, rfl⟩
        unfold jump
        rw [if_pos hac]
      · rintro rfl
        exact ⟨0, ⟨le_rfl, by norm_num⟩, by norm_num [jump]⟩
    rw [this]
    exact csInf_singleton 1
  have hR : rightVal jump = 0 := by
    unfold rightVal
    rw [hcr]
    have : jump '' Ioc (1 / 2) 1 = {0} := by
      ext y
      simp only [Set.mem_image, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, ⟨hca, _⟩, rfl⟩
        unfold jump
        rw [if_neg (not_lt.2 hca.le), if_pos hca]
      · rintro rfl
        exact ⟨1, ⟨by norm_num, le_rfl⟩, by norm_num [jump]⟩
    rw [this]
    exact csSup_singleton 0
  have hgap : settleGap jump (1 / 2) = 1 / 8 := by
    unfold settleGap jump
    norm_num
  have h := isGLB_settleGap_crossing hanti hm hnf (by rw [hcr]; norm_num) (by rw [hcr]; norm_num)
  rw [hcr, hL, hR, hgap] at h
  refine ⟨hanti, hm, hnf, hcr, hL, hR, hgap, ?_, ?_⟩
  · rwa [show min (1 / 8 : ℝ) (min (1 - 1 / 2) (1 / 2 - 0)) = 1 / 8 by norm_num] at h
  · rw [hcr, hL, hR]
    norm_num

end Crossing

end

end Cleanroom.Trust.LegitFiniteDefect.Settlement
