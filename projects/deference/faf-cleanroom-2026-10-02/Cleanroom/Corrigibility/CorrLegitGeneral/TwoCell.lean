import Cleanroom.Corrigibility.CorrLegitGeneral.LocalValue
import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesFn66

/-!
# corr-legit-general — T4(b), the Value half that survives: two-cell local Value from
Simple Trust for tie-consistent strategies

`tie4` (WitnessesFn66) shows that fn 64's local Value fails under Simple Trust when a recommended
strategy breaks a tie *differently at two worlds with the same `P_w(q)`*. The theorem here is
that this is the only obstruction: for a `{q,¬q}`-measurable menu and a recommended strategy
whose choice is determined by `P_w(q)` on the support (`hSdet`), the Simple-Trust cuts give
`E_π(O) ≤ E_π(S)` for every option `O`. Two corollaries: (i) `ValuesWrt (questionOf q) π F` when
the frame's rows on the support are determined by `P_w(q)` (every recommended strategy is then
consistent, by the cell constraint) — this covers fn 66; (ii) `WeakValuesWrt (questionOf q) π F`
unconditionally (choose the consistent strategy), which is the two-cell case of the weak reading
of fn 65's conjecture.

**The argument.** Write each option as `β_O + b_O·𝟙_q` and the chosen option's line relative to
`O` as `ℓ_w(p) = A_w + B_w·p`, so `E_π(S) − E_π(O) = ∑_w π_w (A_w + B_w·𝟙_q(w))`. Optimality at
each world gives `ℓ_w(p_w) ≥ 0`, `ℓ_w(p_w) ≥ ℓ_v(p_w)`, hence slopes `B_w` monotone in `p_w`.
Split the support at the sign change of `B`. On the upper part (`B ≥ 0`, an upward-closed set in
`p`), induct on the set: subtracting the line of the lowest cluster `ℓ₀` leaves lines with
`B ≥ 0` again on the strictly-higher worlds, and the subtracted part is
`A₀·π(U) + B₀·π(q ∧ U) ≥ (A₀ + B₀·p₀)·π(U) ≥ 0` by the above-threshold cut at `p₀`. The lower part
is the mirror image (`q ↦ ¬q`, `p ↦ 1 − p`) using the below-threshold cut.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A sum of a product with an indicator is the mass of the intersection.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_mul_ind_eq_mass (π : W → ℝ) (q T : Finset W) :
    ∑ w ∈ T, π w * ind q w = mass π (q ∩ T) := by
  simp only [ind, mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, inter_comm]
  rfl

/-- **The upper induction.** Abstract data: a nonnegative weight `π`, a "probability" `p`, an
"indicator" `c`, lines `(A, B)` indexed by worlds; the above-threshold cut for `(p, c)` at every
`t`; optimality of each positive world's line at its own `p` among all positive worlds' lines;
consistency of the lines on worlds with equal `p`. For an upward-closed `U ⊆ supp π` on which all
slopes are `≥ 0` and all lines are `≥ 0` at their own `p`, `∑_{w ∈ U} π_w (A_w + B_w c_w) ≥ 0`.
Source: this package (the two-cell argument, upper half)
Kind: P
Fidelity: n/a
Hyps: (a) as listed -/
theorem upper_sum_nonneg {π p c : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    (hcut : ∀ t, t * ∑ w ∈ univ.filter (fun w => t ≤ p w), π w ≤
      ∑ w ∈ univ.filter (fun w => t ≤ p w), π w * c w) :
    ∀ U : Finset W, ∀ A B : W → ℝ,
      (∀ w v, 0 < π w → 0 < π v → A v + B v * p w ≤ A w + B w * p w) →
      (∀ w v, 0 < π w → 0 < π v → p w = p v → A w = A v ∧ B w = B v) →
      (∀ w ∈ U, 0 < π w) → (∀ w ∈ U, ∀ v, 0 < π v → p w ≤ p v → v ∈ U) →
      (∀ w ∈ U, 0 ≤ B w) → (∀ w ∈ U, 0 ≤ A w + B w * p w) →
      0 ≤ ∑ w ∈ U, π w * (A w + B w * c w) := by
  intro U
  refine Finset.strongInductionOn U ?_
  intro U ih A B hopt hcons hUs hUup hB hA
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨w₀, hw₀, hmin⟩ := U.exists_min_image p hne
  have hπ₀ := hUs w₀ hw₀
  set U' := U.filter (fun w => p w₀ < p w) with hU'
  have hU'sub : U' ⊆ U := filter_subset _ _
  have hU'ss : U' ⊂ U := by
    rw [hU']
    exact filter_ssubset.2 ⟨w₀, hw₀, lt_irrefl _⟩
  -- the threshold event at `p w₀` meets the support exactly in `U`
  set T := univ.filter (fun w => p w₀ ≤ p w) with hT
  have hsumT : ∀ f : W → ℝ, ∑ w ∈ U, π w * f w = ∑ w ∈ T, π w * f w := by
    intro f
    apply sum_subset
    · intro w hw
      rw [hT, mem_filter]
      exact ⟨mem_univ w, hmin w hw⟩
    · intro w hwT hwU
      rw [hT, mem_filter] at hwT
      have : π w = 0 := by
        by_contra hne'
        have hpos : 0 < π w := lt_of_le_of_ne (hπ w) (Ne.symm hne')
        exact hwU (hUup w₀ hw₀ w hpos hwT.2)
      simp [this]
  -- split the sum: the line of `w₀` on all of `U`, plus the differences on `U'`
  have hsplit : ∑ w ∈ U, π w * (A w + B w * c w) =
      ∑ w ∈ U, π w * (A w₀ + B w₀ * c w) +
        ∑ w ∈ U', π w * ((A w - A w₀) + (B w - B w₀) * c w) := by
    have e1 : ∑ w ∈ U', π w * ((A w - A w₀) + (B w - B w₀) * c w) =
        ∑ w ∈ U, π w * ((A w - A w₀) + (B w - B w₀) * c w) := by
      apply sum_subset hU'sub
      intro w hwU hwU'
      rw [hU', mem_filter, not_and] at hwU'
      have hle : p w₀ ≤ p w := hmin w hwU
      have heq : p w = p w₀ := le_antisymm (not_lt.1 (hwU' hwU)) hle
      obtain ⟨hA', hB'⟩ := hcons w w₀ (hUs w hwU) hπ₀ heq
      simp [hA', hB']
    rw [e1, ← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    ring
  rw [hsplit]
  -- first part: the cut at `p w₀`
  have hfirst : 0 ≤ ∑ w ∈ U, π w * (A w₀ + B w₀ * c w) := by
    have hT1 : ∑ w ∈ U, π w * 1 = ∑ w ∈ T, π w * 1 := hsumT (fun _ => 1)
    have hTc : ∑ w ∈ U, π w * c w = ∑ w ∈ T, π w * c w := hsumT c
    have e : ∑ w ∈ U, π w * (A w₀ + B w₀ * c w) =
        A w₀ * ∑ w ∈ T, π w + B w₀ * ∑ w ∈ T, π w * c w := by
      have e1 : ∑ w ∈ U, π w * (A w₀ + B w₀ * c w) =
          A w₀ * ∑ w ∈ U, π w * 1 + B w₀ * ∑ w ∈ U, π w * c w := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro w _
        ring
      rw [e1, hT1, hTc]
      simp
    rw [e]
    have hc := hcut (p w₀)
    rw [← hT] at hc
    have hTnn : 0 ≤ ∑ w ∈ T, π w := sum_nonneg (fun w _ => hπ w)
    have hB₀ := hB w₀ hw₀
    have hA₀ := hA w₀ hw₀
    have hmul : B w₀ * (p w₀ * ∑ w ∈ T, π w) ≤ B w₀ * ∑ w ∈ T, π w * c w :=
      mul_le_mul_of_nonneg_left hc hB₀
    calc (0 : ℝ) ≤ (A w₀ + B w₀ * p w₀) * ∑ w ∈ T, π w := mul_nonneg hA₀ hTnn
      _ = A w₀ * ∑ w ∈ T, π w + B w₀ * (p w₀ * ∑ w ∈ T, π w) := by ring
      _ ≤ A w₀ * ∑ w ∈ T, π w + B w₀ * ∑ w ∈ T, π w * c w := by linarith
  -- second part: the induction hypothesis on `U'` with the shifted lines
  have hsecond : 0 ≤ ∑ w ∈ U', π w * ((A w - A w₀) + (B w - B w₀) * c w) := by
    have hmono : ∀ w ∈ U', 0 ≤ B w - B w₀ := by
      intro w hw
      rw [hU', mem_filter] at hw
      have h1 := hopt w w₀ (hUs w hw.1) hπ₀
      have h2 := hopt w₀ w hπ₀ (hUs w hw.1)
      by_contra hneg
      have hlt : B w - B w₀ < 0 := not_le.1 hneg
      have := mul_neg_of_neg_of_pos hlt (sub_pos.2 hw.2)
      nlinarith
    exact ih U' hU'ss (fun w => A w - A w₀) (fun w => B w - B w₀)
      (fun w v hw hv => by have := hopt w v hw hv; linarith)
      (fun w v hw hv h => by
        obtain ⟨e1, e2⟩ := hcons w v hw hv h
        exact ⟨by rw [e1], by rw [e2]⟩)
      (fun w hw => hUs w (hU'sub hw))
      (fun w hw v hv hle => by
        rw [hU', mem_filter] at hw ⊢
        exact ⟨hUup w hw.1 v hv hle, lt_of_lt_of_le hw.2 hle⟩)
      hmono
      (fun w hw => by
        rw [hU', mem_filter] at hw
        have := hopt w w₀ (hUs w hw.1) hπ₀
        linarith)
  linarith

/-- **The lower induction**: the mirror image of `upper_sum_nonneg` under `p ↦ 1 − p`,
`c ↦ 1 − c`, with the below-threshold cut, for a downward-closed `U` on which all slopes are
`≤ 0`.
Source: this package (the two-cell argument, lower half)
Kind: P
Fidelity: n/a
Hyps: (a) as listed -/
theorem lower_sum_nonneg {π p c A B : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    (hcut : ∀ t, ∑ w ∈ univ.filter (fun w => p w ≤ t), π w * c w ≤
      t * ∑ w ∈ univ.filter (fun w => p w ≤ t), π w)
    (hopt : ∀ w v, 0 < π w → 0 < π v → A v + B v * p w ≤ A w + B w * p w)
    (hcons : ∀ w v, 0 < π w → 0 < π v → p w = p v → A w = A v ∧ B w = B v)
    (U : Finset W) (hUs : ∀ w ∈ U, 0 < π w)
    (hUdown : ∀ w ∈ U, ∀ v, 0 < π v → p v ≤ p w → v ∈ U)
    (hB : ∀ w ∈ U, B w ≤ 0) (hA : ∀ w ∈ U, 0 ≤ A w + B w * p w) :
    0 ≤ ∑ w ∈ U, π w * (A w + B w * c w) := by
  have hcut' : ∀ t, t * ∑ w ∈ univ.filter (fun w => t ≤ 1 - p w), π w ≤
      ∑ w ∈ univ.filter (fun w => t ≤ 1 - p w), π w * (1 - c w) := by
    intro t
    have hfilt : (univ.filter (fun w => t ≤ 1 - p w)) = univ.filter (fun w => p w ≤ 1 - t) := by
      ext w; simp only [mem_filter, mem_univ, true_and]; constructor <;> intro h <;> linarith
    rw [hfilt]
    have := hcut (1 - t)
    simp only [mul_sub, mul_one, sum_sub_distrib]
    linarith
  have hopt' : ∀ w v, 0 < π w → 0 < π v →
      (A v + B v) + (-B v) * (1 - p w) ≤ (A w + B w) + (-B w) * (1 - p w) := by
    intro w v hw hv
    have := hopt w v hw hv
    linarith
  have hcons' : ∀ w v, 0 < π w → 0 < π v → 1 - p w = 1 - p v →
      (A w + B w = A v + B v) ∧ (-B w = -B v) := by
    intro w v hw hv h
    obtain ⟨e1, e2⟩ := hcons w v hw hv (by linarith)
    exact ⟨by rw [e1, e2], by rw [e2]⟩
  have hUup' : ∀ w ∈ U, ∀ v, 0 < π v → 1 - p w ≤ 1 - p v → v ∈ U :=
    fun w hw v hv hle => hUdown w hw v hv (by linarith)
  have hB' : ∀ w ∈ U, 0 ≤ -B w := fun w hw => by linarith [hB w hw]
  have hA' : ∀ w ∈ U, 0 ≤ (A w + B w) + (-B w) * (1 - p w) := by
    intro w hw
    have := hA w hw
    linarith
  have key := upper_sum_nonneg (p := fun w => 1 - p w) (c := fun w => 1 - c w) hπ hcut' U
    (fun w => A w + B w) (fun w => -B w) hopt' hcons' hUs hUup' hB' hA'
  have e : ∑ w ∈ U, π w * (A w + B w * c w) =
      ∑ w ∈ U, π w * ((A w + B w) + (-B w) * (1 - c w)) :=
    sum_congr rfl (fun w _ => by ring)
  rw [e]
  exact key

/-- Slopes of optimal lines are monotone in `p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem slope_mono {π p A B : W → ℝ}
    (hopt : ∀ w v, 0 < π w → 0 < π v → A v + B v * p w ≤ A w + B w * p w)
    {w v : W} (hw : 0 < π w) (hv : 0 < π v) (hlt : p w < p v) : B w ≤ B v := by
  have h1 := hopt w v hw hv
  have h2 := hopt v w hv hw
  by_contra hneg
  have hlt' : B v - B w < 0 := by linarith [not_le.1 hneg]
  have := mul_neg_of_neg_of_pos hlt' (sub_pos.2 hlt)
  nlinarith

/-- **Two-cell local Value from Simple Trust, for tie-consistent strategies** (the core): for a
`{q,¬q}`-measurable menu `𝒪`, a recommended strategy `S` whose choice on the support is
determined by `P_w(q)`, and any option `O ∈ 𝒪`, the Simple-Trust cuts give `E_π(O) ≤ E_π(S)`.
Source: this package (the surviving neighbour of [[ddb-mm-authors]] C5 l. 95 and
[[legitimacy]] R5.3 l. 100 after `tie4`); [[Deference Done Better]] §5 l. 398, fn 65
Kind: P
Fidelity: exact (the tie-consistency hypothesis is a sufficient tie control that `tie4` shows
cannot be dropped — not a necessary one: a frame may violate it and still value every two-cell
menu when the tie-cell masses keep every split nonnegative; audit r3 fidelity N4)
Hyps: (a) `∀ w, 0 ≤ π w`, `SimpleTrustOn q π F`, measurability, recommendedness,
tie-consistency `hSdet` -/
theorem valuesWrt_questionOf_core {q : Finset W} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (hST : SimpleTrustOn q π F) (𝒪 : DecisionProblem W)
    (hmeas : ∀ o ∈ 𝒪, MeasurableWrt (questionOf q) o) (S : W → (W → ℝ))
    (hS : F.Recommended 𝒪 S)
    (hSdet : ∀ w v, 0 < π w → 0 < π v → mass (F.P w) q = mass (F.P v) q → S w = S v)
    (o : W → ℝ) (ho : o ∈ 𝒪) : E π o ≤ stratValue π S := by
  have haff : ∀ o' ∈ 𝒪, ∃ β b : ℝ, ∀ w, o' w = β + b * ind q w :=
    fun o' ho' => exists_affine_of_measurableWrt_questionOf (hmeas o' ho')
  choose! β b hβb using haff
  have hE : ∀ o' ∈ 𝒪, ∀ w, E (F.P w) o' = β o' + b o' * mass (F.P w) q := by
    intro o' ho' w
    have e : o' = fun v => β o' + b o' * ind q v := funext (hβb o' ho')
    conv_lhs => rw [e]
    exact E_affine_ind (F.P_mem w) q (β o') (b o')
  set p : W → ℝ := fun w => mass (F.P w) q with hp
  set A : W → ℝ := fun w => β (S w) - β o with hA
  set B : W → ℝ := fun w => b (S w) - b o with hB
  have hSmem : ∀ w, S w ∈ 𝒪 := hS.1.1
  -- the difference of values as the line sum
  have hdiff : stratValue π S - E π o = ∑ w, π w * (A w + B w * ind q w) := by
    unfold stratValue E
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro w _
    rw [hβb (S w) (hSmem w) w, hβb o ho w]
    simp only [hA, hB]
    ring
  rw [← sub_nonneg, hdiff]
  -- the structural facts about the lines
  have hopt : ∀ w v, 0 < π w → 0 < π v → A v + B v * p w ≤ A w + B w * p w := by
    intro w v _ _
    have := hS.2 w (S v) (hSmem v)
    rw [hE (S v) (hSmem v) w, hE (S w) (hSmem w) w] at this
    simp only [hA, hB, hp]
    linarith
  have hA0 : ∀ w, 0 ≤ A w + B w * p w := by
    intro w
    have := hS.2 w o ho
    rw [hE o ho w, hE (S w) (hSmem w) w] at this
    simp only [hA, hB, hp]
    linarith
  have hcons : ∀ w v, 0 < π w → 0 < π v → p w = p v → A w = A v ∧ B w = B v := by
    intro w v hw hv h
    have := hSdet w v hw hv h
    simp only [hA, hB, this, and_self]
  -- the cuts
  have hcutU : ∀ t, t * ∑ w ∈ univ.filter (fun w => t ≤ p w), π w ≤
      ∑ w ∈ univ.filter (fun w => t ≤ p w), π w * ind q w := by
    intro t
    have := hST.1 t
    rw [sum_mul_ind_eq_mass]
    exact this
  have hcutL : ∀ t, ∑ w ∈ univ.filter (fun w => p w ≤ t), π w * ind q w ≤
      t * ∑ w ∈ univ.filter (fun w => p w ≤ t), π w := by
    intro t
    have := hST.2 t
    rw [sum_mul_ind_eq_mass]
    exact this
  -- split the support at the sign of the slope
  have hsupp : ∑ w, π w * (A w + B w * ind q w) = ∑ w ∈ supp π, π w * (A w + B w * ind q w) := by
    symm
    apply sum_subset (subset_univ _)
    intro w _ hw
    have : π w = 0 := le_antisymm (not_lt.1 (mem_supp.not.1 hw)) (hπ w)
    simp [this]
  rw [hsupp, ← sum_filter_add_sum_filter_not (supp π) (fun w => 0 ≤ B w)]
  have hup : 0 ≤ ∑ w ∈ (supp π).filter (fun w => 0 ≤ B w), π w * (A w + B w * ind q w) := by
    refine upper_sum_nonneg hπ hcutU _ A B hopt hcons (fun w hw => ?_)
      (fun w hw v hv hle => ?_) (fun w hw => ?_) (fun w _ => hA0 w)
    · exact mem_supp.1 (mem_filter.1 hw).1
    · rw [mem_filter] at hw ⊢
      refine ⟨mem_supp.2 hv, ?_⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact le_trans hw.2 (slope_mono hopt (mem_supp.1 hw.1) hv hlt)
      · rw [← (hcons w v (mem_supp.1 hw.1) hv heq).2]; exact hw.2
    · exact (mem_filter.1 hw).2
  have hlo : 0 ≤ ∑ w ∈ (supp π).filter (fun w => ¬ 0 ≤ B w), π w * (A w + B w * ind q w) := by
    refine lower_sum_nonneg hπ hcutL hopt hcons _ (fun w hw => ?_) (fun w hw v hv hle => ?_)
      (fun w hw => ?_) (fun w _ => hA0 w)
    · exact mem_supp.1 (mem_filter.1 hw).1
    · rw [mem_filter] at hw ⊢
      refine ⟨mem_supp.2 hv, ?_⟩
      rcases hle.lt_or_eq with hlt | heq
      · have := slope_mono hopt hv (mem_supp.1 hw.1) hlt
        intro hc; exact hw.2 (le_trans hc this)
      · rw [(hcons w v (mem_supp.1 hw.1) hv heq.symm).2] at hw; exact hw.2
    · exact (not_le.1 (mem_filter.1 hw).2).le
  linarith

/-- **Two-cell local Value from Simple Trust when the rows are determined by `P_w(q)`**: if
support worlds with the same `P_w(q)` have the same row, every recommended strategy is
tie-consistent (cell constraint), and `ValuesWrt (questionOf q) π F` follows from the
Simple-Trust cuts. With `totalTrustWrt_questionOf_iff`, this is the two-cell equivalence
"local Total Trust ⟺ local Value" on this class of frames.
Source: [[Deference Done Better]] §5 l. 398, fn 65 l. 1237; [[ddb-mm-authors]] C5 l. 95 (the
surviving form)
Kind: P
Fidelity: weaker: the source's claim holds only under `hdet` (refuted without it, `tie4`)
Hyps: (a) `∀ w, 0 ≤ π w`, `SimpleTrustOn q π F`, `hdet` (rows determined by `P_w(q)` on the
support) -/
theorem valuesWrt_questionOf_of_simpleTrustOn {q : Finset W} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} (hST : SimpleTrustOn q π F)
    (hdet : ∀ w v, 0 < π w → 0 < π v → mass (F.P w) q = mass (F.P v) q → F.P w = F.P v) :
    ValuesWrt (questionOf q) π F := by
  intro 𝒪 _ hmeas S hS o ho
  exact valuesWrt_questionOf_core hπ hST 𝒪 hmeas S hS
    (fun w v hw hv h => hS.1.2 w v (hdet w v hw hv h)) o ho

/-- **The two-cell equivalence on row-determined frames**: for `π ∈ stdSimplex` and rows
determined by `P_w(q)` on the support, local Total Trust w.r.t. `{q,¬q}` ⟺ local Value w.r.t.
`{q,¬q}` ⟺ the Simple-Trust cuts at `q`.
Source: [[Deference Done Better]] §5 l. 398; mandate T4(b)
Kind: C
Fidelity: weaker: under `hdet` (see `tie4`)
Hyps: (a) `π ∈ stdSimplex ℝ W`, `hdet` -/
theorem localTotalTrust_iff_localValue_two_cell {q : Finset W} {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (hdet : ∀ w v, 0 < π w → 0 < π v → mass (F.P w) q = mass (F.P v) q → F.P w = F.P v) :
    TotalTrustWrt (questionOf q) π F ↔ ValuesWrt (questionOf q) π F :=
  ⟨fun h => valuesWrt_questionOf_of_simpleTrustOn hπ.1 ((totalTrustWrt_questionOf_iff hπ.1).1 h)
    hdet, fun h => valuesWrt_imp_totalTrustWrt hπ h⟩

/-- **Weak two-cell local Value from Simple Trust, unconditionally**: the strategy that picks,
at each world, a maximizer of `β_O + b_O·P_w(q)` chosen as a function of `P_w(q)` alone is
recommended and tie-consistent, so the core applies. This is fn 65's conjecture, two-cell case,
in the weak reading.
Source: [[Deference Done Better]] fn 65 l. 1237 (weak reading); this package
Kind: P
Fidelity: variant: Weak Value (some recommended strategy) in place of fn 64's Value
Hyps: (a) `∀ w, 0 ≤ π w`, `SimpleTrustOn q π F` -/
theorem weakValuesWrt_questionOf_of_simpleTrustOn {q : Finset W} {π : W → ℝ}
    (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (hST : SimpleTrustOn q π F) :
    WeakValuesWrt (questionOf q) π F := by
  intro 𝒪 hne hmeas
  have haff : ∀ o' ∈ 𝒪, ∃ β b : ℝ, ∀ w, o' w = β + b * ind q w :=
    fun o' ho' => exists_affine_of_measurableWrt_questionOf (hmeas o' ho')
  choose! β b hβb using haff
  have hE : ∀ o' ∈ 𝒪, ∀ w, E (F.P w) o' = β o' + b o' * mass (F.P w) q := by
    intro o' ho' w
    have e : o' = fun v => β o' + b o' * ind q v := funext (hβb o' ho')
    conv_lhs => rw [e]
    exact E_affine_ind (F.P_mem w) q (β o') (b o')
  have hex : ∀ x : ℝ, ∃ o ∈ 𝒪, ∀ o' ∈ 𝒪, β o' + b o' * x ≤ β o + b o * x :=
    fun x => 𝒪.exists_max_image (fun o => β o + b o * x) hne
  choose sel hsel_mem hsel_max using hex
  set S : W → (W → ℝ) := fun w => sel (mass (F.P w) q) with hSdef
  have hSrec : F.Recommended 𝒪 S := by
    refine ⟨⟨fun w => hsel_mem _, fun w v hwv => ?_⟩, fun w o' ho' => ?_⟩
    · simp only [hSdef, hwv]
    · rw [hE o' ho' w, hE (S w) (hsel_mem _) w]
      exact hsel_max _ o' ho'
  refine ⟨S, hSrec, fun o ho => ?_⟩
  exact valuesWrt_questionOf_core hπ hST 𝒪 hmeas S hSrec
    (fun w v _ _ h => by simp only [hSdef, h]) o ho

/-! ## fn 66's frame values with respect to `{q, ¬q}` -/

/-- fn 66's rows are determined by `P_w(q)` on the support (the two rows with `P(q) = 3/5`
coincide).
Source: [[Deference Done Better]] fn 66 l. 1239
Kind: L
Fidelity: n/a -/
theorem fn66_rows_det : ∀ w v, 0 < quarter w → 0 < quarter v →
    mass (fn66.P w) q66 = mass (fn66.P v) q66 → fn66.P w = fn66.P v := by
  obtain ⟨m0, m1, m2, m3⟩ := fn66_mass_q
  intro w v _ _ h
  fin_cases w <;> fin_cases v <;>
    first
      | rfl
      | (norm_num [m0, m1, m2, m3] at h)

/-- **fn 66, local Value holds** (DDB's "in fact, `π` values this frame with respect to `Q`"):
by the two-cell theorem, since the rows are determined by `P_w(q)`.
Source: [[Deference Done Better]] fn 66 l. 1239; [[legitimacy]] R2.3 l. 58 (E4)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn66_valuesWrt : ValuesWrt (questionOf q66) quarter fn66 :=
  valuesWrt_questionOf_of_simpleTrustOn (fun _ => by norm_num [quarter])
    ((totalTrustWrt_questionOf_iff (fun _ => by norm_num [quarter])).1 fn66_totalTrustWrt)
    fn66_rows_det

/-- **fn 66, the package's canonical witness, assembled**: an immodest frame and a deferrer with
local Total Trust and local Value on `{q, ¬q}` but without local Reflection on `{q, ¬q}` — the
local equality form is strictly stronger than local Total Trust even under immodesty.
Source: [[Deference Done Better]] fn 66 l. 1239; corr-wf14-027; fixpoint-lit-074
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn66_witness : fn66.Immodest ∧ quarter ∈ stdSimplex ℝ (Fin 4) ∧
    ¬ ReflectsWrt (questionOf q66) quarter fn66 ∧ TotalTrustWrt (questionOf q66) quarter fn66 ∧
    ValuesWrt (questionOf q66) quarter fn66 :=
  ⟨fn66_immodest, ⟨fun _ => by norm_num [quarter], by norm_num [Fin.sum_univ_four, quarter]⟩,
    fn66_not_reflectsWrt, fn66_totalTrustWrt, fn66_valuesWrt⟩

end

end Cleanroom.Corrigibility.CorrLegitGeneral
