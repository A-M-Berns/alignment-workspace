import Cleanroom.Lit.LitWeathersonFrames.CFrame
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The pooling constraints on a countable carrier (S3): Zhang with finite range

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). The four constraints of §1 on
an arbitrary carrier `W` with `tsum`s: deference `DefersC`, the closed-interval betweenness
`Between4C` (and its upper half `BetweenUpperC`), agreement on the support `AgreeAEC`. The
summability guard is `Bdd Y` (Zhang's `Y = 𝟙_p`) together with `Summable C`.

**S3.** Zhang's theorem with constraint 5 as the paper means it — the experts take values in a
finite set `S` on the support of `C` — on any carrier (`zhang_countable_finiteRange`): the
finite-carrier extremal proof (`Pooling.lean`) goes through verbatim, the fiber decomposition of a
level set now running over the finite `S` and the null remainder. Finiteness of the *range*, not
of the carrier, is what the proof uses; `Chain.lean` (E1) exhibits a countable-range model on
`ℤ × Bool` satisfying every other hypothesis of this theorem with `A ≠ B` everywhere.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

open Finset

noncomputable section

variable {W : Type}

/-! ## The constraints -/

/-- **Total deference** to an expert on a countable carrier, product form:
`∀ a, ∑' w, C w · (Y w − a) · 𝟙[A w = a] = 0`.
Source: [[Deference and Infinite Frames]] §1 l. 41, constraints 1–2 (l. 56–57)
Kind: D
Fidelity: exact (product form; summable under `Bdd Y`, `Summable C`) -/
def DefersC (C Y A : W → ℝ) : Prop :=
  ∀ a, ∑' w, C w * (Y w - a) * (if A w = a then 1 else 0) = 0

/-- **Zhang's constraint 4, reading R-closed**, on a countable carrier.
Source: [[Deference and Infinite Frames]] §1 l. 59
Kind: D
Fidelity: variant: closed-interval reading (as `Between4`) -/
def Between4C (C Y A B : W → ℝ) : Prop :=
  ∀ a b, ∃ c, ∑' w, C w * (Y w - c) * (if A w = a ∧ B w = b then 1 else 0) = 0 ∧
    min a b ≤ c ∧ c ≤ max a b ∧ (a ≠ b → min a b < c ∧ c < max a b)

/-- The upper half of R-closed on a countable carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def BetweenUpperC (C Y A B : W → ℝ) : Prop :=
  ∀ a b, ∃ c, ∑' w, C w * (Y w - c) * (if A w = a ∧ B w = b then 1 else 0) = 0 ∧
    c ≤ max a b ∧ (a ≠ b → c < max a b)

/-- The experts agree on the support of `C`.
Source: [[Deference and Infinite Frames]] §1 l. 49 (constraint 3, negated)
Kind: D
Fidelity: exact -/
def AgreeAEC (C A B : W → ℝ) : Prop := ∀ w, 0 < C w → A w = B w

/-- **Constraint 5 as the paper means it**: on the support of `C` both experts take values in
the finite set `S` (equivalent to `C(A ∈ S ∧ B ∈ S) = 1`, `finiteRange_of_mass_eq_one`).
Source: [[Deference and Infinite Frames]] §1 l. 60 (constraint 5)
Kind: D
Fidelity: exact (support form) -/
def FiniteRangeOn (C A B : W → ℝ) (S : Finset ℝ) : Prop := ∀ w, 0 < C w → A w ∈ S ∧ B w ∈ S

/-! ## Plumbing -/

/-- R-closed implies its upper half.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Between4C.upper {C Y A B : W → ℝ} (h : Between4C C Y A B) : BetweenUpperC C Y A B := by
  intro a b
  obtain ⟨c, hc, -, hle, hlt⟩ := h a b
  exact ⟨c, hc, hle, fun hab => (hlt hab).2⟩

/-- The upper half is symmetric in the two experts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem BetweenUpperC.symm {C Y A B : W → ℝ} (h : BetweenUpperC C Y A B) :
    BetweenUpperC C Y B A := by
  intro b a
  obtain ⟨c, hc, hle, hlt⟩ := h a b
  refine ⟨c, ?_, by rwa [max_comm], fun hne => by rw [max_comm]; exact hlt (Ne.symm hne)⟩
  exact (tsum_congr fun w => by simp only [and_comm]).trans hc

/-- Symmetry of the finite-range constraint.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem FiniteRangeOn.symm {C A B : W → ℝ} {S : Finset ℝ} (h : FiniteRangeOn C A B S) :
    FiniteRangeOn C B A S := fun w hw => ⟨(h w hw).2, (h w hw).1⟩

/-- `C w · g w · 𝟙[p w]` is summable for bounded `g` and summable nonnegative `C`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem summable_mul_ind {C : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C) {g : W → ℝ}
    {M : ℝ} (hg : ∀ w, |g w| ≤ M) (p : W → Prop) [DecidablePred p] :
    Summable (fun w => C w * g w * (if p w then 1 else 0)) := by
  refine Summable.of_norm_bounded (g := fun w => C w * M) (hCs.mul_right M) fun w => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hC w)]
  have h1 : |(if p w then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  calc C w * |g w| * |(if p w then (1:ℝ) else 0)| ≤ C w * |g w| * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (hC w) (abs_nonneg _))
    _ ≤ C w * M := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hg w) (hC w)

/-- The mass of a cell, `∑' w, C w · 𝟙[A w = a ∧ B w = b]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def cellMass (C A B : W → ℝ) (a b : ℝ) : ℝ := ∑' w, C w * (if A w = a ∧ B w = b then 1 else 0)

/-- Cell masses are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellMass_nonneg {C : W → ℝ} (hC : ∀ w, 0 ≤ C w) (A B : W → ℝ) (a b : ℝ) :
    0 ≤ cellMass C A B a b :=
  tsum_nonneg fun w => mul_nonneg (hC w) (by split_ifs <;> norm_num)

/-- A supported world in a cell makes the cell's mass positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellMass_pos {C : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C) {A B : W → ℝ}
    {w : W} (hw : 0 < C w) : 0 < cellMass C A B (A w) (B w) := by
  unfold cellMass
  have hs : Summable (fun v => C v * (if A v = A w ∧ B v = B w then (1:ℝ) else 0)) :=
    summable_mul_ind hC hCs (g := fun _ => 1) (M := 1) (fun _ => by simp) _ |>.congr
      fun v => by ring
  refine hs.tsum_pos (fun v => mul_nonneg (hC v) (by split_ifs <;> norm_num)) w ?_
  simp [hw]

/-- The contribution of a cell to the deference sum at threshold `M` is `(c − M) · mass(cell)`
when the cell's posterior is `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cell_tsum_shift {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C)
    {MY : ℝ} (hY : ∀ w, |Y w| ≤ MY) {a b c M : ℝ}
    (hc : ∑' w, C w * (Y w - c) * (if A w = a ∧ B w = b then 1 else 0) = 0) :
    ∑' w, C w * (Y w - M) * (if A w = a ∧ B w = b then 1 else 0) =
      (c - M) * cellMass C A B a b := by
  have h1 : Summable (fun w => C w * (Y w - c) * (if A w = a ∧ B w = b then (1:ℝ) else 0)) :=
    summable_mul_ind hC hCs (g := fun w => Y w - c) (M := MY + |c|)
      (fun w => le_trans (abs_sub _ _) (add_le_add (hY w) le_rfl)) _
  have h2 : Summable (fun w => (c - M) * (C w * (if A w = a ∧ B w = b then (1:ℝ) else 0))) :=
    (summable_mul_ind hC hCs (g := fun _ => 1) (M := 1) (fun _ => by simp) _ |>.congr
      fun v => by ring).mul_left _
  have : (fun w => C w * (Y w - M) * (if A w = a ∧ B w = b then (1:ℝ) else 0)) =
      fun w => C w * (Y w - c) * (if A w = a ∧ B w = b then (1:ℝ) else 0) +
        (c - M) * (C w * (if A w = a ∧ B w = b then (1:ℝ) else 0)) := by
    funext w; ring
  rw [this, h1.tsum_add h2, hc, zero_add, tsum_mul_left]
  rfl

/-- **Fiber decomposition of a level set over a finite range**: if every supported world has
`B w ∈ S`, the deference sum over `[A = a]` is the sum over `b ∈ S` of the cell sums.
Source: none: infrastructure (the countable form of `sum_lev₂_eq_sum_lev`)
Kind: L
Fidelity: n/a -/
theorem tsum_lev_eq_sum_cells {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C)
    {MY : ℝ} (hY : ∀ w, |Y w| ≤ MY) {S : Finset ℝ} (h5 : ∀ w, 0 < C w → B w ∈ S)
    (a M : ℝ) :
    ∑' w, C w * (Y w - M) * (if A w = a then 1 else 0) =
      ∑ b ∈ S, ∑' w, C w * (Y w - M) * (if A w = a ∧ B w = b then 1 else 0) := by
  rw [← Summable.tsum_finsetSum fun b _ => summable_mul_ind hC hCs (g := fun w => Y w - M) (M := MY + |M|)
    (fun w => le_trans (abs_sub _ _) (add_le_add (hY w) le_rfl)) _]
  refine tsum_congr fun w => ?_
  rcases (hC w).lt_or_eq with hw | hw
  · have hB := h5 w hw
    by_cases hA : A w = a
    · simp only [hA, if_true, true_and]
      simp [mul_ite, Finset.sum_ite_eq, hB]
    · simp [hA]
  · simp [← hw]

/-- **The extremal step on a countable carrier**: if `C ≥ 0` summable defers to `A`, the upper
half of constraint 4 holds, `B` takes values in the finite `S` on the support, and `M` bounds
`max (A w) (B w)` over every supported disagreeing world, then no supported world has `A w = M`
and `B w ≠ M`.
Source: [[Deference and Infinite Frames]] §1 l. 88, made a proof (countable form of
`no_top_disagreement`)
Kind: L
Fidelity: n/a -/
theorem no_top_disagreement_C {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C)
    {MY : ℝ} (hY : ∀ w, |Y w| ≤ MY) (hA : DefersC C Y A) (h4 : BetweenUpperC C Y A B)
    {S : Finset ℝ} (h5 : ∀ w, 0 < C w → B w ∈ S) (M : ℝ)
    (hM : ∀ w, 0 < C w → A w ≠ B w → max (A w) (B w) ≤ M) :
    ∀ w, 0 < C w → A w = M → A w = B w := by
  intro w₀ hw₀ hA₀
  by_contra hne
  have hdef := hA M
  rw [tsum_lev_eq_sum_cells hC hCs hY h5 M M] at hdef
  have hcell : ∀ b, ∑' w, C w * (Y w - M) * (if A w = M ∧ B w = b then 1 else 0) ≤ 0 := by
    intro b
    obtain ⟨c, hc, hle, hlt⟩ := h4 M b
    rw [cell_tsum_shift hC hCs hY hc]
    rcases (cellMass_nonneg hC A B M b).lt_or_eq with hpos | hzero
    · obtain ⟨w, hw, hCw⟩ : ∃ w, (A w = M ∧ B w = b) ∧ 0 < C w := by
        by_contra hall
        push Not at hall
        have : cellMass C A B M b = 0 := by
          unfold cellMass
          have hz : ∀ w, C w * (if A w = M ∧ B w = b then (1:ℝ) else 0) = 0 := by
            intro w
            by_cases hcell : A w = M ∧ B w = b
            · have : C w = 0 := le_antisymm (hall w hcell) (hC w)
              simp [this]
            · simp [hcell]
          simp [hz]
        linarith
      have hbM : b ≤ M := by
        by_cases hab : A w = B w
        · rw [← hw.2, ← hab, hw.1]
        · have := hM w hCw hab
          rw [hw.1, hw.2] at this
          exact le_trans (le_max_right _ _) this
      have : c ≤ M := by
        have := hle; rwa [max_eq_left hbM] at this
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
    · rw [← hzero, mul_zero]
  have hneg : ∑' w, C w * (Y w - M) * (if A w = M ∧ B w = B w₀ then 1 else 0) < 0 := by
    obtain ⟨c, hc, hle, hlt⟩ := h4 M (B w₀)
    rw [cell_tsum_shift hC hCs hY hc]
    have hb : B w₀ < M := by
      have := hM w₀ hw₀ hne
      rw [hA₀] at this
      exact lt_of_le_of_ne (le_trans (le_max_right _ _) this) (fun h => hne (by rw [hA₀, h]))
    have hcM : c < M := by
      have := hlt hb.ne'
      rwa [max_eq_left hb.le] at this
    have hpos : 0 < cellMass C A B M (B w₀) := by
      have := cellMass_pos hC hCs (A := A) (B := B) hw₀
      rwa [hA₀] at this
    exact mul_neg_of_neg_of_pos (by linarith) hpos
  have hzero := (sum_eq_zero_iff_of_nonpos (fun b _ => hcell b)).1 hdef (B w₀) (h5 w₀ hw₀)
  linarith

/-- **S3. Zhang's theorem with finite range on any carrier.** If `C ≥ 0` is summable, `Y` is
bounded, `C` defers to `A` and to `B`, the upper half of constraint 4 holds, and on the support
both experts take values in a finite set `S` (constraint 5 as the paper means it), then
`A = B` on the support. Same extremal proof as `zhang_finite_upper`: the maximum is taken over
the finitely many attained values in `S`, and the fiber decomposition of a level set runs over
`S` plus a null remainder. Finiteness of the **range** is all that is used; `Chain.lean` (E1)
shows it cannot be weakened to countability.
Source: [[Deference and Infinite Frames]] §1 ll. 54–61 (Zhang; constraint 5 l. 60); inventory
022, 024; mandate S3
Kind: P
Fidelity: stronger: only the upper half of constraint 4, any bounded target `Y`, any carrier
Hyps: (a) all -/
theorem zhang_countable_finiteRange {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C)
    (hY : Bdd Y) (hA : DefersC C Y A) (hB : DefersC C Y B) (h4 : BetweenUpperC C Y A B)
    {S : Finset ℝ} (h5 : FiniteRangeOn C A B S) : AgreeAEC C A B := by
  classical
  obtain ⟨MY, hY⟩ := hY
  by_contra hnot
  simp only [AgreeAEC, not_forall] at hnot
  obtain ⟨w₁, hw₁, hne₁⟩ := hnot
  set V : Finset ℝ := S.filter (fun v => ∃ w, 0 < C w ∧ A w ≠ B w ∧ max (A w) (B w) = v) with hV
  have hmemS : ∀ w, 0 < C w → max (A w) (B w) ∈ S := by
    intro w hw
    rcases le_total (A w) (B w) with h | h
    · rw [max_eq_right h]; exact (h5 w hw).2
    · rw [max_eq_left h]; exact (h5 w hw).1
  have hV_ne : V.Nonempty := ⟨max (A w₁) (B w₁), by
    simp only [hV, mem_filter]
    exact ⟨hmemS w₁ hw₁, w₁, hw₁, hne₁, rfl⟩⟩
  obtain ⟨M, hMV, hmax⟩ := exists_max_image V id hV_ne
  simp only [hV, mem_filter] at hMV
  obtain ⟨-, w₀, hw₀, hne₀, hM₀⟩ := hMV
  have hM : ∀ w, 0 < C w → A w ≠ B w → max (A w) (B w) ≤ M := by
    intro w hw hne
    exact hmax _ (by simp only [hV, mem_filter]; exact ⟨hmemS w hw, w, hw, hne, rfl⟩)
  have hM' : ∀ w, 0 < C w → B w ≠ A w → max (B w) (A w) ≤ M :=
    fun w hw hne => by rw [max_comm]; exact hM w hw (Ne.symm hne)
  rcases le_total (B w₀) (A w₀) with hle | hle
  · have hA₀ : A w₀ = M := by rw [← hM₀, max_eq_left hle]
    exact hne₀ (no_top_disagreement_C hC hCs hY hA h4 (fun w hw => (h5 w hw).2) M hM w₀ hw₀ hA₀)
  · have hB₀ : B w₀ = M := by rw [← hM₀, max_eq_right hle]
    exact hne₀ (no_top_disagreement_C hC hCs hY hB h4.symm (fun w hw => (h5 w hw).1) M hM'
      w₀ hw₀ hB₀).symm

/-- **S3, reading R-closed**: the corollary with the full closed-interval constraint.
Source: [[Deference and Infinite Frames]] §1 ll. 54–61; mandate S3
Kind: L
Fidelity: variant: closed-interval reading
Hyps: (a) all -/
theorem zhang_countable_finiteRange' {C Y A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : Summable C)
    (hY : Bdd Y) (hA : DefersC C Y A) (hB : DefersC C Y B) (h4 : Between4C C Y A B)
    {S : Finset ℝ} (h5 : FiniteRangeOn C A B S) : AgreeAEC C A B :=
  zhang_countable_finiteRange hC hCs hY hA hB h4.upper h5

/-- The paper's form of constraint 5, `C(A ∈ S ∧ B ∈ S) = 1`, implies the support form (for a
distribution `C`).
Source: [[Deference and Infinite Frames]] §1 l. 60
Kind: L
Fidelity: n/a -/
theorem finiteRange_of_mass_eq_one {C A B : W → ℝ} (hC : ∀ w, 0 ≤ C w) (hCs : HasSum C 1)
    {S : Finset ℝ} (h : ∑' w, C w * (if A w ∈ S ∧ B w ∈ S then 1 else 0) = 1) :
    FiniteRangeOn C A B S := by
  intro w hw
  by_contra hnot
  have hs : Summable (fun v => C v * (if A v ∈ S ∧ B v ∈ S then (1:ℝ) else 0)) :=
    summable_mul_ind hC hCs.summable (g := fun _ => 1) (M := 1) (fun _ => by simp) _ |>.congr
      fun v => by ring
  have hlt : ∑' v, C v * (if A v ∈ S ∧ B v ∈ S then (1:ℝ) else 0) < ∑' v, C v := by
    refine hs.tsum_lt_tsum (i := w) (fun v => ?_) ?_ hCs.summable
    · split_ifs <;> simp [hC v]
    · simp [hnot, hw]
  rw [h, hCs.tsum_eq] at hlt
  exact lt_irrefl _ hlt

end

end Cleanroom.Lit.LitWeathersonFrames
