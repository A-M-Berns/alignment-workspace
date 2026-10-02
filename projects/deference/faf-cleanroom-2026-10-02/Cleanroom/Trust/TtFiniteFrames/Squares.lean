import Cleanroom.Trust.TtFiniteFrames.Chains

/-!
# The composition squares of `route-transitivity` §5.1

Package `tt-finite-frames`, Targets S1 and S2.

The correctly shaped square: one prior `π` (H), a partition `c` (future-H's information `𝔐`, with
`m X := E_π[X | 𝔐]`) and a partition `d` (A's information `𝔄`, with `a X := E_π[m X | 𝔄]`).
Link 1 (`π` totally trusts `m`) is T1; Link 2 is exact calibration `a = E_π[m | 𝔄]`, which holds
by construction. The question is whether `π` totally trusts `a`.

* **Theorem 5.1 (nesting suffices)**: if `a X` is `𝔐`-measurable then
  `t · π(a X ≥ t) ≤ ∑_{a X ≥ t} π X` — two tower steps. Frame form: `A := D.comp C` has quote
  `a X`; when `c` refines `d`, `D.comp C = D` (the tower), so the frame statement collapses to T1;
  the content of 5.1 is the per-quote version with the weaker hypothesis.
* **Witness 5.2 (refuted without nesting)**: `Fin 4`, uniform, `c = {{0,1},{2},{3}}`,
  `d = {{0,2},{1,3}}`, `X = (0,1,1,0)`: `m = (1/2,1/2,1,0)`, `a = (3/4,1/4,3/4,1/4)`, and at
  `t = 3/4` the mass is `−1/8`, so `π` does not totally trust `A`.
* **S2**: the chain square's Link 2 ("future-H totally trusts A") and the calibration square's
  Link 2 are independent: Witness 5.2 has calibration without trust (future-H at world `0` does
  not totally trust `A`); the omniscient expert has trust from every prior without calibration.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Composition of frames and the conditional expectations -/

/-- **Composition of frames**: `(D.comp C)_w = ∑ v, D_w(v) · C_v` — `D`'s expectation of `C`'s
row. Its quote of `X` is `E_{D_w}(v ↦ E_{C_v}(X))`.
Source: [[route-transitivity]] §5.1 (the frame of `a = E[m | 𝔄]`)
Kind: D
Fidelity: exact -/
def Frame.comp (D C : Frame W) : Frame W where
  P := fun w u => ∑ v, D.P w v * C.P v u
  P_mem := fun w => by
    refine ⟨fun u => sum_nonneg fun v _ => mul_nonneg (D.P_nonneg w v) (C.P_nonneg v u), ?_⟩
    rw [sum_comm]
    simp only [← mul_sum, C.P_sum, mul_one]
    exact D.P_sum w

/-- The tower: the composite's estimate of `X` is `D`'s estimate of `C`'s estimates.
Source: [[route-transitivity]] §5.1
Kind: L
Fidelity: n/a -/
theorem Frame.comp_E (D C : Frame W) (w : W) (X : W → ℝ) :
    E ((Frame.comp D C).P w) X = E (D.P w) (fun v => E (C.P v) X) := by
  unfold E Frame.comp
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro v _; apply sum_congr rfl; intro u _; ring

/-- `m X`: future-H's estimate, the `c`-conditional expectation of `X` as a random variable.
Source: [[route-transitivity]] §5.1 (`m := E_π[X | 𝔐]`)
Kind: D
Fidelity: exact -/
def condExp {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w) (c : W → ι)
    (X : W → ℝ) : W → ℝ :=
  fun v => E ((Frame.ofPartition π hpos c).P v) X

/-- `m X` is constant on the cells of `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condExp_const {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w) (c : W → ι)
    (X : W → ℝ) {v v' : W} (h : c v = c v') : condExp π hpos c X v = condExp π hpos c X v' := by
  unfold condExp
  rw [(Frame.ofPartition_P_inj π hpos c v v').2 h]

/-- **Tower over a partition**: on any union of `c`-cells `A`, `∑_{A} π X = ∑_{A} π (m X)`.
Source: [[route-transitivity]] §5.1 ("tower over `𝔐`")
Kind: L
Fidelity: n/a -/
theorem sum_condExp_of_closed {ι : Type} [DecidableEq ι] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (c : W → ι) (X : W → ℝ) {A : Finset W} (hA : ∀ w ∈ A, ∀ v, c v = c w → v ∈ A) :
    ∑ w ∈ A, π w * X w = ∑ w ∈ A, π w * condExp π hpos c X w := by
  have hK := Corr.ofMap_partitional c
  -- `A` is the union of the cells it meets; regroup both sides
  have hsplit : ∀ g : W → ℝ, ∑ w ∈ A, g w = ∑ C ∈ A.image (Corr.ofMap c), ∑ w ∈ C, g w := by
    intro g
    rw [← sum_fiberwise_of_maps_to (g := Corr.ofMap c) (t := A.image (Corr.ofMap c))
      (fun w hw => mem_image_of_mem _ hw)]
    apply sum_congr rfl
    intro C hC
    obtain ⟨v, hvA, rfl⟩ := mem_image.1 hC
    apply sum_congr _ (fun _ _ => rfl)
    ext w
    simp only [mem_filter, Corr.mem_ofMap]
    constructor
    · rintro ⟨_, h⟩
      exact Corr.mem_ofMap.1 ((hK.mem_iff_eq).2 h)
    · intro h
      have hmem : w ∈ Corr.ofMap c v := Corr.mem_ofMap.2 h
      exact ⟨hA v hvA w h, (hK.mem_iff_eq).1 hmem⟩
  rw [hsplit, hsplit]
  apply sum_congr rfl
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  have hconst : ∀ w ∈ Corr.ofMap c v, condExp π hpos c X w = condExp π hpos c X v :=
    fun w hw => condExp_const π hpos c X (Corr.mem_ofMap.1 hw)
  rw [sum_congr rfl (fun w hw => by rw [hconst w hw] :
    ∀ w ∈ Corr.ofMap c v, π w * condExp π hpos c X w = π w * condExp π hpos c X v)]
  rw [← sum_mul, mul_comm]
  unfold condExp
  exact (Frame.ofPartition_E π hpos c v X).symm

/-! ## Theorem 5.1 and its collapse -/

/-- **Theorem 5.1 (nesting suffices), per quote.** If A's quote `a X` is `𝔐`-measurable
(constant on `c`-cells), then for every threshold `t`, `t · π(a X ≥ t) ≤ ∑_{a X ≥ t} π X`. Here
`a X = E_π[m X | 𝔄]` is built from the partition `d`, so calibration (Link 2) holds by
construction; the hypothesis is the measurability alone. Proof: tower over `c` (the event is a
union of `c`-cells by the hypothesis), tower over `d` (the event is a union of `d`-cells since
`a X` is `d`-measurable), then `a X ≥ t` on the event.
Source: [[route-transitivity]] §5.1 Theorem 5.1; vq-wiki-064
Kind: P
Fidelity: exact
Hyps: (a) `hpos`, `hmeas` (the theorem's hypothesis) -/
theorem thm51 {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (π : W → ℝ) (hpos : ∀ w, 0 < π w)
    (c : W → ι) (d : W → κ) (X : W → ℝ)
    (hmeas : ∀ v v', c v = c v' →
      condExp π hpos d (condExp π hpos c X) v = condExp π hpos d (condExp π hpos c X) v')
    (t : ℝ) :
    t * mass π (univ.filter (fun w => t ≤ condExp π hpos d (condExp π hpos c X) w)) ≤
      ∑ w ∈ univ.filter (fun w => t ≤ condExp π hpos d (condExp π hpos c X) w), π w * X w := by
  set a := condExp π hpos d (condExp π hpos c X) with ha
  set A := univ.filter (fun w => t ≤ a w) with hA
  -- tower over `c`
  have h1 : ∑ w ∈ A, π w * X w = ∑ w ∈ A, π w * condExp π hpos c X w := by
    apply sum_condExp_of_closed
    intro w hw v hv
    rw [hA, mem_filter] at hw ⊢
    exact ⟨mem_univ _, by rw [hmeas v w hv]; exact hw.2⟩
  -- tower over `d`
  have h2 : ∑ w ∈ A, π w * condExp π hpos c X w = ∑ w ∈ A, π w * a w := by
    apply sum_condExp_of_closed
    intro w hw v hv
    rw [hA, mem_filter] at hw ⊢
    exact ⟨mem_univ _, by rw [ha, condExp_const π hpos d _ hv]; exact hw.2⟩
  rw [h1, h2, mass, mul_sum]
  apply sum_le_sum
  intro w hw
  rw [hA, mem_filter] at hw
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hw.2 (hpos w).le

/-- **The frame form collapses**: when `c` refines `d` (`d` factors through `c`), the composite
`D.comp C` of the two partition experts is `D` itself (the tower `E[E[X | 𝔐] | 𝔄] = E[X | 𝔄]`),
so "`π` totally trusts `D.comp C`" is T1 for `d`.
Source: [[route-transitivity]] §5.1 (mandate S1: "state the collapse as a lemma")
Kind: P
Fidelity: exact
Hyps: (a) `hpos`, `href` -/
theorem comp_ofPartition_eq_of_refines {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (π : W → ℝ)
    (hpos : ∀ w, 0 < π w) {c : W → ι} {d : W → κ} (href : Blackwell.Refines c d) :
    (Frame.comp (Frame.ofPartition π hpos d) (Frame.ofPartition π hpos c)).P =
      (Frame.ofPartition π hpos d).P := by
  obtain ⟨g, rfl⟩ := href
  funext w u
  simp only [Frame.comp, Frame.ofPartition_P_apply]
  by_cases hu : (g ∘ c) u = (g ∘ c) w
  · rw [if_pos hu]
    -- only `v` in the `c`-cell of `u` contribute; they all lie in the `d`-cell of `w`
    have hcell : ∀ v, (if (g ∘ c) v = (g ∘ c) w then π v else 0) / mass π (Corr.ofMap (g ∘ c) w) *
        ((if c u = c v then π u else 0) / mass π (Corr.ofMap c v)) =
        if c v = c u then π v / mass π (Corr.ofMap (g ∘ c) w) * (π u / mass π (Corr.ofMap c u))
        else 0 := by
      intro v
      by_cases hcv : c v = c u
      · have h1 : (g ∘ c) v = (g ∘ c) w := by
          show g (c v) = g (c w)
          rw [hcv]
          exact hu
        have h2 : Corr.ofMap c v = Corr.ofMap c u := by
          ext x; simp [Corr.mem_ofMap, hcv]
        rw [if_pos h1, if_pos hcv.symm, if_pos hcv, h2]
      · have h2 : (if c u = c v then π u else 0) = 0 := if_neg (fun h => hcv h.symm)
        rw [h2, zero_div, mul_zero, if_neg hcv]
    rw [Finset.sum_congr (rfl : (univ : Finset W) = univ) (fun v _ => hcell v), ← sum_filter]
    have hfilt : univ.filter (fun v => c v = c u) = Corr.ofMap c u := by
      ext v; simp [Corr.mem_ofMap]
    rw [hfilt]
    have hsum : ∑ v ∈ Corr.ofMap c u, π v / mass π (Corr.ofMap (g ∘ c) w) *
        (π u / mass π (Corr.ofMap c u)) =
        (∑ v ∈ Corr.ofMap c u, π v) / mass π (Corr.ofMap c u) *
          (π u / mass π (Corr.ofMap (g ∘ c) w)) := by
      rw [sum_div, sum_mul]
      apply sum_congr rfl
      intro v _
      ring
    have hm : (∑ v ∈ Corr.ofMap c u, π v) = mass π (Corr.ofMap c u) := rfl
    rw [hsum, hm, div_self (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional c).1 u).ne',
      one_mul]
  · rw [if_neg hu, zero_div]
    apply sum_eq_zero
    intro v _
    by_cases hcv : c u = c v
    · have : ¬ (g ∘ c) v = (g ∘ c) w := by
        show ¬ g (c v) = g (c w)
        rw [← hcv]
        exact hu
      rw [if_neg this, zero_div, zero_mul]
    · rw [if_neg hcv, zero_div, mul_zero]

/-- **Theorem 5.1, frame form, under nesting**: if `c` refines `d` then `π` totally trusts the
composite `D.comp C` — which is T1 for `d`, by the collapse.
Source: [[route-transitivity]] §5.1 Theorem 5.1 (frame form)
Kind: C (collapse + T1)
Fidelity: exact (of the frame form; the content of 5.1 is `thm51`)
Hyps: (a) `hpos`, `href` -/
theorem totalTrust_comp_of_refines {ι κ : Type} [DecidableEq ι] [DecidableEq κ] (π : W → ℝ)
    (hpos : ∀ w, 0 < π w) {c : W → ι} {d : W → κ} (href : Blackwell.Refines c d) :
    TotalTrust π (Frame.comp (Frame.ofPartition π hpos d) (Frame.ofPartition π hpos c)) :=
  totalTrust_of_P_eq (comp_ofPartition_eq_of_refines π hpos href).symm
    (totalTrust_ofPartition hpos d)

/-! ## Theorem 5.1 at a quote measurable for a common coarsening: T1 for that coarsening

(Repair round 2, audit r2 adversarial N3(b).) When A's quote `a X = E[E[X ∣ 𝔐] ∣ 𝔄]` is constant
on the cells of a partition `e` that both `𝔐` and `𝔄` refine — for instance the join of the two,
the components of their overlap graph, on which `a X` is constant whenever it is `𝔐`-measurable —
then `a X = E[X ∣ e]`, and `thm51`'s inequality at `(X, t)` is T1's product-form inequality for
`e`'s partition expert at `(X, t)`, even when the composite frame `D.comp C` is not that expert
(`Thm51Inhabitant`). The join is not defined here; `e` is a parameter. -/

/-- **A conditional expectation measurable for a coarser partition is the coarser conditional
expectation.** If `c` refines `e` and `E[X ∣ c]` is constant on `e`-cells, then
`E[X ∣ c] = E[X ∣ e]`: on an `e`-cell (a union of `c`-cells) the tower gives
`∑_cell π · E[X ∣ c] = ∑_cell π X`, and constancy turns the left side into `E[X ∣ c] · π(cell)`.
Source: none: infrastructure (S1; audit r2 adversarial N3(b))
Kind: L
Fidelity: n/a -/
theorem condExp_eq_of_refines_of_const {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (π : W → ℝ) (hpos : ∀ w, 0 < π w) {c : W → ι} {e : W → κ} (href : Blackwell.Refines c e)
    (X : W → ℝ) (hconst : ∀ v v', e v = e v' → condExp π hpos c X v = condExp π hpos c X v') :
    condExp π hpos c X = condExp π hpos e X := by
  obtain ⟨g, rfl⟩ := href
  funext w
  -- the `e`-cell of `w` is a union of `c`-cells
  have hclosed : ∀ u ∈ Corr.ofMap (g ∘ c) w, ∀ v, c v = c u → v ∈ Corr.ofMap (g ∘ c) w := by
    intro u hu v hv
    rw [Corr.mem_ofMap] at hu ⊢
    show g (c v) = g (c w)
    rw [hv]
    exact hu
  have htower := sum_condExp_of_closed π hpos c X hclosed
  have hc : ∀ u ∈ Corr.ofMap (g ∘ c) w, condExp π hpos c X u = condExp π hpos c X w :=
    fun u hu => hconst u w (Corr.mem_ofMap.1 hu)
  have hsum : ∑ u ∈ Corr.ofMap (g ∘ c) w, π u * condExp π hpos c X u =
      condExp π hpos c X w * mass π (Corr.ofMap (g ∘ c) w) := by
    rw [mass, mul_sum]
    apply sum_congr rfl
    intro u hu
    rw [hc u hu, mul_comm]
  have hE := Frame.ofPartition_E π hpos (g ∘ c) w X
  have hm := Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional (g ∘ c)).1 w
  show condExp π hpos c X w = E ((Frame.ofPartition π hpos (g ∘ c)).P w) X
  apply mul_right_cancel₀ hm.ne'
  rw [hE, htower, hsum]

/-- **The tower at the level of quotes**: if `c` refines `e` then `E[E[X ∣ c] ∣ e] = E[X ∣ e]`.
Source: [[route-transitivity]] §5.1 (the tower); none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condExp_condExp_of_refines {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (π : W → ℝ) (hpos : ∀ w, 0 < π w) {c : W → ι} {e : W → κ} (href : Blackwell.Refines c e)
    (X : W → ℝ) : condExp π hpos e (condExp π hpos c X) = condExp π hpos e X := by
  obtain ⟨g, rfl⟩ := href
  funext w
  have hclosed : ∀ u ∈ Corr.ofMap (g ∘ c) w, ∀ v, c v = c u → v ∈ Corr.ofMap (g ∘ c) w := by
    intro u hu v hv
    rw [Corr.mem_ofMap] at hu ⊢
    show g (c v) = g (c w)
    rw [hv]
    exact hu
  have htower := sum_condExp_of_closed π hpos c X hclosed
  have hm := Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional (g ∘ c)).1 w
  show E ((Frame.ofPartition π hpos (g ∘ c)).P w) (condExp π hpos c X) =
    E ((Frame.ofPartition π hpos (g ∘ c)).P w) X
  apply mul_right_cancel₀ hm.ne'
  rw [Frame.ofPartition_E, Frame.ofPartition_E, htower]

/-- **A's quote at a meet-measurable `X` is the common coarsening's quote.** If `e` is a common
coarsening of `𝔐 = c` and `𝔄 = d` (both refine `e`) on whose cells `a X = E[E[X ∣ c] ∣ d]` is
constant, then `a X = E[X ∣ e]`: `a X = E[E[X ∣ c] ∣ e]` by `condExp_eq_of_refines_of_const`
(applied to `d` and `E[X ∣ c]`), then the tower over `c`. The join of `c` and `d` is the finest
such `e`, and `a X` is constant on its cells whenever `thm51`'s hypothesis (`c`-measurability)
holds, since `a X` is always `d`-measurable; the join is not constructed here.
Source: [[route-transitivity]] §5.1; audit r2 adversarial N3(b)
Kind: P
Fidelity: n/a (a reading of 5.1's content; the theorem of record is `thm51`)
Hyps: (a) `hpos`, `hce`, `hde`, `hconst` -/
theorem quote_eq_condExp_of_common_coarsening {ι κ μ : Type} [DecidableEq ι] [DecidableEq κ]
    [DecidableEq μ] (π : W → ℝ) (hpos : ∀ w, 0 < π w) {c : W → ι} {d : W → κ} {e : W → μ}
    (hce : Blackwell.Refines c e) (hde : Blackwell.Refines d e) (X : W → ℝ)
    (hconst : ∀ v v', e v = e v' →
      condExp π hpos d (condExp π hpos c X) v = condExp π hpos d (condExp π hpos c X) v') :
    condExp π hpos d (condExp π hpos c X) = condExp π hpos e X := by
  rw [condExp_eq_of_refines_of_const π hpos hde (condExp π hpos c X) hconst,
    condExp_condExp_of_refines π hpos hce X]

/-- **`thm51`'s inequality is T1's, at a meet-measurable quote.** Under the hypotheses of
`quote_eq_condExp_of_common_coarsening`, `thm51`'s conclusion at every threshold follows from
`totalTrust_ofPartition hpos e` (T1 for `e`) alone: the event `[a X ≥ t]` is `[E_e(X) ≥ t]`, and
`t · π(event) ≤ ∑_event π X` is the product-form Total Trust inequality at `(X, t)` rearranged.
This is the one-line content of "nesting suffices, per quote" (F-S1): on the `X` where A's quote
is constant on the cells of a common coarsening, A quotes as that coarsening's expert would — and
`thm51` there says nothing beyond T1 for it, even when the frame `D.comp C` is not that expert.
Source: [[route-transitivity]] §5.1 Theorem 5.1; audit r2 adversarial N3(b)
Kind: C (T1 + `quote_eq_condExp_of_common_coarsening`)
Fidelity: n/a (an independent route to `thm51`'s conclusion in this case)
Hyps: (a) `hpos`, `hce`, `hde`, `hconst` -/
theorem thm51_of_common_coarsening {ι κ μ : Type} [DecidableEq ι] [DecidableEq κ]
    [DecidableEq μ] (π : W → ℝ) (hpos : ∀ w, 0 < π w) {c : W → ι} {d : W → κ} {e : W → μ}
    (hce : Blackwell.Refines c e) (hde : Blackwell.Refines d e) (X : W → ℝ)
    (hconst : ∀ v v', e v = e v' →
      condExp π hpos d (condExp π hpos c X) v = condExp π hpos d (condExp π hpos c X) v')
    (t : ℝ) :
    t * mass π (univ.filter (fun w => t ≤ condExp π hpos d (condExp π hpos c X) w)) ≤
      ∑ w ∈ univ.filter (fun w => t ≤ condExp π hpos d (condExp π hpos c X) w), π w * X w := by
  rw [quote_eq_condExp_of_common_coarsening π hpos hce hde X hconst]
  have h : 0 ≤ ∑ w, π w * (X w - t) * (if t ≤ condExp π hpos e X w then 1 else 0) :=
    totalTrust_ofPartition hpos e X t
  have hsplit : ∑ w, π w * (X w - t) * (if t ≤ condExp π hpos e X w then 1 else 0) =
      ∑ w ∈ univ.filter (fun w => t ≤ condExp π hpos e X w), π w * X w -
        t * mass π (univ.filter (fun w => t ≤ condExp π hpos e X w)) := by
    rw [mass, mul_sum, ← sum_sub_distrib, sum_filter]
    apply sum_congr rfl
    intro w _
    split_ifs <;> ring
  rw [hsplit] at h
  linarith

/-! ## Witness 5.2 -/

namespace W52

/-- The uniform prior on `Fin 4`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: D
Fidelity: exact -/
def π : Fin 4 → ℝ := fun _ => 1 / 4

/-- Full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hpos : ∀ w, 0 < π w := fun _ => by norm_num [π]

/-- `𝔐`: cells `{0,1}, {2}, {3}`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: D
Fidelity: exact -/
def c : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- `𝔄`: cells `{0,2}, {1,3}`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: D
Fidelity: exact -/
def d : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- `X = (0, 1, 1, 0)`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: D
Fidelity: exact -/
def X : Fin 4 → ℝ := ![0, 1, 1, 0]

/-- Future-H's frame `C` (partition expert on `c`).
Source: [[route-transitivity]] §5.1
Kind: D
Fidelity: exact -/
def C : Frame (Fin 4) := Frame.ofPartition π hpos c

/-- A's information frame `D` (partition expert on `d`).
Source: [[route-transitivity]] §5.1
Kind: D
Fidelity: exact -/
def D : Frame (Fin 4) := Frame.ofPartition π hpos d

/-- `m = (1/2, 1/2, 1, 0)`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: L
Fidelity: n/a -/
theorem m_val : condExp π hpos c X = ![1 / 2, 1 / 2, 1, 0] := by
  funext v
  unfold condExp
  rw [Frame.ofPartition_E_eq']
  fin_cases v <;> simp [Fin.sum_univ_four, π, c, X] <;> norm_num

/-- `a = (3/4, 1/4, 3/4, 1/4)`.
Source: [[route-transitivity]] §5.1 Witness 5.2
Kind: L
Fidelity: n/a -/
theorem a_val : condExp π hpos d (condExp π hpos c X) = ![3 / 4, 1 / 4, 3 / 4, 1 / 4] := by
  rw [m_val]
  funext v
  unfold condExp
  rw [Frame.ofPartition_E_eq']
  fin_cases v <;> simp [Fin.sum_univ_four, π, d] <;> norm_num

/-- The composite's quote of `X` is `a X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem comp_E_eq (w : Fin 4) :
    E ((Frame.comp D C).P w) X = condExp π hpos d (condExp π hpos c X) w := by
  rw [Frame.comp_E]; rfl

/-- **Witness 5.2 (refuted without nesting).** `a X` is not `𝔐`-measurable (`a 0 ≠ a 1` on the
cell `{0,1}`), and at `t = 3/4` the product-form mass of "`π` totally trusts `D.comp C`" is
exactly `−1/8`; so `π` does not totally trust `A` although Link 1 holds and Link 2 (calibration)
holds by construction.
Source: [[route-transitivity]] §5.1 Witness 5.2; vq-wiki-064
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem refuted : ¬ TotalTrust π (Frame.comp D C) ∧
    ∑ w, π w * (X w - 3 / 4) * (if (3 / 4 : ℝ) ≤ E ((Frame.comp D C).P w) X then 1 else 0) =
      -1 / 8 ∧
    condExp π hpos d (condExp π hpos c X) 0 ≠ condExp π hpos d (condExp π hpos c X) 1 := by
  have hgap : ∑ w, π w * (X w - 3 / 4) *
      (if (3 / 4 : ℝ) ≤ E ((Frame.comp D C).P w) X then 1 else 0) = -1 / 8 := by
    simp only [comp_E_eq, a_val]
    simp [Fin.sum_univ_four, π, X]
    norm_num
  refine ⟨fun h => ?_, hgap, ?_⟩
  · have := h X (3 / 4)
    rw [hgap] at this
    norm_num at this
  · rw [a_val]; norm_num

/-! ### S2(a): calibration without trust -/

/-- **Calibration** of an expert frame `A` to future-H's estimate `m`: A's quote of every `X`
equals A's expectation of `m X` (Link 2 of the calibration square, `a = E[m | 𝔄]`). This puts
`A`'s own row in place of the source's `π(· | 𝔄)`: the two coincide for `A = D.comp C`
(`comp_calibrated`, through `comp_E`) and for `omni` (`𝔄` discrete) — the frames S2 uses — but
for an arbitrary `A` it is a modelling choice (e.g. `Calibrated π hpos c C` holds for future-H's
own frame `C` for every `c`, while "`C`'s quote is `E_π[m | 𝔄]`" holds only if `𝔄 = 𝔐`).
Source: [[route-transitivity]] §5.1 Link 2; vq-wiki-2-012
Kind: D
Fidelity: variant: `A`'s row replaces `π(· | 𝔄)`; the two coincide on the frames used (audit
r1 fidelity N5, adversarial N7) -/
def Calibrated {W : Type} [Fintype W] [DecidableEq W] {ι : Type} [DecidableEq ι] (π : W → ℝ)
    (hpos : ∀ w, 0 < π w) (c : W → ι) (A : Frame W) : Prop :=
  ∀ (X : W → ℝ) (w : W), E (A.P w) X = E (A.P w) (condExp π hpos c X)

/-- The composite `D.comp C` is calibrated to `m` (`m` is idempotent).
Source: [[route-transitivity]] §5.1 ("Link 2 holds exactly")
Kind: L
Fidelity: n/a -/
theorem comp_calibrated : Calibrated π hpos c (Frame.comp D C) := by
  intro X w
  rw [Frame.comp_E, Frame.comp_E]
  congr 1
  funext v
  show condExp π hpos c X v = E (C.P v) (condExp π hpos c X)
  unfold C
  rw [Frame.ofPartition_E_eq']
  -- `m X` is constant on the cell of `v`, so its cell average is `m X v`
  have hconst : ∀ u, c u = c v → condExp π hpos c X u = condExp π hpos c X v :=
    fun u hu => condExp_const π hpos c X hu
  have : ∑ u, (if c u = c v then π u * condExp π hpos c X u else 0) =
      condExp π hpos c X v * ∑ u, (if c u = c v then π u else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    split_ifs with hu
    · rw [hconst u hu]; ring
    · ring
  rw [this, mul_div_assoc, div_self, mul_one]
  rw [← mass_ofMap_eq]
  exact (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional c).1 v).ne'

/-- **S2(a).** In Witness 5.2, A (`D.comp C`) is calibrated to future-H, yet future-H at world `0`
(prior `C_0 = π(· | {0,1})`) does not totally trust A: at `(X, 3/4)` the mass is `−3/8`.
Source: vq-wiki-2-012 (the two Link-2s are independent, direction (a))
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem calibrated_not_trusted : Calibrated π hpos c (Frame.comp D C) ∧
    ¬ TotalTrust (C.P 0) (Frame.comp D C) := by
  refine ⟨comp_calibrated, fun h => ?_⟩
  have := h X (3 / 4)
  simp only [comp_E_eq, a_val] at this
  rw [Fin.sum_univ_four] at this
  simp [C, Frame.ofPartition_P_apply, mass_ofMap_eq, Fin.sum_univ_four, π, c, X] at this
  norm_num at this

/-! ### S2(b): trust without calibration -/

/-- The omniscient expert: `P_w = δ_w`.
Source: vq-wiki-2-012 (direction (b), the degenerate instance)
Kind: D
Fidelity: exact -/
def omni : Frame (Fin 4) where
  P := fun w => Pi.single w 1
  P_mem := fun w => ⟨fun v => by simp [Pi.single_apply]; split_ifs <;> norm_num, by simp⟩

/-- Every prior in the simplex totally trusts the omniscient expert: the product-form mass is
`∑_{X_w ≥ s} ρ w (X w − s) ≥ 0` termwise.
Source: vq-wiki-2-012 (b)
Kind: L (N−-ish: the expert is degenerate)
Fidelity: exact -/
theorem omni_totalTrust {ρ : Fin 4 → ℝ} (hρ : ∀ w, 0 ≤ ρ w) : TotalTrust ρ omni := by
  intro X s
  apply sum_nonneg
  intro w _
  have hE : E (omni.P w) X = X w := by simp [E, omni, Pi.single_apply]
  rw [hE]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (hρ w) (by linarith)) zero_le_one
  · simp

/-- **S2(b).** The omniscient expert is totally trusted by every future-H (indeed by every prior)
but is not calibrated to future-H: its quote of `X = (0,1,1,0)` at world `0` is `0 ≠ 1/2 = m X 0`.
Source: vq-wiki-2-012 (b)
Kind: N− (degenerate expert, as the mandate allows; a non-degenerate one was not sought)
Fidelity: exact
Hyps: (a) none -/
theorem trusted_not_calibrated : (∀ w, TotalTrust (C.P w) omni) ∧ ¬ Calibrated π hpos c omni := by
  refine ⟨fun w => omni_totalTrust (C.P_nonneg w), fun h => ?_⟩
  have := h X 0
  rw [m_val] at this
  simp [E, omni, Pi.single_apply, X] at this

end W52

end

end Cleanroom.Trust.TtFiniteFrames
