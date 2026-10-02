import Cleanroom.Found.LitDdbFrames.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The structure lemmas: 7.2.2 (repaired), 7.2.4, 7.2.5, 7.2.7

Package `lit-ddb-frames`, Targets 7–10. The engine is one lemma, `no_selfless_maximal_set`:
a nonempty finite set of points, each of which is a convex combination of points that are all
"no higher" than it under a linear functional `E · X`, with the maximisers among them lying in
the set and different from it, is impossible — because the set has an extreme point (Lemma
7.2.2, proved from `IsCompact.extremePoints_nonempty`), and the weights of a maximiser's
combination must all sit on other maximisers (`weights_on_max`). DDB run this argument by hand
three times (7.2.4, 7.2.5, 7.3) and once more for 7.4; here it is run once.

Both hypotheses DDB use (modest informedness over `C_ρ⁻`, class-convexity over `C_π \ {ρ}`)
give the same abstract decomposition `Frame.DecompOver`, so 7.2.4 and 7.2.5 are proved once for
both.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Lemma 7.2.2, repaired: a finite set has a member outside the hull of the rest -/

/-- **Target 7 (Lemma 7.2.2, repaired).** A nonempty finite set of points has a member that is
not in the convex hull of the others: the hull is compact and nonempty, so has an extreme point
(Krein–Milman lemma), which lies in the set and outside the hull of the rest. DDB's statement
("some `P_i ∈ A` has `λ_ii > 0`") is the contrapositive applied to their decompositions; the
transcription's proof is incomplete at its last line, the PDF's compresses this argument
(see `lit-ddb-frames-findings.md`).
Source: [[Deference Done Better]] App. B Lemma 7.2.2 l. 504
Kind: P
Fidelity: stronger: stated for an arbitrary finite set of points of `W → ℝ`, with the
decomposition hypotheses of DDB's version discharged by the callers
Hyps: (a) none -/
theorem exists_not_mem_convexHull_erase (M : Finset (W → ℝ)) (hM : M.Nonempty) :
    ∃ σ ∈ M, σ ∉ convexHull ℝ ((M.erase σ : Finset (W → ℝ)) : Set (W → ℝ)) := by
  obtain ⟨x, hx⟩ := (M.finite_toSet.isCompact_convexHull ℝ).extremePoints_nonempty
    (hM.to_set.mono (subset_convexHull ℝ _))
  have hxs : x ∈ M := extremePoints_convexHull_subset hx
  refine ⟨x, hxs, ?_⟩
  rw [(convex_convexHull ℝ _).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff] at hx
  intro h
  apply hx.2
  refine convexHull_mono ?_ h
  intro y hy
  simp only [coe_erase, Set.mem_sdiff, Set.mem_singleton_iff, mem_coe] at hy ⊢
  exact ⟨subset_convexHull ℝ _ hy.1, hy.2⟩

/-! ## Weights of a maximiser's decomposition sit on maximisers -/

/-- If `σ = ∑ c y • y` is a convex combination whose positively weighted points all have
`E y X ≤ t = E σ X`, then every positively weighted point has `E y X = t`.
Source: none: infrastructure (Target 7)
Kind: L
Fidelity: n/a -/
theorem weights_on_max {s : Finset (W → ℝ)} {c : (W → ℝ) → ℝ} {σ X : W → ℝ} {t : ℝ}
    (hc₀ : ∀ y ∈ s, 0 ≤ c y) (hc₁ : ∑ y ∈ s, c y = 1) (hσ : ∑ y ∈ s, c y • y = σ)
    (hσt : E σ X = t) (hle : ∀ y ∈ s, 0 < c y → E y X ≤ t) :
    ∀ y ∈ s, 0 < c y → E y X = t := by
  have hEt : ∑ y ∈ s, c y * E y X = t := by rw [← hσt, ← hσ, E_sum_left]
  have h1 : ∑ y ∈ s, c y * (t - E y X) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hc₁, one_mul, hEt, sub_self]
  have h2 : ∀ y ∈ s, 0 ≤ c y * (t - E y X) := by
    intro y hy
    rcases (hc₀ y hy).lt_or_eq with hpos | hzero
    · exact mul_nonneg hpos.le (by linarith [hle y hy hpos])
    · rw [← hzero, zero_mul]
  intro y hy hpos
  have h3 := (sum_eq_zero_iff_of_nonneg h2).1 h1 y hy
  rcases mul_eq_zero.1 h3 with h | h
  · linarith
  · linarith

/-- A convex combination whose positively weighted points lie in `M'` lies in the hull of `M'`.
Source: none: infrastructure (Target 7)
Kind: L
Fidelity: n/a -/
theorem mem_convexHull_of_weights_subset {s : Finset (W → ℝ)} {c : (W → ℝ) → ℝ} {σ : W → ℝ}
    (hc₀ : ∀ y ∈ s, 0 ≤ c y) (hc₁ : ∑ y ∈ s, c y = 1) (hσ : ∑ y ∈ s, c y • y = σ)
    {M' : Set (W → ℝ)} (hM : ∀ y ∈ s, 0 < c y → y ∈ M') : σ ∈ convexHull ℝ M' := by
  have hzero : ∀ y ∈ s, y ∉ s.filter (fun y => 0 < c y) → c y = 0 := by
    intro y hy hy'
    simp only [mem_filter, not_and, not_lt] at hy'
    exact le_antisymm (hy' hy) (hc₀ y hy)
  have hc₁' : ∑ y ∈ s.filter (fun y => 0 < c y), c y = 1 := by
    rw [← hc₁]
    exact sum_subset (filter_subset _ _) (fun y hy hy' => hzero y hy hy')
  have hσ' : ∑ y ∈ s.filter (fun y => 0 < c y), c y • y = σ := by
    rw [← hσ]
    exact sum_subset (filter_subset _ _) (fun y hy hy' => by rw [hzero y hy hy', zero_smul])
  have hcm : (s.filter (fun y => 0 < c y)).centerMass c id = σ := by
    rw [centerMass_eq_of_sum_1 _ _ hc₁']
    simpa using hσ'
  rw [← hcm]
  apply centerMass_mem_convexHull
  · intro y hy; exact hc₀ y (mem_filter.1 hy).1
  · rw [hc₁']; exact zero_lt_one
  · intro y hy; exact hM y (mem_filter.1 hy).1 (mem_filter.1 hy).2

/-- **The maximal-set lemma.** Let `M` be a nonempty finite set of points all with `E σ X = t`.
If every `σ ∈ M` is a convex combination of points each of which (when positively weighted)
has `E y X ≤ t`, and has `y ∈ M` and `y ≠ σ` whenever `E y X = t`, then contradiction. This is
the argument DDB run by hand in Lemmas 7.2.4, 7.2.5, 7.3 and 7.4.
Source: [[Deference Done Better]] App. B Lemmas 7.2.2–7.2.5, 7.3 (the shared pattern)
Kind: P
Fidelity: n/a (infrastructure abstracted from the source's repeated argument) -/
theorem no_selfless_maximal_set (M : Finset (W → ℝ)) (hM : M.Nonempty) (X : W → ℝ) (t : ℝ)
    (hMt : ∀ σ ∈ M, E σ X = t)
    (hdec : ∀ σ ∈ M, ∃ (s : Finset (W → ℝ)) (c : (W → ℝ) → ℝ), (∀ y ∈ s, 0 ≤ c y) ∧
      ∑ y ∈ s, c y = 1 ∧ ∑ y ∈ s, c y • y = σ ∧
      ∀ y ∈ s, 0 < c y → E y X ≤ t ∧ (E y X = t → y ∈ M ∧ y ≠ σ)) : False := by
  obtain ⟨σ, hσM, hσ⟩ := exists_not_mem_convexHull_erase M hM
  obtain ⟨s, c, hc₀, hc₁, hσs, hpt⟩ := hdec σ hσM
  apply hσ
  apply mem_convexHull_of_weights_subset hc₀ hc₁ hσs
  intro y hys hpos
  have ht := weights_on_max hc₀ hc₁ hσs (hMt σ hσM) (fun z hz hp => (hpt z hz hp).1) y hys hpos
  obtain ⟨hyM, hyne⟩ := (hpt y hys hpos).2 ht
  simp [hyM, hyne]

/-! ## Decompositions over the informed self and other candidates -/

/-- The abstract decomposition shared by modest informedness and class-convexity: every candidate
`ρ ∈ C_π` is a convex combination of its informed self `P̂_ρ` and frame rows `P_v ≠ ρ` at worlds
`v` seen by `π` or by `ρ`.
Source: none: infrastructure (Targets 8–10)
Kind: D
Fidelity: n/a -/
def Frame.DecompOver (F : Frame W) (π : W → ℝ) : Prop :=
  ∀ ρ ∈ F.cands π, ∃ D : Finset (W → ℝ),
    (∀ σ ∈ D, σ ≠ ρ ∧ ∃ v, σ = F.P v ∧ (0 < π v ∨ 0 < ρ v)) ∧
    ρ ∈ convexHull ℝ (insert (F.informed ρ) (↑D : Set (W → ℝ)))

/-- The hull condition gives the abstract decomposition (over `C_ρ⁻`).
Source: none: infrastructure (Target 8)
Kind: L
Fidelity: n/a -/
theorem HullAndModestlyInformed.decompOver {π : W → ℝ} {F : Frame W}
    (h : HullAndModestlyInformed π F) : F.DecompOver π := fun ρ hρ =>
  ⟨F.candsMinus ρ, fun σ hσ => by
    obtain ⟨hne, hσc⟩ := Frame.mem_candsMinus.1 hσ
    obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hσc
    exact ⟨hne, v, rfl, Or.inr hv⟩, (h.2 ρ hρ).2⟩

/-- Class-convexity gives the abstract decomposition (over `C_π \ {ρ}`).
Source: none: infrastructure (Target 10)
Kind: L
Fidelity: n/a -/
theorem ClassConvex.decompOver {π : W → ℝ} {F : Frame W} (h : ClassConvex π F) :
    F.DecompOver π := fun ρ hρ =>
  ⟨(F.cands π).erase ρ, fun σ hσ => by
    obtain ⟨hne, hσc⟩ := mem_erase.1 hσ
    obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hσc
    exact ⟨hne, v, rfl, Or.inl hv⟩, h ρ hρ⟩

/-- Weights on `C_π` from `π ∈ convexHull C_π`, and the candidates they positively weight have
full mass on `W_π`.
Source: [[Deference Done Better]] App. B Lemma 7.2.4 l. 512 (`W_π⁰` nonempty)
Kind: L
Fidelity: n/a -/
theorem Frame.exists_weights_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) :
    ∃ lam : (W → ℝ) → ℝ, (∀ ρ ∈ F.cands π, 0 ≤ lam ρ) ∧ ∑ ρ ∈ F.cands π, lam ρ = 1 ∧
      ∑ ρ ∈ F.cands π, lam ρ • ρ = π ∧
      ∀ ρ ∈ F.cands π, 0 < lam ρ → mass ρ (supp π) = 1 := by
  obtain ⟨lam, hl₀, hl₁, hπeq⟩ := Finset.mem_convexHull'.1 hhull
  refine ⟨lam, hl₀, hl₁, hπeq, ?_⟩
  have := weights_on_max hl₀ hl₁ hπeq (X := ind (supp π)) (t := 1)
    (by rw [E_ind, mass_supp hπ])
    (fun ρ hρ _ => by rw [E_ind]; exact mass_le_one (F.mem_stdSimplex_of_mem_cands hρ) _)
  intro ρ hρ hpos
  have h := this ρ hρ hpos
  rwa [E_ind] at h

/-- Mass of a singleton.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_singleton (ρ : W → ℝ) (x : W) : mass ρ {x} = ρ x := by simp [mass]

/-- A point of the sum of a nonnegative combination is at least each weighted term.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_apply_of_sum_smul {s : Finset (W → ℝ)} {c : (W → ℝ) → ℝ} {σ : W → ℝ}
    (hc₀ : ∀ y ∈ s, 0 ≤ c y) (hnn : ∀ y ∈ s, ∀ v, 0 ≤ y v) (hσ : ∑ y ∈ s, c y • y = σ)
    {y : W → ℝ} (hy : y ∈ s) (v : W) : c y * y v ≤ σ v := by
  rw [← hσ, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact single_le_sum (fun z hz => mul_nonneg (hc₀ z hz) (hnn z hz v)) hy

/-! ## Lemma 7.2.4 (Transitivity) -/

/-- **Target 8 (Lemma 7.2.4, Transitivity).** If `π ∈ convexHull C_π` and every candidate
decomposes over its informed self and other candidates (`Frame.DecompOver`, which both modest
informedness and class-convexity give), then every candidate has full mass on `W_π`. DDB's
`W_π⁰`/maximal-weight-set argument, with the maximal-set lemma doing the contradiction.
Source: [[Deference Done Better]] App. B Lemma 7.2.4 l. 510
Kind: P
Fidelity: stronger: proved under the abstract decomposition, so it also serves 7.2.7 (⇒)
Hyps: (a) none beyond the stated ones -/
theorem Frame.mass_supp_eq_one_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) (hdec : F.DecompOver π) :
    ∀ ρ ∈ F.cands π, mass ρ (supp π) = 1 := by
  obtain ⟨lam, hl₀, hl₁, hπeq, hfull⟩ := F.exists_weights_of_hull hπ hhull
  set W0 := (supp π).filter (fun w => mass (F.P w) (supp π) = 1) with hW0
  have hW0sub : W0 ⊆ supp π := filter_subset _ _
  have hmemW0 : ∀ w, w ∈ W0 ↔ 0 < π w ∧ mass (F.P w) (supp π) = 1 := by
    intro w; simp [hW0]
  -- Step 1: the decomposition of a candidate at `i ∈ W0` positively weights only rows at `W0`.
  have hstep1 : ∀ i ∈ W0, ∀ (s : Finset (W → ℝ)) (c : (W → ℝ) → ℝ),
      (∀ y ∈ s, 0 ≤ c y) → ∑ y ∈ s, c y = 1 → ∑ y ∈ s, c y • y = F.P i →
      (∀ y ∈ s, y = F.informed (F.P i) ∨ (∃ v, y = F.P v ∧ (0 < π v ∨ 0 < F.P i v))) →
      ∀ y ∈ s, 0 < c y → mass y (supp π) = 1 := by
    intro i hi s c hc₀ hc₁ hs hsy y hy hpos
    obtain ⟨hπi, hmi⟩ := (hmemW0 i).1 hi
    have := weights_on_max hc₀ hc₁ hs (X := ind (supp π)) (t := 1) (by rw [E_ind, hmi])
      (fun z hz _ => by
        rw [E_ind]
        rcases hsy z hz with rfl | ⟨v, rfl, _⟩
        · exact F.mass_informed_le_one (F.P_nonneg i) _
        · exact mass_le_one (F.P_mem v) _) y hy hpos
    rwa [E_ind] at this
  -- Step 2: for `i ∈ W0`, `P_i` has full mass on `W0`.
  have hstep2 : ∀ i ∈ W0, mass (F.P i) W0 = 1 := by
    intro i hi
    obtain ⟨hπi, hmi⟩ := (hmemW0 i).1 hi
    by_contra hne
    have hsplit := mass_inter_add_mass_sdiff (F.P i) (supp π) W0
    rw [inter_eq_right.2 hW0sub, hmi] at hsplit
    have hpos : 0 < mass (F.P i) (supp π \ W0) := by
      have := mass_le_one (F.P_mem i) W0
      have := mass_nonneg (F.P_nonneg i) (supp π \ W0)
      rcases lt_or_eq_of_le (mass_nonneg (F.P_nonneg i) (supp π \ W0)) with h | h
      · exact h
      · exact absurd (by linarith : mass (F.P i) W0 = 1) hne
    obtain ⟨x, hx, hPix⟩ := (mass_pos_iff (F.P_nonneg i)).1 hpos
    obtain ⟨hxsupp, hxW0⟩ := mem_sdiff.1 hx
    have hW0ne : W0.Nonempty := ⟨i, hi⟩
    obtain ⟨m, hmW0, hmax⟩ := W0.exists_max_image (fun w => F.P w x) hW0ne
    set t := F.P m x with ht
    have htpos : 0 < t := lt_of_lt_of_le hPix (hmax i hi)
    set M0 := W0.filter (fun w => F.P w x = t) with hM0
    set M := M0.image F.P with hM
    have hMne : M.Nonempty := ⟨F.P m, mem_image.2 ⟨m, mem_filter.2 ⟨hmW0, rfl⟩, rfl⟩⟩
    refine no_selfless_maximal_set M hMne (ind {x}) t ?_ ?_
    · intro σ hσ
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hσ
      rw [E_ind, mass_singleton]
      exact (mem_filter.1 hw).2
    · intro σ hσ
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hσ
      obtain ⟨hwW0, hwx⟩ := mem_filter.1 hw
      obtain ⟨hπw, hmw⟩ := (hmemW0 w).1 hwW0
      obtain ⟨D, hD, hhullw⟩ := hdec (F.P w) (F.P_mem_cands hπw)
      rw [← coe_insert] at hhullw
      obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hhullw
      refine ⟨insert (F.informed (F.P w)) D, c, hc₀, hc₁, hs, ?_⟩
      have hsy : ∀ y ∈ insert (F.informed (F.P w)) D,
          y = F.informed (F.P w) ∨ (∃ v, y = F.P v ∧ (0 < π v ∨ 0 < F.P w v)) := by
        intro y hy
        rcases mem_insert.1 hy with rfl | hyD
        · exact Or.inl rfl
        · exact Or.inr (hD y hyD).2
      have hfull1 := hstep1 w hwW0 _ c hc₀ hc₁ hs hsy
      intro y hy hpos
      have hyfull := hfull1 y hy hpos
      rw [E_ind, mass_singleton]
      rcases mem_insert.1 hy with rfl | hyD
      · -- the informed self vanishes at `x`, which is outside the cell of `P_w`
        have hxne : F.P x ≠ F.P w := by
          intro e
          apply hxW0
          rw [hmemW0]
          exact ⟨(mem_supp.1 hxsupp), e ▸ hmw⟩
        rw [F.informed_eq_zero_of_ne hxne]
        exact ⟨htpos.le, fun h => absurd h htpos.ne⟩
      · obtain ⟨hne, v, rfl, hv⟩ := hD y hyD
        have hvsupp : v ∈ supp π := by
          rcases hv with hv | hv
          · exact mem_supp.2 hv
          · exact mem_of_mass_eq_one (F.P_mem w) hmw hv
        have hvW0 : v ∈ W0 := (hmemW0 v).2 ⟨mem_supp.1 hvsupp, hyfull⟩
        refine ⟨hmax v hvW0, fun h => ⟨?_, hne⟩⟩
        exact mem_image.2 ⟨v, mem_filter.2 ⟨hvW0, h⟩, rfl⟩
  -- Step 3: `π` has full mass on `W0`, hence `W_π ⊆ W0`.
  have hstep3 : mass π W0 = 1 := by
    rw [← hπeq, mass_sum_left]
    have : ∀ ρ ∈ F.cands π, lam ρ * mass ρ W0 = lam ρ := by
      intro ρ hρ
      rcases (hl₀ ρ hρ).lt_or_eq with hpos | hzero
      · obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
        have hwW0 : w ∈ W0 := (hmemW0 w).2 ⟨hw, hfull _ hρ hpos⟩
        rw [hstep2 w hwW0, mul_one]
      · rw [← hzero, zero_mul]
    rw [sum_congr rfl this, hl₁]
  intro ρ hρ
  obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
  exact ((hmemW0 w).1 (mem_of_mass_eq_one hπ hstep3 hw)).2

/-- Corollary of Transitivity: the candidates of a candidate are candidates of `π`
(`C_i ⊆ C_π`).
Source: [[Deference Done Better]] App. B Lemma 7.2.7 proof l. 526 ("`C_i ⊆ C_π`")
Kind: L
Fidelity: n/a -/
theorem Frame.cands_subset_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) (hdec : F.DecompOver π)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : F.cands ρ ⊆ F.cands π := by
  intro σ hσ
  obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hσ
  have hfull := F.mass_supp_eq_one_of_hull hπ hhull hdec ρ hρ
  exact F.P_mem_cands (mem_supp.1 (mem_of_mass_eq_one (F.mem_stdSimplex_of_mem_cands hρ) hfull hv))

/-! ## Lemma 7.2.5 (Reflexivity) -/

/-- **Target 9 (Lemma 7.2.5, Reflexivity).** Under `π ∈ convexHull C_π` and the abstract
decomposition, every world seen by `π` gives itself positive probability: `0 < P_i i` for
`i ∈ W_π`. The positivity is *derived*, not assumed: this is where the null-worlds risk lives.
Source: [[Deference Done Better]] App. B Lemma 7.2.5 l. 518
Kind: P
Fidelity: stronger: proved under the abstract decomposition
Hyps: (a) none beyond the stated ones -/
theorem Frame.P_self_pos_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) (hdec : F.DecompOver π)
    {i : W} (hi : 0 < π i) : 0 < F.P i i := by
  by_contra hnot
  have hPii : F.P i i = 0 := le_antisymm (not_lt.1 hnot) (F.P_nonneg i i)
  obtain ⟨lam, hl₀, hl₁, hπeq, _⟩ := F.exists_weights_of_hull hπ hhull
  -- some candidate positively weighted by `π` gives `i` positive probability
  have hπi : π i = ∑ ρ ∈ F.cands π, lam ρ * ρ i := by
    conv_lhs => rw [← hπeq]
    rw [Finset.sum_apply]
    simp [Pi.smul_apply]
  have hex : ∃ ρ ∈ F.cands π, 0 < ρ i := by
    by_contra hnone
    push_neg at hnone
    have : ∑ ρ ∈ F.cands π, lam ρ * ρ i ≤ 0 := by
      apply sum_nonpos
      intro ρ hρ
      exact mul_nonpos_of_nonneg_of_nonpos (hl₀ ρ hρ) (hnone ρ hρ)
    linarith
  obtain ⟨ρ₀, hρ₀, hρ₀i⟩ := hex
  obtain ⟨m, hm, hmax⟩ := (F.cands π).exists_max_image (fun σ => σ i)
    (F.cands_nonempty hπ)
  set t := m i with ht
  have htpos : 0 < t := lt_of_lt_of_le hρ₀i (hmax ρ₀ hρ₀)
  set M := (F.cands π).filter (fun σ => σ i = t) with hM
  have hMne : M.Nonempty := ⟨m, mem_filter.2 ⟨hm, rfl⟩⟩
  refine no_selfless_maximal_set M hMne (ind {i}) t ?_ ?_
  · intro σ hσ
    rw [E_ind, mass_singleton]
    exact (mem_filter.1 hσ).2
  · intro σ hσ
    obtain ⟨hσc, hσi⟩ := mem_filter.1 hσ
    obtain ⟨D, hD, hhullσ⟩ := hdec σ hσc
    rw [← coe_insert] at hhullσ
    obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hhullσ
    refine ⟨insert (F.informed σ) D, c, hc₀, hc₁, hs, ?_⟩
    intro y hy _
    rw [E_ind, mass_singleton]
    rcases mem_insert.1 hy with rfl | hyD
    · have hne : F.P i ≠ σ := by
        intro e
        rw [← e] at hσi
        linarith
      rw [F.informed_eq_zero_of_ne hne]
      exact ⟨htpos.le, fun h => absurd h htpos.ne⟩
    · obtain ⟨hne, v, rfl, hv⟩ := hD y hyD
      have hvc : F.P v ∈ F.cands π := by
        rcases hv with hv | hv
        · exact F.P_mem_cands hv
        · exact F.cands_subset_of_hull hπ hhull hdec hσc (F.P_mem_cands hv)
      exact ⟨hmax _ hvc, fun h => ⟨mem_filter.2 ⟨hvc, h⟩, hne⟩⟩

/-- Every candidate has a positive self-cell under the hull condition (from Reflexivity).
Source: [[Deference Done Better]] App. B Lemma 7.5 proof l. 585 ("`P_i(i) > 0`, `P_i ∈ C_i`")
Kind: L
Fidelity: n/a -/
theorem Frame.selfMass_pos_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) (hdec : F.DecompOver π)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : 0 < F.selfMass ρ := by
  obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
  exact mass_pos_of_mem (F.P_nonneg w) (F.mem_cell_self w) (F.P_self_pos_of_hull hπ hhull hdec hw)

/-- Every candidate is a candidate of itself under the hull condition.
Source: [[Deference Done Better]] App. B Lemma 7.5 proof l. 585
Kind: L
Fidelity: n/a -/
theorem Frame.mem_cands_self_of_hull (F : Frame W) {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W)
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) (hdec : F.DecompOver π)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : ρ ∈ F.cands ρ := by
  obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
  exact F.P_mem_cands (F.P_self_pos_of_hull hπ hhull hdec hw)

/-! ## Lemma 7.2.7 (class-convexity ⟺ modest informedness, given the hull) -/

/-- **Target 10 (Lemma 7.2.7).** Given `π ∈ convexHull C_π`: `W_π` is class-convex iff every
candidate is modestly informed. (⇒) uses Reflexivity to show a positively weighted other
candidate of `π` is a candidate of `ρ`; (⇐) uses Transitivity for `C_ρ⁻ ⊆ C_π \ {ρ}`.
Source: [[Deference Done Better]] App. B Lemma 7.2.7 l. 524
Kind: P
Fidelity: exact
Hyps: (a) none beyond the stated ones -/
theorem classConvex_iff_modestlyInformed {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (hhull : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ))) :
    ClassConvex π F ↔ ∀ ρ ∈ F.cands π, F.ModestlyInformed ρ := by
  constructor
  · intro hcc ρ hρ
    have hdec := hcc.decompOver
    refine ⟨F.selfMass_pos_of_hull hπ hhull hdec hρ, ?_⟩
    have hρs := F.mem_stdSimplex_of_mem_cands hρ
    have h := hcc ρ hρ
    rw [← coe_insert] at h
    obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 h
    apply mem_convexHull_of_weights_subset hc₀ hc₁ hs
    intro y hy hpos
    rcases mem_insert.1 hy with rfl | hyC
    · exact Set.mem_insert _ _
    · obtain ⟨hne, hyc⟩ := mem_erase.1 hyC
      obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hyc
      have hPvv := F.P_self_pos_of_hull hπ hhull hdec hv
      have hnn : ∀ z ∈ insert (F.informed ρ) ((F.cands π).erase ρ), ∀ u, 0 ≤ z u := by
        intro z hz u
        rcases mem_insert.1 hz with rfl | hz
        · exact F.informed_nonneg hρs.1 u
        · exact (F.mem_stdSimplex_of_mem_cands (mem_erase.1 hz).2).1 u
      have hρv : 0 < ρ v := lt_of_lt_of_le (mul_pos hpos hPvv) (le_apply_of_sum_smul hc₀ hnn hs hy v)
      apply Set.mem_insert_of_mem
      rw [mem_coe, Frame.mem_candsMinus]
      exact ⟨hne, F.P_mem_cands hρv⟩
  · intro hmi ρ hρ
    have hdec := HullAndModestlyInformed.decompOver ⟨hhull, hmi⟩
    refine convexHull_mono ?_ (hmi ρ hρ).2
    apply Set.insert_subset_insert
    intro y hy
    rw [mem_coe, Frame.mem_candsMinus] at hy
    rw [mem_coe, mem_erase]
    exact ⟨hy.1, F.cands_subset_of_hull hπ hhull hdec hρ hy.2⟩

/-- The hull condition implies class-convexity.
Source: [[Deference Done Better]] App. B Lemma 7.3 proof l. 542
Kind: L
Fidelity: n/a -/
theorem HullAndModestlyInformed.classConvex {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : HullAndModestlyInformed π F) : ClassConvex π F :=
  (classConvex_iff_modestlyInformed hπ h.1).2 h.2

end

end Cleanroom.Found.LitDdbFrames
