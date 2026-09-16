/-
# The convergence measure: hull, overlap, discord

Round `2026-09-17-convergence-measure`.  Consumes `SeedStatics` unchanged.  Every name is
provisional (`AGENTS.md` standard 6); nothing is registered.

Sections:

1. **Interval data and the three masses.**  Reasoners `ι` (finite, nonempty) each carry a
   forced interval per coordinate.  Hull, common interval, discord, and the weighted
   masses over a declared fragment `Φ`.  The basic inequalities, the refutation of
   `Disc = 0 → Ovl > 0` (touching intervals), and the positivity theorem
   `discordMass_eq_zero_iff`.
2. **Blocked hull mass.**  Normalizing by the unpinned part of `Φ` is invariant under
   adding pinned coordinates (`blockedHull_insert_pinned`); the naive average is not
   (`naiveHull_insert_pinned_le`).
3. **Dynamics on interval data.**  Nesting lowers hull and overlap and preserves discord
   (`hullMass_anti`, `overlapMass_anti`, `discord_persists`); reopening raises hull
   (`hullMass_mono`).  Discord is pairwise (`discord_iff_pair`, Helly in dimension one).
4. **Region level.**  Region inclusion under more warrants and fewer defeats
   (`forcedRegionR_anti_warrants`, `forcedRegionR_anti_defeat`), and nesting of the
   computed intervals under any inclusion (`forcedInterval_nest_of_subset`).
5. **The discord certificate.**  Two bound certificates whose values cross merge into a
   `FarkasCert` for the merged bundle (`mergeCert`, `discord_certificate`).
6. **Convergence.**  Summable reopenings of the hull endpoints give a convergent hull mass
   (`hullMass_tendsto_of_summable`); summable upward steps of the mass itself suffice
   (`hullMass_tendsto_of_summable_rises`).
7. **The pinned fragment.**  A point pinned by any humble reasoner is pinned by all at the
   same value (`pinned_lift`), from `seed_independence_strict`.
-/

import Workspace.Normativity.Contrib.SeedStatics

namespace Workspace.Normativity.Contrib.ConvergenceMeasure

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Finset

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## 1. Interval data and the three masses -/

/-- Reasoner `i`'s forced interval on coordinate `φ`, as endpoints. -/
abbrev IntervalData (ι : Type*) (d : ℕ) := ι → Fin d → ℚ × ℚ

/-- Every interval is a nonempty subinterval of `[0,1]`. -/
def Valid (I : IntervalData ι d) : Prop :=
  ∀ i φ, 0 ≤ (I i φ).1 ∧ (I i φ).1 ≤ (I i φ).2 ∧ (I i φ).2 ≤ 1

/-- Lower endpoint of the hull `conv (⋃ᵢ Iⁱ_φ)`. -/
def hullLo (I : IntervalData ι d) (φ : Fin d) : ℚ := univ.inf' univ_nonempty fun i => (I i φ).1

/-- Upper endpoint of the hull. -/
def hullHi (I : IntervalData ι d) (φ : Fin d) : ℚ := univ.sup' univ_nonempty fun i => (I i φ).2

/-- The hull width `|H_φ|`. -/
def hullWidth (I : IntervalData ι d) (φ : Fin d) : ℚ := hullHi I φ - hullLo I φ

/-- Lower endpoint of the common interval `⋂ᵢ Iⁱ_φ`. -/
def commonLo (I : IntervalData ι d) (φ : Fin d) : ℚ := univ.sup' univ_nonempty fun i => (I i φ).1

/-- Upper endpoint of the common interval. -/
def commonHi (I : IntervalData ι d) (φ : Fin d) : ℚ := univ.inf' univ_nonempty fun i => (I i φ).2

/-- The common width `|C_φ|`, zero when the common interval is empty. -/
def commonWidth (I : IntervalData ι d) (φ : Fin d) : ℚ := max 0 (commonHi I φ - commonLo I φ)

/-- **Discord** on `φ`: the common interval is empty. -/
def Discord (I : IntervalData ι d) (φ : Fin d) : Prop := commonHi I φ < commonLo I φ

instance (I : IntervalData ι d) (φ : Fin d) : Decidable (Discord I φ) := by
  unfold Discord; infer_instance

/-- **Declared weights** on a declared fragment: positive on `Φ`, summing to one.  A
constitutive-layer declaration, never a reasoner's choice. -/
structure Weights (d : ℕ) (Φ : Finset (Fin d)) where
  w : Fin d → ℚ
  pos : ∀ φ ∈ Φ, 0 < w φ
  sum_one : ∑ φ ∈ Φ, w φ = 1

/-- **Hull mass** `Σ_φ w_φ |H_φ|`. -/
def hullMass (I : IntervalData ι d) (Φ : Finset (Fin d)) (w : Fin d → ℚ) : ℚ :=
  ∑ φ ∈ Φ, w φ * hullWidth I φ

/-- **Overlap mass** `Σ_φ w_φ |C_φ|`. -/
def overlapMass (I : IntervalData ι d) (Φ : Finset (Fin d)) (w : Fin d → ℚ) : ℚ :=
  ∑ φ ∈ Φ, w φ * commonWidth I φ

/-- **Discord mass** `Σ_{φ ∈ Δ} w_φ`. -/
def discordMass (I : IntervalData ι d) (Φ : Finset (Fin d)) (w : Fin d → ℚ) : ℚ :=
  ∑ φ ∈ Φ.filter (fun φ => Discord I φ), w φ

section Basic

variable (I : IntervalData ι d) (φ : Fin d)

lemma hullLo_le (i : ι) : hullLo I φ ≤ (I i φ).1 := inf'_le _ (mem_univ i)

lemma le_hullHi (i : ι) : (I i φ).2 ≤ hullHi I φ := by
  unfold hullHi; exact le_sup' (fun i => (I i φ).2) (mem_univ i)

lemma le_commonLo (i : ι) : (I i φ).1 ≤ commonLo I φ := by
  unfold commonLo; exact le_sup' (fun i => (I i φ).1) (mem_univ i)

lemma commonHi_le (i : ι) : commonHi I φ ≤ (I i φ).2 := inf'_le _ (mem_univ i)

lemma hullLo_nonneg (hV : Valid I) : 0 ≤ hullLo I φ :=
  le_inf' _ _ fun i _ => (hV i φ).1

lemma hullHi_le_one (hV : Valid I) : hullHi I φ ≤ 1 :=
  sup'_le _ _ fun i _ => (hV i φ).2.2

lemma hullWidth_nonneg (hV : Valid I) : 0 ≤ hullWidth I φ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  unfold hullWidth
  linarith [hullLo_le I φ i, le_hullHi I φ i, (hV i φ).2.1]

lemma hullWidth_le_one (hV : Valid I) : hullWidth I φ ≤ 1 := by
  unfold hullWidth
  linarith [hullLo_nonneg I φ hV, hullHi_le_one I φ hV]

lemma commonWidth_nonneg : 0 ≤ commonWidth I φ := le_max_left _ _

/-- `|C_φ| ≤ |H_φ|`. -/
lemma commonWidth_le_hullWidth (hV : Valid I) : commonWidth I φ ≤ hullWidth I φ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  unfold commonWidth
  apply max_le (hullWidth_nonneg I φ hV)
  unfold hullWidth
  linarith [commonHi_le I φ i, le_commonLo I φ i, hullLo_le I φ i, le_hullHi I φ i]

end Basic

section Masses

variable (I : IntervalData ι d) (Φ : Finset (Fin d))

/-- `Ovl ≤ Hull`. -/
theorem overlapMass_le_hullMass (hV : Valid I) {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) :
    overlapMass I Φ w ≤ hullMass I Φ w := by
  apply sum_le_sum
  intro φ hφ
  exact mul_le_mul_of_nonneg_left (commonWidth_le_hullWidth I φ hV) (hw φ hφ)

/-- `Hull ≤ 1`. -/
theorem hullMass_le_one (hV : Valid I) (W : Weights d Φ) : hullMass I Φ W.w ≤ 1 := by
  calc hullMass I Φ W.w ≤ ∑ φ ∈ Φ, W.w φ * 1 := by
        apply sum_le_sum
        intro φ hφ
        exact mul_le_mul_of_nonneg_left (hullWidth_le_one I φ hV) (W.pos φ hφ).le
    _ = 1 := by simp [W.sum_one]

theorem hullMass_nonneg (hV : Valid I) {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) :
    0 ≤ hullMass I Φ w :=
  sum_nonneg fun φ hφ => mul_nonneg (hw φ hφ) (hullWidth_nonneg I φ hV)

theorem discordMass_nonneg {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : 0 ≤ discordMass I Φ w :=
  sum_nonneg fun φ hφ => hw φ (mem_filter.1 hφ).1

/-- **Positive weights make discord mass honest**: it vanishes exactly when no declared
coordinate is in discord.  This is the theorem weight capture would break. -/
theorem discordMass_eq_zero_iff (W : Weights d Φ) :
    discordMass I Φ W.w = 0 ↔ ∀ φ ∈ Φ, ¬ Discord I φ := by
  unfold discordMass
  rw [sum_eq_zero_iff_of_nonneg fun φ hφ => (W.pos φ (mem_filter.1 hφ).1).le]
  constructor
  · intro h φ hφ hd
    have := h φ (mem_filter.2 ⟨hφ, hd⟩)
    exact absurd this (W.pos φ hφ).ne'
  · intro h φ hφ
    exact absurd (mem_filter.1 hφ).2 (h φ (mem_filter.1 hφ).1)

/-- Under any weights, discord on some declared coordinate makes discord mass positive. -/
theorem discordMass_pos (W : Weights d Φ) {φ : Fin d} (hφ : φ ∈ Φ) (hd : Discord I φ) :
    0 < discordMass I Φ W.w :=
  lt_of_lt_of_le (W.pos φ hφ)
    (single_le_sum (fun ψ hψ => (W.pos ψ (mem_filter.1 hψ).1).le) (mem_filter.2 ⟨hφ, hd⟩))

end Masses

/-- **`Disc = 0 → Ovl > 0` is false.**  Two reasoners whose intervals touch at a point:
`[0, 1/2]` and `[1/2, 1]`.  No discord, and the common width is zero. -/
def touching : IntervalData (Fin 2) 1 := fun i _ => if i = 0 then (0, 1/2) else (1/2, 1)

theorem touching_refutes : ¬ Discord touching 0 ∧ commonWidth touching 0 = 0 := by
  have hlo : commonLo touching 0 = 1/2 := by
    apply le_antisymm
    · apply sup'_le; intro i _; fin_cases i <;> norm_num [touching]
    · have := le_commonLo touching 0 1; simpa [touching] using this
  have hhi : commonHi touching 0 = 1/2 := by
    apply le_antisymm
    · have := commonHi_le touching 0 0; simpa [touching] using this
    · apply le_inf'; intro i _; fin_cases i <;> norm_num [touching]
  constructor
  · unfold Discord; rw [hlo, hhi]; exact lt_irrefl _
  · unfold commonWidth; rw [hlo, hhi]; simp

/-! ## 2. Blocked hull mass -/

/-- The unweighted hull sum over `Φ`. -/
def hullSum (I : IntervalData ι d) (Φ : Finset (Fin d)) : ℚ := ∑ φ ∈ Φ, hullWidth I φ

/-- The unpinned part of `Φ`: coordinates with positive hull width. -/
def unpinned (I : IntervalData ι d) (Φ : Finset (Fin d)) : Finset (Fin d) :=
  Φ.filter fun φ => 0 < hullWidth I φ

/-- The naive average: hull sum over the size of `Φ`. -/
def naiveHull (I : IntervalData ι d) (Φ : Finset (Fin d)) : ℚ := hullSum I Φ / Φ.card

/-- The blocked average: hull sum over the size of the unpinned part. -/
def blockedHull (I : IntervalData ι d) (Φ : Finset (Fin d)) : ℚ :=
  hullSum I Φ / (unpinned I Φ).card

/-- **Fragment dilution succeeds against the naive average**: adding a pinned coordinate
lowers it (weakly; strictly when the hull sum is positive). -/
theorem naiveHull_insert_pinned_le (I : IntervalData ι d) (hV : Valid I) (Φ : Finset (Fin d))
    (hΦ : Φ.Nonempty) {ψ : Fin d} (hψ : hullWidth I ψ = 0) (hnot : ψ ∉ Φ) :
    naiveHull I (insert ψ Φ) ≤ naiveHull I Φ := by
  unfold naiveHull hullSum
  rw [sum_insert hnot, hψ, zero_add, card_insert_of_notMem hnot]
  have hs : 0 ≤ ∑ φ ∈ Φ, hullWidth I φ := sum_nonneg fun φ _ => hullWidth_nonneg I φ hV
  have hc : (0 : ℚ) < Φ.card := by exact_mod_cast hΦ.card_pos
  push_cast
  apply div_le_div_of_nonneg_left hs hc
  linarith

/-- **The blocked average is invariant** under adding a pinned coordinate. -/
theorem blockedHull_insert_pinned (I : IntervalData ι d) (Φ : Finset (Fin d)) {ψ : Fin d}
    (hψ : hullWidth I ψ = 0) (hnot : ψ ∉ Φ) :
    blockedHull I (insert ψ Φ) = blockedHull I Φ := by
  unfold blockedHull hullSum unpinned
  rw [sum_insert hnot, hψ, zero_add, filter_insert]
  simp [hψ]

/-! ## 3. Dynamics on interval data -/

/-- `I'` is **nested** in `I`: every reasoner's interval shrank or stayed. -/
def Nested (I I' : IntervalData ι d) : Prop :=
  ∀ i φ, (I i φ).1 ≤ (I' i φ).1 ∧ (I' i φ).2 ≤ (I i φ).2

omit [Fintype ι] [Nonempty ι] in
theorem Nested.refl (I : IntervalData ι d) : Nested I I := fun _ _ => ⟨le_rfl, le_rfl⟩

omit [Fintype ι] [Nonempty ι] in
/-- Private narrowing: only reasoner `i₀` shrinks; everyone else is unchanged.  A special
case of `Nested`. -/
theorem Nested.ofPrivate {I I' : IntervalData ι d} (i₀ : ι)
    (h₀ : ∀ φ, (I i₀ φ).1 ≤ (I' i₀ φ).1 ∧ (I' i₀ φ).2 ≤ (I i₀ φ).2)
    (hrest : ∀ i, i ≠ i₀ → I' i = I i) : Nested I I' := by
  intro i φ
  by_cases h : i = i₀
  · subst h; exact h₀ φ
  · rw [hrest i h]; exact ⟨le_rfl, le_rfl⟩

section Dynamics

variable {I I' : IntervalData ι d} (h : Nested I I') (φ : Fin d)
include h

lemma hullLo_mono : hullLo I φ ≤ hullLo I' φ :=
  le_inf' _ _ fun i _ => le_trans (hullLo_le I φ i) (h i φ).1

lemma hullHi_anti : hullHi I' φ ≤ hullHi I φ :=
  sup'_le _ _ fun i _ => le_trans (h i φ).2 (le_hullHi I φ i)

lemma commonLo_mono : commonLo I φ ≤ commonLo I' φ :=
  sup'_le _ _ fun i _ => le_trans (h i φ).1 (le_commonLo I' φ i)

lemma commonHi_anti : commonHi I' φ ≤ commonHi I φ :=
  le_inf' _ _ fun i _ => le_trans (commonHi_le I' φ i) (h i φ).2

lemma hullWidth_anti : hullWidth I' φ ≤ hullWidth I φ := by
  unfold hullWidth; linarith [hullLo_mono h φ, hullHi_anti h φ]

lemma commonWidth_anti : commonWidth I' φ ≤ commonWidth I φ := by
  unfold commonWidth
  apply max_le (le_max_left _ _)
  apply le_max_of_le_right
  linarith [commonLo_mono h φ, commonHi_anti h φ]

/-- **Discord persists under narrowing.**  Once the common interval is empty, no
settlement, shared warrant or private warrant restores it — only reopening can. -/
theorem discord_persists (hd : Discord I φ) : Discord I' φ := by
  unfold Discord at hd ⊢
  linarith [commonLo_mono h φ, commonHi_anti h φ]

end Dynamics

/-- **H1, narrowing.**  Hull mass is nonincreasing under any nesting: settlement, shared
narrowing, and private narrowing alike. -/
theorem hullMass_anti {I I' : IntervalData ι d} (h : Nested I I') (Φ : Finset (Fin d))
    {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : hullMass I' Φ w ≤ hullMass I Φ w :=
  sum_le_sum fun φ hφ => mul_le_mul_of_nonneg_left (hullWidth_anti h φ) (hw φ hφ)

/-- Overlap mass is nonincreasing under nesting too: narrowing never adds common ground. -/
theorem overlapMass_anti {I I' : IntervalData ι d} (h : Nested I I') (Φ : Finset (Fin d))
    {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : overlapMass I' Φ w ≤ overlapMass I Φ w :=
  sum_le_sum fun φ hφ => mul_le_mul_of_nonneg_left (commonWidth_anti h φ) (hw φ hφ)

/-- **H1, reopening.**  Hull mass is nondecreasing when intervals widen. -/
theorem hullMass_mono {I I' : IntervalData ι d} (h : Nested I' I) (Φ : Finset (Fin d))
    {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : hullMass I Φ w ≤ hullMass I' Φ w :=
  hullMass_anti h Φ hw

/-- Discord mass is nondecreasing under narrowing. -/
theorem discordMass_mono {I I' : IntervalData ι d} (h : Nested I I') (Φ : Finset (Fin d))
    {w : Fin d → ℚ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ) : discordMass I Φ w ≤ discordMass I' Φ w := by
  unfold discordMass
  apply sum_le_sum_of_subset_of_nonneg
  · intro φ hφ
    rw [mem_filter] at hφ ⊢
    exact ⟨hφ.1, discord_persists h φ hφ.2⟩
  · intro φ hφ _
    exact hw φ (mem_filter.1 hφ).1

/-- **Helly in dimension one.**  The common interval is empty iff some pair of reasoners
has disjoint intervals: discord is pairwise. -/
theorem discord_iff_pair (I : IntervalData ι d) (φ : Fin d) :
    Discord I φ ↔ ∃ i j : ι, (I j φ).2 < (I i φ).1 := by
  unfold Discord commonLo commonHi
  rw [lt_sup'_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    rw [inf'_lt_iff] at hi
    obtain ⟨j, _, hj⟩ := hi
    exact ⟨i, j, hj⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨i, mem_univ i, (inf'_lt_iff _).2 ⟨j, mem_univ j, hij⟩⟩

/-! ## 4. Region level -/

section Region

variable {A : Type*} (S : Seed d A) (W W' : List (SubItem d)) (F : Settlement d)

/-- **Shared or private narrowing shrinks the region**: more warrants, smaller region. -/
theorem forcedRegionR_anti_warrants (st : DocketState) {x : Fin d → ℝ}
    (hx : forcedRegionR S (W ++ W') st F x) : forcedRegionR S W st F x := by
  rw [forcedRegionR_iff] at hx ⊢
  refine ⟨hx.1, hx.2.1, ?_, hx.2.2.2⟩
  intro it hit
  apply hx.2.2.1
  simp only [List.mem_append] at hit ⊢
  tauto

/-- **Reopening enlarges the region**: more defeated ports, fewer live rows. -/
theorem forcedRegionR_anti_defeat {st st' : DocketState} (hdef : st.defeated ⊆ st'.defeated)
    (hwd : st.withdrawn = st'.withdrawn) {x : Fin d → ℝ}
    (hx : forcedRegionR S W st F x) : forcedRegionR S W st' F x := by
  rw [forcedRegionR_iff] at hx ⊢
  refine ⟨hx.1, hx.2.1, ?_, ?_⟩
  · intro it hit
    apply hx.2.2.1
    simp only [List.mem_append, Seed.liveSub, List.mem_filter, decide_eq_true_eq] at hit ⊢
    rcases hit with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, fun hm => h2 (hdef hm)⟩
    · exact Or.inr h
  · intro it hit
    apply hx.2.2.2
    unfold Seed.liveStr at hit ⊢
    rw [← hwd] at hit
    exact hit

end Region

/-- **Nesting of the computed intervals under any region inclusion.**  Instantiates to
settlement (`forcedInterval_mono`), shared and private narrowing
(`forcedRegionR_anti_warrants`) and, reversed, to reopening (`forcedRegionR_anti_defeat`). -/
theorem forcedInterval_nest_of_subset {m : ℕ} {A A' : Type*} (S : Seed (m + 1) A)
    (S' : Seed (m + 1) A') (W W' : List (SubItem (m + 1))) (st st' : DocketState)
    (F F' : Settlement (m + 1)) (φ : Fin (m + 1))
    (hsub : ∀ x, forcedRegionR S' W' st' F' x → forcedRegionR S W st F x)
    (hne' : ∃ x, forcedRegionR S' W' st' F' x) :
    (forcedInterval S W st F φ).1 ≤ (forcedInterval S' W' st' F' φ).1 ∧
    (forcedInterval S' W' st' F' φ).2 ≤ (forcedInterval S W st F φ).2 := by
  have hne : ∃ x, forcedRegionR S W st F x := hne'.imp fun x hx => hsub x hx
  obtain ⟨hb, -, -⟩ := forcedInterval_spec S W st F φ hne
  obtain ⟨-, ⟨x, hx, hxφ⟩, ⟨y, hy, hyφ⟩⟩ := forcedInterval_spec S' W' st' F' φ hne'
  have h1 := (hb x (hsub x hx)).1
  have h2 := (hb y (hsub y hy)).2
  rw [hxφ] at h1
  rw [hyφ] at h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## 5. The discord certificate -/

/-- **Two crossing bound certificates merge into a Farkas certificate.**  A lower
certificate `Σλa = −e_φ` of value `−lo` and an upper certificate `Σμa = e_φ` of value `hi`
with `hi < lo` sum to zero coefficients and a negative constant. -/
def mergeCert {m₁ m₂ : ℕ} {φ : Fin d} (c₁ : BoundCert d m₁ φ (-1)) (c₂ : BoundCert d m₂ φ 1)
    (h : c₁.value + c₂.value < 0) : FarkasCert d (m₁ + m₂) where
  mult := Fin.append c₁.mult c₂.mult
  row := Fin.append c₁.row c₂.row
  mult_nonneg := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact c₁.mult_nonneg i
    · rw [Fin.append_right]; exact c₂.mult_nonneg i
  coeff_sum := by
    intro j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [c₁.coeff_sum j, c₂.coeff_sum j]
    split_ifs <;> norm_num
  const_sum := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    unfold BoundCert.value at h
    exact h

lemma allowed_append_left {Q : Type*} (B₁ B₂ : Bundle Q d) {r : Row d} (h : B₁.Allowed r) :
    (B₁ ++ B₂).Allowed r := by
  rcases h with ⟨c, hc, hr⟩ | h | h
  · exact Or.inl ⟨c, List.mem_append_left _ hc, hr⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma allowed_append_right {Q : Type*} (B₁ B₂ : Bundle Q d) {r : Row d} (h : B₂.Allowed r) :
    (B₁ ++ B₂).Allowed r := by
  rcases h with ⟨c, hc, hr⟩ | h | h
  · exact Or.inl ⟨c, List.mem_append_right _ hc, hr⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The region of a concatenated bundle is the intersection. -/
theorem region_append_iff {Q : Type*} (B₁ B₂ : Bundle Q d) (x : Fin d → ℚ) :
    (B₁ ++ B₂).Region x ↔ B₁.Region x ∧ B₂.Region x := by
  unfold Bundle.Region
  simp only [List.mem_append]
  constructor
  · rintro ⟨hc, hr⟩
    exact ⟨⟨hc, fun c h => hr c (Or.inl h)⟩, ⟨hc, fun c h => hr c (Or.inr h)⟩⟩
  · rintro ⟨⟨hc, h₁⟩, ⟨-, h₂⟩⟩
    exact ⟨hc, fun c h => h.elim (h₁ c) (h₂ c)⟩

/-- **The discord certificate is sound.**  A lower certificate over reasoner 1's bundle
and an upper certificate over reasoner 2's bundle whose values cross refute every common
point of the two forced regions: what one of them holds must go. -/
theorem discord_certificate {Q : Type*} (B₁ B₂ : Bundle Q d) {m₁ m₂ : ℕ} {φ : Fin d}
    (c₁ : BoundCert d m₁ φ (-1)) (c₂ : BoundCert d m₂ φ 1)
    (h₁ : ∀ i, B₁.Allowed (c₁.row i)) (h₂ : ∀ i, B₂.Allowed (c₂.row i))
    (h : c₂.value < -c₁.value) :
    ¬ ∃ x, B₁.Region x ∧ B₂.Region x := by
  have hc : ¬ ∃ x, (B₁ ++ B₂).Region x := by
    refine conflict_sound (B₁ ++ B₂) (mergeCert c₁ c₂ (by linarith)) ?_
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · show (B₁ ++ B₂).Allowed (Fin.append c₁.row c₂.row (Fin.castAdd _ i))
      rw [Fin.append_left]
      exact allowed_append_left _ _ (h₁ i)
    · show (B₁ ++ B₂).Allowed (Fin.append c₁.row c₂.row (Fin.natAdd _ i))
      rw [Fin.append_right]
      exact allowed_append_right _ _ (h₂ i)
  rintro ⟨x, hx₁, hx₂⟩
  exact hc ⟨x, (region_append_iff B₁ B₂ x).2 ⟨hx₁, hx₂⟩⟩

/-! ## 6. Convergence -/

open Filter Topology in
/-- A nonnegative real sequence whose upward steps are summable converges. -/
theorem tendsto_of_summable_rises (l : ℕ → ℝ) (hb : ∀ n, 0 ≤ l n)
    (hs : Summable fun n => max 0 (l (n + 1) - l n)) : ∃ L, Tendsto l atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := tendsto_of_summable_drops (fun n => -l n) (fun n => by linarith [hb n])
    (hs.congr fun n => by ring_nf)
  refine ⟨-L, ?_⟩
  have := hL.neg
  simpa using this

lemma hullLo_le_one (I : IntervalData ι d) (φ : Fin d) (hV : Valid I) : hullLo I φ ≤ 1 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  linarith [hullLo_le I φ i, (hV i φ).2.1, (hV i φ).2.2]

lemma hullHi_nonneg (I : IntervalData ι d) (φ : Fin d) (hV : Valid I) : 0 ≤ hullHi I φ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  linarith [le_hullHi I φ i, (hV i φ).2.1, (hV i φ).1]

open Filter Topology in
/-- **H2.**  Along a chain of interval data, summable reopenings of every declared hull
endpoint give a convergent hull mass. -/
theorem hullMass_tendsto_of_summable (I : ℕ → IntervalData ι d) (hV : ∀ t, Valid (I t))
    (Φ : Finset (Fin d)) (w : Fin d → ℚ)
    (hlo : ∀ φ ∈ Φ, Summable fun t => max 0 ((hullLo (I t) φ : ℝ) - hullLo (I (t + 1)) φ))
    (hhi : ∀ φ ∈ Φ, Summable fun t => max 0 ((hullHi (I (t + 1)) φ : ℝ) - hullHi (I t) φ)) :
    ∃ L, Tendsto (fun t => (hullMass (I t) Φ w : ℝ)) atTop (𝓝 L) := by
  have hw : ∀ φ ∈ Φ, ∃ L, Tendsto (fun t => (hullWidth (I t) φ : ℝ)) atTop (𝓝 L) := by
    intro φ hφ
    obtain ⟨Llo, hLlo⟩ := tendsto_of_summable_drops (fun t => (hullLo (I t) φ : ℝ))
      (fun t => by exact_mod_cast hullLo_le_one (I t) φ (hV t)) (hlo φ hφ)
    obtain ⟨Lhi, hLhi⟩ := tendsto_of_summable_rises (fun t => (hullHi (I t) φ : ℝ))
      (fun t => by exact_mod_cast hullHi_nonneg (I t) φ (hV t)) (hhi φ hφ)
    refine ⟨Lhi - Llo, ?_⟩
    have := hLhi.sub hLlo
    refine this.congr fun t => ?_
    simp [hullWidth]
  choose L hL using hw
  let Lf : Fin d → ℝ := fun φ => if h : φ ∈ Φ then L φ h else 0
  refine ⟨∑ φ ∈ Φ, (w φ : ℝ) * Lf φ, ?_⟩
  have hsum : Tendsto (fun t => ∑ φ ∈ Φ, (w φ : ℝ) * (hullWidth (I t) φ : ℝ)) atTop
      (𝓝 (∑ φ ∈ Φ, (w φ : ℝ) * Lf φ)) := by
    apply tendsto_finsetSum
    intro φ hφ
    have : Lf φ = L φ hφ := by simp [Lf, hφ]
    rw [this]
    exact (hL φ hφ).const_mul _
  refine hsum.congr fun t => ?_
  simp [hullMass]

open Filter Topology in
/-- **H2, the short form.**  Summable upward steps of the hull mass itself give
convergence. -/
theorem hullMass_tendsto_of_summable_rises (I : ℕ → IntervalData ι d) (hV : ∀ t, Valid (I t))
    (Φ : Finset (Fin d)) (w : Fin d → ℚ) (hw : ∀ φ ∈ Φ, 0 ≤ w φ)
    (hs : Summable fun t => max 0 ((hullMass (I (t + 1)) Φ w : ℝ) - hullMass (I t) Φ w)) :
    ∃ L, Tendsto (fun t => (hullMass (I t) Φ w : ℝ)) atTop (𝓝 L) :=
  tendsto_of_summable_rises _ (fun t => by exact_mod_cast hullMass_nonneg (I t) Φ (hV t) hw) hs

/-! ## 7. The pinned fragment -/

omit [Fintype ι] [Nonempty ι] in
/-- **A point pinned by one humble reasoner is pinned by all, at the same value.**
`seed_independence_strict` lifted to a family: all share the closed layer `B`; each carries
a strict substantive layer `L i` with nonempty region. -/
theorem pinned_lift {Q : Type*} (B : Bundle Q d) (L : ι → List (Row d)) (φ : Fin d) (p : ℝ)
    (hne : ∀ i, ∃ x, B.RegionR x ∧ ∀ r ∈ L i, StrictSatR r x) (i₀ : ι)
    (hpin : ∀ x, B.RegionR x → (∀ r ∈ L i₀, StrictSatR r x) → x φ = p) :
    ∀ i, ∀ x, B.RegionR x → (∀ r ∈ L i, StrictSatR r x) → x φ = p :=
  fun i => seed_independence_strict B (L i₀) (L i) φ p (hne i₀) hpin


#print axioms overlapMass_le_hullMass
#print axioms hullMass_le_one
#print axioms discordMass_eq_zero_iff
#print axioms discordMass_pos
#print axioms touching_refutes
#print axioms naiveHull_insert_pinned_le
#print axioms blockedHull_insert_pinned
#print axioms hullMass_anti
#print axioms overlapMass_anti
#print axioms hullMass_mono
#print axioms discord_persists
#print axioms discordMass_mono
#print axioms discord_iff_pair
#print axioms forcedRegionR_anti_warrants
#print axioms forcedRegionR_anti_defeat
#print axioms forcedInterval_nest_of_subset
#print axioms mergeCert
#print axioms region_append_iff
#print axioms discord_certificate
#print axioms tendsto_of_summable_rises
#print axioms hullMass_tendsto_of_summable
#print axioms hullMass_tendsto_of_summable_rises
#print axioms pinned_lift

end Workspace.Normativity.Contrib.ConvergenceMeasure
