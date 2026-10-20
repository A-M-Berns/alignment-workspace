/-
# The convergence measure: hull, overlap, discord — the interval-data layer

Landed on `main` by the round `2026-10-21-rebuttal-and-end-to-end` from the branch
`round/2026-09-17-convergence-measure` (`ConvergenceMeasure.lean` §1–§4); the branch's
§5 (the discord certificate), §6 (convergence of the hull mass) and §7 (the pinned
fragment) are not landed and are listed in that round's `LANDING.md`.  Consumes
`SeedStatics` unchanged.  Every name is provisional (`AGENTS.md` standard 6).

Sections, numbered as on the branch:

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

The single-reasoner case `ι = Unit` is what the end-to-end witness reports.
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

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.IntervalData
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Valid
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullLo
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullHi
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullWidth
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonLo
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonHi
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonWidth
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Discord
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Weights
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.overlapMass
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discordMass
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullLo_le
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.le_hullHi
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.le_commonLo
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonHi_le
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullLo_nonneg
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullHi_le_one
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullWidth_nonneg
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullWidth_le_one
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonWidth_nonneg
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonWidth_le_hullWidth
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.overlapMass_le_hullMass
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_le_one
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_nonneg
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discordMass_nonneg
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discordMass_eq_zero_iff
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discordMass_pos
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.touching
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.touching_refutes
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullSum
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.unpinned
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.naiveHull
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.blockedHull
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.naiveHull_insert_pinned_le
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.blockedHull_insert_pinned
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Nested
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Nested.refl
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.Nested.ofPrivate
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullLo_mono
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullHi_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonLo_mono
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonHi_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullWidth_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.commonWidth_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discord_persists
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.overlapMass_anti
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.hullMass_mono
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discordMass_mono
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.discord_iff_pair
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.forcedRegionR_anti_warrants
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.forcedRegionR_anti_defeat
#print axioms Workspace.Normativity.Contrib.ConvergenceMeasure.forcedInterval_nest_of_subset

end Workspace.Normativity.Contrib.ConvergenceMeasure
