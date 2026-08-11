/-
  StalenessDensity.lean
  =====================

  The counting lemma needed for the Total-Trust counterexample (program document
  `staleness-program.md`, item L1, used by T3).

  WHY THIS EXISTS.  In the counterexample, the human's expectation of an eventually-true
  indicator is known only **on Cesàro average** — that is all the human's own Recurring
  Unbiasedness delivers — while the days on which trust fails form a set of positive
  *density*.  To conclude that some failing day also carries a large expectation, one needs a
  counting fact.  An informal argument is tempted at exactly this point to assume a *pointwise*
  bound it has not got.  So this is the step to check.

  As in `Staleness.lean`: no market, no traders, no criterion.  Bare sequences and finite sets.

  No `sorry`; axiom audit at the end.
-/
import Mathlib

open Filter Topology
open scoped Classical

namespace Staleness

/-- Cesàro average of `x` over `[0, N)`. -/
noncomputable def cesaro (x : ℕ → ℝ) (N : ℕ) : ℝ := (∑ i ∈ Finset.range N, x i) / N

/-- `#(S ∩ [0,N))`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i => i ∈ S)).card

/-- Positive upper density, in the form the argument actually uses: the counting bound
    `d · N ≤ #(S ∩ [0,N))` holds for arbitrarily large `N`. -/
def UpperDensityGE (S : Set ℕ) (d : ℝ) : Prop :=
  ∃ᶠ (N : ℕ) in atTop, d * (N : ℝ) ≤ (countIn S N : ℝ)

/--
  **The density lemma.**  If `x` is bounded above by `1`, its Cesàro averages tend to `1`, and
  `S` has upper density at least `d > 0`, then `x n ≥ 1/2` for infinitely many `n ∈ S`.

  Contrapositive shape: if `x` were `< 1/2` throughout a positive-density set, the Cesàro
  average could not reach `1`.  Note only the upper bound `x ≤ 1` is needed — no lower bound,
  which is what makes it applicable to an expectation of a `[0,1]`-valued indicator.
-/
theorem exists_freq_mem_and_ge_half
    {x : ℕ → ℝ} {S : Set ℕ} {d : ℝ} (hd : 0 < d)
    (hx1 : ∀ n, x n ≤ 1)
    (hces : Tendsto (cesaro x) atTop (𝓝 1))
    (hdens : UpperDensityGE S d) :
    ∃ᶠ n in atTop, n ∈ S ∧ 1 / 2 ≤ x n := by
  intro hcon
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hcon
  -- from day `N₀` on, every member of `S` has `x < 1/2`
  have hbad : ∀ i, N₀ ≤ i → i ∈ S → x i < 1 / 2 := by
    intro i hi hiS
    by_contra hge
    exact hN₀ i hi ⟨hiS, not_lt.1 hge⟩
  -- `G N` : the members of `S` below `N` that are also at least `N₀`
  set G : ℕ → Finset ℕ := fun N => (Finset.range N).filter (fun i => i ∈ S ∧ N₀ ≤ i) with hGdef
  -- STEP 1.  Each element of `G N` costs the sum at least `1/2` against the trivial bound `N`.
  have key : ∀ N, (∑ i ∈ Finset.range N, x i) ≤ (N : ℝ) - (1 / 2) * ((G N).card : ℝ) := by
    intro N
    have hy0 : ∀ i, (0 : ℝ) ≤ 1 - x i := fun i => by linarith [hx1 i]
    have hsub : G N ⊆ Finset.range N := by
      intro i hi; exact (Finset.mem_filter.1 hi).1
    have h1 : (1 / 2) * ((G N).card : ℝ) ≤ ∑ i ∈ G N, (1 - x i) := by
      have hpt : ∀ i ∈ G N, (1 / 2 : ℝ) ≤ 1 - x i := by
        intro i hi
        have hf := Finset.mem_filter.1 hi
        have := hbad i hf.2.2 hf.2.1
        linarith
      calc (1 / 2) * ((G N).card : ℝ) = ∑ _i ∈ G N, (1 / 2 : ℝ) := by
            rw [Finset.sum_const]; ring
        _ ≤ ∑ i ∈ G N, (1 - x i) := Finset.sum_le_sum hpt
    have h2 : ∑ i ∈ G N, (1 - x i) ≤ ∑ i ∈ Finset.range N, (1 - x i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hy0 i)
    have h3 : ∑ i ∈ Finset.range N, (1 - x i) = (N : ℝ) - ∑ i ∈ Finset.range N, x i := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]; ring
    linarith
  -- STEP 2.  `G N` misses at most `N₀` members of `S ∩ [0,N)`.
  have hcard : ∀ N, (countIn S N : ℝ) - N₀ ≤ ((G N).card : ℝ) := by
    intro N
    have hTG : ((Finset.range N).filter (fun i => i ∈ S)) \ G N ⊆ Finset.range N₀ := by
      intro i hi
      have hs := Finset.mem_sdiff.1 hi
      have hiT := hs.1
      have hiR : i ∈ Finset.range N := (Finset.mem_filter.1 hiT).1
      have hiS : i ∈ S := (Finset.mem_filter.1 hiT).2
      have hnot : ¬ (N₀ ≤ i) := by
        intro hle
        exact hs.2 (Finset.mem_filter.2 ⟨hiR, hiS, hle⟩)
      exact Finset.mem_range.2 (by omega)
    have h1 : (((Finset.range N).filter (fun i => i ∈ S)) \ G N).card ≤ N₀ := by
      have := Finset.card_le_card hTG; simpa using this
    have h2 : countIn S N
        ≤ (G N).card + (((Finset.range N).filter (fun i => i ∈ S)) \ G N).card := by
      have hs : ((Finset.range N).filter (fun i => i ∈ S))
          ⊆ (G N) ∪ (((Finset.range N).filter (fun i => i ∈ S)) \ G N) := by
        intro i hi
        by_cases hc : i ∈ G N
        · exact Finset.mem_union_left _ hc
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hi, hc⟩)
      calc countIn S N ≤ ((G N) ∪ (((Finset.range N).filter (fun i => i ∈ S)) \ G N)).card :=
            Finset.card_le_card hs
        _ ≤ (G N).card + (((Finset.range N).filter (fun i => i ∈ S)) \ G N).card :=
            Finset.card_union_le _ _
    have hnat : countIn S N ≤ (G N).card + N₀ := by omega
    have : (countIn S N : ℝ) ≤ ((G N).card : ℝ) + N₀ := by exact_mod_cast hnat
    linarith
  -- STEP 3.  Combine with `cesaro → 1` and the vanishing of `N₀ / N`.
  have hclose : ∀ᶠ (N : ℕ) in atTop, 1 - d / 8 < cesaro x N :=
    hces.eventually (lt_mem_nhds (by linarith : (1 : ℝ) - d / 8 < 1))
  have hgrow : Tendsto (fun N : ℕ => (d / 8) * (N : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < d / 8)
      tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ (N : ℕ) in atTop, (N₀ : ℝ) + 1 ≤ (d / 8) * (N : ℝ) :=
    hgrow.eventually_ge_atTop _
  rcases (((hdens.and_eventually hclose).and_eventually hsmall).and_eventually
      (eventually_ge_atTop 1)).exists with ⟨N, ⟨⟨⟨hdN, hcl⟩, hsm⟩, hNge⟩⟩
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ (N : ℝ) := by exact_mod_cast hNge
    linarith
  have hdNR : 0 < d * (N : ℝ) := mul_pos hd hNpos
  -- unpack into linear form over the monomials `N`, `d*N`, `N₀`
  have hcl' : (1 - d / 8) * (N : ℝ) < ∑ i ∈ Finset.range N, x i := by
    simp only [cesaro] at hcl
    rw [lt_div_iff₀ hNpos] at hcl; linarith
  have hsm' : (N₀ : ℝ) < (d / 8) * (N : ℝ) := by linarith
  have hkey' : (∑ i ∈ Finset.range N, x i)
      ≤ (N : ℝ) - (1 / 2) * (d * (N : ℝ) - N₀) := by
    have h1 := key N
    have h2 := hcard N
    have h3 : d * (N : ℝ) - N₀ ≤ ((G N).card : ℝ) := by linarith
    linarith
  nlinarith [hcl', hsm', hkey', hdNR]

-- Axiom audit: must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms exists_freq_mem_and_ge_half

end Staleness
