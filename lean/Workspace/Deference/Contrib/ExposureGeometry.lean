/-
# Settlement windows: piercing duality and the exposure–harvest bound

Source: `prompts/2026-08-11-deference-densification/REPORT.md` §1, Lemma 1 (piercing
duality) and Theorem 2 (the exact exposure–harvest bound), with the inhabitation witness of
that report's §1 greedy family at `F(n) = 2n+1`.

Finite, exact-rational, combinatorial. No Logical-Induction fact appears: the source's §4
records that the linear harvest model is posited and that nothing here narrows the standing
gap, and that remains true of the port.

**How `ν = τ` is carried.** The source states Lemma 1 as an equality of two extremal
cardinals. Rather than define `ν` and `τ` as a maximum and a minimum over subfamilies, this
file carries the same content in the form the proof produces: greedy exhibits a piercing set
and a disjoint subfamily *of equal size* (`greedy_duality`), and weak duality
(`card_le_card_of_pierces`) says every disjoint subfamily is at most every piercing set. The
two together say that the exhibited pair is simultaneously a maximum and a minimum —
`greedy_disjoint_maximum` and `greedy_piercing_minimum` state exactly that. Nothing is lost
and no order-theoretic scaffolding is introduced.

Provisional names (`AGENTS.md` §6): `InWindow`, `Pierces`, `WindowsDisjoint`, `exposure`,
and the theorem names below.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Workspace.Deference.Contrib.ExposureGeometry

open Finset

/-- `t` lies in the settlement window `I_n = [n, F n)` of a position opened at `n`. -/
def InWindow (F : ℕ → ℕ) (n t : ℕ) : Prop := n ≤ t ∧ t < F n

instance (F : ℕ → ℕ) (n t : ℕ) : Decidable (InWindow F n t) :=
  inferInstanceAs (Decidable (n ≤ t ∧ t < F n))

/-- `Pset` pierces the family `{I_n : n ∈ Ω}`. -/
def Pierces (F : ℕ → ℕ) (Pset Ω : Finset ℕ) : Prop :=
  ∀ n ∈ Ω, ∃ t ∈ Pset, InWindow F n t

/-- The windows indexed by `T` are pairwise disjoint. -/
def WindowsDisjoint (F : ℕ → ℕ) (T : Finset ℕ) : Prop :=
  ∀ m ∈ T, ∀ n ∈ T, m ≠ n → ∀ t, ¬ (InWindow F m t ∧ InWindow F n t)

/-- Outstanding exposure at time `t`: the total weight of positions whose window is still
open. -/
def exposure (F : ℕ → ℕ) (Ω : Finset ℕ) (a : ℕ → ℚ) (t : ℕ) : ℚ :=
  ∑ n ∈ Ω with InWindow F n t, a n

/-! ## Weak duality -/

/-- `ν ≤ τ`: disjoint windows need distinct piercing points. Source: same report, §1,
Lemma 1, first line of the proof. -/
theorem card_le_card_of_pierces {F : ℕ → ℕ} {Ω Pset T : Finset ℕ}
    (hT : T ⊆ Ω) (hdisj : WindowsDisjoint F T) (hP : Pierces F Pset Ω) :
    T.card ≤ Pset.card := by
  classical
  have hex : ∀ m ∈ T, ∃ t, t ∈ Pset ∧ InWindow F m t := by
    intro m hm
    obtain ⟨t, ht, hw⟩ := hP m (hT hm)
    exact ⟨t, ht, hw⟩
  choose! f hf1 hf2 using hex
  refine Finset.card_le_card_of_injOn f (fun m hm => hf1 m hm) ?_
  intro a ha b hb hab
  by_contra hne
  exact hdisj a ha b hb hne (f a) ⟨hf2 a ha, by rw [hab]; exact hf2 b hb⟩

/-! ## Lemma 1 — greedy duality -/

/-- **Lemma 1.** Source: `prompts/2026-08-11-deference-densification/REPORT.md` §1.

Greedy produces a piercing set and a pairwise-disjoint subfamily of the same size. The only
hypothesis is the source's standing `F(n) > n`; monotonicity is *not* needed, and the
source's §4 flags that as the reason the exact bound survives non-monotone delay while the
orbit formula does not.

Greedy is the source's: take the index of least `F` still uncovered, pierce at `F(m) − 1`,
and drop everything the point meets — which, since `F(m)` is least, is exactly the indices
below `F(m)`. -/
theorem greedy_duality {F : ℕ → ℕ} (hF : ∀ n, n < F n) (Ω : Finset ℕ) :
    ∃ Pset T : Finset ℕ, T ⊆ Ω ∧ Pierces F Pset Ω ∧ WindowsDisjoint F T ∧
      Pset.card = T.card := by
  classical
  induction hn : Ω.card using Nat.strong_induction_on generalizing Ω with
  | _ k ih =>
    rcases Finset.eq_empty_or_nonempty Ω with rfl | hne
    · exact ⟨∅, ∅, Finset.Subset.refl _, by simp [Pierces], by simp [WindowsDisjoint], rfl⟩
    obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image Ω F hne
    set R : Finset ℕ := Ω.filter (fun n => F m ≤ n) with hR
    have hRsub : R ⊆ Ω := Finset.filter_subset _ _
    have hmR : m ∉ R := by
      simp only [hR, Finset.mem_filter, not_and]
      intro _
      exact not_le.mpr (hF m)
    have hRlt : R.card < Ω.card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hRsub).mpr ⟨m, hm, hmR⟩)
    obtain ⟨P', T', hT'sub, hP', hdisj', hcard'⟩ := ih R.card (hn ▸ hRlt) R rfl
    refine ⟨insert (F m - 1) P', insert m T', ?_, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hm (hT'sub.trans hRsub)
    · intro n hnΩ
      by_cases hnR : n ∈ R
      · obtain ⟨t, ht, hw⟩ := hP' n hnR
        exact ⟨t, Finset.mem_insert_of_mem ht, hw⟩
      · refine ⟨F m - 1, Finset.mem_insert_self _ _, ?_, ?_⟩
        · have : ¬ (F m ≤ n) := by
            simp only [hR, Finset.mem_filter, not_and] at hnR
            exact hnR hnΩ
          omega
        · have h1 : F m ≤ F n := hmin n hnΩ
          have h2 := hF m
          omega
    · intro x hx y hy hxy t ht
      have hstep : ∀ n ∈ T', ∀ s, ¬ (InWindow F m s ∧ InWindow F n s) := by
        intro n hn' s hs
        have hFn : F m ≤ n := by
          have := hT'sub hn'
          simp only [hR, Finset.mem_filter] at this
          exact this.2
        obtain ⟨⟨_, h2⟩, ⟨h3, _⟩⟩ := hs
        omega
      rcases Finset.mem_insert.mp hx with rfl | hx' <;>
        rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hxy rfl
      · exact hstep y hy' t ht
      · exact hstep x hx' t ⟨ht.2, ht.1⟩
      · exact hdisj' x hx' y hy' hxy t ht
    · have hins : (insert m T').card = T'.card + 1 :=
        Finset.card_insert_of_notMem (fun h => hmR (hT'sub h))
      have hle : (insert m T').card ≤ (insert (F m - 1) P').card := by
        refine card_le_card_of_pierces (F := F) (Finset.insert_subset hm (hT'sub.trans hRsub)) ?_ ?_
        · intro x hx y hy hxy t ht
          have hstep : ∀ n ∈ T', ∀ s, ¬ (InWindow F m s ∧ InWindow F n s) := by
            intro n hn' s hs
            have hFn : F m ≤ n := by
              have := hT'sub hn'
              simp only [hR, Finset.mem_filter] at this
              exact this.2
            obtain ⟨⟨_, h2⟩, ⟨h3, _⟩⟩ := hs
            omega
          rcases Finset.mem_insert.mp hx with rfl | hx' <;>
            rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact hxy rfl
          · exact hstep y hy' t ht
          · exact hstep x hx' t ⟨ht.2, ht.1⟩
          · exact hdisj' x hx' y hy' hxy t ht
        · intro n hnΩ
          by_cases hnR : n ∈ R
          · obtain ⟨t, ht, hw⟩ := hP' n hnR
            exact ⟨t, Finset.mem_insert_of_mem ht, hw⟩
          · refine ⟨F m - 1, Finset.mem_insert_self _ _, ?_, ?_⟩
            · have : ¬ (F m ≤ n) := by
                simp only [hR, Finset.mem_filter, not_and] at hnR
                exact hnR hnΩ
              omega
            · have h1 : F m ≤ F n := hmin n hnΩ
              have h2 := hF m
              omega
      have hle2 : (insert (F m - 1) P').card ≤ P'.card + 1 := Finset.card_insert_le _ _
      omega

/-- The disjoint family greedy returns is a maximum: `ν` is attained at it. -/
theorem greedy_disjoint_maximum {F : ℕ → ℕ} {Ω Pset T T' : Finset ℕ}
    (hP : Pierces F Pset Ω) (hcard : Pset.card = T.card)
    (hT'sub : T' ⊆ Ω) (hT'disj : WindowsDisjoint F T') :
    T'.card ≤ T.card :=
  hcard ▸ card_le_card_of_pierces hT'sub hT'disj hP

/-- The piercing set greedy returns is a minimum: `τ` is attained at it. -/
theorem greedy_piercing_minimum {F : ℕ → ℕ} {Ω Pset Pset' T : Finset ℕ}
    (hT : T ⊆ Ω) (hTdisj : WindowsDisjoint F T) (hcard : Pset.card = T.card)
    (hP' : Pierces F Pset' Ω) :
    Pset.card ≤ Pset'.card :=
  hcard ▸ card_le_card_of_pierces hT hTdisj hP'

/-! ## Theorem 2 — the exact exposure–harvest bound -/

/-- **Theorem 2, the bound.** Source: same report, §1. Under a pointwise exposure cap `M`,
the total placed weight is at most the packing number times `M` — here, at most the size of
any piercing set times `M`, which by Lemma 1 is the packing number.

The quantification is over all nonnegative offline weightings, which is the source's
"adaptivity buys nothing": no decision-time placement rule can exceed it. -/
theorem exposure_harvest_bound {F : ℕ → ℕ} {Ω Pset : Finset ℕ} {a : ℕ → ℚ} {M : ℚ}
    (ha : ∀ n, 0 ≤ a n) (hP : Pierces F Pset Ω) (hE : ∀ t, exposure F Ω a t ≤ M) :
    ∑ n ∈ Ω, a n ≤ Pset.card * M := by
  classical
  have hex : ∀ n ∈ Ω, ∃ t, t ∈ Pset ∧ InWindow F n t := by
    intro n hn
    obtain ⟨t, ht, hw⟩ := hP n hn
    exact ⟨t, ht, hw⟩
  choose! f hf1 hf2 using hex
  calc ∑ n ∈ Ω, a n = ∑ t ∈ Pset, ∑ n ∈ Ω with f n = t, a n :=
        (Finset.sum_fiberwise_of_maps_to (fun n hn => hf1 n hn) a).symm
    _ ≤ ∑ t ∈ Pset, exposure F Ω a t := by
        refine Finset.sum_le_sum fun t _ => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => ha n)
        intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, by rw [← hn.2]; exact hf2 n hn.1⟩
    _ ≤ ∑ _t ∈ Pset, M := Finset.sum_le_sum fun t _ => hE t
    _ = Pset.card * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Theorem 2, the attainment.** Source: same report, §1. Weight `M` on a pairwise
disjoint family respects the cap pointwise and places exactly `|T| · M` — so the bound of
`exposure_harvest_bound` is an exact value, not an estimate. -/
theorem exposure_harvest_attained {F : ℕ → ℕ} {T : Finset ℕ} {M : ℚ} (hM : 0 ≤ M)
    (hdisj : WindowsDisjoint F T) :
    (∀ t, exposure F T (fun n => if n ∈ T then M else 0) t ≤ M)
      ∧ ∑ n ∈ T, (if n ∈ T then M else 0) = T.card * M := by
  classical
  constructor
  · intro t
    have hcard : (T.filter (fun n => InWindow F n t)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy => ?_
      simp only [Finset.mem_filter] at hx hy
      by_contra hne
      exact hdisj x hx.1 y hy.1 hne t ⟨hx.2, hy.2⟩
    have hval : exposure F T (fun n => if n ∈ T then M else 0) t
        = (T.filter (fun n => InWindow F n t)).card * M := by
      unfold exposure
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun n hn => if_pos (Finset.mem_filter.mp hn).1
    rw [hval]
    have : ((T.filter (fun n => InWindow F n t)).card : ℚ) ≤ 1 := by exact_mod_cast hcard
    nlinarith
  · rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun n hn => if_pos hn

/-- **Corollary 3, the harvest cap.** Source: same report, §1. -/
theorem harvest_cap {F : ℕ → ℕ} {Ω Pset : Finset ℕ} {a D : ℕ → ℚ} {M Dbar : ℚ}
    (ha : ∀ n, 0 ≤ a n) (hD : ∀ n, 0 ≤ D n) (hDbar : ∀ n, D n ≤ Dbar)
    (hP : Pierces F Pset Ω) (hE : ∀ t, exposure F Ω a t ≤ M) :
    ∑ n ∈ Ω, a n * D n ≤ Dbar * (Pset.card * M) := by
  have hDbar0 : 0 ≤ Dbar := le_trans (hD 0) (hDbar 0)
  calc ∑ n ∈ Ω, a n * D n ≤ ∑ n ∈ Ω, a n * Dbar :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hDbar n) (ha n)
    _ = Dbar * ∑ n ∈ Ω, a n := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ Dbar * (Pset.card * M) :=
        mul_le_mul_of_nonneg_left (exposure_harvest_bound ha hP hE) hDbar0

/-! ## The greedy family at `F(n) = 2n+1` — the inhabitation witness

Source: same report, §1 (Theorem 5's construction, `n_{k+1} = min {n ∈ S : n ≥ F(n_k)}`)
and the `2n+1` row of its regime tables. Starting at `0`, greedy's orbit is `0, 1, 3`
within `[0, 10]`; the windows `[0,1)`, `[1,3)`, `[3,7)` are pairwise disjoint, and
`{0, 2, 6}` — the points `F(n) − 1` — pierces them. Three windows, three points: the packing
number and the piercing number agree at `3`, and the placement `a ≡ M` on the orbit attains
`3M`.
-/

namespace Greedy

/-- The exponential-type delay regime `F(n) = 2n+1` of the source's tables. -/
def F : ℕ → ℕ := fun n => 2 * n + 1

theorem F_gt : ∀ n, n < F n := by intro n; unfold F; omega

def orbit : Finset ℕ := {0, 1, 3}
def points : Finset ℕ := {0, 2, 6}

theorem orbit_disjoint : WindowsDisjoint F orbit := by
  intro m hm n hn hmn t ht
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ht
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hm hn
  simp only [F] at h2 h4
  rcases hm with rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl <;> omega

theorem points_pierce : Pierces F points orbit := by
  intro n hn
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨0, by decide, by simp only [InWindow, F]; omega⟩
  · exact ⟨2, by decide, by simp only [InWindow, F]; omega⟩
  · exact ⟨6, by decide, by simp only [InWindow, F]; omega⟩

theorem orbit_card : orbit.card = 3 := by decide

theorem points_card : points.card = 3 := by decide

theorem card_eq : points.card = orbit.card := by rw [orbit_card, points_card]

/-- Lemma 1's conclusion is inhabited: the packing number and the piercing number of this
family both equal `3`, and both are attained by the exhibited pair. -/
theorem duality_nonvacuous :
    orbit ⊆ orbit ∧ Pierces F points orbit ∧ WindowsDisjoint F orbit ∧
      points.card = orbit.card :=
  ⟨Finset.Subset.refl _, points_pierce, orbit_disjoint, card_eq⟩

/-- The unit placement on the orbit. -/
def a : ℕ → ℚ := fun n => if n ∈ orbit then 1 else 0

theorem a_nonneg : ∀ n, 0 ≤ a n := by
  intro n
  unfold a
  split <;> norm_num

theorem exposure_le_one : ∀ t, exposure F orbit a t ≤ 1 := fun t =>
  (exposure_harvest_attained (F := F) (T := orbit) (M := 1) (by norm_num) orbit_disjoint).1 t

theorem placed_weight : ∑ n ∈ orbit, a n = 3 := by
  have h := (exposure_harvest_attained (F := F) (T := orbit) (M := 1) (by norm_num)
    orbit_disjoint).2
  rw [orbit_card] at h
  show ∑ n ∈ orbit, (if n ∈ orbit then (1 : ℚ) else 0) = 3
  rw [h]
  norm_num

/-- Theorem 2 at the witness, with the bound attained: `3 = |P| · M`. -/
theorem bound_attained : ∑ n ∈ orbit, a n = points.card * (1 : ℚ) := by
  rw [placed_weight, points_card]
  norm_num

theorem theorem2_nonvacuous : ∑ n ∈ orbit, a n ≤ points.card * (1 : ℚ) :=
  exposure_harvest_bound a_nonneg points_pierce exposure_le_one

end Greedy

#print axioms card_le_card_of_pierces
#print axioms greedy_duality
#print axioms greedy_disjoint_maximum
#print axioms greedy_piercing_minimum
#print axioms exposure_harvest_bound
#print axioms exposure_harvest_attained
#print axioms harvest_cap
#print axioms Greedy.F_gt
#print axioms Greedy.orbit_disjoint
#print axioms Greedy.points_pierce
#print axioms Greedy.orbit_card
#print axioms Greedy.points_card
#print axioms Greedy.card_eq
#print axioms Greedy.duality_nonvacuous
#print axioms Greedy.a_nonneg
#print axioms Greedy.exposure_le_one
#print axioms Greedy.placed_weight
#print axioms Greedy.bound_attained
#print axioms Greedy.theorem2_nonvacuous

end Workspace.Deference.Contrib.ExposureGeometry
