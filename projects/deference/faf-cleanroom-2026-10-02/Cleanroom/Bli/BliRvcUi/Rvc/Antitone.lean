import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# `bli-rvc-ui` · Rvc/Antitone: `RVC_B` is the antitone characterization (T2.1, the cheap half)

**The claim.** A threshold-belief profile on a finite threshold set `R` is the profile of a finite
mixture of point values in `[0,1]` (`RVC_B`) **iff** it lies in `[0,1]`, is antitone in the
threshold, is `1` below `0` and `0` at or above `1` (`ThresholdAntitone`).

**Route (⟸).** Sort the thresholds of `R` inside `[0,1)` as `r₁ < ⋯ < rₘ`. Put mass `1 − V(r₁)` at
the point `0`, mass `V(rⱼ) − V(rⱼ₊₁)` strictly inside the gap `(rⱼ, rⱼ₊₁)` (at its midpoint) and
mass `V(rₘ)` inside `(rₘ, 1)` — never *on* a threshold, because FAF's cut semantics is agnostic
at the value itself (mandate T2.1's trap). Thresholds below `0` see all the mass, thresholds at or
above `1` see none. The construction is by induction on the sorted list, generic over the ordered
field so that the same lemma serves the rational (two-axiom) and real (`RVC_B`) sides.

**Route (⟹).** From the mixture: indicators are antitone in `r` and in `{0,1}`, so the profile is.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset

section MixTotal

variable {K : Type*} [Field K]

/-- The total weight of a list of (point, weight) pairs.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def mixTotal (m : List (K × K)) : K := (m.map Prod.snd).sum

/-- `mixTotal_nil`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mixTotal_nil : mixTotal ([] : List (K × K)) = 0 := rfl

/-- `mixTotal_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mixTotal_cons (p : K × K) (m : List (K × K)) :
    mixTotal (p :: m) = p.2 + mixTotal m := by
  simp [mixTotal]

/-- Sum over `Fin m.length` of a function of the entries is the list sum of the mapped list.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_fin_get {α : Type*} (g : α → K) : ∀ (m : List α),
    ∑ i : Fin m.length, g (m.get i) = (m.map g).sum
  | [] => by simp
  | a :: m => by
      show ∑ i : Fin (m.length + 1), g ((a :: m).get i) = _
      rw [Fin.sum_univ_succ, List.map_cons, List.sum_cons, ← sum_fin_get g m]
      rfl

end MixTotal

section MixMass

variable {K : Type*} [Field K] [LinearOrder K]

/-- The weight the list puts strictly above the threshold `r`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def mixMass (m : List (K × K)) (r : ℚ) : K :=
  (m.map (fun p => if (r : K) < p.1 then p.2 else 0)).sum

/-- `mixMass_nil`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mixMass_nil (r : ℚ) : mixMass ([] : List (K × K)) r = 0 := rfl

/-- `mixMass_cons`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mixMass_cons (p : K × K) (m : List (K × K)) (r : ℚ) :
    mixMass (p :: m) r = (if (r : K) < p.1 then p.2 else 0) + mixMass m r := by
  simp [mixMass]

/-- Mass above a threshold lying below every point is the total.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixMass_eq_total {m : List (K × K)} {r : ℚ} (h : ∀ p ∈ m, (r : K) < p.1) :
    mixMass m r = mixTotal m := by
  induction m with
  | nil => rfl
  | cons p m ih =>
      rw [mixMass_cons, mixTotal_cons, if_pos (h p (List.mem_cons_self ..)),
        ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- Mass above a threshold lying at or above every point is zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mixMass_eq_zero {m : List (K × K)} {r : ℚ} (h : ∀ p ∈ m, p.1 ≤ (r : K)) :
    mixMass m r = 0 := by
  induction m with
  | nil => rfl
  | cons p m ih =>
      rw [mixMass_cons, if_neg (not_lt.mpr (h p (List.mem_cons_self ..))),
        ih fun q hq => h q (List.mem_cons_of_mem _ hq), zero_add]

end MixMass

section Mixture

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The mixture construction on a sorted list of thresholds in `[0,1)`.** For `f` antitone and
`[0,1]`-valued on a strictly increasing list `l ⊆ [0,1)`, there is a rest-list of (point, weight)
pairs with points in `(head l, 1]` and nonnegative weights, of total `f (head l)` (or `0` if `l` is
empty), whose mass above each `r ∈ l` is exactly `f r`. (The final mixture adds the point `0` with
the complementary weight.)
Source: mandate T2.1 route (the telescoping construction), made inductive
Kind: P
Fidelity: n/a -/
theorem exists_rest_mixture (f : ℚ → K) : ∀ (l : List ℚ), l.Pairwise (· < ·) →
    (∀ r ∈ l, 0 ≤ r ∧ r < 1) → (∀ r ∈ l, 0 ≤ f r ∧ f r ≤ 1) →
    (∀ r ∈ l, ∀ s ∈ l, r < s → f s ≤ f r) →
    ∃ rest : List (K × K), (∀ p ∈ rest, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2) ∧
      (∀ p ∈ rest, ∀ s ∈ l.head?, (s : K) < p.1) ∧
      mixTotal rest = (l.head?.map f).getD 0 ∧
      ∀ r ∈ l, mixMass rest r = f r
  | [], _, _, _, _ => ⟨[], by simp, by simp, by simp, by simp⟩
  | [r], _, hrange, hf, _ => by
      have hr := hrange r (List.mem_singleton_self r)
      have hfr := hf r (List.mem_singleton_self r)
      refine ⟨[(((r : K) + 1) / 2, f r)], ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        have h0 : (0 : K) ≤ r := by exact_mod_cast hr.1
        have h1 : (r : K) < 1 := by exact_mod_cast hr.2
        refine ⟨by linarith, by linarith, hfr.1⟩
      · intro p hp s hs
        rw [List.mem_singleton] at hp
        subst hp
        have hsr : s = r := by simpa [Option.mem_def, eq_comm] using hs
        rw [hsr]
        have h1 : (r : K) < 1 := by exact_mod_cast hr.2
        show (r : K) < ((r : K) + 1) / 2
        linarith
      · simp [mixTotal]
      · intro r' hr'
        rw [List.mem_singleton] at hr'
        subst hr'
        have h1 : (r' : K) < 1 := by exact_mod_cast hr.2
        rw [mixMass_cons, mixMass_nil, if_pos (by linarith), add_zero]
  | r :: s :: l, hsorted, hrange, hf, hanti => by
      have hsorted' : (s :: l).Pairwise (· < ·) := hsorted.of_cons
      have hrs : r < s := List.rel_of_pairwise_cons hsorted (List.mem_cons_self ..)
      obtain ⟨rest, hpts, hhead, htot, hmass⟩ := exists_rest_mixture f (s :: l) hsorted'
        (fun r' hr' => hrange r' (List.mem_cons_of_mem _ hr'))
        (fun r' hr' => hf r' (List.mem_cons_of_mem _ hr'))
        (fun r' hr' s' hs' h => hanti r' (List.mem_cons_of_mem _ hr') s'
          (List.mem_cons_of_mem _ hs') h)
      have hr := hrange r (List.mem_cons_self ..)
      have hs := hrange s (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hfr := hf r (List.mem_cons_self ..)
      have hfsr : f s ≤ f r := hanti r (List.mem_cons_self ..) s
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hrs
      have htot' : mixTotal rest = f s := by simpa using htot
      have hrK : (r : K) < s := by exact_mod_cast hrs
      have hr0 : (0 : K) ≤ r := by exact_mod_cast hr.1
      have hs1 : (s : K) < 1 := by exact_mod_cast hs.2
      have hheads : ∀ p ∈ rest, (s : K) < p.1 := fun p hp => hhead p hp s (by simp)
      refine ⟨(((r : K) + s) / 2, f r - f s) :: rest, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨by dsimp only; linarith, by dsimp only; linarith, by dsimp only; linarith⟩
        · exact hpts p hp
      · intro p hp t ht
        have htr : t = r := by simpa [Option.mem_def, eq_comm] using ht
        rw [htr]
        rw [List.mem_cons] at hp
        rcases hp with rfl | hp
        · show (r : K) < ((r : K) + s) / 2
          linarith
        · exact lt_trans hrK (hheads p hp)
      · rw [mixTotal_cons, htot']
        simp
      · intro r' hr'
        rw [List.mem_cons] at hr'
        rcases hr' with rfl | hr'
        · rw [mixMass_cons, if_pos (by dsimp only; linarith),
            mixMass_eq_total (fun p hp => lt_trans hrK (hheads p hp)), htot']
          ring
        · have hsr' : s ≤ r' := by
            rw [List.mem_cons] at hr'
            rcases hr' with rfl | hr'
            · exact le_rfl
            · exact (List.rel_of_pairwise_cons hsorted' hr').le
          have hsr'K : (s : K) ≤ r' := by exact_mod_cast hsr'
          rw [mixMass_cons, if_neg (by dsimp only; linarith), zero_add]
          exact hmass r' hr'

end Mixture

/-! ## The antitone characterization of `RVC_B` -/

/-- **(⟹)** A mixture profile is antitone and `[0,1]`-valued, `1` below `0` and `0` at or above `1`.
Source: mandate T2.1 route
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem thresholdAntitone_of_rvcB {V : Sentence → ℝ} {X : LUV} {R : Finset ℚ}
    (h : RVC_B V X R) : ThresholdAntitone V X R := by
  obtain ⟨k, x, w, hx, hw, hw1, hV⟩ := h
  have hind : ∀ (r : ℚ) (i : Fin k), 0 ≤ (if (r : ℝ) < x i then (1 : ℝ) else 0) ∧
      (if (r : ℝ) < x i then (1 : ℝ) else 0) ≤ 1 := by
    intro r i
    split_ifs <;> norm_num
  refine ⟨fun r hr => ?_, fun r hr r' hr' hlt => ?_, fun r hr hlt => ?_, fun r hr hle => ?_⟩
  · rw [hV r hr]
    constructor
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hind r i).1
    · calc ∑ i, w i * (if (r : ℝ) < x i then (1 : ℝ) else 0)
          ≤ ∑ i, w i := Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hw i) (hind r i).2
        _ = 1 := hw1
  · rw [hV r hr, hV r' hr']
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    by_cases h1 : (r : ℝ) < x i
    · have h2 : (r' : ℝ) < x i := lt_trans (by exact_mod_cast hlt) h1
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      split_ifs <;> norm_num
  · rw [hV r hr]
    calc ∑ i, w i * (if (r : ℝ) < x i then (1 : ℝ) else 0)
        = ∑ i, w i := by
          apply Finset.sum_congr rfl
          intro i _
          have : (r : ℝ) < x i := lt_of_lt_of_le (by exact_mod_cast hlt) (hx i).1
          rw [if_pos this, mul_one]
      _ = 1 := hw1
  · rw [hV r hr]
    apply Finset.sum_eq_zero
    intro i _
    have : ¬ (r : ℝ) < x i := not_lt.mpr (le_trans (hx i).2 (by exact_mod_cast hle))
    rw [if_neg this, mul_zero]

/-- The thresholds of `R` inside `[0,1)`, sorted.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def innerThresholds (R : Finset ℚ) : List ℚ :=
  (R.filter (fun r => 0 ≤ r ∧ r < 1)).sort (· ≤ ·)

/-- `mem_innerThresholds`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_innerThresholds {R : Finset ℚ} {r : ℚ} :
    r ∈ innerThresholds R ↔ r ∈ R ∧ 0 ≤ r ∧ r < 1 := by
  simp [innerThresholds, Finset.mem_sort, Finset.mem_filter]

/-- `innerThresholds_sorted`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma innerThresholds_sorted (R : Finset ℚ) : (innerThresholds R).Pairwise (· < ·) :=
  List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)

/-- **(⟸)** An antitone, `[0,1]`-valued threshold profile that is `1` below `0` and `0` at or above
`1` is the profile of a finite mixture of point values, over any ordered field: the mixture is
`exists_rest_mixture`'s rest-list plus the point `0` with the complementary weight.
Source: mandate T2.1 route
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_mixture_of_thresholdAntitone {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {V : Sentence → K} {X : LUV} {R : Finset ℚ}
    (h : ThresholdAntitone V X R) :
    ∃ m : List (K × K), (∀ p ∈ m, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2) ∧ mixTotal m = 1 ∧
      ∀ r ∈ R, V (X.gt r) = mixMass m r := by
  obtain ⟨h0, hanti, hneg, hone⟩ := h
  set l := innerThresholds R with hl
  have hmem : ∀ r, r ∈ l ↔ r ∈ R ∧ 0 ≤ r ∧ r < 1 := fun r => mem_innerThresholds
  obtain ⟨rest, hpts, hhead, htot, hmass⟩ := exists_rest_mixture (fun r => V (X.gt r)) l
    (innerThresholds_sorted R)
    (fun r hr => ((hmem r).mp hr).2)
    (fun r hr => h0 r ((hmem r).mp hr).1)
    (fun r hr s hs hlt => hanti s ((hmem s).mp hs).1 r ((hmem r).mp hr).1 hlt)
  -- the head weight
  set w₀ : K := 1 - mixTotal rest with hw₀
  have hw₀nn : 0 ≤ w₀ := by
    rw [hw₀, htot, sub_nonneg]
    cases hhd : l.head? with
    | none => simp
    | some s =>
        simp only [Option.map_some, Option.getD_some]
        have hs : s ∈ l := List.mem_of_mem_head? hhd
        exact (h0 s ((hmem s).mp hs).1).2
  refine ⟨((0 : K), w₀) :: rest, ?_, ?_, ?_⟩
  · intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨le_rfl, zero_le_one, hw₀nn⟩
    · exact hpts p hp
  · rw [mixTotal_cons, hw₀]
    ring
  · intro r hr
    by_cases hr0 : r < 0
    · -- every point (all in `[0,1]`) is above `r`
      rw [hneg r hr hr0, mixMass_eq_total]
      · rw [mixTotal_cons, hw₀]; ring
      · intro p hp
        rw [List.mem_cons] at hp
        have hrK : (r : K) < 0 := by exact_mod_cast hr0
        rcases hp with rfl | hp
        · exact hrK
        · exact lt_of_lt_of_le hrK (hpts p hp).1
    · by_cases hr1 : 1 ≤ r
      · rw [hone r hr hr1, mixMass_eq_zero]
        intro p hp
        rw [List.mem_cons] at hp
        have hrK : (1 : K) ≤ r := by exact_mod_cast hr1
        rcases hp with rfl | hp
        · exact le_trans zero_le_one hrK
        · exact le_trans (hpts p hp).2.1 hrK
      · have hrl : r ∈ l := (hmem r).mpr ⟨hr, not_lt.mp hr0, not_le.mp hr1⟩
        rw [mixMass_cons, if_neg (by
          show ¬ (r : K) < (0 : K)
          exact not_lt.mpr (by exact_mod_cast (not_lt.mp hr0))), zero_add]
        exact (hmass r hrl).symm

/-- **`RVC_B` ⟺ the antitone characterization** (real-valued profiles).
Source: mandate T2.1 route (`rvcB_iff_antitone`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem rvcB_iff_antitone {V : Sentence → ℝ} {X : LUV} {R : Finset ℚ} :
    RVC_B V X R ↔ ThresholdAntitone V X R := by
  refine ⟨thresholdAntitone_of_rvcB, fun h => ?_⟩
  obtain ⟨m, hm, htot, hV⟩ := exists_mixture_of_thresholdAntitone h
  refine ⟨m.length, fun i => (m.get i).1, fun i => (m.get i).2, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · exact ⟨(hm _ (List.get_mem m i)).1, (hm _ (List.get_mem m i)).2.1⟩
  · exact (hm _ (List.get_mem m i)).2.2
  · rw [sum_fin_get (fun p : ℝ × ℝ => p.2) m]
    exact htot
  · intro r hr
    rw [hV r hr, mixMass]
    rw [sum_fin_get (fun p : ℝ × ℝ => p.2 * (if (r : ℝ) < p.1 then 1 else 0)) m]
    congr 1
    apply List.map_congr_left
    intro p _
    split_ifs <;> ring

end Cleanroom.Bli.BliRvcUi
