/-
# Reason supply: the content residual, the service obstruction, and the composition

Round `projects/deference/rounds/2026-09-16-noncapture-compilation/`, second pass.

The steering inequality of `TraceSteering.lean` charges the advisor's advantage on the
common-audit branch at `L · d_canon`.  This module replaces the count by the quantity
the principal program actually needs, bounds it by what an independent supplier fails to
serve before the commitment deadline, characterizes when that failure is zero, and
composes the result with the landed Logical-Induction theorem so that the conclusion of
one theorem is literally the hypothesis of the next.

**1. Sensitivity** (`sensitive_symmDiff`, `adverse_union`): for an extensional program `F`
on canonical content with per-reason certificates, `|F c − F c'| ≤ Σ_{r ∈ c Δ c'} L r`,
and the advisor's *omission gain* is `F c − F (c ∪ S) ≤ Σ_{r ∈ S} A r` with `A` the
adverse sensitivity.  Weighted-count programs have `A r = (−w r)⁺`
(`weightedCount_adverse`).

**2. The service obstruction** (`served_cut_le`, `cut_of_servesAll`,
`unit_servable_iff_cut`): reasons released at `a r` with costs `c r`, slots `t < T` with
capacities; for every `s`, the cost served from reasons released at or after `s` is at
most the capacity of `[s, T)`; so full service forces the suffix-cut condition, and for
unit costs and unit slots the suffix-cut condition is also sufficient (Hall).

**3. Protected scope as a design parameter** (`hybrid_bound`): on the audited branch only
the *unprotected* missing mass is charged; a missing protected reason turns the audit off.

**4. Composition** (`li_gated_le`, `expect_constLUV`, `li_noncapture`): a family of
gated LUVs bounded by `α` in every consistent world has expectation `≲ α`; with a
certified content bound `α`, an extensional program and a sealed audit, the landed
theorem gives `𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α`.

Nothing of Logical Induction is re-proved.  Names are provisional (`AGENTS.md`
standard 6).
-/
import Workspace.Deference.Contrib.TraceSteering
import Mathlib.Combinatorics.Hall.Basic

namespace Workspace.Deference.Contrib.ReasonSupply

open LogicalInduction
open Workspace.Deference.Contrib.LICorrigibility
open Workspace.Deference.Contrib.TraceSteering
open scoped Classical
open Finset

/-! ## 1. Sensitivity certificates of an extensional program -/

section Sensitivity

variable {ι : Type*} [DecidableEq ι]

/-- Per-reason sensitivity: adding one reason moves the verdict by at most `L r`. -/
def Sensitive (F : Finset ι → ℝ) (L : ι → ℝ) : Prop :=
  ∀ (c : Finset ι) (r : ι), r ∉ c → |F (insert r c) - F c| ≤ L r

/-- Per-reason adverse sensitivity: adding one reason *lowers* the verdict by at most
`A r`.  This is what the advisor gains from the reason's absence. -/
def Adverse (F : Finset ι → ℝ) (A : ι → ℝ) : Prop :=
  ∀ (c : Finset ι) (r : ι), r ∉ c → F c - F (insert r c) ≤ A r

theorem sensitive_union {F : Finset ι → ℝ} {L : ι → ℝ} (h : Sensitive F L)
    (c s : Finset ι) (hd : Disjoint s c) : |F (c ∪ s) - F c| ≤ ∑ r ∈ s, L r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hd' : Disjoint s c := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hd
    have hac : a ∉ c := Finset.disjoint_left.mp hd (Finset.mem_insert_self a s)
    have hnot : a ∉ c ∪ s := by simp [hac, ha]
    have h1 := h (c ∪ s) a hnot
    have h2 := ih hd'
    rw [Finset.sum_insert ha, Finset.union_insert]
    calc |F (insert a (c ∪ s)) - F c|
        = |(F (insert a (c ∪ s)) - F (c ∪ s)) - (F c - F (c ∪ s))| := by ring_nf
      _ ≤ |F (insert a (c ∪ s)) - F (c ∪ s)| + |F c - F (c ∪ s)| := abs_sub _ _
      _ = |F (insert a (c ∪ s)) - F (c ∪ s)| + |F (c ∪ s) - F c| := by
          rw [abs_sub_comm (F c)]
      _ ≤ L a + ∑ r ∈ s, L r := add_le_add h1 h2

/-- **The telescoping bound.**  Two canonical contents differ in verdict by at most the
sensitivity mass of their symmetric difference. -/
theorem sensitive_symmDiff {F : Finset ι → ℝ} {L : ι → ℝ} (h : Sensitive F L)
    (c c' : Finset ι) : |F c - F c'| ≤ ∑ r ∈ (c \ c' ∪ c' \ c), L r := by
  have h1 : |F (c ∪ (c' \ c)) - F c| ≤ ∑ r ∈ c' \ c, L r :=
    sensitive_union h c (c' \ c) Finset.sdiff_disjoint
  have h2 : |F (c' ∪ (c \ c')) - F c'| ≤ ∑ r ∈ c \ c', L r :=
    sensitive_union h c' (c \ c') Finset.sdiff_disjoint
  rw [Finset.union_sdiff_self_eq_union] at h1
  rw [Finset.union_sdiff_self_eq_union, Finset.union_comm] at h2
  have hdisj : Disjoint (c \ c') (c' \ c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  rw [Finset.sum_union hdisj]
  calc |F c - F c'| = |(F (c ∪ c') - F c') - (F (c ∪ c') - F c)| := by ring_nf
    _ ≤ |F (c ∪ c') - F c'| + |F (c ∪ c') - F c| := abs_sub _ _
    _ ≤ ∑ r ∈ c \ c', L r + ∑ r ∈ c' \ c, L r := add_le_add h2 h1

/-- **The omission gain.**  What the advisor's candidate gains from the absence of the
reasons `s` is at most their adverse sensitivity mass. -/
theorem adverse_union {F : Finset ι → ℝ} {A : ι → ℝ} (h : Adverse F A)
    (c s : Finset ι) (hd : Disjoint s c) : F c - F (c ∪ s) ≤ ∑ r ∈ s, A r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hd' : Disjoint s c := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hd
    have hac : a ∉ c := Finset.disjoint_left.mp hd (Finset.mem_insert_self a s)
    have hnot : a ∉ c ∪ s := by simp [hac, ha]
    have h1 := h (c ∪ s) a hnot
    have h2 := ih hd'
    rw [Finset.sum_insert ha, Finset.union_insert]
    linarith

/-- Weighted-count programs: the adverse sensitivity of a reason is the negative part of
its weight. -/
theorem weightedCount_adverse (w : ι → ℝ) :
    Adverse (weightedCount w) (fun r => max 0 (-w r)) := by
  intro c r hr
  simp only [weightedCount, Finset.sum_insert hr]
  linarith [le_max_right 0 (-w r)]

/-- Weighted-count programs: the symmetric sensitivity is the absolute weight. -/
theorem weightedCount_sensitive (w : ι → ℝ) : Sensitive (weightedCount w) (fun r => |w r|) := by
  intro c r hr
  simp only [weightedCount, Finset.sum_insert hr, add_sub_cancel_right, le_refl]

end Sensitivity

/-! ## 2. The service obstruction -/

section Service

variable {ι : Type*} [Fintype ι]

/-- A supply instance: discovery slot, service cost, the commitment deadline `T` (slots
`t < T` are available), and the capacity of each slot. -/
structure Instance (ι : Type*) where
  release : ι → ℕ
  cost : ι → ℕ
  T : ℕ
  cap : ℕ → ℕ

/-- The capacity of the slots `[s, T)`. -/
def Instance.Cap (I : Instance ι) (s : ℕ) : ℕ := ∑ t ∈ Finset.Ico s I.T, I.cap t

/-- The reasons released at or after `s`. -/
def Instance.late (I : Instance ι) (s : ℕ) : Finset ι := univ.filter (fun r => s ≤ I.release r)

/-- The service cost of the reasons released at or after `s`. -/
def Instance.Demand (I : Instance ι) (s : ℕ) : ℕ := ∑ r ∈ I.late s, I.cost r

/-- **The suffix-cut condition**: at every `s`, what is released at or after `s` fits in
the capacity that remains. -/
def Instance.CutCondition (I : Instance ι) : Prop := ∀ s, I.Demand s ≤ I.Cap s

/-- A preemptive schedule: units of service assigned to reasons at slots, none before a
reason's release, none at or after the deadline, within capacity. -/
structure Schedule (I : Instance ι) where
  x : ι → ℕ → ℕ
  release_ok : ∀ r t, t < I.release r → x r t = 0
  horizon : ∀ r t, I.T ≤ t → x r t = 0
  cap_ok : ∀ t, ∑ r, x r t ≤ I.cap t

/-- The units a reason receives before the deadline. -/
def Schedule.served {I : Instance ι} (S : Schedule I) (r : ι) : ℕ :=
  ∑ t ∈ Finset.range I.T, S.x r t

/-- Every reason is fully served. -/
def Schedule.ServesAll {I : Instance ι} (S : Schedule I) : Prop := ∀ r, S.served r = I.cost r

/-- **The cut bound.**  The service received by the reasons released at or after `s` is
at most the capacity of `[s, T)`. -/
theorem served_cut_le {I : Instance ι} (S : Schedule I) (s : ℕ) :
    ∑ r ∈ I.late s, S.served r ≤ I.Cap s := by
  have hwin : ∀ r ∈ I.late s, S.served r = ∑ t ∈ Finset.Ico s I.T, S.x r t := by
    intro r hr
    have hs : s ≤ I.release r := (Finset.mem_filter.mp hr).2
    unfold Schedule.served
    symm
    apply Finset.sum_subset
    · intro t ht
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
    · intro t ht hnot
      have ht' : t < I.T := Finset.mem_range.mp ht
      have : t < s := by
        by_contra hc
        exact hnot (Finset.mem_Ico.mpr ⟨not_lt.mp hc, ht'⟩)
      exact S.release_ok r t (lt_of_lt_of_le this hs)
  rw [Finset.sum_congr rfl hwin, Finset.sum_comm]
  unfold Instance.Cap
  apply Finset.sum_le_sum
  intro t _
  calc ∑ r ∈ I.late s, S.x r t ≤ ∑ r, S.x r t :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ I.cap t := S.cap_ok t

/-- **Necessity.**  Full service forces the suffix-cut condition. -/
theorem cut_of_servesAll {I : Instance ι} (S : Schedule I) (h : S.ServesAll) :
    I.CutCondition := by
  intro s
  have := served_cut_le S s
  unfold Instance.Demand
  rw [Finset.sum_congr rfl (fun r _ => (h r).symm)]
  exact this

/-- **The unserved mass is at least the cut excess**: for every `s`, the cost left
unserved among the reasons released at or after `s` is at least `Demand s − Cap s`. -/
theorem unserved_ge_excess {I : Instance ι} (S : Schedule I) (s : ℕ) :
    (I.Demand s : ℤ) - I.Cap s ≤ ∑ r ∈ I.late s, ((I.cost r : ℤ) - S.served r) := by
  have := served_cut_le S s
  unfold Instance.Demand
  rw [Finset.sum_sub_distrib]
  push_cast
  have h' : ((∑ r ∈ I.late s, S.served r : ℕ) : ℤ) ≤ (I.Cap s : ℤ) := by exact_mod_cast this
  push_cast at h'
  linarith

/-- **Unit service: the cut condition is also sufficient.**  With unit costs and unit
slot capacities, a schedule serving every reason exists iff the suffix-cut condition
holds (Hall's theorem on the nested neighbourhoods `[release r, T)`). -/
theorem unit_servable_iff_cut (I : Instance ι) (hcost : ∀ r, I.cost r = 1)
    (hcap : ∀ t, I.cap t = 1) :
    (∃ f : ι → ℕ, Function.Injective f ∧ ∀ r, I.release r ≤ f r ∧ f r < I.T) ↔
      I.CutCondition := by
  have hCap : ∀ s, I.Cap s = I.T - s := by
    intro s
    unfold Instance.Cap
    simp [hcap]
  have hDem : ∀ s, I.Demand s = (I.late s).card := by
    intro s
    unfold Instance.Demand
    simp [hcost]
  -- Hall's condition for the neighbourhoods `t r = Ico (release r) T`
  have hall := Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun r : ι => Finset.Ico (I.release r) I.T)
  constructor
  · rintro ⟨f, hf, hfr⟩ s
    rw [hDem, hCap]
    -- `f` restricted to `late s` is injective into `Ico s T`
    have himg : (I.late s).image f ⊆ Finset.Ico s I.T := by
      intro t ht
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
      have hs : s ≤ I.release r := (Finset.mem_filter.mp hr).2
      exact Finset.mem_Ico.mpr ⟨hs.trans (hfr r).1, (hfr r).2⟩
    calc (I.late s).card = ((I.late s).image f).card := (Finset.card_image_of_injective _ hf).symm
      _ ≤ (Finset.Ico s I.T).card := Finset.card_le_card himg
      _ = I.T - s := Nat.card_Ico s I.T
  · intro hcut
    have hhall : ∀ S : Finset ι, S.card ≤ (S.biUnion fun r => Finset.Ico (I.release r) I.T).card := by
      intro S
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp
      · -- the earliest release in `S`
        obtain ⟨r₀, hr₀, hmin⟩ := S.exists_min_image I.release hne
        set m := I.release r₀ with hm
        have hsub : S ⊆ I.late m := by
          intro r hr
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hmin r hr⟩
        have h1 : S.card ≤ I.T - m := by
          calc S.card ≤ (I.late m).card := Finset.card_le_card hsub
            _ = I.Demand m := (hDem m).symm
            _ ≤ I.Cap m := hcut m
            _ = I.T - m := hCap m
        have h2 : Finset.Ico m I.T ⊆ S.biUnion fun r => Finset.Ico (I.release r) I.T := by
          intro t ht
          exact Finset.mem_biUnion.mpr ⟨r₀, hr₀, by simpa [hm] using ht⟩
        calc S.card ≤ I.T - m := h1
          _ = (Finset.Ico m I.T).card := (Nat.card_Ico m I.T).symm
          _ ≤ _ := Finset.card_le_card h2
    obtain ⟨f, hf, hfr⟩ := hall.mp hhall
    exact ⟨f, hf, fun r => Finset.mem_Ico.mp (hfr r)⟩

end Service

/-! ## 3. Protected scope as a design parameter -/

section Hybrid

variable {ι : Type*} [DecidableEq ι]

/-- **The hybrid bound.**  On the audited branch, the advisor's omission gain is charged
only for the *unprotected* missing reasons: the coverage barrier turns the audit off
whenever a protected true reason is missing. -/
theorem hybrid_bound {F : Finset ι → ℝ} {A : ι → ℝ} (hA : Adverse F A)
    (present full prot : Finset ι) (hsub : present ⊆ full) (audit : Bool)
    (hbarrier : audit = true → ∀ r ∈ full \ present, r ∉ prot) :
    indR audit * (F present - F full)
      ≤ indR audit * ∑ r ∈ (full \ present).filter (fun r => r ∉ prot), A r := by
  cases audit with
  | false => simp [indR]
  | true =>
    simp only [indR, if_true, one_mul]
    have hgain : F present - F full ≤ ∑ r ∈ full \ present, A r := by
      have := adverse_union hA present (full \ present) Finset.sdiff_disjoint
      rwa [Finset.union_sdiff_of_subset hsub] at this
    have hfilter : (full \ present).filter (fun r => r ∉ prot) = full \ present :=
      Finset.filter_true_of_mem (hbarrier rfl)
    rw [hfilter]
    exact hgain

end Hybrid

/-! ## 4. The composition with Logical Induction -/

section Composition

/-- Asymptotic inequalities add. -/
theorem asympLE_add {f g f' g' : ℕ → ℝ} (h : f ≲ₙ g) (h' : f' ≲ₙ g') :
    (fun n => f n + f' n) ≲ₙ fun n => g n + g' n := by
  intro ε hε
  filter_upwards [h (ε / 2) (by linarith), h' (ε / 2) (by linarith)] with n hn hn'
  linarith

/-- Asymptotic inequalities scale by nonnegative constants. -/
theorem asympLE_const_mul {f g : ℕ → ℝ} (c : ℝ) (hc : 0 ≤ c) (h : f ≲ₙ g) :
    (fun n => c * f n) ≲ₙ fun n => c * g n := by
  intro ε hε
  rcases hc.lt_or_eq with hc' | rfl
  · filter_upwards [h (ε / c) (div_pos hε hc')] with n hn
    calc c * f n ≤ c * (g n + ε / c) := mul_le_mul_of_nonneg_left hn hc
      _ = c * g n + ε := by field_simp
  · filter_upwards with n
    simp; linarith

/-- The single-LUV emission code of a constant. -/
theorem constLUV_thresholdCodes (a b : ℕ) (hb : 0 < b) :
    (constLUV ((a : ℚ) / (b : ℚ))).RpnThresholdCodes := by
  have hseq : LUV.RpnThresholdCodeSeq (fun _ => constLUV ((a : ℚ) / (b : ℚ))) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using constLUV_thresholdCodeSeq_zero
    · exact constLUV_thresholdCodeSeq_pos a b ha hb
  unfold LUV.RpnThresholdCodeSeq at hseq
  unfold LUV.RpnThresholdCodes
  refine (hseq.comp (PolyFueled.pair (PolyFueled.const 0) PolyFueled.id)).of_eq ?_
  intro m
  simp [Nat.unpair_pair]

/-- **The inductor's expectation of a constant converges to it.** -/
theorem expect_constLUV {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    (fun n => (constLUV ((a : ℚ) / (b : ℚ))).expect P n) ≈ₙ fun _ => ((a : ℚ) / (b : ℚ) : ℝ) := by
  have hq : (0 : ℚ) ≤ (a : ℚ) / (b : ℚ) ∧ (a : ℚ) / (b : ℚ) ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_one (by exact_mod_cast hb)]
      exact_mod_cast hab
  exact lic_expectation_provind_eq P DP _ (constLUV_thresholdCodes a b hb) hworld _
    (Filter.Eventually.of_forall (fun n v _ => by
      simpa using (constLUV_valuesAt v _ hq).expectApprox_near n.succ_pos))

/-- The degenerate pair: `U − α − 0·0 − 0 − 0`. -/
def gatedPair (U : LUV) (φ : Sentence) (α : ℚ) : MediatedPair where
  Uraw := U
  Ucorr := constLUV α
  Gδ := constLUV 0
  Gρ := constLUV 0
  GM := constLUV 0
  φraw := φ
  φcorr := top
  lam := 0

/-- The degenerate pair's validity package: `U` is valued `w` where `φ` holds and `0`
otherwise, with `w ≤ α` where `φ` holds. -/
def gatedPair_validAt (U : LUV) (φ : Sentence) (α : ℚ) (hq : 0 ≤ α ∧ α ≤ 1) (v : PCWorld)
    (w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) (hU : v.ValuesAt U (if v.Holds φ then w else 0))
    (hwα : v.Holds φ → w ≤ (α : ℝ)) : ValidAt (gatedPair U φ α) v where
  wr := w
  wapp := w
  wa := α
  δ := 0
  ρ := 0
  wr_mem := hw
  wa_mem := by exact_mod_cast hq
  δ_mem := ⟨le_rfl, zero_le_one⟩
  ρ_mem := ⟨le_rfl, zero_le_one⟩
  raw_val := hU
  corr_val := by
    simp only [gatedPair, holds_top v, if_true]
    exact constLUV_valuesAt v α hq
  δ_val := by
    simp only [gatedPair, ite_self]
    simpa using constLUV_valuesAt v 0 ⟨le_rfl, zero_le_one⟩
  ρ_val := by
    simp only [gatedPair, ite_self]
    simpa using constLUV_valuesAt v 0 ⟨le_rfl, zero_le_one⟩
  M_val := by
    simp only [gatedPair, holds_top v, not_true_eq_false, and_false, if_false]
    simpa using constLUV_valuesAt v 0 ⟨le_rfl, zero_le_one⟩
  lip := fun _ _ => by norm_num [gatedPair]
  regret := fun h _ => by linarith [hwα h]

/-- **A gated family bounded by `α` in every consistent world has expectation `≲ α`.**
The hypotheses are the world facts, the emission of the gating sentences and of the family,
and a consistent world at every stage; the proof routes through the landed compiled
theorem with the degenerate pair. -/
theorem li_gated_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (U : ℕ → LUV) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ w : ℝ, (0 ≤ w ∧ w ≤ 1) ∧ v.ValuesAt (U n) (if v.Holds (φ n) then w else 0) ∧
        (v.Holds (φ n) → w ≤ (a : ℚ) / (b : ℚ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hU : LUV.RpnThresholdCodeSeq U) :
    (fun n => (U n).expect P n) ≲ₙ fun _ => ((a : ℚ) / (b : ℚ) : ℝ) := by
  have hq : (0 : ℚ) ≤ (a : ℚ) / (b : ℚ) ∧ (a : ℚ) / (b : ℚ) ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_one (by exact_mod_cast hb)]
      exact_mod_cast hab
  let q : ℕ → MediatedPair := fun n => gatedPair (U n) (φ n) ((a : ℚ) / (b : ℚ))
  have hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (q n) v := by
    intro n v hv
    have hex := hval n v hv
    let w : ℝ := Classical.choose hex
    have hw : (0 ≤ w ∧ w ≤ 1) ∧ v.ValuesAt (U n) (if v.Holds (φ n) then w else 0) ∧
        (v.Holds (φ n) → w ≤ (a : ℚ) / (b : ℚ)) := Classical.choose_spec hex
    exact gatedPair_validAt (U n) (φ n) _ hq v w hw.1 hw.2.1
      (fun h => by have := hw.2.2 h; push_cast at this ⊢; exact this)
  have hC : LUV.RpnThresholdCodeSeq (fun n => (q n).Ucorr) := by
    show LUV.RpnThresholdCodeSeq (fun _ => constLUV ((a : ℚ) / (b : ℚ)))
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using constLUV_thresholdCodeSeq_zero
    · exact constLUV_thresholdCodeSeq_pos a b ha hb
  have hbyp := li_bypass_le_generated (P := P) (DP := DP) q hvalid hworld 0
    (fun n => by simp [q, gatedPair])
    ⟨_, (PolyFueled.const (Encodable.encode (-(0 : ℚ)))).of_eq (fun n => rfl)⟩
    hU hC constLUV_thresholdCodeSeq_zero constLUV_thresholdCodeSeq_zero
    constLUV_thresholdCodeSeq_zero
  have hα' := expect_constLUV (P := P) (DP := DP) hworld a b hb hab
  have h0 := expect_constLUV (P := P) (DP := DP) hworld 0 1 Nat.one_pos (Nat.zero_le 1)
  rw [asympEq_iff_eventuallyWithin] at hα' h0
  intro ε hε
  have hα'' := hα' (ε / 4) (by linarith)
  have h0' := h0 (ε / 4) (by linarith)
  filter_upwards [hbyp (ε / 4) (by linarith), hα'', h0'] with n hn hnα hn0
  simp only [q, gatedPair] at hn
  simp only [Nat.cast_zero, Nat.cast_one, div_one, Rat.cast_zero] at hn0
  have hn0' : |(constLUV 0).expect P n| ≤ ε / 4 := by simpa using hn0
  rw [abs_le] at hnα hn0'
  simp only [Rat.cast_zero, zero_mul, zero_add] at hn
  push_cast at hn hnα ⊢
  linarith [hnα.1, hnα.2, hn0'.1, hn0'.2]

/-- **The reason-supplied non-capture theorem.**  With a committed program re-executed on
the authenticated trace, a certified content bound `α = a/b` on the audited branch (the
supply theorem's output), an extensional program (`κ = 0` in every consistent world) and a
sealed audit (no directional mismatch), Logical Induction learns
`𝔼ₙ(U_T) − 𝔼ₙ(U_N) ≲ₙ L·α`. -/
theorem li_noncapture {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φs φn : ℕ → Sentence) (Xs Xn Xd Xκ : ℕ → LUV) (L : ℚ) (hL : 0 ≤ L)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φs n) (φn n) (Xs n) (Xn n) (Xd n) (Xκ n) L) v)
    (hsupply : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xd n) d ∧ (v.Holds (φs n) → v.Holds (φn n) → d ≤ (a : ℚ) / (b : ℚ)))
    (hext : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ n) 0)
    (hsealed : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φs n) → v.Holds (φn n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hφs : RpnSentenceCodes φs) (hφn : RpnSentenceCodes φn)
    (hXs : LUV.RpnThresholdCodeSeq Xs) (hXn : LUV.RpnThresholdCodeSeq Xn)
    (hXd : LUV.RpnThresholdCodeSeq Xd) (hXκ : LUV.RpnThresholdCodeSeq Xκ) :
    let p := fun n => MediatedPair.compile (φs n) (φn n) (Xs n) (Xn n) (Xd n) (Xκ n) L
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun _ => (L : ℝ) * ((a : ℚ) / (b : ℚ) : ℝ) := by
  intro p
  have hboth : RpnSentenceCodes (fun n => LO.Propositional.Formula.and (φs n) (φn n)) :=
    RpnSentenceCodes.and hφs hφn
  have hmis : RpnSentenceCodes (fun n => LO.Propositional.Formula.and (φs n) (neg (φn n))) :=
    RpnSentenceCodes.and hφs (rpnSentenceCodes_neg hφn)
  -- the landed steering theorem
  have hbyp := li_steering_le (P := P) (DP := DP) φs φn Xs Xn Xd Xκ (fun _ => L) hvalid hworld
    (|(L : ℝ)|) (fun n => le_rfl)
    ⟨_, (PolyFueled.const (Encodable.encode (-L))).of_eq (fun n => rfl)⟩
    hφs hφn hXs hXn hXd hXκ
  -- the content term
  have hδ : (fun n => (p n).Gδ.expect P n) ≲ₙ fun _ => ((a : ℚ) / (b : ℚ) : ℝ) := by
    refine li_gated_le (P := P) (DP := DP)
      (fun n => LO.Propositional.Formula.and (φs n) (φn n)) (fun n => (p n).Gδ) a b hb hab
      ?_ hworld (gate_thresholdCodeSeq hboth hXd)
    intro n v hv
    obtain ⟨d, hd, hdα⟩ := hsupply n v hv
    refine ⟨d, ⟨hd.1, hd.2.1⟩, (gate_gatedAt v _ _).valuesAt hd, fun h => ?_⟩
    exact hdα ((holds_and_iff v _ _).mp h).1 ((holds_and_iff v _ _).mp h).2
  -- the form term
  have hρ : (fun n => (p n).Gρ.expect P n) ≲ₙ fun _ => (((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) : ℝ) := by
    refine li_gated_le (P := P) (DP := DP)
      (fun n => LO.Propositional.Formula.and (φs n) (φn n)) (fun n => (p n).Gρ) 0 1
      Nat.one_pos (Nat.zero_le 1) ?_ hworld (gate_thresholdCodeSeq hboth hXκ)
    intro n v hv
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, (gate_gatedAt v _ _).valuesAt (hext n v hv), fun _ => by simp⟩
  -- the mismatch term
  have hM : (fun n => (p n).GM.expect P n) ≲ₙ fun _ => (((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) : ℝ) := by
    refine li_gated_le (P := P) (DP := DP)
      (fun n => LO.Propositional.Formula.and (φs n) (neg (φn n))) (fun n => (p n).GM) 0 1
      Nat.one_pos (Nat.zero_le 1) ?_ hworld (indicator_thresholdCodeSeq hmis)
    intro n v hv
    refine ⟨1, ⟨zero_le_one, le_rfl⟩, (indicator_indicatorAt v _).valuesAt, fun h => ?_⟩
    have h1 := ((holds_and_iff v _ _).mp h).1
    have h2 := ((holds_and_iff v _ _).mp h).2
    exact absurd (hsealed n v hv h1) ((holds_neg_iff v _).mp h2)
  -- combine
  have hrhs : (fun n => ((fun _ => L) n : ℚ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
      + (p n).GM.expect P n) ≲ₙ
      fun _ => (L : ℝ) * ((a : ℚ) / (b : ℚ) : ℝ) := by
    have h1 := asympLE_add (asympLE_add (asympLE_const_mul (L : ℝ) (by exact_mod_cast hL) hδ) hρ) hM
    intro ε hε
    filter_upwards [h1 ε hε] with n hn
    simpa using hn
  exact hbyp.trans hrhs

end Composition

end Workspace.Deference.Contrib.ReasonSupply

#print axioms Workspace.Deference.Contrib.ReasonSupply.sensitive_symmDiff
#print axioms Workspace.Deference.Contrib.ReasonSupply.adverse_union
#print axioms Workspace.Deference.Contrib.ReasonSupply.weightedCount_adverse
#print axioms Workspace.Deference.Contrib.ReasonSupply.weightedCount_sensitive
#print axioms Workspace.Deference.Contrib.ReasonSupply.served_cut_le
#print axioms Workspace.Deference.Contrib.ReasonSupply.cut_of_servesAll
#print axioms Workspace.Deference.Contrib.ReasonSupply.unserved_ge_excess
#print axioms Workspace.Deference.Contrib.ReasonSupply.unit_servable_iff_cut
#print axioms Workspace.Deference.Contrib.ReasonSupply.hybrid_bound
#print axioms Workspace.Deference.Contrib.ReasonSupply.constLUV_thresholdCodes
#print axioms Workspace.Deference.Contrib.ReasonSupply.expect_constLUV
#print axioms Workspace.Deference.Contrib.ReasonSupply.gatedPair_validAt
#print axioms Workspace.Deference.Contrib.ReasonSupply.li_gated_le
#print axioms Workspace.Deference.Contrib.ReasonSupply.li_noncapture
