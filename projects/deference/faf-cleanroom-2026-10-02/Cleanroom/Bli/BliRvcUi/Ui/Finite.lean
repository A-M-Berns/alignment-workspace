import Cleanroom.Bli.BliRvcUi.Ui.Defs
import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import Cleanroom.Bli.BliFound.Constraints
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Fin

/-!
# `bli-rvc-ui` · Ui/Finite: exact universal instantiation at a finite day versus coherence (T3.4)

**The claim (P8, corrected).** Exact UI at one valuation is an instance of propositional
coherence relative to the augmented stage — the direction the desiderata need:

* `uiAt_of_coherentOn` (C): `Constraints.CoherentOn D A V`, with `u 🡒 inst c ∈ D` for `c ∈ C` and
  the atoms of `u`, `inst c` in `A`, gives `UIAt V F C`.
* `coherentOn_of_uiAt_atoms` (P): when `u` and the `inst c`, `c ∈ C`, are pairwise distinct atoms
  and `V ∈ [0,1]` on them, `UIAt V F C` makes `V` on those atoms the restriction of a world
  marginal relative to `{u 🡒 inst c}`: mass `V u` on the all-true world, the rest on `u`-false
  worlds with independent instance marginals `(V (inst c) − V u)/(1 − V u)` — the product mixture
  over `C.powerset` (`Finset.prod_add`).
* `uiAt_not_coherent_shared` (N−): with `inst 0 = p`, `inst 1 = ∼p`, `V u = 0`, `V p = V (∼p) = 1`,
  `UIAt` holds and `V` is not coherent relative to any stage on the atom `p`.
* `uiAt_not_coherent_baseCoherent` (N−, repair round 1): even a valuation that is coherent relative
  to the *empty* stage on every atom set (`uniformFour`, the uniform mixture of the four worlds on
  `u := atom 1`, `inst := atom 0`) satisfies `UIAt` yet is not coherent relative to the augmented
  stage `{u 🡒 inst}`: augmented-stage coherence forces `V (u ⋏ ∼inst) = 0`, here `¼`. So the
  charitable reading of P8 ("among base-coherent valuations, exact UI ⟺ augmented-stage
  coherence") fails too, and the "extends to" shape is the only true converse — not a
  technicality about junk on compounds (audit r1, adversarial (a)).

**Finding F-7.** [[bli-program-desiderata]] P8's "exact UI at finite day is *equivalent* to
`FiniteCoherent`" is one-directional in general: the equivalence holds for pairwise distinct
instance atoms and fails when instances share primes. The one-directional statement is what SSC
needs. **Honesty**: exact UI at finite days is a theorem only *relative to coherence w.r.t. the
augmented process*; nothing here claims the LIA satisfies it (it is not coherent at finite days,
`bli-superbelief` E7).
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFound

/-! ## Coherence gives exact UI -/

/-- **T3.4 (⟹) — exact UI at a finite day from stage coherence**: a valuation coherent relative
to a stage containing `u 🡒 inst c` satisfies `V u ≤ V (inst c)`.
Source: [[bli-program-desiderata]] P8 (the direction the desiderata need); mandate T3.4
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem uiAt_of_coherentOn {D : Finset Sentence} {A : Finset ℕ} {V : Sentence → ℝ}
    (h : CoherentOn D A V) {F : UIFamily} {C : Finset ℕ}
    (hD : ∀ c ∈ C, F.u 🡒 F.inst c ∈ D) (hu : sentenceAtomCodes F.u ⊆ A)
    (hinst : ∀ c ∈ C, sentenceAtomCodes (F.inst c) ⊆ A) : UIAt V F C := by
  obtain ⟨k, W, w, hW, hw0, hw1, hV⟩ := h
  intro c hc
  rw [hV _ hu, hV _ (hinst c hc)]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw0 i)
  have himp : (W i).Holds F.u → (W i).Holds (F.inst c) := hW i _ (hD c hc)
  by_cases hh : (W i).Holds F.u
  · rw [payout_of_holds hh, payout_of_holds (himp hh)]
  · rw [payout_of_not_holds hh]
    exact (payout_mem_Icc _ _).1

/-! ## Exact UI on distinct atoms extends to a coherent valuation -/

/-- A finite mixture of `D`-consistent worlds, indexed by any finite type, is `CoherentOn D A`
(transport to `Fin k`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentOn_of_mixture {ι : Type*} [Fintype ι] (D : Finset Sentence) (A : Finset ℕ)
    (W : ι → PCWorld) (w : ι → ℝ) (hW : ∀ i, (W i).ConsistentWith D) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : CoherentOn D A (fun φ => ∑ i, w i * (W i).payout φ) :=
  ⟨Fintype.card ι, fun j => W ((Fintype.equivFin ι).symm j),
    fun j => w ((Fintype.equivFin ι).symm j), fun _ => hW _, fun _ => hw0 _,
    by rw [Equiv.sum_comp (Fintype.equivFin ι).symm w]; exact hw1,
    fun φ _ => (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => w i * (W i).payout φ)).symm⟩

/-- The all-true world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def allTrueWorld : PCWorld := fun _ => True

/-- The `u`-false world of the subset `S`: atom `a` false, atom `b c` true iff `c ∈ S`.
Source: mandate T3.4 (the construction)
Kind: D
Fidelity: n/a -/
def subsetWorld (a : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : PCWorld :=
  fun x => x ≠ a ∧ ∃ c ∈ S, x = b c

/-- The product weight of the subset `S` (before the `1 − V u` factor).
Source: mandate T3.4
Kind: D
Fidelity: n/a -/
noncomputable def subsetWeight (q : ℕ → ℝ) (C S : Finset ℕ) : ℝ :=
  (∏ c ∈ S, q c) * ∏ c ∈ C \ S, (1 - q c)

/-- The subset weights over `C.powerset` sum to `1` (`Finset.prod_add`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_subsetWeight (q : ℕ → ℝ) (C : Finset ℕ) :
    ∑ S ∈ C.powerset, subsetWeight q C S = 1 := by
  classical
  have h := Finset.prod_add q (fun c => 1 - q c) C
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  unfold subsetWeight
  exact h.symm

/-- The subset weights of the subsets containing `c ∈ C` sum to `q c`.
Source: none: infrastructure (`Finset.sum_powerset_insert`, `Finset.prod_add`)
Kind: L
Fidelity: n/a -/
lemma sum_subsetWeight_mem (q : ℕ → ℝ) (C : Finset ℕ) {c : ℕ} (hc : c ∈ C) :
    ∑ S ∈ C.powerset, (if c ∈ S then subsetWeight q C S else 0) = q c := by
  classical
  set C' := C.erase c with hC'
  have hcC' : c ∉ C' := Finset.notMem_erase c C
  have hC : C = insert c C' := (Finset.insert_erase hc).symm
  have hsplit := Finset.sum_powerset_insert hcC'
    (fun S => if c ∈ S then subsetWeight q C S else 0)
  rw [← hC] at hsplit
  rw [hsplit]
  have hfirst : ∑ S ∈ C'.powerset, (if c ∈ S then subsetWeight q C S else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_powerset] at hS
    rw [if_neg (fun hcS => hcC' (hS hcS))]
  rw [hfirst, zero_add]
  have hsecond : ∀ S ∈ C'.powerset,
      (if c ∈ insert c S then subsetWeight q C (insert c S) else 0) =
        q c * ((∏ x ∈ S, q x) * ∏ x ∈ C' \ S, (1 - q x)) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hcS : c ∉ S := fun h => hcC' (hS h)
    rw [if_pos (Finset.mem_insert_self c S)]
    unfold subsetWeight
    rw [Finset.prod_insert hcS]
    have hdiff : C \ insert c S = C' \ S := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, hC', Finset.mem_erase]
      tauto
    rw [hdiff]
    ring
  rw [Finset.sum_congr rfl hsecond, ← Finset.mul_sum]
  have h := Finset.prod_add q (fun c => 1 - q c) C'
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  rw [← h, mul_one]

/-- Subset weights are nonnegative for `q ∈ [0,1]` on `C`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma subsetWeight_nonneg {q : ℕ → ℝ} {C : Finset ℕ} (hq0 : ∀ c ∈ C, 0 ≤ q c)
    (hq1 : ∀ c ∈ C, q c ≤ 1) {S : Finset ℕ} (hS : S ⊆ C) : 0 ≤ subsetWeight q C S := by
  unfold subsetWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun c hc => hq0 c (hS hc)
  · exact Finset.prod_nonneg fun c hc => by
      have := hq1 c (Finset.mem_sdiff.mp hc).1
      linarith

/-- **T3.4 (⟸) — exact UI on pairwise distinct atoms extends to a stage-coherent valuation**: if
`u = atom a`, `inst c = atom (b c)` for `c ∈ C` with `b` injective on `C` and never `a`, and
`V ∈ [0,1]` on them with `UIAt V F C`, then some `V'` agreeing with `V` on `u` and the `inst c`
is `CoherentOn` relative to the stage `{u 🡒 inst c : c ∈ C}` (on any atom set): mass `V u` on the
all-true world, mass `(1 − V u)·∏_{S} q·∏_{C∖S}(1 − q)` on the `u`-false world of each `S ⊆ C`,
`q c := (V (inst c) − V u)/(1 − V u)`.
Source: mandate T3.4; [[bli-program-desiderata]] P8 (the converse, for independent instance atoms)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem coherentOn_of_uiAt_atoms {V : Sentence → ℝ} {F : UIFamily} {C : Finset ℕ} {a : ℕ}
    {b : ℕ → ℕ} (hu : F.u = Formula.atom a) (hinst : ∀ c ∈ C, F.inst c = Formula.atom (b c))
    (hab : ∀ c ∈ C, b c ≠ a) (hb : ∀ c ∈ C, ∀ c' ∈ C, b c = b c' → c = c')
    (hV0 : 0 ≤ V F.u) (hVu1 : V F.u ≤ 1) (hV1 : ∀ c ∈ C, V (F.inst c) ≤ 1) (hUI : UIAt V F C)
    (A : Finset ℕ) :
    ∃ V' : Sentence → ℝ, V' F.u = V F.u ∧ (∀ c ∈ C, V' (F.inst c) = V (F.inst c)) ∧
      CoherentOn (C.image (fun c => F.u 🡒 F.inst c)) A V' := by
  classical
  set D := C.image (fun c => F.u 🡒 F.inst c) with hD
  -- the all-true world is consistent with `D`
  have hall : allTrueWorld.ConsistentWith D := by
    intro φ hφ
    rw [hD, Finset.mem_image] at hφ
    obtain ⟨c, hc, rfl⟩ := hφ
    change allTrueWorld.Holds F.u → allTrueWorld.Holds (F.inst c)
    intro _
    rw [hinst c hc, PCWorld.holds_atom]
    exact trivial
  by_cases h1 : V F.u = 1
  · -- everything is `1`: the all-true world alone
    have hall1 : ∀ c ∈ C, V (F.inst c) = 1 := fun c hc =>
      le_antisymm (hV1 c hc) (h1 ▸ hUI c hc)
    refine ⟨fun φ => allTrueWorld.payout φ, ?_, fun c hc => ?_, ?_⟩
    · show allTrueWorld.payout F.u = V F.u
      rw [h1, hu, payout_of_holds (by rw [PCWorld.holds_atom]; exact trivial)]
    · show allTrueWorld.payout (F.inst c) = V (F.inst c)
      rw [hall1 c hc, hinst c hc, payout_of_holds (by rw [PCWorld.holds_atom]; exact trivial)]
    · refine ⟨1, fun _ => allTrueWorld, fun _ => 1, fun _ => hall, fun _ => zero_le_one, by simp,
        fun φ _ => by simp⟩
  · have hlt : V F.u < 1 := lt_of_le_of_ne hVu1 h1
    have hpos : 0 < 1 - V F.u := by linarith
    set q : ℕ → ℝ := fun c => (V (F.inst c) - V F.u) / (1 - V F.u) with hq
    have hq0 : ∀ c ∈ C, 0 ≤ q c := fun c hc =>
      div_nonneg (by linarith [hUI c hc]) hpos.le
    have hq1 : ∀ c ∈ C, q c ≤ 1 := fun c hc => by
      rw [hq]; dsimp only
      rw [div_le_one hpos]
      linarith [hV1 c hc]
    -- the mixture over `Option ↥C.powerset`
    let W : Option ↥C.powerset → PCWorld := fun o =>
      match o with
      | none => allTrueWorld
      | some S => subsetWorld a b S.1
    let w : Option ↥C.powerset → ℝ := fun o =>
      match o with
      | none => V F.u
      | some S => (1 - V F.u) * subsetWeight q C S.1
    have hW : ∀ o, (W o).ConsistentWith D := by
      rintro (_ | S)
      · exact hall
      · intro φ hφ
        rw [hD, Finset.mem_image] at hφ
        obtain ⟨c, hc, rfl⟩ := hφ
        change (subsetWorld a b S.1).Holds F.u → (subsetWorld a b S.1).Holds (F.inst c)
        intro hh
        exfalso
        rw [hu, PCWorld.holds_atom] at hh
        exact hh.1 rfl
    have hw0 : ∀ o, 0 ≤ w o := by
      rintro (_ | S)
      · exact hV0
      · exact mul_nonneg hpos.le
          (subsetWeight_nonneg hq0 hq1 (Finset.mem_powerset.mp S.2))
    have hw1 : ∑ o, w o = 1 := by
      rw [Fintype.sum_option]
      show V F.u + ∑ S : ↥C.powerset, (1 - V F.u) * subsetWeight q C S.1 = 1
      rw [← Finset.mul_sum, Finset.sum_coe_sort C.powerset (fun S => subsetWeight q C S),
        sum_subsetWeight, mul_one]
      ring
    -- payouts of the subset worlds on the atoms
    have hpay_u : ∀ S : ↥C.powerset, (subsetWorld a b S.1).payout F.u = 0 := fun S => by
      rw [hu, payout_of_not_holds]
      rw [PCWorld.holds_atom]
      exact fun h => h.1 rfl
    have hpay_inst : ∀ S : ↥C.powerset, ∀ c ∈ C,
        (subsetWorld a b S.1).payout (F.inst c) = if c ∈ S.1 then 1 else 0 := by
      intro S c hc
      have hS := Finset.mem_powerset.mp S.2
      rw [hinst c hc]
      by_cases hcS : c ∈ S.1
      · rw [if_pos hcS, payout_of_holds]
        rw [PCWorld.holds_atom]
        exact ⟨hab c hc, c, hcS, rfl⟩
      · rw [if_neg hcS, payout_of_not_holds]
        rw [PCWorld.holds_atom]
        rintro ⟨-, c', hc', hcc'⟩
        exact hcS ((hb c hc c' (hS hc') hcc') ▸ hc')
    refine ⟨fun φ => ∑ o, w o * (W o).payout φ, ?_, fun c hc => ?_,
      coherentOn_of_mixture D A W w hW hw0 hw1⟩
    · show ∑ o, w o * (W o).payout F.u = V F.u
      rw [Fintype.sum_option]
      show V F.u * allTrueWorld.payout F.u +
        ∑ S : ↥C.powerset, (1 - V F.u) * subsetWeight q C S.1 * (subsetWorld a b S.1).payout F.u
          = V F.u
      rw [hu, payout_of_holds (by rw [PCWorld.holds_atom]; exact trivial), mul_one, ← hu]
      rw [Finset.sum_eq_zero (fun S _ => by rw [hpay_u S, mul_zero]), add_zero]
    · show ∑ o, w o * (W o).payout (F.inst c) = V (F.inst c)
      rw [Fintype.sum_option]
      show V F.u * allTrueWorld.payout (F.inst c) +
        ∑ S : ↥C.powerset, (1 - V F.u) * subsetWeight q C S.1 *
          (subsetWorld a b S.1).payout (F.inst c) = V (F.inst c)
      rw [hinst c hc, payout_of_holds (by rw [PCWorld.holds_atom]; exact trivial), mul_one,
        ← hinst c hc]
      have hsum : ∑ S : ↥C.powerset, (1 - V F.u) * subsetWeight q C S.1 *
          (subsetWorld a b S.1).payout (F.inst c) = (1 - V F.u) * q c := by
        rw [Finset.sum_congr rfl (fun S _ => by rw [hpay_inst S c hc])]
        rw [← sum_subsetWeight_mem q C hc, Finset.mul_sum,
          ← Finset.sum_coe_sort C.powerset (fun S => (1 - V F.u) *
            (if c ∈ S then subsetWeight q C S else 0))]
        apply Finset.sum_congr rfl
        intro S _
        split_ifs <;> ring
      rw [hsum, hq]
      dsimp only
      field_simp
      ring

/-! ## Shared primes: exact UI without coherence -/

/-- The shared-prime family: `inst 0 = p`, `inst 1 = ∼p` (the atom `p := atom 0`), `u := atom 1`.
Source: mandate T3.4 (`uiAt_not_coherent_shared`)
Kind: D
Fidelity: n/a -/
def sharedUI : UIFamily where
  u := Formula.atom 1
  inst c := if c = 0 then Formula.atom 0 else ∼Formula.atom 0

/-- The valuation `V u = 0`, `V p = V (∼p) = 1` (`0` elsewhere).
Source: mandate T3.4
Kind: D
Fidelity: n/a -/
noncomputable def sharedV : Sentence → ℝ := fun φ =>
  if φ = Formula.atom 0 ∨ φ = ∼Formula.atom 0 then 1 else 0

/-- **T3.4 (N−) — exact UI does not give coherence when instances share primes**: `sharedV`
satisfies `UIAt` on `{0, 1}` and is not `CoherentOn` relative to any stage on any atom set
containing the prime `0`.
Source: mandate T3.4; [[bli-program-desiderata]] P8 (the failing converse)
Kind: N-
Fidelity: exact -/
theorem uiAt_not_coherent_shared :
    UIAt sharedV sharedUI {0, 1} ∧
    ∀ (D : Finset Sentence) (A : Finset ℕ), 0 ∈ A → ¬ CoherentOn D A sharedV := by
  constructor
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    have hu : sharedV sharedUI.u = 0 := by
      simp [sharedV, sharedUI]
    rw [hu]
    rcases hc with rfl | rfl <;> simp [sharedV, sharedUI]
  · rintro D A hA ⟨k, W, w, -, hw0, hw1, hV⟩
    have hp : sharedV (Formula.atom 0) = ∑ i, w i * (W i).payout (Formula.atom 0) :=
      hV _ (by simpa using hA)
    have hnp : sharedV (∼Formula.atom 0) = ∑ i, w i * (W i).payout (∼Formula.atom 0) :=
      hV _ (by simpa using hA)
    simp only [sharedV, true_or, or_true, if_true] at hp hnp
    -- payouts of `p` and `∼p` sum to `1` in every world, so the two mixtures sum to `1`, not `2`
    have hsum : ∀ i, (W i).payout (Formula.atom 0) + (W i).payout (∼Formula.atom 0) = 1 := by
      intro i
      unfold PCWorld.payout
      rw [PCWorld.holds_neg]
      split_ifs <;> simp_all
    have : (2 : ℝ) = 1 := by
      calc (2 : ℝ) = ∑ i, w i * (W i).payout (Formula.atom 0)
            + ∑ i, w i * (W i).payout (∼Formula.atom 0) := by rw [← hp, ← hnp]; norm_num
        _ = ∑ i, w i * ((W i).payout (Formula.atom 0) + (W i).payout (∼Formula.atom 0)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = ∑ i, w i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hsum i, mul_one]
        _ = 1 := hw1
    norm_num at this

/-! ## Distinct atoms, base-coherent: exact UI still without augmented-stage coherence -/

/-- The two-atom family `u := atom 1`, every instance `atom 0`.
Source: audit r1 (adversarial, non-blocking (a)); mandate T3.4
Kind: D
Fidelity: n/a -/
def pairUI : UIFamily where
  u := Formula.atom 1
  inst _ := Formula.atom 0

/-- The all-true world on the two atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def w11 : PCWorld := fun _ => True

/-- The world with only atom `1` (`u`) true.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def w10 : PCWorld := fun a => a = 1

/-- The world with only atom `0` (`inst`) true.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def w01 : PCWorld := fun a => a = 0

/-- The all-false world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def w00 : PCWorld := fun _ => False

/-- The uniform mixture of the four worlds on atoms `0`, `1`.
Source: audit r1 (adversarial (a))
Kind: D
Fidelity: n/a -/
noncomputable def uniformFour : Sentence → ℝ := fun φ =>
  (1 / 4) * w11.payout φ + (1 / 4) * w10.payout φ + (1 / 4) * w01.payout φ + (1 / 4) * w00.payout φ

/-- `uniformFour` is coherent relative to the empty stage on every atom set (base-coherent).
Source: audit r1 (adversarial (a))
Kind: L
Fidelity: n/a -/
theorem uniformFour_coherent_base (A : Finset ℕ) : CoherentOn ∅ A uniformFour :=
  ⟨4, ![w11, w10, w01, w00], fun _ => 1 / 4,
    fun _ φ hφ => absurd hφ (Finset.notMem_empty φ),
    fun _ => by norm_num,
    by simp,
    fun φ _ => by simp only [Fin.sum_univ_four, uniformFour]; simp⟩

/-- Exact UI holds at `{0}`: `V u = ½ ≤ ½ = V inst`.
Source: audit r1 (adversarial (a))
Kind: L
Fidelity: n/a -/
theorem uniformFour_uiAt : UIAt uniformFour pairUI {0} := by
  intro c _
  simp [pairUI, uniformFour, PCWorld.payout, w11, w10, w01, w00]

/-- `uniformFour` is not coherent relative to the augmented stage `{u 🡒 inst 0}` on `{0, 1}`:
that would force `V (u ⋏ ∼inst) = 0`, but it is `¼`.
Source: audit r1 (adversarial (a))
Kind: L
Fidelity: n/a -/
theorem uniformFour_not_coherent_aug :
    ¬ CoherentOn {pairUI.u 🡒 pairUI.inst 0} {0, 1} uniformFour := by
  rintro ⟨k, W, w, hW, hw0, hw1, hV⟩
  have hmem : sentenceAtomCodes (pairUI.u ⋏ ∼pairUI.inst 0) ⊆ ({0, 1} : Finset ℕ) := by
    simp [pairUI]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    omega
  have h := hV _ hmem
  have hL : uniformFour (pairUI.u ⋏ ∼pairUI.inst 0) = 1 / 4 := by
    simp [pairUI, uniformFour, PCWorld.payout, PCWorld.holds_and, w11, w10, w01, w00]
  have hR : ∑ i, w i * (W i).payout (pairUI.u ⋏ ∼pairUI.inst 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have himp : (W i).Holds pairUI.u → (W i).Holds (pairUI.inst 0) :=
      hW i _ (Finset.mem_singleton_self _)
    rw [payout_of_not_holds, mul_zero]
    rw [PCWorld.holds_and, PCWorld.holds_neg]
    rintro ⟨hu, hni⟩
    exact hni (himp hu)
  rw [hL, hR] at h
  norm_num at h

/-- The augmented stage `{u 🡒 inst 0}` is itself coherently inhabited (the all-true world's
payout), so the failure below is `uniformFour`'s, not an artifact of an unsatisfiable stage; it
also inhabits `uiAt_of_coherentOn`'s hypothesis package at `pairUI`.
Source: audit r1 (fidelity N3, adversarial (e)); [[STANDARDS]] §3 (impossibility results)
Kind: N-
Fidelity: n/a -/
theorem pairUI_aug_coherent (A : Finset ℕ) :
    CoherentOn {pairUI.u 🡒 pairUI.inst 0} A w11.payout :=
  ⟨1, fun _ => w11, fun _ => 1,
    fun _ φ hφ => by
      rw [Finset.mem_singleton] at hφ
      subst hφ
      exact fun _ => trivial,
    fun _ => zero_le_one, by simp, fun φ _ => by simp⟩

/-- **T3.4 (N−, sharpened) — P8's equivalence fails even among base-coherent valuations on
distinct atoms**: `uniformFour` is coherent relative to the empty stage on every atom set,
satisfies exact UI at `{0}`, and is not coherent relative to the augmented stage `{u 🡒 inst 0}`
on `{0, 1}` — while that stage is coherently inhabited (`pairUI_aug_coherent`). Augmented-stage
coherence is strictly stronger than `UIAt` among coherent valuations, so the "extends to" shape of
`coherentOn_of_uiAt_atoms` is the only true converse (F-7, F-13).
Source: [[bli-program-desiderata]] P8; audit r1 (adversarial (a), fidelity N1)
Kind: N-
Fidelity: exact -/
theorem uiAt_not_coherent_baseCoherent :
    (∀ A, CoherentOn ∅ A uniformFour) ∧ UIAt uniformFour pairUI {0} ∧
    ¬ CoherentOn {pairUI.u 🡒 pairUI.inst 0} {0, 1} uniformFour :=
  ⟨uniformFour_coherent_base, uniformFour_uiAt, uniformFour_not_coherent_aug⟩

end Cleanroom.Bli.BliRvcUi
