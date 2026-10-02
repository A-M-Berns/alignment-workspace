import Cleanroom.Bli.BliExtrapolation.Soto

/-!
# `bli-extrapolation` · Extension: non-dogmatism of the extrapolation (target 10)

"Is there a first universal the extrapolation kills?" Under full support on the `Ax`-consistent
conjunctions, no: the ½-rule kills nothing `Ax` does not kill (`extrapolate_pos_of_axConsistent`),
and with a dogmatic base the extrapolation inherits exactly the base's zeros
(`extrapolate_zero_iff`). The `paperDP` row of record (the liminf over the day-`n` bases of FAF's
LIA through `bli-finite`'s `IsWorldMarginal`) is *not* stated here: it needs the coherent base
of `bli-coherent-mm` (FAF's LIA is not coherent on `smallSet`, program E7) and a `paperDP`-facing
file; it is recorded in the report as a question, not as an `OPEN` row.

Sources: mandate entry `extension`; [[bli-soto-a-inventory]] 082 (the contrast with the LI's
non-dogmatism); PDF 07 p. 2.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld Finset

section

variable (S : UnivStructure) [∀ Γ φ, Decidable (AxEntails S Γ φ)] (e : ℕ ≃ ℕ) {B : ℕ}

/-- **Full support on the `Ax`-consistent conjunctions**: every `Ax`-consistent base conjunction
has positive mass.
Source: mandate target 10
Kind: D
Fidelity: exact -/
def FullSupport (q : FiniteWorld B → ℚ) : Prop :=
  ∀ u : FiniteWorld B, AxConsistent S {conj e u} → 0 < q u

open Classical in
/-- **The chained pmf is positive on every `Ax`-consistent conjunction** under full support: the
base regime by `FullSupport` (marginals of positive masses), the `Ax` regime because an
`Ax`-consistent `conj u ⋏ lit` gets the factor `1` or `½`, never `0` (the `0` clause fires only
when the literal's negation is entailed, which contradicts consistency of the extension).
Source: mandate target 10 ("the ½-rule kills nothing `Ax` does not kill")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `FullSupport` -/
theorem sotoPMF_pos_of_axConsistent {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hfull : FullSupport S e q) :
    ∀ (k : ℕ) (u : FiniteWorld k), AxConsistent S {conj e u} → 0 < sotoPMF S e q k u := by
  intro k
  induction k with
  | zero => intro u _; simp [sotoPMF, chainPMF]
  | succ k ih =>
      intro u hu
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld k) (b : Bool), u = (Fin.snoc u' b : FiniteWorld (k + 1)) :=
        ⟨Fin.init u, u (Fin.last k), (Fin.snoc_init_self u).symm⟩
      have hu' : AxConsistent S {conj e u'} := by
        obtain ⟨v, hv, hΓ⟩ := hu
        refine ⟨v, hv, ?_⟩
        intro φ hφ
        rw [Finset.mem_singleton] at hφ
        subst hφ
        exact ((holds_conj_snoc_iff e u' b v).mp (hΓ _ (Finset.mem_singleton_self _))).1
      by_cases hkB : k + 1 ≤ B
      · -- base regime: the marginal of positive masses is positive
        rw [sotoPMF_eq_baseMarginal S e hq0 hq1 _ hkB]
        unfold baseMarginal
        rw [dif_pos hkB]
        -- some extension of `u` is `Ax`-consistent (extend the witnessing world) and has positive mass
        obtain ⟨v, hv, hΓ⟩ := hu
        have hconj : v.Holds (conj e (Fin.snoc u' b)) := hΓ _ (Finset.mem_singleton_self _)
        let wB : FiniteWorld B := fun j => decide (v (e j))
        have hext : Extends hkB wB (Fin.snoc u' b : FiniteWorld (k + 1)) := by
          intro j
          rw [conj_holds_iff] at hconj
          have := hconj j
          simp only [wB, Fin.castLE]
          cases hb : (Fin.snoc u' b : FiniteWorld (k + 1)) j <;> simp_all
        have hwB : AxConsistent S {conj e wB} := by
          refine ⟨v, hv, ?_⟩
          intro φ hφ
          rw [Finset.mem_singleton] at hφ
          subst hφ
          rw [conj_holds_iff]
          intro j
          simp [wB]
        apply lt_of_lt_of_le (hfull wB hwB)
        apply Finset.single_le_sum (f := fun w => if Extends hkB w (Fin.snoc u' b) then q w else 0)
          (fun w _ => by split_ifs <;> simp [hq0 w]) (Finset.mem_univ wB) |>.trans'
        rw [if_pos hext]
      · -- `Ax` regime: the factor is `1` or `½`
        rw [sotoPMF, chainPMF_snoc, ← sotoPMF]
        apply mul_pos (ih u' hu')
        rw [sotoRule_of_le S e q (by omega) u']
        have hnot : ¬ AxEntails S {conj e u'} (∼lit (e k) b) := by
          intro h
          obtain ⟨v, hv, hΓ⟩ := hu
          have hconj := (holds_conj_snoc_iff e u' b v).mp (hΓ _ (Finset.mem_singleton_self _))
          exact (PCWorld.holds_neg _ _).mp (h v hv (fun φ hφ => by
            rw [Finset.mem_singleton] at hφ; subst hφ; exact hconj.1)) hconj.2
        cases b
        · have h1 : ¬ AxEntails S {conj e u'} (Formula.atom (e k)) := by
            intro h; apply hnot; intro v hv hΓ
            have := h v hv hΓ
            simpa [lit] using this
          simp only [Bool.false_eq_true, if_false]
          unfold axClause
          rw [if_neg h1]
          split_ifs <;> norm_num
        · have h0 : ¬ AxEntails S {conj e u'} (∼Formula.atom (e k)) := by
            simpa [lit] using hnot
          simp only [if_true]
          unfold axClause
          rw [if_neg h0]
          split_ifs <;> norm_num

open Classical in
/-- **10, `extrapolate_pos_of_axConsistent`**: under full support on the `Ax`-consistent base
conjunctions, every `Ax`-consistent sentence has positive extrapolated value — the extrapolation
is non-dogmatic on everything `Ax` allows; there is no first universal it kills.
Source: mandate entry `extension`; [[bli-soto-a-inventory]] 082 (contrast: an LI may keep a true
universal near `0` forever)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `FullSupport S e q`; (a) `AxConsistent S {φ}` -/
theorem extrapolate_pos_of_axConsistent {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w)
    (hq1 : ∑ w, q w = 1) (hfull : FullSupport S e q) {φ : Sentence}
    (hφ : AxConsistent S {φ}) : 0 < extrapolateVal S e q φ := by
  obtain ⟨v, hv, hΓ⟩ := hφ
  have hvφ : v.Holds φ := hΓ _ (Finset.mem_singleton_self _)
  unfold extrapolateVal chainVal chainValAt
  -- the level-`level e φ` conjunction read off `v` holds `φ`, is `Ax`-consistent, and has positive mass
  let u : FiniteWorld (level e φ) := fun j => decide (v (e j))
  have hconj : v.Holds (conj e u) := by
    rw [conj_holds_iff]; intro j; simp [u]
  have hu : (enumWorld e u).toPCWorld.Holds φ :=
    (holds_congr_of_holds_conj_pc e le_rfl hconj).mp hvφ
  have hcons : AxConsistent S {conj e u} := ⟨v, hv, fun ψ hψ => by
    rw [Finset.mem_singleton] at hψ; subst hψ; exact hconj⟩
  have hpos := sotoPMF_pos_of_axConsistent S e hq0 hq1 hfull _ u hcons
  apply lt_of_lt_of_le hpos
  apply Finset.single_le_sum (f := fun w => if (enumWorld e w).toPCWorld.Holds φ then
    sotoPMF S e q (level e φ) w else 0)
    (fun w _ => by split_ifs <;> simp [chainPMF_nonneg (sotoRule_inUnit S e hq0)])
    (Finset.mem_univ u) |>.trans'
  rw [if_pos hu]

/-- **`sotoPMF_pos_of_prefix_pos`**: an `Ax`-consistent level-`(B + d)` conjunction whose
`B`-prefix has positive chained mass has positive mass — the `Ax`-regime half of
`sotoPMF_pos_of_axConsistent`, needing no `FullSupport` and no hypothesis on `q`. Together with
`sotoPMF_zero_of_inconsistent` and `chainPMF_zero_of_prefix` it gives `extrapolate_zero_iff`
below: the extrapolation inherits exactly the base's zeros beyond what `Ax` kills.
Source: mandate target 10 ("the answer is 'the base's'")
Kind: P
Fidelity: exact
Hyps: (a) none beyond `AxConsistent` and the positive prefix mass -/
theorem sotoPMF_pos_of_prefix_pos (q : FiniteWorld B → ℚ) :
    ∀ (d : ℕ) (u : FiniteWorld (B + d)), AxConsistent S {conj e u} →
      0 < sotoPMF S e q B (fun j => u (Fin.castLE (Nat.le_add_right B d) j)) →
      0 < sotoPMF S e q (B + d) u := by
  intro d
  induction d with
  | zero => intro u _ h; simpa using h
  | succ d ih =>
      intro u hu hpre
      obtain ⟨u', b, rfl⟩ : ∃ (u' : FiniteWorld (B + d)) (b : Bool),
          u = (Fin.snoc u' b : FiniteWorld (B + d + 1)) :=
        ⟨Fin.init u, u (Fin.last _), (Fin.snoc_init_self u).symm⟩
      have hu' : AxConsistent S {conj e u'} := by
        obtain ⟨v, hv, hΓ⟩ := hu
        refine ⟨v, hv, ?_⟩
        intro φ hφ
        rw [Finset.mem_singleton] at hφ
        subst hφ
        exact ((holds_conj_snoc_iff e u' b v).mp (hΓ _ (Finset.mem_singleton_self _))).1
      have hpre' : 0 < sotoPMF S e q B (fun j => u' (Fin.castLE (Nat.le_add_right B d) j)) := by
        convert hpre using 2
        funext j
        rw [show Fin.castLE (Nat.le_add_right B (d + 1)) j =
          Fin.castSucc (Fin.castLE (Nat.le_add_right B d) j) from Fin.ext rfl, Fin.snoc_castSucc]
      show 0 < sotoPMF S e q (B + d + 1) (Fin.snoc u' b)
      rw [sotoPMF, chainPMF_snoc, ← sotoPMF]
      apply mul_pos (ih u' hu' hpre')
      rw [sotoRule_of_le S e q (Nat.le_add_right B d) u']
      have hnot : ¬ AxEntails S {conj e u'} (∼lit (e (B + d)) b) := by
        intro h
        obtain ⟨v, hv, hΓ⟩ := hu
        have hconj := (holds_conj_snoc_iff e u' b v).mp (hΓ _ (Finset.mem_singleton_self _))
        exact (PCWorld.holds_neg _ _).mp (h v hv (fun φ hφ => by
          rw [Finset.mem_singleton] at hφ; subst hφ; exact hconj.1)) hconj.2
      cases b
      · have h1 : ¬ AxEntails S {conj e u'} (Formula.atom (e (B + d))) := by
          intro h; apply hnot; intro v hv hΓ
          have := h v hv hΓ
          simpa [lit] using this
        simp only [Bool.false_eq_true, if_false]
        unfold axClause
        rw [if_neg h1]
        split_ifs <;> norm_num
      · have h0 : ¬ AxEntails S {conj e u'} (∼Formula.atom (e (B + d))) := by
          simpa [lit] using hnot
        simp only [if_true]
        unfold axClause
        rw [if_neg h0]
        split_ifs <;> norm_num

/-- Zero mass is hereditary along `d` further levels: a null `B`-prefix has null extensions
(`chainPMF_zero_of_init` iterated).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_zero_of_prefix (p : CondRule) {B : ℕ} :
    ∀ (d : ℕ) (u : FiniteWorld (B + d)),
      chainPMF p B (fun j => u (Fin.castLE (Nat.le_add_right B d) j)) = 0 →
      chainPMF p (B + d) u = 0
  | 0, u, h => by simpa using h
  | d + 1, u, h => by
      apply chainPMF_zero_of_init
      apply chainPMF_zero_of_prefix p d
      convert h using 2
      funext j
      rfl

/-- **`extrapolate_zero_iff`** (10): a level-`(B + d)` conjunction has zero chained mass iff it is
`Ax`-inconsistent or its `B`-prefix has zero base mass — the extrapolation inherits exactly the
base's zeros beyond what `Ax` kills; in particular the ½-rule itself kills nothing.
Source: mandate target 10 ("the answer is 'the base's'")
Kind: C
Fidelity: exact
Hyps: (a) `0 ≤ q`, `∑ q = 1`, `BaseAxConsistent` -/
theorem extrapolate_zero_iff {q : FiniteWorld B → ℚ} (hq0 : ∀ w, 0 ≤ q w) (hq1 : ∑ w, q w = 1)
    (hbase : BaseAxConsistent S e q) (d : ℕ) (u : FiniteWorld (B + d)) :
    sotoPMF S e q (B + d) u = 0 ↔
      ¬ AxConsistent S {conj e u} ∨ q (fun j => u (Fin.castLE (Nat.le_add_right B d) j)) = 0 := by
  constructor
  · intro h
    by_contra hcon
    rw [not_or, not_not] at hcon
    have hpos : 0 < sotoPMF S e q B (fun j => u (Fin.castLE (Nat.le_add_right B d) j)) := by
      rw [sotoPMF_base S e hq0 hq1]
      exact lt_of_le_of_ne (hq0 _) (Ne.symm hcon.2)
    exact absurd h (ne_of_gt (sotoPMF_pos_of_prefix_pos S e q d u hcon.1 hpos))
  · rintro (h | h)
    · exact sotoPMF_zero_of_inconsistent S e hq0 hq1 hbase _ u h
    · apply chainPMF_zero_of_prefix
      rw [← sotoPMF, sotoPMF_base S e hq0 hq1]
      exact h

end

end Cleanroom.Bli.BliExtrapolation
