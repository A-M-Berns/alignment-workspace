import Cleanroom.Decision.DpCausalConsist.NRValue

/-!
# `dp-causal-consist`: Axiom NR forces the `V`-component under the weaker guard (T8, repair round 2)

`nr_forces_kpart_V` (`NRValue.lean`) asks that **every** cell meet `a` positively. Audit r2
(adversarial N3) observed that with a designation some of whose cells are empty or `P`-null that
hypothesis is unsatisfiable, and that the natural weakening — every *positive* cell meets `a`
positively (the guard of `nr_forces_kpart`) plus support regularity of the supposition `cf a` —
would make the two forcing theorems twins. `nr_forces_kpart_V'` proves that weakening: on a
`P`-null cell `e` the part `a ∧ e` is `cf`-null (clause (i)), so support regularity of `cf a` lets
the averaging axiom run over the positive cells only, and the K-partition side drops the same
cells because their weights `P(e)` vanish.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

section nrVweak

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- A singleton's mass is at most its cell's. Source: none: infrastructure. Kind: L -/
theorem w_le_pr_cell (s : State Ω K) (exo : Ω → E) (ω : Ω) :
    s.P.w ω ≤ s.pr (cell exo (exo ω)) := by
  have h := probOf_mono s.P (Finset.singleton_subset_iff.mpr ((mem_cell exo (exo ω) ω).mpr rfl))
  rwa [probOf_singleton] at h

/-- **Axiom NR forces the desirability of the act under the weaker guard** (T8, repair round 2,
audit r2 adv N3): under `NRAt`, if every *positive* cell meets `a` positively, `t.s` is
support-regular and the supposition `cf a` is support-regular, then `V^a(a) = (kPart s a exo).V(a)`
— the exact twin of `nr_forces_kpart`'s hypothesis, now for the `V`-component. The all-cells
version `nr_forces_kpart_V` is the special case in which no cell is null.
Source: [[non-responsiveness]] "Axiom NR" (the `V`-clause) and "Hence `P^a_s = ∑_e …`"; mandate T8
Kind: P
Fidelity: exact for the `V`-clause as rendered in `NRAt`
Hyps: (a) `NRAt`; (a) positive cells meet `a` positively; (a) `t.s` and `cf a` support-regular -/
theorem nr_forces_kpart_V' {A : Type} (t : CfState Ω K) (actEv : A → Finset Ω) (exo : Ω → E)
    (hNR : NRAt t actEv exo) (hreg : SuppRegular t.s) (a : A) (h : (actEv a).Nonempty)
    (hcf : SuppRegular (t.cf (actEv a) h))
    (hpos : ∀ e, 0 < t.s.pr (cell exo e) → 0 < t.s.pr (actEv a ∩ cell exo e)) :
    (t.cf (actEv a) h).V (actEv a) = (kPart t.s (actEv a) exo).V (actEv a) := by
  obtain ⟨h1, -, h3⟩ := hNR a h
  set cf := t.cf (actEv a) h with hcf_def
  set T : Finset E := Finset.univ.filter fun e => 0 < t.s.pr (cell exo e) with hT
  set f : E → Finset Ω := fun e => actEv a ∩ cell exo e with hf
  have hmemT : ∀ e, e ∈ T ↔ 0 < t.s.pr (cell exo e) := by
    intro e; simp [hT]
  have hnull : ∀ e, e ∉ T → t.s.pr (cell exo e) = 0 := fun e he =>
    le_antisymm (not_lt.mp (fun h' => he ((hmemT e).mpr h'))) (probOf_nonneg _ _)
  have hsucc : cf.pr (actEv a) = 1 := t.success _ h
  -- the complement of the act is `cf`-null
  have hcompl : cf.pr (Finset.univ \ actEv a) = 0 := by
    have hd : Disjoint (actEv a) (Finset.univ \ actEv a) := Finset.disjoint_sdiff
    have hu := probOf_union cf.P hd
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), probOf_univ] at hu
    simp only [State.pr] at hsucc ⊢
    linarith
  -- clause (i) + success: `P^a(a ∧ e) = P(e)`
  have hcfcell : ∀ e, cf.pr (f e) = t.s.pr (cell exo e) := by
    intro e
    rw [← h1 e]
    have hd : Disjoint (actEv a ∩ cell exo e) (cell exo e \ actEv a) := by
      rw [Finset.disjoint_left]
      intro ω h1' h2'
      exact (Finset.mem_sdiff.mp h2').2 (Finset.mem_inter.mp h1').1
    have hU : actEv a ∩ cell exo e ∪ cell exo e \ actEv a = cell exo e := by
      ext ω
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hz : cf.pr (cell exo e \ actEv a) = 0 :=
      pr_eq_zero_of_subset cf
        (fun ω hω => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hω).2⟩) hcompl
    have hu := probOf_union cf.P hd
    rw [hU] at hu
    simp only [State.pr, hf] at hu hz ⊢
    rw [hu, hz, add_zero]
  -- clause (iii) at `X = a` on the positive cells
  have hV : ∀ e ∈ T, cf.V (f e) = t.s.V (f e) := by
    intro e he
    have := h3 e (actEv a) (by rw [Finset.inter_self]; exact hpos e ((hmemT e).mp he))
    rwa [Finset.inter_self] at this
  -- the cells are pairwise disjoint
  have hdisj : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (f e) (f e') := fun e _ e' _ hne =>
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (cell_disjoint exo hne))
  have hposT : ∀ e ∈ T, 0 < cf.pr (f e) := fun e he => by
    rw [hcfcell e]; exact (hmemT e).mp he
  -- the union of the positive parts carries all of `cf`'s mass on `a`
  have hprU : cf.pr (T.biUnion f) = 1 := by
    have h1' : cf.pr (T.biUnion f) = ∑ e ∈ T, cf.pr (f e) := by
      simp only [State.pr, probOf]
      rw [Finset.sum_biUnion]
      intro e he e' he' hne
      exact hdisj e he e' he' hne
    have h2' : cf.pr (actEv a) = ∑ e ∈ T, cf.pr (f e) := by
      rw [pr_eq_sum_cells cf exo (actEv a)]
      refine (Finset.sum_subset (Finset.subset_univ T) fun e _ he => ?_).symm
      show cf.pr (f e) = 0
      rw [hcfcell e]; exact hnull e he
    rw [h1', ← h2', hsucc]
  -- and its desirability is `cf`'s desirability of `a` (support regularity of `cf`)
  have hVU : cf.V (T.biUnion f) = cf.V (actEv a) := by
    rw [← hcf (T.biUnion f), ← hcf (actEv a)]
    congr 1
    ext ω
    simp only [Finset.mem_inter, Finset.mem_biUnion, hf, mem_cell]
    constructor
    · rintro ⟨⟨e, _, hωa, _⟩, hs⟩; exact ⟨hωa, hs⟩
    · rintro ⟨hωa, hs⟩
      refine ⟨⟨exo ω, ?_, hωa, rfl⟩, hs⟩
      rw [hmemT]
      by_contra hc
      have hz : t.s.pr (cell exo (exo ω)) = 0 :=
        le_antisymm (not_lt.mp hc) (probOf_nonneg _ _)
      have hcfz : cf.pr (cell exo (exo ω)) = 0 := by rw [h1]; exact hz
      have hw : cf.P.w ω ≤ 0 := by rw [← hcfz]; exact w_le_pr_cell cf exo ω
      rw [mem_supp] at hs
      exact absurd hw (not_le.mpr hs)
  -- the averaging axiom of `cf` over the positive cells
  have hL := V_mul_pr_biUnion cf T f hdisj hposT
  rw [hprU, mul_one, hVU] at hL
  rw [hL, Finset.sum_congr rfl fun e he => by rw [hcfcell e, hV e he]]
  -- the K-partition side
  rw [kPart_V_of_suppRegular t.s hreg]
  have hcomp : ∀ e ∈ T, (kPartComp t.s (actEv a) exo e).pr (actEv a) = 1 ∧
      (kPartComp t.s (actEv a) exo e).V (actEv a) = t.s.V (actEv a ∩ cell exo e) := by
    intro e he
    have hpe := hpos e ((hmemT e).mp he)
    unfold kPartComp
    rw [dif_pos hpe, jeffreyCond_pr, jeffreyCond_V]
    have hset : actEv a ∩ (actEv a ∩ cell exo e) = actEv a ∩ cell exo e := by
      rw [← Finset.inter_assoc, Finset.inter_self]
    rw [hset]
    exact ⟨div_self hpe.ne', rfl⟩
  have hnum : ∑ e, t.s.pr (cell exo e) * (kPartComp t.s (actEv a) exo e).pr (actEv a)
      * (kPartComp t.s (actEv a) exo e).V (actEv a)
      = ∑ e ∈ T, t.s.pr (cell exo e) * t.s.V (f e) := by
    rw [← Finset.sum_subset (Finset.subset_univ T) fun e _ he => by
      rw [hnull e he, zero_mul, zero_mul]]
    exact Finset.sum_congr rfl fun e he => by rw [(hcomp e he).1, (hcomp e he).2, mul_one]
  have hden : ∑ e, t.s.pr (cell exo e) * (kPartComp t.s (actEv a) exo e).pr (actEv a) = 1 := by
    rw [← Finset.sum_subset (Finset.subset_univ T) fun e _ he => by
      rw [hnull e he, zero_mul]]
    rw [Finset.sum_congr rfl fun e he => by rw [(hcomp e he).1, mul_one]]
    rw [Finset.sum_subset (Finset.subset_univ T) fun e _ he => hnull e he]
    exact (cellDistr t.s exo).sum_one
  rw [hnum, hden, div_one]

end nrVweak

/-! ## Mixtures are support-regular, so `kPart` and `kPart`-built suppositions qualify -/

section mixSupp

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {ι' : Type} [Fintype ι']

/-- A component with positive weight has its support inside the mixture's.
Source: none: infrastructure
Kind: L -/
theorem supp_subset_supp_mixState (π : FinDistr K ι') (t : ι' → State Ω K) (i : ι')
    (hi : 0 < π.w i) : supp (t i) ⊆ supp (mixState π t) := by
  intro ω hω
  rw [mem_supp] at hω ⊢
  show 0 < ∑ j, π.w j * (t j).P.w ω
  refine lt_of_lt_of_le (mul_pos hi hω) ?_
  exact Finset.single_le_sum (fun j _ => mul_nonneg (π.nonneg j) ((t j).P.nonneg ω))
    (Finset.mem_univ i)

/-- **A finite Jeffrey mixture is support-regular whatever its components are**: `mixState` reads
each component on that component's support, and a positive-weight component's support lies in the
mixture's.
Source: none: infrastructure (finding F9's support reading, closed under mixing)
Kind: L -/
theorem suppRegular_mixState (π : FinDistr K ι') (t : ι' → State Ω K) :
    SuppRegular (mixState π t) := by
  intro X
  rw [mixState_V, mixState_V]
  have hset : ∀ i, 0 < π.w i → X ∩ supp (mixState π t) ∩ supp (t i) = X ∩ supp (t i) := by
    intro i hi
    ext ω
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hX, _⟩, hti⟩; exact ⟨hX, hti⟩
    · rintro ⟨hX, hti⟩; exact ⟨⟨hX, supp_subset_supp_mixState π t i hi hti⟩, hti⟩
  have hpr : ∀ i, π.w i * (t i).pr (X ∩ supp (mixState π t)) = π.w i * (t i).pr X := by
    intro i
    rcases (π.nonneg i).lt_or_eq with hi | hi
    · rw [← pr_inter_supp (t i) (X ∩ supp (mixState π t)), hset i hi, pr_inter_supp]
    · rw [← hi, zero_mul, zero_mul]
  have hV : ∀ i, π.w i * (t i).pr (X ∩ supp (mixState π t))
        * (t i).V (X ∩ supp (mixState π t) ∩ supp (t i))
      = π.w i * (t i).pr X * (t i).V (X ∩ supp (t i)) := by
    intro i
    rcases (π.nonneg i).lt_or_eq with hi | hi
    · rw [hpr i, hset i hi]
    · rw [← hi, zero_mul, zero_mul, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hV i, Finset.sum_congr rfl fun i _ => hpr i]

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The K-partition state is support-regular (it is a mixture). Source: none: infrastructure.
Kind: L -/
theorem suppRegular_kPart (s : State Ω K) (A : Finset Ω) (exo : Ω → E) :
    SuppRegular (kPart s A exo) :=
  suppRegular_mixState _ _

end mixSupp

end Cleanroom.Decision.DpCausalConsist
