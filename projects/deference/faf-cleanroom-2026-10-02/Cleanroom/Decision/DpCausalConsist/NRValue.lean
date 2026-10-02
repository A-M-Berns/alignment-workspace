import Cleanroom.Decision.DpCausalConsist.NR
import Cleanroom.Decision.DpCausalConsist.Regular

/-!
# `dp-causal-consist`: Axiom NR forces the `V`-component too (T8, repair round 1)

`nr_forces_kpart` (`NR.lean`) gives only the **probability** component of an `NRAt`
counterfactual: `(cf a).pr = kPart.pr` where every positive cell meets `a` positively. Audit r1
(adversarial B1) observed that the package's "NR-cf(cross)" statements are about `kPart`'s
desirability, and that nothing related an `NRAt` component's `V` to it. This file supplies the
missing lemma:

* `V_mul_pr_biUnion`, `V_mul_pr_eq_sum_cells_of_pos`: the averaging axiom over a finite family of
  positive, pairwise-disjoint parts (the two-set axiom iterated), and its instance over the cells
  of an exogenous designation;
* `nr_forces_kpart_V`: under `NRAt`, when **every** cell meets `a` positively and the state is
  support-regular, `(cf a).V (a) = (kPart s a exo).V (a)` — clause (iii) pins `V^a` on each
  `a ∧ e`, clause (i) with success pins `P^a(a ∧ e) = P(e)`, and the supposition's own averaging
  axiom assembles `V^a(a) = ∑_e P(e) V(a ∧ e)`, which is `kPart`'s value by `kPart_V_of_suppRegular`.

The hypothesis "every cell meets `a` positively" (rather than "every positive cell") is what the
averaging argument needs: on a `P`-null cell `e` the part `a ∧ e` is `cf`-null and the axiom is
silent on its contribution to `V^a(a)`, so the `V`-forcing genuinely requires all cells positive
(or a support-regular `cf`); at `TB(θ)`'s mixed labels both cells are positive and meet `cross`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

section avg

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

omit [Fintype E] in
/-- **The averaging axiom over a finite family of positive, pairwise-disjoint parts**:
`V(⋃ f) · P(⋃ f) = ∑_e P(f e) V(f e)` (the two-set axiom iterated; the empty family gives `0 = 0`).
Source: [[decision-problems-v2]] Definition 2 (the averaging axiom); none: infrastructure
Kind: L -/
theorem V_mul_pr_biUnion (s : State Ω K) (T : Finset E) (f : E → Finset Ω)
    (hdisj : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (f e) (f e'))
    (hpos : ∀ e ∈ T, 0 < s.pr (f e)) :
    s.V (T.biUnion f) * s.pr (T.biUnion f) = ∑ e ∈ T, s.pr (f e) * s.V (f e) := by
  induction T using Finset.induction_on with
  | empty => simp [State.pr]
  | insert a T ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hdisj' : ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (f e) (f e') := fun e he e' he' =>
      hdisj e (Finset.mem_insert_of_mem he) e' (Finset.mem_insert_of_mem he')
    have hpos' : ∀ e ∈ T, 0 < s.pr (f e) := fun e he => hpos e (Finset.mem_insert_of_mem he)
    rw [← ih hdisj' hpos']
    rcases T.eq_empty_or_nonempty with hT | hT
    · subst hT
      simp only [Finset.biUnion_empty, Finset.union_empty]
      simp [State.pr]
      ring
    · have hd : Disjoint (f a) (T.biUnion f) := by
        rw [Finset.disjoint_biUnion_right]
        intro e he
        exact hdisj a (Finset.mem_insert_self a T) e (Finset.mem_insert_of_mem he)
          (fun h => ha (h ▸ he))
      have hpa : 0 < probOf s.P (f a) := hpos a (Finset.mem_insert_self a T)
      have hpT : 0 < probOf s.P (T.biUnion f) := by
        obtain ⟨e, he⟩ := hT
        exact lt_of_lt_of_le (hpos' e he) (probOf_mono _ (Finset.subset_biUnion_of_mem f he))
      have := s.avg (f a) (T.biUnion f) hd hpa hpT
      simp only [State.pr] at this ⊢
      rw [this]
      ring

/-- The averaging axiom over the cells of an exogenous designation, when every cell part of `X`
is positive: `V(X) · P(X) = ∑_e P(X ∧ e) V(X ∧ e)`.
Source: none: infrastructure
Kind: L -/
theorem V_mul_pr_eq_sum_cells_of_pos (s : State Ω K) (exo : Ω → E) (X : Finset Ω)
    (hpos : ∀ e, 0 < s.pr (X ∩ cell exo e)) :
    s.V X * s.pr X = ∑ e, s.pr (X ∩ cell exo e) * s.V (X ∩ cell exo e) := by
  have hU : (Finset.univ : Finset E).biUnion (fun e => X ∩ cell exo e) = X := by
    ext ω
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter, mem_cell]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨exo ω, h, rfl⟩⟩
  have := V_mul_pr_biUnion s Finset.univ (fun e => X ∩ cell exo e)
    (fun e _ e' _ hne => Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right (cell_disjoint exo hne)))
    (fun e _ => hpos e)
  rwa [hU] at this

end avg

section nrV

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- **Axiom NR forces the desirability of the act too** (T8, repair round 1, audit r1 B1): under
`NRAt`, if every cell meets `a` positively and `t.s` is support-regular, then the counterfactual
component's value of `a` is the K-partition state's: `V^a(a) = ∑_e P(e) V(a ∧ e)`.
Derivation: success makes the stay worlds `cf`-null, so clause (i) pins `P^a(a ∧ e) = P(e)`;
clause (iii) at `X = a` pins `V^a(a ∧ e) = V(a ∧ e)`; the averaging axiom of `cf a` over the
cells (`V_mul_pr_eq_sum_cells_of_pos`) assembles `V^a(a)`; `kPart_V_of_suppRegular` evaluates
the K-partition side to the same sum.
Source: [[non-responsiveness]] "Axiom NR" (the `V`-clause: "`V^a_s(X ∧ a ∧ e) = V_s(X ∧ a ∧ e)`")
and the five-evaluation table's "NR-cf(cross)"; mandate T8
Kind: P
Fidelity: exact for the `V`-clause as rendered in `NRAt`; the positivity of every cell is the
hypothesis under which the axiom determines `V^a(a)` at all (module docstring)
Hyps: (a) `NRAt`; (a) every cell meets `a` positively; (a) `t.s` support-regular -/
theorem nr_forces_kpart_V {A : Type} (t : CfState Ω K) (actEv : A → Finset Ω) (exo : Ω → E)
    (hNR : NRAt t actEv exo) (hreg : SuppRegular t.s) (a : A) (h : (actEv a).Nonempty)
    (hpos : ∀ e, 0 < t.s.pr (actEv a ∩ cell exo e)) :
    (t.cf (actEv a) h).V (actEv a) = (kPart t.s (actEv a) exo).V (actEv a) := by
  obtain ⟨h1, -, h3⟩ := hNR a h
  set cf := t.cf (actEv a) h with hcf
  have hsucc : cf.pr (actEv a) = 1 := t.success _ h
  -- the complement of the act is `cf`-null
  have hcompl : cf.pr (Finset.univ \ actEv a) = 0 := by
    have hd : Disjoint (actEv a) (Finset.univ \ actEv a) := Finset.disjoint_sdiff
    have hu := probOf_union cf.P hd
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _), probOf_univ] at hu
    simp only [State.pr] at hsucc ⊢
    linarith
  -- clause (i) + success: `P^a(a ∧ e) = P(e)`
  have hcfcell : ∀ e, cf.pr (actEv a ∩ cell exo e) = t.s.pr (cell exo e) := by
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
    simp only [State.pr] at hu hz ⊢
    rw [hu, hz, add_zero]
  -- clause (iii) at `X = a`: `V^a(a ∧ e) = V(a ∧ e)`
  have hV : ∀ e, cf.V (actEv a ∩ cell exo e) = t.s.V (actEv a ∩ cell exo e) := by
    intro e
    have := h3 e (actEv a) (by rw [Finset.inter_self]; exact hpos e)
    rwa [Finset.inter_self] at this
  -- the averaging axiom of `cf` over the cells
  have hcfpos : ∀ e, 0 < cf.pr (actEv a ∩ cell exo e) := by
    intro e
    rw [hcfcell e]
    exact lt_of_lt_of_le (hpos e) (probOf_mono _ Finset.inter_subset_right)
  have hL := V_mul_pr_eq_sum_cells_of_pos cf exo (actEv a) hcfpos
  rw [hsucc, mul_one] at hL
  rw [hL, Finset.sum_congr rfl fun e _ => by rw [hcfcell e, hV e]]
  -- the K-partition side
  rw [kPart_V_of_suppRegular t.s hreg]
  have hcomp : ∀ e, (kPartComp t.s (actEv a) exo e).pr (actEv a) = 1 ∧
      (kPartComp t.s (actEv a) exo e).V (actEv a) = t.s.V (actEv a ∩ cell exo e) := by
    intro e
    unfold kPartComp
    rw [dif_pos (hpos e), jeffreyCond_pr, jeffreyCond_V]
    have hset : actEv a ∩ (actEv a ∩ cell exo e) = actEv a ∩ cell exo e := by
      rw [← Finset.inter_assoc, Finset.inter_self]
    rw [hset]
    exact ⟨div_self (hpos e).ne', rfl⟩
  have hnum : ∑ e, t.s.pr (cell exo e) * (kPartComp t.s (actEv a) exo e).pr (actEv a)
      * (kPartComp t.s (actEv a) exo e).V (actEv a)
      = ∑ e, t.s.pr (cell exo e) * t.s.V (actEv a ∩ cell exo e) :=
    Finset.sum_congr rfl fun e _ => by rw [(hcomp e).1, (hcomp e).2, mul_one]
  have hden : ∑ e, t.s.pr (cell exo e) * (kPartComp t.s (actEv a) exo e).pr (actEv a) = 1 := by
    rw [Finset.sum_congr rfl fun e _ => by rw [(hcomp e).1, mul_one]]
    exact (cellDistr t.s exo).sum_one
  rw [hnum, hden, div_one]

end nrV

end Cleanroom.Decision.DpCausalConsist
