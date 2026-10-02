import Cleanroom.Decision.DpCausalConsist.Collapse

/-!
# `dp-causal-consist`: Axiom NR — the K-partition iff, what NR forces, the recording-point coincidence (T8)

* `nr_kpart_iff`: for a state with `P(A) > 0`, the K-partition state `∑_e P(e) P(· | A, e)` has the
  act-conditional `P(· | A)` as its law **iff** `P(A ∧ e) = P(A) P(e)` for every cell — the wiki's
  "`∑_e P(e) P(X | a, e) = P(X | a)` for all `X` iff `P(e | a) = P(e)` for all `e`", with the cell
  guards made explicit: on a cell with `P(e) > 0 = P(A ∧ e)` the printed sum is not a probability
  (finding §6.4); `kPart`'s fallback there is `P(· | e)`, and the iff survives because such a cell
  makes `kPart(A) < 1`.
* `nr_forces_kpart`: `NRAt` forces `P^a = kPart` on the cells where `P(a ∧ e) > 0`; with every
  positive cell meeting `a` positively, `P^a = kPart` outright. The N− companion (an `NRAt` state
  on a bad cell whose `cf a` differs from `kPart`) is `TbThetaNR.lean`'s `cfNR_ne_kPart`; the
  `V`-component is forced too, where every cell meets `a` positively, by `NRValue.lean`'s
  `nr_forces_kpart_V` (repair round 1).
* `nr_evidential_at_recording`: at a recorded point under strict calibration with pre-query
  cells, Lemma 3′ gives the cell independence, so NR forces `P^a = P(· | a)` — Axiom NR and
  Definition 20's evidential criterion coincide there (composition of `pr_inter_eq_mul_of_recordsFor`,
  `nr_forces_kpart`, `nr_kpart_iff`).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

section kpart

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- `probOf` of the empty event. Source: none: infrastructure. Kind: L -/
theorem probOf_empty (P : FinDistr K Ω) : probOf P ∅ = 0 := by simp [probOf]

/-- A sub-event of a null event is null. Source: none: infrastructure. Kind: L -/
theorem pr_eq_zero_of_subset (s : State Ω K) {X Y : Finset Ω} (h : X ⊆ Y) (hY : s.pr Y = 0) :
    s.pr X = 0 :=
  le_antisymm (by rw [← hY]; exact probOf_mono _ h) (probOf_nonneg _ _)

/-- The law of a K-partition component at a cell, by cases.
Source: none: infrastructure
Kind: L -/
theorem kPartComp_pr (s : State Ω K) (A : Finset Ω) (exo : Ω → E) (e : E) (X : Finset Ω) :
    (kPartComp s A exo e).pr X =
      if 0 < s.pr (A ∩ cell exo e) then s.pr (X ∩ (A ∩ cell exo e)) / s.pr (A ∩ cell exo e)
      else if 0 < s.pr (cell exo e) then s.pr (X ∩ cell exo e) / s.pr (cell exo e) else s.pr X := by
  unfold kPartComp
  split_ifs with h1 h2
  · rw [jeffreyCond_pr]
  · rw [jeffreyCond_pr]
  · rfl

/-- The law of the K-partition state as a cell sum. Source: none: infrastructure. Kind: L -/
theorem kPart_pr (s : State Ω K) (A : Finset Ω) (exo : Ω → E) (X : Finset Ω) :
    (kPart s A exo).pr X = ∑ e, s.pr (cell exo e) * (kPartComp s A exo e).pr X :=
  mixState_pr _ _ X

/-- **The K-partition iff** (T8, `nr_kpart_iff`): for `P(A) > 0`, `∑_e P(e) P(· | A, e) = P(· | A)`
iff `P(A ∧ e) = P(A) P(e)` for every cell `e`.
Source: [[non-responsiveness]] "Consistency with cf = conditional" ("`∑_e P(e) P(X | a, e) = P(X | a)`
for all `X` iff `P(e | a) = P(e)` for all `e ∈ 𝓔_exo`"); mandate T8
Kind: P
Fidelity: exact for the package's `kPart`, whose bad-cell fallback is `P(· | e)` (finding §6.4);
the `→` direction is robust to the fallback — any component with `(kPartComp e).pr A ≠ 1` on a
bad cell (the wiki's junk-`0` summand included) makes `kPart(A) < 1`, so the iff holds under
the printed convention too; the `←` direction never meets a bad cell
Hyps: (a) `0 < P(A)` -/
theorem nr_kpart_iff (s : State Ω K) (A : Finset Ω) (hA : 0 < s.pr A) (exo : Ω → E) :
    (∀ X, (kPart s A exo).pr X = (jeffreyCond s A hA).pr X) ↔
      ∀ e, s.pr (A ∩ cell exo e) = s.pr A * s.pr (cell exo e) := by
  constructor
  · intro h
    -- no bad cells
    have hbad : ∀ e, 0 < s.pr (cell exo e) → 0 < s.pr (A ∩ cell exo e) := by
      intro e he
      by_contra hcon
      have hAe : s.pr (A ∩ cell exo e) = 0 := le_antisymm (not_lt.mp hcon) (probOf_nonneg _ _)
      have h1 := h A
      rw [jeffreyCond_pr, Finset.inter_self, div_self hA.ne', kPart_pr] at h1
      have hle : ∀ e' ∈ (Finset.univ : Finset E),
          s.pr (cell exo e') * (kPartComp s A exo e').pr A ≤ s.pr (cell exo e') := fun e' _ =>
        mul_le_of_le_one_right (probOf_nonneg _ _) (probOf_le_one _ _)
      have hsum : ∑ e', s.pr (cell exo e') = 1 := (cellDistr s exo).sum_one
      have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [h1, hsum]) e (Finset.mem_univ e)
      have hc : (kPartComp s A exo e).pr A = 1 := (mul_eq_left₀ he.ne').mp heq
      rw [kPartComp_pr, if_neg hcon, if_pos he, hAe, zero_div] at hc
      exact zero_ne_one hc
    intro e
    have h1 := h (cell exo e)
    rw [jeffreyCond_pr, kPart_pr_of_pos s A exo hbad, Finset.sum_eq_single e] at h1
    · rcases (probOf_nonneg s.P (cell exo e)).lt_or_eq with he | he
      · have hAe := hbad e he
        have hset : cell exo e ∩ (A ∩ cell exo e) = A ∩ cell exo e := by
          ext ω; simp only [Finset.mem_inter]; tauto
        rw [hset, div_self hAe.ne', mul_one, Finset.inter_comm, eq_div_iff hA.ne'] at h1
        rw [← h1]; ring
      · have h0 : s.pr (A ∩ cell exo e) = 0 :=
          pr_eq_zero_of_subset s Finset.inter_subset_right he.symm
        have he' : s.pr (cell exo e) = 0 := he.symm
        rw [h0, he', mul_zero]
    · intro e' _ hne
      have hset : cell exo e ∩ (A ∩ cell exo e') = ∅ := by
        ext ω
        simp only [Finset.mem_inter, mem_cell, Finset.notMem_empty, iff_false, not_and]
        intro h1 _ h2; exact hne (h2.symm.trans h1)
      rw [hset]
      simp [State.pr, probOf_empty]
    · intro h'; exact absurd (Finset.mem_univ e) h'
  · intro h X
    have hpos : ∀ e, 0 < s.pr (cell exo e) → 0 < s.pr (A ∩ cell exo e) := fun e he => by
      rw [h e]; exact mul_pos hA he
    rw [kPart_pr_of_pos s A exo hpos X, jeffreyCond_pr, pr_eq_sum_cells s exo (X ∩ A),
      Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    rcases (probOf_nonneg s.P (cell exo e)).lt_or_eq with he | he
    · rw [h e, Finset.inter_assoc]
      field_simp
    · have h0 : s.pr (X ∩ A ∩ cell exo e) = 0 :=
        pr_eq_zero_of_subset s Finset.inter_subset_right he.symm
      have he' : s.pr (cell exo e) = 0 := he.symm
      rw [h0, he']; simp

end kpart

section nr

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] {E : Type} [Fintype E] [DecidableEq E]

/-- **Axiom NR forces the K-partition law on the good cells** (T8, `nr_forces_kpart`): under
`NRAt`, if every positive cell meets the act positively, `P^a = ∑_e P(e) P(· | a, e)`.
Source: [[non-responsiveness]] "Axiom NR" ("Hence `P^a_s = ∑_e P_s(e) P_s(· | a, e)`"); mandate T8
Kind: P
Fidelity: exact (the positivity of `P(a ∧ e)` on positive cells is where the wiki's "hence" is
silent, finding §6.4)
Hyps: (a) `NRAt`; (a) positive cells meet `a` positively -/
theorem nr_forces_kpart {A : Type} (t : CfState Ω K) (actEv : A → Finset Ω) (exo : Ω → E)
    (hNR : NRAt t actEv exo) (a : A) (h : (actEv a).Nonempty)
    (hpos : ∀ e, 0 < t.s.pr (cell exo e) → 0 < t.s.pr (actEv a ∩ cell exo e)) (X : Finset Ω) :
    (t.cf (actEv a) h).pr X = (kPart t.s (actEv a) exo).pr X := by
  obtain ⟨h1, h2, -⟩ := hNR a h
  rw [kPart_pr_of_pos t.s (actEv a) exo hpos X, pr_eq_sum_cells (t.cf (actEv a) h) exo X]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases (probOf_nonneg t.s.P (cell exo e)).lt_or_eq with he | he
  · have hAe := hpos e he
    have key := h2 e X hAe
    rw [h1 e] at key
    rw [← Finset.inter_assoc, mul_div_assoc', eq_div_iff hAe.ne']
    exact key
  · have hcf : (t.cf (actEv a) h).pr (cell exo e) = 0 := by rw [h1 e]; exact he.symm
    have he' : t.s.pr (cell exo e) = 0 := he.symm
    rw [pr_eq_zero_of_subset _ Finset.inter_subset_right hcf, he', zero_mul]

variable {ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)]

/-- **At a recorded point Axiom NR is the evidential criterion** (T8, `nr_evidential_at_recording`):
if `B` records at `d` for `C` with `ν(O_d) > 0` and the strict clauses, the exogenous cells are
pre-query, and `t.s = s_d`, then for every `a ∈ A_d^+` an `NRAt` counterfactual component has
`P^a = P_{s_d}(· | a)`: Lemma 3′ supplies `P(a ∧ e) = P(a) P(e)` on every cell, NR forces the
K-partition law, and the K-partition law is the conditional.
Source: [[non-responsiveness]] "Consistency with cf = conditional" ("At a recording point with
`𝓔_exo` the pre-query chance algebra, Lemma 3 gives that independence, so Axiom NR and
Definition 20's evidential criterion coincide"); mandate T8
Kind: C
Fidelity: exact
Hyps: (a) recording; (a) `0 < ν(O_d)`; (a) clause 1; (a) cells pre-query; (a) `NRAt`; (a) `a ∈ A_d^+` -/
theorem nr_evidential_at_recording (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    {C : Proc ι acts ℚ} {B : Tree Ω ι acts ℚ} {d : ι} (s : ι → State Ω ℚ)
    (hrec : RecordsFor obs actEv C B d) (hO : 0 < nu C B (obs d))
    (h1 : StrictClause1At s obs C B d) (exo : Ω → E)
    (hpre : ∀ e, PreQuery obs C B d (cell exo e)) (t : CfState Ω ℚ) (hts : t.s = s d)
    (hNR : NRAt t (actEv d) exo) (a : acts d) (ha : a ∈ APlus s actEv d)
    (h : (actEv d a).Nonempty) (X : Finset Ω) :
    (t.cf (actEv d a) h).pr X
      = (jeffreyCond (s d) (actEv d a) (Finset.mem_filter.mp ha).2).pr X := by
  have hApos : 0 < (s d).pr (actEv d a) := (Finset.mem_filter.mp ha).2
  have hind : ∀ e, (s d).pr (actEv d a ∩ cell exo e) = (s d).pr (actEv d a) * (s d).pr (cell exo e) := by
    intro e
    rw [Finset.inter_comm, pr_inter_eq_mul_of_recordsFor obs actEv s hrec hO h1 (hpre e) a]
    ring
  have hpos : ∀ e, 0 < t.s.pr (cell exo e) → 0 < t.s.pr (actEv d a ∩ cell exo e) := by
    intro e he
    rw [hts] at he ⊢
    rw [hind e]; exact mul_pos hApos he
  rw [nr_forces_kpart t (actEv d) exo hNR a h hpos X, hts]
  exact (nr_kpart_iff (s d) (actEv d a) hApos exo).mpr hind X

end nr

end Cleanroom.Decision.DpCausalConsist
