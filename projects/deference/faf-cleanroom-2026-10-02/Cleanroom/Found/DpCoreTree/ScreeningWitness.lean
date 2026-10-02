import Cleanroom.Found.DpCoreTree.Screening
import Cleanroom.Found.DpCoreTree.Witnesses

/-!
# Lemma 3′: the N+ witness and the refutation of the SSC form under recording alone

* `coinQuery_recordsFor`, `coinQuery_preQuery_coin`, `coinQuery_screening_instance`: the
  coin-then-query tree inhabits Lemma 3′'s full hypothesis package with a non-degenerate
  pre-query event (`ν({c=1} ∩ O_d) = ½`, `ν(a ∩ O_d) = q`), and the identity reads
  `½q · 1 = ½ · q`.
* `mug1_ssc_refuted`: the mugging `B₁` at `C(d) = ½` is recorded at `d` and `O_T` is pre-query,
  yet the occurrence-conditioned form fails: `occ(d)` is every leaf and
  `μ(O_T ∩ pay ∩ occ) · μ(occ) = ¼ ≠ ⅛ = μ(O_T ∩ occ) · μ(pay ∩ occ)`. So the SSC form needs
  `H*` (the hypothetical `H`-branch query breaks "`occ(d)` = the `O_d`-runs").
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-! ### The coin-then-query tree -/

/-- Every path of the coin-then-query tree meets `d` exactly once.
Source: mandate T6
Kind: L -/
theorem coinQuery_count (ℓ : coinQuery.Leaves) : count () coinQuery ℓ = 1 := by
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  rfl

/-- The coin-then-query tree is recorded at `d` for every procedure.
Source: mandate T6
Kind: N+ -/
theorem coinQuery_recordsFor (C : Proc Unit (fun _ => Act2) ℚ) :
    RecordsFor cqObs cqActEv C coinQuery () := by
  intro ℓ _ _
  refine ⟨coinQuery_count ℓ, ?_⟩
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  rintro ⟨i', (_ | ⟨b, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' _; simp [cqObs]
      · simp [cqActEv]
      · intro a' ha'
        simp [cqActEv] at ha'
        first | exact ha'.symm | exact ha'
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-- `{c = 1}` is pre-query for `d`.
Source: mandate T6
Kind: N+ -/
theorem coinQuery_preQuery_coin (C : Proc Unit (fun _ => Act2) ℚ) :
    PreQuery cqObs C coinQuery () cqCoin := by
  intro ℓ _ _ q _ hq
  unfold coinQuery at ℓ q hq ⊢
  rcases q with ⟨i', (_ | ⟨b, q'⟩)⟩
  · -- the `d`-node below coin outcome `i'` decides `{c = 1}`
    by_cases hi : i' = 0
    · left
      rintro ⟨j, act, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hji : j = i'
      · subst hji; simp [cqCoin, hi]
      · simp [edgeOf_chance, hji] at hj
    · right
      rintro ⟨j, act, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hji : j = i'
      · subst hji; simp [cqCoin, hi]
      · simp [edgeOf_chance, hji] at hj
  · exact q'.elim

/-- `ν` on the coin-then-query tree as an explicit sum.
Source: none: infrastructure
Kind: L -/
theorem coinQuery_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset CoinQueryW) :
    nu C coinQuery X =
      ∑ i : Fin 2, ∑ act : Act2, if (decide (i = 0), act) ∈ X
        then (1/2 : ℚ) * (C ()).w act else 0 := by
  rw [nu_eq_sum]
  unfold coinQuery
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [world_chance, world_decision, world_leaf, leafLaw_chance, leafLaw_decision,
    leafLaw_leaf, FinDistr.fair, FinDistr.coin, mul_one]
  fin_cases i <;> simp <;> norm_num

/-- **Lemma 3′ instantiated, non-degenerately**: on the coin-then-query tree with
`C(d) = (q, 1−q)`, `ν({c=1} ∩ a ∩ O) = q/2`, `ν(O) = 1`, `ν({c=1} ∩ O) = ½`, `ν(a ∩ O) = q`.
Source: mandate T6 (N+ inhabiting the full hypothesis package with `ν(O_d) > 0` and
`ν(a ∩ O_d) > 0` for `q > 0`)
Kind: N+ -/
theorem coinQuery_screening_instance (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (procQ q h0 h1) coinQuery (cqCoin ∩ cqActEv () .a ∩ cqObs ()) = q / 2 ∧
    nu (procQ q h0 h1) coinQuery (cqObs ()) = 1 ∧
    nu (procQ q h0 h1) coinQuery (cqCoin ∩ cqObs ()) = 1 / 2 ∧
    nu (procQ q h0 h1) coinQuery (cqActEv () .a ∩ cqObs ()) = q := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [coinQuery_nu]
    simp [Fin.sum_univ_two, Act2.sum_univ, cqCoin, cqActEv, cqObs, procQ] <;> ring

/-! ### The mugging refutes the SSC form under recording alone -/

/-- `B₁` at `C(d) = ½` is recorded at `d` (the `T`-branch node is the unique `d`-node on
`O_T`-runs; it is subtree-veridical and action-veridical; the `H`-branch query is a simulation
off `O_T`).
Source: [[decision-problems-v2]] Proposition 6; `faithful.md` ("`B₁` — F3′ and Def 7")
Kind: N+ -/
theorem mug1_recordsFor (x y : ℚ) :
    RecordsFor mugObs mugActEv (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) () := by
  intro ℓ _ hobs
  unfold mug1 at ℓ hobs ⊢
  rcases ℓ with ⟨i, act, _⟩
  refine ⟨rfl, ?_⟩
  rintro ⟨i', (_ | ⟨b, q⟩)⟩ hq a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      fin_cases i
      · refine ⟨?_, ?_, ?_⟩
        · rintro ⟨j, b, _⟩ hj
          rw [mem_leavesBelow] at hj
          by_cases hj0 : j = 0
          · subst hj0; cases b <;> simp [mugObs, mugWorld1]
          · simp [edgeOf_chance, hj0] at hj
        · cases act <;> simp [mugActEv, mugWorld1]
        · intro a' ha'; cases act <;> cases a' <;> simp_all [mugActEv, mugWorld1, mugObs]
      · exfalso
        cases act <;> simp [mugObs, mugWorld1] at hobs
    · simp [edgeOf_chance, hi] at ha
  · exact q.elim

/-- `O_T` is pre-query for `d` on `B₁`.
Source: mandate T6
Kind: N+ -/
theorem mug1_preQuery_obs (x y : ℚ) :
    PreQuery mugObs (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) () (mugObs ()) := by
  intro ℓ _ hobs q _ hq
  unfold mug1 at ℓ hobs q hq ⊢
  rcases ℓ with ⟨i, act, _⟩
  rcases q with ⟨i', (_ | ⟨b, q'⟩)⟩
  · by_cases hi : i = i'
    · subst hi
      fin_cases i
      · left
        rintro ⟨j, b, _⟩ hj
        rw [mem_leavesBelow] at hj
        by_cases hj0 : j = 0
        · subst hj0; cases b <;> simp [mugObs, mugWorld1]
        · simp [edgeOf_chance, hj0] at hj
      · exfalso
        cases act <;> simp [mugObs, mugWorld1] at hobs
    · simp [edgeOf_chance, hi] at hq
  · exact q'.elim

/-- `μ` on `B₁` of a run event as an explicit sum.
Source: none: infrastructure
Kind: L -/
theorem mug1_mass (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) (P : (mug1 x y).Leaves → Prop)
    [DecidablePred P] :
    mass C (mug1 x y) (Finset.univ.filter P) =
      ∑ i : Fin 2, ∑ act : Act2, if P ⟨i, ⟨act, ()⟩⟩ then (1/2 : ℚ) * (C ()).w act else 0 := by
  rw [mass_filter]
  unfold mug1
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair, FinDistr.coin,
    mul_one]
  fin_cases i <;> simp <;> norm_num

/-- **SSC screening fails under recording alone**: on `B₁` at `C(d) = ½`, with `X = O_T`
(pre-query) and `a` = pay, `μ(X ∩ a ∩ occ) · μ(occ) = ¼` while `μ(X ∩ occ) · μ(a ∩ occ) = ⅛`.
Source: mandate T6 ("refuted under `RecordsFor` alone by the mugging `B₁` at `C(d) = ½`:
`occ d` is every leaf, and `μ(coin=T ∣ pay) = 1 ≠ ½`"); `sl-defensible-claims.md` S4 ("the
SSC version needs `H*`")
Kind: N−
Fidelity: exact (the refuted statement is `screening_ssc_of_hStar`'s conclusion with
`RecordsFor` in place of `H*`) -/
theorem mug1_ssc_refuted (x y : ℚ) :
    RecordsFor mugObs mugActEv (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) () ∧
    PreQuery mugObs (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) () (mugObs ()) ∧
    mass (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y)
        (worldEv (mug1 x y) (mugObs () ∩ mugActEv () .a) ∩ occ () (mug1 x y)) *
      mass (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y) (occ () (mug1 x y)) ≠
    mass (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y)
        (worldEv (mug1 x y) (mugObs ()) ∩ occ () (mug1 x y)) *
      mass (procQ (1/2) (by norm_num) (by norm_num)) (mug1 x y)
        (worldEv (mug1 x y) (mugActEv () .a) ∩ occ () (mug1 x y)) := by
  refine ⟨mug1_recordsFor x y, mug1_preQuery_obs x y, ?_⟩
  have hocc : occ () (mug1 x y) = Finset.univ := by
    ext ℓ
    unfold mug1 at ℓ ⊢
    rcases ℓ with ⟨i, act, _⟩
    simp
  have e1 : ∀ (Y : Finset MugW), worldEv (mug1 x y) Y ∩ occ () (mug1 x y) =
      Finset.univ.filter fun ℓ => world (mug1 x y) ℓ ∈ Y := by
    intro Y; rw [hocc, Finset.inter_univ]; rfl
  rw [e1, e1, e1, hocc, mass_univ, mug1_mass, mug1_mass, mug1_mass]
  unfold mug1
  simp [Fin.sum_univ_two, Act2.sum_univ, mugObs, mugActEv, mugWorld1, procQ]
  norm_num

end Cleanroom.Found.DpCoreTree
