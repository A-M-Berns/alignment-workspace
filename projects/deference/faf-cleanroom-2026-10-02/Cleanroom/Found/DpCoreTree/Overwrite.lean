import Cleanroom.Found.DpCoreTree.Screening
import Cleanroom.Found.DpCoreTree.Tickle

/-!
# The overwrite tree: Lemma 3's world-level clause needs recording (findings F1)

dp-core-083's overwrite tree, made concrete (repair round 1; adopted from the fidelity audit's
probe `audit-r1-probes/Fidelity.lean` and extended with the run-level instance): `ℓ ∼ Bern(½)`
(index `0` = lesion); query `d`, drawing `m'`; a post-draw coin fires with probability `½` on
the lesion branch and `0` off it, and when it fires overwrites the act coordinate with `m := 1`;
then `k ∼ Bern(γ_ℓ)` with `γ₁ = ¾`, `γ₀ = ¼`; leaf `(ℓ, m, k)`, payoff `0`.

* Every run meets `d` exactly once (`overwrite_count`) and `{ℓ = 1}` is decided at every
  `d`-node (`overwrite_decided_lesion`), so the printed Lemma 3's hypothesis shape holds and the
  run-level theorem `screening_draw` applies: `μ({ℓ=1} ∩ drew₁) · μ(occ) = μ({ℓ=1} ∩ occ) ·
  μ(drew₁)`, numerically `¼ · 1 = ½ · ½` (`overwrite_screening_draw`, `overwrite_draw_values`).
* The world-level clause `m ⊥ ℓ` under `ν` **fails**: `ν(m=1 ∧ ℓ=1) · ν(⊤) = 3/8 ≠ 5/16 =
  ν(m=1) · ν(ℓ=1)` (`overwrite_m_not_indep_lesion`).
* The tree is not Definition-7 recorded at `d` (`overwrite_not_recordsFor`): on the positive run
  (lesion, draw `0`, coin fires) the world's act coordinate is `1`, so clause 3 fails. The
  passage from the draw to the act is recording, which the printed lemma does not assume.

Both post-query coins are functions of `ℓ` and (through `owM`) of the draw only — the printed
lemma's informal "post-query chance depends on the path only through pre-query chance and the
drawn action" holds by inspection; it is not a tree predicate of this package (mandate
alternative (b)).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Catalogue Tree

/-- Overwrite worlds `(ℓ, m, k)`: lesion, act coordinate, cancer.
Source: [[decision-problems-v2]] §7.3 (the `(ℓ, m, k)` worlds); dp-core-083
Kind: D -/
abbrev OwW : Type := Bool × Bool × Bool

/-- `O_d = ⊤` (S3).
Source: [[decision-problems-v2]] §7.3 (S3)
Kind: D -/
def owObs : Unit → Finset OwW := fun _ => Finset.univ

/-- Action events `{m = ·}` (the act coordinate of the world, as in the tickle tree).
Source: [[decision-problems-v2]] §7.3 (S1)
Kind: D -/
def owActEv (_ : Unit) (m : Bool) : Finset OwW := Finset.univ.filter fun w => w.2.1 = m

/-- The act coordinate: on the lesion branch (`i = 0`) a post-draw coin (`j = 0` = fires)
overwrites the draw with `m = 1`; otherwise the draw stands.
Source: dp-core-083 (the overwrite)
Kind: D -/
def owM (i : Fin 2) (m' : Bool) (j : Fin 2) : Bool := if i = 0 ∧ j = 0 then true else m'

/-- The procedure `C(d)(m' = 1) = ½`.
Source: none: infrastructure
Kind: D -/
def owProc : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.bool (1/2) (by norm_num) (by norm_num)

/-- **The overwrite tree** (dp-core-083, lesion side): `ℓ ∼ Bern(½)` (index `0` = lesion);
query `d`, drawing `m'`; a post-draw coin fires with probability `δ = ½` on the lesion branch
and `0` off it, and when it fires sets `m := 1`; then `k ∼ Bern(γ_ℓ)` with `γ₁ = ¾`, `γ₀ = ¼`;
leaf `(ℓ, m, k)`, payoff `0`. Every run meets `d` exactly once, and every post-query chance
node's distribution is a function of `ℓ` (and, through `owM`, of the draw) only — the printed
Lemma 3's hypothesis shape.
Source: dp-core-083; [[decision-problems-v2]] §7.3 Lemma 3 (the hypothesis it fails to cover)
Kind: D -/
def overwrite : Tree OwW Unit (fun _ => Bool) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision () fun m' =>
      .chance 2 (FinDistr.coin (if i = 0 then 1/2 else 0) (by split_ifs <;> norm_num)
          (by split_ifs <;> norm_num)) fun j =>
        .chance 2 (FinDistr.coin (if i = 0 then 3/4 else 1/4) (by split_ifs <;> norm_num)
            (by split_ifs <;> norm_num)) fun k =>
          .leaf (decide (i = 0), owM i m' j, decide (k = 0)) 0

/-- The event `{m = 1}`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def owM1 : Finset OwW := Finset.univ.filter fun w => w.2.1 = true

/-- The event `{ℓ = 1}`. Source: [[decision-problems-v2]] §7.3. Kind: D -/
def owL1 : Finset OwW := Finset.univ.filter fun w => w.1 = true

/-- Every run of the overwrite tree meets `d` exactly once.
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("each run realizes at most one `d`-node")
Kind: L -/
theorem overwrite_count (ℓ : overwrite.Leaves) : count () overwrite ℓ = 1 := by
  unfold overwrite at ℓ ⊢
  rcases ℓ with ⟨i, m', j, k, _⟩
  rfl

/-- `{ℓ = 1}` is decided at every `d`-node of the overwrite tree.
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("pre-query events")
Kind: L -/
theorem overwrite_decided_lesion (q : overwrite.DecNode) : DecidedAt overwrite q owL1 := by
  unfold overwrite at q ⊢
  rcases q with ⟨i, (_ | ⟨m', ⟨j, ⟨k, e⟩⟩⟩)⟩
  · by_cases hi : i = 0
    · left
      rintro ⟨i', m', j, k, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hii : i' = i
      · subst hii; simp [owL1, hi]
      · simp [edgeOf_chance, hii] at hj
    · right
      rintro ⟨i', m', j, k, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hii : i' = i
      · subst hii; simp [owL1, hi]
      · simp [edgeOf_chance, hii] at hj
  · exact e.elim

/-- `μ` on the overwrite tree of a run event as an explicit sixteen-term sum.
Source: none: infrastructure
Kind: L -/
theorem overwrite_mass (C : Proc Unit (fun _ => Bool) ℚ) (P : overwrite.Leaves → Prop)
    [DecidablePred P] :
    mass C overwrite (Finset.univ.filter P) =
      ∑ i : Fin 2, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        if P ⟨i, m', j, k, ()⟩ then leafLaw C overwrite ⟨i, m', j, k, ()⟩ else 0 := by
  rw [mass_filter]
  unfold overwrite
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Tree.sum_leaves_leaf]

/-- `ν` on the overwrite tree as an explicit sixteen-term sum.
Source: none: infrastructure
Kind: L -/
theorem overwrite_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset OwW) :
    nu C overwrite X =
      ∑ i : Fin 2, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        if (decide (i = 0), owM i m' j, decide (k = 0)) ∈ X then
          leafLaw C overwrite ⟨i, m', j, k, ()⟩ else 0 := by
  rw [nu_eq_sum]
  unfold overwrite
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Tree.sum_leaves_leaf]
  rfl

/-- The leaf masses of the overwrite tree under `C(d)(m'=1) = ½`, from `leafLaw`.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: L -/
theorem overwrite_leafLaw (i : Fin 2) (m' : Bool) (j k : Fin 2) :
    leafLaw owProc overwrite ⟨i, m', j, k, ()⟩ =
      (1/2 : ℚ) * (1/2) *
        (if i = 0 then (if j = 0 then 1/2 else 1/2) else (if j = 0 then 0 else 1)) *
        (if i = 0 then (if k = 0 then 3/4 else 1/4) else (if k = 0 then 1/4 else 3/4)) := by
  unfold overwrite
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair, FinDistr.coin]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> cases m' <;> simp [owProc, FinDistr.bool] <;>
    norm_num

/-- The four world-level masses: `ν(m=1 ∧ ℓ=1) = 3/8`, `ν(⊤) = 1`, `ν(m=1) = 5/8`,
`ν(ℓ=1) = ½`.
Source: dp-core-083
Kind: N+ -/
theorem overwrite_nu_values :
    nu owProc overwrite (owM1 ∩ owL1) = 3/8 ∧
    nu owProc overwrite Finset.univ = 1 ∧
    nu owProc overwrite owM1 = 5/8 ∧
    nu owProc overwrite owL1 = 1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [overwrite_nu]
    simp only [overwrite_leafLaw]
    simp [Fin.sum_univ_two, owM1, owL1, owM]
    norm_num

/-- **The printed Lemma 3's second clause fails on the overwrite tree**: `m` is not independent
of `ℓ` under `ν` — `ν(m=1 ∧ ℓ=1) · ν(⊤) = 3/8 ≠ 5/16 = ν(m=1) · ν(ℓ=1)` — although every run
meets `d` once and `{ℓ = 1}` is decided at every `d`-node (the run-level clause holds there:
`overwrite_screening_draw`).
Source: [[decision-problems-v2]] §7.3 Lemma 3 ("`m ⊥ (ℓ, k)` under `ν_{B,C}`"), refuted as
printed; dp-core-083; findings F1
Kind: N−
Fidelity: exact (the refuted statement is the lemma's second clause at `X = {ℓ = 1}`, with
`k` marginalised); refuted under the **explicit-hypothesis reading** — the lemma's two stated
clauses ("each run realizes at most one `d`-node", "post-query chance depends on the path only
through pre-query chance and the drawn action") as the whole hypothesis. Under the
**enumerated-shape reading**, where the preceding line "Instantiations: chance `ℓ`; query `d`;
act `m`; chance `k`; leaf `(ℓ, m, k)`" is part of the hypothesis and "act `m`" makes the leaf's
act coordinate the draw (recording's clauses 3–4, (S4)), this tree is out of the lemma's scope
and the lemma is under-hypothesised rather than false. -/
theorem overwrite_m_not_indep_lesion :
    nu owProc overwrite (owM1 ∩ owL1) * nu owProc overwrite Finset.univ ≠
      nu owProc overwrite owM1 * nu owProc overwrite owL1 := by
  obtain ⟨h1, h2, h3, h4⟩ := overwrite_nu_values
  rw [h1, h2, h3, h4]; norm_num

/-- **The overwrite tree is not Definition-7 recorded at `d`**: on the positive run (lesion,
draw `m' = 0`, coin fires, `k = 1`) the world's act coordinate is `1`, so the instance is not
action-veridical (clause 3). This is F1's "the passage from draw to act is recording", made
concrete.
Source: [[decision-problems-v2]] Definition 7 (clause 3); findings F1
Kind: N− -/
theorem overwrite_not_recordsFor : ¬ RecordsFor owObs owActEv owProc overwrite () := by
  intro h
  have hpos : 0 < leafLaw owProc overwrite ⟨0, false, 0, 0, ()⟩ := by
    rw [overwrite_leafLaw]; norm_num
  obtain ⟨_, h2⟩ := h ⟨0, false, 0, 0, ()⟩ hpos (by simp [owObs])
  have hedge : edgeOf overwrite ⟨0, none⟩ ⟨0, false, 0, 0, ()⟩ = some false := by
    unfold overwrite; simp [edgeOf_chance]
  have hav := (h2 ⟨0, none⟩ rfl false hedge).2.1
  simp [owActEv, overwrite, owM] at hav

/-- The four run-level masses: `μ({ℓ=1} ∩ drew₁) = ¼`, `μ(occ) = 1`, `μ({ℓ=1} ∩ occ) = ½`,
`μ(drew₁) = ½`.
Source: dp-core-083
Kind: N+ -/
theorem overwrite_draw_values :
    mass owProc overwrite (worldEv overwrite owL1 ∩ drew () true overwrite) = 1/4 ∧
    mass owProc overwrite (occ () overwrite) = 1 ∧
    mass owProc overwrite (worldEv overwrite owL1 ∩ occ () overwrite) = 1/2 ∧
    mass owProc overwrite (drew () true overwrite) = 1/2 := by
  have hocc : occ () overwrite = Finset.univ := by
    ext ℓ; simp [overwrite_count]
  have e1 : worldEv overwrite owL1 ∩ drew () true overwrite =
      Finset.univ.filter fun ℓ => world overwrite ℓ ∈ owL1 ∧
        (⟨(), true⟩ : Σ d : Unit, Bool) ∈ draws overwrite ℓ := by
    ext ℓ; simp [worldEv, drew]
  have e2 : worldEv overwrite owL1 ∩ occ () overwrite =
      Finset.univ.filter fun ℓ => world overwrite ℓ ∈ owL1 := by
    rw [hocc, Finset.inter_univ]; rfl
  have e3 : drew () true overwrite =
      Finset.univ.filter fun ℓ => (⟨(), true⟩ : Σ d : Unit, Bool) ∈ draws overwrite ℓ := by
    ext ℓ; simp [drew]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, overwrite_mass]
    simp only [overwrite_leafLaw]
    simp [Fin.sum_univ_two, owL1, overwrite, Sigma.mk.injEq, heq_eq_eq]
    norm_num
  · rw [hocc, mass_univ]
  · rw [e2, overwrite_mass]
    simp only [overwrite_leafLaw]
    simp [Fin.sum_univ_two, owL1, overwrite]
    norm_num
  · rw [e3, overwrite_mass]
    simp only [overwrite_leafLaw]
    simp [Fin.sum_univ_two, overwrite, Sigma.mk.injEq, heq_eq_eq]
    norm_num

/-- **The run-level clause holds on the overwrite tree** (`screening_draw` applied): with
`X = {ℓ = 1}` and the draw `m' = 1`, `μ(X ∩ drew₁) · μ(occ) = μ(X ∩ occ) · μ(drew₁)`,
numerically `¼ · 1 = ½ · ½` — while the world-level clause fails on the same tree
(`overwrite_m_not_indep_lesion`). This is the draw/act gap of findings F1 in one tree.
Source: [[decision-problems-v2]] §7.3 Lemma 3, first clause; findings F1
Kind: N+ -/
theorem overwrite_screening_draw :
    mass owProc overwrite (worldEv overwrite owL1 ∩ drew () true overwrite) *
        mass owProc overwrite (occ () overwrite) =
      mass owProc overwrite (worldEv overwrite owL1 ∩ occ () overwrite) *
        mass owProc overwrite (drew () true overwrite) :=
  screening_draw (fun ℓ _ => (overwrite_count ℓ).le)
    (fun _ _ q _ _ => overwrite_decided_lesion q) true

end Cleanroom.Found.DpCoreTree
