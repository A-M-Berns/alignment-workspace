import Cleanroom.Udt.UdtEndorsePolicy.NodeValue
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# T9: decision-flat refinements as a theorem about coupling graphs

Source: [[updateless-deference-ideate]] §5 Idea E ("endorsement⇔deference holds updatelessly iff
the update `u` refines the prior by a partition that is 'decision-flat'"); trust-lab-2-017. The
note defines nothing ("decision-flat", "biconvex" are imported by name); the rendering below is
the formalizer's (ATTRIBUTION-UNVETTED, fidelity `variant`).

**Rendering.** A *coupling graph* `G : S → S → Prop` on situations; `U` *respects* `G`
(`RespectsPairs G U`) if `U π = ∑ s, ∑ t, f s t (π s) (π t)` with `f s t = 0` whenever `s ≠ t` and
`¬ G s t` (diagonal terms are the per-node rewards). A *refinement* is a partition `c : S → C`
(the cells the informed self conditions on); it is *decision-flat* (`DecisionFlat G c`) if no
coupling edge crosses a cell. A *cellwise assembly* (`CellwiseAssembly c β U π`) is a policy
whose restriction to each cell `γ` is optimal for `U` when the rest of the policy is frozen at
the cell's prediction `β γ` (updateful across cells, updateless within cells).

* `cellwise_optimal_of_flat` (⟸, P): flat ⟹ every cellwise assembly is optimal for every `U`
  respecting `G`. T7(b) is the singleton-cell instance (`cellwise_id_iff_edtAssembly`,
  `respectsPairs_bot_iff_separable`).
* `exists_coupled_of_not_flat` (⟹, P by construction): not flat ⟹ some `U` respecting `G` (the
  mugging's matching-pay term on the crossing edge, a `−100` cost on the diagonal) has a
  cellwise assembly that is not optimal.
* `decisionFlat_iff` (C): the biconditional, stated once.

**Not T8's predicate.** Decision-flatness is a property of `(G, c)`, not of an optimum; the
note's fear that "decision-flat may be Idea A in disguise" does not materialize — Idea A is
`IsOptimal` of one assembly, this is a condition on the refinement that makes *every* assembly
optimal for *every* compatible `U`.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {S A C : Type} [Fintype S] [DecidableEq S]

/-- **`U` respects the coupling graph `G`**: `U` is a sum of pair terms `f s t (π s) (π t)` that
vanish on non-edges (diagonal terms — the per-node rewards — are always allowed).
Source: [[updateless-deference-ideate]] §5 Idea E (formalizer's rendering; trust-lab-2-017)
Kind: D
Fidelity: variant: the note defines nothing; pairwise (not clique) coupling, ATTRIBUTION-UNVETTED
Hyps: n/a -/
def RespectsPairs (G : S → S → Prop) (U : Policy S A → ℝ) : Prop :=
  ∃ f : S → S → A → A → ℝ, (∀ s t, s ≠ t → ¬ G s t → ∀ a b, f s t a b = 0) ∧
    ∀ π, U π = ∑ s, ∑ t, f s t (π s) (π t)

/-- **A decision-flat refinement**: no coupling edge crosses a cell of the partition `c`.
Source: [[updateless-deference-ideate]] §5 Idea E (formalizer's rendering; trust-lab-2-017)
Kind: D
Fidelity: variant: a property of `(G, c)`, not defined through optimality (no squeeze)
Hyps: n/a -/
def DecisionFlat (G : S → S → Prop) (c : S → C) : Prop := ∀ s t, s ≠ t → G s t → c s = c t

/-- The policy that follows `π` on the cell `γ` and `β` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def patch [DecidableEq C] (c : S → C) (γ : C) (π β : Policy S A) : Policy S A :=
  fun s => if c s = γ then π s else β s

/-- **A cellwise assembly**: on every cell `γ`, `π`'s restriction is optimal for `U` with the rest
of the policy frozen at the cell's prediction `β γ` — the updateful-across-cells,
updateless-within-cells prescription.
Source: [[updateless-deference-ideate]] §5 Idea E (formalizer's rendering; trust-lab-2-017)
Kind: D
Fidelity: variant
Hyps: n/a -/
def CellwiseAssembly [DecidableEq C] (c : S → C) (β : C → Policy S A) (U : Policy S A → ℝ)
    (π : Policy S A) : Prop :=
  ∀ γ π', U (patch c γ π' (β γ)) ≤ U (patch c γ π (β γ))

/-- The part of a pair-sum utility living inside the cell `γ`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def cellPart [DecidableEq C] (f : S → S → A → A → ℝ) (c : S → C) (γ : C) (π : Policy S A) : ℝ :=
  ∑ s, ∑ t, if c s = γ ∧ c t = γ then f s t (π s) (π t) else 0

section Flat

variable [Fintype C] [DecidableEq C]

/-- Supporting lemma: under flatness, a `G`-respecting utility is the sum of its cell parts (the
cross-cell pair terms vanish).
Source: none: infrastructure (T9(a))
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_cellPart {G : S → S → Prop} {c : S → C} (hflat : DecisionFlat G c)
    {f : S → S → A → A → ℝ} (hf : ∀ s t, s ≠ t → ¬ G s t → ∀ a b, f s t a b = 0)
    (π : Policy S A) :
    ∑ γ, cellPart f c γ π = ∑ s, ∑ t, f s t (π s) (π t) := by
  unfold cellPart
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (c s)]
  · by_cases hct : c t = c s
    · rw [if_pos ⟨rfl, hct⟩]
    · rw [if_neg (fun h => hct h.2)]
      by_cases hst : s = t
      · exact absurd (hst ▸ rfl) hct
      · by_cases hG : G s t
        · exact absurd (hflat s t hst hG).symm hct
        · exact (hf s t hst hG _ _).symm
  · intro γ _ hγ
    rw [if_neg (fun h => hγ h.1.symm)]
  · intro h
    exact absurd (mem_univ _) h

omit [DecidableEq S] [Fintype C] in
/-- Supporting lemma: the cell part depends on the policy only inside the cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cellPart_congr {f : S → S → A → A → ℝ} {c : S → C} {γ : C} {π π' : Policy S A}
    (h : ∀ s, c s = γ → π s = π' s) : cellPart f c γ π = cellPart f c γ π' := by
  unfold cellPart
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases hst : c s = γ ∧ c t = γ
  · rw [if_pos hst, if_pos hst, h s hst.1, h t hst.2]
  · rw [if_neg hst, if_neg hst]

omit [Fintype C] in
/-- Supporting lemma: the cell part of a patch is the cell part of the patched-in policy on its own
cell, and of the background elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cellPart_patch (f : S → S → A → A → ℝ) (c : S → C) (γ γ' : C) (π β : Policy S A) :
    cellPart f c γ' (patch c γ π β) = if γ' = γ then cellPart f c γ π else cellPart f c γ' β := by
  split_ifs with h
  · subst h
    exact cellPart_congr fun s hs => by simp [patch, hs]
  · exact cellPart_congr fun s hs => by simp [patch, hs, h]

/-- **T9(a) (⟸): on a decision-flat refinement, every cellwise assembly is optimal for every
utility respecting the coupling graph.** The utility splits as a sum of cell parts; cellwise
optimality with the background frozen is optimality of each cell part; sum.
Source: [[updateless-deference-ideate]] §5 Idea E | trust-lab-2-017 (T9(a))
Kind: P
Fidelity: variant: the formalizer's definitions (the note defines nothing)
Hyps: (a) all -/
theorem cellwise_optimal_of_flat {G : S → S → Prop} {c : S → C} (hflat : DecisionFlat G c)
    {U : Policy S A → ℝ} (hU : RespectsPairs G U) {β : C → Policy S A} {π : Policy S A}
    (hπ : CellwiseAssembly c β U π) : IsOptimal U π := by
  obtain ⟨f, hf, hUf⟩ := hU
  have hsplit : ∀ π', U π' = ∑ γ, cellPart f c γ π' := fun π' => by
    rw [hUf, sum_cellPart hflat hf]
  intro π'
  rw [hsplit, hsplit]
  refine Finset.sum_le_sum fun γ _ => ?_
  have h := hπ γ π'
  rw [hsplit, hsplit] at h
  simp only [cellPart_patch] at h
  rw [← Finset.add_sum_erase _ _ (mem_univ γ), ← Finset.add_sum_erase _ _ (mem_univ γ)] at h
  simp only [if_true] at h
  have hrest : ∑ x ∈ univ.erase γ, (if x = γ then cellPart f c γ π' else cellPart f c x (β γ)) =
      ∑ x ∈ univ.erase γ, (if x = γ then cellPart f c γ π else cellPart f c x (β γ)) :=
    Finset.sum_congr rfl fun x hx => by
      rw [if_neg (Finset.ne_of_mem_erase hx), if_neg (Finset.ne_of_mem_erase hx)]
  linarith

end Flat

/-! ### (⟹) by construction: a crossing edge carries the mugging -/

section NotFlat

variable [DecidableEq C] [DecidableEq A]

omit [DecidableEq A] in
/-- Supporting lemma: a pair-indicator double sum collapses to the pair.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_pair_ite (s t : S) (g : A → A → ℝ) (π : Policy S A) :
    ∑ s', ∑ t', (if s' = s ∧ t' = t then g (π s') (π t') else 0) = g (π s) (π t) := by
  rw [Finset.sum_comm]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The crossing-edge utility**: for the edge `(s, t)`, `U π = 10000·[π s = a₁ ∧ π t = a₁]
− 100·[π s = a₁]` — the mugging's matching-pay term on the edge and its cost on the diagonal.
Source: mandate T9(b) (the T7 matching-pay term on the crossing edge)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def edgeU (s t : S) (a₁ : A) (π : Policy S A) : ℝ :=
  (if π s = a₁ ∧ π t = a₁ then 10000 else 0) + (if π s = a₁ then -100 else 0)

/-- Supporting lemma: `edgeU` respects any graph containing the edge `(s, t)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem edgeU_respectsPairs {G : S → S → Prop} {s t : S} (hG : G s t) (a₁ : A) :
    RespectsPairs G (edgeU s t a₁) := by
  refine ⟨fun s' t' a b => (if s' = s ∧ t' = t then (if a = a₁ ∧ b = a₁ then 10000 else 0) else 0) +
    (if s' = s ∧ t' = s then (if a = a₁ then -100 else 0) else 0), ?_, ?_⟩
  · intro s' t' hne hnG a b
    dsimp only
    by_cases h1 : s' = s ∧ t' = t
    · exact absurd (h1.1 ▸ h1.2 ▸ hG) hnG
    · rw [if_neg h1]
      by_cases h2 : s' = s ∧ t' = s
      · exact absurd (h2.1.trans h2.2.symm) hne
      · rw [if_neg h2]; ring
  · intro π
    simp only [Finset.sum_add_distrib]
    unfold edgeU
    congr 1
    · exact (sum_pair_ite s t (fun a b => if a = a₁ ∧ b = a₁ then 10000 else 0) π).symm
    · exact (sum_pair_ite s s (fun a _ => if a = a₁ then -100 else 0) π).symm

/-- **T9(b) (⟹): a refinement that is not decision-flat has a utility respecting the graph with
a non-optimal cellwise assembly.** Put the mugging on the crossing edge `(s, t)`: the cell of `s`
optimizing with `t` frozen at `a₀` refuses (`−100` for paying), the cell of `t` is indifferent,
so `const a₀` is a cellwise assembly scoring `0`, while `const a₁` scores `9900`.
Source: [[updateless-deference-ideate]] §5 Idea E | trust-lab-2-017 (T9(b))
Kind: P
Fidelity: variant: the formalizer's definitions; existential in `U`, `β` and the assembly
Hyps: (a) all; `a₀ ≠ a₁` (two actions) -/
theorem exists_coupled_of_not_flat {G : S → S → Prop} {c : S → C} (hnf : ¬ DecisionFlat G c)
    {a₀ a₁ : A} (h01 : a₀ ≠ a₁) :
    ∃ U : Policy S A → ℝ, RespectsPairs G U ∧
      ∃ (β : C → Policy S A) (π : Policy S A), CellwiseAssembly c β U π ∧ ¬ IsOptimal U π := by
  simp only [DecisionFlat, not_forall] at hnf
  obtain ⟨s, t, hst, hG, hc⟩ := hnf
  refine ⟨edgeU s t a₁, edgeU_respectsPairs hG a₁, fun _ _ => a₀, fun _ => a₀, ?_, ?_⟩
  · intro γ π'
    have h0 : edgeU s t a₁ (patch c γ (fun _ => a₀) fun _ => a₀) = 0 := by
      simp [edgeU, patch, h01]
    rw [h0]
    unfold edgeU
    by_cases hs : c s = γ
    · have ht : ¬ c t = γ := fun h => hc (hs.trans h.symm)
      simp only [patch, ht, if_false, h01, and_false]
      split_ifs <;> norm_num
    · simp only [patch, hs, if_false, h01, false_and]
      norm_num
  · intro hopt
    have := hopt fun _ => a₁
    simp [edgeU, h01] at this
    norm_num at this

end NotFlat

/-- **T9, the biconditional**: a refinement is decision-flat iff every cellwise assembly is
optimal for every utility respecting the coupling graph (two actions available).
Source: [[updateless-deference-ideate]] §5 Idea E | trust-lab-2-017
Kind: C
Fidelity: variant: the formalizer's definitions (the note defines nothing)
Hyps: (a) all; `a₀ ≠ a₁` -/
theorem decisionFlat_iff [Fintype C] [DecidableEq C] [DecidableEq A] (G : S → S → Prop)
    (c : S → C) {a₀ a₁ : A} (h01 : a₀ ≠ a₁) :
    DecisionFlat G c ↔
      ∀ U : Policy S A → ℝ, RespectsPairs G U →
        ∀ (β : C → Policy S A) (π : Policy S A), CellwiseAssembly c β U π → IsOptimal U π := by
  constructor
  · intro hflat U hU β π hπ
    exact cellwise_optimal_of_flat hflat hU hπ
  · intro h
    by_contra hnf
    obtain ⟨U, hU, β, π, hπ, hnot⟩ := exists_coupled_of_not_flat hnf h01
    exact hnot (h U hU β π hπ)

/-! ### T7(b) is the singleton-cell instance -/

omit [Fintype S] in
/-- Supporting lemma: patching one point is `Function.update`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem patch_id (γ : S) (π β : Policy S A) :
    patch (id : S → S) γ π β = Function.update β γ (π γ) := by
  funext s
  simp only [patch, id, Function.update_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- **With singleton cells, a cellwise assembly is an EDT-argmax assembly through the decoupled
kernel with base `β`** (`c = id`): the two prescriptions coincide, so T7(b) is T9(a) at the
edgeless graph.
Source: mandate T9(a) ("T7(b) is the singleton-cell instance")
Kind: L
Fidelity: exact
Hyps: none -/
theorem cellwise_id_iff_edtAssembly (β : S → Policy S A) (U : Policy S A → ℝ) (π : Policy S A) :
    CellwiseAssembly (id : S → S) β U π ↔ EdtAssembly U (fun s a => Function.update (β s) s a) π := by
  unfold CellwiseAssembly EdtAssembly IsArgmax vNode
  simp only [patch_id]
  constructor
  · intro h s a
    have := h s (fun _ => a)
    simpa using this
  · intro h s π'
    exact h s (π' s)

/-- **The edgeless graph is respected exactly by the separable utilities**.
Source: mandate T9(a)
Kind: L
Fidelity: exact
Hyps: none -/
theorem respectsPairs_bot_iff_separable (U : Policy S A → ℝ) :
    RespectsPairs (fun _ _ => False) U ↔ Separable U := by
  constructor
  · rintro ⟨f, hf, hU⟩
    refine ⟨fun s a => f s s a a, fun π => ?_⟩
    rw [hU]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · intro t _ hts
      exact hf s t (Ne.symm hts) (fun h => h) _ _
    · intro h; exact absurd (mem_univ _) h
  · rintro ⟨u, hu⟩
    refine ⟨fun s t a _ => if s = t then u s a else 0, fun s t hst _ a b => by simp [hst], fun π => ?_⟩
    rw [hu]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp

/-! ### A flat refinement with an edge inside each cell (N+ for T9(a); repair round 1) -/

omit [DecidableEq S] in
/-- Supporting lemma: utilities respecting `G` are closed under addition.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem respectsPairs_add {G : S → S → Prop} {U U' : Policy S A → ℝ} (hU : RespectsPairs G U)
    (hU' : RespectsPairs G U') : RespectsPairs G (fun π => U π + U' π) := by
  obtain ⟨f, hf, hUf⟩ := hU
  obtain ⟨f', hf', hUf'⟩ := hU'
  refine ⟨fun s t a b => f s t a b + f' s t a b, fun s t hst hG a b => ?_, fun π => ?_⟩
  · dsimp only
    rw [hf s t hst hG, hf' s t hst hG, add_zero]
  · dsimp only
    rw [hUf π, hUf' π]
    simp only [Finset.sum_add_distrib]

section FlatWitness

variable [DecidableEq A]

omit [Fintype S] [DecidableEq S] in
/-- Supporting lemma: the crossing-edge utility never exceeds `9900`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem edgeU_le (s t : S) (a₁ : A) (π : Policy S A) : edgeU s t a₁ π ≤ 9900 := by
  unfold edgeU
  by_cases h1 : π s = a₁
  · by_cases h2 : π t = a₁
    · rw [if_pos ⟨h1, h2⟩, if_pos h1]; norm_num
    · rw [if_neg (fun h => h2 h.2), if_pos h1]; norm_num
  · rw [if_neg (fun h => h1 h.1), if_neg h1]; norm_num

omit [Fintype S] [DecidableEq S] in
/-- Supporting lemma: the crossing-edge utility attains `9900` at `const a₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem edgeU_const (s t : S) (a₁ : A) : edgeU s t a₁ (fun _ => a₁) = 9900 := by
  unfold edgeU
  rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
  norm_num

/-- The coupling graph on four nodes with exactly the two edges `(0, 1)` and `(2, 3)`.
Source: audit r1 N2/N6 (T9(a) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def G4 (s t : Fin 4) : Prop := (s = 0 ∧ t = 1) ∨ (s = 2 ∧ t = 3)

instance : DecidableRel G4 := fun s t => by unfold G4; infer_instance

/-- The two-cell refinement `{0, 1} | {2, 3}` of four nodes.
Source: audit r1 N2/N6 (T9(a) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def c4 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- Two muggings, one inside each cell: `U4 = edgeU 0 1 1 + edgeU 2 3 1` on `Fin 4 → Fin 2`.
Source: audit r1 N2/N6 (T9(a) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U4 (π : Policy (Fin 4) (Fin 2)) : ℝ := edgeU 0 1 1 π + edgeU 2 3 1 π

/-- **T9(a), N+ witness with an edge inside each cell**: the refinement `{0,1} | {2,3}` is
decision-flat for the graph `{(0,1), (2,3)}`; `U4` (a mugging on each edge) respects the graph and
is **not** separable; the within-cell coupling is real (`(0,1)` is an edge inside a cell); the
cellwise assembly `const pay` for the background `const pay` is a `CellwiseAssembly` and is optimal
(`19800`) — the theorem's conclusion with content. Contrast on the same `U4`: the singleton
refinement `id` is *not* flat (the edges cross its cells), and its cellwise assembly `const refuse`
(= the EDT assembly through the kernel decoupled at `const refuse`, `cellwise_id_iff_edtAssembly`)
scores `0` and is not optimal. So "updateless within the cells that contain the coupling, updateful
across cells" is what the flat refinement buys, and the edgeless/singleton instance was not it.
Source: [[updateless-deference-ideate]] §5 Idea E | trust-lab-2-017 (T9(a)) | audit r1 fidelity N2, adversarial N6
Kind: N+
Fidelity: n/a (non-separable `U4`, an edge inside a cell, two cells, the within-cell coupling decides the assembly)
Hyps: none -/
theorem cellwise_flat_witness :
    DecisionFlat G4 c4 ∧ RespectsPairs G4 U4 ∧ CrossSituationDependence U4 ∧
      (G4 0 1 ∧ c4 0 = c4 1) ∧
      CellwiseAssembly c4 (fun _ _ => 1) U4 (fun _ => 1) ∧ IsOptimal U4 (fun _ => 1) ∧
      ¬ DecisionFlat G4 (id : Fin 4 → Fin 4) ∧
      CellwiseAssembly (id : Fin 4 → Fin 4) (fun _ _ => 0) U4 (fun _ => 0) ∧
      ¬ IsOptimal U4 (fun _ => 0) := by
  have hU1 : U4 (fun _ => 1) = 19800 := by
    unfold U4; rw [edgeU_const, edgeU_const]; norm_num
  refine ⟨?_, ?_, ?_, ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ∀ s t, s ≠ t → G4 s t → c4 s = c4 t
    decide
  · exact respectsPairs_add
      (edgeU_respectsPairs (G := G4) (s := 0) (t := 1) (by exact Or.inl ⟨rfl, rfl⟩) 1)
      (edgeU_respectsPairs (G := G4) (s := 2) (t := 3) (by exact Or.inr ⟨rfl, rfl⟩) 1)
  · rintro ⟨u, hu⟩
    have h1 := hu ![1, 1, 0, 0]
    have h2 := hu ![1, 0, 0, 0]
    have h3 := hu ![0, 1, 0, 0]
    have h4 := hu ![0, 0, 0, 0]
    simp [U4, edgeU, Fin.sum_univ_four] at h1 h2 h3 h4
    linarith
  · intro γ π'
    have hc : patch c4 γ (fun _ => 1) (fun _ => (1 : Fin 2)) = fun _ => 1 := by
      funext s; simp [patch]
    rw [hc, hU1]
    unfold U4
    linarith [edgeU_le 0 1 1 (patch c4 γ π' fun _ => 1), edgeU_le 2 3 1 (patch c4 γ π' fun _ => 1)]
  · intro π
    rw [hU1]
    unfold U4
    linarith [edgeU_le 0 1 1 π, edgeU_le 2 3 1 π]
  · intro h
    have := h 0 1 (by decide) (Or.inl ⟨rfl, rfl⟩)
    exact absurd this (by decide)
  · intro γ π'
    have hc : patch (id : Fin 4 → Fin 4) γ (fun _ => 0) (fun _ => (0 : Fin 2)) = fun _ => 0 := by
      funext s; simp [patch]
    rw [hc, patch_id]
    obtain ⟨a, ha⟩ : ∃ a, π' γ = a := ⟨_, rfl⟩
    rw [ha]
    fin_cases γ <;> fin_cases a <;>
    · simp [U4, edgeU, Function.update] <;> norm_num
  · intro h
    have := h (fun _ => 1)
    rw [hU1] at this
    simp [U4, edgeU] at this
    norm_num at this

end FlatWitness

end

end Cleanroom.Udt.UdtEndorsePolicy
