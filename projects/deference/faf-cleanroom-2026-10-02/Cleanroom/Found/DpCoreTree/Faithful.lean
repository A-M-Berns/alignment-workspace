import Cleanroom.Found.DpCoreTree.Agreement

/-!
# The disposition coordinate is law-faithful when `#_d ≤ 1`

T11 of [[dp-core-tree-mandate]] (dp-cf-2-004, FA-4). Run-level event `drew d a` (some `d`-node
on the path took the `a`-edge). **Theorem** (`disposition_faithful`): if every path meets `d` at
most once, then for every set `S` of leaves
`μ_{B,C}(S ∩ drew d a) · μ_{B,C[d↦a]}(occ d) = μ_{B,C[d↦a]}(S ∩ occ d) · μ_{B,C}(drew d a)` —
conditioning on the recorded draw *is* the deviation restricted to `occ(d)`. Stated on leaves
(no algebra enrichment; R1 is `dp-fairness-reloc`'s). The identity needs no `C(d)(a) > 0`
hypothesis (both sides vanish otherwise), so the mandate's positivity hypothesis is dropped:
`stronger`.

The proof is at the leaf level: with one `d`-draw on the path, `μ_{B,C}(ℓ) = C(d)(a) ·
μ_{B,C[d↦a]}(ℓ)` when that draw is `a` (`leafLaw_eq_mul_deviatePure_of_drew`), and
`μ_{B,C[d↦a]}(ℓ) = 0` when it is another action (`leafLaw_deviatePure_eq_zero_of_other`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]

namespace Tree

/-! ### Products over a draw list with a single draw at `d` -/

/-- Two procedures agreeing off `d` give the same draw product on a list with no draw at `d`.
Source: none: infrastructure
Kind: L -/
theorem prod_draws_congr_off {C C' : Proc ι acts K} {d : ι} (h : ∀ d', d' ≠ d → C d' = C' d') :
    (L : List (Σ d : ι, acts d)) → (∀ x ∈ L, x.1 ≠ d) →
      (L.map fun x => (C x.1).w x.2).prod = (L.map fun x => (C' x.1).w x.2).prod
  | [], _ => rfl
  | x :: L, hL => by
      simp only [List.map_cons, List.prod_cons]
      rw [h x.1 (hL x List.mem_cons_self),
        prod_draws_congr_off h L fun y hy => hL y (List.mem_cons_of_mem _ hy)]

/-- On a list with exactly one draw at `d`, namely `⟨d, a⟩`, the draw product under `C` is
`C(d)(a)` times the draw product under `C[d↦a]`.
Source: `faithful.md` FA-4 ("one consultation per run and Definition 6's path-independent
draw, so conditioning on the recorded draw is the deviation")
Kind: L -/
theorem prod_draws_eq_mul_deviatePure (C : Proc ι acts K) (d : ι) (a : acts d) :
    (L : List (Σ d : ι, acts d)) → (⟨d, a⟩ : Σ d, acts d) ∈ L →
      (L.map Sigma.fst).count d ≤ 1 →
      (L.map fun x => (C x.1).w x.2).prod =
        (C d).w a * (L.map fun x => ((C.deviatePure d a) x.1).w x.2).prod
  | [], h, _ => absurd h List.not_mem_nil
  | x :: L, hmem, hc => by
      simp only [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · -- head is the draw at `d`; no other draw at `d` in the tail
        simp only [List.map_cons, List.count_cons_self] at hc
        have hno : ∀ y ∈ L, y.1 ≠ d := by
          intro y hy hyd
          have : d ∈ L.map Sigma.fst := List.mem_map.mpr ⟨y, hy, hyd⟩
          have := List.count_pos_iff.mpr this
          omega
        rw [prod_draws_congr_off (C := C) (C' := C.deviatePure d a) (d := d)
          (fun d' hd' => (Proc.deviate_ne C _ hd').symm) L hno]
        simp only [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w, if_true, one_mul]
      · -- head is not the draw at `d`: then its point is not `d`
        have hxd : x.1 ≠ d := by
          intro hxd
          have h1 : d ∈ L.map Sigma.fst := List.mem_map.mpr ⟨⟨d, a⟩, hmem', rfl⟩
          have h2 := List.count_pos_iff.mpr h1
          simp only [List.map_cons, List.count_cons, hxd, beq_self_eq_true, if_true] at hc
          omega
        rw [prod_draws_eq_mul_deviatePure C d a L hmem' (by
          simpa [List.count_cons, hxd, Ne.symm hxd] using hc)]
        simp only [Proc.deviatePure, Proc.deviate_ne C _ hxd]
        ring

/-- If some draw at `d` on the list is not `a`, the draw product under `C[d↦a]` vanishes.
Source: `faithful.md` FA-4
Kind: L -/
theorem prod_draws_deviatePure_eq_zero (C : Proc ι acts K) (d : ι) (a b : acts d) (hab : b ≠ a)
    (L : List (Σ d : ι, acts d)) (h : (⟨d, b⟩ : Σ d, acts d) ∈ L) :
    (L.map fun x => ((C.deviatePure d a) x.1).w x.2).prod = 0 := by
  apply List.prod_eq_zero
  refine List.mem_map.mpr ⟨⟨d, b⟩, h, ?_⟩
  simp [Proc.deviatePure, hab]

/-! ### Leaf-level identities -/

/-- On a leaf whose single `d`-draw is `a`: `μ_{B,C}(ℓ) = C(d)(a) · μ_{B,C[d↦a]}(ℓ)`.
Source: `faithful.md` FA-4
Kind: P -/
theorem leafLaw_eq_mul_deviatePure_of_drew (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a : acts d) (ℓ : B.Leaves) (hmem : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ)
    (hc : count d B ℓ ≤ 1) :
    leafLaw C B ℓ = (C d).w a * leafLaw (C.deviatePure d a) B ℓ := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight, leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight
  rw [count_eq_draws_count] at hc
  rw [prod_draws_eq_mul_deviatePure C d a _ hmem hc]
  ring

/-- On a leaf with a `d`-draw other than `a`: `μ_{B,C[d↦a]}(ℓ) = 0`.
Source: `faithful.md` FA-4
Kind: L -/
theorem leafLaw_deviatePure_eq_zero_of_other (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (a b : acts d) (hab : b ≠ a) (ℓ : B.Leaves) (h : (⟨d, b⟩ : Σ d, acts d) ∈ draws B ℓ) :
    leafLaw (C.deviatePure d a) B ℓ = 0 := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight
  rw [prod_draws_deviatePure_eq_zero C d a b hab _ h, mul_zero]

/-- On a leaf not meeting `d`, a deviation at `d` does not change the mass.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_deviate_of_count_eq_zero (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
    (m : FinDistr K (acts d)) (ℓ : B.Leaves) (h : count d B ℓ = 0) :
    leafLaw (C.deviate d m) B ℓ = leafLaw C B ℓ := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight, leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight
  congr 1
  apply prod_draws_congr_off (fun d' hd' => Proc.deviate_ne C m hd')
  intro x hx hxd
  have := count_pos_of_mem_draws (d := d) (a := hxd ▸ x.2) (B := B) (ℓ := ℓ) (by
    obtain ⟨d'', b⟩ := x
    simp only at hxd
    subst hxd
    exact hx)
  omega

/-- A leaf meeting `d` exactly once whose draw at `d` is not `a` carries a draw `⟨d, b⟩` with
`b ≠ a`.
Source: none: infrastructure
Kind: L -/
theorem exists_other_draw_of_not_drew (B : Tree Ω ι acts K) (d : ι) (a : acts d) (ℓ : B.Leaves)
    (hpos : 0 < count d B ℓ) (hnot : (⟨d, a⟩ : Σ d, acts d) ∉ draws B ℓ) :
    ∃ b, b ≠ a ∧ (⟨d, b⟩ : Σ d, acts d) ∈ draws B ℓ := by
  rw [count_eq_draws_count] at hpos
  obtain ⟨x, hx, hxd⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
  obtain ⟨d', b⟩ := x
  simp only at hxd
  subst hxd
  refine ⟨b, fun hba => hnot (hba ▸ hx), hx⟩

/-! ### The theorem -/

/-- Membership in `drew`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem mem_drew (d : ι) (a : acts d) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    ℓ ∈ drew d a B ↔ (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ := by
  simp [drew]

/-- `drew d a ⊆ occ d`.
Source: none: infrastructure
Kind: L -/
theorem drew_subset_occ (d : ι) (a : acts d) (B : Tree Ω ι acts K) : drew d a B ⊆ occ d B := by
  intro ℓ h
  rw [mem_drew] at h
  rw [mem_occ]
  exact count_pos_of_mem_draws h

/-- `μ_{B,C}(S ∩ drew) = C(d)(a) · μ_{B,C[d↦a]}(S ∩ drew)` when `#_d ≤ 1`.
Source: `faithful.md` FA-4
Kind: L -/
theorem mass_inter_drew (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d)
    (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves) :
    mass C B (S ∩ drew d a B) = (C d).w a * mass (C.deviatePure d a) B (S ∩ drew d a B) := by
  unfold mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_inter, mem_drew] at hℓ
  exact leafLaw_eq_mul_deviatePure_of_drew C B d a ℓ hℓ.2 (hfair ℓ)

/-- `μ_{B,C[d↦a]}(S ∩ occ) = μ_{B,C[d↦a]}(S ∩ drew)` when `#_d ≤ 1`: the deviated law lives on
the `a`-runs.
Source: `faithful.md` FA-4
Kind: L -/
theorem mass_deviatePure_inter_occ (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d)
    (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves) :
    mass (C.deviatePure d a) B (S ∩ occ d B) = mass (C.deviatePure d a) B (S ∩ drew d a B) := by
  unfold mass
  symm
  apply Finset.sum_subset
  · exact Finset.inter_subset_inter_left (drew_subset_occ d a B)
  · intro ℓ hℓ hℓ'
    rw [Finset.mem_inter, mem_occ] at hℓ
    rw [Finset.mem_inter, mem_drew, not_and] at hℓ'
    obtain ⟨b, hba, hb⟩ := exists_other_draw_of_not_drew B d a ℓ hℓ.2 (hℓ' hℓ.1)
    exact leafLaw_deviatePure_eq_zero_of_other C B d a b hba ℓ hb

/-- **The disposition coordinate is law-faithful when `#_d ≤ 1`**:
`μ_{B,C}(S ∩ drew d a) · μ_{B,C[d↦a]}(occ d) = μ_{B,C[d↦a]}(S ∩ occ d) · μ_{B,C}(drew d a)`
for every `S ⊆ Leaves` — conditioning on the recorded draw is the deviation restricted to
`occ(d)`.
Source: `cf-workflow/phase2-notes/repair/faithful.md` FA-4 (dp-cf-2-004); mandate T11
Kind: P
Fidelity: stronger (no `C(d)(a) > 0` hypothesis: the identity holds with both sides `0`)
Hyps: none -/
theorem disposition_faithful (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d)
    (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves) :
    mass C B (S ∩ drew d a B) * mass (C.deviatePure d a) B (occ d B) =
      mass (C.deviatePure d a) B (S ∩ occ d B) * mass C B (drew d a B) := by
  have h1 := mass_inter_drew C B d a hfair S
  have h2 := mass_deviatePure_inter_occ C B d a hfair S
  have h3 := mass_inter_drew C B d a hfair Finset.univ
  have h4 := mass_deviatePure_inter_occ C B d a hfair Finset.univ
  simp only [Finset.univ_inter] at h3 h4
  rw [h1, h2, h3, h4]
  ring

/-- Under nesting the identity can fail: this is recorded as a `stretch` N− in the report
(FA-8's concave `k = 2` mugging), not formalised here.
Source: mandate T11 ("Trap: under nesting it fails")
Kind: L -/
theorem disposition_faithful_of_almostFair (C : Proc ι acts K) {B : Tree Ω ι acts K}
    (h : AlmostFair B) (d : ι) (a : acts d) (S : Finset B.Leaves) :
    mass C B (S ∩ drew d a B) * mass (C.deviatePure d a) B (occ d B) =
      mass (C.deviatePure d a) B (S ∩ occ d B) * mass C B (drew d a B) :=
  disposition_faithful C B d a (h d) S

end Tree

end Cleanroom.Found.DpCoreTree
