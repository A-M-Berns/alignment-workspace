import Cleanroom.Decision.DpFairnessReloc.RelationsChain

/-!
# E4 `recombination`: `≈_tr` holds, `≃_Δ` fails (repair round 1)

Package `dp-fairness-reloc`, file 13. The separating pair of `equiv.md` EQ-2/EQ-3 that shows
EQ-3's inner-fairness hypothesis is load-bearing (Dead 5, Amendment (1) as written): two fair
coins over `d'`-nodes with actions `a, b` and four distinct leaves `L₀..L₃` (worlds `Fin 4`),
`T₁ = ½ D_A + ½ D_B` with `D_A : a → L₀, b → L₂`, `D_B : a → L₁, b → L₃`, and
`T₂ = ½ D_C + ½ D_D` with `D_C : a → L₀, b → L₃`, `D_D : a → L₁, b → L₂`. The traces agree for
every procedure (`½[C(a)L₀ + C(b)L₂] + ½[C(a)L₁ + C(b)L₃] = ½[C(a)L₀ + C(b)L₃] + ½[C(a)L₁ +
C(b)L₂]`, `e4_trEq`) but no coupling of the flattenings exists: `D_A` would have to be `≃_Δ` to
`D_C` (forcing `L₂ = L₃`) or to `D_D` (forcing `L₀ = L₁`) (`e4_not_bisimΔ`). The inner
`d'`-fiber `{D_A, D_B}` is unfair in every sense, which is EQ-3's point.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

section leafinj

/-- The trace distribution of a leaf is the point mass at its empty trace.
Source: none: infrastructure
Kind: L -/
theorem traceDist_leaf [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (C : Proc ι acts K) (ω : Ω) (r : K) :
    traceDist C (.leaf ω r : Tree Ω ι acts K) = Finsupp.single ([], (ω, r)) 1 := by
  unfold traceDist
  have key : ∀ f : (Tree.leaf ω r : Tree Ω ι acts K).Leaves → (List (Σ d : ι, acts d) × (Ω × K) →₀ K),
      ∑ ℓ, f ℓ = f () := by
    intro f
    rw [Finset.sum_eq_single (show (Tree.leaf ω r : Tree Ω ι acts K).Leaves from ())]
    · intro b _ hb
      exact absurd rfl hb
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine (key _).trans ?_
  first
  | rfl
  | simp

/-- `≃_Δ`-related leaves are equal.
Source: none: infrastructure
Kind: L -/
theorem BisimΔ.leaf_inj {ω ω' : Ω} {r r' : K}
    (h : BisimΔ (.leaf ω r : Tree Ω ι acts K) (.leaf ω' r')) : ω = ω' ∧ r = r' := by
  classical
  obtain ⟨W, hW, hleaf, -, -, -⟩ := h.exists_flatCoupling
  have h1 := hW.sum_right (.leaf ω r)
  rw [flatDist_leaf, flatDist_leaf, Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same] at h1
  have := hleaf (.leaf ω r) (.leaf ω' r') (by rw [h1]; exact one_ne_zero) ω r rfl
  exact ⟨(Tree.leaf.inj this).1.symm, (Tree.leaf.inj this).2.symm⟩

end leafinj

/-! ### E4 -/

/-- A `d'`-node with two leaves `x`, `y` (payoff `0`).
Source: `equiv.md` EQ-2 (E4 `recombination`, the four `D`-nodes)
Kind: D -/
def e4Node (x y : Fin 4) : Tree (Fin 4) Unit (fun _ => Act2) ℚ :=
  .decision () fun
    | .a => .leaf x 0
    | .b => .leaf y 0

/-- `T₁ = ½ D_A + ½ D_B`. Source: `equiv.md` EQ-2 (E4). Kind: D -/
def e4T₁ : Tree (Fin 4) Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases (e4Node 0 2) (fun _ => e4Node 1 3) i

/-- `T₂ = ½ D_C + ½ D_D`. Source: `equiv.md` EQ-2 (E4). Kind: D -/
def e4T₂ : Tree (Fin 4) Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => Fin.cases (e4Node 0 3) (fun _ => e4Node 1 2) i

theorem e4Node_inj {x y x' y' : Fin 4} (h : e4Node x y = e4Node x' y') : x = x' ∧ y = y' := by
  unfold e4Node at h
  have hc := (Tree.decision.inj h).2
  rw [heq_iff_eq] at hc
  have ha := congrFun hc .a
  have hb := congrFun hc .b
  simp only at ha hb
  exact ⟨(Tree.leaf.inj ha).1, (Tree.leaf.inj hb).1⟩

theorem traceDist_e4Node (C : Proc Unit (fun _ => Act2) ℚ) (x y : Fin 4) :
    traceDist C (e4Node x y) =
      (C ()).w .a • Finsupp.single ([⟨(), Act2.a⟩], (x, (0 : ℚ))) (1 : ℚ) +
        (C ()).w .b • Finsupp.single ([⟨(), Act2.b⟩], (y, (0 : ℚ))) (1 : ℚ) := by
  unfold e4Node
  rw [traceDist_decision, Act2.sum_univ]
  show (C ()).w .a • (traceDist C (.leaf x 0)).sum (fun τ v =>
      Finsupp.single ((⟨(), Act2.a⟩ : Σ _ : Unit, Act2) :: τ.1, τ.2) v) +
    (C ()).w .b • (traceDist C (.leaf y 0)).sum (fun τ v =>
      Finsupp.single ((⟨(), Act2.b⟩ : Σ _ : Unit, Act2) :: τ.1, τ.2) v) = _
  rw [traceDist_leaf, traceDist_leaf, Finsupp.sum_single_index (Finsupp.single_zero _),
    Finsupp.sum_single_index (Finsupp.single_zero _)]

/-- **E4: `≈_tr` holds** — the two recombined coins have the same trace distribution under every
procedure.
Source: `equiv.md` EQ-2 (E4 "`bisΔ:n tr:Y`"); threads `equiv.md` ("Traces of the two `a`-children
agree for every `C`")
Kind: N+ -/
theorem e4_trEq : TrEq e4T₁ e4T₂ := by
  intro C
  unfold e4T₁ e4T₂
  rw [traceDist_chance, traceDist_chance, Fin.sum_univ_two, Fin.sum_univ_two]
  show FinDistr.fair.w 0 • traceDist C (e4Node 0 2) + FinDistr.fair.w 1 • traceDist C (e4Node 1 3) =
    FinDistr.fair.w 0 • traceDist C (e4Node 0 3) + FinDistr.fair.w 1 • traceDist C (e4Node 1 2)
  rw [show FinDistr.fair.w 0 = 1/2 from rfl, show FinDistr.fair.w 1 = 1 - 1/2 from rfl,
    traceDist_e4Node, traceDist_e4Node, traceDist_e4Node, traceDist_e4Node]
  norm_num
  module

theorem flatDist_e4Node (x y : Fin 4) : flatDist (e4Node x y) = Finsupp.single (e4Node x y) 1 := rfl

/-- The flattening of `T₁` puts mass `½` on `D_A`. Source: none: infrastructure. Kind: L -/
theorem flatDist_e4T₁_A : flatDist e4T₁ (e4Node 0 2) = 1/2 := by
  classical
  unfold e4T₁
  rw [flatDist_chance, Fin.sum_univ_two]
  show (FinDistr.fair.w 0 • flatDist (e4Node 0 2) + FinDistr.fair.w 1 • flatDist (e4Node 1 3))
    (e4Node 0 2) = 1/2
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, flatDist_e4Node, flatDist_e4Node,
    Finsupp.single_eq_same, Finsupp.single_apply, if_neg, show FinDistr.fair.w 0 = 1/2 from rfl]
  · simp
  · intro h
    have := (e4Node_inj h).1
    exact absurd this (by decide)

/-- A non-chance descendant of `T₂` is `D_C` or `D_D`. Source: none: infrastructure. Kind: L -/
theorem mem_support_flatDist_e4T₂ {S : Tree (Fin 4) Unit (fun _ => Act2) ℚ}
    (hS : S ∈ (flatDist e4T₂).support) : S = e4Node 0 3 ∨ S = e4Node 1 2 := by
  classical
  rw [Finsupp.mem_support_iff] at hS
  unfold e4T₂ at hS
  rw [flatDist_chance, Fin.sum_univ_two] at hS
  change (FinDistr.fair.w 0 • flatDist (e4Node 0 3) + FinDistr.fair.w 1 • flatDist (e4Node 1 2)) S
    ≠ 0 at hS
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, flatDist_e4Node, flatDist_e4Node,
    Finsupp.single_apply, Finsupp.single_apply] at hS
  by_cases h1 : e4Node 0 3 = S
  · exact Or.inl h1.symm
  by_cases h2 : e4Node 1 2 = S
  · exact Or.inr h2.symm
  rw [if_neg h1, if_neg h2] at hS
  simp at hS

/-- **E4: `≃_Δ` fails** — no coupling of the flattenings: `D_A` (mass `½` in `T₁`) would have to
be `≃_Δ` to `D_C` (forcing the leaves `L₂ = L₃`) or to `D_D` (forcing `L₀ = L₁`).
Source: `equiv.md` EQ-2 (E4 "`bisΔ:n tr:Y`"), EQ-3 ("Without stratification E4 separates";
Dead 5)
Kind: N+ -/
theorem e4_not_bisimΔ : ¬ BisimΔ e4T₁ e4T₂ := by
  intro h
  obtain ⟨W, hW, -, -, -, hdec⟩ := h.exists_flatCoupling
  have hsum := hW.sum_right (e4Node 0 2)
  rw [flatDist_e4T₁_A] at hsum
  have hne : ∑ S' ∈ (flatDist e4T₂).support, W (e4Node 0 2) S' ≠ 0 := by
    rw [hsum]; norm_num
  obtain ⟨S', hS', hW'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rcases mem_support_flatDist_e4T₂ hS' with rfl | rfl
  · -- `D_A` vs `D_C`: the `b`-leaves `L₂`, `L₃` would be `≃_Δ`
    have := hdec (e4Node 0 2) (e4Node 0 3) hW' () _ _ rfl rfl Act2.b
    have h2 := (BisimΔ.leaf_inj this).1
    exact absurd h2 (by decide)
  · -- `D_A` vs `D_D`: the `a`-leaves `L₀`, `L₁` would be `≃_Δ`
    have := hdec (e4Node 0 2) (e4Node 1 2) hW' () _ _ rfl rfl Act2.a
    have h2 := (BisimΔ.leaf_inj this).1
    exact absurd h2 (by decide)

/-- **E4 packaged**: the recombination pair is `≈_tr` and not `≃_Δ` — the strictness witness of
`≃_Δ ⊆ ≈_tr`, and the trap of EQ-3 (its inner-fairness hypothesis is load-bearing).
Source: `equiv.md` EQ-2 (E4), EQ-3 (Dead 5)
Kind: N+ -/
theorem e4_separates : TrEq e4T₁ e4T₂ ∧ ¬ BisimΔ e4T₁ e4T₂ := ⟨e4_trEq, e4_not_bisimΔ⟩

end Cleanroom.Decision.DpFairnessReloc
