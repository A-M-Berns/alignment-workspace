import Cleanroom.Decision.DpFairnessReloc.Fair

/-!
# Relocation: definitions of record (`resolve`, `relocRoot`, the leaf map `π`, `lift`)

Package `dp-fairness-reloc`, file 4. Joint product relocation of a set `U` of points to the
**root site** (`fair-repair.md` Exit E2 / Definition R2; `seeds.md` SE-5):

* **Worlds** of the output: `Ω × ((d : ↥U) → acts d)` — the original world stamped with the
  `pol_d` coordinates of every relocated point (R1's algebra enrichment `𝓔^U`). The coordinates
  are *fresh by construction* (a new product factor, never one of `Ω`'s coordinates), which is
  what the cf toolkit's `pol_<point>` collision (dp-cf-016's flag) lacked.
* **Points** of the output: `ι ⊕ Unit`; `inl d` is the survivor `d`, `inr ()` is the new root
  point `d̂` with action set `∏_{d ∈ U} A_d` (`actsR`).
* **`resolve σ B`**: every `U`-node of `B` is replaced by its `σ d`-child, every survivor node is
  re-tagged `inl`, every leaf world is stamped with `σ`. It is built *together with its canonical
  leaf map* `leafMapW` (a leaf of the resolved tree ↦ the `B`-leaf it came from), as one
  structural recursion returning a pair — this avoids every cast.
* **`relocRoot U B := decision (inr ()) (fun σ => resolve σ B)`**, the root-site output, with
  `leafMap : (relocRoot U B).Leaves → B.Leaves`.
* **`lift C`**: the lifted procedure, `lift C (inr ()) := ⨂_{d ∈ U} C d` (the *product* law,
  `FinDistr.pi`; never a correlated one) and `lift C (inl d) := C d`.

**E4 (dp-cf-2-072) disclosed**: `pol_d = a` is an event of the *enriched* algebra
`Ω × ∏_U A_d` only; on `Ω` there is no such event, so everything below that reads `pol`
(records at `d̂`, `ρ_d(a) := {pol_d = a}`) is derived *conditional on the enrichment*. Here the
enrichment is the definition, so the grade is (a), but the typing fact is real: the relocated
actions do not exist as events of `Ω`.

Theorems here: the leaf invariants of `leafMapW` (world up to the stamp, payoff, chance weight,
`#_d`), and the **resolution lemma** (`resolve_seed_sum`): the memoised walk (Definition 6′) on
`resolve σ B` with the seeds of `U` pre-filled to `σ` pushes forward, along the leaf map, to the
memoised walk on `B` with the same seeds — the real content of SE-5(1). The pushforward
theorems FR-7(a) and SE-5(1) themselves are in `RelocateThms.lean`.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### The relocated point, action and world types -/

/-- Actions of the relocated tree: a survivor `inl d` keeps `A_d`; the new root point `inr ()`
chooses a joint policy `∏_{d ∈ U} A_d`.
Source: `fair-repair.md` Exit E2 ("one node `q̂` … with action set `∏_{d ∈ U} A_d`")
Kind: D -/
@[reducible] def actsR (acts : ι → Type) (U : Finset ι) : ι ⊕ Unit → Type
  | .inl d => acts d
  | .inr _ => (d : ↥U) → acts d

section instances

variable (U : Finset ι)

instance actsR.fintype [DecidableEq ι] [∀ d, Fintype (acts d)] :
    ∀ p, Fintype (actsR acts U p)
  | .inl d => inferInstanceAs (Fintype (acts d))
  | .inr _ => inferInstanceAs (Fintype ((d : ↥U) → acts d))

instance actsR.decEq [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] :
    ∀ p, DecidableEq (actsR acts U p)
  | .inl d => inferInstanceAs (DecidableEq (acts d))
  | .inr _ => inferInstanceAs (DecidableEq ((d : ↥U) → acts d))

instance actsR.nonempty [∀ d, Nonempty (acts d)] : ∀ p, Nonempty (actsR acts U p)
  | .inl d => inferInstanceAs (Nonempty (acts d))
  | .inr _ => inferInstanceAs (Nonempty ((d : ↥U) → acts d))

end instances

/-- The relocated world type `Ω × ∏_{d ∈ U} A_d` (R1's enrichment by the `pol` coordinates).
Source: `fair-repair.md` Definition R1
Kind: D -/
abbrev RW (Ω : Type) (acts : ι → Type) (U : Finset ι) : Type := Ω × ((d : ↥U) → acts d)

/-! ### Product distributions and the lifted procedure -/

section lift

variable [DecidableEq ι] [∀ d, Fintype (acts d)] (U : Finset ι)

/-- The product distribution `⨂_{d ∈ U} p d` on `∏_{d ∈ U} A_d`.
Source: `fair-repair.md` FR-6 ("`C̃(d̂) := ⨂_{d ∈ U} C(d)` (product law)")
Kind: D -/
def FinDistr.pi (p : (d : ↥U) → FinDistr K (acts d)) : FinDistr K ((d : ↥U) → acts d) where
  w σ := ∏ d, (p d).w (σ d)
  nonneg σ := Finset.prod_nonneg fun d _ => (p d).nonneg _
  sum_one := by
    rw [← Fintype.prod_sum]
    simp [FinDistr.sum_one]

@[simp] theorem FinDistr.pi_w (p : (d : ↥U) → FinDistr K (acts d)) (σ : (d : ↥U) → acts d) :
    (FinDistr.pi U p).w σ = ∏ d, (p d).w (σ d) := rfl

/-- **The lifted procedure** `lift C`: `C d` at every survivor, the product `⨂_{d ∈ U} C d` at
the root point.
Source: `fair-repair.md` FR-6 (`C̃`); `seeds.md` SE-5 (`C̃(d̂) := ⨂_{d ∈ U} C(d)`)
Kind: D
Fidelity: exact (product law; the correlated extension is FR-9(iv)'s and not this) -/
def lift (C : Proc ι acts K) : Proc (ι ⊕ Unit) (actsR acts U) K
  | .inl d => C d
  | .inr _ => FinDistr.pi U fun d => C d

@[simp] theorem lift_inl (C : Proc ι acts K) (d : ι) : lift U C (.inl d) = C d := rfl

@[simp] theorem lift_inr (C : Proc ι acts K) : lift U C (.inr ()) = FinDistr.pi U fun d => C d :=
  rfl

/-- The assignment lifted to the relocated points: the tuple at the root, the original elsewhere.
Source: `fair-repair.md` FR-7(a)
Kind: D -/
def liftFun (π : (d : ι) → acts d) : (p : ι ⊕ Unit) → actsR acts U p
  | .inl d => π d
  | .inr _ => fun d => π d

/-- The product of point masses is the point mass of the tuple, so `lift (ofFun π) = ofFun
(liftFun π)`: a deterministic procedure lifts to a deterministic one.
Source: `fair-repair.md` FR-7(a) ("a deterministic `C` answers every occurrence of `d`
identically anyway, which is what resolution does")
Kind: L -/
theorem lift_ofFun [∀ d, DecidableEq (acts d)] (π : (d : ι) → acts d) :
    lift U (Proc.ofFun π : Proc ι acts K) = Proc.ofFun (liftFun U π) := by
  funext p
  cases p with
  | inl d => rfl
  | inr u =>
      cases u
      apply FinDistr.ext'
      intro σ
      simp only [lift_inr, FinDistr.pi_w, Proc.ofFun, FinDistr.pure_w]
      by_cases h : σ = liftFun U π (Sum.inr ())
      · subst h; simp [liftFun]
      · rw [if_neg h]
        have : ∃ d, σ d ≠ π d := by
          by_contra hc
          push Not at hc
          exact h (funext hc)
        obtain ⟨d, hd⟩ := this
        exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp [hd])

end lift

/-! ### Resolution and the root-site relocation -/

section resolve

variable [DecidableEq ι] (U : Finset ι) {Ω' : Type}

/-- Resolution with a world map, built together with its canonical leaf map: every `U`-node is
replaced by its `σ d`-child, survivors are re-tagged `inl`, worlds are mapped by `g`; the second
component sends a leaf of the output to the `B`-leaf it came from (a resolved node contributes
the `σ d`-edge to the path).
Source: `fair-repair.md` Definition R2 step 3 ("every `q ∈ F_d` is deleted and replaced by the
subtree under its `a`-edge"); Exit E2; `seeds.md` SE-5 ("the canonical leaf map")
Kind: D -/
def resolveAux (g : Ω → Ω') (σ : (d : ↥U) → acts d) :
    (B : Tree Ω ι acts K) →
      (T : Tree Ω' (ι ⊕ Unit) (actsR acts U) K) × ((T.Leaves → B.Leaves) × (T.DecNode → B.DecNode))
  | .leaf ω r => ⟨.leaf (g ω) r, fun _ => (), fun q => q.elim⟩
  | .chance n β child =>
      ⟨.chance n β fun i => (resolveAux g σ (child i)).1,
        fun ℓ => ⟨ℓ.1, (resolveAux g σ (child ℓ.1)).2.1 ℓ.2⟩,
        fun q => ⟨q.1, (resolveAux g σ (child q.1)).2.2 q.2⟩⟩
  | .decision d child =>
      if h : d ∈ U then
        ⟨(resolveAux g σ (child (σ ⟨d, h⟩))).1,
          fun ℓ => ⟨σ ⟨d, h⟩, (resolveAux g σ (child (σ ⟨d, h⟩))).2.1 ℓ⟩,
          fun q => some ⟨σ ⟨d, h⟩, (resolveAux g σ (child (σ ⟨d, h⟩))).2.2 q⟩⟩
      else
        ⟨.decision (.inl d) fun a => (resolveAux g σ (child a)).1,
          fun ℓ => ⟨ℓ.1, (resolveAux g σ (child ℓ.1)).2.1 ℓ.2⟩,
          fun q => q.elim none fun p => some ⟨p.1, (resolveAux g σ (child p.1)).2.2 p.2⟩⟩

/-- The resolved tree (worlds mapped by `g`).
Source: `fair-repair.md` Definition R2 step 3
Kind: D -/
def resolveW (g : Ω → Ω') (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K) :
    Tree Ω' (ι ⊕ Unit) (actsR acts U) K :=
  (resolveAux U g σ B).1

/-- The canonical leaf map of the resolved tree.
Source: `fair-repair.md` FR-6 ("the canonical leaf map (leaf of branch `(a_d)_d` below a
resolved `U`-node ↦ the `B`-leaf below that node's chosen edges)")
Kind: D -/
def leafMapW (g : Ω → Ω') (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K) :
    (resolveW U g σ B).Leaves → B.Leaves :=
  (resolveAux U g σ B).2.1

/-- The canonical node map of the resolved tree: a surviving decision node of the output ↦ the
`B`-node it is a copy of.
Source: `fair-repair.md` FR-4 proof ("`e`-nodes inside the scope are copied across branches")
Kind: D -/
def nodeMapW (g : Ω → Ω') (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K) :
    (resolveW U g σ B).DecNode → B.DecNode :=
  (resolveAux U g σ B).2.2

/-- **`resolve σ B`** (definition of record): resolution to `σ` with every leaf world stamped
with the chosen tuple `σ` (`pol_d := σ d` for `d ∈ U`).
Source: `fair-repair.md` Definition R2 step 3 ("every leaf-world in `T_a` is stamped
`pol_d = a`"); Exit E2
Kind: D
Fidelity: exact -/
def resolve (σ : (d : ↥U) → acts d) (B : Tree Ω ι acts K) :
    Tree (RW Ω acts U) (ι ⊕ Unit) (actsR acts U) K :=
  resolveW U (fun ω => (ω, σ)) σ B

/-- **`Rel_U B`, the root-site joint product relocation** (definition of record): a new root
decision node carrying `d̂ = inr ()` whose `σ`-child is `resolve σ B`.
Source: `fair-repair.md` Exit E2 ("insert one node `q̂` above `lca(⋃_{d∈U} F_d)` with action
set `∏_{d ∈ U} A_d` … the `(a_d)_d`-branch resolves every `U`-node to its coordinate and stamps
the pol-coordinates"), at the root site
Kind: D
Fidelity: exact (root site; the LCA site is `stretch`) -/
def relocRoot [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) :
    Tree (RW Ω acts U) (ι ⊕ Unit) (actsR acts U) K :=
  .decision (.inr ()) fun σ => resolve U σ B

/-- **The canonical leaf map `π : (Rel_U B).Leaves → B.Leaves`**.
Source: `fair-repair.md` FR-6
Kind: D -/
def leafMap [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : (relocRoot U B).Leaves → B.Leaves :=
  fun ℓ => leafMapW U (fun ω => (ω, ℓ.1)) ℓ.1 B ℓ.2

/-! #### Equation lemmas -/

variable (g : Ω → Ω') (σ : (d : ↥U) → acts d)

theorem resolveAux_leaf (ω : Ω) (r : K) :
    resolveAux U g σ (.leaf ω r : Tree Ω ι acts K) =
      ⟨.leaf (g ω) r, fun _ => (), fun q => q.elim⟩ := rfl

theorem resolveAux_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    resolveAux U g σ (.chance n β child) =
      ⟨.chance n β fun i => (resolveAux U g σ (child i)).1,
        fun ℓ => ⟨ℓ.1, (resolveAux U g σ (child ℓ.1)).2.1 ℓ.2⟩,
        fun q => ⟨q.1, (resolveAux U g σ (child q.1)).2.2 q.2⟩⟩ := rfl

theorem resolveAux_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    resolveAux U g σ (.decision d child) =
      if h : d ∈ U then
        ⟨(resolveAux U g σ (child (σ ⟨d, h⟩))).1,
          fun ℓ => ⟨σ ⟨d, h⟩, (resolveAux U g σ (child (σ ⟨d, h⟩))).2.1 ℓ⟩,
          fun q => some ⟨σ ⟨d, h⟩, (resolveAux U g σ (child (σ ⟨d, h⟩))).2.2 q⟩⟩
      else
        ⟨.decision (.inl d) fun a => (resolveAux U g σ (child a)).1,
          fun ℓ => ⟨ℓ.1, (resolveAux U g σ (child ℓ.1)).2.1 ℓ.2⟩,
          fun q => q.elim none fun p => some ⟨p.1, (resolveAux U g σ (child p.1)).2.2 p.2⟩⟩ := rfl

@[simp] theorem resolveW_leaf (ω : Ω) (r : K) :
    resolveW U g σ (.leaf ω r : Tree Ω ι acts K) = .leaf (g ω) r := rfl

@[simp] theorem resolveW_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    resolveW U g σ (.chance n β child) = .chance n β fun i => resolveW U g σ (child i) := rfl

theorem resolveW_decision_mem {d : ι} (h : d ∈ U) (child : acts d → Tree Ω ι acts K) :
    resolveW U g σ (.decision d child) = resolveW U g σ (child (σ ⟨d, h⟩)) := by
  unfold resolveW; rw [resolveAux_decision, dif_pos h]

theorem resolveW_decision_not_mem {d : ι} (h : d ∉ U) (child : acts d → Tree Ω ι acts K) :
    resolveW U g σ (.decision d child) = .decision (.inl d) fun a => resolveW U g σ (child a) := by
  unfold resolveW; rw [resolveAux_decision, dif_neg h]

/-- Resolution commutes with world relabelling: `mapWorld f (resolveW g σ B) = resolveW (f ∘ g) σ B`.
Source: none: infrastructure (used to project the `pol` stamps away)
Kind: L -/
theorem mapWorld_resolveW {Ω'' : Type} (f : Ω' → Ω'') :
    (B : Tree Ω ι acts K) → mapWorld f (resolveW U g σ B) = resolveW U (f ∘ g) σ B
  | .leaf _ _ => rfl
  | .chance _ _ child => by
      simp only [resolveW_chance, mapWorld_chance]
      congr 1; funext i; exact mapWorld_resolveW f (child i)
  | .decision d child => by
      by_cases h : d ∈ U
      · rw [resolveW_decision_mem U g σ h, resolveW_decision_mem U (f ∘ g) σ h]
        exact mapWorld_resolveW f (child _)
      · rw [resolveW_decision_not_mem U g σ h, resolveW_decision_not_mem U (f ∘ g) σ h,
          mapWorld_decision]
        congr 1; funext a; exact mapWorld_resolveW f (child a)

/-- The stamps projected away: `mapWorld Prod.fst (resolve σ B) = resolveW id σ B`.
Source: `adversary-repair.md` Claim B (pre-enrichment fairness)
Kind: L -/
theorem mapWorld_fst_resolve (B : Tree Ω ι acts K) :
    mapWorld Prod.fst (resolve U σ B) = resolveW U id σ B :=
  mapWorld_resolveW U _ σ Prod.fst B

/-! #### Leaf invariants of the canonical leaf map -/

variable [∀ d, Fintype (acts d)]

/-- The world of a resolved leaf is `g` of the world of its `B`-leaf.
Source: `fair-repair.md` FR-6 (the leaf map preserves the `𝓔`-world)
Kind: L -/
theorem world_resolveW : (B : Tree Ω ι acts K) → ∀ ℓ,
    world (resolveW U g σ B) ℓ = g (world B (leafMapW U g σ B ℓ))
  | .leaf _ _ => fun _ => rfl
  | .chance _ _ child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩
      exact world_resolveW (child i) ℓ
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro ℓ
        exact world_resolveW (child _) ℓ
      · rw [dif_neg h]; dsimp only; rintro ⟨a, ℓ⟩
        exact world_resolveW (child a) ℓ

/-- The payoff is preserved by the leaf map.
Source: `fair-repair.md` FR-6
Kind: L -/
theorem payoff_resolveW : (B : Tree Ω ι acts K) → ∀ ℓ,
    payoff (resolveW U g σ B) ℓ = payoff B (leafMapW U g σ B ℓ)
  | .leaf _ _ => fun _ => rfl
  | .chance _ _ child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩
      exact payoff_resolveW (child i) ℓ
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro ℓ
        exact payoff_resolveW (child _) ℓ
      · rw [dif_neg h]; dsimp only; rintro ⟨a, ℓ⟩
        exact payoff_resolveW (child a) ℓ

/-- The chance weight of the path is preserved by the leaf map (chance nodes are copied).
Source: `fair-repair.md` FR-6 ("chance labels … are copied")
Kind: L -/
theorem chanceWeight_resolveW : (B : Tree Ω ι acts K) → ∀ ℓ,
    chanceWeight (resolveW U g σ B) ℓ = chanceWeight B (leafMapW U g σ B ℓ)
  | .leaf _ _ => fun _ => rfl
  | .chance _ β child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩
      show β.w i * chanceWeight (resolveW U g σ (child i)) ℓ =
        β.w i * chanceWeight (child i) (leafMapW U g σ (child i) ℓ)
      rw [chanceWeight_resolveW (child i) ℓ]
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro ℓ
        exact chanceWeight_resolveW (child _) ℓ
      · rw [dif_neg h]; dsimp only; rintro ⟨a, ℓ⟩
        exact chanceWeight_resolveW (child a) ℓ

/-- A survivor's `#` is preserved by the leaf map; a relocated point's `#` is zero (its nodes
were resolved away); the new root point does not occur inside a resolved tree.
Source: `fair-repair.md` FR-6; `seeds.md` SE-5(2) ("the output's fibers are copied survivor
fibers and the singleton `{q̂}`")
Kind: L -/
theorem count_resolveW : (B : Tree Ω ι acts K) → ∀ ℓ,
    (∀ d, count (.inl d) (resolveW U g σ B) ℓ =
      if d ∈ U then 0 else count d B (leafMapW U g σ B ℓ)) ∧
      count (.inr ()) (resolveW U g σ B) ℓ = 0
  | .leaf _ _ => fun _ => ⟨fun _ => by simp, rfl⟩
  | .chance _ _ child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩
      exact count_resolveW (child i) ℓ
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro ℓ
        obtain ⟨h1, h2⟩ := count_resolveW (child (σ ⟨d, h⟩)) ℓ
        unfold resolveW at h1 h2; unfold leafMapW at h1
        refine ⟨fun d' => ?_, h2⟩
        show count (.inl d') (resolveAux U g σ (child (σ ⟨d, h⟩))).1 ℓ =
          if d' ∈ U then 0 else (if d = d' then 1 else 0) +
            count d' (child (σ ⟨d, h⟩)) ((resolveAux U g σ (child (σ ⟨d, h⟩))).2.1 ℓ)
        rw [h1 d']
        by_cases hd : d' ∈ U
        · simp [hd]
        · have hne : d ≠ d' := fun heq => hd (heq ▸ h)
          simp [hd, hne]
      · rw [dif_neg h]; dsimp only; rintro ⟨a, ℓ⟩
        obtain ⟨h1, h2⟩ := count_resolveW (child a) ℓ
        unfold resolveW at h1 h2; unfold leafMapW at h1
        refine ⟨fun d' => ?_, ?_⟩
        · show (if (Sum.inl d : ι ⊕ Unit) = .inl d' then 1 else 0) +
              count (.inl d') (resolveAux U g σ (child a)).1 ℓ =
            if d' ∈ U then 0 else (if d = d' then 1 else 0) +
              count d' (child a) ((resolveAux U g σ (child a)).2.1 ℓ)
          rw [h1 d']
          by_cases hd : d' ∈ U
          · have hne : d ≠ d' := fun heq => h (heq ▸ hd)
            simp [hd, hne]
          · by_cases hdd : d = d'
            · subst hdd; simp [hd]
            · simp [hd, hdd]
        · show (if (Sum.inl d : ι ⊕ Unit) = .inr () then 1 else 0) +
              count (.inr ()) (resolveAux U g σ (child a)).1 ℓ = 0
          rw [h2]; simp

/-- The leaf map is injective.
Source: none: infrastructure
Kind: L -/
theorem leafMapW_injective : (B : Tree Ω ι acts K) → Function.Injective (leafMapW U g σ B)
  | .leaf _ _ => fun _ _ _ => rfl
  | .chance _ _ child => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ⟩ ⟨j, ℓ'⟩ h
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
      rw [heq_iff_eq] at h2
      have := leafMapW_injective (child i) h2
      subst this; rfl
  | .decision d child => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases hd : d ∈ U
      · rw [dif_pos hd]; dsimp only; intro ℓ ℓ' h
        have h2 := (Sigma.mk.inj_iff.mp h).2
        rw [heq_iff_eq] at h2
        exact leafMapW_injective (child _) h2
      · rw [dif_neg hd]; dsimp only; rintro ⟨a, ℓ⟩ ⟨b, ℓ'⟩ h
        obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
        rw [heq_iff_eq] at h2
        have := leafMapW_injective (child a) h2
        subst this; rfl

end resolve

/-! ### The resolution lemma: the memoised walk pushes forward along the leaf map -/

section seedsum

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (U : Finset ι)
  {Ω' : Type}

/-- The seed environment on `ι` with the `U`-coordinates pre-filled to `σ`, `env` elsewhere.
Source: `seeds.md` SE-5 proof ("condition on the seed tuple `(a_d)_{d∈U}`")
Kind: D -/
def fillEnv (env : (d : ι) → Option (acts d)) (σ : (d : ↥U) → acts d) : (d : ι) → Option (acts d) :=
  fun d => if h : d ∈ U then some (σ ⟨d, h⟩) else env d

theorem fillEnv_of_mem (env : (d : ι) → Option (acts d)) (σ : (d : ↥U) → acts d) {d : ι}
    (h : d ∈ U) : fillEnv U env σ d = some (σ ⟨d, h⟩) := by simp [fillEnv, h]

theorem fillEnv_of_not_mem (env : (d : ι) → Option (acts d)) (σ : (d : ↥U) → acts d) {d : ι}
    (h : d ∉ U) : fillEnv U env σ d = env d := by simp [fillEnv, h]

/-- **Resolution is the memoised walk with the `U`-seeds pre-drawn (per leaf)**: for every seed
environment `env` on `ι` whose `U`-coordinates read `σ`, and every environment `env'` on the
relocated points agreeing with `env` at the survivors, the memoised walk on `resolve σ B` under
`lift C` at a leaf `ℓ'` equals the memoised walk on `B` under `C` at `leafMapW ℓ'`.
Source: `seeds.md` SE-5 proof ("condition on the seed tuple `(a_d)_{d∈U}`, drawn once … the
resolved branch runs the survivors on the same points")
Kind: P
Fidelity: exact -/
theorem leafLawSeed_resolveW (C : Proc ι acts K) (g : Ω → Ω') (σ : (d : ↥U) → acts d) :
    (B : Tree Ω ι acts K) → ∀ (env : (d : ι) → Option (acts d))
      (env' : (p : ι ⊕ Unit) → Option (actsR acts U p)),
      (∀ d, d ∉ U → env' (.inl d) = env d) → (∀ d (h : d ∈ U), env d = some (σ ⟨d, h⟩)) →
      ∀ ℓ' : (resolveW U g σ B).Leaves,
        leafLawSeed (lift U C) env' (resolveW U g σ B) ℓ' =
          leafLawSeed C env B (leafMapW U g σ B ℓ')
  | .leaf _ _ => fun _ _ _ _ _ => rfl
  | .chance _ β child => fun env env' henv hU => by
      unfold resolveW leafMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, ℓ'⟩
      have ih := leafLawSeed_resolveW C g σ (child i) env env' henv hU ℓ'
      unfold resolveW leafMapW at ih
      show β.w i * leafLawSeed (lift U C) env' (resolveAux U g σ (child i)).1 ℓ' =
        β.w i * leafLawSeed C env (child i) ((resolveAux U g σ (child i)).2.1 ℓ')
      rw [ih]
  | .decision d child => fun env env' henv hU => by
      unfold resolveW leafMapW; rw [resolveAux_decision]
      by_cases hd : d ∈ U
      · rw [dif_pos hd]; dsimp only
        intro ℓ'
        have ih := leafLawSeed_resolveW C g σ (child (σ ⟨d, hd⟩)) env env' henv hU ℓ'
        unfold resolveW leafMapW at ih
        rw [ih, leafLawSeed_decision_of_some C (hU d hd), if_pos rfl]
      · rw [dif_neg hd]; dsimp only
        rintro ⟨b, ℓ'⟩
        rcases henvd : env d with _ | a'
        · have henv'd : env' (.inl d) = none := by rw [henv d hd, henvd]
          rw [leafLawSeed_decision_of_none (lift U C) henv'd,
            leafLawSeed_decision_of_none C henvd]
          have hupd : ∀ d', d' ∉ U → Function.update env' (.inl d) (some b) (.inl d') =
              Function.update env d (some b) d' := by
            intro d' hd'
            by_cases hdd : d' = d
            · subst hdd; simp
            · rw [Function.update_of_ne (by simpa using hdd), Function.update_of_ne hdd]
              exact henv d' hd'
          have hU' : ∀ d' (h : d' ∈ U), Function.update env d (some b) d' = some (σ ⟨d', h⟩) := by
            intro d' h
            have hne : d' ≠ d := fun heq => hd (heq ▸ h)
            rw [Function.update_of_ne hne]; exact hU d' h
          have ih := leafLawSeed_resolveW C g σ (child b) _ _ hupd hU' ℓ'
          unfold resolveW leafMapW at ih
          rw [ih]; rfl
        · have henv'd : env' (.inl d) = some a' := by rw [henv d hd, henvd]
          rw [leafLawSeed_decision_of_some (lift U C) henv'd,
            leafLawSeed_decision_of_some C henvd]
          have ih := leafLawSeed_resolveW C g σ (child b) env env' henv hU ℓ'
          unfold resolveW leafMapW at ih
          rw [ih]

/-- **Leaves outside the image of the leaf map carry no seed-mass**: a `B`-leaf that no resolved
leaf maps to takes, at some `U`-node, an edge other than `σ d`, and the memoised walk with the
`U`-seeds set to `σ` gives it weight zero.
Source: `seeds.md` SE-5 proof
Kind: P -/
theorem leafLawSeed_eq_zero_of_not_image (C : Proc ι acts K) (g : Ω → Ω') (σ : (d : ↥U) → acts d) :
    (B : Tree Ω ι acts K) → ∀ (env : (d : ι) → Option (acts d)),
      (∀ d (h : d ∈ U), env d = some (σ ⟨d, h⟩)) →
      ∀ ℓ : B.Leaves, (∀ ℓ', leafMapW U g σ B ℓ' ≠ ℓ) → leafLawSeed C env B ℓ = 0
  | .leaf _ _ => fun _ _ ℓ h => absurd rfl (h ())
  | .chance _ β child => fun env hU ℓ h => by
      unfold resolveW leafMapW at h; rw [resolveAux_chance] at h; dsimp only at h
      obtain ⟨i, ℓ⟩ := ℓ
      have hne : ∀ ℓ', (resolveAux U g σ (child i)).2.1 ℓ' ≠ ℓ := fun ℓ' heq =>
        h ⟨i, ℓ'⟩ (by rw [heq])
      have ih := leafLawSeed_eq_zero_of_not_image C g σ (child i) env hU ℓ
      unfold resolveW leafMapW at ih
      rw [leafLawSeed_chance, ih hne, mul_zero]
  | .decision d child => fun env hU ℓ h => by
      unfold resolveW leafMapW at h; rw [resolveAux_decision] at h
      obtain ⟨b, ℓ⟩ := ℓ
      by_cases hd : d ∈ U
      · rw [dif_pos hd] at h; dsimp only at h
        rw [leafLawSeed_decision_of_some C (hU d hd)]
        by_cases hb : σ ⟨d, hd⟩ = b
        · rw [if_pos hb]
          subst hb
          have hne : ∀ ℓ', (resolveAux U g σ (child (σ ⟨d, hd⟩))).2.1 ℓ' ≠ ℓ := fun ℓ' heq =>
            h ℓ' (by rw [heq])
          have ih := leafLawSeed_eq_zero_of_not_image C g σ (child (σ ⟨d, hd⟩)) env hU ℓ
          unfold resolveW leafMapW at ih
          exact ih hne
        · rw [if_neg hb]
      · rw [dif_neg hd] at h; dsimp only at h
        have hne : ∀ ℓ', (resolveAux U g σ (child b)).2.1 ℓ' ≠ ℓ := fun ℓ' heq =>
          h ⟨b, ℓ'⟩ (by rw [heq])
        rcases henvd : env d with _ | a'
        · rw [leafLawSeed_decision_of_none C henvd]
          have hU' : ∀ d' (h : d' ∈ U), Function.update env d (some b) d' = some (σ ⟨d', h⟩) := by
            intro d' h
            have hne : d' ≠ d := fun heq => hd (heq ▸ h)
            rw [Function.update_of_ne hne]; exact hU d' h
          have ih := leafLawSeed_eq_zero_of_not_image C g σ (child b) _ hU' ℓ
          unfold resolveW leafMapW at ih
          rw [ih hne, mul_zero]
        · rw [leafLawSeed_decision_of_some C henvd]
          have ih := leafLawSeed_eq_zero_of_not_image C g σ (child b) env hU ℓ
          unfold resolveW leafMapW at ih
          rw [ih hne]; simp

/-- Summing a function over the preimage of a point under an injective map.
Source: none: infrastructure
Kind: L -/
theorem sum_preimage_eq {A A' : Type} [Fintype A] [DecidableEq A'] (e : A → A')
    (he : Function.Injective e) (f : A → K) (g : A' → K) (hfg : ∀ a, f a = g (e a))
    (hzero : ∀ b, (∀ a, e a ≠ b) → g b = 0) (b : A') :
    (∑ a, if e a = b then f a else 0) = g b := by
  by_cases hex : ∃ a, e a = b
  · obtain ⟨a₀, ha₀⟩ := hex
    rw [Finset.sum_eq_single a₀]
    · rw [if_pos ha₀, hfg, ha₀]
    · intro a _ ha
      rw [if_neg]
      intro h; exact ha (he (h.trans ha₀.symm))
    · intro h; exact absurd (Finset.mem_univ a₀) h
  · push Not at hex
    rw [hzero b hex]
    exact Finset.sum_eq_zero fun a _ => if_neg (hex a)

/-- **The resolution lemma (SE-5(1)'s content)**: for every seed environment `env` on `ι` whose
`U`-coordinates read `σ`, and every environment `env'` on the relocated points agreeing with
`env` at the survivors, the memoised walk on `resolve σ B` under `lift C` pushes forward along
the leaf map to the memoised walk on `B` under `C`: `∑_{ℓ' ↦ ℓ} μ'_{env'}(ℓ') = μ'_{env}(ℓ)`.
(Resolution *is* the memoised walk with the `U`-seeds already drawn.)
Source: `seeds.md` SE-5 proof ("condition on the seed tuple `(a_d)_{d∈U}`, drawn once … the
resolved branch runs the survivors on the same points")
Kind: P
Fidelity: exact
Hyps: none -/
theorem resolve_seed_sum (C : Proc ι acts K) (g : Ω → Ω') (σ : (d : ↥U) → acts d)
    (B : Tree Ω ι acts K) (env : (d : ι) → Option (acts d))
    (env' : (p : ι ⊕ Unit) → Option (actsR acts U p))
    (henv : ∀ d, d ∉ U → env' (.inl d) = env d) (hU : ∀ d (h : d ∈ U), env d = some (σ ⟨d, h⟩))
    (ℓ : B.Leaves) :
    (∑ ℓ' : (resolveW U g σ B).Leaves, if leafMapW U g σ B ℓ' = ℓ then
      leafLawSeed (lift U C) env' (resolveW U g σ B) ℓ' else 0) = leafLawSeed C env B ℓ :=
  sum_preimage_eq (leafMapW U g σ B) (leafMapW_injective U g σ B) _ _
    (leafLawSeed_resolveW U C g σ B env env' henv hU)
    (leafLawSeed_eq_zero_of_not_image U C g σ B env hU) ℓ

end seedsum

end Cleanroom.Decision.DpFairnessReloc
