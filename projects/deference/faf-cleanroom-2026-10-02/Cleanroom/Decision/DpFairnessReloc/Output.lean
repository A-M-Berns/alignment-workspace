import Cleanroom.Decision.DpFairnessReloc.RelocateThms
import Cleanroom.Decision.DpFairnessReloc.Fork

/-!
# Fairness and honesty of the relocated output (T5, T6(a)–(c))

Package `dp-fairness-reloc`, file 6.

* **T5 — FR-4 repaired per Claim B.** For every `B` and every `U` that is *closed*
  (`Closed B U`: every point outside `U` has a pairwise-`≅` fiber, and no `U`-node lies at or
  below any node of a point outside `U` — the entanglement closure), the output
  `(Rel_U B).mapWorld Prod.fst` — the `pol` coordinates projected away — is strongly fair
  (`Closed.stronglyFair_output`): `d̂`'s fiber is the singleton root, and every survivor's copies
  across the branches are `≅` to the original. **Pre-enrichment sense**: with the stamps kept,
  copies of a survivor differ in the `pol` coordinate and FR-4 as stated is false
  (adversary-repair Claim B; the refutation witness is in `Witnesses.lean`). Nested `U`-fibers
  are allowed (SE-7′(iii)).
* **T6(a)** At the root site `O_{d̂} = ⊤`, so the conditioned statistics at `d̂` are the
  unconditioned ones (`nu_inter_univ`): an `L` row, definitional once `obs'` is `⊤`.
* **T6(b)** `Rel_U B` records at `d̂` for every procedure (`recordsForAll_root`): every run
  passes `d̂` once, `d̂` is subtree-veridical (`O = ⊤`), action-veridical (the stamp), and no other
  act-event holds (stamps are distinct).
* **T6(c)** `ρ` derived: `ν_{Rel, lift C}(pol_d = a) = C(d)(a)` (`nu_pol_eq`), and on almost-fair
  `B` the act value at `d̂`'s coordinate `a`, `𝔼[r · 1_{pol_d = a}]`, is `C(d)(a) · V_B(C[d ↦ a])`
  (`AlmostFair.expPayoff_pol`): the relocated root's act value at `a` is `V_B(C[d ↦ a])`,
  Claim 5.1's `UDT_{s°,ρ}(d) = EDT(d̂)` for **one** point (F1).
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

variable [DecidableEq ι] {Ω' : Type}

/-! ### Re-tagging and resolution on trees without relocated points -/

section retag

variable (U : Finset ι)

/-- The tree with every point re-tagged `inl` (no resolution): the identity of relocation on a
subtree containing no `U`-node.
Source: `fair-repair.md` FR-4 proof ("resolution does not touch their subtrees")
Kind: D -/
def retag : Tree Ω ι acts K → Tree Ω (ι ⊕ Unit) (actsR acts U) K
  | .leaf ω r => .leaf ω r
  | .chance n β child => .chance n β fun i => retag (child i)
  | .decision d child => .decision (.inl d) fun a => retag (child a)

/-- `≅` is preserved by re-tagging.
Source: none: infrastructure
Kind: L -/
theorem LabIso.retag {T T' : Tree Ω ι acts K} (h : LabIso T T') :
    LabIso (retag U T) (retag U T') := by
  induction h with
  | leaf ω r => exact .leaf ω r
  | chance β β' child child' σ hβ h ih => exact .chance β β' _ _ σ hβ ih
  | decision d child child' h ih => exact .decision (Sum.inl d) _ _ ih

variable [∀ d, Fintype (acts d)]

/-- On a tree with no `U`-node, resolution is re-tagging plus relabelling.
Source: `fair-repair.md` FR-4 proof (b) ("by closure no `U`-node lies below any `e`-node, so
resolution does not touch their subtrees")
Kind: P -/
theorem resolveW_of_disjoint (g : Ω → Ω') (σ : (d : ↥U) → acts d) :
    (T : Tree Ω ι acts K) → Disjoint (queried T) U → resolveW U g σ T = mapWorld g (retag U T)
  | .leaf _ _, _ => rfl
  | .chance _ β child, h => by
      simp only [resolveW_chance, retag, mapWorld_chance]
      congr 1; funext i
      exact resolveW_of_disjoint g σ (child i)
        (Finset.disjoint_of_subset_left (queried_child_subset_chance β child i) h)
  | .decision d child, h => by
      have hd : d ∉ U := fun hd =>
        Finset.disjoint_left.mp h (mem_queried_decision d child) hd
      rw [resolveW_decision_not_mem U g σ hd]
      simp only [retag, mapWorld_decision]
      congr 1; funext a
      exact resolveW_of_disjoint g σ (child a)
        (Finset.disjoint_of_subset_left (queried_child_subset_decision d child a) h)

end retag

/-! ### The node map: every node of the output is a copy of a surviving `B`-node -/

section nodes

variable (U : Finset ι) (g : Ω → Ω') (σ : (d : ↥U) → acts d)

/-- A node of the resolved tree carries the (re-tagged) point of the `B`-node it copies.
Source: `fair-repair.md` FR-4 proof
Kind: L -/
theorem pt_resolveW : (B : Tree Ω ι acts K) → ∀ q : (resolveW U g σ B).DecNode,
    pt (resolveW U g σ B) q = .inl (pt B (nodeMapW U g σ B q))
  | .leaf _ _ => fun q => q.elim
  | .chance _ _ child => by
      unfold resolveW nodeMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, q⟩
      exact pt_resolveW (child i) q
  | .decision d child => by
      unfold resolveW nodeMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro q
        exact pt_resolveW (child _) q
      · rw [dif_neg h]; dsimp only
        rintro (_ | ⟨a, q⟩)
        · rfl
        · exact pt_resolveW (child a) q

/-- The `B`-node a resolved node copies is not a relocated one.
Source: `seeds.md` SE-5(2) ("the output's fibers are copied survivor fibers")
Kind: L -/
theorem nodeMapW_not_mem : (B : Tree Ω ι acts K) → ∀ q : (resolveW U g σ B).DecNode,
    pt B (nodeMapW U g σ B q) ∉ U
  | .leaf _ _ => fun q => q.elim
  | .chance _ _ child => by
      unfold resolveW nodeMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, q⟩
      exact nodeMapW_not_mem (child i) q
  | .decision d child => by
      unfold resolveW nodeMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro q
        exact nodeMapW_not_mem (child _) q
      · rw [dif_neg h]; dsimp only
        rintro (_ | ⟨a, q⟩)
        · exact h
        · exact nodeMapW_not_mem (child a) q

/-- **Resolution commutes with subtrees at surviving nodes**: the subtree of the output at a
node is the resolution of the subtree of `B` at the node it copies.
Source: `fair-repair.md` FR-4 proof
Kind: P -/
theorem subtreeAt_resolveW : (B : Tree Ω ι acts K) → ∀ q : (resolveW U g σ B).DecNode,
    subtreeAt (resolveW U g σ B) q = resolveW U g σ (subtreeAt B (nodeMapW U g σ B q))
  | .leaf _ _ => fun q => q.elim
  | .chance _ _ child => by
      unfold resolveW nodeMapW; rw [resolveAux_chance]; dsimp only
      rintro ⟨i, q⟩
      exact subtreeAt_resolveW (child i) q
  | .decision d child => by
      unfold resolveW nodeMapW; rw [resolveAux_decision]
      by_cases h : d ∈ U
      · rw [dif_pos h]; dsimp only; intro q
        exact subtreeAt_resolveW (child _) q
      · rw [dif_neg h]; dsimp only
        rintro (_ | ⟨a, q⟩)
        · show Tree.decision (.inl d) (fun a => (resolveAux U g σ (child a)).1) =
            resolveW U g σ (.decision d child)
          rw [resolveW_decision_not_mem U g σ h]; rfl
        · exact subtreeAt_resolveW (child a) q

end nodes

/-! ### T5: the output is strongly fair in the pre-enrichment sense -/

section output

variable [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **`U` is closed for `B`**: every point outside `U` has a pairwise-`≅` fiber (`U ⊇ unfair B`),
and no `U`-node lies at or below a node of a point outside `U` (the entanglement closure as a
predicate; the mandate's operator `cl` — the least such `U` — is not constructed here, the theorem
holds for every closed `U`, and `queried B` is always closed: `closed_queried`). The closure
clause cannot be dropped: `closure_load_bearing` (`AuditWitnesses.lean`) relocates exactly the
unfair set of a two-point chain and un-fairs the other point — FR-3's ping-pong in one step.
Source: `fair-repair.md` Exit E2 ("the entanglement closure of the unfair fibers: the least set
containing every unfair fiber and containing `e` whenever some `e`-node has a `U`-node strictly
below it"); mandate T5
Kind: D
Fidelity: exact ("strictly below" = "at or below" since the point itself is not in `U`) -/
def Closed (B : Tree Ω ι acts K) (U : Finset ι) : Prop :=
  (∀ e, e ∉ U → ∀ q ∈ fiber B e, ∀ q' ∈ fiber B e, LabIso (subtreeAt B q) (subtreeAt B q')) ∧
  (∀ e, e ∉ U → ∀ q ∈ fiber B e, Disjoint (queried (subtreeAt B q)) U)

/-- Relocating every queried point is closed (the top repair).
Source: `spectrum.md` SP-D1 ("top repair (full normal form)")
Kind: L -/
theorem closed_queried [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) : Closed B (queried B) := by
  refine ⟨fun e he q hq _ _ => ?_, fun e he q hq => ?_⟩ <;>
  · exfalso
    apply he
    rw [mem_fiber] at hq
    obtain ⟨ℓ, hℓ⟩ := exists_leaf_below B q
    exact (mem_queried_iff e B).mpr ⟨ℓ, hq ▸ count_pos_of_edge B q ℓ hℓ⟩

/-- A strongly fair tree is closed for `U = ∅`.
Source: none: infrastructure
Kind: L -/
theorem StronglyFair.closed_empty {B : Tree Ω ι acts K} (h : StronglyFair B) : Closed B ∅ :=
  ⟨fun e _ q hq q' hq' => h e q hq q' hq', fun _ _ _ _ => Finset.disjoint_empty_right _⟩

/-- The stamps projected away: the root-site output relabelled by `Prod.fst`.
Source: none: infrastructure
Kind: L -/
theorem mapWorld_fst_relocRoot (U : Finset ι) (B : Tree Ω ι acts K) :
    mapWorld Prod.fst (relocRoot U B) = .decision (.inr ()) fun σ => resolveW U id σ B := by
  unfold relocRoot
  rw [mapWorld_decision]
  congr 1; funext σ
  exact mapWorld_fst_resolve U σ B

/-- **T5 (FR-4 repaired, Claim B): the relocated output is strongly fair in the pre-enrichment
sense.** For every `B` and every closed `U`, `(Rel_U B).mapWorld Prod.fst` is strongly fair:
`d̂`'s fiber is the singleton root, and each survivor's copies across the branches are all
labelled-isomorphic to the original (hence to each other). Grade: strong fairness `≅`;
semantics-free; root site; the `pol` coordinates are exempt (projected away); nested
`U`-fibers allowed.
Source: `fair-repair.md` FR-4 (as repaired by `adversary-repair.md` Claim B: "Define fairness
of `Rel_U(B)` over the pre-enrichment algebra: isomorphism preserving `(λ|_E, r)`, fresh
`pol`-coordinates exempted"); `seeds.md` SE-7′(iii) ("the output is strongly fair in the
pre-enrichment-marginal sense whether or not `U`'s fibers are nested")
Kind: P
Fidelity: exact (pre-enrichment sense, root site)
Hyps: none (`Closed B U` is the definition of record of the closure) -/
theorem Closed.stronglyFair_output {B : Tree Ω ι acts K} {U : Finset ι} (h : Closed B U) :
    StronglyFair (mapWorld Prod.fst (relocRoot U B)) := by
  rw [mapWorld_fst_relocRoot]
  intro p q hq q' hq'
  rw [mem_fiber] at hq hq'
  rcases q with _ | ⟨σ, r⟩ <;> rcases q' with _ | ⟨σ', r'⟩
  · exact LabIso.refl _
  · exfalso
    have h1 : pt (.decision (.inr ()) fun σ => resolveW U id σ B) none = Sum.inr () := rfl
    have h2 : pt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ', r'⟩) =
        .inl (pt B (nodeMapW U id σ' B r')) := pt_resolveW U id σ' B r'
    rw [h1] at hq; rw [h2] at hq'
    exact absurd (hq.trans hq'.symm) Sum.inr_ne_inl
  · exfalso
    have h1 : pt (.decision (.inr ()) fun σ => resolveW U id σ B) none = Sum.inr () := rfl
    have h2 : pt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ, r⟩) =
        .inl (pt B (nodeMapW U id σ B r)) := pt_resolveW U id σ B r
    rw [h1] at hq'; rw [h2] at hq
    exact absurd (hq.trans hq'.symm) Sum.inl_ne_inr
  · have h2 : pt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ, r⟩) =
        .inl (pt B (nodeMapW U id σ B r)) := pt_resolveW U id σ B r
    have h2' : pt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ', r'⟩) =
        .inl (pt B (nodeMapW U id σ' B r')) := pt_resolveW U id σ' B r'
    rw [h2] at hq; rw [h2'] at hq'
    have he : pt B (nodeMapW U id σ B r) = pt B (nodeMapW U id σ' B r') :=
      Sum.inl.inj (hq.trans hq'.symm)
    have hnot : pt B (nodeMapW U id σ B r) ∉ U := nodeMapW_not_mem U id σ B r
    have hs : subtreeAt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ, r⟩) =
        retag U (subtreeAt B (nodeMapW U id σ B r)) := by
      show subtreeAt (resolveW U id σ B) r = _
      rw [subtreeAt_resolveW, resolveW_of_disjoint U id σ _
        (h.2 _ hnot _ (by simp)), mapWorld_id]
    have hs' : subtreeAt (.decision (.inr ()) fun σ => resolveW U id σ B) (some ⟨σ', r'⟩) =
        retag U (subtreeAt B (nodeMapW U id σ' B r')) := by
      show subtreeAt (resolveW U id σ' B) r' = _
      rw [subtreeAt_resolveW, resolveW_of_disjoint U id σ' _
        (h.2 _ (he ▸ hnot) _ (by simp)), mapWorld_id]
    rw [hs, hs']
    exact (h.1 _ hnot _ (by simp) _ (by simp [he])).retag U

/-- The output's root fiber is a singleton: no node inside a resolved branch carries `d̂`.
Source: `fair-repair.md` FR-4 proof ("`d̂`'s fiber is a singleton")
Kind: L -/
theorem pt_relocRoot_eq_inr (U : Finset ι) (B : Tree Ω ι acts K) (q : (relocRoot U B).DecNode)
    (hq : pt (relocRoot U B) q = .inr ()) : q = none := by
  rcases q with _ | ⟨σ, r⟩
  · rfl
  · exfalso
    have := pt_resolveW U (fun ω => (ω, σ)) σ B r
    have hq' : pt (relocRoot U B) (some ⟨σ, r⟩) = pt (resolveW U (fun ω => (ω, σ)) σ B) r := rfl
    rw [hq', this] at hq
    exact absurd hq Sum.inl_ne_inr

/-- The output's root fiber is a singleton: no node inside a resolved branch carries `d̂`.
Source: `fair-repair.md` FR-4 proof ("`d̂`'s fiber is a singleton")
Kind: L -/
theorem mem_fiber_inr_relocRoot (U : Finset ι) (B : Tree Ω ι acts K) (q : (relocRoot U B).DecNode) :
    q ∈ fiber (relocRoot U B) (.inr ()) ↔ q = none := by
  rw [mem_fiber]
  exact ⟨pt_relocRoot_eq_inr U B q, fun h => by subst h; rfl⟩

end output

/-! ### T6: honesty of the output at the root -/

section honesty

variable [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (U : Finset ι)

/-- The relocated observation: `O_{d̂} = ⊤` at the root site; `O_{inl d} = O_d × ⊤`.
Source: `fair-repair.md` Definition R2 step 4 ("`⊤` if `q̂` is the root"); mandate §3 (`obs'`)
Kind: D -/
def obsR [Fintype Ω] [DecidableEq Ω] (obs : ι → Finset Ω) : ι ⊕ Unit → Finset (RW Ω acts U)
  | .inl d => Finset.univ.filter fun w => w.1 ∈ obs d
  | .inr _ => Finset.univ

/-- The relocated action events: at `d̂`, `{pol = σ}` (the stamp); at a survivor, the original
event on the first coordinate.
Source: `fair-repair.md` Definition R2 step 2 (`{{pol_d = a} : a ∈ A_d}`); mandate T6(b)
Kind: D -/
def actEvR [Fintype Ω] [DecidableEq Ω] (actEv : (d : ι) → acts d → Finset Ω) :
    (p : ι ⊕ Unit) → actsR acts U p → Finset (RW Ω acts U)
  | .inl d, a => Finset.univ.filter fun w => w.1 ∈ actEv d a
  | .inr _, σ => Finset.univ.filter fun w => w.2 = σ

/-- **T6(a): at the root site `O_{d̂} = ⊤`, so conditioning on `O_{d̂}` is no conditioning** —
`ν(X ∧ O_{d̂}) = ν(X)` for every relocated event `X`: Definition 8's conditioned statistics at `d̂`
*are* Definition 11's unconditioned ones. (An `L` row: definitional once `obs'` is `⊤`.)
Source: `verify-prior-notes.md` F1 ("at a root point with `O = ⊤`, strict OC clause 1 reads
`P_s(X) = ν(X ∣ ⊤) = ν(X)` — literally Def 11's clause"); `fair-repair.md` FR-8; mandate T6(a)
Kind: L
Fidelity: exact -/
theorem nu_inter_obsR_inr [Fintype Ω] [DecidableEq Ω] (obs : ι → Finset Ω)
    (C' : Proc (ι ⊕ Unit) (actsR acts U) K) (B : Tree Ω ι acts K) (X : Finset (RW Ω acts U)) :
    nu C' (relocRoot U B) (X ∩ obsR U obs (.inr ())) = nu C' (relocRoot U B) X := by
  simp [obsR]

/-- **T6(b): the output records at `d̂` for every procedure** (Definition 7 at the root point,
with `O_{d̂} = ⊤` and act-events `{pol = σ}`): every run passes `d̂` exactly once, `d̂` is
subtree-veridical, its stamp satisfies the drawn act-event, and no other act-event holds.
Source: `fair-repair.md` FR-8 ("`q̂` is subtree-veridical … action-veridical (pol stamped),
covered … consulted once per run; hence `B̃` records at `d̂`"), FR-2 ("records at `d̂`")
Kind: P
Fidelity: exact (root site; recording per Definition 7 for every leaf of positive mass)
Hyps: none -/
theorem recordsForAll_root [Fintype Ω] [DecidableEq Ω] (obs : ι → Finset Ω)
    (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K) :
    RecordsForAll (obsR U obs) (actEvR U actEv) (relocRoot U B) (.inr ()) := by
  intro C' ℓ' _ _
  obtain ⟨σ, ℓ'⟩ := ℓ'
  refine ⟨count_inr_relocRoot U B σ ℓ', ?_⟩
  intro q hq a ha
  obtain rfl := pt_relocRoot_eq_inr U B q hq
  have ha' : a = σ := by
    have h1 : edgeOf (relocRoot U B) none ⟨σ, ℓ'⟩ = some σ := rfl
    rw [h1] at ha
    exact (Option.some.inj ha).symm
  have hw : world (relocRoot U B) ⟨σ, ℓ'⟩ = (world B (leafMap U B ⟨σ, ℓ'⟩), σ) :=
    world_relocRoot U B σ ℓ'
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ'' _
    show world (relocRoot U B) ℓ'' ∈ obsR U obs (Sum.inr ())
    simp [obsR]
  · show world (relocRoot U B) ⟨σ, ℓ'⟩ ∈ actEvR U actEv (Sum.inr ()) a
    rw [hw, ha']
    simp [actEvR]
  · intro σ' hσ'
    have h2 : world (relocRoot U B) ⟨σ, ℓ'⟩ ∈ actEvR U actEv (Sum.inr ()) σ' := hσ'
    rw [hw] at h2
    simp only [actEvR, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    rw [ha']
    exact h2.symm

/-! ### T6(c): `ρ` derived -/

variable [∀ d, Nonempty (acts d)]

/-- The relocated-root draw restricted to the coordinate `d`: the mass of the branches whose
tuple reads `a` at `d` is the marginal `C(d)(a)`.
Source: none: infrastructure (marginal of a product distribution)
Kind: L -/
theorem sum_pi_coord (C : Proc ι acts K) (d : ↥U) (a : acts d) :
    (∑ σ : (d : ↥U) → acts d, if σ d = a then ∏ d' : ↥U, (C d').w (σ d') else 0) = (C d).w a := by
  classical
  have hsplit : ∀ σ : (d : ↥U) → acts d,
      (∏ d' : ↥U, (C d').w (σ d')) = (C d).w (σ d) * ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') :=
    fun σ => (Finset.mul_prod_erase Finset.univ (fun d' : ↥U => (C d').w (σ d'))
      (Finset.mem_univ d)).symm
  -- rewrite as a sum over the tuple of the other coordinates
  have hmarg : (∑ σ : (d : ↥U) → acts d, if σ d = a then ∏ d' : ↥U, (C d').w (σ d') else 0) =
      (C d).w a * ∑ σ : (d : ↥U) → acts d,
        (if σ d = a then 1 else 0) * ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hsplit σ]
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [hmarg]
  -- the remaining sum is the total mass of the product over the other coordinates, i.e. `1`
  have htot : (∑ σ : (d : ↥U) → acts d,
      (if σ d = a then 1 else 0) * ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d')) = 1 := by
    have h1 : (∑ σ : (d : ↥U) → acts d, ∏ d' : ↥U, (Proc.deviate C d (FinDistr.pure a) d').w (σ d')) = 1 :=
      (FinDistr.pi U fun d' => Proc.deviate C d (FinDistr.pure a) d').sum_one
    refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) h1
    rw [Finset.mul_prod_erase Finset.univ (fun d' : ↥U => (Proc.deviate C d (FinDistr.pure a) d').w (σ d'))
      (Finset.mem_univ d) |>.symm]
    congr 1
    · simp only [Proc.deviate_same, FinDistr.pure_w]
    · refine Finset.prod_congr rfl fun d' hd' => ?_
      have hne : (d' : ι) ≠ d := fun heq => Finset.ne_of_mem_erase hd' (Subtype.ext heq)
      rw [Proc.deviate_ne C _ hne]
  rw [htot, mul_one]

/-- **`ρ` derived (T6(c)): `ν_{Rel_U B, lift C}(pol_d = a) = C(d)(a)`** — the relocated tree
supplies the policy-interpretation event `ρ_d(a) := {pol_d = a}` with exactly the mixed action's
weight, on every tree. Conditional on the enrichment (E4): the event lives on `Ω × ∏_U A_d`.
Source: `fable-slop-notes.md` Claim 5.1 ("`ρ_d(a)` = 'the root chose `a` for `d`' — a recorded
draw, hence an event"); `fair-repair.md` FR-2 ("the tree supplies `ρ_d(a) = {pol_d = a}`");
`verify-prior-notes.md` E4
Kind: P
Fidelity: exact
Hyps: none -/
theorem nu_pol_eq [Fintype Ω] [DecidableEq Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K)
    (d : ↥U) (a : acts d) :
    nu (lift U C) (relocRoot U B) (Finset.univ.filter fun w : RW Ω acts U => w.2 d = a) =
      (C d).w a := by
  unfold nu mass worldEv relocRoot
  rw [Finset.sum_filter, sum_leaves_decision]
  have hbranch : ∀ σ : (d : ↥U) → acts d, ∀ ℓ' : (resolve U σ B).Leaves,
      ((resolve U σ B).world ℓ').2 = σ := by
    intro σ ℓ'
    unfold resolve
    rw [world_resolveW]
  rw [← sum_pi_coord U C d a]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ d = a
  · rw [if_pos hσ]
    have : ∀ ℓ' : (resolve U σ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩) ∈
          Finset.univ.filter (fun w : RW Ω acts U => w.2 d = a) then
          leafLaw (lift U C) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ else 0) =
        (∏ d' : ↥U, (C d').w (σ d')) * leafLaw (lift U C) (resolve U σ B) ℓ' := by
      intro ℓ'
      rw [if_pos (by simp [Finset.mem_filter, hbranch σ ℓ', hσ])]
      rfl
    simp only [this, ← Finset.mul_sum, sum_leafLaw, mul_one]
  · rw [if_neg hσ]
    apply Finset.sum_eq_zero
    intro ℓ' _
    rw [if_neg]
    simp [Finset.mem_filter, hbranch σ ℓ', hσ]

/-- The expected payoff on the branches whose tuple reads `a` at `d`: `𝔼[r · 1_{pol_d = a}]`.
Source: mandate T6(c) ("the relocated root's act value at `a`", in multiplicative form)
Kind: D -/
def expPayoffPol (C' : Proc (ι ⊕ Unit) (actsR acts U) K) (B : Tree Ω ι acts K) (d : ↥U)
    (a : acts d) : K :=
  ∑ ℓ' : (relocRoot U B).Leaves,
    if (world (relocRoot U B) ℓ').2 d = a then leafLaw C' (relocRoot U B) ℓ' * payoff (relocRoot U B) ℓ'
    else 0

/-- Restricting the root draw to `pol_d = a` is deviating `C` to `a` at `d` and scaling by
`C(d)(a)`: `𝔼_{lift C}[r 1_{pol_d = a}] = C(d)(a) · V_{Rel}(lift (C[d ↦ a]))`, on every tree.
Source: `fair-repair.md` FR-2 (the act values `V_ŝ(pay) = 𝔼[r ∣ pol = pay]`)
Kind: P -/
theorem expPayoffPol_eq (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ↥U) (a : acts d) :
    expPayoffPol U (lift U C) B d a =
      (C d).w a * value (lift U (C.deviatePure d a)) (relocRoot U B) := by
  unfold expPayoffPol value relocRoot
  rw [sum_leaves_decision, sum_leaves_decision, Finset.mul_sum]
  have hbranch : ∀ σ : (d : ↥U) → acts d, ∀ ℓ' : (resolve U σ B).Leaves,
      (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).2 = σ := by
    intro σ ℓ'
    have := world_relocRoot U B σ ℓ'
    unfold relocRoot at this
    rw [this]
  refine Finset.sum_congr rfl fun σ _ => ?_
  -- the branch weight under the deviated procedure
  have hw : (lift U (C.deviatePure d a) (Sum.inr ())).w σ =
      if σ d = a then ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') else 0 := by
    simp only [lift_inr, FinDistr.pi_w]
    rw [Finset.mul_prod_erase Finset.univ (fun d' : ↥U => (Proc.deviatePure C d a d').w (σ d'))
      (Finset.mem_univ d) |>.symm]
    have hrest : (∏ d' ∈ Finset.univ.erase d, (Proc.deviatePure C d a d').w (σ d')) =
        ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') := by
      refine Finset.prod_congr rfl fun d' hd' => ?_
      have hne : (d' : ι) ≠ d := fun heq => Finset.ne_of_mem_erase hd' (Subtype.ext heq)
      rw [Proc.deviatePure, Proc.deviate_ne C _ hne]
    rw [hrest]
    simp only [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w]
    split_ifs <;> simp
  have hw0 : (lift U C (Sum.inr ())).w σ = (C d).w (σ d) * ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') := by
    simp only [lift_inr, FinDistr.pi_w]
    exact (Finset.mul_prod_erase Finset.univ (fun d' : ↥U => (C d').w (σ d')) (Finset.mem_univ d)).symm
  -- the resolved branch's law is the same under `C` and `C[d ↦ a]` (`d` is resolved away)
  have hsame : ∀ ℓ' : (resolve U σ B).Leaves,
      leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' = leafLaw (lift U C) (resolve U σ B) ℓ' := by
    intro ℓ'
    apply leafLaw_congr_queried
    intro p hp
    cases p with
    | inl d' =>
        have hd' : d' ∉ U := by
          intro hd'
          have hq : Sum.inl d' ∈ queried (relocRoot U B) := by
            unfold relocRoot
            rw [queried_decision, Finset.mem_insert, Finset.mem_biUnion]
            exact Or.inr ⟨σ, Finset.mem_univ _, hp⟩
          exact not_mem_U_of_mem_queried_relocRoot U B hq hd'
        have hne : d' ≠ (d : ι) := fun heq => hd' (heq ▸ d.2)
        simp only [lift_inl, Proc.deviatePure, Proc.deviate_ne C _ hne]
    | inr u =>
        exfalso
        obtain ⟨ℓ', hc⟩ := (mem_queried_iff (Sum.inr u) (resolve U σ B)).mp hp
        cases u
        have := (count_resolveW U (fun ω => (ω, σ)) σ B ℓ').2
        unfold resolve at hc
        rw [this] at hc
        exact lt_irrefl _ hc
  by_cases hσ : σ d = a
  · have hleft : ∀ ℓ' : (resolve U σ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).2 d = a then
          leafLaw (lift U C) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ *
            payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ else 0) =
        (C d).w (σ d) * (∏ d' ∈ Finset.univ.erase d, (C d').w (σ d')) *
          leafLaw (lift U C) (resolve U σ B) ℓ' * payoff (resolve U σ B) ℓ' := by
      intro ℓ'
      rw [if_pos (by rw [hbranch σ ℓ']; exact hσ)]
      show (lift U C (Sum.inr ())).w σ * leafLaw (lift U C) (resolve U σ B) ℓ' *
        payoff (resolve U σ B) ℓ' = _
      rw [hw0]
    simp only [hleft]
    have hright : ∀ ℓ' : (resolve U σ B).Leaves,
        leafLaw (lift U (C.deviatePure d a)) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ *
          payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ =
        (∏ d' ∈ Finset.univ.erase d, (C d').w (σ d')) *
          leafLaw (lift U C) (resolve U σ B) ℓ' * payoff (resolve U σ B) ℓ' := by
      intro ℓ'
      show (lift U (C.deviatePure d a) (Sum.inr ())).w σ *
        leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' * payoff (resolve U σ B) ℓ' = _
      rw [hw, if_pos hσ, hsame]
    simp only [hright, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [hσ]; ring
  · have hleft : ∀ ℓ' : (resolve U σ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).2 d = a then
          leafLaw (lift U C) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ *
            payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ else 0) = 0 := by
      intro ℓ'
      rw [if_neg (by rw [hbranch σ ℓ']; exact hσ)]
    have hright : ∀ ℓ' : (resolve U σ B).Leaves,
        leafLaw (lift U (C.deviatePure d a)) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ *
          payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ = 0 := by
      intro ℓ'
      show (lift U (C.deviatePure d a) (Sum.inr ())).w σ *
        leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' * payoff (resolve U σ B) ℓ' = 0
      rw [hw, if_neg hσ]; ring
    simp only [hleft, hright, Finset.sum_const_zero, mul_zero]

/-- **T6(c) on almost-fair inputs: the relocated root's act value at `a` is `V_B(C[d ↦ a])`**:
`𝔼_{Rel, lift C}[r · 1_{pol_d = a}] = C(d)(a) · V_B(C[d ↦ a])`, i.e. `𝔼[r ∣ pol_d = a] =
V_B(C[d ↦ a])` whenever `C(d)(a) > 0`. This is Claim 5.1's `UDT_{s°,ρ}(d) = EDT(d̂)` for **one
point**; for several points EDT at the root maximises over joint policies while `UDT_{s°,ρ}`
maximises componentwise (F1's GAP, recorded as a finding, not attempted).
Source: `fable-slop-notes.md` Claim 5.1; `verify-prior-notes.md` F1 ("exact for ONE-POINT
problems"); `fair-repair.md` FR-2 (`V_ŝ(pol=pay) = (y−x)/2`)
Kind: C
Fidelity: exact (multiplicative form; one coordinate of the root tuple)
Hyps: none -/
theorem AlmostFair.expPayoffPol {B : Tree Ω ι acts K} (h : AlmostFair B) (C : Proc ι acts K)
    (d : ↥U) (a : acts d) :
    expPayoffPol U (lift U C) B d a = (C d).w a * value (C.deviatePure d a) B := by
  rw [expPayoffPol_eq, AlmostFair.value_reloc h U (C.deviatePure d a)]

end honesty

end Cleanroom.Decision.DpFairnessReloc
