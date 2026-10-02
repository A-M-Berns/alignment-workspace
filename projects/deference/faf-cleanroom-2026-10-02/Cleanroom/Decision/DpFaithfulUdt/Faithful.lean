import Cleanroom.Decision.DpFaithfulUdt.Procs
import Cleanroom.Found.DpCoreTree.Faithful

/-!
# Faithfulness (Definition F1) and the `pol` coordinate is faithful (T1 predicates, T2)

`faithful.md` Definition F1 at two levels, and T2 of [[dp-faithful-udt-mandate]]: on the relocated
tree `Rel_U B` with the self-model `lift U C'` and a masked-prior-calibrated `s°`, the disposition
coordinate `pol_d = a` (`polEv`) is **law-faithful** (world marginal and payoff mass of the
deviated run `C'[d ↦ a]`), hence value-faithful, with no faithfulness assumed: the identity
`V_{s°}(pol_d = a) = V_{Rel}(lift (C'[d ↦ a]))` holds on every tree (`polEv_V_eq_value_reloc`) and
on almost-fair trees it is `V_B(C'[d ↦ a])` (`polEv_V_eq_value`). **The best-reply theorem**
(FA-9): `UDT_{s°,pol}(d) = Unif BR_d(C')` (`udtProc_polEv_eq_bestReply`), whose hypothesis
package contains no faithfulness assumption; the abstract form over an assumed value-faithful
`ρ` is the `L` row `udtProc_eq_bestReply_of_valueFaithful`.

* State level (`LawFaithfulAt`, `ValueFaithfulAt`): the state lives on an enrichment `Ω'` and
  is compared with the tree's statistics through a projection `π : Ω' → Ω` (`Prod.fst` for the
  relocated carrier, `id` for the unenriched one). Multiplicative, no division.
* Leaf level (`LeafLawFaithfulWrt`): the candidate event is a leaf-set `E` (an event of the
  enrichment `2^Leaves`) and the law compared is that of a labelling `lab : Leaves → Λ` of the
  runs (the algebra `𝓔 = σ(lab)`; `(λ, r)` for Definition F1's joint law, `(coin, r)` for the
  `k`-fold muggings whose world type is `Unit`), per run (the deviation restricted to `occ(d)`,
  as FA-4's `disposition_faithful` is stated). FA-4 is cited, not reproved
  (`drew_leafLawFaithful`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### Definition F1 at the state level -/

section stateLevel

variable {Ω' : Type} [Fintype Ω'] [DecidableEq Ω']

/-- The event of the enrichment `Ω'` whose projection lies in `X ⊆ Ω` (`λ|_𝓔 ⊨ X`).
Source: `faithful.md` Definition F1 ("`λ|_𝓔`")
Kind: D -/
def preEv (π : Ω' → Ω) (X : Finset Ω) : Finset Ω' := Finset.univ.filter fun w => π w ∈ X

/-- Membership in `preEv`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_preEv (π : Ω' → Ω) (X : Finset Ω) (w : Ω') : w ∈ preEv π X ↔ π w ∈ X := by
  simp [preEv]

/-- `preEv π ⊤ = ⊤`. Source: none: infrastructure. Kind: L -/
@[simp] theorem preEv_univ (π : Ω' → Ω) : preEv π (Finset.univ : Finset Ω) = Finset.univ := by
  ext w; simp

variable (s₀ : State Ω' K) (ρ : (d : ι) → acts d → Finset Ω') (C' : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- **Definition F1, value-faithfulness at `d`** relative to the self-model `C'`: every
`ρ_d(a)` has positive prior probability and `V_{s°}(ρ_d(a)) = V_B(C'[d ↦ a])`.
Source: `faithful.md` Definition F1 ("*value-faithful* if only
`𝔼_{μ_{B,C'}}[r ∣ λ ⊨ ρ_d(a)] = V_B(C'[d↦a])`"; "value-faithfulness reads
`V_{s°}(ρ_d(a)) = V_B(C'[d↦a])`")
Kind: D
Fidelity: exact (the positivity clause of F1 included) -/
def ValueFaithfulAt (d : ι) : Prop :=
  ∀ a, 0 < s₀.pr (ρ d a) ∧ s₀.V (ρ d a) = value (C'.deviatePure d a) B

/-- **Definition F1, law-faithfulness at `d`** relative to `C'`, through the projection `π` of
the enriched carrier onto the tree's worlds: for every `a`, `P_{s°}(ρ_d(a)) > 0`, the
`ρ_d(a)`-conditional world marginal of `s°` is `ν_{B,C'[d↦a]}`, and the `ρ_d(a)`-conditional payoff
mass is that of `μ_{B,C'[d↦a]}` — the "conditional joint law of `(λ|_𝓔, r)`" as a state carries
it (`P` on worlds, `V` on events), cross-multiplied:
`P_{s°}(X ∧ ρ_d(a)) = P_{s°}(ρ_d(a)) · ν_{C'[d↦a]}(X)` and
`V_{s°}(X ∧ ρ_d(a)) · P_{s°}(X ∧ ρ_d(a)) = P_{s°}(ρ_d(a)) · 𝔼_{C'[d↦a]}[r · 1_X]`.
Source: `faithful.md` Definition F1 ("the conditional joint law of `(λ|_𝓔, r)` under `μ_{B,C'}`
given `λ ⊨ ρ_d(a)` equals its law under the deviated run `μ_{B,C'[d↦a]}`")
Kind: D
Fidelity: variant: the joint law is rendered as the pair (world marginal, payoff mass on every
event), which is all a `State` carries; multiplicative form -/
def LawFaithfulAt (π : Ω' → Ω) (d : ι) : Prop :=
  ∀ a, 0 < s₀.pr (ρ d a) ∧
    (∀ X : Finset Ω,
      s₀.pr (preEv π X ∩ ρ d a) = s₀.pr (ρ d a) * nu (C'.deviatePure d a) B X) ∧
    (∀ X : Finset Ω,
      s₀.V (preEv π X ∩ ρ d a) * s₀.pr (preEv π X ∩ ρ d a) =
        s₀.pr (ρ d a) * paySum (C'.deviatePure d a) B X)

/-- `𝔼[r · 1_⊤] = V_B(C)`. Source: none: infrastructure. Kind: L -/
theorem paySum_univ (C : Proc ι acts K) : paySum C B Finset.univ = value C B := by
  unfold paySum value; rw [worldEv_univ]

/-- **Law-faithful implies value-faithful** (take `X := ⊤` in the payoff clause).
Source: `faithful.md` Definition F1 ("*value-faithful* if only …")
Kind: L -/
theorem LawFaithfulAt.valueFaithfulAt {π : Ω' → Ω} {d : ι} (h : LawFaithfulAt s₀ ρ C' B π d) :
    ValueFaithfulAt s₀ ρ C' B d := by
  intro a
  obtain ⟨hpos, -, hV⟩ := h a
  refine ⟨hpos, ?_⟩
  have := hV Finset.univ
  rw [preEv_univ, Finset.univ_inter, paySum_univ] at this
  rw [mul_comm] at this
  exact mul_left_cancel₀ hpos.ne' this

end stateLevel

/-! ### Definition F1 at the leaf level -/

section leafLevel

variable (B : Tree Ω ι acts K)

/-- The leaf-set `{ℓ : lab(ℓ) ∈ X}` of a labelling of the runs.
Source: `faithful.md` Definition F1 (the algebra `𝓔` the law is taken on)
Kind: D -/
def labEv {Λ : Type} [DecidableEq Λ] (lab : B.Leaves → Λ) (X : Finset Λ) : Finset B.Leaves :=
  Finset.univ.filter fun ℓ => lab ℓ ∈ X

/-- Membership in `labEv`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_labEv {Λ : Type} [DecidableEq Λ] (lab : B.Leaves → Λ) (X : Finset Λ)
    (ℓ : B.Leaves) : ℓ ∈ labEv B lab X ↔ lab ℓ ∈ X := by
  simp [labEv]

/-- `labEv id S = S`. Source: none: infrastructure. Kind: L -/
@[simp] theorem labEv_id (S : Finset B.Leaves) : labEv B id S = S := by
  ext ℓ; simp

/-- **Definition F1 at the leaf level, per run, relative to the algebra generated by `lab`**: the
leaf-set `E` (an event of the enrichment `2^Leaves`) is law-faithful for `(B, C')` at `d` for the
action `a` if `μ_{C'}(E) > 0` and, for every `X` of the labelled algebra,
`μ_{C'}(lab ⊨ X ∧ E) · μ_{C'[d↦a]}(occ d) = μ_{C'}(E) · μ_{C'[d↦a]}(lab ⊨ X ∧ occ d)` — conditioning
`μ_{C'}` on `E` gives the deviated run restricted to `occ(d)` (FA-4's form; on trees where every
run meets `d`, `occ(d) = ⊤` and this is the unconditioned deviation law of F1).
Junk: at a point the deviation never reaches (`μ_{C'[d↦a]}(occ d) = 0`) both sides of the law
clause vanish and every positive-mass `E` is vacuously faithful; every headline in this package
has `occ(d) = ⊤`. A consumer stating faithfulness at a possibly off-path point should add the
guard `0 < μ_{C'[d↦a]}(occ d)` (audit r1 (fidelity) N7).
Source: `faithful.md` Definition F1 (on an enrichment `𝓔′ ⊇ 𝓔`), FA-4 ("conditioning on the
recorded draw is the deviation"); `dp-core-tree`'s `disposition_faithful`
Kind: D
Fidelity: variant: per-run (occ-conditioned) form; `𝓔 := σ(lab)` -/
def LeafLawFaithfulWrt {Λ : Type} [DecidableEq Λ] (lab : B.Leaves → Λ) (C' : Proc ι acts K)
    (d : ι) (a : acts d) (E : Finset B.Leaves) : Prop :=
  0 < mass C' B E ∧
    ∀ X : Finset Λ,
      mass C' B (labEv B lab X ∩ E) * mass (C'.deviatePure d a) B (occ d B) =
        mass C' B E * mass (C'.deviatePure d a) B (labEv B lab X ∩ occ d B)

/-- **Definition F1's joint `(λ, r)` law at the leaf level**: `LeafLawFaithfulWrt` with the
labelling `ℓ ↦ (λ(ℓ), r(ℓ))`.
Source: `faithful.md` Definition F1 ("the conditional joint law of `(λ|_𝓔, r)`")
Kind: D -/
def LeafLawFaithful (C' : Proc ι acts K) (d : ι) (a : acts d) (E : Finset B.Leaves) : Prop :=
  LeafLawFaithfulWrt B (fun ℓ => (world B ℓ, payoff B ℓ)) C' d a E

/-- **FA-4 at the leaf level, cited**: when every run meets `d` at most once, the recorded-draw
event `drew d a` is law-faithful (on the finest algebra, `lab = id`, hence on every coarser one)
for every `C'` with `μ_{C'}(drew d a) > 0` — `dp-core-tree`'s `disposition_faithful` in the
package's predicate.
Source: `faithful.md` FA-4 (dp-cf-2-004); `dp-core-tree` `disposition_faithful`
Kind: L
Fidelity: exact (one `exact` over the cited theorem) -/
theorem drew_leafLawFaithful (C' : Proc ι acts K) (d : ι) (a : acts d)
    (hfair : ∀ ℓ, count d B ℓ ≤ 1) (hpos : 0 < mass C' B (drew d a B)) :
    LeafLawFaithfulWrt B id C' d a (drew d a B) := by
  refine ⟨hpos, fun S => ?_⟩
  rw [labEv_id, disposition_faithful C' B d a hfair S, mul_comm]

end leafLevel

/-! ### T2: the `pol` coordinate is faithful -/

section pol

variable (U : Finset ι) (B : Tree Ω ι acts K)

/-- `𝔼[g(λ, r) · 1_{pol_d = a}]` on the relocated tree, for a functional `g` of the unstamped
world and the payoff (the payoff version is `dp-fairness-reloc`'s `expPayoffPol`).
Source: none: infrastructure (generalises `expPayoffPol`)
Kind: D -/
def expFunPol (C'' : Proc (ι ⊕ Unit) (actsR acts U) K) (d : ↥U) (a : acts d) (g : Ω → K → K) :
    K :=
  ∑ ℓ' : (relocRoot U B).Leaves,
    if (world (relocRoot U B) ℓ').2 d = a then
      leafLaw C'' (relocRoot U B) ℓ' * g (world (relocRoot U B) ℓ').1 (payoff (relocRoot U B) ℓ')
    else 0

/-- Restricting the root draw to `pol_d = a` is deviating `C` to `a` at `d` and scaling by
`C(d)(a)`, for every functional of `(λ, r)` — `expPayoffPol_eq`'s proof with `g(λ, r)` in place of
`r`.
Source: `fair-repair.md` FR-2 (the laws at `pol = pay`); `dp-fairness-reloc` `expPayoffPol_eq`
Kind: P -/
theorem expFunPol_eq (C : Proc ι acts K) (d : ↥U) (a : acts d) (g : Ω → K → K) :
    expFunPol U B (lift U C) d a g =
      (C d).w a * ∑ ℓ' : (relocRoot U B).Leaves,
        leafLaw (lift U (C.deviatePure d a)) (relocRoot U B) ℓ' *
          g (world (relocRoot U B) ℓ').1 (payoff (relocRoot U B) ℓ') := by
  unfold expFunPol relocRoot
  rw [sum_leaves_decision, sum_leaves_decision, Finset.mul_sum]
  have hbranch : ∀ σ : (d : ↥U) → acts d, ∀ ℓ' : (resolve U σ B).Leaves,
      (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).2 = σ := by
    intro σ ℓ'
    have := world_relocRoot U B σ ℓ'
    unfold relocRoot at this
    rw [this]
  refine Finset.sum_congr rfl fun σ _ => ?_
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
  have hw0 : (lift U C (Sum.inr ())).w σ =
      (C d).w (σ d) * ∏ d' ∈ Finset.univ.erase d, (C d').w (σ d') := by
    simp only [lift_inr, FinDistr.pi_w]
    exact (Finset.mul_prod_erase Finset.univ (fun d' : ↥U => (C d').w (σ d'))
      (Finset.mem_univ d)).symm
  have hsame : ∀ ℓ' : (resolve U σ B).Leaves,
      leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' =
        leafLaw (lift U C) (resolve U σ B) ℓ' := by
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
            g (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).1
              (payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩) else 0) =
        (C d).w (σ d) * (∏ d' ∈ Finset.univ.erase d, (C d').w (σ d')) *
          leafLaw (lift U C) (resolve U σ B) ℓ' *
            g (world (resolve U σ B) ℓ').1 (payoff (resolve U σ B) ℓ') := by
      intro ℓ'
      rw [if_pos (by rw [hbranch σ ℓ']; exact hσ)]
      show (lift U C (Sum.inr ())).w σ * leafLaw (lift U C) (resolve U σ B) ℓ' *
        g (world (resolve U σ B) ℓ').1 (payoff (resolve U σ B) ℓ') = _
      rw [hw0]
    simp only [hleft]
    have hright : ∀ ℓ' : (resolve U σ B).Leaves,
        leafLaw (lift U (C.deviatePure d a)) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B)
            ⟨σ, ℓ'⟩ *
          g (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).1
            (payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩) =
        (∏ d' ∈ Finset.univ.erase d, (C d').w (σ d')) *
          leafLaw (lift U C) (resolve U σ B) ℓ' *
            g (world (resolve U σ B) ℓ').1 (payoff (resolve U σ B) ℓ') := by
      intro ℓ'
      show (lift U (C.deviatePure d a) (Sum.inr ())).w σ *
        leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' *
          g (world (resolve U σ B) ℓ').1 (payoff (resolve U σ B) ℓ') = _
      rw [hw, if_pos hσ, hsame]
    simp only [hright, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [hσ]; ring
  · have hleft : ∀ ℓ' : (resolve U σ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).2 d = a then
          leafLaw (lift U C) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩ *
            g (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).1
              (payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩) else 0) = 0 := by
      intro ℓ'
      rw [if_neg (by rw [hbranch σ ℓ']; exact hσ)]
    have hright : ∀ ℓ' : (resolve U σ B).Leaves,
        leafLaw (lift U (C.deviatePure d a)) (Tree.decision (Sum.inr ()) fun σ => resolve U σ B)
            ⟨σ, ℓ'⟩ *
          g (world (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩).1
            (payoff (Tree.decision (Sum.inr ()) fun σ => resolve U σ B) ⟨σ, ℓ'⟩) = 0 := by
      intro ℓ'
      show (lift U (C.deviatePure d a) (Sum.inr ())).w σ *
        leafLaw (lift U (C.deviatePure d a)) (resolve U σ B) ℓ' *
          g (world (resolve U σ B) ℓ').1 (payoff (resolve U σ B) ℓ') = 0
      rw [hw, if_neg hσ]; ring
    simp only [hleft, hright, Finset.sum_const_zero, mul_zero]

/-- **FR-6 for `(λ, r)`-functionals**: on almost-fair `B`, every `𝔼_{Rel, lift C}[g(λ, r)]` equals
`𝔼_{B,C}[g(λ, r)]` (the pushforward of the relocated law along the leaf map is the input's law,
`AlmostFair.pushLaw_reloc`).
Source: `fair-repair.md` FR-6; `dp-fairness-reloc` `AlmostFair.pushLaw_reloc`
Kind: C -/
theorem sum_fun_relocRoot_eq (hB : AlmostFair B) (C : Proc ι acts K) (g : Ω → K → K) :
    (∑ ℓ' : (relocRoot U B).Leaves, leafLaw (lift U C) (relocRoot U B) ℓ' *
        g (world (relocRoot U B) ℓ').1 (payoff (relocRoot U B) ℓ')) =
      ∑ ℓ, leafLaw C B ℓ * g (world B ℓ) (payoff B ℓ) := by
  have hw : ∀ ℓ' : (relocRoot U B).Leaves,
      (world (relocRoot U B) ℓ').1 = world B (leafMap U B ℓ') := by
    rintro ⟨σ, ℓ'⟩; rw [world_relocRoot]
  have hp : ∀ ℓ' : (relocRoot U B).Leaves,
      payoff (relocRoot U B) ℓ' = payoff B (leafMap U B ℓ') := by
    rintro ⟨σ, ℓ'⟩; exact payoff_relocRoot U B σ ℓ'
  calc (∑ ℓ' : (relocRoot U B).Leaves, leafLaw (lift U C) (relocRoot U B) ℓ' *
          g (world (relocRoot U B) ℓ').1 (payoff (relocRoot U B) ℓ'))
      = ∑ ℓ' : (relocRoot U B).Leaves, ∑ ℓ, if leafMap U B ℓ' = ℓ then
          leafLaw (lift U C) (relocRoot U B) ℓ' * g (world B ℓ) (payoff B ℓ) else 0 := by
        refine Finset.sum_congr rfl fun ℓ' _ => ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hw ℓ', hp ℓ']
    _ = ∑ ℓ, ∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
          leafLaw (lift U C) (relocRoot U B) ℓ' * g (world B ℓ) (payoff B ℓ) else 0 :=
        Finset.sum_comm
    _ = ∑ ℓ, (∑ ℓ' : (relocRoot U B).Leaves, if leafMap U B ℓ' = ℓ then
          leafLaw (lift U C) (relocRoot U B) ℓ' else 0) * g (world B ℓ) (payoff B ℓ) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ℓ' _ => ?_
        split_ifs <;> simp
    _ = ∑ ℓ, leafLaw C B ℓ * g (world B ℓ) (payoff B ℓ) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [AlmostFair.pushLaw_reloc hB U C ℓ]

variable (C' : Proc ι acts K)

/-- The world event `{λ|_𝓔 ⊨ X} ∧ {pol_d = a}` of the relocated tree, as a leaf condition.
Source: none: infrastructure
Kind: L -/
theorem mem_preEv_inter_polEv {d : ι} (h : d ∈ U) (X : Finset Ω) (a : acts d)
    (w : RW Ω acts U) :
    w ∈ preEv Prod.fst X ∩ polEv U d a ↔ w.1 ∈ X ∧ w.2 ⟨d, h⟩ = a := by
  rw [polEv_of_mem U h]
  simp

/-- `ν_{Rel, lift C'}(X ∧ pol_d = a) = C'(d)(a) · ν_{B, C'[d↦a]}(X)` on almost-fair `B`: the world
marginal of `pol_d = a` is the deviated run's (the sibling of `nu_pol_eq` for every `X`).
Source: `faithful.md` FA-4 (the `pol_d` coordinate's laws); mandate T2(b) (`nu_pol_inter_eq`)
Kind: P -/
theorem nu_preEv_inter_polEv (hB : AlmostFair B) {d : ι} (h : d ∈ U) (X : Finset Ω)
    (a : acts d) :
    nu (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a) =
      (C' d).w a * nu (C'.deviatePure d a) B X := by
  have h1 : nu (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a) =
      expFunPol U B (lift U C') ⟨d, h⟩ a fun ω _ => if ω ∈ X then 1 else 0 := by
    rw [nu_eq_sum]
    unfold expFunPol
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    have hmem := mem_preEv_inter_polEv U h X a (world (relocRoot U B) ℓ')
    by_cases hX : (world (relocRoot U B) ℓ').1 ∈ X <;> by_cases ha : (world (relocRoot U B) ℓ').2 ⟨d, h⟩ = a <;>
      simp [hmem, hX, ha]
  rw [h1, expFunPol_eq]
  have h2 : (∑ ℓ' : (relocRoot U B).Leaves, leafLaw (lift U (C'.deviatePure d a)) (relocRoot U B) ℓ' *
      (if (world (relocRoot U B) ℓ').1 ∈ X then (1 : K) else 0)) =
      ∑ ℓ, leafLaw (C'.deviatePure d a) B ℓ * (if world B ℓ ∈ X then 1 else 0) :=
    sum_fun_relocRoot_eq U B hB (C'.deviatePure d a) fun ω _ => if ω ∈ X then (1 : K) else 0
  have h3 : nu (C'.deviatePure d a) B X =
      ∑ ℓ, leafLaw (C'.deviatePure d a) B ℓ * (if world B ℓ ∈ X then 1 else 0) := by
    rw [nu_eq_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs <;> simp
  rw [h3, ← h2]

/-- `𝔼_{Rel, lift C'}[r · 1_{X ∧ pol_d = a}] = C'(d)(a) · 𝔼_{B, C'[d↦a]}[r · 1_X]` on almost-fair
`B`: the payoff mass of `pol_d = a` on every world event is the deviated run's.
Source: `faithful.md` FA-4; mandate T2(b)
Kind: P -/
theorem paySum_preEv_inter_polEv (hB : AlmostFair B) {d : ι} (h : d ∈ U) (X : Finset Ω)
    (a : acts d) :
    paySum (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a) =
      (C' d).w a * paySum (C'.deviatePure d a) B X := by
  have h1 : paySum (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a) =
      expFunPol U B (lift U C') ⟨d, h⟩ a fun ω r => if ω ∈ X then r else 0 := by
    rw [paySum_eq_sum_ite]
    unfold expFunPol
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    have hmem := mem_preEv_inter_polEv U h X a (world (relocRoot U B) ℓ')
    by_cases hX : (world (relocRoot U B) ℓ').1 ∈ X <;> by_cases ha : (world (relocRoot U B) ℓ').2 ⟨d, h⟩ = a <;>
      simp [hmem, hX, ha]
  rw [h1, expFunPol_eq]
  have h2 : (∑ ℓ' : (relocRoot U B).Leaves, leafLaw (lift U (C'.deviatePure d a)) (relocRoot U B) ℓ' *
      (if (world (relocRoot U B) ℓ').1 ∈ X then payoff (relocRoot U B) ℓ' else 0)) =
      ∑ ℓ, leafLaw (C'.deviatePure d a) B ℓ * (if world B ℓ ∈ X then payoff B ℓ else 0) :=
    sum_fun_relocRoot_eq U B hB (C'.deviatePure d a) fun ω r => if ω ∈ X then r else 0
  have h3 : paySum (C'.deviatePure d a) B X =
      ∑ ℓ, leafLaw (C'.deviatePure d a) B ℓ * (if world B ℓ ∈ X then payoff B ℓ else 0) := by
    rw [paySum_eq_sum_ite]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs <;> simp
  rw [h3, ← h2]

/-- A world event of `ν`-mass zero carries no payoff mass.
Source: none: infrastructure
Kind: L -/
theorem paySum_eq_zero_of_nu_eq_zero (C : Proc ι acts K) (X : Finset Ω) (h : nu C B X = 0) :
    paySum C B X = 0 := by
  unfold paySum
  unfold nu mass at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ).mp h
  exact Finset.sum_eq_zero fun ℓ hℓ => by rw [hz ℓ hℓ, zero_mul]

/-- `𝔼[r · 1_{pol_d = a}]` as `paySum` of the `polEv` event (`expPayoffPol` is the same sum).
Source: none: infrastructure
Kind: L -/
theorem paySum_polEv {d : ι} (h : d ∈ U) (C'' : Proc (ι ⊕ Unit) (actsR acts U) K) (a : acts d) :
    paySum C'' (relocRoot U B) (polEv U d a) = expPayoffPol U C'' B ⟨d, h⟩ a := by
  unfold paySum expPayoffPol worldEv
  rw [polEv_of_mem U h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ℓ' _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable (s₀ : State (RW Ω acts U) K)

/-- `P_{s°}(pol_d = a) = C'(d)(a)` under prior calibration to `lift C'`.
Source: `fair-repair.md` FR-2; mandate T2(a)
Kind: L -/
theorem polEv_pr (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U)
    (a : acts d) : s₀.pr (polEv U d a) = (C' d).w a := by
  rw [hcal.1, nu_polEv U h]

/-- **`V_{s°}(pol_d = a) = V_{Rel_U B}(lift (C'[d ↦ a]))` on every tree** (Definition 11's clause 2
at the event `pol_d = a`, with `nu_pol_eq` and `expPayoffPol_eq`): the prior state's value of the
disposition is the relocated value of the deviated self-model. What fails under nesting is only
the further identification with `V_B(C'[d ↦ a])` (FR-7(b)), stated separately below.
Source: `faithful.md` FA-9 ("Toolkit confirms `V_{s°}(ρ_d(a)) = V_B(C'[d↦a])`"); mandate T2
("the general identity and the almost-fair corollary separately")
Kind: C (Definition 11's clause 2 chained with the upstream `nu_pol_eq` and `expPayoffPol_eq`)
Fidelity: exact (every tree; the guard `C'(d)(a) > 0` is Definition 11's)
Hyps: (a) `PriorCalibrated (lift U C') (Rel_U B) s°`; (a) `0 < C'(d)(a)` -/
theorem polEv_V_eq_value_reloc (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀)
    {d : ι} (h : d ∈ U) (a : acts d) (hpos : 0 < (C' d).w a) :
    s₀.V (polEv U d a) = value (lift U (C'.deviatePure d a)) (relocRoot U B) := by
  have h1 := hcal.2 (polEv U d a) (by rw [nu_polEv U h]; exact hpos)
  rw [nu_polEv U h, paySum_polEv U B h, expPayoffPol_eq] at h1
  have h2 : s₀.V (polEv U d a) * (C' d).w a =
      (C' d).w a * value (lift U (C'.deviatePure d a)) (relocRoot U B) := h1
  rw [mul_comm] at h2
  exact mul_left_cancel₀ hpos.ne' h2

/-- **`V_{s°}(pol_d = a) = V_B(C'[d ↦ a])` on almost-fair trees** (the general identity plus FR-6
value preservation).
Source: `faithful.md` FA-9; mandate T2(a)
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B`; (a) `PriorCalibrated (lift U C') (Rel_U B) s°`; (a) `0 < C'(d)(a)` -/
theorem polEv_V_eq_value (hB : AlmostFair B)
    (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) (a : acts d)
    (hpos : 0 < (C' d).w a) :
    s₀.V (polEv U d a) = value (C'.deviatePure d a) B := by
  rw [polEv_V_eq_value_reloc U B C' s₀ hcal h a hpos, AlmostFair.value_reloc hB U]

/-- **T2(a): the `pol` coordinate is value-faithful**, derived: for almost-fair `B`, every `U`,
and `s°` masked-prior-calibrated under `lift U C'`, `ValueFaithfulAt s° (polEv U) C' B d` at every
`d ∈ U` — no faithfulness is assumed; positivity is the self-model's full support, the value
identity is Definition 11's clause 2 through `nu_pol_eq`, `expPayoffPol_eq` and FR-6.
Source: `faithful.md` FA-4, FA-9 ("the recorded-act `ρ` is faithful relative to `C'` by FA-4's
argument"); dp-cf-2-007, dp-cf-108
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem polEv_valueFaithful (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    ValueFaithfulAt s₀ (polEv U) C' B d := by
  intro a
  have hpos : 0 < (C' d).w a := hcal.1 (.inl d) a
  exact ⟨by rw [polEv_pr U B C' s₀ hcal.2 h]; exact hpos,
    polEv_V_eq_value U B C' s₀ hB hcal.2 h a hpos⟩

/-- **T2(b): the `pol` coordinate is law-faithful** (Definition F1 in full, through `π = Prod.fst`):
under the hypotheses of T2(a), the `pol_d = a`-conditional world marginal of `s°` is
`ν_{B,C'[d↦a]}` and its payoff mass on every world event is `𝔼_{C'[d↦a]}[r · 1_X]`.
Source: `faithful.md` FA-4 ("law-faithful on every tree where `d` is consulted at most once per
run"), FA-9; dp-cf-2-007
Kind: C (Definition 11's two clauses at `X ∧ pol_d = a` chained with `nu_preEv_inter_polEv`,
`paySum_preEv_inter_polEv`)
Fidelity: exact
Hyps: (a) `AlmostFair B`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem polEv_lawFaithful (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    LawFaithfulAt s₀ (polEv U) C' B Prod.fst d := by
  intro a
  have hpos : 0 < (C' d).w a := hcal.1 (.inl d) a
  have hpr : s₀.pr (polEv U d a) = (C' d).w a := polEv_pr U B C' s₀ hcal.2 h a
  refine ⟨by rw [hpr]; exact hpos, fun X => ?_, fun X => ?_⟩
  · rw [hcal.2.1, nu_preEv_inter_polEv U B C' hB h X a, hpr]
  · rw [hpr]
    by_cases hz : 0 < nu (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a)
    · have := hcal.2.2 _ hz
      rw [hcal.2.1, this, paySum_preEv_inter_polEv U B C' hB h X a]
    · push Not at hz
      have h0 : nu (lift U C') (relocRoot U B) (preEv Prod.fst X ∩ polEv U d a) = 0 :=
        le_antisymm hz (nu_nonneg _ _ _)
      rw [nu_preEv_inter_polEv U B C' hB h X a] at h0
      have h0' : nu (C'.deviatePure d a) B X = 0 := by
        rcases mul_eq_zero.mp h0 with h0 | h0
        · exact absurd h0 hpos.ne'
        · exact h0
      rw [hcal.2.1, nu_preEv_inter_polEv U B C' hB h X a, h0', mul_zero, mul_zero,
        paySum_eq_zero_of_nu_eq_zero B _ X h0', mul_zero]

/-! ### The best-reply theorem -/

/-- **The abstract best-reply identity (`L`)**: if `ρ` is value-faithful at `d` relative to `C'`
then `UDT_{s°,ρ}(d) = Unif BR_d(C')` — one unfolding of Definition 17 over the assumed
faithfulness. The headline whose hypothesis package contains no faithfulness assumption is
`udtProc_polEv_eq_bestReply`.
Source: `faithful.md` FA-9 (the conditional form "with `ρ` value-faithful at every point")
Kind: L
Fidelity: exact -/
theorem udtProc_eq_bestReply_of_valueFaithful {Ω' : Type} [Fintype Ω'] [DecidableEq Ω']
    (s : State Ω' K) (ρ : (d : ι) → acts d → Finset Ω') {d : ι}
    (hv : ValueFaithfulAt s ρ C' B d) :
    udtProc s ρ d = uniformOn (BR C' B d) (BR_nonempty C' B d) := by
  rw [udtProc_eq_uniformArgmax s ρ d fun a => (hv a).1]
  have hf : (fun a => s.V (ρ d a)) = fun a => value (C'.deviatePure d a) B :=
    funext fun a => (hv a).2
  simp only [uniformArgmax, hf]
  rfl

/-- **T2(c) — the best-reply theorem (FA-9), derived**: for almost-fair `B`, any `U`, a self-model
`C'` and `s°` masked-prior-calibrated under `lift U C'` on `Rel_U B`, at every `d ∈ U`
`UDT_{s°, pol}(d) = Unif argmax_a V_B(C'[d ↦ a]) = Unif BR_d(C')` — Theorem 2's evaluator with the
self-model `C'` in place of `C`. The `pol` coordinate's faithfulness is proved (T2(a)), not
assumed; the product form of the self-model across points is `lift`'s root law (`lift_inr`), i.e.
"forced by Definition 11's type".
Scope: almost-fair trees, Definition 6, Definition 11 masked with the self-model `C'`, the
disposition coordinate of record.
Source: `faithful.md` FA-9 ("`UDT_{s°,ρ}(d) = Unif argmax_a V_B(C'[d↦a]) =: BR_d(C')`"); answer to
open problem 6 ("Product form is forced by Definition 11's type"); dp-cf-2-007, dp-cf-108
Kind: C
Fidelity: exact
Hyps: (a) `AlmostFair B`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem udtProc_polEv_eq_bestReply (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    udtProc s₀ (polEv U) d = uniformOn (BR C' B d) (BR_nonempty C' B d) :=
  udtProc_eq_bestReply_of_valueFaithful B C' s₀ (polEv U) (polEv_valueFaithful U B C' s₀ hB hcal h)

/-- The support of `UDT_{s°,pol}(d)` is exactly `BR_d(C')` (the form `TUdt` reads).
Source: `faithful.md` FA-9
Kind: L -/
theorem udtProc_polEv_w_pos_iff (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) (a : acts d) :
    0 < (udtProc s₀ (polEv U) d).w a ↔ a ∈ BR C' B d := by
  rw [udtProc_polEv_eq_bestReply U B C' s₀ hB hcal h, uniformOn_w]
  split_ifs with ha
  · simp only [ha, iff_true]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr (BR_nonempty C' B d))
  · simp [ha]

end pol

end Cleanroom.Decision.DpFaithfulUdt
