import Cleanroom.Decision.DpCartesianFrames.ChuWitnesses
import Cleanroom.Found.DpCoreTree.Shadow

/-!
# CFF-8: "spurious queries are frame-invisible" is convention-dependent

Package `dp-cartesian-frames`, file 16 (repair round 1; mandate T8(c)).

The tree: a fair recorded coin followed by an inert query of the single point (`coinQ`, both
edges to the same leaf). Relocating the point to the root puts "a fresh point above two copies
of the recorded coin" (CFF-8's tree).

* **Lazily** the relocated frame is **not** biextensionally equivalent to `Fr coinQ`
  (`lazyReloc_coinQ_not_biextEquiv_fr`): its two rows read different coin copies and differ on
  the off-diagonal column (tails in the first copy, heads in the second) —
  `lazyReloc_coinQ_not_rows_agree` — while every row of `Fr coinQ` is the same function of the
  column (`coinQ_rows_agree`), and "all rows agree" is `PowerlessOutside _ ∅`, a biextensional
  invariant. This is the refutation row for P1 CF-7 ("spurious queries are frame-invisible").
* **Under identification** the rows coincide and the frame is `≃ᵇ Fr coinQ`
  (`ident_coinQ_biextEquiv_fr`, UN-7's instance; `ident_coinQ_rows_agree`).
* **Lazily for chance-free subtrees** the inserted query is invisible
  (`fr_insertQuery_biextEquiv_of_chanceFree`): with no chance node below it, the copies' profiles
  are a singleton, so `Fr (insertQuery d B) ≃ᵇ Fr B`. CFF-8's surviving neighbour.
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames CategoryTheory
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-! ### The general two-branch computation -/

section twoBranchReloc

variable {Ω A : Type} [Fintype A] [DecidableEq A]

/-- The coin coordinate of a profile of a two-branch tree resolved at its single point.
Source: none: infrastructure
Kind: D -/
def sliceCoinTB (β : FinDistr ℚ (Fin 2)) (φ : Fin 2 → A → Ω × ℚ) (σ : (d : ↥U1) → A)
    (ε : ChanceProfile (resolve U1 σ (twoBranch β φ))) : Fin 2 :=
  Prod.fst (ε : Fin 2 × _)

/-- **The world of the lazy relocated two-branch tree at any column**: the run of `ρ` reads the
copy in branch `σ_ρ := ρ (inr ())`, whose coin is that slice's coin, and lands at `φ coin (σ_ρ d)`.
Source: cf-frontier CFF-8 (line 72: "lazy rows `(H,H,T,T)`, `(H,T,H,T)` over `{H,T}²`");
universal UN-6 (line 69)
Kind: P
Fidelity: exact
Hyps: none -/
theorem relocTwoBranch_world (β : FinDistr ℚ (Fin 2)) (φ : Fin 2 → A → Ω × ℚ)
    (ρ : (p : Unit ⊕ Unit) → actsR (fun _ => A) U1 p)
    (ε' : ChanceProfile (relocRoot U1 (twoBranch β φ))) :
    ((Fr (relocRoot U1 (twoBranch β φ))).outcome ρ ε').1.1 =
      (φ (sliceCoinTB β φ (ρ (.inr ())) (ε' (ρ (.inr ())))) (ρ (.inr ()) u1)).1 := by
  show (world (resolveW U1 (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) (twoBranch β φ))
    (runLeaf ρ (resolveW U1 (fun ω => (ω, ρ (.inr ()))) (ρ (.inr ())) (twoBranch β φ))
      (ε' (ρ (.inr ()))))).1 = _
  rw [world_resolveW, leafMapW_twoBranch]
  rfl

end twoBranchReloc

/-! ### The coin with an inert query -/

/-- The recorded fair coin followed by an inert query of the single point: both edges lead to a
leaf recording the coin, payoff `0`.
Source: cf-frontier CFF-8 (line 72: "a fresh point above two copies of a recorded coin" — before
relocation, the point sits below one copy)
Kind: D -/
def coinQ : Tree Bool Unit (fun _ => Act2) ℚ := twoBranch FinDistr.fair fun i _ => (coinOf i, 0)

/-- Every row of `Fr coinQ` is the same function of the column (the query is inert):
"powerless outside `∅`".
Source: cf-frontier CFF-8 (line 72: "identified: rows coincide, `1 × 2`")
Kind: L -/
theorem coinQ_rows_agree : PowerlessOutside (Fr coinQ) ∅ := by
  rintro ⟨i, f⟩ π π' _
  rfl

/-- A profile of the resolved `coinQ` with a prescribed coin.
Source: none: infrastructure
Kind: D -/
noncomputable def coinQSlice (σ : (d : ↥U1) → Act2) (c : Fin 2) :
    ChanceProfile (resolve U1 σ coinQ) := by
  show Fin 2 × ((i : Fin 2) → ChanceProfile (resolveW U1 (fun ω => (ω, σ)) σ
    (Tree.decision (acts := fun _ : Unit => Act2) () fun _ => Tree.leaf (coinOf i) 0)))
  exact ⟨c, fun _ => Classical.arbitrary _⟩

/-- **The off-diagonal column**: the copy below the `a`-answer shows tails, the copy below the
`b`-answer shows heads (a decorrelated counterfactual coin — the lazy seeding's extra column).
Source: cf-frontier CFF-8 (line 72); universal UN-19 (line 95: "the lazy relocated frame's
off-diagonal columns (decorrelated counterfactual coins)")
Kind: D -/
noncomputable def coinQOffDiag : ChanceProfile (relocRoot U1 coinQ) :=
  fun σ => coinQSlice σ (if σ u1 = Act2.a then 0 else 1)

/-- **Lazily the two rows of the relocated `coinQ` differ**: on the off-diagonal column the
`a`-row reads tails and the `b`-row heads. So the lazy relocated frame is not "all rows agree".
Source: cf-frontier CFF-8 (line 72: "lazy rows `(H,H,T,T)`, `(H,T,H,T)` … `2 × 4 ≄ 1 × 2`")
Kind: N+
Fidelity: exact -/
theorem lazyReloc_coinQ_not_rows_agree :
    ¬ PowerlessOutside ((Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 coinQ))) ∅ := by
  intro h
  have h0 := h coinQOffDiag (liftFun U1 fun _ => Act2.a) (liftFun U1 fun _ => Act2.b)
    (Set.notMem_empty _)
  have h1 : ((Fr (relocRoot U1 coinQ)).outcome (liftFun U1 fun _ => Act2.a) coinQOffDiag).1.1 =
      ((Fr (relocRoot U1 coinQ)).outcome (liftFun U1 fun _ => Act2.b) coinQOffDiag).1.1 :=
    congrArg (fun w : Bool × ℚ => w.1) h0
  have ha := relocTwoBranch_world FinDistr.fair (fun i _ => (coinOf i, 0))
    (liftFun U1 fun _ => Act2.a) coinQOffDiag
  have hb := relocTwoBranch_world FinDistr.fair (fun i _ => (coinOf i, 0))
    (liftFun U1 fun _ => Act2.b) coinQOffDiag
  have h2 : (true : Bool) = false := ha.symm.trans (h1.trans hb)
  exact Bool.noConfusion h2

/-- **CFF-8, the refutation row for P1 CF-7 ("spurious queries are frame-invisible"), lazy**:
the coarsened lazy frame of the relocated `coinQ` is not biextensionally equivalent to
`Fr coinQ` — "all rows agree" is a biextensional invariant that holds for the latter and fails
for the former.
Source: cf-frontier CFF-8 (line 72: "collapse `2 × 4 ≄ 1 × 2` … P1 CF-7 is WOUNDED — … false
lazily"); mandate T8(c)
Kind: N+
Fidelity: exact (the lazy frame of the relocation output, coarsened; the matrices are never
transcribed) -/
theorem lazyReloc_coinQ_not_biextEquiv_fr :
    ¬ ((Frame.mapWorlds (Prod.map Prod.fst id)).obj (Fr (relocRoot U1 coinQ)) ≃ᵇ Fr coinQ) :=
  fun h => lazyReloc_coinQ_not_rows_agree
    ((powerlessOutside_iff_of_biextEquiv h ∅).mpr coinQ_rows_agree)

/-- **CFF-8, the surviving neighbour under identification**: the identified frame of the
relocated `coinQ` is `≃ᵇ Fr coinQ` (UN-7's instance) — the spurious query is invisible.
Source: cf-frontier CFF-8 (line 72: "identified: rows coincide, `1 × 2` … true under
identification")
Kind: C
Fidelity: exact
Hyps: none -/
theorem ident_coinQ_biextEquiv_fr :
    (Frame.mapWorlds (Prod.map Prod.fst id)).obj (FrIdent U1 coinQ) ≃ᵇ Fr coinQ :=
  mapWorlds_frIdent_biextEquiv_fr U1 coinQ

/-- Under identification the rows of the relocated `coinQ` coincide.
Source: cf-frontier CFF-8 (line 72: "identified: rows coincide")
Kind: C
Fidelity: exact
Hyps: none -/
theorem ident_coinQ_rows_agree :
    PowerlessOutside ((Frame.mapWorlds (Prod.map Prod.fst id)).obj (FrIdent U1 coinQ)) ∅ :=
  (powerlessOutside_iff_of_biextEquiv ident_coinQ_biextEquiv_fr ∅).mpr coinQ_rows_agree

/-! ### Chance-free subtrees: the inserted query is invisible even lazily -/

section chanceFree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- A tree with no chance node.
Source: cf-frontier CFF-8 (line 72: "chance-free identical subtrees"); none otherwise:
infrastructure
Kind: D -/
def ChanceFree : Tree Ω ι acts K → Prop
  | .leaf _ _ => True
  | .chance _ _ _ => False
  | .decision _ child => ∀ a, ChanceFree (child a)

/-- A chance-free tree has a single chance profile.
Source: none: infrastructure
Kind: L -/
theorem ChanceFree.subsingleton :
    (B : Tree Ω ι acts K) → ChanceFree B → Subsingleton (ChanceProfile B)
  | .leaf _ _, _ => inferInstanceAs (Subsingleton Unit)
  | .chance _ _ _, h => h.elim
  | .decision _ child, h => by
      haveI : ∀ a, Subsingleton (ChanceProfile (child a)) :=
        fun a => ChanceFree.subsingleton (child a) (h a)
      exact inferInstanceAs (Subsingleton ((a : _) → ChanceProfile (child a)))

/-- **CFF-8's other surviving neighbour**: inserting a query of `d` above a chance-free tree is
frame-invisible even lazily — `Fr (insertQuery d B) ≃ᵇ Fr B` — because the copies below the
inserted node carry a single profile, so the lazy seeding has no off-diagonal column to add.
Source: cf-frontier CFF-8 (line 72: "true … for chance-free identical subtrees"); mandate T8(c)
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_insertQuery_biextEquiv_of_chanceFree (d : ι) [Nonempty (acts d)]
    (B : Tree Ω ι acts K) (hB : ChanceFree B) : Fr (insertQuery d B) ≃ᵇ Fr B := by
  haveI := hB.subsingleton B
  refine Frame.biextEquiv_iff_homotopyEquiv.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact
      { agent := id
        env := fun ε => fun _ => ε
        adjoint := fun _ _ => rfl }
  · exact
      { agent := id
        env := fun ε => ε (Classical.arbitrary _)
        adjoint := fun π ε => by
          show readout B (runLeaf π B (ε _)) = readout B (runLeaf π B (ε (π d)))
          rw [Subsingleton.elim (ε _) (ε (π d))] }
  · intro _ _; rfl
  · intro _ _; rfl

end chanceFree

end Cleanroom.Decision.DpCartesianFrames
