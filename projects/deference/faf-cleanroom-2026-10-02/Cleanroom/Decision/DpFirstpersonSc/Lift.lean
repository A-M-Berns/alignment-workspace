import Cleanroom.Decision.DpFirstpersonSc.Audit
import Cleanroom.Udt.UdtSupercondition.DZ

/-!
# Proposition 2's lift as a conditioning model (AN-1/AN-2/AN-13) — T4 of
[[dp-firstperson-sc-mandate]]

The two readings of AN-1, with `udt-supercondition`'s objects and nothing redefined:

* **Reading (a)** (`liftModelA`): SC Def 1.1 with `L := Leaves(B)`, `μ := runPMF C B`,
  `p = p' := world B`, `ev := occ(d)`, prior `ν = (priorState C B).P`, posterior the per-run
  state `occState C B d` — exists for every `C, B, d` with `μ(occ(d)) > 0`. The posterior equals a
  given `P_{s_d}` **iff** per-run clause 1 (`liftModelA_post_iff`); this is the bridge
  dossier's T9 dictionary verbatim (one row, two sources).
* **Reading (b)** (`liftModelB_iff`): a model from `P_{s_d}` (on `Ω`) to the lifted state
  `μ(· | occ(d))` (on `Leaves`) that is compatible with the common information
  `lambdaCI = (Ω, id, λ)` *and has trivial evidence* (`μ(ev) = 1`, AN-1's "trivial evidence,
  density `≡ 1`, `B = 1`") exists iff per-run clause 1: `⟹` by SC Thm 2.4 (⇒)
  (`compatible_boundedDensity`) with the bound `1`, `⟸` by exhibiting the model.
* **AN-2** (`perRunClause1_boundedDensity`): per-run clause 1 at `d` gives SC's D–Z bound
  `‖dP_{s_d}/dν‖_∞ ≤ 1/μ(occ(d))`, by `compatible_boundedDensity` on reading (a) with `idCI Ω`.
  Honesty note: the inequality is one line from clause 1 directly
  (`perRunClause1_atom_le`); what the SC route adds is the placement, not the bound. It is
  **necessary only** and reverse absolute continuity fails for every no-doubt state
  (`not_sameOntology_of_zero`; `mug1` instances in `WitnessesLift.lean`).
* **AN-13 placements** (`liftSameOntology`): one same-ontology model on the run space with the
  evidence as parameter — `⊤` (Definition 11, `liftSameOntology_univ`), `λ⁻¹O_d` (Definition 8,
  `pushdownDistr_condDistr_worldEv`), `occ(d)` (Definition 13 per-run); Definition 9 is the same
  family under `C[d ↦ m]`; Definition 10 at `ν_C(O_d) = 0` is outside (Told-You-So,
  `WitnessesLift.lean`).

Vocabulary (dp-cf-2-064): SC's "prior" below is the *earlier belief* of a model — here the
world's statistics `ν`, never v2's `s₀`; "compatible"/"same ontology" are SC's.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Rational helpers -/

section helpers

variable {α : Type} [Fintype α]

/-- Two distributions with `Q ≤ P` atomwise are equal (both sum to one).
Source: none: infrastructure. Kind: L -/
theorem FinDistr.eq_of_w_le {Q P : FinDistr ℚ α} (h : ∀ x, Q.w x ≤ P.w x) : Q = P := by
  apply FinDistr.ext'
  have hsum : ∑ x, Q.w x = ∑ x, P.w x := by rw [Q.sum_one, P.sum_one]
  exact fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => h x)).mp hsum x (Finset.mem_univ x)

/-- `BoundedDensity` with bound `1` across the bridge forces equality.
Source: none: infrastructure. Kind: L -/
theorem toPMF_eq_of_boundedDensity_one {Q P : FinDistr ℚ α}
    (h : BoundedDensity (toPMF Q) (toPMF P) 1) : Q = P := by
  have h1 : BoundedDensity (toPMF Q) (toPMF P) (ENNReal.ofReal (1 : ℚ)) := by
    simpa using h
  rw [boundedDensity_toPMF_iff Q P 1 zero_le_one] at h1
  exact FinDistr.eq_of_w_le fun x => by simpa using h1 x

/-- No same-ontology model from `P` to `P'` when `P` has a zero that `P'` charges (finite
Diaconis–Zabell, contrapositive): reverse absolute continuity fails.
Source: `anticipation.md` AN-2(iii), AN-11 ("reverse absolute continuity fails for every
no-doubt state"); `udt-supercondition` `sameOntology_condModel_iff_of_fintype`
Kind: L -/
theorem not_sameOntology_of_zero (P P' : FinDistr ℚ α) (x : α) (h0 : P.w x = 0)
    (hpos : 0 < P'.w x) : ¬ Nonempty (SameOntologyModel (toPMF P) (toPMF P')) := by
  rw [sameOntology_condModel_iff_of_fintype, toPMF_ac_iff]
  intro h
  exact hpos.ne' (h x h0)

end helpers

/-! ## The run law conditioned and pushed down -/

section pushdown

variable (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)

/-- `λ_* μ = ν`: the world marginal of the run law is the prior state's probability.
Source: `anticipation.md` AN-1 reading (a) ("`p_* L = ν`")
Kind: L -/
theorem pushdownDistr_leafDistr_eq_priorState_P :
    pushdownDistr B (leafDistr C B) = (priorState C B).P := by
  apply FinDistr.ext'
  intro ω
  rw [pushdownDistr_leafDistr_w]
  show nu C B {ω} = if ω ∈ Finset.univ then nu C B {ω} / nu C B Finset.univ else 0
  rw [if_pos (Finset.mem_univ ω), nu_univ, div_one]

/-- `λ_* μ(· | occ(d)) = P^{sl}_{s_d}`: the pushdown of the occurrence-conditioned run law is the
per-run state's probability (D5).
Source: `firstperson.md` D5 ("`P^{sl}_{s_d} = λ_* μ_C(· | occ(d))`")
Kind: L -/
theorem pushdownDistr_condDistr_occ (d : ι) (h : 0 < Tree.mass C B (occ d B)) :
    pushdownDistr B (condDistr (leafDistr C B) (occ d B) h) = (occState C B d h).P := by
  apply FinDistr.ext'
  intro ω
  show probOf (condDistr (leafDistr C B) (occ d B) h) (worldEv B {ω}) =
    Tree.mass C B (occEv B d {ω}) / Tree.mass C B (occ d B)
  rw [probOf_condDistr]
  rfl

/-- `λ_* μ(· | λ⁻¹O) = ν(· | O)`: conditioning the run law on a world event and pushing down is
the strictly calibrated state's probability (Definition 8 as a same-ontology model).
Source: `anticipation.md` AN-13 ("Def 8: Level 3, evidence `O_d`")
Kind: L -/
theorem pushdownDistr_condDistr_worldEv (O : Finset Ω) (hO : 0 < nu C B O)
    (h : 0 < probOf (leafDistr C B) (worldEv B O)) :
    pushdownDistr B (condDistr (leafDistr C B) (worldEv B O) h) = (calibratedState C B O hO).P := by
  apply FinDistr.ext'
  intro ω
  show probOf (condDistr (leafDistr C B) (worldEv B O) h) (worldEv B {ω}) =
    if ω ∈ O then nu C B {ω} / nu C B O else 0
  rw [probOf_condDistr]
  have hev : worldEv B {ω} ∩ worldEv B O = worldEv B ({ω} ∩ O) := by
    ext ℓ; simp [worldEv]
  rw [hev]
  by_cases hω : ω ∈ O
  · rw [if_pos hω, Finset.singleton_inter_of_mem hω]; rfl
  · rw [if_neg hω, Finset.singleton_inter_of_notMem hω]
    have hempty : worldEv B (∅ : Finset Ω) = ∅ := by ext ℓ; simp [worldEv]
    show Tree.mass C B (worldEv B ∅) / _ = 0
    rw [hempty]
    simp [Tree.mass]

/-- Conditioning on the whole run space does nothing. Source: none: infrastructure. Kind: L -/
theorem condDistr_univ (P : FinDistr ℚ B.Leaves) (h : 0 < probOf P Finset.univ) :
    condDistr P Finset.univ h = P := by
  apply FinDistr.ext'
  intro ℓ
  rw [condDistr_w, if_pos (Finset.mem_univ ℓ), probOf_univ, div_one]

end pushdown

/-! ## Reading (a): the lift as a same-ontology conditioning model -/

section readingA

variable (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)

/-- **AN-1 reading (a) / dossier T9**: Proposition 2's lift as SC Def 1.1 — `L := Leaves(B)`,
`μ := μ_{B,C}`, `p = p' := λ`, evidence `occ(d)`; prior the world's statistics `ν`, posterior
the per-run state `occState C B d`. The fields are `runPMF_map_world` and
`pushdownDistr_condDistr_occ` through the bridge.
Source: `anticipation.md` AN-1 reading (a); `bridge-dossier.md` T9 (the exact dictionary);
[[decision-problems-v2]] Proposition 2
Kind: C
Fidelity: exact (finite regime, Definition 6)
Hyps: (a) `0 < μ(occ(d))` -/
noncomputable def liftModelA (h : 0 < Tree.mass C B (occ d B)) :
    CondModel (toPMF (priorState C B).P) (toPMF (occState C B d h).P) where
  L := B.Leaves
  μ := runPMF C B
  p := world B
  p' := world B
  ev := (↑(occ d B) : Set B.Leaves)
  hp := by rw [runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P]
  hev := (mass_runPMF_pos_iff C B _).mpr h
  hp' := by
    rw [condOn_runPMF C B _ h, toPMF_map_world, pushdownDistr_condDistr_occ]

/-- Reading (a) is compatible with the identity common information (same ontology `𝓔` at both
ends — SC Level 3, `anticipation.md` Dead 4).
Source: `anticipation.md` AN-13 ("Def 13 per-run: Level 3 … `p = p' = λ⁻¹`")
Kind: L -/
theorem liftModelA_compatible_idCI (h : 0 < Tree.mass C B (occ d B)) :
    Compatible (liftModelA C B d h) (idCI Ω) := rfl

/-- `P_{s_d} = P^{sl}` iff per-run clause 1 at `d`. Source: [[decision-problems-v2]] Definition 13.
Kind: L -/
theorem P_eq_occState_iff_perRunClause1At (s : ι → State Ω ℚ) (h : 0 < Tree.mass C B (occ d B)) :
    (s d).P = (occState C B d h).P ↔ PerRunClause1At s C B d := by
  have hpr : ∀ X, (occState C B d h).pr X =
      Tree.mass C B (worldEv B X ∩ occ d B) / Tree.mass C B (occ d B) := fun X => occState_pr C B d h X
  constructor
  · intro hP X
    have := hpr X
    simp only [State.pr] at this ⊢
    rw [hP, this]
    exact div_mul_cancel₀ _ h.ne'
  · intro h1
    apply FinDistr.ext'
    intro ω
    have := h1 {ω}
    have hp := hpr {ω}
    simp only [State.pr, probOf_singleton] at this hp ⊢
    rw [hp, ← this]
    exact (mul_div_cancel_right₀ _ h.ne').symm

/-- **T4(a): the lift's posterior is `P_{s_d}` iff per-run clause 1 at `d`** — Proposition 2's
"`λ_* P_{s'_d} = P_{s_d}` *is* the per-run SSC hypothesis", as a statement about SC's model.
Source: `anticipation.md` AN-1 reading (a) ("`p'_* L(· | l̄) = P_{s_d}` iff per-run SSC clause 1
at `d`"); [[decision-problems-v2]] Proposition 2
Kind: C
Fidelity: exact (`P`-clause; the `V`-clause is not an SC object)
Hyps: (a) `0 < μ(occ(d))` -/
theorem liftModelA_post_iff (s : ι → State Ω ℚ) (h : 0 < Tree.mass C B (occ d B)) :
    (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)).map
        (world B) = toPMF (s d).P ↔
      PerRunClause1At s C B d := by
  rw [condOn_runPMF C B _ h, toPMF_map_world, pushdownDistr_condDistr_occ, toPMF_eq_iff,
    eq_comm]
  exact P_eq_occState_iff_perRunClause1At C B d s h

/-- Reading (a) with the audited state in the posterior slot: the model exists exactly under
per-run clause 1 (packaged for AN-2).
Source: `anticipation.md` AN-1 reading (a)
Kind: D -/
noncomputable def liftModelA' (s : ι → State Ω ℚ) (h : 0 < Tree.mass C B (occ d B))
    (h1 : PerRunClause1At s C B d) :
    CondModel (toPMF (priorState C B).P) (toPMF (s d).P) where
  L := B.Leaves
  μ := runPMF C B
  p := world B
  p' := world B
  ev := (↑(occ d B) : Set B.Leaves)
  hp := by rw [runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P]
  hev := (mass_runPMF_pos_iff C B _).mpr h
  hp' := (liftModelA_post_iff C B d s h).mpr h1

/-- **AN-2 / dossier T9's consequence: per-run clause 1 forces SC's D–Z bound**
`P_{s_d} ≤ ν / μ(occ(d))` atomwise, by SC Thm 2.4 (⇒) (`compatible_boundedDensity`) applied to
reading (a) with `idCI`. The bound is one line from clause 1 directly
(`perRunClause1_atom_le`): the SC route places it, it does not strengthen it. Necessary only:
on `mug1` the tails-certain state fails it (`2 > 1`) and reverse absolute continuity fails
(`WitnessesLift.lean`).
Source: `anticipation.md` AN-2(ii) ("SC Thm 2.4's necessity direction gives `P_{s_d} ≪ ν` with
`‖dP_{s_d}/dν‖_∞ ≤ 1/μ(occ(d))`"); `bridge-dossier.md` T9
Kind: C
Fidelity: exact
Hyps: (a) `0 < μ(occ(d))`, (a) `PerRunClause1At s C B d` -/
theorem perRunClause1_boundedDensity (s : ι → State Ω ℚ) (h : 0 < Tree.mass C B (occ d B))
    (h1 : PerRunClause1At s C B d) :
    BoundedDensity (toPMF (s d).P) (toPMF (priorState C B).P)
      (ENNReal.ofReal ((Tree.mass C B (occ d B) : ℚ) : ℝ))⁻¹ := by
  have := compatible_boundedDensity (m := liftModelA' C B d s h h1) (ci := idCI Ω) rfl
  rw [idCI_C₁, idCI_C₂] at this
  have hm : mass (liftModelA' C B d s h h1).μ (liftModelA' C B d s h h1).ev =
      ENNReal.ofReal ((Tree.mass C B (occ d B) : ℚ) : ℝ) := mass_runPMF C B (occ d B)
  rwa [hm] at this

/-- The D–Z bound in rational atom form, proved from clause 1 alone (the honest one-liner).
Source: `anticipation.md` AN-2(ii)
Kind: L -/
theorem perRunClause1_atom_le (s : ι → State Ω ℚ) (h1 : PerRunClause1At s C B d) (ω : Ω) :
    (s d).P.w ω * Tree.mass C B (occ d B) ≤ nu C B {ω} := by
  have := h1 {ω}
  simp only [State.pr, probOf_singleton] at this
  rw [this]
  exact Tree.mass_mono C B Finset.inter_subset_left

end readingA

/-! ## Reading (b): compatibility with `(𝓔, id, λ)` -/

section readingB

variable (B : Tree Ω ι acts ℚ)

/-- **The common information of reading (b)**: `Ĉ := 𝓔`, `c := id`, `c' := λ`.
Source: `anticipation.md` AN-1 reading (b) ("`Ĉ = 𝓔`, `c = id`, `c' = λ⁻¹`")
Kind: D -/
abbrev lambdaCI : CommonInfo Ω B.Leaves := { C := Ω, c := id, c' := world B }

variable (C : Proc ι acts ℚ) (d : ι)

/-- **T4(b), AN-1 reading (b)**: a conditioning model from `P_{s_d}` (on `𝓔`) to the lifted
state `μ(· | occ(d))` (on `2^{Leaves}`), `λ`-compatible and with trivial evidence, exists iff
per-run clause 1 at `d`. `⟹`: SC Thm 2.4 (⇒) with bound `1/μ(ev) = 1` makes `λ_*(lifted) ≤ P_{s_d}`
atomwise, hence equal; `⟸`: the model `(Leaves, μ(· | occ), λ, id, ⊤)` itself.
Source: `anticipation.md` AN-1 reading (b) ("compatible iff `λ_* P_{s'_d} = P_{s_d}` … a
compatible refinement with trivial evidence, density `≡ 1`, `B = 1`")
Kind: P
Fidelity: exact (the "trivial evidence" clause is AN-1's; without it compatibility alone does not
pin the posterior's marginal)
Hyps: (a) `0 < μ(occ(d))` -/
theorem liftModelB_iff (s : ι → State Ω ℚ) (h : 0 < Tree.mass C B (occ d B)) :
    (∃ m : CondModel (toPMF (s d).P)
        (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)),
        Compatible m (lambdaCI B) ∧ mass m.μ m.ev = 1) ↔
      PerRunClause1At s C B d := by
  constructor
  · rintro ⟨m, hm, hev⟩
    have hbd := compatible_boundedDensity hm
    rw [hev, inv_one] at hbd
    have hC₁ : (lambdaCI B).C₁ (toPMF (s d).P) = toPMF (s d).P := PMF.map_id _
    have hC₂ : (lambdaCI B).C₂ (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves)
        ((mass_runPMF_pos_iff C B _).mpr h)) = toPMF (occState C B d h).P := by
      show (condOn (runPMF C B) _ _).map (world B) = _
      rw [condOn_runPMF C B _ h, toPMF_map_world, pushdownDistr_condDistr_occ]
    rw [hC₁, hC₂] at hbd
    have := toPMF_eq_of_boundedDensity_one hbd
    exact (P_eq_occState_iff_perRunClause1At C B d s h).mp this.symm
  · intro h1
    refine ⟨{ L := B.Leaves
              μ := condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)
              p := world B
              p' := id
              ev := Set.univ
              hp := (liftModelA_post_iff C B d s h).mpr h1
              hev := by rw [mass_univ]; exact zero_lt_one
              hp' := by rw [condOn_univ, PMF.map_id] }, rfl, ?_⟩
    exact mass_univ _

end readingB

/-! ## F5: compatibility alone does not pin the posterior's marginal -/

section f5

variable (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)

/-- **Compatibility alone does not pin the posterior's marginal (F5, the general half)**: on every
tree with `μ(occ(d)) > 0`, the model `(Leaves, μ, λ, id, occ(d))` is a `λ`-compatible conditioning
model from the *prior* state to the lifted state `μ(· | occ(d))` — with evidence `occ(d)`, of mass
`μ(occ(d))`, not `1`. Where the prior state fails per-run clause 1 (`anThree`,
`WitnessesAn3.lean` `anThree_priorState_not_clause1`) this is a `λ`-compatible model whose prior
is not `λ_*` of its posterior: `liftModelB_iff`'s `⟹` needs its clause `mass m.μ m.ev = 1`.
Source: `anticipation.md` AN-1 reading (b); findings F5; audit r1 adversarial N9
Kind: N+
Fidelity: exact
Hyps: (a) `0 < μ(occ(d))` -/
theorem lambdaCI_compatible_model_exists (h : 0 < Tree.mass C B (occ d B)) :
    ∃ m : CondModel (toPMF (priorState C B).P)
        (condOn (runPMF C B) (↑(occ d B) : Set B.Leaves) ((mass_runPMF_pos_iff C B _).mpr h)),
      Compatible m (lambdaCI B) :=
  ⟨{ L := B.Leaves
     μ := runPMF C B
     p := world B
     p' := id
     ev := (↑(occ d B) : Set B.Leaves)
     hp := by rw [runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P]
     hev := (mass_runPMF_pos_iff C B _).mpr h
     hp' := PMF.map_id _ }, rfl⟩

end f5

/-! ## AN-13: the v2 senses as same-ontology models on the run space -/

section placements

variable (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)

/-- **One same-ontology model, the evidence as parameter**: the run space with `p := λ`, prior
`ν`, posterior `λ_* μ(· | E)`. Definition 11 is `E = ⊤`, Definition 8 is `E = λ⁻¹O_d`,
Definition 13 (per-run) is `E = occ(d)`; Definition 9 is the same with `C[d ↦ m]` for `C` (a
family indexed by the self-model, absolutely continuous w.r.t. `ν_{C[d↦m]}`, not `ν_C`).
Source: `anticipation.md` AN-13 ("every v2 sense lives in SC's evidence-constraint landscape with
the model held at Level 3 and the prior fixed to the world")
Kind: D
Fidelity: exact (finite regime)
Hyps: (a) `0 < μ(E)` -/
noncomputable def liftSameOntology (E : Finset B.Leaves) (hE : 0 < Tree.mass C B E) :
    SameOntologyModel (toPMF (priorState C B).P)
      (toPMF (pushdownDistr B (condDistr (leafDistr C B) E hE))) where
  L := B.Leaves
  μ := runPMF C B
  p := world B
  ev := (↑E : Set B.Leaves)
  hp := by rw [runPMF_map_world, pushdownDistr_leafDistr_eq_priorState_P]
  hev := (mass_runPMF_pos_iff C B _).mpr hE
  hp' := by rw [condOn_runPMF C B _ hE, toPMF_map_world]

/-- Definition 11's placement: evidence `⊤`, posterior `ν` itself (density `1`).
Source: `anticipation.md` AN-13 ("Def 11: Level 3, `B = 1`, evidence `⊤`, density `≡ 1`")
Kind: L -/
theorem liftSameOntology_univ_post :
    pushdownDistr B (condDistr (leafDistr C B) Finset.univ
      (by rw [probOf_univ]; exact zero_lt_one)) = (priorState C B).P := by
  rw [condDistr_univ, pushdownDistr_leafDistr_eq_priorState_P]

/-- Definition 13's placement: evidence `occ(d)`, posterior the per-run state.
Source: `anticipation.md` AN-13 ("Def 13 per-run: Level 3 … evidence `occ(d)`")
Kind: L -/
theorem liftSameOntology_occ_post (d : ι) (h : 0 < Tree.mass C B (occ d B)) :
    pushdownDistr B (condDistr (leafDistr C B) (occ d B) h) = (occState C B d h).P :=
  pushdownDistr_condDistr_occ C B d h

end placements

end Cleanroom.Decision.DpFirstpersonSc
