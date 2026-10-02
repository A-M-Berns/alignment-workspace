import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Construction.DeductiveDovetail
import LogicalInduction.Construction.Conditioning.Presentation

/-!
# `bli-rvc-ui` · Ui/Defs: universal instantiation as a family plus a process

**Design decision 5 of the mandate.** FAF's `Sentence` is propositional; a first-order universal
enters it as an opaque prime atom (`paperPrimeDecompose`, `Construction/Paper/FirstOrder.lean`),
and its instances are *other* sentences. Universal instantiation is therefore a **family** — a
universal-role sentence `u` and an instance family `inst : ℕ → Sentence` — **plus the process
that ties them**: `AxProcess F` publishes `u 🡒 inst i` for `i ≤ n` on day `n` (schema 1 of Soto's
`Ax` for one universal; a list of families is a union of these; schema 2 is not here).

* `UIAt V F C` — exact UI at one valuation on the instances `C` (the finite-day object).
* `UILimit P F` — UI for FAF's limiting belief `limitingBelief P` (the object
  `lic_limitCoherence` talks about): the definition of record for D-UI in the limit.
* `UITwoSided P F` — the two-sided clause of bli-paper-2-026, **a refutation target only**
  (`Ui/Limit.lean`, `twoSided_ui_unsat`); never a definition of record.
* `AxProcess`, its monotonicity and computability (from a primitive recursive instance family),
  and `setAtom` — the one-atom override of a world that gives every union `DP ∪ AxProcess F`
  its consistent worlds (with `u` false) as soon as the base process never mentions `u`'s atom.

**Vacuity guard** (mandate §5): a universal atom with no process link makes `UIAt`/`UILimit`
either trivially false or unrelated; every UI theorem of this package is over `DP.union (AxProcess F)`
or over `paperUI φ` with `paperDP T` (`Ui/Paper.lean`).
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset

/-! ## The family and the process -/

/-- A **UI family**: a universal-role sentence and its instance family.
Source: mandate design decision 5; bli-soto-a-013; bli-paper-049
Kind: D
Fidelity: exact -/
structure UIFamily where
  /-- The universal-role sentence `∀x φ(x)` (an opaque prime, or a fresh atom). -/
  u : Sentence
  /-- The instance family `c ↦ φ(c)`. -/
  inst : ℕ → Sentence

/-- **Soto's schema 1 as a deductive process**: on day `n` the implications `u 🡒 inst i`, `i ≤ n`.
Source: Soto PDF 07, Step 1 (schema 1 of `Ax`, one universal); bli-soto-a-054
Kind: D
Fidelity: exact (schema 1; schema 2 is stretch S3, not here) -/
def AxProcess (F : UIFamily) : DeductiveProcess where
  D n := (Finset.range (n + 1)).image (fun i => F.u 🡒 F.inst i)
  mono n := by
    intro φ hφ
    rw [Finset.mem_image] at hφ ⊢
    obtain ⟨i, hi, rfl⟩ := hφ
    exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), rfl⟩

/-- `axProcess_stage`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma axProcess_stage (F : UIFamily) (n : ℕ) :
    (AxProcess F).D n = (Finset.range (n + 1)).image (fun i => F.u 🡒 F.inst i) := rfl

/-- `u 🡒 inst c` is in stage `n` of the schema process for every `c ≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma imp_mem_axProcess (F : UIFamily) {c n : ℕ} (h : c ≤ n) :
    F.u 🡒 F.inst c ∈ (AxProcess F).D n := by
  rw [axProcess_stage, Finset.mem_image]
  exact ⟨c, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every sentence of a schema stage is an implication `u 🡒 inst i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_axProcess_iff (F : UIFamily) {n : ℕ} {φ : Sentence} :
    φ ∈ (AxProcess F).D n ↔ ∃ i ≤ n, F.u 🡒 F.inst i = φ := by
  rw [axProcess_stage, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- A world holds a whole stage of the schema process iff it holds `u 🡒 inst i` for all `i ≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWith_axProcess_iff (F : UIFamily) (v : PCWorld) (n : ℕ) :
    v.ConsistentWith ((AxProcess F).D n) ↔ ∀ i ≤ n, v.Holds F.u → v.Holds (F.inst i) := by
  constructor
  · intro h i hi hu
    exact (h _ (imp_mem_axProcess F hi)) hu
  · intro h φ hφ
    obtain ⟨i, hi, rfl⟩ := (mem_axProcess_iff F).mp hφ
    exact fun hu => h i hi hu

/-- A world consistent with the completed schema process holds every `u 🡒 inst c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_imp_of_consistentWithTheory_ax {F : UIFamily} {v : PCWorld}
    (hv : v.ConsistentWithTheory (AxProcess F)) (c : ℕ) : v.Holds F.u → v.Holds (F.inst c) :=
  hv c _ (imp_mem_axProcess F le_rfl)

/-- **Schema stages are computable** from a primitive recursive instance family: the stage is the
`toFinset` of a primitive recursive list (FAF's `encode_stage_prim_of_list`, `ofEncodePrim`).
Source: mandate T3.1; Soto PDF 07 ("`Ax` … propositionally consistent", the process must be r.e.)
Kind: C
Fidelity: exact
Hyps: (a) `hinst : Primrec F.inst` is the family's own certificate (discharged by every witness) -/
theorem axProcess_computable (F : UIFamily) (hinst : Primrec F.inst) :
    ComputableDeductiveProcess (AxProcess F) := by
  apply ComputableDeductiveProcess.ofEncodePrim
  refine encode_stage_prim_of_list (l := fun n => (List.range (n + 1)).map (fun i => F.u 🡒 F.inst i))
    ?_ ?_
  · exact Primrec.list_map (Primrec.list_range.comp Primrec.succ)
      ((sentenceImp_prim.comp (Primrec.const F.u) hinst).comp Primrec.snd).to₂
  · intro k
    ext φ
    simp [Finset.mem_image, List.mem_map, List.mem_range]

/-- **The union of a computable base with a schema process is computable** (FAF's
`DeductiveProcessComputation.union_toComputable`).
Source: mandate T3.1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem union_ax_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    (F : UIFamily) (hinst : Primrec F.inst) :
    ComputableDeductiveProcess (DP.union (AxProcess F)) :=
  DeductiveProcessComputation.union_toComputable hDP.nonemptyComputation.some
    (axProcess_computable F hinst).nonemptyComputation.some

/-! ## The finite-day, limit and two-sided forms -/

/-- **Exact universal instantiation at one valuation** on the instances `C`:
`V(∀x φ) ≤ V(φ(c))` for `c ∈ C`.
Source: bli-paper-049; bli-slides-033; [[bli-program-desiderata]] D-UI (finite-day form)
Kind: D
Fidelity: exact (one-sided, as the paper's gloss) -/
def UIAt (V : Sentence → ℝ) (F : UIFamily) (C : Finset ℕ) : Prop :=
  ∀ c ∈ C, V F.u ≤ V (F.inst c)

/-- **Universal instantiation in the limit**, for FAF's limiting belief:
`P∞(∀x φ) ≤ P∞(φ(c))` for every `c`.
Source: bli-paper-049; [[bli-program-desiderata]] D-UI; [[bli-program-construction]] U8
Kind: D
Fidelity: exact -/
def UILimit (P : History) (F : UIFamily) : Prop :=
  ∀ c, limitingBelief P F.u ≤ limitingBelief P (F.inst c)

/-- **Two-sided universal instantiation** `P_n(∀x φ) − P_n(φ(c)) →ₙ 0` for every `c` — the
AI-written clause of bli-paper-2-026. **A refutation target only** (`twoSided_ui_unsat`), never a
definition of record.
Source: bli-paper-2-026 (Phase 2.1's "LUV coherence", clause 3); [[bli-program-construction]] X9
Kind: D
Fidelity: exact (the refuted clause) -/
def UITwoSided (P : History) (F : UIFamily) : Prop :=
  ∀ c, (fun n => P n F.u - P n (F.inst c)) ≈ₙ fun _ => 0

/-! ## One-atom overrides and consistent worlds of the union -/

/-- Override one atom of a world.
Source: none: infrastructure (bli-found's `Extend.override` is the schedule-wide version)
Kind: D
Fidelity: n/a -/
def setAtom (v : PCWorld) (a : ℕ) (b : Prop) : PCWorld :=
  fun a' => if a' = a then b else v a'

/-- `setAtom_apply_self`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma setAtom_apply_self (v : PCWorld) (a : ℕ) (b : Prop) : setAtom v a b a ↔ b := by
  simp [setAtom]

/-- `setAtom_apply_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_apply_of_ne (v : PCWorld) (a : ℕ) (b : Prop) {a' : ℕ} (h : a' ≠ a) :
    setAtom v a b a' ↔ v a' := by
  simp [setAtom, h]

/-- The override holds the overridden atom iff the new value holds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_atom_setAtom (v : PCWorld) (a : ℕ) (b : Prop) :
    (setAtom v a b).Holds (Formula.atom a) ↔ b := by
  rw [PCWorld.holds_atom]
  exact setAtom_apply_self v a b

/-- On a sentence not mentioning the overridden atom, the override agrees with the world.
Source: none: infrastructure (FAF `PCWorld.holds_congr_atomCodes`)
Kind: L
Fidelity: n/a -/
lemma holds_setAtom_of_notMem (v : PCWorld) (a : ℕ) (b : Prop) {φ : Sentence}
    (h : a ∉ sentenceAtomCodes φ) : (setAtom v a b).Holds φ ↔ v.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun _ ha' =>
    setAtom_apply_of_ne v a b (fun heq => h (heq ▸ ha'))

/-- A world consistent with a stage mentioning no atom `a` stays consistent with it after
overriding `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWith_setAtom {v : PCWorld} {D : Finset Sentence} (hv : v.ConsistentWith D)
    {a : ℕ} (hfree : ∀ φ ∈ D, a ∉ sentenceAtomCodes φ) (b : Prop) :
    (setAtom v a b).ConsistentWith D := fun φ hφ =>
  (holds_setAtom_of_notMem v a b (hfree φ hφ)).mpr (hv φ hφ)

/-- **Consistent worlds of `DP ∪ AxProcess F` with the universal false.** If the base process
never mentions the atom `a` of `F.u = atom a`, then every consistent world of a base stage,
overridden at `a` to `False`, is consistent with the same stage of the union and fails `u` — the
`hworld` premise every criterion theorem of this package takes, and the `¬ u` premise
`lic_nonDogmatism_dual` needs.
Source: mandate T3.5 (route: "take `paperDP_hworld`'s world and override the fresh atom to
`false`"); bli-found `Extend.extendBy_consistentWith` (the pattern)
Kind: L
Fidelity: exact -/
theorem union_ax_world_u_false {DP : DeductiveProcess} {F : UIFamily} {a : ℕ}
    (hu : F.u = Formula.atom a) (hfree : ∀ n, ∀ φ ∈ DP.D n, a ∉ sentenceAtomCodes φ)
    {v : PCWorld} {n : ℕ} (hv : v.ConsistentWith (DP.D n)) :
    (setAtom v a False).ConsistentWith ((DP.union (AxProcess F)).D n) ∧
      ¬ (setAtom v a False).Holds F.u := by
  have hnot : ¬ (setAtom v a False).Holds F.u := by
    rw [hu, holds_atom_setAtom]
    exact id
  refine ⟨?_, hnot⟩
  rw [PCWorld.consistentWith_union_iff]
  refine ⟨consistentWith_setAtom hv (hfree n) False, ?_⟩
  rw [consistentWith_axProcess_iff]
  intro i _ hui
  exact absurd hui hnot

/-- `hworld` for the union, with the universal false at every stage (the shape
`lic_nonDogmatism_dual` consumes).
Source: mandate T3.5
Kind: L
Fidelity: exact -/
theorem union_ax_hworld_u_false {DP : DeductiveProcess} {F : UIFamily} {a : ℕ}
    (hu : F.u = Formula.atom a) (hfree : ∀ n, ∀ φ ∈ DP.D n, a ∉ sentenceAtomCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (AxProcess F)).D n) ∧ ¬ v.Holds F.u := by
  intro n
  obtain ⟨v, hv⟩ := hworld n
  exact ⟨setAtom v a False, union_ax_world_u_false hu hfree hv⟩

/-- `hworld` for the union (the universal-free half).
Source: mandate T3.3
Kind: L
Fidelity: exact -/
theorem union_ax_hworld {DP : DeductiveProcess} {F : UIFamily} {a : ℕ}
    (hu : F.u = Formula.atom a) (hfree : ∀ n, ∀ φ ∈ DP.D n, a ∉ sentenceAtomCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (AxProcess F)).D n) := fun n =>
  let ⟨v, hv, _⟩ := union_ax_hworld_u_false hu hfree hworld n
  ⟨v, hv⟩

/-- A world consistent with the completed union is consistent with the completed base.
Source: FAF `PCWorld.consistentWith_union_iff`
Kind: L
Fidelity: n/a -/
lemma consistentWithTheory_base_of_union {DP extra : DeductiveProcess} {v : PCWorld}
    (hv : v.ConsistentWithTheory (DP.union extra)) : v.ConsistentWithTheory DP := fun n =>
  ((PCWorld.consistentWith_union_iff v DP extra n).mp (hv n)).1

end Cleanroom.Bli.BliRvcUi
