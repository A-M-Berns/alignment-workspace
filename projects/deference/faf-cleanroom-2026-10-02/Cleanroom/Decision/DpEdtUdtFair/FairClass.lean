import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpFairnessReloc.Singleton
import Cleanroom.Decision.DpFairnessReloc.Fork
import Cleanroom.Decision.DpLocalOpt.GatedInduction

/-!
# `dp-edt-udt-fair`: the fair class `𝔉` and its neighbours (T1)

Definitions of record for the package `Cleanroom.Decision.DpEdtUdtFair` (see
`run/wp/dp-edt-udt-fair/`):

* `Realized obs B d` — some chance-positive leaf-world satisfies `O_d` (adversary-repair Claim
  A's added hypothesis); `FRec obs actEv B` — Definition 7 recording at every queried point for
  every procedure; **`FairClass obs actEv B`** — A36's `(F)(R)(P)(O)`: strongly fair, `FRec`,
  pruned, every queried observation realized (no evented-chance clause: `calibration.md` l. 9;
  every multi-member fiber in `𝔉` is un-evented, Claim B = `singleton_fibers`); `Corner` —
  GR-11's corner (value-fair, almost fair, `FRec`, pruned, realized).
* `refChildren B d` / **`Q C B d a`** — the reference continuation: the children of *some*
  `d`-node's subtree (chosen once per tree and point), and the value of `C` on the `a`-child. On
  strongly fair trees every `d`-node's `a`-child has this value (`stronglyFair_value_eq_Q`), so
  `Q` is the fiber-constant one-step deviation value `Q_C(d, a)` of FR-11 Step 1.
* Fiber propagation of subtree-veridicality (`FairClass.subtreeVeridical`), positivity of the
  fiber mass, of `ν(O_d)` and of `ν(a ∧ O_d)` under full-support procedures — in particular D2's
  escape clause never fires on `𝔉` (`fairClass_escape_never_fires`, representation decision 2).
* GR-11: `FairClass → Corner` (`FairClass.corner`); `tOpt_iff_isOptimal`.

Modelling remark on `refChildren`: at an unqueried `d` it is the junk `fun _ => B`; every
theorem reading `Q` quantifies over `d ∈ queried B`, where `refChildren_spec` holds.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### The vocabulary -/

section defs

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-- **`O_d` is realized**: some chance-positive leaf has its world in `O_d`.
Source: `adversary-repair.md` Claim A ("every queried point's observation is satisfied by some
leaf-world", with zero-probability chance edges pruned); `calibration.md` l. 9 (`𝔉`'s clause (O))
Kind: D
Fidelity: exact -/
def Realized (B : Tree Ω ι acts K) (d : ι) : Prop :=
  ∃ ℓ, Positive B ℓ ∧ world B ℓ ∈ obs d

/-- **FRec**: `B` records (Definition 7) at every queried point for every procedure.
Source: `fair-repair.md` FR-11 ("fully recorded (FRec)"); `calibration.md` l. 9 ("record at
every queried point for every procedure (Definition 7's four clauses, quantified over `C`)")
Kind: D
Fidelity: exact -/
def FRec (B : Tree Ω ι acts K) : Prop :=
  ∀ d ∈ queried B, RecordsForAll obs actEv B d

/-- **`FRec ∧ Pruned ∧ Realized`**: the three clauses of `𝔉` that involve no fairness grade
(`(R)(P)(O)` of A36), shared by `FairClass` and `Corner`. The positivity facts below (the D2
guard, the escape clause, `ν(a ∧ O_d) > 0`, `fiberMass > 0`) need only these.
Source: `v2-amendments.md` A36 (clauses (R)(P)(O)); `grounding.md` GR-10 (hypotheses)
Kind: D -/
structure FRecPR (B : Tree Ω ι acts K) : Prop where
  /-- (R): Definition 7 recording at every queried point for every procedure. -/
  frec : FRec obs actEv B
  /-- (P): every chance edge has positive probability. -/
  pruned : Pruned B
  /-- (O): every queried observation is satisfied by some chance-positive leaf-world. -/
  realized : ∀ d ∈ queried B, Realized obs B d

/-- **The fair class `𝔉`** (A36's `(F)(R)(P)(O)`): strongly fair (`dp-fairness-reloc`'s
`StronglyFair`: every fiber pairwise labelled-isomorphic), recording at every queried point for
every procedure (`FRec`), pruned (every chance edge positive), and every queried observation
realized. No evented-chance clause (`calibration.md` l. 9: "Chance need not be evented: the
proofs below use only pruning"); with evented chance every fiber collapses to a singleton
(`dp-fairness-reloc`'s `singleton_fibers_of_recordsForAll`, Claim B), so every multi-member fiber
in `𝔉` sits on a coin the worlds cannot see.
Source: `v2-amendments.md` A36 Theorem 3 (hypotheses (F)(R)(P)(O)); `calibration.md` l. 9;
`adversary-repair.md` Claim A (the exact repair)
Kind: D
Fidelity: exact -/
structure FairClass (B : Tree Ω ι acts K) : Prop where
  /-- (F): every fiber pairwise labelled-isomorphic. -/
  stronglyFair : StronglyFair B
  /-- (R): Definition 7 recording at every queried point for every procedure. -/
  frec : FRec obs actEv B
  /-- (P): every chance edge has positive probability. -/
  pruned : Pruned B
  /-- (O): every queried observation is satisfied by some chance-positive leaf-world. -/
  realized : ∀ d ∈ queried B, Realized obs B d

/-- **GR-11's corner**: value-fair, almost fair, `FRec`, pruned, every queried observation
realized (`γ_B(Unif) > 0` is exactly `Pruned ∧ Realized`, `nu_uniform_obs_pos`).
Source: `grounding.md` GR-11 ("the corner `{D_V = 0 ∀ C} ∩ {γ_B(Unif) > 0} ∩ almost-fair ∩ FRec`";
its EC clause dropped as in A37 / `calibration.md` l. 9)
Kind: D
Fidelity: variant: GR-11 lists EC; A37 and the fair class of record do not, and T9's proof uses
none -/
structure Corner (B : Tree Ω ι acts K) : Prop where
  /-- Value-fair: every fiber's members have the same act values under every procedure. -/
  valueFair : ValueFair B
  /-- Almost fair: no path meets a point twice. -/
  almostFair : AlmostFair B
  /-- `FRec`. -/
  frec : FRec obs actEv B
  /-- Pruned. -/
  pruned : Pruned B
  /-- Every queried observation realized. -/
  realized : ∀ d ∈ queried B, Realized obs B d

/-- The non-fairness clauses of `𝔉`.
Source: none: infrastructure
Kind: L -/
theorem FairClass.frecPR {B : Tree Ω ι acts K} (h : FairClass obs actEv B) : FRecPR obs actEv B :=
  ⟨h.frec, h.pruned, h.realized⟩

/-- The non-fairness clauses of the corner.
Source: none: infrastructure
Kind: L -/
theorem Corner.frecPR {B : Tree Ω ι acts K} (h : Corner obs actEv B) : FRecPR obs actEv B :=
  ⟨h.frec, h.pruned, h.realized⟩

end defs

/-! ### The reference continuation `Q` -/

section Q

/-- The children of some `d`-node's subtree, chosen once per tree and point (`Classical.choice`
through `dite`); the junk `fun _ => B` at an unqueried `d`.
Source: `fair-repair.md` FR-11 Step 1 ("`Q_C(d,a)`, the value of forcing `a` at the
(unique-per-run) `d`-consultation and following `C` below"); mandate representation decision 4
Kind: D -/
noncomputable def refChildren (B : Tree Ω ι acts K) (d : ι) : acts d → Tree Ω ι acts K :=
  haveI := Classical.propDecidable
  if h : ∃ c : acts d → Tree Ω ι acts K, ∃ q : B.DecNode, subtreeAt B q = .decision d c then
    h.choose
  else fun _ => B

omit [Fintype Ω] [DecidableEq Ω] in
/-- At a queried `d` some node's subtree is `decision d (refChildren B d)`.
Source: none: infrastructure
Kind: L -/
theorem refChildren_spec {B : Tree Ω ι acts K} {d : ι} (hd : d ∈ queried B) :
    ∃ q : B.DecNode, subtreeAt B q = .decision d (refChildren B d) := by
  obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried B d hd
  obtain ⟨c, hc⟩ := subtreeAt_eq_decision' B q d hq
  have h : ∃ c : acts d → Tree Ω ι acts K, ∃ q : B.DecNode, subtreeAt B q = .decision d c :=
    ⟨c, q, hc⟩
  classical
  unfold refChildren
  rw [dif_pos h]
  exact h.choose_spec

/-- **`Q_C(d, a)`**: the value of `C` on the `a`-child of the reference `d`-node. On strongly fair
trees this is the continuation value below *every* `d`-node's `a`-edge
(`stronglyFair_value_eq_Q`) — FR-11's honest one-step deviation value.
Source: `fair-repair.md` FR-11 Step 1 (`Q_C(d,a)`); `grounding.md` Definitions carried
(`Q_q(C,a) := G_q(C,a)`, "under non-nesting the honest one-step deviation value")
Kind: D
Fidelity: exact on strongly fair trees (fiber-constant); on other trees it is one member's value -/
noncomputable def Q (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (a : acts d) : K :=
  value C (refChildren B d a)

omit [Fintype Ω] [DecidableEq Ω] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [DecidableEq ι] in
/-- A node whose subtree is `decision d c` carries `d`.
Source: none: infrastructure
Kind: L -/
theorem pt_eq_of_subtreeAt_eq {B : Tree Ω ι acts K} {q : B.DecNode} {d : ι}
    {c : acts d → Tree Ω ι acts K} (h : subtreeAt B q = .decision d c) : pt B q = d := by
  obtain ⟨c', hc'⟩ := subtreeAt_eq_decision B q
  rw [hc'] at h
  simp only [Tree.decision.injEq] at h
  exact h.1

omit [Fintype Ω] [DecidableEq Ω] in
/-- **`Q` is the value at every fiber member**: on a strongly fair tree, if `subtreeAt B q =
decision d c` then `value C (c a) = Q C B d a` for every `C` and `a` (FR-1(ii): the continuation
law is the same at every member; `LabIso.contLaw_eq`).
Source: `fair-repair.md` FR-1(ii), FR-11 Step 1 ("node-independent by FR-1(ii)"); A36 Lemma 4
Kind: P
Fidelity: exact
Hyps: (a) `StronglyFair B` -/
theorem stronglyFair_value_eq_Q {B : Tree Ω ι acts K} (hB : StronglyFair B)
    (C : Proc ι acts K) {q : B.DecNode} {d : ι} {c : acts d → Tree Ω ι acts K}
    (hc : subtreeAt B q = .decision d c) (a : acts d) : value C (c a) = Q C B d a := by
  have hq : pt B q = d := pt_eq_of_subtreeAt_eq hc
  obtain ⟨q', hq'⟩ := refChildren_spec (B := B) (d := d) (hq ▸ pt_mem_queried B q)
  have hq'd : pt B q' = d := pt_eq_of_subtreeAt_eq hq'
  have hiso : LabIso (subtreeAt B q) (subtreeAt B q') :=
    hB d q ((mem_fiber B d q).mpr hq) q' ((mem_fiber B d q').mpr hq'd)
  rw [hc, hq'] at hiso
  cases hiso with
  | decision _ _ _ hchild => exact value_eq_of_contLaw_eq C ((hchild a).contLaw_eq C)

omit [Fintype Ω] [DecidableEq Ω] in
/-- On a strongly fair tree every `d`-node's subtree is isomorphic to the reference
`decision d (refChildren B d)`.
Source: none: infrastructure
Kind: L -/
theorem stronglyFair_iso_ref {B : Tree Ω ι acts K} (hB : StronglyFair B) {d : ι}
    (hd : d ∈ queried B) :
    ∀ q : B.DecNode, pt B q = d → LabIso (subtreeAt B q) (.decision d (refChildren B d)) := by
  intro q hq
  obtain ⟨q', hq'⟩ := refChildren_spec (B := B) hd
  rw [← hq']
  exact hB d q ((mem_fiber B d q).mpr hq) q' ((mem_fiber B d q').mpr (pt_eq_of_subtreeAt_eq hq'))

end Q

/-! ### Positivity on `𝔉` under full-support procedures -/

section positivity

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- On a pruned tree every leaf has positive mass under a full-support procedure.
Source: none: infrastructure
Kind: L -/
theorem pruned_leafLaw_pos {B : Tree Ω ι acts K} (hp : Pruned B) {C' : Proc ι acts K}
    (hC' : C'.FullSupport) (ℓ : B.Leaves) : 0 < leafLaw C' B ℓ :=
  (leafLaw_pos_iff_of_fullSupport hC' B ℓ).mpr (hp ℓ)

/-- `γ_B(Unif) > 0` read as `Pruned ∧ Realized`: on a pruned tree a realized observation has
positive `ν` under the uniform procedure (and under every full-support one, `nu_obs_pos`).
Source: `grounding.md` GR-11 ("`γ_B(Unif) > 0` is exactly adversary-repair Claim A's
realized-observation hypothesis after pruning")
Kind: L -/
theorem nu_obs_pos {B : Tree Ω ι acts K} (hp : Pruned B) {d : ι} (hr : Realized obs B d)
    {C' : Proc ι acts K} (hC' : C'.FullSupport) : 0 < nu C' B (obs d) := by
  obtain ⟨ℓ, hpos, hobs⟩ := hr
  have hmem : ℓ ∈ worldEv B (obs d) := by simp [worldEv, hobs]
  unfold nu mass
  exact lt_of_lt_of_le (pruned_leafLaw_pos hp hC' ℓ)
    (Finset.single_le_sum (f := fun ℓ' => leafLaw C' B ℓ') (fun ℓ' _ => leafLaw_nonneg C' B ℓ') hmem)

/-- `γ_B(Unif) > 0` literally: the uniform procedure.
Source: `grounding.md` GR-11
Kind: L -/
theorem nu_uniform_obs_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (hp : Pruned B) {d : ι}
    (hr : Realized obs B d) : 0 < nu (Proc.uniform : Proc ι acts K) B (obs d) :=
  nu_obs_pos hp hr Proc.uniform_fullSupport

/-- On `𝔉` the D2 guard `nuPoly C B (obs d) ≠ 0` holds at every queried point for every `C`.
Source: none: infrastructure (`dp-calibration`'s `nuPoly_ne_zero_iff`)
Kind: L -/
theorem FRecPR.nuPoly_obs_ne_zero [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) (C : Proc ι acts K) {d : ι} (hd : d ∈ queried B) :
    nuPoly C B (obs d) ≠ 0 := by
  obtain ⟨ℓ, hpos, hobs⟩ := h.realized d hd
  exact (nuPoly_ne_zero_iff C B (obs d)).mpr ⟨ℓ, hobs, hpos⟩

/-- **Fiber propagation of subtree-veridicality** (Claim A Step 1): on `𝔉`, every `d`-node is
subtree-veridical — a realized `O_d`-run exists, recording makes the `d`-node it passes
subtree-veridical, and the fiber isomorphism preserves leaf-worlds.
Source: `adversary-repair.md` Claim A Step 1 ("strong fairness (the isomorphism preserves
leaf-worlds) propagates subtree-veridicality to the *whole* fiber"); `zoo.md` ZO-2
Kind: P
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.subtreeVeridical [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {d : ι} (hd : d ∈ queried B) (q : B.DecNode) (hq : pt B q = d) :
    SubtreeVeridical obs B q := by
  obtain ⟨ℓ₀, hpos, hobs⟩ := h.realized d hd
  have hlaw : 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓ₀ :=
    pruned_leafLaw_pos h.pruned Proc.uniform_fullSupport ℓ₀
  obtain ⟨hcount, hnodes⟩ := h.frec d hd Proc.uniform ℓ₀ hlaw hobs
  obtain ⟨m, hm, hme⟩ := exists_dNode_of_count_pos d B ℓ₀ (by omega)
  obtain ⟨a₀, ha₀⟩ := Option.isSome_iff_exists.mp hme
  have hsv : SubtreeVeridical obs B m := (hnodes m hm a₀ ha₀).1
  exact h.stronglyFair.subtreeVeridical_transfer obs (hq.trans hm.symm) hsv

/-- On `𝔉` the fiber mass of a queried point is positive under every full-support procedure
(the realized `O_d`-run passes a `d`-node, whose reach is at least the run's mass).
Source: `adversary-repair.md` Claim A ("this yields `ν_{B,C^ε}(O_d) > 0` at every queried `d`")
Kind: L -/
theorem FRecPR.fiberMass_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) : 0 < fiberMass C' B d := by
  obtain ⟨ℓ₀, hpos, hobs⟩ := h.realized d hd
  have hlaw : 0 < leafLaw C' B ℓ₀ := pruned_leafLaw_pos h.pruned hC' ℓ₀
  obtain ⟨hcount, -⟩ := h.frec d hd C' ℓ₀ hlaw hobs
  obtain ⟨q₀, hq₀, hme⟩ := exists_dNode_of_count_pos d B ℓ₀ (by omega)
  have hreach : 0 < reach C' B q₀ := by
    rw [reach_eq_mass_leavesBelow]
    unfold mass
    exact lt_of_lt_of_le hlaw (Finset.single_le_sum (fun ℓ _ => leafLaw_nonneg C' B ℓ)
      ((mem_leavesBelow B q₀ ℓ₀).mpr hme))
  unfold fiberMass
  exact lt_of_lt_of_le hreach (Finset.single_le_sum (fun q _ => reach_nonneg C' B q)
    ((mem_fiber B d q₀).mpr hq₀))

/-- On `𝔉`, `ν_{C'}(a ∧ O_d) = C'(d)(a) · ν_{C'}(O_d)` for every procedure (the recording
argument, `dp-calibration`'s `nu_actEv_inter_obs_of_recordsFor`, at `FRec`).
Source: [[decision-problems-v2]] Remark 3.6; `fair-repair.md` FR-11 Step 2
Kind: L -/
theorem FRecPR.nu_actEv_inter_obs {B : Tree Ω ι acts K} (h : FRecPR obs actEv B)
    (C' : Proc ι acts K) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    nu C' B (actEv d a ∩ obs d) = (C' d).w a * nu C' B (obs d) :=
  nu_actEv_inter_obs_of_recordsFor obs actEv C' B (h.frec d hd C') a

/-- On `𝔉`, `ν_{C'}(a ∧ O_d) > 0` for every action under every full-support procedure.
Source: `fair-repair.md` FR-11 Step 2 ("`ν_ε(a ∣ O_d) = C^ε(d)(a) > 0` … so `A_d^+ = A_d`")
Kind: L -/
theorem FRecPR.nu_actEv_inter_obs_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) : 0 < nu C' B (actEv d a ∩ obs d) := by
  rw [h.nu_actEv_inter_obs C' hd a]
  exact mul_pos (hC' d a) (nu_obs_pos h.pruned (h.realized d hd) hC')

/-- **D2's escape clause never fires on `𝔉`**: for every `C`, every `ε ∈ (0, 1]` and every
queried `d`, some action event is realized within `O_d` under `C^ε` (every one is).
Source: mandate representation decision 2; `fair-repair.md` FR-11 Step 2 (`A_d^+ = A_d`)
Kind: L
Fidelity: exact -/
theorem FRecPR.escape_never_fires [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FRecPR obs actEv B) (C : Proc ι acts K) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1) {d : ι}
    (hd : d ∈ queried B) : ∃ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) :=
  ⟨Classical.arbitrary _, h.nu_actEv_inter_obs_pos (tremble_fullSupport C ε h0 h1) hd _⟩

/-- The `FairClass`-level names of the positivity facts (mandate representation decision 2).
Source: mandate representation decision 2
Kind: L -/
theorem fairClass_escape_never_fires [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1) {d : ι}
    (hd : d ∈ queried B) : ∃ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) :=
  h.frecPR.escape_never_fires C ε h0 h1 hd

/-- `FairClass` wrapper of `FRecPR.nuPoly_obs_ne_zero`. Source: none: infrastructure. Kind: L -/
theorem FairClass.nuPoly_obs_ne_zero [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) {d : ι} (hd : d ∈ queried B) :
    nuPoly C B (obs d) ≠ 0 := h.frecPR.nuPoly_obs_ne_zero C hd

/-- `FairClass` wrapper of `FRecPR.fiberMass_pos`. Source: none: infrastructure. Kind: L -/
theorem FairClass.fiberMass_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) : 0 < fiberMass C' B d := h.frecPR.fiberMass_pos hC' hd

/-- `FairClass` wrapper of `FRecPR.nu_actEv_inter_obs`. Source: none: infrastructure. Kind: L -/
theorem FairClass.nu_actEv_inter_obs {B : Tree Ω ι acts K} (h : FairClass obs actEv B)
    (C' : Proc ι acts K) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    nu C' B (actEv d a ∩ obs d) = (C' d).w a * nu C' B (obs d) :=
  h.frecPR.nu_actEv_inter_obs C' hd a

/-- `FairClass` wrapper of `FRecPR.nu_actEv_inter_obs_pos`. Source: none: infrastructure. Kind: L -/
theorem FairClass.nu_actEv_inter_obs_pos [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C' : Proc ι acts K} (hC' : C'.FullSupport) {d : ι}
    (hd : d ∈ queried B) (a : acts d) : 0 < nu C' B (actEv d a ∩ obs d) :=
  h.frecPR.nu_actEv_inter_obs_pos hC' hd a

end positivity

/-! ### GR-11 and the optimality bridge -/

section bridges

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **GR-11 (a), the inclusion**: `𝔉` lies in the corner (strong fairness ⟹ law-fairness ⟹
value-fairness, and ⟹ almost fairness). The inclusion is strict: `cornerTree_corner_not_fairClass`
(`Trees.lean`).
Source: `grounding.md` GR-11 ("Phase 1's fair class … is a proper subclass of the corner");
GR-9 (the grades)
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.corner {B : Tree Ω ι acts K} (h : FairClass obs actEv B) :
    Corner obs actEv B where
  valueFair := h.stronglyFair.lawFair.valueFair
  almostFair := StronglyFair.almostFair B h.stronglyFair
  frec := h.frec
  pruned := h.pruned
  realized := h.realized

/-- `dp-calibration`'s `TOpt` and `dp-local-opt`'s `IsOptimal` are one statement.
Source: mandate representation decision 3
Kind: L -/
theorem tOpt_iff_isOptimal (C : Proc ι acts K) (B : Tree Ω ι acts K) :
    TOpt C B ↔ IsOptimal C B := Iff.rfl

end bridges

end Cleanroom.Decision.DpEdtUdtFair
