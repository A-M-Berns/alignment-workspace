import Cleanroom.Deference.DefObstruction.Fragment
import Cleanroom.Deference.DefObstruction.Witness

/-!
# `def-obstruction` · FragmentWitness: the non-dogmatism cluster over FAF's LIA (T7, N+)

The N+ instances of `Fragment.lean` over FAF's constructions:

* **The obstruction atom** `obsAtom := freshAtom 5 0` (family `5` of `bli-found`'s registry is
  this package's) is **undecided in `paperDP 𝗜𝚺₁`** (`obsAtom_undecided`: both polarities at every
  stage) and **decided true at stage `0` of `paperAdjoin := paperDP 𝗜𝚺₁ ⊕ {obsAtom}`**.
* **T7(d), both non-implications, realized**: FAF's LIA over `paperAdjoin` is an inductor over
  `paperAdjoin` and not over `paperDP 𝗜𝚺₁` (`lia_adjoin_not_inductor_base`); FAF's LIA over
  `paperDP 𝗜𝚺₁` is an inductor over it and not over `paperAdjoin` (`lia_base_not_inductor_adjoin`).
  Packaged as the two-sided statement `criterion_not_monotone_either_direction` — an inductor
  on each side — which is where "not monotone in either direction" has content; the abstract
  `criterion_not_monotone_in_process` (`Fragment.lean`) is the single proposition "no market is
  an inductor over both".
* **T7(a)/(b), realized**: over the alternating pair's base, the autonomous LIA and the advised
  LIA both have limiting belief in `(0,1)` on the undecided `obsAtom`
  (`altPair_obsAtom_confined`); over `paperAdjoin` as base (the pair `adjPair`), both have limiting
  belief `1` on it (`adjPair_obsAtom_trusts`).

Scope: one-way.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The obstruction atom and the adjoined process -/

/-- **The obstruction atom**: the fresh atom of family `5` (this package's registry row), payload
`0`. Tag-free for the ledger family (`obsAtom_tagFree`).
Scope: one process.
Source: mandate T7(d) ("a fresh-atom literal from `bli-found`'s `freshAtom`"); `bli-found` registry row `5`
Kind: D
Fidelity: n/a
Hyps: n/a -/
def obsAtom : Sentence := freshAtom 5 0

/-- The obstruction atom carries no ledger-family tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem obsAtom_tagFree : TagFreeSentence (cleanroomBaseTag + ledgerFamily) obsAtom :=
  freshAtom_tagFree_of_ne (by decide)

/-- The paper process is free of the obstruction atom's positive schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperDP_freeT : ProcessFreeOf (atomSchedule 5 0 true) (paperDP 𝗜𝚺₁) :=
  processFreeOf_atomSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) 5 0 true

/-- The paper process is free of the obstruction atom's negative schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperDP_freeF : ProcessFreeOf (atomSchedule 5 0 false) (paperDP 𝗜𝚺₁) :=
  processFreeOf_atomSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) 5 0 false

/-- **The obstruction atom is undecided in the paper process** (both polarities at every stage).
Scope: one process.
Source: [[self-referential-settlement-target]] §6 ("`D⁺_H` never decides `φ`"); mandate T7(d)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem obsAtom_undecided : Undecided (paperDP 𝗜𝚺₁) obsAtom :=
  freshAtom_undecided paperDP_freeT paperDP_freeF (paperDP_hworld 𝗜𝚺₁)

/-- **The stronger process** `paperDP 𝗜𝚺₁ ⊕ {obsAtom}`.
Scope: one process.
Source: [[self-referential-settlement-target]] §6 (the construction's `E`); mandate T7(d)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def paperAdjoin : DeductiveProcess := adjoinAtom (paperDP 𝗜𝚺₁) 5 0

/-- The stronger process is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperAdjoin_computable : ComputableDeductiveProcess paperAdjoin :=
  adjoinAtom_computable (paperDP_computable 𝗜𝚺₁) 5 0

/-- The stronger process has satisfiable stages.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperAdjoin_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (paperAdjoin.D n) :=
  adjoinAtom_hworld paperDP_freeT (paperDP_hworld 𝗜𝚺₁)

/-- The obstruction atom is decided true at stage `0` of the stronger process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperAdjoin_decided : DecidedTrueAt paperAdjoin obsAtom :=
  DecidedTrueAt.of_mem ⟨0, adjoinAtom_mem (paperDP 𝗜𝚺₁) 5 0 0⟩

/-- The stronger process is free of every ledger schedule (its only non-paper atom is the
obstruction atom, of family `5`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperAdjoin_freeOf_ledger (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ProcessFreeOf (ledgerSchedule a e) paperAdjoin := by
  intro k φ hφ
  unfold paperAdjoin adjoinAtom at hφ
  rw [extendBy_D, Finset.mem_union] at hφ
  rcases hφ with h | h
  · exact processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) k φ h
  · rw [Finset.mem_image] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp only [atomSchedule, LiteralSchedule.ofList_lits, List.mem_toFinset,
      List.mem_singleton] at hx
    subst hx
    rw [literalOf_true]
    exact freeOf_ledgerSchedule_of_tagFree obsAtom_tagFree

/-! ## B. T7(d) realized: FAF's LIA on both sides -/

/-- **(i) realized**: FAF's LIA over the stronger process is an inductor over it and **not** an
inductor over the paper process.
Scope: one process pair.
Source: [[self-referential-settlement-target]] §6 (anson-009); mandate T7(d) ("N+ witnesses")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem lia_adjoin_not_inductor_base :
    IsLogicalInductor (liaHistory paperAdjoin) paperAdjoin ∧
    ¬ IsLogicalInductor (liaHistory paperAdjoin) (paperDP 𝗜𝚺₁) :=
  ⟨LIA_is_logical_inductor _ paperAdjoin_computable,
    not_inductor_base_of_inductor_adjoin paperDP_freeT paperDP_freeF (paperDP_hworld 𝗜𝚺₁) _
      (LIA_is_logical_inductor _ paperAdjoin_computable)⟩

/-- **(ii) realized**: FAF's LIA over the paper process is an inductor over it and **not** an
inductor over the stronger process.
Scope: one process pair.
Source: [[self-referential-settlement-target]] §6 (the monotonicity reversal); mandate T7(d)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem lia_base_not_inductor_adjoin :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    ¬ IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) paperAdjoin :=
  ⟨LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁),
    not_inductor_adjoin_of_inductor_base paperDP_freeT paperDP_freeF (paperDP_hworld 𝗜𝚺₁) _
      (LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁))⟩

/-- **T7(d), the two-sided statement: the criterion is not monotone in the process in either
direction.** There is a market that is an inductor over the base `paperDP 𝗜𝚺₁` but not over the
stronger process `paperAdjoin`, and a market that is an inductor over `paperAdjoin` but not over
the base — one inductor on each side (FAF's LIA over each process). This, not
`criterion_not_monotone_in_process` (one proposition: no market is an inductor over both), is
where "both directions" has content; the two existentials are independent facts, each needing an
inductor over its process (repair round 1, audit B3).
Scope: one process pair.
Source: [[self-referential-settlement-target]] §6 (anson-009 and its extension flag, "both non-implications"); root-deference-031; mandate T7(d)
Kind: N+
Fidelity: stronger: both non-implications witnessed (the source refutes one construction)
Hyps: (a) none -/
theorem criterion_not_monotone_either_direction :
    (∃ P : History, IsLogicalInductor P (paperDP 𝗜𝚺₁) ∧ ¬ IsLogicalInductor P paperAdjoin) ∧
    (∃ P : History, IsLogicalInductor P paperAdjoin ∧ ¬ IsLogicalInductor P (paperDP 𝗜𝚺₁)) :=
  ⟨⟨_, lia_base_not_inductor_adjoin⟩, ⟨_, lia_adjoin_not_inductor_base⟩⟩

/-! ## C. T7(a)/(b) realized -/

/-- **T7(b) realized**: on the alternating pair, both the autonomous LIA over `paperDP 𝗜𝚺₁` and
the advised LIA over the ledger process have limiting belief in `(0,1)` on the undecided
obstruction atom.
Scope: one-way.
Source: mandate T7(b) witness; [[self-referential-settlement-target]] §5.3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem altPair_obsAtom_confined :
    (0 < limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) obsAtom ∧
      limitingBelief (liaHistory (paperDP 𝗜𝚺₁)) obsAtom < 1) ∧
    (0 < limitingBelief altPair.H obsAtom ∧ limitingBelief altPair.H obsAtom < 1) :=
  @undecided_fragment_confined altPair (liaHistory (paperDP 𝗜𝚺₁))
    (LIA_is_logical_inductor _ (paperDP_computable 𝗜𝚺₁))
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    obsAtom obsAtom_tagFree obsAtom_undecided

/-- **The pair over the stronger base**: FAF's LIA over `paperAdjoin ⊕ ledger(aAlt)`.
Scope: one-way.
Source: mandate T7(a) witness
Kind: N+
Fidelity: variant: plain trader class
Hyps: (a) none -/
noncomputable def adjPair : TablePair :=
  TablePair.ofLIA paperAdjoin paperAdjoin_computable aAlt aAlt_computable
    (fun _ => PublicationSchedule.succ) succSchedule_computable
    (paperAdjoin_freeOf_ledger _ _) paperAdjoin_hworld aAlt_range

/-- **T7(a) realized**: over the stronger base, where the obstruction atom is a stage-`0` fact,
both the autonomous and the advised LIA have limiting belief `1` on it — whatever the alternating
table says.
Scope: one-way.
Source: mandate T7(a) witness; [[self-referential-settlement-target]] §5.4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem adjPair_obsAtom_trusts :
    limitingBelief (liaHistory paperAdjoin) obsAtom = 1 ∧ limitingBelief adjPair.H obsAtom = 1 :=
  (@decided_fragment_trusts adjPair (liaHistory paperAdjoin)
    (LIA_is_logical_inductor _ paperAdjoin_computable)
    (paperAdjoin_freeOf_ledger _ _) obsAtom obsAtom_tagFree).1 paperAdjoin_decided

end Cleanroom.Deference.DefObstruction
