import Cleanroom.Bli.BliTransfer.AttemptA.Defs
import Cleanroom.Bli.BliTransfer.AttemptA.Splice
import Cleanroom.Bli.BliTransfer.AttemptB.Defs

/-!
# `bli-transfer` · Defs: the definitions of record (reconciled)

The reconciled package of the dual work package `bli-transfer` (area `bli`, namespace
`Cleanroom.Bli.BliTransfer`). Two formalizers attacked the mandate independently — attempt A
(`AttemptA/`, angle A: the machine-model flat pass) and attempt B (`AttemptB/`, angle B: the
splice-stream route); their directories are kept unchanged as evidence. This file fixes the
package's **definitions of record** and states the bridges between the two attempts' copies.

**Which copy is of record, and why.** Both attempts copied the mandate's table verbatim, and
their copies of `overlay`, `EF.freeBound`, `EF.Closed`, `ExprMap`, `RestrictedEC`, `epsK`,
`epsE`, `clamp` and `E1c` are identical clause for clause (the bridges below are `rfl`, or
field-for-field for `ExprMap`). The one definition that differs is the clamp body `clampE`:
attempt A binds `ε_k` once by an outer `letE` (inside it the price is `var 1`) and proves the
body's laws (`clampE_denoteWith`, `clampE_cost_le`, `clampE_freeBound = 1`); attempt B inlines
`epsE k` twice and proves no law for it (T3 was refuted before one was needed). The definitions
of record are **attempt A's** throughout — the copy with the proved laws, and the copy the
criterion-level transfer theorem (T1, attempt A's) is stated over — re-exported here under the
package namespace, so that `Cleanroom.Bli.BliTransfer.overlay` *is*
`Cleanroom.Bli.BliTransfer.AttemptA.overlay` (an alias, not a third copy). The splice of record
(`EF.spliceOn`, `Strategy.spliceOn`, `Trader.spliceOn`, the `SpliceSpec` law package) is
likewise attempt A's.

Downstream (`bli-assemble`): `import Cleanroom.Bli.BliTransfer` and `open
Cleanroom.Bli.BliTransfer`; the names in the mandate's table resolve here.

Sources: [[bli-transfer-mandate]] § Definitions of record; [[bli-program]] §2.1, §3.1, §3.2(d).
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The definitions of record (attempt A's, re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptA
  (overlay overlay_small overlay_large
   EF.freeBound EF.Closed EF.denoteWith_congr_env EF.Closed.denoteWith_env_irrelevant
   EF.Closed.denoteWith_eq_denote EF.rank_le_of_priceQueries
   ExprMap ExprMap.rank_le ExprMap.ofLargeOnly
   RestrictedEC
   epsK epsK_succ epsK_pos epsK_le_half epsE epsE_denoteWith epsE_closed epsE_priceQueries
   epsE_cost negE clampE clampE_denoteWith clampE_cost_le clampE_freeBound clampE_priceQueries
   clamp E1c clamp_mem_Icc abs_clamp_sub_le)

/-! ## The splice of record (attempt A's, re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptA
  (EF.spliceOn EF.rank_le_spliceOn EF.spliceOn_rank_le EF.spliceOn_rank EF.spliceOn_cost_le
   SpliceSpec ExprMap.spliceSpec EF.spliceOn_denoteWith EF.spliceOn_denote
   Strategy.spliceOn Strategy.spliceOn_trades Trader.spliceOn Trader.spliceOn_strat
   Strategy.spliceOn_value)

/-! ## Bridges to attempt B's copies

Attempt B's results that the reconciled package takes (T3's refutation, `Clamp.lean`) are stated
over attempt B's `clamp`/`epsK`; these bridges say the two copies are the same object, so those
results transfer to the definitions of record by `rfl`. -/

/-- Attempt B's `overlay` is the overlay of record (the same term).
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_overlay_eq (Q : History) (ov : ℕ → Sentence → ℚ) :
    AttemptB.overlay Q ov = overlay Q ov := rfl

/-- Attempt B's `ε_k` is the `ε_k` of record.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_epsK_eq : AttemptB.epsK = epsK := rfl

/-- Attempt B's `clamp` is the clamp of record (the same term).
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_clamp_eq (Q : History) : AttemptB.clamp Q = clamp Q := rfl

/-- Attempt B's `E1c` is the `E1c` of record.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_E1c_iff (Q P : History) : AttemptB.E1c Q P ↔ E1c Q P := Iff.rfl

/-- Attempt B's `RestrictedEC` is the restricted class of record.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_restrictedEC_iff (Tr : Trader) : AttemptB.RestrictedEC Tr ↔ RestrictedEC Tr :=
  Iff.rfl

/-- Attempt B's free-variable bound agrees with the one of record on every feature.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_freeBound_eq : ∀ e : EF, AttemptB.EF.freeBound e = EF.freeBound e
  | .price _ _ => rfl
  | .const _ => rfl
  | .add a b => by
      simp only [AttemptB.EF.freeBound, AttemptA.EF.freeBound, attemptB_freeBound_eq a,
        attemptB_freeBound_eq b]
  | .mul a b => by
      simp only [AttemptB.EF.freeBound, AttemptA.EF.freeBound, attemptB_freeBound_eq a,
        attemptB_freeBound_eq b]
  | .max a b => by
      simp only [AttemptB.EF.freeBound, AttemptA.EF.freeBound, attemptB_freeBound_eq a,
        attemptB_freeBound_eq b]
  | .safeRecip a => by
      simp only [AttemptB.EF.freeBound, AttemptA.EF.freeBound, attemptB_freeBound_eq a]
  | .var _ => rfl
  | .letE x b => by
      simp only [AttemptB.EF.freeBound, AttemptA.EF.freeBound, attemptB_freeBound_eq x,
        attemptB_freeBound_eq b]

/-- Attempt B's `Closed` is closedness of record.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
theorem attemptB_closed_iff (e : EF) : AttemptB.EF.Closed e ↔ EF.Closed e := by
  unfold AttemptB.EF.Closed AttemptA.EF.Closed
  rw [attemptB_freeBound_eq]

/-- An expression map of record is an expression map in attempt B's sense (field for field).
Source: none: infrastructure (reconciliation)
Kind: D
Fidelity: n/a -/
def ExprMap.toB {Q : History} {ov : ℕ → Sentence → ℚ} (E : ExprMap Q ov) :
    AttemptB.ExprMap Q ov where
  expr := E.expr
  closed := fun k ψ e h => (attemptB_closed_iff e).2 (E.closed k ψ e h)
  leaves := E.leaves
  fires := E.fires
  silent := E.silent
  ov_range := E.ov_range

/-- An expression map in attempt B's sense is one of record (field for field).
Source: none: infrastructure (reconciliation)
Kind: D
Fidelity: n/a -/
def ExprMap.ofB {Q : History} {ov : ℕ → Sentence → ℚ} (E : AttemptB.ExprMap Q ov) :
    ExprMap Q ov where
  expr := E.expr
  closed := fun k ψ e h => (attemptB_closed_iff e).1 (E.closed k ψ e h)
  leaves := E.leaves
  fires := E.fires
  silent := E.silent
  ov_range := E.ov_range

end Cleanroom.Bli.BliTransfer
