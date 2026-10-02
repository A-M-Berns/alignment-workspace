import Cleanroom.Li.LiPseudorandom.Joint
import Cleanroom.Li.LiPseudorandom.Market

/-!
# Audit round 3 (adversarial) — probe: degenerate instances of the repair-round-2 headlines

1. **The lift along the identity schedule is the builder rule** (`lift_idSched_w`): the subfamily
   theorem `subfamily_of_lift` specialises to T5's shape, so it is not a statement about a
   different object.
2. **Every day belongs to exactly one family of `truthStarω`** (`pairSched_onDay`,
   `exists_unique_family`): the countable-family stream has no orphan days and no day shared by two
   families; the target `omegaTarget q` is well-defined per family.
3. **Non-injective placements make the certified inductor vacuous**
   (`constZero_stage_unsat`): at `a = fun _ => 0` and an alternating stream, stage `2` of
   `atomDP a x (·+1)` contains `atom 0` and `∼atom 0`, so no world is consistent with it and FAF's
   `isLogicalInductor_of_stage_unsatisfiable` makes *every* computable market a logical inductor
   over it. `atomDP_succ_isLogicalInductor` and `diagBuilder_liaHistory_certified` quantify over
   all primitive recursive `a`; their non-degenerate instances are the injective ones (`a = id`,
   `constDP_isLogicalInductor`), which is where the ledger should point.
4. **An empty subfamily schedule cannot be written** (`Schedule` forces `ι` strictly monotone on
   `ℕ`, so every schedule is infinite) — recorded as a `Schedule.le_ι` consequence
   (`schedule_unbounded`).

Not imported by the library.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction LO.Propositional

/-! ## 1. The identity schedule -/

/-- The identity schedule: member `m` on day `m`. -/
def idSched : Schedule where
  ι := id
  π := id
  π_ι _ := rfl
  strictMono := strictMono_id

/-- The lift along the identity schedule is the builder rule, pointwise. -/
theorem lift_idSched_w (B : (ℕ → Bool) → History) (W : ℕ → EF) (x : ℕ → Bool) (n : ℕ) :
    (lift idSched B W).w x n = (builderRule B W).w x n := by
  show (if idSched.ι (idSched.π n) = n then clamp ((W (idSched.π n)).denote (B (restrict x n)))
    else 0) = clamp ((W n).denote (B (restrict x n)))
  have h : idSched.ι (idSched.π n) = n := rfl
  rw [if_pos h]
  rfl

/-! ## 2. The countable-family schedule partitions the days -/

/-- Day `n` is on family `r`'s schedule iff its `Nat.unpair` first component is `r`. -/
theorem pairSched_onDay (r n : ℕ) :
    (pairSched r).ι ((pairSched r).π n) = n ↔ (Nat.unpair n).1 = r := by
  show Nat.pair r (Nat.unpair n).2 = n ↔ _
  constructor
  · intro h
    have := congrArg (fun k => (Nat.unpair k).1) h
    simp only [Nat.unpair_pair] at this
    exact this.symm
  · intro h
    conv_rhs => rw [← Nat.pair_unpair n]
    rw [h]

/-- Every day belongs to exactly one family. -/
theorem exists_unique_family (n : ℕ) : ∃! r, (pairSched r).ι ((pairSched r).π n) = n := by
  refine ⟨(Nat.unpair n).1, (pairSched_onDay _ n).2 rfl, fun r hr => ?_⟩
  exact ((pairSched_onDay r n).1 hr).symm

/-! ## 3. Non-injective placements: the certified inductor is vacuous -/

/-- The alternating stream `true, false, true, …`. -/
def altStream : ℕ → Bool := fun n => decide (n % 2 = 0)

/-- At placement `fun _ => 0`, stage `2` of the delay-one process over the alternating stream has
no consistent world: it contains both `atom 0` (from member `0`) and `∼atom 0` (from member `1`). -/
theorem constZero_stage_unsat :
    ∀ v : PCWorld, ¬ v.ConsistentWith ((atomDP (fun _ => 0) altStream (fun j => j + 1)).D 2) := by
  intro v hv
  have h0 : literalOf (fun _ => 0) altStream 0 ∈
      (atomDP (fun _ => 0) altStream (fun j => j + 1)).D 2 :=
    literalOf_mem_atomDP (fun j => Nat.lt_succ_self j) (j := 0) (by norm_num)
  have h1 : literalOf (fun _ => 0) altStream 1 ∈
      (atomDP (fun _ => 0) altStream (fun j => j + 1)).D 2 :=
    literalOf_mem_atomDP (fun j => Nat.lt_succ_self j) (j := 1) (by norm_num)
  have hv0 := hv _ h0
  have hv1 := hv _ h1
  simp [literalOf, altStream] at hv0 hv1
  exact hv1 hv0

/-- The alternating stream is primitive recursive, so `atomDP_succ_isLogicalInductor` applies at
`a = fun _ => 0` — and by `constZero_stage_unsat` the instance it produces is the vacuous one. -/
theorem altStream_primrec : Primrec altStream := by
  have h : PrimrecPred (fun n : ℕ => n % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  unfold PrimrecPred at h
  obtain ⟨_, h⟩ := h
  exact h.of_eq (fun n => by first | rfl | (congr) | simp [altStream])

/-! ## 4. Schedules are infinite -/

/-- Every schedule places members on arbitrarily late days. -/
theorem schedule_unbounded (S : Schedule) (N : ℕ) : ∃ m, N ≤ S.ι m :=
  ⟨N, S.le_ι N⟩

end Cleanroom.Li.LiPseudorandom

#print axioms Cleanroom.Li.LiPseudorandom.lift_idSched_w
#print axioms Cleanroom.Li.LiPseudorandom.exists_unique_family
#print axioms Cleanroom.Li.LiPseudorandom.constZero_stage_unsat
