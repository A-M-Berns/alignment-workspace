import Cleanroom.Fa.FaDelayBsi.Defs

/-!
# fa-delay-bsi · audit r2 (adversarial) · probe: the OPENs' schedule clauses are satisfiable, and
the inclusive clause is vacuous at lookahead `1`

`deficit_bound_open` and `frozen_divergent_pair_open` (`Open.lean`) carry the schedule clauses
`hclose : ClosesByBoundary S f d` and `hwd : StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1)`.
Audit r1 (adversarial, non-blocking 5) checked their joint satisfiability "by inspection, not by
machine", because building a window-disjoint `DeferralFunction` needs a `UnaryRuler` certificate.
This probe does it by machine, for **every** freeze schedule, with `f := succDeferral` and the
schedule `d k := 2k + 2` (`fa-forcing-trader`'s `linearSchedule 0`, rebuilt here because that
module is outside the package's import closure).

Two things the probe shows beyond satisfiability:

1. **`ClosesByBoundary S succDeferral d` holds for every `S` and every `d`**
   (`closesByBoundary_succ`): at lookahead `1` the inclusive clause is `n + 1 ≤ T (blockOf n + 1)`,
   which is `lt_T_blockOf_succ`. So the clause constrains nothing unless the lookahead can exceed
   one day; for `f = succDeferral` the OPENs are stated for *all* window-disjoint schedules of all
   freeze schedules. Not a defect (BSI's horizon `T_{k+1}` is reached from `T_{k+1} − 1` by exactly
   this lookahead), but the ledger's "schedule closing by the boundary" should not be read as a
   restriction in that regime.
2. At BSI's own schedule the same `d` also closes **strictly** within blocks
   (`evenSchedule_closesWithinBlocks_bsi`): `2k + 3` and `2k + 2` share a block of length `4`
   because `2k + 3` is odd and boundaries are multiples of `4`. So both readings of BSI's clause
   are inhabited at BSI's constants by one schedule.

Not imported by the library.
-/

namespace Cleanroom.Fa.FaDelayBsi.AuditR2

open LogicalInduction Cleanroom.Fa.FaDelayBsi

/-- At lookahead `1` the inclusive clause is vacuous: `n + 1 ≤ T (blockOf n + 1)` for every day. -/
theorem closesByBoundary_succ (S : FreezeSchedule) (d : DeferralFunction) :
    ClosesByBoundary S succDeferral d := fun k =>
  Nat.succ_le_of_lt (S.lt_T_blockOf_succ (d.f k))

/-- `d k := 2k + 2`: a deferral function (graph decided by one affine comparison on the unary
pair), window-disjoint for `succDeferral`. `fa-forcing-trader`'s `linearSchedule 0`, rebuilt. -/
def evenSchedule : DeferralFunction where
  f k := 2 * k + 2
  lt k := by omega
  graph_fp :=
    ⟨fun z => List.replicate
        (if 2 * z.length.unpair.1 + 2 = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag (((UnaryRuler.const 2).mul UnaryRuler.unpairFst).add
        (UnaryRuler.const 2)) UnaryRuler.unpairSnd,
      fun n m => by simp⟩

theorem evenSchedule_f (k : ℕ) : evenSchedule.f k = 2 * k + 2 := rfl

/-- The window-disjointness clause of the OPENs, at `f := succDeferral`, `d := evenSchedule`. -/
theorem evenSchedule_windowDisjoint :
    StrictMono evenSchedule.f ∧ ∀ k, succDeferral.f (evenSchedule.f k) < evenSchedule.f (k + 1) :=
  ⟨fun a b h => by show 2 * a + 2 < 2 * b + 2; omega,
   fun k => by show 2 * k + 2 + 1 < 2 * (k + 1) + 2; omega⟩

/-- **The schedule clauses of `deficit_bound_open` / `frozen_divergent_pair_open` are jointly
satisfiable for every freeze schedule** (machine-checked; audit r1 had it by inspection). -/
theorem schedule_clauses_satisfiable (S : FreezeSchedule) :
    ∃ f d : DeferralFunction,
      ClosesByBoundary S f d ∧ (StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1)) :=
  ⟨succDeferral, evenSchedule, closesByBoundary_succ S _, evenSchedule_windowDisjoint⟩

/-- `bsiSchedule.blockOf n = n / 4`. -/
theorem bsiSchedule_blockOf (n : ℕ) : bsiSchedule.blockOf n = n / 4 :=
  (bsiSchedule.blockOf_eq_iff _ _).2 ⟨by show 4 * (n / 4) ≤ n; omega,
    by show n < 4 * (n / 4 + 1); omega⟩

/-- At BSI's schedule, `evenSchedule` with lookahead `1` also satisfies the **strict** clause:
day `2k + 3` is in the block of day `2k + 2`. -/
theorem evenSchedule_closesWithinBlocks_bsi :
    ClosesWithinBlocks bsiSchedule succDeferral evenSchedule := fun k => by
  show bsiSchedule.blockOf (2 * k + 2 + 1) = bsiSchedule.blockOf (2 * k + 2)
  rw [bsiSchedule_blockOf, bsiSchedule_blockOf]
  omega

end Cleanroom.Fa.FaDelayBsi.AuditR2

#print axioms Cleanroom.Fa.FaDelayBsi.AuditR2.schedule_clauses_satisfiable
#print axioms Cleanroom.Fa.FaDelayBsi.AuditR2.evenSchedule_closesWithinBlocks_bsi
