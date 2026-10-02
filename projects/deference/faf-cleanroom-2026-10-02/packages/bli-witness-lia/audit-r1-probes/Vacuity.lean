import Cleanroom.Bli.BliWitnessLia

/-!
# Audit round 1 (adversarial) — probe: is anything trivially true or junk-valued?

Four checks on the horizon-one prior `segmentSist`:

1. **The strict-stakes hypotheses are load-bearing.** At `c = V` the verdict is `0` and *both*
   actions are one-step choices (a tie). So `isOneStepChoice_pay`'s `c < V` and
   `instance_refuse`'s `V < c` are not decoration: the shape alone decides nothing.
2. **`EU` is not evaluated at a junk point.** `EU T a := condExp μ U (pp · T = a)` is `0` at a
   null policy point (disclosed junk value in `udt-bli-core`). Here `ppMass askTable a = 1/2` for
   both actions, so the verdict compares two genuine conditional expectations.
3. **`homeEU` is not junk either, and it is the mugging's updateful value.** At the Ask table
   (mass `1/2`, cell mass `1/4`): `homeEU Ask give = −c`, `homeEU Ask refuse = 0`.
4. **Faith is not vacuous at the charged state.** At the Ask table the branch frequency of every
   small sentence is `sliceT n φ · 1/2`, not `0 = 0`.
-/

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
open Cleanroom.Bli.BliWitnessLia

namespace AuditR1Vacuity

noncomputable section

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn : n < H) (h2 : 2 ≤ n)
variable (c V : ℚ) (r₀ : Bool → ℚ)

/-- 1. At `c = V` both actions are one-step choices: the verdict is a tie. -/
theorem tie_at_equal_stakes :
    (segmentSist H K hK n hn h2 V V r₀).IsOneStepChoice (askTable K hK hn) true ∧
    (segmentSist H K hK n hn h2 V V r₀).IsOneStepChoice (askTable K hK hn) false := by
  have hd := verdict hK hn h2 V V r₀
  rw [sub_self, zero_div, sub_eq_zero] at hd
  refine ⟨fun b => ?_, fun b => ?_⟩ <;> cases b
  · exact hd.ge
  · exact le_rfl
  · exact le_rfl
  · exact hd.le

/-- 2. The policy points the verdict conditions on have mass `1/2`: `EU` is not junk here. -/
theorem ppMass_ask_half (a : Bool) :
    (segmentSist H K hK n hn h2 c V r₀).ppMass (askTable K hK hn) a = 1 / 2 :=
  ppMass_sistSkel _ _ _ _ _ _ _ _ _ _ a

/-- 3. The updateful values at the Ask table: `−c` for give, `0` for refuse. -/
theorem homeEU_values :
    (segmentSist H K hK n hn h2 c V r₀).homeEU (askTable K hK hn) true = -c ∧
    (segmentSist H K hK n hn h2 c V r₀).homeEU (askTable K hK hn) false = 0 := by
  have h := homeEU_sistSkel (segmentSkeleton H K hK) n 0 (linkedTable n) (coinAt n (by omega))
    c V r₀ (askTable K hK hn) (askC_askTable hK hn h2) (stateMass_ask_pos hK hn h2 c V r₀)
  refine ⟨?_, ?_⟩
  · rw [h]; simp [ind]
  · rw [h]; simp [ind]

/-- 4. Faith at the charged Ask state is `sliceT n φ · 1/2`, not `0 = 0`. -/
theorem faith_at_ask (φ : ↥(smallIndex.S (n + 0 + 1))) :
    integralOf (segmentSist H K hK n hn h2 c V r₀).μ
        (fun ω => ind ((segmentSist H K hK n hn h2 c V r₀).small ω φ))
        (fun ω => (segmentSist H K hK n hn h2 c V r₀).state ω = askTable K hK hn) =
      sliceT n φ * (1 / 2) := by
  rw [faith hK hn h2 c V r₀ (askTable K hK hn) φ, stateMass_ask hK hn h2 c V r₀, askTable_val]

end

end AuditR1Vacuity
