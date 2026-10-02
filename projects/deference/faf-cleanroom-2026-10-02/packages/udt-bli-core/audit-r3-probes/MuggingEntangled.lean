import Cleanroom.Bli.UdtBliCore

/-!
# `udt-bli-core` · audit round 3, adversarial lens · probe: the mugging's `Entangled` structures

Not part of the library (never imported by it). Elaborated with `scripts/lean-check`.

Repair round 2 added `Mugging.not_coordinationFree`: no `Entangled` (or `EntangledExp`) structure
over the mugging prior is coordination-free. That theorem is proved through a consequence
(`localUtility_of_coordinationFree` and `Mugging.not_localUtility`), so it would also hold if the
mugging prior admitted **no** `Entangled` structure at all — as the tent prior does not
(`Tent.no_entangled`). This probe checks that the negative is not vacuous in that way:

1. `mugEntangled r` is an explicit `Entangled` structure on `muggingPrior r` (every branch's
   utility may read the `Ask` point; no branch's probability reads any point).
2. `ask_mem_dep_rec`: **every** `Entangled` structure on the mugging has `Ask ∈ dep Rec` — the
   cross-branch dependency the mugging is built on is forced into any sound structure, which is
   *why* none is coordination-free (a sharper statement than the package's).
-/

namespace AuditR3

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.FiniteBLIPrior
  Finset

namespace MugEnt

variable (r : Bool → ℚ)

/-- An `Entangled` structure on the mugging prior: `dep _ = {Ask}`, `depP _ = ∅`. -/
def mugEntangled : (muggingPrior r).Entangled where
  dep := fun _ => {askT}
  depP := fun _ => ∅
  U_sound := by
    intro ω ω' hs hp
    have hs' : mugState ω.1 = mugState ω'.1 := hs
    have h1 : ω.1 = ω'.1 := mugState_injective hs'
    have hAsk : ω.2 askT = ω'.2 askT :=
      hp askT (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    show mugU r ω.1 (ω.2 askT) = mugU r ω'.1 (ω'.2 askT)
    rw [h1, hAsk]
  mass_sound := by
    intro T π π' _
    unfold muggingPrior
    rw [IndepData.cellMass_toPrior, IndepData.cellMass_toPrior, IndepData.policyMass_toPrior,
      IndepData.policyMass_toPrior]
    ring

/-- The all-pay policy. -/
def payAll : Policy mugTables Bool := fun _ => true

/-- Pay everywhere except at `Ask`. -/
def payExceptAsk : Policy mugTables Bool := fun T => decide (T ≠ askT)

/-- Every `Entangled` structure on the mugging prior records the dependency of the `Rec` branch
on the `Ask` point: the outcomes `(Rec, payAll)` and `(Rec, payExceptAsk)` agree on every point
but `Ask` and have utilities `100` and `0`. -/
theorem ask_mem_dep_rec (E : (muggingPrior r).Entangled) : askT ∈ E.dep recT := by
  by_contra hno
  have hU := E.U_sound ((1 : Fin 3), payAll) ((1 : Fin 3), payExceptAsk) rfl (by
    intro T' hT'
    change T' ∈ insert recT (E.dep recT) at hT'
    have hne : T' ≠ askT := by
      intro h
      subst h
      rcases Finset.mem_insert.mp hT' with h | h
      · exact askT_ne_recT h
      · exact hno h
    show payAll T' = payExceptAsk T'
    simp [payAll, payExceptAsk, hne])
  have h100 : (muggingPrior r).U ((1 : Fin 3), payAll) = 100 := by
    show mugU r 1 (payAll askT) = 100
    simp [payAll]
  have h0 : (muggingPrior r).U ((1 : Fin 3), payExceptAsk) = 0 := by
    show mugU r 1 (payExceptAsk askT) = 0
    simp [payExceptAsk]
  rw [h100, h0] at hU
  norm_num at hU

/-- The two facts together: the structure type is inhabited, and no inhabitant is
coordination-free (so the package's negative is not vacuous). -/
theorem not_vacuous :
    Nonempty (muggingPrior r).Entangled ∧
      ∀ E : (muggingPrior r).Entangled, ¬ (muggingPrior r).CoordinationFree E :=
  ⟨⟨mugEntangled r⟩, fun E hE =>
    askT_ne_recT (Finset.mem_singleton.mp ((hE recT).1 (ask_mem_dep_rec r E)))⟩

end MugEnt

end AuditR3
