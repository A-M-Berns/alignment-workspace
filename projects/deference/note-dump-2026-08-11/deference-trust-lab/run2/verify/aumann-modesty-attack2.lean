/-
  aumann-modesty-attack2.lean — further hypothesis-inertness + structural-faithfulness probes.

  ATTACK 5 (NO_HCOVER): original partition_averaging body verbatim, `hcover` DELETED.
                        Body uses `hcover` ⇒ expect ERROR (load-bearing).
  ATTACK 6 (NO_HQ): original body verbatim, hq₁/hq₂ DELETED ⇒ expect ERROR.
  ATTACK 7 (FAKE-PARTITION near-miss): try to instantiate the GENERAL partition_averaging on a
           NON-disjoint pair (the overlapping cells E0,E3) — i.e. check the near-miss CANNOT be
           re-run with overlapping cells. We supply the real lemma and try to feed it a bogus
           hdisj for the overlapping cover; it must be UNPROVABLE.
  ATTACK 8 (C-as-whole-space sanity): confirm the knowledge-operator fixed-point check is not
           vacuously bypassable — show a NON-self-evident set fails `C_self_evident`-style check,
           i.e. the predicate actually discriminates (decide gives `false` for a bad C).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Finset

namespace AumannAttack2

def π : Fin 4 → ℚ := fun _ => 1/4
def X : Fin 4 → ℚ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0
def C : Fin 4 → Bool := fun _ => true

def E : Fin 4 → Fin 4 → Bool
  | 0, 0 => true  | 0, 1 => true  | 0, 2 => true  | 0, 3 => false
  | 1, 0 => false | 1, 1 => true  | 1, 2 => true  | 1, 3 => false
  | 2, 0 => false | 2, 1 => true  | 2, 2 => true  | 2, 3 => false
  | 3, 0 => false | 3, 1 => true  | 3, 2 => true  | 3, 3 => true

def post (S : Fin 4 → Bool) : ℚ :=
  (∑ v, (if S v then π v * X v else 0)) / (∑ v, (if S v then π v else 0))

def knows (S : Fin 4 → Bool) (w : Fin 4) : Bool := decide (∀ v, E w v = true → S v = true)

/-- ATTACK 5: partition_averaging body verbatim, `hcover` DELETED. Body uses `hcover v`. -/
theorem partition_averaging_NO_HCOVER
    (S₁ S₂ : Fin 4 → Bool) (q : ℚ)
    -- (hcover : ...) DELETED
    (hdisj  : ∀ w, ¬ (S₁ w = true ∧ S₂ w = true))
    (hm₁ : 0 < ∑ v, (if S₁ v then π v else 0))
    (hm₂ : 0 < ∑ v, (if S₂ v then π v else 0))
    (hq₁ : post S₁ = q) (hq₂ : post S₂ = q) :
    post C = q := by
  have hnum : (∑ v, (if C v then π v * X v else 0))
            = (∑ v, (if S₁ v then π v * X v else 0)) + (∑ v, (if S₂ v then π v * X v else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hc := hcover v   -- hcover gone ⇒ error here
    by_cases h1 : S₁ v = true
    · have h2 : S₂ v = false := by
        by_contra h2'; exact hdisj v ⟨h1, by simpa using h2'⟩
      simp [h1, h2, (hc.mpr (Or.inl h1))]
    · sorry
  sorry

/-- ATTACK 7: the FAKE-PARTITION near-miss. The REAL general lemma (with hdisj) below; we then
    try to apply it to the OVERLAPPING cover E0,E3 by supplying a hdisj proof for them. That
    hdisj is FALSE (they share worlds 1,2), so it must be UNPROVABLE — confirming the near-miss
    genuinely needs disjointness and cannot be faked on overlapping cells. -/
theorem fake_partition_unprovable :
    ¬ (∀ w, ¬ (E 0 w = true ∧ E 3 w = true)) := by
  intro h
  exact h 1 (by decide)

/-- ATTACK 8: the self-evidence predicate genuinely discriminates — a BAD candidate set
    `D = {0}` is NOT self-evident under E (since E 0 reaches 1,2 ∉ D). decide must give the
    NEGATIVE, proving `knows`/self-evident is not a vacuous always-true predicate. -/
def D : Fin 4 → Bool
  | 0 => true | _ => false

theorem bad_set_not_self_evident : ¬ (∀ w, D w = true → knows D w = true) := by
  decide

/-- And the whole-space C really is a fixed point of the SAME operator (not bypassed). -/
theorem C_fixed_point_genuine : ∀ w, C w = knows C w := by decide

end AumannAttack2
