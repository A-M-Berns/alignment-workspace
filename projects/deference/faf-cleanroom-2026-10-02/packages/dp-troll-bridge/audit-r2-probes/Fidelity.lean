/-
  Audit round 2, lens `fidelity`, probes for `dp-troll-bridge` (2026-09-30).
  Not imported by the library. Elaborated with `scripts/lean-check`.

  What is probed:
  1. Target 7(a) has the same shape as target 3 after repair round 1, but its Kinds were not
     regraded: `exploring_deliberate_stays` (`⊡(Hexp) 🡒 ∼d`) is axiom L + K + propositional
     logic (no `lob_rule`), `exploring_lesion` is its propositional corollary, and the boxed
     exploring schema *is* boxed deliberate staying: `⊡(Hexp x d) 🡘 ⊡(∼d)`.
  2. The binding-coin schema does **not** collapse: `GL ⊬ ⊡(Hcoin x d) 🡒 ∼d` (three-world
     chain, `d` at the root, `x` at the middle world). So the two target-7 trolls differ
     exactly in whether the boxed schema is boxed staying — a sharper statement of
     "Löb closes" vs "Löb stalls" than the package's two headlines.
  3. Finding F13: the inventory's sketch `A := □⊥` for refuting Stuart's schema can never
     work, for any `B`: the premise `□⊥ 🡒 (□B 🡒 B)` is GL-equivalent to the conclusion
     `□⊥ 🡒 B` (because `□⊥ 🡒 □B`).
  4. The count predicates of `count_crossFirst` / `count_dead` tied to the theorems at the
     *statement* level (the package ties them inside the proof of `classification_complete`):
     every counted cross-first ordering's agents satisfy `χ 🡘 □⊥`, every counted dead
     ordering's agents satisfy `∼χ`.
-/

import Cleanroom.Decision.DpTrollBridge.Lesion
import Cleanroom.Decision.DpTrollBridge.Countermodels
import Cleanroom.Decision.DpTrollBridge.Orderings

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge.AuditR2

/-! ## 1. Target 7(a): the exploring-agent schema is boxed deliberate staying -/

/-- `⊡(Hexp x d) 🡒 ∼d` from axiom L directly, exactly as `stays_schema`: `Hexp` weakens
propositionally to `□L 🡒 L` for `L := cross 🡒 bad` (under `∼d`, `cross` is `x` and `bad`
holds), so `□(Hexp) 🡒 □L` by K and axiom L, and `Hexp ⋏ □L 🡒 ∼d`. No `lob_rule`. -/
theorem exploring_deliberate_stays_by_axiomL (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 ∼(.atom d : Modal.Formula ℕ) := by
  have hweak : Modal.GL ⊢ Hexp x d 🡒
      (□(exploringCross x d 🡒 exploringBad x d) 🡒 (exploringCross x d 🡒 exploringBad x d)) := by
    simp only [Hexp, exploringCross, exploringBad]
    cl_prover
  have hK : Modal.GL ⊢ □(Hexp x d) 🡒
      □(□(exploringCross x d 🡒 exploringBad x d) 🡒 (exploringCross x d 🡒 exploringBad x d)) :=
    imply_box_distribute'! hweak
  have hL : Modal.GL ⊢ □(□(exploringCross x d 🡒 exploringBad x d) 🡒
      (exploringCross x d 🡒 exploringBad x d)) 🡒 □(exploringCross x d 🡒 exploringBad x d) :=
    axiomL!
  simp only [Hexp, exploringCross, exploringBad] at hK ⊢
  cl_prover [hK, hL]

/-- `exploring_lesion` is a propositional corollary of `exploring_deliberate_stays`. -/
example (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡒 (exploringCross x d 🡒 exploringBad x d) := by
  have h := exploring_deliberate_stays x d
  simp only [Hexp, exploringCross, exploringBad] at h ⊢
  cl_prover [h]

/-- The boxed exploring schema is boxed deliberate staying: `⊡(Hexp x d) 🡘 ⊡(∼d)`. -/
theorem boxdotHexp_iff_boxdot_neg (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡘 ⊡(∼(.atom d : Modal.Formula ℕ)) := by
  have h1 : Modal.GL ⊢ ⊡(Hexp x d) 🡒 ∼(.atom d : Modal.Formula ℕ) := exploring_deliberate_stays x d
  have hself : Modal.GL ⊢ ⊡(Hexp x d) 🡒 □(⊡(Hexp x d)) := boxdot_self_box (Hexp x d)
  have h2 : Modal.GL ⊢ □(⊡(Hexp x d)) 🡒 □(∼(.atom d : Modal.Formula ℕ)) :=
    imply_box_distribute'! h1
  have h3 : Modal.GL ⊢ ∼(.atom d : Modal.Formula ℕ) 🡒 Hexp x d := by
    simp only [Hexp]; cl_prover
  have h4 : Modal.GL ⊢ □(∼(.atom d : Modal.Formula ℕ)) 🡒 □(Hexp x d) :=
    imply_box_distribute'! h3
  cl_prover [h1, hself, h2, h3, h4]

/-! ## 2. The binding-coin schema does not collapse -/

/-- Valuation on the three-world chain: `d` true at `w0` only, `x` true at `w1` only. -/
def coinVal (x d : ℕ) : Kripke.Valuation chain3Frame :=
  fun a w => (a = d ∧ w = (0 : Fin 3)) ∨ (a = x ∧ w = (1 : Fin 3))

/-- `GL ⊬ ⊡(Hcoin x d) 🡒 ∼d`: at `w0` of `w0 ≺ w1 ≺ w2`, `d` holds; `□((x ⋎ d) 🡒 □⊥)` fails
at `w0` (at `w1`, `x` holds and `□⊥` fails), so `Hcoin` holds at `w0` vacuously; at `w1` and
`w2`, `∼d` holds, so `Hcoin` holds there too. Hence `⊡(Hcoin)` holds at `w0` while `∼d` fails.
Contrast `boxdotHexp_iff_boxdot_neg`: for the exploring-agent troll the boxed schema forces
`∼d`; for the original troll and the pooled agent it does not. -/
theorem coin_schema_not_boxdot_neg (x d : ℕ) (hxd : x ≠ d) :
    Modal.GL ⊬ (⊡(Hcoin x d) 🡒 ∼(.atom d : Modal.Formula ℕ)) :=
  unprovable_of_countermodel chain3Frame chain3Frame_isGL (coinVal x d) chain3W0
    (by
      simp [Formula.Kripke.Satisfies, Hcoin, chain3Frame, coinVal, chain3W0, hxd, hxd.symm]
      try decide)

/-! ## 3. F13: the inventory's `A := □⊥` sketch can never refute Stuart's schema -/

/-- For every `B`, `GL ⊢ □⊥ 🡒 (□B 🡒 B)` iff `GL ⊢ □⊥ 🡒 B`: under `□⊥` everything is boxed
(`C_box_of_boxBot`), so the premise and the conclusion of Stuart's schema coincide at
`A := □⊥`. The sketch in [[dp-sl-2-inventory]] 032 has no completion. -/
theorem stuart_sketch_boxBot_never (B : Modal.Formula ℕ) :
    (Modal.GL ⊢ (□⊥ : Modal.Formula ℕ) 🡒 (□B 🡒 B)) ↔
      (Modal.GL ⊢ (□⊥ : Modal.Formula ℕ) 🡒 B) := by
  constructor
  · intro h
    have hb : Modal.GL ⊢ (□⊥ : Modal.Formula ℕ) 🡒 □B := ⟨C_box_of_boxBot⟩
    cl_prover [h, hb]
  · intro h
    cl_prover [h]

/-! ## 4. The count predicates tied to the theorems at the statement level -/

/-- No ordering of the four post clauses carries a `−10` clause. -/
lemma allOrderings_no_um10 : ∀ l ∈ allOrderings, ∀ x ∈ l, x.2 ≠ Util.um10 := by decide

/-- Every ordering counted by `count_crossFirst` (head `(cross,10)` or `(cross,0)`) has all
its agents GL-equivalent to `□⊥` — the predicate of the count, tied to the theorem. -/
theorem crossFirst_class_iff_boxBot :
    ∀ l ∈ allOrderings, (l.head? = some cross10 ∨ l.head? = some cross0) →
      ∀ χ : Modal.Formula ℕ, IsAgent l χ → Modal.GL ⊢ χ 🡘 □⊥ := by
  intro l hl hhead χ h
  rcases l with _ | ⟨cl, rest⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    exact crossFirst_iff_boxBot hhead
      (fun x hx => allOrderings_no_um10 _ hl x (List.mem_cons_of_mem _ hx)) h

/-- Every ordering counted by `count_dead` (`(not,0)` before both cross clauses) has all its
agents GL-refutable — the predicate of the count, tied to the theorem. -/
theorem dead_class_stays :
    ∀ l ∈ allOrderings, (l.idxOf not0 < l.idxOf cross10 ∧ l.idxOf not0 < l.idxOf cross0) →
      ∀ χ : Modal.Formula ℕ, IsAgent l χ → Modal.GL ⊢ ∼χ := by
  intro l hl hpred χ h
  have hl' := allOrderings_sub_byClass l hl
  simp only [byClass, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- 12 cross-first, 3 escapers, 1 odd: the dead predicate is false
  all_goals first
    | exact absurd hpred (by decide)
    | skip
  -- 8 dead
  · exact dead_stays (l₁ := []) (l₂ := [cross10, not10, cross0]) (by simp) h
  · exact dead_stays (l₁ := []) (l₂ := [cross10, cross0, not10]) (by simp) h
  · exact dead_stays (l₁ := []) (l₂ := [not10, cross10, cross0]) (by simp) h
  · exact dead_stays (l₁ := []) (l₂ := [not10, cross0, cross10]) (by simp) h
  · exact dead_stays (l₁ := []) (l₂ := [cross0, cross10, not10]) (by simp) h
  · exact dead_stays (l₁ := []) (l₂ := [cross0, not10, cross10]) (by simp) h
  · exact dead_stays (l₁ := [not10]) (l₂ := [cross10, cross0]) (by simp [not10, Clause.isCross]) h
  · exact dead_stays (l₁ := [not10]) (l₂ := [cross0, cross10]) (by simp [not10, Clause.isCross]) h

end Cleanroom.Decision.DpTrollBridge.AuditR2
