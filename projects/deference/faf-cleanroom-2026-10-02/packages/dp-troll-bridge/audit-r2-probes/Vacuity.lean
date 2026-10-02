/-
  Audit round 2, adversarial lens: GL-level probes against `dp-troll-bridge` after repair
  round 1.

  Not imported by the library. Elaborated with `scripts/lean-check`. The audit file
  `dp-troll-bridge-audit-r2-adversarial.md` reads the results.

  Probes:
  1. `binding_coin_lob_stalls` (target 7(b)) admits a sharper countermodel than the package's:
     on the three-world chain the deliberate atom `d` is TRUE at the refuting world (the
     agent deliberately crosses, the coin fires one world up), and the boxed schema still
     holds there. The package's two-world model has `∼d` throughout, so its schema is never
     tested against its antecedent (round-1 adversarial N9); this one tests it.
  2. The exploring-agent schema collapses exactly as target 3 does: `⊡(Hexp x d) 🡘 ⊡(∼d)`.
     So `exploring_lesion`'s Löb content is one axiom-L step, the same as `stays_schema`.
  3. The Proposition-10 family after repair: `provable_crosser_not_afflicted` is one modus
     ponens over FAF's `unprovable_box_bot`, `top_not_afflicted` is `unprovable_box_bot`
     itself up to propositional logic, and `tiling_not_afflicted_provable` is one `cl_prover`
     over `boxdotH_atom_con` — grades, not defects.
  4. The fallible threshold at the boundary `q = 1/2` is the `⊤` branch (the doc's
     "`q ≤ 1/2`, 𝔄 crosses"), so the definition agrees with the source at the boundary.
  5. `crossFirst_iff_boxBot` at a one-clause ordering `[cross10]` (the degenerate end of its
     generality): the agent of "cross iff you can prove crossing safe" is `□⊥`.
-/

import Cleanroom.Decision.DpTrollBridge.Orderings
import Cleanroom.Decision.DpTrollBridge.Lesion
import Cleanroom.Decision.DpTrollBridge.Countermodels
import Cleanroom.Decision.DpTrollBridge.Fallible

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge.AuditR2

/-! ## Probe 1: the binding coin with a deliberate crossing at the refuting world -/

/-- Valuation on the three-world chain: `d` true at `w0` only, `x` true at `w1` only. -/
def chain3ValCoin (x d : ℕ) : Kripke.Valuation chain3Frame :=
  fun a w => (a = d ∧ w = (0 : Fin 3)) ∨ (a = x ∧ w = (1 : Fin 3))

/-- `GL ⊬ ⊡(Hcoin x d) 🡒 ((x ⋎ d) 🡒 □⊥)`, refuted at a world where the agent
*deliberately* crosses (`d` true at `w0`). The boxed schema holds at `w0` because its
antecedent `□((x ⋎ d) 🡒 □⊥)` fails there (at `w1` the coin fires and `w1` is not a dead end),
not because `∼d` holds. Sharper witness than the package's two-world model. -/
theorem binding_coin_lob_stalls_deliberate (x d : ℕ) (hxd : x ≠ d) :
    Modal.GL ⊬ (⊡(Hcoin x d) 🡒 ((.atom x ⋎ .atom d : Modal.Formula ℕ) 🡒 □⊥)) :=
  unprovable_of_countermodel chain3Frame chain3Frame_isGL (chain3ValCoin x d) chain3W0
    (by
      simp [Formula.Kripke.Satisfies, Hcoin, chain3Frame, chain3ValCoin, chain3W0, hxd,
        hxd.symm]
      try decide)

/-- The package's own model has `∼d` everywhere (so its schema is satisfied for the trivial
reason): `chainValAt x` makes `d` false at both worlds when `x ≠ d`. -/
example (x d : ℕ) (hxd : x ≠ d) (w : chainFrame.World) : ¬ chainValAt x d w := by
  simp [chainValAt, hxd.symm]

/-! ## Probe 2: the exploring-agent schema is boxed non-deliberate-crossing -/

/-- `GL ⊢ ⊡(Hexp x d) 🡘 ⊡(∼d)`: the same collapse as `boxdotH_iff_boxdot_neg`. So the Löb
content of target 7(a) (`exploring_lesion`, `exploring_deliberate_stays`) is one axiom-L step,
exactly as target 3's. -/
theorem boxdotHexp_iff_boxdot_neg (x d : ℕ) :
    Modal.GL ⊢ ⊡(Hexp x d) 🡘 ⊡(∼(.atom d : Modal.Formula ℕ)) := by
  have h1 : Modal.GL ⊢ ⊡(Hexp x d) 🡒 ∼(.atom d) := exploring_deliberate_stays x d
  have hself : Modal.GL ⊢ ⊡(Hexp x d) 🡒 □(⊡(Hexp x d)) := boxdot_self_box (Hexp x d)
  have h2 : Modal.GL ⊢ □(⊡(Hexp x d)) 🡒 □(∼(.atom d : Modal.Formula ℕ)) :=
    imply_box_distribute'! h1
  have h3 : Modal.GL ⊢ ∼(.atom d : Modal.Formula ℕ) 🡒 Hexp x d := by
    simp only [Hexp]; cl_prover
  have h4 : Modal.GL ⊢ □(∼(.atom d : Modal.Formula ℕ)) 🡒 □(Hexp x d) :=
    imply_box_distribute'! h3
  cl_prover [h1, hself, h2, h3, h4]

/-- Consequently `exploring_lesion` reads, at the statement level, `⊡(∼d) 🡒 (cross 🡒 bad)`,
which is propositional (under `∼d`, `cross 🡒 bad` is `d 🡒 x ⋎ □⊥`). -/
example (x d : ℕ) :
    Modal.GL ⊢ ⊡(∼(.atom d : Modal.Formula ℕ)) 🡒 (exploringCross x d 🡒 exploringBad x d) := by
  simp only [exploringCross, exploringBad]
  cl_prover

/-! ## Probe 3: the Proposition-10 family is plumbing over FAF's Gödel 2 -/

/-- `provable_crosser_not_afflicted` is one modus ponens over `unprovable_box_bot`. -/
example {c : Modal.Formula ℕ} (hc : Modal.GL ⊢ c) : Modal.GL ⊬ (c 🡒 □⊥) :=
  fun h => unprovable_box_bot (h ⨀ hc)

/-- `top_not_afflicted` is `unprovable_box_bot` up to propositional logic. -/
example : Modal.GL ⊬ ((⊤ : Modal.Formula ℕ) 🡒 □⊥) :=
  fun h => unprovable_box_bot (by cl_prover [h])

/-- `tiling_not_afflicted_provable` is one `cl_prover` over `boxdotH_atom_con`. -/
example (p : ℕ) {c : Modal.Formula ℕ} (hc : Modal.GL ⊢ c) :
    Modal.GL ⊬ (⊡(H (.atom p)) 🡒 (c 🡒 □⊥)) :=
  fun h => boxdotH_atom_con p (by cl_prover [h, hc])

/-- Conversely, `boxdotH_atom_con` is `tiling_not_afflicted_provable` at `c := ⊤`: the two
are the same fact. -/
example (p : ℕ) : Modal.GL ⊬ (⊡(H (.atom p : Modal.Formula ℕ)) 🡒 □⊥) :=
  fun h => tiling_not_afflicted_provable p verum! (by cl_prover [h])

/-! ## Probe 4: the fallible threshold at the boundary -/

/-- At `q = 1/2` exactly, `Hq` is the `⊤` branch — the doc's "for `q ≤ 1/2` … 𝔄 crosses". -/
example (c : Modal.Formula ℕ) : Hq (1 / 2) c = ⊤ := by
  unfold Hq
  rw [if_neg (lt_irrefl _)]

/-! ## Probe 5: the cross-first theorem at its degenerate end -/

/-- A one-clause ordering `[cross10]` ("cross iff you can prove crossing is safe") has the
agent `□⊥`: `crossFirst_iff_boxBot` applies with `rest := []`. -/
example {χ : Modal.Formula ℕ} (h : IsAgent [cross10] χ) : Modal.GL ⊢ χ 🡘 □⊥ :=
  crossFirst_iff_boxBot (Or.inl rfl) (by simp) h

/-- And `□⊥` is its agent: `χ ↔ □(χ 🡒 ∼□⊥)` at `χ := □⊥` is `□⊥ ↔ □∼□⊥`, Gödel 2. -/
example : IsAgent [cross10] (□⊥) :=
  boxBot_isAgent_crossFirst (Or.inl rfl) (by simp)

end Cleanroom.Decision.DpTrollBridge.AuditR2
