import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-self-trust` — target 3: the self-case diamond

root-deference-020 (v6 §3.2 table): for the future self `E* = E^H_{f(n)}` every deference
hypothesis is an LI theorem — Mart (`cee`), the conditional tower (`ccee`), Total Trust (`st`),
and (the inventory claims) Value "unconditionally for every e.c. menu", so that "the whole
diamond is a theorem". This file states the diamond as **one conjunction of separately proved
vertices** (mandate design decision 6: no arrow theorems between them — an arrow
`Tower → TotalTrust` proved by discarding its hypothesis is a `T` row and is not written):

* `selfCase_twoOptionValue`: the Value vertex **at two-option grade** — δ-hedged Value against
  the constant option on every two-option menu `{X, s}`, derived from `est` through
  `def-lattice`'s `twoOptionComb_value_iff_productForm` (an iff, so this vertex is `est`
  restated on the hedged combination: Kind L);
* `selfCase_diamond`: the four-vertex conjunction with `Tower` stated on valued sources
  (exactly what `cee` gives), `CondTower`, `TotalTrust`, and the two-option Value vertex — no
  false antecedent, no arrows.

**Repair round 1.** The round-1 file also carried `selfCase_diamond` in a conditional form
`(∀ X, e.c. X → Valued X) → Tower ∧ CondTower ∧ TotalTrust`, whose antecedent is refutable over
`paperDP T` (`SelfInstances.lean` `not_all_valued`), so that theorem was vacuous (round-1
adversarial audit B1, fidelity audit N3). It was deleted and the honest conjunction (round 1's
`selfCase_diamond_valued`) now carries the natural name.

**What is not claimed.** General-menu `Value P DP (Expert.self P DP f)`: the corpus's own scope
note ([[deference-notions]] §Value, ⚠ 2026-07-25; `def-lattice`'s `Value` docstring) says
unconditional argmax Value is false for inductor experts on selection-referencing menus, and the
proof of that is `def-argmax-value`'s. Finding F1 of this package: the inventory's
"unconditionally for every e.c. menu" over-claims; the Value vertex is a theorem at two-option
grade (δ-hedged, against the constant) and a `def-argmax-value` question at general grade. No
`Value` row here is `proved` beyond two options.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The Value vertex at two-option grade** (δ-hedged Value against the constant option): for
every `(s, δ)` with `δ > 0`, every e.c. source `X` and every ramp `WeightQuote` `(W, XW)`, the
hedged strategy `Ŝ = X·w + s(1 − w)` (`def-lattice`'s `twoOptionComb`) is worth at least the
constant option's face value in the limit: `E^H_n(Ŝ_n) ≳ₙ s` on the two-option menu `{X, s}`
toward the future self. One-sided: it does not say the hedged strategy is worth at least
`E_n(X_n)`. Derived from `est` through `twoOptionComb_value_iff_productForm`, which is an
**iff** by linearity of `LUVCombination.expect` — so this vertex is `est` restated on the hedged
combination, not a fourth independent truth (the content of "this combination is the followed
strategy" is `WeightQuote`'s reflection clause; no `loe`). Not general-menu Value (module
docstring); per [[deference-notions]]'s terminological default the δ-hedged variant always
carries its qualifier and is never "Value" simpliciter.
Source: root-deference-020 (the Value row, at two-option grade); [[two-option-value-iff-total-trust]]
§Soft/LI form; `def-lattice` `twoOptionComb_value_of_softTotalTrustAbove`
Kind: L
Fidelity: weaker: two-option menus only, δ-hedged, against the constant (general-menu Value is
`def-argmax-value`'s question)
Hyps: (a); `hinj` -/
theorem selfCase_twoOptionValue (f : DeferralFunction) (hinj : Function.Injective f.f) (s : ℚ)
    {δ : ℚ} (hδ : 0 < δ) (X W XW : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (q : WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
      (rampAbove δ s) W XW) :
    (fun n => (twoOptionComb s XW W n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (s : ℝ)) :=
  twoOptionComb_value_of_softTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
    (selfSoftTotalTrustAbove T f hinj s hδ) hX q

/-- **The self-case diamond** (load-bearing 3): the Tower vertex on world-valued sources
(exactly what `cee` gives; the predicate `Tower` is not reached, finding F4 /
`not_all_valued`), `CondTower`, `TotalTrust`, and the two-option Value vertex, in one
conjunction — three separately proved truths (`selfTower_valued`, `selfCondTower`,
`selfTotalTrust`) plus the definitional restatement of the third on the hedged two-option
combination (`selfCase_twoOptionValue`); no false antecedent, no arrows. Propositional plumbing
over its vertices (the mandate labels target 3 "C composition"; the conjunction itself is L, the
vertices are C).
Source: root-deference-020 ("the whole diamond is a theorem"); v6 §3.2 table (rows Mart, ccee,
Total Trust, Value)
Kind: L
Fidelity: weaker: `Tower` restricted to valued sources (F4); Value at two-option grade,
δ-hedged, against the constant (F1)
Hyps: (a); `hinj` -/
theorem selfCase_diamond (f : DeferralFunction) (hinj : Function.Injective f.f) :
    (∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
        Valued (paperDP T) X →
        Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X Y →
        (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
          (fun n => (Y n).expect (liaHistory (paperDP T)) n)) ∧
      CondTower (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ∧
      TotalTrust (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ∧
      (∀ (s δ : ℚ), 0 < δ → ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X →
        WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
          (rampAbove δ s) W XW →
        (fun n => (twoOptionComb s XW W n).expect (liaHistory (paperDP T)) n) ≳ₙ
          (fun _ => (s : ℝ))) :=
  ⟨fun X Y hX hY hval hR => selfTower_valued T f X Y hX hY hval hR, selfCondTower T f,
    selfTotalTrust T f hinj,
    fun s _ hδ X W XW hX q => selfCase_twoOptionValue T f hinj s hδ X W XW hX q⟩

/-- The diamond over `𝗣𝗔` at `succDeferral`: the instance binders of the section variable are
discharged (mandate design decision 1, "no binder left unwitnessed") — this is an
instantiability check, not a non-vacuity witness.
Source: mandate design decision 1
Kind: L
Fidelity: n/a -/
example : CondTower (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) ∧
    TotalTrust (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) :=
  ⟨(selfCase_diamond 𝗣𝗔 succDeferral succDeferral_injective).2.1,
    (selfCase_diamond 𝗣𝗔 succDeferral succDeferral_injective).2.2.1⟩

end

end Cleanroom.Deference.DefSelfTrust
