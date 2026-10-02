import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Deference.DefSelfTrust.Weights

/-!
# `legit-li-register` · Modification: corrigibility as legitimacy-endorsement of a modification
map (Target 10)

trust-lab-2-002: "`A` is corrigible w.r.t. `M`, to `H`, iff `H` LUV-Total-Trusts the estimate
stream 'the world after `H` exercises `M`'"; the composition conjecture (trust toward each of a
family of futures ⟹ trust toward their `H`-selected mixture); "resistance is an illegitimacy
signature". trust-lab-2-003: the Soares-type tension.

Over `trust-merge`'s definition of record: **"the world after `H` exercises `M`" has no FAF
object** — the expert is a *parameter* (`Expert DP`, `def-lattice`'s carrier), disclosed:
`CorrigibleWrt N DP E := LUVTotalTrustDay N DP E` is a definition on an expert given as data (D).
The composition conjecture is the **closure lemma** the inventory names — trust toward two experts
on the same deferral implies trust toward their selection by a generable `[0,1]` selector
(`mixExpert`) — stated OPEN (`corrigible_selection_closure_open`): the per-day clause `CondTower`
quantifies over quote packages, and the quote package of a mixture is not in `trust-merge`
(report, "Not done"). "Resistance is an illegitimacy signature" is ill-posed (findings); 2-003 is
recorded (ATTRIBUTION-UNVETTED on the Soares analogy).
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction Cleanroom.Found.DefLattice Cleanroom.Trust.TrustMerge
  Cleanroom.Deference.DefSelfTrust

/-- **Corrigible with respect to a modification map, as LUV-Total-Trust of its expert**: the
reader `N` (over `DP`) LUV-Total-Trusts (per-day grade, `trust-merge`'s definition of record) the
expert whose estimate stream is "the world after the modification" — **an expert given as data**;
nothing here says what a modification is or produces the expert from a map.
Source: trust-lab-2-002 ("`A` is corrigible w.r.t. `M`, to `H`, iff `H` LUV-Total-Trusts the estimate stream"); mandate Target 10
Kind: D
Fidelity: variant: the modified world's estimate stream is a parameter (no FAF object for "the world after `H` exercises `M`"); per-day grade
Hyps: n/a -/
def CorrigibleWrt (N : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  LUVTotalTrustDay N DP E

/-- A convex combination of two `[0,1]` prices stays in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mix_mem_Icc {s x y : ℝ} (hs : 0 ≤ s ∧ s ≤ 1) (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) : 0 ≤ s * x + (1 - s) * y ∧ s * x + (1 - s) * y ≤ 1 := by
  constructor
  · nlinarith [hs.1, hs.2, hx.1, hx.2, hy.1, hy.2]
  · nlinarith [hs.1, hs.2, hx.1, hx.2, hy.1, hy.2]

/-- **The selected expert**: the day-`n` mixture `s_n · E₁ + (1 − s_n) · E₂` of two experts on
the same deferral, selected by a `[0,1]` sequence `s` ("`H` selects which future").
Source: trust-lab-2-002 (the closure-under-selection reading of the composition conjecture)
Kind: D
Fidelity: variant: a two-expert mixture with a day-indexed selector
Hyps: n/a -/
def mixExpert {DP : DeductiveProcess} (s : ℕ → ℚ) (hs : ∀ n, 0 ≤ s n ∧ s n ≤ 1)
    (E₁ E₂ : Expert DP) : Expert DP where
  A := fun n φ => (s n : ℝ) * E₁.A n φ + (1 - (s n : ℝ)) * E₂.A n φ
  f := E₁.f
  range := fun n φ => mix_mem_Icc ⟨by exact_mod_cast (hs n).1, by exact_mod_cast (hs n).2⟩
    (E₁.range n φ) (E₂.range n φ)

/-- **OPEN — closure of corrigibility under generable selection** (the composition conjecture as
the closure lemma): if `N` is corrigible w.r.t. two experts on the same deferral, it is corrigible
w.r.t. their selection by any `N`-generable `[0,1]` selector. Route: linearity of the weighted
cross-defect and `pgenerableRat_mul` for the product weight `s · w`; what is missing is the quote
package (`CondQuote`) of the mixture, which `trust-merge` does not provide.
Source: trust-lab-2-002 (composition conjecture); mandate Target 10
Kind: OPEN
Fidelity: variant: two experts, a generable selector
Hyps: n/a -/
theorem corrigible_selection_closure_open (N : History) (DP : DeductiveProcess)
    (E₁ E₂ : Expert DP) (hf : E₁.f = E₂.f) (s : ℕ → ℚ) (hs : ∀ n, 0 ≤ s n ∧ s n ≤ 1)
    (hgen : PGenerableRat N s) (h₁ : CorrigibleWrt N DP E₁) (h₂ : CorrigibleWrt N DP E₂) :
    CorrigibleWrt N DP (mixExpert s hs E₁ E₂) := by
  sorry

end Cleanroom.Trust.LegitLiRegister
