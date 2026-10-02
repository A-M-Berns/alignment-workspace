import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Found.DefLattice.BetClass
import Cleanroom.Found.LiQuoteLane.Defs

/-!
# `trust-merge` · HardCertificate: no hard in-advance certificate (T8, `core` statement)

**trust-lab-2-005 / 2-021.** The lab's limitative companion to the definition of record: a
*hard* in-advance legitimacy certificate — Total Trust at the hard weight `1[s ≤ est(X_n)]` —
is not a `ccee`/`wub`-shaped object, because the hard indicator is outside the generable-weight
vocabulary. `HardCrossTrustAbove` names the comparison object (the `Est` form of `def-lattice`'s
`HardTotalTrustAbove`), and `ledgerThreshold_hardIndicator_not_generable` transports
`def-lattice`'s `no_generable_hard_indicator` to the merge's ledger atoms: no expressible feature
denotes the hard indicator of the reader's price of a ledger threshold `⌜α_{j,n} > q⌝`, on
`[0,1]`-valued histories — `EF.denote` is continuous in the prices and the step is not. **What
the lemma is and is not about** (audit r1, fidelity N2 / adversarial N6): it concerns the step
of *one threshold's price at `1/2`*, not `HardCrossTrustAbove`'s weight `1[s ≤ est X n]` with
`est X n = 𝔼^H_n(α_{j,n})` (a Riemann sum of threshold prices) at an arbitrary `s`; the extension
(the indicator of a continuous function of finitely many prices is not an `EF`) is the same
argument and is not done, so `HardCrossTrustAbove` has no theorem. The name says what the lemma
is (renamed from `hardCrossTrust_not_generable` in repair round 1). The scope caveat of the
transported lemma stands: it excludes the *same-day* trade-weight reading (one feature read against
the current history); the deferred-day reading of a decided step sequence is a `PGenerableRat`
question not settled there or here.

**Not attempted (stretch):** the liar refutation of hard trust `N → E` on `1[𝔼_E(χ) > 1/2]` for
an `E` that is itself an inductor with `χ_n ↔ (E_n(χ_n) < 1/2)`, over the one-way pair with
`H` reading `E = A`. It needs `lic_paradox_resistance_ofDiagonal_unconditional` on `A` and
`ledger_quote_alias` to link `H`'s worlds to the arithmetical price fact, and must exhibit positive
gate mass (the hard gate's mass may vanish as `A_n(χ_n) → 1/2`, `li-diagonal`'s point) or be
stated at a soft gate; recorded in the findings (F-T8) with the two traps named. **2-021** (a
foreign expert over a richer language escapes the diagonal): no Lean — FAF is single-language;
ill-posed until "foreign" is a language-inclusion hypothesis (findings F-T8).
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane

/-- **The hard cross-trust certificate (comparison object only):** the above-threshold
inequality toward the abstract estimate at the hard weight `1[s ≤ est(X_n)]`
(`def-lattice`'s `hardAbove s`). Named so that the limitative statement has an object; the
transported lemma `ledgerThreshold_hardIndicator_not_generable` is about one threshold's price,
not about this weight (module docstring) — this predicate has no theorem.
Source: trust-lab-2-005 ("hard LUV-Total-Trust (`N → E`) on the weight `Ind_0(𝔼_E(χ) > ½)`");
`def-lattice` `HardTotalTrustAbove`
Kind: D
Fidelity: variant: `Est` form of the hard comparison object
Hyps: n/a -/
abbrev HardCrossTrustAbove (P : History) (DP : DeductiveProcess) (est : (ℕ → LUV) → ℕ → ℝ)
    (s : ℚ) : Prop :=
  ThresholdIneqAboveEst P DP est (hardAbove s) s

/-- **No expressible feature denotes the hard indicator of a ledger threshold price** — the
reader's price of `⌜α_{j,n} > q⌝` stepped at `1/2` — on `[0,1]`-valued histories.
`def-lattice`'s `no_generable_hard_indicator` at the merge's atoms: the cheap limitative
statement that a hard in-advance certificate is not a `ccee`/`wub`-shaped object. Scope as the
transported lemma's (same-day reading). About one threshold's price at `1/2`, not about
`HardCrossTrustAbove`'s weight (module docstring).
Source: trust-lab-2-005 (the negative half); `def-lattice` `no_generable_hard_indicator`
Kind: L
Fidelity: exact (an instance of the transported lemma; weaker than a statement about
`HardCrossTrustAbove`'s weight, which is not made)
Hyps: (a) none -/
theorem ledgerThreshold_hardIndicator_not_generable (n j : ℕ) (q : ℚ) :
    ¬ ∃ e : EF, ∀ P : History, (∀ m ψ, 0 ≤ P m ψ ∧ P m ψ ≤ 1) →
      e.denote P = if (1 / 2 : ℝ) ≤ P n ((ledgerLuv j n).gt q) then 1 else 0 :=
  no_generable_hard_indicator n ((ledgerLuv j n).gt q)

end Cleanroom.Trust.TrustMerge
