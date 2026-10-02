import Cleanroom.Trust.LegitLiRegister.Defs
import Cleanroom.Deference.DefFrozenSibling.Tracking

/-!
# `legit-li-register` · Certificate: the legitimacy certificate and C1's blindness audit
(Target 13)

[[legitimacy-theory-v1]] §4 (root-fa-043): alongside each quote `a_n`, `A` publishes a
**legitimacy certificate** `ℓ_n := 𝔼^A_n(⌜d_n⌝)`; C1 says its sealed-sibling component is a blind
target so "the T1 argument applies verbatim". root-fa-2-012 audits C1: the single LUV `⌜d_n⌝` is
quote-referencing (its coupled half reads `Hplus (F n)`, an inductor over a process containing
`a_n`), and the sealed component alone *is* T1's target. The repair the inventory names: publish
**two** contracts and define the certificate as their gap.

Over FAF: `certSealed S n := 𝔼^A_n(C_n)` is, by the carrier's `a_eq`, the published quote itself
(`certSealed_eq_quote`) — **C1 is T1 renamed, made literal**: its faithfulness is `tracking`
(`certSealed_tracks`). The coupled component `certCoupled S Z n := 𝔼^A_n(Z_n)` reads a
cross-quote LUV `Z_n` of `A`'s language reflecting the advised reasoner's day-`F n` expectation of
`𝟙(P^{(n)})`, taken as a `li-quote-lane` `CrossQuotePackage` **parameter** (one-way data, grade
(a) for the carrier; the package's own `reflected` is `li-quote-lane`'s (c) until discharged, as
its docstring says). The certificate is `|certCoupled − certSealed|`, the two-contract estimate of
`d_n`; no theorem about the coupled component's grade is stated here (that is `fa-theorem-a`'s
averaged unbiasedness, cited in the report). The finding (blocking for §4's grounding argument):
the certificate as a single `A`-LUV is quote-referencing; the formal shape is Target 1's "`defect`
is not a function of the shared data" — the stretch two-system witness is not built (report).
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- **C1's sealed component**: the predictor's day-`n` expectation of the contract LUV `C_n`
(settled to the sibling's verdict) — the certificate's blind half.
Source: [[legitimacy-theory-v1]] §4 C1 (root-fa-043); root-fa-2-012 (ii)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def certSealed (S : FrozenSystem) (n : ℕ) : ℝ := (ledgerLuv 0 n).expect S.A n

/-- **C1 is T1 renamed**: the sealed component of the certificate *is* the published quote
(`a_eq`).
Source: root-fa-2-012 (ii) ("C1 is T1's target itself"); mandate Target 13
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem certSealed_eq_quote (S : FrozenSystem) (n : ℕ) : certSealed S n = S.a n :=
  (S.a_eq n).symm

/-- **C1's faithfulness is T1**: the sealed certificate tracks the sibling's verdict, with T1's
`hz` and nothing else. Two-way: `partial: over the OPEN pair` as `tracking`.
Source: [[legitimacy-theory-v1]] §4 C1 ("the T1 argument applies verbatim"); root-fa-2-012
Kind: L (`tracking` restated)
Fidelity: exact (it is T1)
Hyps: (c) `hz` (row 6); all else (a) -/
theorem certSealed_tracks (S : FrozenSystem) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    (fun n => certSealed S n) ≈ₙ (fun n => (S.Y n : ℝ)) := by
  have he : (fun n => certSealed S n) = fun n => (S.a n : ℝ) := funext (certSealed_eq_quote S)
  rw [he]
  exact tracking S zhat hz hlim

/-- **The coupled component**: the predictor's day-`n` expectation of a cross-quote LUV `Z_n` —
a second ledger item in `A`'s language, which (under the package below) reflects the advised
reasoner's day-`F n` expectation of `𝟙(P^{(n)})`.
Source: root-fa-2-012 (the two-contract repair, `ℓ⁺_n`); mandate Target 13
Kind: D
Fidelity: variant: the coupled verdict quoted as the expectation of the indicator LUV (FAF's `thm:ei` relates it to the price)
Hyps: n/a -/
noncomputable def certCoupled (S : FrozenSystem) (Z : ℕ → LUV) (n : ℕ) : ℝ := (Z n).expect S.A n

/-- **The coupled-quote package** for the certificate: `Z` is e.c. and every completed-theory world
of `A`'s process values `Z n` at `𝔼^{Hplus}_{F n}(𝟙 P^{(n)})` — `li-quote-lane`'s
`CrossQuotePackage` at the indicator family, taken as data.
Source: root-fa-2-012; `li-quote-lane` `CrossQuotePackage`
Kind: D
Fidelity: exact (the package of record)
Hyps: n/a -/
abbrev CertPackage (S : FrozenSystem) (Z : ℕ → LUV) : Prop :=
  CrossQuotePackage S.Hplus S.processA S.F (fun n => LUV.indicatorOf (S.contract n)) Z

/-- **The two-contract certificate**: the gap between the coupled and the sealed component — an
*estimate* of `d_n` whose two halves have the corpus's two known grades (T1 for the sealed half;
the averaged feedback grade for the coupled half, not stated here).
Source: root-fa-2-012 ("define the certificate as `|ℓ⁺_n − ℓ^sealed_n|`"); mandate Target 13
Kind: D
Fidelity: variant: the inventory's repair, not the note's single LUV `⌜d_n⌝`
Hyps: n/a -/
noncomputable def certificate (S : FrozenSystem) (Z : ℕ → LUV) (n : ℕ) : ℝ :=
  |certCoupled S Z n - certSealed S n|

/-- Under the package, the coupled quote's settled value is the advised reasoner's horizon
expectation of the indicator of the contract (the package's own field, named for the certificate).
Source: `li-quote-lane` `CrossQuotePackage.reflected`
Kind: L
Fidelity: n/a
Hyps: (a) (the package is data) -/
theorem certCoupled_target (S : FrozenSystem) (Z : ℕ → LUV) (hZ : CertPackage S Z) (n : ℕ) :
    LUV.DeterminedVia (Z n) S.processA
      ((LUV.indicatorOf (S.contract n)).expect S.Hplus (S.F.f n)) :=
  hZ.reflected n

end Cleanroom.Trust.LegitLiRegister
