import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Construction.Quotation.Packages

/-!
# `fa-theorem-a` · Cee: ingredient (I) at grade (a) — self-trust on the same market (T8)

FA's ingredient (I) ([[faithful-acceleration]] §2 line 31, §4 line 72; root-fa-009): on *one*
market `P`, the day-`n` expectation of `X_n` and the day-`n` expectation of the quote
`⌜𝔼^P_{f n}(X_n)⌝` agree asymptotically — LI's `thm:cee` (expected future expectations). FAF
proves it as `lic_expected_future_expectations_ofRepresentation`, whose `reflected` premise is
literally `CrossQuotePackage.reflected` at `H = A = P` unfolded through `LUV.DeterminedVia`. This
file only *provides* the fact in the package's vocabulary: it is the free half of every Half-2
route (`fa-forcing-trader`'s `cee` lane). Its witness is `li-quote-lane`'s
`crossQuotePackage_paper_self` (N−: same market by construction; the closed form
`lic_expected_future_expectations_closed` is the same fact). Heavy import
(`Construction.Quotation.Packages`): own file, imported only by the root module.

Scope: same market (`H = A = P`) — not a two-market statement; nothing here is about delay.
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **T8. Ingredient (I) at grade (a): `cee` on the same market.** For `[IsLogicalInductor P DP]`
and a quote package `pkg : CrossQuotePackage P DP f X Y` with both sides the *same* market `P`,
an e.c. source family `X` whose members every completed-theory world values, and `hworld`:
`(fun n => 𝔼^P_n(X_n)) ≈ₙ (fun n => 𝔼^P_n(Y_n))`. One FAF application
(`lic_expected_future_expectations_ofRepresentation`), with `pkg.quote_codes` and
`pkg.reflected` supplying `hY` and `reflected`.
Scope: same market. Here `reflected` is FAF's own `thm:cee` premise (the Σ₁ quotation of `P`'s
own run), not the two-market (c); at the self-witness it is FAF's `.reflected`.
Source: [[faithful-acceleration]] §2 line 31, §4 line 72 (root-fa-009; rigor critique 6); FAF `thm:cee`
Kind: L
Fidelity: exact (same-market projection of the package)
Hyps: (a) `hX`, `source_valued`, `hworld` (FAF's `thm:cee` boundaries); `pkg.reflected` is FAF's own premise here. -/
theorem cee_ofCrossQuote {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage P DP f X Y)
    (hX : LUV.MachineThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AsympEq (fun n => (X n).expect P n) (fun n => (Y n).expect P n) :=
  lic_expected_future_expectations_ofRepresentation f X Y hX pkg.quote_codes source_valued
    (fun n v hv => pkg.reflected n v hv) hworld

end Cleanroom.Fa.FaTheoremA
