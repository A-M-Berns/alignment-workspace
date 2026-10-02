import Cleanroom.Found.LiQuoteLane.OneWay
import Cleanroom.Found.LiQuoteLane.CrossQuote
import LogicalInduction.Construction.Quotation.MarketQuoteCodes

/-!
# `li-quote-lane` · MirrorPair: the ledger instance of the cross-market quote package (T2.4)

The mirror one-way pair, `A` reads `H`: `H` is any market with a `MarketComputation` (e.g. FAF's
`liaMarketComputation`), `X` an e.c. LUV family, `f` a deferral function, and `A`'s process
records `H`'s *realized* future expectations `𝔼^H_{f n}(X n)` — FAF's exact rational
`MarketComputation.expectQuoteAt X n (f n)` — as decided ledger literals at the payout schedule
`σ`. Then `CrossQuotePackage H DPA f X (ledgerLuv 0)` is a **theorem** (`reflected` is T1.2,
`quote_codes` is T1.3), and `A := liaHistory DPA` is an inductor over `DPA` (T6.1's argument in
the `A`-reads-`H` direction, `expectQuoteAt_computable` for the table). This makes the package
non-vacuous with two distinct markets inside this package.

**Fidelity: variant** — ledger-recorded determinacy (the process records `H`'s realized
expectation as decided fresh literals) in place of `Γ_A`-provable determinacy (Σ₁-completeness of
`Γ_A` about `H`'s machine; `li-coupled-pair`). **Scope clause:** at day `n` the quote LUV is not
yet decided in `A`'s process — no literal of `ledgerLuv 0 n` is present before stage
`(σ 0).e n` (`ledgerLuv_absent_before_payout`), so `A`'s day-`n` price of it is a genuine
forecast when `n < (σ 0).e n`; and two mirror one-way pairs do not make a two-way pair: do not
cite this file and `OneWay.lean` together as "`H` reads `A` and `A` reads `H`". Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc

/-- The published table of the mirror pair: `H`'s exact rational day-`f n` expectation of `X n`
(FAF's `MarketComputation.expectQuoteAt`), the same number for every item index.
Source: root-deference-036 (the contract `C_n` paying `Y_n`); [[faithful-acceleration]] §3 ("`A` reads `H`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def realizedExpectation {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (_j n : ℕ) : ℚ :=
  M.expectQuoteAt X n (f.f n)

/-- The table is computable from `X`'s e.c. certificate (FAF's `expectQuoteAt_computable`) and
the deferral function's computability.
Source: mandate T2.4; FAF `MarketComputation.expectQuoteAt_computable`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem realizedExpectation_computable {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (f : DeferralFunction) :
    Computable fun p : ℕ × ℕ => realizedExpectation M X f p.1 p.2 :=
  (((M.expectQuoteAt_computable hX).comp
    (Computable.snd.pair (f.computable.comp Computable.snd))).of_eq fun p => rfl : _)

/-- **T2.4 (headline, N+). The cross-market quote package is a theorem over the mirror ledger:**
`A`'s process `ledgerProcess base (realizedExpectation M X f) σ` determines the ledger LUV
`ledgerLuv 0 n` at `𝔼^H_{f n}(X n)` (T1.2 plus `expectQuoteAt_cast`), and the family is e.c.
(T1.3). Scope: one-way (`A` reads `H`); Fidelity: variant (module docstring).
Source: [[faithful-acceleration]] §4(II) (root-fa-002); [[deference-in-logical-induction-v6]] §5.2 ("`A` reads `H`"); root-fa-001 variant (ii) with the roles swapped
Kind: C
Fidelity: variant: ledger-recorded determinacy in place of `Γ_A`-provable determinacy
Hyps: (a) none -/
theorem crossQuotePackage_mirror {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (f : DeferralFunction) (base : DeductiveProcess) (σ : ℕ → PublicationSchedule) :
    CrossQuotePackage H (ledgerProcess base (realizedExpectation M X f) σ) f X
      (fun n => ledgerLuv 0 n) := by
  refine ⟨ledgerLuv_thresholdCodes 0, fun n => ?_⟩
  have h := ledgerLuv_determinedVia base (realizedExpectation M X f) σ
    (fun _ n => M.expectQuoteAt_mem_Icc X n (f.f n)) 0 n
  rw [M.expectQuoteAt_cast X n (f.f n)]
  exact h

/-- **T2.4, the mirror inductor:** `A := liaHistory` over the mirror ledger process is a logical
inductor over it (T6.1's argument in the `A`-reads-`H` direction).
Source: mandate T2.4
Kind: C
Fidelity: variant: plain trader class
Hyps: (a) none -/
theorem mirrorPair_inductor {H : History} (M : MarketComputation H) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (f : DeferralFunction) (base : DeductiveProcess)
    (hbase : ComputableDeductiveProcess base) (σ : ℕ → PublicationSchedule)
    (hσ : Computable fun p : ℕ × ℕ => (σ p.1).e p.2) :
    IsLogicalInductor (liaHistory (ledgerProcess base (realizedExpectation M X f) σ))
      (ledgerProcess base (realizedExpectation M X f) σ) :=
  LIA_is_logical_inductor _
    (ledgerProcess_computable hbase (realizedExpectation_computable M X hX f) hσ)

/-- **Scope clause, proved:** no literal of item `j`'s day-`n` ledger LUV is present at any stage
before its publication stage `(σ j).e n` — so at day `n < (σ j).e n` the reader's price of it is
a forecast, not a lookup.
Source: mandate T2.4 (scope clause)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLuv_absent_before_payout (a : ℕ → ℕ → ℚ) (σ : ℕ → PublicationSchedule)
    (j n : ℕ) (r : ℚ) (b : Bool) {s : ℕ} (hs : s < (σ j).e n) :
    (ledgerFamily, ledgerPayload j n (Encodable.encode r), b) ∉ (ledgerSchedule a σ).lits s := by
  intro h
  rw [ledgerSchedule_mem_iff] at h
  omega

end Cleanroom.Found.LiQuoteLane
