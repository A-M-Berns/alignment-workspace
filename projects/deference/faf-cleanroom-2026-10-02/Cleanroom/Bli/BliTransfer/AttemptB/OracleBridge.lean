import Cleanroom.Bli.BliTransfer.AttemptB.Certificate
import LogicalInduction.Construction.Freeze.Oracle

/-!
# `bli-transfer` · attempt B · OracleBridge: splice oracles from raw spellings and from FAF's
freeze oracle

Two ways to inhabit `SpliceOracle`:

* `SpliceOracle.ofRaw` — from an oracle whose output is the **literal raw spelling**
  `rawSerialize e ++ [8]` of the body (leaves as canonical runs `[0] ++ rpn ψ ++ [j]`, the
  mandate's spelling); `rawSerialize_contractsTo` is the contraction lemma that turns the
  literal form into the interface's contraction form. This is the shape `bli-assemble`'s tent
  oracle would be proved in.
* `SpliceOracle.ofRunOracle` — from **FAF's own `FreezeStep.RunOracle`**: a run-level freeze
  oracle emitting `[1, q, 8]` on selected cells *is* a splice oracle for the constant-body
  expression map `constMap sel quote` (`letE (price ψ k) (const q)` is exactly the freeze's
  administrative binding). Composed with `FreezeOracle.runOracleOf entries` — FAF's `FP`
  recognizer for any finite table, keyed by **parsing** (`tableLookup`), hence correct on
  every spelling — this gives a machine-checked splice oracle for every finite constant-body
  map (`SpliceOracle.ofTable`). It is the oracle behind T1.5's N+ witness, and it exhibits
  FAF's finite-support freeze as the constant-body special case of the splice.

This file is the one importing `Construction.Freeze.Oracle` (measured `lean-check` cost of
the bare import: 56 s wall on forge-verity, 2026-09-30, one run).

Sources: mandate T1.3 (the raw-body spelling), T1.5 (the witness oracle); FAF
`Construction/Freeze/Oracle.lean`, `Construction/Freeze/Step.lean:81`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open LogicalInduction.TokenFold LogicalInduction.FPFold Complexity Complexity.Cobham
open LogicalInduction.FreezeStep LogicalInduction.FreezeOracle

/-! ## Raw spellings -/

namespace EF

/-- The raw token spelling of a feature: `EF.serialize` with every price leaf's sentence
written as its canonical Polish run `[0] ++ rpn ψ ++ [j]` instead of its Gödel code. This is
what an oracle emits (a Gödel code of a small sentence can be doubly exponential in its
`tokenSize`; the canonical run is linear).
Source: mandate T1.3 ("the raw body's leaves must be spelled as canonical runs")
Kind: D
Fidelity: n/a -/
def rawSerialize : LogicalInduction.EF → List ℕ
  | .price φ n => 0 :: rpn φ ++ [n]
  | .const q => [1, Encodable.encode q]
  | .add a b => rawSerialize a ++ rawSerialize b ++ [2]
  | .mul a b => rawSerialize a ++ rawSerialize b ++ [3]
  | .max a b => rawSerialize a ++ rawSerialize b ++ [4]
  | .safeRecip a => rawSerialize a ++ [5]
  | .var i => [7, i]
  | .letE x b => rawSerialize x ++ rawSerialize b ++ [8]

/-- **The raw spelling contracts to the token-level serialization**: each canonical run is a
self-delimiting block (`parseRpn_rpn`), so `UnRpnContractsTo.priceChunk` contracts every leaf
and the payload/operator tokens are transparent.
Source: mandate T1.3
Kind: P
Fidelity: exact -/
lemma rawSerialize_contractsTo : ∀ e : LogicalInduction.EF,
    UnRpnContractsTo (rawSerialize e) e.serialize := by
  intro e
  induction e with
  | price φ n =>
      have hb : parseRpn (rpn φ).length (rpn φ) = some (φ, []) := by
        simpa using parseRpn_rpn φ [] (le_refl (rpn φ).length)
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        UnRpnContractsTo.priceChunk hb n
  | const q => exact UnRpnContractsTo.payload 1 _ (Or.inl rfl)
  | add a b iha ihb =>
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        (iha.append ihb).append (UnRpnContractsTo.single 2 (by norm_num))
  | mul a b iha ihb =>
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        (iha.append ihb).append (UnRpnContractsTo.single 3 (by norm_num))
  | max a b iha ihb =>
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        (iha.append ihb).append (UnRpnContractsTo.single 4 (by norm_num))
  | safeRecip a iha =>
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        iha.append (UnRpnContractsTo.single 5 (by norm_num))
  | var i => exact UnRpnContractsTo.payload 7 _ (Or.inr rfl)
  | letE x b ihx ihb =>
      simpa [rawSerialize, LogicalInduction.EF.serialize] using
        (ihx.append ihb).append (UnRpnContractsTo.single 8 (by norm_num))

end EF

/-- The raw body an oracle emits for an optional body: the raw spelling plus the close, or
nothing.
Source: mandate T1.3
Kind: D
Fidelity: n/a -/
def rawBody : Option LogicalInduction.EF → List ℕ
  | none => []
  | some e => EF.rawSerialize e ++ [8]

/-- The raw body contracts to the token-level body.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rawBody_contractsTo (o : Option LogicalInduction.EF) :
    UnRpnContractsTo (rawBody o) (bodyTokens o) := by
  cases o with
  | none => exact UnRpnContractsTo.nil
  | some e =>
      exact (EF.rawSerialize_contractsTo e).append (UnRpnContractsTo.single 8 (by norm_num))

/-- **A splice oracle from a literal-spelling oracle**: one whose decoded output *is* the raw
body (leaves as canonical runs). The mandate's T1.3 interface, verbatim, converted to the
contraction form of record.
Source: mandate T1.3
Kind: D
Fidelity: exact -/
def SpliceOracle.ofRaw (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (R : List Bool → List Bool) (hR : R ∈ FP)
    (hwf : ∀ tokW bufW : List Bool, BlockWF (R (pair tokW bufW)))
    (hspec : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) → ∀ bufW : List Bool, BlockWF bufW →
      ∀ ψ : Sentence, parseRpn (decodeBits bufW).length (decodeBits bufW) = some (ψ, []) →
        decodeBits (R (pair (digitsToBits cur) bufW)) = rawBody (expr (digitVal cur) ψ)) :
    SpliceOracle expr where
  R := R
  R_FP := hR
  R_wf := hwf
  R_spec := fun cur hcur bufW hbuf ψ hψ => by
    rw [hspec cur hcur bufW hbuf ψ hψ]
    exact rawBody_contractsTo _

/-! ## From FAF's freeze oracle -/

/-- The constant-body expression map of a selector and a quote table: `some (const (quote k ψ))`
where selected, `none` elsewhere. FAF's finite-support freeze is the splice along this map.
Source: mandate § Context ("FAF's own `liaHistory` is the overlay `ov = 0` off support")
Kind: D
Fidelity: n/a -/
def constMap (sel : ℕ → Sentence → Bool) (quote : ℕ → Sentence → ℚ) :
    ℕ → Sentence → Option LogicalInduction.EF :=
  fun k ψ => if sel k ψ then some (.const (quote k ψ)) else none

/-- **FAF's run-level freeze oracle is a splice oracle for the constant-body map.** The
bridges `hsel`/`hquote` say the run-level selector and quote table agree with the
sentence-level ones on every run `parseRpn` accepts (FAF's `selRunOf_bridge` /
`quoteRunOf_bridge` shape).
Source: mandate T1.3, T1.5; `Construction/Freeze/Step.lean:81`
Kind: C
Fidelity: exact -/
def SpliceOracle.ofRunOracle {selRun : List ℕ → ℕ → Bool} {quoteRun : List ℕ → ℕ → ℕ}
    (O : RunOracle selRun quoteRun) (sel : ℕ → Sentence → Bool) (quote : ℕ → Sentence → ℚ)
    (hsel : ∀ (b : List ℕ) (ψ : Sentence), parseRpn b.length b = some (ψ, []) →
      ∀ D, selRun b D = sel D ψ)
    (hquote : ∀ (b : List ℕ) (ψ : Sentence), parseRpn b.length b = some (ψ, []) →
      ∀ D, sel D ψ = true → quoteRun b D = Encodable.encode (quote D ψ)) :
    SpliceOracle (constMap sel quote) where
  R := O.R
  R_FP := O.R_FP
  R_wf := O.R_wf
  R_spec := fun cur hcur bufW _ ψ hψ => by
    rw [O.R_spec cur hcur bufW, hsel _ ψ hψ]
    by_cases hs : sel (digitVal cur) ψ = true
    · rw [if_pos hs, hquote _ ψ hψ _ hs]
      simp only [constMap, hs, if_true, bodyTokens, LogicalInduction.EF.serialize]
      exact (UnRpnContractsTo.payload 1 _ (Or.inl rfl)).append
        (UnRpnContractsTo.single 8 (by norm_num))
    · rw [if_neg hs]
      simp only [constMap, hs, bodyTokens]
      exact UnRpnContractsTo.nil

/-- The sentence-level selector a finite table denotes.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableSel (entries : List TableEntry) (k : ℕ) (ψ : Sentence) : Bool :=
  (tableLookupOn entries ψ k).isSome

/-- The sentence-level quote a finite table denotes (`0` off the table; never read there).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tableQuote (entries : List TableEntry) (k : ℕ) (ψ : Sentence) : ℚ :=
  (tableLookupOn entries ψ k).getD 0

/-- **A machine-checked splice oracle for every finite constant-body map**: FAF's
`runOracleOf entries` (an `FP` recognizer keyed by parsing, correct on every spelling) through
`ofRunOracle`.
Source: mandate T1.5 ("your first `SpliceCertificate`"); `Construction/Freeze/Oracle.lean`
Kind: C
Fidelity: exact -/
def SpliceOracle.ofTable (entries : List TableEntry) :
    SpliceOracle (constMap (tableSel entries) (tableQuote entries)) :=
  SpliceOracle.ofRunOracle (runOracleOf entries) (tableSel entries) (tableQuote entries)
    (fun b ψ hb D => by
      simp only [selRunOf, tableSel, tableLookup_eq_on entries hb D])
    (fun b ψ hb D hs => by
      simp only [quoteRunOf, tableQuote, tableLookup_eq_on entries hb D]
      simp only [tableSel] at hs
      cases h : tableLookupOn entries ψ D with
      | none => rw [h] at hs; simp at hs
      | some q => simp)

/-- The constant-body map of a table fires exactly on the table's cells, with the table's
value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constMap_table_eq (entries : List TableEntry) (k : ℕ) (ψ : Sentence) :
    constMap (tableSel entries) (tableQuote entries) k ψ =
      (tableLookupOn entries ψ k).map fun q => LogicalInduction.EF.const q := by
  simp only [constMap, tableSel, tableQuote]
  cases tableLookupOn entries ψ k <;> simp

end Cleanroom.Bli.BliTransfer.AttemptB
