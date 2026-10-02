import Cleanroom.Bli.BliTransfer.AttemptB.Transfer
import LogicalInduction.Framework.Machine.SpliceMachine

/-!
# `bli-transfer` · attempt B · Certificate: the oracle interface and the presented-class
transfer (T1.3, angle B: the splice-stream route)

**The interface.** `SpliceOracle expr` packages **one `FP` function** `R` and its specification
on blocks, nothing quantified over traders (mandate trap (ii)): on the bits of a day run `cur`
and any block-complete word `bufW` whose decode is a sentence run `b` that `parseRpn` accepts
as `ψ` — **every spelling**: canonical run, Gödel escape, structured escape — `R` emits a
block-complete word whose decode contracts (`UnRpnContractsTo`) to the body's token-level
serialization followed by the `letE` close `8` when `expr (digitVal cur) ψ = some e`, and to
nothing when `none`. Stated at the level of FAF's `FreezeStep.RunOracle` (whose output-length
bound is constant; here the length is whatever `FP` allows, polynomial in the input). The
contraction form admits any spelling of the body's own leaves; `SpliceOracle.ofRaw`
(`OracleBridge.lean`) converts a literal-spelling oracle.

**The new content (`SpliceOracle.spliceLeaf_machineSpliceStream`).** From an oracle, the
rewritten leaf family `z ↦ spliceLeaf expr (df z) (φ (sf z))` of any machine-presented leaf
family (`MachineSentenceCodes φ`, a reindexing ruler `sf`, a written-out day `df`) is a
`MachineSpliceStream`: the emitter is the price chunk's word followed by `R` applied to the
day run and the sentence word, all one `FP` composition; `TokenFold.decodeBits_append` splits
the decode, `UnRpnContractsTo.priceChunk` and the oracle's spec compose the contraction. This is
the link the freeze pipeline lacks (`serialize_price` only emits a leaf; nothing in FAF
rewrites one).

**The class.** `SpliceBuilt A` is the inductive class of coefficient families *presented* by
FAF's `MachineSpliceStream.serialize_*` combinators with every price leaf explicit;
`SpliceBuiltTrader Tr` is a trader presented by `EfficientlyComputable.ofTradeBlocksBig`'s data
with a `SpliceBuilt` coefficient family. Every such trader is e.c.
(`SpliceBuiltTrader.ec`), and — the certificate theorem — its splice along any `expr` with an
oracle is e.c. (`SpliceBuiltTrader.spliceOn_ec`), by replacing each `serialize_price` node
with the leaf lemma.

**Where angle B lands, honestly.** `SpliceBuiltTrader` is a *presented* class: there is no
bridge from `EfficientlyComputable` back to a combinator presentation (FAF's `dd:fuel`
converse is open, [[faf-map-li]] §5.3, and a machine's raw word has no syntax to induct on).
So the headline `overlay_noExploit_spliceBuilt` is `noExploit` **over the class**, kind `C`
with `(c)` the class, ledger status `partial: certificate over SpliceBuiltTrader` — not the
criterion. The criterion-level statement is `overlay_isLogicalInductor_of_transfer`
(`Transfer.lean`) with the transfer for every e.c. trader as its hypothesis, which angle A's
flat pass is meant to discharge; nothing here is cited as if it did.

Sources: [[bli-program]] §3.1 hypothesis (iii) (corrected, Known issue 5); mandate T1.3 and
§ Attempt angles (B, splice-stream route); `Framework/Machine/SpliceMachine.lean`;
`Construction/Freeze/Step.lean:81`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open LogicalInduction.TokenFold LogicalInduction.FPFold Complexity Complexity.Cobham

/-! ## The oracle interface -/

/-- The token-level tokens a rewritten leaf carries after its price chunk: the body's
serialization and the `letE` close, or nothing.
Source: mandate T1.3
Kind: D
Fidelity: n/a -/
def bodyTokens : Option LogicalInduction.EF → List ℕ
  | none => []
  | some e => e.serialize ++ [8]

/-- The serialization of a rewritten leaf is its price chunk followed by `bodyTokens`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceLeaf_serialize (expr : ℕ → Sentence → Option LogicalInduction.EF) (k : ℕ)
    (ψ : Sentence) :
    (EF.spliceLeaf expr k ψ).serialize = [0, Encodable.encode ψ, k] ++ bodyTokens (expr k ψ) := by
  cases h : expr k ψ with
  | none => simp [EF.spliceLeaf_none h, LogicalInduction.EF.serialize, bodyTokens]
  | some e => simp [EF.spliceLeaf_some h, LogicalInduction.EF.serialize, bodyTokens]

/-- **The splice oracle**: one polynomial-time word function `R` that, given the bits of a
well-formed day run and a block-complete sentence word, emits the rewritten leaf's body
(token-level serialization plus the close `8`, up to contraction) — for **every** spelling
`parseRpn` accepts. Model: `FreezeStep.RunOracle` (`Construction/Freeze/Step.lean:81`), with
the constant length budget dropped (an `FP` function's output is polynomially long anyway) and
the emitted body an expression rather than a constant.
Source: [[bli-program]] §3.1 hypothesis (iii), corrected (mandate Known issue 5); mandate T1.3
Kind: D
Fidelity: variant: run-level (spelling-quantified) in place of the program's "`(k, ψ) ↦ expr k ψ` is in `FP`" -/
structure SpliceOracle (expr : ℕ → Sentence → Option LogicalInduction.EF) where
  /-- The oracle. -/
  R : List Bool → List Bool
  /-- It is polynomial time. -/
  R_FP : R ∈ FP
  /-- Its output is a whole number of complete blocks, so splices decode piecewise. -/
  R_wf : ∀ tokW bufW : List Bool, BlockWF (R (pair tokW bufW))
  /-- On every well-formed day run and every block-complete word whose decode parses to `ψ`
  (any spelling), the emitted tokens contract to the body tokens of `expr (digitVal cur) ψ`. -/
  R_spec : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) → ∀ bufW : List Bool, BlockWF bufW →
    ∀ ψ : Sentence, parseRpn (decodeBits bufW).length (decodeBits bufW) = some (ψ, []) →
      UnRpnContractsTo (decodeBits (R (pair (digitsToBits cur) bufW)))
        (bodyTokens (expr (digitVal cur) ψ))

namespace SpliceOracle

variable {expr : ℕ → Sentence → Option LogicalInduction.EF}

/-- **The leaf lemma** (angle B's new content): under an oracle, the rewritten leaves of a
machine-presented price-leaf family form a machine-metered splice stream. The emitter is
`tokBits [0] ++ S ++ (D ++ ⟨4⟩) ++ R (pair D S)` with `S` the sentence family's word and `D`
the written-out day's digit run — one `FP` composition (`appendFn_mem_FP`, `pairFn_mem_FP`,
`mem_FP_comp`); the decode splits by `decodeBits_append`; the contraction is
`UnRpnContractsTo.priceChunk` followed by the oracle's spec. Machine twin of nothing in FAF:
`MachineSpliceStream.serialize_price` emits a leaf, this rewrites one.
Source: mandate T1.3 (angle B); `Framework/Machine/SpliceMachine.lean:391` (`serialize_price`)
Kind: P
Fidelity: exact -/
theorem spliceLeaf_machineSpliceStream (C : SpliceOracle expr) {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) {sf df : ℕ → ℕ} (hs : UnaryRuler sf) (hd : MachineDigits df) :
    MachineSpliceStream (fun z => (EF.spliceLeaf expr (df z) (φ (sf z))).serialize) := by
  obtain ⟨s, hstream, hp⟩ := hφ
  obtain ⟨S, hS, hSwf, hSd⟩ := hstream.comp hs
  obtain ⟨D, hD, hDw, hDv⟩ := hd.exists_digitWord
  let G : List Bool → List Bool := fun w =>
    tokBits [0] ++ S w ++ (D w ++ digitBits 4) ++ C.R (pair (D w) (S w))
  have hR : (fun w => C.R (pair (D w) (S w))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp (pairFn_mem_FP hD hS) C.R_FP
  have hG : G ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP (constFn_mem_FP _) hS)
      (appendFn_mem_FP hD (constFn_mem_FP _))) hR
  -- per day: the digit run of the written-out day
  have hday : ∀ z, ∃ cur : List ℕ, (∀ d ∈ cur, d < 4) ∧ D (unaryDay z) = digitsToBits cur ∧
      digitVal cur = df z := by
    intro z
    obtain ⟨cur, hcur, he⟩ := hDw z
    refine ⟨cur, hcur, he, ?_⟩
    rw [← hDv z, he, DigitFP.wordVal_digitsToBits hcur]
  have hwf : ∀ z, BlockWF (G (unaryDay z)) := by
    intro z
    obtain ⟨cur, hcur, he, -⟩ := hday z
    show BlockWF (tokBits [0] ++ S (unaryDay z) ++ (D (unaryDay z) ++ digitBits 4) ++
      C.R (pair (D (unaryDay z)) (S (unaryDay z))))
    rw [he]
    exact (((blockWF_tokBits _).append (hSwf z)).append (blockWF_run cur hcur)).append
      (C.R_wf _ _)
  refine ⟨fun z => decodeBits (G (unaryDay z)), ⟨G, hG, hwf, fun _ => rfl⟩, fun z => ?_⟩
  obtain ⟨cur, hcur, he, hval⟩ := hday z
  have hdec : decodeBits (G (unaryDay z)) =
      ([0] ++ s (sf z) ++ [df z]) ++ decodeBits (C.R (pair (digitsToBits cur) (S (unaryDay z)))) := by
    show decodeBits (tokBits [0] ++ S (unaryDay z) ++ (D (unaryDay z) ++ digitBits 4) ++
      C.R (pair (D (unaryDay z)) (S (unaryDay z)))) = _
    rw [he, decodeBits_append (((blockWF_tokBits _).append (hSwf z)).append (blockWF_run cur hcur))
        (C.R_wf _ _),
      decodeBits_append ((blockWF_tokBits _).append (hSwf z)) (blockWF_run cur hcur),
      decodeBits_append (blockWF_tokBits _) (hSwf z), decodeBits_tokBits, hSd z,
      decodeBits_run cur hcur, hval]
  show UnRpnContractsTo (decodeBits (G (unaryDay z))) (EF.spliceLeaf expr (df z) (φ (sf z))).serialize
  rw [hdec, spliceLeaf_serialize]
  have hparse : parseRpn (decodeBits (S (unaryDay z))).length (decodeBits (S (unaryDay z)))
      = some (φ (sf z), []) := by rw [hSd z]; exact hp (sf z)
  have hbody := C.R_spec cur hcur (S (unaryDay z)) (hSwf z) (φ (sf z)) hparse
  rw [hval] at hbody
  have hchunk : UnRpnContractsTo ([0] ++ s (sf z) ++ [df z])
      [0, Encodable.encode (φ (sf z)), df z] :=
    (UnRpnContractsTo.priceChunk (hp (sf z)) (df z)).of_eq (by simp) rfl
  exact hchunk.append hbody

end SpliceOracle

/-! ## The presented class -/

/-- **Coefficient families presented by the splice-stream combinators**, with every price leaf
explicit: the inductive closure of FAF's `MachineSpliceStream.serialize_*` suite
(`Framework/Machine/SpliceMachine.lean`) plus reindexing, dispatch and congruence. The
`price` constructor is the one the splice rewrites; `ofPriceFree` admits any machine-metered
price-free family (nothing to rewrite).
Source: mandate § Attempt angles (B, splice-stream route)
Kind: D
Fidelity: n/a -/
inductive SpliceBuilt : (ℕ → LogicalInduction.EF) → Prop
  | const (q : ℚ) : SpliceBuilt (fun _ => .const q)
  | constWrite {q : ℕ → ℚ} (hq : MachineDigits fun z => Encodable.encode (q z)) :
      SpliceBuilt (fun z => .const (q z))
  | var {f : ℕ → ℕ} (hf : MachineDigits f) : SpliceBuilt (fun z => .var (f z))
  | price {φ : ℕ → Sentence} (hφ : MachineSentenceCodes φ) {sf df : ℕ → ℕ}
      (hs : UnaryRuler sf) (hd : MachineDigits df) :
      SpliceBuilt (fun z => .price (φ (sf z)) (df z))
  | add {A B : ℕ → LogicalInduction.EF} (hA : SpliceBuilt A) (hB : SpliceBuilt B) :
      SpliceBuilt (fun z => .add (A z) (B z))
  | mul {A B : ℕ → LogicalInduction.EF} (hA : SpliceBuilt A) (hB : SpliceBuilt B) :
      SpliceBuilt (fun z => .mul (A z) (B z))
  | max {A B : ℕ → LogicalInduction.EF} (hA : SpliceBuilt A) (hB : SpliceBuilt B) :
      SpliceBuilt (fun z => .max (A z) (B z))
  | safeRecip {A : ℕ → LogicalInduction.EF} (hA : SpliceBuilt A) :
      SpliceBuilt (fun z => .safeRecip (A z))
  | letE {X B : ℕ → LogicalInduction.EF} (hX : SpliceBuilt X) (hB : SpliceBuilt B) :
      SpliceBuilt (fun z => .letE (X z) (B z))
  | ofPriceFree {A : ℕ → LogicalInduction.EF} (h : MachineTokenStream fun z => (A z).serialize)
      (hfree : ∀ z, (A z).priceFree) : SpliceBuilt A
  | comp {A : ℕ → LogicalInduction.EF} (h : SpliceBuilt A) {f : ℕ → ℕ} (hf : UnaryRuler f) :
      SpliceBuilt (fun z => A (f z))
  | ifZero {A B : ℕ → LogicalInduction.EF} (hA : SpliceBuilt A) (hB : SpliceBuilt B)
      {t : ℕ → ℕ} (ht : UnaryRuler t) : SpliceBuilt (fun z => if t z = 0 then A z else B z)
  | of_eq {A B : ℕ → LogicalInduction.EF} (h : SpliceBuilt A) (he : ∀ z, A z = B z) :
      SpliceBuilt B

namespace SpliceBuilt

/-- Every presented family is a machine-metered splice stream (the combinators, one per
constructor).
Source: `Framework/Machine/SpliceMachine.lean` (the `serialize_*` suite)
Kind: C
Fidelity: n/a -/
theorem machineSpliceStream {A : ℕ → LogicalInduction.EF} (h : SpliceBuilt A) :
    MachineSpliceStream (fun z => (A z).serialize) := by
  induction h with
  | const q => exact MachineSpliceStream.serialize_const q
  | constWrite hq => exact MachineSpliceStream.serialize_const_write hq
  | var hf => exact MachineSpliceStream.serialize_var hf
  | price hφ hs hd => exact MachineSpliceStream.serialize_price hφ hs hd
  | add _ _ ihA ihB => exact MachineSpliceStream.serialize_add ihA ihB
  | mul _ _ ihA ihB => exact MachineSpliceStream.serialize_mul ihA ihB
  | max _ _ ihA ihB => exact MachineSpliceStream.serialize_max ihA ihB
  | safeRecip _ ihA => exact MachineSpliceStream.serialize_safeRecip ihA
  | letE _ _ ihX ihB => exact MachineSpliceStream.serialize_letE ihX ihB
  | ofPriceFree h hfree => exact MachineSpliceStream.ofPriceFree h hfree
  | comp _ hf ih => exact ih.comp hf
  | @ifZero A B _ _ t ht ihA ihB =>
      exact (ihA.ifZero ihB ht).of_eq (fun z => by
        show (if t z = 0 then (A z).serialize else (B z).serialize)
          = (if t z = 0 then A z else B z).serialize
        split_ifs <;> rfl)
  | of_eq _ he ih => exact ih.of_eq (fun z => by rw [he z])

/-- **The certificate theorem at family level**: under an oracle, the splice of a presented
family is a machine-metered splice stream — each `price` node is replaced by the leaf lemma,
every other node is the corresponding combinator.
Source: mandate T1.3 (angle B)
Kind: C
Fidelity: exact for the class -/
theorem spliceOn_machineSpliceStream {expr : ℕ → Sentence → Option LogicalInduction.EF}
    (C : SpliceOracle expr) {A : ℕ → LogicalInduction.EF} (h : SpliceBuilt A) :
    MachineSpliceStream (fun z => (EF.spliceOn expr (A z)).serialize) := by
  induction h with
  | const q => exact MachineSpliceStream.serialize_const q
  | constWrite hq => exact MachineSpliceStream.serialize_const_write hq
  | var hf => exact MachineSpliceStream.serialize_var hf
  | price hφ hs hd => exact C.spliceLeaf_machineSpliceStream hφ hs hd
  | add _ _ ihA ihB => exact MachineSpliceStream.serialize_add ihA ihB
  | mul _ _ ihA ihB => exact MachineSpliceStream.serialize_mul ihA ihB
  | max _ _ ihA ihB => exact MachineSpliceStream.serialize_max ihA ihB
  | safeRecip _ ihA => exact MachineSpliceStream.serialize_safeRecip ihA
  | letE _ _ ihX ihB => exact MachineSpliceStream.serialize_letE ihX ihB
  | ofPriceFree h hfree =>
      exact (MachineSpliceStream.ofPriceFree h hfree).of_eq
        (fun z => by rw [EF.spliceOn_of_priceFree _ (hfree z)])
  | comp _ hf ih => exact ih.comp hf
  | @ifZero A B _ _ t ht ihA ihB =>
      exact (ihA.ifZero ihB ht).of_eq (fun z => by
        show (if t z = 0 then (EF.spliceOn expr (A z)).serialize
            else (EF.spliceOn expr (B z)).serialize)
          = (EF.spliceOn expr (if t z = 0 then A z else B z)).serialize
        split_ifs <;> rfl)
  | of_eq _ he ih => exact ih.of_eq (fun z => by rw [he z])

end SpliceBuilt

/-- **Traders presented by `ofTradeBlocksBig`'s data with a `SpliceBuilt` coefficient
family**: `count n` trades on day `n`, the `j`-th being `(f ⟨n, j⟩, φ ⟨n, j⟩)`, with the count
a unary ruler and the sentence family machine-metered. The class angle B's certificate covers;
a `(c)` against the criterion's `EfficientlyComputable`.
Source: mandate § Attempt angles (B); `Framework/Machine/SpliceMachine.lean:494`
Kind: D
Fidelity: n/a -/
def SpliceBuiltTrader (Tr : Trader) : Prop :=
  ∃ (count : ℕ → ℕ) (f : ℕ → LogicalInduction.EF) (φ : ℕ → Sentence),
    UnaryRuler count ∧ SpliceBuilt f ∧ MachineSentenceCodes φ ∧
    ∀ n, (Tr.strat n).trades =
      (List.range (count n)).map fun j => (f (Nat.pair n j), φ (Nat.pair n j))

namespace SpliceBuiltTrader

/-- Every presented trader is efficiently computable (`ofTradeBlocksBig`).
Source: `Framework/Machine/SpliceMachine.lean:494`
Kind: C
Fidelity: n/a -/
theorem ec {Tr : Trader} (h : SpliceBuiltTrader Tr) : EfficientlyComputable Tr := by
  obtain ⟨count, f, φ, hcount, hf, hφ, hTr⟩ := h
  exact EfficientlyComputable.ofTradeBlocksBig Tr count f φ hcount hf.machineSpliceStream hφ hTr

/-- **The certificate theorem** (angle B, `EfficientlyComputable.spliceOn` over the presented
class): under an oracle for `expr`, the splice of a presented trader is efficiently computable
— the same `ofTradeBlocksBig` data with the coefficient family spliced.
Source: mandate T1.3 (angle B)
Kind: C
Fidelity: weaker: for `SpliceBuiltTrader`, not for every `EfficientlyComputable` trader -/
theorem spliceOn_ec {expr : ℕ → Sentence → Option LogicalInduction.EF} (C : SpliceOracle expr)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) {Tr : Trader} (h : SpliceBuiltTrader Tr) :
    EfficientlyComputable (Trader.spliceOn expr hr Tr) := by
  obtain ⟨count, f, φ, hcount, hf, hφ, hTr⟩ := h
  refine EfficientlyComputable.ofTradeBlocksBig (Trader.spliceOn expr hr Tr) count
    (fun z => EF.spliceOn expr (f z)) φ hcount (hf.spliceOn_machineSpliceStream C) hφ
    (fun n => ?_)
  simp [Trader.spliceOn_strat, Strategy.spliceOn_trades, hTr n, List.map_map]

end SpliceBuiltTrader

/-! ## The headline over the class -/

/-- **Expressible-overlay transfer over the presented class** (angle B's landing): for a
logical inductor `Q`, an expression map `E` and a splice oracle for it, no `SpliceBuiltTrader`
exploits `overlay Q ov`. Scope: over an expression map whose bodies are closed and read only
small prices of days `≤ k`, with a polynomial-time run-level oracle quantified over every
spelling `parseRpn` accepts; one-market. **Quantified over the presented class
`SpliceBuiltTrader`, not over `EfficientlyComputable`** — not the criterion (mandate trap (i));
the criterion-level form is `overlay_isLogicalInductor_of_transfer` with the transfer for every
e.c. trader as hypothesis.
Source: [[bli-program]] §3.1; bli-paper-039; mandate T1 (angle B)
Kind: C
Fidelity: weaker: `noExploit` over `SpliceBuiltTrader`
Hyps: (a) `hQ`; (a) `E`; (a) `C`; (c) the class `SpliceBuiltTrader` -/
theorem overlay_noExploit_spliceBuilt (Q : History) (DP : DeductiveProcess)
    [IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (C : SpliceOracle E.expr) :
    ∀ Tr, SpliceBuiltTrader Tr → ¬ Tr.Exploits (overlay Q ov) DP :=
  overlay_noExploit_of_class Q DP ov E SpliceBuiltTrader
    (fun _ h => ⟨h.ec, h.spliceOn_ec C E.rank_le⟩)

end Cleanroom.Bli.BliTransfer.AttemptB
