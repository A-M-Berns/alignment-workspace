import Cleanroom.Bli.BliTransfer.AttemptA.TokenModel
import LogicalInduction.Construction.Conditioning.PricePass

/-!
# `bli-transfer` (attempt A) · Contraction: the flat-stream pass and its commutation

A machine holds the **flat** RPN stream (a sentence slot is a whole symbol run, in any of the
spellings `parseRpn` accepts), not the contracted one `strategyOfTokens` parses. The flat pass is
FAF's emitter-generic run-aware automaton `rpnConditionRun emit`
(`Construction/Conditioning/PricePass.lean:613`) with the **splice emitter** `spliceEmitOn exprRun`:
at a price-day slot it emits the day, the *raw* body the run-level lookup `exprRun` returns for the
buffered run, and the `letE` close `8`.

* `EF.rawSerialize` — the flat spelling of a body: every price leaf as the canonical run
  `0 :: rpn ψ ++ [k]` (never as a Gödel code, whose size can be doubly exponential in the
  sentence's `tokenSize`); `unRpn_rawSerialize_append` contracts it back to `EF.serialize`.
* `spliceTokensOn` / `spliceBodyOn` — the token-model rewrite as a whole-stream function and the
  body it splices at a completed price leaf, with the seven chunk laws FAF's master commutation
  `unRpn_rpnConditionRun_of` (`PricePass.lean:1942`) asks for.
* `unRpn_rpnSpliceRunOn` — **whole-stream contraction exactness**: on every input stream,
  well-formed or garbage, contracting the flat pass's output is the token-model splice of the
  contraction, provided `exprRun` agrees with the map on **every spelling** `parseRpn` accepts
  (`hrun`; canonical run, Gödel escape, structured escape — the exploiting machine chooses).
* `SpliceStreamRewriter` — the one `FP` obligation, stated on the contracted stream (mirror of
  FAF's `FreezeStreamRewriter`); `EfficientlyComputable.spliceOn_of_rewriter` is the efficiency
  transport from it (mirror of `EfficientlyComputable.freezeOn`), and
  `spliceStreamRewriter_of_flatPass` reduces it to a flat pass (mirror of
  `RpnFreeze.freezeStreamRewriter_of_flatPass`). `Certificate.lean` supplies the flat pass.

Sources: mandate T1.3 (angle A); FAF `Construction/Freeze/Compiler.lean:78–337`,
`PricePass.lean:1942`, `FinitePerturbations.lean:549–590`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional LogicalInduction.RpnConditioning

/-! ## The flat spelling of a body -/

/-- The flat (RPN-expanded) spelling of a feature: price leaves as canonical runs.
Source: mandate T1.3 ("the raw body's leaves must be spelled as canonical runs")
Kind: D
Fidelity: n/a -/
def EF.rawSerialize : EF → List ℕ
  | .price ψ k => 0 :: (rpn ψ ++ [k])
  | .const q => [1, Encodable.encode q]
  | .add a b => EF.rawSerialize a ++ EF.rawSerialize b ++ [2]
  | .mul a b => EF.rawSerialize a ++ EF.rawSerialize b ++ [3]
  | .max a b => EF.rawSerialize a ++ EF.rawSerialize b ++ [4]
  | .safeRecip a => EF.rawSerialize a ++ [5]
  | .var i => [7, i]
  | .letE x b => EF.rawSerialize x ++ EF.rawSerialize b ++ [8]

/-- The canonical run of a sentence parses to it, with nothing left over.
Source: none: infrastructure; FAF `parseRpn_rpn`
Kind: L
Fidelity: n/a -/
lemma parseRpn_rpn_self (ψ : Sentence) : parseRpn (rpn ψ).length (rpn ψ) = some (ψ, []) := by
  simpa using parseRpn_rpn ψ [] le_rfl

/-- **The flat spelling contracts to the serialization**, in any context: `unRpn` on
`rawSerialize e ++ rest` is `serialize e ++ unRpn rest`.
Source: mandate T1.3; FAF `unRpn_price_chunk_block`, `unRpn_payload_chunk`, `unRpn_single_chunk`
Kind: L
Fidelity: exact -/
lemma unRpn_rawSerialize_append (e : EF) :
    ∀ rest : List ℕ, unRpn (EF.rawSerialize e ++ rest) = e.serialize ++ unRpn rest := by
  induction e with
  | price ψ k =>
      intro rest
      have h := unRpn_price_chunk_block (parseRpn_rpn_self ψ) k rest
      simp only [EF.rawSerialize, EF.serialize, List.cons_append, List.append_assoc,
        List.nil_append]
      exact h
  | const q =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.cons_append, List.nil_append]
      rw [unRpn_payload_chunk 1 _ (Or.inl rfl) rest]
  | add a b iha ihb =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.append_assoc, List.singleton_append]
      rw [iha, ihb, unRpn_single_chunk 2 (by decide) rest]
  | mul a b iha ihb =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.append_assoc, List.singleton_append]
      rw [iha, ihb, unRpn_single_chunk 3 (by decide) rest]
  | max a b iha ihb =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.append_assoc, List.singleton_append]
      rw [iha, ihb, unRpn_single_chunk 4 (by decide) rest]
  | safeRecip a iha =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.append_assoc, List.singleton_append]
      rw [iha, unRpn_single_chunk 5 (by decide) rest]
  | var i =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.cons_append, List.nil_append]
      rw [unRpn_payload_chunk 7 _ (Or.inr rfl) rest]
  | letE x b ihx ihb =>
      intro rest
      simp only [EF.rawSerialize, EF.serialize, List.append_assoc, List.singleton_append]
      rw [ihx, ihb, unRpn_single_chunk 8 (by decide) rest]

/-! ## The token-model rewrite as a whole-stream function -/

/-- The token-model splice, as a whole-stream rewrite.
Source: none: infrastructure; FAF `RpnFreeze.freezeTokensOn`
Kind: D
Fidelity: n/a -/
def spliceTokensOn (expr : ℕ → Sentence → Option EF) (L : List ℕ) : List ℕ :=
  (spliceTokenRunOn expr (0, 0) L).2

/-- The body the token-model splice inserts at a completed price leaf `[0, fc, d]`.
Source: none: infrastructure; FAF `RpnFreeze.freezeBodyOn`
Kind: D
Fidelity: n/a -/
def spliceBodyOn (expr : ℕ → Sentence → Option EF) (fc d : ℕ) : List ℕ :=
  match exprCode expr d fc with
  | some body => body ++ [8]
  | none => []

/-- Chunk law: the empty stream.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_nil (expr : ℕ → Sentence → Option EF) : spliceTokensOn expr [] = [] := rfl

/-- Chunk law: a bare operator token copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_single (expr : ℕ → Sentence → Option EF) (t : ℕ) (L : List ℕ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h6 : t ≠ 6) (h7 : t ≠ 7) :
    spliceTokensOn expr (t :: L) = t :: spliceTokensOn expr L := by
  simp [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn, EF.freezeTokenNext, h0, h1, h6, h7]

/-- Chunk law: a lone token copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_one (expr : ℕ → Sentence → Option EF) (t : ℕ) :
    spliceTokensOn expr [t] = [t] := by
  simp [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn]

/-- Chunk law: an opaque payload pair copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_payload (expr : ℕ → Sentence → Option EF) (t c : ℕ)
    (ht : t = 1 ∨ t = 7) (L : List ℕ) :
    spliceTokensOn expr (t :: c :: L) = t :: c :: spliceTokensOn expr L := by
  rcases ht with rfl | rfl <;>
    simp [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn, EF.freezeTokenNext]

/-- Chunk law: a completed price leaf is copied and followed by its body.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_price (expr : ℕ → Sentence → Option EF) (fc d : ℕ) (L : List ℕ) :
    spliceTokensOn expr (0 :: fc :: d :: L) =
      0 :: fc :: d :: (spliceBodyOn expr fc d ++ spliceTokensOn expr L) := by
  simp only [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn, EF.freezeTokenNext,
    spliceBodyOn]
  cases h : exprCode expr d fc <;> simp [h]

/-- Chunk law: a truncated price frame copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_pricePair (expr : ℕ → Sentence → Option EF) (fc : ℕ) :
    spliceTokensOn expr [0, fc] = [0, fc] := by
  simp [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn, EF.freezeTokenNext]

/-- Chunk law: a trade frame copies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceTokensOn_trade (expr : ℕ → Sentence → Option EF) (fc : ℕ) (L : List ℕ) :
    spliceTokensOn expr (6 :: fc :: L) = 6 :: fc :: spliceTokensOn expr L := by
  simp [spliceTokensOn, spliceTokenRunOn, spliceTokenEmitOn, EF.freezeTokenNext]

/-! ## The flat emitter and the master commutation -/

/-- **The symbol-level splice emitter**: at a price-day slot, retain the day and, when the
run-level lookup fires on the buffered run, splice the raw body under the administrative binding.
Source: mandate T1.3 (angle A: `emit buf D := [D] ++ rawBody buf D ++ [8]`)
Kind: D
Fidelity: n/a -/
def spliceEmitOn (exprRun : List ℕ → ℕ → Option (List ℕ)) : List ℕ → ℕ → List ℕ :=
  fun buf D =>
    match exprRun buf D with
    | some raw => D :: (raw ++ [8])
    | none => [D]

/-- **The run-level lookup agrees with the map on every spelling.** For every run `b` that
`parseRpn` reads as the sentence `φ` — canonical, Gödel-escaped or structured — the lookup at day
`D` is the flat spelling of `expr D φ`. This is the bridge from the run the machine holds to the
sentence the map is stated on; it is quantified over *all* accepted spellings because the
exploiting machine chooses the spelling (mandate T1.3, Known issue 5).
Source: mandate T1.3
Kind: D
Fidelity: n/a -/
def RunAgrees (expr : ℕ → Sentence → Option EF) (exprRun : List ℕ → ℕ → Option (List ℕ)) :
    Prop :=
  ∀ (b : List ℕ) (φ : Sentence), parseRpn b.length b = some (φ, []) →
    ∀ D, exprRun b D = (expr D φ).map EF.rawSerialize

/-- The code-level body at a sentence's own code is the map's serialized body.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exprCode_encode (expr : ℕ → Sentence → Option EF) (D : ℕ) (φ : Sentence) :
    exprCode expr D (Encodable.encode φ) = (expr D φ).map EF.serialize := by
  simp [exprCode, Encodable.encodek]

/-- **The rewritten price chunk contracts to the token-model splice.**
Source: mandate T1.3; FAF `RpnFreeze.unRpn_freezeOn_rewrite_chunk`
Kind: L
Fidelity: exact -/
lemma unRpn_spliceOn_rewrite_chunk (expr : ℕ → Sentence → Option EF)
    (exprRun : List ℕ → ℕ → Option (List ℕ)) (hrun : RunAgrees expr exprRun)
    {b : List ℕ} {φ : Sentence} (hb : parseRpn b.length b = some (φ, []))
    (D : ℕ) (rest : List ℕ) :
    unRpn (0 :: b ++ spliceEmitOn exprRun b D ++ rest) =
      0 :: Encodable.encode φ :: D ::
        (spliceBodyOn expr (Encodable.encode φ) D ++ unRpn rest) := by
  have hr := hrun b φ hb D
  rw [spliceEmitOn, spliceBodyOn, exprCode_encode, hr]
  cases hexpr : expr D φ with
  | none =>
      simp only [Option.map_none]
      have hshape : 0 :: b ++ [D] ++ rest = 0 :: (b ++ D :: rest) := by simp
      rw [hshape, unRpn_price_chunk_block hb]
      simp
  | some e =>
      simp only [Option.map_some]
      have hshape : 0 :: b ++ D :: (EF.rawSerialize e ++ [8]) ++ rest =
          0 :: (b ++ D :: (EF.rawSerialize e ++ 8 :: rest)) := by simp
      rw [hshape, unRpn_price_chunk_block hb, unRpn_rawSerialize_append,
        unRpn_single_chunk 8 (by decide) rest]
      simp

/-- **Whole-stream contraction exactness for the splice pass**: on every input stream — well-formed
or garbage — the contraction of the flat splice transducer's output is the token-model splice of
the contraction. This is the bridge the machine-class certificate needs: the transducer runs on
the flat stream a machine holds, while `spliceTokenRunOn` is stated on the contracted one.
Source: mandate T1.3 (angle A, "the contraction lemma `unRpn_rpnConditionRun_of`"); FAF `RpnFreeze.unRpn_rpnFreezeRunOn`
Kind: C
Fidelity: exact
Hyps: (a) except `hrun`, the run-level agreement on every spelling -/
lemma unRpn_rpnSpliceRunOn (expr : ℕ → Sentence → Option EF)
    (exprRun : List ℕ → ℕ → Option (List ℕ)) (hrun : RunAgrees expr exprRun) :
    ∀ (N : ℕ) (ts : List ℕ), ts.length ≤ N →
    unRpn ((rpnConditionRun (spliceEmitOn exprRun) (rcPack 0 0 0, []) ts).2) =
      spliceTokensOn expr (unRpn ts) :=
  unRpn_rpnConditionRun_of (spliceEmitOn exprRun) (spliceTokensOn expr) (spliceBodyOn expr)
    (spliceTokensOn_nil expr)
    (fun t L h0 h1 h6 h7 => spliceTokensOn_single expr t L h0 h1 h6 h7)
    (spliceTokensOn_one expr)
    (fun t c L ht => spliceTokensOn_payload expr t c ht L)
    (spliceTokensOn_price expr)
    (spliceTokensOn_pricePair expr)
    (spliceTokensOn_trade expr)
    (fun _ _ hb D rest => unRpn_spliceOn_rewrite_chunk expr exprRun hrun hb D rest)

/-! ## The stream rewriter and the efficiency transport -/

/-- **The one `FP` obligation, on the contracted stream**: every polynomial-time output word can
be rewritten, in polynomial time, into one whose contracted token stream is the token-model splice
of the original's. Mirror of FAF's `FreezeStreamRewriter`. Not quantified over traders.
Source: mandate T1.3; FAF `FreezeStreamRewriter`
Kind: D
Fidelity: n/a -/
def SpliceStreamRewriter (expr : ℕ → Sentence → Option EF) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
      unRpn (undigitize (bitsToDigits (G x)))
        = (spliceTokenRunOn expr (0, 0) (unRpn (undigitize (bitsToDigits (F x))))).2

/-- **The splice preserves machine efficiency, given the stream rewriter**: the token model
transports the decoded strategy (`strategyOfTokens_spliceTokenRunOn_trades`), `Strategy.ext`
upgrades the trade list to the strategy, and `Trader.spliceOn` is that strategy-wise.
Source: mandate T1.3; FAF `EfficientlyComputable.freezeOn`
Kind: C
Fidelity: exact
Hyps: (a) except `hrewrite`, the named `FP` obligation -/
lemma EfficientlyComputable.spliceOn_of_rewriter (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    (hrewrite : SpliceStreamRewriter expr) {Tr : Trader} (hTr : EfficientlyComputable Tr) :
    EfficientlyComputable (Trader.spliceOn expr hrank Tr) := by
  obtain ⟨F, hF, hFspec⟩ := hTr
  obtain ⟨G, hG, hGspec⟩ := hrewrite F hF
  refine ⟨G, hG, fun n => ?_⟩
  apply Strategy.ext
  have htok := strategyOfTokens_spliceTokenRunOn_trades expr hrank n
    (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
  simp only at htok
  have hFtok : strategyOfTokens n (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
      = Tr.strat n := hFspec n
  show (strategyOfTokens n (unRpn (undigitize (bitsToDigits (G (unaryDay n)))))).trades = _
  rw [hGspec (unaryDay n), htok, hFtok]
  rfl

/-- **`SpliceStreamRewriter` reduces to a flat-stream pass**: a polynomial-time rewrite of the
machine's own output word computing the symbol-level splice transducer discharges the
contracted-stream obligation, because contraction commutes with the pass.
Source: mandate T1.3; FAF `RpnFreeze.freezeStreamRewriter_of_flatPass`
Kind: C
Fidelity: exact
Hyps: (a) except `hrun` and `hflat`, the residual obligations -/
lemma spliceStreamRewriter_of_flatPass (expr : ℕ → Sentence → Option EF)
    (exprRun : List ℕ → ℕ → Option (List ℕ)) (hrun : RunAgrees expr exprRun)
    (hflat : ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
      ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
        undigitize (bitsToDigits (G x))
          = (rpnConditionRun (spliceEmitOn exprRun) (rcPack 0 0 0, [])
              (undigitize (bitsToDigits (F x)))).2) :
    SpliceStreamRewriter expr := by
  intro F hF
  obtain ⟨G, hG, hGspec⟩ := hflat F hF
  refine ⟨G, hG, fun x => ?_⟩
  rw [hGspec x]
  exact unRpn_rpnSpliceRunOn expr exprRun hrun _ _ le_rfl

end Cleanroom.Bli.BliTransfer.AttemptA
