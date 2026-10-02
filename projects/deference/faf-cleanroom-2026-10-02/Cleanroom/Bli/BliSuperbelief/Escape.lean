import Cleanroom.Bli.BliSuperbelief.Bits
import LogicalInduction.Framework.Emission.RpnSentence

/-!
# `bli-superbelief` · Escape: the stream FAF's efficiency class reads (E2(d), audit r2)

`Bits.lean` bounds `(digitize (tentExpr 𝓜 m h Q).serialize).length`. That is **not** the stream
FAF's class reads: `EfficientlyComputable` decodes a machine's bits through
`strategyOfOutput n w = strategyOfTokens n (unRpn (undigitize (bitsToDigits w)))`
(`Framework/Criterion.lean`), and `unRpn` reads the token after every price tag `0` and every
trade tag `6` as a **Polish-notation sentence block** — the canonical symbol run `rpn φ`, or the
two-token escape `[1, ⌜φ⌝]` — and contracts it to the pair code `⌜φ⌝`. A raw `serialize` stream,
whose sentence slots carry bare pair codes, is misparsed (audit r2 adversarial §2.1, probe
`UnRpnEscape.lean`: `unRpn [0, ⌜pA ⋏ qA⌝, 3] ≠ [0, ⌜pA ⋏ qA⌝, 3]`). What the machine must emit is an
`unRpn`-**preimage** of the strategy stream, and FAF's forward splice for that is `escExpand`
(`Framework/Emission/RpnSentence.lean`): every sentence slot `c` becomes the escape block `[1, c]`,
everything else is copied; `strategyOfTokens_unRpn_escExpand` says the contraction of the
expansion validates to the same strategy.

This file proves, for every closed same-day term (`PriceLeavesIn`) and every strategy stream
built from such terms (`serializeTrades`):

* `escExpand` rewrites the stream to one that `unRpn` contracts back **exactly**
  (`escExpand_serialize_spec`, `escExpand_serializeTrades_spec`; at `tentExpr`:
  `unRpn_escExpand_tentExpr`) — the escape route is available at every leaf because no sentence
  has code `0` (`encode_sentence_ne_zero`: Foundation's `Formula.toNat` adds `1` everywhere);
* in FAF's digit meter the expansion costs **exactly two digits per price leaf** (the escape token
  `1` is the block `[1, 4]`) and two per trade frame; `tentExpr 𝓜 m h Q` has exactly
  `4·|S m|` price leaves (`priceLeaves_tentExpr`: `w0E` and `w1E` read the price once each,
  `wUE` twice through `absE`), so the stream FAF reads is `Bits.lean`'s bound plus `8·|S m|`
  (`tentExpr_escExpand_digitize_length_le`, `_poly`), and a one-trade day's whole stream is
  `escExpand_serializeTrades_single_digitize_length_le`.

**Spelling caveat (audit r2 fidelity §3.1).** The escape spelling meters a leaf by its Gödel code
(the hypothesis `hA : ∀ φ ∈ S m, ⌜φ⌝ < 4^K`), exactly as `Bits.lean` does. The other spelling
`unRpn` accepts, the canonical run `rpn φ` (one token per symbol), meters a leaf by `|rpn φ|`
blocks instead, and is what `bli-transfer`'s mandate T1.3 asks of the raw body; its cost is not
stated here (FAF has no canonical-run splice to state it over; `rpn φ` may be far shorter than
`log ⌜φ⌝` for deep sentences, or longer for shallow ones).

Sources: FAF `Framework/Criterion.lean` (`serialize`, `serializeTrades`, `digitize`, `unRpn`,
`strategyOfOutput`, `EfficientlyComputable`), `Framework/Emission/RpnSentence.lean` (`escExpand`,
the chunk lemmas, `UnRpnContractsTo`, `strategyOfTokens_unRpn_escExpand`); [[bli-program]] §3.4;
mandate E2(d); audit r2 adversarial §2.1.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

variable {𝒮 : SmallIndex}

/-! ## No sentence has code `0` -/

/-- No sentence has code `0`: Foundation's `Formula.toNat` adds `1` to every constructor's pair
code. So FAF's escape block `[1, ⌜φ⌝]` (which `escExpandTokens` refuses at `0`, emitting the
poison `[1, 0, 2]`) is available for every price leaf and every trade frame.
Source: none: infrastructure (Foundation `Propositional/Formula/Basic.lean` `toNat`; FAF
`escExpandTokens`)
Kind: L
Fidelity: n/a -/
lemma encode_sentence_ne_zero (φ : Sentence) : Encodable.encode φ ≠ 0 := by
  cases φ <;> simp [Encodable.encode, LO.Propositional.Formula.toNat]

/-! ## The price-leaf count -/

/-- `priceLeaves e`: the number of `price` leaves of `e` — one sentence slot of `serialize`, hence
one escape block of `escExpand`, each.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def priceLeaves : EF → ℕ
  | .price _ _ => 1
  | .const _ => 0
  | .add a b => priceLeaves a + priceLeaves b
  | .mul a b => priceLeaves a + priceLeaves b
  | .max a b => priceLeaves a + priceLeaves b
  | .safeRecip a => priceLeaves a
  | .var _ => 0
  | .letE x b => priceLeaves x + priceLeaves b

/-- The three-weight mixture reads its price **four** times: once in `w0E`, once in `w1E`, twice
in `wUE` (through `absE a = max a (−a)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLeaves_mix3E (x : EF) (c0 cU c1 : ℚ) :
    priceLeaves (mix3E x c0 cU c1) = 4 * priceLeaves x := by
  simp only [mix3E, w0E, wUE, w1E, clampE, minE, negE, subE, absE, priceLeaves]
  ring

/-- Leaves of a product: the sum of the factors' leaves.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLeaves_prodList : ∀ l : List EF, priceLeaves (prodList l) = (l.map priceLeaves).sum
  | [] => by simp [prodList, priceLeaves]
  | e :: l => by
      simp only [prodList, priceLeaves, List.map_cons, List.sum_cons, priceLeaves_prodList l]

/-- A coordinate term has `4` price leaves if its sentence is small on day `m`, else none.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLeaves_coordExpr (𝓜 : Mesh) (m h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ) :
    priceLeaves (coordExpr 𝓜 m h φ v) = if φ.1 ∈ 𝒮.S m then 4 else 0 := by
  unfold coordExpr
  split_ifs with hφ
  · rw [priceLeaves_mix3E]
    rfl
  · rfl

/-- The sum of a function over the sorted list of day-`k` sentences is the `Finset` sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_sort_eq (𝒮 : SmallIndex) (k : ℕ) (f : ↥(𝒮.S k) → ℕ) :
    (((Finset.univ : Finset ↥(𝒮.S k)).sort (encLE 𝒮 k)).map f).sum = ∑ φ, f φ := by
  rw [((Finset.sort_perm_toList (Finset.univ : Finset ↥(𝒮.S k)) (encLE 𝒮 k)).map f).sum_eq,
    Finset.sum_map_toList]

/-- Among the day-`k` sentences, those small on an earlier day `m` are exactly `S m` in number.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma card_filter_mem_S (𝒮 : SmallIndex) {m k : ℕ} (hmk : m ≤ k) :
    ((Finset.univ : Finset ↥(𝒮.S k)).filter fun φ => φ.1 ∈ 𝒮.S m).card = (𝒮.S m).card := by
  have hsub : 𝒮.S m ⊆ 𝒮.S k := 𝒮.mono_le hmk
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact hφ
  · intro hx
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩

/-- **`tentExpr` has exactly `4·|S m|` price leaves**: four per day-`m` small sentence (one in
`w0E`, two in `wUE`, one in `w1E`), none for the sentences entering later.
Source: none: infrastructure (audit r2 adversarial §2.1 counted three per sentence; it is four)
Kind: P
Fidelity: n/a -/
theorem priceLeaves_tentExpr (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    priceLeaves (tentExpr 𝓜 m h Q) = 4 * (𝒮.S m).card := by
  unfold tentExpr
  rw [priceLeaves_prodList, List.map_map, sum_sort_eq]
  simp only [Function.comp_def, priceLeaves_coordExpr]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul,
    card_filter_mem_S 𝒮 (by omega)]
  ring

/-! ## The escape splice, ahead of any continuation -/

/-- `EscExpandsTo ts out`: ahead of any continuation, `escExpand` rewrites the run `ts` to `out`
and proceeds — the forward mirror of FAF's `UnRpnContractsTo`.
Source: none: infrastructure (FAF `escExpand`, `UnRpnContractsTo`)
Kind: D
Fidelity: n/a -/
def EscExpandsTo (ts out : List ℕ) : Prop := ∀ rest, escExpand (ts ++ rest) = out ++ escExpand rest

/-- `escExpand` of the empty stream is empty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma escExpand_nil : escExpand [] = [] := rfl

/-- `EscExpandsTo` composes under append.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EscExpandsTo.append {xs ox ys oy : List ℕ} (hx : EscExpandsTo xs ox)
    (hy : EscExpandsTo ys oy) : EscExpandsTo (xs ++ ys) (ox ++ oy) := fun rest => by
  rw [List.append_assoc, hx (ys ++ rest), hy rest, List.append_assoc]

/-- The empty run expands to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EscExpandsTo.nil : EscExpandsTo [] [] := fun rest => by simp

/-- At the empty continuation: `escExpand ts = out`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EscExpandsTo.eq {ts out : List ℕ} (h : EscExpandsTo ts out) : escExpand ts = out := by
  have := h []
  rwa [List.append_nil, escExpand_nil, List.append_nil] at this

/-- At the empty continuation: `unRpn ts = out`.
Source: none: infrastructure (FAF `UnRpnContractsTo`)
Kind: L
Fidelity: n/a -/
lemma unRpnContractsTo_eq {ts out : List ℕ} (h : UnRpnContractsTo ts out) : unRpn ts = out := by
  have := h []
  rwa [List.append_nil, unRpn_nil, List.append_nil] at this

/-- The empty run contracts to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unRpnContractsTo_nil : UnRpnContractsTo [] [] := fun rest => by simp

/-- A price chunk `[0, ⌜φ⌝, k]` expands to its escape `[0, 1, ⌜φ⌝, k]` (FAF's
`escExpand_price_chunk`, at a code that is never `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma escExpandsTo_price (φ : Sentence) (k : ℕ) :
    EscExpandsTo [0, Encodable.encode φ, k] [0, 1, Encodable.encode φ, k] := fun rest => by
  simpa using escExpand_price_chunk _ k (encode_sentence_ne_zero φ) rest

/-- The escaped price chunk contracts back to the pair-code chunk (FAF's `unRpn_price_escape` at
the canonical code).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unRpnContractsTo_price_escape (φ : Sentence) (k : ℕ) :
    UnRpnContractsTo [0, 1, Encodable.encode φ, k] [0, Encodable.encode φ, k] := fun rest => by
  simpa using unRpn_price_escape (Encodable.encodek φ) k rest

/-- A trade frame `[6, ⌜ψ⌝]` expands to its escape `[6, 1, ⌜ψ⌝]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma escExpandsTo_trade (ψ : Sentence) :
    EscExpandsTo [6, Encodable.encode ψ] [6, 1, Encodable.encode ψ] := fun rest => by
  simpa using escExpand_trade_chunk _ (encode_sentence_ne_zero ψ) rest

/-- The escaped trade frame contracts back.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unRpnContractsTo_trade_escape (ψ : Sentence) :
    UnRpnContractsTo [6, 1, Encodable.encode ψ] [6, Encodable.encode ψ] := fun rest => by
  simpa using unRpn_trade_escape (Encodable.encodek ψ) rest

/-- A constant chunk `[1, c]` is copied by `escExpand`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma escExpandsTo_const (c : ℕ) : EscExpandsTo [1, c] [1, c] := fun rest => by
  simpa using escExpand_payload_chunk 1 c (Or.inl rfl) rest

/-- A bare operator tag (`2`, `3`, `4`) is copied by `escExpand`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma escExpandsTo_single (t : ℕ) (ht : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ 6 ∧ t ≠ 7) :
    EscExpandsTo [t] [t] := fun rest => by
  simpa using escExpand_single_chunk t ht rest

/-- `digitize` on a cons.
Source: none: infrastructure (FAF `digitize`)
Kind: L
Fidelity: n/a -/
lemma digitize_cons (t : ℕ) (l : List ℕ) : digitize (t :: l) = tokenBlock t ++ digitize l := by
  simp [digitize]

/-- The escape token `1` is the two-digit block `[1, 4]`.
Source: none: infrastructure (FAF `tokenBlock`, `natDigits4`)
Kind: L
Fidelity: n/a -/
lemma length_tokenBlock_one : (tokenBlock 1).length = 2 := by
  simp [tokenBlock, natDigits4]

/-- **The escape splice of a closed same-day term.** `escExpand` rewrites `e.serialize`, ahead
of any continuation, to a stream `out` that `unRpn` contracts back to `e.serialize` ahead of any
continuation, and `out` costs exactly two digits more per price leaf in FAF's digit meter.
Structural induction over the term with FAF's chunk equations (`escExpand_price_chunk`,
`unRpn_price_escape`, the payload and single-token chunks).
Source: FAF `Framework/Emission/RpnSentence.lean` (`escExpand`, `unRpn`); audit r2 adversarial §2.1
Kind: P
Fidelity: n/a
Hyps: (a) `PriceLeavesIn` (closed, day-`n` leaves, no `safeRecip`/`var`/`letE`) -/
theorem escExpand_serialize_spec {A : Finset Sentence} {n : ℕ} :
    ∀ e : EF, PriceLeavesIn A n e →
      ∃ out : List ℕ, EscExpandsTo e.serialize out ∧ UnRpnContractsTo out e.serialize ∧
        (digitize out).length = (digitize e.serialize).length + 2 * priceLeaves e
  | .price φ k, _ =>
      ⟨[0, 1, Encodable.encode φ, k], escExpandsTo_price φ k, unRpnContractsTo_price_escape φ k, by
        simp only [EF.serialize, priceLeaves, digitize_cons, List.length_append,
          length_tokenBlock_one]
        omega⟩
  | .const q, _ =>
      ⟨[1, Encodable.encode q], escExpandsTo_const _,
        (UnRpnTransparent.payload 1 _ (Or.inl rfl)).contractsTo, by simp [EF.serialize, priceLeaves]⟩
  | .add a b, ⟨ha, hb⟩ => by
      obtain ⟨oa, ea, ua, da⟩ := escExpand_serialize_spec a ha
      obtain ⟨ob, eb, ub, db⟩ := escExpand_serialize_spec b hb
      refine ⟨oa ++ ob ++ [2], (ea.append eb).append (escExpandsTo_single 2 (by norm_num)),
        (ua.append ub).append (UnRpnTransparent.single 2 (by norm_num)).contractsTo, ?_⟩
      simp only [EF.serialize, priceLeaves, digitize_append, List.length_append, da, db]
      ring
  | .mul a b, ⟨ha, hb⟩ => by
      obtain ⟨oa, ea, ua, da⟩ := escExpand_serialize_spec a ha
      obtain ⟨ob, eb, ub, db⟩ := escExpand_serialize_spec b hb
      refine ⟨oa ++ ob ++ [3], (ea.append eb).append (escExpandsTo_single 3 (by norm_num)),
        (ua.append ub).append (UnRpnTransparent.single 3 (by norm_num)).contractsTo, ?_⟩
      simp only [EF.serialize, priceLeaves, digitize_append, List.length_append, da, db]
      ring
  | .max a b, ⟨ha, hb⟩ => by
      obtain ⟨oa, ea, ua, da⟩ := escExpand_serialize_spec a ha
      obtain ⟨ob, eb, ub, db⟩ := escExpand_serialize_spec b hb
      refine ⟨oa ++ ob ++ [4], (ea.append eb).append (escExpandsTo_single 4 (by norm_num)),
        (ua.append ub).append (UnRpnTransparent.single 4 (by norm_num)).contractsTo, ?_⟩
      simp only [EF.serialize, priceLeaves, digitize_append, List.length_append, da, db]
      ring
  | .safeRecip _, hp => hp.elim
  | .var _, hp => hp.elim
  | .letE _ _, hp => hp.elim

/-- **The escape splice of a strategy stream** built from closed same-day terms: `escExpand`
rewrites `serializeTrades L` to a stream that `unRpn` contracts back exactly, costing two digits
per price leaf and two per trade frame.
Source: FAF `serializeTrades`, `escExpand_trade_chunk`, `unRpn_trade_escape`; audit r2 adversarial §2.1
Kind: C
Fidelity: n/a
Hyps: (a) every coefficient `PriceLeavesIn` -/
theorem escExpand_serializeTrades_spec {A : Finset Sentence} {n : ℕ} :
    ∀ L : List (EF × Sentence), (∀ p ∈ L, PriceLeavesIn A n p.1) →
      ∃ out : List ℕ, EscExpandsTo (serializeTrades L) out ∧
        UnRpnContractsTo out (serializeTrades L) ∧
        (digitize out).length = (digitize (serializeTrades L)).length +
          2 * (L.map fun p => priceLeaves p.1).sum + 2 * L.length
  | [], _ => ⟨[], EscExpandsTo.nil, unRpnContractsTo_nil, by simp [serializeTrades]⟩
  | (e, ψ) :: L, hL => by
      obtain ⟨oe, ee, ue, de⟩ := escExpand_serialize_spec e (hL _ (List.mem_cons_self ..))
      obtain ⟨oL, eL, uL, dL⟩ :=
        escExpand_serializeTrades_spec L fun p hp => hL p (List.mem_cons_of_mem _ hp)
      have hs : serializeTrades ((e, ψ) :: L) =
          e.serialize ++ ([6, Encodable.encode ψ] ++ serializeTrades L) := by
        simp [serializeTrades]
      refine ⟨oe ++ ([6, 1, Encodable.encode ψ] ++ oL), ?_, ?_, ?_⟩
      · rw [hs]
        exact ee.append ((escExpandsTo_trade ψ).append eL)
      · rw [hs]
        exact ue.append ((unRpnContractsTo_trade_escape ψ).append uL)
      · rw [hs]
        simp only [digitize_append, digitize_cons, List.length_append, List.map_cons,
          List.sum_cons, List.length_cons, length_tokenBlock_one, de, dL]
        simp only [digitize, List.flatMap_nil, List.length_nil]
        ring

/-! ## At `tentExpr`: the stream FAF reads -/

/-- **The escape expansion of `tentExpr` is an `unRpn`-preimage of its serialization**:
`unRpn (escExpand (tentExpr 𝓜 m h Q).serialize) = (tentExpr 𝓜 m h Q).serialize`. So a machine
that emits the digits of `escExpand (… .serialize)` (inside any trade frame, likewise escaped:
`escExpand_serializeTrades_spec`) is read by FAF's decoder as the term itself; FAF's
`strategyOfTokens_unRpn_escExpand` is the strategy-level form.
Source: FAF `strategyOfOutput`, `unRpn`, `escExpand`; audit r2 adversarial §2.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem unRpn_escExpand_tentExpr (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    unRpn (escExpand (tentExpr 𝓜 m h Q).serialize) = (tentExpr 𝓜 m h Q).serialize := by
  obtain ⟨out, e, u, -⟩ := escExpand_serialize_spec _ (tentExpr_priceLeavesIn 𝓜 m h Q)
  rw [e.eq, unRpnContractsTo_eq u]

/-- **The escape expansion of `tentExpr` costs exactly `8·|S m|` more digits** than the raw
serialization: two per price leaf, four leaves per day-`m` sentence.
Source: audit r2 adversarial §2.1 (which estimated `6·|S m|`; the count is `8·|S m|`)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem escExpand_tentExpr_digitize_length (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    (digitize (escExpand (tentExpr 𝓜 m h Q).serialize)).length =
      (digitize (tentExpr 𝓜 m h Q).serialize).length + 8 * (𝒮.S m).card := by
  obtain ⟨out, e, -, d⟩ := escExpand_serialize_spec _ (tentExpr_priceLeavesIn 𝓜 m h Q)
  rw [e.eq, d, priceLeaves_tentExpr]
  ring

/-- **E2(d), the bit bound on the stream FAF's class reads.** Under `Bits.lean`'s hypotheses on
`K` (`4^K` above the day, the day-`m` leaf codes and `(2·chainDen + 2)²`), the digitized
escape-expanded stream of `tentExpr 𝓜 m h Q` — which `unRpn` contracts to the term's
serialization (`unRpn_escExpand_tentExpr`) — has length at most
`(K+1)·3·(88·|S (m+h+1)| + 1) + 8·|S m|`. The leaves are metered by their Gödel codes (`hA`), the
escape spelling; the canonical-run spelling is not metered here (module docstring).
Source: [[bli-program]] §3.4 (size `O(|S_m| · poly(m, log d))`); mandate E2(d); audit r2
adversarial §2.1
Kind: C
Fidelity: exact for FAF's `escExpand` stream; variant: leaves metered by Gödel code (the escape
spelling), not by the canonical run `rpn φ`
Hyps: (a) `4^K` above the day, the leaf codes and `(2·chainDen + 2)²` -/
theorem tentExpr_escExpand_digitize_length_le (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1))
    (K : ℕ) (hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ K) (hm : m < 4 ^ K)
    (hD : (2 * chainDen 𝓜 m h + 2) ^ 2 < 4 ^ K) :
    (digitize (escExpand (tentExpr 𝓜 m h Q).serialize)).length ≤
      (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) + 8 * (𝒮.S m).card := by
  rw [escExpand_tentExpr_digitize_length]
  exact Nat.add_le_add_right (tentExpr_digitize_length_le 𝓜 m h Q K hA hm hD) _

/-- **E2(d) in the mandate's form, on the stream FAF reads**: under a mesh bound `D`, any
`K ≥ (4h+2)·(log₄(D+1)+1) + 2` that covers the day and the day-`m` leaf codes bounds the
escape-expanded digit stream by `(K+1)·3·(88·|S (m+h+1)| + 1) + 8·|S m|`.
Source: mandate E2(d); audit r2 adversarial §2.1
Kind: C
Fidelity: exact for FAF's `escExpand` stream; variant: leaves metered by Gödel code
Hyps: (a) the mesh bound; `K` above the polynomial, the day and the leaf codes -/
theorem tentExpr_escExpand_digitize_length_le_poly (𝓜 : Mesh) (m h : ℕ)
    (Q : Table 𝒮 (m + h + 1)) (D : ℕ) (hD : ∀ k, k ≤ h + 1 → 𝓜.d (m + k) ≤ D) (K : ℕ)
    (hK : (4 * h + 2) * (Nat.log 4 (D + 1) + 1) + 2 ≤ K)
    (hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ K) (hm : m < 4 ^ K) :
    (digitize (escExpand (tentExpr 𝓜 m h Q).serialize)).length ≤
      (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1)) + 8 * (𝒮.S m).card := by
  rw [escExpand_tentExpr_digitize_length]
  exact Nat.add_le_add_right (tentExpr_digitize_length_le_poly 𝓜 m h Q D hD K hK hA hm) _

/-- **A one-trade day, whole stream.** The escape expansion of `serializeTrades [(tentExpr 𝓜 m h Q, ψ)]`
contracts back under `unRpn` and, if `4^K` also covers `⌜ψ⌝`, has digit length at most
`(K+1)·(3·(88·|S (m+h+1)| + 1) + 2) + 8·|S m| + 2` — what `bli-assemble`'s machine emits for a
day whose strategy is one trade with this coefficient (FAF's `strategyOfTokens_unRpn_escExpand`
turns the contraction into the strategy identity).
Source: mandate E2(d); FAF `serializeTrades`, `strategyOfTokens_unRpn_escExpand`; audit r2
adversarial §2.1 (fix (ii), the trade-frame form)
Kind: C
Fidelity: exact for FAF's `escExpand` stream; variant: leaves metered by Gödel code
Hyps: (a) `4^K` above the day, the leaf codes, `⌜ψ⌝` and `(2·chainDen + 2)²` -/
theorem escExpand_serializeTrades_single_digitize_length_le (𝓜 : Mesh) (m h : ℕ)
    (Q : Table 𝒮 (m + h + 1)) (ψ : Sentence) (K : ℕ)
    (hA : ∀ φ ∈ 𝒮.S m, Encodable.encode φ < 4 ^ K) (hm : m < 4 ^ K)
    (hD : (2 * chainDen 𝓜 m h + 2) ^ 2 < 4 ^ K) (hψ : Encodable.encode ψ < 4 ^ K) :
    unRpn (escExpand (serializeTrades [(tentExpr 𝓜 m h Q, ψ)])) =
        serializeTrades [(tentExpr 𝓜 m h Q, ψ)] ∧
      (digitize (escExpand (serializeTrades [(tentExpr 𝓜 m h Q, ψ)]))).length ≤
        (K + 1) * (3 * (88 * (𝒮.S (m + h + 1)).card + 1) + 2) + 8 * (𝒮.S m).card + 2 := by
  obtain ⟨out, e, u, d⟩ := escExpand_serializeTrades_spec (A := 𝒮.S m) (n := m)
    [(tentExpr 𝓜 m h Q, ψ)] (by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact tentExpr_priceLeavesIn 𝓜 m h Q)
  refine ⟨by rw [e.eq, unRpnContractsTo_eq u], ?_⟩
  rw [e.eq, d]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton,
    priceLeaves_tentExpr]
  have hs : serializeTrades [(tentExpr 𝓜 m h Q, ψ)] =
      (tentExpr 𝓜 m h Q).serialize ++ [6, Encodable.encode ψ] := by
    simp [serializeTrades]
  rw [hs, digitize_append, List.length_append]
  have h1 := tentExpr_digitize_length_le 𝓜 m h Q K hA hm hD
  have h2 : (digitize [6, Encodable.encode ψ]).length ≤ (K + 1) * 2 := by
    refine length_digitize_le K _ ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have h8 : 8 < 4 ^ K := by
        have h2 := two_le_chainDen 𝓜 m h
        have h36 : 6 ^ 2 ≤ (2 * chainDen 𝓜 m h + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        norm_num at h36
        omega
      omega
    · exact hψ
  nlinarith

end Cleanroom.Bli.BliSuperbelief
