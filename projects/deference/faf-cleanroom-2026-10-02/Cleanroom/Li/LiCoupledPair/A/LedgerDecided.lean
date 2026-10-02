import Cleanroom.Li.LiCoupledPair.DefsHeavy

/-!
# `li-coupled-pair` · A/LedgerDecided: ledger-decided ⟺ computable (T3.1)

[[ledger-decided-tie-breaks]] (vq-wiki-023, lean-deference-074, lean-deference-2-019): "`Γ` + the
ledger facts decide which option was selected … is extensionally equivalent to 'the tie-break is a
computable function of the published estimates': one direction is `Γ` representing computable
functions and proving their computations; conversely, if the selection is always `Γ`-decided from
the ledger, enumerating proofs computes it."

Over FAF: a **selection family** `S : ℕ → ℕ → Sentence` ("on day `n` option `j` was selected") and
a selector `sel : ℕ → ℕ`. `LedgerDecided DP S sel` is the stage form — the selected option's
sentence enters some stage, and no other option's sentence ever does (the page's "`Γ`-provably
unique"); `LedgerDeterminedVia DP S sel` is its semantic twin — every completed-theory world of `DP`
holds `S n j` iff `j = sel n`.

* **Forward (`computable_of_ledgerDecided`, any computable process):** `LedgerDecided DP S sel` with
  `DP` computable and `S` computable makes `sel` computable — dovetail `⟨j, s⟩` and test
  `S n j ∈ DP.D s` (`Nat.rfindOpt`; the stage sets are computable from the process code, Finset
  membership is primitive recursive through FAF's sorted-list encoding). "Enumerating proofs
  computes it."
* **Backward (`ledgerDecided_selectorFamily`, `ledgerDeterminedVia_selectorFamily`, over
  `paperDP T`):** for computable `sel`, FAF's `BooleanQuoteCode.ofComputable` names the predicate
  `⟨n, j⟩ ↦ sel n = j` by a quotation code; its literal family `selectorFamily T sel` is
  `LedgerDeterminedVia` (`BooleanQuoteCode.reflected`) and, through
  `QuotationTheoryPresentation.quote_positive_enters` / `quote_negative_refutes` at
  `paperQuotationPresentation T`, `LedgerDecided` in the stage form. "`Γ` representing computable
  functions and proving their computations" is `[𝗥₀ ⪯ T]`.
* **The iff (`ledgerDecided_iff_computable`):** at `paperDP T`,
  `(∃ S, Computable₂ S ∧ LedgerDecided (paperDP T) S sel) ↔ Computable sel`.

**Disclosure (mandate T3.1).** The page's "computable *from the ledger*" is rendered as "computable
outright", because in every instance here the ledger table is itself computable (the published
estimates are a LIA's quotes); the relativized form ("computable relative to an uncomputable
table") has no FAF carrier (Mathlib's `Nat.Partrec` is unrelativized) and is recorded as a finding,
not formalized. Fidelity: `exact` for the page's equivalence under that rendering. The uniqueness
half of the backward direction needs `[𝗣𝗔⁻ ⪯ T] [Consistent T]` (over an inconsistent `T` the
stage form's "no other option ever enters" is false, since everything enters) — the honest
requirement, which the page's "`Γ` consistent" supplies.

T3.2 (`legality_not_computability`) is a citation of `li-quote-lane`'s `ledgerLuv_thresholdCodes`
(holds for every table, computable or not) with one sentence in the findings; T3.3 (the `ψ`-rule
counterexample) is angle B's. Scope: one-way.
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-! ## Definitions of record -/

/-- **Ledger-decided selection** (stage form): on every day `n` the selected option's sentence
`S n (sel n)` enters some stage of `DP`, and no other option's sentence `S n j` (`j ≠ sel n`) ever
enters any stage — the selection is decided in a stage and provably unique (the page's
"`Γ`-provably unique"). The second clause is the *stage* form, weaker than the *refutation* form
("`Γ` refutes `S n j` for `j ≠ sel n`"): so the forward direction `computable_of_ledgerDecided`
assumes less than the page needs, and the backward direction derives the stage form from
refutation plus consistency (`ledgerDecided_selectorFamily`). Scope: one-way.
Source: [[ledger-decided-tie-breaks]] §"Ledger-decided ⟺ computable from the ledger" (vq-wiki-023; lean-deference-2-019)
Kind: D
Fidelity: exact (stage form of "`Γ` + the ledger facts decide which option was selected"; weaker than refutation in the uniqueness clause)
Hyps: n/a -/
def LedgerDecided (DP : DeductiveProcess) (S : ℕ → ℕ → Sentence) (sel : ℕ → ℕ) : Prop :=
  (∀ n, ∃ s, S n (sel n) ∈ DP.D s) ∧ (∀ n j s, S n j ∈ DP.D s → j = sel n)

/-- **Ledger-determined selection** (semantic twin): every world consistent with every stage of
`DP` holds `S n j` iff `j = sel n`. Scope: one-way.
Source: [[ledger-decided-tie-breaks]] (vq-wiki-023); `li-asymp-calc` `LUV.DeterminedVia` (the LUV analogue)
Kind: D
Fidelity: exact
Hyps: n/a -/
def LedgerDeterminedVia (DP : DeductiveProcess) (S : ℕ → ℕ → Sentence) (sel : ℕ → ℕ) : Prop :=
  ∀ n j (v : PCWorld), v.ConsistentWithTheory DP → (v.Holds (S n j) ↔ j = sel n)

/-! ## Computability infrastructure -/

/-- The stages of a computable deductive process form a computable function (run the process
code; it is total on every day).
Source: none: infrastructure (FAF `ComputableDeductiveProcess`)
Kind: L
Fidelity: n/a -/
theorem stage_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP) :
    Computable DP.D := by
  obtain ⟨code, hcode⟩ := hDP
  have h1 : Partrec fun n : ℕ => code.eval n :=
    Nat.Partrec.Code.eval_part.comp (Computable.const code) Computable.id
  have h2 : Computable fun n => Encodable.encode (DP.D n) := h1.of_eq_tot hcode
  have h3 : Computable fun n =>
      (Encodable.decode (α := Finset Sentence) (Encodable.encode (DP.D n))).getD ∅ :=
    Computable.option_getD (Computable.decode.comp h2) (Computable.const ∅)
  exact h3.of_eq fun n => by simp [Encodable.encodek]

/-- Decoding the code of a `Finset Sentence` as a `List Sentence` gives a list with the same
members (FAF's `Finset Sentence` encoding is Mathlib's multiset encoding of the sorted list).
Source: none: infrastructure (FAF `sentenceFinsetEncode_eq`; Mathlib `Multiset.encodable`)
Kind: L
Fidelity: n/a -/
lemma finsetSentence_decode_list (s : Finset Sentence) :
    ∃ l : List Sentence, Encodable.decode (α := List Sentence) (Encodable.encode s) = some l ∧
      ∀ φ, φ ∈ l ↔ φ ∈ s := by
  have h : Encodable.decode (α := Multiset Sentence) (Encodable.encode s) = some s.1 := by
    rw [sentenceFinsetEncode_eq]
    exact Encodable.encodek s.1
  change decodeMultiset (Encodable.encode s) = some s.1 at h
  unfold decodeMultiset at h
  cases hd : Encodable.decode (α := List Sentence) (Encodable.encode s) with
  | none => rw [hd] at h; simp at h
  | some l =>
    rw [hd] at h
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h
    refine ⟨l, rfl, fun φ => ?_⟩
    rw [Finset.mem_def, ← h, Multiset.mem_coe]

/-- Membership in a `Finset Sentence` is primitive recursive (through the sorted-list encoding and
`List.idxOf`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma finsetSentence_mem_prim :
    Primrec₂ fun (φ : Sentence) (s : Finset Sentence) => decide (φ ∈ s) := by
  have hl : Primrec fun s : Finset Sentence =>
      (Encodable.decode (α := List Sentence) (Encodable.encode s)).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const [])
  have hidx : Primrec fun p : Sentence × List Sentence => decide (p.2.idxOf p.1 < p.2.length) :=
    Primrec.nat_lt.decide.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)
  refine (hidx.comp (Primrec.fst.pair (hl.comp Primrec.snd))).of_eq fun p => ?_
  obtain ⟨l, hl', hmem⟩ := finsetSentence_decode_list p.2
  simp only [hl', Option.getD_some]
  rw [decide_eq_decide, List.idxOf_lt_length_iff]
  exact hmem p.1

/-! ## T3.1, forward: ledger-decided ⟹ computable (any computable process) -/

/-- The dovetail test: at packed candidate `⟨j, s⟩`, answer `j` if `S n j` is in stage `s`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def selSearch (DP : DeductiveProcess) (S : ℕ → ℕ → Sentence) (n k : ℕ) : Option ℕ :=
  cond (decide (S n k.unpair.1 ∈ DP.D k.unpair.2)) (some k.unpair.1) none

/-- The dovetail test is computable from the process and the family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma selSearch_computable {DP : DeductiveProcess} (hDP : ComputableDeductiveProcess DP)
    {S : ℕ → ℕ → Sentence} (hS : Computable₂ S) : Computable₂ (selSearch DP S) := by
  have hj : Computable fun p : ℕ × ℕ => p.2.unpair.1 :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have hs : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have hsent : Computable fun p : ℕ × ℕ => S p.1 p.2.unpair.1 := hS.comp Computable.fst hj
  have hstage : Computable fun p : ℕ × ℕ => DP.D p.2.unpair.2 := (stage_computable hDP).comp hs
  have hmem : Computable fun p : ℕ × ℕ => decide (S p.1 p.2.unpair.1 ∈ DP.D p.2.unpair.2) :=
    (finsetSentence_mem_prim.to_comp.comp hsent hstage : _)
  exact (Computable.cond hmem (Computable.option_some.comp hj) (Computable.const none)).of_eq
    fun _ => rfl

/-- **T3.1, forward (headline).** Over any computable deductive process, a ledger-decided
selection along a computable family is computable: dovetail the candidates `⟨j, s⟩`, return the
first `j` whose sentence has entered stage `s`; by uniqueness it is `sel n`. "If the selection is
always `Γ`-decided from the ledger, enumerating proofs computes it."
Source: [[ledger-decided-tie-breaks]] §"Ledger-decided ⟺ computable from the ledger" (vq-wiki-023; lean-deference-074; lean-deference-2-019)
Kind: C
Fidelity: exact (with the "computable outright" rendering of "from the ledger"; module docstring)
Hyps: (a) none -/
theorem computable_of_ledgerDecided {DP : DeductiveProcess} {S : ℕ → ℕ → Sentence} {sel : ℕ → ℕ}
    (hDP : ComputableDeductiveProcess DP) (hS : Computable₂ S) (h : LedgerDecided DP S sel) :
    Computable sel := by
  have hpart : Partrec fun n => Nat.rfindOpt (selSearch DP S n) :=
    Partrec.rfindOpt (selSearch_computable hDP hS)
  refine hpart.of_eq_tot fun n => ?_
  obtain ⟨s, hs⟩ := h.1 n
  have hdom : (Nat.rfindOpt (selSearch DP S n)).Dom :=
    Nat.rfindOpt_dom.mpr ⟨Nat.pair (sel n) s, sel n, by simp [selSearch, Option.mem_def, hs]⟩
  have hget := Part.get_mem hdom
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hget
  rw [Option.mem_def] at hk
  have hval : (Nat.rfindOpt (selSearch DP S n)).get hdom = sel n := by
    generalize hA : (Nat.rfindOpt (selSearch DP S n)).get hdom = A at hk ⊢
    unfold selSearch at hk
    cases hdec : decide (S n k.unpair.1 ∈ DP.D k.unpair.2) with
    | false => rw [hdec] at hk; exact absurd hk (by simp)
    | true =>
      rw [hdec] at hk
      simp only [Bool.cond_true, Option.some.injEq] at hk
      rw [← hk]
      exact h.2 n _ _ (decide_eq_true_iff.mp hdec)
  rw [← hval]
  exact hget

/-! ## T3.1, backward: computable ⟹ ledger-decided and ledger-determined (over `paperDP T`) -/

/-- The selector's truth predicate on the packed input `⟨n, j⟩`: `sel n = j`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def selTruth (sel : ℕ → ℕ) (z : ℕ) : Prop := sel z.unpair.1 = z.unpair.2

/-- The truth predicate of a computable selector is a computable predicate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma selTruth_computablePred {sel : ℕ → ℕ} (hsel : Computable sel) :
    ComputablePred (selTruth sel) := by
  rw [ComputablePred.computable_iff]
  refine ⟨fun z => decide (sel z.unpair.1 = z.unpair.2), ?_, ?_⟩
  · exact (Primrec.eq.decide.to_comp.comp (hsel.comp (Computable.fst.comp Primrec.unpair.to_comp))
      (Computable.snd.comp Primrec.unpair.to_comp) : _)
  · funext z
    simp [selTruth]

section paper

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] (sel : ℕ → ℕ) (hsel : Computable sel)

/-- FAF's Boolean quote code naming the selector's truth predicate (`BooleanQuoteCode.ofComputable`:
the predicate's decider is named by its program; completeness is Σ₁-completeness of `T`).
Source: mandate T3.1; FAF `BooleanQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
noncomputable def selectorCode : BooleanQuoteCode T (selTruth sel) :=
  BooleanQuoteCode.ofComputable (selTruth_computablePred hsel)

/-- **The selection family of a computable selector:** `S n j := ⌜sel n = j⌝`, the quotation literal
`selectorCode.sentence ⟨n, j⟩` of `A`'s language (a tag-`2` quotation atom).
Source: mandate T3.1
Kind: D
Fidelity: exact -/
noncomputable def selectorFamily (n j : ℕ) : Sentence :=
  (selectorCode T sel hsel).sentence (Nat.pair n j)

omit [T.Δ₁] in
/-- The selection family is computable (the quotation atom's code is a fixed arithmetic shell
around the packed input, `encode_quoteAtom`).
Source: none: infrastructure (FAF `encode_quoteAtom`)
Kind: L
Fidelity: n/a -/
theorem selectorFamily_computable : Computable₂ (selectorFamily T sel hsel) := by
  have hq : Primrec fun w : ℕ => quoteAtom w := by
    refine Primrec.encode_iff.mp ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuotePos))
          (Primrec₂.natPair.comp (Primrec.const (Encodable.encode universalQuoteNeg))
            Primrec.id))))).of_eq fun w => ?_)
    rw [encode_quoteAtom]
    rfl
  have hpack : Primrec fun p : ℕ × ℕ => Nat.pair (selectorCode T sel hsel).code (Nat.pair p.1 p.2) :=
    Primrec₂.natPair.comp (Primrec.const _) (Primrec₂.natPair.comp Primrec.fst Primrec.snd)
  exact ((hq.comp hpack).to_comp).of_eq fun _ => rfl

/-- **T3.1, backward (semantic): the selection family of a computable selector is
ledger-determined over `paperDP T`** — every completed-theory world holds `⌜sel n = j⌝` iff
`j = sel n` (FAF's `BooleanQuoteCode.reflected` at `paperQuotationPresentation T`).
Source: [[ledger-decided-tie-breaks]] ("`Γ` representing computable functions and proving their computations"); mandate T3.1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerDeterminedVia_selectorFamily :
    LedgerDeterminedVia (paperDP T) (selectorFamily T sel hsel) sel := by
  intro n j v hv
  have := (selectorCode T sel hsel).reflected (paperQuotationPresentation T) (Nat.pair n j) v hv
  simpa [selectorFamily, selTruth, Nat.unpair_pair, eq_comm] using this

/-- **T3.1, backward (stage form): the selection family of a computable selector is
ledger-decided over `paperDP T`** — `⌜sel n = sel n⌝` enters some stage
(`quote_positive_enters`), and for `j ≠ sel n` the refutation `∼⌜sel n = j⌝` enters some stage
(`quote_negative_refutes`), so `⌜sel n = j⌝` itself never does (every stage has a consistent
world, `paperDP_hworld`).
Source: [[ledger-decided-tie-breaks]]; mandate T3.1
Kind: C
Fidelity: exact
Hyps: (a) none (`[𝗣𝗔⁻ ⪯ T] [Consistent T]` for the uniqueness half; module docstring) -/
theorem ledgerDecided_selectorFamily [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T] :
    LedgerDecided (paperDP T) (selectorFamily T sel hsel) sel := by
  refine ⟨fun n => ?_, fun n j s hmem => ?_⟩
  · have hpos := (selectorCode T sel hsel).pos_complete (Nat.pair n (sel n))
      (by simp [selTruth])
    obtain ⟨k, hk⟩ := (paperQuotationPresentation T).quote_positive_enters _ _ hpos
    exact ⟨k, hk⟩
  · by_contra hne
    have hneg := (selectorCode T sel hsel).neg_complete (Nat.pair n j)
      (by simp only [selTruth, Nat.unpair_pair]; exact fun h => hne h.symm)
    obtain ⟨k, hk⟩ := (paperQuotationPresentation T).quote_negative_refutes _ _ hneg
    obtain ⟨v, hv⟩ := paperDP_hworld T (max s k)
    have h1 : v.Holds (selectorFamily T sel hsel n j) :=
      hv _ ((paperDP T).mono_le (le_max_left s k) hmem)
    have h2 : v.Holds (∼ selectorFamily T sel hsel n j) :=
      hv _ ((paperDP T).mono_le (le_max_right s k) hk)
    exact (PCWorld.holds_neg v _).mp h2 h1

/-- **T3.1 (headline): ledger-decided ⟺ computable, over `paperDP T`.** A selector is ledger-decided
along *some* computable selection family iff it is computable. Forward: `computable_of_ledgerDecided`;
backward: `selectorFamily` with `ledgerDecided_selectorFamily`. Disclosure: "computable from the
ledger" is rendered "computable outright" (module docstring). Statement weakness (repair round 1,
audit r1): with the family existentially quantified, the `⟸` half is trivially witnessable by a
family that encodes the answer with one fixed theorem and its negation — the content of the
backward direction is `ledgerDecided_selectorFamily` (the page's family), not this iff.
Source: [[ledger-decided-tie-breaks]] §"Ledger-decided ⟺ computable from the ledger" (vq-wiki-023; lean-deference-074; lean-deference-2-019)
Kind: C
Fidelity: variant: the family is existentially quantified (its `⟸` half trivially witnessable); the page's family is `selectorFamily`; "from the ledger" rendered "computable outright"
Hyps: (a) none -/
theorem ledgerDecided_iff_computable [𝗣𝗔⁻ ⪯ T] [LO.Entailment.Consistent T] :
    (∃ S : ℕ → ℕ → Sentence, Computable₂ S ∧ LedgerDecided (paperDP T) S sel) ↔ Computable sel :=
  ⟨fun ⟨_, hS, h⟩ => computable_of_ledgerDecided (paperDP_computable T) hS h,
    fun hsel => ⟨selectorFamily T sel hsel, selectorFamily_computable T sel hsel,
      ledgerDecided_selectorFamily T sel hsel⟩⟩

end paper

/-! ## N+: a non-constant selector over `paperDP 𝗜𝚺₁` -/

/-- The alternating selector `n ↦ n % 2`.
Source: none: infrastructure (T3.1 witness)
Kind: D
Fidelity: n/a -/
def altSel (n : ℕ) : ℕ := n % 2

/-- `altSel` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma altSel_computable : Computable altSel :=
  (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)).to_comp

/-- **N+ for T3.1:** the full hypothesis package of `computable_of_ledgerDecided` is inhabited over
`paperDP 𝗜𝚺₁` by the *non-constant* selector `altSel` with its computable selection family
`selectorFamily 𝗜𝚺₁ altSel` — ledger-decided and ledger-determined — and `altSel 0 ≠ altSel 1`.
Source: mandate T3.1 (non-vacuity)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem altSel_ledgerDecided :
    LedgerDecided (paperDP 𝗜𝚺₁) (selectorFamily 𝗜𝚺₁ altSel altSel_computable) altSel ∧
      LedgerDeterminedVia (paperDP 𝗜𝚺₁) (selectorFamily 𝗜𝚺₁ altSel altSel_computable) altSel ∧
      Computable₂ (selectorFamily 𝗜𝚺₁ altSel altSel_computable) ∧ altSel 0 ≠ altSel 1 :=
  ⟨ledgerDecided_selectorFamily 𝗜𝚺₁ altSel altSel_computable,
    ledgerDeterminedVia_selectorFamily 𝗜𝚺₁ altSel altSel_computable,
    selectorFamily_computable 𝗜𝚺₁ altSel altSel_computable, by decide⟩

end Cleanroom.Li.LiCoupledPair.A
