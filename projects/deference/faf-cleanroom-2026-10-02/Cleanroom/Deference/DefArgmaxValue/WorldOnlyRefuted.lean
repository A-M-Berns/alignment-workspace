import Cleanroom.Deference.DefArgmaxValue.Characterize
import Cleanroom.Deference.DefArgmaxValue.Refuted
import Cleanroom.Deference.DefArgmaxValue.Open
import LogicalInduction.Construction.Knowledge.Endpoints

/-!
# `def-argmax-value` · WorldOnlyRefuted: the two world-only conjectures are false as stated — the
liar rebuilt through `paperDP T`'s first-order theorem lane is syntactically world-only
(repair round 2; audit r2 adversarial B2, probe `audit-r2-probes/WorldOnlyLiar.lean` adopted)

`Open.lean` stated (OPEN, "possibly false as stated") that H3 holds on every syntactically
world-only menu — `∀ k (M : Menu k), WorldOnly M → CondStableOn M (selectionPackage_self T f M)`,
where `WorldOnly M` forbids only payload tag `2` (FAF's quotation atoms) in the threshold
sentences — and (2-026's self-opaque route) that the per-index gap `E*(Q^j) − E*(I^j)·m^j`
vanishes on such menus. Audit r1 (fidelity, item 6) predicted a refutation through another lane
of `paperDP T`; the round-2 adversarial auditor carried it out through **`T`'s theorem lane**
(payload tag `paperPrimeTag = 5`):

* FAF's `schemaArgClaimSentence σ t` (`Construction/Knowledge/Endpoints.lean`) is the paper-prime
  atom of `∃⁰ σ(t)`, published by `paperTheoryDP T` when `T ⊢ σ(t)` and refuted when `T ⊢ ∼σ(t)`
  (`paperDP_covers_schemaArgClaim`, `_neg`). With `σ := universalQuotePos` (the positive fiber of
  FAF's universal quotation schema) and `t := binNumeral ⟨c, ⟨n, 1⟩⟩`, the atom `foAtomZ ⟨c, n⟩`
  is reflected in every `paperDP T`-world at the selector's decision — exactly as the tag-`2`
  `quoteAtom` is — because `T` proves `universalQuotePos/[w]` when the decision is `1`
  (`BooleanQuoteCode.pos_complete`), proves `universalQuoteNeg/[w]` when it is `0`, and refutes
  their conjunction (`universalQuote_exclusive_prov`); the compact and unary spellings of `w`
  are interprovable (`provable_subst_binNumeral_iff`).
* The family is e.c. (`schemaArgClaimSentence_machineSentenceCodes` at the compact numeral
  emitter `machineTokenStream_binNumeral_const`), and its codes are primitive recursive jointly
  in `(c, n)` (`MachineSentenceCodes.primrec` on the packed index), which is what the Kleene
  selector needs to read its own price (`foQuotes_computable`).
* The rest is the package's own liar probe verbatim with `foLiar` in place of `liarSentence`:
  the selection identity at the menu's own comparison (`foLiar_holds_iff`), the honest follower,
  the deferred pin through `Pin.lean`'s engine (`foLiarPrice_tendsto_s`), the estimate
  `E*(S) ≈ₙ s·P_{f n}(χ'_n) → s² < s`, so the self-endorsement instance fails and, by the
  package's own characterization `condStableOn_iff_selfEndorseGE_instance_self`, H3 fails for
  `selectionPackage_self` on the menu `{1[χ'_n], const s}` — which is `WorldOnly`
  (`foMenu_worldOnly`: every threshold atom carries tag `5`).

Hence **`condStableOn_of_worldOnly_refuted`**: the former OPEN statement is false for every `T`,
every strictly increasing deferral and every `s ∈ (0,1)`; and **`selfOpaque_perIndex_refuted`**
on the same menu: at `j = 0` the per-index gap tends to `−(1 − s)s ≠ 0`. Instance lines at `𝗣𝗔`,
`succDeferral`, `½`.

Why the theorem lane and not the computation-claim lane (tags `0`/`1`) the round-1 diagnosis
named (audit r2 adversarial N1): FAF's `ComputationTheoryPresentation` publishes a halting claim
when `T` proves it halts and refutes only a *bounded*-halting claim (`boundedFailure_refutes`);
"does not halt" is Π₁ and `T ⊬ ∼halts` in general, so that lane lacks the negative direction a
liar needs. The quotation lane works because `universalQuotePos`/`universalQuoteNeg` are the
value-`1`/value-`0` fibers of one total computation — both Σ₁ — and the theorem lane inherits
exactly that through `paperTheoryDP`'s coverage of `T`'s theorems.

What survives (F19): the honest conjecture needs the complexity clause the sources state ("below
the produce-hardness of `A`'s quotes", vq-wiki-017); no payload-tag test can express it, since
tag `5` carries both ordinary arithmetic and, via `universalQuotePos`, the market's own
decisions; FAF has no object for it.

Single market (self); `[𝗣𝗔⁻ ⪯ T]`-level for the construction.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The first-order (tag-5) twin of the selector atom -/

/-- The packed payload `⟨c, ⟨n, 1⟩⟩` read off a single index `z = ⟨c, n⟩`.
Source: audit r2 adversarial B2 (probe adopted); none: infrastructure
Kind: D
Fidelity: n/a -/
def foPayload (z : ℕ) : ℕ := Nat.pair z.unpair.1 (Nat.pair z.unpair.2 1)

/-- The payload map is a unary ruler.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foPayload_unaryRuler : UnaryRuler foPayload :=
  UnaryRuler.unpairFst.pair (UnaryRuler.unpairSnd.pair (UnaryRuler.const 1))

/-- The payload map has machine digits (a compact numeral emitter exists for it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foPayload_machineDigits : MachineDigits foPayload :=
  MachineDigits.ofUnaryRuler foPayload_unaryRuler

/-- The payload of a pair, unpacked.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foPayload_pair (c n : ℕ) : foPayload (Nat.pair c n) = Nat.pair c (Nat.pair n 1) := by
  simp [foPayload]

/-- **The first-order claim atom** of the packed index `z = ⟨c, n⟩`: the paper-prime of
`∃⁰ universalQuotePos(binNumeral ⟨c, ⟨n, 1⟩⟩)` — one atom with payload tag `paperPrimeTag = 5`
(FAF `schemaArgClaimSentence`), never tag `2`.
Source: audit r2 adversarial B2; FAF `Construction/Knowledge/Endpoints.lean`
Kind: D
Fidelity: exact -/
def foAtomZ (z : ℕ) : Sentence :=
  schemaArgClaimSentence universalQuotePos (binNumeral (foPayload z))

/-- The tag-5 family is e.c. (FAF `schemaArgClaimSentence_machineSentenceCodes` at the compact
numeral emitter).
Source: none: infrastructure (FAF)
Kind: L
Fidelity: n/a -/
theorem foAtomZ_codes : MachineSentenceCodes foAtomZ :=
  schemaArgClaimSentence_machineSentenceCodes universalQuotePos (fun z => binNumeral (foPayload z))
    (fun l => machineTokenStream_binNumeral_const foPayload_machineDigits l)

/-- Its codes are primitive recursive in the packed index.
Source: none: infrastructure (FAF `MachineSentenceCodes.primrec`)
Kind: L
Fidelity: n/a -/
theorem foAtomZ_encode_primrec : Primrec fun z => Encodable.encode (foAtomZ z) :=
  MachineSentenceCodes.primrec foAtomZ_codes

/-- Every atom of `foAtomZ z` carries tag `5`, never `2`.
Source: audit r2 adversarial B2; FAF `paperPrimeCode_unpair_tag`
Kind: L
Fidelity: exact -/
theorem foAtomZ_atom_tag (z : ℕ) : ∀ a ∈ sentenceAtomCodes (foAtomZ z), a.unpair.1 ≠ 2 := by
  intro a ha
  simp only [foAtomZ, schemaArgClaimSentence, sentenceAtomCodes_paperPrimeSentence,
    Finset.mem_singleton] at ha
  subst ha
  rw [paperPrimeCode_unpair_tag]
  norm_num [paperPrimeTag]

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-! ## The selector reading the price of its own tag-5 atom -/

/-- The selector's quotes: `[P_{f n}(foAtomZ ⟨c, n⟩), s_{f n}]`.
Source: audit r2 adversarial B2; mandate target 1a route (ii) (the template)
Kind: D
Fidelity: exact -/
def foQuotes (c : Nat.Partrec.Code) (n : ℕ) : List ℚ :=
  [(paperMarketComputation T).quote (f.f n)
      (Encodable.encode (foAtomZ (Nat.pair (Encodable.encode c) n))),
    probeThreshold T f s n]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quotes are computable in `(c, n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foQuotes_computable (hs : 0 ≤ s) : Computable₂ (foQuotes T f s) := by
  have hg : Computable fun z : Nat.Partrec.Code × ℕ =>
      Encodable.encode (foAtomZ (Nat.pair (Encodable.encode z.1) z.2)) :=
    (foAtomZ_encode_primrec.comp
      (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)).to_comp
  have h1 : Computable fun z : Nat.Partrec.Code × ℕ => (paperMarketComputation T).quote (f.f z.2)
      (Encodable.encode (foAtomZ (Nat.pair (Encodable.encode z.1) z.2))) :=
    (paperMarketComputation T).quote_comp_computable (f.computable.comp Computable.snd) hg
  have h2 : Computable fun z : Nat.Partrec.Code × ℕ => probeThreshold T f s z.2 :=
    (probeThreshold_computable T f s hs).comp Computable.snd
  exact Computable.list_cons.comp h1 (Computable.list_cons.comp h2 (Computable.const []))

/-- The Kleene fixed point of the tag-5 selector.
Source: audit r2 adversarial B2; mandate target 3a (the `selectorCode` template)
Kind: D
Fidelity: exact -/
def foCode (hs : 0 ≤ s) : Nat.Partrec.Code :=
  selectorCode (foQuotes T f s) eqRel (foQuotes_computable T f s hs) eqRel_primrec

/-- **The world-only liar** `χ'_n := foAtomZ ⟨foCode, n⟩`.
Source: audit r2 adversarial B2
Kind: D
Fidelity: exact -/
def foLiar (hs : 0 ≤ s) (n : ℕ) : Sentence :=
  foAtomZ (Nat.pair (Encodable.encode (foCode T f s hs)) n)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The world-only liar is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foLiar_codes (hs : 0 ≤ s) : MachineSentenceCodes (foLiar T f s hs) :=
  (MachineSentenceCodes.comp foAtomZ_codes
    ((UnaryRuler.const (Encodable.encode (foCode T f s hs))).pair UnaryRuler.id)).of_eq
    (fun _ => rfl)

/-- The tag-2 Boolean quote code of the same selector — used only for its two `T`-completeness
fields (`pos_complete`, `neg_complete`), never for its (tag-2) sentence.
Source: audit r2 adversarial B2; `Selector.lean` `selectorQuoteCode`
Kind: D
Fidelity: n/a -/
abbrev foQC (hs : 0 ≤ s) :
    BooleanQuoteCode T (selectorTruth (foQuotes T f s) eqRel (foQuotes_computable T f s hs)
      eqRel_primrec) :=
  selectorQuoteCode (foQuotes T f s) eqRel T (foQuotes_computable T f s hs) eqRel_primrec

omit [Entailment.Consistent T] in
/-- **Reflection through the theorem lane**: a `paperDP T`-world holds `χ'_n` iff the selector's
decision at `⟨n, 1⟩` is `1` — positively by Σ₁-completeness (`pos_complete`), negatively by
`neg_complete` plus `universalQuote_exclusive_prov`, moved between the compact and unary numeral
spellings by `provable_subst_binNumeral_iff`, and published by `paperDP_covers_schemaArgClaim`
/ `_neg`.
Source: audit r2 adversarial B2; FAF `Construction/Knowledge/Endpoints.lean`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem foLiar_holds_iff_truth (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (foLiar T f s hs n) ↔
      selectorTruth (foQuotes T f s) eqRel (foQuotes_computable T f s hs) eqRel_primrec
        (Nat.pair n 1) := by
  have hpay : foPayload (Nat.pair (Encodable.encode (foCode T f s hs)) n) =
      Nat.pair (foQC T f s hs).code (Nat.pair n 1) := foPayload_pair _ _
  constructor
  · intro hH
    by_contra hnt
    have hneg := (foQC T f s hs).neg_complete (Nat.pair n 1) hnt
    have hexc := universalQuote_exclusive_prov T (Nat.pair (foQC T f s hs).code (Nat.pair n 1))
    have hnpos : T ⊢ ∼(universalQuotePos/[↑(Nat.pair (foQC T f s hs).code (Nat.pair n 1))] :
        ArithmeticSentence) := by
      cl_prover [hneg, hexc]
    have h1 : T ⊢ ((∼universalQuotePos)/[↑(Nat.pair (foQC T f s hs).code (Nat.pair n 1))] :
        ArithmeticSentence) := by
      simpa using hnpos
    have h2 := (provable_subst_binNumeral_iff (T := T) (∼universalQuotePos) _).mpr h1
    have hnpos' : T ⊢ ∼(universalQuotePos/[(binNumeral
        (Nat.pair (foQC T f s hs).code (Nat.pair n 1))).const] : ArithmeticSentence) := by
      simpa using h2
    obtain ⟨k, hk⟩ := paperDP_covers_schemaArgClaim_neg (T := T) universalQuotePos _ hnpos'
    have hneg_holds := hv k _ hk
    rw [PCWorld.holds_neg] at hneg_holds
    apply hneg_holds
    unfold foLiar foAtomZ at hH
    rw [hpay] at hH
    exact hH
  · intro ht
    have hpos := (foQC T f s hs).pos_complete (Nat.pair n 1) ht
    have hpos' := (provable_subst_binNumeral_iff (T := T) universalQuotePos _).mpr hpos
    obtain ⟨k, hk⟩ := paperDP_covers_schemaArgClaim (T := T) universalQuotePos _ hpos'
    have := hv k _ hk
    unfold foLiar foAtomZ
    rw [hpay]
    exact this

/-- **The selection identity at the menu's own comparison**: `χ'_n` holds iff
`P_{f n}(χ'_n) < s_{f n}` (route (ii), as `liarSentence_holds_iff`).
Source: audit r2 adversarial B2; mandate target 1a
Kind: C
Fidelity: exact (definitional, route (ii))
Hyps: (a) none -/
theorem foLiar_holds_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (foLiar T f s hs n) ↔
      (liaHistory (paperDP T)) (f n) (foLiar T f s hs n) < ((probeThreshold T f s n : ℚ) : ℝ) := by
  have hq : 0 ≤ probeThreshold T f s n :=
    ((paperMarketComputation T).expectQuoteAt_mem_Icc _ _ _).1
  have hp : 0 ≤ (paperMarketComputation T).quote (f.f n)
      (Encodable.encode (foLiar T f s hs n)) :=
    ((paperMarketComputation T).quote_mem_Icc _ _).1
  have hqe := (paperMarketComputation T).quote_exact (f.f n) (foLiar T f s hs n)
  change (liaHistory (paperDP T)) (f n) (foLiar T f s hs n) =
    (((paperMarketComputation T).quote (f.f n) (Encodable.encode (foLiar T f s hs n)) : ℚ) : ℝ)
    at hqe
  rw [foLiar_holds_iff_truth T f s hs n v hv]
  have key : selectorTruth (foQuotes T f s) eqRel (foQuotes_computable T f s hs) eqRel_primrec
      (Nat.pair n 1) ↔
      argmaxList [(paperMarketComputation T).quote (f.f n)
        (Encodable.encode (foLiar T f s hs n)), probeThreshold T f s n] = 1 := by
    simp only [selectorTruth, Nat.unpair_pair, eqRel, decide_eq_true_eq]
    exact Iff.rfl
  rw [key, argmaxList_pair_eq_one_iff hp hq, hqe]
  exact (Rat.cast_lt).symm

/-! ## The world-only probe menu -/

/-- **The world-only probe menu** `{1[χ'_n], const s}`.
Source: audit r2 adversarial B2
Kind: D
Fidelity: exact -/
def foMenu (hs : 0 ≤ s) : Menu 1 :=
  twoOptionMenu (fun n => literalIndicator (foLiar T f s hs n)) (fun _ => constLUV s)
    (literalIndicator_machineThresholdCodeSeq (foLiar_codes T f s hs)) (constLUV_codes hs)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- Option `0` is the liar's indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem foMenu_O_zero (hs : 0 ≤ s) :
    (foMenu T f s hs).O 0 = fun n => literalIndicator (foLiar T f s hs n) := rfl

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- Option `1` is the constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem foMenu_O_one (hs : 0 ≤ s) :
    (foMenu T f s hs).O 1 = fun _ => constLUV s := rfl

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The world-only probe menu is world-valued for `s ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foMenu_valued (hs : 0 ≤ s ∧ s ≤ 1) : (foMenu T f s hs.1).Valued (paperDP T) := by
  intro j
  fin_cases j
  · exact fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩
  · exact constLUV_valued hs (paperDP T)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quote of option `0` is the deferred price of the world-only liar, exactly.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foMenu_quote_zero (hs : 0 ≤ s) (n : ℕ) :
    (foMenu T f s hs).quote (selfExpert T f) 0 n =
      (liaHistory (paperDP T)) (f n) (foLiar T f s hs n) := by
  simp [Menu.quote, foMenu, twoOptionMenu, literalIndicator_expect]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quote of option `1` is the threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foMenu_quote_one (hs : 0 ≤ s) (n : ℕ) :
    (foMenu T f s hs).quote (selfExpert T f) 1 n = ((probeThreshold T f s n : ℚ) : ℝ) := by
  simp [Menu.quote, foMenu, twoOptionMenu, probeThreshold_cast]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- **The probe menu is syntactically world-only**: no threshold sentence carries a tag-`2` atom
(every atom of `χ'_n` carries tag `5`; the constant has no atoms).
Source: audit r2 adversarial B2; mandate target 12a
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem foMenu_worldOnly (hs : 0 ≤ s) : WorldOnly (foMenu T f s hs) := by
  intro j n r a ha
  have key0 : ∀ a ∈ sentenceAtomCodes ((literalIndicator (foLiar T f s hs n)).gt r),
      a.unpair.1 ≠ 2 := by
    intro a ha
    simp only [literalIndicator] at ha
    split_ifs at ha
    · simp at ha
    · exact foAtomZ_atom_tag _ a ha
    · simp at ha
  have key1 : ∀ a ∈ sentenceAtomCodes ((constLUV s).gt r), a.unpair.1 ≠ 2 := by
    intro a ha
    simp only [constLUV] at ha
    split_ifs at ha <;> simp at ha
  fin_cases j
  · exact key0 a ha
  · exact key1 a ha

/-- The argmax is `1` iff the world-only liar holds.
Source: none: infrastructure (as `probeMenu_argmax_iff`)
Kind: L
Fidelity: n/a -/
theorem foMenu_argmax_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (foMenu T f s hs).argmax (selfExpert T f) n = 1 ↔ v.Holds (foLiar T f s hs n) := by
  rw [foLiar_holds_iff T f s hs n v hv, Menu.argmax_two, foMenu_quote_zero, foMenu_quote_one]
  by_cases hc : ((probeThreshold T f s n : ℚ) : ℝ) ≤
      (liaHistory (paperDP T)) (f n) (foLiar T f s hs n)
  · rw [if_pos hc]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_lt.2 hc)⟩
  · rw [if_neg hc]
    exact ⟨fun _ => not_le.1 hc, fun _ => rfl⟩

/-- The argmax is `0` iff the world-only liar fails.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foMenu_argmax_zero_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (foMenu T f s hs).argmax (selfExpert T f) n = 0 ↔ ¬ v.Holds (foLiar T f s hs n) := by
  rw [← foMenu_argmax_iff T f s hs n v hv]
  generalize (foMenu T f s hs).argmax (selfExpert T f) n = a
  fin_cases a <;> simp

/-! ## The honest follower and its estimate -/

/-- **The honest follower** on the world-only menu: the select by `χ'_n` between the constant
(when `χ'_n`, i.e. argmax `1`) and the indicator (otherwise), as `probeFollower`.
Source: audit r2 adversarial B2; mandate target 1c
Kind: D
Fidelity: exact -/
def foFollower (hs : 0 ≤ s) : ℕ → LUV :=
  selectLUV (foLiar T f s hs) (fun _ => constLUV s) (fun n => literalIndicator (foLiar T f s hs n))

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The follower is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foFollower_codes (hs : 0 ≤ s) : LUV.MachineThresholdCodeSeq (foFollower T f s hs) :=
  selectLUV_codes (foLiar_codes T f s hs) (constLUV_codes hs)
    (literalIndicator_machineThresholdCodeSeq (foLiar_codes T f s hs))

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The follower's world value is `s · 1[χ'_n]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foFollower_valuesAt (hs : 0 ≤ s ∧ s ≤ 1) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (foFollower T f s hs.1 n) ((s : ℝ) * v.payout (foLiar T f s hs.1 n)) := by
  have h := selectLUV_valuesAt (foLiar T f s hs.1) (fun _ => constLUV s)
    (fun n => literalIndicator (foLiar T f s hs.1 n)) n v (constLUV_valuesAt hs v)
    (literalIndicator_valuesAt _ (paperDP T) hv)
  unfold PCWorld.payout foFollower
  by_cases hχ : v.Holds (foLiar T f s hs.1 n)
  · simpa [hχ, PCWorld.payout] using h
  · simpa [hχ, PCWorld.payout] using h

/-- **The follower follows the self-expert's argmax** on the world-only menu.
Source: audit r2 adversarial B2; mandate target 1c
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem foFollower_follows (hs : 0 ≤ s ∧ s ≤ 1) :
    Follows (paperDP T) (selfExpert T f) (foMenu T f s hs.1) (foFollower T f s hs.1) := by
  intro n v hv x hx
  have hsel := selectLUV_valuesAt (foLiar T f s hs.1) (fun _ => constLUV s)
    (fun n => literalIndicator (foLiar T f s hs.1 n)) n v (constLUV_valuesAt hs v)
    (literalIndicator_valuesAt _ (paperDP T) hv)
  show v.ValuesAt (selectLUV _ _ _ n) x
  by_cases hχ : v.Holds (foLiar T f s hs.1 n)
  · have ha := (foMenu_argmax_iff T f s hs.1 n v hv).2 hχ
    rw [ha, foMenu_O_one] at hx
    rw [hx.eq (constLUV_valuesAt hs v)]
    simpa [hχ] using hsel
  · have ha := (foMenu_argmax_zero_iff T f s hs.1 n v hv).2 hχ
    rw [ha, foMenu_O_zero] at hx
    rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
    simpa [hχ] using hsel

/-- **The expert's estimate of the follower**: `E*(S_n) ≈ₙ s · P_{f n}(χ'_n)`.
Source: audit r2 adversarial B2; mandate target 1c
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem foFollower_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (foFollower T f s hs.1 n).expect (liaHistory (paperDP T)) (f n)) ≈ₙ
      (fun n => (s : ℝ) * (liaHistory (paperDP T)) (f n) (foLiar T f s hs.1 n)) := by
  have h := expect_deferred_const_mul (P := liaHistory (paperDP T)) (DP := paperDP T) f hf s
    (X := fun n => literalIndicator (foLiar T f s hs.1 n))
    (literalIndicator_machineThresholdCodeSeq (foLiar_codes T f s hs.1))
    (foFollower_codes T f s hs.1)
    (fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩) (fun _ => 0)
    tendsto_const_nhds
    (fun n v hv x hx => ⟨(s : ℝ) * v.payout (foLiar T f s hs.1 n),
      foFollower_valuesAt T f s hs n v hv, by
        rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]; simp⟩) (paperDP_hworld T)
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [literalIndicator_expect]

/-- **The deferred pin** of the world-only liar: `P_{f n}(χ'_n) → s` (`Pin.lean`'s engine).
Source: audit r2 adversarial B2; vq-wiki-020; LI §4.11 (mandate target 1b)
Kind: C
Fidelity: exact (asymptotic)
Hyps: (a); `hf` -/
theorem foLiarPrice_tendsto_s (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (foLiar T f s hs0.le n)) atTop
      (𝓝 (s : ℝ)) :=
  liarPrice_tendsto T f hf (foLiar_codes T f s hs0.le)
    (fun n => ((probeThreshold T f s n : ℚ) : ℝ)) s hs0 hs1
    (probeThreshold_tendsto T f s ⟨hs0.le, hs1.le⟩) (foLiar_holds_iff T f s hs0.le)

/-! ## H3 fails on the world-only menu -/

/-- The self-endorsement instance fails on the world-only menu: `E*(S) → s² < s ≤ M_n − o(1)`.
Source: audit r2 adversarial B2; mandate target 1c (as `selfEndorseGE_instance_refuted`)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem fo_selfEndorseGE_instance_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ ((fun n => (selfExpert T f).estimate (foFollower T f s hs0.le) n) ≳ₙ
        (fun n => (foMenu T f s hs0.le).maxQuote (selfExpert T f) n)) := by
  intro h
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  have h' : (fun n => (selfExpert T f).estimate (foFollower T f s hs0.le) n) ≳ₙ
      (fun n => ((probeThreshold T f s n : ℚ) : ℝ)) :=
    asympGE_of_asympGE_of_le h (fun n => by
      rw [← foMenu_quote_one T f s hs.1 n]
      exact Menu.quote_le_maxQuote _ _ _ _)
  refine not_asympGE_of_tendsto_neg (c := (s : ℝ) * s - s) ?_ ?_ h'
  · have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    nlinarith
  · have hS := foFollower_estimate T f s hf hs
    unfold AsympEq at hS
    have hp := foLiarPrice_tendsto_s T f s hf hs0 hs1
    have hthr := probeThreshold_tendsto T f s hs
    have := (hS.add (hp.const_mul (s : ℝ))).sub hthr
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    simp only [Expert.self_estimate]
    try ring

/-- **H3 fails on the world-only menu for the self-expert's own package** (through the package's
characterization H3 ⟺ the self-endorsement instance, `condStableOn_iff_selfEndorseGE_instance_self`).
Source: audit r2 adversarial B2; mandate target 4c
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_foMenu_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ CondStableOn (foMenu T f s hs0.le) (selectionPackage_self T f (foMenu T f s hs0.le)) :=
  fun h => fo_selfEndorseGE_instance_refuted T f s hf hs0 hs1
    ((condStableOn_iff_selfEndorseGE_instance_self T f hf (foMenu T f s hs0.le)
      (foMenu_valued T f s ⟨hs0.le, hs1.le⟩) (foFollower_codes T f s hs0.le)
      (foFollower_follows T f s ⟨hs0.le, hs1.le⟩)).1 h)

/-- **`condStableOn_of_worldOnly` is false as stated** (the former OPEN of `Open.lean`, target
12a): the syntactic `WorldOnly` admits the liar rebuilt through `T`'s theorem lane, on which H3
fails — for every `T`, every strictly increasing deferral and every `s ∈ (0,1)`. The exact
negation of the former statement's universal closure.
Source: audit r2 adversarial B2; vq-wiki-017; lean-deference-073; mandate target 12a
Kind: C
Fidelity: exact (the negation of the OPEN's closed statement; refutation of its syntactic form)
Hyps: (a); `hf` -/
theorem condStableOn_of_worldOnly_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ ∀ (k : ℕ) (M : Menu k), WorldOnly M → CondStableOn M (selectionPackage_self T f M) :=
  fun h => condStableOn_foMenu_refuted T f s hf hs0 hs1 (h 1 _ (foMenu_worldOnly T f s hs0.le))

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`. -/
example : ¬ ∀ (k : ℕ) (M : Menu k), WorldOnly M →
    CondStableOn M (selectionPackage_self 𝗣𝗔 succDeferral M) :=
  condStableOn_of_worldOnly_refuted 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

/-! ## The second OPEN, `selfOpaque_perIndex`, falls on the same menu

At `j = 0`: `selI 0` is valued `1[sel = 0] = 1[∼χ'_n]` in every world, so
`E*(selI 0) ≈ₙ P_{f n}(∼χ'_n) → 1 − s`; `selQ 0` is valued within `1/(n+1)` of
`1[χ'_n]·1[∼χ'_n] = 0`, so `E*(selQ 0) → 0`; and `m^0_n = P_{f n}(χ'_n) → s`. The per-index gap
tends to `−(1 − s)s ≠ 0`. -/

/-- `P_{f n}(∼χ'_n) → 1 − s` (deferred coherence and the pin).
Source: audit r2 adversarial B2
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem foLiarNegPrice_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (∼ foLiar T f s hs0.le n)) atTop
      (𝓝 (1 - (s : ℝ))) := by
  have h1 := tendsto_of_asympEq_const (deferred_neg_coherence (P := liaHistory (paperDP T))
    (DP := paperDP T) f hf (foLiar_codes T f s hs0.le) (paperDP_hworld T))
  have h2 := foLiarPrice_tendsto_s T f s hf hs0 hs1
  have := h1.sub h2
  refine (tendsto_congr (fun n => ?_)).mp this
  ring

/-- `E*(selI 0) ≈ₙ P_{f n}(∼χ'_n)`: the quoted bit `1[sel = 0]` is `1[∼χ'_n]` in every world.
Source: audit r2 adversarial B2
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem fo_selI_zero_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selI T f (foMenu T f s hs.1) 0 n).expect (liaHistory (paperDP T)) (f n)) ≈ₙ
      (fun n => (liaHistory (paperDP T)) (f n) (∼ foLiar T f s hs.1 n)) := by
  have h := expect_deferred_const_mul (P := liaHistory (paperDP T)) (DP := paperDP T) f hf 1
    (X := fun n => literalIndicator (∼ foLiar T f s hs.1 n))
    (literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.neg (foLiar_codes T f s hs.1)))
    (selI_codes T f (foMenu T f s hs.1) 0)
    (fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩) (fun _ => 0)
    tendsto_const_nhds
    (fun n v hv x hx => ⟨_, selI_reflected T f (foMenu T f s hs.1) 0 n v hv, by
        rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
        unfold PCWorld.payout
        by_cases hχ : v.Holds (foLiar T f s hs.1 n)
        · have ha : (foMenu T f s hs.1).argmax (selfExpert T f) n = 1 :=
            (foMenu_argmax_iff T f s hs.1 n v hv).2 hχ
          rw [ha]
          simp [PCWorld.holds_neg, hχ]
        · have ha : (foMenu T f s hs.1).argmax (selfExpert T f) n = 0 :=
            (foMenu_argmax_zero_iff T f s hs.1 n v hv).2 hχ
          rw [ha]
          simp [PCWorld.holds_neg, hχ]⟩) (paperDP_hworld T)
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [literalIndicator_expect]

/-- `E*(selQ 0) ≈ₙ 0`: the product `x_0 · 1[sel = 0] = 1[χ'_n]·1[∼χ'_n]` is `0` in every world.
Source: audit r2 adversarial B2
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem fo_selQ_zero_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (selQ T f (foMenu T f s hs.1) 0 n).expect (liaHistory (paperDP T)) (f n)) ≈ₙ
      (fun _ => ((0 : ℚ) : ℝ)) := by
  refine expect_deferred_const (P := liaHistory (paperDP T)) (DP := paperDP T) f hf 0
    (selQ_codes T f (foMenu T f s hs.1) 0) (fun n => 1 / ((n : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n v hv => ?_) (paperDP_hworld T)
  have hx : v.ValuesAt ((foMenu T f s hs.1).O 0 n) (v.payout (foLiar T f s hs.1 n)) := by
    rw [foMenu_O_zero]
    exact literalIndicator_valuesAt _ (paperDP T) hv
  obtain ⟨z, hz, hb⟩ := selQ_reflected T f (foMenu T f s hs.1) 0 n v hv _ hx
  refine ⟨z, hz, ?_⟩
  have key : v.payout (foLiar T f s hs.1 n) *
      (if (foMenu T f s hs.1).argmax (selfExpert T f) n = 0 then (1 : ℝ) else 0) = 0 := by
    unfold PCWorld.payout
    by_cases hχ : v.Holds (foLiar T f s hs.1 n)
    · have ha : (foMenu T f s hs.1).argmax (selfExpert T f) n = 1 :=
        (foMenu_argmax_iff T f s hs.1 n v hv).2 hχ
      rw [ha]
      simp
    · simp [hχ]
  calc |z - ((0 : ℚ) : ℝ)| = |z - v.payout (foLiar T f s hs.1 n) *
        (if (foMenu T f s hs.1).argmax (selfExpert T f) n = 0 then (1 : ℝ) else 0)| := by
          rw [key]; simp
    _ ≤ 1 / ((n : ℝ) + 1) := hb

/-- **The per-index gap at `j = 0` tends to `−(1 − s)s`** on the world-only menu.
Source: audit r2 adversarial B2; 2-026 (mandate target 12b)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem fo_perIndex_gap_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (selQ T f (foMenu T f s hs0.le) 0 n).expect (liaHistory (paperDP T)) (f n) -
      (selI T f (foMenu T f s hs0.le) 0 n).expect (liaHistory (paperDP T)) (f n) *
        (foMenu T f s hs0.le).quote (selfExpert T f) 0 n) atTop
      (𝓝 (-((1 - (s : ℝ)) * s))) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  have hQ := tendsto_of_asympEq_const (fo_selQ_zero_estimate T f s hf hs)
  have hIdiff := fo_selI_zero_estimate T f s hf hs
  unfold AsympEq at hIdiff
  have hneg := foLiarNegPrice_tendsto T f s hf hs0 hs1
  have hI : Tendsto (fun n => (selI T f (foMenu T f s hs0.le) 0 n).expect (liaHistory (paperDP T))
      (f n)) atTop (𝓝 (1 - (s : ℝ))) := by
    have := hIdiff.add hneg
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    ring
  have hm : Tendsto (fun n => (foMenu T f s hs0.le).quote (selfExpert T f) 0 n) atTop
      (𝓝 (s : ℝ)) :=
    (tendsto_congr (fun n => foMenu_quote_zero T f s hs0.le n)).mpr
      (foLiarPrice_tendsto_s T f s hf hs0 hs1)
  have := hQ.sub (hI.mul hm)
  refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
  first
    | rfl
    | (rw [foMenu_quote_zero, literalIndicator_expect])
    | simp [Menu.quote, Expert.self_estimate]

/-- **`selfOpaque_perIndex` is false as stated** (the former OPEN of `Open.lean`, target 12b;
2-026's self-opaque route in its syntactic form): on the world-only liar menu the per-index gap
at `j = 0` tends to `−(1 − s)s ≠ 0`. The exact negation of the former statement's universal
closure.
Source: audit r2 adversarial B2; 2-026; mandate target 12b
Kind: C
Fidelity: exact (the negation of the OPEN's closed statement; refutation of its syntactic form)
Hyps: (a); `hf` -/
theorem selfOpaque_perIndex_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ ∀ (k : ℕ) (M : Menu k), WorldOnly M → ∀ j : Fin (k + 1),
      (fun n => (selfExpert T f).estimate (selQ T f M j) n -
        (selfExpert T f).estimate (selI T f M j) n * M.quote (selfExpert T f) j n) ≈ₙ
        (fun _ => (0 : ℝ)) := by
  intro h
  have hgap := h 1 (foMenu T f s hs0.le) (foMenu_worldOnly T f s hs0.le) 0
  simp only [Expert.self_estimate] at hgap
  have h0 := tendsto_of_asympEq_const hgap
  have hlim := fo_perIndex_gap_tendsto T f s hf hs0 hs1
  have heq := tendsto_nhds_unique h0 hlim
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
  nlinarith

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`. -/
example : ¬ ∀ (k : ℕ) (M : Menu k), WorldOnly M → ∀ j : Fin (k + 1),
      (fun n => (selfExpert 𝗣𝗔 succDeferral).estimate (selQ 𝗣𝗔 succDeferral M j) n -
        (selfExpert 𝗣𝗔 succDeferral).estimate (selI 𝗣𝗔 succDeferral M j) n *
          M.quote (selfExpert 𝗣𝗔 succDeferral) j n) ≈ₙ (fun _ => (0 : ℝ)) :=
  selfOpaque_perIndex_refuted 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

end

end Cleanroom.Deference.DefArgmaxValue
