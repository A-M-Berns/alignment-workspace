import Cleanroom.Bli.BliFound.StateSentence
import LogicalInduction.Construction.SemanticExtension.Quote

/-!
# `bli-found` — audit round 3, lens `fidelity`: probe (part 2, the `rfl` bridge and the alias
of the package's own quote)

Not imported by the library. Companion of `Fidelity.lean` (part 1); heavy imports
(`StateSentence` for `marketQuoteCode`/`quoteLuv`, FAF's `SemanticExtension.Quote` for
`semanticQuoteLeaf_reflected`), so it may be slow inside the memory slice. It (i) proves by
`rfl` that part 1's literal `handle`/`handleCode`/`quoteSchema` are FAF's
`semanticPrimeSentence`/`semanticPrimeCode`/`semanticQuoteSchema`, that `handle (quoteSchema
code) input` is `semanticQuoteLeaf code input`, and that `handle schema ⟨n, ⌜r⌝⟩` is
`(semanticHandleLUVSeq schema n).gt r`; and (ii) ties the alias to the package's own market
quote code: `marketQuoteAlias T m φ r` holds iff the package's day-`m` threshold literal
`(quoteLuv T m φ).gt r` holds in every completed world of `semanticQuoteDP`
(`marketQuoteAlias_reflected`), lies in `Sminus k m` for some `k` (and, by part 1's
`quoteAlias_mem_Sminus_self` at `c := (marketQuoteCode T).code`, in `Sminus m m` for every
large `m`), while the literal lies in no `Sminus n m` (`quoteLuv_gt_notMem_Sminus`).
-/

namespace AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- Part 1's literal handle index (restated; the probes are not modules of the build). -/
def handleCode (schema input : ℕ) : ℕ := Nat.pair 4 (Nat.pair schema input)

/-- Part 1's literal handle. -/
def handle (schema input : ℕ) : Sentence := Formula.atom (handleCode schema input)

/-- Part 1's literal quotation-alias selector. -/
def quoteSchema (code : ℕ) : ℕ := Nat.pair 2 code

/-! ## The `rfl` bridge to FAF's names -/

lemma handleCode_eq (schema input : ℕ) : handleCode schema input = semanticPrimeCode schema input :=
  rfl

lemma handle_eq (schema input : ℕ) : handle schema input = semanticPrimeSentence schema input :=
  rfl

lemma quoteSchema_eq (code : ℕ) : quoteSchema code = semanticQuoteSchema code := rfl

lemma handle_quoteSchema_eq_semanticQuoteLeaf (code input : ℕ) :
    handle (quoteSchema code) input = semanticQuoteLeaf code input := rfl

lemma handleLUV_gt_eq (schema n : ℕ) (r : ℚ) :
    handle schema (Nat.pair n (Encodable.encode r)) = (semanticHandleLUVSeq schema n).gt r := rfl

/-! ## The alias of the package's own quote -/

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]

/-- The tag-`4` alias of the package's own day-`m` threshold literal `⌜𝑸_m(φ) > r⌝`. -/
noncomputable def marketQuoteAlias (m : ℕ) (φ : Sentence) (r : ℚ) : Sentence :=
  semanticQuoteLeaf (marketQuoteCode T).code
    (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode r))

/-- In every completed world of FAF's `semanticQuoteDP`, the alias holds iff the package's own
threshold literal holds: it *is* a day-`m` market quote under another atom. -/
lemma marketQuoteAlias_reflected {v : PCWorld} (hv : v.ConsistentWithTheory semanticQuoteDP)
    (m : ℕ) (φ : Sentence) (r : ℚ) :
    v.Holds (marketQuoteAlias T m φ r) ↔ v.Holds ((quoteLuv T m φ).gt r) := by
  unfold marketQuoteAlias
  rw [semanticQuoteLeaf_reflected hv]
  simp [quoteLuv, RationalQuoteCode.luv, arithmeticThresholdLUV]

/-- The threshold literal itself lies in no `Sminus n m` (the package's tag-`2` reading:
`atomDay` is the packed input, `≥ m`). -/
lemma quoteLuv_gt_notMem_Sminus (m n : ℕ) (φ : Sentence) (r : ℚ) :
    (quoteLuv T m φ).gt r ∉ Sminus n m := by
  intro h
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (marketQuoteCode T).code
      (Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode r))))
    (by simp [quoteLuv, RationalQuoteCode.luv, arithmeticThresholdLUV, quoteAtom,
      quotationClaimSentence])
  rw [atomDay_quotationClaimCode, Nat.unpair_pair] at this
  have h1 : m ≤ Nat.pair m (Encodable.encode φ) := Nat.left_le_pair _ _
  have h2 : Nat.pair m (Encodable.encode φ) ≤
      Nat.pair (Nat.pair m (Encodable.encode φ)) (Encodable.encode r) := Nat.left_le_pair _ _
  omega

/-- The alias reads day `0` (it is a tag-`4` handle) and so lies in `Sminus k m` for some `k`,
for every `m ≥ 1` — whereas the literal it aliases lies in none. -/
lemma marketQuoteAlias_mem_Sminus_exists (m : ℕ) (hm : 0 < m) (φ : Sentence) (r : ℚ) :
    (∃ k, marketQuoteAlias T m φ r ∈ Sminus k m) ∧
      ∀ n, (quoteLuv T m φ).gt r ∉ Sminus n m := by
  refine ⟨⟨tokenSize (marketQuoteAlias T m φ r), ?_⟩, fun n => quoteLuv_gt_notMem_Sminus T m n φ r⟩
  rw [mem_Sminus]
  refine ⟨smallOn_tokenSize _, fun a ha => ?_⟩
  simp only [marketQuoteAlias, semanticQuoteLeaf, semanticPrimeSentence, sentenceAtomCodes_atom,
    Finset.mem_singleton] at ha
  subst ha
  simp [atomDay, atomDayBase, semanticPrimeCode, semanticPrimeTag, cleanroomBaseTag, hm]

end AuditR3
