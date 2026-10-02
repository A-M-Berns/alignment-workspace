import Cleanroom.Bli.BliFound

/-!
# `bli-found` · audit round 3 · adversarial lens · probes

**Not imported by the library.** Written 2026-09-30 by the round-3 adversarial auditor against
the package as committed after repair round 2 (commit `abe61343`, fourteen modules, 897
declarations, gate PASS). Each section is the evidence for one item of
`bli-found-audit-r3-adversarial.md`.

* **P1 (blocking issue B1)** — the repaired direction claim on `Size.atomDay`/`Size.Sminus`
  ("on every atom of a FAF-allocated family `atomDay a ≥` the day it quotes, so `Sminus`
  under-approximates the prose scope") fails on **tag `2` itself**, the family the package says it
  reads "`≥` the day". `atomDay` reads the packed *input* of a quotation claim `⟨code, input⟩`; the
  day of a FAF `BooleanQuoteCode` need not be a component of its input — it can live in the
  program. `laterDayQuote T` is FAF's `BooleanQuoteCode.ofComputable` of the computable predicate
  `i ↦ "on day i + 2 the market's quote of the sentence with code i rounds (halfRound) to 1"`. Its
  literal at input `i` is a tag-`2` atom with `atomDay = i` (`atomDay_laterDaySentence`); in every
  completed-theory world of `paperDP T` it holds iff the day-`(i+2)` rounded quote of `i` is `1`
  (`laterDaySentence_reflected`) — i.e. iff the package's **own** cell literal
  `cellSentence T halfRound _ (i+2) i 1` holds (`laterDaySentence_iff_cellSentence`); `paperDP T`
  decides it (`laterDaySentence_decided`). For every `i` beyond a fixed threshold the literal is
  small on day `i + 1` (`laterDaySentence_small`), hence **lies in `Sminus (i+1) (i+1)`** — E2x's
  scope of faith at day `m = i + 1` — while the semantically identical `cellSentence` does not
  (`sminus_scope_is_packing_dependent`). So `Sminus m m` contains a decided claim about the
  market state of day `m + 1`, strictly later than `m`, which the prose scope excludes under
  every reading (the Notion's "no info about market states later than `m`", the program's
  "quoting no market day `≥ m`"), and membership in the scope of faith depends on how a quote
  code packs its input, not on what it says.
* **P2** — the day reader is blind to arithmetic content: every tag-`5` first-order prime
  `paperPrimeSentence b φ` reads day `0` (`atomDay_paperPrimeSentence`) and lies in `Sminus n m`
  iff it is small on day `n` (`paperPrimeSentence_mem_Sminus_iff`), whatever `φ` says. What such a
  `φ` can say about the market on later days is a fact about `𝗜𝚺₁`'s expressivity that no
  propositional day reader can see; recorded in the audit as the reason the semantic prose scope
  is not syntactically renderable.
* **P3** — `Grid.fixedStates_decided` is not vacuous in the world: a completed-theory world of
  `paperDP 𝗜𝚺₁` exists and holds one of the four fixed tables (`fixedStates_decided_nonvacuous`).
* **P4** — `Grid.b2StateSystem_roundsOf` is instantiable *now*, classically: the index list
  `(smallSet m).toList.map encode` covers `smallSet m` (`fullIndex_covers`), so the `RoundsOf`
  tie holds for the one-state B2 system over it (`b2_roundsOf_instance`). The package's "no
  instance … waits on a computable enumeration of `smallSet` (stretch S1)" is true only of a
  *computable* index; the theorem does not ask for one.
-/

namespace Cleanroom.Bli.BliFound.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## P1. A quotation claim whose day is computed from its input -/

section DayInTheProgram

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁]

/-- "On day `i + 2`, the market's quote of the sentence with code `i` rounds (by `halfRound`) to
`1`": a predicate of the single input `i` whose *day* `i + 2` is computed by the program, not
packed as a component of the input. Compare the package's `cellTruth T halfRound ⟨m, ⟨c, r⟩⟩`,
which packs the day first. -/
def laterDayTruth (i : ℕ) : Prop :=
  halfRound (i + 2) (marketValue T (Nat.pair (i + 2) i)) = 1

/-- The day function `i ↦ i + 2` is computable. -/
lemma dayOf_computable : Computable fun i : ℕ => i + 2 :=
  (Primrec.nat_add.comp Primrec.id (Primrec.const 2)).to_comp

set_option maxHeartbeats 400000 in
/-- `laterDayTruth T` is a computable predicate: it is the package's own `cellTruth T halfRound`
(a `ComputablePred`, `cellTruth_computable`) precomposed with the computable input map
`i ↦ ⟨i + 2, ⟨i, 1⟩⟩` — the day is computed from the input rather than read off it. -/
theorem laterDayTruth_computable : ComputablePred (laterDayTruth T) := by
  obtain ⟨f, hf, hfeq⟩ :=
    ComputablePred.computable_iff.1 (cellTruth_computable T halfRound halfRound_computable)
  rw [ComputablePred.computable_iff]
  have hg : Computable fun i : ℕ => Nat.pair (i + 2) (Nat.pair i 1) :=
    Primrec₂.natPair.to_comp.comp dayOf_computable
      (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
  refine ⟨fun i => f (Nat.pair (i + 2) (Nat.pair i 1)), hf.comp hg, ?_⟩
  funext i
  have h := congrFun hfeq (Nat.pair (i + 2) (Nat.pair i 1))
  simp only [cellTruth, Nat.unpair_pair] at h
  exact h

variable [𝗥₀ ⪯ T]

/-- FAF's Boolean quote code for `laterDayTruth T` (`BooleanQuoteCode.ofComputable`, exactly as
the package builds `cellQuote`). -/
noncomputable def laterDayQuote : BooleanQuoteCode T (laterDayTruth T) :=
  BooleanQuoteCode.ofComputable (laterDayTruth_computable T)

/-- The tag-`2` quotation literal of `laterDayQuote T` at input `i`: "the day-`(i+2)` rounded
quote of `i` is `1`", with the day nowhere in the atom's input. -/
noncomputable def laterDaySentence (i : ℕ) : Sentence := (laterDayQuote T).sentence i

/-- The literal, in closed shell form: a single tag-`2` atom whose `input` is `i`. -/
lemma laterDaySentence_eq (i : ℕ) :
    laterDaySentence T i = Formula.atom (Nat.pair 2 (Nat.pair (Encodable.encode universalQuotePos)
      (Nat.pair (Encodable.encode universalQuoteNeg) (Nat.pair (laterDayQuote T).code i)))) := rfl

/-- **Reflection**: in every completed-theory world of `paperDP T` the literal holds iff the
day-`(i+2)` rounded quote of the sentence with code `i` is `1` — a claim about the day-`(i+2)`
market state, decided through FAF's `BooleanQuoteCode.reflected` at `paperQuotationPresentation`. -/
theorem laterDaySentence_reflected (i : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (laterDaySentence T i) ↔ laterDayTruth T i :=
  (laterDayQuote T).reflected (paperQuotationPresentation T) i v hv

/-- The literal or its negation enters a stage of `paperDP T` (event tags `4`/`5`). -/
theorem laterDaySentence_decided (i : ℕ) :
    (∃ k, laterDaySentence T i ∈ (paperDP T).D k) ∨
      (∃ k, (∼laterDaySentence T i) ∈ (paperDP T).D k) := by
  by_cases h : laterDayTruth T i
  · exact Or.inl ((paperQuotationPresentation T).quote_positive_enters _ _
      ((laterDayQuote T).pos_complete i h))
  · exact Or.inr ((paperQuotationPresentation T).quote_negative_refutes _ _
      ((laterDayQuote T).neg_complete i h))

/-- **The same claim as the package's own cell literal.** In every completed-theory world,
`laterDaySentence T i` holds iff `cellSentence T halfRound _ (i + 2) i 1` holds: two tag-`2`
atoms that quote the same fact about the same day, packed differently. -/
theorem laterDaySentence_iff_cellSentence (i : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (laterDaySentence T i) ↔
      v.Holds (cellSentence T halfRound halfRound_computable (i + 2) i 1) :=
  (laterDaySentence_reflected T i v hv).trans
    (cellSentence_reflected T halfRound halfRound_computable (i + 2) i 1 v hv).symm

/-- `atomDay` reads `i` off the literal: the packed input, which here is *not* the day. -/
lemma atomDay_laterDaySentence (i : ℕ) :
    ∀ a ∈ sentenceAtomCodes (laterDaySentence T i), atomDay a = i := by
  intro a ha
  rw [laterDaySentence_eq, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  have := atomDay_quotationClaimCode (Nat.pair (laterDayQuote T).code i)
  simp only [quotationClaimCode] at this
  rw [this, Nat.unpair_pair]

/-- `8 i + 11 ≤ 2 ^ (2 ^ (i + 1))` from `i = 2` on. -/
lemma eight_mul_add_eleven_le_sizeBound : ∀ i, 2 ≤ i → 8 * i + 11 ≤ sizeBound (i + 1) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => norm_num [sizeBound]
  | succ k hk ih =>
      rw [sizeBound_succ]
      have h4 : 4 ≤ sizeBound (k + 1) := four_le_sizeBound (by omega)
      have hmul := Nat.mul_le_mul h4 ih
      omega

/-- **Smallness.** Once `i` dominates the three fixed constants of the atom shell (the codes of
the two universal quote schemas and of `laterDayQuote T`'s decider) and `i ≥ 2`, the literal is
small on day `i + 1`: its index is below `(i + 1)^16`, so it has at most `8 (i + 1) + 2` base-4
digits, and `8 i + 11 ≤ 2^(2^(i+1))`. -/
theorem laterDaySentence_small {i : ℕ} (hP : Encodable.encode universalQuotePos ≤ i)
    (hN : Encodable.encode universalQuoteNeg ≤ i) (hc : (laterDayQuote T).code ≤ i)
    (h2 : 2 ≤ i) : SmallOn (i + 1) (laterDaySentence T i) := by
  have hB : ∀ a b k : ℕ, a ≤ b → b < k → Nat.pair a b < k ^ 2 := by
    intro a b k hab hbk
    have := Nat.pair_lt_max_add_one_sq a b
    rw [max_eq_right hab] at this
    calc Nat.pair a b < (b + 1) ^ 2 := this
      _ ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold SmallOn
  rw [laterDaySentence_eq, tokenSize_atom]
  generalize hcg : (laterDayQuote T).code = c at hc ⊢
  generalize hPg : Encodable.encode universalQuotePos = P at hP ⊢
  generalize hNg : Encodable.encode universalQuoteNeg = N at hN ⊢
  have h1 : Nat.pair c i < (i + 1) ^ 2 := hB c i (i + 1) hc (by omega)
  have h2' : Nat.pair N (Nat.pair c i) < ((i + 1) ^ 2) ^ 2 :=
    hB N _ _ (le_trans hN (Nat.right_le_pair c i)) h1
  have h3 : Nat.pair P (Nat.pair N (Nat.pair c i)) < (((i + 1) ^ 2) ^ 2) ^ 2 :=
    hB P _ _ (le_trans hP (le_trans (Nat.right_le_pair c i) (Nat.right_le_pair N _))) h2'
  have h4 : Nat.pair 2 (Nat.pair P (Nat.pair N (Nat.pair c i))) <
      ((((i + 1) ^ 2) ^ 2) ^ 2) ^ 2 :=
    hB 2 _ _ (le_trans h2 (le_trans (Nat.right_le_pair c i)
      (le_trans (Nat.right_le_pair N _) (Nat.right_le_pair P _)))) h3
  have h16 : ((((i + 1) ^ 2) ^ 2) ^ 2) ^ 2 = (i + 1) ^ 16 := by ring
  have hpow : (i + 1) ^ 16 ≤ 2 ^ (16 * (i + 1)) := by
    calc (i + 1) ^ 16 ≤ (2 ^ (i + 1)) ^ 16 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 16
      _ = 2 ^ (16 * (i + 1)) := by rw [← pow_mul]; ring_nf
  have h4L : (4 : ℕ) ^ (8 * (i + 1) + 2) = 16 * 2 ^ (16 * (i + 1)) := by
    have h4eq : (4 : ℕ) ^ (8 * (i + 1) + 2) = (2 ^ 2) ^ (8 * (i + 1) + 2) := by norm_num
    rw [h4eq, ← pow_mul]
    ring
  have hlt : Nat.pair 2 (Nat.pair P (Nat.pair N (Nat.pair c i))) + 5 < 4 ^ (8 * (i + 1) + 2) := by
    rw [h4L]
    have hpos : 1 ≤ 2 ^ (16 * (i + 1)) := Nat.one_le_two_pow
    omega
  have hdig := length_natDigits4_le_of_lt_pow hlt
  have hsb := eight_mul_add_eleven_le_sizeBound i h2
  omega

/-- **The literal lies in `Sminus (i+1) (i+1)` for every large `i`**: small on day `i + 1` and
`atomDay = i < i + 1`. -/
theorem laterDaySentence_mem_Sminus_eventually :
    ∃ M, ∀ i ≥ M, laterDaySentence T i ∈ Sminus (i + 1) (i + 1) := by
  refine ⟨max (max (Encodable.encode universalQuotePos) (Encodable.encode universalQuoteNeg))
    (max (laterDayQuote T).code 2), fun i hi => ?_⟩
  have hP : Encodable.encode universalQuotePos ≤ i :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hN : Encodable.encode universalQuoteNeg ≤ i :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have hc : (laterDayQuote T).code ≤ i :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hi
  have h2 : 2 ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hi
  rw [mem_Sminus]
  exact ⟨laterDaySentence_small T hP hN hc h2,
    fun a ha => by rw [atomDay_laterDaySentence T i a ha]; omega⟩

/-- **Headline of P1.** For every large `i`, with `m := i + 1`: the day-`m` scope of faith
`Sminus m m` contains `laterDaySentence T i` and excludes
`cellSentence T halfRound _ (m + 1) i 1`, although the two literals hold in exactly the same
completed-theory worlds of `paperDP T` — both say "the day-`(m+1)` rounded quote of `i` is `1`",
a claim about a market state strictly later than `m`. Membership in the scope depends on the
packing of the quote code's input, not on the day the literal quotes; the ledger's "`atomDay a ≥`
the day quoted, on every FAF-allocated family" is false on tag `2`. -/
theorem sminus_scope_is_packing_dependent :
    ∃ M, ∀ i ≥ M,
      laterDaySentence T i ∈ Sminus (i + 1) (i + 1) ∧
      cellSentence T halfRound halfRound_computable (i + 2) i 1 ∉ Sminus (i + 1) (i + 1) ∧
      ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
        (v.Holds (laterDaySentence T i) ↔
          v.Holds (cellSentence T halfRound halfRound_computable (i + 2) i 1)) := by
  obtain ⟨M, hM⟩ := laterDaySentence_mem_Sminus_eventually T
  refine ⟨M, fun i hi => ⟨hM i hi, ?_, fun v hv => laterDaySentence_iff_cellSentence T i v hv⟩⟩
  intro h
  have h1 := cellSentence_mem_Sminus_imp T halfRound halfRound_computable h
  have h2 := Nat.left_le_pair (i + 2) (Nat.pair i 1)
  omega

end DayInTheProgram

/-! ## P2. The day reader is blind to first-order primes -/

/-- Every tag-`5` prime reads day `0`, whatever arithmetic sentence it carries. -/
lemma atomDay_paperPrimeSentence (b : Bool) (φ : LO.FirstOrder.ArithmeticProposition) :
    ∀ a ∈ sentenceAtomCodes (paperPrimeSentence b φ), atomDay a = 0 := by
  intro a ha
  simp only [paperPrimeSentence, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  simp [atomDay, atomDayBase, paperPrimeCode, paperPrimeTag, cleanroomBaseTag]

/-- A first-order prime lies in `Sminus n m` (for `m ≥ 1`) iff it is small on day `n`: the
scope of faith never excludes an arithmetic sentence on account of what it says. -/
theorem paperPrimeSentence_mem_Sminus_iff (b : Bool) (φ : LO.FirstOrder.ArithmeticProposition)
    (n m : ℕ) (hm : 0 < m) :
    paperPrimeSentence b φ ∈ Sminus n m ↔ SmallOn n (paperPrimeSentence b φ) := by
  rw [mem_Sminus]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun a ha => by rw [atomDay_paperPrimeSentence b φ a ha]; exact hm⟩

/-! ## P3. `fixedStates_decided` is not vacuous in the world -/

/-- A completed-theory world of `paperDP 𝗜𝚺₁` exists (`paperDP_nonvacuous`) and holds one of the
four fixed tables — the actual one. -/
theorem fixedStates_decided_nonvacuous (m : ℕ) :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) ∧
      ∃ q ∈ fixedStates m, v.Holds (stateSentence 𝗜𝚺₁ halfRound halfRound_computable m q) := by
  obtain ⟨v, hv⟩ := paperDP_nonvacuous 𝗜𝚺₁
  exact ⟨v, hv, actualCode 𝗜𝚺₁ halfRound witnessIndex m, actualCode_mem_fixedStates m,
    actualCode_holds m v hv⟩

/-! ## P4. `b2StateSystem_roundsOf` has a classical instance today -/

/-- The index list of all day-`m` small sentences (classical: `Finset.toList`). -/
noncomputable def fullIndex (m : ℕ) : List ℕ := (smallSet m).toList.map Encodable.encode

/-- It covers `smallSet m` — the hypothesis `b2StateSystem_roundsOf` asks for. -/
lemma fullIndex_covers : ∀ m, ∀ φ ∈ smallSet m, Encodable.encode φ ∈ fullIndex m :=
  fun _ φ hφ => List.mem_map.2 ⟨φ, Finset.mem_toList.2 hφ, rfl⟩

/-- The one-state B2 candidate set over the full index: just the actual rounded table. -/
noncomputable def fullStates (m : ℕ) : Finset ℕ := {actualCode 𝗜𝚺₁ halfRound fullIndex m}

lemma actualCode_mem_fullStates (m : ℕ) : actualCode 𝗜𝚺₁ halfRound fullIndex m ∈ fullStates m := by
  unfold fullStates
  exact Finset.mem_singleton_self _

/-- **`RoundsOf` for a B2 system over the paper market, instantiated**: the theorem needs only
coverage of `smallSet m`, which a noncomputable index supplies at once. -/
theorem b2_roundsOf_instance :
    RoundsOf (b2StateSystem 𝗜𝚺₁ halfRound fullIndex fullStates actualCode_mem_fullStates witnessRep)
      (liaHistory (paperDP 𝗜𝚺₁))
      (fun m x => ((witnessRep m (halfRound m (ratOfReal x)) : ℚ) : ℝ)) :=
  b2StateSystem_roundsOf 𝗜𝚺₁ halfRound fullIndex fullStates actualCode_mem_fullStates witnessRep
    fullIndex_covers

end Cleanroom.Bli.BliFound.AuditR3
