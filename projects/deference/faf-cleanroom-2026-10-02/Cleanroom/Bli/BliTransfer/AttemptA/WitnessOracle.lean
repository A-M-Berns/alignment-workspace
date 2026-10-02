import Cleanroom.Bli.BliTransfer.AttemptA.Certificate
import LogicalInduction.Framework.Machine.DigitArithFP

/-!
# `bli-transfer` (attempt A) · WitnessOracle: the first `SpliceCertificate` oracle (T1.5, oracle half)

The polynomial-time run-level oracle for the N+ witness map of `WitnessLia.lean`: on day `0`,
every atom of the run's family `7` (`freshAtom 7 payload = atom (Nat.pair (cleanroomBaseTag + 7) payload)`,
tag `wTag = 16`) is re-priced to `1/2`. Every atom is large on day `0` (size `≥ 3 > sizeBound 0 = 2`),
so the oracle needs no size comparison — only the family test on the buffered run, under **both**
spellings `parseRpn` accepts for an atom: the canonical run `[t]` with `t = a + 5`, and the Gödel
escape `[1, c]` with `c = ⌜atom a⌝ = Nat.pair 1 a + 1` (`encode_atom`). Structured escapes
`[1, 0, …]` denote tag-`5` atoms and never fire, so the oracle returns nothing on them (and on every
run of three or more tokens).

* `familyRun` — the token-level test (a function of the buffered run's tokens), and `wExprRun`,
  the run-level lookup: on day `0` and a family run, the raw body `[1, ⌜1/2⌝]` of `const (1/2)`.
* The oracle: a block fold over the buffered run's bits recording the block count (capped at
  `3`, in unary), whether the first block is the numeral `1`, and the last block's bits
  (`wStepOf`; `runFold_cli_mem_FP`), then the value tests through FAF's `DigitFP` word
  arithmetic — `subW`, `predW`, `unpairFstW`, `unpairSndW`, `leW` — and the fixed-numeral day
  test `NumEqBits 0`.
* `wOracle : SpliceOracle wExprRun`: `FP` membership, block-well-formed output, a constant output
  bound, and the spec on every well-formed day block and every buffered word (its complete blocks
  are exactly the tokens `decodeBits` produces, `undigitize_eq_blockSplit`).

This is the shape `bli-assemble`'s oracle for the tent kernel's state atoms extends (a family
test on the atom's payload, and for days `≥ 1` a size comparison against `2^{2^k}`, which day
`0` does not need).

Sources: mandate T1.5; FAF `Framework/Machine/DigitArithFP.lean`, `TokenFold.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.DigitFP

/-! ## The family and the run-level lookup -/

/-- The witness family's tag: family `7` of the run's allocator.
Source: `Cleanroom.Bli.BliFound.Tags` (family registry); mandate T1.5
Kind: D
Fidelity: n/a -/
def wTag : ℕ := cleanroomBaseTag + 7

/-- Whether a token list spells a family-`wTag` atom: the canonical run `[t]` with
`(t - 5).unpair.1 = wTag`, or the Gödel escape `[1, c]` with `c - 1 = Nat.pair 1 a` and
`a.unpair.1 = wTag`.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def familyRun : List ℕ → Bool
  | [t] => decide (5 ≤ t ∧ (t - 5).unpair.1 = wTag)
  | [t, c] => decide (t = 1 ∧ 1 ≤ c ∧ (c - 1).unpair.1 = 1 ∧ (c - 1).unpair.2.unpair.1 = wTag)
  | _ => false

/-- The raw body of `const (1/2)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wBody : List ℕ := [1, Encodable.encode (1 / 2 : ℚ)]

/-- The run-level lookup: on day `0`, a family run gets the body `wBody`.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def wExprRun (b : List ℕ) (D : ℕ) : Option (List ℕ) :=
  if D = 0 ∧ familyRun b = true then some wBody else none

/-- The oracle's output word when it fires.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wOut : List Bool := tokBits (wBody ++ [8])

/-! ## The block fold: count, first-is-one flag, last block -/

/-- The block count of the client state (unary, capped at `3`). -/
def wCnt (s : List Bool) : List Bool := fstBlock (fstBlock s)
/-- Whether the first block was the numeral `1` (`[true]`/`[]`). -/
def wFlag (s : List Bool) : List Bool := sndBlock (fstBlock s)
/-- The last block's bits. -/
def wPay (s : List Bool) : List Bool := sndBlock s

/-- One block: bump the count (capped), set the flag on the first block, keep the block.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wStepOf (cli tok : List Bool) : List Bool :=
  pair (pair ((wCnt cli ++ [true]).take 3)
    (if (wCnt cli).length = 0 then (if NumEqBits 1 tok then [true] else [])
      else (wFlag cli).take 1)) tok

/-- The word-level step on `pair W (pair cli tok)`. -/
def wStepW (v : List Bool) : List Bool := wStepOf (midBlock v) (lastBlock v)

/-- The block-level step. -/
def wStepR (cli : List Bool) (cur : List ℕ) : List Bool := wStepOf cli (digitsToBits cur)

/-- The initial client state. -/
def wInit : List Bool := pair (pair [] []) []

@[simp] lemma wCnt_wStepOf (cli tok : List Bool) :
    wCnt (wStepOf cli tok) = (wCnt cli ++ [true]).take 3 := by simp [wCnt, wStepOf]

@[simp] lemma wFlag_wStepOf (cli tok : List Bool) :
    wFlag (wStepOf cli tok) = (if (wCnt cli).length = 0 then
      (if NumEqBits 1 tok then [true] else []) else (wFlag cli).take 1) := by
  simp [wFlag, wStepOf]

@[simp] lemma wPay_wStepOf (cli tok : List Bool) : wPay (wStepOf cli tok) = tok := by
  simp [wPay, wStepOf]

@[simp] lemma wCnt_wInit : wCnt wInit = [] := by simp [wCnt, wInit]
@[simp] lemma wFlag_wInit : wFlag wInit = [] := by simp [wFlag, wInit]

/-- The word step reads a packed block argument as the block step does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wStepW_eq (W cli : List Bool) (cur : List ℕ) :
    wStepW (pair W (pair cli (digitsToBits cur))) = wStepR cli cur := by
  simp [wStepW, wStepR, midBlock, lastBlock]

/-- The step is polynomial time.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wStepW_mem_FP : wStepW ∈ FP := by
  have hcli : midBlock ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : lastBlock ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hff : (fun v => fstBlock (midBlock v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hcnt : (fun v => wCnt (midBlock v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hflag : (fun v => wFlag (midBlock v)) ∈ FP := mem_FP_comp hff sndBlock_mem_FP
  have hnewCnt : (fun v => (wCnt (midBlock v) ++ [true]).take 3) ∈ FP := by
    have h := takeLenFn_mem_FP (constFn_mem_FP (List.replicate 3 true))
      (appendFn_mem_FP hcnt (constFn_mem_FP [true]))
    simpa using h
  have hflag1 : (fun v => (wFlag (midBlock v)).take 1) ∈ FP := by
    have h := takeLenFn_mem_FP (constFn_mem_FP (List.replicate 1 true)) hflag
    simpa using h
  have hnewFlag : (fun v => if (wCnt (midBlock v)).length = 0 then
      (if NumEqBits 1 (lastBlock v) then [true] else []) else (wFlag (midBlock v)).take 1) ∈ FP :=
    ifEqLen_mem_FP hcnt 0 (ifNumEq_mem_FP htok 1 (constFn_mem_FP [true]) (constFn_mem_FP []))
      hflag1
  exact pairFn_mem_FP (pairFn_mem_FP hnewCnt hnewFlag) htok

/-- The step grows the state by at most the block plus a constant, on every word.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wStepW_length_le (W cli tok : List Bool) :
    (wStepW (pair W (pair cli tok))).length ≤ cli.length + tok.length + 20 := by
  have hcli : midBlock (pair W (pair cli tok)) = cli := by simp [midBlock]
  have htok : lastBlock (pair W (pair cli tok)) = tok := by simp [lastBlock]
  rw [wStepW, hcli, htok, wStepOf]
  simp only [pair_length, List.length_take]
  have h3 : min 3 (wCnt cli ++ [true]).length ≤ 3 := Nat.min_le_left _ _
  split_ifs <;> simp only [List.length_singleton, List.length_nil, List.length_take] <;> omega

/-- The client component of the fold with a silent emitter is a left fold of the step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma runFold_fst_silent : ∀ (rs : List (List ℕ)) (cli out : List Bool),
    (runFold wStepR (fun _ _ => []) cli out rs).1 = List.foldl wStepR cli rs
  | [], _, _ => rfl
  | r :: rs, cli, out => by
      rw [runFold, List.foldl_cons, runFold_fst_silent rs]

/-- The fold over the buffered word's complete blocks.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wFoldR (bufW : List Bool) : List Bool :=
  List.foldl wStepR wInit (blockSplit (bitsToDigits bufW)).1

/-- The fold is polynomial time in the packed oracle argument.
Source: none: infrastructure; FAF `TokenFold.runFold_cli_mem_FP`
Kind: C
Fidelity: n/a -/
lemma wFoldR_mem_FP : (fun v => wFoldR (sndBlock (sndBlock v))) ∈ FP := by
  have h := runFold_cli_mem_FP (STEPr := fun _ => wStepR) (EMITr := fun _ _ _ => [])
    (c := 20) (k := 0) (qQ := 0) (Wf := fun _ => []) (Sf := fun v => sndBlock (sndBlock v))
    wStepW_mem_FP (constFn_mem_FP []) (constFn_mem_FP [])
    (mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP)
    wStepW_length_le (fun _ _ _ => by simp)
    (fun W cli cur _ => wStepW_eq W cli cur) (fun _ _ _ _ => rfl) wInit []
  have heq : (fun z => (runFold wStepR (fun _ _ => []) wInit []
      (blockSplit (bitsToDigits (sndBlock (sndBlock z)))).1).1)
      = fun v => wFoldR (sndBlock (sndBlock v)) := by
    funext z
    rw [wFoldR, runFold_fst_silent]
  exact heq ▸ h

/-! ## The value tests -/

/-- The canonical digit word of a numeral. -/
def kW (K : ℕ) : List Bool := digitsToBits (natDigits4 K)

lemma isDigitWord_kW (K : ℕ) : IsDigitWord (kW K) :=
  isDigitWord_digitsToBits (natDigits4_lt K)

lemma wordVal_kW (K : ℕ) : wordVal (kW K) = K := by
  rw [kW, wordVal_digitsToBits (natDigits4_lt K), digitVal_natDigits4]

/-- `[true]` when the digit word's value is `K`, `[]` otherwise. -/
def eqValW (x : List Bool) (K : ℕ) : List Bool :=
  selectHead (leW (pair x (kW K))) (leW (pair (kW K) x)) []

@[simp] lemma selectHead_true_head (x y : List Bool) : selectHead [true] x y = x := by
  simp [selectHead]

@[simp] lemma selectHead_nil_flag (x y : List Bool) : selectHead [] x y = [] := by
  simp [selectHead]

/-- The equality test decides the value of a digit word.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eqValW_spec {x : List Bool} (hx : IsDigitWord x) (K : ℕ) :
    eqValW x K = if wordVal x = K then [true] else [] := by
  rw [eqValW, leW_spec hx (isDigitWord_kW K), leW_spec (isDigitWord_kW K) hx, wordVal_kW]
  by_cases h1 : wordVal x ≤ K
  · rw [if_pos h1, selectHead_true_head]
    by_cases h2 : K ≤ wordVal x
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]
  · rw [if_neg h1, selectHead_nil_flag, if_neg (by omega)]

/-- The canonical-spelling test on the last block: `5 ≤ t ∧ (t - 5).unpair.1 = wTag`.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def canonTest (pay : List Bool) : List Bool :=
  selectHead (leW (pair (kW 5) pay)) (eqValW (unpairFstW (subW (pair pay (kW 5)))) wTag) []

/-- The Gödel-spelling test: first block `1`, last block `c` with
`1 ≤ c ∧ (c - 1).unpair.1 = 1 ∧ (c - 1).unpair.2.unpair.1 = wTag`.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def godelTest (flag pay : List Bool) : List Bool :=
  selectHead flag
    (selectHead (leW (pair (kW 1) pay))
      (selectHead (eqValW (unpairFstW (predW pay)) 1)
        (eqValW (unpairFstW (unpairSndW (predW pay))) wTag) []) []) []

/-- The canonical-spelling test decides the family condition on a digit word.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma canonTest_spec {pay : List Bool} (hpay : IsDigitWord pay) :
    canonTest pay = if 5 ≤ wordVal pay ∧ (wordVal pay - 5).unpair.1 = wTag then [true] else [] := by
  have hsub := isDigitWord_subW hpay (isDigitWord_kW 5)
  have hsubv := wordVal_subW hpay (isDigitWord_kW 5)
  rw [wordVal_kW] at hsubv
  obtain ⟨hfst, -, hfstv, -⟩ := unpairW_spec hsub
  rw [canonTest, leW_spec (isDigitWord_kW 5) hpay, wordVal_kW, eqValW_spec hfst, hfstv, hsubv]
  by_cases h5 : 5 ≤ wordVal pay
  · by_cases htag : (wordVal pay - 5).unpair.1 = wTag
    · simp [h5, htag]
    · simp [h5, htag]
  · simp [h5]

/-- The Gödel-spelling test decides the family condition on a digit word, given the first-block flag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma godelTest_spec {pay : List Bool} (hpay : IsDigitWord pay) (p : Prop) [Decidable p] :
    godelTest (if p then [true] else []) pay =
      if p ∧ 1 ≤ wordVal pay ∧ (wordVal pay - 1).unpair.1 = 1 ∧
          (wordVal pay - 1).unpair.2.unpair.1 = wTag then [true] else [] := by
  have hpred := isDigitWord_predW hpay
  have hpredv := wordVal_predW hpay
  obtain ⟨hfst, hsnd, hfstv, hsndv⟩ := unpairW_spec hpred
  obtain ⟨hfst2, -, hfst2v, -⟩ := unpairW_spec hsnd
  rw [godelTest, leW_spec (isDigitWord_kW 1) hpay, wordVal_kW, eqValW_spec hfst, hfstv,
    eqValW_spec hfst2, hfst2v, hsndv, hpredv]
  by_cases hp : p
  · by_cases h1 : 1 ≤ wordVal pay
    · by_cases h2 : (wordVal pay - 1).unpair.1 = 1
      · by_cases h3 : (wordVal pay - 1).unpair.2.unpair.1 = wTag
        · simp [hp, h1, h2, h3]
        · simp [hp, h1, h2, h3]
      · simp [hp, h1, h2]
    · simp [hp, h1]
  · simp [hp]

/-! ## The oracle -/

/-- **The witness oracle**: on the day block `0`, the family test on the buffered run's blocks
(one block: canonical; two blocks with first `1`: Gödel escape), emitting `wOut` or nothing.
Source: mandate T1.5
Kind: D
Fidelity: n/a -/
def wOracleFn (v : List Bool) : List Bool :=
  if NumEqBits 0 (fstBlock (sndBlock v)) then
    (if (wCnt (wFoldR (sndBlock (sndBlock v)))).length = 1 then
      selectHead (canonTest (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []
    else if (wCnt (wFoldR (sndBlock (sndBlock v)))).length = 2 then
      selectHead (godelTest (wFlag (wFoldR (sndBlock (sndBlock v))))
        (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []
    else [])
  else []

/-- The oracle is polynomial time.
Source: mandate T1.5
Kind: C
Fidelity: n/a -/
lemma wOracleFn_mem_FP : wOracleFn ∈ FP := by
  have htokW : (fun v => fstBlock (sndBlock v)) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have hfold : (fun v => wFoldR (sndBlock (sndBlock v))) ∈ FP := wFoldR_mem_FP
  have hff : (fun v => fstBlock (wFoldR (sndBlock (sndBlock v)))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hfold fstBlock_mem_FP
  have hcnt : (fun v => wCnt (wFoldR (sndBlock (sndBlock v)))) ∈ FP := by
    simpa [Function.comp_def, wCnt] using mem_FP_comp hff fstBlock_mem_FP
  have hflag : (fun v => wFlag (wFoldR (sndBlock (sndBlock v)))) ∈ FP := by
    simpa [Function.comp_def, wFlag] using mem_FP_comp hff sndBlock_mem_FP
  have hpay : (fun v => wPay (wFoldR (sndBlock (sndBlock v)))) ∈ FP := by
    simpa [Function.comp_def, wPay] using mem_FP_comp hfold sndBlock_mem_FP
  have hleW : ∀ {A B : List Bool → List Bool}, A ∈ FP → B ∈ FP →
      (fun v => leW (pair (A v) (B v))) ∈ FP := fun hA hB => by
    simpa [Function.comp_def] using mem_FP_comp (pairFn_mem_FP hA hB) leW_mem_FP
  have heqVal : ∀ {A : List Bool → List Bool}, A ∈ FP → ∀ K : ℕ,
      (fun v => eqValW (A v) K) ∈ FP := fun hA K => by
    have h := selectHeadFn_mem_FP (hleW hA (constFn_mem_FP (kW K)))
      (hleW (constFn_mem_FP (kW K)) hA) (constFn_mem_FP [])
    exact h
  have hsub : (fun v => subW (pair (wPay (wFoldR (sndBlock (sndBlock v)))) (kW 5))) ∈ FP := by
    simpa [Function.comp_def] using
      mem_FP_comp (pairFn_mem_FP hpay (constFn_mem_FP (kW 5))) subW_mem_FP
  have hfstSub : (fun v => unpairFstW (subW (pair (wPay (wFoldR (sndBlock (sndBlock v)))) (kW 5)))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hsub unpairFstW_mem_FP
  have hcanon : (fun v => canonTest (wPay (wFoldR (sndBlock (sndBlock v))))) ∈ FP := by
    have h := selectHeadFn_mem_FP (hleW (constFn_mem_FP (kW 5)) hpay) (heqVal hfstSub wTag)
      (constFn_mem_FP [])
    exact h
  have hpred : (fun v => predW (wPay (wFoldR (sndBlock (sndBlock v))))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hpay predW_mem_FP
  have hfstPred : (fun v => unpairFstW (predW (wPay (wFoldR (sndBlock (sndBlock v)))))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hpred unpairFstW_mem_FP
  have hsndPred : (fun v => unpairSndW (predW (wPay (wFoldR (sndBlock (sndBlock v)))))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hpred unpairSndW_mem_FP
  have hfstSndPred : (fun v => unpairFstW (unpairSndW (predW (wPay (wFoldR (sndBlock (sndBlock v))))))) ∈ FP := by
    simpa [Function.comp_def] using mem_FP_comp hsndPred unpairFstW_mem_FP
  have hgodel : (fun v => godelTest (wFlag (wFoldR (sndBlock (sndBlock v))))
      (wPay (wFoldR (sndBlock (sndBlock v))))) ∈ FP := by
    have h := selectHeadFn_mem_FP hflag
      (selectHeadFn_mem_FP (hleW (constFn_mem_FP (kW 1)) hpay)
        (selectHeadFn_mem_FP (heqVal hfstPred 1) (heqVal hfstSndPred wTag) (constFn_mem_FP []))
        (constFn_mem_FP []))
      (constFn_mem_FP [])
    exact h
  have hbranch1 : (fun v => selectHead (canonTest (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []) ∈ FP :=
    selectHeadFn_mem_FP hcanon (constFn_mem_FP wOut) (constFn_mem_FP [])
  have hbranch2 : (fun v => selectHead (godelTest (wFlag (wFoldR (sndBlock (sndBlock v))))
      (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []) ∈ FP :=
    selectHeadFn_mem_FP hgodel (constFn_mem_FP wOut) (constFn_mem_FP [])
  have hinner : (fun v => if (wCnt (wFoldR (sndBlock (sndBlock v)))).length = 1 then
      selectHead (canonTest (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []
    else if (wCnt (wFoldR (sndBlock (sndBlock v)))).length = 2 then
      selectHead (godelTest (wFlag (wFoldR (sndBlock (sndBlock v))))
        (wPay (wFoldR (sndBlock (sndBlock v))))) wOut []
    else []) ∈ FP :=
    ifEqLen_mem_FP hcnt 1 hbranch1 (ifEqLen_mem_FP hcnt 2 hbranch2 (constFn_mem_FP []))
  have h := ifNumEq_mem_FP htokW 0 hinner (constFn_mem_FP [])
  exact h

/-- Selection between block-well-formed words is block-well-formed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blockWF_selectHead {x y : List Bool} (hx : BlockWF x) (hy : BlockWF y) (s : List Bool) :
    BlockWF (selectHead s x y) := by
  unfold selectHead
  split_ifs
  · exact hx
  · exact hy
  · exact BlockWF.nil

/-- A selection is no longer than its longer branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma length_selectHead_le (s x y : List Bool) :
    (selectHead s x y).length ≤ max x.length y.length := by
  unfold selectHead
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _
  · simp

/-- The output is block-well-formed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wOracleFn_wf (v : List Bool) : BlockWF (wOracleFn v) := by
  unfold wOracleFn
  split_ifs
  · exact blockWF_selectHead (blockWF_tokBits _) BlockWF.nil _
  · exact blockWF_selectHead (blockWF_tokBits _) BlockWF.nil _
  · exact BlockWF.nil
  · exact BlockWF.nil

/-- The output is at most `wOut` long.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wOracleFn_length_le (v : List Bool) : (wOracleFn v).length ≤ wOut.length := by
  unfold wOracleFn
  split_ifs
  · exact (length_selectHead_le _ _ _).trans (by simp)
  · exact (length_selectHead_le _ _ _).trans (by simp)
  · simp
  · simp

/-! ## The spec -/

/-- The count's length after three or more blocks stays `3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wCnt_length_three : ∀ (rest : List (List ℕ)) (cli : List Bool),
    (wCnt cli).length = 3 → (wCnt (List.foldl wStepR cli rest)).length = 3
  | [], _, h => h
  | r :: rest, cli, h => by
      rw [List.foldl_cons]
      apply wCnt_length_three rest
      rw [wStepR, wCnt_wStepOf, List.length_take, List.length_append, h]
      rfl

/-- The fold on one block.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wFold_one (r : List ℕ) :
    wCnt (List.foldl wStepR wInit [r]) = [true] ∧
      wPay (List.foldl wStepR wInit [r]) = digitsToBits r := by
  simp [wStepR]

/-- The fold on two blocks.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wFold_two (r1 r2 : List ℕ) :
    wCnt (List.foldl wStepR wInit [r1, r2]) = [true, true] ∧
      wFlag (List.foldl wStepR wInit [r1, r2]) =
        (if NumEqBits 1 (digitsToBits r1) then [true] else []) ∧
      wPay (List.foldl wStepR wInit [r1, r2]) = digitsToBits r2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [wStepR]
  · simp only [List.foldl_cons, List.foldl_nil, wStepR, wFlag_wStepOf, wCnt_wStepOf, wCnt_wInit,
      wFlag_wInit, List.nil_append]
    by_cases h : NumEqBits 1 (digitsToBits r1) <;> simp [h]
  · simp [wStepR]

/-- **The oracle computes the run-level lookup**, on every well-formed day block and every
buffered word.
Source: mandate T1.5
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma wOracleFn_spec (zW : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) (bufW : List Bool) :
    decodeBits (wOracleFn (pair zW (pair (digitsToBits cur) bufW)))
      = match wExprRun (decodeBits bufW) (digitVal cur) with
        | some raw => raw ++ [8]
        | none => [] := by
  have htok : fstBlock (sndBlock (pair zW (pair (digitsToBits cur) bufW))) = digitsToBits cur := by
    simp
  have hbuf : sndBlock (sndBlock (pair zW (pair (digitsToBits cur) bufW))) = bufW := by simp
  have hday : NumEqBits 0 (digitsToBits cur) ↔ digitVal cur = 0 := numEqBits_spec 0 cur hcur
  have hdec : decodeBits bufW = (blockSplit (bitsToDigits bufW)).1.map digitVal := by
    rw [decodeBits, undigitize_eq_blockSplit]
  have hblk : ∀ r ∈ (blockSplit (bitsToDigits bufW)).1, ∀ d ∈ r, d < 4 :=
    fun r hr => (blockSplit_digits_lt (bitsToDigits bufW)).1 r hr
  rw [wOracleFn, htok, hbuf, hdec, wFoldR]
  generalize hrs : (blockSplit (bitsToDigits bufW)).1 = rs at hblk ⊢
  -- The day test.
  by_cases hD : digitVal cur = 0
  · rw [if_pos (hday.mpr hD)]
    simp only [wExprRun, hD, true_and]
    match rs, hblk with
    | [], _ =>
        simp [familyRun, wCnt, wInit]
    | [r], hblk =>
        obtain ⟨hcnt, hpay⟩ := wFold_one r
        have hr : ∀ d ∈ r, d < 4 := hblk r (by simp)
        rw [hcnt, hpay]
        simp only [List.length_singleton, ↓reduceIte, List.map_cons, List.map_nil, familyRun]
        rw [canonTest_spec (isDigitWord_digitsToBits hr), wordVal_digitsToBits hr]
        by_cases hfam : 5 ≤ digitVal r ∧ (digitVal r - 5).unpair.1 = wTag
        · rw [if_pos hfam, selectHead_true_head, if_pos (by simpa using hfam)]
          simp [wOut]
        · rw [if_neg hfam, selectHead_nil_flag, if_neg (by simpa using hfam)]
          simp
    | [r1, r2], hblk =>
        obtain ⟨hcnt, hflag, hpay⟩ := wFold_two r1 r2
        have hr1 : ∀ d ∈ r1, d < 4 := hblk r1 (by simp)
        have hr2 : ∀ d ∈ r2, d < 4 := hblk r2 (by simp)
        rw [hcnt, hflag, hpay]
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ↓reduceIte,
          OfNat.ofNat_ne_one, List.map_cons, List.map_nil, familyRun]
        have hb : (if NumEqBits 1 (digitsToBits r1) then ([true] : List Bool) else [])
            = if digitVal r1 = 1 then [true] else [] := by
          simp [numEqBits_spec 1 r1 hr1]
        rw [hb, godelTest_spec (isDigitWord_digitsToBits hr2) (digitVal r1 = 1),
          wordVal_digitsToBits hr2]
        by_cases hfam : digitVal r1 = 1 ∧ 1 ≤ digitVal r2 ∧ (digitVal r2 - 1).unpair.1 = 1 ∧
            (digitVal r2 - 1).unpair.2.unpair.1 = wTag
        · rw [if_pos hfam, selectHead_true_head, if_pos (by simpa using hfam)]
          simp [wOut]
        · rw [if_neg hfam, selectHead_nil_flag, if_neg (by simpa using hfam)]
          simp
    | r1 :: r2 :: r3 :: rest, _ =>
        have h3 : (wCnt (List.foldl wStepR wInit (r1 :: r2 :: r3 :: rest))).length = 3 := by
          apply wCnt_length_three rest
          simp [wStepR]
        rw [if_neg (by rw [h3]; decide), if_neg (by rw [h3]; decide)]
        have hfalse : familyRun (digitVal r1 :: digitVal r2 :: digitVal r3 :: rest.map digitVal)
            = false := rfl
        simp [hfalse]
  · rw [if_neg (fun h => hD (hday.mp h))]
    simp [wExprRun, hD]

/-- **The witness oracle, as a `SpliceOracle`.**
Source: mandate T1.5 ("your first `SpliceCertificate`")
Kind: D
Fidelity: n/a -/
noncomputable def wOracle : SpliceOracle wExprRun where
  R := wOracleFn
  R_FP := wOracleFn_mem_FP
  R_wf := wOracleFn_wf
  R_poly := Polynomial.C wOut.length
  R_length_le := fun v => by simpa using wOracleFn_length_le v
  R_spec := wOracleFn_spec

end Cleanroom.Bli.BliTransfer.AttemptA
