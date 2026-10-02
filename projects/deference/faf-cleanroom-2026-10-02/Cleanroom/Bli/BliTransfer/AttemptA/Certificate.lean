import Cleanroom.Bli.BliTransfer.AttemptA.Contraction
import LogicalInduction.Construction.Freeze.Step

/-!
# `bli-transfer` (attempt A) · Certificate: the splice as a polynomial-time transduction (T1.3)

The one genuinely new certificate of the package: the flat splice pass
`rpnConditionRun (spliceEmitOn exprRun)` (`Contraction.lean`) as a `Complexity.FP` function of the
trader's raw bit word, through FAF's emitter-generic block fold `TokenFold.runFold_mem_FP` with the
conditioning automaton `CondStep.condStepR` and a **splice emitter** in place of the freeze's
`FreezeStep.flatEmitR` (`Construction/Freeze/Step.lean`, copied link by link).

## The interface: `SpliceOracle`

The run-level lookup, as FAF's `FreezeStep.RunOracle` but with the one change the overlay needs:
its output is bounded by a **polynomial** in its input (`R_length_le`), not by a constant — the
emitted body is a serialized expression of size polynomial in the sentence, not a finite table's
quote. Its input is `pair zW (pair tokW bufW)`: the machine's raw input word (the unary day —
unused here, available to a day-aware instance), the day's token block, and the buffered sentence
run's bits. `R_spec` fixes the decoded output on every well-formed day block and **every**
buffered run: the raw body `exprRun` returns for the run, plus the `letE` close, or nothing.

## Why a guard, and why it is harmless

`runFold_mem_FP`'s emission budget is `qQ.eval W.length + k * (cli.length + tok.length)`:
polynomial in the parameter block, only *linear* in the state. The body is polynomial in the
buffered run, which lives in the state, so the emitter guards the oracle call by the length of
`guardWord W` (a fixed multiple of the parameter block's length, computed in `FP` by pairing) and
emits nothing when the guard fails. The parameter block is `pair (F x) x`, the trader's whole
output word beside its input (`FPFold.mem_FP_withInput`'s shape), so on every **reachable**
state the buffered run is a sub-word of `F x` and the guard holds; the fold invariant
`decodeBits_runFold_splice` carries exactly that bound and `blockSplit_measure` seeds it. The
guard is therefore a proof device for the universal budget, not a restriction on the rewrite.

## The chain

oracle → `splicePass_mem_FP` (the block fold in `FP`) → `decodeBits_splicePass` (it computes the
symbol-level pass on every word) → `spliceStreamRewriter_of_certificate` (contraction commutes,
`Contraction.lean`) → `EfficientlyComputable.spliceOn` (the token model transports the strategy,
`TokenModel.lean`). `SpliceCertificate expr` packages a lookup, its agreement with the map on
every spelling, and an oracle for it — nothing quantified over traders (mandate trap (ii)).

Measured cost: `import LogicalInduction.Construction.Freeze.Step` alone elaborated in 6.8 s wall
on forge-verity (warm cache, 2026-09-30, one run).

Sources: mandate T1.3 (angle A); FAF `Construction/Freeze/Step.lean`,
`Framework/Machine/TokenFold.lean:2356`, `Framework/Machine/FPFold.lean:191`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional
open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.CondStep LogicalInduction.RpnConditioning

/-! ## The oracle -/

/-- **The run-level lookup, as an interface** (FAF's `FreezeStep.RunOracle` with a polynomial
output bound). Given the machine's raw input word, the day's token block and the buffered
sentence run's bits, `R` returns the bits of the raw body followed by the `letE` close `8` when the
lookup fires on the run, and nothing otherwise. `R_spec` quantifies over every buffered run
(any spelling). `R_length_le` is the only place the freeze's interface was too narrow.
Source: mandate T1.3 (angle A, "(i) a `SpliceOracle` structure = `RunOracle` with `R_length_le` polynomial")
Kind: D
Fidelity: n/a -/
structure SpliceOracle (exprRun : List ℕ → ℕ → Option (List ℕ)) where
  /-- The oracle. -/
  R : List Bool → List Bool
  /-- It is polynomial time. -/
  R_FP : R ∈ FP
  /-- Its output is a whole number of complete blocks, so splices decode piecewise. -/
  R_wf : ∀ v : List Bool, BlockWF (R v)
  /-- The output budget, polynomial in the input. -/
  R_poly : Polynomial ℕ
  /-- The bound itself. -/
  R_length_le : ∀ v : List Bool, (R v).length ≤ R_poly.eval v.length
  /-- And it emits the spliced body, on every well-formed day block and every buffered run. -/
  R_spec : ∀ (zW : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) → ∀ bufW : List Bool,
    decodeBits (R (pair zW (pair (digitsToBits cur) bufW)))
      = match exprRun (decodeBits bufW) (digitVal cur) with
        | some raw => raw ++ [8]
        | none => []

/-! ## The guarded emitter -/

/-- The guard word: a fixed multiple of the parameter block's length, built by pairing.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def guardWord (W : List Bool) : List Bool := pair (pair W W) (pair W W)

/-- `|guardWord W| = 9 |W| + 8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma guardWord_length (W : List Bool) : (guardWord W).length = 9 * W.length + 8 := by
  simp only [guardWord, pair_length]
  omega

/-- The oracle call, guarded by the parameter block's length.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def guardedR (R : List Bool → List Bool) (W v : List Bool) : List Bool :=
  if v.length ≤ (guardWord W).length then R v else []

/-- The splice pass's block-level emitter: copy the token through, and at a price-day slot append
the (guarded) oracle's body.
Source: mandate T1.3; FAF `FreezeStep.flatEmitR`
Kind: D
Fidelity: n/a -/
def spliceEmitR (R : List Bool → List Bool) (W cli : List Bool) (cur : List ℕ) : List Bool :=
  if (csMode cli).length = 2 then
    dayBits (digitsToBits cur) ++
      guardedR R W (pair (sndBlock W) (pair (digitsToBits cur) (csBuf cli)))
  else dayBits (digitsToBits cur)

/-- Its word-level reading, on the packed argument `pair W (pair cli tok)`.
Source: mandate T1.3; FAF `FreezeStep.flatEmitW`
Kind: D
Fidelity: n/a -/
def spliceEmitW (R : List Bool → List Bool) (v : List Bool) : List Bool :=
  if (csMode (midBlock v)).length = 2 then
    dayBits (lastBlock v) ++
      guardedR R (fstBlock v) (pair (sndBlock (fstBlock v)) (pair (lastBlock v) (csBuf (midBlock v))))
  else dayBits (lastBlock v)

/-- The word emitter reads a packed block argument exactly as `spliceEmitR` does.
Source: none: infrastructure; FAF `FreezeStep.flatEmitW_eq`
Kind: L
Fidelity: n/a -/
lemma spliceEmitW_eq (R : List Bool → List Bool) (W cli : List Bool) (cur : List ℕ) :
    spliceEmitW R (pair W (pair cli (digitsToBits cur))) = spliceEmitR R W cli cur := by
  rw [spliceEmitW, spliceEmitR]
  simp only [midBlock, lastBlock, sndBlock_pair, fstBlock_pair]

/-! ## What the emitter emits -/

/-- The emitter's output is a whole number of complete blocks.
Source: none: infrastructure; FAF `FreezeStep.blockWF_flatEmitR`
Kind: L
Fidelity: n/a -/
lemma blockWF_spliceEmitR {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun)
    (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4) :
    BlockWF (spliceEmitR O.R W cli cur) := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  rw [spliceEmitR]
  split_ifs
  · refine hday.append ?_
    rw [guardedR]
    split_ifs
    · exact O.R_wf _
    · exact BlockWF.nil
  · exact hday

/-- **The emitter computes the symbol-level splice emission**, on any state whose oracle argument
passes the guard.
Source: mandate T1.3; FAF `FreezeStep.decodeBits_flatEmitR`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma decodeBits_spliceEmitR {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun)
    (W cli : List Bool) (cur : List ℕ) (hcur : ∀ d ∈ cur, d < 4)
    (hguard : (pair (sndBlock W) (pair (digitsToBits cur) (csBuf cli))).length ≤
      (guardWord W).length) :
    decodeBits (spliceEmitR O.R W cli cur)
      = if rcMode (csPack cli) = 2 then
          spliceEmitOn exprRun (csTokens cli) (digitVal cur)
        else [digitVal cur] := by
  have hday : BlockWF (dayBits (digitsToBits cur)) := blockWF_run cur hcur
  have hdayd : decodeBits (dayBits (digitsToBits cur)) = [digitVal cur] :=
    decodeBits_run cur hcur
  have hmode : rcMode (csPack cli) = (csMode cli).length := by
    rw [csPack, rcMode_pack]
  rw [spliceEmitR, hmode, guardedR, if_pos hguard]
  split_ifs
  · rw [decodeBits_append hday (O.R_wf _), hdayd, O.R_spec (sndBlock W) cur hcur,
      spliceEmitOn, csTokens]
    cases exprRun (decodeBits (csBuf cli)) (digitVal cur) <;> simp
  · exact hdayd

/-! ## Membership and the emission bound -/

/-- The word-level emitter is polynomial time, from the oracle's own `FP` membership,
`TokenFold`'s block projections and the length-guarded branch.
Source: mandate T1.3; FAF `FreezeStep.flatEmitW_mem_FP`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma spliceEmitW_mem_FP {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun) :
    spliceEmitW O.R ∈ FP := by
  have hW : fstBlock ∈ FP := fstBlock_mem_FP
  have hW2 : (fun v => sndBlock (fstBlock v)) ∈ FP := mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP
  have hcli : midBlock ∈ FP := mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have htok : lastBlock ∈ FP := mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP
  have hff : (fun v => fstBlock (midBlock v)) ∈ FP := mem_FP_comp hcli fstBlock_mem_FP
  have hsf : (fun v => sndBlock (midBlock v)) ∈ FP := mem_FP_comp hcli sndBlock_mem_FP
  have hm : (fun v => csMode (midBlock v)) ∈ FP := mem_FP_comp hff fstBlock_mem_FP
  have hbuf : (fun v => csBuf (midBlock v)) ∈ FP := mem_FP_comp hsf sndBlock_mem_FP
  have harg : (fun v => pair (sndBlock (fstBlock v)) (pair (lastBlock v) (csBuf (midBlock v)))) ∈ FP :=
    pairFn_mem_FP hW2 (pairFn_mem_FP htok hbuf)
  have hguardW : (fun v => guardWord (fstBlock v)) ∈ FP :=
    pairFn_mem_FP (pairFn_mem_FP hW hW) (pairFn_mem_FP hW hW)
  have hr : (fun v => O.R (pair (sndBlock (fstBlock v)) (pair (lastBlock v) (csBuf (midBlock v))))) ∈ FP :=
    mem_FP_comp harg O.R_FP
  have hguarded : (fun v => guardedR O.R (fstBlock v)
      (pair (sndBlock (fstBlock v)) (pair (lastBlock v) (csBuf (midBlock v))))) ∈ FP :=
    selectHeadFn_leFlag_mem_FP hguardW harg hr (constFn_mem_FP [])
  have hday : (fun v => dayBits (lastBlock v)) ∈ FP :=
    appendFn_mem_FP htok (constFn_mem_FP (digitBits 4))
  have h := selectHeadFn_eqLen_mem_FP hm (constFn_mem_FP (uw 2))
    (appendFn_mem_FP hday hguarded) hday
  simp only [length_uw] at h
  exact h

/-- The emission budget polynomial: the oracle's bound at the guard word's length, plus the day
block's terminator.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def emitPoly {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun) :
    Polynomial ℕ :=
  O.R_poly.comp (Polynomial.C 9 * Polynomial.X + Polynomial.C 8) + Polynomial.C 3

/-- The emission bound is polynomial in the parameter block and **linear** in the state — all
`runFold_mem_FP` allows, and what the guard buys.
Source: mandate T1.3; FAF `FreezeStep.flatEmitW_length_le`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma spliceEmitW_length_le {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun)
    (W cli tok : List Bool) :
    (spliceEmitW O.R (pair W (pair cli tok))).length
      ≤ (emitPoly O).eval W.length + 1 * (cli.length + tok.length) := by
  have hcli : midBlock (pair W (pair cli tok)) = cli := by simp [midBlock]
  have htok : lastBlock (pair W (pair cli tok)) = tok := by simp [lastBlock]
  have hfst : fstBlock (pair W (pair cli tok)) = W := by simp
  have hpoly : (emitPoly O).eval W.length = O.R_poly.eval (9 * W.length + 8) + 3 := by
    simp [emitPoly, Polynomial.eval_comp]
  rw [hpoly, spliceEmitW, hcli, htok, hfst]
  have hguarded : (guardedR O.R W (pair (sndBlock W) (pair tok (csBuf cli)))).length
      ≤ O.R_poly.eval (9 * W.length + 8) := by
    rw [guardedR]
    split_ifs with hle
    · refine (O.R_length_le _).trans ?_
      apply polynomial_eval_mono_nat
      rw [guardWord_length] at hle
      exact hle
    · simp
  split_ifs
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega
  · rw [dayBits]
    simp only [List.length_append, length_digitBits]
    omega

/-! ## The pass, decoded -/

/-- One automaton step grows the buffer by at most the incoming block and its terminator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma csBuf_condStepR_length_le (cli : List Bool) (cur : List ℕ) :
    (csBuf (condStepR cli cur)).length ≤ (csBuf cli).length + 3 * cur.length + 3 := by
  rw [condStepR, condStepOf, csBuf_condSt, csBufStep]
  split_ifs
  · simp
  · simp only [List.length_append, length_digitsToBits, length_digitBits]
    omega

/-- Folding the emitter over a well-formed block sequence decodes to `rpnConditionRun` applied to
the same tokens, as long as the buffer plus the remaining blocks fit the parameter block — the
invariant that discharges the guard on every reachable state.
Source: mandate T1.3; FAF `FreezeStep.decodeBits_runFold_freeze`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma decodeBits_runFold_splice {exprRun : List ℕ → ℕ → Option (List ℕ)}
    (O : SpliceOracle exprRun) (W : List Bool) :
    ∀ (rs : List (List ℕ)) (cli out : List Bool),
      (∀ r ∈ rs, ∀ d ∈ r, d < 4) → BlockWF (csBuf cli) → BlockWF out →
      (csBuf cli).length + (rs.map fun r => 3 * r.length + 3).sum ≤ W.length + 3 →
      decodeBits (runFold condStepR (spliceEmitR O.R W) cli out rs).2
        = decodeBits out
          ++ (rpnConditionRun (spliceEmitOn exprRun)
                (csPack cli, csTokens cli) (rs.map digitVal)).2
  | [], cli, out, _, _, _, _ => by
      rw [runFold, List.map_nil, rpnConditionRun_nil]
      simp
  | r :: rs, cli, out, hrs, hbuf, hout, hinv => by
      have hr : ∀ d ∈ r, d < 4 := hrs r (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rs, ∀ d ∈ q, d < 4 :=
        fun q hq => hrs q (List.mem_cons_of_mem _ hq)
      have hbuf' : BlockWF (csBuf (condStepR cli r)) := bufWF_condStepR cli r hr hbuf
      have hemit : BlockWF (spliceEmitR O.R W cli r) := blockWF_spliceEmitR O W cli r hr
      simp only [List.map_cons, List.sum_cons] at hinv
      have hstep := csBuf_condStepR_length_le cli r
      have hinv' : (csBuf (condStepR cli r)).length +
          (rs.map fun r => 3 * r.length + 3).sum ≤ W.length + 3 := by omega
      have hsnd : (sndBlock W).length ≤ W.length := by
        have := two_fstBlock_add_sndBlock_le W
        omega
      have hguard : (pair (sndBlock W) (pair (digitsToBits r) (csBuf cli))).length ≤
          (guardWord W).length := by
        rw [guardWord_length]
        simp only [pair_length, length_digitsToBits]
        omega
      rw [runFold, decodeBits_runFold_splice O W rs _ _ hrest hbuf' (hout.append hemit) hinv',
        decodeBits_append hout hemit, csPack_condStepR, csTokens_condStepR cli r hr hbuf,
        decodeBits_spliceEmitR O W cli r hr hguard, List.map_cons]
      rw [show (csPack cli, csTokens cli) = ((csPack cli, csTokens cli).1,
            (csPack cli, csTokens cli).2) from rfl, rpnConditionRun]
      simp only [List.append_assoc]

/-- The block measure of a digit stream: completed blocks (with terminators) plus the trailing
partial account for every digit.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blockSplit_measure (ds : List ℕ) :
    ((blockSplit ds).1.map fun r => r.length + 1).sum + (blockSplit ds).2.length = ds.length := by
  suffices h : ∀ init : List (List ℕ) × List ℕ,
      ((List.foldl blockStep init ds).1.map fun r => r.length + 1).sum
          + (List.foldl blockStep init ds).2.length
        = (init.1.map fun r => r.length + 1).sum + init.2.length + ds.length by
    simpa [blockSplit] using h ([], [])
  induction ds with
  | nil => intro init; simp
  | cons d rest ih =>
      intro init
      rw [List.foldl_cons, ih (blockStep init d), List.length_cons]
      rw [blockStep]
      split_ifs
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, List.length_nil]
        omega

/-- **The splice pass is polynomial time.** `Sf` is the trader's serialized stream; the parameter
block is the stream beside the raw input (`pair (Sf z) z`), which is what makes the emission
budget close and gives a day-aware oracle its day.
Source: mandate T1.3; FAF `FreezeStep.freezePass_mem_FP`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma splicePass_mem_FP {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun)
    {Sf : List Bool → List Bool} (hSf : Sf ∈ FP) :
    (fun z => (runFold condStepR (spliceEmitR O.R (pair (Sf z) z)) condInit []
        (blockSplit (bitsToDigits (Sf z))).1).2) ∈ FP :=
  runFold_mem_FP (STEPr := fun _ => condStepR) (EMITr := spliceEmitR O.R)
    (c := 51) (k := 1) (qQ := emitPoly O)
    condStepW_mem_FP (spliceEmitW_mem_FP O) (mem_FP_pairWithInput hSf) hSf
    condStepW_length_le (spliceEmitW_length_le O)
    (fun W cli cur h => condStepW_eq W cli cur h)
    (fun W cli cur _ => spliceEmitW_eq O.R W cli cur) condInit []

/-- **And it computes the symbol-level splice**, on every word, well-formed or garbage, with no
clamp — `rpnConditionRun (spliceEmitOn exprRun)` itself.
Source: mandate T1.3; FAF `FreezeStep.decodeBits_freezePass`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma decodeBits_splicePass {exprRun : List ℕ → ℕ → Option (List ℕ)} (O : SpliceOracle exprRun)
    (w z : List Bool) :
    decodeBits (runFold condStepR (spliceEmitR O.R (pair w z)) condInit []
        (blockSplit (bitsToDigits w)).1).2
      = (rpnConditionRun (spliceEmitOn exprRun) (rcPack 0 0 0, [])
          (undigitize (bitsToDigits w))).2 := by
  have hmeasure := blockSplit_measure (bitsToDigits w)
  have hsum : ∀ l : List (List ℕ),
      (l.map fun r => 3 * r.length + 3).sum = 3 * (l.map fun r => r.length + 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons r rs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  have hinv : (csBuf condInit).length +
      ((blockSplit (bitsToDigits w)).1.map fun r => 3 * r.length + 3).sum
        ≤ (pair w z).length + 3 := by
    rw [csBuf_condInit, hsum, pair_length]
    simp only [List.length_nil, length_bitsToDigits] at hmeasure ⊢
    omega
  have h := decodeBits_runFold_splice O (pair w z) (blockSplit (bitsToDigits w)).1 condInit []
    (fun r hr => (blockSplit_digits_lt (bitsToDigits w)).1 r hr)
    (by simpa using BlockWF.nil) BlockWF.nil hinv
  rw [csPack_condInit, csTokens_condInit] at h
  simpa [← undigitize_eq_blockSplit] using h

/-! ## The certificate and the efficiency transport -/

/-- **The certificate interface** an instance must inhabit: a run-level lookup, its agreement with
the expression map on every spelling `parseRpn` accepts, and a polynomial-time oracle for it.
Nothing here is quantified over traders (mandate trap (ii)); `bli-assemble` instantiates it for
the tent kernel's expression map.
Source: mandate T1.3
Kind: D
Fidelity: n/a -/
structure SpliceCertificate (expr : ℕ → Sentence → Option EF) where
  /-- The run-level lookup. -/
  exprRun : List ℕ → ℕ → Option (List ℕ)
  /-- It agrees with the map on every accepted spelling. -/
  agrees : RunAgrees expr exprRun
  /-- Its polynomial-time oracle. -/
  oracle : SpliceOracle exprRun

/-- **`SpliceStreamRewriter` follows from the certificate, and from nothing else.**
Source: mandate T1.3; FAF `FreezeStep.freezeStreamRewriter_of_runOracle`
Kind: C
Fidelity: exact
Hyps: (a) except the certificate -/
lemma spliceStreamRewriter_of_certificate {expr : ℕ → Sentence → Option EF}
    (C : SpliceCertificate expr) : SpliceStreamRewriter expr := by
  refine spliceStreamRewriter_of_flatPass expr C.exprRun C.agrees ?_
  intro F hF
  exact ⟨_, splicePass_mem_FP C.oracle hF, fun x => decodeBits_splicePass C.oracle (F x) x⟩

/-- **The splice preserves efficient computability, for every efficiently computable trader**,
given a certificate for the expression map. This is T1.3's theorem at the criterion's own
quantifier: `EfficientlyComputable` in, `EfficientlyComputable` out, no trader class.
Source: [[bli-program]] §3.1 (iii); mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) except `C`, the certificate (an `FP` oracle with its spec on every spelling) -/
theorem EfficientlyComputable.spliceOn {expr : ℕ → Sentence → Option EF}
    (C : SpliceCertificate expr) (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    {Tr : Trader} (hTr : EfficientlyComputable Tr) :
    EfficientlyComputable (Trader.spliceOn expr hrank Tr) :=
  EfficientlyComputable.spliceOn_of_rewriter expr hrank
    (spliceStreamRewriter_of_certificate C) hTr

end Cleanroom.Bli.BliTransfer.AttemptA
