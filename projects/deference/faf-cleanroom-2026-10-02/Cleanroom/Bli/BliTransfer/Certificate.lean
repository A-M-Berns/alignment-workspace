import Cleanroom.Bli.BliTransfer.Defs
import Cleanroom.Bli.BliTransfer.AttemptA.Certificate

/-!
# `bli-transfer` · Certificate: the splice certificate of record (T1.3)

The certificate interface and the efficiency transport are **attempt A's**: they reach the
criterion's own quantifier — the splice of *every* `EfficientlyComputable` trader is
`EfficientlyComputable`, given one `FP` run-level oracle for the expression map — through FAF's
emitter-generic flat-stream rewriter (`rpnConditionRun`), the contraction commutation
(`unRpn_rpnConditionRun_of`) and the polynomial-time block fold (`runFold_mem_FP`) with the whole
input word as parameter block. Attempt B's certificate (`AttemptB.Certificate`) lands, as its
angle predicted, on the *presented* class `SpliceBuiltTrader` (traders built from FAF's
`MachineSpliceStream.serialize_*` combinators); it is kept as an attempt-level result, with its
oracle interface (`AttemptB.SpliceOracle`, contraction form) and its bridge showing FAF's freeze
`RunOracle` is a splice oracle (`AttemptB.SpliceOracle.ofRunOracle`, `.ofTable`). The two oracle
interfaces are not bridged here: attempt B's specification is up to contraction and may depend
on the day token's spelling, attempt A's is literal on `(run, digitVal cur)`, so a B-oracle does
not yield an A-certificate without further work (recorded in the report).

The interface `bli-assemble` instantiates: `SpliceCertificate expr` = a run-level lookup
`exprRun`, its agreement with the map on every spelling `parseRpn` accepts (`RunAgrees`), and a
polynomial-time oracle `SpliceOracle exprRun` (FAF's `FreezeStep.RunOracle` with a polynomial
output bound). Nothing in it is quantified over traders (mandate trap (ii)). The template
instance is `WitnessLia.wCertificate`.

Sources: [[bli-program]] §3.1 (iii), corrected per mandate Known issue 5; mandate T1.3.
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The interface and the chain (attempt A's, re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptA
  (EF.rawSerialize RunAgrees SpliceStreamRewriter EfficientlyComputable.spliceOn_of_rewriter
   spliceStreamRewriter_of_flatPass unRpn_rpnSpliceRunOn
   strategyOfTokens_spliceTokenRunOn_trades
   SpliceOracle SpliceCertificate spliceStreamRewriter_of_certificate
   splicePass_mem_FP decodeBits_splicePass)

/-- **The splice preserves efficient computability, for every efficiently computable trader**,
given a certificate for the expression map (a polynomial-time run-level oracle whose
specification is quantified over every spelling `parseRpn` accepts). T1.3 at the criterion's own
quantifier: `EfficientlyComputable` in, `EfficientlyComputable` out, no trader class. Proved by
attempt A (`AttemptA.EfficientlyComputable.spliceOn`: the flat pass is `FP` with a guarded,
polynomially bounded emitter; contraction commutes; the token-model transducer law transports
the decoded strategy).
Source: [[bli-program]] §3.1 (iii); mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) except `C`, the certificate (an `FP` oracle with its spec on every spelling — the instance's obligation) -/
theorem EfficientlyComputable.spliceOn {expr : ℕ → Sentence → Option EF}
    (C : SpliceCertificate expr) (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    {Tr : Trader} (hTr : EfficientlyComputable Tr) :
    EfficientlyComputable (Trader.spliceOn expr hrank Tr) :=
  AttemptA.EfficientlyComputable.spliceOn C hrank hTr

end Cleanroom.Bli.BliTransfer
