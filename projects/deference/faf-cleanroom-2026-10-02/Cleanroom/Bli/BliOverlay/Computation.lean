import Cleanroom.Bli.BliOverlay.Recursion
import Cleanroom.Bli.BliOverlay.AttemptA.Computation

/-!
# `bli-overlay` · Computation (reconciled): T6, the compiler boundary (stretch; open)

Both attempts built the fuel-bounded evaluator of their recursion in the shape of FAF's
`LIAComputation.lean` (monotone in fuel, sound — a success is the semantic prefix — and
eventually successful), the encoded day-quote evaluators, and a compiler boundary
`OverlayBoundedEvaluatorCompiler` (one `Computable₂` field) with `toComputableMarket` and the
criterion assembly. **Neither instantiated the boundary**: that is the primitive-recursive
compilation of the day step (FAF's `LIACompiler.lean`, 4041 lines, does it for the LIA) plus
the compilation of the overlay itself — which is where `ov`'s computability enters, and which
no customer has yet fixed as a definition. So nothing in this package proves
`ComputableMarket (overlayHistory DP ov)`, and the assembly lemma's ledger row is
`partial: computability open`, as the mandate expects. The record exposes attempt A's boundary
(it is stated over the recursion of record); attempt A's evaluator and its soundness
(`AttemptA.overlayPrefixAtFuel`, `AttemptA.overlayPrefixAtFuel_sound`,
`AttemptA.exists_overlayPrefixAtFuel`, the encoded quote evaluators) are imported and carry
their own ledger rows. Attempt B's evaluator (`AttemptB.Computation`) is the same design over
its recursion, with the stage table as a parameter.

Sources: [[bli-overlay-mandate]] T6; [[bli-program]] §7 item 8; [[bli-found-liacomputation]].
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-- **The compiler boundary (not instantiated).** The one structure asserting that attempt A's
bounded evaluator of the record's recursion is a computable two-argument natural function —
the shape of FAF's `LIABoundedEvaluatorCompiler`. It carries no market content; inhabiting it
is L6(b), open.
Source: [[bli-overlay-mandate]] T6
Kind: D
Fidelity: exact -/
abbrev OverlayBoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay) :=
  AttemptA.OverlayBoundedEvaluatorCompiler process ov

/-- **From the boundary to `ComputableMarket`.** Once the bounded evaluator is compiled, the
overlaid market has the exact rational market program the criterion asks for. The boundary
itself is not instantiated.
Source: [[bli-overlay-mandate]] T6; [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: conditional on the (uninstantiated) compiler boundary
Hyps: (b) `compiler : OverlayBoundedEvaluatorCompiler process ov` — the compilation
certificate, not proved -/
theorem OverlayBoundedEvaluatorCompiler.toComputableMarket {DP : DeductiveProcess}
    {process : DeductiveProcessComputation DP} {ov : Overlay}
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    ComputableMarket (overlayHistory DP ov) :=
  AttemptA.OverlayBoundedEvaluatorCompiler.toComputableMarket compiler

/-- **Criterion assembly from the boundary**: with a compiled evaluator, the overlaid market is
a logical inductor. The boundary is the one missing piece (L6(b)); nothing else is assumed.
Source: [[bli-overlay-mandate]] T6
Kind: L
Fidelity: weaker: conditional on the (uninstantiated) compiler boundary
Hyps: (b) `compiler` as in `toComputableMarket` -/
theorem overlay_isLogicalInductor_of_compiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (ov : Overlay)
    (compiler : OverlayBoundedEvaluatorCompiler process ov) :
    IsLogicalInductor (overlayHistory DP ov) DP :=
  AttemptA.overlay_isLogicalInductor_of_compiler process ov compiler

end

end Cleanroom.Bli.BliOverlay
