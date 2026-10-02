import Cleanroom.Bli.BliTransfer.AttemptA.Transfer
import Cleanroom.Bli.BliTransfer.AttemptA.Certificate

/-!
# `bli-transfer` (attempt A) · Headline: the expressible-overlay transfer theorem (T1)

The two legs assembled: the economic leg (`Transfer.lean`: bridge day, finite-prefix accounting,
exploitation transport) and the certificate leg (`Certificate.lean`: the splice is an `FP`
transduction of every efficiently computable trader's raw word). `overlay_isLogicalInductor` takes
the overlay's computability as its remaining hypothesis (T1.4, `Computable.lean`, discharges it in
`overlay_isLogicalInductor'`).

Sources: [[bli-program]] §3.1; bli-paper-039 (`main.tex:440`); mandate T1.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- **The expressible-overlay transfer theorem** (L1). For every logical inductor `Q` over `DP`,
every re-pricing `ov` with an expression map `E` — bodies closed, reading only prices of sentences
small on the day read, at days `≤ k`; un-fired sentences keep `Q`'s value or are small — and a
`SpliceCertificate` for the map (a polynomial-time run-level oracle whose spec is quantified over
every spelling `parseRpn` accepts), the overlay market `overlay Q ov` is a logical inductor over
`DP`, given its computability `hcomp`. One-market: nothing reads the overlay back into `Q`.
`noExploit` is at the criterion's own quantifier: for **every** `EfficientlyComputable` trader
exploiting the overlay, its splice is `EfficientlyComputable` and exploits `Q`.
Source: [[bli-program]] §3.1; bli-paper-039, bli-paper-031, bli-slides-002/006/030, bli-soto-a-002 (reading A), bli-soto-a-004; mandate T1
Kind: C
Fidelity: exact (the program's §3.1 statement, with the run-level oracle in place of its "(k, ψ) ↦ expr k ψ ∈ FP", Known issue 5, and the guard dropped, Known issue 6)
Hyps: (a) except `C` (the certificate: an `FP` oracle and its spec, the instance's obligation) and `hcomp` (the overlay's computability, T1.4) -/
theorem overlay_isLogicalInductor (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (C : SpliceCertificate E.expr) (hcomp : ComputableMarket (overlay Q ov)) :
    IsLogicalInductor (overlay Q ov) DP :=
  overlay_isLogicalInductor_of_spliceEC E
    (fun _ hTr => EfficientlyComputable.spliceOn C E.rank_le hTr) hcomp

end Cleanroom.Bli.BliTransfer.AttemptA
