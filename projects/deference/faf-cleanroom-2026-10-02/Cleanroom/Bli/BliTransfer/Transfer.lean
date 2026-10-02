import Cleanroom.Bli.BliTransfer.Certificate
import Cleanroom.Bli.BliTransfer.AttemptA.Transfer
import Cleanroom.Bli.BliTransfer.AttemptA.Headline
import Cleanroom.Bli.BliTransfer.AttemptA.Computable

/-!
# `bli-transfer` · Transfer: the expressible-overlay transfer theorem (T1) and the overlay's
computability (T1.4)

The package's headline, stated once over the definitions of record and proved by attempt A's
route. Three forms, from the most hypothetical to the one of record:

* `overlay_isLogicalInductor_of_transfer` — the two-hypothesis form (attempt B's shape): the
  transfer of efficiency for every e.c. trader (`htrans`) and the overlay's computability
  (`hcomp`) as named hypotheses; the economic leg alone (bridge day, finite-prefix accounting,
  exploitation transport). Both attempts proved this form independently (A:
  `overlay_isLogicalInductor_of_spliceEC`; B: `overlay_isLogicalInductor_of_transfer` over its
  own `spliceTrader`).
* `overlay_isLogicalInductor` — `htrans` discharged by the certificate (T1.3, attempt A):
  hypotheses are the certificate and `hcomp`.
* `overlay_isLogicalInductor'` — **the headline of record**: `hcomp` discharged by T1.4
  (`overlay_computableMarket`), so the remaining hypotheses are the certificate and a computable
  table for the re-pricing — both the instance's obligations, neither a `(b)` nor a `(c)`.

Scope (plan rule 9): over an expression map whose bodies are closed and read only small prices
of days `≤ k`, with a polynomial-time run-level oracle quantified over every spelling `parseRpn`
accepts; one-market (nothing reads the overlay back into `Q`). `noExploit` is at the criterion's
own quantifier: for **every** `EfficientlyComputable` trader exploiting the overlay, its splice
is `EfficientlyComputable` and exploits `Q`. Tier B (mandate trap (iv)): `ExprMap.silent` is a
real hypothesis — an `ov` that changes an un-fired large sentence is not covered, and the
theorem is false for it (a trader reading that leaf is not rewritten).

T1.4 was proved by both attempts independently (A: `tsCode_prim`/`smallCode_prim` by
course-of-values recursion on Foundation's decoder; B: `AttemptB.smallCode_primrec`, the same
recursion certified on `ℕ` alone). The form of record is attempt A's, because the headline of
record uses it.

Sources: [[bli-program]] §3.1; bli-paper-039 (`main.tex:440`), bli-paper-031, bli-slides-002/006/030,
bli-soto-a-002 (reading A), bli-soto-a-004; mandate T1, T1.2, T1.4.
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The accounting and the computability kit (attempt A's, re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptA
  (overlay_range exists_settle_day Trader.netWorth_difference_le_of_tail_eq spliceErrorBound
   Trader.spliceOn_netWorth_difference_le Trader.spliceOn_exploits
   noExploit_overlay_of_spliceEC overlay_isLogicalInductor_of_spliceEC
   ComputableTable ComputableMarket.exists_computableTable overlayTable
   tsCode tsCode_prim smallCode smallCode_prim)

/-! ## T1.4 -/

/-- **The overlay of a computable market by a computable re-pricing is a computable market**:
the smallness test on Gödel codes is primitive recursive (`smallCode_prim`, course-of-values
recursion on Foundation's decoder), so the overlay's table is `Q`'s table where the code is
small and `ov`'s elsewhere. No polynomial-time content is claimed. Proved by attempt A
(`AttemptA.overlay_computableMarket`); attempt B proved the same test primitive recursive
independently (`AttemptB.smallCode_primrec`).
Source: mandate T1.4
Kind: C
Fidelity: exact
Hyps: (a) `hQ` (the inductor's certificate), `hov` (the re-pricing's own computable table), `hrange` -/
theorem overlay_computableMarket {Q : History} {ov : ℕ → Sentence → ℚ}
    (hQ : ComputableMarket Q) (hov : ComputableTable ov)
    (hrange : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) :
    ComputableMarket (overlay Q ov) :=
  AttemptA.overlay_computableMarket hQ hov hrange

/-! ## T1 -/

/-- **The two-hypothesis form of the transfer theorem** (the economic leg alone): the overlay of
a logical inductor by an expression map is a logical inductor, given the transfer of efficiency
for every e.c. trader (`htrans`, what T1.3's certificate supplies) and the overlay's
computability (`hcomp`, T1.4). `marketComputable := hcomp`,
`processComputable := hQ.processComputable`, `noExploit` from the bridge day
(`exists_settle_day`, from `bli-found`'s `bridge_lemma`), the exact strategy-value transport on
the days after it (`Strategy.spliceOn_value`), the finite-prefix accounting before it
(`Trader.netWorth_difference_le_of_tail_eq`) and FAF's `Exploits.of_boundedDifference`. Kept as
a lemma so an auditor can see which leg is which; `htrans` and `hcomp` are named hypotheses,
never fields of a structure (mandate trap (ii)).
Source: [[bli-program]] §3.1; bli-paper-039; mandate T1 (two-hypothesis form), T1.2
Kind: C
Fidelity: exact for the stated hypotheses
Hyps: (a) except `htrans` (T1.3, discharged in `overlay_isLogicalInductor`) and `hcomp` (T1.4, discharged in `overlay_isLogicalInductor'`), named -/
theorem overlay_isLogicalInductor_of_transfer (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (htrans : ∀ Tr : Trader, EfficientlyComputable Tr →
      EfficientlyComputable (Trader.spliceOn E.expr E.rank_le Tr))
    (hcomp : ComputableMarket (overlay Q ov)) :
    IsLogicalInductor (overlay Q ov) DP :=
  AttemptA.overlay_isLogicalInductor_of_spliceEC E htrans hcomp

/-- **The expressible-overlay transfer theorem** (L1), certificate form. For every logical
inductor `Q` over `DP`, every re-pricing `ov` with an expression map `E` — bodies closed, reading
only prices of sentences small on the day read, at days `≤ k`; un-fired sentences keep `Q`'s
value or are small — and a `SpliceCertificate` for the map (a polynomial-time run-level oracle
whose spec is quantified over every spelling `parseRpn` accepts), the overlay market
`overlay Q ov` is a logical inductor over `DP`, given its computability `hcomp`. One-market:
nothing reads the overlay back into `Q`. `noExploit` is at the criterion's own quantifier: for
**every** `EfficientlyComputable` trader exploiting the overlay, its splice is
`EfficientlyComputable` (`EfficientlyComputable.spliceOn`) and exploits `Q`
(`Trader.spliceOn_exploits`).
Source: [[bli-program]] §3.1; bli-paper-039, bli-paper-031, bli-slides-002/006/030, bli-soto-a-002 (reading A), bli-soto-a-004; mandate T1
Kind: C
Fidelity: exact (the program's §3.1 statement, with the run-level oracle in place of its "(k, ψ) ↦ expr k ψ ∈ FP", Known issue 5, and the guard dropped, Known issue 6)
Hyps: (a) except `C` (the certificate: an `FP` oracle and its spec, the instance's obligation) and `hcomp` (the overlay's computability, discharged in `overlay_isLogicalInductor'`) -/
theorem overlay_isLogicalInductor (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (C : SpliceCertificate E.expr) (hcomp : ComputableMarket (overlay Q ov)) :
    IsLogicalInductor (overlay Q ov) DP :=
  AttemptA.overlay_isLogicalInductor Q DP ov E C hcomp

/-- **T1, the headline of record**: the overlay of a logical inductor by an expression map with
a splice certificate is a logical inductor, with the overlay's computability derived from the
inductor's certificate and a computable table for the re-pricing (T1.4). The remaining
hypotheses — the certificate `C` and the table `hov` — are the instance's obligations
(`bli-assemble` discharges them for the tent kernel's map; `WitnessLia.wCertificate` and
`WitnessLia.wOv_computableTable` are the template). Scope as `overlay_isLogicalInductor`.
Source: [[bli-program]] §3.1; bli-paper-039; mandate T1 (`overlay_isLogicalInductor'`)
Kind: C
Fidelity: exact (as `overlay_isLogicalInductor`, with `hcomp` discharged)
Hyps: (a) except `C` (the certificate) and `hov` (the re-pricing's computable table) — both the instance's obligations; no (b), no (c) -/
theorem overlay_isLogicalInductor' (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (C : SpliceCertificate E.expr) (hov : ComputableTable ov) :
    IsLogicalInductor (overlay Q ov) DP :=
  AttemptA.overlay_isLogicalInductor' Q DP ov E C hov

end Cleanroom.Bli.BliTransfer
