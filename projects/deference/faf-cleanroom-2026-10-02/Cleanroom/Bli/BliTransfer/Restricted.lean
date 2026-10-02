import Cleanroom.Bli.BliTransfer.Defs
import Cleanroom.Bli.BliTransfer.AttemptA.Restricted
import Cleanroom.Bli.BliTransfer.AttemptA.Witnesses

/-!
# `bli-transfer` · Restricted: the restricted-class transfer (T2, disclosed `(c)`)

L4: if `Q` is a logical inductor, no `RestrictedEC` trader — efficiently computable, every
price leaf reading a sentence small on the day read — exploits `overlay Q ov`, for **every**
re-pricing `ov` in `[0,1]`: no expression map, no certificate. This is bli-slides-002's reading
"traders never read large prices", and it is **not the criterion**: `RestrictedEC` is a proper
subclass of `EfficientlyComputable` (`restrictedEC_separation`: an e.c. trader may read the
day-`0` price of a sentence large on day `0`). No `IsLogicalInductor` conclusion is stated here —
`IsLogicalInductor` quantifies over `EfficientlyComputable`, and that is T1.

Both attempts proved T2 with the same witnesses (a day-`n ≥ 1` reader of `price ⌜aₙ⌝ n`, nothing
on day `0`; and the large reader of `price ⌜a_{4^{sizeBound 0}}⌝ 0`), certified through FAF's
`EfficientlyComputable.ofTradeBlocksBig`. The statements of record are attempt A's; attempt B's
(`AttemptB.restrictedEC_not_exploits_overlay`, `AttemptB.restrictedWitness_restrictedEC`,
`AttemptB.largeReader_not_restrictedEC`) are the independent confirmation, over a copy of the
class shown identical in `Defs.attemptB_restrictedEC_iff`.

Sources: bli-slides-002; [[bli-program]] `C:I4`; mandate T2.
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

export Cleanroom.Bli.BliTransfer.AttemptA
  (EF.denoteWith_congr_prices Strategy.value_congr_of_small
   restrictedCount restrictedWitness restrictedWitness_ec restrictedWitness_day_one
   largeReader largeReader_ec)

/-- **Restricted-class transfer (L4) — for the restricted class `RestrictedEC`, not the
criterion.** If `Q` is a logical inductor, no `RestrictedEC` trader exploits `overlay Q ov`, for
every `[0,1]`-valued `ov`: the trader is its own rewrite, every leaf reads a small price the
overlay leaves alone, the bridge lemma makes its traded sentences small from some day on, and
the finite-prefix accounting transports exploitation to `Q`. Proved by attempt A
(`AttemptA.restrictedEC_not_exploits_overlay`); attempt B independently.
Source: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`; mandate T2
Kind: C
Fidelity: variant: (c) quantified over `RestrictedEC`, a proper subclass of `EfficientlyComputable`
Hyps: (a) `hQ`, `hov`; (c) `hTr : RestrictedEC Tr` — the restricted class, not the criterion's class -/
theorem restrictedEC_not_exploits_overlay (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ)
    (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) (Tr : Trader) (hTr : RestrictedEC Tr) :
    ¬ Tr.Exploits (overlay Q ov) DP :=
  AttemptA.restrictedEC_not_exploits_overlay Q DP ov hov Tr hTr

/-- **N+ for `RestrictedEC`**: the witness (day-`n ≥ 1` trade `(price ⌜aₙ⌝ n, ⌜aₙ⌝)`, nothing on
day `0`) is efficiently computable and in the class, with a genuine day-varying price leaf.
Source: mandate T2 (N+ for the class)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem restrictedWitness_restricted : RestrictedEC restrictedWitness :=
  AttemptA.restrictedWitness_restricted

/-- **The separation**: `RestrictedEC` is a proper subclass of `EfficientlyComputable` — the
large reader (every day, one share of `⊥` at the coefficient `price ⌜a_{4^{sizeBound 0}}⌝ 0`) is
efficiently computable but reads a day-`0` price of a sentence large on day `0`
(`bli-found`'s `largeOn_witness`). Without it the `(c)` of T2 would be undocumented.
Source: mandate T2 (separation)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem restrictedEC_separation :
    EfficientlyComputable largeReader ∧ ¬ RestrictedEC largeReader :=
  AttemptA.restrictedEC_separation

end Cleanroom.Bli.BliTransfer
