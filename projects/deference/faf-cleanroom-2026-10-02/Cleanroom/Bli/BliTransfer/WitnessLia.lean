import Cleanroom.Bli.BliTransfer.Transfer
import Cleanroom.Bli.BliTransfer.Clamp
import Cleanroom.Bli.BliTransfer.AttemptA.WitnessLia
import Cleanroom.Bli.BliTransfer.AttemptB.WitnessLia

/-!
# `bli-transfer` · WitnessLia: non-vacuity over FAF's logical inductor (T1.5; T3's N+)

The only main module importing the construction (through both attempts' `WitnessLia`, which
import `LogicalInduction.Construction.Paper.TheoremDP` / `LIACompiler`).

**T1.5, the witness of record (attempt A's).** `Q := liaHistory DP` with FAF's
`LIA_is_logical_inductor` (and `paperLIA 𝗜𝚺₁` at the paper's process, whose stages all have
consistent worlds, `paperDP_hworld` — trap (v)); the witness map `wExpr` re-prices, on day `0`,
every atom of the run's reserved family `7` (tag `wTag`; registry row in
`Cleanroom.Bli.BliFound.Tags`) to `1/2`, with `wOv DP` equal to the LIA's own exact quote
elsewhere (Tier B). Its certificate `wCertificate` is the first `SpliceCertificate`: a hand-built
`FP` oracle whose run-level agreement `wRunAgrees` is proved on **every** spelling `parseRpn`
accepts (canonical run, Gödel escape, structured escape). Non-degeneracy is proved, not
assumed: the day-`0` LIA state is a finite table quoting `0` off it, the family is infinite, so
some family atom is priced `0` by `Q` and `1/2` by the overlay (`overlay_ne_lia`); and the
trader side is exercised — the e.c. `familyReader` has a splice that is not the identity
(`familyReader_splice_ne`). `witness_isLogicalInductor` is then the criterion-level theorem T1
at the witness, for every computable process, and `witness_package_paperDP` bundles the full N+
package at `paperDP 𝗜𝚺₁`. Grade **N+**. Disclosed scope: the map fires on day `0` only, where
every atom is large (`sizeBound 0 = 2`), so its oracle needs no size comparison; a map firing on
every day's large family atoms needs the capped double-exponential length test in its oracle —
the shape `bli-assemble`'s oracle adds.

**Attempt B's witness** (`AttemptB.transfer_witness_lia`, kept at attempt level): a two-cell
(finite-support) map on `freshAtom 7 ⟨0, 4^{sizeBound 1}⟩`, days `0`–`1`, with an all-spellings
oracle obtained from FAF's freeze `RunOracle` (`AttemptB.SpliceOracle.ofTable`), the overlay
proved different from the LIA at a day-large sentence for *every* `Q`, and a presented trader
the rewrite changes. It is the N+ of attempt B's class-level theorem, not of the criterion-level
T1 (its oracle interface is attempt B's; see `Certificate.lean`).

**T3's N+ (attempt B's).** `clamp_lia_not_isLogicalInductor`: the LIA over `paperDP 𝗜𝚺₁` is a
logical inductor and its clamp is not — the refutation is not an artifact of a vacuous process.

Sources: mandate T1.5, T3; FAF `Construction/LIACompiler.lean`, `Construction/Paper/TheoremDP.lean`
(`paperLIA` at `:442` — it exists at this pin, contrary to the mandate's remark; attempt B's F-B10),
`Construction/MarketMaker.lean`.
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

export Cleanroom.Bli.BliTransfer.AttemptA
  (wTag wExpr wExpr_rank wExprRun wOracle wRunAgrees wCertificate wOv wMap
   wOv_computableTable familyReader familyReader_ec)

/-- **The overlay changes a day-`0` price of the LIA**: the day-`0` state is a finite table
quoting `0` off its support, the family is infinite, so some family atom is priced `0` by the
LIA and `1/2` by the overlay. Proved by attempt A (`AttemptA.overlay_ne_lia`).
Source: mandate T1.5 (non-degeneracy, trap (iii))
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_ne_lia (DP : DeductiveProcess) :
    ∃ ψ, overlay (liaHistory DP) (wOv DP) 0 ψ ≠ liaHistory DP 0 ψ :=
  AttemptA.overlay_ne_lia DP

/-- **The trader side is exercised**: the efficiently computable `familyReader` (every day,
`price ⌜a⌝ 0` for the family atom `a = Nat.pair wTag 0`, on `⊥`) has a splice that is not the
identity on any day. Proved by attempt A (`AttemptA.familyReader_splice_ne`).
Source: mandate T1.5 (trader side)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem familyReader_splice_ne (n : ℕ) :
    ((Trader.spliceOn wExpr wExpr_rank familyReader).strat n).trades ≠
      (familyReader.strat n).trades :=
  AttemptA.familyReader_splice_ne n

/-- **T1 at the witness, over FAF's logical inductor**: for every computable deductive process,
the day-`0` family-`7` overlay of `liaHistory DP` is a logical inductor over `DP` — the headline
of record `overlay_isLogicalInductor'` with `Q := liaHistory DP`, `E := wMap DP`,
`C := wCertificate`, `hov := wOv_computableTable DP hDP`. Proved by attempt A.
Source: mandate T1.5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witness_isLogicalInductor (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (overlay (liaHistory DP) (wOv DP)) DP :=
  AttemptA.witness_isLogicalInductor DP hDP

/-- **The full N+ package at the paper's process over `𝗜𝚺₁`**: the LIA is a logical inductor
(`paperLIA`); every stage has a consistent world (`paperDP_hworld`, so the criterion's world
quantifier is not vacuous — trap (v)); the overlay changes a day-`0` price; the family reader is
efficiently computable and rewritten non-trivially on every day; and the overlay is a logical
inductor. Every conjunct is a theorem of this package or of FAF; nothing is assumed.
Source: mandate T1.5 (N+ for T1, both senses: a large-sentence price changed, an e.c. trader rewritten)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem witness_package_paperDP :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
    (∃ ψ, overlay (liaHistory (paperDP 𝗜𝚺₁)) (wOv (paperDP 𝗜𝚺₁)) 0 ψ ≠
      liaHistory (paperDP 𝗜𝚺₁) 0 ψ) ∧
    EfficientlyComputable familyReader ∧
    (∀ n, ((Trader.spliceOn wExpr wExpr_rank familyReader).strat n).trades ≠
      (familyReader.strat n).trades) ∧
    IsLogicalInductor (overlay (liaHistory (paperDP 𝗜𝚺₁)) (wOv (paperDP 𝗜𝚺₁))) (paperDP 𝗜𝚺₁) :=
  ⟨paperLIA 𝗜𝚺₁, paperDP_hworld 𝗜𝚺₁, AttemptA.overlay_ne_lia _, AttemptA.familyReader_ec,
    AttemptA.familyReader_splice_ne, AttemptA.witness_isLogicalInductor_paperDP⟩

/-- **T3's refutation is not vacuous**: the LIA over `paperDP 𝗜𝚺₁` is a logical inductor and its
clamp is not. Proved by attempt B (`AttemptB.clamp_lia_not_isLogicalInductor`, over the same
`clamp`, `Defs.attemptB_clamp_eq`).
Source: mandate T3 (N+ for the refutation)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem clamp_lia_not_isLogicalInductor :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    ¬ IsLogicalInductor (clamp (liaHistory (paperDP 𝗜𝚺₁))) (paperDP 𝗜𝚺₁) :=
  AttemptB.clamp_lia_not_isLogicalInductor

end Cleanroom.Bli.BliTransfer
