import Cleanroom.Li.LiCoupledPair.A.SigmaWitness
import Cleanroom.Li.LiCoupledPair.B.ConditionedWitness

/-!
# `li-coupled-pair` · QuotePackage: T1 of record — the cross-market quote package discharged

Reconciled module (namespace `Cleanroom.Li.LiCoupledPair`) for [[li-coupled-pair-mandate]] T1.
`li-quote-lane` built `CrossQuotePackage H DPA f X Y` as a *hypothesis package* (its `reflected`
field a (c)); the two angles discharged it independently, by different routes, and both are kept:

* **Of record (angle A, the Σ₁ discharge): `crossQuotePackage_sigma`.** Over `paperDP T` itself —
  nothing adjoined, no ledger, zero (c): `A`'s quotation code names `H`'s exact rational deferred
  expectation (`RationalQuoteCode.ofComputable` at `MarketComputation.expectQuoteAt`), and FAF's
  Σ₁-completeness makes every completed-theory world of `paperDP T` value it there. **Timing:
  none** — the quotation literal is decided at a dovetail stage nobody controls; fa-v3 (A3) asks
  for exactly that ("no bound on how long the construction takes to run"). Witness
  `sigmaPair_paper` (N+, over `paperDP 𝗜𝚺₁`, `H = paperOneWayPair.H`).
* **Variant kept (angle B, the conditioning route): `crossQuotePackage_clocked`.** Over
  `DPA0 ∪ prefixProcess (clockedSeq c₁ σ)`: the quote literal is adjoined at a *clocked* position,
  never before `(σ 0).e n`, and the certificate the route needs — `MachineSentenceCodes` of the
  conditioning sequence, li-quote-lane's (c) `hψ` — is the theorem `clockedSeq_codes`, with no
  hypothesis on the recorded table. **Timed, ledger-recorded** determinacy (Fidelity `variant`),
  which the Σ₁ discharge cannot give; the price is that the stage is the literal's clocked cost
  (FAF's `evaln` fuel), not a stage the publisher picks. **"Timed" is a lower bound only** (repair
  round 1, audit r1 fidelity B2): `B.clocked_absent_before_schedule` says the day-`n` literal is in
  no stage before `(σ j).e n`, and `B.clockedSeq_eventually` that it is written at *some* position
  `t = ⟨ledgerPayload j n c, d⟩` once the clock covers the polarity program's run — a position at
  least the payload and at least that program's fuel; **no upper bound on the stage**, and later
  than any scheduled ledger (`B.paperConditionedPair_processes_differ`: `H`'s scheduled ledger
  holds the threshold-`c` literal at stage `c`, the clocked record not before `c⁴`). A dependent
  needing "decided *by* stage `σ(n)`" takes li-quote-lane's mirror ledger (`ledgerLuv_decided_by`,
  `crossQuotePackage_mirror`), not this. Witness `paperConditionedPair` (N+).

The two witnesses read the **same** reader `H = paperOneWayPair.H` at the same `XH = cleanX` and
`f = succDeferral` (`sigmaPair_H_eq_conditionedPair_H`): the Σ₁ and the clocked package are two
determinacies of one realized expectation sequence. Both are **one-way in timing**: `H` reads
`A` at controlled stages, `A`'s side reads `H` only through determinacy (A) or a clocked record
(B); neither is the plan's two-way pair (`TwoWay.lean`). Consumer rows (`A.sigma_determinedViaTheory`,
`A.sigma_worldValued`, `A.sigma_approxDetermined_mesh`, `A.sigma_determinedViaTheory_affineImage`,
`A.sigma_expect_provind_ge`; `B.clocked_absent_before_schedule`, `B.clockedProcess_hworld`) are
cited from the attempts in the ledger, not restated.
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane
open Nat.Partrec (Code)

/-! ## A. T1.1 of record: the Σ₁ discharge -/

export Cleanroom.Li.LiCoupledPair.A (sigmaValue sigmaQuoteCode sigmaPair_paper witnessMH
  witnessHProcess)

/-- **T1.1 (headline of record). The cross-market quote package is discharged over `paperDP T`:**
for any market `H` with an exact market program `MH`, any e.c. LUV family `XH` and any deferral
function `f`, `CrossQuotePackage H (paperDP T) f XH (sigmaQuoteCode T MH XH hX f).luv` — `A`'s
tag-2 quotation LUVs `⌜𝔼^H_{f n}(XH n)⌝` are e.c. and every completed-theory world of `paperDP T`
values them at `H`'s realized expectation. No hypothesis beyond `XH`'s e.c. certificate and
`[T.Δ₁] [𝗥₀ ⪯ T]`; zero (c). **Timing: none** (determinacy via the completed theory). A dependent
needing "decided *by* stage `σ(n)`" takes li-quote-lane's mirror ledger (`ledgerLuv_decided_by`,
`crossQuotePackage_mirror`, `ledgerLuv_absent_before_payout`), not this and **not**
`crossQuotePackage_clocked`, which gives only a lower bound (not before `(σ 0).e n`) and eventual
decision at the clocked cost, with no stage bound (repair round 1, audit r1 fidelity B2).
**Carries no world** (pair with `paperDP_hworld T`, as `sigmaPair_paper` does). Proved by
angle A (`A.crossQuotePackage_sigma`). Scope: one-way in timing, two-way in determinacy.
Source: [[faithful-acceleration]] §4(II) (root-fa-002); [[fa-positive-results-corrected-v3]] (A3); anson-2-014; [[route-sparse-schedule]] §10 (S1) (vq-wiki-029)
Kind: C
Fidelity: exact (determinacy); timing: none
Hyps: (a) none -/
theorem crossQuotePackage_sigma (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]
    {H : History} (MH : MarketComputation H) (XH : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq XH) (f : DeferralFunction) :
    CrossQuotePackage H (paperDP T) f XH (sigmaQuoteCode T MH XH hX f).luv :=
  A.crossQuotePackage_sigma T MH XH hX f

/-! ## B. T1.2: the quote names a machine; `H` is what it computes -/

/-- **T1.2.** The LIA's price is exactly the quote of its named program (`liaMarketComputation`),
cast to `ℝ`: "the quote names a *machine*; `H` is what it computes". Angle A
(`A.liaHistory_eq_machine`).
Source: plan rigor critique 17; [[route-negative-introspective]] §4.3; FAF `MarketComputation.quote_exact`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaHistory_eq_machine (DPH : DeductiveProcess) (hH : ComputableDeductiveProcess DPH)
    (n : ℕ) (φ : Sentence) :
    liaHistory DPH n φ = ((liaMarketComputation DPH hH).quote n (Encodable.encode φ) : ℝ) :=
  A.liaHistory_eq_machine DPH hH n φ

/-- **T1.2, rational form.** Angle A (`A.liaQuote_eq_machine`).
Source: plan rigor critique 17
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaQuote_eq_machine (DPH : DeductiveProcess) (hH : ComputableDeductiveProcess DPH)
    (n : ℕ) (φ : Sentence) :
    liaQuote DPH n φ = (liaMarketComputation DPH hH).quote n (Encodable.encode φ) :=
  A.liaQuote_eq_machine DPH hH n φ

/-- **T1.2, expectation form.** `H`'s day-`m` expectation of `X n` is the cast of its program's
exact rational `expectQuoteAt X n m`. Angle A (`A.liaHistory_expect_eq_machine`).
Source: plan rigor critique 17; FAF `MarketComputation.expectQuoteAt_cast`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaHistory_expect_eq_machine (DPH : DeductiveProcess)
    (hH : ComputableDeductiveProcess DPH) (X : ℕ → LUV) (n m : ℕ) :
    (X n).expect (liaHistory DPH) m = ((liaMarketComputation DPH hH).expectQuoteAt X n m : ℝ) :=
  A.liaHistory_expect_eq_machine DPH hH X n m

/-! ## C. T1.3: the witness of record, and its grounds -/

/-- `sigmaPair_paper`'s `H` is li-quote-lane's one-way reader over `paperDP 𝗜𝚺₁`, definitionally.
Source: mandate T1.3
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sigmaPair_paper_H : sigmaPair_paper.H = paperOneWayPair.H := A.sigmaPair_paper_H

/-- `sigmaPair_paper`'s `A` is FAF's paper LIA, definitionally.
Source: mandate T1.3
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sigmaPair_paper_A : sigmaPair_paper.A = liaHistory (paperDP 𝗜𝚺₁) := A.sigmaPair_paper_A

/-- **`reflected` is inhabited at the witness** (audit r2 adversarial N5). `CrossQuotePackage.reflected`
quantifies over worlds consistent with the *whole* completed theory of `paperDP 𝗜𝚺₁`
(`PCWorld.ConsistentWithTheory`), and `sigmaPair_paper`'s `hworldA := paperDP_hworld` gives only
a world per stage. FAF's `paperDP_nonvacuous` (a model of `𝗜𝚺₁` is consistent with every stage)
supplies a theory-world, which then values `A`'s quotation LUV `⌜𝔼^H_{n+1}(cleanX n)⌝` at `H`'s
realized expectation: the determinacy clause of `crossQuotePackage_sigma` is not vacuous at the
witness. (The auditor's probe `SigmaReflectedInhabited.lean`, made part of the package.)
Source: mandate T1.3 (non-vacuity); FAF `paperDP_nonvacuous`
Kind: N+
Fidelity: n/a (non-vacuity ground)
Hyps: (a) none -/
theorem sigma_reflected_inhabited (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) ∧
      v.ValuesAt (sigmaPair_paper.code.luv n) ((cleanX n).expect paperOneWayPair.H (n + 1)) := by
  obtain ⟨v, hv⟩ := paperDP_nonvacuous (T := 𝗜𝚺₁)
  exact ⟨v, hv, sigmaPair_paper.package.reflected n v hv⟩

/-! ## D. The variant kept: T1 by conditioning on a clocked record (angle B) -/

export Cleanroom.Li.LiCoupledPair.B (clockedSeq clockedProcess clockedCondition clockedHistory
  gateVal ConditionedPair paperConditionedPair)

/-- **The conditioning route's certificate, discharged** (angle B's result): the clocked quote
record `clockedSeq c₁ σ` is `MachineSentenceCodes` for *every* polarity program `c₁` and every
poly-time schedule `σ`, with **no hypothesis on the recorded table**. This is the `hψ` of
li-quote-lane's `conditioningRoute_inductor` (its one (c)), now a theorem: FAF's fuel calculus
cannot catch a timeout (`Fueled` requires success), but FAF's one exported timeout-tolerant
polynomial-time evaluation (`TraderMachine.traderOutput_mem_FP`, read through
`B.clockDigit_ruler`) can, so the position pays the quote's `evaln`-fuel cost. Proved by angle B
(`B.clockedSeq_codes`).
Source: anson-2-007 (the `e ≥ Λ` argument); li-quote-lane findings F8 (corrected: findings R-1); mandate angle B
Kind: P
Fidelity: variant: the source's cost-domination schedule is realized as the clock (FAF's fuel), not as a runtime bound FAF lacks; no stage bound (a literal's position is at least its payload and at least the polarity program's fuel; later than any scheduled ledger)
Hyps: (a) none (`hσ` is the schedule's own poly-time certificate, discharged at `succ`, `sameDay`, `payoutSchedule`) -/
theorem clockedSeq_codes (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) :
    MachineSentenceCodes (clockedSeq c₁ σ) :=
  B.clockedSeq_codes c₁ σ hσ

/-- **`A = P | ψ_H` is a logical inductor over the clocked process, no certificate hypothesis**:
FAF's `thm:scon` at the clocked sequence with `clockedSeq_codes` as its premise. Angle B
(`B.clocked_inductor`). FAF's `conditionalQuote` is `1` at a zero-price condition (disclosed;
nothing is stated about the conditioned prices). Scope: one-way (`A` reads a fixed table).
Source: anson-2-002 (the conditioning construction); mandate angle B; FAF `lic_conditioned_growing_ofSequence`
Kind: L (one application of FAF's endpoint; the content is `clockedSeq_codes`)
Fidelity: variant: plain trader class; clock as the lag (a lower bound on the literal's stage, no upper bound); FAF's capped conditional
Hyps: (a) none -/
theorem clocked_inductor (P : History) (DPA0 : DeductiveProcess) [IsLogicalInductor P DPA0]
    (c₁ : Code) (σ : ℕ → PublicationSchedule)
    (hσ : UnaryRuler fun p => (σ p.unpair.1).e p.unpair.2) :
    IsLogicalInductor (clockedHistory P c₁ σ) (clockedProcess DPA0 c₁ σ) :=
  B.clocked_inductor P DPA0 c₁ σ hσ

/-- **T1 by conditioning (the timed variant): the cross-market quote package is a theorem over
the clocked process**, for any `H` with a market program, any base `DPA0` and any program `c₁`
for the polarity of `H`'s realized expectations (`B.quoteGateCode_exists` supplies one). The
family `n ↦ ledgerLuv 0 n` is e.c. and every completed-theory world of
`DPA0 ∪ prefixProcess (clockedSeq c₁ σ)` values it at `𝔼^H_{f n}(XH n)`. **Timed, as a lower
bound only**: the day-`n` literal is never in `A`'s stage before `(σ 0).e n`
(`B.clocked_absent_before_schedule`); it is decided eventually (`B.clockedSeq_eventually`) at a
position at least its payload and at least the polarity program's fuel — **no stage bound**, and
later than any scheduled ledger (`B.paperConditionedPair_processes_differ`). A dependent needing
"decided *by* stage `σ(n)`" takes li-quote-lane's mirror ledger, not this (repair round 1, audit
r1 fidelity B2). Carries no world (pair with `B.clockedProcess_hworld`). Angle B
(`B.crossQuotePackage_clocked`). Scope: one-way (`A` reads `H`).
Source: [[faithful-acceleration]] §4(II) (root-fa-002); anson-2-014; [[deference-in-logical-induction-v6]] §5.2; mandate T1.1 (angle B)
Kind: C
Fidelity: variant: timed, ledger-recorded determinacy in place of `Γ_A`-provable determinacy; the stage is the clocked cost — not before `(σ 0).e n`, no stage bound, later than any scheduled ledger
Hyps: (a) none (`hc`: `c₁` computes the table's polarity, supplied by `B.quoteGateCode_exists`) -/
theorem crossQuotePackage_clocked {H : History} (MH : MarketComputation H) (XH : ℕ → LUV)
    (f : DeferralFunction) (DPA0 : DeductiveProcess) (c₁ : Code)
    (hc : ∀ p, c₁.eval p = Part.some (gateVal (fun _ n => MH.expectQuoteAt XH n (f.f n)) p))
    (σ : ℕ → PublicationSchedule) :
    CrossQuotePackage H (clockedProcess DPA0 c₁ σ) f XH (fun n => ledgerLuv 0 n) :=
  B.crossQuotePackage_clocked MH XH f DPA0 c₁ hc σ

/-! ## E. The two witnesses read the same reader -/

/-- **Reconciliation: the Σ₁ witness and the clocked witness are two determinacies of one
realized expectation sequence.** `sigmaPair_paper.H` and `paperConditionedPair.H` are the same
market — li-quote-lane's one-way reader `paperOneWayPair.H` over `paperDP 𝗜𝚺₁` — read at the
same `XH = cleanX` and `f = succDeferral`; angle A's `paperDP 𝗜𝚺₁` determines its expectations
through Σ₁-completeness with no stage bound, angle B's clocked process records them at clocked
positions after `payoutSchedule`.
Source: mandate "Reconciler" (ships both witnesses)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sigmaPair_H_eq_conditionedPair_H : sigmaPair_paper.H = paperConditionedPair.H :=
  A.sigmaPair_paper_H.trans B.paperConditionedPair_H.symm

end Cleanroom.Li.LiCoupledPair
