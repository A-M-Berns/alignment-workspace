import Cleanroom.Li.LiCoupledPair.A.Open

/-!
# `li-coupled-pair` · TwoWay: T4.2, T4.3, T5 — the sealed-sibling system and the two-way pair

Reconciled module (namespace `Cleanroom.Li.LiCoupledPair`) for [[li-coupled-pair-mandate]] T4.2,
T4.3 and T5 — all angle A's (angle B established, from the conditioning side, that it *cannot*
reach them: conditioning transforms a fixed inductor, so a market reading the conditioned `A`
reads a function of its own expectations; `B.ConditionedPair` is `A = P | ψ_H` with `H` reading
**`P`**, not `A`, and is tagged "not the two-way pair"; findings R-2).

**What is unconditional** (no hypothesis): the staggered joint recursion on the day
(`jointDay`, `sealedDay`) at FAF's own day step, the processes and markets of record
(`jointDPA`/`jointDPH`, `sealedDPA`/`sealedDPH`/`sealedSib`), and the **identification**
`jointDay_states` / `sealedDay_states`: FAF's semantic LIA over each process of record *is* the
recursion's state sequence — the source's "recurse on the shared clock" realized with no Brouwer
step beyond FAF's own. Every `TwoWayPair` / `SealedSiblingSystem` field but the inductor facts is
derived (`twoWayPair_of_inductors`, `sealedSystem_of_inductors`).

**What waits on one named hypothesis:** the inductor facts, because `LIA_is_logical_inductor`
needs `ComputableDeductiveProcess` of the *jointly defined* process, i.e. FAF's bounded LIA
evaluator computable **uniformly in the stage table** — which FAF proves as the `private`
`liaPrefixFromStagesAtFuel_prim` (`Construction/LIACompiler.lean:3665`) and does not export.
Named `UniformLIAEvaluator` (`DefsHeavy.lean`), graded **(b)**; `uniform_of_primrec` discharges
it from the private lemma's statement in one line. Under it: `contract_computable` (T4.2),
`sealedA_inductor`/`sealedHplus_inductor`/`sealedSib_inductor`, `sealedSystem_of_uniform` (T4.3),
`jointA_inductor`/`jointH_inductor`, `twoWayPair_of_uniform` (T5.1), and the conditional forms of
both OPEN rows (`sealedSystem_exists_of_uniform`, `twoWayPair_exists_of_uniform`). Every row reads
`partial: UniformLIAEvaluator (b)`. **Conflict flagged** (report): STANDARDS §1 says a lemma FAF
keeps private is *re-proved here*; the mandate waived that for this 4,041-line compiler lemma
and graded it (b). The reconciler keeps (b) and the flag.

**The two OPEN rows of record** (`li-coupled-pair-open.txt`): `twoWayPair_exists` (T5.2) and
`sealedSystem_exists` (T4.3), the unconditional forms over `paperDP 𝗜𝚺₁`, stated in `A/Open.lean`
and pointed to from here under the package's names. Their N+ witnesses under the hypothesis
(`paperTwoWayPair_of_uniform`, `paperSealedSystem_of_uniform`) have unconditional grounds
(`paperTwoWay_processes_differ'`, `paperSealed_sibling_succ_ne`, the both-polarity lemmas), so an
API fix makes both rows `proved` with no further work. Every two-way row elsewhere in the run
cites these names (plan §0.4 rule 1).
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane

/-! ## A. The recursions, processes and markets of record (angle A, re-exported) -/

export Cleanroom.Li.LiCoupledPair.A (TwoWaySpec jointDay jointDPA jointDPH jointA jointH aA aH
  jointDay_dA_eq jointDay_dH_eq joint_aA_eq joint_aH_eq joint_determinedA joint_determinedH
  joint_hworldA joint_hworldH twoWayPair_of_inductors liaPrefixFromStages
  liaPrefixFromStages_computable jointStep jointStep_spec jointDay_computable
  twoWayPair_of_uniform paperTwoWaySpec paperTwoWayPair_of_uniform paperTwoWay_processes_differ
  paperTwoWay_both_polarities
  SealedSpec sealedDay aS sealedY sealedDPA sealedA sealedDPH sealedHplus sealedSib
  siblingQuote_congr sealedDay_d_eq sealed_a_eq sealedY_eq sealed_determinedA sealed_determinedH
  sealed_determinedSib sealed_hworldA sealed_hworldH sealed_hworldSib sealedSystem_of_inductors
  liaStates_computable_param sealedStep sealedStep_spec sealedDay_computable sealedY_computable
  sealedSystem_of_uniform paperSealedSpec paperSealedSystem_of_uniform siblingProcess_succ_ne
  paperSealed_processes_differ paperSealed_both_polarities)

/-! ## B. T5.1: the two-way pair — the identification (unconditional) and the inductors (b) -/

/-- **T5.1, identification (unconditional): FAF's semantic LIA over each process of record is
the staggered joint recursion's state sequence.** Day `t` computes `A`'s stage from `H`'s past
states, `A`'s state by FAF's `MarketMaker` of `TradingFirmAtFromStages` against the stage table
so far, then `H`'s stage from `A`'s states *including* the new one, then `H`'s state; the stagger
`f n < (σ j).e n` makes every published entry readable. No fixed `DeductiveProcess`, no Brouwer
step beyond FAF's own. Angle A (`A.jointDay_states`). Scope: two-way.
Source: mandate T5.1; [[deference-in-logical-induction-v6]] §5.2 (root-deference-037); anson-017 ("delay by one stage, recurse on the shared clock")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem jointDay_states (P : TwoWaySpec) :
    ∀ t, liaStates (jointDPA P) t = (jointDay P t).1.2 ∧
      liaStates (jointDPH P) t = (jointDay P t).2.2 :=
  A.jointDay_states P

/-- **T5.1, `A`'s side: the market `A` of the two-way pair is a logical inductor over its
process, which reads `H`** — under `UniformLIAEvaluator`. Angle A (`A.jointA_inductor`).
Source: mandate T5.1; [[deference-in-logical-induction-v6]] §5.2; [[route-sparse-schedule]] §9 (vq-wiki-067)
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` (FAF private `liaPrefixFromStagesAtFuel_prim`; API request) -/
theorem jointA_inductor (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    IsLogicalInductor (jointA P) (jointDPA P) :=
  A.jointA_inductor P hU hA0 hH0 hq he hX hσ

/-- **T5.1, `H`'s side: the market `H` of the two-way pair is a logical inductor over its
process, which reads `A`** — under `UniformLIAEvaluator`. Angle A (`A.jointH_inductor`).
Source: mandate T5.1
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem jointH_inductor (P : TwoWaySpec) (hU : UniformLIAEvaluator)
    (hA0 : ComputableDeductiveProcess P.DPA0) (hH0 : ComputableDeductiveProcess P.DPH0)
    (hq : Computable fun p : ℕ × ℕ => P.quotedA p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (P.e p.1).e p.2)
    (hX : LUV.MachineThresholdCodeSeq P.XH)
    (hσ : Computable fun p : ℕ × ℕ => (P.σ p.1).e p.2) :
    IsLogicalInductor (jointH P) (jointDPH P) :=
  A.jointH_inductor P hU hA0 hH0 hq he hX hσ

/-- **T5.2's statement under the hypothesis (proved):** there is a two-way pair over `paperDP 𝗜𝚺₁`
on both sides with the witness's data pinned — `quotedA = witnessQuoted`, next-day publication,
`XH = cleanX`, `f = succDeferral`, settlement `payoutSchedule`, payout after the lookahead
(`paperTwoWayPair_of_uniform`). Angle A (`A.twoWayPair_exists_of_uniform`). Repair round 1 pinned
`quotedA`, `e`, `σ` (audit r1 fidelity N2), so the row cannot be met by a degenerate pair.
Source: mandate T5.2/T5.3
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem twoWayPair_exists_of_uniform (hU : UniformLIAEvaluator) :
    ∃ p : TwoWayPair, p.DPA0 = paperDP 𝗜𝚺₁ ∧ p.DPH0 = paperDP 𝗜𝚺₁ ∧ p.quotedA = witnessQuoted ∧
      p.e = (fun _ => PublicationSchedule.succ) ∧ p.XH = cleanX ∧ p.f = succDeferral ∧
      p.σ = (fun _ => payoutSchedule) ∧ ∀ j n, p.f.f n < (p.σ j).e n :=
  A.twoWayPair_exists_of_uniform hU

/-- **OPEN (T5.2): the two-way pair exists unconditionally** over `paperDP 𝗜𝚺₁`, with the witness's
data pinned (`quotedA = witnessQuoted`, next-day publication, `XH = cleanX`, `f = succDeferral`,
settlement `payoutSchedule`, payout after the lookahead). The package's name for angle A's listed
OPEN row `A.twoWayPair_exists` (`A/Open.lean`): open because the only missing input is
`UniformLIAEvaluator` (`twoWayPair_exists_of_uniform`), which FAF proves as a private lemma. Every
two-way row in the run cites this name. Listed in `li-coupled-pair-open.txt`.
Source: [[route-sparse-schedule]] §10 hypothesis 7 (vq-wiki-067); [[route-negative-introspective]] §4.4 (vq-wiki-2-017 (b)); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: OPEN
Fidelity: variant: plain trader class
Hyps: n/a (open; rests on the listed `A.twoWayPair_exists`) -/
theorem twoWayPair_exists :
    ∃ p : TwoWayPair, p.DPA0 = paperDP 𝗜𝚺₁ ∧ p.DPH0 = paperDP 𝗜𝚺₁ ∧ p.quotedA = witnessQuoted ∧
      p.e = (fun _ => PublicationSchedule.succ) ∧ p.XH = cleanX ∧ p.f = succDeferral ∧
      p.σ = (fun _ => payoutSchedule) ∧ ∀ j n, p.f.f n < (p.σ j).e n :=
  A.twoWayPair_exists

/-- **N+ grounds for T5.3 (unconditional): the two jointly defined processes of the paper
witness differ** at some stage (`H`'s process holds `A`'s day-`(s−1)` quote literal published the
next day; `A`'s process publishes `H`'s day-`(s−1)` entries at `s + 1`; `paperDP 𝗜𝚺₁` is
cleanroom-free). Angle A (`A.paperTwoWay_processes_differ'`).
Source: mandate T5.3 ("prove the two jointly defined processes differ")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperTwoWay_processes_differ' :
    ∃ s, (jointDPH paperTwoWaySpec).D s ≠ (jointDPA paperTwoWaySpec).D s :=
  A.paperTwoWay_processes_differ'

/-! ## C. T4.2 and T4.3: the sealed-sibling system -/

/-- **T4.3, identification (unconditional): FAF's semantic LIA over `A`'s process of record is
the `A`-side recursion's state sequence.** The sealed system needs only an `A`-side recursion:
the siblings read a *fixed* table (`A`'s prices), and `Y k` depends on `A`'s states at days `< k`
only because sibling `k` is **frozen** at day `k` (`siblingQuote_congr`) — freezing, not delay,
makes it well-founded (findings F12). Angle A (`A.sealedDay_states`). Scope: two-way.
Source: mandate T4.3 ("identify the components with `liaStates` of the final processes"); [[frozen-deliberation-deference-v6]] §4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem sealedDay_states (S : SealedSpec) : ∀ t, liaStates (sealedDPA S) t = (sealedDay S t).2 :=
  A.sealedDay_states S

/-- **T4.2: the contract `n ↦ Y_n := H^{[n]}_{F n}(P^{(n)})` is computable** for computable
`base`, `a`, `e`, `F`, `P` — under `UniformLIAEvaluator` (the stage list of `siblingProcess … n`
is computable uniformly in `n`, the day-`F n` state is the total evaluator's last entry, the
quote is read off it). Where the corpus says "computing `Y_n` costs about `R_H(F(n))`": FAF has
no cost, only computability. Angle A (`A.contract_computable`). Scope: one-way per `n`.
Source: [[frozen-deliberation-deference-v6]] §5 (anson-016, the cost of `Y_n`); mandate T4.2
Kind: C
Fidelity: variant: computability, no cost model (li-quote-lane F8)
Hyps: (b) `UniformLIAEvaluator` -/
theorem contract_computable (hU : UniformLIAEvaluator) {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) {a : ℕ → ℕ → ℚ}
    (ha : Computable fun p : ℕ × ℕ => a p.1 p.2) {e : ℕ → PublicationSchedule}
    (he : Computable fun p : ℕ × ℕ => (e p.1).e p.2) {F : ℕ → ℕ} (hF : Computable F)
    {P : ℕ → Sentence} (hP : Computable P) :
    Computable fun n => liaQuote (siblingProcess base a e n) (F n) (P n) :=
  A.contract_computable hU hbase ha he hF hP

/-- **T4.3, `A`'s side: `A` is a logical inductor over its base plus the contract ledger settled
to the siblings' exact quotes** — under `UniformLIAEvaluator`. Angle A (`A.sealedA_inductor`).
Source: [[frozen-deliberation-deference-v6]] §4 (anson-017); [[deference-in-logical-induction-v6]] §5.2; mandate T4.3
Kind: C
Fidelity: variant: plain trader class; exact rational contract
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedA_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    IsLogicalInductor (sealedA S) (sealedDPA S) :=
  A.sealedA_inductor S hU hbase hA0 hq he hc hσ

/-- **T4.3, `H⁺`'s side: `H⁺` is a logical inductor over the full quote ledger of `A`** — under
`UniformLIAEvaluator` (only because `A`'s table is). Angle A (`A.sealedHplus_inductor`).
Source: mandate T4.3
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedHplus_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) :
    IsLogicalInductor (sealedHplus S) (sealedDPH S) :=
  A.sealedHplus_inductor S hU hbase hA0 hq he hc hσ

/-- **T4.3, the family: every sealed sibling `H^{[N]}` is a logical inductor over its frozen
process at `A`'s table of record** — under `UniformLIAEvaluator` (only because `A`'s table is).
Angle A (`A.sealedSib_inductor`).
Source: mandate T4.3; [[frozen-deliberation-deference-v6]] §3–§4 (anson-016/017)
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedSib_inductor (S : SealedSpec) (hU : UniformLIAEvaluator)
    (hbase : ComputableDeductiveProcess S.base) (hA0 : ComputableDeductiveProcess S.DPA0)
    (hq : Computable fun p : ℕ × ℕ => S.quoted p.1 p.2)
    (he : Computable fun p : ℕ × ℕ => (S.e p.1).e p.2) (hc : Computable S.contract)
    (hσ : Computable S.σ.e) (N : ℕ) :
    IsLogicalInductor (sealedSib S N) (siblingProcess S.base (aS S) S.e N) :=
  A.sealedSib_inductor S hU hbase hA0 hq he hc hσ N

/-- **T4.3's statement under the hypothesis (proved):** there is a sealed-sibling system over
`paperDP 𝗜𝚺₁` (both bases) with same-day publication, horizon `succDeferral`, settlement
`payoutSchedule`, `quoted = witnessQuoted` and `contract = witnessQuoted 0`
(`paperSealedSystem_of_uniform`; every field pinned since repair round 1, audit r1 fidelity N2;
the siblings pinned to FAF's LIA on each frozen process since repair round 2, audit r2
adversarial N1, so that the carrier's `Y_eq` reads `Y n = sib n (F n) (contract n)`).
Same-day publication is forced by FAF's stock of deferral functions (findings F11) and is
well-founded for the sealed system (F12). The channel is a `variant` of the source's: `A` quotes
the base propositions `⟨0, ⟨j, n⟩⟩` themselves, not the contract `C_n` (fidelity N3; see
`paperSealedSpec`). Angle A (`A.sealedSystem_exists_of_uniform`).
Source: mandate T4.3
Kind: C
Fidelity: variant: exact rational contract; plain trader class; `A` quotes the base propositions, not the contract `C_n`
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedSystem_exists_of_uniform (hU : UniformLIAEvaluator) :
    ∃ S : SealedSiblingSystem, S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧
      S.e = (fun _ => PublicationSchedule.sameDay) ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
      S.quoted = witnessQuoted ∧ S.contract = witnessQuoted 0 ∧
      S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N) :=
  A.sealedSystem_exists_of_uniform hU

/-- **OPEN (T4.3): the sealed-sibling system exists unconditionally** over `paperDP 𝗜𝚺₁` (both
bases), same-day publication, horizon `succDeferral`, settlement `payoutSchedule`, and the
witness's `quoted = witnessQuoted`, `contract = witnessQuoted 0`, and the siblings FAF's LIA on
each frozen process (repair round 2). The package's name for angle A's listed OPEN row
`A.sealedSystem_exists` (`A/Open.lean`): open because the only missing input is
`UniformLIAEvaluator` (`sealedSystem_exists_of_uniform`), which FAF proves as a private lemma.
Listed in `li-coupled-pair-open.txt`.
Source: [[frozen-deliberation-deference-v6]] §4 (anson-017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: OPEN
Fidelity: variant: exact rational contract; plain trader class; `A` quotes the base propositions, not the contract `C_n`
Hyps: n/a (open; rests on the listed `A.sealedSystem_exists`) -/
theorem sealedSystem_exists :
    ∃ S : SealedSiblingSystem, S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧
      S.e = (fun _ => PublicationSchedule.sameDay) ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
      S.quoted = witnessQuoted ∧ S.contract = witnessQuoted 0 ∧
      S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N) :=
  A.sealedSystem_exists

/-- **N+ grounds for T4.3 (unconditional): consecutive siblings' processes of the paper witness
differ** (the day-`N` affirmed literal of item `0` is in a stage of `H^{[N+1]}`'s process and in no
stage of `H^{[N]}`'s). Angle A (`A.paperSealed_sibling_succ_ne`, from the general
`siblingProcess_succ_ne`).
Source: mandate T4.3 N+ grounds
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperSealed_sibling_succ_ne (N : ℕ) :
    siblingProcess paperSealedSpec.base (aS paperSealedSpec) paperSealedSpec.e (N + 1) ≠
      siblingProcess paperSealedSpec.base (aS paperSealedSpec) paperSealedSpec.e N :=
  A.paperSealed_sibling_succ_ne N

end Cleanroom.Li.LiCoupledPair
