import Cleanroom.Li.LiCoupledPair.B.Conditioned
import Cleanroom.Li.LiCoupledPair.B.Scheduled
import Cleanroom.Li.LiCoupledPair.B.Counting
import Cleanroom.Li.LiCoupledPair.B.ConditionedWitness

/-!
# `li-coupled-pair` · Scheduling: T2 — fresh vs conditioned, the counting bound, the e.c. process

Reconciled module (namespace `Cleanroom.Li.LiCoupledPair`) for [[li-coupled-pair-mandate]] T2,
which angle B owned (angle A did not attack it); the statements of record are angle B's, restated
once here.

* **T2.1 (citation rows).** `fresh_needs_computable` (FAF's `LIA_is_logical_inductor`: built
  fresh needs only `ComputableDeductiveProcess`, unary-time, no polynomial clause) and
  `conditioned_needs_machineCodes` (FAF's `thm:scon`: conditioned needs `MachineSentenceCodes`
  of the conditioning sequence). Both are the *sufficiency* direction of their pole (audit r2
  adversarial N3); the first pole's necessity is the criterion's own field
  `IsLogicalInductor.processComputable`, and the two together are
  `liaHistory_inductor_iff_computable`; no necessity is claimed for the second. Over FAF the
  dichotomy of anson-2-007 (i)/(ii) is exactly these two poles — and
  `QuotePackage.clockedSeq_codes` meets the second for the clocked record of *any* computable
  table, so the chat's `e ≥ Λ` is realized as the clock (findings R-1/R-8/F-B1).
* **T2.2.** `quoteStream_cost_le`: `∑_{i < t, e i < t} Λ i ≤ t(t−1)` (the source's `< t²` is
  `quoteStream_cost_lt_sq`); no monotonicity of `e` is used. The source's count "at most `t − 1`
  indices satisfy `e(i) < t`" is **correct** under its own convention (`e` strictly increasing
  from `ℕ⁺` to `ℕ⁺`, chat 04 L445: `e(i) ≥ i`, so `1 ≤ i ≤ t − 1`); the Lean is stated over `ℕ`
  with the 0-based window `range t`, which has `t` indices, and proves the weaker `t(t−1)`, which
  still gives the chat's `< t²`. (Angle B's F-B4, "off by one", was an artifact of the 0-based
  restatement and is retracted — repair round 1, audit r1 adversarial B1 / fidelity B3.) Pure
  arithmetic, Kind `L`; Fidelity `variant: sequence-level` (FAF has no runtime model for quote
  production).
* **T2.3 (stretch).** `theoremDP_is_steps_form`: anson-2-008's "theorems output in the first `n`
  steps of a fixed proof search" is, **in shape**, FAF's `theoremDP T` by definition (`rfl`): a
  dovetail of a semi-decider whose stage `k` holds what is accepted within `k` steps. FAF's
  enumerates the `T`-provable *event literals* the paper process needs, not every theorem of `T`
  (audit r2 fidelity N2); the "poly-time in unary `n`" clause has no FAF object for processes
  (findings F-B6).
* **The scheduled sequence under fuel domination.** `ledgerSeq_codes_of_dominated`: li-quote-lane's
  original scheduled record `ledgerSeq a e` has its certificate under `FuelDominated`
  (anson-2-007's `e ≥ Λ` with the cost metered in `evaln` fuel at the route's clock and the
  threshold's payload in the bound) — the one remaining (c) of the conditioning route, which the
  clocked record avoids. **Repair round 2** (audit r2 adversarial B1): the hypothesis as first
  shipped (fuel `≤ max ((e j).e n) payload`) was unsatisfiable for every program, table and
  schedule — now the theorem `not_fuelDominated_le`; it is repaired to the clock at the scheduled
  position, which exceeds the payload. **No instance of the repaired hypothesis is known**
  (`B.exists_fuelDominated`, OPEN), so the rows read `partial: FuelDominated (c); no instance
  known`, and the schedule-free `PayloadClocked` brackets it (`fuelDominated_of_payloadClocked`,
  `payloadClocked_of_fuelDominated_above`): in FAF's fuel model the schedule can pay for the
  value, never for the threshold comparison (findings R-13). `not_perDay_dominated` is the
  per-day version of the same refutation (findings F-B7).
-/

namespace Cleanroom.Li.LiCoupledPair

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane
open Nat.Partrec (Code)

/-! ## A. T2.1: the two poles of the dichotomy -/

/-- **T2.1, citation row: built fresh needs only `ComputableDeductiveProcess`** — FAF's
`LIA_is_logical_inductor` asks for a unary-time program printing the stages and nothing else
(no polynomial clause). This is the *sufficiency* direction ("only"); the necessity in the name
("needs") is FAF's class field `IsLogicalInductor.processComputable`, and the two together are
`liaHistory_inductor_iff_computable` (audit r2 adversarial N3). Angle B
(`B.fresh_needs_computable`).
Source: anson-2-007 (the fresh/conditioned dichotomy); mandate T2.1; FAF `LIA_is_logical_inductor`
Kind: L
Fidelity: exact (sufficiency)
Hyps: (a) none -/
theorem fresh_needs_computable (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (liaHistory DP) DP :=
  B.fresh_needs_computable DP hDP

/-- **T2.1, the first pole as an equivalence:** FAF's LIA over `DP` is a logical inductor exactly
when `DP` is a computable deductive process — sufficiency is `LIA_is_logical_inductor`, necessity
is the criterion's own field `processComputable` (the class `IsLogicalInductor` carries the
certificate). What the name `fresh_needs_computable` promises, made a statement (audit r2
adversarial N3).
Source: anson-2-007 (the fresh/conditioned dichotomy); mandate T2.1; FAF `LIA_is_logical_inductor`, `IsLogicalInductor.processComputable`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem liaHistory_inductor_iff_computable (DP : DeductiveProcess) :
    IsLogicalInductor (liaHistory DP) DP ↔ ComputableDeductiveProcess DP :=
  ⟨fun h => h.processComputable, fun h => B.fresh_needs_computable DP h⟩

/-- **T2.1, citation row: conditioned needs the sentence certificate** — FAF's `thm:scon` for a
growing sequence asks for `MachineSentenceCodes ψ` and nothing about the recorded values; this
is the obligation anson-2-007 (ii) prices as `σ ≥ R(F(n))`. The *sufficiency* direction (the
cited theorem takes the certificate as its premise); no necessity is claimed or suggested
(audit r2 adversarial N3). Angle B (`B.conditioned_needs_machineCodes`).
Source: anson-2-007; mandate T2.1; FAF `lic_conditioned_growing_ofSequence`
Kind: L
Fidelity: exact (sufficiency)
Hyps: (a) none (the certificate is the cited theorem's premise) -/
theorem conditioned_needs_machineCodes (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    IsLogicalInductor
      (conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
      (DP.union (prefixProcess ψ)) :=
  B.conditioned_needs_machineCodes P DP ψ hψ

/-! ## B. T2.2: the counting bound -/

/-- **T2.2: the cost of the quotes published by stage `t` is at most `t · (t − 1)`.** Each
published quote `i < t` with `e i < t` costs `Λ i ≤ e i ≤ t − 1`, and there are at most `t` of
them in the 0-based window `range t` (the source's "at most `t − 1`" is its own ℕ⁺-indexed count
and is correct there); no monotonicity of `e` is used (where the source's strict-monotonicity
clause enters is `B.quoteStream_cost_le_window`). Angle B (`B.quoteStream_cost_le`); N+
`B.quoteStream_cost_instance` (`e i = 2i + 1`, `Λ i = i + 1`, `t = 4`: cost `3 ≤ 12`). A
`sum_le_sum` and a cardinality bound — plumbing, named because the mandate names it.
Source: anson-2-007 (chat 04 L686–703); mandate T2.2
Kind: L
Fidelity: variant: sequence-level (FAF has no runtime model); 0-based window of `t` terms, bound `t(t−1)` (weaker than the source's `(t−1)²`, still `< t²`)
Hyps: (a) none (`hΛ` is the source's own `e(i) ≥ Λ(i)`) -/
theorem quoteStream_cost_le (e Λ : ℕ → ℕ) (hΛ : ∀ i, Λ i ≤ e i) (t : ℕ) :
    (∑ i ∈ (Finset.range t).filter (fun i => e i < t), Λ i) ≤ t * (t - 1) :=
  B.quoteStream_cost_le e Λ hΛ t

/-- **The source's `< t²`**, for `t ≥ 1`. Angle B (`B.quoteStream_cost_lt_sq`).
Source: anson-2-007 (chat 04 L686–703); mandate T2.2
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem quoteStream_cost_lt_sq (e Λ : ℕ → ℕ) (hΛ : ∀ i, Λ i ≤ e i) (t : ℕ) (ht : 1 ≤ t) :
    (∑ i ∈ (Finset.range t).filter (fun i => e i < t), Λ i) < t * t :=
  B.quoteStream_cost_lt_sq e Λ hΛ t ht

/-! ## C. T2.3: the "first `n` steps" process is FAF's paper process -/

/-- **T2.3 (finding, cited): anson-2-008's e.c. and `Γ`-complete process** "theorems output in
the first `n` steps of a fixed proof search" is, **in shape**, FAF's `theoremDP T` by definition:
a dovetail of a semi-decider (`dovetailProcess`) whose stage `k` holds what is accepted within
`k` steps. FAF's enumerates the `T`-provable *event literals* (the computation literals the paper
process needs) rather than every theorem of `T` — the shape is the chat's, the scope is FAF's
(audit r2 fidelity N2). The "poly-time in unary `n`" clause has no FAF object for processes.
Angle B (`B.theoremDP_is_steps_form`; also `B.paperTheoryDP_is_steps_form`).
Source: anson-2-008 (chat 04 L7404–7407); mandate T2.3; FAF `theoremDP`, `dovetailProcess`
Kind: L
Fidelity: variant: shape (dovetail of a semi-decider, stage `k` = accepted within `k` steps), with FAF's event-literal scope in place of "every theorem"; the efficiency clause has no FAF carrier
Hyps: (a) none -/
theorem theoremDP_is_steps_form (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] :
    theoremDP T = dovetailProcess eventAtom (exists_eventCode T).choose :=
  B.theoremDP_is_steps_form T

/-! ## D. The scheduled record under fuel domination (the route's remaining (c); no instance known) -/

export Cleanroom.Li.LiCoupledPair.B (FuelDominated PayloadClocked)

/-- **li-quote-lane's scheduled record has its certificate under fuel domination**: if the
polarity program halts on each literal's payload `p` within the route's clock at the scheduled
position, `B.clock (max ((e j).e n) p)` (`FuelDominated` — anson-2-007's `e ≥ Λ` with the cost
in `evaln` fuel and the threshold's payload in the bound), then `ledgerSeq a e` is
`MachineSentenceCodes`, so li-quote-lane's `conditioningRoute_inductor` applies with its (c)
replaced by this one (`B.conditioningRoute_inductor_of_dominated`). **Repair round 2** (audit r2
adversarial B1): the hypothesis as first shipped, fuel `≤ max ((e j).e n) p`, was unsatisfiable
for every program, table and schedule (`not_fuelDominated_le`); the repaired bound exceeds the
payload. **No instance of the repaired hypothesis is known** (`B.exists_fuelDominated`, OPEN):
`gateVal a` is never constant and runs Mathlib's rational `decode` (a gcd), and a certificate
for such a program at a fixed quadratic clock is a fuel-calculus construction FAF's `PolyFueled`
combinators do not give. Not a sharper hypothesis than li-quote-lane's `hψ` — a different one.
The clocked route (`QuotePackage.clockedSeq_codes`) needs none. Angle B
(`B.ledgerSeq_codes_of_dominated`).
Source: anson-2-007; li-quote-lane T6.3 and findings F8; mandate angle B
Kind: C
Fidelity: variant: fuel in place of runtime; the threshold's payload in the bound
Hyps: (c) `hdom : FuelDominated c₁ a e` (a fuel bound FAF does not supply for an opaque program; no instance known); `he` the schedule's poly-time certificate -/
theorem ledgerSeq_codes_of_dominated {a : ℕ → ℕ → ℚ} (c₁ : Code) (e : ℕ → PublicationSchedule)
    (hc : ∀ p, c₁.eval p = Part.some (B.gateVal a p)) (hdom : FuelDominated c₁ a e)
    (he : UnaryRuler fun p => (e p.unpair.1).e p.unpair.2) :
    MachineSentenceCodes (ledgerSeq a e) :=
  B.ledgerSeq_codes_of_dominated c₁ e hc hdom he

/-- **The schedule is not needed**: a polarity program that halts within the route's clock on
every literal's own payload (`PayloadClocked`) dominates every schedule. Angle B
(`B.fuelDominated_of_payloadClocked`).
Source: findings R-13
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem fuelDominated_of_payloadClocked {c₁ : Code} {a : ℕ → ℕ → ℚ} (h : PayloadClocked c₁ a)
    (e : ℕ → PublicationSchedule) : FuelDominated c₁ a e :=
  B.fuelDominated_of_payloadClocked h e

/-- **The schedule cannot pay for the threshold comparison**: under `FuelDominated`, every
literal whose payload is at or above its publication stage — all but finitely many rational
codes per `(j, n)` — is decided within the clock of its own payload. So in FAF's fuel model the
chat's `e ≥ Λ`, over li-quote-lane's per-threshold rendering, is a property of the polarity
program, up to finitely many small codes per day that the schedule may cover. Angle B
(`B.payloadClocked_of_fuelDominated_above`).
Source: findings R-13 (sharpening F-B7 / R-8)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem payloadClocked_of_fuelDominated_above {c₁ : Code} {a : ℕ → ℕ → ℚ}
    {e : ℕ → PublicationSchedule} (hdom : FuelDominated c₁ a e) (j n c : ℕ)
    (hd : (Encodable.decode (α := ℚ) c).isSome = true)
    (hp : (e j).e n ≤ ledgerPayload j n c) :
    B.gateVal a (ledgerPayload j n c) ∈
      Code.evaln (B.clock (ledgerPayload j n c)) c₁ (ledgerPayload j n c) :=
  B.payloadClocked_of_fuelDominated_above hdom j n c hd hp

/-- **Why the bound must exceed the payload, per day** (findings F-B7, relabelled *presentation
(rendering)* in repair round 1): a per-day fuel domination for *all* thresholds is unsatisfiable
for every program, since a run on input `p` needs fuel `> p` (Mathlib's `evaln_bound`) and the
payload is unbounded in the threshold code. This is a fact about the rendering — li-quote-lane's
per-threshold literal family with the threshold's code inside the machine's input, and `evaln`'s
fuel-exceeds-input convention — not an error in the source, whose `Λ(n)` is the cost of producing
*one* rational `a_n` and whose cost model prices no per-threshold comparison (audit r1 fidelity
B3 / adversarial §3.1; the probe `NotPerDayDominatedArtifact.lean` proves it for any output
function, any program and any fixed bound). The conclusion is that the bound must *exceed* the
payload, not merely carry it: `not_fuelDominated_le` is the same refutation for the bound
`max ((e j).e n) p` (audit r2 adversarial B1). Angle B (`B.not_perDay_dominated`).
Source: anson-2-007 (the literal reading of `e(n) ≥ Λ(n)`); Mathlib `evaln_bound`
Kind: L (Mathlib's input guard plus the unboundedness of the payload)
Fidelity: n/a (a fact about the rendering)
Hyps: (a) none -/
theorem not_perDay_dominated (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (j n : ℕ) :
    ¬ ∀ c, (Encodable.decode (α := ℚ) c).isSome = true →
      ∃ k ≤ (e j).e n, B.gateVal a (ledgerPayload j n c) ∈ Code.evaln k c₁ (ledgerPayload j n c) :=
  B.not_perDay_dominated c₁ a e j n

/-- **The pre-repair `FuelDominated` had no instance** (audit r2 adversarial B1, probe
`FuelDominatedVacuous.lean`): fuel `≤ max ((e j).e n) p` is at most the payload once the
rational code exceeds the publication stage, and `evaln_bound` needs more. Machine-checked
record of why the definition changed in repair round 2. Angle B (`B.not_fuelDominated_le`).
Source: audit r2 adversarial B1; Mathlib `evaln_bound`
Kind: P
Fidelity: n/a (a fact about the rendering)
Hyps: (a) none -/
theorem not_fuelDominated_le (c₁ : Code) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) :
    ¬ ∀ j n c, (Encodable.decode (α := ℚ) c).isSome = true →
      ∃ k ≤ max ((e j).e n) (ledgerPayload j n c),
        B.gateVal a (ledgerPayload j n c) ∈ Code.evaln k c₁ (ledgerPayload j n c) :=
  B.not_fuelDominated_le c₁ a e

end Cleanroom.Li.LiCoupledPair
