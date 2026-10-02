import Cleanroom.Bli.BliCoherentMm.AttemptA.Waived
import Cleanroom.Bli.BliCoherentMm.AttemptB.Waived

/-!
# `bli-coherent-mm` · Waived (reconciled): T0, the stage-relative waived-days lemma

**Of record: attempt A's declarations.** Both attempts state T0 in the mandate's shape, word
for word the same theorem (`not_exploits_of_dayValue_le_consistent_off_finite`: a trader whose
day-`n` strategy has value `≤ marketMakerError n` on a `[0,1]` history in every world consistent
with `DP.D n`, on every day outside a finite set, does not exploit the history relative to
`DP`), with the same accounting (`netWorth ≤ 1 + ∑_{i ∈ W} absBound`; a world consistent with
`DP.D n` is consistent with every earlier stage by `DP.mono_le`). Attempt B's proof is kept as
the independent second proof of the record statement (`…_viaB`), and attempt B's observation
that `bli-overlay`'s all-worlds lemma is the special case (`…_of_consistent`) is kept too.

Scope clause (copied into every docstring): **over `DP.D n`-consistent worlds** — the whole
difference from `bli-overlay`'s all-worlds form, and what a coherent maker can supply (the
record's lemma quantifies over all `PCWorld`s; a `PCWorld` inconsistent with the stage can pay
a coherent table, findings F14).

Sources: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a).
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-- **T0 (of record, headline). The stage-relative waived-days lemma.** If on every day `n`
outside a finite set `W` the trader's day-`n` strategy has value `≤ marketMakerError n`
on the `[0,1]` history `P` in every world **consistent with the stage `DP.D n`**, then the
trader does not exploit `P` relative to `DP`.
Source: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause, `hacc` the per-day stage-relative bound the
lemma is about -/
theorem not_exploits_of_dayValue_le_consistent_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP :=
  AttemptA.not_exploits_of_dayValue_le_consistent_off_finite Tr P DP hP W hacc

/-- **T0, attempt B's independent proof of the record statement** (the same theorem, proved
again by the other attempt; kept as evidence that the statement is stable).
Source: [[bli-coherent-mm-mandate]] T0; §Deliverables (reconciler cross-check)
Kind: P
Fidelity: exact
Hyps: (a) as above -/
theorem not_exploits_of_dayValue_le_consistent_off_finite_viaB (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP :=
  AttemptB.not_exploits_of_dayValue_le_consistent_off_finite Tr P DP hP W hacc

/-- **T0, corollary: the static firm on a rational `[0,1]` table**, bounded stage-relatively on
every day outside a finite set, does not exploit the table's market.
Source: [[bli-coherent-mm-mandate]] T0 (corollaries)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun day φ => (Q day φ : ℝ)) v.payout ≤
        (marketMakerError n : ℝ)) :
    ¬ (tradingFirmTrader DP Q).Exploits (fun day φ => (Q day φ : ℝ)) DP :=
  AttemptA.firm_not_exploits_of_coherentAccepted_off_finite DP Q hQ W hacc

/-- **T0, corollary: no efficiently computable trader exploits** a rational `[0,1]` table on
which the firm is bounded stage-relatively off a finite set (FAF's `trading_firm_dominance`).
Source: [[bli-coherent-mm-mandate]] T0 (corollaries); FAF `trading_firm_dominance`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem no_ec_trader_exploits_of_firm_coherentAccepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (TradingFirmAt DP Q n).value (fun day φ => (Q day φ : ℝ)) v.payout ≤
        (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun day φ => (Q day φ : ℝ)) DP :=
  AttemptA.no_ec_trader_exploits_of_firm_coherentAccepted_off_finite DP Q hQ W hacc

/-- **`bli-overlay`'s all-worlds waived-days lemma is the special case of T0** (attempt B's
observation): a bound in every `PCWorld` is a bound in every stage-consistent one, so every
customer of the all-worlds lemma can switch to the stage-relative one.
Source: [[bli-coherent-mm-mandate]] T0; [[bli-overlay-mandate]] T3(a)
Kind: L
Fidelity: n/a -/
theorem not_exploits_of_dayValue_le_off_finite_of_consistent (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld, (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP :=
  AttemptB.not_exploits_of_dayValue_le_off_finite_of_consistent Tr P DP hP W hacc

end Cleanroom.Bli.BliCoherentMm
