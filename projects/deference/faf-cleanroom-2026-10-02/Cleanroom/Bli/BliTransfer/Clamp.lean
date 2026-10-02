import Cleanroom.Bli.BliTransfer.Defs
import Cleanroom.Bli.BliTransfer.AttemptA.Clamp
import Cleanroom.Bli.BliTransfer.AttemptB.Clamp

/-!
# `bli-transfer` · Clamp: the clamped re-pricing is **not** a logical inductor (T3, refuted)

**The disagreement between the two attempts, and its resolution.** The mandate's T3 asked for
`IsLogicalInductor Q DP → IsLogicalInductor (clamp Q) DP`, where `clamp Q k ψ =
max (min (Q k ψ) (1 − ε_k)) ε_k` on **every** sentence, `ε_k = 2^{-2^k}` ([[bli-program]]
§3.2(d); bli-paper-033/039, bli-slides-006/008, bli-soto-a-002 reading C), by a rewrite that
reads the clamp exactly plus a settlement residual `∑_n magnitude_n · ε_n`, summable because
"trade magnitude `≤ 2^{p(n)}`" (program §4 L5; the mandate's new lemma `magnitude_le_of_ec`).

* **Attempt A** proved the accounting through the rewrite (`clampSpec`,
  `Strategy.clamp_value_sub_le`, `Trader.clamp_netWorth_sub_le`) and left the headline
  conditional (`AttemptA.clamp_isLogicalInductor_of`) on three named hypotheses: the clamp
  certificate `hec`, bounded partial sums of `magnitude · ε` for every e.c. trader `hbound`
  (what `magnitude_le_of_ec` would give), and the clamped table's computability `hcomp`. Status
  `partial`.
* **Attempt B** refuted the claim: the trader `sellBottom`, which on day `n` sells `2^{2^{n+1}}`
  shares of `⊥` (coefficient `n+1` nested `letE`-squarings of `const 2`, cost `O(n)`), is
  efficiently computable (`sellBottom_ec`, through FAF's machine combinators), and on any
  market pricing `⊥` at `≥ ε_n` it banks `≥ 2^{2^{n+1}} · 2^{-2^n} = 2^{2^n}` per day with no
  downside (`⊥` pays `0` in every world). The clamp forces exactly that floor
  (`clamp_mem_Icc`), so `clamp Q` is exploited for **every** history `Q` over every process
  with consistent worlds (`clamp_not_isLogicalInductor`), and the program's magnitude bound is
  false (`not_magnitude_le_two_pow_poly`). Non-vacuity at FAF's LIA over `paperDP 𝗜𝚺₁`:
  `WitnessLia.clamp_lia_not_isLogicalInductor`.

**Attempt B is right, and attempt A's conditional is conditional on a false hypothesis.** This
file records that in Lean: `clamp_bounded_partial_sums_false` shows attempt A's `hbound` fails
for `sellBottom` on every `Q` (its day-`i` term is `2^{2^{i+1}} · 2^{-2^i} = 2^{2^i} ≥ 1`, so the
partial sums are unbounded), and `clamp_conditional_antecedent_false` shows the three
hypotheses of `AttemptA.clamp_isLogicalInductor_of` are jointly unsatisfiable over any process
with consistent worlds — by composing the two attempts' theorems. Status of T3: **refuted**
(the ledger row's Status), with the accounting lemmas kept as `L`/`C` rows of their own: they
are correct, and they show precisely where the program's argument breaks (the settlement
residual is not summable, because e.c. magnitude is doubly exponential, not `2^{poly}`).

**What this says about the sources.** Any re-pricing that forces a positive floor `≥ 2^{-2^n}`
on a refuted sentence is exploitable by the same trader (`floor_not_isLogicalInductor`, the
form that also settles the ceiling half of Route A, T4). Attempt B's analysis (F-B1, not
formalized): an *expressible* floor of polynomial cost is `≥ 2^{-2^{p(n)}}` for some polynomial
`p`, and a trader with `p + 1` squarings beats it, so no clamp with an expressible rate rescues
the variant. The surviving neighbour is T1 with exact constraint 1: an expressible re-pricing of
large sentences that never touches `⊥` (small on every day) has no settlement residual at all.
`clamp` and `E1c` remain definitions of record for `bli-assemble`, whose "clamped B1" plan needs
revisiting: the clamp destroys the criterion.

Sources: [[bli-program]] §3.2(d), §4 L5; bli-paper-033/039; bli-slides-006/008; mandate T3,
Known issue 7, T4.
-/

namespace Cleanroom.Bli.BliTransfer

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open scoped BigOperators

/-! ## Attempt A's accounting through the rewrite (correct, re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptA
  (clampExpr clampExpr_rank clampSpec Strategy.clamp_value_sub_le Trader.clamp_netWorth_sub_le)

/-! ## Attempt B's `⊥`-seller (re-exported) -/

export Cleanroom.Bli.BliTransfer.AttemptB
  (sqTower sqTower_denoteWith sqTower_rank sqTower_priceFree sellBottomCoeff sellBottomCoeff_denote
   sellBottom payout_falsum sellBottom_value sellBottom_magnitude sellBottom_ec)

/-- **Any market pricing `⊥` at `≥ ε_n` (and `≥ 0`) is exploited by the `⊥`-seller**, over any
process with consistent worlds: its net worth is `≥ 0` in every world and `≥ 2^{2^n}` on day
`n`. Stronger than T3's refutation needs (any market with the floor, not only the clamp); it is
also the ceiling half of Route A (T4): a rounding that maps a positive price of a refuted
sentence up to a grid point `≥ 2^{-2^n}` is dead whenever the base prices it positively. Proved
by attempt B (`AttemptB.sellBottom_exploits`).
Source: mandate T3 (refutation), T4 (ceiling half); [[bli-program]] §3.2(c)–(d)
Kind: P
Fidelity: stronger: any market with the floor, not only the clamp
Hyps: (a) `hworld` — the process has a consistent world at every stage (trap (v)) -/
theorem sellBottom_exploits (P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP0 : ∀ n, 0 ≤ P n ⊥) (hP : ∀ n, (epsK n : ℝ) ≤ P n ⊥) :
    sellBottom.Exploits P DP :=
  AttemptB.sellBottom_exploits P DP hworld hP0 hP

/-- **No market with the floor `ε_n` on `⊥` is a logical inductor** (over a process with
consistent worlds): the `⊥`-seller is efficiently computable and exploits it.
Source: mandate T3 (refutation), T4 (ceiling half)
Kind: C
Fidelity: stronger: any market with the floor
Hyps: (a) `hworld` (trap (v)) -/
theorem floor_not_isLogicalInductor (P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP0 : ∀ n, 0 ≤ P n ⊥) (hP : ∀ n, (epsK n : ℝ) ≤ P n ⊥) :
    ¬ IsLogicalInductor P DP :=
  fun h => h.noExploit sellBottom sellBottom_ec (sellBottom_exploits P DP hworld hP0 hP)

/-- **T3 refuted**: the clamped market is exploited by an e.c. trader for **every** history `Q`
over every process with consistent worlds, so it is never a logical inductor — whether or not
`Q` is one. Scope: the clamp is applied to every sentence with `ε_k = 2^{-2^k}` (the definition
of record); the refutation needs neither `IsLogicalInductor Q DP` nor any property of `Q`.
Proved by attempt B (`AttemptB.clamp_not_isLogicalInductor`, over the same `clamp`,
`Defs.attemptB_clamp_eq`).
Source: [[bli-program]] §3.2(d); bli-paper-033/039; bli-slides-006/008; bli-soto-a-002 (reading C); mandate T3
Kind: P
Fidelity: n/a (refutation)
Hyps: (a) `hworld` — trap (v); at `paperDP 𝗜𝚺₁` it is `paperDP_hworld` (`WitnessLia.clamp_lia_not_isLogicalInductor`) -/
theorem clamp_not_isLogicalInductor (Q : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (clamp Q) DP :=
  AttemptB.clamp_not_isLogicalInductor Q DP hworld

/-- **Known issue 7 refuted**: no polynomial `p` bounds the `⊥`-seller's magnitude by `2^{p(n)}`,
against any market. The program's "trade magnitude `≤ 2^{p(n)}`" (§4 L5) and the mandate's
`magnitude_le_of_ec` are false for FAF's e.c. traders: `letE` sharing lets a feature of cost
`O(n)` denote `2^{2^{n+1}}`. Proved by attempt B (`AttemptB.not_magnitude_le_two_pow_poly`).
Source: [[bli-program]] §4 L5; mandate T3, Known issue 7
Kind: P
Fidelity: n/a (refutation)
Hyps: (a) -/
theorem not_magnitude_le_two_pow_poly (V : History) :
    ¬ ∃ p : Polynomial ℕ, ∀ n, (sellBottom.strat n).magnitude V ≤ (2 : ℝ) ^ p.eval n :=
  AttemptB.not_magnitude_le_two_pow_poly V

/-! ## The reconciliation: attempt A's antecedent is false -/

/-- The `⊥`-seller's day-`i` settlement residual term: `magnitude_i · ε_i = 2^{2^{i+1}} · 2^{-2^i}
= 2^{2^i}`, against any market.
Source: none: infrastructure (reconciliation)
Kind: L
Fidelity: n/a -/
lemma sellBottom_magnitude_mul_epsK (V : History) (i : ℕ) :
    (sellBottom.strat i).magnitude V * (epsK i : ℝ) = (2 : ℝ) ^ 2 ^ i := by
  rw [sellBottom_magnitude]
  have h1 : (2 : ℝ) ^ 2 ^ (i + 1) = 2 ^ 2 ^ i * 2 ^ 2 ^ i := by
    rw [pow_succ, pow_mul, sq]
  have h2 : ((epsK i : ℚ) : ℝ) = (1 / 2 : ℝ) ^ 2 ^ i := by
    simp [AttemptA.epsK]
  rw [h1, h2, mul_assoc, ← mul_pow]
  norm_num

/-- **Attempt A's hypothesis `hbound` is false on every `Q`**: the partial sums
`∑_{i ≤ n} magnitude_i (clamp Q) · ε_i` are not bounded for every e.c. trader, because for the
`⊥`-seller each term is `2^{2^i} ≥ 1`. So `AttemptA.clamp_isLogicalInductor_of` is conditional
on a hypothesis no market satisfies, and the mandate's route to T3 (summability of the
settlement residual from `magnitude_le_of_ec`) is closed, not merely undischarged.
Source: mandate T3; [[bli-program]] §3.2(d), §4 L5 (reconciliation of the two attempts)
Kind: P
Fidelity: n/a (refutation of a hypothesis)
Hyps: (a) -/
theorem clamp_bounded_partial_sums_false (Q : History) :
    ¬ ∀ Tr : Trader, EfficientlyComputable Tr → ∃ C : ℝ, ∀ n,
      ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude (clamp Q) * (epsK i : ℝ) ≤ C := by
  intro h
  obtain ⟨C, hC⟩ := h sellBottom sellBottom_ec
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (1 : ℝ) ≤ (sellBottom.strat i).magnitude (clamp Q) * (epsK i : ℝ) := by
    intro i _
    rw [sellBottom_magnitude_mul_epsK]
    exact one_le_pow₀ (by norm_num)
  have hsum : ((n : ℝ) + 1) ≤
      ∑ i ∈ Finset.range (n + 1), (sellBottom.strat i).magnitude (clamp Q) * (epsK i : ℝ) := by
    calc ((n : ℝ) + 1) = ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range]; simp
      _ ≤ _ := Finset.sum_le_sum hterm
  linarith [hC n]

/-- **The two attempts reconciled in one statement**: the three hypotheses of attempt A's
conditional T3 (`AttemptA.clamp_isLogicalInductor_of` — the clamp certificate, bounded
`magnitude · ε` partial sums, the clamped table's computability) are jointly unsatisfiable over
any process with consistent worlds, because their conclusion is refuted by attempt B. (The
second alone is already false, `clamp_bounded_partial_sums_false`; this form composes the two
attempts' theorems as they stand.)
Source: mandate T3 (reconciliation of the two attempts)
Kind: C
Fidelity: n/a
Hyps: (a) `hQ`, `hworld` -/
theorem clamp_conditional_antecedent_false (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ ((∀ Tr : Trader, EfficientlyComputable Tr →
          EfficientlyComputable (Trader.spliceOn clampExpr clampExpr_rank Tr)) ∧
       (∀ Tr : Trader, EfficientlyComputable Tr → ∃ C : ℝ, ∀ n,
          ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude (clamp Q) * (epsK i : ℝ) ≤ C) ∧
       ComputableMarket (clamp Q)) := by
  rintro ⟨hec, hbound, hcomp⟩
  exact clamp_not_isLogicalInductor Q DP hworld
    (AttemptA.clamp_isLogicalInductor_of Q DP hec hbound hcomp)

end Cleanroom.Bli.BliTransfer
