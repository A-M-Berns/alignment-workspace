import Cleanroom.Deference.DefTrackingPin.Atoms
import LogicalInduction.Properties.ExpectationAffine

/-!
# `def-tracking-pin` · Encoding: real-payout accounting is FAF's criterion up to the mesh error (T8)

anson-2-021 (ATTRIBUTION-UNVETTED: the inventory's reading of what every construction in the
corpus assumes, stated as a lemma nowhere): the corpus's contract `C_n := (1/n) Σ_{k=1}^{n} θ_{n,k}`
with `val_W(n) = m/n`, pinned by the settling profile `𝒜_n(m*_n)` at `σ(n)`, **is** FAF's
precision-`n` threshold mesh `LUV.expectAffine X n` of a `[0,1]`-LUV `X` (grid `k/n`), and the
settling profile is the ledger's polarity rule at `a j n = m*_n/n`.

* (i) **Identification (D + L)**: `contract X n := X.expectAffine n`; its completed-world value is
  `expectApprox` (`contract_value`), its day-`n` price at the day's grid is the day-`n` expectation
  (`contract_price`), and in every completed-theory world of a process settling `X` at `y` it is
  within `1/n` of `y` (`contract_value_near`, from `determinedVia_expectApprox_near`). For the
  ledger LUV the settling profile is `ledgerLuv_gt_holds_iff`: `θ_{n,k}` is affirmed iff
  `k/n < a_{j,n}` (strict — the corpus's `k ≤ m*_n` with the grid point `k/n = a` unconstrained,
  disclosure (β)).
* (ii) **Transport (L, valuation level)**: the real-payout net worth `Σ_i t_i (v_i − p_i)` of a
  trader holding `t_i` shares of the contract on `X_i` bought at `p_i` (`realPayoutWorth`, a
  definition of record with no FAF object — labelled (c) variant) differs from the mesh-accounting
  net worth of the same trades in any completed-theory world (`meshWorth`) by at most
  `Σ_i |t_i|/(i+1)` (`meshWorth_sub_realPayoutWorth_le`), hence by a constant when that series is
  bounded (`meshWorth_sub_realPayoutWorth_le_of_bounded`). **What is not done:** lifting this to
  FAF's `Trader.Exploits` through `Trader.Exploits.of_boundedDifference` for a FAF trader whose
  day-`i` strategy is `t_i` shares of the mesh. That needs a mesh-trader constructor over FAF's
  `Strategy` (an e.c. certificate for a feature-coefficient strategy on the mesh terms), which this
  package does not build; the valuation-level bound is the whole content of the step except that
  constructor, and the report records the transport as not attempted rather than as a sorry'd
  statement whose shape would be guessed.

Roles: `P` the reader; one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-! ## (i) The contract is the mesh -/

/-- **The corpus's contract `C_n` of record**: FAF's precision-`n` threshold bundle
`(1/n) Σ_{k<n} ⌜X > k/n⌝` of the `[0,1]`-LUV `X` (`LUV.expectAffine`). The corpus's `θ_{n,k}` are
the thresholds `⌜X > k/n⌝`, its monotonicity axioms are `PCWorld.ValuesAt`'s threshold coherence,
and `val_W(n) = m/n` is the mesh value in `W`.
Source: anson-2-021 (chat 05 L10380–10420, `C_n := (1/n) Σ_k α_{n,k}`); ATTRIBUTION-UNVETTED reading
Kind: D
Fidelity: exact (FAF's `def:e` bundle; the grid is `k/n`, `k < n`)
Hyps: n/a -/
def contract (X : LUV) (n : ℕ) : AffineCombination := X.expectAffine n

/-- The contract's value in a valuation is the approximate expectation (`def:e`).
Source: anson-2-021; FAF `LUV.expectAffine_value`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem contract_value (X : LUV) (P : History) (w : Valuation) (n : ℕ) :
    (contract X n).value P w = X.expectApprox w n :=
  X.expectAffine_value P w n

/-- The contract at the day's own grid is priced at the day-`n` expectation: `P_n(C_{n+1}) =
𝔼^P_n(X)` (FAF's day-index convention, Lean day `n` = grid `n + 1`).
Source: anson-2-021; FAF `LUV.expectAffine_price`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem contract_price (X : LUV) (P : History) (n : ℕ) :
    (contract X (n + 1)).price P n = X.expect P n :=
  X.expectAffine_price P n

/-- **T8 (i) (headline). A settled contract is valued within `1/n` of its settled value in every
completed-theory world** — the corpus's "`|val_W(C_n) − m*_n/n| ≤ 1/n`", with the settling profile
read as `DeterminedVia` and the contract as the mesh. Reader-independent; one-way.
Source: anson-2-021 (chat 08 L921–991); FAF `lem:conluvapprox`
Kind: L
Fidelity: stronger: no grid-rounding of the target (`Defs.lean`, `determinedVia_expectApprox_near`)
Hyps: (a) none -/
theorem contract_value_near {X : LUV} {DP : DeductiveProcess} {y : ℝ}
    (hdet : LUV.DeterminedVia X DP y) (P : History) {n : ℕ} (hn : 0 < n) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) :
    |(contract X n).value P v.payout - y| ≤ 1 / n := by
  rw [contract_value]
  exact determinedVia_expectApprox_near hdet hn v hv

/-- **The settling profile, at the ledger**: the threshold `θ_{n,k} = ⌜α_{j,n} > k/m⌝` is affirmed
in every completed-theory world of the ledger process iff `k/m < a_{j,n}` — the corpus's "adjoin
`θ_{n,k}` for `k ≤ m*_n`" with the strict polarity the ledger publishes (disclosure (β)).
Source: anson-2-021 (chat 08 L921–991, settling profiles `Θ_n(m*_n)`); `li-quote-lane` (β)
Kind: L
Fidelity: variant: strict polarity, the grid point `k/m = a_{j,n}` unconstrained
Hyps: (a) none -/
theorem ledger_profile (base : DeductiveProcess) (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule)
    (j n k m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (ledgerProcess base a e)) :
    v.Holds ((ledgerLuv j n).gt ((k : ℚ) / (m : ℚ))) ↔ (k : ℚ) / (m : ℚ) < a j n :=
  ledgerLuv_gt_holds_iff base a e j n _ v hv

/-! ## (ii) Real-payout accounting versus mesh accounting -/

/-- **The real-payout net worth of record** (a definition with no FAF object — the corpus's
`LI(H,F)` criterion values a day-`i` trade of `t_i` shares of the contract on `X_i`, bought at
`p_i`, at the real `v_i` the contract "pays"): `Σ_{i<n} t_i (v_i − p_i)`. Labelled (c) variant:
FAF's payouts are `PCWorld.payout`, `0/1`; a real payout enters FAF only through the mesh
(`meshWorth`) and the transport bound below.
Source: anson-2-020 (chat 01 L1494–1512, the `LI(H,F)` definition); anson-2-021
Kind: D
Fidelity: variant: a real-valued accounting with no FAF object, stated to be compared with the mesh accounting
Hyps: n/a -/
def realPayoutWorth (t v p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t i * (v i - p i)

/-- **The mesh-accounting net worth of the same trades** in a valuation `w`: `Σ_{i<n} t_i
(w(C_{i+1}(X_i)) − p_i)` — what a FAF world pays the holder of `t_i` shares of the day-`i` mesh
contract (FAF's `Trader.netWorth` for such a trader, before the trader is built).
Source: anson-2-021
Kind: D
Fidelity: exact (the mesh value is FAF's `AffineCombination.value`)
Hyps: n/a -/
noncomputable def meshWorth (X : ℕ → LUV) (P : History) (t p : ℕ → ℝ) (w : Valuation)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t i * ((contract (X i) (i + 1)).value P w - p i)

/-- **T8 (ii), valuation level: the two accountings differ by at most `Σ_i |t_i|/(i+1)`** in any
world consistent with every stage of a process settling every `X_i` at `v_i`. Per term, the mesh
value is within `1/(i+1)` of the real payout (`contract_value_near`). One-way.
Source: anson-2-021 ("net worth … equals `Σ t_i (v_i − A_i(C_i))` up to `Σ |t_i|/(2i)`")
Kind: L
Fidelity: variant: FAF's grid error `1/(i+1)` in place of the corpus's `1/(2i)` (no rounding of the target, so no halving)
Hyps: (a) none -/
theorem meshWorth_sub_realPayoutWorth_le {X : ℕ → LUV} {DP : DeductiveProcess} {v : ℕ → ℝ}
    (hdet : ∀ i, LUV.DeterminedVia (X i) DP (v i)) (P : History) (t p : ℕ → ℝ) (w : PCWorld)
    (hw : w.ConsistentWithTheory DP) (n : ℕ) :
    |meshWorth X P t p w.payout n - realPayoutWorth t v p n| ≤
      ∑ i ∈ Finset.range n, |t i| / ((i : ℝ) + 1) := by
  unfold meshWorth realPayoutWorth
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h := contract_value_near (hdet i) P (Nat.succ_pos i) w hw
  have hterm : t i * ((contract (X i) (i + 1)).value P w.payout - p i) - t i * (v i - p i) =
      t i * ((contract (X i) (i + 1)).value P w.payout - v i) := by ring
  rw [hterm, abs_mul]
  calc |t i| * |(contract (X i) (i + 1)).value P w.payout - v i|
      ≤ |t i| * (1 / ((i + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |t i| / ((i : ℝ) + 1) := by push_cast; ring

/-- **T8 (ii), the bounded-difference form**: for trade sizes with `Σ_i |t_i|/(i+1) ≤ K` uniformly
(e.g. `|t_i| ≤ 1` with at most one open position per window, the corpus's ramp trader), the two
accountings differ by at most `K` on every day in every completed-theory world — the `hdiff`
input of FAF's `Trader.Exploits.of_boundedDifference` for a trader whose net worths are these.
One-way.
Source: anson-2-021 ("if `Σ_i |t_i|/i` is bounded … exploited under the real-payout criterion iff under FAF's")
Kind: L
Fidelity: variant: the valuation-level bound; the FAF-trader transport is not built (module docstring)
Hyps: (a) none -/
theorem meshWorth_sub_realPayoutWorth_le_of_bounded {X : ℕ → LUV} {DP : DeductiveProcess}
    {v : ℕ → ℝ} (hdet : ∀ i, LUV.DeterminedVia (X i) DP (v i)) (P : History) (t p : ℕ → ℝ)
    {K : ℝ} (hK : ∀ n, ∑ i ∈ Finset.range n, |t i| / ((i : ℝ) + 1) ≤ K) (w : PCWorld)
    (hw : w.ConsistentWithTheory DP) (n : ℕ) :
    |meshWorth X P t p w.payout n - realPayoutWorth t v p n| ≤ K :=
  (meshWorth_sub_realPayoutWorth_le hdet P t p w hw n).trans (hK n)

end Cleanroom.Deference.DefTrackingPin
