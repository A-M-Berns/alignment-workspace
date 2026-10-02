import Cleanroom.Fa.FaEisenstatConj.GenRefuted
import Mathlib.Analysis.PSeries

/-!
# `fa-eisenstat-conj` · Transfer: per-sentence asymptotic equality does not transfer the criterion (E2)

E1 (`Companion.lean`) shows that under the package of record the merge is **per-sentence
asymptotically equal** to `H`'s own prices: `𝔼^∗_n(φ) − ℙ^H_n(φ) → 0` for every `φ`. The inductor
half (`Open.lean`) therefore asks whether a market per-sentence asymptotically equal to an
inductor is itself an inductor over the same process. **It is not, in general** — and not even
when the equality is *uniform* in the sentence. The damped market `damped P n φ := P n φ · n/(n+1)`
is a computable market within `1/(n+1)` of `P` on every sentence on day `n`
(`damped_dist_le`), yet the trader that buys one share of `⊤` every day gains at least `1/(n+1)`
on day `n` in every world, and the harmonic series diverges (`damped_not_inductor`). The
existential form over FAF's paper LIA is `asympEq_not_transfer` (`Witnesses.lean`).

Consequences for the OPEN: E1 settles the inductor half in **neither direction** — the merge's
closeness to `H` is per-sentence and (as far as E1 says) *rate-free*, and a rate-free
perturbation of an inductor can be exploited at a non-summable rate. What would transfer the
criterion is a *summable* uniform rate (FAF's finite-perturbation closure,
`Exploits.of_boundedDifference`, needs a bounded total error), which no corpus result gives for
the merge. This is the precise sense in which the inductor half is a genuinely new question and
not a corollary of the trust-half positives. (The mandate's E2 (i) asked for this as an OPEN
stated as the negation's refutation, "direction unknown"; the direction is now known.)

Scope: single market (no `H`/`A` pair); a fact about FAF's criterion used to locate the OPEN.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- **The damped market** `P' n φ := P n φ · n/(n+1)`: a uniformly-vanishing perturbation of `P`
that is not summable along the diagonal.
Source: mandate E2 (i) (the `relabel_not_inductor` pattern, direction settled)
Kind: D
Fidelity: n/a -/
noncomputable def damped (P : History) : History :=
  fun n φ => P n φ * ((n : ℝ) / ((n + 1 : ℕ) : ℝ))

/-- The damping factor lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma damping_mem (n : ℕ) : 0 ≤ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ∧ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    exact_mod_cast Nat.le_succ n

/-- The damped market prices in `[0,1]` when `P` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem damped_mem_Icc {P : History} (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) (φ : Sentence) :
    0 ≤ damped P n φ ∧ damped P n φ ≤ 1 := by
  unfold damped
  have h := hP n φ
  have hd := damping_mem n
  constructor
  · exact mul_nonneg h.1 hd.1
  · calc P n φ * ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ 1 * 1 := mul_le_mul h.2 hd.2 hd.1 zero_le_one
      _ = 1 := one_mul 1

/-- **Uniform closeness:** on day `n` the damped market is within `1/(n+1)` of `P` on every
sentence.
Source: mandate E2 (i)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem damped_dist_le {P : History} (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) (φ : Sentence) :
    |damped P n φ - P n φ| ≤ 1 / ((n : ℝ) + 1) := by
  unfold damped
  have h := hP n φ
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hid : P n φ * ((n : ℝ) / ((n : ℝ) + 1)) - P n φ = -(P n φ / ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [hid, abs_neg, abs_of_nonneg (div_nonneg h.1 hn.le)]
  exact div_le_div_of_nonneg_right h.2 hn.le

/-- **Per-sentence (indeed uniform) asymptotic equality:** `damped P n φ − P n φ → 0` for every `φ`.
Source: mandate E2 (i)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem damped_asympEq {P : History} (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (φ : Sentence) :
    AsympEq (fun n => damped P n φ) (fun n => P n φ) := by
  refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs]
  exact damped_dist_le hP n φ

/-- The damped market is a computable market when `P` is: the table `quote n c · n/(n+1)` is
exact and computable (FAF's `ComputableMarket.ofComputableTable`).
Source: mandate E2 (i) (`ComputableMarket P'`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem damped_computableMarket {P : History} (hP : ComputableMarket P) :
    ComputableMarket (damped P) := by
  obtain ⟨M⟩ := hP.nonemptyComputation
  refine ComputableMarket.ofComputableTable
    (fun n c => M.quote n c * ((n : ℚ) / ((n + 1 : ℕ) : ℚ)))
    (damped_mem_Icc hP.price_mem_Icc) (fun n φ => ?_) ?_
  · unfold damped
    rw [M.quote_exact n φ]
    push_cast
    ring
  · have htab : Computable fun z : ℕ => M.quote z.unpair.1 z.unpair.2 :=
      quote_comp_computable M (Computable.fst.comp Computable.unpair)
        (Computable.snd.comp Computable.unpair)
    have hfac : Computable fun z : ℕ => ((z.unpair.1 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ)) :=
      ratDiv_prim.to_comp.comp (ratNatCast_prim.to_comp.comp (Computable.fst.comp Computable.unpair))
        (ratNatCast_prim.to_comp.comp
          (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.unpair)))
    exact Computable.encode.comp (ratMul_prim.to_comp.comp htab hfac)

/-- **The harmonic exploitation engine for the `⊤`-share trader**: against a `[0,1]`-valued market
with consistent stages whose day-`i` price of `⊤` is at most `1 − 1/(i+1)`, `buyOneDaily ⊤`
exploits — its net worth is `≥ 0` in every world and `≥ ∑_{i ≤ n} 1/(i+1)`, which diverges
(Mathlib's `Real.tendsto_sum_range_one_div_nat_succ_atTop`). FAF's `exploits_of_ge_partialSums_from`
does not apply (no fixed `ε` is met frequently), so this is `Trader.Exploits` by its definition.
Source: mandate E2 (i); FAF `def:exploitation`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem buyOneDaily_top_exploits_harmonic (P : History) (DP : DeductiveProcess)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hgain : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 - P i ⊤) :
    (buyOneDaily ⊤).Exploits P DP := by
  have hpay : ∀ v : PCWorld, v.payout (⊤ : Sentence) = 1 := fun v => by
    unfold PCWorld.payout
    rw [if_pos (PCWorld.holds_top v)]
  constructor
  · refine ⟨0, ?_⟩
    rintro x ⟨n, v, _, rfl⟩
    rw [buyOneDaily_netWorth]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [hpay]
    linarith [(hP i ⊤).2]
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.1 Real.tendsto_sum_range_one_div_nat_succ_atTop (B + 1)
    obtain ⟨v, hv⟩ := hcons N
    have hle := hB ⟨N, v, hv, rfl⟩
    rw [buyOneDaily_netWorth] at hle
    have h2 : ∑ i ∈ Finset.range (N + 1), (1 / ((i : ℝ) + 1)) ≤
        ∑ i ∈ Finset.range (N + 1), (v.payout ⊤ - P i ⊤) :=
      Finset.sum_le_sum fun i _ => by rw [hpay]; exact hgain i
    have h3 := hN (N + 1) (Nat.le_succ N)
    linarith

/-- **E2 (headline). Per-sentence asymptotic equality does not transfer the criterion:** for any
inductor `P` over `DP` with consistent stages, the damped market — a computable market within
`1/(n+1)` of `P` on every sentence — is not a logical inductor over `DP`: `buyOneDaily ⊤` gains
`1 − P n ⊤ · n/(n+1) ≥ 1/(n+1)` on day `n` in every world, a divergent series.
Scope: single market; a fact about FAF's criterion that locates the inductor half (E1 does not
imply it, in either direction).
Source: mandate E2 (i) ("per-sentence asymptotic equality to an inductor does not transfer the criterion"; `def-tracking-pin`'s `relabel_not_inductor` pattern — here the direction is settled)
Kind: P
Fidelity: stronger: the perturbation is uniform in the sentence, not merely per-sentence
Hyps: (a) `hworld` (FAF's disclosed world boundary) -/
theorem damped_not_inductor {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (damped P) DP := by
  intro hLI
  refine hLI.noExploit _ (buyOneDaily_efficientlyComputable ⊤)
    (buyOneDaily_top_exploits_harmonic (damped P) DP
      (damped_mem_Icc (IsLogicalInductor.price_mem_Icc (P := P) (DP := DP))) hworld fun (i : ℕ) => ?_)
  unfold damped
  have h := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) i ⊤
  have hd := damping_mem i
  have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hfac : 1 - ((i : ℝ) / ((i : ℝ) + 1)) = 1 / ((i : ℝ) + 1) := by
    field_simp
    ring
  rw [hcast] at hd ⊢
  calc 1 / ((i : ℝ) + 1) = 1 - ((i : ℝ) / ((i : ℝ) + 1)) := hfac.symm
    _ ≤ 1 - P i ⊤ * ((i : ℝ) / ((i : ℝ) + 1)) := by
        have : P i ⊤ * ((i : ℝ) / ((i : ℝ) + 1)) ≤ 1 * ((i : ℝ) / ((i : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right h.2 hd.1
        linarith

end Cleanroom.Fa.FaEisenstatConj
