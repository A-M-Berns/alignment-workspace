import Cleanroom.Bli.BliCoherentMm.AttemptA.Worlds

/-!
# `bli-coherent-mm` (attempt A) · Payoffs: Soto's intermediate payoffs as finite arithmetic (T8)

**T8 of the mandate** (bli-soto-a-031, 2-003). PDF 04's scheme pays a world share *during* the
run — `1/2^{n−k}` on purchase when `k` of its `n` prime assignments are confirmed and none
refuted, `1/2^{n−k−1} − 1/2^{n−k}` on each further confirmation, `−1/2^{n−k}` on a refutation —
and is **not FAF's market** (FAF pays by world at the end). It is formalized here as finite
arithmetic, disclosed `variant`, with no claim about `Exploits`:

* `intermediateTotal n k := 1 / 2^(n − k)` and **(a)** `intermediateTotal_eq_completionProb`: the
  total received is the uniform-completion probability `(1/2)^(n − k)` of the world (2-003 (i));
  `increments_telescope`: the increments of `j` successive confirmations sum to the difference of
  totals (the scheme's bookkeeping is consistent).
* **(b)** `intermediateTotal_decided`: once every assignment is decided (`k = n`) the total is `1`;
  `bundle_total_decided`: in a decided state, where the true world is `u₀` and every other world
  has been refuted (total `0`), a share of `φ` — the bundle of one share of each `φ`-world —
  totals `1[u₀ ⊨ φ]` (031's telescoping identity, over `FiniteWorld B`).
* **(c)** `split_cash_inequality`: splitting an unrefuted world on a never-decided prime at a
  price `θ < 1/2` gives the cheaper child's share an immediate payoff `(1/2) · 2^{−m}` exceeding
  its cost `θ · P(W)` when `P(W) ≤ 2^{−m}` — a per-step inequality (2-003 (iii)), **not** FAF's
  `Exploits`.

Sources: [[bli-coherent-mm-mandate]] T8; Soto PDF 04 "Propositional coherence" (bli-soto-a-031,
bli-soto-a-2-003).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFinite

/-- **The total intermediate payoff** received so far by a share of a world with `n` prime
assignments of which `k` are confirmed and none refuted: `1 / 2^(n − k)` (PDF 04 p. 1).
Source: [[bli-coherent-mm-mandate]] T8(a); Soto PDF 04 "Propositional coherence"
Kind: D
Fidelity: variant: PDF 04's scheme as arithmetic, not FAF's market -/
def intermediateTotal (n k : ℕ) : ℚ := 1 / 2 ^ (n - k)

/-- The uniform-completion probability of a world with `n − k` undecided assignments.
Source: [[bli-coherent-mm-mandate]] T8(a) (2-003 (i), this run's reading)
Kind: D
Fidelity: n/a -/
def completionProb (n k : ℕ) : ℚ := (1 / 2) ^ (n - k)

/-- **T8(a).** The total received equals the uniform-completion probability of the world.
Source: [[bli-coherent-mm-mandate]] T8(a); bli-soto-a-2-003 (i)
Kind: P
Fidelity: variant (see module docstring)
Hyps: (a) none -/
theorem intermediateTotal_eq_completionProb (n k : ℕ) :
    intermediateTotal n k = completionProb n k := by
  unfold intermediateTotal completionProb
  rw [one_div_pow]

/-- The increment paid on the `i`-th further confirmation after `k` confirmed ones.
Source: Soto PDF 04 p. 1 ("receives `1/2^{n−k−1} − 1/2^{n−k}`")
Kind: D
Fidelity: variant -/
def confirmIncrement (n k i : ℕ) : ℚ := intermediateTotal n (k + i + 1) - intermediateTotal n (k + i)

/-- **The scheme's bookkeeping is consistent**: the increments of `j` successive confirmations
telescope to the difference of totals.
Source: [[bli-coherent-mm-mandate]] T8(a)
Kind: P
Fidelity: variant
Hyps: (a) none -/
theorem increments_telescope (n k j : ℕ) :
    ∑ i ∈ Finset.range j, confirmIncrement n k i = intermediateTotal n (k + j) - intermediateTotal n k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      unfold confirmIncrement
      ring_nf

/-- **T8(b).** Once every assignment is decided (all `n` confirmed) the total is `1`.
Source: [[bli-coherent-mm-mandate]] T8(b); bli-soto-a-031
Kind: L
Fidelity: variant -/
theorem intermediateTotal_decided (n : ℕ) : intermediateTotal n n = 1 := by
  simp [intermediateTotal]

open Classical in
/-- **T8(b), the bundle identity.** In a decided state — the true world `u₀` fully confirmed
(total `1`), every other world refuted (total `0`) — a share of `φ`, i.e. one share of every
world holding `φ`, totals `1[u₀ ⊨ φ]`: the payoff of `φ` is its truth value, 031's claim as a
finite identity over `FiniteWorld B`.
Source: [[bli-coherent-mm-mandate]] T8(b); bli-soto-a-031
Kind: P
Fidelity: variant (decided state only; the undecided case is the finding F9)
Hyps: (a) none -/
theorem bundle_total_decided {B : ℕ} (u₀ : FiniteWorld B) (φ : Sentence) :
    ∑ u ∈ Finset.univ.filter (fun u : FiniteWorld B => (worldOf u).Holds φ),
        (if u = u₀ then (1 : ℚ) else 0) = u₀.payoutRat φ := by
  rw [Finset.sum_ite_eq' (Finset.univ.filter fun u : FiniteWorld B => (worldOf u).Holds φ) u₀,
    payoutRat_eq_ite]
  simp

/-- **T8(c), the per-step cash inequality** behind 2-003 (iii): if the child world's share pays
`(1/2) · 2^{−m}` at once and is bought at price `θ < 1/2` on a parent of mass `P ≤ 2^{−m}`, the
immediate payoff exceeds the cost. A single-step inequality; nothing about `Exploits`.
Source: [[bli-coherent-mm-mandate]] T8(c); bli-soto-a-2-003 (iii) (this run's observation)
Kind: L
Fidelity: variant
Hyps: (a) `hθ0`, `hθ`, `hP` -/
theorem split_cash_inequality {θ P : ℚ} (m : ℕ) (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hP : P ≤ 1 / 2 ^ m) : θ * P < 1 / 2 * (1 / 2 ^ m) := by
  calc θ * P ≤ θ * (1 / 2 ^ m) := mul_le_mul_of_nonneg_left hP hθ0
    _ < 1 / 2 * (1 / 2 ^ m) := by
        apply mul_lt_mul_of_pos_right hθ
        positivity

end Cleanroom.Bli.BliCoherentMm.AttemptA
