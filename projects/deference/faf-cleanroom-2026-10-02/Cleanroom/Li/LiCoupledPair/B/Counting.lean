import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.WellFounded

/-!
# `li-coupled-pair` · B · Counting: the quote stream costs less than `t²` (T2.2)

anson-2-007 (chat 04, L686–703): "at any stage `t` the conjunction `Q_A^{(t)}` ranges only over
quotes whose entire production finished at some stage `e(i) < t`, so `Λ(i) < t` for each. Since
`e` is strictly increasing, at most `t − 1` indices satisfy `e(i) < t`, so recomputing all of them
from scratch costs at most `∑_{i : e(i) < t} Λ(i) < t²`." Here `Λ i` is the production cost of
quote `i` and `e i ≥ Λ i` its publication stage.

Pure arithmetic over `ℕ`: FAF has no runtime model for quote production (li-quote-lane findings
F8), so the sequence-level statement is the only one available — Fidelity `variant:
sequence-level`. The clocked ledger of `Clocked.lean` is where the sentence "`H⁺` never computes a
quote before the quote is published" lives over FAF: there the position *is* the fuel.

**On the source's sentence.** (i) *Retracted in repair round 1* (audit r1 adversarial B1 /
fidelity B3): angle B's finding F-B4 said the count "at most `t − 1` indices" is off by one,
because with `e = id` exactly `t` indices `0, …, t − 1` satisfy `e(i) < t`. That is a fact about
this file's 0-based restatement (`e : ℕ → ℕ`, window `range t`), not about the source: the chat
fixes `e` as "strictly increasing from `ℕ⁺` to `ℕ⁺`" (chat 04 L445), so `e(i) ≥ i` and `e(i) < t`
forces `1 ≤ i ≤ t − 1` — at most `t − 1` indices, exactly as written. The Lean proves the weaker
`≤ t · (t − 1)` over its `t`-term window (`quoteStream_cost_le`), which still gives the chat's
`< t²` (`quoteStream_cost_lt_sq`); under the chat's convention the sharper `(t − 1)²` holds.
(ii) Strict monotonicity is used only to confine the index set to `i < t` (`i ≤ e i < t`); the
bound itself needs nothing of `e` (`quoteStream_cost_le` takes no monotonicity;
`quoteStream_cost_le_window` is where it enters). Scope: one-way.
-/

namespace Cleanroom.Li.LiCoupledPair.B

open Finset

/-- **T2.2: the cost of the quotes published by stage `t` is at most `t · (t − 1)`.** Each
published quote `i < t` with `e i < t` costs `Λ i ≤ e i ≤ t − 1`, and there are at most `t` of
them. No monotonicity of `e` is used.
Source: anson-2-007 (chat 04 L686–703, "costs at most `∑_{i: e(i)<t} Λ(i) < t²`"); mandate T2.2
Kind: P
Fidelity: variant: sequence-level (FAF has no runtime model for quote production); exact bound `t(t−1)`, the source's `< t²` is `quoteStream_cost_lt_sq`
Hyps: (a) none (`hΛ` is the source's own `e(i) ≥ Λ(i)`) -/
theorem quoteStream_cost_le (e Λ : ℕ → ℕ) (hΛ : ∀ i, Λ i ≤ e i) (t : ℕ) :
    (∑ i ∈ (range t).filter (fun i => e i < t), Λ i) ≤ t * (t - 1) := by
  calc (∑ i ∈ (range t).filter (fun i => e i < t), Λ i)
      ≤ ∑ _i ∈ (range t).filter (fun i => e i < t), (t - 1) := by
        apply sum_le_sum
        intro i hi
        have h1 := (mem_filter.mp hi).2
        have h2 := hΛ i
        omega
    _ = ((range t).filter (fun i => e i < t)).card * (t - 1) :=
        sum_const_nat fun _ _ => rfl
    _ ≤ t * (t - 1) := by
        apply Nat.mul_le_mul_right
        exact (card_filter_le _ _).trans (by simp)

/-- **The source's `< t²`**, for `t ≥ 1` (at `t = 0` the sum is `0 = t²`; the source's strict
inequality needs `t ≥ 1`).
Source: anson-2-007 (chat 04 L686–703); mandate T2.2
Kind: L
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem quoteStream_cost_lt_sq (e Λ : ℕ → ℕ) (hΛ : ∀ i, Λ i ≤ e i) (t : ℕ) (ht : 1 ≤ t) :
    (∑ i ∈ (range t).filter (fun i => e i < t), Λ i) < t * t :=
  lt_of_le_of_lt (quoteStream_cost_le e Λ hΛ t)
    ((Nat.mul_lt_mul_left (by omega : 0 < t)).mpr (by omega))

/-- **Where strict monotonicity enters**: for `e` strictly increasing every index with `e i < t`
is below `t` (`i ≤ e i`), so the window `range t` loses nothing — the sum over *any* window
`range N` of the published indices is bounded by the same `t · (t − 1)`. This is the source's
"since `e` is strictly increasing" clause, used for the index set and nothing else.
Source: anson-2-007 (chat 04 L686–703, "since `e` is strictly increasing, at most … indices satisfy `e(i) < t`")
Kind: P
Fidelity: variant: sequence-level
Hyps: (a) none -/
theorem quoteStream_cost_le_window (e Λ : ℕ → ℕ) (he : StrictMono e) (hΛ : ∀ i, Λ i ≤ e i)
    (t N : ℕ) :
    (∑ i ∈ (range N).filter (fun i => e i < t), Λ i) ≤ t * (t - 1) := by
  calc (∑ i ∈ (range N).filter (fun i => e i < t), Λ i)
      ≤ ∑ i ∈ (range t).filter (fun i => e i < t), Λ i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [mem_filter] at hi ⊢
          refine ⟨mem_range.mpr ?_, hi.2⟩
          exact lt_of_le_of_lt (he.id_le i) hi.2
        · intros; exact Nat.zero_le _
    _ ≤ t * (t - 1) := quoteStream_cost_le e Λ hΛ t

/-- **N+ instance**: `e i = 2i + 1` (strictly increasing, not the identity), `Λ i = i + 1`
(not constant, `Λ i ≤ e i`), `t = 4`: the published indices are `{0, 1}` — a proper, non-empty
part of the window — and the cost is `1 + 2 = 3 ≤ 12`.
Source: mandate T2.2 (N+)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem quoteStream_cost_instance :
    ((range 4).filter (fun i => 2 * i + 1 < 4)) = {0, 1} ∧
      (∑ i ∈ (range 4).filter (fun i => 2 * i + 1 < 4), (i + 1)) = 3 ∧
      (3 : ℕ) ≤ 4 * (4 - 1) ∧ StrictMono (fun i : ℕ => 2 * i + 1) ∧
      (∀ i : ℕ, i + 1 ≤ 2 * i + 1) := by
  refine ⟨by decide, by decide, by omega, ?_, fun i => by omega⟩
  intro a b hab
  simp only
  omega

end Cleanroom.Li.LiCoupledPair.B
