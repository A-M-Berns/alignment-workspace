import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-self-trust` — target 11: soft threshold conditioning is directed; the converse fails degenerately

trust-lab-2-023 (Idea 6): the soft update `E_n^{X,t,δ}(·) := E_n(· · Ind_δ(E(X) > t)) /
E_n(Ind_δ(E(X) > t))` never lowers the estimate of `X` below `t` (directed) — a corollary of
`est`; and the converse question, whether directedness of every soft update characterizes
inductors among price sequences, which the note suspects is false.

* **11a** (`softUpdate_directed`): from `est`, for every `κ > 0` and `ε > 0`, eventually on
  every day of conditioning mass `≥ κ` the soft update is `≥ s − ε`. **Never stated without the
  mass bound**: Lean's `x / 0 = 0` would make the normalized form trivially satisfiable.
* **11b** (`constHalf_softUpdate_directed`, `constHalf_not_inductor`): the constant history
  `P₀ n φ := 1/2` satisfies every directed soft update (every expectation is `1/2`, every
  quotient `1`) and is not a logical inductor over `paperDP 𝗣𝗔` (`lic_provind_true` at the
  theorem family `⊤` would force its price to `1`). So "directedness of all soft threshold
  updates characterizes inductors among price sequences" is refuted — degenerately
  (ATTRIBUTION-UNVETTED as a reading of the note, which itself suspects the converse false);
  the surviving neighbour (restriction to histories that fail some directedness instance) is
  OPEN and not attempted.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

/-- The soft (normalized) update: `E_n(XW_n) / E_n(W_n)`. Junk value: Lean's `x / 0 = 0` when the
conditioning mass vanishes — every theorem below carries a mass bound.
Source: trust-lab-2-023 (Idea 6, the soft update)
Kind: D
Fidelity: exact (with the junk value disclosed) -/
def softUpdate (P : History) (W XW : ℕ → LUV) (n : ℕ) : ℝ :=
  (XW n).expect P n / (W n).expect P n

/-- **The soft update is directed** (11a): for the self-expert over the paper's inductor, every
ramp quote `(W, XW)` at `(s, δ)`, every mass bound `κ > 0` and every `ε > 0`, eventually on
every day with conditioning mass `E_n(W_n) ≥ κ` the update is `≥ s − ε`. From `est`
(`selfSoftTotalTrustAbove`) at tolerance `ε κ`, divided by the mass.
Source: trust-lab-2-023 (forward direction: "Self-Trust says it never lowers the estimate of
`X` below `t`"); DDB fn 35
Kind: C
Fidelity: variant: product within the quote's slack; stated with the mass bound (never without)
Hyps: (a); `hinj` -/
theorem softUpdate_directed (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    (f : DeferralFunction) (hinj : Function.Injective f.f) (s : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (X W XW : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (q : WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
      (rampAbove δ s) W XW) (κ : ℝ) (hκ : 0 < κ) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, κ ≤ (W n).expect (liaHistory (paperDP T)) n →
      (s : ℝ) - ε ≤ softUpdate (liaHistory (paperDP T)) W XW n := by
  have hest := selfSoftTotalTrustAbove T f hinj s hδ X W XW hX q
  intro ε hε
  filter_upwards [hest (ε * κ) (by positivity)] with n hn hmass
  have hpos : 0 < (W n).expect (liaHistory (paperDP T)) n := lt_of_lt_of_le hκ hmass
  unfold softUpdate
  rw [le_div_iff₀ hpos]
  nlinarith [hn, hmass]

/-! ## 11b — the degenerate refutation of the converse -/

/-- The constant history at `1/2`.
Source: trust-lab-2-023 (the converse's suspected refutation: "a history constant at a coherent
limit value")
Kind: D
Fidelity: n/a -/
def constHalf : History := fun _ _ => (1 / 2 : ℝ)

/-- Every expectation of the constant history is `1/2`.
Source: none: infrastructure (FAF `LUV.expect`, `expectApprox`)
Kind: L
Fidelity: n/a -/
theorem constHalf_expect (X : LUV) (n : ℕ) : X.expect constHalf n = 1 / 2 := by
  simp only [LUV.expect, LUV.expectApprox, constHalf, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The constant history satisfies every directed soft update**: for every `W XW`, every
threshold `s ≤ 1`, every `ε > 0`, on every day (the mass is `1/2 > 0`) the update is `1 ≥ s − ε`.
Source: trust-lab-2-023 (converse, refuted degenerately)
Kind: N−
Fidelity: n/a (a degenerate instance: all expectations constant) -/
theorem constHalf_softUpdate_directed (W XW : ℕ → LUV) (s : ℝ) (hs : s ≤ 1) :
    ∀ ε > (0 : ℝ), ∀ n, softUpdate constHalf W XW n = 1 ∧ s - ε ≤ softUpdate constHalf W XW n := by
  intro ε hε n
  have h : softUpdate constHalf W XW n = 1 := by
    unfold softUpdate
    rw [constHalf_expect, constHalf_expect]
    norm_num
  exact ⟨h, by rw [h]; linarith⟩

/-- **The constant history is not a logical inductor** over `paperDP 𝗣𝗔`: `thm:provind` at the
constant theorem family `⊤` would force its price to `1`, but it is `1/2`.
Source: trust-lab-2-023 (converse); FAF `lic_provind_true`
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem constHalf_not_inductor : ¬ IsLogicalInductor constHalf (paperDP 𝗣𝗔) := by
  intro hLI
  have h := lic_provind_true constHalf (paperDP 𝗣𝗔) (fun _ => (⊤ : Sentence))
    (MachineSentenceCodes.const ⊤) (fun _ v _ => holds_verum v) (paperDP_hworld 𝗣𝗔)
  have h' : Tendsto (fun n => constHalf n ⊤ - 1) atTop (𝓝 0) := h
  have hc : (fun n => constHalf n (⊤ : Sentence) - 1) = fun _ => (-(1 / 2) : ℝ) := by
    funext n; simp [constHalf]; norm_num
  rw [hc] at h'
  have := tendsto_nhds_unique h' tendsto_const_nhds
  norm_num at this

/-- **The converse of 11a fails, degenerately**: a history that satisfies every directed soft
update (at thresholds `≤ 1`) and is not a logical inductor.
Source: trust-lab-2-023 (the converse question); mandate target 11b
Kind: N−
Fidelity: n/a (degenerate refutation: constant prices; the surviving neighbour is OPEN)
Hyps: (a) -/
theorem softUpdate_converse_refuted :
    (∀ W XW : ℕ → LUV, ∀ s : ℝ, s ≤ 1 → ∀ ε > (0 : ℝ), ∀ n,
        s - ε ≤ softUpdate constHalf W XW n) ∧
      ¬ IsLogicalInductor constHalf (paperDP 𝗣𝗔) :=
  ⟨fun W XW s hs ε hε n => (constHalf_softUpdate_directed W XW s hs ε hε n).2,
    constHalf_not_inductor⟩

end

end Cleanroom.Deference.DefSelfTrust
