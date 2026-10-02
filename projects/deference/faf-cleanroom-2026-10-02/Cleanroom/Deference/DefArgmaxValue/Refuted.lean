import Cleanroom.Deference.DefArgmaxValue.LiarProbe
import Cleanroom.Deference.DefSqueezeDiamond.Diamond
import Cleanroom.Deference.DefSelfTrust.GateCollapse
import Cleanroom.Deference.DefSelfTrust.SelfInstances
import Cleanroom.Found.DefLattice.Witness

/-!
# `def-argmax-value` · Refuted: the four computations of the liar probe (targets 1c–1d, 2)

On the probe menu `{1[χ_n], const s}` of `LiarProbe.lean`, with the honest follower `S` valued
`s · 1[χ_n]` and the pins `P_{f n}(χ_n) → s`, `P_n(χ_n) → s`, `s_{f n} → s`:

1. **H3 fails** (target 4c's N−): `Σ_j E*(Q^j) → s²` while `Σ_j E*(I^j)·m^j → (1−s)s + s² = s`,
   deficit `→ −s(1−s) < 0` (`probe_condStable_deficit_tendsto`, `condStableOn_probe_refuted`,
   `condStable_refuted`).
2. **Value fails**: `E^P_n(S_n) ≈ₙ s·P_n(χ_n) → s² < s ← E^P_n(const s)` (`value_refuted`) — the
   instance of `Value` at `k = 1`, this menu, this follower, `i = 1`.
3. **The hard above-threshold inequality at `(O^0, s)` with the sharp selection bit fails by
   `s(1−s)`**: `E^P_n(O^0·1[sel=0]) − s·E^P_n(1[sel=0]) → 0 − s(1−s)` (`hardAbove_probe_tendsto`),
   stated as the real-number form (see its docstring for the relation to `def-lattice`'s
   `ThresholdIneqAbove (hardAbove s)`).
4. **Soft Total Trust holds**: `selfTotalTrust` (`softTotalTrust_probe`).

Also `¬ SelfEndorsesGE`, `¬ SelfEndorses`, exact F1 refuted (1d), and target 2:
`mart_implies_value_refuted` (`TowerValued ∧ ¬ Value` for the self-expert) and the
one-row moral `all_epistemic_notions_hold_and_value_fails`.

Single market (self); `0 < s < 1`; `f` strictly increasing; instance lines at `𝗣𝗔`,
`succDeferral`, `s = ½` (Death in Damascus).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open Cleanroom.Li.LiDiagonal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- `≳ₙ` against a pointwise smaller lower sequence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_of_asympGE_of_le {a b c : ℕ → ℝ} (h : a ≳ₙ b) (hcb : ∀ n, c n ≤ b n) :
    a ≳ₙ c :=
  fun ε hε => (h ε hε).mono (fun n hn => (hcb n).trans hn)

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-! ## The five limits -/

/-- The deferred-day estimate of the follower: `E*(S_n) ≈ₙ s · P_{f n}(χ_n)` (deferred provind on
`S − s·1[χ]`, valued `0`).
Source: mandate target 1c ("deferred-day provind on `S`")
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem probeFollower_estimate (hf : StrictlyIncreasingDeferral f) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (probeFollower T f s hs.1 n).expect (liaHistory (paperDP T)) (f n)) ≈ₙ
      (fun n => (s : ℝ) * (liaHistory (paperDP T)) (f n) (liarSentence T f s hs.1 n)) := by
  have h := expect_deferred_const_mul (P := liaHistory (paperDP T)) (DP := paperDP T) f hf s
    (X := fun n => literalIndicator (liarSentence T f s hs.1 n))
    (literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs.1))
    (probeFollower_codes T f s hs.1)
    (fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩) (fun _ => 0)
    tendsto_const_nhds
    (fun n v hv x hx => ⟨(s : ℝ) * v.payout (liarSentence T f s hs.1 n),
      probeFollower_valuesAt T f s hs n v hv, by
        rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]; simp⟩) (paperDP_hworld T)
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [literalIndicator_expect]

/-- The present-day expectation of the follower: `E^P_n(S_n) ≈ₙ s · P_n(χ_n)` (`thm:expprovind`
with the constant feature `s`, `def-self-trust`'s `gateKnowledge_product`).
Source: mandate target 1c ("`E^P_n(S_n) ≈ₙ s · P_n(χ_n)`")
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem probeFollower_expect (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (probeFollower T f s hs.1 n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (s : ℝ) * (liaHistory (paperDP T)) n (liarSentence T f s hs.1 n)) := by
  have h := gateKnowledge_product (P := liaHistory (paperDP T)) (DP := paperDP T)
    (Cleanroom.Found.DefLattice.Witness.sGenerable T s) (fun _ => hs)
    (X := fun n => literalIndicator (liarSentence T f s hs.1 n))
    (literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs.1))
    (fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩)
    (probeFollower_codes T f s hs.1) (slack := fun _ => 0) tendsto_const_nhds
    (fun n v hv x hx => ⟨(s : ℝ) * v.payout (liarSentence T f s hs.1 n),
      probeFollower_valuesAt T f s hs n v hv, by
        rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]; simp [mul_comm]⟩)
    (paperDP_hworld T)
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [literalIndicator_expect]

/-- The deferred price of the negated liar: `P_{f n}(∼χ_n) → 1 − s`.
Source: none: infrastructure (`deferred_neg_coherence` and the deferred pin)
Kind: L
Fidelity: n/a -/
theorem liarNegPrice_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (∼ liarSentence T f s hs0.le n)) atTop
      (𝓝 (1 - (s : ℝ))) := by
  have h1 := tendsto_of_asympEq_const (deferred_neg_coherence (P := liaHistory (paperDP T))
    (DP := paperDP T) f hf (liarSentence_codes T f s hs0.le) (paperDP_hworld T))
  have h2 := liarPrice_tendsto_s T f s hf hs0 hs1
  have := h1.sub h2
  refine (tendsto_congr (fun n => ?_)).mp this
  ring

/-- The present price of the negated liar: `P_n(∼χ_n) → 1 − s`.
Source: none: infrastructure (li-diagonal `neg_coherence` and the present pin)
Kind: L
Fidelity: n/a -/
theorem liarNegPresentPrice_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) n (∼ liarSentence T f s hs0.le n)) atTop
      (𝓝 (1 - (s : ℝ))) := by
  have h1 := tendsto_of_asympEq_const (neg_coherence (liaHistory (paperDP T)) (paperDP T) _
    (liarSentence_codes T f s hs0.le) (paperDP_hworld T))
  have h2 := liarPresentPrice_tendsto_s T f s hf hs0 hs1
  have := h1.sub h2
  refine (tendsto_congr (fun n => ?_)).mp this
  ring

/-! ## 1c(1) — conditional-stability fails on the probe (target 4c's N−) -/

/-- **The H3 deficit on the probe converges to `−s(1−s)`**: left side `Σ_j E*(Q^j_n) → 0 + s²`,
right side `Σ_j E*(I^j_n)·m^j_n → (1−s)·s + s·s = s`.
Source: [[loop-direction]] §The liar probe, computation (1); mandate target 1c(1), 4c (N−)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem probe_condStable_deficit_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    Tendsto (fun n =>
      (∑ j, (selfExpert T f).estimate (probeQ T f s hs0.le j) n) -
        ∑ j, (selfExpert T f).estimate (probeI T f s hs0.le j) n *
          (probeMenu T f s hs0.le).quote (selfExpert T f) j n) atTop
      (𝓝 (-((s : ℝ) * (1 - s)))) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  have hp := liarPrice_tendsto_s T f s hf hs0 hs1
  have hnp := liarNegPrice_tendsto T f s hf hs0 hs1
  have hthr := probeThreshold_tendsto T f s hs
  have hS : Tendsto (fun n => (probeFollower T f s hs.1 n).expect (liaHistory (paperDP T)) (f n) -
      (s : ℝ) * (liaHistory (paperDP T)) (f n) (liarSentence T f s hs.1 n)) atTop (𝓝 0) :=
    probeFollower_estimate T f s hf hs
  have h0 := constZero_estimate_tendsto T f hf
  have hleft : Tendsto (fun n => ∑ j, (selfExpert T f).estimate (probeQ T f s hs0.le j) n) atTop
      (𝓝 ((s : ℝ) * s)) := by
    have := h0.add ((hS.add (hp.const_mul (s : ℝ))))
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    simp only [Fin.sum_univ_two, probeQ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Expert.self_estimate]
    try ring
  have hright : Tendsto (fun n => ∑ j, (selfExpert T f).estimate (probeI T f s hs0.le j) n *
      (probeMenu T f s hs0.le).quote (selfExpert T f) j n) atTop (𝓝 (s : ℝ)) := by
    have := (hnp.mul hp).add (hp.mul hthr)
    refine (tendsto_congr (fun n => ?_)).mp (by
      have e : (1 - (s : ℝ)) * s + s * s = s := by ring
      rw [e] at this; exact this)
    simp only [Fin.sum_univ_two, probeI, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Expert.self_estimate, literalIndicator_expect,
      probeMenu_O_zero, probeMenu_O_one, ← probeThreshold_cast]
    try ring
  have := hleft.sub hright
  refine (tendsto_congr (fun n => rfl)).mp (by
    have e : (s : ℝ) * s - s = -(s * (1 - s)) := by ring
    rw [e] at this; exact this)

/-- **Conditional-stability fails on the probe** (target 4c, N−): the global scope condition is
refutable on a single menu, which is what makes H3 a condition on the menu and not a property
of the pair.
Source: [[loop-direction]] §The liar probe (1); [[total-trust-implies-value]] §Necessity (the
constant-probe variant); mandate target 4c
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_probe_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ CondStableOn (probeMenu T f s hs0.le) (probePackage T f s ⟨hs0.le, hs1.le⟩) :=
  not_asympGE_of_tendsto_neg (c := -((s : ℝ) * (1 - s)))
    (by have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
        have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
        nlinarith)
    (probe_condStable_deficit_tendsto T f s hf hs0 hs1)

/-- **The global form `CondStable` is false for the self-expert** (at every `s ∈ (0,1)`, every
strictly increasing deferral).
Source: mandate target 4b ("defined and immediately refuted")
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStable_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ CondStable (paperDP T) (selfExpert T f) :=
  fun h => condStableOn_probe_refuted T f s hf hs0 hs1
    (h 1 _ (probeMenu_valued T f s ⟨hs0.le, hs1.le⟩) _ _ _)

/-! ## 1c(2) — Value fails -/

/-- **Unconditional argmax Value is refuted for the self-expert over FAF's inductor** (target 1c(2),
load-bearing 1): on the probe menu with the honest follower,
`E^P_n(S_n) ≈ₙ s·P_n(χ_n) → s² < s ← E^P_n(const s)`, so the `Value` instance at `i = 1` fails.
Source: [[loop-direction]] §The liar probe (2); [[deference-notions]] §Value ⚠ 2026-07-25
("for inductor-experts, unconditional argmax Value is false"); lean-deference-066
Kind: refuted
Fidelity: exact (`def-lattice`'s `Value`, instantiated at `probeMenu`)
Hyps: (a); `hf` -/
theorem value_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ Value (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) := by
  intro hV
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  have h := hV 1 (probeMenu T f s hs.1) (probeMenu_valued T f s hs) (probeFollower T f s hs.1)
    (probeFollower_codes T f s hs.1) (probeFollower_follows T f s hs) 1
  simp only [probeMenu_O_one] at h
  refine not_asympGE_of_tendsto_neg (c := (s : ℝ) * s - s) ?_ ?_ h
  · have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    nlinarith
  · have hS := probeFollower_expect T f s hs
    unfold AsympEq at hS
    have hpn := liarPresentPrice_tendsto_s T f s hf hs0 hs1
    have hc := tendsto_of_asympEq_const (expect_constLUV_asympEq (P := liaHistory (paperDP T))
      (DP := paperDP T) hs (paperDP_hworld T))
    have := (hS.add (hpn.const_mul (s : ℝ))).sub hc
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    ring

/-! ## Self-endorsement fails (1c, 1d) -/

/-- **The one-sided self-endorsement instance fails on the probe**:
`E*(S_n) ≈ₙ s·P_{f n}(χ_n) → s² < s ← s_{f n} ≤ M_n`.
Source: mandate target 1c ("`¬ SelfEndorsesGE`: `E*(S_n) ≈ₙ s · P_{f n}(χ_n) → s² < s ≤ M_n − o(1)`")
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem selfEndorseGE_instance_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ ((fun n => (selfExpert T f).estimate (probeFollower T f s hs0.le) n) ≳ₙ
        (fun n => (probeMenu T f s hs0.le).maxQuote (selfExpert T f) n)) := by
  intro h
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  have h' : (fun n => (selfExpert T f).estimate (probeFollower T f s hs0.le) n) ≳ₙ
      (fun n => ((probeThreshold T f s n : ℚ) : ℝ)) :=
    asympGE_of_asympGE_of_le h (fun n => by
      rw [← probeMenu_quote_one T f s hs.1 n]
      exact Menu.quote_le_maxQuote _ _ _ _)
  refine not_asympGE_of_tendsto_neg (c := (s : ℝ) * s - s) ?_ ?_ h'
  · have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    nlinarith
  · have hS := probeFollower_estimate T f s hf hs
    unfold AsympEq at hS
    have hp := liarPrice_tendsto_s T f s hf hs0 hs1
    have hthr := probeThreshold_tendsto T f s hs
    have := (hS.add (hp.const_mul (s : ℝ))).sub hthr
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    simp only [Expert.self_estimate]
    try ring

/-- **`SelfEndorsesGE` is refuted for the self-expert** (the hypothesis Mart ⟹ Value spends,
`def-squeeze-diamond` `value_of_towerValued_of_selfEndorseGE`, is false on the probe).
Source: mandate target 1c; `def-squeeze-diamond` findings K5
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem selfEndorsesGE_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ SelfEndorsesGE (paperDP T) (selfExpert T f) :=
  fun h => selfEndorseGE_instance_refuted T f s hf hs0 hs1
    (h 1 _ (probeMenu_valued T f s ⟨hs0.le, hs1.le⟩) _ (probeFollower_codes T f s hs0.le)
      (probeFollower_follows T f s ⟨hs0.le, hs1.le⟩))

/-- **Two-sided `SelfEndorses` is refuted** (a fortiori).
Source: mandate target 1d; lean-deference-064 (the asymptotic form of exact F1)
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem selfEndorses_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ SelfEndorses (paperDP T) (selfExpert T f) :=
  fun h => selfEndorsesGE_refuted T f s hf hs0 hs1 (SelfEndorsesGE.of_selfEndorses h)

/-- **Exact F1 is refuted** (target 1d, lean-deference-064): `Γ ⊢ E*(Ŝ_n) = M_n` — here the
exact identity `∀ n, E*(S_n) = M_n` on the probe — is false; so is its asymptotic form
(`selfEndorseGE_instance_refuted`). The surviving neighbours: `SelfEndorsesGE`'s instance on
conditional-stable menus (`Theorem.lean`) and soft self-endorsement (`Hedged.lean`).
Source: lean-deference-064; mandate target 1d
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem exactF1_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ (∀ n, (selfExpert T f).estimate (probeFollower T f s hs0.le) n =
        (probeMenu T f s hs0.le).maxQuote (selfExpert T f) n) := by
  intro h
  apply selfEndorseGE_instance_refuted T f s hf hs0 hs1
  have : (fun n => (selfExpert T f).estimate (probeFollower T f s hs0.le) n) =
      (fun n => (probeMenu T f s hs0.le).maxQuote (selfExpert T f) n) := funext h
  rw [this]
  exact (AsympEq.refl _).asympGE

/-! ## 1c(3)–(4) — the hard inequality fails, soft Total Trust holds -/

/-- **The hard above-threshold inequality at `(O^0, s)` with the sharp selection bit fails by
`s(1−s)`** (target 1c(3)), in the real-number form: with `W_n := 1[∼χ_n] = 1[sel_n = 0]` and
the product `O^0_n · W_n = 1[χ_n]·1[∼χ_n] = 0`, `E^P_n(O^0 W_n) − s·E^P_n(W_n) → 0 − s(1−s)`.
Register: `def-lattice`'s `ThresholdIneqAbove (hardAbove s)` takes the weight `1[s ≤ E*(O^0_n)]`
at the *fixed* threshold `s`, while the menu's selection bit is `1[s_{f n} ≤ P_{f n}(χ_n)]` at the
mesh value `s_{f n} ∈ [s, s + 1/(f n+1))`; the two coincide except on days with
`s ≤ P_{f n}(χ_n) < s_{f n}`, which are not known to be finite, so the `WeightQuote` at
`hardAbove s` is not the selection bit, and this theorem states the page's computation with the
page's weight (the selection bit). The fixed-threshold hard faces are refuted by
`def-squeeze-diamond`'s `hardTotalTrust_refuted_paper` (both faces at `½`).
Source: [[loop-direction]] §The liar probe (3); mandate target 1c(3)
Kind: C
Fidelity: variant: real-number form with the selection bit as weight (see register)
Hyps: (a); `hf` -/
theorem hardAbove_probe_tendsto (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (constLUV 0).expect (liaHistory (paperDP T)) n -
      (s : ℝ) * (literalIndicator (∼ liarSentence T f s hs0.le n)).expect (liaHistory (paperDP T)) n)
      atTop (𝓝 (-((s : ℝ) * (1 - s)))) := by
  have h0 := tendsto_of_asympEq_const (expect_constLUV_asympEq (P := liaHistory (paperDP T))
    (DP := paperDP T) (s := 0) ⟨le_rfl, zero_le_one⟩ (paperDP_hworld T))
  have hn := liarNegPresentPrice_tendsto T f s hf hs0 hs1
  have := h0.sub (hn.const_mul (s : ℝ))
  refine (tendsto_congr (fun n => ?_)).mp (by
    have e : ((0 : ℚ) : ℝ) - (s : ℝ) * (1 - s) = -(s * (1 - s)) := by push_cast; ring
    rw [e] at this; exact this)
  simp [literalIndicator_expect]

/-- **Soft Total Trust holds on the pair the probe refutes everything else on** (target 1c(4)):
`def-self-trust`'s `selfTotalTrust`, cited.
Source: [[loop-direction]] §The liar probe (4); mandate target 1c(4)
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem softTotalTrust_probe (hf : StrictlyIncreasingDeferral f) :
    TotalTrust (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) :=
  selfTotalTrust T f hf.injective

/-! ## Target 2 — Mart ⟹ Value refuted; the small impossibility -/

/-- **Mart ⟹ Value is refuted, not merely unproved** (target 2a, load-bearing 2). Source sentence
([[value-iff-mart]] ⚠ 2026-07-27 l. 20): "Mart ⟹ Value … is refuted for inductor-experts by the
punishing menu". Reading: Mart = `TowerValued` (Tower on valued sources, `def-squeeze-diamond`
decision 2 — a theorem for the self-expert, `selfTower_valued`), Value = `def-lattice`'s
unconditional predicate, the pair = the self-instance over FAF's inductor at any strictly
increasing deferral; the menu is the liar probe at `s`, the follower `probeFollower`. Surviving
neighbours: `value_of_towerValued_of_selfEndorseGE` (Value under one-sided self-endorsement,
itself refuted here) and the scoped theorem on conditional-stable menus (`Theorem.lean`).
Source: lean-deference-066; vq-wiki-008(b); [[value-iff-mart]] l. 20; `def-squeeze-diamond`
findings K5
Kind: refuted
Fidelity: exact (`TowerValued` is Mart on valued sources)
Hyps: (a); `hf` -/
theorem mart_implies_value_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    TowerValued (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) ∧
      ¬ Value (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) :=
  ⟨fun X Y hX hY hval hR => selfTower_valued T f X Y hX hY hval hR,
    value_refuted T f s hf hs0 hs1⟩

/-- **The small impossibility, one row** (target 2b): for the self-expert, Total Trust, Mart
(on valued sources), the conditional tower and band Reflection are all theorems, and Value
fails — no epistemic hypothesis on the pair implies unconditional Value; what fixes Value
restricts Value's own quantifier (`CondStableOn`, `Theorem.lean`).
Source: the arc l. 2469 ("no hypothesis quantified over all e.d. LUV sequences, however strong,
can imply Value quantified over all e.d. menus"); mandate target 2b
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem all_epistemic_notions_hold_and_value_fails (hf : StrictlyIncreasingDeferral f)
    (hs0 : 0 < s) (hs1 : s < 1) :
    TotalTrust (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) ∧
      TowerValued (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) ∧
      CondTower (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) ∧
      BandReflection (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) ∧
      ¬ Value (liaHistory (paperDP T)) (paperDP T) (selfExpert T f) :=
  ⟨selfTotalTrust T f hf.injective,
    fun X Y hX hY hval hR => selfTower_valued T f X Y hX hY hval hR,
    selfCondTower T f, bandReflection_self T f hf, value_refuted T f s hf hs0 hs1⟩

/-! ## Instance lines (`𝗣𝗔`, `succDeferral`, `s = ½`: Death in Damascus) -/

example : ¬ Value (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  value_refuted 𝗣𝗔 succDeferral (1 / 2) Cleanroom.Found.LiQuoteLane.succDeferral_strict
    (by norm_num) (by norm_num)

example : ¬ SelfEndorsesGE (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  selfEndorsesGE_refuted 𝗣𝗔 succDeferral (1 / 2) Cleanroom.Found.LiQuoteLane.succDeferral_strict
    (by norm_num) (by norm_num)

example : ¬ CondStable (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  condStable_refuted 𝗣𝗔 succDeferral (1 / 2) Cleanroom.Found.LiQuoteLane.succDeferral_strict
    (by norm_num) (by norm_num)

example : TowerValued (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) ∧
    ¬ Value (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) (selfExpert 𝗣𝗔 succDeferral) :=
  mart_implies_value_refuted 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

end

end Cleanroom.Deference.DefArgmaxValue
