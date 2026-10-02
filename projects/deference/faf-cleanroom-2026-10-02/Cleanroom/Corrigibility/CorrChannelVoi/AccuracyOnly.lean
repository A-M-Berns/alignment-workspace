import Cleanroom.Corrigibility.CorrChannelVoi.Sensors

/-!
# `corr-channel-voi` — AccuracyOnly: D5, the accuracy-only criterion and its two examples

"Accuracy-only `L`" is undefined in the sources (Known issue 4). D5 fixes one reading
(ATTRIBUTION-UNVETTED): a predicate on experiments at a fixed prior is *accuracy-only* iff it is
Blackwell-monotone — whatever it admits, it admits every more informative experiment. The two
examples the sources use are shown to be of this kind, and both hold for **every** experiment:
the reflection (martingale) identity `∑ s, P(s) · P(w | s) = μ w`, and the expected-Brier
improvement `E_s[Brier(post_s)] ≤ Brier(μ)` for any target `θ`. A different reading of the phrase
could change the verdict of T4(d); this file is the reading the package's theorems use.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Found.CorrThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {W S : Type} [Fintype W] [Fintype S]

/-- **D5. Accuracy-only criterion** (this package's reading, ATTRIBUTION-UNVETTED): a predicate
`L` on experiments over `W`, at a fixed prior, is accuracy-only iff it is Blackwell-monotone:
`BlackwellLE k₂ k₁ → L k₂ → L k₁`. The predicate ranges over every finite signal type.
Source: [[corr-channel-voi-mandate]] D5; legitimacy.md R3 item 1 ("any accuracy-only `L` is a property of the transition's Bayesian structure"); byrnes-herd.md l. 203 ("`L` … determined by the `ω`-algebra and the agent's belief trajectory alone")
Kind: D
Fidelity: variant: the sources leave "accuracy-only" undefined; Blackwell monotonicity is this package's reading -/
def AccuracyOnly (L : (S : Type) → [Fintype S] → Experiment W S → Prop) : Prop :=
  ∀ (S T : Type) [Fintype S] [Fintype T] (k₁ : Experiment W S) (k₂ : Experiment W T),
    BlackwellLE k₂ k₁ → L T k₂ → L S k₁

/-- A predicate true of every experiment is accuracy-only.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem accuracyOnly_of_forall {L : (S : Type) → [Fintype S] → Experiment W S → Prop}
    (h : ∀ (S : Type) [Fintype S] (k : Experiment W S), L S k) : AccuracyOnly L :=
  fun S _ _ _ k₁ _ _ _ => h S k₁

/-! ## Example 1: the reflection (martingale) identity -/

/-- The signal mass `P(s) = ∑ w, μ w · k w s`.
Source: [[corr-channel-voi-mandate]] D5 (example 1)
Kind: D
Fidelity: exact -/
def signalMass (μ : Distr W) (k : Experiment W S) (s : S) : ℝ := ∑ w, μ.mass w * k.k w s

/-- The posterior `P(w | s) = μ w · k w s / P(s)` (Lean's `x / 0 = 0` on a null signal; the
reflection identity below is stated so that null signals contribute `0` either way).
Source: [[corr-channel-voi-mandate]] D5 (example 1)
Kind: D
Fidelity: exact under `0 < signalMass`; junk-free in the identity's product form -/
def posterior (μ : Distr W) (k : Experiment W S) (s : S) (w : W) : ℝ :=
  μ.mass w * k.k w s / signalMass μ k s

/-- **The reflection identity** `Reflects μ k`: `∑ s, P(s) · P(w | s) = μ w` for every world —
the pre-update self's expectation of the post-update belief is its own belief.
Source: [[corr-channel-voi-mandate]] D5 (example 1); legitimacy.md R3 item 1 ("every criterion in the table … holds for both transitions")
Kind: D
Fidelity: exact -/
def Reflects (μ : Distr W) (k : Experiment W S) : Prop :=
  ∀ w, ∑ s, signalMass μ k s * posterior μ k s w = μ.mass w

/-- On a null signal every joint term `μ w · k w s` vanishes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_eq_zero_of_signalMass_eq_zero (μ : Distr W) (k : Experiment W S) (s : S)
    (h : signalMass μ k s = 0) (w : W) : μ.mass w * k.k w s = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg (μ.nonneg w) ((k.k_mem w).1 s)).mp h w
    (mem_univ w)

/-- **Every experiment reflects**: `Reflects μ k` holds for every prior and every experiment
(Bayesian conditioning is a martingale). So the reflection identity is a *constant-true*
predicate on experiments, hence accuracy-only.
Source: [[corr-channel-voi-mandate]] D5; legitimacy.md R3 item 1; substitution.md R9 item 37 ("minimal viability is a martingale condition and a finer conditioning preserves it")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem reflects_all (μ : Distr W) (k : Experiment W S) : Reflects μ k := by
  intro w
  have h : ∀ s, signalMass μ k s * posterior μ k s w = μ.mass w * k.k w s := by
    intro s
    unfold posterior
    by_cases hs : signalMass μ k s = 0
    · rw [hs, zero_mul, joint_eq_zero_of_signalMass_eq_zero μ k s hs w]
    · exact mul_div_cancel₀ _ hs
  simp only [h, ← Finset.mul_sum, (k.k_mem w).2, mul_one]

/-- The reflection identity is accuracy-only (D5): it holds of every experiment.
Source: [[corr-channel-voi-mandate]] D5 (example 1)
Kind: L
Fidelity: exact -/
theorem accuracyOnly_reflects (μ : Distr W) :
    AccuracyOnly (fun (S : Type) [Fintype S] (k : Experiment W S) => Reflects μ k) :=
  accuracyOnly_of_forall fun _ _ k => reflects_all μ k

/-! ## Example 2: expected Brier improvement -/

/-- The posterior mean of a target `θ` on signal `s`: `E[θ | s] = ∑ w, μ w · k w s · θ w / P(s)`.
Source: [[corr-channel-voi-mandate]] D5 (example 2)
Kind: D
Fidelity: exact under `0 < signalMass` -/
def postMean (μ : Distr W) (k : Experiment W S) (θ : W → ℝ) (s : S) : ℝ :=
  (∑ w, μ.mass w * k.k w s * θ w) / signalMass μ k s

/-- The Brier score of the prior forecast `E_μ[θ]` for the target `θ`: `∑ w, μ w (E_μ[θ] − θ w)²`.
Source: [[corr-channel-voi-mandate]] D5 (example 2)
Kind: D
Fidelity: exact -/
def priorBrier (μ : Distr W) (θ : W → ℝ) : ℝ := ∑ w, μ.mass w * (expect μ θ - θ w) ^ 2

/-- The expected Brier score after the experiment: `∑ s, ∑ w, μ w · k w s · (E[θ | s] − θ w)²`.
Source: [[corr-channel-voi-mandate]] D5 (example 2)
Kind: D
Fidelity: exact -/
def expBrier (μ : Distr W) (k : Experiment W S) (θ : W → ℝ) : ℝ :=
  ∑ s, ∑ w, μ.mass w * k.k w s * (postMean μ k θ s - θ w) ^ 2

/-- A weighted quadratic in `q`: `∑ w, m w (q − θ w)² = M q² − 2 q T + U`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_weighted_sq (m θ : W → ℝ) (q : ℝ) :
    ∑ w, m w * (q - θ w) ^ 2 =
      (∑ w, m w) * q ^ 2 - 2 * q * ∑ w, m w * θ w + ∑ w, m w * θ w ^ 2 := by
  have h : ∀ w, m w * (q - θ w) ^ 2 = m w * q ^ 2 - 2 * q * (m w * θ w) + m w * θ w ^ 2 := by
    intro w; ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- The posterior mean minimises the weighted quadratic: for nonnegative weights `m` with
`T = ∑ m θ`, `M = ∑ m`, `∑ m (T/M − θ)² ≤ ∑ m (q − θ)²` for every `q` (on `M = 0` all weights
vanish and both sides are `0`).
Source: none: infrastructure (the proper-scoring step of D5's example 2)
Kind: P
Fidelity: n/a -/
theorem sum_weighted_sq_postMean_le (m θ : W → ℝ) (hm : ∀ w, 0 ≤ m w) (q : ℝ) :
    ∑ w, m w * ((∑ w, m w * θ w) / (∑ w, m w) - θ w) ^ 2 ≤ ∑ w, m w * (q - θ w) ^ 2 := by
  rw [sum_weighted_sq, sum_weighted_sq]
  set M := ∑ w, m w with hM
  set T := ∑ w, m w * θ w with hT
  by_cases h0 : M = 0
  · have hz : ∀ w, m w = 0 := fun w =>
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hm w).mp h0 w (mem_univ w)
    have hT0 : T = 0 := by rw [hT]; exact Finset.sum_eq_zero fun w _ => by rw [hz w, zero_mul]
    have hU0 : ∑ w, m w * θ w ^ 2 = 0 := Finset.sum_eq_zero fun w _ => by rw [hz w, zero_mul]
    rw [h0, hT0, hU0]; ring_nf; exact le_rfl
  · have hMpos : 0 < M := lt_of_le_of_ne (Finset.sum_nonneg fun w _ => hm w) (Ne.symm h0)
    have key : M * q ^ 2 - 2 * q * T - (M * (T / M) ^ 2 - 2 * (T / M) * T) =
        (M * q - T) ^ 2 / M := by
      field_simp
      ring
    have : 0 ≤ (M * q - T) ^ 2 / M := div_nonneg (sq_nonneg _) hMpos.le
    linarith

/-- **Expected Brier improvement**: `E_s[Brier(post_s)] ≤ Brier(μ)` for every prior, experiment
and target `θ` — conditioning never worsens the expected Brier score (signal by signal, the
posterior mean is the minimiser of the weighted quadratic; the prior mean is one competitor).
Source: [[corr-channel-voi-mandate]] D5 (example 2); legitimacy.md R3 item 1 ("expected Brier about `𝟙_W`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem expBrier_le_priorBrier (μ : Distr W) (k : Experiment W S) (θ : W → ℝ) :
    expBrier μ k θ ≤ priorBrier μ θ := by
  unfold expBrier priorBrier
  have hstep : ∀ s, ∑ w, μ.mass w * k.k w s * (postMean μ k θ s - θ w) ^ 2 ≤
      ∑ w, μ.mass w * k.k w s * (expect μ θ - θ w) ^ 2 := fun s =>
    sum_weighted_sq_postMean_le (fun w => μ.mass w * k.k w s) θ
      (fun w => mul_nonneg (μ.nonneg w) ((k.k_mem w).1 s)) (expect μ θ)
  calc ∑ s, ∑ w, μ.mass w * k.k w s * (postMean μ k θ s - θ w) ^ 2
      ≤ ∑ s, ∑ w, μ.mass w * k.k w s * (expect μ θ - θ w) ^ 2 := Finset.sum_le_sum fun s _ => hstep s
    _ = ∑ w, μ.mass w * (expect μ θ - θ w) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [show ∑ s, μ.mass w * k.k w s * (expect μ θ - θ w) ^ 2 =
            μ.mass w * (expect μ θ - θ w) ^ 2 * ∑ s, k.k w s by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
        rw [(k.k_mem w).2, mul_one]

/-- **Brier improvement as a predicate on experiments** (the source's "increase in expected
accuracy" about a target `θ`).
Source: [[corr-channel-voi-mandate]] D5 (example 2)
Kind: D
Fidelity: exact -/
def BrierImproves (μ : Distr W) (θ : W → ℝ) (k : Experiment W S) : Prop :=
  expBrier μ k θ ≤ priorBrier μ θ

/-- Brier improvement is accuracy-only (D5): it holds of every experiment.
Source: [[corr-channel-voi-mandate]] D5 (example 2)
Kind: L
Fidelity: exact -/
theorem accuracyOnly_brier (μ : Distr W) (θ : W → ℝ) :
    AccuracyOnly (fun (S : Type) [Fintype S] (k : Experiment W S) => BrierImproves μ θ k) :=
  accuracyOnly_of_forall fun _ _ k => expBrier_le_priorBrier μ k θ

/-! ## Example 3: a non-constant accuracy-only criterion (audit r1, B1)

The two source examples hold of *every* experiment, so on them the separation theorem's clauses
are `True → True` and `True ↔ True`. The value threshold `t ≤ 𝒱_μ(k)(X)` is accuracy-only by
T8(a) and is not constant (`Witnesses.w_threshold_rejects_trivial`, `w_threshold_admits_button`):
it is the inhabitant on which `AccuracyOnly.cannot_separate` is exercised. -/

/-- `sensorValue` does not depend on the `DecidableEq` instance (the instance only builds the
`Fintype` of decision rules).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sensorValue_inst_irrel (i₁ i₂ : DecidableEq S) (μ : Distr W) (k : Experiment W S)
    (X : W → ℝ) : @sensorValue W S _ _ i₁ μ k X = @sensorValue W S _ _ i₂ μ k X := by
  congr

/-- **The value-threshold criterion** `thresholdL μ X t`: "the channel is worth at least `t`",
`t ≤ 𝒱_μ(k)(X)`, at a fixed prior and stakes. Not constant: it rejects `trivialExp` and admits
`perfectExp` whenever `max(E X, 0) < t ≤ E[max(X, 0)]`.
Source: [[corr-channel-voi-audit-r1-fidelity]] B1; [[corr-channel-voi-audit-r1-adversarial]] B1 (the repair both audits ask for)
Kind: D
Fidelity: n/a (a non-constant instance of D5) -/
def thresholdL (μ : Distr W) (X : W → ℝ) (t : ℝ) :
    (S : Type) → [Fintype S] → Experiment W S → Prop :=
  fun S _ k => letI := Classical.decEq S; t ≤ sensorValue μ k X

/-- **The value threshold is accuracy-only (D5)**: Blackwell-monotone by T8(a).
Source: [[corr-channel-voi-audit-r1-fidelity]] B1
Kind: C (T8(a))
Fidelity: n/a -/
theorem thresholdL_accuracyOnly (μ : Distr W) (X : W → ℝ) (t : ℝ) :
    AccuracyOnly (thresholdL μ X t) := by
  intro S T _ _ k₁ k₂ hB h
  letI := Classical.decEq S
  letI := Classical.decEq T
  exact le_trans h (sensorValue_mono hB μ X)

/-! ## D5′: the invariance reading (audit r1, adversarial N6)

The sources' wording — "a property of the transition's Bayesian structure", "determined by the
`ω`-algebra and the belief trajectory alone" — reads at least as naturally as *invariance under
Blackwell equivalence* as it does as upward-closure. Under invariance, clause (ii) of the
separation theorem survives (both scans carry `perfect`) and clause (i) does **not**: the
exact-value criterion `𝒱(k) = v` is invariant, admits the button at `v = 𝒱(button)`, and rejects
`⟨button, perfect⟩` whenever the button is worth less than perfect information. So the two
readings split the mandate's sentence exactly along its two halves. ATTRIBUTION-UNVETTED either
way. -/

/-- **D5′. The invariance reading** of "accuracy-only": `L` takes the same value on any two
Blackwell-equivalent experiments. Weaker than D5 (`AccuracyOnly.invariant`).
Source: legitimacy.md R3 item 1; byrnes-herd.md l. 203 (the alternative reading, [[corr-channel-voi-audit-r1-adversarial]] N6)
Kind: D
Fidelity: variant: the sources leave the phrase undefined; this is the second candidate reading (ATTRIBUTION-UNVETTED) -/
def AccuracyInvariant (L : (S : Type) → [Fintype S] → Experiment W S → Prop) : Prop :=
  ∀ (S T : Type) [Fintype S] [Fintype T] (k₁ : Experiment W S) (k₂ : Experiment W T),
    BlackwellLE k₂ k₁ → BlackwellLE k₁ k₂ → (L S k₁ ↔ L T k₂)

/-- D5 implies D5′: a Blackwell-monotone predicate is invariant under Blackwell equivalence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem AccuracyOnly.invariant {L : (S : Type) → [Fintype S] → Experiment W S → Prop}
    (hL : AccuracyOnly L) : AccuracyInvariant L :=
  fun _ _ _ _ k₁ k₂ h21 h12 => ⟨hL _ _ k₂ k₁ h12, hL _ _ k₁ k₂ h21⟩

/-- **Clause (ii) survives under D5′**: an invariant `L` takes the same value on `⟨k₁, perfect⟩`
and `⟨k₂, perfect⟩` for any two channels — read-only and disabling scans are still
indistinguishable, since both carry the perfect scan (`prod_perfect_equiv`).
Source: [[corr-channel-voi-mandate]] T4(d) (second sentence), under the invariance reading
Kind: L
Fidelity: exact, for the D5′ reading -/
theorem AccuracyInvariant.prod_perfect_iff [DecidableEq W] {T : Type} [Fintype T]
    {L : (S : Type) → [Fintype S] → Experiment W S → Prop} (hL : AccuracyInvariant L)
    (k₁ : Experiment W S) (k₂ : Experiment W T) :
    L (S × W) (expProd k₁ perfectExp) ↔ L (T × W) (expProd k₂ perfectExp) :=
  (hL _ _ _ _ (prod_perfect_equiv k₁).2 (prod_perfect_equiv k₁).1).trans
    (hL _ _ _ _ (prod_perfect_equiv k₂).2 (prod_perfect_equiv k₂).1).symm

/-- **The exact-value criterion** `valueIs μ X v`: "the channel is worth exactly `v`",
`𝒱_μ(k)(X) = v`.
Source: [[corr-channel-voi-audit-r1-adversarial]] N6 (the witness that D5′ is strictly weaker than D5 on the separation theorem)
Kind: D
Fidelity: n/a -/
def valueIs (μ : Distr W) (X : W → ℝ) (v : ℝ) :
    (S : Type) → [Fintype S] → Experiment W S → Prop :=
  fun S _ k => letI := Classical.decEq S; sensorValue μ k X = v

/-- **The exact-value criterion is invariant (D5′)**: two-sided monotonicity gives equal values.
Source: [[corr-channel-voi-audit-r1-adversarial]] N6
Kind: C (T8(a) both ways)
Fidelity: n/a -/
theorem valueIs_invariant (μ : Distr W) (X : W → ℝ) (v : ℝ) :
    AccuracyInvariant (valueIs μ X v) := by
  intro S T _ _ k₁ k₂ h21 h12
  letI := Classical.decEq S
  letI := Classical.decEq T
  have e : sensorValue μ k₁ X = sensorValue μ k₂ X :=
    le_antisymm (sensorValue_mono h12 μ X) (sensorValue_mono h21 μ X)
  show sensorValue μ k₁ X = v ↔ sensorValue μ k₂ X = v
  rw [e]

/-- **Clause (i) fails under D5′**: whenever a channel `k` is worth strictly less than perfect
information, the invariant criterion "worth exactly `𝒱(k)`" admits `k` and **rejects**
`⟨k, perfect⟩`. So "admitting the button admits the read-only scan" is a theorem of the monotone
reading (D5) and not of the invariance reading (D5′); on `twoState` the hypothesis is
`0 < VOI(perfect | button)`, i.e. the button is not already perfect (T2).
Source: [[corr-channel-voi-mandate]] T4(d) (first sentence), under the invariance reading; [[corr-channel-voi-audit-r1-adversarial]] N6
Kind: C (T8(a) + D2)
Fidelity: exact, for the D5′ reading
Hyps: (a) `𝒱(k) < 𝒱(perfect)` named -/
theorem valueIs_admits_rejects_scan [DecidableEq W] [DecidableEq S] (μ : Distr W) (X : W → ℝ)
    (k : Experiment W S) (hlt : sensorValue μ k X < sensorValue μ perfectExp X) :
    valueIs μ X (sensorValue μ k X) S k ∧
      ¬ valueIs μ X (sensorValue μ k X) (S × W) (expProd k perfectExp) := by
  refine ⟨?_, ?_⟩
  · show @sensorValue W S _ _ (Classical.decEq S) μ k X = sensorValue μ k X
    exact sensorValue_inst_irrel _ _ μ k X
  · intro H
    have H' : sensorValue μ (expProd k perfectExp) X = sensorValue μ k X := by
      rw [← H]; exact sensorValue_inst_irrel _ _ μ _ X
    rw [sensorValue_prod_perfect] at H'
    exact absurd H' hlt.ne'

end

end Cleanroom.Corrigibility.CorrChannelVoi
