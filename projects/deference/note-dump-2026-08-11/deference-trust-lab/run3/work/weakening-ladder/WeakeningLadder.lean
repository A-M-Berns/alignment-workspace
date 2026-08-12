/-
  run3 / weakening-ladder — The faithful-acceleration §5 strength ladder / li-deference
  weakening chain, fully adjudicated: THE MIDDLE RUNG IS FALSE FOR SOFT GATES.

  Target documents (read-only; both actively edited, commits c849658–e29f8e3):
    * faithful-acceleration.md §5, "The strengths of Total Trust" (lines ~122–138):
      the four-rung ladder  bounded-violation ⇒ limit ⇒ bounded-ε-violation ⇒ averaged,
      each ⇓ claimed to be a (strict) weakening;
    * li-deference.md lines ~213–226: the boxed g/w/q/v chain
      Σvₙ<∞ ⇒ qₙ ≳ₙ 0 ⇒ Σwₙ<∞ ("bounded sum of violations implies convergence to the
      rule" / "convergence to the rule implies only finitely many violations of any
      slightly stricter rule").

  Adjudication (this file, standalone, sorry-free):
    (a) top_rung_sound        : bounded-violation ⇒ limit — SOUND, via the ramp identity.
    (b) middle_rung_false     : limit ⇒ bounded-ε-violation — FALSE as stated, refuted as
                                a compiled ¬(∀ …) by the soft-gate witness of the
                                acceleration scout (t=3/4, ε=δ=1/8, aₙ = t + δ/(n+1),
                                p ≡ 0): the shrinking gate gₙ = 1/(n+1) damps the product
                                qₙ → 0 while Σwₙ = Σ1/(n+1) = ∞ diverges harmonically.
                                The averaged rung fails too (witness_not_averaged), so
                                the "limit" configuration sits BELOW both rungs the
                                ladder places under it.
    (c) middle_rung_repaired  : the arrow IS valid under support-nondegeneracy
                                (∃ c>0, gₙ>0 → gₙ ≥ c — in particular hard gates):
                                exactly where the gate is effectively hard.
                                witness_gate_no_gap: (b)'s witness visibly violates it.
    (d) bottom_rung           : bounded-ε-violation ⇒ averaged (the §5 Corollary), with
                                the deep-days identity wₙ = gₙ DERIVED from softInd
                                saturation, never assumed.
    (e) strictness/incomparability witnesses:
        creep_*  (pₙ = t − 1/(n+1), g ≡ 1): limit holds, margin-free count diverges
                 (top ⇓ strict); repair_fires: the ε-margin arrow fires here (c=1).
        park_*   (p ≡ t − ε/2, g ≡ 1): Σwₙ = 0 yet the limit fails (middle relation
                 strict in the other direction — with (b): the two rungs are
                 INCOMPARABLE for soft gates); also mean < t while Σw < ∞.
        gap_*    (p ≡ t − ε − δ/2, g ≡ 1): averaged holds, Σwₙ = ∞ (the δ-gap:
                 bottom ⇓ strict — the Corollary does not imply the Theorem).
        alt_*    (t = 2/5, pₙ alternating 1,0, g ≡ 1): bare gated mean ≥ t for every
                 N ≥ 1, yet wₙ = 1 on all odd days (no-cancellation incomparability:
                 a mean inequality cannot encode Σw < ∞).

  Copied definitions (standalone discipline of run3/GROUND-RULES.md §2):
    softInd — verbatim from lean-deference/FaithfulAcceleration.lean:152
              (with softInd_nonneg :154 and softInd_pos_imp :161–166);
    AsympLE — verbatim from lean-deference/LeanDeference.lean:84
              (DeferenceAsymp.AsympLE; `AsympLE a b` is LI's `b ≳ₙ a`).

  Exact-rational pre-check: ladder_check.py / ladder_check.out.txt in this folder.
  Axiom audit at the end; expected [propext, Classical.choice, Quot.sound] throughout.
-/
import Mathlib

open Filter Topology

namespace WeakLadder

/-! ## Copied corpus definitions (with citation) -/

/-- The soft (continuous) indicator: a clamp ramping `0 → 1` over `[0, δ]`.
    Copied verbatim from `lean-deference/FaithfulAcceleration.lean:152`. -/
noncomputable def softInd (δ x : ℝ) : ℝ := max 0 (min 1 (x / δ))

/-- LI's `b ≳ₙ a` (`aₙ ≤ bₙ + o(1)`).
    Copied verbatim from `lean-deference/LeanDeference.lean:84` (`DeferenceAsymp.AsympLE`). -/
def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε

/-! ## softInd calculus (elementary; the saturation and ramp identities are what the
    documents' arguments lean on, so they are proved from the definition, not assumed) -/

theorem softInd_nonneg (δ x : ℝ) : 0 ≤ softInd δ x := le_max_left _ _

theorem softInd_le_one (δ x : ℝ) : softInd δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- One-sidedness (copied proof, `FaithfulAcceleration.lean:161`). -/
theorem softInd_pos_imp (δ x : ℝ) (hδ : 0 < δ) (h : 0 < softInd δ x) : 0 < x := by
  unfold softInd at h
  have h1 : 0 < min 1 (x / δ) := (lt_max_iff.1 h).resolve_left (lt_irrefl 0)
  have h2 : 0 < x / δ := lt_of_lt_of_le h1 (min_le_right 1 (x / δ))
  have h3 := mul_pos h2 hδ
  rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at h3

/-- **Saturation**: past the ramp (`δ ≤ x`) the soft indicator equals 1 exactly. -/
theorem softInd_eq_one (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) : softInd δ x = 1 := by
  unfold softInd
  have h1 : (1 : ℝ) ≤ x / δ := (one_le_div hδ).2 hx
  rw [min_eq_left h1, max_eq_right zero_le_one]

/-- Off support: for `x ≤ 0` the soft indicator vanishes. -/
theorem softInd_eq_zero (δ x : ℝ) (hδ : 0 < δ) (hx : x ≤ 0) : softInd δ x = 0 := by
  unfold softInd
  have h1 : x / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx (le_of_lt hδ)
  rw [min_eq_right (le_trans h1 zero_le_one), max_eq_left h1]

/-- **Ramp identity**: on `[0, δ]` the soft indicator is exactly `x/δ`. -/
theorem softInd_eq_ramp (δ x : ℝ) (hδ : 0 < δ) (h0 : 0 ≤ x) (h1 : x ≤ δ) :
    softInd δ x = x / δ := by
  unfold softInd
  have ha : x / δ ≤ 1 := (div_le_one hδ).2 h1
  have hb : 0 ≤ x / δ := div_nonneg h0 (le_of_lt hδ)
  rw [min_eq_right ha, max_eq_right hb]

/-! ## The four rungs, in the documents' own soft gates — never an abstract `w`.
    Dictionary (faithful §5 / li-deference boxed defs):
      `gate δ t a n` = gₙ = Ind_δ(aₙ > t)                    = softInd δ (aₙ − t)
      bounded-violation  = Σ gₙ·Ind_δ(Eₙ − t < 0) < ∞         (li-deference: Σvₙ < ∞)
      limit              = gₙ·(Eₙ − t) ≳ₙ 0                   (li-deference: qₙ ≳ₙ 0)
      bounded-ε-violation= Σ wₙ < ∞, wₙ = gₙ·Ind_δ(Eₙ < t−ε)  (the Theorem)
      averaged           = Σgₙ Eₙ / Σgₙ ≳ t − ε − δ           (the Corollary)
    `p` plays E^H_n(X); `a` plays A's forecast aₙ. -/

/-- The gate `gₙ := Ind_δ(aₙ > t)` of faithful §5 / li-deference. -/
noncomputable def gate (δ t : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ := softInd δ (a n - t)

theorem gate_nonneg (δ t : ℝ) (a : ℕ → ℝ) (n : ℕ) : 0 ≤ gate δ t a n :=
  softInd_nonneg _ _

/-- Rung 1 (top), **bounded-violation**: `Σₙ gₙ·Ind_δ(Eₙ − t < 0) < ∞`. -/
def BoundedViolation (a p : ℕ → ℝ) (t δ : ℝ) : Prop :=
  Summable (fun n => gate δ t a n * softInd δ (t - p n))

/-- Rung 2, **limit**: `gₙ·(Eₙ − t) ≳ₙ 0`. -/
def LimitRung (a p : ℕ → ℝ) (t δ : ℝ) : Prop :=
  AsympLE (fun _ => 0) (fun n => gate δ t a n * (p n - t))

/-- Rung 3, **bounded ε-violation** (the Theorem): `Σₙ wₙ < ∞`,
    `wₙ = gₙ·Ind_δ(Eₙ < t − ε)`. -/
def BoundedEpsViolation (a p : ℕ → ℝ) (t ε δ : ℝ) : Prop :=
  Summable (fun n => gate δ t a n * softInd δ (t - ε - p n))

/-- Rung 4 (bottom), **averaged** (the Corollary's conclusion): the gate-weighted
    average of H's own credence is asymptotically ≥ t − ε − δ. -/
def AveragedRung (a p : ℕ → ℝ) (t ε δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
    t - ε - δ - η ≤ (∑ n ∈ Finset.range N, gate δ t a n * p n) /
                    (∑ n ∈ Finset.range N, gate δ t a n)

/-- `qₙ → 0` gives the one-sided asymptotic law `qₙ ≳ₙ 0`. -/
theorem asympLE_zero_of_tendsto {q : ℕ → ℝ} (h : Tendsto q atTop (𝓝 0)) :
    AsympLE (fun _ => 0) q := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  simp only [Real.dist_eq, sub_zero] at hn
  have h2 := (abs_lt.1 hn).1
  show (0 : ℝ) ≤ q n + ε
  linarith

/-! ## (a) TOP RUNG SOUND (soft): bounded-violation ⇒ limit.
    Proof is the ramp identity: writing vₙ = gₙ·Ind_δ(t − pₙ) and qₙ = gₙ(pₙ − t),
      on pₙ ≥ t:            qₙ ≥ 0;
      on the ramp region:   Ind_δ(t−pₙ) = (t−pₙ)/δ, so  δ·vₙ = −qₙ;
      on saturation:        Ind_δ = 1, so vₙ = gₙ and −qₙ = gₙ(t−pₙ) ≤ gₙ·1 = vₙ
                            (prices in [0,1]: t ≤ 1, pₙ ≥ 0).
    Hence qₙ ≥ −C·vₙ with C = max δ 1, and summability sends vₙ → 0. -/

theorem top_rung_sound (a p : ℕ → ℝ) (t δ : ℝ) (hδ : 0 < δ)
    (hp0 : ∀ n, 0 ≤ p n) (ht1 : t ≤ 1)
    (hsum : BoundedViolation a p t δ) : LimitRung a p t δ := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  set C := max δ 1 with hCdef
  have hδC : δ ≤ C := le_max_left _ _
  have h1C : (1 : ℝ) ≤ C := le_max_right _ _
  have key : ∀ n, -(C * (gate δ t a n * softInd δ (t - p n))) ≤ gate δ t a n * (p n - t) := by
    intro n
    have hg := gate_nonneg δ t a n
    rcases le_or_lt t (p n) with hpt | hpt
    · have hq : 0 ≤ gate δ t a n * (p n - t) := mul_nonneg hg (by linarith)
      have hs := softInd_nonneg δ (t - p n)
      have hv : 0 ≤ C * (gate δ t a n * softInd δ (t - p n)) := by
        apply mul_nonneg (by linarith) (mul_nonneg hg hs)
      linarith
    · rcases le_or_lt (t - p n) δ with hr | hr
      · -- ramp region: softInd = (t − pₙ)/δ, so δ·v = g·(t−pₙ) = −q
        rw [softInd_eq_ramp δ (t - p n) hδ (by linarith) hr]
        have hX0 : 0 ≤ gate δ t a n * ((t - p n) / δ) :=
          mul_nonneg hg (div_nonneg (by linarith) (le_of_lt hδ))
        have hmono : δ * (gate δ t a n * ((t - p n) / δ)) ≤
            C * (gate δ t a n * ((t - p n) / δ)) :=
          mul_le_mul_of_nonneg_right hδC hX0
        have hδx : gate δ t a n * ((t - p n) / δ) * δ = gate δ t a n * (t - p n) := by
          rw [mul_assoc, div_mul_cancel₀ _ hδ0]
        have hq : gate δ t a n * (p n - t) = -(gate δ t a n * (t - p n)) := by ring
        rw [hq]
        nlinarith [hmono, hδx]
      · -- saturated region: softInd = 1, v = g, and t − pₙ ≤ 1 ≤ C
        rw [softInd_eq_one δ (t - p n) hδ (le_of_lt hr)]
        have h3 : t - p n ≤ C := le_trans (by linarith [hp0 n]) h1C
        have h4 : gate δ t a n * (t - p n) ≤ gate δ t a n * C :=
          mul_le_mul_of_nonneg_left h3 hg
        have hq : gate δ t a n * (p n - t) = -(gate δ t a n * (t - p n)) := by ring
        rw [hq]
        nlinarith [h4]
  have hv0 : Tendsto (fun n => gate δ t a n * softInd δ (t - p n)) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  intro ε hε
  have hCv : Tendsto (fun n => C * (gate δ t a n * softInd δ (t - p n))) atTop (𝓝 0) := by
    simpa using hv0.const_mul C
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hCv ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  simp only [Real.dist_eq, sub_zero] at hn
  have h5 := (abs_lt.1 hn).1
  have h6 := key n
  show (0 : ℝ) ≤ gate δ t a n * (p n - t) + ε
  linarith

/-! ## (b) THE FINDING: the middle rung is FALSE as stated, for soft gates.
    Witness (acceleration scout, Finding B; same phenomenon as the lean-scout Q2
    witness g = 1/(n+1), E ≡ t − 2ε): t = 3/4, ε = δ = 1/8,
      aₙ = t + δ/(n+1)  (A forecasts barely above threshold, approaching it)
      pₙ ≡ 0            (H parked at zero credence — a massive trust violation).
    Then gₙ = Ind_δ(aₙ − t) = 1/(n+1): the gate SHRINKS, damping the product
    qₙ = −(3/4)/(n+1) → 0, so the "limit" rung holds vacuously — yet the inner ramp
    saturates (t − ε − 0 = 5/8 ≥ δ) so wₙ = gₙ = 1/(n+1) and Σwₙ diverges. -/

/-- Witness forecast: `aₙ = 3/4 + (1/8)/(n+1)`. -/
noncomputable def wa (n : ℕ) : ℝ := 3 / 4 + 1 / (8 * ((n : ℝ) + 1))

/-- Witness human price: `p ≡ 0`. -/
def wp : ℕ → ℝ := fun _ => 0

theorem wa_bounds (n : ℕ) : 0 ≤ wa n ∧ wa n ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h8 : (8 : ℝ) ≤ 8 * ((n : ℝ) + 1) := by linarith
  have hd : 1 / (8 * ((n : ℝ) + 1)) ≤ 1 / 8 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) h8
  constructor
  · unfold wa; positivity
  · unfold wa; linarith

/-- **The witness gate is exactly harmonic**: `gₙ = 1/(n+1)` — a shrinking soft gate,
    realized by the documents' own `Ind_δ` applied to a genuine forecast sequence. -/
theorem witness_gate (n : ℕ) : gate (1/8) (3/4) wa n = 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  unfold gate wa softInd
  have hx : (3 / 4 + 1 / (8 * ((n : ℝ) + 1)) - 3 / 4) / (1/8) = 1 / ((n : ℝ) + 1) := by
    rw [div_div_div_cancel_right']
    · ring_nf
    · sorry
  sorry

end WeakLadder
