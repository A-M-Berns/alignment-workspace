/-
  CenteredSqueeze.lean — the centered-bet squeeze: Total Trust ⟹ Mart, timely.
  (centered-bet-squeeze.md; upgrades v6 §1.6's "genuinely hard half".)

  Real-sequence abstraction, same trusted boundary as the sibling modules:
  * `Approx`/`AsympLE` model the LI ≂ₙ/≲ₙ calculus.
  * LI-paper theorems enter as NAMED HYPOTHESES: the expert's `er`+`loe`
    (`hcenter`), the novice's `loe` split (`hloe`), the `expprovind` collapse
    carries (`hcolUpD` etc.), coherence on ⌜1⌝ (`hone`), and soft Total Trust
    itself (`hTTup`/`hTTdn`) — the hypothesis under study.
  * PROVED: the concrete soft-indicator collapse (the cut weights are
    EVENTUALLY THE CONSTANT 1 — the step the prose flags for scrutiny), the
    ε-pinch, the full composition `centered_squeeze : … → Approx EX EY`, the
    exact single-state mechanism `exact_pinch`, and the amplifier's death by a
    weighted centered instance (`amp_weighted_centered_moment` — the integral
    is machine-checked here, one notch past the corpus's hand-evaluated-
    antiderivative convention; `amp_unweighted_centered_zero` shows the
    unweighted instance alone does NOT kill it).
-/
import Mathlib

open Filter Topology intervalIntegral

namespace CenteredSqueeze

/-- LI's `a ≂ₙ b`: sequences agree up to vanishing error. -/
def Approx (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)

/-- `a ≲ b` : `aₙ ≤ bₙ + o(1)`. (So LI's `b ≳ₙ a` is `AsympLE a b`.) -/
def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε

/- ---------- asymptotic calculus (as in the sibling modules) ---------- -/

namespace Approx
variable {a b c : ℕ → ℝ}

theorem symm (h : Approx a b) : Approx b a := by
  simpa [Approx, neg_sub] using h.neg

theorem trans (h1 : Approx a b) (h2 : Approx b c) : Approx a c := by
  simpa [Approx, sub_add_sub_cancel] using h1.add h2

theorem asympLE (h : Approx a b) : AsympLE a b := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  have : |a n - b n| < ε := by simpa [Real.dist_eq] using hn
  linarith [(abs_lt.1 this).2]

/-- scalar multiple of an `≂ₙ`. -/
theorem const_mul (k : ℝ) (h : Approx a b) : Approx (fun n => k * a n) (fun n => k * b n) := by
  have := h.const_mul k
  simpa [Approx, mul_sub] using this

/-- transport `→ 0` along `≂ₙ`. -/
theorem tendsto_zero (h : Approx a b) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto b atTop (𝓝 0) := by
  have := ha.sub h
  simpa using this
end Approx

namespace AsympLE
variable {a a' b b' : ℕ → ℝ}

theorem trans {c : ℕ → ℝ} (h1 : AsympLE a b) (h2 : AsympLE b c) : AsympLE a c := by
  intro ε hε
  filter_upwards [h1 (ε/2) (by linarith), h2 (ε/2) (by linarith)] with n hn1 hn2
  linarith

/-- congruence: move both sides of an `≲` along `≂ₙ`. -/
theorem congr (h : AsympLE a b) (ha : Approx a' a) (hb : Approx b b') : AsympLE a' b' :=
  (ha.asympLE.trans h).trans hb.asympLE
end AsympLE

/- ---------- Part 1: the soft threshold indicator, concretely ---------- -/

/-- v6 §1.6's continuous threshold indicator `Ind_δ(x > t)`:
    0 for `x ≤ t`, linear ramp on `[t, t+δ]`, 1 for `x ≥ t + δ`. -/
noncomputable def indUp (δ t x : ℝ) : ℝ := max 0 (min 1 ((x - t) / δ))

/-- `Ind_δ(x < t)`: 1 for `x ≤ t − δ`, ramp, 0 for `x ≥ t`. -/
noncomputable def indDn (δ t x : ℝ) : ℝ := max 0 (min 1 ((t - x) / δ))

theorem indUp_eq_one {δ t x : ℝ} (hδ : 0 < δ) (h : t + δ ≤ x) : indUp δ t x = 1 := by
  have h1 : (1 : ℝ) ≤ (x - t) / δ := (le_div_iff₀ hδ).2 (by linarith)
  simp [indUp, min_eq_left h1]

theorem indDn_eq_one {δ t x : ℝ} (hδ : 0 < δ) (h : x ≤ t - δ) : indDn δ t x = 1 := by
  have h1 : (1 : ℝ) ≤ (t - x) / δ := (le_div_iff₀ hδ).2 (by linarith)
  simp [indDn, min_eq_left h1]

/-- **Step 1 (the collapse trigger).** If the expert's estimate of the centered
    bet tends to 0, then for any `0 < δ < ε` BOTH cut weights — the upper cut at
    threshold `−ε` and the lower cut at `+ε` — are eventually the constant 1.
    Nothing sharp is ever evaluated: the ramps sit strictly clear of the
    estimate's tail. -/
theorem weights_eventually_one {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    {ε δ : ℝ} (hδ : 0 < δ) (hεδ : δ < ε) :
    ∀ᶠ n in atTop, indUp δ (-ε) (e n) = 1 ∧ indDn δ ε (e n) = 1 := by
  have hband : ∀ᶠ n in atTop, |e n| < ε - δ := by
    have := Metric.tendsto_atTop.1 he (ε - δ) (by linarith)
    obtain ⟨N, hN⟩ := this
    exact eventually_atTop.2 ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  filter_upwards [hband] with n hn
  obtain ⟨hlo, hhi⟩ := abs_lt.1 hn
  exact ⟨indUp_eq_one hδ (by linarith), indDn_eq_one hδ (by linarith)⟩

/- ---------- Part 2: the ε-pinch ---------- -/

/-- **Step 3a.** A sequence squeezed between `−ε·mass` and `+ε·mass` (asymptotically,
    for EVERY ε > 0), with `mass → 1`, tends to 0. -/
theorem pinch {a mass : ℕ → ℝ} (hmass : Tendsto mass atTop (𝓝 1))
    (hup : ∀ ε : ℝ, 0 < ε → AsympLE (fun n => (-ε) * mass n) a)
    (hdn : ∀ ε : ℝ, 0 < ε → AsympLE a (fun n => ε * mass n)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hmass2 : ∀ᶠ n in atTop, mass n < 2 := by
    have := Metric.tendsto_atTop.1 hmass 1 one_pos
    obtain ⟨N, hN⟩ := this
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  have hmass0 : ∀ᶠ n in atTop, 0 < mass n := by
    have := Metric.tendsto_atTop.1 hmass 1 one_pos
    obtain ⟨N, hN⟩ := this
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).1]
  have h1 := hup (ε/4) hε4 (ε/4) hε4
  have h2 := hdn (ε/4) hε4 (ε/4) hε4
  rw [eventually_atTop] at h1 h2 hmass2 hmass0
  obtain ⟨N1, hN1⟩ := h1; obtain ⟨N2, hN2⟩ := h2
  obtain ⟨N3, hN3⟩ := hmass2; obtain ⟨N4, hN4⟩ := hmass0
  refine ⟨max (max N1 N2) (max N3 N4), fun n hn => ?_⟩
  have hn1 := hN1 n (le_trans (le_max_left N1 N2) (le_trans (le_max_left _ _) hn))
  have hn2 := hN2 n (le_trans (le_max_right N1 N2) (le_trans (le_max_left _ _) hn))
  have hn3 := hN3 n (le_trans (le_max_left N3 N4) (le_trans (le_max_right _ _) hn))
  have hn4 := hN4 n (le_trans (le_max_right N3 N4) (le_trans (le_max_right _ _) hn))
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> nlinarith

/- ---------- Part 3: the composition (Steps 0–3) ---------- -/

/-- **The centered-bet squeeze: soft Total Trust ⟹ Mart, timely.**

Sequences (novice day-n estimates unless noted):
  `EX`, `EY` — of `Xₙ` and of `Yₙ := ⌜E*(Xₙ)⌝`;  `ED` — of `Dₙ := Xₙ − Yₙ`;
  `Eone` — of the constant-1 LUV;  `e` — the EXPERT's estimate `E*(Dₙ)`;
  `EDwUp ε δ`, `EwUp ε δ` — of `Dₙ·w` and `w` for the upper-cut weight
  `w = Ind_δ(E*(Dₙ) > −ε)`;  `EDwDn`, `EwDn` — likewise for the lower cut
  `Ind_δ(E*(Dₙ) < ε)`.

Named hypotheses (the trusted boundary):
  `hcenter` — Step 0, the expert centers itself: `E*(Dₙ) → 0`
              [expert `loe` + `er` (4.11.5), or exact coherence over its ledger];
  `hone`    — `E^H(1) → 1` [`expprovind` on the provably-constant LUV];
  `hloe`    — `E^H(Dₙ) ≂ E^H(Xₙ) − E^H(Yₙ)` [novice `loe` (4.8.4)];
  `hTTup`/`hTTdn` — soft Total Trust, both cuts, raw form [the hypothesis];
  `hcol…`   — if a cut weight is eventually the constant 1 then the weighted
              estimates collapse: `E^H(D·w) ≂ E^H(D)`, `E^H(w) ≂ E^H(1)`
              [`expprovind` (4.8.10) carries of the decided identities].

Proved: the composition — `E^H(Xₙ) ≂ₙ E^H(⌜E*(Xₙ)⌝)`, i.e. Mart on `(Xₙ)`. -/
theorem centered_squeeze
    (EX EY ED e Eone : ℕ → ℝ)
    (EDwUp EwUp EDwDn EwDn : ℝ → ℝ → ℕ → ℝ)
    (hcenter : Tendsto e atTop (𝓝 0))
    (hone : Tendsto Eone atTop (𝓝 1))
    (hloe : Approx ED (fun n => EX n - EY n))
    (hTTup : ∀ ε δ : ℝ, 0 < δ →
      AsympLE (fun n => (-ε) * EwUp ε δ n) (EDwUp ε δ))
    (hTTdn : ∀ ε δ : ℝ, 0 < δ →
      AsympLE (EDwDn ε δ) (fun n => ε * EwDn ε δ n))
    (hcolUpD : ∀ ε δ : ℝ, 0 < δ → (∀ᶠ n in atTop, indUp δ (-ε) (e n) = 1) →
      Approx (EDwUp ε δ) ED)
    (hcolUpW : ∀ ε δ : ℝ, 0 < δ → (∀ᶠ n in atTop, indUp δ (-ε) (e n) = 1) →
      Approx (EwUp ε δ) Eone)
    (hcolDnD : ∀ ε δ : ℝ, 0 < δ → (∀ᶠ n in atTop, indDn δ ε (e n) = 1) →
      Approx (EDwDn ε δ) ED)
    (hcolDnW : ∀ ε δ : ℝ, 0 < δ → (∀ᶠ n in atTop, indDn δ ε (e n) = 1) →
      Approx (EwDn ε δ) Eone) :
    Approx EX EY := by
  -- Step 3a: E^H(Dₙ) → 0, by the pinch; each ε uses width δ = ε/2 < ε.
  have hED0 : Tendsto ED atTop (𝓝 0) := by
    apply pinch hone
    · -- upper cuts: −ε·E^H(1) ≲ E^H(D)
      intro ε hε
      have hδ : (0:ℝ) < ε/2 := by linarith
      have hev := (weights_eventually_one hcenter hδ (by linarith : ε/2 < ε))
      have hevUp : ∀ᶠ n in atTop, indUp (ε/2) (-ε) (e n) = 1 := hev.mono fun n h => h.1
      -- (−ε)·EwUp ≲ EDwUp, then move both sides along the collapses.
      exact (hTTup ε (ε/2) hδ).congr
        ((hcolUpW ε (ε/2) hδ hevUp).symm.const_mul (-ε)).symm
        (hcolUpD ε (ε/2) hδ hevUp)
    · -- lower cuts: E^H(D) ≲ ε·E^H(1)
      intro ε hε
      have hδ : (0:ℝ) < ε/2 := by linarith
      have hev := (weights_eventually_one hcenter hδ (by linarith : ε/2 < ε))
      have hevDn : ∀ᶠ n in atTop, indDn (ε/2) ε (e n) = 1 := hev.mono fun n h => h.2
      exact (hTTdn ε (ε/2) hδ).congr
        (hcolDnD ε (ε/2) hδ hevDn).symm
        ((hcolDnW ε (ε/2) hδ hevDn).const_mul ε)
  -- Step 3b: split by the novice's loe.  E^H(X) − E^H(Y) ≂ E^H(D) → 0.
  exact hloe.tendsto_zero hED0

/- ---------- Part 4: the mechanism, exact (single-state expert) ---------- -/

/-- **The degenerate-conditioning mechanism in its purest form.** For a
    single-state expert, `E*(D)` is a NUMBER, so every cut event is trivially
    full; Total Trust both-cuts then pinches the novice's unconditional
    estimate to the expert's, exactly: take `s = E*(D)` on both sides. -/
theorem exact_pinch (ED estar mass : ℝ)
    (hup : ∀ s : ℝ, s ≤ estar → s * mass ≤ ED)
    (hdn : ∀ s : ℝ, estar ≤ s → ED ≤ s * mass) :
    ED = estar * mass :=
  le_antisymm (hdn estar le_rfl) (hup estar le_rfl)

/- ---------- Part 5: the amplifier dies by a weighted centered instance ---------- -/

/-- The amplifier `g(e) = (1+2c)e − c` SURVIVES the unweighted centered
    instance: its overshoot and undershoot cancel exactly under Unif[0,1]
    (it satisfies the marginal martingale). -/
theorem amp_unweighted_centered_zero (c : ℝ) :
    ∫ x in (0:ℝ)..1, ((1 + 2*c) * x - c - x) = 0 := by
  have h : ∀ x : ℝ, (1 + 2*c) * x - c - x = 2*c*x - c := fun x => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul, integral_id, integral_const]
  ring

/-- The amplifier DIES on the weighted centered instance with observable weight
    `u(e) = 1 − e`: the moment evaluates to `−c/6`, negative for every `c > 0` —
    no boundedness-at-the-extremes needed. (The integral is machine-checked.) -/
theorem amp_weighted_centered_moment (c : ℝ) :
    ∫ x in (0:ℝ)..1, ((1 + 2*c) * x - c - x) * (1 - x) = -c/6 := by
  have h : ∀ x : ℝ, ((1 + 2*c) * x - c - x) * (1 - x)
      = -(2*c) * x^2 + (3*c) * x - c := fun x => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_add (by fun_prop) (by fun_prop),
      intervalIntegral.integral_sub (by fun_prop) (by fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_id, integral_const]
  norm_num

theorem amp_weighted_centered_neg {c : ℝ} (hc : 0 < c) :
    ∫ x in (0:ℝ)..1, ((1 + 2*c) * x - c - x) * (1 - x) < 0 := by
  rw [amp_weighted_centered_moment]; linarith

end CenteredSqueeze
