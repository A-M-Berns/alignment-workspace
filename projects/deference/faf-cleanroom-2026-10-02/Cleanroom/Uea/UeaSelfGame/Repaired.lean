import Cleanroom.Uea.UeaSelfGame.Defs

/-!
# The repaired theorem: self-evidence, Theorems C, C′ and D (pure)

The self-posterior identity `E_{μ_π}[U | π'(s) = π(s)] = ((1-δ) U(π) + δ p V_o)/((1-δ) + δ p)` is *proved* from
the definitions of `muSelf` and `cond` (`cond_muSelf_self`); nothing here assumes it. From it:

* **self-evidence** (note §2 end): under the static belief `mu` the trust bound holds at every situation —
  `TB` is a consequence of believing in `piStar`, not an extra hypothesis (`self_evidence`, `TB_mu`);
* **Theorem C** (note §5): a pure fixed point with the trust bound at one situation is within `δ/(1-δ)` of
  optimal, with the `p`-dependent form, the `δ = 0` corner and the sketch's weaker constant;
* **Theorem C′** (note §5): the same for mixed fixed points, Herrmann or extension, with no `|A|` factor —
  through `Umix_eq_sum_Ucoord` (total expectation) and `∑_a p_a = 1`;
* **Theorem D, pure** (note §7): every pure floored fixed point is within `δ/(1-δ)`.

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static or
self-consistent belief, product self-hypothesis for mixed policies, continuous extension at null actions
(`Fext`); not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-! ### The self-posterior identity -/

/-- **The self-posterior identity**: under `μ_π = (1-δ) δ_π + δ Po`, the conditional of the agent's own
action at `s` is `((1-δ) U(π) + δ p_s V_s)/((1-δ) + δ p_s)` with `p_s V_s = pva s (π s)` — proved from
the definitions by splitting the sum over `{π' : π'(s) = π(s)}` into `π' = π` and the rest.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C proof, "the only computation"), §2 (self-evidence)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_muSelf_self (π : S → A) (s : S) :
    G.cond (G.muSelf π) s (π s) =
      ((1 - G.δ) * G.U π + G.δ * G.pva s (π s)) / ((1 - G.δ) + G.δ * G.pa s (π s)) := by
  unfold cond
  rw [G.condNum_muSelf, G.condDen_muSelf, if_pos rfl, if_pos rfl, mul_one]

/-- The identity in the note's `(p, V_o)` form: `V_o := pva/pa` when `p = pa > 0`.
Source: [[updateless-self-game]] §5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_muSelf_self_pV (π : S → A) (s : S) (hp : 0 < G.pa s (π s)) :
    G.cond (G.muSelf π) s (π s) =
      ((1 - G.δ) * G.U π + G.δ * G.pa s (π s) * (G.pva s (π s) / G.pa s (π s))) /
        ((1 - G.δ) + G.δ * G.pa s (π s)) := by
  rw [G.cond_muSelf_self]
  congr 1
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem muSelf_self_den_pos (π : S → A) (s : S) : 0 < (1 - G.δ) + G.δ * G.pa s (π s) := by
  have := G.one_sub_δ_pos; have := G.δ_nonneg; have := G.pa_nonneg s (π s)
  positivity

/-- The own-action conditional is at least `(1-δ) U(π)` (the self-mass alone guarantees it: the `Po`-part
of the conditional is nonnegative and the normalisation is at most `1`).
Source: [[updateless-self-game]] §2 ("self-evidence"), with `π` for `π*`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem one_sub_δ_mul_U_le_cond_muSelf_self (π : S → A) (s : S) :
    (1 - G.δ) * G.U π ≤ G.cond (G.muSelf π) s (π s) := by
  rw [G.cond_muSelf_self, le_div_iff₀ (G.muSelf_self_den_pos π s)]
  have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg; have h3 := G.pa_nonneg s (π s)
  have h4 := G.pa_le_one s (π s); have h5 := G.pva_nonneg s (π s); have h6 := G.U_nonneg π
  nlinarith [mul_nonneg (mul_nonneg h1.le h6) (sub_nonneg.2 h4), mul_nonneg h2 h5]

/-! ### Self-evidence (target 3) -/

/-- **Self-evidence**: under the static belief `μ = (1-δ) δ_{π*} + δ Po`, the conditional of `π*(s)` is
`((1-δ) U* + δ p V)/((1-δ) + δ p) ≥ (1-δ) U*` for every `Po` and `s`. The trust bound is a consequence of
believing in `π*`, not an extra hypothesis — which is why it cannot rescue the proposed theorem (Theorem A).
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static belief; not
rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §2 ("Why the trust bound cannot help"); [[uea-inventory]] 024
Kind: P
Fidelity: exact (identity proved from `cond`'s definition, unlike `UpdatelessTrustBound.self_evidence`)
Hyps: (a) -/
theorem self_evidence (s : S) :
    G.cond G.mu s (G.piStar s) =
      ((1 - G.δ) * G.Ustar + G.δ * G.pva s (G.piStar s)) / ((1 - G.δ) + G.δ * G.pa s (G.piStar s)) ∧
    G.thr ≤ G.cond G.mu s (G.piStar s) :=
  ⟨G.cond_muSelf_self G.piStar s, G.one_sub_δ_mul_U_le_cond_muSelf_self G.piStar s⟩

/-- **The trust bound holds at every situation under the static belief**, for every `Po` and `δ`.
Scope: finite updateless self-game — static belief; not rOSI, not the sequential model.
Source: [[updateless-self-game]] §2 ("so `TB_s` holds at every `s` for every `P_o`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_mu (s : S) : G.TB G.mu s :=
  ⟨G.piStar s, G.avail_muSelf_self G.piStar s, (G.self_evidence s).2⟩

/-! ### Theorem C: pure fixed points -/

/-- The cleared-denominator core of Theorem C: if the own action's conditional at `s₀` is at least the
threshold, then `(1-δ) U* ((1-δ) + δ p) ≤ (1-δ) U(π) + δ p V_o`.
Source: [[updateless-self-game]] §5 (Theorem C proof, "Clearing the (positive) denominator")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC_cleared (π : S → A) (s₀ : S) (h : G.thr ≤ G.cond (G.muSelf π) s₀ (π s₀)) :
    (1 - G.δ) * G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) ≤
      (1 - G.δ) * G.U π + G.δ * G.pva s₀ (π s₀) := by
  rw [G.cond_muSelf_self, le_div_iff₀ (G.muSelf_self_den_pos π s₀)] at h
  unfold thr at h
  linarith

/-- **Theorem C, from the argmax at one situation**: if `π s₀` is a Herrmann argmax under `μ_π` and the trust
bound holds at `s₀`, then `U(π) ≥ U* ((1-δ) + δ p) − δ p/(1-δ)` (the `p`-dependent form) and hence
`U(π) ≥ U* − δ/(1-δ)`. Stronger than the note's Theorem C: the argmax is needed only at `s₀`, not at every
situation (used by Theorem D).
Scope: finite updateless self-game — pointwise EDT conditional, self-consistent belief; not rOSI, not the
sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C)
Kind: P
Fidelity: stronger: argmax at `s₀` only
Hyps: (a) -/
theorem theoremC_argmax_at (π : S → A) (s₀ : S) (hfp : G.IsArgmaxH (G.muSelf π) s₀ (π s₀))
    (htb : G.TB (G.muSelf π) s₀) :
    G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) - G.δ * G.pa s₀ (π s₀) / (1 - G.δ) ≤ G.U π ∧
    G.Ustar - G.δ / (1 - G.δ) ≤ G.U π := by
  obtain ⟨a, ha, hthr⟩ := htb
  have h : G.thr ≤ G.cond (G.muSelf π) s₀ (π s₀) := le_trans hthr (hfp.2 a ha)
  have hc := G.theoremC_cleared π s₀ h
  have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg; have h3 := G.pa_nonneg s₀ (π s₀)
  have h4 := G.pa_le_one s₀ (π s₀); have h5 := G.pva_le_pa s₀ (π s₀)
  have h6 := G.Ustar_le_one; have h7 := G.Ustar_nonneg
  have hr : G.δ * G.pa s₀ (π s₀) / (1 - G.δ) * (1 - G.δ) = G.δ * G.pa s₀ (π s₀) :=
    div_mul_cancel₀ _ (ne_of_gt h1)
  have hr1 : G.δ / (1 - G.δ) * (1 - G.δ) = G.δ := div_mul_cancel₀ _ (ne_of_gt h1)
  have hp : G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) - G.δ * G.pa s₀ (π s₀) / (1 - G.δ) ≤ G.U π := by
    have key : (1 - G.δ) * (G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) -
        G.δ * G.pa s₀ (π s₀) / (1 - G.δ)) ≤ (1 - G.δ) * G.U π := by
      nlinarith [mul_le_mul_of_nonneg_left h5 h2]
    exact le_of_mul_le_mul_left key h1
  refine ⟨hp, le_trans ?_ hp⟩
  have h8 : 0 ≤ G.δ * (1 - G.pa s₀ (π s₀)) * (1 - G.Ustar * (1 - G.δ)) := by
    apply mul_nonneg (mul_nonneg h2 (by linarith))
    nlinarith
  have key : (1 - G.δ) * (G.Ustar - G.δ / (1 - G.δ)) ≤
      (1 - G.δ) * (G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) - G.δ * G.pa s₀ (π s₀) / (1 - G.δ)) := by
    nlinarith
  exact le_of_mul_le_mul_left key h1

/-- **Theorem C (pure fixed points)**: a pure fixed point `π` of the self-consistent agent at which the trust
bound holds at some situation `s₀` satisfies `U(π) ≥ U* − δ/(1-δ)`, for every `δ ∈ [0,1)`; the
`p`-dependent form `U(π) ≥ U* ((1-δ) + δ p) − δ p/(1-δ)` is `theoremC_argmax_at`. The identity behind it is
`cond_muSelf_self`, proved here; no `htb`-style hypothesis appears. Content region: the conclusion holds for
every policy of every game with `δ ≥ 1/2` (`Regimes.theoremC_bound_trivial_of_half_le`), so the theorem
says something only for `δ < U*/(1 + U*) ≤ 1/2`; the witnesses T1, T2, T3 sit there.
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C); [[uea-inventory]] 026
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC (π : S → A) (hfp : G.IsPureFP π) (s₀ : S) (htb : G.TB (G.muSelf π) s₀) :
    G.Ustar - G.δ / (1 - G.δ) ≤ G.U π :=
  (G.theoremC_argmax_at π s₀ (hfp s₀) htb).2

/-- Theorem C, `p`-dependent form, as a named headline.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C, first displayed inequality)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC_p (π : S → A) (hfp : G.IsPureFP π) (s₀ : S) (htb : G.TB (G.muSelf π) s₀) :
    G.Ustar * ((1 - G.δ) + G.δ * G.pa s₀ (π s₀)) - G.δ * G.pa s₀ (π s₀) / (1 - G.δ) ≤ G.U π :=
  (G.theoremC_argmax_at π s₀ (hfp s₀) htb).1

/-- The `δ = 0` corner of Theorem C: a certain agent's fixed point with the trust bound is optimal.
Source: [[updateless-self-game]] §5.4 (`exact_of_certain`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem theoremC_of_δ_eq_zero (π : S → A) (hfp : G.IsPureFP π) (s₀ : S) (htb : G.TB (G.muSelf π) s₀)
    (h0 : G.δ = 0) : G.Ustar ≤ G.U π := by
  have := G.theoremC π hfp s₀ htb
  rw [h0] at this
  simpa using this

/-- The founding sketch's weaker constant `δ (1 + 1/(1-δ))`, for the record (implied by Theorem C).
Source: [[updateless-self-game]] §5.4 (`trust_bound_sketch`); [[00-founding-sketches]] §3
Kind: L
Fidelity: weaker: the sketch's constant, implied by `theoremC`
Hyps: (a) -/
theorem theoremC_sketch (π : S → A) (hfp : G.IsPureFP π) (s₀ : S) (htb : G.TB (G.muSelf π) s₀) :
    G.Ustar - G.δ * (1 + 1 / (1 - G.δ)) ≤ G.U π := by
  have h := G.theoremC π hfp s₀ htb
  have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg
  have : G.δ / (1 - G.δ) ≤ G.δ * (1 + 1 / (1 - G.δ)) := by
    rw [mul_add, mul_one, mul_one_div]
    linarith
  linarith

/-! ### Theorem C′: mixed fixed points -/

/-- The per-action inequality of Theorem C′: at every action `a` (supported or not),
`(1-δ) q_a U_a ≥ (1-δ) U* (1-δ) q_a − δ p_a (1 − (1-δ) U*)`, given that every supported action's extended
conditional is at least the threshold.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C′ proof, "Clearing denominators and using `V_a ≤ 1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theoremC'_per_action {σ : S → A → ℝ} (hσ : IsMixed σ) (s₀ : S)
    (hmax : ∀ a, 0 < σ s₀ a → G.thr ≤ G.Fext σ s₀ a) (a : A) :
    G.thr * (1 - G.δ) * σ s₀ a - G.δ * G.pa s₀ a * (1 - G.thr) ≤
      (1 - G.δ) * σ s₀ a * G.Ucoord σ s₀ a := by
  have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg; have h3 := G.pa_nonneg s₀ a
  have h4 := G.pva_le_pa s₀ a; have h5 := G.pva_nonneg s₀ a
  have hthr1 : G.thr ≤ 1 := by
    unfold thr; have := G.Ustar_le_one; have := G.Ustar_nonneg; nlinarith
  have hthr0 := G.thr_nonneg
  rcases (hσ.nonneg s₀ a).eq_or_lt with hq | hq
  · rw [← hq]
    have : 0 ≤ G.δ * G.pa s₀ a * (1 - G.thr) := by
      apply mul_nonneg (mul_nonneg h2 h3); linarith
    nlinarith
  · have hav := G.availMix_of_pos s₀ hq
    have hF := hmax a hq
    rw [G.Fext_eq_of_availMix hav, le_div_iff₀ hav] at hF
    unfold denMix at hF
    nlinarith

/-- **Theorem C′ (mixed fixed points, Herrmann)**: a Herrmann mixed fixed point `σ` with the trust bound at
some `s₀` (over available actions) satisfies `U(σ) ≥ U* − δ/(1-δ)` — the same constant, no `|A|` factor.
The proof sums the per-action inequality over `a` using `∑_a σ_{s₀}(a) = 1`, `U(σ) = ∑_a σ_{s₀}(a) U_a`
(total expectation, `Umix_eq_sum_Ucoord`) and `∑_a p_a = 1`. Content region: as for `theoremC`, the
conclusion is automatic when `δ ≥ 1/2` (`Regimes.theoremC_bound_trivial_of_half_le`).
Scope: finite updateless self-game — pointwise EDT conditional, self-consistent belief, product
self-hypothesis for mixed policies; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C′); [[uea-inventory]] 026
Kind: P
Fidelity: exact (Herrmann convention; the extension form is `theoremC'_ext`)
Hyps: (a) -/
theorem theoremC'_herr {σ : S → A → ℝ} (hfp : G.IsFPherr σ) (s₀ : S) (htb : G.TBherr σ s₀) :
    G.Ustar - G.δ / (1 - G.δ) ≤ G.Umix σ := by
  obtain ⟨b, hb, hthr⟩ := htb
  have hmax : ∀ a, 0 < σ s₀ a → G.thr ≤ G.Fext σ s₀ a := fun a ha =>
    le_trans hthr (hfp.2 s₀ a ha b hb)
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    G.theoremC'_per_action hfp.1 s₀ hmax a
  rw [Finset.sum_sub_distrib] at hsum
  have e1 : ∑ a, G.thr * (1 - G.δ) * σ s₀ a = G.thr * (1 - G.δ) := by
    rw [← Finset.mul_sum, hfp.1.sum s₀, mul_one]
  have e2 : ∑ a, G.δ * G.pa s₀ a * (1 - G.thr) = G.δ * (1 - G.thr) := by
    have : ∀ a, G.δ * G.pa s₀ a * (1 - G.thr) = (G.δ * (1 - G.thr)) * G.pa s₀ a := fun a => by ring
    simp_rw [this]
    rw [← Finset.mul_sum, G.sum_pa, mul_one]
  have e3 : ∑ a, (1 - G.δ) * σ s₀ a * G.Ucoord σ s₀ a = (1 - G.δ) * G.Umix σ := by
    rw [G.Umix_eq_sum_Ucoord σ s₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, e3] at hsum
  have h1 := G.one_sub_δ_pos
  have hr1 : G.δ / (1 - G.δ) * (1 - G.δ) = G.δ := div_mul_cancel₀ _ (ne_of_gt h1)
  unfold thr at hsum
  have key : (1 - G.δ) * (G.Ustar - G.δ / (1 - G.δ)) ≤ (1 - G.δ) * G.Umix σ := by
    nlinarith
  exact le_of_mul_le_mul_left key h1

/-- **Theorem C′ (mixed fixed points, extension)**: an extension fixed point with the extension trust bound
at some `s₀` satisfies `U(σ) ≥ U* − δ/(1-δ)` (via `FP_ext ⊆ FP_Herr`).
Scope: finite updateless self-game — continuous extension at null actions; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §5 (Theorem C′), §6 (the extension)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremC'_ext {σ : S → A → ℝ} (hfp : G.IsFPext σ) (s₀ : S) (htb : G.TBext σ s₀) :
    G.Ustar - G.δ / (1 - G.δ) ≤ G.Umix σ :=
  G.theoremC'_herr hfp.isFPherr s₀ (hfp.tbherr_of_tbext htb)

/-- `U(δ_π) = U(π)`: the mixed value of a pure policy.
Source: [[updateless-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Umix_pureMix (π : S → A) : G.Umix (pureMix π) = G.U π := by
  unfold Umix
  simp_rw [prodW_pureMix]
  simp [Finset.sum_ite_eq']

/-- Theorem C recovered from Theorem C′ through the pure/mixed bridge — a consistency check that the two
developments agree (the pure trust bound is the Herrmann mixed one at `δ_π`).
Source: [[updateless-self-game]] §5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremC_via_bridge (π : S → A) (hfp : G.IsPureFP π) (s₀ : S) (htb : G.TB (G.muSelf π) s₀) :
    G.Ustar - G.δ / (1 - G.δ) ≤ G.U π := by
  rw [← G.Umix_pureMix]
  refine G.theoremC'_herr ((G.isPureFP_iff_isFPherr_pureMix π).1 hfp) s₀ ?_
  obtain ⟨a, ha, hthr⟩ := htb
  exact ⟨a, (G.availMix_pureMix_iff π s₀ a).2 ha, by rwa [G.Fext_pureMix π ha]⟩

/-! ### Theorem D: pure floored fixed points -/

/-- **Theorem D (pure)**: every pure floored fixed point is within `δ/(1-δ)` of optimal. Either some
situation is in the argmax branch, or in the equality branch playing an argmax — then the trust bound holds
there and `theoremC_argmax_at` applies — or every situation resets, so `π = piStar` and the gap is `0`.
The floored agent here is the Herrmann one (`IsPureFPfloored`, max over *available* actions); the
extension's floored notion at a pure policy is stronger (`IsFlooredFPext.isPureFPfloored`, `FlooredBridge`),
so this theorem covers it too, and the two differ at pure policies (`OneSituation`). Content region: the
conclusion is automatic when `δ ≥ 1/2` (`Regimes.theoremC_bound_trivial_of_half_le`).
Scope: finite updateless self-game — pointwise EDT conditional, self-consistent belief, floored agent;
not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §7 (Theorem D); [[uea-inventory]] 030
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem theoremD_pure (π : S → A) (hfp : G.IsPureFPfloored π) : G.Ustar - G.δ / (1 - G.δ) ≤ G.U π := by
  by_cases hex : ∃ s, G.IsArgmaxH (G.muSelf π) s (π s) ∧ G.TB (G.muSelf π) s
  · obtain ⟨s, hs, htb⟩ := hex
    exact (G.theoremC_argmax_at π s hs htb).2
  · push Not at hex
    have hall : ∀ s, π s = G.piStar s := by
      intro s
      obtain ⟨hA, hB, hC⟩ := hfp s
      by_cases hlt : ∀ a, avail (G.muSelf π) s a → G.cond (G.muSelf π) s a < G.thr
      · exact hA hlt
      · push Not at hlt
        obtain ⟨a, ha, hge⟩ := hlt
        by_cases hgt : ∃ b, avail (G.muSelf π) s b ∧ G.thr < G.cond (G.muSelf π) s b
        · exfalso
          have hB' := hB hgt
          obtain ⟨b, hb, hb'⟩ := hgt
          exact hex s hB' ⟨b, hb, hb'.le⟩
        · push Not at hgt
          have heq : G.cond (G.muSelf π) s a = G.thr := le_antisymm (hgt a ha) hge
          rcases hC hgt ⟨a, ha, heq⟩ with hmax | hreset
          · exact absurd ⟨a, ha, hge⟩ (hex s hmax)
          · exact hreset
    have : π = G.piStar := funext hall
    rw [this]
    have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg
    have : 0 ≤ G.δ / (1 - G.δ) := div_nonneg h2 h1.le
    unfold Ustar; linarith

end Game

end Cleanroom.Uea.UeaSelfGame
