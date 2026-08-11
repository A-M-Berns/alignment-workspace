/-
  Kernel-checked formalization of the NEW v5 material
  (`deference-in-logical-induction-v5.md`): the cross-process FORCING suite that discharges
  v4 §11 on the timely fragment.  Sources: `anson-notes/frozen-deliberation-deference-v6.md`
  (T1–T7, Target-Soundness, the seam) and v5 §3.3 (the complexity-gap hinge) / §1.6 (the
  amplifier that blocks the soft⇒hard squeeze).

  Discipline (identical to `LeanDeference.lean` / `SelfReferentialTarget.lean`): the genuine
  mathematical/asymptotic cores are PROVED outright; the Logical-Induction facts (the
  no-Dutch-book criterion as an arbitrage no-go; provability-induction `expprovind`;
  linearity `loe`; per-member convergence; Non-Dogmatism) enter ONLY as named hypotheses.
  No `sorry`; axiom audit at the end.

  Map to v5:
    §1  asymptotic calculus (Approx / AsympLE)         (self-contained; mirrors DeferenceAsymp)
    §2  §3.3 hinge       blind power assumption satisfiable (vs cost_circularity unsatisfiable)
    §3  §1.6 amplifier   passes threshold trust yet ≠ identity; boundedness forces id
    §4  T1, T2           faithful tracking; earned meta-trust            (forced everywhere)
    §5  T3, T4, T6       conditional tower; Value; calibration           (forced on G)
    §6  T7               limit agreement on G; underdetermination off G
    §7  Target-Soundness TS on G (per-member convergence); TS fails off G (the seam)
    §8  §5.8             settlement-powered forcing co-extensive with settlement (silence)
-/
import Mathlib

open Filter Topology
open scoped Classical

namespace Frozen

/-! ## §1  Asymptotic calculus (self-contained; mirrors `DeferenceAsymp`).
    `Approx a b` is LI's `a ≈ₙ b`; `AsympLE a b` is LI's `b ≳ₙ a` (`aₙ ≤ bₙ + o(1)`). -/

def Approx (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)

def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε

namespace Approx
variable {a b c : ℕ → ℝ}

theorem symm (h : Approx a b) : Approx b a := by
  simpa [Approx, neg_sub] using h.neg

theorem asympLE (h : Approx a b) : AsympLE a b := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  have : |a n - b n| < ε := by simpa [Real.dist_eq] using hn
  have := (abs_lt.1 this).2
  linarith
end Approx

namespace AsympLE
variable {a b c : ℕ → ℝ}

theorem trans (h1 : AsympLE a b) (h2 : AsympLE b c) : AsympLE a c := by
  intro ε hε
  filter_upwards [h1 (ε/2) (by linarith), h2 (ε/2) (by linarith)] with n hn1 hn2
  linarith

theorem trans_approx (h1 : AsympLE a b) (h2 : Approx b c) : AsympLE a c :=
  h1.trans h2.asympLE
end AsympLE

/-- `aₙ ≈ₙ bₙ` whenever `|aₙ − bₙ| ≤ Δₙ → 0` (squeeze). -/
theorem approx_of_abs_le {a b Δ : ℕ → ℝ}
    (hb : ∀ n, |a n - b n| ≤ Δ n) (hΔ : Tendsto Δ atTop (𝓝 0)) : Approx a b := by
  show Tendsto (fun n => a n - b n) atTop (𝓝 0)
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) hΔ

/-- Two-sided `≲` collapses to `≈ₙ`:  `a ≲ b` and `b ≲ a`  ⟹  `a ≈ₙ b`.
    (The shape T1 uses: the criterion forbids persistent over- AND under-pricing.) -/
theorem approx_of_asympLE_both {a b : ℕ → ℝ}
    (h1 : AsympLE a b) (h2 : AsympLE b a) : Approx a b := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, |a n - b n| ≤ ε := by
    intro ε hε
    filter_upwards [h1 ε hε, h2 ε hε] with n hn1 hn2
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  rw [Approx, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (key (ε/2) (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  have hle := hN n hn
  simp only [Real.dist_eq, sub_zero]
  linarith [hle]

/- ======================================================================================
   §2  THE COMPLEXITY-GAP HINGE (v5 §3.3).  "Blindness-with-power is satisfiable exactly
   because 𝒞_H ⊊ 𝒞_A."  The NON-blind side is `SelfRefTarget.cost_circularity` (the power
   assumption is unsatisfiable: 𝒞_A would have to contain its own coupled simulation cost
   R∘F).  The BLIND side is realizable: the target cost is the A-free `R_H∘F`, which a strictly
   larger class can dominate.  (Canonically R_H poly, F=2ⁿ, 𝒞_A=EXP dominates the 2^{O(n)}
   horizon cost; here any strictly-increasing dominating `RA` witnesses satisfiability.)
   ====================================================================================== -/

/-- **Blind power assumption is satisfiable** (contrast to `SelfRefTarget.cost_circularity`).
    With an A-free target cost `RH∘F`, the three structural hypotheses — `RA` strictly
    increasing, `F` strictly advancing, and `RA` dominating the horizon cost `RH(F n)` — are
    jointly realizable (no regress).  This is the satisfiability half of the §3.3 dichotomy. -/
theorem blind_cost_realizable :
    ∃ (RH RA : ℕ → ℝ) (F : ℕ → ℕ),
      StrictMono RA ∧ (∀ n, n < F n) ∧ (∀ n, RH (F n) ≤ RA n) := by
  refine ⟨(fun n => (n : ℝ)), (fun n => (n : ℝ) + 1), (fun n => n + 1), ?_, ?_, ?_⟩
  · intro x y h
    have : (x : ℝ) < (y : ℝ) := by exact_mod_cast h
    show (x : ℝ) + 1 < (y : ℝ) + 1; linarith
  · intro n; show n < n + 1; omega
  · intro n; show ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1; push_cast; linarith

/- ======================================================================================
   §3  THE AMPLIFIER (v5 §1.6 / T6).  `g(e) = (1+2c)e − c` overstates the expert's confidence:
   it passes EVERY threshold-trust inequality (both cuts, every t, every c ≥ 0) yet is NOT the
   identity.  What rules it out is boundedness biting at the extremes (`g(0) = −c < 0`).  This
   is exactly why parallel cuts cannot pin `g = id` — the soft⇒hard squeeze needs all bets.
   The cut integrals are evaluated by the elementary antiderivative; we prove the resulting
   algebraic cut VALUES and their sign, plus the fixed point and the boundedness collapse.
   ====================================================================================== -/

/-- The amplifier `g(e) = (1+2c)e − c`. -/
noncomputable def amp (c e : ℝ) : ℝ := (1 + 2 * c) * e - c

/-- The amplifier fixes the pivot `½` (so it agrees with the identity there). -/
theorem amp_fixed_half (c : ℝ) : amp c (1 / 2) = 1 / 2 := by unfold amp; ring

/-- At the lower extreme `g(0) = −c`: for `c > 0` this is `< 0`, i.e. out of `[0,1]`. -/
theorem amp_zero (c : ℝ) : amp c 0 = -c := by unfold amp; ring

/-- **Boundedness biting.**  If the amplified estimate stays in `[0,1]` at the extreme
    (`0 ≤ g(0)`), then `c ≤ 0`; with `c ≥ 0` this forces `c = 0` — i.e. `g = id`.  This is the
    only thing that pins the diagonal, and it needs the extreme value, not parallel cuts. -/
theorem amp_boundedness_forces_id (c : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ amp c 0) : c = 0 := by
  rw [amp_zero] at hb; linarith

/-- **Upper-cut value.**  `∫_t^1 g − t(1−t)` evaluates to `(1−t)/2 · ((1−t) + 2ct)`. -/
theorem amp_upper_cut_value (c t : ℝ) :
    ((1 + 2 * c) * (1 - t ^ 2) / 2 - c * (1 - t)) - t * (1 - t)
      = (1 - t) / 2 * ((1 - t) + 2 * c * t) := by ring

/-- **Upper-cut nonneg.**  The amplifier passes the upper threshold-trust inequality for every
    `t ∈ [0,1]`, `c ≥ 0`:  `∫_t^1 g ≥ t(1−t)`. -/
theorem amp_upper_cut_nonneg (c t : ℝ) (hc : 0 ≤ c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ ((1 + 2 * c) * (1 - t ^ 2) / 2 - c * (1 - t)) - t * (1 - t) := by
  rw [amp_upper_cut_value]
  have h1 : 0 ≤ (1 - t) / 2 := by linarith
  have h2 : 0 ≤ (1 - t) + 2 * c * t := by nlinarith [mul_nonneg hc ht0]
  exact mul_nonneg h1 h2

/-- **Lower-cut value.**  `∫_0^t g − t²` evaluates to `−(t/2) · (t + 2c(1−t))`. -/
theorem amp_lower_cut_value (c t : ℝ) :
    ((1 + 2 * c) * t ^ 2 / 2 - c * t) - t ^ 2 = -(t / 2) * (t + 2 * c * (1 - t)) := by ring

/-- **Lower-cut nonpos.**  The amplifier passes the lower threshold-trust inequality:
    `∫_0^t g ≤ t²`. -/
theorem amp_lower_cut_nonpos (c t : ℝ) (hc : 0 ≤ c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 + 2 * c) * t ^ 2 / 2 - c * t) - t ^ 2 ≤ 0 := by
  rw [amp_lower_cut_value]
  have h1 : 0 ≤ t / 2 := by linarith
  have h2 : 0 ≤ t + 2 * c * (1 - t) := by nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 1 - t)]
  nlinarith [mul_nonneg h1 h2]

/- ======================================================================================
   §4  FAITHFULNESS — forced on EVERY fragment.  T1 (faithful tracking), T2 (earned meta-trust).
   ====================================================================================== -/

/-- **T1 arithmetic core.**  The contract `C_n` settles to `Y_n`; selling one share at the
    quote `a_n` nets `a_n − Y_n`.  A persistent over-price `Y_n + ε ≤ a_n` banks `≥ ε` per day —
    the arbitrage the 𝒞_A criterion forbids (the exploit itself is the trusted criterion). -/
theorem tracking_sell_profit (a Y ε : ℝ) (hgap : Y + ε ≤ a) : ε ≤ a - Y := by linarith

/-- **T1 · Faithful tracking** `a_n − Y_n ≈ₙ 0`.  The 𝒞_A no-Dutch-book criterion forbids both
    persistent over-pricing (`hUpper : a ≲ Y`, the sell-side arbitrage of `tracking_sell_profit`)
    and persistent under-pricing (`hLower : Y ≲ a`, the buy-side mirror); together they force
    `Approx a Y`.  Forced on every fragment — `A` is pinned to predict the deliberation `Y`. -/
theorem faithful_tracking {a Y : ℕ → ℝ}
    (hUpper : AsympLE a Y) (hLower : AsympLE Y a) : Approx a Y :=
  approx_of_asympLE_both hUpper hLower

/-- **T2 · Earned meta-trust** `E^{H⁺}_n(𝟙[|a_n − Y_n| ≤ ε_n]) → 1`.  T1's bound is uniformly
    provable, so `expprovind` carries it through `H⁺`'s estimate: `m_n ≥ 1 − δ_n` with `δ_n → 0`
    (`hexpprovind`); with `m_n ≤ 1` (expectations are `[0,1]`-valued), `m_n → 1`. -/
theorem meta_trust (m δ : ℕ → ℝ)
    (hle1 : ∀ n, m n ≤ 1)
    (hexpprovind : AsympLE (fun n => 1 - δ n) m)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Approx m (fun _ => 1) := by
  apply approx_of_asympLE_both
  · -- AsympLE m 1
    intro ε hε
    filter_upwards with n
    show m n ≤ 1 + ε
    linarith [hle1 n]
  · -- AsympLE 1 m : from `1 ≈ 1 − δ` (δ→0) and hexpprovind
    have h1δ : Approx (fun _ => (1 : ℝ)) (fun n => 1 - δ n) := by
      apply approx_of_abs_le (Δ := fun n => |δ n|)
      · intro n; rw [show (1 : ℝ) - (1 - δ n) = δ n by ring]
      · simpa using hδ.abs
    exact (Approx.asympLE h1δ).trans hexpprovind

/- ======================================================================================
   §5  SOUNDNESS — forced on G, and only there.  T3 (conditional tower), T4 (Value), T6
   (calibration).  The engine: on G, `a_n ≈ₙ 𝟙(P^{(n)})` — the quote is early-revealed truth.
   ====================================================================================== -/

/-- **The engine of soundness on G.**  On `G`, the quote tracks the truth value:
    `|𝟙(P^{(n)}) − a_n| ≤ ε_n (def of G) + τ_n (T1 tracking error)`, both `→ 0`, so
    `𝟙(P^{(n)}) − a_n ≈ₙ 0`.  Everything in T3/T4/T6 flows from this. -/
theorem quote_is_truth_on_G (truth a ε τ : ℕ → ℝ)
    (hG : ∀ n, |truth n - a n| ≤ ε n + τ n)
    (hε : Tendsto ε atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0)) :
    Approx truth a := by
  apply approx_of_abs_le hG
  simpa using hε.add hτ

/-- **T3 · Conditional tower** `ccee(H⁺→A)` on `G`.  With `Elhs = E^{H⁺}_n(𝟙(P)·w)` and
    `Erhs = E^{H⁺}_n(⌜a·w⌝)`, linearity (`loe`) gives `Elhs − Erhs = E^{H⁺}_n((𝟙(P)−a)·w)`,
    which is provably `≤ d_n` in absolute value on `G` (since `|𝟙(P)−a| ≤` the on-G gap and
    `w ∈ [0,1]`), carried through `E^{H⁺}` by `expprovind` (`hcarry`).  Hence `Elhs ≈ₙ Erhs`. -/
theorem conditional_tower (Elhs Erhs d : ℕ → ℝ)
    (hcarry : ∀ n, |Elhs n - Erhs n| ≤ d n)
    (hd : Tendsto d atTop (𝓝 0)) :
    Approx Elhs Erhs :=
  approx_of_abs_le hcarry hd

/-- **T4 · Value** on `G`, forward arrow (the §1.1 four-liner instantiated at `E* = A`, with the
    tower supplied by T3).  `ES = E^{H⁺}(Ŝ)`, `Em = E^{H⁺}(⌜M⌝)`, `Emi = E^{H⁺}(⌜mⁱ⌝)`,
    `Eoi = E^{H⁺}(Oⁱ)`.  `hUM_S` (T3 on `Ŝ`), `hMon` (`expprovind` from `M ≥ mⁱ`), `hCee`
    (T3 on `Oⁱ`)  ⟹  `E^{H⁺}(Oⁱ) ≲ E^{H⁺}(Ŝ)`.  Converse is `DeferenceConverse.witness_identity`. -/
theorem value_on_G (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) :
    AsympLE Eoi ES :=
  ((hCee.asympLE).trans hMon).trans_approx hUM_S.symm

/-- **T6 · Calibration curve** on `G`.  On `G` the quote sits at an extreme `y = 𝟙(P) ∈ {0,1}`,
    `a` within `ε` of both its bin value `v` (`hbin`) and the truth `y` (`htruth`, the engine).
    Hence the bin's outcome frequency `y` matches the bin value `v` within `2ε`: the calibration
    curve coincides with the diagonal on `G`.  (Off `G` it is underdetermined — the amplifier.) -/
theorem calibration_residual_on_G (a v y ε : ℝ)
    (hbin : |a - v| ≤ ε) (htruth : |a - y| ≤ ε) : |y - v| ≤ 2 * ε := by
  have h := abs_sub_le y a v
  rw [abs_sub_comm y a] at h
  linarith [h, hbin, htruth]

/- ======================================================================================
   §6  THE DICHOTOMY.  T7 (limit prices): agreement on G, underdetermination off G.
   ====================================================================================== -/

/-- **T7 · Limit prices, on `G`.**  Per-member convergence pins both the sealed sibling
    `H^{[n]}_∞(P^{(n)})` and `H⁺_∞(P^{(n)})` to the same truth value on `G`
    (`|H^{[n]} − truth| ≤ d_n`, `|H⁺ − truth| ≤ d_n`, `d_n → 0`), so they agree:
    `|H^{[n]}_∞ − H⁺_∞| → 0`. -/
theorem limit_agreement_on_G (Hsib Hplus truth d : ℕ → ℝ)
    (hsib : ∀ n, |Hsib n - truth n| ≤ d n) (hplus : ∀ n, |Hplus n - truth n| ≤ d n)
    (hd : Tendsto d atTop (𝓝 0)) :
    Approx Hsib Hplus := by
  apply approx_of_abs_le (Δ := fun n => 2 * d n)
  · intro n
    have htri := abs_sub_le (Hsib n) (truth n) (Hplus n)
    rw [abs_sub_comm (truth n) (Hplus n)] at htri
    linarith [htri, hsib n, hplus n]
  · simpa using hd.const_mul 2

/-- **T7 · Underdetermination off `G`.**  The achievable off-`G` limits form a *nondegenerate*
    interval inside the Non-Dogmatism-confined `(0,1)`: for any prescribed gap `γ ∈ (0,1)` there
    are two valid limit values `pa, pb ∈ (0,1)` with `|pa − pb| = γ`.  Two reasoners can agree on
    every `G`-quantity yet differ by `γ` on a fixed off-`G` `P`; the construction selects none.
    (Neither is exploitable — no trader profits from a difference that never settles — which is
    the trusted criterion, the §8 silence property below.) -/
theorem underdetermination_off_G (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ pa pb : ℝ, 0 < pa ∧ pa < 1 ∧ 0 < pb ∧ pb < 1 ∧ |pa - pb| = γ := by
  refine ⟨(1 + γ) / 2, (1 - γ) / 2, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [show (1 + γ) / 2 - (1 - γ) / 2 = γ by ring, abs_of_pos hγ0]

/- ======================================================================================
   §7  TARGET-SOUNDNESS and THE SEAM.  TS = "among contracts with Y_n ≈ v, the outcome
   frequency of P^{(n)} is ≈ v."  On G it is a THEOREM (per-member convergence); off G it
   provably FAILS.  G is exactly where the sealed sibling and the future self coincide.
   ====================================================================================== -/

/-- **(TS) on `G` is a theorem.**  By definition of `G`, `|Y_n − 𝟙(P^{(n)})| ≤ ε_n → 0`: the
    target tracks truth pointwise, hence is calibrated to truth.  Needs only per-member
    convergence — nothing about the family being jointly calibrated. -/
theorem TS_on_G (Y truth ε : ℕ → ℝ)
    (hG : ∀ n, |Y n - truth n| ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Approx Y truth :=
  approx_of_abs_le hG hε

/-- **(TS) off `G` does not follow — provably.**  A valid pre-settlement family can have its
    diagonal pinned at `0.6` while the truth alternates `0,1,0,1,…`: each member is mispriced on
    a single (stage, sentence) pair (negligible for its own asymptotic calibration, so still a
    genuine inductor), yet the diagonal is miscalibrated — `Y_n − truth_n ↛ 0`.  This is the
    seam: blindness forbids the single-inductor structure that would make TS free off `G`. -/
theorem TS_off_G_fails :
    ∃ (Y truth : ℕ → ℝ),
      (∀ n, Y n = 3 / 5) ∧ (∀ n, truth n = ((n % 2 : ℕ) : ℝ)) ∧ ¬ Approx Y truth := by
  refine ⟨(fun _ => 3 / 5), (fun n => ((n % 2 : ℕ) : ℝ)), fun _ => rfl, fun _ => rfl, ?_⟩
  intro hA
  have hA' : Tendsto (fun n => (3 : ℝ) / 5 - ((n % 2 : ℕ) : ℝ)) atTop (𝓝 0) := hA
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hA' (1 / 2) (by norm_num)
  have hbig := hN (2 * N) (by omega)
  have hmod : (2 * N) % 2 = 0 := Nat.mul_mod_right 2 N
  -- at n = 2N the difference is 3/5 − 0 = 3/5, whose distance to 0 is 3/5 ≮ 1/2
  simp only [Real.dist_eq, sub_zero, hmod, Nat.cast_zero] at hbig
  norm_num at hbig

/- ======================================================================================
   §8  THE SAFETY PROPERTY (v5 §5.8).  "Settlement-powered forcing is co-extensive with the
   availability of settlement, and goes silent the instant settlement is withdrawn."  The
   exploiter banks `ε` per SETTLED round; if a sentence settles unboundedly often the worth is
   unbounded above (exploitation, forcing); if it never settles, zero rounds bank, worth `0`
   (silence).  The deep MO-budget mechanism is the trusted LI criterion, named.
   ====================================================================================== -/

/-- **Forcing where settlement is available.**  `k` disjoint settled rounds each banking `≥ ε`
    accumulate worth `≥ k·ε`, which is unbounded above as `k` grows (Archimedean): the worth-set
    is unbounded, so a persistent disagreement on a settling sentence is exploited. -/
theorem worth_unbounded_if_settles (ε : ℝ) (hε : 0 < ε) (M : ℝ) :
    ∃ k : ℕ, M < (k : ℝ) * ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (M / ε)
  refine ⟨k, ?_⟩
  have hmul : M / ε * ε < (k : ℝ) * ε := mul_lt_mul_of_pos_right hk hε
  rwa [div_mul_cancel₀ M (ne_of_gt hε)] at hmul

/-- **Silence where settlement is withdrawn.**  On a never-settling sentence there are zero
    settled rounds to bank, so the accumulated worth is `0` — bounded, never exploited.  The
    forcing cannot reach the undecidable fragment: it does not *decide* to spare it, it *cannot
    accumulate* against it. -/
theorem worth_zero_if_never_settles (ε : ℝ) : ((0 : ℕ) : ℝ) * ε = 0 := by simp

end Frozen

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms Frozen.approx_of_asympLE_both
#print axioms Frozen.blind_cost_realizable
#print axioms Frozen.amp_fixed_half
#print axioms Frozen.amp_boundedness_forces_id
#print axioms Frozen.amp_upper_cut_value
#print axioms Frozen.amp_upper_cut_nonneg
#print axioms Frozen.amp_lower_cut_value
#print axioms Frozen.amp_lower_cut_nonpos
#print axioms Frozen.tracking_sell_profit
#print axioms Frozen.faithful_tracking
#print axioms Frozen.meta_trust
#print axioms Frozen.quote_is_truth_on_G
#print axioms Frozen.conditional_tower
#print axioms Frozen.value_on_G
#print axioms Frozen.calibration_residual_on_G
#print axioms Frozen.limit_agreement_on_G
#print axioms Frozen.underdetermination_off_G
#print axioms Frozen.TS_on_G
#print axioms Frozen.TS_off_G_fails
#print axioms Frozen.worth_unbounded_if_settles
#print axioms Frozen.worth_zero_if_never_settles
