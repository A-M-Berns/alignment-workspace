/-
  Kernel-checked formalization of the arguments in
  `anson-notes/self-referential-settlement-target.md` — the §2.2 dead-end of the
  SELF-REFERENTIAL settlement target  Y_n = H⁺_{F(n)}(P^(n))  (deference contracts settling
  against the novice's OWN future credence).

  Discipline (identical to `LeanDeference.lean`): the genuine mathematical cores are PROVED
  outright; the Logical-Induction paper's theorems enter ONLY as named hypotheses
  (convergence-on-decidables / provability induction; the no-Dutch-book criterion as an
  inter-temporal no-arbitrage; Non-Dogmatism).  No `sorry`; axiom audit at the end (each
  result must rest on only `[propext, Classical.choice, Quot.sound]`).

  Map to the note:
    §A  Lemma 2.1   no exact quote                               (PURE — fully proved)
    §B  2a          failure of universal pointwise tracking      (lift; LI provability-induction named)
    §C  2b          cost-circularity regress                     (PURE arithmetic; soft joint named)
    §D  dichotomy   predictable iff uninfluenced                 (contrapositive of 2a+2b)
    §E  §5.1        externalized self-trust (inter-temporal arbitrage)
                                                                 (resale algebra PROVED; LI criterion named)
    §F  §5.3/§6     Non-Dogmatism confinement & the refuted divergence construction
-/
import Mathlib

open Filter Topology
open scoped Classical

namespace SelfRefTarget

/-! ## Asymptotic calculus (minimal, self-contained; mirrors `DeferenceAsymp`).
    `Approx a b` is LI's `a ≂ₙ b`; `AsympLE a b` is LI's `b ≳ₙ a` (`aₙ ≤ bₙ + o(1)`). -/

def Approx (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)

def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε

theorem AsympLE.trans {a b c : ℕ → ℝ} (h1 : AsympLE a b) (h2 : AsympLE b c) : AsympLE a c := by
  intro ε hε
  filter_upwards [h1 (ε/2) (by linarith), h2 (ε/2) (by linarith)] with n hn1 hn2
  linarith

/- ======================================================================================
   §A  Lemma 2.1 — NO EXACT QUOTE  (the arithmetic core of 2a; fully proved).
   The settlement reacts AGAINST the quote: `antiInd a = 1` iff `a ≤ ½`.  No quote in `[0,1]`
   is within `½` of its own anti-inductive settlement, and the bound is tight at `a = ½`.
   ====================================================================================== -/

/-- The anti-inductive 0/1 settlement response to a quote (tie at ½ resolves to 1). -/
noncomputable def antiInd (a : ℝ) : ℝ := if a ≤ 1/2 then 1 else 0

/-- The strict-`<` tie convention (resolves the tie to 0). -/
noncomputable def antiInd' (a : ℝ) : ℝ := if a < 1/2 then 1 else 0

/-- **Lemma 2.1.**  For every quote `a ∈ [0,1]`, the exactness residual against its own
    anti-inductive settlement is at least `½`.  Compute-independent: `a` is arbitrary, so no
    predictive power produces an exact quote. -/
theorem no_exact_quote (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    1/2 ≤ |a - antiInd a| := by
  unfold antiInd
  by_cases h : a ≤ 1/2
  · rw [if_pos h, abs_of_nonpos (show a - 1 ≤ 0 by linarith)]; linarith
  · rw [if_neg h, sub_zero, abs_of_nonneg h0]; push_neg at h; linarith

/-- The bound is attained (hence the infimum of the residual over `[0,1]` is exactly `½`):
    even the best-response quote `a = ½` is off by `½`. -/
theorem residual_half : |(1/2 : ℝ) - antiInd (1/2)| = 1/2 := by
  unfold antiInd; rw [if_pos (by norm_num : (1:ℝ)/2 ≤ 1/2)]; norm_num

/-- Robustness to the tie convention: the strict-`<` settlement gives the same `½` bound. -/
theorem no_exact_quote' (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    1/2 ≤ |a - antiInd' a| := by
  unfold antiInd'
  by_cases h : a < 1/2
  · rw [if_pos h, abs_of_nonpos (show a - 1 ≤ 0 by linarith)]; linarith
  · rw [if_neg h, sub_zero, abs_of_nonneg h0]; push_neg at h; linarith

/-- **Residual lower bound with a rounding gap.**  The settlement reacts to the *recorded*
    value `r` (the grid-rounded quote), which may differ from `a`.  Then the residual is at
    least `½ − |r − a|`.  (Specialises to Lemma 2.1 when `r = a`.) -/
theorem residual_lb (a r : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    1/2 - |r - a| ≤ |a - antiInd r| := by
  unfold antiInd
  by_cases h : r ≤ 1/2
  · rw [if_pos h, abs_of_nonpos (show a - 1 ≤ 0 by linarith)]
    have hra : a - r ≤ |r - a| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · rw [if_neg h, sub_zero, abs_of_nonneg h0]; push_neg at h
    have hra : r - a ≤ |r - a| := le_abs_self _
    linarith

/- ======================================================================================
   §B  2a — FAILURE OF UNIVERSAL POINTWISE TRACKING (the asymptotic lift).
   The genuine LI fact (convergence on decidables / provability induction) enters ONLY as the
   named hypothesis `hLIPI`.  Conclusion: the tracking residual `|aₙ − Yₙ|` stays `≥ ½ − o(1)`,
   so timely tracking `aₙ − Yₙ → 0` is FALSE — for every quote sequence, of any power.
   ====================================================================================== -/

/-- **2a, quantitative (`liminf ≥ ½`).**  Hypotheses:
      `ha`     quotes valued in `[0,1]`                 — LI expectations are `[0,1]`-valued;
      `hround` `rₙ − aₙ → 0`                            — the `1/(2n)` grid rounding;
      `hLIPI`  `Yₙ − antiInd(rₙ) → 0`                   — LI provability induction: `H⁺` converges
               to the `D⁺`-decided truth value of the anti-inductive contract by stage `F(n)`.
    No computability hypothesis on `a`: the failure is independent of `A`'s power. -/
theorem tracking_fails_liminf
    (a r Y : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hround : Tendsto (fun n => r n - a n) atTop (𝓝 0))
    (hLIPI : Tendsto (fun n => Y n - antiInd (r n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, 1/2 - ε ≤ |a n - Y n| := by
  intro ε hε
  have hr0 : Tendsto (fun n => |r n - a n|) atTop (𝓝 0) := by simpa using hround.abs
  have hY0 : Tendsto (fun n => |Y n - antiInd (r n)|) atTop (𝓝 0) := by simpa using hLIPI.abs
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hr0 (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hY0 (ε/2) (by linarith)
  rw [eventually_atTop]
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  have hr : |r n - a n| < ε/2 := by simpa [Real.dist_eq, sub_zero, abs_abs] using h1
  have hY : |Y n - antiInd (r n)| < ε/2 := by simpa [Real.dist_eq, sub_zero, abs_abs] using h2
  have hrb : 1/2 - |r n - a n| ≤ |a n - antiInd (r n)| := residual_lb (a n) (r n) (ha n).1 (ha n).2
  have htri : |a n - antiInd (r n)| - |Y n - antiInd (r n)| ≤ |a n - Y n| := by
    have key := abs_sub_abs_le_abs_sub (a n - antiInd (r n)) (a n - Y n)
    have heq : (a n - antiInd (r n)) - (a n - Y n) = Y n - antiInd (r n) := by ring
    rw [heq] at key; linarith
  linarith

/-- **2a, tracking fails outright.**  No `Approx a Y` (no timely tracking) for the
    anti-inductive contract. -/
theorem tracking_fails
    (a r Y : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ 1)
    (hround : Tendsto (fun n => r n - a n) atTop (𝓝 0))
    (hLIPI : Tendsto (fun n => Y n - antiInd (r n)) atTop (𝓝 0)) :
    ¬ Approx a Y := by
  intro hA
  have hlim := tracking_fails_liminf a r Y ha hround hLIPI (1/4) (by norm_num)
  have h2 : Tendsto (fun n => |a n - Y n|) atTop (𝓝 0) := by simpa using hA.abs
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h2 (1/4) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ :=
    (hlim.and (eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩)).exists
  have hlt : |a n - Y n| < 1/4 := by simpa [Real.dist_eq, sub_zero, abs_abs] using hn2
  linarith

/-- Non-vacuity: even the best-response quote `aₙ ≡ ½` (with `rₙ ≡ ½`, settled `Yₙ ≡ 1`)
    satisfies all hypotheses yet fails tracking by exactly `½`. -/
theorem tracking_fails_nonvacuous :
    ∃ (a r Y : ℕ → ℝ),
      (∀ n, 0 ≤ a n ∧ a n ≤ 1) ∧
      Tendsto (fun n => r n - a n) atTop (𝓝 0) ∧
      Tendsto (fun n => Y n - antiInd (r n)) atTop (𝓝 0) ∧
      ¬ Approx a Y := by
  refine ⟨(fun _ => 1/2), (fun _ => 1/2), (fun _ => 1), (fun n => ⟨by norm_num, by norm_num⟩),
    ?_, ?_, ?_⟩
  · simp
  · have he : (fun _ : ℕ => (1:ℝ) - antiInd (1/2)) = (fun _ => 0) := by
      funext n; unfold antiInd; rw [if_pos (by norm_num : (1:ℝ)/2 ≤ 1/2)]; norm_num
    rw [he]; exact tendsto_const_nhds
  · intro hA
    have hc : Tendsto (fun _ : ℕ => ((1:ℝ)/2 - 1)) atTop (𝓝 ((1:ℝ)/2 - 1)) := tendsto_const_nhds
    have := tendsto_nhds_unique hA hc
    norm_num at this

/- ======================================================================================
   §C  2b — COST-CIRCULARITY.  Timely per-instance tracking needs `𝒞_A ∋ R∘F`.  Pure
   arithmetic shows that assumption is self-contradictory; the only soft step (does
   inexploitability make `A` pay the simulating trader's runtime?) is isolated as the named
   hypothesis `hcost` — the ~75–80% joint flagged in the note.
   ====================================================================================== -/

/-- **The regress (bare).**  A strictly increasing cost `RA` cannot dominate its own
    `F`-composition when the deferral strictly advances the stage. -/
theorem regress (RA : ℕ → ℝ) (F : ℕ → ℕ)
    (hmono : StrictMono RA) (hF : ∀ n, n < F n) :
    ¬ (∀ n, RA (F n) ≤ RA n) := by
  intro h
  have : RA 0 < RA (F 0) := hmono (hF 0)
  linarith [h 0]

/-- **Cost-circularity (structured).**  `hcost` = timely tracking forces `A` to host (and
    pay) a stage-`n` trader computing `Y_n`, cost `R(F n)` (the soft joint);  `hshare` = total
    coupled cost dominates `A`'s share;  `hmono`,`hF` structural.  Together: `False`.  Hence
    no satisfiable power assumption of this shape exists. -/
theorem cost_circularity (R RA : ℕ → ℝ) (F : ℕ → ℕ)
    (hmono : StrictMono RA) (hF : ∀ n, n < F n)
    (hshare : ∀ n, RA (F n) ≤ R (F n))
    (hcost : ∀ n, R (F n) ≤ RA n) : False := by
  have h1 : RA 0 < RA (F 0) := hmono (hF 0)
  have h2 : RA (F 0) ≤ RA 0 := le_trans (hshare 0) (hcost 0)
  linarith

/-- The non-cost hypotheses (`hmono`, `hF`, `hshare`) are jointly realizable, so the
    contradiction in `cost_circularity` falls squarely on the timely-cost hypothesis. -/
theorem cost_setup_realizable :
    ∃ (R RA : ℕ → ℝ) (F : ℕ → ℕ),
      StrictMono RA ∧ (∀ n, n < F n) ∧ (∀ n, RA (F n) ≤ R (F n)) ∧
      ¬ (∀ n, R (F n) ≤ RA n) := by
  refine ⟨(fun n => (n : ℝ)), (fun n => (n : ℝ)), (fun n => n + 1), ?_, ?_, ?_, ?_⟩
  · intro a b h; show (a : ℝ) < (b : ℝ); exact_mod_cast h
  · intro n; show n < n + 1; omega
  · intro n; exact le_refl _
  · intro h; have h0 := h 0; simp only [] at h0; norm_num at h0

/- ======================================================================================
   §D  THE DICHOTOMY — "predictable iff uninfluenced."  The contrapositive packaging of 2a
   (§B) and 2b (§C): an `A`-dependent (`¬Blind`) settlement either admits the anti-inductive
   counterexample on a quote-referencing family (`h2a`) or has no satisfiable power assumption
   (`h2b`).  So anything that *tracks* on such a family, or with a satisfiable power assumption,
   must be Blind.  The MATHEMATICAL content is §B and §C; this is their logical structure.
   ====================================================================================== -/

theorem predictable_imp_uninfluenced
    {Blind Tracks SatPower QuoteRef : Prop}
    (h2a : ¬ Blind → QuoteRef → ¬ Tracks)
    (h2b : ¬ Blind → ¬ SatPower) :
    (QuoteRef → Tracks → Blind) ∧ (SatPower → Blind) := by
  refine ⟨fun hq hc => ?_, fun hp => ?_⟩
  · by_contra hb; exact (h2a hb hq) hc
  · by_contra hb; exact (h2b hb) hp

/- ======================================================================================
   §E  WHAT IS NOT KILLED — EXTERNALIZED SELF-TRUST (§5.1).  The inter-temporal arbitrage.
   The subtle resale algebra (one-sided indicator) is PROVED; the only black box is the LI
   criterion phrased as inter-temporal no-arbitrage (`hNoArb`: the present price is not
   persistently below the future resale).  This is `H⁺_n(B_n) ≳ₙ 0` — externalized self-trust —
   and it dodges 2a/2b (it is `H⁺`-side coherence, proven by an arbitrage that WAITS to `F(n)`).
   ====================================================================================== -/

/-- **Resale lower bound (one-sided indicator).**  Settled indicator value `i ∈ [0,1]`, with
    the one-sided property `0 < i → p < r` (i.e. `Ind_δ(r > p) > 0 ⇒ r > p`, the feature that
    lands the conclusion at exactly `p`).  Then the resale `i·(Y − p) ≥ −|r − Y|`. -/
theorem resale_lb (i p r Y : ℝ) (hi0 : 0 ≤ i) (hi1 : i ≤ 1)
    (hone : 0 < i → p < r) : -|r - Y| ≤ i * (Y - p) := by
  rcases eq_or_lt_of_le hi0 with hi | hi
  · rw [← hi, zero_mul]; linarith [abs_nonneg (r - Y)]
  · have hr : p < r := hone hi
    have hYr : -|r - Y| ≤ Y - p := by
      have h1 : r - Y ≤ |r - Y| := le_abs_self _
      linarith
    rcases le_total 0 (Y - p) with hsign | hsign
    · have hpos : 0 ≤ i * (Y - p) := mul_nonneg hi0 hsign
      linarith [abs_nonneg (r - Y)]
    · have hprod : 0 ≤ (1 - i) * (p - Y) := mul_nonneg (by linarith) (by linarith)
      have hge : Y - p ≤ i * (Y - p) := by nlinarith [hprod]
      linarith

/-- `0 ≲ b` from a vanishing pointwise lower bound `−Δₙ ≤ bₙ`, `Δₙ → 0`. -/
theorem asympLE_zero_of_lb (b Δ : ℕ → ℝ)
    (hlb : ∀ n, -(Δ n) ≤ b n) (hΔ : Tendsto Δ atTop (𝓝 0)) :
    AsympLE (fun _ => 0) b := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hΔ ε hε
  rw [eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hd : |Δ n| < ε := by simpa [Real.dist_eq, sub_zero] using hN n hn
  have : Δ n < ε := lt_of_le_of_lt (le_abs_self _) hd
  linarith [hlb n]

/-- **Externalized self-trust (asymptotic).**  `HB n = H⁺_n(B_n)` the present price of the
    arbitrage bundle.  Resale at `F(n)` is `i_n·(Y_n − p_n)`.  Inputs:
      `hi0,hi1` settled indicator in `[0,1]`;  `hone` the one-sided property;
      `htrack`  `|r_n − Y_n| → 0`   — Tracking (LI) + rounding;
      `hNoArb`  `i·(Y−p) ≲ HB`      — the LI no-Dutch-book criterion (inter-temporal): the
                present price is not persistently below the future resale (the NAMED LI box).
    Conclusion `0 ≲ HB`, i.e. `H⁺_n(B_n) ≳ₙ 0` — externalized self-trust on the fixed
    `𝒞_H`-computable witness. -/
theorem externalized_self_trust
    (HB i p r Y : ℕ → ℝ)
    (hi0 : ∀ n, 0 ≤ i n) (hi1 : ∀ n, i n ≤ 1) (hone : ∀ n, 0 < i n → p n < r n)
    (htrack : Tendsto (fun n => |r n - Y n|) atTop (𝓝 0))
    (hNoArb : AsympLE (fun n => i n * (Y n - p n)) HB) :
    AsympLE (fun _ => 0) HB := by
  have hres : ∀ n, -(|r n - Y n|) ≤ i n * (Y n - p n) :=
    fun n => resale_lb (i n) (p n) (r n) (Y n) (hi0 n) (hi1 n) (hone n)
  exact (asympLE_zero_of_lb (fun n => i n * (Y n - p n)) (fun n => |r n - Y n|) hres htrack).trans
    hNoArb

/-- The arbitrage arithmetic behind `hNoArb`: a present price `pbuy` strictly below the future
    resale `psell` nets a strictly positive guaranteed round profit.  (The exploit itself —
    unbounded profit, bounded risk, disjoint rounds — is the trusted LI criterion, exactly as
    `DeferenceTrader` leaves it.) -/
theorem round_profit_pos (pbuy psell : ℝ) (hgap : pbuy < psell) : 0 < psell - pbuy := by linarith

/- ======================================================================================
   §F  NON-DOGMATISM — confinement (§5.3) and the refuted divergence construction (§6).
   Non-Dogmatism (LI Thm 4.6.2 / Uniform form) enters as the named bound; the §6 attempt to
   force the augmented limit to an endpoint dies against it, and manipulation is confined to
   the interior `[δ, 1−δ]`.
   ====================================================================================== -/

/-- **§6 refutation.**  A construction claiming the augmented limit reaches `1` on a
    `Γ`-independent sentence contradicts Non-Dogmatism (`hND : Y∞ < 1`). -/
theorem nondogmatism_refutes (Yinf : ℝ) (hND : Yinf < 1) (hclaim : Yinf = 1) : False := by
  rw [hclaim] at hND; exact lt_irrefl 1 hND

/-- **§5.3 confinement.**  The uniform Non-Dogmatism margin `δ > 0` confines the augmented
    limit to `[δ, 1−δ] ⊂ (0,1)`: deference can never drive certainty on undecided sentences. -/
theorem manipulation_confined (Yinf δ : ℝ) (hδ : 0 < δ)
    (hlo : δ ≤ Yinf) (hhi : Yinf ≤ 1 - δ) : 0 < Yinf ∧ Yinf < 1 :=
  ⟨by linarith, by linarith⟩

end SelfRefTarget

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms SelfRefTarget.no_exact_quote
#print axioms SelfRefTarget.residual_half
#print axioms SelfRefTarget.no_exact_quote'
#print axioms SelfRefTarget.residual_lb
#print axioms SelfRefTarget.tracking_fails_liminf
#print axioms SelfRefTarget.tracking_fails
#print axioms SelfRefTarget.tracking_fails_nonvacuous
#print axioms SelfRefTarget.regress
#print axioms SelfRefTarget.cost_circularity
#print axioms SelfRefTarget.cost_setup_realizable
#print axioms SelfRefTarget.predictable_imp_uninfluenced
#print axioms SelfRefTarget.resale_lb
#print axioms SelfRefTarget.asympLE_zero_of_lb
#print axioms SelfRefTarget.externalized_self_trust
#print axioms SelfRefTarget.round_profit_pos
#print axioms SelfRefTarget.nondogmatism_refutes
#print axioms SelfRefTarget.manipulation_confined
