import Cleanroom.Info.InfoVoiLatents.Finite
import Cleanroom.Found.LitDdbFrames.Blackwell
import Cleanroom.Found.LitDdbFrames.Defs

/-!
# info-voi-latents — the value of information over `Blackwell.Experiment` (Target 3, finite part)

Carrier (i): a prior `μ ∈ stdSimplex ℝ W`, an experiment `k : Experiment W S` (from
`lit-ddb-frames`), a menu `u : Fin (n+1) → W → ℝ`. `voi μ k u := bayesValue μ k u − priorValue μ u`.

* `bayesValue_eq_sum_sup'`: the posterior-wise form `bayesValue = ∑ s, max_a postScore s a`
  (no division: `postScore s a = ∑ w, μ w · k w s · u a w`).
* `voi_nonneg` (Good's theorem, no Jensen: the constant rules are candidates).
* `E_sub_E_le_mul_tv`, `abs_priorValue_sub_le`: the Lipschitz step, `|max_a E_ρ u_a − max_a E_σ u_a|
  ≤ M · tv ρ σ` for a menu of within-action range `M` (the shift by the minimum is done, so
  `u ≥ 0` is never assumed).
* `voi_le_mul_sum_tv`: `voi ≤ M · ∑ s, P(s) · tv (post s) μ` (null signals contribute `0`).
* `voi_le_mul_regretMass`: the *regret-mass bound* `voi ≤ M · μ(B)`, `B = {w | ∃ a, u a⋆ w < u a w}`
  for a prior-optimal `a⋆` — a *repair* of S2's "harm-mass bound `VOI ≤ M·m_t(A)`", which is
  false under D5's own definition of `m_t` for a general menu (`VoiHarmMass.harmMass_zero_voi_pos`)
  and true for the binary execute-or-null menu (`VoiHarmMass.voi_le_mul_harmMass_binary`);
  ATTRIBUTION-UNVETTED that the regret set is what the note meant by "harmful".
* `voi_congr_of_support`: the VOI sees the menu only on the support of the prior.

The bridge to PFR's mutual information (Target 3(iv)) and the last step of the chain
(`voi ≤ M√(I/2)`) are in `Bridge.lean`. Witnesses are in `VoiWitness.lean`.

Mandate: `run/wp/info-voi-latents/info-voi-latents-mandate.md`, Target 3.
-/

namespace Cleanroom.Info.InfoVoiLatents.Voi

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell

noncomputable section

set_option linter.unusedSectionVars false

variable {W S : Type} [Fintype W] [Fintype S]

/-! ### Definitions of record -/

/-- **Prior value** of a menu: `max_a E_μ[u a]` (the value of the trivial experiment;
`priorValue_eq_bayesValue_trivial`).
Source: [[generalization-final]] D11 l. 47 (the subtrahend of `VOI`)
Kind: D
Fidelity: exact -/
def priorValue (μ : W → ℝ) {n : ℕ} (u : Fin (n + 1) → W → ℝ) : ℝ :=
  (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => E μ (u a))

/-- **Value of information** of an experiment for a menu: `bayesValue μ k u − priorValue μ u`
(Bayes value over all decision rules `S → Fin (n+1)`, never one fixed rule).
Source: [[generalization-final]] D11 l. 47
Kind: D
Fidelity: exact -/
def voi [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ} (u : Fin (n + 1) → W → ℝ) : ℝ :=
  bayesValue μ k u - priorValue μ u

/-- The **signal mass** `P(s) = ∑ w, μ w · k w s`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def sigMass (μ : W → ℝ) (k : Experiment W S) (s : S) : ℝ := ∑ w, μ w * k.k w s

/-- The **posterior** given signal `s`, in ratio form `μ w · k w s / P(s)`; junk `0` on a null
signal, where every consumer uses the product form `post_mul_sigMass` instead.
Source: none: infrastructure
Kind: D
Fidelity: exact under `0 < sigMass μ k s` -/
def post (μ : W → ℝ) (k : Experiment W S) (s : S) : W → ℝ :=
  fun w => μ w * k.k w s / sigMass μ k s

/-- The **unnormalised posterior score** of action `a` at signal `s`, `∑ w, μ w · k w s · u a w`
(`= P(s) · E_{post s}[u a]`, with no division).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def postScore (μ : W → ℝ) (k : Experiment W S) {n : ℕ} (u : Fin (n + 1) → W → ℝ) (s : S)
    (a : Fin (n + 1)) : ℝ :=
  ∑ w, μ w * k.k w s * u a w

/-- The **trivial experiment** (one signal, always sent).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def trivialExp (W : Type) [Fintype W] : Experiment W Unit where
  k := fun _ _ => 1
  k_mem := fun _ => ⟨fun _ => zero_le_one, by simp⟩

/-! ### Basic facts -/

/-- `∑ s, P(s) = 1` for a prior in the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_sigMass {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) :
    ∑ s, sigMass μ k s = 1 := by
  unfold sigMass
  rw [Finset.sum_comm]
  calc ∑ w, ∑ s, μ w * k.k w s = ∑ w, μ w * ∑ s, k.k w s := by
        simp_rw [Finset.mul_sum]
    _ = ∑ w, μ w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [(k.k_mem w).2, mul_one]
    _ = 1 := hμ.2

/-- `0 ≤ P(s)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sigMass_nonneg {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) (s : S) :
    0 ≤ sigMass μ k s :=
  Finset.sum_nonneg fun w _ => mul_nonneg (hμ.1 w) ((k.k_mem w).1 s)

/-- On a null signal every joint mass `μ w · k w s` vanishes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint_eq_zero_of_sigMass_eq_zero {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W)
    (k : Experiment W S) {s : S} (hs : sigMass μ k s = 0) (w : W) : μ w * k.k w s = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg (hμ.1 w) ((k.k_mem w).1 s)).1 hs w
    (mem_univ w)

/-- **Product form of the posterior**: `post s w · P(s) = μ w · k w s`, for every signal
(including null ones, where both sides are `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem post_mul_sigMass {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) (s : S)
    (w : W) : post μ k s w * sigMass μ k s = μ w * k.k w s := by
  unfold post
  by_cases hs : sigMass μ k s = 0
  · rw [hs, mul_zero, joint_eq_zero_of_sigMass_eq_zero hμ k hs w]
  · exact div_mul_cancel₀ _ hs

/-- The posterior of a signal of positive mass is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem post_mem_stdSimplex {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) {s : S}
    (hs : 0 < sigMass μ k s) : post μ k s ∈ stdSimplex ℝ W := by
  refine ⟨fun w => div_nonneg (mul_nonneg (hμ.1 w) ((k.k_mem w).1 s)) hs.le, ?_⟩
  unfold post
  rw [← Finset.sum_div, div_eq_one_iff_eq hs.ne']
  rfl

/-- `postScore s a = P(s) · E_{post s}[u a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem postScore_eq {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (s : S) (a : Fin (n + 1)) :
    postScore μ k u s a = sigMass μ k s * E (post μ k s) (u a) := by
  unfold postScore E
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← post_mul_sigMass hμ k s w]
  ring

/-- `sup'` commutes with multiplication by a nonnegative constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sup'_mul_left_nonneg {ι : Type} {t : Finset ι} (ht : t.Nonempty) (f : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : t.sup' ht (fun i => c * f i) = c * t.sup' ht f := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc
  · obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_sup' ht f
    rw [hi']
    exact Finset.le_sup' (fun i => c * f i) hi

/-- A decision rule's payoff, rearranged signal-first: `∑ w, μ w · ∑ s, k w s · u (δ s) w =
∑ s, postScore s (δ s)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rule_value_eq_sum_postScore (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) (δ : S → Fin (n + 1)) :
    ∑ w, μ w * ∑ s, k.k w s * u (δ s) w = ∑ s, postScore μ k u s (δ s) := by
  unfold postScore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => ?_
  ring

/-- **Posterior-wise form of the Bayes value**: `bayesValue μ k u = ∑ s, max_a postScore s a`.
Source: none: infrastructure (Target 3; Raiffa–Schlaifer's preposterior form)
Kind: P
Fidelity: exact -/
theorem bayesValue_eq_sum_sup' [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) :
    bayesValue μ k u
      = ∑ s, (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => postScore μ k u s a) := by
  apply le_antisymm
  · unfold bayesValue
    rw [Finset.sup'_le_iff]
    intro δ _
    rw [rule_value_eq_sum_postScore]
    exact Finset.sum_le_sum fun s _ =>
      Finset.le_sup' (fun a => postScore μ k u s a) (mem_univ (δ s))
  · have hδ : ∀ s, ∃ a : Fin (n + 1),
        (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => postScore μ k u s a)
          = postScore μ k u s a := fun s => by
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' univ_nonempty (fun a => postScore μ k u s a)
      exact ⟨a, ha⟩
    choose δ hδ using hδ
    unfold bayesValue
    refine Finset.le_sup'_of_le _ (mem_univ δ) ?_
    rw [rule_value_eq_sum_postScore]
    exact le_of_eq (Finset.sum_congr rfl fun s _ => hδ s)

/-- **The prior value is the Bayes value of the trivial experiment.**
Source: [[generalization-final]] D11 l. 47; Target 3 (kind L)
Kind: L
Fidelity: exact -/
theorem priorValue_eq_bayesValue_trivial (μ : W → ℝ) {n : ℕ} (u : Fin (n + 1) → W → ℝ) :
    priorValue μ u = bayesValue μ (trivialExp W) u := by
  unfold priorValue bayesValue
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro a _
    refine Finset.le_sup'_of_le _ (mem_univ (fun _ : Unit => a)) ?_
    simp [trivialExp, E]
  · rw [Finset.sup'_le_iff]
    intro δ _
    refine Finset.le_sup'_of_le _ (mem_univ (δ ())) ?_
    simp [trivialExp, E]

/-! ### Target 3(i): `0 ≤ voi` -/

/-- **Good's theorem**: `0 ≤ voi`. The constant decision rules are among the candidates of
the Bayes value, so no convexity argument is needed (and no hypothesis on `μ` either: only
the rows of `k` being distributions is used).
Source: [[generalization-final]] D11 l. 47 ("Good's theorem: ≥ 0"), S2 l. 61
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voi_nonneg [DecidableEq S] (μ : W → ℝ) (k : Experiment W S) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) : 0 ≤ voi μ k u := by
  unfold voi priorValue
  rw [sub_nonneg, Finset.sup'_le_iff]
  intro a _
  unfold bayesValue
  refine Finset.le_sup'_of_le _ (mem_univ (fun _ : S => a)) (le_of_eq ?_)
  unfold E
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_mul, (k.k_mem w).2, one_mul]

/-! ### Target 3(ii): the Lipschitz step -/

/-- **One-sided Lipschitz bound in total variation**: for distributions `ρ σ` and a function
`X` of range at most `M` (`X w − X w' ≤ M`), `E_ρ X − E_σ X ≤ M · tv ρ σ`. Proof: shift `X` by
its minimum (so `0 ≤ X − min ≤ M`, and `∑ (ρ − σ) = 0` absorbs the shift), then bound the sum
over `{σ < ρ}` by `M · tv` (set form of `tv`) and the rest by `0`.
Source: [[generalization-final]] P2 l. 107 ("a range-`M` function integrated against a signed
measure of total mass `2 TV` and net mass `0` moves by at most `M TV`")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem E_sub_E_le_mul_tv {ρ σ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (hσ : σ ∈ stdSimplex ℝ W)
    {X : W → ℝ} {M : ℝ} (hM : ∀ w w', X w - X w' ≤ M) : E ρ X - E σ X ≤ M * tv ρ σ := by
  have hne : (univ : Finset W).Nonempty :=
    Finset.nonempty_of_sum_ne_zero (by rw [hρ.2]; exact one_ne_zero)
  obtain ⟨w₀, _, hw₀⟩ := Finset.exists_min_image univ X hne
  have hzero : ∑ w, (ρ w - σ w) = 0 := by
    rw [Finset.sum_sub_distrib, hρ.2, hσ.2, sub_self]
  have hshift : E ρ X - E σ X = ∑ w, (ρ w - σ w) * (X w - X w₀) := by
    unfold E
    have : ∑ w, (ρ w - σ w) * (X w - X w₀)
        = ∑ w, (ρ w - σ w) * X w - (∑ w, (ρ w - σ w)) * X w₀ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [this, hzero, zero_mul, sub_zero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hshift, tv_eq_sum_filter hρ hσ, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not univ (fun w => σ w < ρ w)]
  have h1 : ∑ w ∈ univ.filter (fun w => σ w < ρ w), (ρ w - σ w) * (X w - X w₀)
      ≤ ∑ w ∈ univ.filter (fun w => σ w < ρ w), M * (ρ w - σ w) := by
    refine Finset.sum_le_sum fun w hw => ?_
    simp only [mem_filter] at hw
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM w w₀) (by linarith [hw.2])
  have h2 : ∑ w ∈ univ.filter (fun w => ¬ σ w < ρ w), (ρ w - σ w) * (X w - X w₀) ≤ 0 := by
    refine Finset.sum_nonpos fun w hw => ?_
    simp only [mem_filter, not_lt] at hw
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hw.2]) (by linarith [hw₀ w (mem_univ w)])
  linarith

/-- **The prior value is `M`-Lipschitz in total variation** for a menu of within-action range
`M`: `|max_a E_ρ u_a − max_a E_σ u_a| ≤ M · tv ρ σ`.
Source: [[generalization-final]] P2 l. 107 ("a max of `M`-Lipschitz maps is `M`-Lipschitz")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem abs_priorValue_sub_le {ρ σ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W)
    (hσ : σ ∈ stdSimplex ℝ W) {n : ℕ} {u : Fin (n + 1) → W → ℝ} {M : ℝ}
    (hM : ∀ a w w', u a w - u a w' ≤ M) :
    |priorValue ρ u - priorValue σ u| ≤ M * tv ρ σ := by
  have key : ∀ {ρ σ : W → ℝ}, ρ ∈ stdSimplex ℝ W → σ ∈ stdSimplex ℝ W →
      priorValue ρ u - priorValue σ u ≤ M * tv ρ σ := by
    intro ρ σ hρ hσ
    unfold priorValue
    rw [sub_le_iff_le_add, Finset.sup'_le_iff]
    intro a _
    have := E_sub_E_le_mul_tv hρ hσ (hM a)
    have h2 : E σ (u a) ≤ (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun a => E σ (u a)) :=
      Finset.le_sup' (fun a => E σ (u a)) (mem_univ a)
    linarith
  rw [abs_le]
  constructor
  · have := key hσ hρ
    rw [tv_comm] at this
    linarith
  · exact key hρ hσ

/-! ### Target 3(iii): `voi ≤ M · E[tv]` -/

/-- **The TV bound on the value of information**: `voi μ k u ≤ M · ∑ s, P(s) · tv (post s) μ`
for a menu of within-action range `M`. Null signals contribute `0` on both sides.
Source: [[generalization-final]] S2 l. 61, P2 l. 107; [[generalization-adversary]] A2.1 l. 34
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem voi_le_mul_sum_tv [DecidableEq S] {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) {n : ℕ}
    {u : Fin (n + 1) → W → ℝ} {M : ℝ} (hM : ∀ a w w', u a w - u a w' ≤ M) :
    voi μ k u ≤ M * ∑ s, sigMass μ k s * tv (post μ k s) μ := by
  unfold voi
  rw [bayesValue_eq_sum_sup']
  have hprior : priorValue μ u = ∑ s, sigMass μ k s * priorValue μ u := by
    rw [← Finset.sum_mul, sum_sigMass hμ k, one_mul]
  rw [hprior, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hsc : ∀ a, postScore μ k u s a = sigMass μ k s * E (post μ k s) (u a) :=
    postScore_eq hμ k u s
  simp_rw [hsc]
  rw [sup'_mul_left_nonneg univ_nonempty _ (sigMass_nonneg hμ k s), ← mul_sub]
  rcases (sigMass_nonneg hμ k s).lt_or_eq with hs | hs
  · have := abs_priorValue_sub_le (post_mem_stdSimplex hμ k hs) hμ hM
    rw [abs_le] at this
    calc sigMass μ k s * ((univ : Finset (Fin (n + 1))).sup' univ_nonempty
            (fun a => E (post μ k s) (u a)) - priorValue μ u)
        = sigMass μ k s * (priorValue (post μ k s) u - priorValue μ u) := rfl
      _ ≤ sigMass μ k s * (M * tv (post μ k s) μ) := mul_le_mul_of_nonneg_left this.2 hs.le
      _ = M * (sigMass μ k s * tv (post μ k s) μ) := by ring
  · rw [← hs]
    simp

/-- **The VOI sees the menu only on the support of the prior**: if `u` and `u'` agree at every
state of non-zero prior mass, `voi μ k u = voi μ k u'` (every posterior score and prior expectation
is a `μ`-weighted sum).
Source: none: infrastructure (audit r2, adversarial item 6)
Kind: L
Fidelity: n/a -/
theorem voi_congr_of_support [DecidableEq S] {μ : W → ℝ} (k : Experiment W S) {n : ℕ}
    {u u' : Fin (n + 1) → W → ℝ} (h : ∀ a w, μ w ≠ 0 → u a w = u' a w) :
    voi μ k u = voi μ k u' := by
  have hpost : ∀ s a, postScore μ k u s a = postScore μ k u' s a := by
    intro s a
    unfold postScore
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : μ w = 0
    · simp [hw]
    · rw [h a w hw]
  have hE : ∀ a, E μ (u a) = E μ (u' a) := by
    intro a
    unfold E
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : μ w = 0
    · simp [hw]
    · rw [h a w hw]
  unfold voi priorValue
  rw [bayesValue_eq_sum_sup', bayesValue_eq_sum_sup']
  simp_rw [hpost, hE]

/-! ### The regret-mass bound (S2's "harm-mass bound", made precise) -/

/-- **The regret-mass bound**: for a prior-optimal action `aStar` (`E_μ[u aStar] = priorValue`)
and `B := {w | ∃ a, u aStar w < u a w}` (the states where some action beats `aStar`), with
cross-action range `M` at each state (`u a w − u a' w ≤ M`), `voi μ k u ≤ M · μ(B)`. Proof:
`voi = max_δ ∑ s ∑ w μ w k w s (u (δ s) w − u aStar w)` and the bracket is `≤ M·𝟙_B(w)`.
This is a *repair* of S2's "`VOI ≤ M · m_t(A)` (harm mass, D5) is the one to quote": D5 l. 35
does define `m_t` (`sup_a P_t(a is harmful)`, harm relative to the null action), and under that
definition the sentence is false for a general menu (`VoiHarmMass.harmMass_zero_voi_pos`,
`nullMenu_no_M`; findings F6) and true for the binary execute-or-null menu, where the harm mass
is the regret mass (`VoiHarmMass.voi_le_mul_harmMass_binary`). ATTRIBUTION-UNVETTED that the
regret set is what the note meant by "harmful". For the rare-state instance `B = {wrong}` and
the bound is `ε M`.
Source: [[generalization-final]] S2 l. 61 (last sentence), D5 l. 35; [[generalization-adversary]]
D5 l. 19
Kind: P
Fidelity: variant: regret-mass reading of "harm mass"
Hyps: (a) all -/
theorem voi_le_mul_regretMass [DecidableEq S] {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) (k : Experiment W S) {n : ℕ}
    {u : Fin (n + 1) → W → ℝ} {M : ℝ} (hM : ∀ a a' w, u a w - u a' w ≤ M) {aStar : Fin (n + 1)}
    (hstar : E μ (u aStar) = priorValue μ u) :
    voi μ k u ≤ M * ∑ w ∈ univ.filter (fun w => ∃ a, u aStar w < u a w), μ w := by
  unfold voi bayesValue
  rw [sub_le_iff_le_add, Finset.sup'_le_iff]
  intro δ _
  rw [← hstar]
  have hE : E μ (u aStar) = ∑ w, μ w * ∑ s, k.k w s * u aStar w := by
    unfold E
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, (k.k_mem w).2, one_mul]
  rw [hE, ← sub_le_iff_le_add, ← Finset.sum_sub_distrib]
  have hpt : ∀ w, μ w * ∑ s, k.k w s * u (δ s) w - μ w * ∑ s, k.k w s * u aStar w
      ≤ M * (if ∃ a, u aStar w < u a w then μ w else 0) := by
    intro w
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hk : ∀ s, k.k w s * u (δ s) w - k.k w s * u aStar w
        ≤ k.k w s * (M * (if ∃ a, u aStar w < u a w then 1 else 0)) := by
      intro s
      rw [← mul_sub]
      refine mul_le_mul_of_nonneg_left ?_ ((k.k_mem w).1 s)
      split_ifs with h
      · rw [mul_one]; exact hM _ _ _
      · rw [mul_zero, sub_nonpos]
        push Not at h
        exact h (δ s)
    calc μ w * ∑ s, (k.k w s * u (δ s) w - k.k w s * u aStar w)
        ≤ μ w * ∑ s, k.k w s * (M * (if ∃ a, u aStar w < u a w then 1 else 0)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hk s) (hμ.1 w)
      _ = μ w * (M * (if ∃ a, u aStar w < u a w then 1 else 0)) := by
          rw [← Finset.sum_mul, (k.k_mem w).2, one_mul]
      _ = M * (if ∃ a, u aStar w < u a w then μ w else 0) := by
          split_ifs <;> ring
  calc ∑ w, (μ w * ∑ s, k.k w s * u (δ s) w - μ w * ∑ s, k.k w s * u aStar w)
      ≤ ∑ w, M * (if ∃ a, u aStar w < u a w then μ w else 0) := Finset.sum_le_sum fun w _ => hpt w
    _ = M * ∑ w ∈ univ.filter (fun w => ∃ a, u aStar w < u a w), μ w := by
        rw [← Finset.mul_sum, Finset.sum_filter]

end

end Cleanroom.Info.InfoVoiLatents.Voi
