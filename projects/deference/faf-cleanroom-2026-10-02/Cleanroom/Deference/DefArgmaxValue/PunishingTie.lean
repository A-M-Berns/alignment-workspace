import Cleanroom.Deference.DefArgmaxValue.Concentration
import Cleanroom.Deference.DefArgmaxValue.Punishing

/-!
# `def-argmax-value` · PunishingTie: the punishing quotes tie, the masses converge to `1/(k+1)`,
and H3 fails on the full punishing menu unconditionally (target 3b(iv), repair round 1)

Audit round 1 (adversarial, N1) found that the OPEN `punishing_masses_interior` is provable
from the package's own concentration lemma, with the exact limit. The route needs no pinning
engine: `concentrates_self` on the punishing menu with `punishPackage` says
`P_{f n}(∼b_{n,j}) · 1[m^j_n ≤ M_n − ε] → 0`; on a day where the indicator is `1`,
`P_{f n}(b_{n,j}) ≤ M_n − ε ≤ 1 − ε`, so `P_{f n}(∼b_{n,j}) ≥ ε − o(1)` by deferred coherence,
and the indicator must eventually be `0`. Hence:

* `punishing_quotes_tie` — every quote is eventually within `ε` of the maximum;
* `punishing_quote_tendsto` — with `Σ_j m^j_n ≈ₙ k` (`punishing_sum_estimate`), every quote
  converges to `k/(k+1)`;
* `punishing_mass_tendsto` — every self-prediction mass `p_j(n) = P_{f n}(sel_n = j)` converges to
  `1/(k+1)`: **the chooser is forced to maximal uncertainty**, a sharpening of the page's "bounded
  away from `0` exactly when the chooser stays uncertain";
* `punishing_masses_interior` — the former OPEN, proved: `Σ_j p_j(1 − p_j) → k/(k+1) > 0`;
* `punishing_h3_deficit_tendsto` / `condStableOn_punishing_refuted` — H3's deficit on the full
  punishing menu `→ −k/(k+1)`, so `CondStableOn` fails there **unconditionally** (3b(iv), F17).

Construction-facing; single market (self); the mathematics is the auditor's probe
(`run/wp/def-argmax-value/audit-r1-probes/PunishingTie.lean`), adopted into the library with
docstrings.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (k : ℕ)

omit [Entailment.Consistent T] in
/-- The estimate of the punishing indicator is the deferred price of `∼b_{n,j}`, exactly.
Source: none: infrastructure (`literalIndicator_expect`)
Kind: L
Fidelity: n/a -/
theorem punishI_estimate (j : Fin (k + 1)) (n : ℕ) :
    (selfExpert T f).estimate (punishI T f k j) n =
      (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) := by
  simp [punishI, Expert.self_estimate, literalIndicator_expect]

omit [Entailment.Consistent T] in
/-- The quote of the punishing option is the deferred price of `b_{n,j}`, exactly.
Source: none: infrastructure (`literalIndicator_expect`)
Kind: L
Fidelity: n/a -/
theorem punishing_quote_eq (j : Fin (k + 1)) (n : ℕ) :
    (punishingMenu T f k).quote (selfExpert T f) j n =
      (liaHistory (paperDP T)) (f n) (punishAtom T f k n j) := by
  simp [punishingMenu, Menu.quote, literalIndicator_expect]

/-- The maximal quote is at most `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem maxQuote_le_one {DP : DeductiveProcess} (E : Expert DP) {k : ℕ} (M : Menu k) (n : ℕ) :
    M.maxQuote E n ≤ 1 := by
  unfold Menu.maxQuote
  exact Finset.sup'_le _ _ (fun j _ => (E.estimate_mem_Icc _ _).2)

/-- **Every quote of the punishing menu is eventually within `ε` of the maximum** — from
`concentrates_self` alone, plus deferred coherence: on a day where `m^j_n ≤ M_n − ε`, the mass
`P_{f n}(∼b_{n,j}) ≥ ε − o(1)` cannot vanish, but concentration says the mass vanishes along
exactly those days.
Source: audit r1 adversarial N1 (the probe `PunishingTie.lean`); [[total-trust-implies-value]]
§Necessity
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_quotes_tie (hf : StrictlyIncreasingDeferral f) (ε : ℝ) (hε : 0 < ε)
    (j : Fin (k + 1)) :
    ∀ᶠ n in atTop, (punishingMenu T f k).maxQuote (selfExpert T f) n - ε <
      (punishingMenu T f k).quote (selfExpert T f) j n := by
  have hc := concentrates_self T f hf (punishingMenu T f k) (punishPackage T f k) ε hε j
  have hneg := tendsto_of_asympEq_const (deferred_neg_coherence (P := liaHistory (paperDP T))
    (DP := paperDP T) f hf (punishAtom_codes T f k j) (paperDP_hworld T))
  have h1 : ∀ᶠ n in atTop, |(liaHistory (paperDP T)) (f n) (punishAtom T f k n j) +
      (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) - 1| < ε / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hneg (ε / 2) (by positivity)
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
      have := hN n hn; rwa [Real.dist_eq] at this⟩
  have h2 : ∀ᶠ n in atTop, (selfExpert T f).estimate (punishI T f k j) n *
      (if (punishingMenu T f k).quote (selfExpert T f) j n ≤
        (punishingMenu T f k).maxQuote (selfExpert T f) n - ε then 1 else 0) < ε / 2 :=
    (tendsto_order.1 hc).2 _ (by positivity)
  filter_upwards [h1, h2] with n hn1 hn2
  by_contra hcon
  push Not at hcon
  rw [if_pos hcon, mul_one, punishI_estimate] at hn2
  rw [punishing_quote_eq] at hcon
  have hM := maxQuote_le_one (selfExpert T f) (punishingMenu T f k) n
  rw [abs_lt] at hn1
  linarith [hn1.1, hn1.2, hn2, hcon, hM]

/-- **Every quote of the punishing menu converges to `k/(k+1)`** (ties + `Σ_j m^j_n ≈ₙ k`).
Source: audit r1 adversarial N1; [[total-trust-implies-value]] §Necessity
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_quote_tendsto (hf : StrictlyIncreasingDeferral f) (j : Fin (k + 1)) :
    Tendsto (fun n => (punishingMenu T f k).quote (selfExpert T f) j n) atTop
      (𝓝 ((k : ℝ) / (k + 1))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / 4 with hη
  have hηpos : 0 < η := by positivity
  have hsum : Tendsto (fun n => ∑ i, (punishingMenu T f k).quote (selfExpert T f) i n) atTop
      (𝓝 (k : ℝ)) := tendsto_of_asympEq_const (punishing_sum_estimate T f k hf)
  have h1 : ∀ᶠ n in atTop,
      |(∑ i, (punishingMenu T f k).quote (selfExpert T f) i n) - k| < η := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hsum η hηpos
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
      have := hN n hn; rwa [Real.dist_eq] at this⟩
  have h2 : ∀ᶠ n in atTop, ∀ i : Fin (k + 1),
      (punishingMenu T f k).maxQuote (selfExpert T f) n - η <
        (punishingMenu T f k).quote (selfExpert T f) i n := by
    rw [Filter.eventually_all]
    exact fun i => punishing_quotes_tie T f k hf η hηpos i
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn1, hn2⟩ := hN n hn
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- S ≤ (k+1) M
  have hle : (∑ i, (punishingMenu T f k).quote (selfExpert T f) i n) ≤
      ((k : ℝ) + 1) * (punishingMenu T f k).maxQuote (selfExpert T f) n := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Menu.quote_le_maxQuote (selfExpert T f) (punishingMenu T f k) i n)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    push_cast at h
    exact h
  -- (k+1)(M − η) < S
  have hge : ((k : ℝ) + 1) * ((punishingMenu T f k).maxQuote (selfExpert T f) n - η) <
      ∑ i, (punishingMenu T f k).quote (selfExpert T f) i n := by
    have h := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
      (fun i _ => hn2 i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    push_cast at h
    exact h
  have hqM : (punishingMenu T f k).quote (selfExpert T f) j n ≤
      (punishingMenu T f k).maxQuote (selfExpert T f) n :=
    Menu.quote_le_maxQuote _ _ j n
  have hqm := hn2 j
  rw [abs_lt] at hn1
  have hηk : η / (k + 1) ≤ η := by
    rw [div_le_iff₀ hk1]; nlinarith
  have hsplit : ((k : ℝ) + η) / (k + 1) = k / (k + 1) + η / (k + 1) := by ring
  have hsplit' : ((k : ℝ) - η) / (k + 1) = k / (k + 1) - η / (k + 1) := by ring
  have hMlo : ((k : ℝ) - η) / (k + 1) < (punishingMenu T f k).maxQuote (selfExpert T f) n := by
    rw [div_lt_iff₀ hk1]; linarith [hn1.1, hle]
  have hMhi : (punishingMenu T f k).maxQuote (selfExpert T f) n < ((k : ℝ) + η) / (k + 1) + η := by
    rw [← sub_lt_iff_lt_add, lt_div_iff₀ hk1]; linarith [hn1.2, hge]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Every self-prediction mass converges to `1/(k+1)`**: `p_j(n) = P_{f n}(∼b_{n,j}) =
P_{f n}(sel_n = j) → 1/(k+1)` — the chooser of the punishing menu is forced to maximal
uncertainty (a sharpening of [[total-trust-implies-value]] §Necessity's "bounded away from `0`
exactly when the chooser stays uncertain": it cannot do otherwise).
Source: audit r1 adversarial N1; [[total-trust-implies-value]] §Necessity
Kind: C
Fidelity: stronger: the exact limit
Hyps: (a); `hf` -/
theorem punishing_mass_tendsto (hf : StrictlyIncreasingDeferral f) (j : Fin (k + 1)) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j)) atTop
      (𝓝 (1 / ((k : ℝ) + 1))) := by
  have hneg := tendsto_of_asympEq_const (deferred_neg_coherence (P := liaHistory (paperDP T))
    (DP := paperDP T) f hf (punishAtom_codes T f k j) (paperDP_hworld T))
  have hq := punishing_quote_tendsto T f k hf j
  have h := hneg.sub hq
  have e : (1 : ℝ) - (k : ℝ) / (k + 1) = 1 / ((k : ℝ) + 1) := by
    field_simp
    ring
  rw [e] at h
  refine (tendsto_congr (fun n => ?_)).mp h
  simp only [punishing_quote_eq]
  ring

/-- **The sum of the mass variances converges to `k/(k+1)`**: `Σ_j p_j(1 − p_j) → k/(k+1)`.
Source: audit r1 adversarial N1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_massVariance_tendsto (hf : StrictlyIncreasingDeferral f) :
    Tendsto (fun n => ∑ j : Fin (k + 1),
      (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) *
        (1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j))) atTop
      (𝓝 ((k : ℝ) / (k + 1))) := by
  have hlim : Tendsto (fun n => ∑ j : Fin (k + 1),
      (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) *
        (1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j))) atTop
      (𝓝 (∑ _j : Fin (k + 1), (1 / ((k : ℝ) + 1)) * (1 - 1 / ((k : ℝ) + 1)))) := by
    refine tendsto_finsetSum _ (fun j _ => ?_)
    have h := punishing_mass_tendsto T f k hf j
    exact h.mul (tendsto_const_nhds.sub h)
  have hval : (∑ _j : Fin (k + 1), (1 / ((k : ℝ) + 1)) * (1 - 1 / ((k : ℝ) + 1))) =
      (k : ℝ) / (k + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  rwa [hval] at hlim

/-- **The punishing masses stay interior** (3b(iv); the former OPEN of `Open.lean`, proved in
repair round 1 from audit r1's N1): on the `k+1`-option punishing menu, `k ≥ 1`, some `c > 0` is
attained frequently by `Σ_j p_j(n)(1 − p_j(n))` — in fact the sum converges to `k/(k+1)`
(`punishing_massVariance_tendsto`). With `punishing_h3_deficit` this is "H3 fails on the full
punishing menu" (`condStableOn_punishing_refuted`).
Source: [[total-trust-implies-value]] §Necessity ("bounded away from `0` exactly when the chooser
stays uncertain"); mandate target 3b(iv); audit r1 adversarial N1
Kind: C
Fidelity: exact (the conjecture as stated; the limit is stronger)
Hyps: (a); `hf`; `hk` -/
theorem punishing_masses_interior (hf : StrictlyIncreasingDeferral f) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop,
      c ≤ ∑ j : Fin (k + 1), (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j) *
        (1 - (liaHistory (paperDP T)) (f n) (∼ punishAtom T f k n j)) := by
  have hlim := punishing_massVariance_tendsto T f k hf
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) / (k + 1) := div_pos (by linarith) (by positivity)
  refine ⟨(k : ℝ) / (k + 1) / 2, by positivity, ?_⟩
  have hev := (tendsto_order.1 hlim).1 _ (half_lt_self hpos)
  exact (hev.mono (fun n hn => hn.le)).frequently

/-- **H3's deficit on the full punishing menu converges to `−k/(k+1)`**:
`Σ_j E*(Q^j_n) − Σ_j E*(I^j_n)·m^j_n → −k/(k+1)` for `punishPackage` (2-023(b), with the limit).
Source: 2-023(b); [[total-trust-implies-value]] §Necessity; audit r1 adversarial N1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem punishing_h3_deficit_tendsto (hf : StrictlyIncreasingDeferral f) :
    Tendsto (fun n => (∑ _j : Fin (k + 1), (selfExpert T f).estimate (fun _ => constLUV 0) n) -
        ∑ j, (selfExpert T f).estimate (punishI T f k j) n *
          (punishingMenu T f k).quote (selfExpert T f) j n) atTop
      (𝓝 (-((k : ℝ) / (k + 1)))) := by
  have h := punishing_h3_deficit T f k hf
  unfold AsympEq at h
  have hv := (punishing_massVariance_tendsto T f k hf).neg
  have := h.add hv
  rw [zero_add] at this
  refine (tendsto_congr (fun n => ?_)).mp this
  try dsimp only
  ring

/-- **H3 fails on the full punishing menu, unconditionally** (3b(iv), F17): `CondStableOn` is
false for the self-expert's exact package on the `k+1`-option punishing menu, every `k ≥ 1`
(the deficit `→ −k/(k+1) < 0`). Together with `condStableOn_probe_refuted`, the two menus of
the necessity direction both violate H3 — H3 is a scope condition the self-expert does not meet
on self-referential menus.
Source: [[total-trust-implies-value]] §Necessity; 2-023(b); mandate target 3b(iv)
Kind: refuted
Fidelity: exact
Hyps: (a); `hf`; `hk` -/
theorem condStableOn_punishing_refuted (hf : StrictlyIncreasingDeferral f) (hk : 1 ≤ k) :
    ¬ CondStableOn (punishingMenu T f k) (punishPackage T f k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) / (k + 1) := div_pos (by linarith) (by positivity)
  exact not_asympGE_of_tendsto_neg (c := -((k : ℝ) / (k + 1))) (by linarith)
    (punishing_h3_deficit_tendsto T f k hf)

/-- Instance line: `k = 2` at `𝗣𝗔`, `succDeferral`. -/
example : ¬ CondStableOn (punishingMenu 𝗣𝗔 succDeferral 2) (punishPackage 𝗣𝗔 succDeferral 2) :=
  condStableOn_punishing_refuted 𝗣𝗔 succDeferral 2
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num)

end

end Cleanroom.Deference.DefArgmaxValue
