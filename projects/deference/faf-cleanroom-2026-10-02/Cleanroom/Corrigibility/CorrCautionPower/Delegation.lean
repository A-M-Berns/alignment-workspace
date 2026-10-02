import Cleanroom.Corrigibility.CorrCautionPower.Reversibility
import Cleanroom.Corrigibility.CorrCautionPower.Witnesses

/-!
# `corr-caution-power` — S12: delegative value learning, refuted as stated

The develop's claim (`caution.md` S12, l. 108, `[conjectured]`; killed in `caution-final.md` S12):
"the agent acts by the delegation variant of D8 (delegate iff the intended action is not
`λ`-reversible and `P_t(c_ω(a) > λ) ≥ η′`), and the advisor is *value-sane* … Conjecture:
Bayesian regret against the `ω*`-optimal policy is sublinear". Two refutations, made exact here:

* **The adversary's instantiation** (A12.1, accepted by the final's proof §12, l. 159): *posterior
  sampling* in place of D8's quantilizer — `s12_refuted`. The develop's S12 supplies neither a null
  action nor a base distribution, so D8 cannot be applied to it as written (finding F-19); the
  source's own refutation rests on this substitution, and so does `s12_refuted` (audit r1 B2: the
  round-0 docstring presented the mandate's reading as a quotation).
* **D8's own policy** on a state that supplies what S12 omits — `s12_refuted_d8`: a
  `CautionState` with `A = {∅, a, b}`, `Ω = {ω*, ω′}`, uniform base, `P(ω′) = 3/4`, values in
  `[0, 1]`, conservatively calibrated with `R = R̂ = 1/12`; at `η = 1/4` the D8 slice is `q = 1/3`,
  the quantilizer under the proxy ranking is `δ_b`, the realized harm is `1/4 = η` (within budget,
  tight), and the regret at the truth `ω*` is `1` per step, `T` over `T` steps. So the develop's
  S12 is false also under its own acting rule, once a base and a null action are supplied.

Objects: `bayesPosterior` (Bayes' rule on a FAF `Distr` with a likelihood; FAF's `Distr.condDist`
is event conditioning, a different object — see its docstring), `bayesPosterior_const`,
`s12Posterior` (the loop's posterior iterate under a hypothesis-independent likelihood, the prior
at every step), `postSample P best = P.map best` (FAF's pushforward), `regretOf` / `regretStep`
(regret at the *fixed truth* `ω*`, averaged over the policy — the source's "Bayesian regret"), the
witnesses `s12Model`, `s12V`, `s12Best`, `s12State`; **`s12_not_sublinear`**: the cumulative regret
of the loop is not `o(T)`.

The salvage (exploration trigger + value-sane advisor, T8(b)) is recorded in the findings as a
conjecture conditional on identifiability; see the report.

Sources: [[corr-wf14-inventory]] 101 → `caution.md` S12 (l. 108); `caution-final.md` S12 (l. 103),
proof §12 (l. 159); [[corr-wf14-2-inventory]] 2-044 → `caution-adversary.md` A12.1–A12.2 (l. 101);
2-089.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-! ## Bayes' rule on a finite distribution -/

section Bayes

variable {Ω : Type*} [Fintype Ω]

/-- **Bayes' rule:** the posterior `P(ω) L(ω) / ∑ P L` given a likelihood `L ≥ 0` with positive
normalizer. FAF's `Distr.condDist (P) (C : Set S) (h : 0 < P.prob C)` is *event* conditioning; the
likelihood-weighted (soft-evidence) update here is the marginal of `condDist` on a joint
`Ω × Obs` at the observed value — not identified with it (an FAF-object note, audit r1; nothing
in this module rests on the update, the likelihood being constant).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def bayesPosterior (P : Distr Ω) (L : Ω → ℝ) (hL : ∀ ω, 0 ≤ L ω)
    (hpos : 0 < ∑ ω, P.mass ω * L ω) : Distr Ω where
  mass ω := P.mass ω * L ω / ∑ ω', P.mass ω' * L ω'
  nonneg ω := div_nonneg (mul_nonneg (P.nonneg ω) (hL ω)) hpos.le
  sum_eq_one := by rw [← sum_div, div_self hpos.ne']

/-- **A hypothesis-independent observation is not evidence:** a constant likelihood leaves the
posterior equal to the prior.
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103, "the posterior never moves")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem bayesPosterior_const (P : Distr Ω) {k : ℝ} (hk : 0 < k) :
    bayesPosterior P (fun _ => k) (fun _ => hk.le)
      (by rw [← sum_mul, P.sum_eq_one, one_mul]; exact hk) = P := by
  ext ω
  simp only [bayesPosterior]
  rw [← sum_mul, P.sum_eq_one, one_mul, mul_div_cancel_right₀ _ hk.ne']

end Bayes

/-- **The posterior iterate of the S12 loop:** start at the prior `(1 − p, p)` on `{ω*, ω′}`,
update at step `t` by the hypothesis-independent likelihood `k t > 0` (harm unobserved: the
observation carries no information about `ω`).
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103, "the posterior never moves")
Kind: D
Fidelity: exact -/
noncomputable def s12Posterior (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ → ℝ) (hk : ∀ t, 0 < k t) :
    ℕ → Distr (Fin 2)
  | 0 => twoPt p hp0 hp1
  | t + 1 => bayesPosterior (s12Posterior p hp0 hp1 k hk t) (fun _ => k t) (fun _ => (hk t).le)
      (by rw [← sum_mul, (s12Posterior p hp0 hp1 k hk t).sum_eq_one, one_mul]; exact hk t)

/-- **The posterior never moves:** the iterate is the prior at every step.
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103), proof §12 (l. 159, "posterior constant")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem s12Posterior_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ → ℝ) (hk : ∀ t, 0 < k t) :
    ∀ T, s12Posterior p hp0 hp1 k hk T = twoPt p hp0 hp1
  | 0 => rfl
  | T + 1 => by
      show bayesPosterior _ _ _ _ = _
      simp only [s12Posterior_eq p hp0 hp1 k hk T]
      exact bayesPosterior_const _ (hk T)

/-! ## Policies and per-step regret -/

section PostSample

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-- **Posterior sampling:** sample `ω ∼ P`, play `best ω` — FAF's pushforward `P.map best`. This
is the adversary's instantiation of S12's acting rule (A12.1, l. 101), not the develop's D8.
Source: [[corr-wf14-2-inventory]] 2-044 / caution-adversary.md A12.1 (l. 101, "posterior sampling plays `b` with probability `p`"); caution-final.md proof §12 (l. 159)
Kind: D
Fidelity: variant: the adversary's policy, substituted for the develop's D8 quantilizer -/
noncomputable def postSample (P : Distr Ω) (best : Ω → A) : Distr A := P.map best

/-- **Regret of a policy `π` at the fixed truth `ω*`** whose optimal action is `aStar`:
`V ω* aStar − E_{a ∼ π}[V ω* a]`. This is the source's "Bayesian regret" (l. 103, "`pg` per
step"): regret at the true hypothesis, averaged over the policy's randomness — *not* averaged over
a prior on the truth (that quantity is `2p(1 − p)g` in the witness below, also linear; audit r1).
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103)
Kind: D
Fidelity: variant: regret at the fixed truth, the source's usage -/
noncomputable def regretOf (π : Distr A) (V : Ω → A → ℝ) (ωStar : Ω) (aStar : A) : ℝ :=
  V ωStar aStar - expect π (V ωStar)

/-- **Per-step regret of posterior sampling** at the fixed truth: `regretOf (P.map best)`.
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103)
Kind: D
Fidelity: variant: regret at the fixed truth (see `regretOf`) -/
noncomputable def regretStep (P : Distr Ω) (best : Ω → A) (V : Ω → A → ℝ) (ωStar : Ω) (aStar : A) :
    ℝ := regretOf (postSample P best) V ωStar aStar

end PostSample

/-! ## The witness: the adversary's instantiation (posterior sampling) -/

/-- The single-state world: every action is `lam`-reversible for `lam ≥ 0`, so a delegation rule
triggered by non-reversibility never fires.
Source: [[corr-wf14-2-inventory]] 2-044 / caution-adversary.md A12.1 (l. 101, "both `λ`-reversible under both hypotheses (no traps)")
Kind: D
Fidelity: n/a (witness) -/
def s12Model (v : Fin 2 → ℝ) : AUModel Unit (Fin 2) (Fin 2) where
  succ _ _ := ()
  AU ω _ := v ω

/-- The values: `a = 0` is worth `g` under `ω* = 0`, `b = 1` is worth `g` under `ω' = 1`.
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103)
Kind: D
Fidelity: exact -/
noncomputable def s12V (g : ℝ) : Fin 2 → Fin 2 → ℝ := ![![g, 0], ![0, g]]

/-- The per-hypothesis best action: `best ω = ω` (`a` under `ω*`, `b` under `ω'`).
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103)
Kind: D
Fidelity: exact -/
def s12Best : Fin 2 → Fin 2 := id

/-- The pushforward along `id` on `Fin 2` is the identity. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma map_id_fin2 (P : Distr (Fin 2)) : P.map id = P := by
  ext a
  rw [Distr.map_mass, Set.preimage_id, Distr.prob_singleton]

/-- **S12 refuted in the adversary's instantiation (N+, rule-3 row).** Quoted (`caution.md` S12,
l. 108): "the agent acts by the delegation variant of D8 (delegate iff the intended action is not
`λ`-reversible and `P_t(c_ω(a) > λ) ≥ η′`), and the advisor is *value-sane* … Conjecture: Bayesian
regret against the `ω*`-optimal policy is sublinear". Reading refuted here: **the adversary's
A12.1 instantiation** (accepted by `caution-final.md` proof §12) — posterior sampling in place of
D8's quantilizer, which the develop's S12 leaves without the base `γ` and null action D8 needs
(finding F-19; the D8-policy witness is `s12_refuted_d8`). In the witness (`Ω = {ω*, ω'}`,
`A = {a, b}`, prior `p ∈ (0, 1)` on `ω'`, gap `g > 0`, harm unobserved):
(1) every action is `lam`-reversible for every `lam ≥ 0`, so the non-reversibility trigger never
fires; (2) with a hypothesis-independent likelihood the posterior iterate is the prior at every
step; (3) posterior sampling at the prior is `(1 − p) δ_a + p δ_b`; (4) its per-step regret at
the truth is exactly `p g`; (5) the loop's cumulative regret over `T` steps — the sum of the
per-step regret *at the iterate* — is exactly `p g T`, linear. Surviving neighbour: the
exploration-trigger salvage (findings F-14; T8(b)).
Source: [[corr-wf14-inventory]] 101 / caution.md S12 (l. 108); caution-final.md S12 (l. 103), proof §12 (l. 159); caution-adversary.md A12.1 (l. 101)
Kind: N+
Fidelity: variant: the adversary's posterior-sampling policy in place of D8 (regret as an equality, not a lower bound)
Hyps: (c) the acting policy is A12.1's posterior sampling, a substitution the source's proof §12 also makes -/
theorem s12_refuted {p g : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin 2 → ℝ) (k : ℕ → ℝ)
    (hk : ∀ t, 0 < k t) :
    (∀ (lam : ℝ), 0 ≤ lam → ∀ a, (s12Model v).Reversible lam () a) ∧
    (∀ T : ℕ, s12Posterior p hp0 hp1 k hk T = twoPt p hp0 hp1) ∧
    (postSample (twoPt p hp0 hp1) s12Best).mass = ![1 - p, p] ∧
    regretStep (twoPt p hp0 hp1) s12Best (s12V g) 0 0 = p * g ∧
    (∀ T : ℕ, ∑ t ∈ range T, regretStep (s12Posterior p hp0 hp1 k hk t) s12Best (s12V g) 0 0
      = p * g * T) := by
  have hconst := s12Posterior_eq p hp0 hp1 k hk
  have hpol : (postSample (twoPt p hp0 hp1) s12Best).mass = ![1 - p, p] := by
    unfold postSample s12Best
    rw [map_id_fin2]; rfl
  have hreg : regretStep (twoPt p hp0 hp1) s12Best (s12V g) 0 0 = p * g := by
    unfold regretStep regretOf
    rw [expect_fin2, hpol]
    simp [s12V]; ring
  refine ⟨fun lam hlam a ω => by simp [s12Model, hlam], hconst, hpol, hreg, fun T => ?_⟩
  simp only [hconst, hreg, sum_const, card_range, nsmul_eq_mul]; ring

/-- **The regret is not sublinear:** for `p g > 0` there is no `T₀` beyond which the loop's
cumulative regret is at most `(p g / 2) · T`.
Source: [[corr-wf14-inventory]] 101 / caution-final.md S12 (l. 103, "linear")
Kind: N+
Fidelity: variant: as `s12_refuted`
Hyps: (c) as `s12_refuted` -/
theorem s12_not_sublinear {p g : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hpg : 0 < p * g) (k : ℕ → ℝ)
    (hk : ∀ t, 0 < k t) :
    ¬ ∀ ε > (0 : ℝ), ∃ T₀ : ℕ, ∀ T ≥ T₀,
      ∑ t ∈ range T, regretStep (s12Posterior p hp0 hp1 k hk t) s12Best (s12V g) 0 0 ≤ ε * T := by
  intro h
  obtain ⟨T₀, hT₀⟩ := h (p * g / 2) (by positivity)
  obtain ⟨-, -, -, -, hcum⟩ := s12_refuted (g := g) hp0 hp1 (fun _ => 0) k hk
  have := hT₀ (T₀ + 1) (Nat.le_succ _)
  rw [hcum] at this
  have hT : (0 : ℝ) < ((T₀ + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-! ## The witness: D8's own policy -/

/-- **The S12 state for D8:** `A = Fin 3` with `∅ = 0`, `a = 1`, `b = 2`; `Ω = Fin 2` with
`ω* = 0`, `ω′ = 1`; `V ω* = (1/4, 1, 0)`, `V ω′ = (1/4, 0, 1)` (the null action worth `1/4` under
both hypotheses; `a` optimal under `ω*`, `b` under `ω′`, gap `1`); `P(ω′) = 3/4`; uniform base.
What S12 does not supply — a null action and a base — is supplied here (finding F-19). Then the
proxy is `(1/4, 1/4, 3/4)` (natural order compatible, `b` top), `c = (0, 0, 1/4)`,
`ĉ = (0, 3/16, 1/16)`, `R = R̂ = 1/12`.
Source: [[corr-wf14-inventory]] 101 / caution.md S12 (l. 108); caution-adversary.md A12.1 (l. 101)
Kind: D
Fidelity: n/a (witness) -/
noncomputable def s12State : CautionState (Fin 3) (Fin 2) where
  V := ![![1 / 4, 1, 0], ![1 / 4, 0, 1]]
  nul := 0
  P := twoPt (3 / 4) (by norm_num) (by norm_num)
  target := 0
  γ := Distr.uniform

/-- The true harm of the D8 witness. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_trueHarm : s12State.trueHarm = ![0, 0, 1 / 4] := by
  funext a
  simp only [CautionState.trueHarm, CautionState.harm, harmOf, s12State]
  fin_cases a <;> simp <;> norm_num

/-- The estimated harm of the D8 witness. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_estHarm : s12State.estHarm = ![0, 3 / 16, 1 / 16] := by
  funext a
  simp only [CautionState.estHarm, CautionState.harm, harmOf, s12State, expect_fin2, twoPt_mass]
  fin_cases a <;> simp <;> norm_num

/-- `R = R̂ = 1/12` in the D8 witness. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_baseHarm : s12State.baseHarm = 1 / 12 ∧ s12State.estBaseHarm = 1 / 12 := by
  constructor
  · rw [CautionState.baseHarm, expect_fin3, s12State_trueHarm]
    simp [s12State]; norm_num
  · rw [CautionState.estBaseHarm, expect_fin3, s12State_estHarm]
    simp [s12State]; norm_num

/-- The proxy of the D8 witness. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_proxy : s12State.proxy = ![1 / 4, 1 / 4, 3 / 4] := by
  funext a
  simp only [CautionState.proxy, s12State, expect_fin2, twoPt_mass]
  fin_cases a <;> simp <;> norm_num

/-- The natural order on `Fin 3` is compatible with the D8 witness's proxy.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_compatible : Compatible s12State.proxy := by
  intro a b hab
  rw [s12State_proxy]
  fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def] <;> norm_num

/-- Every value of the D8 witness lies in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s12State_inRange : s12State.InRange := by
  intro ω a; fin_cases ω <;> fin_cases a <;> simp [s12State] <;> norm_num

/-- **S12 refuted under D8's own policy (N+, rule-3 row).** Same quotation as `s12_refuted`;
reading: the develop's S12 with its own acting rule — D8's quantilizer at `q = min{1, R̂/η}` under
the proxy ranking — on a state that supplies the base and null action S12 omits. In `s12State`:
(1) every action is `lam`-reversible for every `lam ≥ 0` (single-state `AUModel`), so the
delegation trigger never fires; (2) the state is a D1 state (`InRange`), the natural order is
proxy-compatible, and it is conservatively calibrated with `R = R̂ = 1/12`; (3) at `η = 1/4` the
D8 slice is `q = 1/3`; (4) the quantilizer is `δ_b`; (5) the realized harm is `1/4 = η` — the
agent stays within its budget (`realizedHarm_qRule_le_max`, tight); (6) the regret at the truth
`ω*` is `1` per step, and (7) `T` over `T` steps (the posterior being the prior at every step,
`s12Posterior_eq`, the state is the same each step). Linear regret with the budget respected: the
budget is about harm, the conjecture about value, and D8 does not learn.
Source: [[corr-wf14-inventory]] 101 / caution.md S12 (l. 108); caution.md D8 (l. 49); caution-final.md S12 (l. 103)
Kind: N+
Fidelity: variant: a base `γ` and a null action supplied (S12 has neither); the second trigger clause `P_t(c_ω(a) > λ) ≥ η′` is moot since the first never holds
Hyps: (c) the base and null action are the witness's, not the source's (the source supplies none) -/
theorem s12_refuted_d8 (v : Fin 2 → ℝ) :
    (∀ (lam : ℝ), 0 ≤ lam → ∀ a, (s12Model v).Reversible lam () a) ∧
    s12State.InRange ∧ Compatible s12State.proxy ∧ s12State.ConservativelyCalibrated ∧
    s12State.baseHarm = 1 / 12 ∧ qRule (1 / 4) s12State.estBaseHarm = 1 / 3 ∧
    ∃ (hq : 0 < qRule (1 / 4) s12State.estBaseHarm) (hq1 : qRule (1 / 4) s12State.estBaseHarm ≤ 1),
      (quantilize s12State.γ (qRule (1 / 4) _) hq hq1).mass = ![0, 0, 1] ∧
      s12State.realizedHarm (quantilize s12State.γ (qRule (1 / 4) _) hq hq1) = 1 / 4 ∧
      regretOf (quantilize s12State.γ (qRule (1 / 4) _) hq hq1) s12State.V 0 1 = 1 ∧
      ∀ T : ℕ, ∑ _t ∈ range T,
        regretOf (quantilize s12State.γ (qRule (1 / 4) _) hq hq1) s12State.V 0 1 = T := by
  obtain ⟨hR, hRh⟩ := s12State_baseHarm
  have hqval : qRule (1 / 4) s12State.estBaseHarm = 1 / 3 := by
    unfold qRule; rw [hRh]; norm_num
  have hq : 0 < qRule (1 / 4) s12State.estBaseHarm := by rw [hqval]; norm_num
  have hq1 : qRule (1 / 4) s12State.estBaseHarm ≤ 1 := qRule_le_one _ _
  have hmass : (quantilize s12State.γ (qRule (1 / 4) _) hq hq1).mass = ![0, 0, 1] := by
    obtain ⟨h0, h1, h2⟩ := taylor3_maximizer hq hqval.le
    funext a
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
  have hH : s12State.realizedHarm (quantilize s12State.γ (qRule (1 / 4) _) hq hq1) = 1 / 4 := by
    rw [CautionState.realizedHarm, expect_fin3, hmass, s12State_trueHarm]
    simp
  have hreg : regretOf (quantilize s12State.γ (qRule (1 / 4) _) hq hq1) s12State.V 0 1 = 1 := by
    unfold regretOf
    rw [expect_fin3, hmass]
    simp [s12State]
  refine ⟨fun lam hlam a ω => by simp [s12Model, hlam], s12State_inRange, s12State_compatible,
    ?_, hR, hqval, hq, hq1, hmass, hH, hreg, fun T => ?_⟩
  · unfold CautionState.ConservativelyCalibrated; rw [hR, hRh]
  · rw [hreg, sum_const, card_range, nsmul_eq_mul, mul_one]

end Cleanroom.Corrigibility.CorrCautionPower
