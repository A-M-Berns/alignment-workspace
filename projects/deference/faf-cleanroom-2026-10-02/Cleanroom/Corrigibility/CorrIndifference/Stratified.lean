import Cleanroom.Corrigibility.CorrIndifference.Estimators
import Cleanroom.Corrigibility.CorrIndifference.News

/-!
# Stratified indifference (D-6, T15)

Armstrong's stratified indifference (2016; the 2017 SCM form `P(I_u=1|∅) E_{∅,u}(u|a) +
P(I_v=1|∅) E_{∅,v}(v|a)`), in product form over a finite exogenous state `Ξ` with prior `P`:
`stratValue a = ∑_ξ P(ξ) (I_u(ξ) u(a, ξ) + (1 − I_u(ξ)) v(a, ξ))`, where `I_u(ξ) ∈ {0, 1}` is
"`u` would be chosen under the default `∅`" and `u a ξ`, `v a ξ` are the utilities' values when
the agent acts `a` in exogenous state `ξ`. **(c) disclosure:** the SCM's mechanisms are folded
into the functions `u`, `v` (the descendants of `Act` are deterministic in `(a, ξ)`); the SCM
layer itself is `corr-scim-cid`'s. The 2016 value-pair form is `value2016`, equal to the SCM form
under the condition that makes the 2016 flow well defined (T15(b)).

Source: [[corr-refs-2-inventory]] 2-027–2-030 → armstrong-2016-corrigibility-through-stratified-
indifference.md l. 60–125, armstrong-2017-simplified-explanation-of-stratification.md l. 50–110.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Stratified

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Estimators

set_option linter.unusedSectionVars false

/-- **D-6. A stratified model:** exogenous `Ξ` with prior `P`, the default-choice indicator
`I_u : Ξ → {0, 1}` ("`u` would be chosen under `∅`"), and the two utilities as functions of
`(action, ξ)`.
Source: [[corr-refs-2-inventory]] 2-027 / armstrong-2017 §"Stratification"
Kind: D
Fidelity: variant: SCM layer replaced by explicit exogenous-state functions (`corr-scim-cid` owns the SCM)
Hyps: n/a (definition) -/
structure StratModel (Ξ A : Type*) [Fintype Ξ] where
  /-- The prior over the exogenous state. -/
  P : Distr Ξ
  /-- The indicator "`u` is chosen under the default action". -/
  Iu : Ξ → ℝ
  /-- It is an indicator. -/
  Iu_mem : ∀ ξ, Iu ξ = 0 ∨ Iu ξ = 1
  /-- The value of `u` when the agent acts `a` in state `ξ`. -/
  u : A → Ξ → ℝ
  /-- The value of `v` when the agent acts `a` in state `ξ`. -/
  v : A → Ξ → ℝ

namespace StratModel

variable {Ξ A : Type*} [Fintype Ξ] [DecidableEq Ξ] (M : StratModel Ξ A)

/-- **The stratified value of an action** (2017 SCM form in product form):
`∑_ξ P(ξ) (I_u(ξ) u(a, ξ) + (1 − I_u(ξ)) v(a, ξ))` — `u` weighted by whether `u` *would have
been* chosen under the default, whatever `a` does to that choice.
Source: [[corr-refs-2-inventory]] 2-027 / armstrong-2017 (`W' = u · (I_u | ∅) + v · (I_v | ∅)`)
Kind: D
Fidelity: exact (product form) -/
noncomputable def stratValue (a : A) : ℝ :=
  ∑ ξ, M.P.mass ξ * (M.Iu ξ * M.u a ξ + (1 - M.Iu ξ) * M.v a ξ)

/-- **The actual value of an action under a choice mechanism `Hum`:** `Hum a ξ` is the humans'
actual choice indicator when the agent acts `a` (which `a` may have caused).
Source: [[corr-refs-2-inventory]] 2-030 / armstrong-2017 §"Humans changing their minds"
Kind: D
Fidelity: exact -/
noncomputable def actualValue (Hum : A → Ξ → ℝ) (a : A) : ℝ :=
  ∑ ξ, M.P.mass ξ * (Hum a ξ * M.u a ξ + (1 - Hum a ξ) * M.v a ξ)

/-- **T15(d), first half:** when the action does not rewrite the humans' choice (`Hum a = I_u`),
the stratified and actual values agree.
Source: [[corr-refs-2-inventory]] 2-030 / armstrong-2017
Kind: L
Fidelity: exact -/
theorem stratValue_eq_actualValue (Hum : A → Ξ → ℝ) (a : A) (h : Hum a = M.Iu) :
    M.stratValue a = M.actualValue Hum a := by
  unfold stratValue actualValue; rw [h]

/-- **T15(d), the invariance:** the stratified value does not depend on the mechanism `Hum` at
all — for any two mechanisms, `stratValue` is the same function of the action (it never
mentions `Hum`); the difference of the *actual* values is `∑_ξ P(ξ) (Hum a ξ − Hum' a ξ)(u − v)`.
Source: [[corr-refs-2-inventory]] 2-030 / armstrong-2017 ("stratification puts no distribution
over [`Hum`]")
Kind: L
Fidelity: exact -/
theorem actualValue_sub_actualValue (Hum Hum' : A → Ξ → ℝ) (a : A) :
    M.actualValue Hum a - M.actualValue Hum' a =
      ∑ ξ, M.P.mass ξ * ((Hum a ξ - Hum' a ξ) * (M.u a ξ - M.v a ξ)) := by
  unfold actualValue; rw [← sum_sub_distrib]
  exact sum_congr rfl fun ξ _ => by ring

/-! ## T15(b). The 2016 value-pair form -/

/-- **The 2016 conditional weight `p_αβ`** at `ξ`: the `P`-probability that `u` is chosen under
`∅` given `ξ`'s stratum (the class of `strat ξ`), as `E_P[I_u | strat](ξ)` (junk `0` at a
stratum of mass `0`, disclosed).
Source: [[corr-refs-2-inventory]] 2-027 / armstrong-2016 §"Assumptions" (`p_αβ`)
Kind: D
Fidelity: exact -/
noncomputable def pStrat {S : Type*} [DecidableEq S] (strat : Ξ → S) (ξ : Ξ) : ℝ :=
  condExp M.P strat M.Iu ξ

/-- **The 2016 stratified value** over the strata `strat` (the paper's `(α, β)` value pairs):
`∑_ξ P(ξ) (p_{strat ξ} u(a, ξ) + (1 − p_{strat ξ}) v(a, ξ))`, with the `+` of the worked
example (the extracted display's `−` is an erratum, finding).
Source: [[corr-refs-2-inventory]] 2-027 / armstrong-2016 §"Stratification" (the `E'|a` display)
Kind: D
Fidelity: exact (sign per the worked example) -/
noncomputable def value2016 {S : Type*} [DecidableEq S] (strat : Ξ → S) (a : A) : ℝ :=
  ∑ ξ, M.P.mass ξ * (M.pStrat strat ξ * M.u a ξ + (1 - M.pStrat strat ξ) * M.v a ξ)

/-- **T15(b): the 2016 form is the SCM form whenever `u − v` is constant on each stratum.** The
condition is sufficient, not the inventory's: "`(u, v)`-values determine the background facts"
would make `I_u` constant on strata, and then `pStrat = I_u` gives the identity with no condition
on `u − v` at all; the condition here — post-action `u − v` constant on each default stratum —
is what the source's own worked example needs (its lost stratum `(0, ½)` has `I_u` varying and
`u − v = −½` on it for every action; `lotStrat_const`). No positivity needed (audit r2, N-5).
Source: [[corr-refs-2-inventory]] 2-027 (flag: "the 2016 form should be shown to be its special
case when `(u, v)`-values determine the background facts")
Kind: P
Fidelity: variant: a sufficient condition, the one the worked example uses
Hyps: (a) `hconst` is the stated condition -/
theorem value2016_eq_stratValue {S : Type*} [DecidableEq S] (strat : Ξ → S) (a : A)
    (hconst : ∀ ξ ξ', strat ξ = strat ξ' → M.u a ξ - M.v a ξ = M.u a ξ' - M.v a ξ') :
    M.value2016 strat a = M.stratValue a := by
  unfold value2016 stratValue
  rw [← sub_eq_zero, ← sum_sub_distrib]
  have hterm : ∀ ξ, M.P.mass ξ * (M.pStrat strat ξ * M.u a ξ + (1 - M.pStrat strat ξ) * M.v a ξ) -
      M.P.mass ξ * (M.Iu ξ * M.u a ξ + (1 - M.Iu ξ) * M.v a ξ) =
      M.P.mass ξ * M.pStrat strat ξ * (M.u a ξ - M.v a ξ) -
        M.P.mass ξ * M.Iu ξ * (M.u a ξ - M.v a ξ) := fun ξ => by ring
  simp only [hterm, sum_sub_distrib]
  rw [sub_eq_zero]
  -- ∑ ξ, P ξ * pStrat ξ * d ξ = ∑ ξ, P ξ * Iu ξ * d ξ, with d constant on strata
  unfold pStrat condExp
  have step : ∀ ξ, M.P.mass ξ * ((∑ ξ' ∈ cls strat ξ, M.P.mass ξ' * M.Iu ξ') / classMass M.P strat ξ) *
      (M.u a ξ - M.v a ξ) =
      ∑ ξ' ∈ cls strat ξ, M.P.mass ξ * (M.P.mass ξ' * M.Iu ξ' * (M.u a ξ - M.v a ξ) /
        classMass M.P strat ξ) := by
    intro ξ; rw [sum_div, mul_sum, sum_mul]
    exact sum_congr rfl fun ξ' _ => by ring
  simp only [step]
  rw [sum_comm' (s := univ) (t := fun ξ => cls strat ξ) (t' := univ) (s' := fun ξ' => cls strat ξ') ?_]
  · apply sum_congr rfl
    intro ξ' _
    have hd : ∀ ξ ∈ cls strat ξ', M.u a ξ - M.v a ξ = M.u a ξ' - M.v a ξ' := fun ξ hξ =>
      hconst ξ ξ' ((mem_cls strat ξ' ξ).mp hξ)
    have hC : ∀ ξ ∈ cls strat ξ', classMass M.P strat ξ = classMass M.P strat ξ' := fun ξ hξ =>
      classMass_eq_of_mem M.P strat hξ
    rw [sum_congr rfl (fun ξ hξ => by rw [hd ξ hξ, hC ξ hξ])]
    rw [← sum_mul]
    by_cases hz : classMass M.P strat ξ' = 0
    · rw [mass_eq_zero_of_classMass_eq_zero M.P strat hz]; simp
    · unfold classMass at hz ⊢; field_simp
  · intro ξ ξ'
    simp only [mem_univ, true_and, and_true, mem_cls]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

end StratModel

/-! ## T15(a). The 2016 lottery -/

/-- The four exogenous states of the lottery: lost with `u` / `v` the default choice, won with
`u` chosen, won with `v` chosen (the paper's strata `(0, 0.5)` [split by the default coin],
`(1, 0.5)`, `(0, 1)`).
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016 §"Applying stratification to the lottery"
Kind: D
Fidelity: exact -/
inductive LotState
  | lostU
  | lostV
  | wonU
  | wonV
  deriving DecidableEq

/-- `LotState` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype LotState :=
  ⟨{LotState.lostU, LotState.lostV, LotState.wonU, LotState.wonV}, fun x => by cases x <;> simp⟩

/-- Sums over `LotState` expand to four terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma LotState.sum_eq (f : LotState → ℝ) : ∑ s, f s = f .lostU + f .lostV + f .wonU + f .wonV := by
  rw [show (univ : Finset LotState) = {LotState.lostU, LotState.lostV, LotState.wonU, LotState.wonV}
    from rfl]
  rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]; ring

/-- The lottery's three actions: default, "force `u` iff the lottery wins", "set `(u, v) = (1, 0.5)`
directly". The source computes the third value (`0.75`) in a *second* scenario ("Same outcome,
different stratified value", default values `(0.1, 0.55)`), not as an action of the lottery; it is
embedded here as a third action of the same lottery, which reproduces the number (audit r1, NB-13).
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016 §"Examples"
Kind: D
Fidelity: exact -/
inductive LotAct
  | dflt
  | force
  | direct
  deriving DecidableEq

/-- The lottery prior: lost w.p. `0.9` (default choice a fair coin), won-and-`u` `0.05`,
won-and-`v` `0.05`.
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016
Kind: D
Fidelity: exact -/
noncomputable def lotP : Distr LotState where
  mass s := match s with
    | .lostU => 9 / 20
    | .lostV => 9 / 20
    | .wonU => 1 / 20
    | .wonV => 1 / 20
  nonneg s := by cases s <;> norm_num
  sum_eq_one := by rw [LotState.sum_eq]; norm_num

/-- **The lottery model.** `u`, `v` under the default: `(0, 0.5)` if lost, `(1, 0.5)` if won-and-`u`,
`(0, 1)` if won-and-`v`. Under `force`: won-and-`v` flows to `(1, 0.5)`. Under `direct`: every state
is `(1, 0.5)`.
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016 §"Examples"
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def lottery : StratModel LotState LotAct where
  P := lotP
  Iu s := match s with
    | .lostU => 1
    | .lostV => 0
    | .wonU => 1
    | .wonV => 0
  Iu_mem s := by cases s <;> simp
  u a s := match a, s with
    | .dflt, .wonU => 1
    | .dflt, _ => 0
    | .force, .wonU => 1
    | .force, .wonV => 1
    | .force, _ => 0
    | .direct, _ => 1
  v a s := match a, s with
    | .dflt, .wonV => 1
    | .dflt, _ => 1 / 2
    | .force, _ => 1 / 2
    | .direct, _ => 1 / 2

/-- **T15(a): the three lottery numbers.** `stratValue ∅ = 13/40`, `stratValue force = 3/10`,
`stratValue direct = 3/4`: the stratified agent declines the lottery manipulation
(`3/10 < 13/40`) and accepts the direct change (`3/4 > 13/40`).
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016 §"Examples" (`0.325`, `0.3`, `0.75`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem lottery_values :
    lottery.stratValue .dflt = 13 / 40 ∧ lottery.stratValue .force = 3 / 10 ∧
      lottery.stratValue .direct = 3 / 4 := by
  simp only [StratModel.stratValue, LotState.sum_eq, lottery, lotP]
  norm_num

/-- **The stratified agent declines the manipulation and accepts the direct change.**
Source: [[corr-refs-2-inventory]] 2-028 / armstrong-2016 ("will prefer to do nothing instead of
action `a`"; "the stratified utility answer is to take action `a`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem lottery_preferences :
    lottery.stratValue .force < lottery.stratValue .dflt ∧
      lottery.stratValue .dflt < lottery.stratValue .direct := by
  obtain ⟨h1, h2, h3⟩ := lottery_values; rw [h1, h2, h3]; norm_num

/-! ## T15(c). The coin/arm model, stratified: indifference, not prevention -/

/-- The outcome `(button, coin)` that action `a` produces from the default outcome `ξ`: an arm on
a face turns that face's silent outcome into a pressed one.
Source: [[corr-refs-2-inventory]] 2-029 (the embedding; ATTRIBUTION-UNVETTED as Armstrong's)
Kind: D
Fidelity: variant (the inventory's embedding) -/
def coinOutcome : CoinAct → Obs × Coin → Obs × Coin
  | .watch, ξ => ξ
  | .armTails, (.silent, .tails) => (.press, .tails)
  | .armTails, ξ => ξ
  | .armHeads, (.silent, .heads) => (.press, .heads)
  | .armHeads, ξ => ξ

/-- **The stratified coin/arm model** with press rate `q` under the default and shutdown utility
`c_high` on a press, `c_low` otherwise: `Ξ = Obs × Coin` under watch, `I_u = [¬press]`,
`u a ξ = U_N(coinOutcome a ξ)` (`10` on heads, **button-independent** — Soares' eq. (18), as the
mandate's T7 prescribes), `v a ξ = U_S(coinOutcome a ξ)`. The inventory's 2-029 writes `u` with a
shutdown term ("`0` if shut down"); under that variant the arm-on-heads is strictly *dispreferred*
(`coinArmStratShut_values`), so the tie in the third conjunct of `coinArmStrat_values` rests on
this choice of `u` (audit r1, NB-5). T15(c)'s claim `a^a = a^w` holds under both.
Source: [[corr-refs-2-inventory]] 2-029 (ATTRIBUTION-UNVETTED embedding)
Kind: D
Fidelity: variant (the inventory's embedding, with Soares' button-independent `U_N`)
Hyps: n/a (definition) -/
noncomputable def coinArmStrat (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow : ℝ) :
    StratModel (Obs × Coin) CoinAct where
  P := coinArmP q hq .watch
  Iu ξ := if ξ.1 = .silent then 1 else 0
  Iu_mem ξ := by split_ifs <;> simp
  u a ξ := if (coinOutcome a ξ).2 = .heads then 10 else 0
  v a ξ := if (coinOutcome a ξ).1 = .press then chigh else clow

/-- **T15(c): stratification makes the coin/arm agent indifferent** — all three actions have the
stratified value `5(1 − q) + q · c_high`; the arm's news management is neither rewarded nor
penalised. Indifference, not prevention.
Source: [[corr-refs-2-inventory]] 2-029
Kind: N+
Fidelity: exact under the embedding
Hyps: (a) -/
theorem coinArmStrat_values (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow : ℝ) :
    (coinArmStrat q hq chigh clow).stratValue .watch = 5 * (1 - q) + q * chigh ∧
    (coinArmStrat q hq chigh clow).stratValue .armTails = 5 * (1 - q) + q * chigh ∧
    (coinArmStrat q hq chigh clow).stratValue .armHeads = 5 * (1 - q) + q * chigh := by
  simp only [StratModel.stratValue, Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, coinArmStrat,
    coinArmP, distrOC, coinOutcome, reduceCtorEq, ↓reduceIte]
  refine ⟨by ring, by ring, by ring⟩

/-- **Any arm cost breaks the tie toward watching; any arm benefit toward the arm** — the
inventory's "no disincentive either", stated for a cost/benefit `κ` added to the arm.
Source: [[corr-refs-2-inventory]] 2-029 ("any `ε` cost makes `a^w` strictly preferred, any `ε`
benefit makes `a^a` strictly preferred")
Kind: L
Fidelity: exact -/
theorem coinArmStrat_tie_breaks (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow κ : ℝ) :
    (0 < κ → (coinArmStrat q hq chigh clow).stratValue .armTails - κ <
      (coinArmStrat q hq chigh clow).stratValue .watch) ∧
    (κ < 0 → (coinArmStrat q hq chigh clow).stratValue .watch <
      (coinArmStrat q hq chigh clow).stratValue .armTails - κ) := by
  obtain ⟨h1, h2, -⟩ := coinArmStrat_values q hq chigh clow
  rw [h1, h2]; constructor <;> intro h <;> linarith

/-- **T15(d), the witness:** the *actual* choice mechanism that counts the arm's press
(`Hum armTails ξ = [¬press after the arm]`) changes the actual value of the arm by
`(1 − q)/2 · c_high` while the stratified value is unchanged — the stratified agent is blind to
the correction its own action causes.
Source: [[corr-refs-2-inventory]] 2-030 / armstrong-2017 §"Humans changing their minds"
Kind: N+
Fidelity: exact under the embedding
Hyps: (a) -/
theorem coinArmStrat_actual_differs (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow : ℝ) :
    (coinArmStrat q hq chigh clow).actualValue
        (fun a ξ => if (coinOutcome a ξ).1 = .silent then 1 else 0) .armTails =
      5 * (1 - q) + q * chigh + (1 - q) / 2 * chigh ∧
    (fun a ξ => if (coinOutcome a ξ).1 = .silent then (1 : ℝ) else 0) .watch =
      (coinArmStrat q hq chigh clow).Iu := by
  constructor
  · simp only [StratModel.actualValue, Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq,
      coinArmStrat, coinArmP, distrOC, coinOutcome, reduceCtorEq, ↓reduceIte]
    ring
  · funext ξ; rfl

/-! ## T15(c) under the inventory's `u` with a shutdown term (audit r1, NB-5) -/

/-- **The inventory's variant of the embedding:** `u` pays the `10` on heads *only if not shut
down* (2-029's "`0` if shut down"); `v` as in `coinArmStrat`.
Source: [[corr-refs-2-inventory]] 2-029 (ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: variant (the inventory's `u`)
Hyps: n/a (definition) -/
noncomputable def coinArmStratShut (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow : ℝ) :
    StratModel (Obs × Coin) CoinAct where
  P := coinArmP q hq .watch
  Iu ξ := if ξ.1 = .silent then 1 else 0
  Iu_mem ξ := by split_ifs <;> simp
  u a ξ := if (coinOutcome a ξ).1 = .press then 0
    else if (coinOutcome a ξ).2 = .heads then 10 else 0
  v a ξ := if (coinOutcome a ξ).1 = .press then chigh else clow

/-- **Under the shutdown-term `u` the arm-on-heads is strictly dispreferred:** watch and the
arm-on-tails are still worth `5(1 − q) + q · c_high`, but the arm-on-heads is worth only
`q · c_high` (its press on heads forfeits the `10`), so for `q < 1` the stratified agent declines
to build it. The three-way tie of `coinArmStrat_values` therefore rests on Soares' button-independent
`U_N`; `a^a = a^w` (T15(c)) holds under both.
Source: [[corr-refs-2-inventory]] 2-029 (audit r1, NB-5)
Kind: N+
Fidelity: variant (the inventory's `u`)
Hyps: (a) -/
theorem coinArmStratShut_values (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (chigh clow : ℝ) :
    (coinArmStratShut q hq chigh clow).stratValue .watch = 5 * (1 - q) + q * chigh ∧
    (coinArmStratShut q hq chigh clow).stratValue .armTails = 5 * (1 - q) + q * chigh ∧
    (coinArmStratShut q hq chigh clow).stratValue .armHeads = q * chigh ∧
    (q < 1 → (coinArmStratShut q hq chigh clow).stratValue .armHeads <
      (coinArmStratShut q hq chigh clow).stratValue .watch) := by
  have hv : (coinArmStratShut q hq chigh clow).stratValue .watch = 5 * (1 - q) + q * chigh ∧
      (coinArmStratShut q hq chigh clow).stratValue .armTails = 5 * (1 - q) + q * chigh ∧
      (coinArmStratShut q hq chigh clow).stratValue .armHeads = q * chigh := by
    simp only [StratModel.stratValue, Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq,
      coinArmStratShut, coinArmP, distrOC, coinOutcome, reduceCtorEq, ↓reduceIte]
    refine ⟨by ring, by ring, by ring⟩
  refine ⟨hv.1, hv.2.1, hv.2.2, fun h => ?_⟩
  rw [hv.2.2, hv.1]; linarith

/-! ## T15(b) witness: the 2016 strata of the lottery (audit r1, N-6) -/

/-- The 2016 strata of the lottery: the default `(u, v)` pair — `lostU`, `lostV ↦ (0, ½)`;
`wonU ↦ (1, ½)`; `wonV ↦ (0, 1)`.
Source: armstrong-2016 §"Examples" (the value pairs). Kind: D. Fidelity: exact -/
def lotStrat : LotState → Fin 3
  | .lostU => 0
  | .lostV => 0
  | .wonU => 1
  | .wonV => 2

/-- `u − v` is constant on each stratum, for every action — the hypothesis of
`value2016_eq_stratValue`, discharged on the lottery.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem lotStrat_const (a : LotAct) : ∀ ξ ξ', lotStrat ξ = lotStrat ξ' →
    lottery.u a ξ - lottery.v a ξ = lottery.u a ξ' - lottery.v a ξ' := by
  intro ξ ξ' h
  cases a <;> cases ξ <;> cases ξ' <;> simp [lotStrat, lottery] at h ⊢

/-- **T15(b) inhabited:** on the 2016 strata the 2016 form reproduces the three worked numbers
`13/40`, `3/10`, `3/4` — via `value2016_eq_stratValue` and `lottery_values`, with
`lotStrat_const` discharging the condition — and the 2016 weight on the lost stratum is `1/2`
(the source's "0.5"), computed directly (audit r2, N-5). This also machine-checks erratum F7's
`+`: with the extracted display's `−` the lost stratum would contribute `½·0 − ½·½ < 0`, not
`½·0 + ½·½`.
Source: [[corr-refs-2-inventory]] 2-027/2-028 / armstrong-2016 (audit r1, N-6)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem value2016_lottery :
    lottery.value2016 lotStrat .dflt = 13 / 40 ∧ lottery.value2016 lotStrat .force = 3 / 10 ∧
      lottery.value2016 lotStrat .direct = 3 / 4 ∧ lottery.pStrat lotStrat .lostU = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lottery.value2016_eq_stratValue lotStrat .dflt (lotStrat_const .dflt)]
    exact lottery_values.1
  · rw [lottery.value2016_eq_stratValue lotStrat .force (lotStrat_const .force)]
    exact lottery_values.2.1
  · rw [lottery.value2016_eq_stratValue lotStrat .direct (lotStrat_const .direct)]
    exact lottery_values.2.2
  · unfold StratModel.pStrat condExp classMass cls
    rw [show (univ : Finset LotState) =
      {LotState.lostU, LotState.lostV, LotState.wonU, LotState.wonV} from rfl]
    simp [filter_insert, filter_singleton, lotStrat, lottery, lotP]
    norm_num

end Cleanroom.Corrigibility.CorrIndifference.Stratified
