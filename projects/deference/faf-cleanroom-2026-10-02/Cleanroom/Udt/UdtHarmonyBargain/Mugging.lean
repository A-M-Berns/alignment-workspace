import Cleanroom.Udt.UdtHarmonyBargain.Translation
import Cleanroom.Found.DpCoreTree.Catalogue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# `udt-harmony-bargain` — the two-prior mugging: the pessimistic prior-self's veto (T10)

Two decision-points with different priors on the mugging coin, `X₁(H) = 1/2` and `X₂(H) = 1/4`,
common utility of the *implemented* policy (pay iff both say pay), on the mugging with `x = 1`,
`y = 2`: `U₁(pay,pay) = 1/2`, `U₂(pay,pay) = −1/4`, every other outcome `(0, 0)`. For **every**
selector (welfare or not), no profile with outcome `(pay, pay)` is a Nash equilibrium of the
bargaining game — player 2's `(refuse, ∅)` forces the batna profile, worth `0 > −1/4` — hence
none is harmonious, in the pure and in the support form (`veto`, `veto_support`).

**Refuted slogan** (HA-15′'s KILLED headline): "utilitarian bargaining between prior-selves = UDT
under the mixture prior". Reading: `W = w₁U₁ + w₂U₂` with `w₁ > 1/3` strictly prefers the pay deal
(`mugW_argmax`) and is Pareto-consistent, yet no harmonious profile realises it. Surviving
neighbour: the linearity identity `w₁U₁(O) + w₂U₂(O) = 𝔼_{w₁X₁ + w₂X₂}[u(O, ·)]`
(`mugW_eq_mixture`) — a statement about an *imposed* aggregator that is not a player.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue

/-- The mugging with `P(H) = θ` (the catalogue's `mug1` with `FinDistr.coin` in place of the fair
coin; index `0` = `T` carries `1 − θ`).
Source: `repair/harmony.md` HA-15′ ("`X₁(H) = 1/2`, `X₂(H) = θ = 1/4`"); [[decision-problems-v2]]
Proposition 6; mandate T10
Kind: D -/
def mugTheta (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℚ) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (1 - θ) (by linarith) (by linarith)) fun i =>
    .decision () fun act => .leaf (mugWorld1 i act) (mugPay x y (mugWorld1 i act))

/-- The catalogue's `mug1` is `mugTheta` at `θ = 1/2`.
Source: mandate T10
Kind: L -/
theorem mug1_eq_mugTheta (x y : ℚ) : mug1 x y = mugTheta (1/2) (by norm_num) (by norm_num) x y := by
  unfold mug1 mugTheta FinDistr.fair
  congr 1
  ext i
  fin_cases i <;> simp [FinDistr.coin] <;> norm_num

/-- The value of a deterministic policy on `mugTheta`: `(1 − θ)(−x) + θ y` if it pays, else `0`.
Source: [[decision-problems-v2]] Proposition 6; mandate T10
Kind: P -/
theorem value_mugTheta (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℚ) (π : Unit → Act2) :
    value (Proc.ofFun π) (mugTheta θ h0 h1 x y) =
      if π () = .a then (1 - θ) * (-x) + θ * y else 0 := by
  unfold mugTheta
  rw [value_chance', Fin.sum_univ_two]
  simp only [value_decision', Act2.sum_univ, value_leaf', Proc.ofFun_w, FinDistr.coin,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mugWorld1, mugPay]
  cases π () <;> simp <;> ring

/-! ### The two-prior collection -/

/-- Joint outcomes: an action for each prior-self (`a` = pay, `b` = refuse).
Source: mandate T10
Kind: D -/
abbrev MugOut : Type := Fin 2 → Act2

/-- The outcome `(pay, pay)`. Source: mandate T10. Kind: D -/
def pp : MugOut := fun _ => .a

/-- The implemented policy: pay iff both prior-selves say pay.
Source: `repair/harmony.md` HA-15′ ("implemented policy pay iff both say pay"); mandate T10
Kind: D -/
def impl (O : MugOut) : Unit → Act2 := fun _ => if O = pp then .a else .b

/-- `Uᵢ(O)` for the prior-self with `P(H) = θ`: the value of the implemented policy on the
mugging `x = 1`, `y = 2`.
Source: `repair/harmony.md` HA-15′; mandate T10
Kind: D -/
def mugU (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (O : MugOut) : ℚ :=
  value (Proc.ofFun (impl O)) (mugTheta θ h0 h1 1 2)

theorem mugU_pp (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : mugU θ h0 h1 pp = 3 * θ - 1 := by
  unfold mugU
  rw [value_mugTheta]
  simp [impl]
  ring

theorem mugU_other (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {O : MugOut} (h : O ≠ pp) :
    mugU θ h0 h1 O = 0 := by
  unfold mugU
  rw [value_mugTheta]
  simp [impl, h]

/-- The prior-self with `P(H) = θ` as an SC decision-point: world-model the chance profiles of its
own mugging tree under the chance law, utility the payoff of the implemented policy.
Source: `repair/harmony.md` HA-15′; mandate T10
Kind: D -/
noncomputable def mugPoint (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    DecisionPoint (fun _ : Fin 2 => Act2) where
  X := ChanceProfile (mugTheta θ h0 h1 1 2)
  μ := { w := fun e => Rat.cast (chanceLaw (mugTheta θ h0 h1 1 2) e)
         nonneg := fun e => by exact_mod_cast chanceLaw_nonneg _ e
         sum_one := by rw [← Rat.cast_sum, sum_chanceLaw]; simp }
  u O e := Rat.cast (payoff (mugTheta θ h0 h1 1 2) (leafOf (impl O) _ e))

/-- `U (mugPoint θ) O = mugU θ O`: the decision-point's expected utility is the tree value of the
implemented policy (via `sum_chanceLaw_payoff`).
Source: mandate T10 ("derive … via T9(ii) on each tree")
Kind: P -/
theorem U_mugPoint (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (O : MugOut) :
    U (mugPoint θ h0 h1) O = (mugU θ h0 h1 O : ℝ) := by
  unfold U mugPoint mugU
  simp only
  rw [← sum_chanceLaw_payoff (impl O), Rat.cast_sum]
  simp

/-- **The two-prior mugging game**: prior-selves with `P(H) = 1/2` and `P(H) = 1/4`.
Source: `repair/harmony.md` HA-15′; mandate T10
Kind: D -/
noncomputable def mugGame : Game (Fin 2) (fun _ => Act2) :=
  collectionGame ![mugPoint (1/2) (by norm_num) (by norm_num), mugPoint (1/4) (by norm_num) (by norm_num)]

theorem mugGame_u_zero (O : MugOut) :
    mugGame.u O 0 = (mugU (1/2) (by norm_num) (by norm_num) O : ℝ) := by
  show U (mugPoint (1/2) _ _) O = _
  exact U_mugPoint _ _ _ O

theorem mugGame_u_one (O : MugOut) :
    mugGame.u O 1 = (mugU (1/4) (by norm_num) (by norm_num) O : ℝ) := by
  show U (mugPoint (1/4) _ _) O = _
  exact U_mugPoint _ _ _ O

attribute [irreducible] mugGame

/-- **The derived utilities**: `U₁(pay,pay) = 1/2`, `U₂(pay,pay) = −1/4`, all other outcomes `(0,0)`.
Source: `repair/harmony.md` HA-15′; mandate T10
Kind: N+ -/
theorem mugGame_values :
    mugGame.u pp 0 = 1/2 ∧ mugGame.u pp 1 = -1/4 ∧
      ∀ O, O ≠ pp → mugGame.u O 0 = 0 ∧ mugGame.u O 1 = 0 := by
  refine ⟨?_, ?_, fun O h => ⟨?_, ?_⟩⟩
  · rw [mugGame_u_zero, mugU_pp]; norm_num
  · rw [mugGame_u_one, mugU_pp]; norm_num
  · rw [mugGame_u_zero, mugU_other _ _ _ h]; simp
  · rw [mugGame_u_one, mugU_other _ _ _ h]; simp

theorem mugGame_u_one_nonpos (O : MugOut) : mugGame.u O 1 ≤ 0 := by
  by_cases h : O = pp
  · rw [h, mugGame_values.2.1]; norm_num
  · rw [(mugGame_values.2.2 O h).2]

/-- Player 2's `(refuse, ∅)` forces the batna profile, which is not `(pay, pay)`.
Source: `repair/harmony.md` HA-15′
Kind: L -/
theorem outcome_refuse_empty (sel : Finset MugOut → MugOut) (σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i) :
    outcome sel (Function.update σ 1 (.b, ∅)) ≠ pp := by
  have hempty : inter (Function.update σ 1 (.b, ∅)) = ∅ := by
    ext O
    simp only [mem_inter, Finset.notMem_empty, iff_false]
    intro h
    have := h 1
    simp at this
  rw [outcome_of_empty sel (by rw [hempty]; exact Finset.not_nonempty_empty)]
  intro heq
  have := congrFun heq 1
  simp [batna, pp] at this

/-- **The veto**: for every selector, no proposal profile with outcome `(pay, pay)` is a Nash
equilibrium of the two-prior bargaining game — the pessimistic prior-self refuses.
Source: `repair/harmony.md` HA-15′ (the veto); mandate T10 (load-bearing 5)
Kind: P
Fidelity: exact (every `sel`, welfare or not)
Hyps: (a) all -/
theorem veto (sel : Finset MugOut → MugOut) (σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i)
    (h : outcome sel σ = pp) : ¬ BargainNash mugGame sel σ := by
  intro hn
  have hdev := hn 1 (.b, ∅)
  rw [h, mugGame_values.2.1, (mugGame_values.2.2 _ (outcome_refuse_empty sel σ)).2] at hdev
  norm_num at hdev

/-- No pure harmonious profile realises `(pay, pay)`, for every selector.
Source: `repair/harmony.md` HA-15′; mandate T10
Kind: C -/
theorem veto_harmoniousPure (sel : Finset MugOut → MugOut)
    (σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i) (h : HarmoniousPure mugGame sel σ) :
    outcome sel σ ≠ pp := fun hout => veto sel σ hout h.bargainNash

set_option maxRecDepth 8000 in
/-- **The veto, support form**: no pure profile in the support of any harmonious mixed profile
realises `(pay, pay)` (player 2's support proposal would have to be a best response, but
`(refuse, ∅)` guarantees `0` while the support proposal loses `1/4` with positive probability).
Source: `repair/harmony.md` HA-15′; mandate T10 ("the support form via thpe_isMixedNash")
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem veto_support (sel : Finset MugOut → MugOut)
    {p : MixedProfile (bargain mugGame sel).toStrategic} (hp : Harmonious mugGame sel p)
    (τ : (bargain mugGame sel).toStrategic.Profile) (hτ : 0 < profWeight p τ) :
    outcome sel ((bargain mugGame sel).ofStrategicProfile τ) ≠ pp := by
  intro hout
  have hsupp := (profWeight_pos_iff p τ).mp hτ
  have hbr := hp.support_isBestResponse 1 (τ 1) (hsupp 1)
  let s'' : (bargain mugGame sel).toStrategic.strategy 1 := ⟨(.b, ∅), mem_univ _⟩
  have h1 : pureDev p 1 s'' = 0 := by
    unfold pureDev
    refine sum_eq_zero fun τ' _ => ?_
    rw [bargain_payoff, ofStrategicProfile_update,
      (mugGame_values.2.2 _ (outcome_refuse_empty sel _)).2, mul_zero]
  have h2 : pureDev p 1 (τ 1) < 0 := by
    have hle : ∀ τ' : (bargain mugGame sel).toStrategic.Profile,
        profWeight p τ' * (bargain mugGame sel).toStrategic.payoff (Function.update τ' 1 (τ 1)) 1
          ≤ 0 := fun τ' =>
      mul_nonpos_of_nonneg_of_nonpos (profWeight_nonneg _ _)
        (by rw [bargain_payoff]; exact mugGame_u_one_nonpos _)
    have hlt : profWeight p τ *
        (bargain mugGame sel).toStrategic.payoff (Function.update τ 1 (τ 1)) 1 < 0 := by
      rw [Function.update_eq_self, bargain_payoff, hout, mugGame_values.2.1]
      exact mul_neg_of_pos_of_neg hτ (by norm_num)
    unfold pureDev
    have := Finset.sum_lt_sum (s := (univ : Finset (bargain mugGame sel).toStrategic.Profile))
      (f := fun τ' => profWeight p τ' *
        (bargain mugGame sel).toStrategic.payoff (Function.update τ' 1 (τ 1)) 1)
      (g := fun _ => (0 : ℝ)) (fun τ' _ => hle τ') ⟨τ, mem_univ _, hlt⟩
    rw [Finset.sum_const_zero] at this
    exact this
  linarith [hbr s'']

/-! ### The refuted slogan and its surviving neighbour -/

/-- The utilitarian welfare `w₁U₁ + w₂U₂`, `w₂ = 1 − w₁`.
Source: `repair/harmony.md` HA-15′ ("the utilitarian `W = w₁U₁ + w₂U₂`"); mandate T10
Kind: D -/
def mugW (w : ℚ) (O : MugOut) : ℚ :=
  w * mugU (1/2) (by norm_num) (by norm_num) O + (1 - w) * mugU (1/4) (by norm_num) (by norm_num) O

/-- For `w₁ > 1/3` the utilitarian welfare strictly prefers the pay deal to every other outcome.
Source: `repair/harmony.md` HA-15′ ("pay iff `w₁ > 1/3`"); mandate T10
Kind: P -/
theorem mugW_argmax (w : ℚ) (hw : 1/3 < w) (O : MugOut) (hO : O ≠ pp) : mugW w O < mugW w pp := by
  unfold mugW
  rw [mugU_other _ _ _ hO, mugU_other _ _ _ hO, mugU_pp, mugU_pp]
  norm_num
  linarith

/-- The utilitarian welfare with positive weights is Pareto-consistent for the two-prior game.
Source: mandate T10 (the reading of the slogan)
Kind: P -/
theorem mugW_paretoConsistent (w : ℚ) (h0 : 0 < w) (h1 : w < 1) :
    ParetoConsistent mugGame fun O => (mugW w O : ℝ) := by
  intro O O' h
  rw [paretoDom_iff] at h
  obtain ⟨hle, hex⟩ := h
  have h0' := hle 0
  have h1' := hle 1
  rw [mugGame_u_zero, mugGame_u_zero, Rat.cast_le] at h0'
  rw [mugGame_u_one, mugGame_u_one, Rat.cast_le] at h1'
  rw [Fin.exists_fin_two, mugGame_u_zero, mugGame_u_zero, mugGame_u_one, mugGame_u_one,
    Rat.cast_lt, Rat.cast_lt] at hex
  unfold mugW
  rw [Rat.cast_lt]
  have hw' : (0 : ℚ) ≤ 1 - w := by linarith
  have e0 := mul_le_mul_of_nonneg_left h0' h0.le
  have e1 := mul_le_mul_of_nonneg_left h1' hw'
  rcases hex with hex | hex
  · have := mul_lt_mul_of_pos_left hex h0
    linarith
  · have := mul_lt_mul_of_pos_left hex (by linarith : (0 : ℚ) < 1 - w)
    linarith

/-- **The surviving neighbour**: the utilitarian welfare is the value under the *mixture prior*
`P(H) = w₁ · 1/2 + w₂ · 1/4` — a linearity identity about an imposed aggregator that is not a
player (T12(i) instantiated).
Source: `repair/harmony.md` HA-15′ ("what survives is a linearity identity"); mandate T10
Kind: P -/
theorem mugW_eq_mixture (w : ℚ) (h0 : 0 ≤ w) (h1 : w ≤ 1) (O : MugOut) :
    mugW w O = mugU (w * (1/2) + (1 - w) * (1/4)) (by nlinarith) (by nlinarith) O := by
  unfold mugW
  by_cases h : O = pp
  · subst h; rw [mugU_pp, mugU_pp, mugU_pp]; ring
  · rw [mugU_other _ _ _ h, mugU_other _ _ _ h, mugU_other _ _ _ h]; ring

/-- **Refuted slogan**: "utilitarian bargaining between prior-selves = UDT under the mixture
prior". Quoted (HA-15′, KILLED headline): "for `w₁ ∈ {1/2, 3/4, 9/10, 99/100}` the utilitarian
`W = w₁U₁ + w₂U₂` prefers the pay deal … and every uniform-THPE outcome implements refuse".
Reading: for every `w₁ ∈ (1/3, 1)` the Pareto-consistent welfare `W` strictly prefers `(pay, pay)`,
yet no harmonious profile of the bargaining game realises it (the veto). Surviving neighbour:
`mugW_eq_mixture`.
Source: `repair/harmony.md` HA-15′; mandate T10 (rule 3 row)
Kind: N+ (refutation)
Fidelity: exact
Hyps: (a) all -/
theorem slogan_refuted (w : ℚ) (hw : 1/3 < w) (hw1 : w < 1) :
    ParetoConsistent mugGame (fun O => (mugW w O : ℝ)) ∧
      (∀ O, O ≠ pp → mugW w O < mugW w pp) ∧
      ∀ (sel : Finset MugOut → MugOut) (σ : ∀ i : Fin 2, Proposal (fun _ => Act2) i),
        HarmoniousPure mugGame sel σ → outcome sel σ ≠ pp :=
  ⟨mugW_paretoConsistent w (by linarith) hw1, fun O hO => mugW_argmax w hw O hO,
    fun sel σ h => veto_harmoniousPure sel σ h⟩

end Cleanroom.Udt.UdtHarmonyBargain
