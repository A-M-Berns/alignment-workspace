import Cleanroom.Decision.DpDutchBook.BetExt
import Cleanroom.Decision.DpDutchBook.Newcomb

/-!
# T2: who buys — the sophisticated bettor declines, buys iff `Δ > 2δ` with the reverse bet
offered regardless, the myopic bettor prices `E[r] − 2δ + Δ`

All values are `dp-calibration`'s `condExp` on the extended tree, derived through `nu_ext` /
`paySum_ext` from the master identity — nothing is asserted. The bet point's observation is the
lifted `O_d` (`betObs`), its action events are `buyEv`/`declineEv`; the standing hypothesis
`Covered C B q₀ O` says every positive `O`-run passes the real node `q₀` (P12's "the `d`-node
met on `O_d`-runs" — on a nested tree this fails for every single node, see findings).

* `belowMass`/`belowPay` — `M := μ(below q₀ ∧ O)` and its payoff mass `P`; `belowMassA`/
  `belowPayA` — the same on the runs taking edge `a` at `q₀`. Under `Covered`, node-action
  veridicality at `q₀` and disjoint action events these are `ν(O)`, `paySum O`,
  `ν(a ∧ O)`, `paySum (a ∧ O)` on the base tree (`belowMass_eq_nu` …), so
  **`Δ = P_{s_d}(a)·|c − e(a)|`** is P12's `Δ` at the strictly calibrated state
  (`bookGapExt_eq`).
* `sophisticated_declines` (T2(a), **C**): with the true continuation (sell), the calibrated
  values at `d_B` are `V(buy) = P/M − δ`, `V(decline) = P/M`: any self-model putting weight on
  buying is not `T_EDT`-approved at `d_B` (`sophisticated_not_approved`).
* `regardless_buy_sub_decline` (T2(b), **C**): with the reverse bet offered regardless,
  `V(buy) − V(decline) = Δ − 2δ`, so the sophisticated bettor buys iff `Δ > 2δ`
  (`regardless_buys_iff`), and the pair still loses `δ` leaf-wise (`betPayR_book_sub_dec`).
* `myopic_buy_sub_decline` (T2(c), **P**): the myopic bettor (side law keep) prices
  `V(buy) = P/M − 2δ + Δ` against `V(decline) = P/M`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- The lifted observation of the bet point: the base world satisfies `O`.
Source: P12.md line 7 (`d_B = (s_{d_B}, O_d, {buy, decline})`)
Kind: D -/
def betObs (O : Finset Ω) : Finset (BetW Ω) := Finset.univ.filter fun w => w.1 ∈ O

/-- The action event "bought" at the bet point. Source: P12.md line 7. Kind: D -/
def buyEv : Finset (BetW Ω) := Finset.univ.filter fun w => w.2.1 = true

/-- The action event "declined" at the bet point. Source: P12.md line 7. Kind: D -/
def declineEv : Finset (BetW Ω) := Finset.univ.filter fun w => w.2.1 = false

/-- The bet point's action events as a function of `Bool`. Source: none: infrastructure. Kind: D -/
def betEv : Bool → Finset (BetW Ω)
  | true => buyEv
  | false => declineEv

section masses

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (q₀ : B.DecNode) (O : Finset Ω)

/-- `M := μ{ℓ below q₀, λ(ℓ) ⊨ O}`. Source: none: infrastructure. Kind: D -/
def belowMass : K :=
  ∑ ℓ, if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0

/-- `P := ∑_{ℓ below q₀, λ(ℓ) ⊨ O} μ(ℓ) r(ℓ)`. Source: none: infrastructure. Kind: D -/
def belowPay : K :=
  ∑ ℓ, if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0

/-- `M_a := μ{ℓ taking edge a at q₀, λ(ℓ) ⊨ O}`. Source: none: infrastructure. Kind: D -/
def belowMassA (a : acts (pt B q₀)) : K :=
  ∑ ℓ, if edgeOf B q₀ ℓ = some a ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0

/-- `P_a := ∑_{ℓ taking edge a at q₀, λ(ℓ) ⊨ O} μ(ℓ) r(ℓ)`. Source: none: infrastructure. Kind: D -/
def belowPayA (a : acts (pt B q₀)) : K :=
  ∑ ℓ, if edgeOf B q₀ ℓ = some a ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0

/-- **P12's standing assumption made explicit**: every positive `O`-run passes the real node
`q₀` ("the `d`-node met on `O_d`-runs").
Source: P12.md line 7 ("inserted immediately above the `d`-node met on `O_d`-runs")
Kind: D -/
def Covered : Prop := ∀ ℓ, 0 < leafLaw C B ℓ → world B ℓ ∈ O → (edgeOf B q₀ ℓ).isSome

/-- **The book gap on the extension**: `Δ := (M_a / M) · |c − P_a / M_a|` — the bet-point state's
probability of the booked act times the gap between the supposed value `c` and the conditional
value of the act below `q₀`.
Source: P12.md line 7 (`Δ := P_{s_d}(a) |c − e|`)
Kind: D -/
noncomputable def bookGapExt (a : acts (pt B q₀)) (ca : K) : K :=
  belowMassA C B q₀ O a / belowMass C B q₀ O * |ca - belowPayA C B q₀ O a / belowMassA C B q₀ O a|

/-! ### The bridge to the base tree's calibrated state -/

/-- Under `Covered`, `M = ν_C(O)`. Source: none: infrastructure. Kind: L -/
theorem belowMass_eq_nu (hcov : Covered C B q₀ O) : belowMass C B q₀ O = nu C B O := by
  unfold belowMass
  rw [nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hO : world B ℓ ∈ O
  · rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
    · simp [hO, hcov ℓ hpos hO]
    · simp [← hz]
  · simp [hO]

/-- Under `Covered`, `P = paySum_C(O)`. Source: none: infrastructure. Kind: L -/
theorem belowPay_eq_paySum (hcov : Covered C B q₀ O) : belowPay C B q₀ O = paySum C B O := by
  unfold belowPay
  rw [paySum_eq_sum_ite]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hO : world B ℓ ∈ O
  · rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
    · simp [hO, hcov ℓ hpos hO]
    · simp [← hz]
  · simp [hO]

variable (actEv : (d : ι) → acts d → Finset Ω)

/-- Under `Covered`, node-action veridicality at `q₀` and disjoint action events,
`M_a = ν_C(a ∧ O)`. Source: none: infrastructure. Kind: L -/
theorem belowMassA_eq_nu (hcov : Covered C B q₀ O) (hnav : NodeActionVeridical actEv B q₀)
    (hdisj : DisjointActEv actEv (pt B q₀)) (a : acts (pt B q₀)) :
    belowMassA C B q₀ O a = nu C B (actEv (pt B q₀) a ∩ O) := by
  unfold belowMassA
  rw [nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_inter]
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
  · by_cases hO : world B ℓ ∈ O
    · have hsome := hcov ℓ hpos hO
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      have hwb : world B ℓ ∈ actEv (pt B q₀) b := hnav ℓ b hb
      by_cases hab : b = a
      · subst hab; simp [hb, hO, hwb]
      · have : world B ℓ ∉ actEv (pt B q₀) a := fun hc =>
          Finset.disjoint_left.mp (hdisj a b (Ne.symm hab)) hc hwb
        simp [hb, hab, this]
    · simp [hO]
  · simp [← hz]

/-- Under the same hypotheses, `P_a = paySum_C(a ∧ O)`. Source: none: infrastructure. Kind: L -/
theorem belowPayA_eq_paySum (hcov : Covered C B q₀ O) (hnav : NodeActionVeridical actEv B q₀)
    (hdisj : DisjointActEv actEv (pt B q₀)) (a : acts (pt B q₀)) :
    belowPayA C B q₀ O a = paySum C B (actEv (pt B q₀) a ∩ O) := by
  unfold belowPayA
  rw [paySum_eq_sum_ite]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Finset.mem_inter]
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
  · by_cases hO : world B ℓ ∈ O
    · have hsome := hcov ℓ hpos hO
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
      have hwb : world B ℓ ∈ actEv (pt B q₀) b := hnav ℓ b hb
      by_cases hab : b = a
      · subst hab; simp [hb, hO, hwb]
      · have : world B ℓ ∉ actEv (pt B q₀) a := fun hc =>
          Finset.disjoint_left.mp (hdisj a b (Ne.symm hab)) hc hwb
        simp [hb, hab, this]
    · simp [hO]
  · simp [← hz]

/-- **`Δ` is P12's `Δ` at the strictly calibrated state of the base point**: under `Covered`,
node-action veridicality and disjoint action events, `bookGapExt = P_{s_d}(a) · |c − V_{s_d}(a)|`
with `s_d = calibratedState C B O` (whose `P(a) = ν(a ∧ O)/ν(O)` and `V(a) = 𝔼[r ∣ a ∧ O]`).
Source: P12.md line 7 (`Δ := P_{s_d}(a)|c − e|`, `e := V_{s_d}(a)`); mandate T2 ("`Δ` must come
out of `calibratedState_V`")
Kind: L
Fidelity: exact
Hyps: (a) `Covered`, node-action veridicality at `q₀`, disjoint action events, `0 < ν(O)` -/
theorem bookGapExt_eq (hcov : Covered C B q₀ O) (hnav : NodeActionVeridical actEv B q₀)
    (hdisj : DisjointActEv actEv (pt B q₀)) (hO : 0 < nu C B O) (a : acts (pt B q₀)) (ca : K) :
    bookGapExt C B q₀ O a ca =
      (calibratedState C B O hO).pr (actEv (pt B q₀) a) *
        |ca - (calibratedState C B O hO).V (actEv (pt B q₀) a)| := by
  unfold bookGapExt
  rw [belowMassA_eq_nu C B q₀ O actEv hcov hnav hdisj, belowPayA_eq_paySum C B q₀ O actEv hcov hnav hdisj,
    belowMass_eq_nu C B q₀ O hcov, calibratedState_pr, calibratedState_V]

end masses

/-! ### Values at the bet point -/

section values

variable (δ ca s : K) (π : (e : ι) → acts e) (C : Proc ι acts K) (B : Tree Ω ι acts K)
  (q₀ : B.DecNode) (O : Finset Ω) (bet : FinDistr K Bool)

/-- Membership in the buy event within the lifted observation. Source: none: infrastructure.
Kind: L -/
theorem mem_buyEv_betObs (w : BetW Ω) : w ∈ buyEv ∩ betObs O ↔ w.2.1 = true ∧ w.1 ∈ O := by
  simp [buyEv, betObs]

/-- Membership in the decline event within the lifted observation. Source: none: infrastructure.
Kind: L -/
theorem mem_declineEv_betObs (w : BetW Ω) :
    w ∈ declineEv ∩ betObs O ↔ w.2.1 = false ∧ w.1 ∈ O := by
  simp [declineEv, betObs]

/-- `ν(buy ∧ O) = bet(buy) · M` on either extension (the side plays no role).
Source: P12-3 (the sophisticated state's law); mandate T2
Kind: L -/
theorem nu_buy (pay : Bool → Bool → Side → K → K) (σ₀ : Side) :
    nu (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) (buyEv ∩ betObs O) =
      bet.w true * belowMass C B q₀ O := by
  rw [nu_ext, belowMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases edgeOf B q₀ ℓ with
  | none => simp [buyEv, betObs]
  | some x =>
      simp only [Fintype.sum_bool, Option.isSome_some, true_and]
      by_cases hO : world B ℓ ∈ O <;> simp [buyEv, betObs, hO, mul_comm]

/-- `ν(decline ∧ O) = bet(decline) · M` under `Covered`.
Source: mandate T2
Kind: L
Hyps: (a) `Covered` -/
theorem nu_decline (pay : Bool → Bool → Side → K → K) (σ₀ : Side) (hcov : Covered C B q₀ O) :
    nu (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) (declineEv ∩ betObs O) =
      bet.w false * belowMass C B q₀ O := by
  rw [nu_ext, belowMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases h : edgeOf B q₀ ℓ with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_and, if_false, mul_zero]
      by_cases hO : world B ℓ ∈ O
      · rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
        · exact absurd (hcov ℓ hpos hO) (by rw [h]; exact Bool.false_ne_true)
        · simp [← hz]
      · simp [declineEv, betObs, hO]
  | some x =>
      simp only [Fintype.sum_bool, Option.isSome_some, true_and]
      by_cases hO : world B ℓ ∈ O <;> simp [declineEv, betObs, hO, mul_comm]

/-- The per-leaf weight of `paySum` on an extension, in closed form (the common core of the four
`paySum` identities below).
Source: none: infrastructure. Kind: L -/
theorem paySum_ext_leaf (pay : Bool → Bool → Side → K → K)
    (hpay : ∀ isA r, pay false isA .keep r = r) (X : Finset (BetW Ω)) (σ₀ : Side) :
    paySum (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) X =
      ∑ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, σ₀) ∈ X
            then pay bt (decide (x = π (pt B q₀))) σ₀ (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, .keep) ∈ X then payoff B ℓ else 0) :=
  paySum_ext π C B q₀ σ₀ bet pay hpay X

/-- `paySum(buy ∧ O)` on `attachBet` with the true continuation (sell): `bet(buy) · (P − δM)`.
Source: P12-3 ("buy (`−δ` surely)"); mandate T2(a)
Kind: L -/
theorem paySum_buy_sell :
    paySum (liftProc C .sell bet) (attachBet δ ca s π B q₀) (buyEv ∩ betObs O) =
      bet.w true * (belowPay C B q₀ O - δ * belowMass C B q₀ O) := by
  unfold attachBet
  rw [paySum_ext_leaf π C B q₀ bet _ (fun isA r => betPay_false δ ca s isA .keep r)]
  have key : ∀ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, Side.sell) ∈ buyEv ∩ betObs O
            then betPay δ ca s bt (decide (x = π (pt B q₀))) Side.sell (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, Side.keep) ∈ buyEv ∩ betObs O then payoff B ℓ else 0) =
      bet.w true * ((if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0)
        - δ * (if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)) := by
    intro ℓ
    cases edgeOf B q₀ ℓ with
    | none => simp [buyEv, betObs]
    | some x =>
        simp only [Fintype.sum_bool, Option.isSome_some, true_and, betPay]
        by_cases hO : world B ℓ ∈ O <;> simp [buyEv, betObs, hO] <;> ring
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  unfold belowPay belowMass
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

/-- `paySum(decline ∧ O)` on `attachBet` under `Covered`, either side: `bet(decline) · P` (the
side is payoff-irrelevant when the bet is declined).
Source: mandate T2
Kind: L
Hyps: (a) `Covered` -/
theorem paySum_decline (σ₀ : Side) (hcov : Covered C B q₀ O) :
    paySum (liftProc C σ₀ bet) (attachBet δ ca s π B q₀) (declineEv ∩ betObs O) =
      bet.w false * belowPay C B q₀ O := by
  unfold attachBet
  rw [paySum_ext_leaf π C B q₀ bet _ (fun isA r => betPay_false δ ca s isA .keep r), belowPay,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases h : edgeOf B q₀ ℓ with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_and, if_false, mul_zero]
      by_cases hO : world B ℓ ∈ O
      · rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
        · exact absurd (hcov ℓ hpos hO) (by rw [h]; exact Bool.false_ne_true)
        · simp [← hz]
      · simp [declineEv, betObs, hO]
  | some x =>
      simp only [Fintype.sum_bool, Option.isSome_some, true_and, betPay]
      by_cases hO : world B ℓ ∈ O <;> simp [declineEv, betObs, hO] <;> ring

/-- `paySum(buy ∧ O)` on `attachBet` with the myopic continuation (keep):
`bet(buy) · (P − 2δM + s·(ca·M_a − P_a))`, `a := π (pt B q₀)`.
Source: P12-4(i) ("`𝔼[r] − 2δ + Δ` for a myopic state"); mandate T2(c)
Kind: L -/
theorem paySum_buy_keep :
    paySum (liftProc C .keep bet) (attachBet δ ca s π B q₀) (buyEv ∩ betObs O) =
      bet.w true * (belowPay C B q₀ O - 2 * δ * belowMass C B q₀ O +
        s * (ca * belowMassA C B q₀ O (π (pt B q₀)) - belowPayA C B q₀ O (π (pt B q₀)))) := by
  unfold attachBet
  rw [paySum_ext_leaf π C B q₀ bet _ (fun isA r => betPay_false δ ca s isA .keep r)]
  have key : ∀ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, Side.keep) ∈ buyEv ∩ betObs O
            then betPay δ ca s bt (decide (x = π (pt B q₀))) Side.keep (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, Side.keep) ∈ buyEv ∩ betObs O then payoff B ℓ else 0) =
      bet.w true * ((if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0)
        - 2 * δ * (if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)
        + s * (ca * (if edgeOf B q₀ ℓ = some (π (pt B q₀)) ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)
          - (if edgeOf B q₀ ℓ = some (π (pt B q₀)) ∧ world B ℓ ∈ O
              then leafLaw C B ℓ * payoff B ℓ else 0))) := by
    intro ℓ
    cases edgeOf B q₀ ℓ with
    | none => simp [buyEv, betObs]
    | some x =>
        simp only [Fintype.sum_bool, Option.isSome_some, true_and, betPay, Option.some.injEq]
        by_cases hO : world B ℓ ∈ O
        · by_cases hx : x = π (pt B q₀)
          · subst hx; simp [buyEv, betObs, hO]; ring
          · simp [buyEv, betObs, hO, hx]; ring
        · simp [buyEv, betObs, hO]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  unfold belowPay belowMass belowMassA belowPayA
  simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- `paySum(decline ∧ O)` on `attachBetRegardless` with the reverse bet taken (sell), under
`Covered`: `bet(decline) · (P + δM − s·(ca·M_a − P_a))`.
Source: P12-3 ("decline (`δ − Δ` in evidential expectation)"); mandate T2(b)
Kind: L
Hyps: (a) `Covered` -/
theorem paySumR_decline_sell (hcov : Covered C B q₀ O) :
    paySum (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (declineEv ∩ betObs O) =
      bet.w false * (belowPay C B q₀ O + δ * belowMass C B q₀ O -
        s * (ca * belowMassA C B q₀ O (π (pt B q₀)) - belowPayA C B q₀ O (π (pt B q₀)))) := by
  unfold attachBetRegardless
  rw [paySum_ext_leaf π C B q₀ bet _ (fun isA r => betPayR_false_keep δ ca s isA r)]
  have key : ∀ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, Side.sell) ∈ declineEv ∩ betObs O
            then betPayR δ ca s bt (decide (x = π (pt B q₀))) Side.sell (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, Side.keep) ∈ declineEv ∩ betObs O then payoff B ℓ else 0) =
      bet.w false * ((if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0)
        + δ * (if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)
        - s * (ca * (if edgeOf B q₀ ℓ = some (π (pt B q₀)) ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)
          - (if edgeOf B q₀ ℓ = some (π (pt B q₀)) ∧ world B ℓ ∈ O
              then leafLaw C B ℓ * payoff B ℓ else 0))) := by
    intro ℓ
    cases h : edgeOf B q₀ ℓ with
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, false_and, if_false, mul_zero,
          reduceCtorEq, zero_add, sub_zero]
        by_cases hO : world B ℓ ∈ O
        · rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hz
          · exact absurd (hcov ℓ hpos hO) (by rw [h]; exact Bool.false_ne_true)
          · simp [← hz]
        · simp [declineEv, betObs, hO]
    | some x =>
        simp only [Fintype.sum_bool, Option.isSome_some, true_and, betPayR, Option.some.injEq]
        by_cases hO : world B ℓ ∈ O
        · by_cases hx : x = π (pt B q₀)
          · subst hx; simp [declineEv, betObs, hO]; ring
          · simp [declineEv, betObs, hO, hx]; ring
        · simp [declineEv, betObs, hO]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  unfold belowPay belowMass belowMassA belowPayA
  simp only [mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- `paySum(buy ∧ O)` on `attachBetRegardless` with the reverse bet taken: `bet(buy) · (P − δM)`
(the two legs cancel).
Source: P12-3 ("`B` and `R` settle jointly to `0`"); mandate T2(b)
Kind: L -/
theorem paySumR_buy_sell :
    paySum (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (buyEv ∩ betObs O) =
      bet.w true * (belowPay C B q₀ O - δ * belowMass C B q₀ O) := by
  unfold attachBetRegardless
  rw [paySum_ext_leaf π C B q₀ bet _ (fun isA r => betPayR_false_keep δ ca s isA r)]
  have key : ∀ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, Side.sell) ∈ buyEv ∩ betObs O
            then betPayR δ ca s bt (decide (x = π (pt B q₀))) Side.sell (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, Side.keep) ∈ buyEv ∩ betObs O then payoff B ℓ else 0) =
      bet.w true * ((if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ * payoff B ℓ else 0)
        - δ * (if (edgeOf B q₀ ℓ).isSome ∧ world B ℓ ∈ O then leafLaw C B ℓ else 0)) := by
    intro ℓ
    cases edgeOf B q₀ ℓ with
    | none => simp [buyEv, betObs]
    | some x =>
        simp only [Fintype.sum_bool, Option.isSome_some, true_and, betPayR]
        by_cases hO : world B ℓ ∈ O
        · cases decide (x = π (pt B q₀)) <;> simp [buyEv, betObs, hO] <;> ring
        · simp [buyEv, betObs, hO]
  rw [Finset.sum_congr rfl fun ℓ _ => key ℓ]
  unfold belowPay belowMass
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

end values

/-! ### The headlines -/

section headlines

variable (δ ca s : K) (π : (e : ι) → acts e) (C : Proc ι acts K) (B : Tree Ω ι acts K)
  (q₀ : B.DecNode) (O : Finset Ω) (bet : FinDistr K Bool)

/-- **T2(a), the sophisticated bettor declines**: under the true continuation (sell) the
calibrated values at `d_B` are `V(buy) = P/M − δ` and `V(decline) = P/M` — for every self-model
`bet` with both bets positive (the comparison needs both events realized).
Source: P12-3 ("the literal offer … nets `−δ` surely against `0`: the agent declines"); C2-16;
mandate T2(a)
Kind: C
Fidelity: exact (values as `condExp` on the extension, derived from the master identity)
Hyps: (a) `Covered`, `0 < M`, both bets positive -/
theorem sophisticated_values (hcov : Covered C B q₀ O) (hM : 0 < belowMass C B q₀ O)
    (hb : 0 < bet.w true) (hd : 0 < bet.w false) :
    condExp (liftProc C .sell bet) (attachBet δ ca s π B q₀) (buyEv ∩ betObs O) =
        belowPay C B q₀ O / belowMass C B q₀ O - δ ∧
      condExp (liftProc C .sell bet) (attachBet δ ca s π B q₀) (declineEv ∩ betObs O) =
        belowPay C B q₀ O / belowMass C B q₀ O := by
  unfold condExp attachBet
  rw [nu_buy, nu_decline π C B q₀ O bet _ _ hcov]
  constructor
  · have := paySum_buy_sell δ ca s π C B q₀ O bet
    unfold attachBet at this
    rw [this]
    field_simp
  · have := paySum_decline δ ca s π C B q₀ O bet .sell hcov
    unfold attachBet at this
    rw [this]
    field_simp

/-- **T2(a) as a verdict**: for `δ > 0` the sophisticated bettor strictly prefers to decline, so
no self-model putting weight on buying is approved at `d_B`.
Source: P12-3; S12 ("no calibrated … procedure buys the book as written"); mandate T2(a)
Kind: C
Hyps: (a) as `sophisticated_values`, `0 < δ` -/
theorem sophisticated_not_approved (hcov : Covered C B q₀ O) (hM : 0 < belowMass C B q₀ O)
    (hb : 0 < bet.w true) (hd : 0 < bet.w false) (hδ : 0 < δ) :
    ¬ ApprovedBy bet (fun bt => condExp (liftProc C .sell bet) (attachBet δ ca s π B q₀)
      (betEv bt ∩ betObs O)) := by
  obtain ⟨h1, h2⟩ := sophisticated_values δ ca s π C B q₀ O bet hcov hM hb hd
  intro h
  have := h true hb false
  simp only [betEv] at this
  rw [h1, h2] at this
  linarith

/-- **T2(b), the reverse bet offered regardless**: `V(buy) − V(decline) = Δ − 2δ`, where
`Δ = bookGapExt` and `s` is the sign of `c − e(a)` (as `s·(c − e(a)) = |c − e(a)|`).
Source: P12-3 ("buys iff `Δ > 2δ` — the myopic threshold"); P09-3′; mandate T2(b)
Kind: C
Fidelity: exact
Hyps: (a) `Covered`, `0 < M`, `0 < M_a`, both bets positive, `s` the sign of the gap -/
theorem regardless_buy_sub_decline (hcov : Covered C B q₀ O) (hM : 0 < belowMass C B q₀ O)
    (hMa : 0 < belowMassA C B q₀ O (π (pt B q₀))) (hb : 0 < bet.w true) (hd : 0 < bet.w false)
    (hs : s * (ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))) =
      |ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))|) :
    condExp (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (buyEv ∩ betObs O) -
      condExp (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (declineEv ∩ betObs O) =
      bookGapExt C B q₀ O (π (pt B q₀)) ca - 2 * δ := by
  unfold condExp attachBetRegardless
  rw [nu_buy, nu_decline π C B q₀ O bet _ _ hcov]
  have h1 := paySumR_buy_sell δ ca s π C B q₀ O bet
  have h2 := paySumR_decline_sell δ ca s π C B q₀ O bet hcov
  unfold attachBetRegardless at h1 h2
  rw [h1, h2]
  unfold bookGapExt
  rw [← hs]
  field_simp
  ring

/-- **T2(b) as a verdict**: with the reverse bet offered regardless, the sophisticated bettor
buys (strictly prefers buy) iff `Δ > 2δ`.
Source: P12-3; mandate T2(b)
Kind: C
Hyps: (a) as `regardless_buy_sub_decline` -/
theorem regardless_buys_iff (hcov : Covered C B q₀ O) (hM : 0 < belowMass C B q₀ O)
    (hMa : 0 < belowMassA C B q₀ O (π (pt B q₀))) (hb : 0 < bet.w true) (hd : 0 < bet.w false)
    (hs : s * (ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))) =
      |ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))|) :
    condExp (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (declineEv ∩ betObs O) <
      condExp (liftProc C .sell bet) (attachBetRegardless δ ca s π B q₀) (buyEv ∩ betObs O) ↔
      2 * δ < bookGapExt C B q₀ O (π (pt B q₀)) ca := by
  have := regardless_buy_sub_decline δ ca s π C B q₀ O bet hcov hM hMa hb hd hs
  constructor <;> intro h <;> linarith

/-- **T2(c), the myopic bettor**: with the side law keep, `V(buy) − V(decline) = Δ − 2δ` — the
post's Step-1 number `𝔼[r] − 2δ + Δ` against `𝔼[r]`.
Source: P12-4(i) ("`𝔼[r] − 2δ + Δ` for a myopic state (the post's Step-1 number)"); mandate T2(c)
Kind: P
Fidelity: exact
Hyps: (a) as `regardless_buy_sub_decline` -/
theorem myopic_buy_sub_decline (hcov : Covered C B q₀ O) (hM : 0 < belowMass C B q₀ O)
    (hMa : 0 < belowMassA C B q₀ O (π (pt B q₀))) (hb : 0 < bet.w true) (hd : 0 < bet.w false)
    (hs : s * (ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))) =
      |ca - belowPayA C B q₀ O (π (pt B q₀)) / belowMassA C B q₀ O (π (pt B q₀))|) :
    condExp (liftProc C .keep bet) (attachBet δ ca s π B q₀) (buyEv ∩ betObs O) -
      condExp (liftProc C .keep bet) (attachBet δ ca s π B q₀) (declineEv ∩ betObs O) =
      bookGapExt C B q₀ O (π (pt B q₀)) ca - 2 * δ := by
  unfold condExp attachBet
  rw [nu_buy, nu_decline π C B q₀ O bet _ _ hcov]
  have h1 := paySum_buy_keep δ ca s π C B q₀ O bet
  have h2 := paySum_decline δ ca s π C B q₀ O bet .keep hcov
  unfold attachBet at h1 h2
  rw [h1, h2]
  unfold bookGapExt
  rw [← hs]
  field_simp
  ring

end headlines

end Cleanroom.Decision.DpDutchBook
