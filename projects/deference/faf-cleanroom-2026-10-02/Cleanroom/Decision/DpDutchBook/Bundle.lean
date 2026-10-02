import Cleanroom.Decision.DpDutchBook.NewcombSeed

/-!
# T1(c), T5(b)–(d): P09's bundled book on Death in Damascus — the label shift `½ ↦ 21/40`

**The tree** (`didBundle U k K k' bundleOn offer`, P09.md Setting, the 2019 ordering): Death's
location is a *hypothetical-node* prediction — a simulation query of the act point `d₁`
(answer `x`, Death at the city of `base(x)`); then the live act `a = (base, bundled)` at `d₁`
(`S = (.a, false)`, `Sb = (.a, true)`, `R = (.b, false)`, `Rb = (.b, true)`; the bundled side
bet costs `k` and pays `K` on survival, honoured on the bases in `bundleOn`); then the post-act
point `d₂` whose side coordinate is *sell* (take the reverse bet `+k'`, `−K` on survival, offered
"regardless" on the bases in `offer`); payoff `U` on survival. Both points carry the same action
type (`d₂` reads only the side coordinate — a disclosed convention, as `attachBet`'s). P09-2′ is
`bundleOn = offer = all`; P09-6′ (`A₁ = {S, R, Rb}`, the reverse bet on R-branches) is
`bundleOn = offer = {R}`, with `Sb` then a payoff-irrelevant duplicate of `S`. `q := P(base = S)`
of the `d₁` label, `s := P(sell)` of the `d₂` label.

* **Definition 6** (`bundleE_eq`): Death is an independent sample of the label, so the strict
  act value is `bundleVal q s a = U·sv + [bundled](−k + K·sv) + s·[offered](k' − K·sv)` with
  survival `sv = 1 − q` for `S`-based acts and `q` for `R`-based — which is also the
  marginal-holding classical cf's value (`c`-data in P09; here the same formula).
* **6′** (`bundle_leafLaw'`, `bundleE'_eq`): the seed makes Death's prediction the live act, so
  nobody survives: `bundleVal' s a = −k·[bundled] + s·k'·[offered]`.
* **P09-2′(a)** (`bundle_booked_*`): at the booked label `(0, ½, 0, ½)` with sell forced, the
  6′ values of the supported acts tie at `−k + k'` (strict-grade `T_EDT` **approves** the booked
  label), while at every full-support self-model `S` is worth `k' > −k + k'` (the masked grade
  declines the bet); the classical cf's values `(4, 9/2, 4, 9/2)` at `(10, 1, 3, ½)`
  (`bundleVal` at `q = ½`, `s = 1`) approve the booked label; the book pays `k' − k` on every
  leaf against declining both (`bundle_leafwise`), `V'(book) = −k + k'` (`−½`) against `0`
  (decline both) and `k'` (decline the bet, take the reverse one).
* **P09-6′** (`bundle_tie_iff`, `bundle_tie_2140`, `bundle_2140_*`): the `S ∼ Rb` tie is
  `q(2U + K − sK) = U + k − sk'`: with sell forced `q* = 21/40` at `(10, 1, 3, ½)`, values
  `(19/4, 167/40, 19/4)`, `Rb − R = 23/40`, the label `(21/40, 0, 0, 19/40)` approved; Definition
  17's uniform label `½` is not at a tie; strict `T_EDT` under 6′ refuses it (`V'(S) = 0 >
  −½ = V'(Rb)`); `V'(book) = −19/80 = P(Rb)(k' − k)`; under Definition 6 with keep the tie is
  `q(2U + K) = U + k`, `11/23`, and no label makes both legs favourable when `k' ≤ k`
  (`bundle_no_pair_def6`).
* **F10** (`bundle_cf_sub_e'`): the discrepancy `c(Rb) − e'(Rb) = U·q = U(1 − P(Rb))` is tied to
  the label on this tree.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Doubled acts `(base, bundled)`: base `.a` = stay (S), `.b` = run (R); the flag takes the
bundled side bet. Source: P09.md Setting ("bet bundled with the act"). Kind: D -/
abbrev BAct : Type := Act2 × Bool

/-- Worlds `(death, act, sell)`. Source: P09.md Setting. Kind: D -/
abbrev BW : Type := Act2 × BAct × Bool

/-- **The bundled-book payoff**: `U` on survival (`base ≠ death`), the bundled side bet
`−k + K·[survive]` when the act is bundled on a base in `bundleOn`, the reverse bet
`k' − K·[survive]` when sold on a base in `offer`.
Source: P09.md Setting ("side bet costs `k`, pays `K` on survival; reverse bet pays `k'` for
`−K` on survival"); P09-1. Kind: D -/
def bundlePay (U k K k' : ℚ) (bundleOn offer : Act2 → Bool) (death : Act2) (a : BAct)
    (sell : Bool) : ℚ :=
  (if a.1 ≠ death then U else 0) +
    (if a.2 = true ∧ bundleOn a.1 = true then -k + (if a.1 ≠ death then K else 0) else 0) +
    (if sell = true ∧ offer a.1 = true then k' - (if a.1 ≠ death then K else 0) else 0)

/-- **P09's bundled book on Death in Damascus** (hypothetical-node encoding): the simulation of
`d₁` (Death's prediction), the live act, the post-act sell point.
Source: P09.md Setting; P09-2′ (hypothetical-node); mandate T1(c), T5
Kind: D
Fidelity: variant: both points share the action type `BAct` and `d₂` reads only the side
coordinate (its base coordinate is payoff-irrelevant); Death's prediction is a simulation query
of `d₁`, perfect under 6′ and an independent sample under Definition 6 -/
def didBundle (U k K k' : ℚ) (bundleOn offer : Act2 → Bool) :
    Tree BW Bool (fun _ => BAct) ℚ :=
  .decision true fun x =>
    .decision true fun a =>
      .decision false fun σ =>
        .leaf (x.1, a, σ.2) (bundlePay U k K k' bundleOn offer x.1 a σ.2)

/-- Observations: `⊤` at both points (`d₂^a`'s conditioning on the act is carried by the action
events). Source: P09.md Setting. Kind: D -/
def bObs : Bool → Finset BW := fun _ => Finset.univ

/-- Action events: the live act at `d₁`; the side coordinate at `d₂`. Source: P09.md Setting.
Kind: D -/
def bActEv : (d : Bool) → BAct → Finset BW := fun d a =>
  if d then Finset.univ.filter fun w => w.2.1 = a
  else Finset.univ.filter fun w => w.2.2 = a.2

/-- `P(base = S)` of a `d₁` label. Source: P09-6′ (`q = P(S)`). Kind: D -/
def bQS (m : FinDistr ℚ BAct) : ℚ := m.w (.a, false) + m.w (.a, true)

/-- `P(sell)` of a `d₂` label. Source: P09-3′. Kind: D -/
def bSell (m : FinDistr ℚ BAct) : ℚ := m.w (.a, true) + m.w (.b, true)

/-- Survival probability of a base act when Death's location is an independent sample with
`P(S) = q`. Source: P09-6′ ("`S ↦ U(1−q)`, `R ↦ Uq …`"). Kind: D -/
def bSurv (q : ℚ) : Act2 → ℚ
  | .a => 1 - q
  | .b => q

/-- **The Definition-6 strict act value = the marginal-holding cf's value**:
`U·sv + [bundled](−k + K·sv) + s·[offered](k' − K·sv)`.
Source: P09-6′ (the three values); P09-2′(b); mandate T5(b)(c). Kind: D -/
def bundleVal (U k K k' : ℚ) (bundleOn offer : Act2 → Bool) (q s : ℚ) (a : BAct) : ℚ :=
  U * bSurv q a.1 +
    (if a.2 = true ∧ bundleOn a.1 = true then -k + K * bSurv q a.1 else 0) +
    s * (if offer a.1 = true then k' - K * bSurv q a.1 else 0)

/-- **The 6′ strict act value**: nobody survives, `−k·[bundled] + s·k'·[offered]`.
Source: P09-2′(a) ("`ν(survive ∣ act = a) = 0` for every `a`"). Kind: D -/
def bundleVal' (k k' : ℚ) (bundleOn offer : Act2 → Bool) (s : ℚ) (a : BAct) : ℚ :=
  (if a.2 = true ∧ bundleOn a.1 = true then -k else 0) +
    s * (if offer a.1 = true then k' else 0)

/-- Approval among the supported acts only (the strict grade's comparison set `A⁺`): every
supported act maximises `c` over the supported acts. Source: [[decision-problems-v2]] §4
Definition 18 at the strict grade (`A⁺_d`); P09-2′(a). Kind: D -/
def ApprovedAmongSupported {A : Type} [Fintype A] (m : FinDistr ℚ A) (c : A → ℚ) : Prop :=
  ∀ x, 0 < m.w x → ∀ y, 0 < m.w y → c y ≤ c x

section tree

variable (U k K k' : ℚ) (bundleOn offer : Act2 → Bool) (C : Proc Bool (fun _ => BAct) ℚ)

/-- Sums over the 64 leaves. Source: none: infrastructure. Kind: L -/
theorem didBundle_sum {M : Type} [AddCommMonoid M]
    (f : (didBundle U k K k' bundleOn offer).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ x : BAct, ∑ a : BAct, ∑ σ : BAct, f ⟨x, ⟨a, ⟨σ, ()⟩⟩⟩ := by
  unfold didBundle at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The `d₁` label's weights sum to one, in coordinates. Source: none: infrastructure. Kind: L -/
theorem bact_sum_one (m : FinDistr ℚ BAct) :
    m.w (.a, false) + m.w (.a, true) + m.w (.b, false) + m.w (.b, true) = 1 := by
  have := m.sum_one
  rw [Fintype.sum_prod_type] at this
  simp only [Act2.sum_univ, Fintype.sum_bool] at this
  linarith

/-- `ν(a) = C(d₁)(a)` under Definition 6. Source: none: infrastructure. Kind: L -/
theorem bundle_nu_act (a : BAct) :
    nu C (didBundle U k K k' bundleOn offer) (bActEv true a) = (C true).w a := by
  rw [nu_eq_sum, didBundle_sum]
  have h1 := bact_sum_one (C true)
  have h2 := bact_sum_one (C false)
  have e1 : (C true).w (.a, false) = 1 - (C true).w (.a, true) - (C true).w (.b, false) -
      (C true).w (.b, true) := by linarith
  have e2 : (C false).w (.a, false) = 1 - (C false).w (.a, true) - (C false).w (.b, false) -
      (C false).w (.b, true) := by linarith
  simp only [Fintype.sum_prod_type, Act2.sum_univ, Fintype.sum_bool]
  rcases a with ⟨b, f⟩
  cases b <;> cases f <;>
    simp [didBundle, bActEv] <;> (try rw [e1]) <;> (try rw [e2]) <;> ring

/-- `𝔼[r·1_a] = C(d₁)(a)·bundleVal(q, s, a)` under Definition 6: Death's location is an
independent sample of the label with `P(S) = q`, the sell draw independent with `P(sell) = s`.
Source: P09-2′(b), P09-6′; mandate T5(c). Kind: P. Fidelity: exact -/
theorem bundle_paySum_act (a : BAct) :
    paySum C (didBundle U k K k' bundleOn offer) (bActEv true a) =
      (C true).w a * bundleVal U k K k' bundleOn offer (bQS (C true)) (bSell (C false)) a := by
  rw [paySum_eq_sum_ite, didBundle_sum]
  have h1 := bact_sum_one (C true)
  have h2 := bact_sum_one (C false)
  have e1 : (C true).w (.a, false) = 1 - (C true).w (.a, true) - (C true).w (.b, false) -
      (C true).w (.b, true) := by linarith
  have e2 : (C false).w (.a, false) = 1 - (C false).w (.a, true) - (C false).w (.b, false) -
      (C false).w (.b, true) := by linarith
  simp only [Fintype.sum_prod_type, Act2.sum_univ, Fintype.sum_bool]
  rcases a with ⟨b, f⟩
  cases b <;> cases f <;>
    simp [didBundle, bActEv, bundlePay, bundleVal, bQS, bSell, bSurv] <;>
    (try rw [e1]) <;> (try rw [e2]) <;> split_ifs <;> ring

/-- The Definition-6 strict act value at `d₁`. Source: P09-2′(b). Kind: D -/
noncomputable def bundleE (a : BAct) : ℚ :=
  condExp C (didBundle U k K k' bundleOn offer) (bActEv true a)

/-- **Definition 6: the strict act value is `bundleVal`** at every realized act.
Source: P09-2′(b) ("`ν(survive ∣ a) = ½ =` the classical cf's value; every evaluator buys");
P09-6′ ("Definition 6: reverse bet worth `k' − Kq`, side bet `Kq − k`"); mandate T5(c)
Kind: P
Fidelity: exact -/
theorem bundleE_eq (a : BAct) (ha : 0 < (C true).w a) :
    bundleE U k K k' bundleOn offer C a =
      bundleVal U k K k' bundleOn offer (bQS (C true)) (bSell (C false)) a := by
  unfold bundleE condExp
  rw [bundle_paySum_act, bundle_nu_act]
  field_simp

/-! ### The shared seed -/

/-- **The 6′ run law**: `μ'(x, a, σ) = C(d₁)(x)·[x = a]·C(d₂)(σ)` — Death's prediction is the
live act. Source: `seeds.md` Definition 6′; P09-2′(a). Kind: P. Fidelity: exact -/
theorem bundle_leafLaw' (x a σ : BAct) :
    leafLaw' C (didBundle U k K k' bundleOn offer) ⟨x, ⟨a, ⟨σ, ()⟩⟩⟩ =
      (C true).w x * (if x = a then 1 else 0) * (C false).w σ := by
  unfold leafLaw' didBundle
  rw [leafLawSeed_decision_of_none C rfl, leafLawSeed_decision_of_some C (a' := x) (by simp),
    leafLawSeed_decision_of_none C (by simp)]
  simp only [leafLawSeed_leaf]
  split_ifs <;> ring

/-- `ν'(a) = C(d₁)(a)`. Source: none: infrastructure. Kind: L -/
theorem bundle_nu'_act (a : BAct) :
    nu' C (didBundle U k K k' bundleOn offer) (bActEv true a) = (C true).w a := by
  rw [nu'_eq_sum_ite, didBundle_sum]
  simp only [bundle_leafLaw']
  have h2 := bact_sum_one (C false)
  have e2 : (C false).w (.a, false) = 1 - (C false).w (.a, true) - (C false).w (.b, false) -
      (C false).w (.b, true) := by linarith
  simp only [Fintype.sum_prod_type, Act2.sum_univ, Fintype.sum_bool]
  rcases a with ⟨b, f⟩
  cases b <;> cases f <;> simp [didBundle, bActEv] <;> (try rw [e2]) <;> ring

/-- `𝔼'[r·1_a] = C(d₁)(a)·bundleVal'(s, a)`: nobody survives under the seed.
Source: P09-2′(a). Kind: P. Fidelity: exact -/
theorem bundle_paySumSeed_act (a : BAct) :
    paySumSeed C (didBundle U k K k' bundleOn offer) (bActEv true a) =
      (C true).w a * bundleVal' k k' bundleOn offer (bSell (C false)) a := by
  rw [paySumSeed_eq_sum_ite, didBundle_sum]
  simp only [bundle_leafLaw']
  have h2 := bact_sum_one (C false)
  have e2 : (C false).w (.a, false) = 1 - (C false).w (.a, true) - (C false).w (.b, false) -
      (C false).w (.b, true) := by linarith
  simp only [Fintype.sum_prod_type, Act2.sum_univ, Fintype.sum_bool]
  rcases a with ⟨b, f⟩
  cases b <;> cases f <;>
    simp [didBundle, bActEv, bundlePay, bundleVal', bSell] <;> (try rw [e2]) <;> split_ifs <;> ring

/-- The 6′ strict act value at `d₁`. Source: P09-2′(a). Kind: D. Fidelity: variant: 6′ -/
noncomputable def bundleE' (a : BAct) : ℚ :=
  condExpSeed C (didBundle U k K k' bundleOn offer) (bActEv true a)

/-- **6′: the strict act value is `bundleVal'`** at every realized act.
Source: P09-2′(a) ("survival is `0` under every `m`"); mandate T5(b)
Kind: P
Fidelity: variant: 6′ -/
theorem bundleE'_eq (a : BAct) (ha : 0 < (C true).w a) :
    bundleE' U k K k' bundleOn offer C a = bundleVal' k k' bundleOn offer (bSell (C false)) a := by
  unfold bundleE' condExpSeed
  rw [bundle_paySumSeed_act, bundle_nu'_act]
  field_simp

/-- **The 6′ value of a procedure**: `∑_a C(d₁)(a)·bundleVal'(s, a)`.
Source: P09-2′(a) ("`V_B(book) = −½` against `0` and `+½`"); P09-6′ ("`V(book) = −19/80`").
Kind: P. Fidelity: variant: 6′ -/
theorem bundle_value' :
    value' C (didBundle U k K k' bundleOn offer) =
      ∑ a : BAct, (C true).w a * bundleVal' k k' bundleOn offer (bSell (C false)) a := by
  unfold value'
  rw [didBundle_sum]
  simp only [bundle_leafLaw']
  have h2 := bact_sum_one (C false)
  have e2 : (C false).w (.a, false) = 1 - (C false).w (.a, true) - (C false).w (.b, false) -
      (C false).w (.b, true) := by linarith
  simp only [Fintype.sum_prod_type, Act2.sum_univ, Fintype.sum_bool]
  simp [didBundle, bundlePay, bundleVal', bSell]
  rw [e2]
  split_ifs <;> ring

end tree

/-! ### P09-1: the leaf-wise identity -/

/-- **P09-1, the sure loss is a leaf-wise identity**: on every leaf, bet-and-sell minus
no-bet-and-keep is `k' − k` (the `K`-legs cancel whatever the survival indicator is), for every
`U`, every Death location, either base act (where both legs are offered).
Source: P09.md line 34 (P09-1: "`−k + K[X] + k' − K[X] = −(k − k')` on every reached leaf");
mandate T1(c)
Kind: L (the plan pre-labels the identity `L`)
Fidelity: exact -/
theorem bundle_leafwise (U k K k' : ℚ) (bundleOn offer : Act2 → Bool) (death base : Act2)
    (hb : bundleOn base = true) (ho : offer base = true) :
    bundlePay U k K k' bundleOn offer death (base, true) true -
      bundlePay U k K k' bundleOn offer death (base, false) false = k' - k := by
  unfold bundlePay
  simp [hb, ho]
  split_ifs <;> ring

/-! ### P09-2′(a): the booked label `(0, ½, 0, ½)` -/

/-- The booked label: `Sb` and `Rb` w.p. `½` each. Source: P09-2′ ("base label `½` with sell on
every branch"). Kind: D -/
def bookedLabel : FinDistr ℚ BAct where
  w := fun a => if a.2 = true then 1/2 else 0
  nonneg := fun a => by split_ifs <;> norm_num
  sum_one := by
    rw [Fintype.sum_prod_type, Act2.sum_univ]
    simp [Fintype.sum_bool]
    norm_num

/-- The all-bases flag. Source: none: infrastructure. Kind: D -/
def allBases : Act2 → Bool := fun _ => true

/-- **At the booked label with sell forced, the 6′ values of the supported acts tie at
`−k + k'`** — strict-grade `T_EDT` (comparison among `A⁺ = {Sb, Rb}`) approves the booked label.
Source: P09-2′(a) ("the strictly calibrated state has `A⁺ = {Sb, Rb}` with tied values `−½`, so
`T_EDT` (Definition 18) approves the booked label"); mandate T5(b)
Kind: P
Fidelity: variant: 6′; the strict grade rendered as comparison among supported acts
Hyps: (a) `C(d₁)` is the booked label, the sell forced at every base point -/
theorem bundle_booked_strict_approved (U k K k' : ℚ) (C : Proc Bool (fun _ => BAct) ℚ)
    (hC : C true = bookedLabel) (hs : bSell (C false) = 1) :
    bundleE' U k K k' allBases allBases C (.a, true) = -k + k' ∧
      bundleE' U k K k' allBases allBases C (.b, true) = -k + k' ∧
      ApprovedAmongSupported bookedLabel (bundleE' U k K k' allBases allBases C) := by
  have hv : ∀ a : BAct, 0 < (C true).w a →
      bundleE' U k K k' allBases allBases C a = bundleVal' k k' allBases allBases 1 a := by
    intro a ha; rw [bundleE'_eq _ _ _ _ _ _ _ a ha, hs]
  have hSb : 0 < (C true).w (.a, true) := by rw [hC]; simp [bookedLabel]
  have hRb : 0 < (C true).w (.b, true) := by rw [hC]; simp [bookedLabel]
  refine ⟨?_, ?_, ?_⟩
  · rw [hv _ hSb]; simp [bundleVal', allBases]
  · rw [hv _ hRb]; simp [bundleVal', allBases]
  · intro x hx y hy
    rw [hv x (by rw [hC]; exact hx), hv y (by rw [hC]; exact hy)]
    rcases x with ⟨bx, fx⟩; rcases y with ⟨by', fy⟩
    cases fx <;> cases fy <;> simp [bookedLabel] at hx hy <;> simp [bundleVal', allBases]

/-- **At every full-support self-model the bet is declined** (the masked grade): `S` is worth
`k' > −k + k'`, so the booked label is not approved against all acts when `k > 0`.
Source: P09-2′(a) ("'the evidential evaluator declines the bet' holds at the masked grade — for
every full-support self-model `m`"); mandate T5(b)
Kind: P
Fidelity: variant: 6′; the masked grade rendered as the values at a full-support label -/
theorem bundle_booked_masked_refused (U k K k' : ℚ) (hk : 0 < k) (C : Proc Bool (fun _ => BAct) ℚ)
    (hfull : ∀ a, 0 < (C true).w a) (hs : bSell (C false) = 1) :
    ¬ ApprovedBy bookedLabel (bundleE' U k K k' allBases allBases C) := by
  intro h
  have := h (.a, true) (by simp [bookedLabel]) (.a, false)
  rw [bundleE'_eq _ _ _ _ _ _ _ _ (hfull _), bundleE'_eq _ _ _ _ _ _ _ _ (hfull _), hs] at this
  simp [bundleVal', allBases] at this
  linarith

/-- **The classical cf's values at `(U, k, K, k') = (10, 1, 3, ½)`**: survival `½` for every act
(`bundleVal` at `q = ½`, `s = 1`) gives `(S, Sb, R, Rb) = (4, 9/2, 4, 9/2)`, and the booked label
is approved by it (a fixed point of the classical argmax).
Source: P09-2′(a) ("`T_CDT`'s values are `(4, 9/2, 4, 9/2)` (argmax `{Sb, Rb}`; the label is a
fixed point)"); dp-sl-046 (the values are `c`-data); mandate T5(b)
Kind: P / N+
Fidelity: exact
Hyps: (c) the cf holds survival at the marginal `½` -/
theorem bundle_cf_values :
    bundleVal 10 1 3 (1/2) allBases allBases (1/2) 1 (.a, false) = 4 ∧
      bundleVal 10 1 3 (1/2) allBases allBases (1/2) 1 (.a, true) = 9/2 ∧
      bundleVal 10 1 3 (1/2) allBases allBases (1/2) 1 (.b, false) = 4 ∧
      bundleVal 10 1 3 (1/2) allBases allBases (1/2) 1 (.b, true) = 9/2 ∧
      ApprovedBy bookedLabel (bundleVal 10 1 3 (1/2) allBases allBases (1/2) 1) := by
  refine ⟨by simp [bundleVal, bSurv, allBases]; norm_num, by simp [bundleVal, bSurv, allBases]; norm_num,
    by simp [bundleVal, bSurv, allBases]; norm_num, by simp [bundleVal, bSurv, allBases]; norm_num, ?_⟩
  intro x hx y
  rcases x with ⟨bx, fx⟩; rcases y with ⟨by', fy⟩
  cases bx <;> cases fx <;> cases by' <;> cases fy <;> simp [bookedLabel] at hx ⊢ <;>
    simp [bundleVal, bSurv, allBases] <;> norm_num

/-- **The book's 6′ value**: `V'(book) = −k + k'` at the booked label with sell forced (`−½`),
against `0` for declining both and `k'` for declining the bet and taking the reverse one.
Source: P09-2′(a) ("`V_B(book) = −½` against `0` (decline-both) and `+½`"); mandate T5(b)
Kind: P / N+
Fidelity: variant: 6′ -/
theorem bundle_book_value' (U k K k' : ℚ) (C : Proc Bool (fun _ => BAct) ℚ)
    (hC : C true = bookedLabel) (hs : bSell (C false) = 1) :
    value' C (didBundle U k K k' allBases allBases) = -k + k' := by
  rw [bundle_value', hs, hC, Fintype.sum_prod_type, Act2.sum_univ]
  simp [Fintype.sum_bool, bookedLabel, bundleVal', allBases]
  ring

/-- Declining both (`S` surely, keep) is worth `0`; declining the bet and taking the reverse one
(`S` surely, sell) is worth `k'`, under 6′. Source: P09-2′(a). Kind: N+. Fidelity: variant: 6′ -/
theorem bundle_decline_values' (U k K k' : ℚ) :
    value' (Proc.ofFun fun _ => ((.a, false) : BAct)) (didBundle U k K k' allBases allBases) = 0 ∧
      value' (Proc.ofFun fun d => if d then ((.a, false) : BAct) else (.a, true))
        (didBundle U k K k' allBases allBases) = k' := by
  constructor <;>
  · rw [bundle_value', Fintype.sum_prod_type, Act2.sum_univ]
    simp [Fintype.sum_bool, Proc.ofFun, bundleVal', allBases, bSell]

/-! ### P09-6′: booking one act moves the label -/

/-- The R-only flag (`A₁ = {S, R, Rb}`: the side bet bundled with R only, the reverse bet
offered on R-branches). Source: P09-6′ hypotheses. Kind: D -/
def rOnly : Act2 → Bool := fun b => decide (b = .b)

/-- **The `S ∼ Rb` tie equation**: `bundleVal q s S = bundleVal q s Rb ↔ q(2U + K − sK) = U + k − sk'`
on the R-only tree.
Source: P09-6′ ("shared-seed tie `2Uq = U + k − k'`"; "Definition 6: `q(2U + K) = U + k`");
`P09-bundled-book-identities.lean` (the tie as a linear hypothesis); mandate T5(c)
Kind: P
Fidelity: exact -/
theorem bundle_tie_iff (U k K k' q s : ℚ) :
    bundleVal U k K k' rOnly rOnly q s (.a, false) = bundleVal U k K k' rOnly rOnly q s (.b, true) ↔
      q * (2 * U + K - s * K) = U + k - s * k' := by
  simp only [bundleVal, bSurv, rOnly]
  simp
  constructor <;> intro h <;> linear_combination (-1 : ℚ) * h

/-- **With sell forced the tie is at `q* = 21/40`** at `(10, 1, 3, ½)`, with values
`(S, R, Rb) = (19/4, 167/40, 19/4)` and `Rb − R = 23/40`.
Source: P09-6′ ("unique tie `S ∼ Rb` at `q* = 21/40`, values `(19/4, 167/40, 19/4)`,
`Rb − R = 23/40 > 0`"); mandate T5(c)
Kind: P / N+
Fidelity: exact -/
theorem bundle_tie_2140 :
    (∀ q : ℚ, bundleVal 10 1 3 (1/2) rOnly rOnly q 1 (.a, false) =
        bundleVal 10 1 3 (1/2) rOnly rOnly q 1 (.b, true) ↔ q = 21/40) ∧
      bundleVal 10 1 3 (1/2) rOnly rOnly (21/40) 1 (.a, false) = 19/4 ∧
      bundleVal 10 1 3 (1/2) rOnly rOnly (21/40) 1 (.b, false) = 167/40 ∧
      bundleVal 10 1 3 (1/2) rOnly rOnly (21/40) 1 (.b, true) = 19/4 := by
  refine ⟨fun q => ?_, ?_, ?_, ?_⟩
  · rw [bundle_tie_iff]; constructor <;> intro h <;> linarith
  all_goals simp [bundleVal, bSurv, rOnly]; norm_num

/-- **Under Definition 6 with keep (`s = 0`) the tie is at `q* = 11/23`** at `(10, 1, 3)`.
Source: P09-6′ ("under Definition 6 the tie is at `q(2U + K) = U + k` (`q = 11/23`)");
mandate T5(c)
Kind: P
Fidelity: exact -/
theorem bundle_tie_1123 (q : ℚ) :
    bundleVal 10 1 3 (1/2) rOnly rOnly q 0 (.a, false) =
      bundleVal 10 1 3 (1/2) rOnly rOnly q 0 (.b, true) ↔ q = 11/23 := by
  rw [bundle_tie_iff]; constructor <;> intro h <;> linarith

/-- The shifted label `(S: 21/40, Rb: 19/40)`. Source: P09-6′. Kind: D -/
def label2140 : FinDistr ℚ BAct where
  w := fun a => if a = (.a, false) then 21/40 else if a = (.b, true) then 19/40 else 0
  nonneg := fun a => by split_ifs <;> norm_num
  sum_one := by
    rw [Fintype.sum_prod_type, Act2.sum_univ]
    simp [Fintype.sum_bool]
    norm_num

/-- **The shifted label is approved by the classical cf** (Definition 18's tie-freedom: support
`{S, Rb}` inside the argmax), **and Definition 17's uniform label `½` is not at a tie**
(`S = 5 ≠ 9/2 = Rb` there).
Source: P09-6′ ("the label `(21/40, 0, 19/40)` is `T_CDT`-approved (Definition 18's tie-freedom —
Definition 17's uniform tie would output `(½, ½)`, not at a tie)"); mandate T5(c)
Kind: P / N+
Fidelity: exact (`Sb` is a payoff-irrelevant duplicate of `S` on the R-only tree, tied with it)
Hyps: (c) the cf's values (here `bundleVal`, which equals Definition 6's conditioning) -/
theorem bundle_2140_approved :
    ApprovedBy label2140 (bundleVal 10 1 3 (1/2) rOnly rOnly (21/40) 1) ∧
      bundleVal 10 1 3 (1/2) rOnly rOnly (1/2) 1 (.a, false) = 5 ∧
      bundleVal 10 1 3 (1/2) rOnly rOnly (1/2) 1 (.b, true) = 9/2 := by
  refine ⟨?_, by simp [bundleVal, bSurv, rOnly]; norm_num, by simp [bundleVal, bSurv, rOnly]; norm_num⟩
  intro x hx y
  rcases x with ⟨bx, fx⟩; rcases y with ⟨by', fy⟩
  cases bx <;> cases fx <;> cases by' <;> cases fy <;> simp [label2140] at hx ⊢ <;>
    simp [bundleVal, bSurv, rOnly] <;> norm_num

/-- **Strict-grade `T_EDT` under 6′ refuses the shifted label**: `V'(S) = 0 > −k + k' = V'(Rb)`
with `Rb` supported; and **`V'(book) = (19/40)(k' − k) = −19/80`** at `(1, ½)`.
Source: P09-6′ ("strict-grade `T_EDT` refuses this label (`V(S) = 0 > −½`); `V(book) = −19/80`
vs `0`; … a weak book"); mandate T5(c)
Kind: P
Fidelity: variant: 6′
Hyps: (a) `k' < k`, `C(d₁)` is the shifted label, the sell forced at every base point -/
theorem bundle_2140_seed (U k K k' : ℚ) (hk : k' < k) (C : Proc Bool (fun _ => BAct) ℚ)
    (hC : C true = label2140) (hs : bSell (C false) = 1) :
    bundleE' U k K k' rOnly rOnly C (.a, false) = 0 ∧
      bundleE' U k K k' rOnly rOnly C (.b, true) = -k + k' ∧
      ¬ ApprovedAmongSupported label2140 (bundleE' U k K k' rOnly rOnly C) ∧
      value' C (didBundle U k K k' rOnly rOnly) = 19/40 * (k' - k) := by
  have hS : 0 < (C true).w (.a, false) := by rw [hC]; simp [label2140]
  have hRb : 0 < (C true).w (.b, true) := by rw [hC]; simp [label2140]
  have eS : bundleE' U k K k' rOnly rOnly C (.a, false) = 0 := by
    rw [bundleE'_eq _ _ _ _ _ _ _ _ hS, hs]; simp [bundleVal', rOnly]
  have eRb : bundleE' U k K k' rOnly rOnly C (.b, true) = -k + k' := by
    rw [bundleE'_eq _ _ _ _ _ _ _ _ hRb, hs]; simp [bundleVal', rOnly]
  refine ⟨eS, eRb, ?_, ?_⟩
  · intro h
    have := h (.b, true) (by simp [label2140]) (.a, false) (by simp [label2140])
    rw [eS, eRb] at this
    linarith
  · rw [bundle_value', hs, hC, Fintype.sum_prod_type, Act2.sum_univ]
    simp [Fintype.sum_bool, label2140, bundleVal', rOnly]
    ring

/-- **No label makes both legs favourable under Definition 6** when `k' ≤ k`: the bundled side
bet on R is worth `Kq − k` (favourable iff `q > k/K`) and the reverse bet `k' − Kq` (favourable
iff `q < k'/K`).
Source: P09-6′ ("Definition 6: reverse bet worth `k' − Kq` (taken iff `q < 1/6`), side bet
`Kq − k` (bought iff `q > 1/3`): no label admits both legs"); `no_pair_under_def6`; mandate T5(c)
Kind: P
Fidelity: exact -/
theorem bundle_no_pair_def6 (U k K k' q : ℚ) (hkk : k' ≤ k) :
    (bundleVal U k K k' rOnly rOnly q 0 (.b, true) - bundleVal U k K k' rOnly rOnly q 0 (.b, false)
        = K * q - k) ∧
      (bundleVal U k K k' rOnly rOnly q 1 (.b, false) - bundleVal U k K k' rOnly rOnly q 0 (.b, false)
        = k' - K * q) ∧
      ¬ (0 < K * q - k ∧ 0 < k' - K * q) := by
  refine ⟨by simp [bundleVal, bSurv, rOnly]; try ring, by simp [bundleVal, bSurv, rOnly]; try ring, ?_⟩
  rintro ⟨h1, h2⟩
  linarith

/-- **F10: the discrepancy is tied to the label** — on the R-only tree with sell forced,
`c(Rb) − e'(Rb) = U·q`, i.e. `U·(1 − P(Rb))` for a label on `{S, Rb}`: no family with fixed
discrepancy and `P(Rb) → 0` lives here.
Source: P09-6′ ("in Death in Damascus `c_a − e_a = 1 − P(a)` is tied to `P(a)` (Open 1)");
dp-sl-2-025 (F10); mandate T5(d)
Kind: P
Fidelity: exact (`U = 1` is the source's normalisation) -/
theorem bundle_cf_sub_e' (U k K k' q : ℚ) :
    bundleVal U k K k' rOnly rOnly q 1 (.b, true) - bundleVal' k k' rOnly rOnly 1 (.b, true) =
      U * q := by
  simp [bundleVal, bundleVal', bSurv, rOnly]
  try ring

end Cleanroom.Decision.DpDutchBook
