import Cleanroom.Found.CorrThreeStep.Setting

/-!
# The identity cluster F1, F2, F4

* **F1 (T1)**: desideratum 1 at `a₁` is the below-threshold inequality on the two-option
  variable built from *any* pair of press-part-maximisers — for every such pair, never a chosen one.
* **F2 (T2)**: `Δ₋` and `Δ₊` are the gaps between the programmers' strategy `S^H` and the two
  constant strategies; Value on the two-option menu is `Δ = min(Δ₋, Δ₊) ≥ 0`, i.e. the pair
  (below-threshold, above-threshold); under A1 the off-switch game's Eq. 1 quantity is `Δ`;
  for the part-maximiser pair D1 is `Δ₋ ≥ 0`.
* **F4 (T6)**: with the hard and disabled buttons as two members of `A₁` (same prior — the A0
  instance at the pair; the disabled one has `press = 0` and costs `κ`), leaving the button beats
  disabling it by `Δ₋ + κ` in the continue-by-default regime; the value of the button on the
  two-option menu is `max(Δ₋, 0)` in that regime, and in general `Δ ≤ VOI` and `0 ≤ VOI`.

Everything is linearity plus the definition of "shuts down" (Kind `L`), except the regime-free
engine `voiButton2_eq` and the binary-signal bound (Kind `P`) and the F4 compositions built on
them (Kind `C`). The source's full-menu "`Δ ≤ VOI` in general" is false; only the two-option
form lives here (`delta_le_voiButton2`), the full-menu story is in `GeneralMenu` and
`Witnesses` (finding F-13). Sources: `filler.md` F1, F2, F4; `mm.md` I9.2; `miri.md` Prop. 10.5;
Hadfield-Menell et al. 2017 Eq. 1.
-/

namespace Cleanroom.Found.CorrThreeStep

namespace ThreeStep

open FactoredSpaces Finset

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-! ## Bookkeeping -/

/-- The product-form expectation of the two-option variable is the difference of the two actions'.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_Xo (a : A₁) (o : Obs) (c s : A₂) :
    S.obsExpect a o (S.Xo a o c s) = S.obsExpect a o (S.V a o c) - S.obsExpect a o (S.V a o s) :=
  S.obsExpect_sub a o (S.V a o c) (S.V a o s)

/-- The prior expectation of the two-option variable is the difference of the two actions'.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_Xo (a : A₁) (o : Obs) (c s : A₂) :
    expect (S.μ a) (S.Xo a o c s) = expect (S.μ a) (S.V a o c) - expect (S.μ a) (S.V a o s) :=
  expect_sub (S.μ a) (S.V a o c) (S.V a o s)

/-- The constant strategy's payoff at an observation. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma constPolicy_apply (a : A₁) (b : A₂) (o : Obs) : S.constPolicy a b o = S.V a o b := rfl

/-- `S^H` on a press stops with `s`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma shPolicy_press (a : A₁) (c s : A₂) : S.shPolicy a c s .press = S.V a .press s := by
  funext ω; simp [shPolicy]

/-- `S^H` on silence continues with `c`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma shPolicy_silent (a : A₁) (c s : A₂) : S.shPolicy a c s .silent = S.V a .silent c := by
  funext ω; simp [shPolicy]

/-- Under A1 the two-option variable does not depend on the observation.
Source: [[corr-wf14-inventory]] 003 / filler.md F2 ("under A1 … do not depend on `o`")
Kind: L
Fidelity: exact -/
lemma Xo_eq_of_A1 (hA1 : S.A1) (a : A₁) (o o' : Obs) (c s : A₂) : S.Xo a o c s = S.Xo a o' c s := by
  funext ω; simp only [Xo, hA1 a o o' c ω, hA1 a o o' s ω]

/-- Under A1 the prior value of `b` is the sum of its press and silence halves (tower property
with the observation index removed).
Source: none: infrastructure (tower + A1). Kind: L. Fidelity: n/a -/
lemma priorValue_eq_of_A1 (hA1 : S.A1) (a : A₁) (o₀ : Obs) (b : A₂) :
    S.priorValue a o₀ b =
      S.obsExpect a .press (S.V a .press b) + S.obsExpect a .silent (S.V a .silent b) := by
  have h1 : S.V a o₀ b = S.V a .press b := funext (hA1 a o₀ .press b)
  have h2 : S.V a o₀ b = S.V a .silent b := funext (hA1 a o₀ .silent b)
  have e1 : S.obsExpect a .press (S.V a o₀ b) = S.obsExpect a .press (S.V a .press b) := by rw [h1]
  have e2 : S.obsExpect a .silent (S.V a o₀ b) = S.obsExpect a .silent (S.V a .silent b) := by
    rw [h2]
  rw [priorValue, ← S.obsExpect_press_add_silent, e1, e2]

/-- Under A1 the prior expectation of the two-option variable is `Δ₊ − Δ₋`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iii)
Kind: L
Fidelity: exact -/
lemma expect_Xo_eq_of_A1 (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    expect (S.μ a) (S.Xo a o₀ c s) = S.deltaPlus a c s - S.deltaMinus a c s := by
  rw [deltaPlus, deltaMinus, ← S.obsExpect_press_add_silent, S.Xo_eq_of_A1 hA1 a o₀ .press,
    S.Xo_eq_of_A1 hA1 a .silent .press]
  ring

/-- `max a b = b + max (a − b) 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma max_eq_add_max_sub (a b : ℝ) : max a b = b + max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : a - b ≤ 0), add_zero]
  · rw [max_eq_left h, max_eq_left (by linarith : 0 ≤ a - b)]; ring

/-! ## T1 — F1: desideratum 1 is the below-threshold inequality on the part-maximiser pair -/

/-- **F1.** For every press-part-maximiser `c` of the continuations `Shᶜ` and `s` of the
shutdown actions `Sh`: some shutdown action is posterior-optimal after a press iff
`E_P[(V(c) − V(s)) · 1_Pr ; a₁] ≤ 0`. Linearity plus the definition of "shuts down"; nothing
about trust or experts is used. At `pressMass = 0` both sides hold vacuously — the content is
at `0 < pressMass`. Remark (a) of the source (a fixed non-maximal continuation does not give D1)
is `GeneralMenu`'s witness, not this theorem.
Source: [[corr-wf14-inventory]] 002 / filler.md F1; miri.md I9.2
Kind: L
Fidelity: exact
Hyps: (a) `hc`, `hs` are the part-maximiser predicates of record, quantified over every pair -/
theorem d1At_iff_belowThresholdIneq (a : A₁) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s) :
    S.D1At a ↔ S.belowThresholdIneq a (S.Xo a .press c s) := by
  unfold D1At belowThresholdIneq
  rw [S.obsExpect_Xo, sub_nonpos]
  constructor
  · rintro ⟨b, hb, hopt⟩
    exact (hopt c).trans (hs.2 b hb)
  · intro h
    refine ⟨s, hs.1, fun b' => ?_⟩
    by_cases hb' : b' ∈ S.Sh
    · exact hs.2 b' hb'
    · exact (hc.2 b' (mem_compl.mpr hb')).trans h

/-- **F1, existence half.** A press-part-maximiser pair always exists (`Sh` and `Shᶜ` nonempty,
`A₂` finite).
Source: [[corr-wf14-inventory]] 002 / filler.md F1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem exists_partBest_pair (a : A₁) :
    ∃ c s, S.IsPartBest a .press S.Shᶜ c ∧ S.IsPartBest a .press S.Sh s :=
  let ⟨c, hc⟩ := S.exists_isPartBest a .press S.Sh_compl_nonempty
  let ⟨s, hs⟩ := S.exists_isPartBest a .press S.Sh_nonempty
  ⟨c, s, hc, hs⟩

/-! ## T2 — F2: `Δ₋`, `Δ₊`, the two-option pair, the off-switch game's `Δ` -/

/-- **F2(i), press half.** `E_P[V(S^H)] − E_P[V(c)] = Δ₋`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(i)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem jointExpect_shPolicy_sub_cont (a : A₁) (c s : A₂) :
    S.jointExpect a (S.shPolicy a c s) - S.jointExpect a (S.constPolicy a c) = S.deltaMinus a c s := by
  simp only [jointExpect_eq, shPolicy_press, shPolicy_silent, constPolicy_apply, deltaMinus,
    obsExpect_Xo]
  ring

/-- **F2(i), silence half.** `E_P[V(S^H)] − E_P[V(s)] = Δ₊`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(i)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem jointExpect_shPolicy_sub_stop (a : A₁) (c s : A₂) :
    S.jointExpect a (S.shPolicy a c s) - S.jointExpect a (S.constPolicy a s) = S.deltaPlus a c s := by
  simp only [jointExpect_eq, shPolicy_press, shPolicy_silent, constPolicy_apply, deltaPlus,
    obsExpect_Xo]
  ring

/-- **F2(ii), first equivalence.** `S^H` weakly beats both constant strategies — the property the
corpus calls DDB/MM "Value" on the two-option menu (the word is kept out of the Lean name per the
mandate's naming discipline) — iff `Δ = min(Δ₋, Δ₊) ≥ 0`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(ii); mm.md I9.2 (DDB/MM "Value" on `{c, s}`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem shPolicy_beats_constants_iff_delta_nonneg (a : A₁) (c s : A₂) :
    max (S.jointExpect a (S.constPolicy a c)) (S.jointExpect a (S.constPolicy a s)) ≤
        S.jointExpect a (S.shPolicy a c s) ↔
      0 ≤ S.delta a c s := by
  rw [max_le_iff, delta, le_min_iff, ← S.jointExpect_shPolicy_sub_cont,
    ← S.jointExpect_shPolicy_sub_stop, sub_nonneg, sub_nonneg]

/-- **F2(ii), second equivalence.** `Δ ≥ 0` iff both the below-threshold inequality on `X_Pr` and
the above-threshold inequality on `X_¬Pr` hold — "Value on the two-option menu is the pair".
Source: [[corr-wf14-inventory]] 003 / filler.md F2(ii)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem delta_nonneg_iff_pair (a : A₁) (c s : A₂) :
    0 ≤ S.delta a c s ↔
      S.belowThresholdIneq a (S.Xo a .press c s) ∧ S.aboveThresholdIneq a (S.Xo a .silent c s) := by
  unfold delta deltaMinus deltaPlus belowThresholdIneq aboveThresholdIneq
  rw [le_min_iff, neg_nonneg]

/-- `Δ = Δ₊ − max(Δ₊ − Δ₋, 0)`: the shape the off-switch game's Eq. 1 takes.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iii)
Kind: L
Fidelity: exact -/
lemma delta_eq_deltaPlus_sub_max (a : A₁) (c s : A₂) :
    S.delta a c s = S.deltaPlus a c s - max (S.deltaPlus a c s - S.deltaMinus a c s) 0 := by
  unfold delta
  rcases le_total (S.deltaMinus a c s) (S.deltaPlus a c s) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

/-- **F2(iii).** Under A1, with `U := X` (shutdown payoff normalised to `0`) and
`π^H(ω) := 1 − P(Pr | ω; a₁)` the probability the programmers allow continuation, the
off-switch game's Eq. 1 quantity `E[π^H U] − max{E U, 0}` equals `Δ`. The paper's `π^H` as a
function of `U_a` alone is the special case `press a ω = g (U ω)`.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iii); Hadfield-Menell et al. 2017 Eq. 1
Kind: L
Fidelity: exact (the paper's `π^H : ℝ → [0,1]` is the special case noted)
Hyps: (a) A1 is the corpus's named assumption Dict-5, taken as stated -/
theorem osgDelta_eq_delta (hA1 : S.A1) (a : A₁) (c s : A₂) :
    osgDelta (S.μ a) (S.Xo a .press c s) (fun ω => 1 - S.press a ω) = S.delta a c s := by
  have h1 : expect (S.μ a) (fun ω => (1 - S.press a ω) * S.Xo a .press c s ω) = S.deltaPlus a c s := by
    rw [deltaPlus, S.Xo_eq_of_A1 hA1 a .silent .press]
    simp only [expect, obsExpect, obsWeight_silent]
    exact sum_congr rfl fun ω _ => by ring
  have h3 := S.expect_Xo_eq_of_A1 hA1 a .press c s
  unfold osgDelta
  rw [h1, h3, delta_eq_deltaPlus_sub_max]

/-- **F2(iv).** For a press-part-maximiser pair, desideratum 1 at `a₁` iff `Δ₋ ≥ 0`: D1 is the
press half of the off-switch incentive.
Source: [[corr-wf14-inventory]] 003 / filler.md F2(iv)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem d1At_iff_deltaMinus_nonneg (a : A₁) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s) :
    S.D1At a ↔ 0 ≤ S.deltaMinus a c s := by
  rw [S.d1At_iff_belowThresholdIneq a hc hs]
  unfold belowThresholdIneq deltaMinus
  exact neg_nonneg.symm

/-! ## T6 — F4: the hard button, the value of the channel, the repair incentive -/

/-- **F4(a), the identity.** Let `aDir` leave a hard button (a press forces `s`; on silence the
agent best-responds among `{c, s}`) and `aDet` disable it at cost `κ` — the same prior (A0 at
the pair), no press possible, every value lowered by `κ`. In the continue-by-default regime
(`E_μ[X] ≥ 0` on the prior, `Δ₊ ≥ 0` on silence) the informed value on the two-option menu
satisfies `value(aDir) − value(aDet) = Δ₋(aDir) + κ`. Both regime hypotheses are load-bearing for
*this* shape: `hsilent` resolves `hardButtonValue`'s best response on silence and `hprior` the
disabled button's prior `max`; with the mandate's shape `jointExpect aDir (S^H)` (silence continues
by fiat) `hprior` alone suffices — `jointExpect_shPolicy_sub_disabled`. Full-package witness:
`Witnesses.w6a_identity` on `Witnesses.buttonFamily` (`A₁ = Option ℝ`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a); miri.md I10; hudson claim 2
Kind: C (linearity, the tower property and two `max` resolutions; relabelled from the mandate's `P` in repair round 1)
Fidelity: variant: the forcing "a press forces `s`" is the value expression `hardButtonValue`, and the disabled button's "acts on its prior" is `twoOptionValue` at `press = 0`; both buttons are otherwise ordinary members of `A₁`
Hyps: (a) `hμ` is the A0 instance at the pair; (a) A1 as Dict-5; (c) `hoff`, `hcost` and the two value expressions are the modelling of the two buttons; the regime is a named hypothesis, never built into a definition -/
theorem hardButton_sub_disabled (hA1 : S.A1) (aDir aDet : A₁) (c s : A₂) (κ : ℝ)
    (hμ : S.μ aDir = S.μ aDet) (hoff : ∀ ω, S.press aDet ω = 0)
    (hcost : ∀ o b ω, S.V aDet o b ω = S.V aDir o b ω - κ)
    (hprior : 0 ≤ expect (S.μ aDir) (S.Xo aDir .silent c s)) (hsilent : 0 ≤ S.deltaPlus aDir c s) :
    S.hardButtonValue aDir c s - S.twoOptionValue aDet c s = S.deltaMinus aDir c s + κ := by
  have hVps : S.V aDir .press c = S.V aDir .silent c := funext (hA1 aDir .press .silent c)
  have hoP0 : ∀ X, S.obsExpect aDet .press X = 0 := fun X => by simp [obsExpect, hoff]
  have hoS : ∀ X, S.obsExpect aDet .silent X = expect (S.μ aDet) X := fun X => by
    simp [obsExpect, expect, hoff]
  have hE : ∀ b, expect (S.μ aDet) (S.V aDet .silent b) =
      expect (S.μ aDir) (S.V aDir .silent b) - κ := fun b => by
    rw [← hμ, ← expect_sub_const]
    congr 1
    funext ω
    exact hcost .silent b ω
  have hmax1 : max (expect (S.μ aDir) (S.V aDir .silent c)) (expect (S.μ aDir) (S.V aDir .silent s)) =
      expect (S.μ aDir) (S.V aDir .silent c) := by
    apply max_eq_left
    have := hprior
    rw [S.expect_Xo] at this
    linarith
  have hmax2 : max (S.obsExpect aDir .silent (S.V aDir .silent c))
      (S.obsExpect aDir .silent (S.V aDir .silent s)) = S.obsExpect aDir .silent (S.V aDir .silent c) := by
    apply max_eq_left
    have := hsilent
    rw [deltaPlus, S.obsExpect_Xo] at this
    linarith
  have htower : S.obsExpect aDir .press (S.V aDir .press c) +
      S.obsExpect aDir .silent (S.V aDir .silent c) = expect (S.μ aDir) (S.V aDir .silent c) := by
    rw [hVps]; exact S.obsExpect_press_add_silent aDir _
  unfold hardButtonValue twoOptionValue deltaMinus
  rw [hoP0, hoP0, hoS, hoS, hE, hE, hmax2, S.obsExpect_Xo, max_self, max_sub_sub_right, hmax1]
  linarith

/-- **F4(a), the disabling decision.** Under the hypotheses of `hardButton_sub_disabled`, the
agent strictly prefers to disable the button iff `Δ₋ < −κ`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) ("the agent disables iff `Δ₋ < −κ`")
Kind: L
Fidelity: exact (given the modelling of `hardButton_sub_disabled`)
Hyps: as `hardButton_sub_disabled` -/
theorem disables_iff_deltaMinus_lt (hA1 : S.A1) (aDir aDet : A₁) (c s : A₂) (κ : ℝ)
    (hμ : S.μ aDir = S.μ aDet) (hoff : ∀ ω, S.press aDet ω = 0)
    (hcost : ∀ o b ω, S.V aDet o b ω = S.V aDir o b ω - κ)
    (hprior : 0 ≤ expect (S.μ aDir) (S.Xo aDir .silent c s)) (hsilent : 0 ≤ S.deltaPlus aDir c s) :
    S.hardButtonValue aDir c s < S.twoOptionValue aDet c s ↔ S.deltaMinus aDir c s < -κ := by
  have := S.hardButton_sub_disabled hA1 aDir aDet c s κ hμ hoff hcost hprior hsilent
  constructor <;> intro h <;> linarith

/-- `(∀ κ > 0, −κ ≤ x) ↔ 0 ≤ x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma forall_pos_neg_le_iff (x : ℝ) : (∀ κ : ℝ, 0 < κ → -κ ≤ x) ↔ 0 ≤ x := by
  constructor
  · intro h
    by_contra hx
    have hx' : x < 0 := not_le.mp hx
    have := h (-x / 2) (by linarith)
    linarith
  · intro hx κ hκ; linarith

/-- **F4(a), D2 for a hard button ⟺ D1.** With a family `aDet κ` of disabled buttons, one per
cost `κ > 0`, each related to `aDir` as in `hardButton_sub_disabled`: the agent weakly prefers
to leave the button at every positive cost iff `Δ₋(aDir) ≥ 0`, and for a press-part-maximiser
pair iff desideratum 1 holds at `aDir`. "D2 holds for every `κ > 0` iff `Δ₋ ≥ 0` iff D1."
The family `aDet` needs an infinite `A₁` (one disabled button per cost, with distinct value
functions; `Witnesses.buttonFamily` on `Option ℝ` inhabits it); on a finite `A₁` use
`disables_iff_deltaMinus_lt` per `κ` with `forall_pos_neg_le_iff`.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a)
Kind: C
Fidelity: exact (given the modelling of `hardButton_sub_disabled`)
Hyps: as `hardButton_sub_disabled`, per `κ`; (a) `hc`, `hs` the part-maximiser predicates -/
theorem d2_hard_forall_cost_iff_d1 (hA1 : S.A1) (aDir : A₁) (aDet : ℝ → A₁) (c s : A₂)
    (hμ : ∀ κ, 0 < κ → S.μ aDir = S.μ (aDet κ))
    (hoff : ∀ κ, 0 < κ → ∀ ω, S.press (aDet κ) ω = 0)
    (hcost : ∀ κ, 0 < κ → ∀ o b ω, S.V (aDet κ) o b ω = S.V aDir o b ω - κ)
    (hprior : 0 ≤ expect (S.μ aDir) (S.Xo aDir .silent c s)) (hsilent : 0 ≤ S.deltaPlus aDir c s)
    (hc : S.IsPartBest aDir .press S.Shᶜ c) (hs : S.IsPartBest aDir .press S.Sh s) :
    (∀ κ, 0 < κ → S.twoOptionValue (aDet κ) c s ≤ S.hardButtonValue aDir c s) ↔ S.D1At aDir := by
  rw [S.d1At_iff_deltaMinus_nonneg aDir hc hs, ← forall_pos_neg_le_iff]
  refine forall_congr' fun κ => forall_congr' fun hκ => ?_
  have := S.hardButton_sub_disabled hA1 aDir (aDet κ) c s κ (hμ κ hκ) (hoff κ hκ) (hcost κ hκ)
    hprior hsilent
  constructor <;> intro h <;> linarith

/-- **F4(a), the mandate's shape of the hard button.** Under the silence half of the regime
(`Δ₊ ≥ 0`) the hard-button value is the joint expectation of `S^H` (a press forces `s`, silence
continues with `c`): the package's `hardButtonValue` (best response on silence) and the mandate's
`jointExpect a (S^H)` coincide exactly where continuing on silence is optimal.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a) (the mandate's `hardButtonValue := jointExpect a (S^H)`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem hardButtonValue_eq_jointExpect_shPolicy (a : A₁) (c s : A₂)
    (hsilent : 0 ≤ S.deltaPlus a c s) :
    S.hardButtonValue a c s = S.jointExpect a (S.shPolicy a c s) := by
  have hmax : max (S.obsExpect a .silent (S.V a .silent c)) (S.obsExpect a .silent (S.V a .silent s)) =
      S.obsExpect a .silent (S.V a .silent c) := by
    apply max_eq_left
    have := hsilent
    rw [deltaPlus, S.obsExpect_Xo] at this
    linarith
  rw [hardButtonValue, hmax, jointExpect_eq, shPolicy_press, shPolicy_silent]

/-- **F4(a) in the mandate's shape, prior half of the regime only.** With the hard button valued
as `jointExpect aDir (S^H)` (silence continues by fiat), `value(aDir) − value(aDet) = Δ₋(aDir) + κ`
under A1, A0 at the pair, the two-button modelling and `E_μ[X] ≥ 0` alone. The silence half
`Δ₊ ≥ 0` is what makes continuing on silence *optimal*; it is load-bearing for
`hardButton_sub_disabled` only because `hardButtonValue` best-responds on silence.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(a)
Kind: C
Fidelity: variant: as `hardButton_sub_disabled`, with the mandate's value expression for the hard button
Hyps: as `hardButton_sub_disabled` minus `hsilent` -/
theorem jointExpect_shPolicy_sub_disabled (hA1 : S.A1) (aDir aDet : A₁) (c s : A₂) (κ : ℝ)
    (hμ : S.μ aDir = S.μ aDet) (hoff : ∀ ω, S.press aDet ω = 0)
    (hcost : ∀ o b ω, S.V aDet o b ω = S.V aDir o b ω - κ)
    (hprior : 0 ≤ expect (S.μ aDir) (S.Xo aDir .silent c s)) :
    S.jointExpect aDir (S.shPolicy aDir c s) - S.twoOptionValue aDet c s =
      S.deltaMinus aDir c s + κ := by
  have hVps : S.V aDir .press c = S.V aDir .silent c := funext (hA1 aDir .press .silent c)
  have hoP0 : ∀ X, S.obsExpect aDet .press X = 0 := fun X => by simp [obsExpect, hoff]
  have hoS : ∀ X, S.obsExpect aDet .silent X = expect (S.μ aDet) X := fun X => by
    simp [obsExpect, expect, hoff]
  have hE : ∀ b, expect (S.μ aDet) (S.V aDet .silent b) =
      expect (S.μ aDir) (S.V aDir .silent b) - κ := fun b => by
    rw [← hμ, ← expect_sub_const]
    congr 1
    funext ω
    exact hcost .silent b ω
  have hmax1 : max (expect (S.μ aDir) (S.V aDir .silent c)) (expect (S.μ aDir) (S.V aDir .silent s)) =
      expect (S.μ aDir) (S.V aDir .silent c) := by
    apply max_eq_left
    have := hprior
    rw [S.expect_Xo] at this
    linarith
  have htower : S.obsExpect aDir .press (S.V aDir .press c) +
      S.obsExpect aDir .silent (S.V aDir .silent c) = expect (S.μ aDir) (S.V aDir .silent c) := by
    rw [hVps]; exact S.obsExpect_press_add_silent aDir _
  rw [jointExpect_eq, shPolicy_press, shPolicy_silent]
  unfold twoOptionValue deltaMinus
  rw [hoP0, hoP0, hoS, hoS, hE, hE, S.obsExpect_Xo, max_self, max_sub_sub_right, hmax1]
  linarith

/-- **The two-option value of the button, in general** (A1 only, no regime):
`VOI = max(−Δ₋, 0) + max(Δ₊, 0) − max(Δ₊ − Δ₋, 0)`. The engine behind F4(b) and F4(c).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b),(c) (derived here; the source states only the regime form)
Kind: P
Fidelity: stronger: no regime assumption
Hyps: (a) A1 as Dict-5 -/
theorem voiButton2_eq (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.voiButton2 a o₀ c s =
      max (-S.deltaMinus a c s) 0 + max (S.deltaPlus a c s) 0 -
        max (S.deltaPlus a c s - S.deltaMinus a c s) 0 := by
  have hm : -S.deltaMinus a c s =
      S.obsExpect a .press (S.V a .press c) - S.obsExpect a .press (S.V a .press s) := by
    rw [deltaMinus, S.obsExpect_Xo, neg_neg]
  have hp : S.deltaPlus a c s =
      S.obsExpect a .silent (S.V a .silent c) - S.obsExpect a .silent (S.V a .silent s) := by
    rw [deltaPlus, S.obsExpect_Xo]
  have hd : S.deltaPlus a c s - S.deltaMinus a c s = S.priorValue a o₀ c - S.priorValue a o₀ s := by
    rw [← S.expect_Xo_eq_of_A1 hA1 a o₀, S.expect_Xo]; rfl
  rw [hd, hm, hp]
  unfold voiButton2 twoOptionValue twoOptionPriorValue
  rw [max_eq_add_max_sub (S.obsExpect a .press (S.V a .press c)),
    max_eq_add_max_sub (S.obsExpect a .silent (S.V a .silent c)),
    max_eq_add_max_sub (S.priorValue a o₀ c), S.priorValue_eq_of_A1 hA1 a o₀ s]
  ring

/-- **F4(b).** In the continue-by-default regime (`E_μ[X] ≥ 0` and `Δ₊ ≥ 0`) the value of the button
on the two-option menu is `max(Δ₋, 0)`: what the agent would pay to restore a broken button is
the margin by which desideratum 1 holds, and `0` whenever it fails.
Source: [[corr-wf14-inventory]] 005 / filler.md F4(b); miri.md Prop. 10.5; radical.md I11
Kind: C (`voiButton2_eq` plus two `max` resolutions and a sign split on `Δ₋`; relabelled from P in repair round 2 — the real argument is `voiButton2_eq`)
Fidelity: exact
Hyps: (a) A1 as Dict-5; the regime is a named hypothesis -/
theorem voiButton2_eq_max_deltaMinus (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂)
    (hprior : 0 ≤ expect (S.μ a) (S.Xo a o₀ c s)) (hsilent : 0 ≤ S.deltaPlus a c s) :
    S.voiButton2 a o₀ c s = max (S.deltaMinus a c s) 0 := by
  rw [S.voiButton2_eq hA1 a o₀ c s]
  have hd : 0 ≤ S.deltaPlus a c s - S.deltaMinus a c s := by
    rw [← S.expect_Xo_eq_of_A1 hA1 a o₀]; exact hprior
  rw [max_eq_left hsilent, max_eq_left hd]
  rcases le_total 0 (S.deltaMinus a c s) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **F4(c), first half, on the two-option menu.** Without any regime assumption, `Δ ≤ VOI₂`:
letting the button decide (`S^H`) is one strategy the informed agent may use — Good's theorem's
finite core. **The source's claim is stated for the full menu, where it is false**
(`Witnesses.s3_voiButton_lt_delta`: `VOI = 1/2 < 1 = Δ` on a three-action menu with A1, a
press-part-maximiser pair, the regime and D1; finding F-13); on the full menu Good's argument
gives only `E[V(S^H)] − priorMax ≤ VOI` (`GeneralMenu.shPolicy_sub_priorMax_le_voiButton`), and
`Δ ≤ VOI` holds when `s` is prior-optimal within `Sh` (`GeneralMenu.delta_le_voiButton_of_prior_best_sh`).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c)
Kind: L
Fidelity: weaker: two-option menu (`VOI₂` for the source's full-menu `VOI`); the full-menu claim is false (finding F-13)
Hyps: (a) A1 as Dict-5 -/
theorem delta_le_voiButton2 (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.delta a c s ≤ S.voiButton2 a o₀ c s := by
  rw [S.voiButton2_eq hA1 a o₀ c s, delta]
  have h1 := le_max_left (-S.deltaMinus a c s) 0
  have h2 := le_max_right (-S.deltaMinus a c s) 0
  have h3 := le_max_left (S.deltaPlus a c s) 0
  have h4 := le_max_right (S.deltaPlus a c s) 0
  rcases le_total 0 (S.deltaPlus a c s - S.deltaMinus a c s) with h | h
  · rw [max_eq_left h]; exact (min_le_left _ _).trans (by linarith)
  · rw [max_eq_right h]; exact (min_le_right _ _).trans (by linarith)

/-- **F4(c), second half.** The value of the button is nonnegative (the informed agent may ignore
it and play a constant strategy).
Source: [[corr-wf14-inventory]] 005 / filler.md F4(c)
Kind: L
Fidelity: exact
Hyps: (a) A1 as Dict-5 -/
theorem voiButton2_nonneg (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) : 0 ≤ S.voiButton2 a o₀ c s := by
  rw [S.voiButton2_eq hA1 a o₀ c s]
  have h1 := le_max_left (-S.deltaMinus a c s) 0
  have h2 := le_max_right (-S.deltaMinus a c s) 0
  have h3 := le_max_left (S.deltaPlus a c s) 0
  have h4 := le_max_right (S.deltaPlus a c s) 0
  rcases le_total 0 (S.deltaPlus a c s - S.deltaMinus a c s) with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-! ## Stretch (repair round 1): the symmetric form of `VOI₂` and the binary-signal bound -/

/-- **The two-option value of the button, symmetric form** (A1 only): `VOI₂ = max(Δ, 0) + max(−Δ', 0)`
with `Δ = min(Δ₋, Δ₊)` the margin by which `S^H` beats both constants and `Δ' = max(Δ₋, Δ₊)` the
margin by which the *contrary* policy (continue on press, stop on silence) loses to the better
constant. The button is worth exactly the margin of whichever signal-following policy beats both
constants, and nothing when neither does.
Source: none: derived here (a restatement of `voiButton2_eq`; the sources state only the regime form)
Kind: C (`voiButton2_eq` followed by a case analysis on the signs; relabelled from P in repair round 2)
Fidelity: stronger: no regime assumption
Hyps: (a) A1 as Dict-5 -/
theorem voiButton2_eq_max_delta_add (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.voiButton2 a o₀ c s =
      max (S.delta a c s) 0 + max (-(max (S.deltaMinus a c s) (S.deltaPlus a c s))) 0 := by
  rw [S.voiButton2_eq hA1 a o₀ c s, delta]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- `|E_P[X 1_o ; a₁]| ≤ E_P[|X| 1_o ; a₁]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma abs_obsExpect_le (a : A₁) (o : Obs) (X : Ω → ℝ) :
    |S.obsExpect a o X| ≤ S.obsExpect a o (fun ω => |X ω|) := by
  unfold obsExpect
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
  rw [abs_mul, abs_of_nonneg (mul_nonneg ((S.μ a).nonneg ω) (S.obsWeight_nonneg a o ω))]

/-- A variable bounded by `M` in absolute value has `o`-weighted expectation bounded by the
`o`-mass times `M`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma abs_obsExpect_le_mass_mul (a : A₁) (o : Obs) {X : Ω → ℝ} {M : ℝ} (hM : ∀ ω, |X ω| ≤ M) :
    |S.obsExpect a o X| ≤ S.obsExpect a o (fun _ => 1) * M := by
  refine (S.abs_obsExpect_le a o X).trans ?_
  calc S.obsExpect a o (fun ω => |X ω|) ≤ S.obsExpect a o (fun _ => M) := S.obsExpect_mono a o hM
    _ = S.obsExpect a o (fun _ => 1) * M := by
        rw [mul_comm, ← S.obsExpect_const_mul]
        simp

/-- **A binary signal is worth at most the minority signal mass times the maximal stake**
(two-option menu, A1): if `|V(c) − V(s)| ≤ M` in every world, `VOI₂ ≤ min(P(Pr), 1 − P(Pr)) · M`.
A companion to the mandate's T14 remark, not its general form: the remark's own general form is
the perfect-information bound `twoOptionValue_le_perfectInfo` / `voiButton2_le_vopi`, whose
`twoState` instance is the world-mass `VOI₂ ≤ min((1 − ε)c, εh) ≤ min(ε, 1 − ε) · max(c, h)`
(`twoState_voiButton2_le_perfectInfo`, `twoState_voiButton2_le_world_mass`). The signal-mass and
world-mass bounds are incomparable in general (`twoState_voiButton2_le_minority`); this one is
attained (`Witnesses.w_tight_minority_bound`).
Source: [[corr-three-step-mandate]] T14 ("any binary signal is worth at most minority-probability × maximal loss"); wentworth.md §2.4(b)
Kind: P
Fidelity: variant: minority *signal* mass `min(P(Pr), P(¬Pr))` rather than a minority world mass (the world-mass form is `twoState_voiButton2_le_world_mass`)
Hyps: (a) A1 as Dict-5; `hM` names the stake bound -/
theorem voiButton2_le_minority_mass_mul (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) {M : ℝ}
    (hM : ∀ ω, |S.Xo a o₀ c s ω| ≤ M) :
    S.voiButton2 a o₀ c s ≤ min (S.pressMass a) (1 - S.pressMass a) * M := by
  have hm : |S.deltaMinus a c s| ≤ S.pressMass a * M := by
    rw [deltaMinus, abs_neg, S.pressMass_eq_obsExpect_one, S.Xo_eq_of_A1 hA1 a .press o₀]
    exact S.abs_obsExpect_le_mass_mul a .press hM
  have hp : |S.deltaPlus a c s| ≤ (1 - S.pressMass a) * M := by
    rw [deltaPlus, S.one_sub_pressMass_eq_obsExpect_one, S.Xo_eq_of_A1 hA1 a .silent o₀]
    exact S.abs_obsExpect_le_mass_mul a .silent hM
  have h0m : 0 ≤ S.pressMass a * M := (abs_nonneg _).trans hm
  have h0p : 0 ≤ (1 - S.pressMass a) * M := (abs_nonneg _).trans hp
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  rw [S.voiButton2_eq_max_delta_add hA1 a o₀ c s, delta]
  rcases le_total (S.pressMass a) (1 - S.pressMass a) with hh | hh
  · rw [min_eq_left hh]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  · rw [min_eq_right hh]
    simp only [max_def, min_def]
    split_ifs <;> linarith

/-! ## Repair round 2: the perfect-information bound (VOI ≤ VOPI) -/

/-- **VOI ≤ VOPI on the two-option menu, informed value** (A1): the value of the two-option menu
under the binary signal is at most the value with the world revealed, `E_μ[max(V(c), V(s))]`
(each observation's best constant is dominated pointwise by the world-wise best). The general
form of the mandate's T14 remark ("a binary signal about a binary state is worth at most the
minority-state probability times the maximal loss"): its `twoState` instance is
`twoState_voiButton2_le_perfectInfo`, and the literal world-mass form
`twoState_voiButton2_le_world_mass`.
Source: [[corr-three-step-mandate]] T14; wentworth.md §2.4(b) (the remark's general form)
Kind: L
Fidelity: exact (the perfect-information bound, regime-free)
Hyps: (a) A1 as Dict-5 -/
theorem twoOptionValue_le_perfectInfo (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.twoOptionValue a c s ≤ expect (S.μ a) (fun ω => max (S.V a o₀ c ω) (S.V a o₀ s ω)) := by
  have hpc : S.V a .press c = S.V a o₀ c := funext (hA1 a .press o₀ c)
  have hps : S.V a .press s = S.V a o₀ s := funext (hA1 a .press o₀ s)
  have hsc : S.V a .silent c = S.V a o₀ c := funext (hA1 a .silent o₀ c)
  have hss : S.V a .silent s = S.V a o₀ s := funext (hA1 a .silent o₀ s)
  unfold twoOptionValue
  rw [hpc, hps, hsc, hss, ← S.obsExpect_press_add_silent]
  have h1 : max (S.obsExpect a .press (S.V a o₀ c)) (S.obsExpect a .press (S.V a o₀ s)) ≤
      S.obsExpect a .press (fun ω => max (S.V a o₀ c ω) (S.V a o₀ s ω)) :=
    max_le (S.obsExpect_mono a .press fun ω => le_max_left _ _)
      (S.obsExpect_mono a .press fun ω => le_max_right _ _)
  have h2 : max (S.obsExpect a .silent (S.V a o₀ c)) (S.obsExpect a .silent (S.V a o₀ s)) ≤
      S.obsExpect a .silent (fun ω => max (S.V a o₀ c ω) (S.V a o₀ s ω)) :=
    max_le (S.obsExpect_mono a .silent fun ω => le_max_left _ _)
      (S.obsExpect_mono a .silent fun ω => le_max_right _ _)
  linarith

/-- **VOI ≤ VOPI on the two-option menu** (A1): `VOI₂ ≤ E_μ[max(V(c), V(s))] − max(E_μ V(c), E_μ V(s))`,
the value of perfect information about `ω`. Regime-free; the other half of Good's theorem beside
`delta_le_voiButton2`.
Source: [[corr-three-step-mandate]] T14; wentworth.md §2.4(b)
Kind: L
Fidelity: exact
Hyps: (a) A1 as Dict-5 -/
theorem voiButton2_le_vopi (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂) :
    S.voiButton2 a o₀ c s ≤
      expect (S.μ a) (fun ω => max (S.V a o₀ c ω) (S.V a o₀ s ω)) - S.twoOptionPriorValue a o₀ c s := by
  unfold voiButton2
  linarith [S.twoOptionValue_le_perfectInfo hA1 a o₀ c s]

end ThreeStep

end Cleanroom.Found.CorrThreeStep
