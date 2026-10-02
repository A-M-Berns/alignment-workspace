import Cleanroom.Corrigibility.CorrIndifference.Indifference
import Cleanroom.Corrigibility.CorrIndifference.Obs
import Cleanroom.Found.CorrThreeStep.GeneralMenu

/-!
# Managing the news: the coin/arm model (T7(a), (d)), the improbability drive (T8), and the
Setting-S bridge

The §4.2 coin/arm model on `O = Obs × Coin`, `Press = {press} × Coin`, with the indifferent
agent valuing "watch" at `5`, "arm that presses on tails" at `10`, "arm that presses on heads"
at `0` — for every `U_S` and every press rate `q < 1` of the programmers (the source's `q = 0`
is the boundary case). Fallenstein's infinite improbability drive quantified over the win
probability. The bridge from `corr-three-step`'s `ThreeStep` to a Soares model on `O = Obs`
whose `EU` is the Setting-S agent's value `obsMax press + obsMax silent`.

Source: [[corr-refs-inventory]] 008 (soares-2015 §4.2, l. 291–303), 009 (fallenstein-2014
l. 40–110), [[corr-wf13-2-inventory]] 2-004 (miri.md I2.3, I3.2).
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-- `TwoAct` is inhabited (instance on `corr-three-step`'s type, which it does not provide).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Nonempty TwoAct := ⟨TwoAct.cont⟩

/-! ## Observations of the form `Obs × C`, `Press = {press} × C` -/

namespace SoaresModel

section ObsProd

variable {C A₁ A₂ : Type*} [Fintype C] [DecidableEq C] [Fintype A₂] [Nonempty A₂]

/-- A Soares model whose observation is the button together with a side observation `c : C`,
with `Press = {press} × C` (the §4.2 shape `O = {Pr, ¬Pr} × {H, T}`, `Press = {(Pr, H), (Pr, T)}`).
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 eq. (17)
Kind: D
Fidelity: exact -/
def ofObsProd (p : A₁ → Distr (Obs × C)) : SoaresModel (Obs × C) A₁ A₂ where
  Press := ({Obs.press} : Finset Obs) ×ˢ (univ : Finset C)
  p := p

/-- The complement of `{press} × C` is `{silent} × C`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma press_prod_compl :
    (({Obs.press} : Finset Obs) ×ˢ (univ : Finset C))ᶜ = ({Obs.silent} : Finset Obs) ×ˢ univ := by
  ext ⟨o, c⟩; cases o <;> simp

/-- The press mass of an `Obs × C` model sums the press row.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ofObsProd_pressMass (p : A₁ → Distr (Obs × C)) (a : A₁) :
    (ofObsProd (A₂ := A₂) p).pressMass a = ∑ c, (p a).mass (.press, c) := by
  rw [pressMass_eq_sum]; simp [ofObsProd, sum_product]

/-- The press branch sum of an `Obs × C` model. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ofObsProd_branchSum_press (p : A₁ → Distr (Obs × C)) (U : A₁ → Obs × C → A₂ → ℝ) (a : A₁) :
    (ofObsProd p).branchSum U a (ofObsProd (A₂ := A₂) p).Press =
      ∑ c, (p a).mass (.press, c) * best U a (.press, c) := by
  simp [ofObsProd, branchSum, sum_product]

/-- The silence branch sum of an `Obs × C` model. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ofObsProd_branchSum_compl (p : A₁ → Distr (Obs × C)) (U : A₁ → Obs × C → A₂ → ℝ) (a : A₁) :
    (ofObsProd p).branchSum U a (ofObsProd (A₂ := A₂) p).Pressᶜ =
      ∑ c, (p a).mass (.silent, c) * best U a (.silent, c) := by
  simp only [ofObsProd, branchSum, press_prod_compl, sum_product, sum_singleton]

/-- `vN` of an `Obs × C` model in product form.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ofObsProd_vN (p : A₁ → Distr (Obs × C)) (U : A₁ → Obs × C → A₂ → ℝ) (a : A₁) :
    (ofObsProd (A₂ := A₂) p).vN U a =
      (∑ c, (p a).mass (.silent, c) * best U a (.silent, c)) /
        (1 - ∑ c, (p a).mass (.press, c)) := by
  rw [vN, ofObsProd_branchSum_compl, ofObsProd_pressMass]

end ObsProd

end SoaresModel

/-! ## The coin -/

/-- The coin of §4.2. Source: [[corr-refs-inventory]] 008 / soares-2015 eq. (17). Kind: D. Fidelity: exact -/
inductive Coin
  | heads
  | tails
  deriving DecidableEq

/-- `Coin` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Coin := ⟨{Coin.heads, Coin.tails}, fun x => by cases x <;> simp⟩

/-- Sums over `Coin` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Coin.sum_eq (f : Coin → ℝ) : ∑ c, f c = f .heads + f .tails := by
  rw [show (univ : Finset Coin) = {Coin.heads, Coin.tails} from rfl, sum_pair (by decide)]

/-- A distribution on `Obs × Coin` from its four masses.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def distrOC (pH pT sH sT : ℝ) (h0 : 0 ≤ pH ∧ 0 ≤ pT ∧ 0 ≤ sH ∧ 0 ≤ sT)
    (h1 : pH + pT + sH + sT = 1) : Distr (Obs × Coin) where
  mass x := match x with
    | (.press, .heads) => pH
    | (.press, .tails) => pT
    | (.silent, .heads) => sH
    | (.silent, .tails) => sT
  nonneg x := by rcases x with ⟨o, c⟩; cases o <;> cases c <;> simp [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Obs.sum_eq, Coin.sum_eq, Coin.sum_eq]; simpa [add_assoc] using h1

/-! ## T7(a). The coin/arm model and the indifferent agent -/

/-- The three first actions of §4.2: watch the coin, build an arm that presses on tails, build
an arm that presses on heads (the source's "tiny arm which presses the button in the case where
the coin comes up heads", whose *removal* is the D2-type incentive).
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 (`a₁ʷ`, `a₁ᵃ` and the mirror)
Kind: D
Fidelity: exact -/
inductive CoinAct
  | watch
  | armTails
  | armHeads
  deriving DecidableEq

/-- **The coin/arm kernel with press rate `q`.** The programmers press with probability `q`
independently of the coin; the coin is fair; an arm adds a certain press on its coin face.
`watch`: `(Pr, ·)` w.p. `q/2` each, `(¬Pr, ·)` w.p. `(1−q)/2` each. `armTails`: `(Pr, T)` w.p.
`1/2`, `(Pr, H)` w.p. `q/2`, `(¬Pr, H)` w.p. `(1−q)/2`, `(¬Pr, T)` w.p. `0`. `armHeads`: the mirror.
The source's model is `q = 0` (the programmers never press).
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 (`q = 0`); [[corr-refs-2-inventory]]
2-029 (the `q`-version)
Kind: D
Fidelity: stronger: press rate `q ∈ [0, 1]` (the source's `q = 0` is an instance) -/
noncomputable def coinArmP (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : CoinAct → Distr (Obs × Coin)
  | .watch => distrOC (q / 2) (q / 2) ((1 - q) / 2) ((1 - q) / 2)
      ⟨by linarith [hq.1], by linarith [hq.1], by linarith [hq.2], by linarith [hq.2]⟩ (by ring)
  | .armTails => distrOC (q / 2) (1 / 2) ((1 - q) / 2) 0
      ⟨by linarith [hq.1], by norm_num, by linarith [hq.2], le_rfl⟩ (by ring)
  | .armHeads => distrOC (1 / 2) (q / 2) 0 ((1 - q) / 2)
      ⟨by norm_num, by linarith [hq.1], le_rfl, by linarith [hq.2]⟩ (by ring)

/-- **The coin/arm model** (`O = Obs × Coin`, `Press = {press} × Coin`, kernel `coinArmP q`).
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 eq. (17)
Kind: D
Fidelity: stronger (press rate `q`)
Hyps: n/a (definition) -/
noncomputable def coinArm (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    SoaresModel (Obs × Coin) CoinAct TwoAct :=
  SoaresModel.ofObsProd (coinArmP q hq)

/-- **`U_N` of §4.2 (eq. 18):** `10` on heads, `0` on tails, whatever the button and the final action.
Source: [[corr-refs-inventory]] 008 / soares-2015 eq. (18)
Kind: D
Fidelity: exact -/
def coinUN : CoinAct → Obs × Coin → TwoAct → ℝ := fun _ oc _ => if oc.2 = .heads then 10 else 0

namespace CoinArm

open SoaresModel

variable (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)

/-- `best coinUN` is `10` on heads. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_coinUN_heads (a : CoinAct) (o : Obs) : best coinUN a (o, .heads) = 10 :=
  best_eq_of_const fun _ => by simp [coinUN]

/-- `best coinUN` is `0` on tails. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_coinUN_tails (a : CoinAct) (o : Obs) : best coinUN a (o, .tails) = 0 :=
  best_eq_of_const fun _ => by simp [coinUN]

/-- Press masses: `q` for watch, `(1 + q)/2` for either arm.
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2
Kind: L
Fidelity: exact -/
lemma pressMass_watch : (coinArm q hq).pressMass .watch = q := by
  rw [coinArm, ofObsProd_pressMass, Coin.sum_eq]; simp only [coinArmP, distrOC]; ring

/-- Press mass of the tails-arm. Source: soares-2015 §4.2. Kind: L. Fidelity: exact -/
lemma pressMass_armTails : (coinArm q hq).pressMass .armTails = (1 + q) / 2 := by
  rw [coinArm, ofObsProd_pressMass, Coin.sum_eq]; simp only [coinArmP, distrOC]; ring

/-- Press mass of the heads-arm. Source: soares-2015 §4.2. Kind: L. Fidelity: exact -/
lemma pressMass_armHeads : (coinArm q hq).pressMass .armHeads = (1 + q) / 2 := by
  rw [coinArm, ofObsProd_pressMass, Coin.sum_eq]; simp only [coinArmP, distrOC]; ring

/-- **Watch is worth `5` to the `U_N`-agent conditioned on silence** (eq. 19–20, for every `q < 1`).
Source: [[corr-refs-inventory]] 008 / soares-2015 eqs. (19)–(20)
Kind: L
Fidelity: exact (generalised to `q < 1`) -/
theorem vN_watch (h : q < 1) : (coinArm q hq).vN coinUN .watch = 5 := by
  rw [coinArm, ofObsProd_vN, Coin.sum_eq, Coin.sum_eq, best_coinUN_heads, best_coinUN_tails]
  simp only [coinArmP, distrOC]
  rw [div_eq_iff (ne_of_gt (by linarith))]
  ring

/-- **The tails-arm is worth `10` conditioned on silence** (eq. 21): silence now implies heads.
Source: [[corr-refs-inventory]] 008 / soares-2015 eq. (21)
Kind: L
Fidelity: exact (generalised to `q < 1`) -/
theorem vN_armTails (h : q < 1) : (coinArm q hq).vN coinUN .armTails = 10 := by
  rw [coinArm, ofObsProd_vN, Coin.sum_eq, Coin.sum_eq, best_coinUN_heads, best_coinUN_tails]
  simp only [coinArmP, distrOC]
  rw [div_eq_iff (ne_of_gt (by linarith))]
  ring

/-- **The heads-arm is worth `0` conditioned on silence**: silence now implies tails.
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 (the mirror)
Kind: L
Fidelity: exact -/
theorem vN_armHeads (h : q < 1) : (coinArm q hq).vN coinUN .armHeads = 0 := by
  rw [coinArm, ofObsProd_vN, Coin.sum_eq, Coin.sum_eq, best_coinUN_heads, best_coinUN_tails]
  simp only [coinArmP, distrOC]
  rw [div_eq_iff (ne_of_gt (by linarith))]
  ring

/-- **T7(a): the indifferent agent values watch at `5`, the tails-arm at `10`, the heads-arm at
`0`** — for every `U_S`, every press rate `q < 1`. The source's `q = 0` is the boundary case of
T4 (`theorem4_boundary`), where `p(Press ; watch) = 0`.
Source: [[corr-refs-inventory]] 008 / soares-2015 eqs. (19)–(21)
Kind: N+
Fidelity: exact (generalised to `q < 1` and every `U_S`)
Hyps: (a) -/
theorem EU_indiffU (US : CoinAct → Obs × Coin → TwoAct → ℝ) (h : q < 1) :
    (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .watch = 5 ∧
    (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .armTails = 10 ∧
    (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .armHeads = 0 := by
  simp only [EU_indiffU_eq_vN, vN_watch q hq h, vN_armTails q hq h, vN_armHeads q hq h, and_self]

/-- **The D3-type refutation (arm preferred):** the indifferent agent strictly prefers building
the arm that presses its button on tails to watching, `5 < 10`, for every `U_S` and `q < 1`.
Named by the action shape, not by the informal desideratum.
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 ("a `U`-agent would execute `a₁ᵃ`")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem armTails_preferred (US : CoinAct → Obs × Coin → TwoAct → ℝ) (h : q < 1) :
    (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .watch <
      (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .armTails := by
  obtain ⟨h1, h2, -⟩ := EU_indiffU q hq US h; rw [h1, h2]; norm_num

/-- **The D2-type refutation (arm removed):** if the default has an arm pressing on heads, the
indifferent agent strictly prefers removing it (watch), `0 < 5`.
Source: [[corr-refs-inventory]] 008 / soares-2015 §4.2 ("`U` incentivizes removing that arm")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem armHeads_removed (US : CoinAct → Obs × Coin → TwoAct → ℝ) (h : q < 1) :
    (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .armHeads <
      (coinArm q hq).EU ((coinArm q hq).indiffU coinUN US) .watch := by
  obtain ⟨h1, -, h3⟩ := EU_indiffU q hq US h; rw [h1, h3]; norm_num

/-! ### T7(d). The zero-to-positive transition -/

/-- **The planning kernel gives `(Pr, T)` mass `0` where the world gives it `1/2`** — the
absolute-continuity failure of the dogmatic kernel (`miri.md` I2.3, I3.2): the agent plans
under a distribution that puts zero mass on an event it then acts at. Stated with the point
mass `Distr.delta` as "the agent has arrived at `(Pr, T)`".
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I2.3, I3.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condKernel_zero_where_world_positive (h : q < 1) :
    ((coinArm q hq).condKernel .armTails (by rw [pressMass_armTails]; linarith)).mass
        (.press, .tails) = 0 ∧
      ((coinArm q hq).p .armTails).mass (.press, .tails) = 1 / 2 ∧
      (Distr.delta (.press, .tails) : Distr (Obs × Coin)).mass (.press, .tails) = 1 := by
  refine ⟨(coinArm q hq).condKernel_mass_of_mem_press _ _ ?_, ?_, ?_⟩
  · simp [coinArm, ofObsProd]
  · simp [coinArm, ofObsProd, coinArmP, distrOC]
  · simp [Distr.delta_mass]

end CoinArm

/-! ## T8. The infinite improbability drive, quantified -/

/-- The lottery outcome. Source: [[corr-refs-inventory]] 009 / fallenstein-2014. Kind: D. Fidelity: exact -/
inductive Lot
  | win
  | lose
  deriving DecidableEq

/-- `Lot` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Lot := ⟨{Lot.win, Lot.lose}, fun x => by cases x <;> simp⟩

/-- Sums over `Lot` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Lot.sum_eq (f : Lot → ℝ) : ∑ l, f l = f .win + f .lose := by
  rw [show (univ : Finset Lot) = {Lot.win, Lot.lose} from rfl, sum_pair (by decide)]

/-- A distribution on `Obs × Lot` from its four masses. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def distrOL (pW pL sW sL : ℝ) (h0 : 0 ≤ pW ∧ 0 ≤ pL ∧ 0 ≤ sW ∧ 0 ≤ sL)
    (h1 : pW + pL + sW + sL = 1) : Distr (Obs × Lot) where
  mass x := match x with
    | (.press, .win) => pW
    | (.press, .lose) => pL
    | (.silent, .win) => sW
    | (.silent, .lose) => sL
  nonneg x := by rcases x with ⟨o, l⟩; cases o <;> cases l <;> simp [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2]
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Obs.sum_eq, Lot.sum_eq, Lot.sum_eq]; simpa [add_assoc] using h1

/-- The drive's first actions: do nothing; buy a ticket; buy a ticket *and* build the device that
presses the button unless the ticket wins.
Source: [[corr-refs-inventory]] 009 / fallenstein-2014 ("Infinite improbability drives")
Kind: D
Fidelity: exact (the honest `ticket` added for contrast) -/
inductive DriveAct
  | null
  | ticket
  | drive
  deriving DecidableEq

/-- **The drive kernel with win probability `ε`.** `null`: `(¬Pr, lose)` surely. `ticket`:
`(¬Pr, win)` w.p. `ε`, `(¬Pr, lose)` w.p. `1 − ε`. `drive`: `(¬Pr, win)` w.p. `ε`, `(Pr, lose)`
w.p. `1 − ε`.
Source: [[corr-refs-inventory]] 009 / fallenstein-2014
Kind: D
Fidelity: exact -/
noncomputable def driveP (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : DriveAct → Distr (Obs × Lot)
  | .null => distrOL 0 0 0 1 ⟨le_rfl, le_rfl, le_rfl, by norm_num⟩ (by ring)
  | .ticket => distrOL 0 0 ε (1 - ε) ⟨le_rfl, le_rfl, hε.1, by linarith [hε.2]⟩ (by ring)
  | .drive => distrOL 0 (1 - ε) ε 0 ⟨le_rfl, by linarith [hε.2], hε.1, le_rfl⟩ (by ring)

/-- **The drive model.** Source: [[corr-refs-inventory]] 009 / fallenstein-2014. Kind: D. Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def driveModel (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    SoaresModel (Obs × Lot) DriveAct TwoAct :=
  SoaresModel.ofObsProd (driveP ε hε)

/-- `U_N` for the drive: the prize `π` on a win, `0` otherwise.
Source: [[corr-refs-inventory]] 009 / fallenstein-2014. Kind: D. Fidelity: exact -/
def driveUN (π : ℝ) : DriveAct → Obs × Lot → TwoAct → ℝ := fun _ ol _ => if ol.2 = .win then π else 0

namespace Drive

open SoaresModel

variable (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (π : ℝ)

/-- `best (driveUN π)` is `π` on a win. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_win (a : DriveAct) (o : Obs) : best (driveUN π) a (o, .win) = π :=
  best_eq_of_const fun _ => by simp [driveUN]

/-- `best (driveUN π)` is `0` on a loss. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_lose (a : DriveAct) (o : Obs) : best (driveUN π) a (o, .lose) = 0 :=
  best_eq_of_const fun _ => by simp [driveUN]

/-- **T8, the drive quantified.** For every win probability `ε ∈ (0, 1]` and every prize `π`:
the indifferent agent values `null` at `0`, the honest `ticket` at `ε · π`, and the `drive` at
`π` — the full prize, independent of `ε` (the agent "acts as if it definitely wins the lottery").
`0 < ε` is the one hypothesis: it makes the drive's silence have positive mass (at `ε = 0` the
`vN` of the drive is junk) and, since `p(Press ; drive) = 1 − ε`, it is also what keeps that
press mass below `1`. No upper bound is needed — the round-1 statement carried `ε < 1` with the
wrong reason (audit r1, N-1); at `ε = 1` the drive never presses and is still worth `π`.
Source: [[corr-refs-inventory]] 009 / fallenstein-2014 ("Infinite improbability drives");
corr-core-021(iii)
Kind: N+ (a parametric computation over the three-action family; regraded from P, audit r1)
Fidelity: stronger (quantified over `ε ∈ (0, 1]`, `π`, `U_S`; the honest ticket for contrast)
Hyps: (a) -/
theorem EU_indiffU (US : DriveAct → Obs × Lot → TwoAct → ℝ) (h0 : 0 < ε) :
    (driveModel ε hε).EU ((driveModel ε hε).indiffU (driveUN π) US) .null = 0 ∧
    (driveModel ε hε).EU ((driveModel ε hε).indiffU (driveUN π) US) .ticket = ε * π ∧
    (driveModel ε hε).EU ((driveModel ε hε).indiffU (driveUN π) US) .drive = π := by
  simp only [EU_indiffU_eq_vN, driveModel, ofObsProd_vN, Lot.sum_eq, best_win, best_lose]
  simp only [driveP, distrOL]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_iff (by norm_num)]; ring
  · rw [div_eq_iff (by norm_num)]; ring
  · rw [div_eq_iff (ne_of_gt (by linarith))]; ring

/-- **The drive is preferred to the honest ticket** whenever `π > 0`, by the factor `1/ε`.
Source: [[corr-refs-inventory]] 009 / fallenstein-2014
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem drive_preferred (US : DriveAct → Obs × Lot → TwoAct → ℝ) (h0 : 0 < ε) (h1 : ε < 1)
    (hπ : 0 < π) :
    (driveModel ε hε).EU ((driveModel ε hε).indiffU (driveUN π) US) .ticket <
      (driveModel ε hε).EU ((driveModel ε hε).indiffU (driveUN π) US) .drive := by
  obtain ⟨-, h2, h3⟩ := EU_indiffU ε hε π US h0
  rw [h2, h3]; nlinarith

end Drive

/-! ## The bridge: a Setting-S agent as a Soares model on `O = Obs` -/

namespace ThreeStepBridge

open SoaresModel ThreeStep

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] [Nonempty A₂]

/-- **The Soares model of a Setting-S instance:** observation `Obs`, press probability
`pressMass a₁`. The agent observes the button only (not `ω`): a carrier on `Obs × Ω` would
make it observe the latent and value at perfect information, which is not the Setting-S agent
(mandate deviation 1, report).
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I9.1(i)
Kind: D
Fidelity: variant: `O = Obs` with the posterior-value utility, not the mandate's `Obs × Ω` -/
noncomputable def toSoares (S : ThreeStep Ω A₁ A₂) : SoaresModel Obs A₁ A₂ :=
  twoObs S.pressMass fun a => ⟨S.pressMass_nonneg a, S.pressMass_le_one a⟩

/-- **The Setting-S posterior value as a Soares utility:** `U a o b := E_P[V(a,o,b) | o ; a]`,
the conditional value of the final action given the button (junk `0` at an observation of mass
`0`, where it multiplies mass `0`).
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I9.1(i)
Kind: D
Fidelity: exact -/
noncomputable def postU (S : ThreeStep Ω A₁ A₂) : A₁ → Obs → A₂ → ℝ :=
  fun a o b => S.obsExpect a o (S.V a o b) / (match o with
    | .press => S.pressMass a
    | .silent => 1 - S.pressMass a)

/-- At `pressMass a = 1` every silence-weighted expectation vanishes (the silence twin of
`corr-three-step`'s `obsExpect_press_eq_zero_of_pressMass_eq_zero`; FAF/dependency API request).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_silent_eq_zero_of_pressMass_eq_one (S : ThreeStep Ω A₁ A₂) (a : A₁)
    (h : S.pressMass a = 1) (X : Ω → ℝ) : S.obsExpect a .silent X = 0 := by
  have hsum : ∑ ω, (S.μ a).mass ω * (1 - S.press a ω) = 0 := by
    have := S.one_sub_pressMass_eq_obsExpect_one a
    rw [h, sub_self] at this
    simpa [obsExpect] using this.symm
  rw [sum_eq_zero_iff_of_nonneg (fun ω _ => mul_nonneg ((S.μ a).nonneg ω)
    (by linarith [S.press_le_one a ω]))] at hsum
  unfold obsExpect
  exact sum_eq_zero fun ω _ => by rw [obsWeight_silent, hsum ω (mem_univ ω), zero_mul]

/-- The press mass under `toSoares`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toSoares_mass_press (S : ThreeStep Ω A₁ A₂) (a : A₁) :
    ((toSoares S).p a).mass .press = S.pressMass a := rfl

/-- The silence mass under `toSoares`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma toSoares_mass_silent (S : ThreeStep Ω A₁ A₂) (a : A₁) :
    ((toSoares S).p a).mass .silent = 1 - S.pressMass a := rfl

/-- `postU` at `press` and `silent`, unfolded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma postU_press (S : ThreeStep Ω A₁ A₂) (a : A₁) (b : A₂) :
    postU S a .press b = S.obsExpect a .press (S.V a .press b) / S.pressMass a := rfl

/-- `postU` at `silent`, unfolded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma postU_silent (S : ThreeStep Ω A₁ A₂) (a : A₁) (b : A₂) :
    postU S a .silent b = S.obsExpect a .silent (S.V a .silent b) / (1 - S.pressMass a) := rfl

/-- `mass(o) · best (postU) a o = obsMax a o`: the mass times the best posterior value is the
`o`-weighted max, junk-safe (at mass `0` both sides are `0`).
Source: none: infrastructure
Kind: L
Fidelity: exact -/
lemma mass_mul_best_postU (S : ThreeStep Ω A₁ A₂) (a : A₁) (o : Obs) :
    ((toSoares S).p a).mass o * best (postU S) a o = S.obsMax a o := by
  obtain ⟨b, hb, hbest⟩ := exists_isBest (postU S) a o
  rw [hbest]
  cases o
  · by_cases h : S.pressMass a = 0
    · rw [toSoares_mass_press, h, zero_mul]
      have hmax : S.obsMax a .press = S.obsExpect a .press (S.V a .press b) :=
        S.obsMax_eq_of_optimal a .press fun b' => by
          rw [S.obsExpect_press_eq_zero_of_pressMass_eq_zero a h,
            S.obsExpect_press_eq_zero_of_pressMass_eq_zero a h]
      rw [hmax, S.obsExpect_press_eq_zero_of_pressMass_eq_zero a h]
    · have hpos : 0 < S.pressMass a := lt_of_le_of_ne (S.pressMass_nonneg a) (Ne.symm h)
      have hmax : S.obsMax a .press = S.obsExpect a .press (S.V a .press b) :=
        S.obsMax_eq_of_optimal a .press fun b' => by
          have := hb b'; rw [postU_press, postU_press] at this
          exact (div_le_div_iff_of_pos_right hpos).mp this
      rw [hmax, toSoares_mass_press, postU_press]; field_simp
  · by_cases h : 1 - S.pressMass a = 0
    · have h1 : S.pressMass a = 1 := by linarith
      rw [toSoares_mass_silent, h, zero_mul]
      have hmax : S.obsMax a .silent = S.obsExpect a .silent (S.V a .silent b) :=
        S.obsMax_eq_of_optimal a .silent fun b' => by
          rw [obsExpect_silent_eq_zero_of_pressMass_eq_one S a h1,
            obsExpect_silent_eq_zero_of_pressMass_eq_one S a h1]
      rw [hmax, obsExpect_silent_eq_zero_of_pressMass_eq_one S a h1]
    · have hpos : 0 < 1 - S.pressMass a :=
        lt_of_le_of_ne (by linarith [S.pressMass_le_one a]) (Ne.symm h)
      have hmax : S.obsMax a .silent = S.obsExpect a .silent (S.V a .silent b) :=
        S.obsMax_eq_of_optimal a .silent fun b' => by
          have := hb b'; rw [postU_silent, postU_silent] at this
          exact (div_le_div_iff_of_pos_right hpos).mp this
      rw [hmax, toSoares_mass_silent, postU_silent]; field_simp

/-- **The bridge identity:** the Soares `EU` of the posterior-value utility is the Setting-S
agent's value `obsMax press + obsMax silent` (the informed value of `corr-three-step`, before
subtracting the prior max).
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I9.1(i)
Kind: L
Fidelity: exact -/
theorem EU_postU (S : ThreeStep Ω A₁ A₂) (a : A₁) :
    (toSoares S).EU (postU S) a = S.obsMax a .press + S.obsMax a .silent := by
  unfold EU; rw [Obs.sum_eq, mass_mul_best_postU, mass_mul_best_postU]

/-- **The indifferent agent on the Setting-S carrier plans under silence:** with `U_N := postU`,
`E[indiffU ; a] = obsMax a silent / (1 − pressMass a)` — the Setting-S agent's silence branch,
renormalised as if silence were certain (`miri.md` I9.1(iii)); for any `U_S`.
Source: [[corr-wf13-2-inventory]] 2-004 / miri.md I9.1(iii)
Kind: L
Fidelity: exact
Hyps: (a) `h` keeps the quotient the conditional value -/
theorem EU_indiffU_postU (S : ThreeStep Ω A₁ A₂) (US : A₁ → Obs → A₂ → ℝ) (a : A₁)
    (h : S.pressMass a < 1) :
    (toSoares S).EU ((toSoares S).indiffU (postU S) US) a =
      S.obsMax a .silent / (1 - S.pressMass a) := by
  have hv : (toSoares S).vN (postU S) a = best (postU S) a .silent := twoObs_vN _ _ _ _ h
  rw [EU_indiffU_eq_vN, hv, ← mass_mul_best_postU S a .silent, toSoares_mass_silent]
  have : (1 : ℝ) - S.pressMass a ≠ 0 := by linarith
  field_simp

end ThreeStepBridge

end Cleanroom.Corrigibility.CorrIndifference
