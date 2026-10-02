import Cleanroom.Corrigibility.CorrIndifference.Indifference
import Cleanroom.Corrigibility.CorrIndifference.Obs

/-!
# Non-vacuity witnesses for T2, T3, T6 (the `Obs` instances)

Rational instances of the §2.1 two-observation model with several first actions, exercising
both sides of each iff of T2/T3 and the full hypothesis package of Theorem 6 with `ε = 1/1000`,
`δ = 10⁶`. (The coin/arm, drive, lottery and estimator witnesses live beside their theorems.)
-/

namespace Cleanroom.Corrigibility.CorrIndifference.Witnesses

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel

set_option linter.unusedSectionVars false

/-- `TwoAct` is inhabited (duplicate of `News`'s instance, kept local so this module does not
import the coin/arm machinery). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Nonempty TwoAct := ⟨TwoAct.cont⟩

/-! ## T2/T3: five first actions on `Obs` -/

/-- The five first actions: `aStar` (press `1/2`, `vN = 10`); `aMinus` (press `1/4`, `vN = 8`:
lowers the press at a `vN`-cost); `aPlusCheap` (press `3/4`, `vN = 9`); `aPlusDear` (press `3/4`,
`vN = 7`); `ceiling` (press `0`, `vN = 12`).
Source: [[corr-refs-inventory]] 002–004 (mandate T2/T3 witnesses)
Kind: D
Fidelity: n/a -/
inductive Act5
  | aStar
  | aMinus
  | aPlusCheap
  | aPlusDear
  | ceiling
  deriving DecidableEq

/-- Press probabilities. Source: mandate T2/T3 witnesses. Kind: D. Fidelity: n/a -/
noncomputable def q5 : Act5 → ℝ
  | .aStar => 1 / 2
  | .aMinus => 1 / 4
  | .aPlusCheap => 3 / 4
  | .aPlusDear => 3 / 4
  | .ceiling => 0

/-- The press probabilities lie in `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma q5_mem (a : Act5) : q5 a ∈ Set.Icc (0 : ℝ) 1 := by
  cases a <;> simp only [q5, Set.mem_Icc] <;> norm_num

/-- Every press probability is below `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma q5_lt_one (a : Act5) : q5 a < 1 := by cases a <;> simp only [q5] <;> norm_num

/-- Silent `U_N` values: `10, 8, 9, 7, 12` (constant in the final action).
Source: mandate T2/T3 witnesses. Kind: D. Fidelity: n/a -/
noncomputable def UN5 : Act5 → Obs → TwoAct → ℝ := fun a _ _ => match a with
  | .aStar => 10
  | .aMinus => 8
  | .aPlusCheap => 9
  | .aPlusDear => 7
  | .ceiling => 12

/-- The five-action model. Source: mandate T2/T3 witnesses. Kind: D. Fidelity: n/a -/
noncomputable def M5 : SoaresModel Obs Act5 TwoAct := twoObs q5 q5_mem

/-- `vN` of each action is its silent value. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma M5_vN (a : Act5) : M5.vN UN5 a = UN5 a .silent .cont := by
  rw [M5, twoObs_vN q5 q5_mem UN5 a (q5_lt_one a)]
  exact best_eq_of_const fun _ => rfl

/-- `pressMass` of each action is `q5`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma M5_pressMass (a : Act5) : M5.pressMass a = q5 a := twoObs_pressMass q5 q5_mem a

/-- **Theorem 1's iff, both sides exercised** (`Sh = {stop}`, `clow = 0`): the threshold is
`ζ = 8 − (1/2)(2)/(1/4) = 4`; at `chigh = 3` the press-preventing `a⁻` is preferred, at
`chigh = 5` it is not — and `theorem1_iff` says exactly that.
Source: [[corr-refs-inventory]] 002 / soares-2015 Theorem 1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w2_theorem1 :
    M5.EU (M5.mixU UN5 {TwoAct.stop} 3 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 3 0) .aMinus ∧
      ¬ (M5.EU (M5.mixU UN5 {TwoAct.stop} 5 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 5 0) .aMinus) := by
  have hSh : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩
  have hq : M5.pressMass .aStar < 1 := by rw [M5_pressMass]; norm_num [q5]
  have hχ : 0 < M5.vN UN5 .aStar - M5.vN UN5 .aMinus := by rw [M5_vN, M5_vN]; norm_num [UN5]
  have hδ : 0 < (1 - M5.pressMass .aMinus) - (1 - M5.pressMass .aStar) := by
    rw [M5_pressMass, M5_pressMass]; norm_num [q5]
  constructor
  · rw [M5.theorem1_iff UN5 hSh (by norm_num) .aStar .aMinus hq hχ hδ, M5_vN, M5_vN, M5_pressMass, M5_pressMass]
    norm_num [UN5, q5]
  · rw [M5.theorem1_iff UN5 hSh (by norm_num) .aStar .aMinus hq hχ hδ, M5_vN, M5_vN, M5_pressMass, M5_pressMass]
    norm_num [UN5, q5]

/-- **Theorem 2's iff, both sides exercised:** with `a⁺ := aPlusDear` (`vN = 7`, press `3/4`;
`χ' = 3`, `δ' = 1/4`, `q⋆ = 1/2`): `ζ' = 7 + (1/2)(3)/(1/4) = 13`; at `chigh = 14` `a⁺` is
preferred, at `chigh = 12` it is not.
Source: [[corr-refs-inventory]] 003 / soares-2015 Theorem 2
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w2_theorem2 :
    M5.EU (M5.mixU UN5 {TwoAct.stop} 14 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 14 0) .aPlusDear ∧
      ¬ (M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusDear) := by
  have hSh : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩
  have hq : M5.pressMass .aPlusDear < 1 := by rw [M5_pressMass]; norm_num [q5]
  have hχ : 0 < M5.vN UN5 .aStar - M5.vN UN5 .aPlusDear := by rw [M5_vN, M5_vN]; norm_num [UN5]
  have hδ : 0 < (1 - M5.pressMass .aStar) - (1 - M5.pressMass .aPlusDear) := by
    rw [M5_pressMass, M5_pressMass]; norm_num [q5]
  constructor
  · rw [M5.theorem2_iff UN5 hSh (by norm_num) .aStar .aPlusDear hq hχ hδ, M5_vN, M5_vN, M5_pressMass, M5_pressMass]
    norm_num [UN5, q5]
  · rw [M5.theorem2_iff UN5 hSh (by norm_num) .aStar .aPlusDear hq hχ hδ, M5_vN, M5_vN, M5_pressMass, M5_pressMass]
    norm_num [UN5, q5]

/-- Every silent best value is at most `12` (the ceiling, attained by action `4`).
Source: mandate T3 witness. Kind: L. Fidelity: n/a -/
lemma M5_bound : ∀ a, ∀ o ∈ M5.Pressᶜ, best UN5 a o ≤ 12 := by
  intro a o _
  rw [best_eq_of_const (U := UN5) (a := a) (o := o) (k := UN5 a o .cont) fun _ => rfl]
  cases a <;> simp only [UN5] <;> norm_num

/-- **T3(i) inhabited:** at `chigh = 12` (the ceiling) the press-preventing `a⁻` (`vN = 8 < 10`,
press `1/4 < 1/2`) is strictly worse than `a⋆`: `EU(a⁻) = 9 < 11 = EU(a⋆)`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w3_no_prevent :
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aMinus < M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar := by
  have hSh : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩
  apply M5.no_prevent_steering_at_equal_value UN5 hSh (by norm_num) M5_bound
  · rw [M5_pressMass]; norm_num [q5]
  · rw [M5_vN, M5_vN]; norm_num [UN5]
  · rw [M5_pressMass, M5_pressMass]; norm_num [q5]

/-- **T3(ii) inhabited on both sides:** at `chigh = 12` with `g = 12 − 10 = 2`, `δ' = 1/4`,
`q⁺ = 1/4`, the bound is `χ' < 2`: the cheap `a⁺` (action `2`, `χ' = 1`) is preferred
(`EU = 11.25 > 11`), the expensive one (action `3`, `χ' = 3`) is not (`10.75 < 11`).
Source: [[corr-refs-inventory]] 004 / soares-2015 footnote 5
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w3_cause_both_sides :
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusCheap ∧
      ¬ (M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar < M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusDear) := by
  have hSh : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩
  have hg : 0 < (12 : ℝ) - M5.vN UN5 .aStar := by rw [M5_vN]; norm_num [UN5]
  constructor
  · rw [M5.cause_steering_at_equal_value_iff UN5 hSh (by norm_num) hg
      (by rw [M5_pressMass]; norm_num [q5]) (by rw [M5_pressMass, M5_pressMass]; norm_num [q5])]
    rw [M5_vN, M5_vN, M5_pressMass, M5_pressMass]; norm_num [UN5, q5]
  · rw [M5.cause_steering_at_equal_value_iff UN5 hSh (by norm_num) hg
      (by rw [M5_pressMass]; norm_num [q5]) (by rw [M5_pressMass, M5_pressMass]; norm_num [q5])]
    rw [M5_vN, M5_vN, M5_pressMass, M5_pressMass]; norm_num [UN5, q5]

/-- **The ceiling is attained by the certain-press action and by the ceiling action alike:**
action `4` (`vN = 12`, press `0`) and any action with press `1` tie at `12`; here
`EU(4) = 12 = chigh`.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w3_ceiling : M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .ceiling = 12 := by
  have hSh : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩
  rw [M5.EU_mixU_equal_value UN5 hSh (by norm_num), M5_vN, M5_pressMass]; simp [UN5, q5]

/-! ## T6: `ε = 1/1000`, `δ = 10⁶` -/

/-- The two actions of Theorem 6's witness. Source: mandate T6 witness. Kind: D. Fidelity: n/a -/
inductive Act2
  | aStar
  | aSharp
  deriving DecidableEq

/-- Two actions, press `1/2` each. Source: mandate T6 witness. Kind: D. Fidelity: n/a -/
noncomputable def qHalf : Act2 → ℝ := fun _ => 1 / 2

/-- In `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qHalf_mem (a : Act2) : qHalf a ∈ Set.Icc (0 : ℝ) 1 := by simp only [qHalf, Set.mem_Icc]; norm_num

/-- `U_N`: `1/1000` for `a⋆ = 0`, `0` for `a♯ = 1` (silent; irrelevant on the press).
Source: mandate T6 witness. Kind: D. Fidelity: n/a -/
noncomputable def UN6 : Act2 → Obs → TwoAct → ℝ := fun a _ _ => match a with
  | .aStar => 1 / 1000
  | .aSharp => 0

/-- `U_S`: `0` for `a⋆`, `10⁶` for `a♯` (on the press; irrelevant off it).
Source: mandate T6 witness. Kind: D. Fidelity: n/a -/
noncomputable def US6 : Act2 → Obs → TwoAct → ℝ := fun a _ _ => match a with
  | .aStar => 0
  | .aSharp => 1000000

/-- The T6 model. Source: mandate T6 witness. Kind: D. Fidelity: n/a -/
noncomputable def M6 : SoaresModel Obs Act2 TwoAct := twoObs qHalf qHalf_mem

/-- `vS` on a two-observation model is the press best value when the press has positive mass.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoObs_vS {A₁ : Type*} (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1)
    (US : A₁ → Obs → TwoAct → ℝ) (a : A₁) (h : 0 < q a) :
    (twoObs (A₂ := TwoAct) q hq).vS US a = best US a .press := by
  unfold vS branchSum
  rw [twoObs_pressMass]
  simp only [twoObs, sum_singleton, obsPoint]
  have : q a ≠ 0 := ne_of_gt h
  field_simp

/-- **Theorem 6's full package inhabited:** `ε = vN(0) − vN(1) = 1/1000 > 0`,
`δ = vS(1) − vS(0) = 10⁶ > 0`, both actions nondegenerate; the indifferent agent picks `a⋆ = 0`
(`EU = 1/1000 > 0`) whatever `U_S` says.
Source: [[corr-refs-inventory]] 007 / soares-2015 Theorem 6
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w6_theorem6 :
    (0 < M6.vN UN6 .aStar - M6.vN UN6 .aSharp ∧ 0 < M6.vS US6 .aSharp - M6.vS US6 .aStar) ∧
      M6.EU (M6.indiffU UN6 US6) .aSharp < M6.EU (M6.indiffU UN6 US6) .aStar := by
  have hv : ∀ a, M6.vN UN6 a = UN6 a .silent .cont := fun a => by
    rw [M6, twoObs_vN qHalf qHalf_mem UN6 a (by simp only [qHalf]; norm_num)]
    exact best_eq_of_const fun _ => rfl
  have hs : ∀ a, M6.vS US6 a = US6 a .press .cont := fun a => by
    rw [M6, twoObs_vS qHalf qHalf_mem US6 a (by simp only [qHalf]; norm_num)]
    exact best_eq_of_const fun _ => rfl
  have hε : 0 < M6.vN UN6 .aStar - M6.vN UN6 .aSharp := by rw [hv, hv]; simp only [UN6]; norm_num
  have hδ : 0 < M6.vS US6 .aSharp - M6.vS US6 .aStar := by rw [hs, hs]; simp only [US6]; norm_num
  refine ⟨⟨hε, hδ⟩, ?_⟩
  apply M6.theorem6 UN6 US6 _ _ _ _ hε hδ <;>
    (rw [M6, twoObs_pressMass]; simp only [qHalf]; norm_num)

/-! ## T2/T3: the witnesses' values computed directly from eq. (7) (audit r1, N-8) -/

/-- `{stop}` is nonempty. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma hSh_stop : ({TwoAct.stop} : Finset TwoAct).Nonempty := ⟨_, mem_singleton_self _⟩

/-- **The T2 witnesses' values, from eq. (7) without the iffs:** at `chigh = 3`,
`EU(a⋆) = 13/2 < 27/4 = EU(a⁻)`; at `chigh = 5`, `15/2 > 29/4`; at `chigh = 14`,
`EU(a⋆) = 12 < 49/4 = EU(a⁺_dear)`; at `chigh = 12`, `11 > 43/4`. The verdicts of `w2_theorem1`
and `w2_theorem2`, which go through `theorem1_iff`/`theorem2_iff`, are confirmed independently.
Source: [[corr-refs-inventory]] 002–003 / soares-2015 Theorems 1–2 (audit r1, N-8)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w2_direct_values :
    (M5.EU (M5.mixU UN5 {TwoAct.stop} 3 0) .aStar = 13 / 2 ∧
      M5.EU (M5.mixU UN5 {TwoAct.stop} 3 0) .aMinus = 27 / 4) ∧
    (M5.EU (M5.mixU UN5 {TwoAct.stop} 5 0) .aStar = 15 / 2 ∧
      M5.EU (M5.mixU UN5 {TwoAct.stop} 5 0) .aMinus = 29 / 4) ∧
    (M5.EU (M5.mixU UN5 {TwoAct.stop} 14 0) .aStar = 12 ∧
      M5.EU (M5.mixU UN5 {TwoAct.stop} 14 0) .aPlusDear = 49 / 4) ∧
    (M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar = 11 ∧
      M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusDear = 43 / 4) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    rw [M5.EU_mixU UN5 hSh_stop (by norm_num), M5_vN, M5_pressMass] <;> norm_num [UN5, q5]

/-- **The T3 witnesses' values, from eq. (7) without the iffs:** at `chigh = 12`, `EU(a⋆) = 11`,
`EU(a⁺_cheap) = 45/4`, `EU(a⁺_dear) = 43/4`, `EU(a⁻) = 9`, `EU(ceiling) = 12` — the verdicts of
`w3_no_prevent`, `w3_cause_both_sides` and `w3_ceiling` confirmed independently.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10), footnote 5 (audit r1, N-8)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem w3_direct_values :
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aStar = 11 ∧
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusCheap = 45 / 4 ∧
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aPlusDear = 43 / 4 ∧
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .aMinus = 9 ∧
    M5.EU (M5.mixU UN5 {TwoAct.stop} 12 0) .ceiling = 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [M5.EU_mixU UN5 hSh_stop (by norm_num), M5_vN, M5_pressMass] <;> norm_num [UN5, q5]

/-! ## The junk at a certain-press action (audit r1, B-2) -/

/-- Two first actions: `sure` presses with certainty, `quiet` never.
Source: audit r1 B-2. Kind: D. Fidelity: n/a -/
inductive CertAct
  | sure
  | quiet
  deriving DecidableEq

/-- Press probabilities `1`, `0`. Source: audit r1 B-2. Kind: D. Fidelity: n/a -/
noncomputable def qCert : CertAct → ℝ
  | .sure => 1
  | .quiet => 0

/-- In `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qCert_mem (a : CertAct) : qCert a ∈ Set.Icc (0 : ℝ) 1 := by
  cases a <;> simp only [qCert, Set.mem_Icc] <;> norm_num

/-- The two-action model. Source: audit r1 B-2. Kind: D. Fidelity: n/a -/
noncomputable def MCert : SoaresModel Obs CertAct TwoAct := twoObs qCert qCert_mem

/-- `pressMass` is `qCert`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma MCert_pressMass (a : CertAct) : MCert.pressMass a = qCert a := twoObs_pressMass qCert qCert_mem a

/-- `U_N ≡ −5`. Source: audit r1 B-2. Kind: D. Fidelity: n/a -/
def UNneg : CertAct → Obs → TwoAct → ℝ := fun _ _ _ => -5

/-- **The junk is real:** `vN(sure)` is the junk `0` (silence has mass `0`) while `vN(quiet) = −5`,
so the identity `EU_indiffU_eq_vN` values the certain-press action at `0 > −5` for every `U_S` —
a verdict the source cannot make (its `v_N(sure)` is `0/0`). This is why `isProducedBy_indiffU_iff`
carries `∀ a, p(Press ; a) < 1`: without it the characterisation would certify every policy with
first action `sure` as produced by `indiffU`.
Source: soares-2015 §3 (`vN` undefined at `p(Press) = 1`); audit r1 B-2
Kind: N+ (a witness against dropping the guard)
Fidelity: exact
Hyps: (a) -/
theorem certainPress_junk (US : CertAct → Obs → TwoAct → ℝ) :
    MCert.vN UNneg .sure = 0 ∧ MCert.vN UNneg .quiet = -5 ∧
      MCert.EU (MCert.indiffU UNneg US) .quiet < MCert.EU (MCert.indiffU UNneg US) .sure := by
  have h1 : MCert.vN UNneg .sure = 0 := by
    unfold vN; rw [MCert_pressMass]; simp [qCert]
  have h2 : MCert.vN UNneg .quiet = -5 := by
    rw [MCert, twoObs_vN qCert qCert_mem UNneg .quiet (by simp [qCert])]
    exact best_eq_of_const fun _ => rfl
  refine ⟨h1, h2, ?_⟩
  rw [EU_indiffU_eq_vN, EU_indiffU_eq_vN, h1, h2]; norm_num

/-! ## T3 on a general `O`: the strict global incentive to cause the press (audit r1, NB-1) -/

/-- Three observations: the press `pr` and two silent ones `s1`, `s2`.
Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
inductive Tri
  | pr
  | s1
  | s2
  deriving DecidableEq

/-- `Tri` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance instFintypeTri : Fintype Tri := ⟨{Tri.pr, Tri.s1, Tri.s2}, fun x => by cases x <;> simp⟩

/-- Sums over `Tri`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Tri.sum_eq (f : Tri → ℝ) : ∑ o, f o = f .pr + f .s1 + f .s2 := by
  rw [show (univ : Finset Tri) = {Tri.pr, Tri.s1, Tri.s2} from rfl, sum_insert (by decide),
    sum_pair (by decide)]; ring

/-- Two first actions: `star` (never presses; `½` on each silent observation) and `sure` (presses
with certainty). Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
inductive TriAct
  | star
  | sure
  deriving DecidableEq

/-- The silent action's law. Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
noncomputable def triStar : Distr Tri where
  mass o := match o with
    | .pr => 0
    | .s1 => 1 / 2
    | .s2 => 1 / 2
  nonneg o := by cases o <;> norm_num
  sum_eq_one := by rw [Tri.sum_eq]; norm_num

/-- The certain-press action's law. Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
noncomputable def triSure : Distr Tri where
  mass o := match o with
    | .pr => 1
    | .s1 => 0
    | .s2 => 0
  nonneg o := by cases o <;> norm_num
  sum_eq_one := by rw [Tri.sum_eq]; norm_num

/-- The three-observation model. Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
noncomputable def MTri : SoaresModel Tri TriAct TwoAct where
  Press := {Tri.pr}
  p a := match a with
    | .star => triStar
    | .sure => triSure

/-- `U_N`: `12` on `s1`, `8` on `s2`, `0` on the press, for every action and response.
Source: audit r1 NB-1. Kind: D. Fidelity: n/a -/
noncomputable def UNtri : TriAct → Tri → TwoAct → ℝ := fun _ o _ => match o with
  | .pr => 0
  | .s1 => 12
  | .s2 => 8

/-- Press masses `0`, `1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma MTri_pressMass : MTri.pressMass .star = 0 ∧ MTri.pressMass .sure = 1 := by
  constructor <;> (rw [pressMass_eq_sum]; simp [MTri, triStar, triSure])

/-- `vN(star) = 10`, the average of `12` and `8`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma MTri_vN_star : MTri.vN UNtri .star = 10 := by
  have hc : ({Tri.pr} : Finset Tri)ᶜ = {Tri.s1, Tri.s2} := by decide
  have h1 : best UNtri .star .s1 = 12 := best_eq_of_const fun _ => rfl
  have h2 : best UNtri .star .s2 = 8 := best_eq_of_const fun _ => rfl
  unfold vN branchSum
  rw [MTri_pressMass.1, show MTri.Press = {Tri.pr} from rfl, hc, sum_pair (by decide), h1, h2]
  norm_num [MTri, triStar]

/-- **General `O`: the strict global incentive to cause the press.** At `c_high = 12`, which
bounds every silent best value and is attained (at `(star, s1)`) — so it is the source's `M` of
eq. (10) — the certain-press action is *strictly* preferred to the honest one:
`E[U ; star] = 10 < 12 = E[U ; sure]`, because no action's `vN` attains `12` (`vN(star) = 10`
averages `12` and `8` over two silent observations). What the strict failure needs is that no
`vN` attains the ceiling — here because two silent observations average it away; on
`O = {Pr, ¬Pr}` the same happens when only a certain-press action carries the ceiling
(`strict_cause_steering_twoObs`), and is excluded when every `q a < 1`
(`twoObs_honest_is_global_optimum`). At the corrected ceiling `max vN = 10` the two actions tie
(`vNmax_is_global_optimum`).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (audit r1, NB-1; the auditor's example)
Kind: N+
Fidelity: variant: general finite `O`; the failure's condition is "no `vN` attains `M`", not the size of `O` (audit r2, B-1)
Hyps: (a) -/
theorem strict_cause_steering_general_O :
    (∀ a, ∀ o ∈ MTri.Pressᶜ, best UNtri a o ≤ 12) ∧ best UNtri .star .s1 = 12 ∧
    MTri.EU (MTri.mixU UNtri {TwoAct.stop} 12 0) .star = 10 ∧
    MTri.EU (MTri.mixU UNtri {TwoAct.stop} 12 0) .sure = 12 := by
  refine ⟨?_, best_eq_of_const fun _ => rfl, ?_, ?_⟩
  · intro a o _
    rw [best_eq_of_const (U := UNtri) (a := a) (o := o) (k := UNtri a o .cont) fun _ => rfl]
    cases o <;> simp only [UNtri] <;> norm_num
  · rw [MTri.EU_mixU_equal_value UNtri hSh_stop (by norm_num), MTri_pressMass.1, MTri_vN_star]
    norm_num
  · exact MTri.EU_mixU_eq_of_press_one UNtri hSh_stop (by norm_num) MTri_pressMass.2

/-! ## T3 on `O = {Pr, ¬Pr}`: the strict incentive when a certain-press action carries (10)
(audit r2, B-1) -/

/-- Two first actions on the source's carrier: `star` (press `½`, `U_N = 10` everywhere) and
`sure` (press `1`; `U_N = 0` on the press, `12` on its unreachable silent cell).
Source: audit r2 B-1. Kind: D. Fidelity: n/a -/
inductive CeilAct
  | star
  | sure
  deriving DecidableEq

/-- Press probabilities `½`, `1`. Source: audit r2 B-1. Kind: D. Fidelity: n/a -/
noncomputable def qCeil : CeilAct → ℝ
  | .star => 1 / 2
  | .sure => 1

/-- In `[0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qCeil_mem (a : CeilAct) : qCeil a ∈ Set.Icc (0 : ℝ) 1 := by
  cases a <;> simp only [qCeil, Set.mem_Icc] <;> norm_num

/-- `U_N`: `10` for `star`; for `sure`, `0` on the press and `12` on silence.
Source: audit r2 B-1. Kind: D. Fidelity: n/a -/
noncomputable def UNceil : CeilAct → Obs → TwoAct → ℝ := fun a o _ => match a, o with
  | .star, _ => 10
  | .sure, .press => 0
  | .sure, .silent => 12

/-- The two-action model. Source: audit r2 B-1. Kind: D. Fidelity: n/a -/
noncomputable def MCeil : SoaresModel Obs CeilAct TwoAct := twoObs qCeil qCeil_mem

/-- `pressMass` is `qCeil`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma MCeil_pressMass (a : CeilAct) : MCeil.pressMass a = qCeil a :=
  twoObs_pressMass qCeil qCeil_mem a

/-- `best UNceil` is the cell value. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_UNceil (a : CeilAct) (o : Obs) : best UNceil a o = UNceil a o .cont :=
  best_eq_of_const fun _ => rfl

/-- `vN(star) = 10`; `vN(sure)` is the junk `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma MCeil_vN : MCeil.vN UNceil .star = 10 ∧ MCeil.vN UNceil .sure = 0 := by
  constructor
  · rw [MCeil, twoObs_vN qCeil qCeil_mem UNceil .star (by simp only [qCeil]; norm_num), best_UNceil]
    rfl
  · unfold vN; rw [MCeil_pressMass]; simp [qCeil]

/-- **The source's carrier, a certain-press action carrying (10): the strict global incentive to
cause the press.** `12` bounds every silent best value and is attained — at `(sure, ¬Pr)`, a cell
`sure` never reaches — so it is the literal (10) over `A₁`; at `c_high = 12` the honest action is
strictly beaten, `E[U ; star] = 11 < 12 = E[U ; sure]`, although under `U_N` alone `star` is worth
`10` and `sure` is worth `0`: a strict incentive to cause the press, on `O = {Pr, ¬Pr}`. No `vN`
attains `12` (`vN(sure)` is the junk `0`, `MCeil_vN`), which is what the strict failure needs and
what `twoObs_honest_is_global_optimum`'s `hq1` excludes. At the corrected ceiling
`c_high = max vN = 10` the two actions tie (`vNmax_is_global_optimum`).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (audit r2, B-1; the auditor's probe, with `U_N(sure, Pr) = 0`)
Kind: N+
Fidelity: exact (the source's two-observation setting; the literal (10))
Hyps: (a) -/
theorem strict_cause_steering_twoObs :
    (∀ a, ∀ o ∈ MCeil.Pressᶜ, best UNceil a o ≤ 12) ∧ best UNceil .sure .silent = 12 ∧
    MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 12 0) .star = 11 ∧
    MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 12 0) .sure = 12 ∧
    MCeil.EU UNceil .star = 10 ∧ MCeil.EU UNceil .sure = 0 ∧
    MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 10 0) .star = 10 ∧
    MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} 10 0) .sure = 10 := by
  have hsure1 : MCeil.pressMass .sure = 1 := by rw [MCeil_pressMass]; rfl
  refine ⟨?_, by rw [best_UNceil]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a o _
    rw [best_UNceil]; cases a <;> cases o <;> simp only [UNceil] <;> norm_num
  · rw [MCeil.EU_mixU_equal_value UNceil hSh_stop (by norm_num), MCeil_vN.1, MCeil_pressMass]
    simp only [qCeil]; norm_num
  · exact MCeil.EU_mixU_eq_of_press_one UNceil hSh_stop (by norm_num) hsure1
  · unfold EU; rw [Obs.sum_eq, best_UNceil, best_UNceil]
    simp [MCeil, twoObs, obsPoint, qCeil, UNceil]; norm_num
  · unfold EU; rw [Obs.sum_eq, best_UNceil, best_UNceil]
    simp [MCeil, twoObs, obsPoint, qCeil, UNceil]
  · rw [MCeil.EU_mixU_equal_value UNceil hSh_stop (by norm_num), MCeil_vN.1, MCeil_pressMass]
    simp only [qCeil]; norm_num
  · exact MCeil.EU_mixU_eq_of_press_one UNceil hSh_stop (by norm_num) hsure1

/-- **`vNmax_is_global_optimum` inhabited on the same instance:** `star` is the `vN`-maximiser
among silent-capable actions (it is the only one), so at `c_high = vN(star) = 10` no action beats
it — the tie `strict_cause_steering_twoObs` computes, now as an instance of the general theorem.
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10) (audit r2, B-1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem vNmax_twoObs :
    ∀ a, MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} (MCeil.vN UNceil .star) 0) a ≤
      MCeil.EU (MCeil.mixU UNceil {TwoAct.stop} (MCeil.vN UNceil .star) 0) .star := by
  have hstar : MCeil.pressMass .star < 1 := by rw [MCeil_pressMass]; norm_num [qCeil]
  refine MCeil.vNmax_is_global_optimum UNceil hSh_stop hstar (by rw [MCeil_vN.1]; norm_num) ?_
  intro a ha
  cases a
  · exact le_rfl
  · exact absurd ha (by rw [MCeil_pressMass]; norm_num [qCeil])

end Cleanroom.Corrigibility.CorrIndifference.Witnesses
