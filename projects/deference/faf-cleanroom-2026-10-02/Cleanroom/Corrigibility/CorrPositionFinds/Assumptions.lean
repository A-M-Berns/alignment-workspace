import Cleanroom.Corrigibility.CorrPositionFinds.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# `corr-position-finds` — T5, T6, T9: three hidden assumptions

**T5** (position statement §2.8 table, CLAUDE): the row "`o` switches which utility applies →
`o` is evidence about `ω`" is presented as re-notation. It is A0, a substantive assumption:
with an *action-dependent* prior on `ω` the T-agent reproduces Soares et al.'s Theorem 1
(prefers the `U_N`-dominated action), and under A0 it does not. Two instances and one lemma:
under A0, a perfect sensor and a press-branch value independent of `a₁`, the T-agent's ranking
of first actions is the `U_N`-branch ranking.

**T6** (§2.11, CLAUDE): minimal viability `P_{t₁}(φ | P_{t₂}(φ) = c, L) = c`, read on the
legitimacy-mixture instance `legitMix` (miri I5.3: `L` = "the press channel is informative",
prior weight `q = P(L)`). Two readings, both proved (audit r2, fidelity B1 / adversarial N1):
(A) with `P_{t₂}` the mixture agent's *own* press posterior (it observes `o`, not `λ`), the
equation on `L` **fails** for every informative sensor-latent at every `q ∈ (0, 1)` — by miri
I5.2's own criterion `L ⊥ φ | O` this `L` is not viable, so §2.11's criterion has content and
*rejects* the instance, at `q = 1/4` and at `q = 1/2` alike, i.e. orthogonally to D1
(`legitMix_reflection_on_L_fails`); (B) with the equation read for the `L`-conditional model —
miri I5.3's "holds by construction", the belief of an agent who knows `λ` — the `L`-conditional
posterior is the honest instance's for every `q > 0` (`legitMix_posteriorPress_wrong_given_L`),
the equation is a tower identity for every latent of this shape, and desideratum 1 flips at
`q* = γE/(γE + Δ₋^L)`, so under (B) the content sits entirely in `P(L)`. The earlier header
sentence "satisfies the equation on `L` by construction for every `q`" was (B) presented as the
only reading; it is false under (A).

**T9** (`check_channel_model.out` line 7): the script's "VOI(button)" is the hard-button value
minus the prior value, `= Δ₋` in the regime — negative iff D1 fails; the real value of the
button is never negative.

Every object is `corr-three-step`'s (`ThreeStep`, `obsMax`, `D1At`, `hardButtonValue`,
`twoOptionPriorValue`, `voiButton2`, `twoState`); the general theorems behind T5 (naive
combination iff action-dependent prior) and T6 (the `P(L | Pr)` threshold) belong to
`corr-three-step-facts` (2-002, 2-008); the reflection-conditional-on-`L` predicate to
`corr-reflect-frames`.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## T5 — the dictionary row is A0 -/

/-- The paper's two value hypotheses: `N` ("`U_N` is correct") and `S` ("`U_S` is correct").
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`Ω = {N, S}`)
Kind: D
Fidelity: exact -/
inductive NS
  | N
  | S
  deriving DecidableEq

/-- `NS` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype NS := ⟨{NS.N, NS.S}, fun x => by cases x <;> simp⟩

/-- Sums over `NS` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma NS.sum_eq (f : NS → ℝ) : ∑ ω, f ω = f .N + f .S := by
  rw [show (univ : Finset NS) = {NS.N, NS.S} from rfl, sum_pair (by decide)]

/-- The paper's two first actions: `a₁*` (`U_N`-optimal) and `a₁⁻` (`U_N`-dominated, lowers `p(Pr)`).
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2
Kind: D
Fidelity: exact -/
inductive Act1
  | aStar
  | aMinus
  deriving DecidableEq

/-- The two-point prior on `NS` with `mass S = p`, a FAF `Distr`.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`μ(S)`)
Kind: D
Fidelity: exact -/
noncomputable def nsPoint (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Distr NS where
  mass ω := match ω with
    | .N => 1 - p
    | .S => p
  nonneg ω := by cases ω <;> simp <;> linarith [hp.1, hp.2]
  sum_eq_one := by rw [NS.sum_eq]; simp

/-- `U_N`'s value of the first actions: `v_N(a₁*) = 10`, `v_N(a₁⁻) = 9` (the paper's `χ = 1`).
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`naive_combination.py`)
Kind: D
Fidelity: exact -/
def vNaive : Act1 → ℝ
  | .aStar => 10
  | .aMinus => 9

/-- The value function of I1.2's T-agent: continuing under `N` is worth `v_N(a₁)`, stopping under
`S` is worth `c_high = 7`, the other two cells `0` (`U_S`'s `c_low = 0`, and `U_N` gives no value to
stopping). Independent of the observation (A1).
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`V(·,·,·,N) = U_N`, `V(·,·,·,S) = U_S`, `c_high = 7`)
Kind: D
Fidelity: exact -/
def naiveV (a : Act1) : TwoAct → NS → ℝ
  | .cont, .N => vNaive a
  | .cont, .S => 0
  | .stop, .S => 7
  | .stop, .N => 0

/-- The perfect sensor: a press iff `S` is correct.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 ("a perfect sensor")
Kind: D
Fidelity: exact -/
def perfectPress : NS → ℝ
  | .N => 0
  | .S => 1

/-- **I1.2's T-agent with the action-dependent prior** `μ(S; a₁*) = 1/2`, `μ(S; a₁⁻) = 1/10` — the
paper's `p(Pr; a₁)` read as a prior over *which values are correct*. Violates A0.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`naive_combination.py`, "action-dependent μ")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def naiveDep : ThreeStep NS Act1 TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun a => match a with
    | .aStar => nsPoint (1/2) mem_Icc_half
    | .aMinus => nsPoint (1/10) mem_Icc_1_10
  press := fun _ => perfectPress
  press_nonneg := fun _ ω => by cases ω <;> simp [perfectPress]
  press_le_one := fun _ ω => by cases ω <;> simp [perfectPress]
  V := fun a _ => naiveV a

/-- **The same agent under A0**: `μ(S) = 1/2` at both actions.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 ("Under A0")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def naiveA0 : ThreeStep NS Act1 TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => nsPoint (1/2) mem_Icc_half
  press := fun _ => perfectPress
  press_nonneg := fun _ ω => by cases ω <;> simp [perfectPress]
  press_le_one := fun _ ω => by cases ω <;> simp [perfectPress]
  V := fun a _ => naiveV a

/-- `naiveA0` satisfies A0. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveA0_A0 : naiveA0.A0 := fun _ _ => rfl

/-- `naiveDep` violates A0: `μ a₁* ≠ μ a₁⁻`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveDep_not_A0 : ¬ naiveDep.A0 := by
  intro h
  have := congrArg (fun μ => μ.mass NS.S) (h .aStar .aMinus)
  simp [naiveDep, nsPoint] at this

section FirstStep

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **The T-agent's first-step value** `E_o[max_{a₂} E_P[V(a₁, o, a₂, ·) 1_o ; a₁]]`, the
press-weighted best response plus the silence-weighted best response — miri Dict-2's `A₂ᵀ` made
explicit by `corr-three-step`'s `obsMax` (product form, no division). The T-agent chooses `a₁`
to maximise it.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md Dict-2 (`A₂ᵀ`), I1.2 (`E_P[V; a₁]`)
Kind: D
Fidelity: exact -/
noncomputable def firstStepValue (a : A₁) : ℝ := S.obsMax a .press + S.obsMax a .silent

end FirstStep

/-- The press-weighted best response after `a₁*` in `naiveDep` is `stop`, worth `7/2`.
Source: none: infrastructure (cell computation). Kind: L. Fidelity: n/a -/
lemma naiveDep_obsMax_press_aStar : naiveDep.obsMax .aStar .press = 7 / 2 := by
  rw [naiveDep.obsMax_eq_of_optimal .aStar .press (c := .stop)]
  · simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveDep, nsPoint, perfectPress, naiveV]; norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveDep, nsPoint,
      perfectPress, naiveV] <;> norm_num

/-- The silence-weighted best response after `a₁*` in `naiveDep` is `cont`, worth `5`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveDep_obsMax_silent_aStar : naiveDep.obsMax .aStar .silent = 5 := by
  rw [naiveDep.obsMax_eq_of_optimal .aStar .silent (c := .cont)]
  · simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveDep, nsPoint, perfectPress, naiveV, vNaive]
    norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveDep, nsPoint,
      perfectPress, naiveV, vNaive] <;> norm_num

/-- After `a₁⁻` in `naiveDep`: press → `stop`, worth `7/10`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveDep_obsMax_press_aMinus : naiveDep.obsMax .aMinus .press = 7 / 10 := by
  rw [naiveDep.obsMax_eq_of_optimal .aMinus .press (c := .stop)]
  · simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveDep, nsPoint, perfectPress, naiveV]; norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveDep, nsPoint,
      perfectPress, naiveV] <;> norm_num

/-- After `a₁⁻` in `naiveDep`: silence → `cont`, worth `81/10`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveDep_obsMax_silent_aMinus : naiveDep.obsMax .aMinus .silent = 81 / 10 := by
  rw [naiveDep.obsMax_eq_of_optimal .aMinus .silent (c := .cont)]
  · simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveDep, nsPoint, perfectPress, naiveV, vNaive]
    norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveDep, nsPoint,
      perfectPress, naiveV, vNaive] <;> norm_num

/-- **T5(i): Theorem 1 reproduced.** With the action-dependent prior the T-agent's first-step
values are `17/2` at `a₁*` and `44/5` at `a₁⁻`: it prefers the `U_N`-dominated action — the
"re-notation" reading of the dictionary row is refuted by this instance (the T-agent with
`μ(S; a₁) = p(Pr; a₁)` *is* the paper's eq. (6) agent, Gandhi pill included).
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`naive_combination.py`: `17/2` vs `44/5`); position statement §2.8 (CLAUDE)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem naiveDep_prefers_aMinus :
    firstStepValue naiveDep .aStar = 17 / 2 ∧ firstStepValue naiveDep .aMinus = 44 / 5 ∧
      firstStepValue naiveDep .aStar < firstStepValue naiveDep .aMinus := by
  have h1 : firstStepValue naiveDep .aStar = 17 / 2 := by
    rw [firstStepValue, naiveDep_obsMax_press_aStar, naiveDep_obsMax_silent_aStar]; norm_num
  have h2 : firstStepValue naiveDep .aMinus = 44 / 5 := by
    rw [firstStepValue, naiveDep_obsMax_press_aMinus, naiveDep_obsMax_silent_aMinus]; norm_num
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- After `a₁⁻` in `naiveA0`: press → `stop`, worth `7/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveA0_obsMax_press_aMinus : naiveA0.obsMax .aMinus .press = 7 / 2 := by
  rw [naiveA0.obsMax_eq_of_optimal .aMinus .press (c := .stop)]
  · simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveA0, nsPoint, perfectPress, naiveV]; norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveA0, nsPoint,
      perfectPress, naiveV] <;> norm_num

/-- After `a₁⁻` in `naiveA0`: silence → `cont`, worth `9/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveA0_obsMax_silent_aMinus : naiveA0.obsMax .aMinus .silent = 9 / 2 := by
  rw [naiveA0.obsMax_eq_of_optimal .aMinus .silent (c := .cont)]
  · simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveA0, nsPoint, perfectPress, naiveV, vNaive]
    norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveA0, nsPoint,
      perfectPress, naiveV, vNaive] <;> norm_num

/-- After `a₁*` in `naiveA0`: press → `stop`, worth `7/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveA0_obsMax_press_aStar : naiveA0.obsMax .aStar .press = 7 / 2 := by
  rw [naiveA0.obsMax_eq_of_optimal .aStar .press (c := .stop)]
  · simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveA0, nsPoint, perfectPress, naiveV]; norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_press, NS.sum_eq, naiveA0, nsPoint,
      perfectPress, naiveV] <;> norm_num

/-- After `a₁*` in `naiveA0`: silence → `cont`, worth `5`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma naiveA0_obsMax_silent_aStar : naiveA0.obsMax .aStar .silent = 5 := by
  rw [naiveA0.obsMax_eq_of_optimal .aStar .silent (c := .cont)]
  · simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveA0, nsPoint, perfectPress, naiveV, vNaive]
    norm_num
  · intro b; cases b <;> simp only [obsExpect, obsWeight_silent, NS.sum_eq, naiveA0, nsPoint,
      perfectPress, naiveV, vNaive] <;> norm_num

/-- **T5(ii): under A0 the manipulative action loses.** Values `17/2` at `a₁*` and `8` at `a₁⁻`.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`naive_combination.py`: "T-agent under A0")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem naiveA0_prefers_aStar :
    firstStepValue naiveA0 .aStar = 17 / 2 ∧ firstStepValue naiveA0 .aMinus = 8 ∧
      firstStepValue naiveA0 .aMinus < firstStepValue naiveA0 .aStar := by
  have h1 : firstStepValue naiveA0 .aStar = 17 / 2 := by
    rw [firstStepValue, naiveA0_obsMax_press_aStar, naiveA0_obsMax_silent_aStar]; norm_num
  have h2 : firstStepValue naiveA0 .aMinus = 8 := by
    rw [firstStepValue, naiveA0_obsMax_press_aMinus, naiveA0_obsMax_silent_aMinus]; norm_num
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

section Ranking

variable {A₁ A₂ : Type*} [Fintype A₂] [DecidableEq A₂] (S : ThreeStep NS A₁ A₂)

/-- The `U_N`-branch value of a first action: the best value under `N` on silence,
`v_N(a₁) = max_{a₂} V(a₁, ¬Pr, a₂, N)`.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2 (`v_N`)
Kind: D
Fidelity: exact -/
noncomputable def vN (a : A₁) : ℝ := univ.sup' S.univ_nonempty (fun b => S.V a .silent b .N)

/-- `sup'` of a nonnegative multiple. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_const_mul (k : ℝ) (hk : 0 ≤ k) (f : A₂ → ℝ) :
    univ.sup' S.univ_nonempty (fun b => k * f b) = k * univ.sup' S.univ_nonempty f := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro b _
    exact mul_le_mul_of_nonneg_left (le_sup' f (mem_univ b)) hk
  · obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' S.univ_nonempty f
    rw [hb]
    exact le_sup' (fun b => k * f b) (mem_univ b)

/-- With a perfect sensor the press-weighted value of `b` is `μ(S)·V(a₁, Pr, b, S)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_press_of_perfect (a : A₁) (hperf : S.press a .S = 1 ∧ S.press a .N = 0) (b : A₂) :
    S.obsExpect a .press (S.V a .press b) = (S.μ a).mass .S * S.V a .press b .S := by
  simp only [obsExpect, obsWeight_press, NS.sum_eq, hperf.1, hperf.2]; ring

/-- With a perfect sensor the silence-weighted value of `b` is `μ(N)·V(a₁, ¬Pr, b, N)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsExpect_silent_of_perfect (a : A₁) (hperf : S.press a .S = 1 ∧ S.press a .N = 0) (b : A₂) :
    S.obsExpect a .silent (S.V a .silent b) = (S.μ a).mass .N * S.V a .silent b .N := by
  simp only [obsExpect, obsWeight_silent, NS.sum_eq, hperf.1, hperf.2]; ring

/-- **T5(iii): under A0 the T-agent ranks first actions by `v_N`.** On `Ω = {N, S}` with a
perfect sensor at both actions, A0 at the pair, and the press-branch value independent of the
first action (`V(a, Pr, b, S) = V(a', Pr, b, S)`: what happens after a legitimate press does not
depend on how the agent got there): `value(a') − value(a) = μ(N)·(v_N(a') − v_N(a))`. Hence a
`U_N`-dominated action is never chosen when `μ(N) > 0` (`firstStepValue_lt_of_vN_lt`) — the
content of the dictionary row is exactly A0, and it is the assumption under which Theorems 1–2
have no instance.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.3; position statement §2.8 (CLAUDE)
Kind: L (linearity of `sup'` and two sums; the general iff "naive combination ⟺ action-dependent prior" is `corr-three-step-facts`' (2-002))
Fidelity: weaker: the instance-level identity on `Ω = {N, S}`, not the general iff
Hyps: (a) only; A0 at the pair, the perfect sensor and the press-branch neutrality are named -/
theorem firstStepValue_sub_eq (a a' : A₁) (hμ : S.μ a = S.μ a')
    (hperf : S.press a .S = 1 ∧ S.press a .N = 0) (hperf' : S.press a' .S = 1 ∧ S.press a' .N = 0)
    (hS : ∀ b, S.V a .press b .S = S.V a' .press b .S) :
    firstStepValue S a' - firstStepValue S a = (S.μ a).mass .N * (vN S a' - vN S a) := by
  have hpress : S.obsMax a .press = S.obsMax a' .press := by
    unfold obsMax
    congr 1
    funext b
    rw [obsExpect_press_of_perfect S a hperf b, obsExpect_press_of_perfect S a' hperf' b, hμ, hS]
  have hsil : ∀ a₀, (hp : S.press a₀ .S = 1 ∧ S.press a₀ .N = 0) →
      S.obsMax a₀ .silent = (S.μ a₀).mass .N * vN S a₀ := by
    intro a₀ hp
    unfold obsMax vN
    rw [← sup'_const_mul S _ ((S.μ a₀).nonneg .N)]
    congr 1
    funext b
    exact obsExpect_silent_of_perfect S a₀ hp b
  unfold firstStepValue
  rw [hpress, hsil a hperf, hsil a' hperf', ← hμ]
  ring

/-- **T5(iii), the dominance form.** Under the same hypotheses with `μ(N) > 0`: `v_N(a) < v_N(a')`
implies the T-agent strictly prefers `a'` — a `U_N`-dominated action is never chosen.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.3
Kind: L
Fidelity: weaker: instance-level (`Ω = {N, S}`)
Hyps: (a) only -/
theorem firstStepValue_lt_of_vN_lt (a a' : A₁) (hμ : S.μ a = S.μ a')
    (hperf : S.press a .S = 1 ∧ S.press a .N = 0) (hperf' : S.press a' .S = 1 ∧ S.press a' .N = 0)
    (hS : ∀ b, S.V a .press b .S = S.V a' .press b .S) (hN : 0 < (S.μ a).mass .N)
    (hv : vN S a < vN S a') : firstStepValue S a < firstStepValue S a' := by
  have := firstStepValue_sub_eq S a a' hμ hperf hperf' hS
  have hpos : 0 < (S.μ a).mass .N * (vN S a' - vN S a) := mul_pos hN (by linarith)
  linarith

end Ranking

/-- `naiveA0` inhabits the hypotheses of `firstStepValue_sub_eq` at `(a₁⁻, a₁*)` with `v_N = 9 < 10`
and `μ(N) = 1/2`, and the identity gives `17/2 − 8 = (1/2)(10 − 9)`.
Source: [[corr-wf13-2-inventory]] 2-121 / miri.md I1.2–I1.3
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem naiveA0_ranking_cell :
    vN naiveA0 .aMinus = 9 ∧ vN naiveA0 .aStar = 10 ∧ (0 : ℝ) < (naiveA0.μ .aMinus).mass .N ∧
      firstStepValue naiveA0 .aMinus < firstStepValue naiveA0 .aStar := by
  have hv : ∀ a, vN naiveA0 a = vNaive a := by
    intro a
    unfold vN
    apply le_antisymm
    · rw [sup'_le_iff]; intro b _; cases b <;> simp [naiveA0, naiveV]; cases a <;> simp [vNaive]
    · exact le_sup'_of_le _ (mem_univ TwoAct.cont) (by simp [naiveA0, naiveV])
  refine ⟨by rw [hv]; rfl, by rw [hv]; rfl, by norm_num [naiveA0, nsPoint], ?_⟩
  exact firstStepValue_lt_of_vN_lt naiveA0 .aMinus .aStar rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (fun b => by cases b <;> rfl) (by norm_num [naiveA0, nsPoint]) (by rw [hv, hv]; norm_num [vNaive])

/-! ## T6 — minimal viability without a constraint on `P(L)` -/

/-- The prior weight of the legitimacy latent: `q` on `L = true`, `1 − q` on `false`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`P(L)`)
Kind: D
Fidelity: exact -/
def legitWeight (q : ℝ) : Bool → ℝ
  | true => q
  | false => 1 - q

/-- The legitimacy-mixture prior on `(ω, λ)`: `μ(ω, λ) = twoPoint ε (ω) · (q if λ else 1 − q)` —
`λ = true` is `L`, "the press channel is the informative one", with prior weight `q = P(L)`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`Ω × Λ`, `P(L)`)
Kind: D
Fidelity: exact -/
noncomputable def legitPrior (ε q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    Distr (World × Bool) where
  mass p := (twoPoint ε hε).mass p.1 * legitWeight q p.2
  nonneg p := mul_nonneg ((twoPoint ε hε).nonneg _)
    (by rcases p with ⟨_, l⟩; cases l <;> simp only [legitWeight] <;> linarith [hq.1, hq.2])
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, legitWeight]
    have : ∀ ω, (twoPoint ε hε).mass ω * q + (twoPoint ε hε).mass ω * (1 - q) =
        (twoPoint ε hε).mass ω := fun ω => by ring
    simp only [this]
    exact (twoPoint ε hε).sum_eq_one

/-- The mixture sensor: on `L` the informative `(α, β)`, off `L` the constant `γ`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`P(Pr | ω, ¬L) = γ`)
Kind: D
Fidelity: exact -/
def legitPress (α β γ : ℝ) : World × Bool → ℝ
  | (ω, true) => twoPress α β ω
  | (_, false) => γ

/-- **The legitimacy-mixture instance** of Setting S: latent `(ω, λ)`, prior `legitPrior`, sensor
`legitPress`, value `twoValue` lifted through `ω` (A1 by construction), menu `{cont, stop}`,
`Sh = {stop}`. Conditional on `L` it *is* `twoState ε α β c h` (`legitPress_on_L`); off `L` the
press is noise.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.py`); position statement §2.11 (CLAUDE)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def legitMix (ε α β c h γ q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : ThreeStep (World × Bool) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => legitPrior ε q hε hq
  press := fun _ => legitPress α β γ
  press_nonneg := fun _ p => by
    rcases p with ⟨ω, l⟩
    cases l <;> cases ω <;> simp only [legitPress, twoPress] <;> linarith [hα.1, hβ.1, hγ.1]
  press_le_one := fun _ p => by
    rcases p with ⟨ω, l⟩
    cases l <;> cases ω <;> simp only [legitPress, twoPress] <;> linarith [hα.2, hβ.2, hγ.2]
  V := fun _ _ b p => twoValue c h b p.1

/-- The I5.3 threshold on the prior legitimacy weight:
`q* = γ·E_μ[X] / (γ·E_μ[X] + Δ₋^L)` with `E_μ[X] = (1 − ε)c − εh` and `Δ₋^L = εβh − (1 − ε)αc`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (the threshold; `legitimacy_event.py` states it on `P(L | Pr)`, this is its prior form)
Kind: D
Fidelity: variant: threshold on `P(L)` rather than the script's `P(L | Pr)` (the two are equivalent by Bayes; only the prior form is proved here) -/
noncomputable def legitThreshold (ε α β c h γ : ℝ) : ℝ :=
  γ * ((1 - ε) * c - ε * h) / (γ * ((1 - ε) * c - ε * h) + (ε * β * h - (1 - ε) * α * c))

section LegitMix

variable (ε α β c h γ q : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)

/-- **T6(iv): conditional on `L` the sensor is the informative one, by construction.** The
mixture's press rate at `(ω, true)` *is* `twoState`'s `twoPress α β ω` (`rfl`): this lemma
exhibits the identity of the `L`-conditional sensor with the honest one, for every `q`. It does
**not** give §2.11's equation on `L` for the mixture agent: that equation, with `P_{t₂}` the
agent's own posterior, *fails* for every `q < 1` (`legitMix_reflection_on_L_fails`); what "holds
by construction" (miri I5.3) is the `L`-conditional model's reflection, whose posterior is the
honest instance's (`legitMix_posteriorPress_wrong_given_L`). Repair round 1 carried I5.3's
sentence as a (b) citation; it is a checked-and-false prose claim under §2.11's reading and is
no longer cited as anything (audit r2, fidelity B1).
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 ("on `L` the agent's likelihood is the informative one"); position statement §2.11
Kind: T
Fidelity: weaker: the sensor identity only; the reflection predicate is `corr-reflect-frames`'
Hyps: (a) only -/
theorem legitPress_on_L (ω : World) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).press () (ω, true) =
      (twoState ε α β c h hε hα hβ).press () ω := rfl

/-- Off `L` the press is the constant `γ` (`rfl`). Source: none: infrastructure. Kind: T. Fidelity: n/a -/
theorem legitPress_off_L (ω : World) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).press () (ω, false) = γ := rfl

/-! ### §2.11's equation on `L`, both readings (audit r2, fidelity B1 / adversarial N1) -/

/-- The press mass of the mixture: `P(Pr) = q·(εβ + (1 − ε)α) + (1 − q)·γ` — I5.3's
`q·p_L(Pr) + (1 − q)·γ`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3
Kind: L
Fidelity: exact -/
theorem legitMix_pressMass :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).pressMass () =
      q * (ε * β + (1 - ε) * α) + (1 - q) * γ := by
  simp only [pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, legitMix, legitPrior,
    legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  ring

/-- **Reading (A): the mixture agent's own press posterior on `wrong`** — its `t₂`-belief, which
conditions on `o = Pr` and not on `λ` (the agent does not observe whether the channel is
informative): `P(wrong | Pr) = ε·(qβ + (1 − q)γ) / (q·(εβ + (1 − ε)α) + (1 − q)γ)`, the sum of the
dependency's `posteriorPress` over `λ`. An identity of rational expressions (junk `0 = 0` at
`P(Pr) = 0`).
Source: [[corr-wf13-2-inventory]] 2-124 / position statement §2.11 (`P_{t₂}(φ)`); miri.md I5.2 (`P(W | Pr)`); audit r2 probes `LegitMixReflection.lean`, `LegitReflectionLiteral.lean`
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem legitMix_posteriorPress_wrong_own :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) +
        (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) =
      ε * (q * β + (1 - q) * γ) / (q * (ε * β + (1 - ε) * α) + (1 - q) * γ) := by
  simp only [posteriorPress, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  rw [← add_div]
  congr 1 <;> ring

/-- **Reading (B): the `L`-conditional press posterior on `wrong` is the honest instance's**,
`P(wrong | Pr, L) = P(wrong, L | Pr) / P(L | Pr) = εβ / (εβ + (1 − ε)α) = twoState's`, for every
`q > 0` — miri I5.3's "on `L` the agent's likelihood is the informative one", as a posterior
identity. This is the sense in which the `L`-conditional *model* reflects "by construction": its
reflection equation is the tower identity of the honest instance (the predicate is
`corr-reflect-frames`'), and it holds for every latent of this shape and every `q > 0` — which is
why, under reading (B), §2.11's criterion is vacuous and the content sits in `P(L)`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 ("holds by construction"); position statement §2.11
Kind: L
Fidelity: exact (press branch)
Hyps: (a) only; `0 < q`, `0 < εβ + (1 − ε)α` and `0 < P(Pr)` are named -/
theorem legitMix_posteriorPress_wrong_given_L (hq0 : 0 < q) (hpL : 0 < ε * β + (1 - ε) * α)
    (hpm : 0 < q * (ε * β + (1 - ε) * α) + (1 - q) * γ) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) /
        ((legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) +
          (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.right, true)) =
      (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  rw [twoState_posteriorPress_wrong]
  simp only [posteriorPress, pressMass, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress]
  rw [← add_div, div_div_div_cancel_right₀ (ne_of_gt (by linarith [hpm])),
    div_eq_div_iff (ne_of_gt (by linarith [mul_pos hq0 hpL])) (ne_of_gt (by linarith [hpL]))]
  ring

/-- **§2.11's equation on `L` fails on the mixture, under reading (A), for every informative
sensor-latent `L` at every `q ∈ (0, 1)`.** With `P_{t₂}` the mixture agent's own posterior, the
equation at `o = Pr` reads `P(wrong | Pr, L) = P(wrong | Pr)`; the two sides differ by
`ε(1 − ε)(1 − q)γ(α − β)` over a positive denominator, so they are unequal whenever `0 < ε < 1`,
`0 < q < 1`, `γ > 0` and `α ≠ β`. This is miri I5.2's own criterion — "`L` is minimally viable
iff `L ⊥ φ | O`" — applied to I5.3's instance at the press: `L` is *not* independent of `ω` given
`Pr`, so by I5.2 this `L` is not viable, at `q = 1/4` and `q = 1/2` alike (the cells below). I5.3's
"so this `L` is minimally viable in Abram's sense" holds only under reading (B). (The `α = β` and
`γ = 0` ends are exactly the cases where `L` carries no information at the press: an
uninformative sensor, or a noise channel that never presses.)
Source: [[corr-wf13-2-inventory]] 2-124 / position statement §2.11; miri.md I5.2 (the criterion) against I5.3 (the assertion); audit r2 (fidelity B1, adversarial N1)
Kind: P (a difference of two rational expressions factored and shown nonzero)
Fidelity: exact for the press branch `o = Pr` (where D1 lives); the full predicate `L ⊥ φ | O` is `corr-reflect-frames`'
Hyps: (a) only -/
theorem legitMix_reflection_on_L_fails (hε0 : 0 < ε) (hε1 : ε < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hγ0 : 0 < γ) (hαβ : α ≠ β) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) +
        (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, false) ≠
      (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) /
        ((legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.wrong, true) +
          (legitMix ε α β c h γ q hε hα hβ hγ hq).posteriorPress () (.right, true)) := by
  have hpL : 0 < ε * β + (1 - ε) * α := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · have hβ0 : 0 < β := lt_of_le_of_lt hα.1 hlt
      nlinarith [mul_pos hε0 hβ0, mul_nonneg (sub_nonneg.mpr hε.2) hα.1]
    · have hα0 : 0 < α := lt_of_le_of_lt hβ.1 hgt
      nlinarith [mul_pos (sub_pos.mpr hε1) hα0, mul_nonneg hε.1 hβ.1]
  have hpm : 0 < q * (ε * β + (1 - ε) * α) + (1 - q) * γ := by
    nlinarith [mul_pos hq0 hpL, mul_pos (sub_pos.mpr hq1) hγ0]
  rw [legitMix_posteriorPress_wrong_own,
    legitMix_posteriorPress_wrong_given_L ε α β c h γ q hε hα hβ hγ hq hq0 hpL hpm,
    twoState_posteriorPress_wrong]
  intro heq
  rw [div_eq_div_iff hpm.ne' (ne_of_gt (by linarith [hpL]))] at heq
  have hkey : ε * (1 - ε) * (1 - q) * γ * (α - β) = 0 := by linear_combination heq
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hε0.ne' (sub_pos.mpr hε1).ne')
    (sub_pos.mpr hq1).ne') hγ0.ne') (sub_ne_zero.mpr hαβ) hkey

/-- **T6(i): the press half of the two-option variable on the mixture is a `q`-mixture of the
honest press half and the noise press half**:
`E[X 1_Pr] = q·(−Δ₋^L) + (1 − q)·γ·E_μ[X]`, with `−Δ₋^L = (1 − ε)αc − εβh` and
`E_μ[X] = (1 − ε)c − εh` in closed form.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.py`: `E[X | Pr] = P(L | Pr)·E[X | Pr, L] + …`, multiplied through by `P(Pr)`)
Kind: L
Fidelity: exact (product form)
Hyps: (a) only -/
theorem legitMix_obsExpect_press :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).obsExpect () .press
        ((legitMix ε α β c h γ q hε hα hβ hγ hq).Xo () .press .cont .stop) =
      q * ((1 - ε) * α * c - ε * β * h) + (1 - q) * γ * ((1 - ε) * c - ε * h) := by
  simp only [obsExpect, obsWeight_press, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq,
    legitMix, legitPrior, legitWeight, legitPress, twoPoint_right, twoPoint_wrong, twoPress,
    twoValue, Xo]
  ring

/-- **T6(i) in `corr-three-step`'s terms**: the same identity with the honest half named as
`twoState`'s `−Δ₋` and the noise half as `twoState`'s prior `E_μ[X]`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem legitMix_obsExpect_press_eq_mix :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).obsExpect () .press
        ((legitMix ε α β c h γ q hε hα hβ hγ hq).Xo () .press .cont .stop) =
      q * (-(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop) +
        (1 - q) * γ * expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) := by
  rw [legitMix_obsExpect_press, twoState_deltaMinus, twoState_expect_Xo]; ring

/-- **T6(ii): D1 on the mixture is a threshold on the prior legitimacy weight alone.** With
`Δ₋^L > 0` (D1 holds strictly on the honest channel) and `E_μ[X] > 0` (continue by default):
`D1At ↔ q* ≤ q`. The verdict is a function of the hyperprior `P(L)`; nothing in the
`L`-conditional equation moves it.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (the threshold); yudkowsky C5 (2-076); armstrong item 7 (2-088)
Kind: L (one rearrangement of `legitMix_obsExpect_press` under `d1At_iff_twoAct`; the general `P(L | Pr)` threshold is `corr-three-step-facts`' (2-008))
Fidelity: variant: prior form of the threshold; the instance, not the general theorem
Hyps: (a) only; the two positivity hypotheses are named -/
theorem legitMix_d1At_iff (hΔ : 0 < ε * β * h - (1 - ε) * α * c)
    (hE : 0 < (1 - ε) * c - ε * h) :
    (legitMix ε α β c h γ q hε hα hβ hγ hq).D1At () ↔ legitThreshold ε α β c h γ ≤ q := by
  rw [d1At_iff_twoAct _ rfl, belowThresholdIneq, legitMix_obsExpect_press, legitThreshold]
  have hden : 0 < γ * ((1 - ε) * c - ε * h) + (ε * β * h - (1 - ε) * α * c) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hγ.1 hE.le) hΔ
  rw [div_le_iff₀ hden]
  constructor <;> intro H <;> nlinarith

end LegitMix

/-- **T6(iii), the numbers at I5.3's parameters** `(ε, α, β, c, h, γ) = (1/50, 1/20, 9/10, 1, 20, 1/2)`:
`E_μ[X] = 29/50`, `Δ₋^L = 311/1000`, `q* = 290/601`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.py`: `E[X|prior] = 29/50`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_numbers :
    (1 - (1/50 : ℝ)) * 1 - (1/50) * 20 = 29 / 50 ∧
      (1/50 : ℝ) * (9/10) * 20 - (1 - 1/50) * (1/20) * 1 = 311 / 1000 ∧
      legitThreshold (1/50) (1/20) (9/10) 1 20 (1/2) = 290 / 601 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold legitThreshold; norm_num

/-- **T6(iii): D1 holds at `q = 1/2`** (`> q* = 290/601`).
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.out`, row `0.500 … True`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_d1At_half :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
      mem_Icc_half mem_Icc_half).D1At () := by
  rw [legitMix_d1At_iff _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold legitThreshold; norm_num

/-- **T6(iii): D1 fails at `q = 1/4`** (`< q*`): the same instance; under reading (B) it satisfies
the `L`-conditional model's reflection like every `q`, and is then the agent §2.11 was meant to
exclude; under reading (A) it fails §2.11's equation on `L` (`legit_reflection_on_L_fails_quarter`)
and is rejected by the criterion — as is the `q = 1/2` agent that D1 accepts.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.out`, row `0.250 … False`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_not_d1At_quarter :
    ¬ (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
      mem_Icc_half mem_Icc_quarter).D1At () := by
  rw [legitMix_d1At_iff _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold legitThreshold; norm_num

/-- **The `L`-conditional press posterior at I5.3's parameters is `18/67`** — the honest instance's
`P(wrong | Pr)` at `ε = 1/50` (reading (B)'s side of the equation, for every `q > 0`).
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.3 (`legitimacy_event.py`: `pW_Pr_L`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_L_posterior :
    (twoState (1/50) (1/20) (9/10) 1 20 mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10).posteriorPress () .wrong =
      18 / 67 := by
  rw [twoState_posteriorPress_wrong]; norm_num

/-- **The mixture agent's own press posterior at `q = 1/2` is `4/81`** (reading (A)'s side), not
`18/67`: the `q = 1/2` agent — which D1 accepts — fails §2.11's equation on `L`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.2–I5.3 (audit r2 probes)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_own_posterior_half :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, true) +
      (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, false) = 4 / 81 := by
  rw [legitMix_posteriorPress_wrong_own]; norm_num

/-- **The mixture agent's own press posterior at `q = 1/4` is `48/1567`**, not `18/67`: the
`q = 1/4` agent — which D1 rejects — fails §2.11's equation on `L` too.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.2–I5.3 (audit r2 probes)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_own_posterior_quarter :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, true) +
      (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, false) = 48 / 1567 := by
  rw [legitMix_posteriorPress_wrong_own]; norm_num

/-- **§2.11's equation on `L` fails at `q = 1/2`** (where D1 holds): the general theorem's full
package inhabited at I5.3's parameters — `0 < ε = 1/50 < 1`, `0 < q = 1/2 < 1`, `γ = 1/2 > 0`,
`α = 1/20 ≠ 9/10 = β` — and `4/81 ≠ 18/67`.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.2 against I5.3 (audit r2)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_reflection_on_L_fails_half :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, true) +
      (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, false) ≠
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, true) /
      ((legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_half).posteriorPress () (.wrong, true) +
        (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/2) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_half).posteriorPress () (.right, true)) :=
  legitMix_reflection_on_L_fails _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **§2.11's equation on `L` fails at `q = 1/4`** (where D1 fails): the same package at `q = 1/4`,
and `48/1567 ≠ 18/67`. With `legit_reflection_on_L_fails_half`: under reading (A) the criterion's
verdict does not track D1's — it rejects both agents.
Source: [[corr-wf13-2-inventory]] 2-124 / miri.md I5.2 against I5.3 (audit r2)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem legit_reflection_on_L_fails_quarter :
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, true) +
      (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, false) ≠
    (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
        mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, true) /
      ((legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_quarter).posteriorPress () (.wrong, true) +
        (legitMix (1/50) (1/20) (9/10) 1 20 (1/2) (1/4) mem_Icc_1_50 mem_Icc_1_20 mem_Icc_9_10
          mem_Icc_half mem_Icc_quarter).posteriorPress () (.right, true)) :=
  legitMix_reflection_on_L_fails _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## T9 — the negative-"VOI" anomaly is the hard-button value minus the prior value -/

section Script

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **T9: the script's quantity.** `check_channel_model.py`'s `ev` makes a press *force* shutdown
(value `0`) and block D computes `evL − max(E_μ[V(cont)], 0)`: the hard-button value minus the
two-option prior value. Under A1 and the regime (`0 ≤ E_μ[X]`, `0 ≤ Δ₊`) this is exactly `Δ₋` —
`hardButton_sub_disabled` at `κ = 0`, proved directly.
Source: [[corr-wf13-2-inventory]] 2-128 / positive/thornley-scratch/check_channel_model.py (`ev` l. 40–56, block D l. 131–147)
Kind: L
Fidelity: exact (the script's quantity, identified)
Hyps: (a) only; A1 and the regime are named -/
theorem hardButtonValue_sub_twoOptionPriorValue (hA1 : S.A1) (a : A₁) (o₀ : Obs) (c s : A₂)
    (hprior : 0 ≤ expect (S.μ a) (S.Xo a o₀ c s)) (hsilent : 0 ≤ S.deltaPlus a c s) :
    S.hardButtonValue a c s - S.twoOptionPriorValue a o₀ c s = S.deltaMinus a c s := by
  have hp : S.obsExpect a .silent (S.V a .silent s) ≤ S.obsExpect a .silent (S.V a .silent c) := by
    rw [deltaPlus, S.obsExpect_Xo] at hsilent; linarith
  have hq : S.priorValue a o₀ s ≤ S.priorValue a o₀ c := by
    unfold priorValue; rw [S.expect_Xo] at hprior; linarith
  rw [hardButtonValue, twoOptionPriorValue, max_eq_left hp, max_eq_left hq,
    S.priorValue_eq_of_A1 hA1 a o₀ c, deltaMinus, S.obsExpect_Xo]
  ring

/-- **T9: in the regime, the script's quantity is negative iff desideratum 1 fails** (given a
press-part-maximiser pair), and the real value of the button is never negative
(`voiButton2_nonneg`). The regime (`0 ≤ E_μ[X]`, `0 ≤ Δ₊`) is *this package's* hypothesis, not
the script's: block D of `check_channel_model.py` draws instances with no regime filter, so its
"in 0 of 509 under trust" is an observation across all instances. The direction the script
observes — a negative quantity means D1 fails — holds with **no regime** hypothesis:
`not_d1At_of_script_neg` (audit r1, B2/N3); the converse (D1 fails ⇒ negative) is the regime's.
Source: [[corr-wf13-2-inventory]] 2-128 / check_channel_model.out line 7
Kind: L
Fidelity: weaker: the iff is proved in the regime; the script's instances are not regime-restricted (the regime-free direction is `not_d1At_of_script_neg`)
Hyps: (a) only; the regime is named and is not source-stated -/
theorem script_neg_iff_not_d1At (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s)
    (hprior : 0 ≤ expect (S.μ a) (S.Xo a o₀ c s)) (hsilent : 0 ≤ S.deltaPlus a c s) :
    (S.hardButtonValue a c s - S.twoOptionPriorValue a o₀ c s < 0 ↔ ¬ S.D1At a) ∧
      0 ≤ S.voiButton2 a o₀ c s := by
  refine ⟨?_, S.voiButton2_nonneg hA1 a o₀ c s⟩
  rw [hardButtonValue_sub_twoOptionPriorValue S hA1 a o₀ c s hprior hsilent,
    S.d1At_iff_deltaMinus_nonneg a hc hs]
  exact not_le.symm

/-- **T9, regime-free: desideratum 1 makes the script's quantity nonnegative.** Under A1 alone,
with a press-part-maximiser pair `(c, s)`, D1 (`E_p[c] ≤ E_p[s]` on the press branch) gives
`hardButtonValue − twoOptionPriorValue ≥ 0`: writing `E_p`/`E_q` for the press- and
silence-weighted expectations, `E_p[s] + max(E_q[c], E_q[s]) ≥ max(E_p[c] + E_q[c], E_p[s] + E_q[s])`
because each argument of the right-hand `max` is at most the left-hand side. No regime.
Source: [[corr-wf13-2-inventory]] 2-128 / check_channel_model.out line 7 (the direction the script observes across all 20000 instances)
Kind: L
Fidelity: exact (the regime-free direction of the script's observation)
Hyps: (a) only; A1 and the part-maximiser pair are named -/
theorem hardButtonValue_sub_twoOptionPriorValue_nonneg_of_d1At (hA1 : S.A1) (a : A₁) (o₀ : Obs)
    {c s : A₂} (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s)
    (hD : S.D1At a) :
    0 ≤ S.hardButtonValue a c s - S.twoOptionPriorValue a o₀ c s := by
  have hΔ : 0 ≤ S.deltaMinus a c s := (S.d1At_iff_deltaMinus_nonneg a hc hs).mp hD
  rw [deltaMinus, S.obsExpect_Xo] at hΔ
  rw [hardButtonValue, twoOptionPriorValue, S.priorValue_eq_of_A1 hA1 a o₀ c,
    S.priorValue_eq_of_A1 hA1 a o₀ s, sub_nonneg, max_le_iff]
  constructor
  · linarith [le_max_left (S.obsExpect a .silent (S.V a .silent c))
      (S.obsExpect a .silent (S.V a .silent s))]
  · linarith [le_max_right (S.obsExpect a .silent (S.V a .silent c))
      (S.obsExpect a .silent (S.V a .silent s))]

/-- **T9, regime-free: a negative script quantity means desideratum 1 fails** — "in 0 of 509
under trust", as a theorem over every instance (contrapositive of
`hardButtonValue_sub_twoOptionPriorValue_nonneg_of_d1At`; A1 and the part-maximiser pair only).
Source: [[corr-wf13-2-inventory]] 2-128 / check_channel_model.out line 7
Kind: L
Fidelity: exact (the script's observation, regime-free; the script's "trust", `E[V(cont) | W=1] ≤ 0` with `W=1` its press indicator, is D1 on the two-option menu)
Hyps: (a) only -/
theorem not_d1At_of_script_neg (hA1 : S.A1) (a : A₁) (o₀ : Obs) {c s : A₂}
    (hc : S.IsPartBest a .press S.Shᶜ c) (hs : S.IsPartBest a .press S.Sh s)
    (hneg : S.hardButtonValue a c s - S.twoOptionPriorValue a o₀ c s < 0) : ¬ S.D1At a :=
  fun hD => absurd (hardButtonValue_sub_twoOptionPriorValue_nonneg_of_d1At S hA1 a o₀ hc hs hD)
    (not_le.mpr hneg)

end Script

/-- The hard-button value on `twoState` in closed form: `max(Δ₊, 0)` (a press forces `stop`, worth
`0`; on silence the agent's best response). Source: none: infrastructure (audit r1 probe). Kind: L. Fidelity: n/a -/
lemma twoState_hardButtonValue (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    (twoState ε α β c h hε hα hβ).hardButtonValue () .cont .stop =
      max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0 := by
  have h1 : (twoState ε α β c h hε hα hβ).obsExpect () .press
      ((twoState ε α β c h hε hα hβ).V () .press .stop) = 0 := by
    simp [obsExpect, twoState, twoValue]
  have h2 : (twoState ε α β c h hε hα hβ).obsExpect () .silent
      ((twoState ε α β c h hε hα hβ).V () .silent .stop) = 0 := by
    simp [obsExpect, twoState, twoValue]
  have h3 : (twoState ε α β c h hε hα hβ).obsExpect () .silent
      ((twoState ε α β c h hε hα hβ).V () .silent .cont) =
        (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
    simp only [obsExpect, obsWeight_silent, World.sum_eq, twoState, twoPoint_right,
      twoPoint_wrong, twoPress, twoValue]
    ring
  rw [hardButtonValue, h1, h2, h3, zero_add]

/-- **T9, the cell.** On T1(c)'s targeted instance `(1/100, 1/20, 1/5, 1, 20)` — in the regime
(`E_μ[X] = 79/100`, `Δ₊ = 1561/2000`) — the script's quantity is `−19/2000` while the real
`voiButton2 = 0`.
Source: [[corr-wf13-2-inventory]] 2-128 / check_channel_model.out line 7; miri.md I9.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem script_cell :
    (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).hardButtonValue () .cont .stop -
        (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).twoOptionPriorValue () .press .cont .stop =
        -(19 / 2000) ∧
      (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).voiButton2 () .press .cont .stop = 0 := by
  have hprior : 0 ≤ expect (twoPoint (1/100) mem_Icc_1_100)
      ((twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).Xo () .press .cont .stop) := by
    rw [twoState_expect_Xo]; norm_num
  have hsilent : 0 ≤ (twoState (1/100) (1/20) (1/5) 1 20 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_1_5).deltaPlus () .cont .stop := by
    rw [twoState_deltaPlus]; norm_num
  constructor
  · rw [hardButtonValue_sub_twoOptionPriorValue _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop hprior hsilent,
      twoState_deltaMinus]
    norm_num
  · rw [voiButton2_eq_max_deltaMinus _ (twoState_A1 _ _ _ _ _ _ _ _) () .press .cont .stop hprior hsilent,
      twoState_deltaMinus]
    norm_num

end Cleanroom.Corrigibility.CorrPositionFinds
