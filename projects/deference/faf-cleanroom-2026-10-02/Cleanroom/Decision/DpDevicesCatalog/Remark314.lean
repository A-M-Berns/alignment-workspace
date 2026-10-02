import Cleanroom.Decision.DpDevicesCatalog.ToldYouSo

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T5(d): Remark 3.14 (traps versus dilemmas), and D1 on Told-You-So

SL-17's proposed Remark 3.14 (`sl-amendments.md:126–128`, an ADOPT amendment, **not v2 text**).
Its definitional sentence, verbatim: "Say a procedure class fails a stipulation set *regardless
of label* if every member makes the good outcome inconsistent at every κ-calibrated label, and
call the failure a *dilemma* rather than a *trap* if some procedure outside the class attains
more (Definition 21)." Its three applications: strict Told-You-So (the family fails only at the
self-fulfilling label) is "a dilemma of selection"; masked/limit Told-You-So (the family fails at
every calibrated label while `C*` attains `10`) is "a trap with a way out"; "a two-round tree
punishing every crossing is a trap and no dilemma". **The definitional sentence and the
applications contradict each other** (findings F12): read literally, fails-regardless-of-label
plus an outside procedure attaining more is a *dilemma*, which is exactly the case the second
application calls a *trap*. This package renders the **applications** (the Told-You-So verdicts
are the target, and P13-10′'s two tests agree with them), not the definitional clause:

* `FailsRegardlessOfLabel`: every member of the class makes the good outcome inconsistent at
  every `κ`-calibrated instantiation (rendered as `V < v`; the Definition-16 event form is
  `FailsRegardlessOfLabelEv`, and on `B_P` the two coincide, `tys_failsEv_imp_fails`);
* `Trap`: the class fails regardless of label **and** there is a way out — a procedure outside
  the class that is itself `κ`-calibrated at some instantiation and attains `v` there (the
  repair of audit round 1 added the calibration requirement on the way out);
* `Dilemma`: the class does not fail regardless of label — some member attains `v` at some
  `κ`-calibrated instantiation.

Under these a tree with no way out is neither a `Trap` nor a `Dilemma`; under SL-17's literal
clause it would be the only trap, and masked/limit Told-You-So would be a dilemma. The
sense-indexed verdict on Told-You-So with the zero-respecting class and the good outcome `10`:

* strict — a **dilemma**: at the label `π = P_{s₅}(m=10) = 1` the member `C*` is zero-respecting,
  strictly calibrated (Definition 8 is vacuous at `d₅`, `ν(O₅) = 0`) and attains `10`;
* masked, limit — a **trap**: at `d₅` every masked-calibrated and every limit-calibrated label
  has `P_{s₅} = δ_{(5,5)}` (`tys_maskedOCAt_five_pr`, `tys_limitOCAt_five_pr`), so the class
  takes `five` at `d₅` and gets `5 < 10` (indeed `ν(m=10) = 0`, the Definition-16 form), while
  `C* ∉ 𝒞` attains `10` at a label at which it is itself calibrated: `tysStateWayOut` (`s₅ =
  δ_{(5,5)}`, `s₁₀` the `O₁₀`-conditional of the uniform self-model) for masked, `tysState` for
  limit. Moreover at *every* calibrated instantiation of the class `C*` is outside the class and
  attains `10` (`tys_masked_wayOut_everywhere`, `tys_limit_wayOut_everywhere`).

D1 (`LimitStateEdt`) on Told-You-So (CA-17′): approves `C₀` with the stipulated states and
rejects `C*` with *every* state assignment (the limit state at `d₅` is certain of `m = 5`).

P13-10′'s reading of the label `π` as the agent's prior is ATTRIBUTION-UNVETTED.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## The label at `d₅` under masked and limit calibration, for every procedure -/

/-- `ν_{C'}(X ∩ O₅) = [(5,5) ∈ X] · C'(d₅)(five)` for every procedure. Source: none:
infrastructure. Kind: L -/
theorem tys_nu_inter_obs_five (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    nu C toldYouSo (X ∩ tysObs .five) =
      if (Five10.five, Five10.five) ∈ X then (C .five).w .five else 0 := by
  rw [tys_nu]; simp [tysObs]

/-- `ν_{C'}(O₅) = C'(d₅)(five)`. Source: none: infrastructure. Kind: L -/
theorem tys_nu_obs_five (C : Proc Five10 (fun _ => Five10) ℚ) :
    nu C toldYouSo (tysObs .five) = (C .five).w .five := by
  rw [tys_nu]; simp [tysObs]

/-- **Every masked-calibrated label at `d₅` is `δ_{(5,5)}`**, for every procedure `C` and every
state assignment `s`: a full-support self-model `C[d₅ ↦ m]` realizes `O₅` with mass `m(five) > 0`
and its `O₅`-conditional is `δ_{(5,5)}` (Remark 3.7's branch-fact); the vacuity disjunct is
impossible (the uniform self-model realizes `O₅`).
Source: `sl-amendments.md` SL-17 ("under masked … calibration `π = 0` is the only calibrated
label at `d₅`"); `P13.md` P13-10′ ("every full-support self-model `m` gives
`ν_{C[d₅↦m]}(· ∣ O₅) = δ_{(5,5)}`")
Kind: P
Fidelity: exact (LF, vacuity reading — the definition of record)
Hyps: (a) masked-OC at `d₅` -/
theorem tys_maskedOCAt_five_pr (s : Five10 → State TysW ℚ) (C : Proc Five10 (fun _ => Five10) ℚ)
    (h : MaskedOCAt s tysObs C toldYouSo .five) (X : Finset TysW) :
    (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0 := by
  rcases h with ⟨C', ⟨m, hm, rfl⟩, hpos, hcl⟩ | ⟨-, hvac⟩
  · have h1 := hcl.1 X
    rw [tys_nu_inter_obs_five, tys_nu_obs_five] at h1
    rw [tys_nu_obs_five] at hpos
    split_ifs at h1 ⊢ with hX
    · exact mul_right_cancel₀ hpos.ne' (by rw [h1, one_mul])
    · exact (mul_eq_zero.mp h1).resolve_right hpos.ne'
  · exfalso
    have := hvac (C.deviate .five FinDistr.uniform)
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [tys_nu_obs_five, Proc.deviate_same] at this
    exact (FinDistr.uniform_w_pos (K := ℚ) (α := Five10) .five).ne' this

/-- `nuPoly (X ∩ O₅) = [(5,5) ∈ X] · nuPoly O₅` on `B_P`. Source: none: infrastructure. Kind: L -/
theorem tys_nuPoly_inter_obs_five (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    nuPoly C toldYouSo (X ∩ tysObs .five) =
      if (Five10.five, Five10.five) ∈ X then nuPoly C toldYouSo (tysObs .five) else 0 := by
  rw [tys_nuPoly, tys_nuPoly]; simp [tysObs]

/-- **Every limit-calibrated label at `d₅` is `δ_{(5,5)}`**, for every procedure and state
assignment: `nuPoly(X ∩ O₅)` is `nuPoly(O₅)` or `0`, so the limiting conditional is `1` or `0`.
Source: `sl-amendments.md` SL-17 ("under … limit calibration `π = 0` is the only calibrated
label at `d₅`"); `P13.md` P13-10′ ("`C^ε(d₅)(5) = ε/2 > 0` and `ν_ε(· ∣ O₅) = δ_{(5,5)}` at
every `ε`")
Kind: P
Fidelity: exact (the algebraic limit of record)
Hyps: (a) limit-OC at `d₅` -/
theorem tys_limitOCAt_five_pr (s : Five10 → State TysW ℚ) (C : Proc Five10 (fun _ => Five10) ℚ)
    (h : LimitOCAt s tysObs C toldYouSo .five) (X : Finset TysW) :
    (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0 := by
  have hne := tys_nuPoly_obs_five_ne_zero C
  rw [(h hne).1 X]
  unfold limitCond
  rw [tys_nuPoly_inter_obs_five]
  have hc : (nuPoly C toldYouSo (tysObs .five)).coeff
      (nuPoly C toldYouSo (tysObs .five)).natTrailingDegree ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne
  by_cases hX : (Five10.five, Five10.five) ∈ X
  · rw [if_pos hX, if_pos hX]; exact div_self hc
  · rw [if_neg hX, if_neg hX]; simp

/-! ## D1 on Told-You-So (CA-17′) -/

/-- **D1 approves `C₀`** with the stipulated states: limit-calibrated (`tys_fiveTen_limitOC`)
and `T_EDT`-approved (`A⁺ = {five}` at `d₅`, `{ten}` at `d₁₀`, each the played act).
Source: `calibration.md` CA-17′ ("on Told-You-So it approves `C₀`"), CA-20′ (D1 row)
Kind: C
Fidelity: exact -/
theorem procFiveTen_limitStateEdt :
    LimitStateEdt tysObs tysActEv procFiveTen toldYouSo tysState := by
  refine ⟨tys_fiveTen_limitOC, fun d _ _ a ha => ?_⟩
  rw [mem_argmaxPlus]
  cases d <;> cases a <;> simp [procFiveTen] at ha <;> simp [tys_aPlus_five, tys_aPlus_ten]

/-- **D1 rejects `C*` with every state assignment**: any limit-calibrated `s` has
`P_{s₅} = δ_{(5,5)}`, so `A⁺_{d₅} = {five}` and `ten ∈ supp C*(d₅)` is not in the argmax domain.
Source: `calibration.md` CA-17′ ("*rejects* the optimal `C*` (the limit state at `d₅` is
certain of `m=5`)"), CA-20′ (D1 row: Told-You-So `C₀` only)
Kind: P
Fidelity: exact (every `s`)
Hyps: none -/
theorem procTake10_not_limitStateEdt (s : Five10 → State TysW ℚ) :
    ¬ LimitStateEdt tysObs tysActEv procTake10 toldYouSo s := by
  rintro ⟨hlim, hedt⟩
  have hpr := tys_limitOCAt_five_pr s procTake10 (hlim .five (tys_queried .five))
  have hA : APlus s tysActEv .five = {.five} := by
    ext a; cases a <;> simp [APlus, hpr, tysActEv]
  have := hedt .five (tys_queried .five) (by rw [hA]; exact ⟨.five, by simp⟩) .ten
    (by simp [procTake10])
  have hmem := argmaxPlus_subset s tysActEv .five this
  rw [hA] at hmem
  simp at hmem

/-! ## Remark 3.14: traps versus dilemmas -/

section remark314

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)]

/-- **Fails regardless of label** (proposed Remark 3.14, value form): every member of the class
`𝒞 I` (the class may depend on the instantiation's labels, as the zero-respecting class does)
makes the good outcome `v` inconsistent — `V_B(C) < v` — at every `κ`-calibrated instantiation.
SL-17's full definitional sentence: "Say a procedure class fails a stipulation set *regardless
of label* if every member makes the good outcome inconsistent at every κ-calibrated label, and
call the failure a *dilemma* rather than a *trap* if some procedure outside the class attains
more (Definition 21)." This definition renders its first half; the Definition-16 event form
("makes the good outcome inconsistent" literally) is `FailsRegardlessOfLabelEv`.
Source: `sl-amendments.md` SL-17 (proposed Remark 3.14, the definitional sentence's first half);
this package's proposal
Kind: D
Fidelity: variant: "makes the good outcome inconsistent" rendered as `V_B(C) < v` (the good
outcome's value is not attained; the event form is `FailsRegardlessOfLabelEv`), with the class
indexed by the instantiation -/
def FailsRegardlessOfLabel (κ : Sense) (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts ℚ) (𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ))
    (v : ℚ) : Prop :=
  ∀ I ∈ AP, ∀ C ∈ 𝒞 I, IsCalibrated κ obs I.s C I.B → value C I.B < v

/-- **Fails regardless of label, Definition-16 form**: every member of the class makes the
good-outcome *event* `X` `0`-inconsistent — `ν_{B,C}(X) = 0` — at every `κ`-calibrated
instantiation (SL-17's "makes the good outcome inconsistent" read with Definition 16 and
`δ = 0`). For an instantiation-independent class this is Definition 16 member by member
(`failsRegardlessOfLabelEv_iff_makesInconsistent`).
Source: `sl-amendments.md` SL-17 ("every member makes the good outcome inconsistent at every
κ-calibrated label"); [[decision-problems-v2]] §3.2 Definition 16; this package's proposal
Kind: D
Fidelity: exact (Definition 16 with `δ = 0`, the class indexed by the instantiation) -/
def FailsRegardlessOfLabelEv (κ : Sense) (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts ℚ) (𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ))
    (X : Finset Ω) : Prop :=
  ∀ I ∈ AP, ∀ C ∈ 𝒞 I, IsCalibrated κ obs I.s C I.B → nu C I.B X = 0

/-- For an instantiation-independent class, the Definition-16 form is `MakesInconsistent` with
`δ = 0` for every member (`ν ≥ 0` turns `≤ 0` into `= 0`).
Source: [[decision-problems-v2]] §3.2 Definition 16
Kind: L -/
theorem failsRegardlessOfLabelEv_iff_makesInconsistent (κ : Sense) (obs : ι → Finset Ω)
    (AP : AbstractProblem Ω ι acts ℚ) (S : Set (Proc ι acts ℚ)) (X : Finset Ω) :
    FailsRegardlessOfLabelEv κ obs AP (fun _ => S) X ↔
      ∀ C ∈ S, MakesInconsistent κ obs AP C X 0 := by
  constructor
  · intro h C hC I hI hcal
    exact (h I hI C hC hcal).le
  · intro h I hI C hC hcal
    exact le_antisymm (h C hC I hI hcal) (nu_nonneg _ _ _)

/-- **Trap**: the class fails regardless of label, and there is a *way out* — a procedure
outside the class that is itself `κ`-calibrated at some instantiation and attains `v` there.
This renders SL-17's second application ("the family fails at every calibrated label while `C*`
attains `10` (Proposition 8): a trap with a way out"), **not** its definitional clause, which
calls this case a dilemma (findings F12). The way out is required to be calibrated (audit round
1 repair): SL-17's "attains more (Definition 21)" asks only for value, but its "`C*` attains `10`
(Proposition 8)" leans on `C*` being calibrated, and a way out one cannot consistently run is no
way out. A tree with no way out is not a `Trap` (nor a `Dilemma`).
Source: `sl-amendments.md` SL-17 (the application "a trap with a way out"; the definitional
sentence reads "call the failure a *dilemma* rather than a *trap* if some procedure outside the
class attains more", which this package does not follow — F12); this package's proposal
Kind: D
Fidelity: variant: SL-17's applications rather than its definitional clause; the way out must be
`κ`-calibrated where it attains `v` -/
def Trap (κ : Sense) (obs : ι → Finset Ω) (AP : AbstractProblem Ω ι acts ℚ)
    (𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ)) (v : ℚ) : Prop :=
  FailsRegardlessOfLabel κ obs AP 𝒞 v ∧
    ∃ I ∈ AP, ∃ C, C ∉ 𝒞 I ∧ IsCalibrated κ obs I.s C I.B ∧ v ≤ value C I.B

/-- **Dilemma**: the class does *not* fail regardless of label — some member attains `v` at
some `κ`-calibrated instantiation (Remark 5.2's multiplicity: the outcome is a matter of which
self-fulfilling label is stipulated). This renders SL-17's first application ("the
zero-respecting family fails only at the self-fulfilling label … a dilemma of selection"), a
case its definitional sentence does not cover (there the family does not fail regardless of
label); under the definitional sentence read literally, "dilemma" would instead name a failure
regardless of label with an outside procedure attaining more (findings F12).
Source: `sl-amendments.md` SL-17 (the application "a dilemma of selection (Remark 5.2)"); this
package's proposal
Kind: D
Fidelity: variant: SL-17's application rather than its definitional clause; rendered as the
direct negation-with-a-witness of `FailsRegardlessOfLabel` -/
def Dilemma (κ : Sense) (obs : ι → Finset Ω) (AP : AbstractProblem Ω ι acts ℚ)
    (𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ)) (v : ℚ) : Prop :=
  ∃ I ∈ AP, ∃ C ∈ 𝒞 I, IsCalibrated κ obs I.s C I.B ∧ v ≤ value C I.B

/-- A dilemma is not a failure regardless of label. Source: none: infrastructure. Kind: L -/
theorem Dilemma.not_fails {κ : Sense} {obs : ι → Finset Ω} {AP : AbstractProblem Ω ι acts ℚ}
    {𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ)} {v : ℚ} (h : Dilemma κ obs AP 𝒞 v) :
    ¬ FailsRegardlessOfLabel κ obs AP 𝒞 v := by
  rintro hf
  obtain ⟨I, hI, C, hC, hcal, hv⟩ := h
  exact absurd (hf I hI C hC hcal) (not_lt.mpr hv)

/-- The two verdicts are exclusive: a trap is not a dilemma. Source: none: infrastructure.
Kind: L -/
theorem Trap.not_dilemma {κ : Sense} {obs : ι → Finset Ω} {AP : AbstractProblem Ω ι acts ℚ}
    {𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ)} {v : ℚ} (h : Trap κ obs AP 𝒞 v) :
    ¬ Dilemma κ obs AP 𝒞 v :=
  fun hd => hd.not_fails h.1

/-- A trap's way out is in particular a procedure outside the class attaining `v` (the weaker,
value-only clause of SL-17's "attains more (Definition 21)"). Source: none: infrastructure.
Kind: L -/
theorem Trap.wayOut_value {κ : Sense} {obs : ι → Finset Ω} {AP : AbstractProblem Ω ι acts ℚ}
    {𝒞 : Instance Ω ι acts ℚ → Set (Proc ι acts ℚ)} {v : ℚ} (h : Trap κ obs AP 𝒞 v) :
    ∃ I ∈ AP, ∃ C, C ∉ 𝒞 I ∧ v ≤ value C I.B :=
  let ⟨I, hI, C, hC, _, hv⟩ := h.2
  ⟨I, hI, C, hC, hv⟩

end remark314

/-! ### The instance: Told-You-So, the zero-respecting class, the good outcome `10` -/

/-- The abstract problem `Σ_{B_P}`: every state assignment on Told-You-So (the label
`π := P_{s₅}(m=10)` is read off `I.s`).
Source: [[decision-problems-v2]] §7.1; `P13.md` P13-10′ (the label sweep)
Kind: D -/
def sigmaTys : AbstractProblem TysW Five10 (fun _ => Five10) ℚ := {I | I.B = toldYouSo}

/-- The zero-respecting class, relative to an instantiation's labels.
Source: [[decision-problems-v2]] Proposition 8 ("`C₀` any zero-respecting procedure")
Kind: D -/
def zeroRespClass (I : Instance TysW Five10 (fun _ => Five10) ℚ) :
    Set (Proc Five10 (fun _ => Five10) ℚ) :=
  {C | ZeroRespecting I.s tysActEv C}

/-- The label `π = 1` at `d₅`: `s₅` certain of `(5, 10)` (the announced-five, took-ten world,
which no leaf carries), `s₁₀` the stipulated state.
Source: `P13.md` P13-10′ ("sweep of `π ∈ {0, 1/100, 1/2, 1}`"), the `π = 1` member
Kind: D -/
def tysStateOne : Five10 → State TysW ℚ
  | .five => State.dirac (.five, .ten) 10
  | .ten => tysState .ten

/-- `C*` is zero-respecting for the `π = 1` label. Source: `P13.md` P13-10′. Kind: L -/
theorem procTake10_zeroRespecting_one : ZeroRespecting tysStateOne tysActEv procTake10 := by
  intro d _ a ha
  simp only [procTake10, Proc.ofFun_w] at ha
  have ha' : a = .ten := by by_contra h; simp [h] at ha
  subst ha'
  cases d <;> simp [APlus, tysStateOne, tysState, State.dirac_pr, tysActEv]

/-- `C*` is strictly calibrated for the `π = 1` label: vacuous at `d₅` (`ν(O₅) = 0`), and at
`d₁₀` the stipulated state is the `O₁₀`-conditional (as in `tys_take10_strictOC`).
Source: `P13.md` P13-10′ ("Definition 8 is *vacuous* at `d₅`")
Kind: L -/
theorem procTake10_strictOC_one : StrictOC tysStateOne tysObs procTake10 toldYouSo := by
  intro d hd
  cases d
  · intro hpos
    rw [tys_nu_obs_five] at hpos
    simp [procTake10] at hpos
  · exact tys_take10_strictOC .ten hd

/-- **Told-You-So under strict calibration is a dilemma** for the zero-respecting class: at the
label `π = 1` the member `C*` is zero-respecting, strictly calibrated and attains `10`.
Source: `sl-amendments.md` SL-17 ("under strict observation calibration the zero-respecting
family fails only at the self-fulfilling label … a dilemma of selection"); `P13.md` P13-10′
Kind: P
Fidelity: exact
Hyps: none -/
theorem tys_strict_dilemma : Dilemma .strict tysObs sigmaTys zeroRespClass 10 :=
  ⟨⟨toldYouSo, tysStateOne⟩, rfl, procTake10, procTake10_zeroRespecting_one,
    procTake10_strictOC_one, by rw [procTake10_value]⟩

/-- Hence the zero-respecting class does **not** fail regardless of label at the strict sense.
Source: `sl-amendments.md` SL-17
Kind: L -/
theorem tys_strict_not_fails :
    ¬ FailsRegardlessOfLabel .strict tysObs sigmaTys zeroRespClass 10 :=
  tys_strict_dilemma.not_fails

/-- For a label with `P_{s₅} = δ_{(5,5)}`, `A⁺_{d₅} = {five}`. Source: none: infrastructure.
Kind: L -/
theorem tys_aPlus_five_of_delta (s : Five10 → State TysW ℚ)
    (hpr : ∀ X, (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0) :
    APlus s tysActEv .five = {.five} := by
  ext a; cases a <;> simp [APlus, hpr, tysActEv]

/-- A zero-respecting procedure for a label with `P_{s₅} = δ_{(5,5)}` puts no mass on `ten` at
`d₅`. Source: none: infrastructure (the common step of the two trap verdicts). Kind: L -/
theorem tys_zeroRespecting_delta_ten (s : Five10 → State TysW ℚ)
    (C : Proc Five10 (fun _ => Five10) ℚ)
    (hpr : ∀ X, (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0)
    (h : ZeroRespecting s tysActEv C) : (C .five).w .ten = 0 := by
  have hA := tys_aPlus_five_of_delta s hpr
  by_contra hne
  have hpos : 0 < (C .five).w .ten := lt_of_le_of_ne ((C .five).nonneg _) (Ne.symm hne)
  have := h .five (by rw [hA]; exact ⟨.five, by simp⟩) .ten hpos
  rw [hA] at this
  simp at this

/-- A zero-respecting procedure for a label with `P_{s₅} = δ_{(5,5)}` has `V = 5`.
Source: none: infrastructure (the common step of the two trap verdicts)
Kind: L -/
theorem tys_value_of_zeroRespecting_delta (s : Five10 → State TysW ℚ)
    (C : Proc Five10 (fun _ => Five10) ℚ)
    (hpr : ∀ X, (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0)
    (h : ZeroRespecting s tysActEv C) : value C toldYouSo = 5 := by
  rw [toldYouSo_value_all, tys_zeroRespecting_delta_ten s C hpr h]; ring

/-- `ν_C({m = 10}) = C(d₅)(ten) · C(d₁₀)(ten)` on `B_P` (the act-event `{m = 10}` at either point
is `{(5,10), (10,10)}`, and `(5,10)` is no leaf). Source: none: infrastructure. Kind: L -/
theorem tys_nu_ten_event (C : Proc Five10 (fun _ => Five10) ℚ) (d : Five10) :
    nu C toldYouSo (tysActEv d .ten) = (C .five).w .ten * (C .ten).w .ten := by
  rw [tys_nu]; simp [tysActEv]

/-- `C*` is not zero-respecting for any label with `P_{s₅} = δ_{(5,5)}` (it plays `ten ∉ A⁺_{d₅}`).
Source: v2 Prop. 8. Kind: L -/
theorem procTake10_not_zeroRespecting_of_delta (s : Five10 → State TysW ℚ)
    (hpr : ∀ X, (s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0) :
    ¬ ZeroRespecting s tysActEv procTake10 := by
  intro h
  have hA := tys_aPlus_five_of_delta s hpr
  have := h .five (by rw [hA]; exact ⟨.five, by simp⟩) .ten (by simp [procTake10])
  rw [hA] at this
  simp at this

/-- `C*` is not zero-respecting for the stipulated states. Source: v2 Prop. 8. Kind: L -/
theorem procTake10_not_zeroRespecting : ¬ ZeroRespecting tysState tysActEv procTake10 :=
  procTake10_not_zeroRespecting_of_delta tysState fun X => by
    simp only [tysState]; rw [State.dirac_pr]

/-! ### The Definition-16 form of the two trap verdicts -/

/-- **Masked, Definition-16 form**: every zero-respecting procedure makes the good-outcome event
`{m = 10}` `0`-inconsistent at every masked-calibrated instantiation of `Σ_{B_P}` — the label
is `δ_{(5,5)}` at `d₅`, so the member puts no mass on `ten` there and `ν(m=10) = 0`.
Source: `sl-amendments.md` SL-17 ("every member makes the good outcome inconsistent at every
κ-calibrated label", masked); [[decision-problems-v2]] Definition 16; `P13.md` P13-10′
Kind: P
Fidelity: exact (LF, vacuity reading; Definition 16 with `δ = 0`)
Hyps: none -/
theorem tys_masked_fails_ev :
    FailsRegardlessOfLabelEv .masked tysObs sigmaTys zeroRespClass (tysActEv .five .ten) := by
  intro I hI C hC hcal
  simp only [sigmaTys, Set.mem_setOf_eq] at hI
  simp only [zeroRespClass, Set.mem_setOf_eq] at hC
  simp only [IsCalibrated] at hcal
  rw [hI] at hcal ⊢
  have hpr := tys_maskedOCAt_five_pr I.s C (hcal .five (tys_queried .five))
  rw [tys_nu_ten_event, tys_zeroRespecting_delta_ten I.s C hpr hC, zero_mul]

/-- **Limit, Definition-16 form**: the same with `tys_limitOCAt_five_pr`.
Source: `sl-amendments.md` SL-17 (limit); [[decision-problems-v2]] Definition 16; `P13.md`
P13-10′
Kind: P
Fidelity: exact (algebraic limit of record; Definition 16 with `δ = 0`)
Hyps: none -/
theorem tys_limit_fails_ev :
    FailsRegardlessOfLabelEv .limit tysObs sigmaTys zeroRespClass (tysActEv .five .ten) := by
  intro I hI C hC hcal
  simp only [sigmaTys, Set.mem_setOf_eq] at hI
  simp only [zeroRespClass, Set.mem_setOf_eq] at hC
  simp only [IsCalibrated] at hcal
  rw [hI] at hcal ⊢
  have hpr := tys_limitOCAt_five_pr I.s C (hcal .five (tys_queried .five))
  rw [tys_nu_ten_event, tys_zeroRespecting_delta_ten I.s C hpr hC, zero_mul]

/-- **On `B_P` the Definition-16 form implies the value form** for any class and sense:
`V = 5 + 5·ν(m=10)`, so `ν(m=10) = 0` gives `V = 5 < 10`. (The converse fails in general —
`V = 15/2 < 10` at `u = 1`, `v = ½` with `ν(m=10) = ½` — but not at any calibrated label of a
zero-respecting member, where both hold.)
Source: none: infrastructure (links the two renderings of SL-17's "makes the good outcome
inconsistent")
Kind: L -/
theorem tys_failsEv_imp_fails (κ : Sense)
    (𝒞 : Instance TysW Five10 (fun _ => Five10) ℚ → Set (Proc Five10 (fun _ => Five10) ℚ))
    (h : FailsRegardlessOfLabelEv κ tysObs sigmaTys 𝒞 (tysActEv .five .ten)) :
    FailsRegardlessOfLabel κ tysObs sigmaTys 𝒞 10 := by
  intro I hI C hC hcal
  have h0 := h I hI C hC hcal
  have hB : I.B = toldYouSo := hI
  rw [hB] at h0 ⊢
  rw [tys_nu_ten_event] at h0
  have hv : value C toldYouSo = 5 := by
    rw [toldYouSo_value_all]; linear_combination 5 * h0
  rw [hv]; norm_num

/-! ### The calibrated way out -/

/-- `C*[d₁₀ ↦ uniform]` realizes `O₁₀` (with mass `1`). Source: none: infrastructure. Kind: L -/
theorem tys_take10_uniform_nu_obs_ten :
    0 < nu (procTake10.deviate .ten FinDistr.uniform) toldYouSo (tysObs .ten) := by
  rw [tys_nu]
  simp [tysObs, Proc.deviate, procTake10, Function.update_of_ne, Fintype.card_pos]

/-- **The way-out label**: `s₅ = δ_{(5,5)}` (the stipulated state, as every masked-calibrated
label at `d₅` must be) and `s₁₀` the `O₁₀`-conditional of the uniform self-model
`C*[d₁₀ ↦ uniform]` — `P_{s₁₀} = ½δ_{(10,10)} + ½δ_{(10,5)}`, `V_{s₁₀}` its conditional payoff.
At this label `C*` is masked-calibrated (the stipulated `tysState`, with `s₁₀ = δ_{(10,10)}`,
is *not* masked-calibrated for `C*`: dp-calibration findings F2).
Source: `sl-amendments.md` SL-17 ("`C*` attains `10` (Proposition 8): a trap with a way out"),
the label at which the way out is consistently runnable; this package's choice
Kind: D -/
noncomputable def tysStateWayOut : Five10 → State TysW ℚ
  | .five => tysState .five
  | .ten => calibratedState (procTake10.deviate .ten FinDistr.uniform) toldYouSo (tysObs .ten)
      tys_take10_uniform_nu_obs_ten

/-- `P_{s₅} = δ_{(5,5)}` at the way-out label. Source: none: infrastructure. Kind: L -/
theorem tysStateWayOut_five_pr (X : Finset TysW) :
    (tysStateWayOut .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0 := by
  simp only [tysStateWayOut, tysState]; rw [State.dirac_pr]

/-- **`C*` is masked-calibrated at the way-out label** (LF, vacuity reading): at `d₅` the
full-support self-model `C*[d₅ ↦ uniform]` realizes `O₅` with `O₅`-conditional `δ_{(5,5)}`; at
`d₁₀` the self-model `C*[d₁₀ ↦ uniform]` realizes `O₁₀` and `s₁₀` is its calibrated state.
Source: `sl-amendments.md` SL-17 ("`C*` attains `10` (Proposition 8)" — the calibration clause
of Proposition 8 is false at `tysState` (dp-calibration F2) and true here)
Kind: N+
Fidelity: exact (LF, vacuity reading) -/
theorem procTake10_maskedOC_wayOut : MaskedOC tysStateWayOut tysObs procTake10 toldYouSo := by
  intro d _
  cases d
  · refine Or.inl ⟨procTake10.deviate .five FinDistr.uniform,
      ⟨_, fun a => FinDistr.uniform_w_pos a, rfl⟩, ?_, fun X => ?_, fun X _ _ => ?_⟩
    · rw [tys_nu]; simp [tysObs, Proc.deviate, procTake10, Fintype.card_pos]
    · rw [tys_nu, tys_nu]
      simp [tysObs, tysStateWayOut, tysState, State.dirac_pr, Proc.deviate, procTake10]
    · rw [tys_nu, tys_paySum]
      simp [tysObs, tysStateWayOut, tysState, Proc.deviate, procTake10, Five10.val]
      split_ifs <;> ring
  · exact Or.inl ⟨_, ⟨_, fun a => FinDistr.uniform_w_pos a, rfl⟩, tys_take10_uniform_nu_obs_ten,
      strictClausesAt_calibratedState tysObs _ toldYouSo tysStateWayOut .ten _ rfl⟩

/-- `C*` is outside the zero-respecting class at the way-out label. Source: v2 Prop. 8. Kind: L -/
theorem procTake10_not_zeroRespecting_wayOut : ¬ ZeroRespecting tysStateWayOut tysActEv procTake10 :=
  procTake10_not_zeroRespecting_of_delta tysStateWayOut tysStateWayOut_five_pr

/-- **Told-You-So under masked calibration is a trap** for the zero-respecting class: at every
masked-calibrated label `P_{s₅} = δ_{(5,5)}`, so every member takes `five` and gets `5 < 10`
(Definition-16 form: `tys_masked_fails_ev`), while `C* ∉ 𝒞` attains `10` at a label at which it
is itself masked-calibrated (`tysStateWayOut`, `procTake10_maskedOC_wayOut`).
Source: `sl-amendments.md` SL-17 ("under masked … calibration `π = 0` is the only calibrated
label at `d₅` … a trap with a way out"); `P13.md` P13-10′
Kind: P
Fidelity: exact (LF, vacuity reading; `Trap` renders SL-17's application, not its definitional
clause — F12)
Hyps: none -/
theorem tys_masked_trap : Trap .masked tysObs sigmaTys zeroRespClass 10 :=
  ⟨tys_failsEv_imp_fails _ _ tys_masked_fails_ev, ⟨toldYouSo, tysStateWayOut⟩, rfl, procTake10,
    procTake10_not_zeroRespecting_wayOut, procTake10_maskedOC_wayOut, by rw [procTake10_value]⟩

/-- **Told-You-So under limit calibration is a trap** for the zero-respecting class (the same
argument with `tys_limitOCAt_five_pr`); the way out `C*` is limit-calibrated at the stipulated
`tysState` itself (`tys_take10_limitOC`).
Source: `sl-amendments.md` SL-17 ("under … limit calibration"); `P13.md` P13-10′
Kind: P
Fidelity: exact (algebraic limit of record; `Trap` renders SL-17's application — F12)
Hyps: none -/
theorem tys_limit_trap : Trap .limit tysObs sigmaTys zeroRespClass 10 :=
  ⟨tys_failsEv_imp_fails _ _ tys_limit_fails_ev, ⟨toldYouSo, tysState⟩, rfl, procTake10,
    procTake10_not_zeroRespecting, tys_take10_limitOC, by rw [procTake10_value]⟩

/-- Hence under masked and limit calibration Told-You-So is no dilemma for the zero-respecting
class. Source: `sl-amendments.md` SL-17. Kind: L -/
theorem tys_masked_limit_not_dilemma :
    ¬ Dilemma .masked tysObs sigmaTys zeroRespClass 10 ∧
      ¬ Dilemma .limit tysObs sigmaTys zeroRespClass 10 :=
  ⟨tys_masked_trap.not_dilemma, tys_limit_trap.not_dilemma⟩

/-- At any instantiation of `Σ_{B_P}` whose label at `d₅` is `δ_{(5,5)}`, `C*` is outside the
zero-respecting class and attains `10`. Source: none: infrastructure. Kind: L -/
theorem tys_wayOut_of_delta (I : Instance TysW Five10 (fun _ => Five10) ℚ) (hI : I ∈ sigmaTys)
    (hpr : ∀ X, (I.s .five).pr X = if (Five10.five, Five10.five) ∈ X then 1 else 0) :
    procTake10 ∉ zeroRespClass I ∧ 10 ≤ value procTake10 I.B := by
  have hB : I.B = toldYouSo := hI
  exact ⟨procTake10_not_zeroRespecting_of_delta I.s hpr, by rw [hB, procTake10_value]⟩

/-- **The way out is available at every masked-calibrated instantiation**: wherever any
procedure is masked-calibrated on `Σ_{B_P}`, `C*` is outside the zero-respecting class for that
label and attains `10` there (the way out does not have to move to a different label than the
one at which the class fails).
Source: `sl-amendments.md` SL-17 ("the family fails at every calibrated label while `C*` attains
`10`"), the stronger reading in which the attainment is at the same labels
Kind: P
Fidelity: stronger: for every procedure's masked-calibrated instantiation, not only the class's
Hyps: none -/
theorem tys_masked_wayOut_everywhere (I : Instance TysW Five10 (fun _ => Five10) ℚ)
    (hI : I ∈ sigmaTys) (C : Proc Five10 (fun _ => Five10) ℚ)
    (hcal : IsCalibrated .masked tysObs I.s C I.B) :
    procTake10 ∉ zeroRespClass I ∧ 10 ≤ value procTake10 I.B := by
  have hB : I.B = toldYouSo := hI
  simp only [IsCalibrated] at hcal
  rw [hB] at hcal
  exact tys_wayOut_of_delta I hI (tys_maskedOCAt_five_pr I.s C (hcal .five (tys_queried .five)))

/-- The same at every limit-calibrated instantiation.
Source: `sl-amendments.md` SL-17 (limit)
Kind: P
Fidelity: stronger: for every procedure's limit-calibrated instantiation
Hyps: none -/
theorem tys_limit_wayOut_everywhere (I : Instance TysW Five10 (fun _ => Five10) ℚ)
    (hI : I ∈ sigmaTys) (C : Proc Five10 (fun _ => Five10) ℚ)
    (hcal : IsCalibrated .limit tysObs I.s C I.B) :
    procTake10 ∉ zeroRespClass I ∧ 10 ≤ value procTake10 I.B := by
  have hB : I.B = toldYouSo := hI
  simp only [IsCalibrated] at hcal
  rw [hB] at hcal
  exact tys_wayOut_of_delta I hI (tys_limitOCAt_five_pr I.s C (hcal .five (tys_queried .five)))

end Cleanroom.Decision.DpDevicesCatalog
