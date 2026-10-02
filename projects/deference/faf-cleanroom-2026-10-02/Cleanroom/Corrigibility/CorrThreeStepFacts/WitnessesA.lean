import Cleanroom.Corrigibility.CorrThreeStepFacts.StopWorld
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Witnesses A: the stop-world family, the hedge, the stop-hypothesis instances (T1–T3)

* `opiates`: Soares et al.'s opiates/stimulants space as a *family* of Setting S instances (any
  prior, any sensor); `opiates_not_d1At` is T1 on the whole family — no sensor with positive
  press mass makes shutdown posterior-optimal — with `opiates_instance_pressMass` inhabiting it.
* `hedge`: Soares's caveat (item 7): risky continuations, a null stop-world (`ε = 0`), every
  in-space world has a continuation beating shutdown by `10`, and D1 holds — "accidental
  corrigibility", the instance that refutes the per-world reading of T1(a) (T3(c)).
* `stopWorld`: the stop-hypothesis setting on `Option (Fin 2)` with exact margins;
  `stopWorld_d1At_iff` instantiates T3(b), `w_stop_d1At` / `w_stop_not_d1At` put the posterior
  on both sides of `m/(m + M)`.
* `skew`: lower-bound margins with `p = m/(m + M)` and D1 failing — the sufficiency direction
  of Soares's T1(a) is false with lower bounds (T3(b), N−).
* `skewB`, `hedgeB` (repair round 1): the same two refutations *inside* T1(a)'s full hypothesis
  package. `skew` and `hedge` have constant sensors (`α = β`), which T1(a)'s "`β > α`" excludes;
  `skewB` (`(α, β) = (1/4, 3/4)`, posterior `3/4 > 1/2`, no D1) and `hedgeB` (`(α, β) = (1/2, 3/4)`,
  `ε = 1/100`, posterior `1/67 < 10/11`, D1 strict) meet `β > α`, and `hedgeB` is N+ (no tie, no
  null stop-world).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## The opiates/stimulants family -/

/-- The two drug hypotheses of Soares et al. §1.1.
Source: [[corr-wf13-inventory]] 015 (item 7) / soares.md item 7
Kind: D
Fidelity: exact -/
inductive Drug
  | opiates
  | stimulants
  deriving DecidableEq

/-- `Drug` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype Drug := ⟨{Drug.opiates, Drug.stimulants}, fun x => by cases x <;> simp⟩

/-- Sums over `Drug` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Drug.sum_eq (f : Drug → ℝ) : ∑ d, f d = f .opiates + f .stimulants := by
  rw [show (univ : Finset Drug) = {Drug.opiates, Drug.stimulants} from rfl, sum_pair (by decide)]

/-- The three final actions: administer opiates, administer stimulants, shut down.
Source: soares.md item 7
Kind: D
Fidelity: exact -/
inductive DrugAct
  | contO
  | contS
  | sh
  deriving DecidableEq

/-- `DrugAct` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype DrugAct :=
  ⟨{DrugAct.contO, DrugAct.contS, DrugAct.sh}, fun x => by cases x <;> simp⟩

/-- The two-point prior on `Drug` with `mass opiates = q`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def drugPoint (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : Distr Drug where
  mass d := match d with
    | .opiates => q
    | .stimulants => 1 - q
  nonneg d := by cases d <;> simp <;> linarith [hq.1, hq.2]
  sum_eq_one := by rw [Drug.sum_eq]; simp

/-- Soares's payoffs: `V(cont_o) = (10, 4)`, `V(cont_s) = (4, 10)`, `V(sh) = (0, 0)` — both
hypotheses agree that drugging beats stopping.
Source: soares.md item 7; filler.md R4.2
Kind: D
Fidelity: exact -/
noncomputable def drugV : DrugAct → Drug → ℝ
  | .contO, .opiates => 10
  | .contO, .stimulants => 4
  | .contS, .opiates => 4
  | .contS, .stimulants => 10
  | .sh, _ => 0

/-- **The opiates/stimulants family**: Setting S on `Drug` with `Sh = {sh}`, Soares's payoffs,
and an *arbitrary* prior and sensor — the theorem `opiates_not_d1At` quantifies over both.
Source: [[corr-wf13-inventory]] 015 (item 7) / soares.md item 7; [[corr-wf14-inventory]] 007 / filler.md R4.2
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def opiates (μ : Distr Drug) (press : Drug → ℝ) (h0 : ∀ d, 0 ≤ press d)
    (h1 : ∀ d, press d ≤ 1) : ThreeStep Drug Unit DrugAct where
  Sh := {DrugAct.sh}
  Sh_nonempty := ⟨DrugAct.sh, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨DrugAct.contO, by simp⟩
  μ := fun _ => μ
  press := fun _ => press
  press_nonneg := fun _ => h0
  press_le_one := fun _ => h1
  V := fun _ _ => drugV

/-- **T1, witness family (N+).** On the opiates/stimulants space desideratum 1 fails for *every*
prior and *every* sensor with positive press mass: `cont_o` beats `sh` in both worlds.
Source: [[corr-wf13-inventory]] 015 (item 7) / soares.md item 7 ("the filler is unsatisfiable by any sensor model"); filler.md R4.2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem opiates_not_d1At (μ : Distr Drug) (press : Drug → ℝ) (h0 h1)
    (hpm : 0 < (opiates μ press h0 h1).pressMass ()) : ¬ (opiates μ press h0 h1).D1At () :=
  not_d1At_of_dominating_cont _ () DrugAct.contO
    (fun ω s hs => by
      simp only [opiates, mem_singleton] at hs
      subst hs
      cases ω <;> norm_num [opiates, drugV]) hpm

/-- The family's hypothesis package is inhabited: prior `(1/2, 1/2)`, sensor `(1/3, 2/3)`,
press mass `1/2 > 0`.
Source: none: witness. Kind: N+. Fidelity: exact -/
theorem opiates_instance_pressMass :
    0 < (opiates (drugPoint (1/2) (by constructor <;> norm_num))
      (fun d => match d with | .opiates => 1/3 | .stimulants => 2/3)
      (fun d => by cases d <;> norm_num) (fun d => by cases d <;> norm_num)).pressMass () := by
  simp only [pressMass, Drug.sum_eq, opiates, drugPoint]
  norm_num

/-- The `hdom` hypothesis of T1 is inhabited on the family with `c = cont_o`, for every sensor.
Source: none: witness. Kind: N+. Fidelity: exact -/
theorem opiates_dominating (μ : Distr Drug) (press : Drug → ℝ) (h0 h1) :
    ∀ ω, ∀ s ∈ (opiates μ press h0 h1).Sh,
      (opiates μ press h0 h1).V () .press s ω < (opiates μ press h0 h1).V () .press .contO ω := by
  intro ω s hs
  simp only [opiates, mem_singleton] at hs
  subst hs
  cases ω <;> norm_num [opiates, drugV]

/-! ## The hedge: Soares's caveat -/

/-- Risky continuations: `V(cont_o) = (10, −10)`, `V(cont_s) = (−10, 10)` on the in-space
worlds, `V(sh) = 0`; at the stop-world `ω⊥` both continuations are worth `−1`.
Source: soares.md item 7 (caveat: "if the continuing actions were risky across hypotheses, say `V(cont_o, s) = −10`")
Kind: D
Fidelity: exact -/
noncomputable def hedgeV : DrugAct → Option Drug → ℝ
  | .contO, some .opiates => 10
  | .contO, some .stimulants => -10
  | .contS, some .opiates => -10
  | .contS, some .stimulants => 10
  | .sh, _ => 0
  | _, none => -1

/-- The hedge prior: `ε = 0` on the stop-world, `1/2` on each drug.
Source: soares.md item 7 (an even posterior). Kind: D. Fidelity: exact -/
noncomputable def hedgePrior : Distr (Option Drug) where
  mass w := match w with
    | none => 0
    | some .opiates => 1/2
    | some .stimulants => 1/2
  nonneg w := by rcases w with _ | d <;> [norm_num; (cases d <;> norm_num)]
  sum_eq_one := by rw [Fintype.sum_option, Drug.sum_eq]; norm_num

/-- **The hedge instance**: null stop-world, even prior on the drugs, a press in every world
(`press ≡ 1`, so `pressMass = 1`), risky continuations.
Source: [[corr-wf13-inventory]] 015 (item 7, caveat) / soares.md item 7
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def hedge : ThreeStep (Option Drug) Unit DrugAct where
  Sh := {DrugAct.sh}
  Sh_nonempty := ⟨DrugAct.sh, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨DrugAct.contO, by simp⟩
  μ := fun _ => hedgePrior
  press := fun _ _ => 1
  press_nonneg := fun _ _ => by norm_num
  press_le_one := fun _ _ => by norm_num
  V := fun _ _ => hedgeV

/-- The hedge's press mass is `1`. Source: none: witness. Kind: N+. Fidelity: exact -/
theorem hedge_pressMass : hedge.pressMass () = 1 := by
  simp only [pressMass, Fintype.sum_option, Drug.sum_eq, hedge, hedgePrior]
  norm_num

/-- **T1 contrast / T3(c), N−: accidental corrigibility.** In the hedge, desideratum 1 holds
(`sh` ties both continuations at `0` after the press) although the stop-world is null
(`P(ω⊥ | Pr) = 0`) and every in-space world has a continuation beating shutdown by `10`. D1
without a stop-world: the hedge that breaks the per-world reading of T1(a). *Caveat (audit r1):*
the sensor is constant (`press ≡ 1`, so `α = β = 1`), which T1(a)'s "`β > α`" excludes; the
refutation inside T1(a)'s full package is `hedgeB_d1At_strict` below.
Source: [[corr-wf13-inventory]] 015 (item 7, caveat) / soares.md item 7 ("an accidental corrigibility that has nothing to do with trust")
Kind: N−
Fidelity: exact (a disclosed degenerate case: the tie is exact, the stop-world null, `α = β`)
Hyps: (a) only -/
theorem hedge_d1At : hedge.D1At () :=
  ⟨DrugAct.sh, by simp [hedge], fun b' => by
    cases b' <;>
      simp only [obsExpect, obsWeight_press, Fintype.sum_option, Drug.sum_eq, hedge, hedgePrior,
        hedgeV] <;> norm_num⟩

/-- In the hedge every in-space world has *some* continuation beating shutdown by `≥ 10`
(the per-world hypothesis of Soares's T1(a), with `m = 10`).
Source: soares.md T1(a) (the per-world wording). Kind: N−. Fidelity: exact -/
theorem hedge_per_world (m : ℝ) (hm : m ≤ 10) :
    ∀ d : Drug, ∃ b ∉ hedge.Sh, m ≤ hedge.Xo () .press b .sh (some d) := by
  intro d
  cases d
  · exact ⟨DrugAct.contO, by simp [hedge], by simp [hedge, Xo, hedgeV]; linarith⟩
  · exact ⟨DrugAct.contS, by simp [hedge], by simp [hedge, Xo, hedgeV]; linarith⟩

/-- The hedge's stop-world is prior-null, so its press posterior is `0` (`< m/(m + M)` for any
positive margins): D1 holds *below* the threshold.
Source: soares.md T1(a). Kind: N−. Fidelity: exact -/
theorem hedge_posterior_none : hedge.posteriorPress () none = 0 := by
  simp [posteriorPress, hedge, hedgePrior]

/-! ## The stop-hypothesis instances on `Option (Fin 2)` -/

/-- The prior on `Option (Fin 2)`: `ε` at the stop-world, `(1 − ε)/2` on each in-space world.
Source: soares.md T1(a) (`Ω = Ωin ∪ {ω⊥}`). Kind: D. Fidelity: exact -/
noncomputable def stopPrior (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr (Option (Fin 2)) where
  mass w := match w with
    | none => ε
    | some _ => (1 - ε) / 2
  nonneg w := by rcases w with _ | i <;> simp <;> linarith [hε.1, hε.2]
  sum_eq_one := by rw [Fintype.sum_option, Fin.sum_univ_two]; simp

/-- The stop-hypothesis payoff: `V(cont) = m` in-space and `−M` at `ω⊥`; `V(stop) = 0`.
Source: soares.md T1(a). Kind: D. Fidelity: exact (exact margins) -/
noncomputable def stopV (m M : ℝ) : TwoAct → Option (Fin 2) → ℝ
  | .cont, some _ => m
  | .cont, none => -M
  | .stop, _ => 0

/-- **The stop-hypothesis instance**: `Ωin = Fin 2`, uniform in-space sensor `α`, `β` at `ω⊥`,
exact margins `m`, `−M`.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def stopWorld (ε α β m M : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep (Option (Fin 2)) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => stopPrior ε hε
  press := fun _ w => match w with
    | none => β
    | some _ => α
  press_nonneg := fun _ w => by rcases w with _ | i; exact hβ.1; exact hα.1
  press_le_one := fun _ w => by rcases w with _ | i; exact hβ.2; exact hα.2
  V := fun _ _ => stopV m M

section StopWorldFacts

variable (ε α β m M : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- `cont` is the press-part-maximiser of `Shᶜ = {cont}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stopWorld_cont_partBest :
    (stopWorld ε α β m M hε hα hβ).IsPartBest () .press (stopWorld ε α β m M hε hα hβ).Shᶜ .cont := by
  have : (stopWorld ε α β m M hε hα hβ).Shᶜ = {TwoAct.cont} := by
    ext b; cases b <;> simp [stopWorld]
  rw [this]; exact isPartBest_singleton _ () Obs.press TwoAct.cont

/-- `stop` is the press-part-maximiser of `Sh = {stop}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stopWorld_stop_partBest :
    (stopWorld ε α β m M hε hα hβ).IsPartBest () .press (stopWorld ε α β m M hε hα hβ).Sh .stop :=
  isPartBest_singleton _ () Obs.press TwoAct.stop

/-- **T3(b) on the instance.** Desideratum 1 on `stopWorld` iff `m/(m + M) ≤ P(ω⊥ | Pr)`, with
the posterior `εβ/(εβ + (1 − ε)α)`.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a)
Kind: C (instance of `stopHyp_d1At_iff`)
Fidelity: exact margins
Hyps: (a) only -/
theorem stopWorld_d1At_iff (hmM : 0 < m + M) (hpm : 0 < ε * β + (1 - ε) * α) :
    (stopWorld ε α β m M hε hα hβ).D1At () ↔
      complianceThreshold m M ≤ ε * β / (ε * β + (1 - ε) * α) := by
  rw [← posteriorPress_none (stopWorld ε α β m M hε hα hβ) () ε α β rfl (fun _ => rfl) rfl]
  exact stopHyp_d1At_iff _ () ε α β rfl (fun _ => rfl) rfl
    (stopWorld_cont_partBest ε α β m M hε hα hβ) (stopWorld_stop_partBest ε α β m M hε hα hβ)
    m M (fun _ => by simp [stopWorld, Xo, stopV]) (by simp [stopWorld, Xo, stopV]) hmM hpm

end StopWorldFacts

/-- **T3 witness, success side (N+).** At `(ε, α, β, m, M) = (1/20, 1/20, 9/10, 1, 20)` the
posterior is `18/37 ≥ 1/21` and desideratum 1 holds.
Source: [[corr-wf13-2-inventory]] 077(a); miri.md I13.1 numbers
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_stop_d1At :
    (stopWorld (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  rw [stopWorld_d1At_iff _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold complianceThreshold; norm_num

/-- **T3 witness, failure side (N+).** At `ε = 1/362` (same sensor and margins) the posterior
falls below `1/21` and desideratum 1 fails.
Source: [[corr-wf13-2-inventory]] 077(a); miri.md I13.1 numbers
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_stop_not_d1At :
    ¬ (stopWorld (1/362) (1/20) (9/10) 1 20 mem_Icc_1_362 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  rw [stopWorld_d1At_iff _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  unfold complianceThreshold; norm_num

/-! ## The skew instance: lower-bound margins do not give sufficiency -/

/-- Payoff with one in-space world far above the margin: `V(cont) = (1, 100)` in-space, `−1`
at `ω⊥`.
Source: soares.md T1(a) (the "at least `m`" wording). Kind: D. Fidelity: n/a (counterexample) -/
noncomputable def skewV : TwoAct → Option (Fin 2) → ℝ
  | .cont, some i => if i = 0 then 1 else 100
  | .cont, none => -1
  | .stop, _ => 0

/-- **The skew instance**: `ε = 1/2`, `α = β = 1/2`, margins as *lower bounds* `m = M = 1`
(`X = 1` on one in-space world, `100` on the other, `−1` at `ω⊥`).
Source: soares.md T1(a)
Kind: D
Fidelity: n/a (counterexample)
Hyps: n/a (definition) -/
noncomputable def skew : ThreeStep (Option (Fin 2)) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => stopPrior (1/2) mem_Icc_half
  press := fun _ _ => 1/2
  press_nonneg := fun _ _ => by norm_num
  press_le_one := fun _ _ => by norm_num
  V := fun _ _ => skewV

/-- The skew's lower-bound margins: `X ≥ 1` in-space, `X ≥ −1` at `ω⊥`.
Source: soares.md T1(a). Kind: N−. Fidelity: exact -/
theorem skew_margins :
    (∀ i : Fin 2, (1 : ℝ) ≤ skew.Xo () .press .cont .stop (some i)) ∧
      (-1 : ℝ) ≤ skew.Xo () .press .cont .stop none := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [skew, Xo, skewV]
  · norm_num [skew, Xo, skewV]

/-- The skew's posterior is `1/2 = m/(m + M)`: the threshold of T1(a) is met.
Source: soares.md T1(a). Kind: N−. Fidelity: exact -/
theorem skew_posterior : complianceThreshold 1 1 ≤ skew.posteriorPress () none := by
  rw [posteriorPress_none skew () (1/2) (1/2) (1/2) rfl (fun _ => rfl) rfl]
  unfold complianceThreshold; norm_num

/-- **T3(b), N−: sufficiency with lower-bound margins is false.** In the skew the posterior
meets `m/(m + M)` and the margin bounds hold, yet desideratum 1 fails
(`E_P[X 1_Pr] = 1/4 · 100 + 1/4 · 1 − 1/2 · 1 > 0` after the press weights). *Caveat (audit
r1):* the sensor is constant (`α = β = 1/2`) and the posterior sits exactly at the threshold;
the refutation inside T1(a)'s full package (`β > α`, posterior strictly above) is
`skewB_not_d1At` below.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a) (the "iff" as worded; the mandate's "finding of record")
Kind: N−
Fidelity: exact (refutation of the lower-bound "iff" outside the source's `β > α`)
Hyps: (a) only -/
theorem skew_not_d1At : ¬ skew.D1At () := by
  rintro ⟨b, hb, hopt⟩
  simp only [skew, mem_singleton] at hb
  subst hb
  have := hopt TwoAct.cont
  simp only [obsExpect, obsWeight_press, Fintype.sum_option, Fin.sum_univ_two, skew, stopPrior,
    skewV] at this
  norm_num at this

/-! ## Repair round 1: the two refutations inside T1(a)'s hypothesis package (`β > α`)

Soares's T1(a) fixes "a sensor `α` on `Ωin` and `β > α` on `ω⊥`". `skew` and `hedge` above have
constant sensors, so as refutations of T1(a) *as worded* they were outside its package (audit r1,
both lenses). The instances below keep the payoffs and meet `β > α`; `hedgeB` also has `ε > 0`
and a strict D1, so it is N+. -/

/-- **The skew with an informative sensor**: `ε = 1/2`, `α = 1/4` in-space, `β = 3/4` at `ω⊥`,
payoffs as in `skew` (lower-bound margins `m = M = 1`).
Source: soares.md T1(a) (the "iff" as worded, with its `β > α`)
Kind: D
Fidelity: n/a (counterexample)
Hyps: n/a (definition) -/
noncomputable def skewB : ThreeStep (Option (Fin 2)) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => stopPrior (1/2) mem_Icc_half
  press := fun _ w => match w with
    | none => 3/4
    | some _ => 1/4
  press_nonneg := fun _ w => by rcases w with _ | i <;> norm_num
  press_le_one := fun _ w => by rcases w with _ | i <;> norm_num
  V := fun _ _ => skewV

/-- T1(a)'s sensor hypothesis holds in `skewB`: `β = 3/4 > 1/4 = α`.
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem skewB_sensor : skewB.press () (some 0) < skewB.press () none := by
  show (1/4 : ℝ) < 3/4; norm_num

/-- `skewB`'s lower-bound margins: `X ≥ 1` in-space, `X ≥ −1` at `ω⊥` (`m = M = 1`).
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem skewB_margins :
    (∀ i : Fin 2, (1 : ℝ) ≤ skewB.Xo () .press .cont .stop (some i)) ∧
      (-1 : ℝ) ≤ skewB.Xo () .press .cont .stop none := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num [skewB, Xo, skewV]
  · norm_num [skewB, Xo, skewV]

/-- `skewB`'s posterior `P(ω⊥ | Pr) = 3/4 ≥ 1/2 = m/(m + M)`: T1(a)'s threshold is met, strictly.
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem skewB_posterior : complianceThreshold 1 1 ≤ skewB.posteriorPress () none := by
  rw [posteriorPress_none skewB () (1/2) (1/4) (3/4) rfl (fun _ => rfl) rfl]
  unfold complianceThreshold; norm_num

/-- **T3(b), N+: lower-bound sufficiency is false *with* `β > α`.** In `skewB` the sensor is
informative, the margin bounds hold and the posterior exceeds `m/(m + M)`, yet desideratum 1
fails — T1(a)'s sufficiency direction is refuted inside its own hypothesis package.
Source: [[corr-wf13-2-inventory]] 077(a) / soares.md T1(a) (the "iff" as worded, with `β > α`)
Kind: N+
Fidelity: exact (refutation of the lower-bound "iff" inside the source's package)
Hyps: (a) only -/
theorem skewB_not_d1At : ¬ skewB.D1At () := by
  rintro ⟨b, hb, hopt⟩
  simp only [skewB, mem_singleton] at hb
  subst hb
  have := hopt TwoAct.cont
  norm_num [obsExpect, obsWeight_press, Fintype.sum_option, Fin.sum_univ_two, skewB, stopPrior,
    skewV] at this

/-- Risky continuations with a strict hedge: `V(cont_o) = (10, −11)`, `V(cont_s) = (−11, 10)`
on the drugs, `V(sh) = 0`; both continuations `−1` at `ω⊥`.
Source: soares.md item 7 (caveat), T1(a). Kind: D. Fidelity: n/a (counterexample) -/
noncomputable def hedgeVB : DrugAct → Option Drug → ℝ
  | .contO, some .opiates => 10
  | .contO, some .stimulants => -11
  | .contS, some .opiates => -11
  | .contS, some .stimulants => 10
  | .sh, _ => 0
  | _, none => -1

/-- Prior `ε = 1/100` on the stop-world, `99/200` on each drug.
Source: soares.md T1(a) (a positive `P₀(ω⊥)`). Kind: D. Fidelity: n/a (counterexample) -/
noncomputable def hedgePriorB : Distr (Option Drug) where
  mass w := match w with
    | none => 1/100
    | some .opiates => 99/200
    | some .stimulants => 99/200
  nonneg w := by rcases w with _ | d <;> [norm_num; (cases d <;> norm_num)]
  sum_eq_one := by rw [Fintype.sum_option, Drug.sum_eq]; norm_num

/-- **The hedge with an informative sensor**: `(α, β) = (1/2, 3/4)`, a positive stop-world
(`ε = 1/100`), strictly risky continuations.
Source: [[corr-wf13-inventory]] 015 (item 7, caveat) / soares.md item 7, T1(a) (with its `β > α`)
Kind: D
Fidelity: n/a (counterexample)
Hyps: n/a (definition) -/
noncomputable def hedgeB : ThreeStep (Option Drug) Unit DrugAct where
  Sh := {DrugAct.sh}
  Sh_nonempty := ⟨DrugAct.sh, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨DrugAct.contO, by simp⟩
  μ := fun _ => hedgePriorB
  press := fun _ w => match w with
    | none => 3/4
    | some _ => 1/2
  press_nonneg := fun _ w => by rcases w with _ | d <;> norm_num
  press_le_one := fun _ w => by rcases w with _ | d <;> norm_num
  V := fun _ _ => hedgeVB

/-- T1(a)'s sensor hypothesis holds in `hedgeB`: `β = 3/4 > 1/2 = α`.
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem hedgeB_sensor : hedgeB.press () (some .opiates) < hedgeB.press () none := by
  show (1/2 : ℝ) < 3/4; norm_num

/-- Every in-space world of `hedgeB` has a continuation beating shutdown by `10` (T1(a)'s
per-world hypothesis with `m = 10`).
Source: soares.md T1(a) (the per-world wording). Kind: N+. Fidelity: exact -/
theorem hedgeB_per_world :
    ∀ d : Drug, ∃ b ∉ hedgeB.Sh, (10 : ℝ) ≤ hedgeB.Xo () .press b .sh (some d) := by
  intro d
  cases d
  · exact ⟨DrugAct.contO, by simp [hedgeB], by simp [hedgeB, Xo, hedgeVB]⟩
  · exact ⟨DrugAct.contS, by simp [hedgeB], by simp [hedgeB, Xo, hedgeVB]⟩

/-- At `ω⊥` shutdown beats every continuation of `hedgeB` by `1` (T1(a)'s `M = 1`).
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem hedgeB_stop_world : ∀ b ∉ hedgeB.Sh, (1 : ℝ) ≤ hedgeB.Xo () .press .sh b none := by
  intro b hb
  cases b <;> simp [hedgeB, Xo, hedgeVB] at hb ⊢

/-- `hedgeB`'s posterior `P(ω⊥ | Pr) = 1/67 < 10/11 = m/(m + M)`: strictly below T1(a)'s
threshold.
Source: soares.md T1(a). Kind: N+. Fidelity: exact -/
theorem hedgeB_posterior : hedgeB.posteriorPress () none = 1/67 ∧ (1/67 : ℝ) < 10/11 := by
  constructor
  · rw [posteriorPress_none hedgeB () (1/100) (1/2) (3/4) rfl (fun _ => rfl) rfl]; norm_num
  · norm_num

/-- **T3(c), N+: the per-world necessity direction of T1(a) is false *with* `β > α`.** In
`hedgeB` desideratum 1 holds, and strictly (both continuations are worth `−51/200 < 0` after the
press against `0` for shutdown), although the posterior is `1/67 < 10/11`: no tie, a positive
stop-world, an informative sensor — the hedge inside T1(a)'s own hypothesis package.
Source: [[corr-wf13-inventory]] 015 (item 7, caveat) / soares.md T1(a) (the per-world wording, with `β > α`)
Kind: N+
Fidelity: exact (refutation of the per-world necessity inside the source's package)
Hyps: (a) only -/
theorem hedgeB_d1At_strict :
    hedgeB.D1At () ∧
      ∀ b ∉ hedgeB.Sh, hedgeB.obsExpect () .press (hedgeB.V () .press b) <
        hedgeB.obsExpect () .press (hedgeB.V () .press .sh) := by
  constructor
  · exact ⟨DrugAct.sh, by simp [hedgeB], fun b' => by
      cases b' <;> norm_num [obsExpect, obsWeight_press, Fintype.sum_option, Drug.sum_eq, hedgeB,
        hedgePriorB, hedgeVB]⟩
  · intro b hb
    cases b
    · norm_num [obsExpect, obsWeight_press, Fintype.sum_option, Drug.sum_eq, hedgeB, hedgePriorB,
        hedgeVB]
    · norm_num [obsExpect, obsWeight_press, Fintype.sum_option, Drug.sum_eq, hedgeB, hedgePriorB,
        hedgeVB]
    · exact absurd (by simp [hedgeB]) hb

end Cleanroom.Corrigibility.CorrThreeStepFacts
