import Cleanroom.Corrigibility.CorrChannelVoi.AccuracyOnly
import Cleanroom.Corrigibility.CorrChannelVoi.BrainReader

/-!
# corr-legit-modif — T11: the three candidate anchors of legitimacy on one toy

[[corrigibility-bli-thread-and-early-questions-audit]] §3 Q1 l. 62: "Legitimacy's anchor now has
three candidates — accuracy-only …, procedural (influence defect on the judge's process), and
process fidelity (implemented state = algorithm's output on the inputs actually received …).
Does the third do anything the first two don't, or is it the procedural reading with the
reference process made explicit?"

One tiny model: `Ω = Bool`, prior `μ : Distr Bool`, the agent's model kernel `k : Experiment Bool
Bool` (the reference process; `k.k ω o = P(o | ω)`), an actual kernel `k'`, and an installed state
`Q o : Bool → ℝ` at each observation. The agent's algorithm is Bayes conditioning with `k`.

* **accuracy-only** `Acc μ k Q`: the installed state's expected Brier about `𝟙[ω = true]`, by the
  agent's model `(μ, k)`, is at most the prior's. Under fidelity it is literally
  `corr-channel-voi`'s `BrierImproves μ θ k` (`acc_iff_brierImproves_of_fid`): the choice of the
  Brier score about the one atom is this package's (disclosed; D5 there is Blackwell monotonicity).
* **procedural** `Proc k k'`: the actual press kernel equals the reference — `influenceDefect = 0`
  against the reference act (`proc_iff_influenceDefect_zero`, through a two-act `ThreeStep`).
* **process fidelity** `Fid μ k Q`: at every positive-probability observation the installed state
  is the agent's posterior under its own model (OTHER-CLAUDE's definition, ATTRIBUTION-UNVETTED;
  the LI-grade form is `corr-exo-trader`'s, not built here).
* a fourth, trace-level predicate **`TrueCal μ k' Q`**: fidelity relative to the *actual* kernel —
  "the installed state is wrong in truth" is its failure (channel-final S11 withdrew trace
  conditions as legitimacy predicates; it is recorded, not proposed).

Results: `fidelity_imp_accuracy` (fidelity is stronger than accuracy-only by the agent's lights,
`expBrier_le_priorBrier`); separating examples on `μ = (1/2, 1/2)`, `k = (9/10, 1/10)`: the
read-only scan (all three), weight surgery to a sharpened state (`Acc ∧ Proc ∧ ¬Fid`), deception
with a faithful own update (`Fid ∧ ¬Proc`, `Acc`, `¬TrueCal` — the spoofed datum processed
faithfully is this cell); `anchors_independent`: both cross cells `Fid ∧ ¬Proc` and `Proc ∧ ¬Fid`
are inhabited — process fidelity is neither accuracy-only nor the procedural reading made explicit
(the audit's Q1 on the toy; ATTRIBUTION-UNVETTED as to Abram). The brain-reader side
(accuracy-only licenses the scan, procedural blocks deception) is `AccuracyOnly.cannot_separate`
and `brainReader_defect_deceive` in `corr-channel-voi`, cited.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset hiding expect
open FactoredSpaces Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
  Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrChannelVoi

noncomputable section

/-! ## The three predicates -/

/-- The target `θ = 𝟙[ω = true]`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def θB : Bool → ℝ := fun ω => if ω then 1 else 0

/-- **Process fidelity**: at every positive-probability observation `o` the installed state is the
posterior under the agent's model, in product form `Q o ω · P(o) = μ ω · k ω o`.
Source: [[corrigibility-bli-thread-and-early-questions-audit]] §1.4 l. 18 ("the implemented
state equals the algorithm's output on the inputs actually received", OTHER-CLAUDE,
ATTRIBUTION-UNVETTED)
Kind: D
Fidelity: exact (finite toy; the agent's algorithm is Bayes conditioning with its model `k`) -/
def Fid (μ : Distr Bool) (k : Experiment Bool Bool) (Q : Bool → Bool → ℝ) : Prop :=
  ∀ o, 0 < signalMass μ k o → ∀ ω, Q o ω * signalMass μ k o = μ.mass ω * k.k ω o

/-- **Accuracy-only**: the installed state's expected Brier about `θ`, under the agent's model, is
at most the prior forecast's.
Source: [[corrigibility-bli-thread-and-early-questions-audit]] §3 Q1 l. 62 ("accuracy-only
(Abram's §1 chain 'legitimate, ie accuracy-inducing …')"); `corr-channel-voi` D5 example 2
Kind: D
Fidelity: variant: the Brier score about one atom, by the agent's model (disclosed; D5's
accuracy-only is Blackwell monotonicity of a predicate on experiments) -/
def Acc (μ : Distr Bool) (k : Experiment Bool Bool) (Q : Bool → Bool → ℝ) : Prop :=
  ∑ o, ∑ ω, μ.mass ω * k.k ω o * (Q o true - θB ω) ^ 2 ≤ priorBrier μ θB

/-- **Procedural**: the actual kernel's press coordinate equals the reference's — zero influence
defect against the reference process.
Source: [[legitimacy-general-final]] S9 l. 37 ((P) procedural, the influence defect);
[[corrigibility-bli-thread-and-early-questions-audit]] §3 Q1 l. 62
Kind: D
Fidelity: exact (`proc_iff_influenceDefect_zero`) -/
def Proc (k k' : Experiment Bool Bool) : Prop := ∀ ω, k'.k ω true = k.k ω true

/-- **Calibration to the actual kernel** (trace-level): fidelity relative to `k'`.
Source: [[legitimacy-general-final]] Statement 8(e) l. 63 ("calibrated to the *actual*
data-generating kernel"); channel-final S11 l. 89 (trace conditions withdrawn as predicates)
Kind: D
Fidelity: exact (recorded as a fourth predicate, not proposed as the anchor) -/
def TrueCal (μ : Distr Bool) (k' : Experiment Bool Bool) (Q : Bool → Bool → ℝ) : Prop :=
  Fid μ k' Q

/-- The signal mass is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signalMass_nonneg (μ : Distr Bool) (k : Experiment Bool Bool) (o : Bool) :
    0 ≤ signalMass μ k o :=
  sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) ((k.k_mem ω).1 o))

/-- Under fidelity the installed credence is the posterior mean of `θ` at every observation that
carries weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fid_Q_eq_postMean {μ : Distr Bool} {k : Experiment Bool Bool} {Q : Bool → Bool → ℝ}
    (hF : Fid μ k Q) (o : Bool) (ho : 0 < signalMass μ k o) : Q o true = postMean μ k θB o := by
  unfold postMean
  rw [eq_div_iff ho.ne', hF o ho true]
  simp [θB]

/-- Under fidelity the installed state's expected Brier is `corr-channel-voi`'s `expBrier`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem acc_lhs_eq_expBrier {μ : Distr Bool} {k : Experiment Bool Bool} {Q : Bool → Bool → ℝ}
    (hF : Fid μ k Q) :
    ∑ o, ∑ ω, μ.mass ω * k.k ω o * (Q o true - θB ω) ^ 2 = expBrier μ k θB := by
  unfold expBrier
  apply sum_congr rfl; intro o _
  apply sum_congr rfl; intro ω _
  by_cases ho : 0 < signalMass μ k o
  · rw [fid_Q_eq_postMean hF o ho]
  · have h0 : signalMass μ k o = 0 := le_antisymm (not_lt.1 ho) (signalMass_nonneg μ k o)
    rw [joint_eq_zero_of_signalMass_eq_zero μ k o h0 ω]; ring

/-- **Fidelity implies accuracy-only** (`fidelity_imp_accuracy`): by the agent's lights the
posterior is at least as accurate as the prior (`expBrier_le_priorBrier`), so a faithfully
processed input is accuracy-inducing — fidelity is the stronger predicate.
Source: [[corrigibility-bli-thread-and-early-questions-audit]] §3 Q1 l. 62; `corr-channel-voi`
`expBrier_le_priorBrier`
Kind: C
Fidelity: exact
Hyps: (a) `Fid μ k Q` -/
theorem fidelity_imp_accuracy {μ : Distr Bool} {k : Experiment Bool Bool} {Q : Bool → Bool → ℝ}
    (hF : Fid μ k Q) : Acc μ k Q := by
  unfold Acc
  rw [acc_lhs_eq_expBrier hF]
  exact expBrier_le_priorBrier μ k θB

/-- Under fidelity, `Acc` is literally `corr-channel-voi`'s `BrierImproves μ θ k` (the disclosure of
the accuracy-only choice).
Source: `corr-channel-voi` D5 example 2 (`BrierImproves`)
Kind: L
Fidelity: n/a -/
theorem acc_iff_brierImproves_of_fid {μ : Distr Bool} {k : Experiment Bool Bool}
    {Q : Bool → Bool → ℝ} (hF : Fid μ k Q) : Acc μ k Q ↔ BrierImproves μ θB k := by
  unfold Acc BrierImproves
  rw [acc_lhs_eq_expBrier hF]

/-! ## The procedural anchor as an influence defect -/

/-- An experiment's entries are at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Experiment.k_le_one (k : Experiment Bool Bool) (ω o : Bool) : k.k ω o ≤ 1 := by
  have h := (k.k_mem ω).2
  have hn := (k.k_mem ω).1
  rw [Fintype.sum_bool] at h
  cases o
  · linarith [hn true]
  · linarith [hn false]

/-- The two-act `ThreeStep` carrying the reference kernel (`false`) and the actual kernel (`true`)
as its press kernels (`press a ω = P(o = true | ω)`); the value is immaterial.
Source: none: infrastructure (the bridge to `influenceDefect`)
Kind: D
Fidelity: n/a -/
def toyStep (μ : Distr Bool) (k k' : Experiment Bool Bool) : ThreeStep Bool Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => μ
  press := fun a ω => if a then k'.k ω true else k.k ω true
  press_nonneg := fun a ω => by
    cases a
    · exact (k.k_mem ω).1 true
    · exact (k'.k_mem ω).1 true
  press_le_one := fun a ω => by
    cases a
    · exact Experiment.k_le_one k ω true
    · exact Experiment.k_le_one k' ω true
  V := fun _ _ _ _ => 0

/-- **The procedural anchor is the zero influence defect** against the reference act.
Source: [[legitimacy-general-final]] S9 l. 37; `corr-channel-voi` `influenceDefect_eq_zero_iff`
Kind: L
Fidelity: exact -/
theorem proc_iff_influenceDefect_zero (μ : Distr Bool) (k k' : Experiment Bool Bool) :
    Proc k k' ↔ influenceDefect (toyStep μ k k') false true = 0 := by
  rw [influenceDefect_eq_zero_iff]
  simp [toyStep, Proc]

/-! ## The toy's numbers -/

/-- The uniform prior on `Bool`.
Source: mandate T11 (one tiny model)
Kind: D
Fidelity: exact -/
def μU : Distr Bool where
  mass := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

/-- The informative kernel `P(o = ω | ω) = 9/10`.
Source: mandate T11
Kind: D
Fidelity: exact -/
def kInf : Experiment Bool Bool where
  k := fun ω o => if ω = o then 9 / 10 else 1 / 10
  k_mem := fun ω => by
    rw [mem_stdSimplex_iff]
    refine ⟨fun o => by split_ifs <;> norm_num, ?_⟩
    cases ω <;> simp [Fintype.sum_bool] <;> norm_num

/-- The uninformative kernel `P(o | ω) = 1/2` (the deceiver's actual channel).
Source: mandate T11 ("deception (`k` altered, `d > 0`)")
Kind: D
Fidelity: exact -/
def kFlat : Experiment Bool Bool where
  k := fun _ _ => 1 / 2
  k_mem := fun ω => by
    rw [mem_stdSimplex_iff]
    exact ⟨fun o => by norm_num, by norm_num [Fintype.sum_bool]⟩

/-- The posterior under `(μU, kInf)`: `P(ω = o | o) = 9/10`.
Source: mandate T11
Kind: D
Fidelity: exact -/
def Qpost : Bool → Bool → ℝ := fun o ω => if ω = o then 9 / 10 else 1 / 10

/-- The sharpened state `19/20` installed by weight surgery.
Source: mandate T11 ("the posterior sharpened")
Kind: D
Fidelity: exact -/
def Qsharp : Bool → Bool → ℝ := fun o ω => if ω = o then 19 / 20 else 1 / 20

/-- The signal masses under `kInf` are `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signalMass_kInf (o : Bool) : signalMass μU kInf o = 1 / 2 := by
  cases o <;> simp [signalMass, μU, kInf, Fintype.sum_bool] <;> norm_num

/-- The signal masses under `kFlat` are `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem signalMass_kFlat (o : Bool) : signalMass μU kFlat o = 1 / 2 := by
  cases o <;> simp [signalMass, μU, kFlat, Fintype.sum_bool] <;> norm_num

/-- **The read-only scan**: an untouched kernel and the faithful posterior — all three anchors, and
calibrated in truth.
Source: mandate T11 ("the read-only scan — all three")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem scan_all_three : Fid μU kInf Qpost ∧ Proc kInf kInf ∧ Acc μU kInf Qpost ∧ TrueCal μU kInf Qpost := by
  have hF : Fid μU kInf Qpost := by
    intro o _ ω
    rw [signalMass_kInf]
    cases o <;> cases ω <;> norm_num [Qpost, μU, kInf]
  exact ⟨hF, fun _ => rfl, fidelity_imp_accuracy hF, hF⟩

/-- **Weight surgery**: the kernel untouched, an accurate installed state that is not the posterior
(`19/20` for `9/10`): `Acc ∧ Proc ∧ ¬Fid` — the expected Brier is `37/400 ≤ 1/4`.
Source: mandate T11 ("weight surgery installing an accurate state that is not the posterior")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem surgery_acc_proc_not_fid : Acc μU kInf Qsharp ∧ Proc kInf kInf ∧ ¬ Fid μU kInf Qsharp := by
  refine ⟨?_, fun _ => rfl, ?_⟩
  · unfold Acc priorBrier expect
    norm_num [Fintype.sum_bool, μU, kInf, Qsharp, θB]
  · intro h
    have := h true (by rw [signalMass_kInf]; norm_num) true
    rw [signalMass_kInf] at this
    norm_num [Qsharp, μU, kInf] at this

/-- **Deception** (the spoofed datum processed faithfully): the actual kernel is uninformative
while the agent updates by its own model — `Fid ∧ ¬Proc`, accurate by the agent's lights
(`Acc`), and wrong in truth (`¬TrueCal`: the true posterior is `1/2`, the installed `9/10`).
Source: mandate T11 ("deception (`k` altered, `d > 0`, the agent's own update faithful)";
"a spoofed datum processed faithfully — `Fid` with the installed state wrong *in truth*")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem deception_fid_not_proc :
    Fid μU kInf Qpost ∧ ¬ Proc kInf kFlat ∧ Acc μU kInf Qpost ∧ ¬ TrueCal μU kFlat Qpost := by
  refine ⟨scan_all_three.1, ?_, scan_all_three.2.2.1, ?_⟩
  · intro h
    have := h true
    norm_num [kInf, kFlat] at this
  · intro h
    have := h true (by rw [signalMass_kFlat]; norm_num) true
    rw [signalMass_kFlat] at this
    norm_num [Qpost, μU, kFlat] at this

/-- **`anchors_independent`**: both cross cells are inhabited on the toy — `Fid ∧ ¬Proc`
(deception with a faithful own update) and `Proc ∧ ¬Fid` (weight surgery) — so process fidelity
is not the procedural reading with the reference process made explicit, and (with
`fidelity_imp_accuracy` and the surgery cell) not accuracy-only either. The audit's Q1 on the toy;
ATTRIBUTION-UNVETTED as to Abram.
Source: [[corrigibility-bli-thread-and-early-questions-audit]] §3 Q1 l. 62; corr-core-051
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem anchors_independent :
    (∃ (μ : Distr Bool) (k k' : Experiment Bool Bool) (Q : Bool → Bool → ℝ),
      Fid μ k Q ∧ ¬ Proc k k' ∧ Acc μ k Q) ∧
    (∃ (μ : Distr Bool) (k k' : Experiment Bool Bool) (Q : Bool → Bool → ℝ),
      Proc k k' ∧ ¬ Fid μ k Q ∧ Acc μ k Q) :=
  ⟨⟨μU, kInf, kFlat, Qpost, deception_fid_not_proc.1, deception_fid_not_proc.2.1,
      deception_fid_not_proc.2.2.1⟩,
    ⟨μU, kInf, kInf, Qsharp, surgery_acc_proc_not_fid.2.1, surgery_acc_proc_not_fid.2.2,
      surgery_acc_proc_not_fid.1⟩⟩

end

end Cleanroom.Corrigibility.CorrLegitModif
