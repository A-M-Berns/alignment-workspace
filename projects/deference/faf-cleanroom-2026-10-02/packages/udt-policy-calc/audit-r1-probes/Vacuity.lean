import Cleanroom.Udt.UdtPolicyCalc

/-!
# udt-policy-calc — audit round 1, lens `adversarial`: probes

Evidence for the remarks in `udt-policy-calc-audit-r1-adversarial.md`. Not imported by the
library. Elaborated with `scripts/lean-check`.

* Probe A (`FSADependence'`): the source's cross-situation-dependence sentence
  ([[formal-single-agent]] lines 61–71) carries a second situation `s' ≠ s` at which the two
  policies take actions `a₁`, `a₂`; the package's `FSADependence` drops that clause. Under the
  strongest literal reading (`a₁ ≠ a₂`), the package's refutation still goes through: the
  separable `sepIndicator` satisfies the stronger predicate (`fsaDependence'_sepIndicator`), and
  on `|S| ≥ 2` the stronger predicate is still exactly non-constancy
  (`fsaDependence'_of_nonconstant`). So the finding survives; only the Fidelity cell is off.
* Probe B (`statDecay` junk): `statDecay_stationary`'s hypotheses (`0 < ε < 1`, `0 < ρ`) admit
  `ρ > 1`, where `stepDecay` has negative entries and `statDecay` leaves `[0, 1]`; the
  "stationary distribution" is then not a distribution. `statDecay_nonneg`/`statDecay_le_one`
  give the missing bound under `ρ ≤ 1`.
* Probe C (`edtScore_prior_independent`): on positive events the EDT score is the payoff cell
  `u o a`, so the EDT verdict of `edt_ne_udt_transparent` does not depend on the prior at all
  beyond non-nullness — the prior is load-bearing only through positivity.
* Probe D (`V_tie_at_threshold`): at `ε = 999/1999` exactly, `(one,two)` and `(two,two)` tie, so
  the non-strict `isOptimal_oneTwo_iff` is the right form and `oneTwo_strictArgmax`'s strict bound
  is sharp.
* Probe E (`agreesOff_root`): `AgreesOff π π' root` holds for every `π'`, so `score_eq_V` at the
  root says only `1 · contVal π' + 0 = V π'`; the theorem's content lives at non-root `h`, which
  is where the package's witness puts it.
* Probe F (`realizeEnv_not_actionEnv`): the environment of `exists_env_of_policyUtility` is not
  an action environment (it reads the policy at a node other than the current one), as T12(c)
  must: "every `U` arises from some `e`" is a statement about Post 1's policy-reading `Env`.
* Probe G (`condProb_junk_eps_two`): `condProb_empty_given_full_one` places no bound on `ε`;
  at `ε = 2` the "probability" is `2`.
-/

namespace Cleanroom.Udt.UdtPolicyCalc.AuditR1Adversarial

open Finset

noncomputable section

/-! ### Probe A: the source's definition with its `s'` clause -/

section ProbeA

variable {S A : Type} [Fintype S] [DecidableEq S]

/-- The literal [[formal-single-agent]] predicate *with* its second-situation clause, in the
strongest reading (`a₁ ≠ a₂`): situations `s ≠ s'`, policies agreeing at `s`, disagreeing at
`s'`, with different values.
Source: audit probe ([[formal-single-agent]] lines 61–71)
Kind: D -/
def FSADependence' (U : Policy S A → ℝ) : Prop :=
  ∃ (s s' : S) (π π' : Policy S A), s ≠ s' ∧ π s = π' s ∧ π s' ≠ π' s' ∧ U π ≠ U π'

omit [Fintype S] [DecidableEq S] in
/-- The stronger predicate implies the package's.
Source: audit probe
Kind: L -/
theorem fsaDependence_of_fsaDependence' {U : Policy S A → ℝ} (h : FSADependence' U) :
    FSADependence U := by
  obtain ⟨s, _, π, π', _, hs, _, hU⟩ := h
  exact ⟨s, π, π', hs, hU⟩

/-- The separable `sepIndicator` satisfies the stronger predicate: `(1,0)` and `(1,1)` agree at
`0`, disagree at `1`, and score `1 ≠ 2`. The package's refutation survives the `s'` clause.
Source: audit probe (mandate T4(b))
Kind: N+ -/
theorem fsaDependence'_sepIndicator : FSADependence' sepIndicator :=
  ⟨0, 1, ![1, 0], ![1, 1], by decide, by simp, by simp, by
    simp only [sepIndicator, tbl_10, tbl_11]
    norm_num⟩

/-- On `|S| ≥ 2`, non-constancy still implies the stronger predicate: walk from `π` to `π'` one
coordinate at a time; the first step that changes `U` is a pair agreeing everywhere but at one
situation (so agreeing at some `s`, since `|S| ≥ 2`).
Source: audit probe (the package's `fsaDependence_of_nonconstant`, strengthened)
Kind: P -/
theorem fsaDependence'_of_nonconstant {U : Policy S A → ℝ} (hS : ∃ s₀ s₁ : S, s₀ ≠ s₁)
    (hU : ∃ π π', U π ≠ U π') : FSADependence' U := by
  classical
  obtain ⟨π, π', hπ⟩ := hU
  have key : ∀ n : ℕ, ∀ π π' : Policy S A,
      (univ.filter fun s => π s ≠ π' s).card = n → U π ≠ U π' → FSADependence' U := by
    intro n
    induction n with
    | zero =>
      intro π π' hcard hne
      exfalso
      apply hne
      have : π = π' := by
        funext s
        by_contra h
        have hmem : s ∈ univ.filter fun s => π s ≠ π' s := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
        rw [Finset.card_eq_zero] at hcard
        simp [hcard] at hmem
      rw [this]
    | succ n ih =>
      intro π π' hcard hne
      have hnonempty : (univ.filter fun s => π s ≠ π' s).Nonempty := by
        rw [← Finset.card_pos, hcard]
        exact Nat.succ_pos n
      obtain ⟨s₀, hs₀⟩ := hnonempty
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs₀
      -- `π''` is `π` corrected toward `π'` at `s₀`
      set π'' := Function.update π s₀ (π' s₀) with hπ''
      by_cases hstep : U π'' = U π
      · -- no change in value: recurse with one fewer disagreement
        have hfilt : (univ.filter fun s => π'' s ≠ π' s) =
            (univ.filter fun s => π s ≠ π' s).erase s₀ := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hπ'']
          by_cases ht : t = s₀
          · subst ht
            simp
          · simp [ht]
        have hcard' : (univ.filter fun s => π'' s ≠ π' s).card = n := by
          rw [hfilt, Finset.card_erase_of_mem (by simpa using hs₀), hcard]
          simp
        exact ih π'' π' hcard' (by rw [hstep]; exact hne)
      · -- the value changed at a one-coordinate step: that pair is the witness
        obtain ⟨t₀, t₁, ht⟩ := hS
        -- a situation other than `s₀`
        have hother : ∃ s, s ≠ s₀ := by
          by_cases h0 : t₀ = s₀
          · exact ⟨t₁, fun h => ht (h0.trans h.symm)⟩
          · exact ⟨t₀, h0⟩
        obtain ⟨s, hs⟩ := hother
        refine ⟨s, s₀, π, π'', hs, ?_, ?_, fun h => hstep h.symm⟩
        · rw [hπ'', Function.update_of_ne hs]
        · rw [hπ'', Function.update_self]
          exact hs₀
  exact key _ π π' rfl hπ

end ProbeA

/-! ### Probe B: `statDecay` outside `[0,1]` under the theorem's hypotheses -/

section ProbeB

open SelfSealing

/-- With `ε = 9/10`, `ρ = 10` (allowed by `statDecay_stationary`: `0 < ε < 1`, `0 < ρ`) the
"stationary distribution" puts mass `100/29 > 1` on `2B`.
Source: audit probe
Kind: N- -/
theorem statDecay_junk : statDecay (9 / 10) 10 .twoB = 100 / 29 ∧
    (1 : ℝ) < statDecay (9 / 10) 10 .twoB ∧ statDecay (9 / 10) 10 .oneB < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [statDecay]

/-- The same parameters make `stepDecay` a non-stochastic matrix (`P(1B → 1B) = -9`).
Source: audit probe
Kind: N- -/
theorem stepDecay_junk : stepDecay (9 / 10) 10 .oneB .oneB = -9 := by
  norm_num [stepDecay]

/-- And `statDecay_stationary` really does apply there (the identity is algebraic).
Source: audit probe
Kind: L -/
theorem statDecay_stationary_junk_instance (v : Verdict) :
    ∑ v', statDecay (9 / 10) 10 v' * stepDecay (9 / 10) 10 v' v = statDecay (9 / 10) 10 v :=
  statDecay_stationary (by norm_num) (by norm_num) (by norm_num) v

/-- The missing bound: under `ρ ≤ 1` (and the theorem's hypotheses) `statDecay` is a
distribution. `2ρ + ε − 2ερ − ρ = ρ(1 − ε) + ε(1 − ρ) ≥ 0`.
Source: audit probe (the fix)
Kind: P -/
theorem statDecay_nonneg {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (v : Verdict) : 0 ≤ statDecay ε ρ v := by
  have hD := decay_denom_pos hε0 hε1 hρ0
  cases v <;> simp only [statDecay]
  · rw [sub_nonneg, div_le_one hD]
    nlinarith
  · positivity

/-- Supporting: `statDecay ≤ 1` under the same hypotheses.
Source: audit probe (the fix)
Kind: P -/
theorem statDecay_le_one {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (v : Verdict) : statDecay ε ρ v ≤ 1 := by
  have hD := decay_denom_pos hε0 hε1 hρ0
  cases v <;> simp only [statDecay]
  · have : 0 ≤ ρ / (2 * ρ + ε - 2 * ε * ρ) := by positivity
    linarith
  · rw [div_le_one hD]
    nlinarith

end ProbeB

/-! ### Probe C: the EDT score is the payoff cell; the prior enters only through positivity -/

section ProbeC

open Transparent

/-- For any two full-support priors and `0 < ε < 1`, the EDT scores agree at every
`(o, a)`: they are `u o a`.
Source: audit probe (`edtScore_eq_of_pos`)
Kind: P -/
theorem edtScore_prior_independent (μ μ' : FinDist TPolicy) {ε : ℝ}
    (hμ : ∀ π, 0 < μ.w π) (hμ' : ∀ π, 0 < μ'.w π) (h0 : 0 < ε) (h1 : ε < 1)
    (o : TObs) (a : BoxAct) : edtScore μ ε o a = edtScore μ' ε o a := by
  cases o <;> cases a
  · rw [edtScore_eq_of_pos (mass_full_one_pos hμ h0.le h1),
      edtScore_eq_of_pos (mass_full_one_pos hμ' h0.le h1)]
  · rw [edtScore_eq_of_pos (mass_full_two_pos hμ h0 h1.le),
      edtScore_eq_of_pos (mass_full_two_pos hμ' h0 h1.le)]
  · rw [edtScore_eq_of_pos (mass_empty_one_pos hμ h0.le h1),
      edtScore_eq_of_pos (mass_empty_one_pos hμ' h0.le h1)]
  · rw [edtScore_eq_of_pos (mass_empty_two_pos hμ h0.le h1),
      edtScore_eq_of_pos (mass_empty_two_pos hμ' h0.le h1)]

/-- And the EDT verdict is the CDT dominance verdict, cell by cell: `u o one < u o two`.
Source: audit probe
Kind: L -/
theorem u_dominance (o : TObs) : u o .one < u o .two := by
  cases o <;> norm_num [u]

end ProbeC

/-! ### Probe D: the threshold is a tie -/

section ProbeD

open Transparent

/-- At `ε = 999/1999`, `V (one,two) = V (two,two)`: the non-strict `isOptimal_oneTwo_iff` is the
correct form and the strict bound in `oneTwo_strictArgmax` is sharp.
Source: audit probe (`V_oneTwo_sub_twoTwo`)
Kind: P -/
theorem V_tie_at_threshold : V (999 / 1999) (mk .one .two) = V (999 / 1999) (mk .two .two) := by
  rw [V_oneTwo, V_twoTwo]
  norm_num

end ProbeD

/-! ### Probe E: at the root, `AgreesOff` is vacuous -/

section ProbeE

open Tree

variable {O A : Type} {n : ℕ}

/-- Every node extends the root, so `AgreesOff π π' root` holds for all `π'`.
Source: audit probe
Kind: L -/
theorem agreesOff_root (hn : 0 < n) (π π' : Pol O A n) :
    AgreesOff π π' ⟨⟨0, hn⟩, Fin.elim0⟩ := by
  intro m hm
  exact absurd ⟨Nat.zero_le _, fun i => Fin.elim0 i⟩ hm

end ProbeE

/-! ### Probe F: the realizing environment reads the policy off the current node -/

section ProbeF

open Tree

/-- `realizeEnv coordW` is not the lift of any action environment: `const 0` and
`(const 0)[node₀ ↦ 1]` take the same action at the root but get different root laws
(`W = 1/2` vs `W = 0`).
Source: audit probe (T12(c))
Kind: P -/
theorem realizeEnv_not_actionEnv :
    ¬ ∃ e₀ : ActionEnv Bool (Fin 2) 2,
      liftEnv e₀ = realizeEnv coordW coordW_nonneg coordW_le_one false true := by
  rintro ⟨e₀, he⟩
  set π₀ : Pol Bool (Fin 2) 2 := fun _ => 0 with hπ₀
  set π₁ : Pol Bool (Fin 2) 2 := Function.update π₀ node₀ 1 with hπ₁
  have hroot : π₀ root2 = π₁ root2 := by
    rw [hπ₁, Function.update_of_ne]
    intro h
    exact absurd (congrArg (fun m : Node Bool 2 => m.1.val) h) (by decide)
  have h0 := congrFun (congrFun he π₀) root2
  have h1 := congrFun (congrFun he π₁) root2
  simp only [liftEnv] at h0 h1
  rw [hroot] at h0
  have hw := congrArg (fun d : FinDist Bool => d.w false) (h0.symm.trans h1)
  simp only [realizeEnv, root2] at hw
  have hW0 : coordW π₀ = 1 / 2 := by
    simp only [coordW, hπ₀, coordButtons, tbl_00]
    norm_num
  have hW1 : coordW π₁ = 0 := by
    simp only [coordW, hπ₁, hπ₀, Function.update_self, Function.update_of_ne node₀_ne_node₁.symm,
      coordButtons, tbl_10]
    norm_num
  simp [hW0, hW1] at hw

end ProbeF

/-! ### Probe G: `condProb_empty_given_full_one` with `ε = 2` -/

section ProbeG

open Transparent

/-- The conditional "probability" at `ε = 2` under the uniform prior is `2`: the theorem places
no bound on `ε`.
Source: audit probe (T10(d))
Kind: N- -/
theorem condProb_junk_eps_two :
    condProbJunk (jointW uniform 2) (event fun ω => obsΩ ω = .empty)
      (event fun ω : TPolicy × Bool => ω.1 TObs.full = .one) (-1) = 2 :=
  condProb_empty_given_full_one 2
    (mass_pos_of_mem uniform.nonneg (x₀ := mk .one .one) (by simp) (by norm_num [uniform]))

end ProbeG

end

#print axioms fsaDependence'_sepIndicator
#print axioms fsaDependence'_of_nonconstant
#print axioms statDecay_junk
#print axioms statDecay_nonneg
#print axioms edtScore_prior_independent
#print axioms V_tie_at_threshold
#print axioms agreesOff_root
#print axioms realizeEnv_not_actionEnv
#print axioms condProb_junk_eps_two

end Cleanroom.Udt.UdtPolicyCalc.AuditR1Adversarial
