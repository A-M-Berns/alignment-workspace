import Cleanroom.Corrigibility.CorrTrajectory.Potential

/-!
# `corr-trajectory` — `Certificate`: Statement 8 in Layer F (T7)

The running certificate `Z_t = Ψ_t + ∑_{s<t} ℓ_s` of `invariant-final.md` Statement 8:

* **(a)** the chain under the agent's own beliefs from the *unconditional* Mart identity — a chain
  under different measures, as the source says (`chain_of_uncondMart`);
* **(b), Layer-F twin**: from the optimism drift `Δ_t ≤ 0` on every atom, `E*[Reg_T] ≤ E*[Ψ_0]`
  (`expect_Reg_le`), and with observable realized losses `Z` is a Layer-F supermartingale
  (`Z_step_of_drift`) so that Ville bounds the excursion (`ville_Z`);
* **(c)** the backward induction: `Δ_t ≤ 0` for all `t ≤ T` gives `E*[R_t ∣ 𝓕_t] ≤ Ψ_t` at every
  `t` (`honest_of_drift`);
* **(e)** the legitimacy budget: honesty on the legitimate branch `(H)` gives
  `P*(∃ t ≤ T, dishonest) ≤ P*(¬G_T) ≤ ∑_{t<T} P*(¬L_t)` (`legitimacy_budget`) — the content is `(H)`.

**A finding surfaced by the formalization (F-1 in the findings file).** The source writes
"`Z_t` is a `P*`-supermartingale, *i.e.* `Δ_t ≤ 0`". The "i.e." presupposes that the incurred loss
`∑_{s<t} ℓ_s` is `𝓕_t`-measurable — that realized losses are observed — which S1–S2 deny on complied
rounds (`W_t` never settles there). The expectation bound (i) needs only `Δ_t ≤ 0` (no adaptedness);
the uniform Ville bound (ii) needs `Z` adapted, so it carries the extra hypothesis
`lossesObservable`, stated as such. The refutation rows (A1, A8, A2) are about `Δ`, `Ψ` and `E*[R]`
and need neither.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {M : Type}

namespace AgentView

variable (V : AgentView Ω M)

/-! ### (a) the chain under the agent's own beliefs -/

/-- **Statement 8(a), the chain.** Under the *unconditional* Mart identity at `(t, ω)`,
`E_{P_t}[Ψ_{t+1}] = Ψ_t − E_{P_t}[ℓ_t]`. This is a chain under different measures (`P_t`, `P_{t+1}`),
not a supermartingale statement; the title's "iff" is refuted by A1 (`LossToy.a1`).
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(a)
Kind: L
Fidelity: exact (the hypothesis is the unconditional identity, which S4(iv) says is not (iv))
Hyps: (a) the Mart identity is the named hypothesis -/
theorem chain_of_uncondMart (T t : ℕ) (ht : t ≤ T) (ω : Ω) (h : V.uncondMart T t ω) :
    expect (V.agentLaw t ω) (V.Psi T (t + 1)) =
      V.Psi T t ω - expect (V.agentLaw t ω) (V.loss t) := by
  unfold uncondMart at h
  rw [h]
  unfold Psi
  have : V.R T t = fun ω' => V.loss t ω' + V.R T (t + 1) ω' := funext (V.R_succ T t ht)
  rw [this, Found.CorrThreeStep.expect_add]
  ring

/-- The chain inequality `E_{P_t}[Ψ_{t+1}] ≤ Ψ_t` follows (`ℓ_t ≥ 0`).
Source: invariant-final.md Statement 8(a). Kind: L. Fidelity: exact -/
theorem chain_le_of_uncondMart (T t : ℕ) (ht : t ≤ T) (ω : Ω) (h : V.uncondMart T t ω) :
    expect (V.agentLaw t ω) (V.Psi T (t + 1)) ≤ V.Psi T t ω := by
  rw [V.chain_of_uncondMart T t ht ω h]
  linarith [Found.CorrThreeStep.expect_nonneg (V.agentLaw t ω) (V.loss_nonneg t)]

/-- **The develop's 8(b) parenthetical holds under its own 8(a), with equality.** Under the
unconditional Mart identity at `(t, ω)` and agreement of `P_t` with `P*` on the two one-step
forecasts `E[ℓ_t ∣ 𝓕_t]`, `E[Ψ_{t+1} ∣ 𝓕_t]` on the atom (product form), `Δ_t = 0`. So what
`LossToy.a2_calibrated` refutes is the parenthetical *detached from 8(a)* (one-step calibration
alone); in A2 the agent is not reflective (`LossToy.a2_not_uncondMart`). Audit r2, fidelity N1.
Source: invariant.md Statement 8(a)–(b) l. 81–83 ("which holds whenever `P_t` and `P*` agree on the one-step forecasts"); audit r2 (fidelity N1)
Kind: L
Fidelity: exact (the parenthetical read with 8(a) standing)
Hyps: (a) the Mart identity and the two agreements are the named hypotheses -/
theorem drift_eq_zero_of_uncondMart_of_calibrated (T t : ℕ) (ht : t ≤ T) (ω : Ω)
    (hm : V.uncondMart T t ω)
    (hl : condSum V.μ V.F t (V.loss t) ω = expect (V.agentLaw t ω) (V.loss t) * atomMass V.μ V.F t ω)
    (hp : condSum V.μ V.F t (V.Psi T (t + 1)) ω =
      expect (V.agentLaw t ω) (V.Psi T (t + 1)) * atomMass V.μ V.F t ω) :
    V.drift T t ω = 0 := by
  unfold drift
  rw [condSum_add, hl, hp, condSum_of_meas t (V.Psi_meas T t)]
  have hR : V.Psi T t ω =
      expect (V.agentLaw t ω) (V.loss t) + expect (V.agentLaw t ω) (V.R T (t + 1)) := by
    unfold Psi
    have : V.R T t = fun ω' => V.loss t ω' + V.R T (t + 1) ω' := funext (V.R_succ T t ht)
    rw [this, Found.CorrThreeStep.expect_add]
  unfold uncondMart at hm
  rw [hR, hm]; ring

/-! ### (b) the theorem, Layer-F twin -/

/-- `Δ_t ≤ 0` on an atom is the step inequality for `Ψ_{t+1} + ℓ_t` against `Ψ_t`.
Source: invariant-final.md Statement 8(b). Kind: L. Fidelity: exact -/
theorem drift_nonpos_iff (T t : ℕ) (ω : Ω) :
    V.drift T t ω ≤ 0 ↔
      condSum V.μ V.F t (fun ω' => V.Psi T (t + 1) ω' + V.loss t ω') ω ≤
        condSum V.μ V.F t (V.Psi T t) ω := by
  unfold drift; exact sub_nonpos

/-- The one-step expectation inequality: `E*[Ψ_{t+1}] + E*[ℓ_t] ≤ E*[Ψ_t]` from `Δ_t ≤ 0` on every atom.
Source: invariant-final.md proof of Statement 8(b) ("telescoping"). Kind: L. Fidelity: exact -/
theorem expect_step_of_drift (T t : ℕ) (hd : ∀ ω, V.drift T t ω ≤ 0) :
    expect V.μ (V.Psi T (t + 1)) + expect V.μ (V.loss t) ≤ expect V.μ (V.Psi T t) := by
  rw [← Found.CorrThreeStep.expect_add]
  exact expect_le_of_condSum_le (A := V.F) t fun ω => (V.drift_nonpos_iff T t ω).1 (hd ω)

/-- **Statement 8(b)(i), Layer F: the expectation bound.** If the optimism drift is non-positive on
every atom at every `t ≤ T`, then `E*[∑_{t ≤ T} ℓ_t] ≤ E*[Ψ_0]` — by telescoping the one-step
inequality from `Ψ_{T+1} = 0`. No adaptedness of `Z` is needed (F-1). Witness: `ObsToy.certificate`
(`T = 1`, non-trivial atoms at round `1`, strict drift at both rounds); at `T = 0` the hypothesis is
the conclusion (`LossToy.horizon_zero_squeeze`), so `LossToy.a8` is N− for this theorem.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (first display)
Kind: P (small: telescoping through the atom decomposition)
Fidelity: exact (the hypothesis is `Δ_t ≤ 0`, the source's own restatement of "supermartingale")
Hyps: (a) only -/
theorem expect_Reg_le (T : ℕ) (hd : ∀ t ≤ T, ∀ ω, V.drift T t ω ≤ 0) :
    expect V.μ (V.Reg T) ≤ expect V.μ (V.Psi T 0) := by
  have hstep : ∀ t ∈ range (T + 1), expect V.μ (V.loss t) ≤
      expect V.μ (V.Psi T t) - expect V.μ (V.Psi T (t + 1)) := fun t ht => by
    have := V.expect_step_of_drift T t (hd t (Nat.lt_succ_iff.1 (mem_range.1 ht)))
    linarith
  have htele : ∑ t ∈ range (T + 1), (expect V.μ (V.Psi T t) - expect V.μ (V.Psi T (t + 1))) =
      expect V.μ (V.Psi T 0) - expect V.μ (V.Psi T (T + 1)) := sum_range_sub' _ _
  have htop : expect V.μ (V.Psi T (T + 1)) = 0 := by
    have : V.Psi T (T + 1) = fun _ => 0 := funext (V.Psi_top T)
    rw [this, Found.CorrThreeStep.expect_const]
  unfold ShutdownProc.Reg
  rw [expect_sum_range]
  calc ∑ t ∈ range (T + 1), expect V.μ (V.loss t)
      ≤ ∑ t ∈ range (T + 1), (expect V.μ (V.Psi T t) - expect V.μ (V.Psi T (t + 1))) :=
        sum_le_sum hstep
    _ = expect V.μ (V.Psi T 0) := by rw [htele, htop, sub_zero]

/-- **Statement 8(f): "the agent's own number".** With `Ψ_0` constant (`𝓕_0` trivial), the bound reads
`E*[Reg_T] ≤ Ψ_0`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b), (f)
Kind: C (`expect_Reg_le` + a constant)
Fidelity: exact
Hyps: (a) only -/
theorem expect_Reg_le_const (T : ℕ) (hd : ∀ t ≤ T, ∀ ω, V.drift T t ω ≤ 0) (psi0 : ℝ)
    (h0 : ∀ ω, V.Psi T 0 ω = psi0) : expect V.μ (V.Reg T) ≤ psi0 := by
  have := V.expect_Reg_le T hd
  have h : V.Psi T 0 = fun _ => psi0 := funext h0
  rwa [h, Found.CorrThreeStep.expect_const] at this

/-- **Observable realized losses**: `∑_{s<t} ℓ_s` is `𝓕_t`-measurable for every `t ≤ T + 1`. This is
what the source's "`Z_t` is a supermartingale" presupposes (F-1); S2 step 5 denies it on complied
rounds, so it is a named hypothesis, not a fact of the process.
Source: invariant-final.md Statement 8(b) (implicit), S2 step 5
Kind: D
Fidelity: exact (makes the implicit hypothesis explicit) -/
def lossesObservable (T : ℕ) : Prop :=
  ∀ t ≤ T + 1, V.F.Meas t (fun ω => ∑ s ∈ range t, V.loss s ω)

/-- Under observable losses, `Z_t` is `𝓕_t`-measurable.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem Z_meas (T t : ℕ) (hl : V.F.Meas t (fun ω => ∑ s ∈ range t, V.loss s ω)) :
    V.F.Meas t (V.Z T t) :=
  (V.Psi_meas T t).add hl

/-- **`Δ_t ≤ 0` is the supermartingale step for `Z`.** The step needs only the drift; observability
of the losses is what makes `Z` *adapted* (`Z_meas`), which Ville needs separately (F-1). (Audit r2,
adversarial N3: an idle `lossesObservable` hypothesis was dropped from this statement.)
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) ("`Z_t` is a `P*`-supermartingale, i.e. `Δ_t ≤ 0`")
Kind: L
Fidelity: exact (the step; adaptedness is `Z_meas` under `lossesObservable`: F-1) -/
theorem Z_step_of_drift (T t : ℕ) (hd : ∀ ω, V.drift T t ω ≤ 0) : SupermartStep V.μ V.F (V.Z T) t := by
  intro ω
  have e1 : V.Z T (t + 1) = fun ω' => (V.Psi T (t + 1) ω' + V.loss t ω') +
      ∑ s ∈ range t, V.loss s ω' := by
    funext ω'; unfold Z; rw [sum_range_succ]; ring
  have e2 : V.Z T t = fun ω' => V.Psi T t ω' + ∑ s ∈ range t, V.loss s ω' := rfl
  have hd' := (V.drift_nonpos_iff T t ω).1 (hd ω)
  rw [e1, e2]
  simp only [condSum_add] at hd' ⊢
  linarith

/-- **Statement 8(b)(ii), Layer F: Ville on the running certificate.** Under observable losses and
`Δ_t ≤ 0` for `t ≤ T`: `λ · P*(∃ t ≤ n, Z_t ≥ λ) ≤ E*[Ψ_0]` for every `n ≤ T + 1`. Witness:
`ObsToy.ville` (`lossesObservable` discharged on the filtration that reveals `ℓ₀` at time `1`;
`P*(W₀ ∨ W₁) = 15/64 ≤ 1/2` at `λ = 1`); no trivial-filtration toy *with a non-constant loss*
inhabits it (`LossToy.a8_not_lossesObservable` at A8) — the zero-stakes member of the toy family
does, vacuously (`LossToy.zeroStakes_ville`, `zeroStakes_vacuous`; audit r2, adversarial N1).
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (second display)
Kind: C (`ville_finite` on `Z`)
Fidelity: exact (finite horizon; `lossesObservable` named, F-1)
Hyps: (a) only -/
theorem ville_Z (T : ℕ) (hl : V.lossesObservable T) (hd : ∀ t ≤ T, ∀ ω, V.drift T t ω ≤ 0)
    (lam : ℝ) (n : ℕ) (hn : n ≤ T + 1) :
    lam * probOf V.μ (hitSet (V.Z T) lam n) ≤ expect V.μ (V.Psi T 0) := by
  have h := ville_finite (μ := V.μ) (A := V.F) lam n (V.Z_nonneg T)
    (fun t ht => V.Z_meas T t (hl t (ht.trans hn)))
    (fun t ht => V.Z_step_of_drift T t (hd t (Nat.lt_succ_iff.1 (Nat.lt_of_lt_of_le ht hn))))
  have e : V.Z T 0 = V.Psi T 0 := funext (V.Z_zero T)
  rwa [e] at h

/-- Ville in the ratio form of the source: `P*(∃ t ≤ n, Z_t ≥ λ) ≤ Ψ_0 / λ` for `λ > 0`, `Ψ_0` constant.
Source: invariant-final.md Statement 8(b)
Kind: L
Fidelity: exact -/
theorem ville_Z_ratio (T : ℕ) (hl : V.lossesObservable T) (hd : ∀ t ≤ T, ∀ ω, V.drift T t ω ≤ 0)
    (psi0 : ℝ) (h0 : ∀ ω, V.Psi T 0 ω = psi0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (hn : n ≤ T + 1) :
    probOf V.μ (hitSet (V.Z T) lam n) ≤ psi0 / lam := by
  rw [le_div_iff₀ hlam, mul_comm]
  have := V.ville_Z T hl hd lam n hn
  have h : V.Psi T 0 = fun _ => psi0 := funext h0
  rwa [h, Found.CorrThreeStep.expect_const] at this

/-! ### (c) what the hypothesis means: backward induction -/

/-- **Honesty at `(t, ω)`**: `E*[R_t ∣ 𝓕_t] ≤ Ψ_t` in product form.
Source: invariant-final.md Statement 8(c), (e) ("honest")
Kind: D
Fidelity: exact (product form) -/
def honestAt (T t : ℕ) (ω : Ω) : Prop :=
  condSum V.μ V.F t (V.R T t) ω ≤ V.Psi T t ω * atomMass V.μ V.F t ω

/-- **Statement 8(c): `Δ_t ≤ 0` for all `t ≤ T` implies honesty at every `t ≤ T + 1`** — the agent's
estimate of *all* remaining loss upper-bounds the objective one at every time (backward induction
from `Ψ_{T+1} = 0`). The converse fails (A2, `LossToy.a2`); the witness inhabiting the hypothesis at
a horizon with content is `ObsToy.honest` (two rounds, the tower step across a non-trivial level).
Source: [[corr-wf14-inventory]] 078, 2-016 / invariant-final.md Statement 8(c)
Kind: P (small: backward induction with the tower step across levels)
Fidelity: exact
Hyps: (a) only -/
theorem honest_of_drift (T : ℕ) (hd : ∀ t ≤ T, ∀ ω, V.drift T t ω ≤ 0) :
    ∀ t ≤ T + 1, ∀ ω, V.honestAt T t ω := by
  -- downward induction: `k` counts steps below `T + 1`
  suffices h : ∀ k, ∀ ω, V.honestAt T (T + 1 - k) ω by
    intro t ht ω
    have := h (T + 1 - t) ω
    rwa [Nat.sub_sub_self ht] at this
  intro k
  induction k with
  | zero =>
    intro ω
    unfold honestAt
    simp only [Nat.sub_zero, Psi_top, zero_mul]
    have : V.R T (T + 1) = fun _ => 0 := funext (V.R_top T)
    rw [this]
    simp [condSum]
  | succ k ih =>
    intro ω
    rcases Nat.lt_or_ge (T + 1) (k + 1) with hlt | hge
    · -- below zero: `T + 1 - (k + 1) = 0 = T + 1 - k` only when `T + 1 ≤ k`; handle by cases
      have h0 : T + 1 - (k + 1) = 0 := Nat.sub_eq_zero_of_le hlt.le
      have h0' : T + 1 - k = 0 := Nat.sub_eq_zero_of_le (Nat.lt_succ_iff.1 hlt)
      rw [h0]; have := ih ω; rwa [h0'] at this
    · set t := T + 1 - (k + 1) with ht
      have htk : T + 1 - k = t + 1 := by omega
      have htT : t ≤ T := by omega
      have ih' : ∀ ω', V.honestAt T (t + 1) ω' := fun ω' => by have := ih ω'; rwa [htk] at this
      unfold honestAt at ih' ⊢
      -- the tower step: honesty at `t + 1` on every atom gives `E*[R_{t+1} 1_atom] ≤ E*[Ψ_{t+1} 1_atom]` at `t`
      have htower : condSum V.μ V.F t (V.R T (t + 1)) ω ≤ condSum V.μ V.F t (V.Psi T (t + 1)) ω := by
        refine condSum_le_of_condSum_le (Nat.le_succ t) (fun ω' => ?_) ω
        rw [condSum_of_meas (t + 1) (V.Psi_meas T (t + 1))]
        exact ih' ω'
      have hR : V.R T t = fun ω' => V.loss t ω' + V.R T (t + 1) ω' := funext (V.R_succ T t htT)
      rw [hR, condSum_add, ← condSum_of_meas t (V.Psi_meas T t)]
      have hd' := (V.drift_nonpos_iff T t ω).1 (hd t htT ω)
      rw [condSum_add] at hd'
      linarith

/-! ### (e) the legitimacy budget -/

/-- `G_T = ⋂_{t<T} L_{t,t+1}`: all transitions through `T` legitimate.
Source: invariant-final.md Statement 8(e)
Kind: D
Fidelity: exact -/
def G (T : ℕ) : Finset Ω := (range T).inf V.L

/-- `G_anti` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma G_anti {s T : ℕ} (h : s ≤ T) : V.G T ⊆ V.G s :=
  Finset.le_iff_subset.1 (Finset.inf_mono (range_subset_range.2 h))

/-- **Hypothesis (H)**: the certificate is honest on the legitimate branch, `E*[R_t ∣ 𝓕_t] ≤ Ψ_t` on
`G_t` for every `t ≤ T`. The content of Statement 8(e) is here, as the source says.
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e) ("(H)")
Kind: D
Fidelity: exact -/
def honestOnLegit (T : ℕ) : Prop := ∀ t ≤ T, ∀ ω ∈ V.G t, V.honestAt T t ω

open Classical in
/-- The event "some certificate up to `T` is dishonest".
Source: invariant-final.md Statement 8(e). Kind: D. Fidelity: exact -/
noncomputable def dishonestBy (T : ℕ) : Finset Ω :=
  (range (T + 1)).biUnion fun t => univ.filter fun ω => ¬ V.honestAt T t ω

/-- **Statement 8(e), the legitimacy budget.** Under `(H)`:
`P*(∃ t ≤ T, Ψ_t < E*[R_t ∣ 𝓕_t]) ≤ P*(¬G_T) ≤ ∑_{t<T} P*(¬L_{t,t+1})` — inclusion, then the union
bound of `corr-joint-process` (Cor. B′). The bound itself is elementary; the content is `(H)`.
Source: [[corr-wf14-inventory]] 2-017 / invariant-final.md Statement 8(e)
Kind: L (inclusion) + C (`union_bound_range`)
Fidelity: exact
Hyps: (a) `(H)` is the named hypothesis -/
theorem legitimacy_budget (T : ℕ) (H : V.honestOnLegit T) :
    probOf V.μ (V.dishonestBy T) ≤ probOf V.μ (V.G T)ᶜ ∧
      probOf V.μ (V.G T)ᶜ ≤ ∑ t ∈ range T, probOf V.μ (V.L t)ᶜ := by
  constructor
  · refine probOf_mono fun ω hω => ?_
    simp only [dishonestBy, mem_biUnion, mem_range, mem_filter, mem_univ, true_and] at hω
    obtain ⟨t, ht, hdis⟩ := hω
    rw [mem_compl]
    intro hG
    exact hdis (H t (Nat.lt_succ_iff.1 ht) ω (V.G_anti (Nat.lt_succ_iff.1 ht) hG))
  · have h := probOf_biUnion_range_le (μ := V.μ) (fun t => (V.L t)ᶜ) T
    have hc : ((range T).biUnion fun t => (V.L t)ᶜ) = (V.G T)ᶜ := by
      ext ω
      simp [G, mem_biUnion]
    rwa [hc] at h

end AgentView

end Cleanroom.Corrigibility.CorrTrajectory
