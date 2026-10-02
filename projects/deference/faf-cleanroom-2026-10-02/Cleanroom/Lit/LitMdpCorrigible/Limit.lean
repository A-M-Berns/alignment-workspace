import Cleanroom.Lit.LitMdpCorrigible.Mdp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `lit-mdp-corrigible` — the horizon limit is the Bellman fixed point

Elementary form of T20: a value function `v` solving the policy Bellman equation (resp. the
optimality equation) is the `n → ∞` limit of the horizon-indexed `V^π_n` (resp. `V*_n`), with the
geometric error bound `|V_n(s) − v(s)| ≤ γⁿ B` for `B ≥ sup |v|`. No contraction-mapping
machinery: a direct induction. `Vlim`/`VoptLim` package the limits as `limUnder` (junk when the
limit does not exist — every use here proves the limit first).

Mandate: [[lit-mdp-corrigible-mandate]] T12(c) ("prove the closed forms … at horizon n with the
limit — choose one and say which"), T20 (stretch, elementary form).
-/

open Finset FactoredSpaces Filter Topology

namespace Cleanroom.Lit.LitMdpCorrigible

namespace FinMDP

variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FinMDP S A)

/-- `v` solves the **policy Bellman equation** for `π`.
Source: [[orseau-armstrong-2016-safely-interruptible-agents]] Eq. (1); Holtman 2020 App. A
Kind: D
Fidelity: exact -/
def IsPolFixed (π : Pol S A) (v : S → ℝ) : Prop := ∀ s, v s = ∑ a, (π s).mass a * M.Qof v s a

/-- `v` solves the **optimality Bellman equation**.
Source: Holtman 2020 App. A (the Bellman equations)
Kind: D
Fidelity: exact -/
def IsOptFixed [Nonempty A] (v : S → ℝ) : Prop :=
  ∀ s, v s = univ.sup' univ_nonempty (fun a => M.Qof v s a)

/-- One backup shrinks a uniform error by `γ`: `|Q[V](s,a) − Q[v](s,a)| ≤ γ · sup |V − v|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_Qof_sub_Qof_le (V v : S → ℝ) (B : ℝ) (hB : ∀ s, |V s - v s| ≤ B) (s : S) (a : A) :
    |M.Qof V s a - M.Qof v s a| ≤ M.γ * B := by
  unfold Qof
  rw [← Finset.sum_sub_distrib]
  have : ∀ s', (M.P s a).mass s' * (M.R s a s' + M.γ * V s') - (M.P s a).mass s' * (M.R s a s' + M.γ * v s')
      = (M.P s a).mass s' * (M.γ * (V s' - v s')) := fun s' => by ring
  simp_rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ s', |(M.P s a).mass s' * (M.γ * (V s' - v s'))|
      = ∑ s', (M.P s a).mass s' * (M.γ * |V s' - v s'|) := by
        apply Finset.sum_congr rfl
        intro s' _
        rw [abs_mul, abs_mul, abs_of_nonneg ((M.P s a).nonneg s'), abs_of_nonneg M.γ_nonneg]
    _ ≤ ∑ s', (M.P s a).mass s' * (M.γ * B) := by
        apply Finset.sum_le_sum
        intro s' _
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB s') M.γ_nonneg) ((M.P s a).nonneg s')
    _ = M.γ * B := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]

/-- **Policy values converge geometrically to the Bellman fixed point**:
`|V^π_n(s) − v(s)| ≤ γⁿ B` when `v` solves the policy equation and `|v| ≤ B`.
Source: [[lit-mdp-corrigible-mandate]] T20 (elementary form)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem abs_Vpol_sub_le (π : Pol S A) (v : S → ℝ) (hv : M.IsPolFixed π v) (B : ℝ)
    (hB : ∀ s, |v s| ≤ B) : ∀ n s, |M.Vpol π n s - v s| ≤ M.γ ^ n * B := by
  intro n
  induction n with
  | zero => intro s; simp [hB s]
  | succ n ih =>
    intro s
    rw [Vpol_succ, hv s, ← Finset.sum_sub_distrib]
    have : ∀ a, (π s).mass a * M.Qof (M.Vpol π n) s a - (π s).mass a * M.Qof v s a
        = (π s).mass a * (M.Qof (M.Vpol π n) s a - M.Qof v s a) := fun a => by ring
    simp_rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |(π s).mass a * (M.Qof (M.Vpol π n) s a - M.Qof v s a)|
        = ∑ a, (π s).mass a * |M.Qof (M.Vpol π n) s a - M.Qof v s a| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul, abs_of_nonneg ((π s).nonneg a)]
      _ ≤ ∑ a, (π s).mass a * (M.γ * (M.γ ^ n * B)) := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (M.abs_Qof_sub_Qof_le _ _ _ ih s a) ((π s).nonneg a)
      _ = M.γ ^ (n + 1) * B := by rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul]; ring

/-- `|sup' f − sup' g| ≤ ε` when `|f − g| ≤ ε` pointwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_sup'_sub_sup'_le {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (f g : ι → ℝ) (ε : ℝ)
    (h : ∀ i ∈ t, |f i - g i| ≤ ε) : |t.sup' ht f - t.sup' ht g| ≤ ε := by
  rw [abs_le]
  constructor
  · have : t.sup' ht g ≤ t.sup' ht f + ε := by
      apply sup'_le
      intro i hi
      have := (abs_le.mp (h i hi)).1
      linarith [le_sup' f hi]
    linarith
  · have : t.sup' ht f ≤ t.sup' ht g + ε := by
      apply sup'_le
      intro i hi
      have := (abs_le.mp (h i hi)).2
      linarith [le_sup' g hi]
    linarith

/-- **Optimal values converge geometrically to the optimality fixed point**:
`|V*_n(s) − v(s)| ≤ γⁿ B` when `v` solves the optimality equation and `|v| ≤ B`.
Source: [[lit-mdp-corrigible-mandate]] T20 (elementary form)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem abs_Vopt_sub_le [Nonempty A] (v : S → ℝ) (hv : M.IsOptFixed v) (B : ℝ)
    (hB : ∀ s, |v s| ≤ B) : ∀ n s, |M.Vopt n s - v s| ≤ M.γ ^ n * B := by
  intro n
  induction n with
  | zero => intro s; simp [hB s]
  | succ n ih =>
    intro s
    rw [Vopt_succ, hv s]
    refine (abs_sup'_sub_sup'_le _ _ _ _ (M.γ * (M.γ ^ n * B)) fun a _ =>
      M.abs_Qof_sub_Qof_le _ _ _ ih s a).trans (le_of_eq ?_)
    ring

/-- The horizon-`n` policy value tends to the Bellman fixed point.
Source: [[lit-mdp-corrigible-mandate]] T20 (elementary form)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem tendsto_Vpol (π : Pol S A) (v : S → ℝ) (hv : M.IsPolFixed π v) (B : ℝ)
    (hB : ∀ s, |v s| ≤ B) (s : S) : Tendsto (fun n => M.Vpol π n s) atTop (𝓝 (v s)) := by
  have hgeo : Tendsto (fun n : ℕ => M.γ ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.γ_nonneg M.γ_lt_one).mul_const B
  have hlo : Tendsto (fun n => v s - M.γ ^ n * B) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.sub hgeo
  have hhi : Tendsto (fun n => v s + M.γ ^ n * B) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.add hgeo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
  · have := abs_le.mp (M.abs_Vpol_sub_le π v hv B hB n s); linarith
  · have := abs_le.mp (M.abs_Vpol_sub_le π v hv B hB n s); linarith

/-- The horizon-`n` optimal value tends to the optimality fixed point.
Source: [[lit-mdp-corrigible-mandate]] T20 (elementary form)
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem tendsto_Vopt [Nonempty A] (v : S → ℝ) (hv : M.IsOptFixed v) (B : ℝ)
    (hB : ∀ s, |v s| ≤ B) (s : S) : Tendsto (fun n => M.Vopt n s) atTop (𝓝 (v s)) := by
  have hgeo : Tendsto (fun n : ℕ => M.γ ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.γ_nonneg M.γ_lt_one).mul_const B
  have hlo : Tendsto (fun n => v s - M.γ ^ n * B) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.sub hgeo
  have hhi : Tendsto (fun n => v s + M.γ ^ n * B) atTop (𝓝 (v s)) := by
    simpa using tendsto_const_nhds.add hgeo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
  · have := abs_le.mp (M.abs_Vopt_sub_le v hv B hB n s); linarith
  · have := abs_le.mp (M.abs_Vopt_sub_le v hv B hB n s); linarith

/-- The **infinite-horizon policy value** as the horizon limit (`limUnder`; a junk value when the
limit does not exist — every use proves it does via `tendsto_Vpol`).
Source: [[orseau-armstrong-2016-safely-interruptible-agents]] Eq. (1)
Kind: D
Fidelity: variant: the limit of the horizon-indexed value -/
noncomputable def Vlim (π : Pol S A) (s : S) : ℝ := limUnder atTop (fun n => M.Vpol π n s)

/-- The **infinite-horizon optimal value** as the horizon limit.
Source: [[orseau-armstrong-2016-safely-interruptible-agents]] §2 (`π^μ`)
Kind: D
Fidelity: variant: the limit of the horizon-indexed value -/
noncomputable def VoptLim [Nonempty A] (s : S) : ℝ := limUnder atTop (fun n => M.Vopt n s)

/-- `Vlim` is the Bellman fixed point when one exists.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Vlim_eq (π : Pol S A) (v : S → ℝ) (hv : M.IsPolFixed π v) (B : ℝ) (hB : ∀ s, |v s| ≤ B)
    (s : S) : M.Vlim π s = v s :=
  (M.tendsto_Vpol π v hv B hB s).limUnder_eq

/-- `VoptLim` is the optimality fixed point when one exists.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem VoptLim_eq [Nonempty A] (v : S → ℝ) (hv : M.IsOptFixed v) (B : ℝ) (hB : ∀ s, |v s| ≤ B)
    (s : S) : M.VoptLim s = v s :=
  (M.tendsto_Vopt v hv B hB s).limUnder_eq

end FinMDP

end Cleanroom.Lit.LitMdpCorrigible
