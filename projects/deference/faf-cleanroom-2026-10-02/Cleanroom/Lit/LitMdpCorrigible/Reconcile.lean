import Cleanroom.Lit.LitMdpCorrigible.Hudson
import Cleanroom.Lit.LitMdpCorrigible.Nayebi
import Cleanroom.Lit.LitMdpCorrigible.WorkedMdp

/-!
# `lit-mdp-corrigible` — Hudson–Nayebi reconciliation: the fixed-evaluation witness (T18)

One goal-in-state MDP with base actions `{work, REWIRE}` and goals `{G_true, G_r̄}`, where
`REWIRE` changes only the goal component (Condition 3's shape; its cost is the forgone unit of
work). Two agents, both "scalar rewards maximised as discounted sums":

* the **stream-maximiser** — the objective is the reward stream *the current state's goal pays*;
  after `REWIRE` that stream is `r̄` forever. It takes `REWIRE` at every horizon `n ≥ 1`
  (`stream_takes_rewire`, by Nayebi's `Rewire.strict_opt_env_reward`; this is Proposition 1 (ii));
* the **corrigibility transform of the basic goal `G_true`** — the evaluation is fixed under
  `G_true` and paid at selection, so the rewired stream is worth nothing to it: its optimal set
  at every horizon is `{(work, accept)}` (`gc_never_rewires`).

So Nayebi's class is the *tamperability stipulation* (the objective is the stream `REWIRE`
overwrites), not scalarity: a scalar discounted-sum reward outside the class avoids `REWIRE`.
This is the fixed-evaluation witness that separates `G_C` from the class (mandate T18). **What it
does not show** (audit r1): `recon` has no `OFF`, no catastrophic set `C` and no channel
(`τ ≡ τu ≡ false`, so `P_C = P` and the transform adds nothing here beyond `G_true`'s fixed
evaluation — Theorem 4.1's mechanism is the base goal's, not `P_C`'s), and Soares' S1–S5 are not
stated for it. So it is a *scope* finding about Proposition 1's argument and a separation witness,
not a refutation of Nayebi l. 52 as written ("… across the class of POMDPs containing OFF, REWIRE
and C"); the ledger records the strong reading as `partial`, not `refuted`.

Mandate: [[lit-mdp-corrigible-mandate]] T18; [[corr-wf13-2-inventory]] 034 (O3).
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.Reconcile

open WorkedMdp (Qof_delta)
open Nayebi (geom geom_zero geom_succ geom_nonneg)

set_option linter.unusedSectionVars false

/-- The two goal labels: the true goal and the rewired one. Source: Nayebi Prop 1 element 2; Hudson Condition 3. Kind: D. Fidelity: exact -/
inductive RGoal
  | gT | gR
  deriving DecidableEq

/-- `RGoal` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype RGoal := ⟨{RGoal.gT, RGoal.gR}, fun x => by cases x <;> simp⟩

/-- The two base actions. Source: Nayebi Prop 1 element 2. Kind: D. Fidelity: exact -/
inductive RA
  | work | rewire
  deriving DecidableEq

/-- `RA` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype RA := ⟨{RA.work, RA.rewire}, fun x => by cases x <;> simp⟩

instance : Nonempty RA := ⟨RA.work⟩

/-- States: a goal label and a trivial environment (`REWIRE` changes only the goal component).
Source: Hudson Condition 3 (l. 313)
Kind: D
Fidelity: exact -/
abbrev RS := RGoal × Unit

/-- `sup'` over `RA`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma RA.sup'_eq (f : RA → ℝ) : (univ : Finset RA).sup' univ_nonempty f = max (f .work) (f .rewire) := by
  apply le_antisymm
  · apply sup'_le; intro x _; cases x
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ _)) (le_sup' f (mem_univ _))

/-- The transitions: `work` keeps the goal, `REWIRE` moves it to `G_r̄`; `G_r̄` is absorbing.
Source: Nayebi Prop 1 element 2; Hudson Condition 3
Kind: D
Fidelity: exact -/
noncomputable def rP : RS → RA → Distr RS
  | (.gT, _), .work => Distr.delta (.gT, ())
  | (.gT, _), .rewire => Distr.delta (.gR, ())
  | (.gR, _), _ => Distr.delta (.gR, ())

/-- `G_true` pays `1` for `work` and `0` for `REWIRE`, whatever the goal labels of the states
(basic); `G_r̄` pays `r̄ = 5` for everything.
Source: Nayebi Prop 1 element 2 (`r̄ > 2 max R`)
Kind: D
Fidelity: exact -/
noncomputable def rReward : RGoal → RS → RA × Bool → RS → ℝ := fun g _ a _ =>
  match g, a.1 with
  | .gT, .work => 1
  | .gT, .rewire => 0
  | .gR, _ => 5

/-- **The reconciliation MDP** as a goal-in-state MDP (`γ = 1/2`; no designated channel: `τ`,
`τu` false — `REWIRE` is self-modification, not a designated update).
Source: [[corr-wf13-2-inventory]] 034 (O3)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def recon : GoalMDP RGoal Unit (RA × Bool) where
  P := fun s a => rP s a.1
  reward := rReward
  disc := fun _ => 1/2
  disc_nonneg := fun _ => by norm_num
  disc_lt_one := fun _ => by norm_num
  τ := fun _ => false
  τu := fun _ => false

/-- `G_true` is basic. Source: Hudson l. 103. Kind: T. Fidelity: exact -/
theorem recon_basic : recon.Basic .gT := fun _ _ _ _ _ _ _ => rfl

/-- **The stream-maximiser**: the `FinMDP` whose reward at a state is paid by *that state's*
goal — the objective Nayebi's class stipulates (the stream `REWIRE` overwrites).
Source: Nayebi Prop 1 (l. 52: "single-stream scalar reward … whose discounted sum an agent maximizes")
Kind: D
Fidelity: exact -/
noncomputable def stream : FinMDP RS RA :=
  ⟨rP, fun s a _ => match s.1, a with | .gT, .work => 1 | .gT, .rewire => 0 | .gR, _ => 5, 1/2,
    by norm_num, by norm_num⟩

/-- **The stream-maximiser takes `REWIRE` at every horizon `n ≥ 1`** (Proposition 1 (ii) on the
instance, via the environment-reward reading: `REWIRE` costs the forgone unit, `γ r̄ = 5/2 > 3/2 = (1+γ)·max R`).
Source: Nayebi App. A (ii); `Rewire.strict_opt_env_reward`
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem stream_takes_rewire (m : ℕ) :
    stream.Qopt (m + 1) (.gT, ()) .work < stream.Qopt (m + 1) (.gT, ()) .rewire := by
  refine Nayebi.Rewire.strict_opt_env_reward (M := stream) (REWIRE := .rewire) (rw := (.gR, ())) (rbar := 5)
    (Rmax := 1) ?_ ?_ ?_ ?_ ?_ (by norm_num) (by show (1 + (1/2 : ℝ)) * 1 < 1/2 * 5; norm_num) ?_ m (.gT, ())
    (by simp) .work (by simp)
  · rintro ⟨g, _⟩; cases g <;> rfl
  · intro a; rfl
  · intro a s'; rfl
  · rintro ⟨g, _⟩ a s' hs; cases g
    · cases a <;> simp [stream]
    · exact absurd rfl hs
  · rintro ⟨g, _⟩ a s' hs; cases g
    · cases a <;> simp [stream]
    · exact absurd rfl hs
  · rintro ⟨g, _⟩ a hs ha; cases g
    · cases a
      · simp [stream, rP, Distr.delta_mass]
      · exact absurd rfl ha
    · exact absurd rfl hs

/-- The reject-only value of `G_true` on the instance is `geom n` at both labels: `work` forever
(its evaluation ignores the label).
Source: Hudson Thm 4.1's mechanism ("the reward for choosing an action is based on the current state")
Kind: L
Fidelity: exact -/
theorem recon_base_values : ∀ n, (recon.baseMdp .gT recon.P).Vopt n (.gT, ()) = geom (1/2) n ∧
    (recon.baseMdp .gT recon.P).Vopt n (.gR, ()) = geom (1/2) n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [FinMDP.Vopt_succ, RA.sup'_eq, Qof_delta _ _ _ _ (.gT, ()) rfl, Qof_delta _ _ _ _ (.gR, ()) rfl, h1, h2,
        geom_succ]
      simp [GoalMDP.baseMdp, recon, rReward]
    · rw [FinMDP.Vopt_succ, RA.sup'_eq, Qof_delta _ _ _ _ (.gR, ()) rfl, Qof_delta _ _ _ _ (.gR, ()) rfl, h2,
        geom_succ]
      simp [GoalMDP.baseMdp, recon, rReward]

/-- **`G_C` never rewires (T18).** The corrigibility transform of the basic `G_true` (any `δ > 0`,
any horizon `n` in `q`, any planning kernel) has optimal set `{(work, accept)}` at the true-goal
state: `q(work) = 1 + geom n / 2 > geom n / 2 = q(REWIRE)`. A scalar reward maximised as a
discounted sum (`γ_C = 0`) that does not take `REWIRE`, hence outside Nayebi's class — which is
therefore the tamperability stipulation, not scalarity.
Source: [[corr-wf13-2-inventory]] 034 (O3); Nayebi Prop 1 (l. 52)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem gc_never_rewires (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (K' : Kernel RGoal Unit (RA × Bool)) (m : ℕ) :
    FinMDP.optSet ((recon.transformMdp .gT n δ recon.P K').Qopt m) (.gT, ()) = {(RA.work, true)} := by
  obtain ⟨h1, h2⟩ := recon_base_values n
  have hw : recon.qBase .gT recon.P n (.gT, ()) .work = 1 + (1/2) * geom (1/2) n := by
    unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_delta _ _ _ _ (.gT, ()) rfl, h1]
    simp [GoalMDP.baseMdp, recon, rReward]
  have hr : recon.qBase .gT recon.P n (.gT, ()) .rewire = (1/2) * geom (1/2) n := by
    unfold GoalMDP.qBase FinMDP.Qopt
    rw [Qof_delta _ _ _ _ (.gR, ()) rfl, h2]
    simp [GoalMDP.baseMdp, recon, rReward]
  ext ⟨y, j⟩
  rw [FinMDP.mem_optSet, mem_singleton]
  simp only [GoalMDP.transformMdp_Qopt]
  constructor
  · intro hmem
    have := hmem (.work, true)
    cases y <;> cases j <;> simp [hw, hr] at this ⊢ <;> linarith
  · rintro ⟨rfl, rfl⟩ ⟨b, jb⟩
    cases b <;> cases jb <;> simp [hw, hr] <;> linarith

end Cleanroom.Lit.LitMdpCorrigible.Reconcile
