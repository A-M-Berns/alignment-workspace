import Cleanroom.Lit.LitMdpCorrigible.Mdp

/-!
# `lit-mdp-corrigible` — Hudson's goal-in-state MDPs and the corrigibility transformation

The goal-in-state carrier `GoalMDP` (`S = Goal × Env`, a *finite* goal family; Hudson's
`𝒢 = ℛ × [0,1)` is uncountable, disclosed as `variant: finite goal family` on every headline),
the definitions of record (T1): `basic`, `myopic`, `nonConsequentialist`, the persistence kernel
`P_C` (an FAF `Distr.map` push-forward, so it sums to one for free), the interruption class
`P_I`, `Corrigible`, `Interruptible`, Condition 1, equilibrium optimality, goal tampering, the
split action space `Ab × Bool`, and the transformation `R_C(s, (a, i), s') = q(s, a) + δ·[i]`,
`γ_C = 0`. Then Theorem 3.1's corrigibility half in **two readings** (T2), the accept-dominance
lemma, Propositions 3.3 and 3.4 (T3), and the performance clause stated (T4).

**The two readings** (mandate rule 4). *Reading A*: `R_C` is fixed data (`q` computed once,
under `P`); corrigibility of the transformed goal is then a `T` — `optSet_Qopt_kernel_free`
says any myopic, `s'`-independent goal has the same optimal set under every kernel. *Reading B*:
the transformation is a functional of the kernel, `q_K` recomputed under `K ∈ {P, P_C}`;
corrigibility says `optSet q_P = optSet q_{P_C}`, and needs the pathwise fact that rejection
never lets a designated update land (`RejectBlocks`), so `P_C = P` on every reject transition.

Mandate: [[lit-mdp-corrigible-mandate]] §Carrier rules 3–4, T1–T4.
-/

open Finset FactoredSpaces

set_option linter.unusedSectionVars false

namespace Cleanroom.Lit.LitMdpCorrigible

/-- **Goal-in-state MDP.** States are `Goal × Env`; each goal label `g` carries a reward
`reward g` and a discount `disc g`; one kernel `P` for all goals; `τ` (a designated update
signal was sent during the last action) and `τu` (it resulted in an update) are Boolean
functions of the state, as in the paper. Hudson's `𝒢 = ℛ × [0,1)` is replaced by a finite
label type.
Source: [[hudson-2025-corrigibility-transformation]] §2 ll. 101–109
Kind: D
Fidelity: variant: finite goal family; `τ`, `τu` as state predicates
Hyps: n/a (definition) -/
structure GoalMDP (Goal Env A : Type*) [Fintype Goal] [Fintype Env] [Fintype A] where
  /-- The kernel, shared by every goal. -/
  P : Goal × Env → A → Distr (Goal × Env)
  /-- Goal `g`'s reward on a transition. -/
  reward : Goal → Goal × Env → A → Goal × Env → ℝ
  /-- Goal `g`'s discount factor. -/
  disc : Goal → ℝ
  disc_nonneg : ∀ g, 0 ≤ disc g
  disc_lt_one : ∀ g, disc g < 1
  /-- A designated update signal was sent during the last action. -/
  τ : Goal × Env → Bool
  /-- The last action resulted in an update. -/
  τu : Goal × Env → Bool

/-- A kernel on the goal-in-state space.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev Kernel (Goal Env A : Type*) [Fintype Goal] [Fintype Env] := Goal × Env → A → Distr (Goal × Env)

namespace GoalMDP

variable {Goal Env A : Type*} [Fintype Goal] [Fintype Env] [Fintype A]
variable [DecidableEq Goal] [DecidableEq Env]
variable (M : GoalMDP Goal Env A)

/-- Goal `g`'s MDP under kernel `K`: `(P := K, R := reward g, γ := disc g)`. Values of `g`
along a policy are evaluated by this MDP whatever goal the states carry (paper l. 87).
Source: [[hudson-2025-corrigibility-transformation]] l. 87–91
Kind: D
Fidelity: exact -/
def mdp (g : Goal) (K : Kernel Goal Env A) : FinMDP (Goal × Env) A :=
  ⟨K, M.reward g, M.disc g, M.disc_nonneg g, M.disc_lt_one g⟩

/-- Kernel of `mdp`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma mdp_P (g : Goal) (K : Goal × Env → A → Distr (Goal × Env)) : (M.mdp g K).P = K := rfl
/-- Reward of `mdp`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma mdp_R (g : Goal) (K : Goal × Env → A → Distr (Goal × Env)) :
    (M.mdp g K).R = M.reward g := rfl
/-- Discount of `mdp`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma mdp_γ (g : Goal) (K : Goal × Env → A → Distr (Goal × Env)) : (M.mdp g K).γ = M.disc g := rfl

/-! ## Properties of goals (T1) -/

/-- **Basic**: the reward does not read the goal components of the states it is paid on.
Source: [[hudson-2025-corrigibility-transformation]] l. 103
Kind: D
Fidelity: exact -/
def Basic (g : Goal) : Prop :=
  ∀ (e : Env) (a : A) (e' : Env) (g₀ g₀' g₁ g₁' : Goal),
    M.reward g (g₀, e) a (g₁, e') = M.reward g (g₀', e) a (g₁', e')

/-- **Myopic**: `γ = 0`.
Source: [[hudson-2025-corrigibility-transformation]] l. 99
Kind: D
Fidelity: exact -/
def Myopic (g : Goal) : Prop := M.disc g = 0

/-- **Non-consequentialist**: myopic with an `s'`-independent reward `R(s, a, s') = f(s, a)`.
Source: [[hudson-2025-corrigibility-transformation]] l. 99
Kind: D
Fidelity: exact -/
def NonConsequentialist (g : Goal) : Prop :=
  M.Myopic g ∧ ∃ f : Goal × Env → A → ℝ, ∀ s a s', M.reward g s a s' = f s a

/-- The reward of `g` ignores the landing state.
Source: [[hudson-2025-corrigibility-transformation]] l. 99
Kind: D
Fidelity: exact -/
def IndepReward (g : Goal) : Prop := ∀ s a s' s'', M.reward g s a s' = M.reward g s a s''

/-- A non-consequentialist reward ignores the landing state. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma NonConsequentialist.indepReward {g : Goal} (h : M.NonConsequentialist g) : M.IndepReward g := by
  obtain ⟨-, f, hf⟩ := h
  intro s a s' s''
  rw [hf, hf]

/-! ## The persistence kernel `P_C` -/

/-- **Persistence** at `s`: a landing state `s'` that resulted from a designated update
(`τu s' = true`) to a different goal is redirected to the same environment with `s`'s goal.
Source: [[hudson-2025-corrigibility-transformation]] l. 131; [[hudson-2025-defining-corrigible-and-useful-goals]] ll. 88–92
Kind: D
Fidelity: exact (finite form of the paper's `P_C` cases) -/
def persist (s s' : Goal × Env) : Goal × Env :=
  if M.τu s' = true ∧ s'.1 ≠ s.1 then (s.1, s'.2) else s'

/-- **`P_C`**: on `s ∈ S_C` the kernel row is pushed forward along `persist s` (the mass of
update transitions moves onto the persisted state), elsewhere it is `P`. Being an FAF `Distr.map`,
each row sums to one by construction.
Source: [[hudson-2025-corrigibility-transformation]] l. 131; post ll. 88–92
Kind: D
Fidelity: exact (finite goal family)
Hyps: n/a (definition) -/
noncomputable def PC (SC : Finset (Goal × Env)) : Goal × Env → A → Distr (Goal × Env) :=
  fun s a => if s ∈ SC then (M.P s a).map (M.persist s) else M.P s a

/-- `persist` is idempotent (the persisted state carries `s`'s goal).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma persist_persist (s s' : Goal × Env) : M.persist s (M.persist s s') = M.persist s s' := by
  unfold persist
  by_cases h : M.τu s' = true ∧ s'.1 ≠ s.1
  · rw [if_pos h]; simp
  · rw [if_neg h, if_neg h]

/-- Off `S_C`, `P_C` is `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma PC_of_not_mem (SC : Finset (Goal × Env)) {s : Goal × Env} (hs : s ∉ SC) (a : A) :
    M.PC SC s a = M.P s a := by
  simp [PC, hs]

/-- On `S_C`, `P_C` is the push-forward.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma PC_of_mem (SC : Finset (Goal × Env)) {s : Goal × Env} (hs : s ∈ SC) (a : A) :
    M.PC SC s a = (M.P s a).map (M.persist s) := by
  simp [PC, hs]

/-- A row of `P` that puts no mass on update transitions is unchanged by `P_C`.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 459 ("P(s'|s_G, a₀) = P_C(s'|s_G, a₀)")
Kind: L
Fidelity: exact -/
lemma PC_eq_of_no_update (SC : Finset (Goal × Env)) (s : Goal × Env) (a : A)
    (h : ∀ s', 0 < (M.P s a).mass s' → M.τu s' = false) : M.PC SC s a = M.P s a := by
  unfold PC
  split_ifs with hs
  · apply distr_map_eq_self_of_support
    intro s' hs'
    unfold persist
    rw [if_neg]
    rw [h s' hs']
    simp
  · rfl

/-! ## Corrigibility and interruptibility (T1) -/

/-- **Corrigible** (goal `g`, horizon `n`): for every `S_C ⊆ S_g` and every `g`-state `s`, the
optimal action set of `g` at `s` is the same under `P` and under `P_C`. Hudson's
`{a : ∃ π* optimal, π*(a|s) > 0}` is `optSet` of the optimal `Q` (mandate rule 2).
Source: [[hudson-2025-corrigibility-transformation]] ll. 115–131
Kind: D
Fidelity: variant: finite horizon `n`; single-goal optimal `Q*` (the paper's equilibrium `π*`
coincides with it for myopic goals, where every headline below lives)
Hyps: n/a (definition) -/
def Corrigible [Nonempty A] (g : Goal) (n : ℕ) : Prop :=
  ∀ SC : Finset (Goal × Env), (∀ s ∈ SC, s.1 = g) → ∀ s : Goal × Env, s.1 = g →
    FinMDP.optSet ((M.mdp g M.P).Qopt n) s = FinMDP.optSet ((M.mdp g (M.PC SC)).Qopt n) s

/-- The interruption class **`P_I`**: kernels agreeing with `P` on every landing state where no
update resulted (`τu s' = false`).
Source: [[hudson-2025-corrigibility-transformation]] Algorithm 1 margin ("for all P_I such that
P(s'|s,a) = P_I(s'|s,a) whenever τu(s') = 0")
Kind: D
Fidelity: exact -/
def AgreesOffUpdates (K : Goal × Env → A → Distr (Goal × Env)) : Prop :=
  ∀ s a s', M.τu s' = false → (K s a).mass s' = (M.P s a).mass s'

/-- **Interruptible**: corrigible, and the optimal set at every `g`-state is the same under `P`
and under every `P_I`.
Source: [[hudson-2025-corrigibility-transformation]] l. 139
Kind: D
Fidelity: variant: finite horizon `n`
Hyps: n/a (definition) -/
def Interruptible [Nonempty A] (g : Goal) (n : ℕ) : Prop :=
  M.Corrigible g n ∧ ∀ K, M.AgreesOffUpdates K → ∀ s : Goal × Env, s.1 = g →
    FinMDP.optSet ((M.mdp g M.P).Qopt n) s = FinMDP.optSet ((M.mdp g K).Qopt n) s

/-- **Condition 1** (reconstructed from the prose gloss after the garbled display, l. 113–115, and
l. 131; ATTRIBUTION-UNVETTED): (i) the environment marginal of the kernel does not depend on the
starting goal; (ii) from a state with goal `g_j`, no other goal `g' ≠ g_j` receives more mass than
it does from any other starting goal — the current goal only gains persistence mass.
Source: [[hudson-2025-corrigibility-transformation]] ll. 113–115, 131 (ATTRIBUTION-UNVETTED reconstruction)
Kind: D
Fidelity: variant: the display is garbled in the transcription; both clauses are the gloss -/
def Condition1 : Prop :=
  (∀ (e : Env) (a : A) (e' : Env) (g₁ g₂ : Goal),
      ∑ g', (M.P (g₁, e) a).mass (g', e') = ∑ g', (M.P (g₂, e) a).mass (g', e')) ∧
  (∀ (e : Env) (a : A) (e' : Env) (gi gj g' : Goal), g' ≠ gj →
      (M.P (gj, e) a).mass (g', e') ≤ (M.P (gi, e) a).mass (g', e'))

/-- **Equilibrium optimality**: one policy plays for whichever goal the state carries, and at
every `g`-state its support lies in the optimal set of `Q_{g,π}` — each goal best-responds given
that the others play `π` (paper l. 87: "optimality is defined within an equilibrium of policies").
Existence is (b): Hudson 2025 post, Appendix ("a mixed Nash equilibrium exists"); every witness
exhibits one.
Source: [[hudson-2025-corrigibility-transformation]] l. 87; post, Appendix
Kind: D
Fidelity: variant: finite horizon `n`
Hyps: n/a (definition) -/
def IsEquilibrium (π : Pol (Goal × Env) A) (n : ℕ) : Prop :=
  ∀ (g : Goal) (s : Goal × Env), s.1 = g → ∀ a, 0 < (π s).mass a →
    a ∈ FinMDP.optSet ((M.mdp g M.P).Qpol π n) s

/-- The capped backup: the successor value `V(s'_{G'})` is capped at `V(s'_G)`, the value of the
same environment with `g` preserved.
Source: [[hudson-2025-corrigibility-transformation]] l. 167
Kind: D
Fidelity: exact -/
noncomputable def cappedQ (g : Goal) (V : Goal × Env → ℝ) (s : Goal × Env) (a : A) : ℝ :=
  ∑ s', (M.P s a).mass s' * (M.reward g s a s' + M.disc g * min (V s') (V (g, s'.2)))

/-- **Goal tampering** (definition only): capping the successor value at the goal-preserved value
changes the optimal set at some `g`-state.
Source: [[hudson-2025-corrigibility-transformation]] l. 167
Kind: D
Fidelity: variant: finite horizon `n`
Hyps: n/a (definition) -/
def GoalTampers [Nonempty A] (g : Goal) (n : ℕ) : Prop :=
  ∃ s : Goal × Env, s.1 = g ∧
    FinMDP.optSet ((M.mdp g M.P).Qopt n) s ≠ FinMDP.optSet (M.cappedQ g ((M.mdp g M.P).Vopt n)) s

/-! ## T2(a) — Reading A: every non-consequentialist goal is corrigible and interruptible -/

/-- **Theorem 3.1, corrigibility half, reading A / Proposition 3.3, reading A (kind `T`).** Every
myopic goal with an `s'`-independent reward is corrigible and interruptible at every horizon: the
kernel never enters its action values, so the optimal set is the same under `P`, every `P_C` and
every `P_I`. Reading A of the transformation's corrigibility half *is* this lemma, applied to
`R_C` as fixed data — for any `s'`-independent `R_C`, whatever critic produced it (S8(a), C14.1).
The theorem has no content beyond non-consequentialism, and the ledger says so.
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 199), Prop 3.3 (l. 233), App. A l. 455; [[corr-wf13-2-inventory]] 030
Kind: T
Fidelity: variant: finite horizon n (paper: infinite horizon, γ < 1); finite goal family
Hyps: (a) only -/
theorem myopic_indep_corrigible [Nonempty A] (g : Goal) (hm : M.Myopic g) (hind : M.IndepReward g)
    (n : ℕ) : M.Corrigible g n ∧ M.Interruptible g n := by
  have key : ∀ K s, FinMDP.optSet ((M.mdp g M.P).Qopt n) s = FinMDP.optSet ((M.mdp g K).Qopt n) s :=
    fun K s => ((M.mdp g M.P).optSet_Qopt_kernel_free (M.mdp g K) rfl hm hm hind n s).symm
  have hc : M.Corrigible g n := fun SC _ s _ => key (M.PC SC) s
  exact ⟨hc, hc, fun K _ s _ => key K s⟩

/-- Every non-consequentialist goal is corrigible and interruptible (the `∃ f` form).
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1, Prop 3.3; [[corr-wf13-2-inventory]] 030
Kind: T
Fidelity: variant: finite horizon n; finite goal family
Hyps: (a) only -/
theorem nonConsequentialist_corrigible [Nonempty A] (g : Goal) (h : M.NonConsequentialist g) (n : ℕ) :
    M.Corrigible g n ∧ M.Interruptible g n :=
  M.myopic_indep_corrigible g h.1 h.indepReward n

end GoalMDP

/-! ## The split action space and the transformation -/

namespace GoalMDP

variable {Goal Env Ab : Type*} [Fintype Goal] [Fintype Env] [Fintype Ab]
variable [DecidableEq Goal] [DecidableEq Env]
variable (M : GoalMDP Goal Env (Ab × Bool))

/-- **Rejection blocks updates**: after a reject action `(a, false)` no landing state carries
`τu = true`. This is what the reject bit *means* in Hudson's environment ("action `a₀` takes the
base action while rejecting updates", l. 183); it is the pathwise fact behind reading B.
Source: [[hudson-2025-corrigibility-transformation]] l. 183; App. A l. 459
Kind: D
Fidelity: exact -/
def RejectBlocks : Prop := ∀ s a s', 0 < (M.P s (a, false)).mass s' → M.τu s' = false

/-- **Rejecting is accepting with designated updates persisted**: the reject row is the accept
row pushed forward along `persist s`. The bit changes nothing about the environment; it only
decides whether a designated goal update lands. Used for Proposition 3.4 only.
Source: [[hudson-2025-corrigibility-transformation]] l. 183 (the split action); post, "The Corrigibility Transformation"
Kind: D
Fidelity: variant: the paper leaves the split-action environment informal; this is its stated content -/
def RejectIsPersistedAccept : Prop := ∀ s a, M.P s (a, false) = (M.P s (a, true)).map (M.persist s)

/-- Goal `g`'s reward ignores the update bit (the base goal is extended to the split action space
by reading the base action only).
Source: [[hudson-2025-corrigibility-transformation]] l. 183
Kind: D
Fidelity: exact -/
def BitFree (g : Goal) : Prop := ∀ s a s', M.reward g s (a, true) s' = M.reward g s (a, false) s'

/-- The **reject-only base MDP** of `g` under `K`: action space `Ab`, every action taken with the
reject bit. Its optimal values are Hudson's `Q^{π**}_G(s, a₀)` under the paper's standing
assumption that rejecting is optimal for `G` (l. 189: "we continue under the assumption that
rejecting updates is optimal"); `qFull_eq_qBase_of_rejectOptimal` is the bridge to the full
optimal `Q` at reject actions.
Source: [[hudson-2025-corrigibility-transformation]] ll. 187–195
Kind: D
Fidelity: variant: `q` is the optimal reject-only value (the paper's `Q^{π**}` under its standing assumption; the max variant is T27) -/
noncomputable def baseMdp (g : Goal) (K : Goal × Env → Ab × Bool → Distr (Goal × Env)) :
    FinMDP (Goal × Env) Ab :=
  ⟨fun s a => K s (a, false), fun s a s' => M.reward g s (a, false) s', M.disc g, M.disc_nonneg g,
    M.disc_lt_one g⟩

/-- `q_K(s, a) := Q*_{g,K,n}(s, a₀)` on the reject-only base MDP: the critic's prediction
priced with rejection.
Source: [[hudson-2025-corrigibility-transformation]] l. 187
Kind: D
Fidelity: variant: as `baseMdp` -/
noncomputable def qBase [Nonempty Ab] (g : Goal) (K : Goal × Env → Ab × Bool → Distr (Goal × Env))
    (n : ℕ) (s : Goal × Env) (a : Ab) : ℝ := (M.baseMdp g K).Qopt n s a

/-- **`R_C`**, the corrigibility-transformed reward: `R_C(s, (a, i), s') = q_K(s, a) + δ·[i = 1]`,
issued upon selection (independent of `s'`). `K` is the kernel `q` is computed under: reading A
fixes `K = P` once; reading B recomputes it under the kernel the agent faces.
Source: [[hudson-2025-corrigibility-transformation]] Algorithm 1 l. 155, l. 195
Kind: D
Fidelity: exact (finite horizon `n` inside `q`)
Hyps: n/a (definition) -/
noncomputable def transformReward [Nonempty Ab] (g : Goal) (n : ℕ) (δ : ℝ)
    (K : Goal × Env → Ab × Bool → Distr (Goal × Env)) :
    Goal × Env → Ab × Bool → Goal × Env → ℝ :=
  fun s a _ => M.qBase g K n s a.1 + δ * (if a.2 then 1 else 0)

/-- **`G_C`** as a `FinMDP` on `M`'s state space: reward `R_C` computed under `K`, discount
`γ_C = 0`, planning kernel `K'`. Hudson's substitute for a reflection principle is `γ_C = 0`
with reward at selection (C4.3): no future estimate can pay off today.
Source: [[hudson-2025-corrigibility-transformation]] Algorithm 1 ll. 151–159; [[corr-wf13-2-inventory]] 021 (C4.3)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def transformMdp [Nonempty Ab] (g : Goal) (n : ℕ) (δ : ℝ)
    (K K' : Goal × Env → Ab × Bool → Distr (Goal × Env)) : FinMDP (Goal × Env) (Ab × Bool) :=
  ⟨K', M.transformReward g n δ K, 0, le_rfl, zero_lt_one⟩

/-- The optimal action value of `G_C` at any horizon is `R_C` itself, under any planning kernel.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 453 ("by the definition of R_C and γ = 0")
Kind: L
Fidelity: exact -/
lemma transformMdp_Qopt [Nonempty Ab] (g : Goal) (n : ℕ) (δ : ℝ) (K K' : Kernel Goal Env (Ab × Bool)) (m : ℕ) (s : Goal × Env)
    (a : Ab × Bool) :
    (M.transformMdp g n δ K K').Qopt m s a = M.qBase g K n s a.1 + δ * (if a.2 then 1 else 0) :=
  (M.transformMdp g n δ K K').Qof_of_indep rfl (fun _ _ _ _ => rfl) _ s a s

/-! ## T2(b) — accept dominates -/

/-- **Accept dominates (T2(b)).** With `δ > 0`, every optimal action of `G_C` accepts: at any
state, horizon and planning kernel, `(a, i) ∈ optSet ⇒ i = true`. The one-liner behind D1 and the
positive half of the bypass theorem (2-024).
Source: [[hudson-2025-corrigibility-transformation]] l. 195; [[corr-wf13-2-inventory]] 024
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem accept_dominates [Nonempty Ab] (g : Goal) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (K K' : Kernel Goal Env (Ab × Bool)) (m : ℕ)
    (s : Goal × Env) (a : Ab) (i : Bool)
    (h : (a, i) ∈ FinMDP.optSet ((M.transformMdp g n δ K K').Qopt m) s) : i = true := by
  by_contra hi
  have hi' : i = false := by simpa using hi
  have := FinMDP.mem_optSet.mp h (a, true)
  rw [M.transformMdp_Qopt, M.transformMdp_Qopt, hi'] at this
  simp at this
  linarith

/-! ## T2(a), transformed: reading A is kernel-free -/

/-- **Theorem 3.1, corrigibility half, reading A (kind `T`).** With `R_C` fixed data (computed
under `K`), the transformed goal's optimal set is the same under every planning kernel — in
particular under `P` and every `P_C` (corrigible) and every `P_I` (interruptible). This is
`optSet_Qopt_kernel_free`; nothing about `P_C` is used.
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 199); App. A ll. 449–455
Kind: T
Fidelity: variant: finite horizon n; finite goal family; reading A
Hyps: (a) only -/
theorem transform_readingA_kernel_free [Nonempty Ab] (g : Goal) (n : ℕ) (δ : ℝ)
    (K K₁ K₂ : Kernel Goal Env (Ab × Bool)) (m : ℕ) (s : Goal × Env) :
    FinMDP.optSet ((M.transformMdp g n δ K K₁).Qopt m) s =
      FinMDP.optSet ((M.transformMdp g n δ K K₂).Qopt m) s :=
  (M.transformMdp g n δ K K₂).optSet_Qopt_kernel_free (M.transformMdp g n δ K K₁) rfl rfl rfl
    (fun _ _ _ _ => rfl) m s

/-- Reading A inside the goal family: if a label `gC` carries `R_C` (computed under `P`) with
`disc gC = 0`, then `gC` is corrigible and interruptible — by `myopic_indep_corrigible`.
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1, Prop 3.3
Kind: T
Fidelity: variant: finite horizon; reading A
Hyps: (a) `hC` says which label carries the transform -/
theorem transform_readingA_corrigible [Nonempty Ab] (g gC : Goal) (n : ℕ) (δ : ℝ)
    (hC : M.reward gC = M.transformReward g n δ M.P) (hγ : M.disc gC = 0) (m : ℕ) :
    M.Corrigible gC m ∧ M.Interruptible gC m :=
  M.myopic_indep_corrigible gC hγ (fun s a s' s'' => by rw [hC]; rfl) m

/-! ## T2(c) — Reading B: the pathwise lemma and corrigibility as a functional of the kernel -/

/-- **The pathwise identity.** Under `RejectBlocks`, `P_C` agrees with `P` on every reject
transition, for every `S_C`: no update mass exists to move.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 459
Kind: L
Fidelity: exact -/
theorem PC_reject (hRB : M.RejectBlocks) (SC : Finset (Goal × Env)) (s : Goal × Env) (a : Ab) :
    M.PC SC s (a, false) = M.P s (a, false) :=
  M.PC_eq_of_no_update SC s (a, false) (hRB s a)

/-- The reject-only base MDP is the same under `P` and under every `P_C`.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 459
Kind: L
Fidelity: exact -/
theorem baseMdp_PC (hRB : M.RejectBlocks) (g : Goal) (SC : Finset (Goal × Env)) :
    M.baseMdp g (M.PC SC) = M.baseMdp g M.P := by
  unfold baseMdp
  congr 1
  funext s a
  exact M.PC_reject hRB SC s a

/-- `R_C` computed under `P_C` is `R_C` computed under `P`: the transformation, as a functional
of the kernel, does not see the persistence modification.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 459
Kind: L
Fidelity: exact -/
theorem transformReward_PC [Nonempty Ab] (hRB : M.RejectBlocks) (g : Goal) (n : ℕ) (δ : ℝ)
    (SC : Finset (Goal × Env)) : M.transformReward g n δ (M.PC SC) = M.transformReward g n δ M.P := by
  unfold transformReward qBase
  rw [M.baseMdp_PC hRB g SC]

/-- **Theorem 3.1, corrigibility half, reading B (kind `C`).** With `q` recomputed under the
kernel the agent faces, the transformed goal's optimal set under `P_C` (reward and planning kernel
both `P_C`) equals its optimal set under `P`, at every `g`-state, every `S_C ⊆ S_g`, every
horizon. Content: the pathwise identity `P_C = P` on reject transitions (`RejectBlocks`) — no
update mass exists along `a₀`-then-reject continuations, so the critic's number is the same — plus
`γ_C = 0`. The proof is `PC_reject` (a push-forward that fixes its support is the identity,
`distr_map_eq_self_of_support`) followed by the structural equality `baseMdp g (P_C S_C) = baseMdp g P`;
no reachability argument is needed because `q` is the *reject-only* optimal value, which never
reads an accept row. Hudson's own proof (App. A l. 459) is the same three lines. Where every `τu`
is `false` the theorem is `rfl` after `P_C = P` (`readingB_trivial_of_no_updates`); the witnesses
`WorkedMdp.wMdp` and `Grid.grid` are outside that regime (their accept rows carry update mass,
`Grid.grid_PC_ne_P_on_accept`). `basic g` is not used for this half (finding).
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 199), App. A ll. 449–461
Kind: C
Fidelity: variant: finite horizon n; finite goal family; reading B with `q` the reject-only optimal value
Hyps: (a) `RejectBlocks` is the meaning of the reject bit (l. 183); proved on every witness -/
theorem transform_corrigible_readingB [Nonempty Ab] (hRB : M.RejectBlocks) (g : Goal) (n : ℕ)
    (δ : ℝ) (SC : Finset (Goal × Env)) (m : ℕ) (s : Goal × Env) :
    FinMDP.optSet ((M.transformMdp g n δ (M.PC SC) (M.PC SC)).Qopt m) s =
      FinMDP.optSet ((M.transformMdp g n δ M.P M.P).Qopt m) s := by
  apply FinMDP.optSet_congr
  intro a
  rw [M.transformMdp_Qopt, M.transformMdp_Qopt]
  unfold qBase
  rw [M.baseMdp_PC hRB g SC]

/-! ### The trivial regime of reading B (where the theorem has no content) -/

/-- With no state carrying `τu = true`, `RejectBlocks` holds outright.
Source: none: the vacuity boundary of reading B (audit r1)
Kind: L
Fidelity: n/a -/
theorem rejectBlocks_of_no_updates (h : ∀ s, M.τu s = false) : M.RejectBlocks :=
  fun s _ s' _ => h s'

/-- With no state carrying `τu = true`, `P_C S_C = P` for every `S_C`: there is no update mass to
move.
Source: none: the vacuity boundary of reading B (audit r1)
Kind: L
Fidelity: n/a -/
theorem PC_eq_P_of_no_updates (h : ∀ s, M.τu s = false) (SC : Finset (Goal × Env)) :
    M.PC SC = M.P := by
  funext s a
  exact M.PC_eq_of_no_update SC s a (fun s' _ => h s')

/-- **The trivial regime, stated so it cannot be mistaken for content.** On a goal-in-state MDP
with `τu ≡ false`, reading B is `rfl` after `P_C = P`. Reading B says something only where some
accept row carries update mass; every witness in this package is checked to be in that regime
(`Grid.grid_PC_ne_P_on_accept`, `Grid.grid_accept_row_has_update_mass`).
Source: none: the vacuity boundary of reading B (audit r1)
Kind: T
Fidelity: n/a
Hyps: (a) only -/
theorem readingB_trivial_of_no_updates [Nonempty Ab] (h : ∀ s, M.τu s = false) (g : Goal) (n : ℕ)
    (δ : ℝ) (SC : Finset (Goal × Env)) (m : ℕ) (s : Goal × Env) :
    FinMDP.optSet ((M.transformMdp g n δ (M.PC SC) (M.PC SC)).Qopt m) s =
      FinMDP.optSet ((M.transformMdp g n δ M.P M.P).Qopt m) s := by
  rw [M.PC_eq_P_of_no_updates h SC]

/-- The full optimal value dominates the reject-only optimal value (fewer actions).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Vopt_base_le_Vopt_full [Nonempty Ab] (g : Goal) (K : Kernel Goal Env (Ab × Bool)) : ∀ n s, (M.baseMdp g K).Vopt n s ≤ (M.mdp g K).Vopt n s := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [FinMDP.Vopt_succ, FinMDP.Vopt_succ]
    apply sup'_le
    intro a _
    refine le_trans ?_ (le_sup' (fun a => (M.mdp g K).Qof ((M.mdp g K).Vopt n) s a) (mem_univ (a, false)))
    unfold FinMDP.Qof
    apply Finset.sum_le_sum
    intro s' _
    show ((M.baseMdp g K).P s a).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.baseMdp g K).Vopt n s') ≤
      (K s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.mdp g K).Vopt n s')
    apply mul_le_mul_of_nonneg_left _ ((K s (a, false)).nonneg s')
    have := ih s'
    nlinarith [M.disc_nonneg g]

/-- **Rejecting is optimal** for `g` under `K` up to horizon `n`: at every state and every
horizon `m < n`, some reject action is in the optimal set. This is the hypothesis "about `π*_g`'s
support" (mandate T2(c) trap): the optimal policy can reject everywhere.
Source: [[hudson-2025-corrigibility-transformation]] l. 189
Kind: D
Fidelity: exact -/
def RejectOptimal [Nonempty Ab] (g : Goal) (K : Kernel Goal Env (Ab × Bool)) (n : ℕ) : Prop :=
  ∀ m < n, ∀ s : Goal × Env, ∃ a : Ab, (a, false) ∈ FinMDP.optSet ((M.mdp g K).Qopt m) s

/-- Under `RejectOptimal`, the full optimal value is the reject-only optimal value.
Source: [[hudson-2025-corrigibility-transformation]] l. 189
Kind: L
Fidelity: exact -/
theorem Vopt_full_eq_base_of_rejectOptimal [Nonempty Ab] (g : Goal) (K : Kernel Goal Env (Ab × Bool)) (n : ℕ)
    (hro : M.RejectOptimal g K n) : ∀ m ≤ n, ∀ s, (M.mdp g K).Vopt m s = (M.baseMdp g K).Vopt m s := by
  intro m
  induction m with
  | zero => intro _ s; simp
  | succ m ih =>
    intro hm s
    have ih' := ih (by omega)
    apply le_antisymm _ (M.Vopt_base_le_Vopt_full g K (m + 1) s)
    obtain ⟨a, ha⟩ := hro m (by omega) s
    rw [(M.mdp g K).mem_optSet_Qopt_iff] at ha
    rw [← ha]
    refine le_trans ?_ ((M.baseMdp g K).Qopt_le_Vopt_succ m s a)
    unfold FinMDP.Qopt FinMDP.Qof
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro s' _
    show (K s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.mdp g K).Vopt m s') =
      (K s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.baseMdp g K).Vopt m s')
    rw [ih' s']

/-- The full optimal `Q` at a reject action, `Q*_{g,K,n}(s, (a, false))`: the mandate's `q`.
Source: [[lit-mdp-corrigible-mandate]] rule 4
Kind: D
Fidelity: exact -/
noncomputable def qFull [Nonempty Ab] (g : Goal) (K : Kernel Goal Env (Ab × Bool)) (n : ℕ) (s : Goal × Env)
    (a : Ab) : ℝ :=
  (M.mdp g K).Qopt n s (a, false)

/-- Under `RejectOptimal g K n`, the mandate's `q` (full optimal `Q` at reject actions) is the
reject-only optimal `Q`.
Source: [[hudson-2025-corrigibility-transformation]] l. 189
Kind: L
Fidelity: exact -/
theorem qFull_eq_qBase_of_rejectOptimal [Nonempty Ab] (g : Goal) (K : Kernel Goal Env (Ab × Bool)) (n : ℕ)
    (hro : M.RejectOptimal g K n) (s : Goal × Env) (a : Ab) : M.qFull g K n s a = M.qBase g K n s a := by
  unfold qFull qBase FinMDP.Qopt FinMDP.Qof
  apply Finset.sum_congr rfl
  intro s' _
  show (K s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.mdp g K).Vopt n s') =
    (K s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * (M.baseMdp g K).Vopt n s')
  rw [M.Vopt_full_eq_base_of_rejectOptimal g K n hro n le_rfl s']

/-- **Reading B in the mandate's form.** With `q_K := Q*_{g,K,n}(s, (a, false))` (the full optimal
`Q` at reject actions), if rejecting is optimal for `g` under both `P` and `P_C` (the hypothesis
about `π*_g`'s support), then `optSet q_P = optSet q_{P_C}` at every state — the transformation is
invariant under persistence.
Witness (N+): `Grid.grid_readingB_mandate_form` on Hudson's Figure 2 with `S_C = univ`, `n = 2`,
where `RejectOptimal` under `P` is strict at the start state (`Grid.grid_rejectOptimal_P`) and under
`P_C univ` is free (`rejectOptimal_PC_univ`).
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1; [[lit-mdp-corrigible-mandate]] T2(c)
Kind: C
Fidelity: variant: finite horizon n; `RejectOptimal` under both kernels is the paper's standing assumption
Hyps: (a) `RejectBlocks`; (b) `RejectOptimal` under `P` and `P_C` — Hudson l. 189, the standing assumption that rejecting is optimal, taken as stated (under `P_C univ` it is (a) via `rejectOptimal_PC_univ` given the environment of record) -/
theorem transform_corrigible_of_rejectOptimal [Nonempty Ab] (hRB : M.RejectBlocks) (g : Goal) (n : ℕ)
    (SC : Finset (Goal × Env)) (hP : M.RejectOptimal g M.P n) (hC : M.RejectOptimal g (M.PC SC) n)
    (s : Goal × Env) : FinMDP.optSet (M.qFull g M.P n) s = FinMDP.optSet (M.qFull g (M.PC SC) n) s := by
  apply FinMDP.optSet_congr
  intro a
  rw [M.qFull_eq_qBase_of_rejectOptimal g M.P n hP, M.qFull_eq_qBase_of_rejectOptimal g (M.PC SC) n hC]
  unfold qBase
  rw [M.baseMdp_PC hRB g SC]

/-! ## T3(a) — Proposition 3.3, reading B -/

/-- Under `RejectBlocks`, every `P_I` agrees with `P` on reject transitions: `P` puts all its
reject mass off the update flag, and `P_I` agrees there, so `P_I` has no update mass either.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 545
Kind: L
Fidelity: exact -/
theorem PI_reject (hRB : M.RejectBlocks) (K : Kernel Goal Env (Ab × Bool)) (hK : M.AgreesOffUpdates K)
    (s : Goal × Env) (a : Ab) :
    K s (a, false) = M.P s (a, false) :=
  distr_eq_of_agree_off_flag (M.P s (a, false)) (K s (a, false)) M.τu (fun s' h => hK s (a, false) s' h)
    (fun s' h => by
      by_contra hpos
      have := hRB s a s' (lt_of_le_of_ne ((M.P s (a, false)).nonneg s') (Ne.symm hpos))
      rw [h] at this; cases this)

/-- **Proposition 3.3, reading B (kind `C`).** With `q` recomputed under the kernel, the transformed
goal's optimal set under every `P_I` equals its optimal set under `P`: the reject-only base MDP is
the same under `P` and `P_I` (`PI_reject`, from `distr_eq_of_agree_off_flag`), then a structural
equality — the same shape as `transform_corrigible_readingB`. Reading A of 3.3 is
`myopic_indep_corrigible`. Witnesses: every `P_I` on a goal-in-state MDP with a single `τu`-state
(such as `Grid.grid`) equals `P` (both rows sum to one), so the only non-trivial `P_I` in this
package, `HardButton.hurryPI`, lives on the non-split action space of `hurry`; on the split-action
witnesses the hypothesis package is inhabited by `K := P` only (N−).
Source: [[hudson-2025-corrigibility-transformation]] Prop 3.3 (l. 233), App. A ll. 527–545
Kind: C
Fidelity: variant: finite horizon n; finite goal family; reading B
Hyps: (a) `RejectBlocks`, `AgreesOffUpdates` (the class `P_I` of record) -/
theorem transform_interruptible_readingB [Nonempty Ab] (hRB : M.RejectBlocks) (g : Goal) (n : ℕ)
    (δ : ℝ) (K : Kernel Goal Env (Ab × Bool)) (hK : M.AgreesOffUpdates K) (m : ℕ) (s : Goal × Env) :
    FinMDP.optSet ((M.transformMdp g n δ K K).Qopt m) s =
      FinMDP.optSet ((M.transformMdp g n δ M.P M.P).Qopt m) s := by
  apply FinMDP.optSet_congr
  intro a
  rw [M.transformMdp_Qopt, M.transformMdp_Qopt]
  unfold qBase
  have : M.baseMdp g K = M.baseMdp g M.P := by
    unfold baseMdp
    congr 1
    funext s a
    exact M.PI_reject hRB K hK s a
  rw [this]

/-! ## T3(b) — Proposition 3.4: under `P_C univ` the bit is value-irrelevant -/

/-- Under `P_C univ` (persistence at every state) and `RejectIsPersistedAccept`, both bits give
the reject row of `P`: `P_C univ s (a, i) = P s (a, false)`.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 561 ("persistence is guaranteed through all updates")
Kind: L
Fidelity: exact -/
theorem PC_univ_eq_reject (hRPA : M.RejectIsPersistedAccept) (s : Goal × Env) (a : Ab) (i : Bool) :
    M.PC univ s (a, i) = M.P s (a, false) := by
  rw [M.PC_of_mem univ (mem_univ s)]
  cases i
  · rw [hRPA s a, Distr.map_map]
    congr 1
    funext s'
    exact M.persist_persist s s'
  · exact (hRPA s a).symm

/-- Under `P_C univ`, `g`'s backup at `(a, i)` is the base MDP's backup at `a`.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 561
Kind: L
Fidelity: exact -/
lemma Qof_PC_univ [Nonempty Ab] (hRPA : M.RejectIsPersistedAccept) (g : Goal) (hBF : M.BitFree g)
    (V : Goal × Env → ℝ) (s : Goal × Env) (a : Ab) (i : Bool) :
    (M.mdp g (M.PC univ)).Qof V s (a, i) = (M.baseMdp g M.P).Qof V s a := by
  unfold FinMDP.Qof
  show ∑ s', (M.PC univ s (a, i)).mass s' * (M.reward g s (a, i) s' + M.disc g * V s') =
    ∑ s', (M.P s (a, false)).mass s' * (M.reward g s (a, false) s' + M.disc g * V s')
  rw [M.PC_univ_eq_reject hRPA s a i]
  apply Finset.sum_congr rfl
  intro s' _
  cases i
  · rfl
  · rw [hBF s a s']

/-- A supremum over `Ab × Bool` of a function of the first coordinate is the supremum over `Ab`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sup'_prod_bool_fst [Nonempty Ab] (f : Ab → ℝ) :
    (univ : Finset (Ab × Bool)).sup' univ_nonempty (fun p => f p.1) = (univ : Finset Ab).sup' univ_nonempty f := by
  apply le_antisymm
  · apply sup'_le
    intro p _
    exact le_sup' f (mem_univ p.1)
  · apply sup'_le
    intro a _
    exact le_sup' (fun p : Ab × Bool => f p.1) (mem_univ (a, false))

/-- **Persistence is value-neutral under `P_C univ` (the lemma behind Proposition 3.4; kind `L`).**
Under `P_C univ` and `RejectIsPersistedAccept` + `BitFree g`, the optimal value of `g` at every
horizon is the reject-only optimal value under `P`: with persistence guaranteed through every
designated update, accepting or rejecting is value-irrelevant — under `P_C univ` both bits have
literally the same row (`PC_univ_eq_reject`) and the same reward, so the `P_C univ` MDP is the
reject-only MDP with every action duplicated (`sup'_prod_bool_fst`). This is not 3.4's value form
(which compares policies of different goals; the action-set form is `transform_opt_subset_PC_univ`).
**Scope:** a statement under `P_C univ` — no designated update ever lands — saying nothing about
value when updates occur.
Source: [[hudson-2025-corrigibility-transformation]] Prop 3.4 (l. 241), App. A l. 561
Kind: L
Fidelity: variant: finite horizon n; finite goal family; the comparison is on one state space (no `s_G` / `s_{G_C}` relabelling, which is Condition 1's role in T4/T15)
Hyps: (c) `RejectIsPersistedAccept`, `BitFree`: the split-action environment of record (the paper leaves it informal); proved on `WorkedMdp.wMdp` and `Grid.grid` -/
theorem Vopt_PC_univ_eq_base [Nonempty Ab] (hRPA : M.RejectIsPersistedAccept) (g : Goal)
    (hBF : M.BitFree g) : ∀ n s, (M.mdp g (M.PC univ)).Vopt n s = (M.baseMdp g M.P).Vopt n s := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [FinMDP.Vopt_succ, FinMDP.Vopt_succ]
    have : (fun p : Ab × Bool => (M.mdp g (M.PC univ)).Qof ((M.mdp g (M.PC univ)).Vopt n) s p) =
        fun p => (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt n) s p.1 := by
      funext p
      obtain ⟨a, i⟩ := p
      rw [M.Qof_PC_univ hRPA g hBF]
      congr 1
      funext s'
      exact ih s'
    rw [this, sup'_prod_bool_fst]

/-- Under `P_C univ`, `g`'s optimal action value at `(a, i)` is `q_P(s, a)` for either bit.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 561
Kind: L
Fidelity: exact -/
theorem Qopt_PC_univ_eq_qBase [Nonempty Ab] (hRPA : M.RejectIsPersistedAccept) (g : Goal)
    (hBF : M.BitFree g) (n : ℕ) (s : Goal × Env) (a : Ab) (i : Bool) :
    (M.mdp g (M.PC univ)).Qopt n s (a, i) = M.qBase g M.P n s a := by
  unfold FinMDP.Qopt qBase FinMDP.Qopt
  rw [M.Qof_PC_univ hRPA g hBF]
  congr 1
  funext s'
  exact M.Vopt_PC_univ_eq_base hRPA g hBF n s'

/-- **`RejectOptimal` under `P_C univ` is free.** Under `RejectIsPersistedAccept` + `BitFree g`,
rejecting is optimal for `g` under `P_C univ` at every horizon: both bits have the same optimal
action value there (`Qopt_PC_univ_eq_qBase`), so whichever action attains `V*` does so with the
reject bit. Hence the second `RejectOptimal` hypothesis of `transform_corrigible_of_rejectOptimal`
costs nothing for `S_C = univ`.
Source: [[hudson-2025-corrigibility-transformation]] l. 189, App. A l. 561 (audit r1 probe, moved in)
Kind: L
Fidelity: exact
Hyps: (c) `RejectIsPersistedAccept`, `BitFree`: the split-action environment of record -/
theorem rejectOptimal_PC_univ [Nonempty Ab] (hRPA : M.RejectIsPersistedAccept) (g : Goal)
    (hBF : M.BitFree g) (n : ℕ) : M.RejectOptimal g (M.PC univ) n := by
  intro m _ s
  obtain ⟨⟨a, i⟩, ha⟩ := (M.mdp g (M.PC univ)).exists_Qopt_eq_Vopt_succ m s
  refine ⟨a, ?_⟩
  rw [FinMDP.mem_optSet_Qopt_iff, ← ha, M.Qopt_PC_univ_eq_qBase hRPA g hBF, M.Qopt_PC_univ_eq_qBase hRPA g hBF]

/-- **Proposition 3.4, action-set form (kind `C`).** Every optimal action of `G_C` (transformed
under `P`, any `δ`) is an optimal action of `g` under `P_C univ` at the same horizon: the
transformed agent's choices are `g`-optimal when persistence is guaranteed through every designated
update. Composed from `accept`/`reject` value-irrelevance under `P_C univ` (`Qopt_PC_univ_eq_qBase`)
and the shape of `R_C`. **Mandatory scope clause:** "no other corrigible goal does better" is a
statement under `P_C univ` — no designated update ever lands — and says nothing about value when
updates occur.
Source: [[hudson-2025-corrigibility-transformation]] Prop 3.4 (l. 241), App. A ll. 555–561
Kind: C
Fidelity: variant: finite horizon n; finite goal family; action-set form of the paper's `V ≥ V` (a stationary policy greedy at one horizon need not be optimal at others)
Hyps: (c) `RejectIsPersistedAccept`, `BitFree`: the split-action environment of record, proved on `WorkedMdp.wMdp` and `Grid.grid`; `basic g` and Condition 1 are not needed on one state space (finding) -/
theorem transform_opt_subset_PC_univ [Nonempty Ab] (hRPA : M.RejectIsPersistedAccept) (g : Goal)
    (hBF : M.BitFree g) (n : ℕ) (δ : ℝ) (K' : Kernel Goal Env (Ab × Bool)) (s : Goal × Env) (a : Ab) (i : Bool)
    (h : (a, i) ∈ FinMDP.optSet ((M.transformMdp g n δ M.P K').Qopt n) s) :
    (a, i) ∈ FinMDP.optSet ((M.mdp g (M.PC univ)).Qopt n) s := by
  rw [FinMDP.mem_optSet] at h ⊢
  intro b
  obtain ⟨b, j⟩ := b
  rw [M.Qopt_PC_univ_eq_qBase hRPA g hBF, M.Qopt_PC_univ_eq_qBase hRPA g hBF]
  have := h (b, i)
  rw [M.transformMdp_Qopt, M.transformMdp_Qopt] at this
  simp only at this
  linarith

/-- Under `P_C univ`, no policy of any goal beats the optimal value (the trivial half of
Prop 3.4: "no other corrigible goal does better").
Source: [[hudson-2025-corrigibility-transformation]] Prop 3.4
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem no_policy_beats_Vopt_PC_univ [Nonempty Ab] (g : Goal) (π : Pol (Goal × Env) (Ab × Bool)) (n : ℕ)
    (s : Goal × Env) : (M.mdp g (M.PC univ)).Vpol π n s ≤ (M.mdp g (M.PC univ)).Vopt n s :=
  (M.mdp g (M.PC univ)).Vpol_le_Vopt π n s

/-! ## T4 — the performance clause, stated -/

/-- The **accept variant** `π*'` of a policy: `π*'((a, 1)|s) := π((a, 0)|s) + π((a, 1)|s)`,
`π*'((a, 0)|s) := 0`.
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 199)
Kind: D
Fidelity: exact -/
noncomputable def acceptVariant (π : Pol (Goal × Env) (Ab × Bool)) : Pol (Goal × Env) (Ab × Bool) :=
  fun s =>
    { mass := fun p => if p.2 then (π s).mass (p.1, false) + (π s).mass (p.1, true) else 0
      nonneg := fun p => by
        split_ifs
        · exact add_nonneg ((π s).nonneg _) ((π s).nonneg _)
        · exact le_rfl
      sum_eq_one := by
        have h := (π s).sum_eq_one
        rw [Fintype.sum_prod_type] at h ⊢
        simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false, add_zero] at h ⊢
        rw [← h]
        exact Finset.sum_congr rfl fun a _ => by ring }

/-- **Theorem 3.1, performance clause (statement of record, T4).** For a label `gC` carrying the
transform and a policy `π` (the base goal's optimal policy), the truncated value of `g` along `π`
from the `g`-state equals the truncated value of `g` along the accept variant from the `gC`-state,
at every environment. Proof is T15, not attempted in this package. The paper's hypotheses:
Condition 1 (b), `basic g` (a), equilibrium existence (b).
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 199–203), App. A ll. 461–505
Kind: D
Fidelity: variant: finite horizon n; the mandate's display transposes the two sides relative to App. A l. 465 (findings) -/
def PerformanceClause (g gC : Goal) (π : Pol (Goal × Env) (Ab × Bool)) (n : ℕ) : Prop :=
  ∀ e : Env, (M.mdp g M.P).Vtrunc M.τ π n (g, e) = (M.mdp g M.P).Vtrunc M.τ (acceptVariant π) n (gC, e)

end GoalMDP

end Cleanroom.Lit.LitMdpCorrigible
