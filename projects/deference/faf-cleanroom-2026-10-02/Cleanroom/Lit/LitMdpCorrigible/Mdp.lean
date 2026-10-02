import FactoredSpaces.Probability
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# `lit-mdp-corrigible` — the finite MDP carrier

Finite Markov decision processes over FAF's `Distr` (every kernel row is a
`FactoredSpaces.Distr S`), stochastic policies `S → Distr A`, **horizon-indexed** policy values
and optimal values (`V 0 = 0`; `Q n s a = ∑ s', P(s'|s,a)(R(s,a,s') + γ V n s')`;
`V (n+1) s = ∑ a π(a|s) Q n s a`, resp. `max_a`), the optimal action set `optSet` (a `Finset`,
never a chosen argmax), the pathwise lemma "two kernels that agree wherever the policy can
lead give equal values", and the myopic closed forms. FAF and Mathlib have no MDP library
(mandate §FAF objects, grep 2026-09-30), so this layer is built here; nothing in it is a
substitute for an FAF object.

Mandate: [[lit-mdp-corrigible-mandate]] §Carrier rules 1–2.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible

/-! ## `Distr` helpers (FAF API requests) -/

section DistrLemmas

variable {S : Type*} [Fintype S]

/-- A push-forward along a map that fixes every point of the support is the identity:
`P.map f = P` when `f s = s` wherever `0 < P(s)`.
Source: none: infrastructure (FAF API request: a `Distr.map_congr_support` lemma)
Kind: L
Fidelity: n/a -/
lemma distr_map_eq_self_of_support (P : Distr S) (f : S → S)
    (hf : ∀ s, 0 < P.mass s → f s = s) : P.map f = P := by
  ext t
  rw [Distr.map_mass, Distr.prob, Finset.sum_eq_single t]
  · by_cases ht : 0 < P.mass t
    · simp [hf t ht]
    · have h0 : P.mass t = 0 := le_antisymm (not_lt.mp ht) (P.nonneg t)
      simp [h0]
  · intro s _ hst
    by_cases hs : 0 < P.mass s
    · simp [hf s hs, hst]
    · have h0 : P.mass s = 0 := le_antisymm (not_lt.mp hs) (P.nonneg s)
      simp [h0]
  · intro h; exact absurd (mem_univ t) h

/-- Two distributions that agree off a flagged set, where the first puts no mass on the flagged
set, are equal: the second cannot hide mass on the flag either, because both sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma distr_eq_of_agree_off_flag (P Q : Distr S) (flag : S → Bool)
    (hT : ∀ s, flag s = false → Q.mass s = P.mass s)
    (hP : ∀ s, flag s = true → P.mass s = 0) : Q = P := by
  have hsplitQ := Finset.sum_filter_add_sum_filter_not (univ : Finset S) (fun s => flag s = false) Q.mass
  have hsplitP := Finset.sum_filter_add_sum_filter_not (univ : Finset S) (fun s => flag s = false) P.mass
  have hQT : ∑ s ∈ univ.filter (fun s => flag s = false), Q.mass s =
      ∑ s ∈ univ.filter (fun s => flag s = false), P.mass s :=
    Finset.sum_congr rfl fun s hs => hT s (mem_filter.mp hs).2
  have hP0 : ∑ s ∈ univ.filter (fun s => ¬ flag s = false), P.mass s = 0 :=
    Finset.sum_eq_zero fun s hs => hP s (by simpa using (mem_filter.mp hs).2)
  have hQ0 : ∑ s ∈ univ.filter (fun s => ¬ flag s = false), Q.mass s = 0 := by
    have h1 := Q.sum_eq_one
    have h2 := P.sum_eq_one
    linarith
  have hQ0' : ∀ s ∈ univ.filter (fun s => ¬ flag s = false), Q.mass s = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun s _ => Q.nonneg s).mp hQ0
  ext s
  by_cases hs : flag s = false
  · exact hT s hs
  · rw [hQ0' s (mem_filter.mpr ⟨mem_univ s, hs⟩), hP s (by simpa using hs)]

end DistrLemmas

/-! ## Finite MDPs, policies, horizon-indexed values -/

/-- A **finite MDP** `(S, A, P, R, γ)`: kernel rows are FAF `Distr`s, reward `R(s, a, s')` on
transitions, discount `0 ≤ γ < 1`. The start distribution `I₀` of Hudson's tuple is not a
field: every statement here is per start state.
Source: [[hudson-2025-corrigibility-transformation]] §2 l. 95; [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: exact (finite `S`, `A`)
Hyps: n/a (definition) -/
structure FinMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- The transition kernel, one FAF distribution per `(s, a)`. -/
  P : S → A → Distr S
  /-- The reward on a transition `(s, a, s')`. -/
  R : S → A → S → ℝ
  /-- The discount factor. -/
  γ : ℝ
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1

/-- A **stochastic stationary policy**: a distribution over actions at each state (so Hudson's
`π*'(a₁|s) := π*(a₀|s) + π*(a₁|s)` is statable).
Source: [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: exact -/
abbrev Pol (S A : Type*) [Fintype A] := S → Distr A

namespace FinMDP

section OptSet

variable {S A : Type*} [Fintype A]

/-! ## Optimal action sets -/

/-- The **optimal action set** of an action-value `Q` at `s`: every maximiser, as a `Finset`.
Hudson's `{a : ∃ π* optimal, π*(a|s) > 0}` *is* `optSet` of the optimal `Q` (a mixed optimal
policy puts mass exactly on maximisers). No argmax is ever chosen (AUDIT §3).
Source: [[lit-mdp-corrigible-mandate]] rule 2; [[hudson-2025-corrigibility-transformation]] l. 115
Kind: D
Fidelity: exact -/
noncomputable def optSet (Q : S → A → ℝ) (s : S) : Finset A :=
  open Classical in univ.filter (fun a => ∀ b, Q s b ≤ Q s a)

/-- Membership in the optimal set. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_optSet {Q : S → A → ℝ} {s : S} {a : A} : a ∈ optSet Q s ↔ ∀ b, Q s b ≤ Q s a := by
  simp [optSet]

/-- The optimal set is nonempty (finite maximum).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma optSet_nonempty [Nonempty A] (Q : S → A → ℝ) (s : S) : (optSet Q s).Nonempty := by
  obtain ⟨a, -, ha⟩ := exists_max_image univ (Q s) univ_nonempty
  exact ⟨a, mem_optSet.mpr fun b => ha b (mem_univ b)⟩

/-- Equal action values at `s` give equal optimal sets.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma optSet_congr {Q Q' : S → A → ℝ} {s : S} (h : ∀ a, Q s a = Q' s a) :
    optSet Q s = optSet Q' s := by
  ext a; simp only [mem_optSet, h]

/-- Adding a constant (in `a`) to the action values leaves the optimal set unchanged.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma optSet_add_const (Q : S → A → ℝ) (c : S → ℝ) (s : S) :
    optSet (fun s a => Q s a + c s) s = optSet Q s := by
  ext a; simp only [mem_optSet]; constructor <;> intro h b <;> have := h b <;> linarith

end OptSet

end FinMDP

namespace FinMDP

variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FinMDP S A)

/-- The **Bellman backup** of a value function: `Q[V](s, a) = ∑ s', P(s'|s,a)(R(s,a,s') + γ V(s'))`.
Source: [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: exact -/
noncomputable def Qof (V : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * V s')

/-- The **horizon-indexed value of a policy**: `V^π_0 = 0`, `V^π_{n+1}(s) = ∑ a π(a|s) Q[V^π_n](s, a)`
(`n` rewards remain). Every headline is stated at every horizon `n` (Holtman 2020 App. A Def. 17 is
the model); the papers' infinite-horizon values are the `n → ∞` limits, not formalized here.
Source: [[lit-mdp-corrigible-mandate]] rule 1; Holtman 2020 App. A Def. 17
Kind: D
Fidelity: variant: finite horizon `n` (papers: infinite horizon, `γ < 1`) -/
noncomputable def Vpol (π : Pol S A) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => ∑ a, (π s).mass a * M.Qof (Vpol π n) s a

/-- `Q^π_n(s, a) = Q[V^π_n](s, a)`: the action value with `n` further rewards along `π`.
Source: [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: variant: finite horizon `n` -/
noncomputable def Qpol (π : Pol S A) (n : ℕ) : S → A → ℝ := M.Qof (M.Vpol π n)

/-- The **horizon-indexed optimal value**: `V*_0 = 0`, `V*_{n+1}(s) = max_a Q[V*_n](s, a)`.
Source: [[lit-mdp-corrigible-mandate]] rule 1; Holtman 2020 App. A Def. 17
Kind: D
Fidelity: variant: finite horizon `n` -/
noncomputable def Vopt [Nonempty A] : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => univ.sup' univ_nonempty (fun a => M.Qof (Vopt n) s a)

/-- `Q*_n(s, a) = Q[V*_n](s, a)`: the optimal action value with `n` further rewards.
Source: [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: variant: finite horizon `n` -/
noncomputable def Qopt [Nonempty A] (n : ℕ) : S → A → ℝ := M.Qof (M.Vopt n)

/-- `V^π_0 = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Vpol_zero (π : Pol S A) (s : S) : M.Vpol π 0 s = 0 := rfl

/-- `V^π` at a successor horizon. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Vpol_succ (π : Pol S A) (n : ℕ) (s : S) :
    M.Vpol π (n + 1) s = ∑ a, (π s).mass a * M.Qof (M.Vpol π n) s a := rfl

/-- `V*_0 = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma Vopt_zero [Nonempty A] (s : S) : M.Vopt 0 s = 0 := rfl

/-- `V*` at a successor horizon. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Vopt_succ [Nonempty A] (n : ℕ) (s : S) :
    M.Vopt (n + 1) s = univ.sup' univ_nonempty (fun a => M.Qof (M.Vopt n) s a) := rfl

/-- The **truncated value** `V^π_{≤T,n}`: rewards along `π` are collected only until the first
state with `τ = true` (Hudson's `T = min{n : τ(s^{(n+1)}) = 1}`); the transition *into* that
state is still paid, nothing after it. Definition of record for Thm 3.1's performance clause.
Source: [[hudson-2025-corrigibility-transformation]] Thm 3.1 (l. 203); [[corr-wf13-2-inventory]] 022
Kind: D
Fidelity: variant: finite horizon `n`; the stopping time is folded into the recursion -/
noncomputable def Vtrunc (τ : S → Bool) (π : Pol S A) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => ∑ a, (π s).mass a *
      ∑ s', (M.P s a).mass s' * (M.R s a s' + M.γ * (if τ s' then 0 else Vtrunc τ π n s'))

/-- The same MDP with another kernel (reward and discount kept).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def withKernel (K : S → A → Distr S) : FinMDP S A := { M with P := K }

/-- Kernel of `withKernel`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma withKernel_P (K : S → A → Distr S) : (M.withKernel K).P = K := rfl
/-- Reward of `withKernel`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma withKernel_R (K : S → A → Distr S) : (M.withKernel K).R = M.R := rfl
/-- Discount of `withKernel`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma withKernel_γ (K : S → A → Distr S) : (M.withKernel K).γ = M.γ := rfl

/-- `a` is in the optimal set of `Q*_n` iff `Q*_n(s, a)` attains `V*_{n+1}(s)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_optSet_Qopt_iff [Nonempty A] (n : ℕ) (s : S) (a : A) :
    a ∈ optSet (M.Qopt n) s ↔ M.Qopt n s a = M.Vopt (n + 1) s := by
  rw [mem_optSet, Vopt_succ]
  constructor
  · intro h
    exact le_antisymm (le_sup' (fun a => M.Qof (M.Vopt n) s a) (mem_univ a))
      (sup'_le _ _ fun b _ => h b)
  · intro h b
    rw [Qopt] at h ⊢
    rw [h]
    exact le_sup' (fun a => M.Qof (M.Vopt n) s a) (mem_univ b)

/-- `Q*_n(s, a) ≤ V*_{n+1}(s)` for every action.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Qopt_le_Vopt_succ [Nonempty A] (n : ℕ) (s : S) (a : A) : M.Qopt n s a ≤ M.Vopt (n + 1) s :=
  le_sup' (fun a => M.Qof (M.Vopt n) s a) (mem_univ a)

/-- `V*_{n+1}(s)` is attained by some action.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_Qopt_eq_Vopt_succ [Nonempty A] (n : ℕ) (s : S) : ∃ a, M.Qopt n s a = M.Vopt (n + 1) s := by
  obtain ⟨a, -, ha⟩ := exists_mem_eq_sup' (univ_nonempty (α := A)) (fun a => M.Qof (M.Vopt n) s a)
  exact ⟨a, by rw [Vopt_succ, ha]; rfl⟩

/-! ## Monotonicity and the optimality of `V*` -/

/-- The backup is monotone in the value function.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Qof_mono {V W : S → ℝ} (h : ∀ s, V s ≤ W s) (s : S) (a : A) : M.Qof V s a ≤ M.Qof W s a := by
  unfold Qof
  apply Finset.sum_le_sum
  intro s' _
  apply mul_le_mul_of_nonneg_left _ ((M.P s a).nonneg s')
  have := h s'
  nlinarith [M.γ_nonneg]

/-- A policy's value never exceeds the optimal value at the same horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Vpol_le_Vopt [Nonempty A] (π : Pol S A) : ∀ n s, M.Vpol π n s ≤ M.Vopt n s := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [Vpol_succ, Vopt_succ]
    calc ∑ a, (π s).mass a * M.Qof (M.Vpol π n) s a
        ≤ ∑ a, (π s).mass a * univ.sup' univ_nonempty (fun a => M.Qof (M.Vopt n) s a) := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ ((π s).nonneg a)
          exact (M.Qof_mono ih s a).trans (le_sup' (fun a => M.Qof (M.Vopt n) s a) (mem_univ a))
      _ = univ.sup' univ_nonempty (fun a => M.Qof (M.Vopt n) s a) := by
          rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul]

/-! ## The pathwise lemma: kernels agreeing where the policy leads -/

/-- **Pathwise agreement.** Two MDPs with the same reward and discount whose kernels agree at
every `(s, a)` with `s ∈ W` and `a` in the policy's support, where `W` is closed under such
transitions, give the same policy value on `W` at every horizon. (The value at `s` only reads the
kernel along `π`-reachable transitions.)
Source: [[lit-mdp-corrigible-mandate]] T2(c) ("a lemma about kernels agreeing on a reachable set")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem Vpol_eq_of_agree (M' : FinMDP S A) (hR : M'.R = M.R) (hγ : M'.γ = M.γ) (π : Pol S A)
    (W : Set S) (hK : ∀ s ∈ W, ∀ a, 0 < (π s).mass a → M'.P s a = M.P s a)
    (hW : ∀ s ∈ W, ∀ a, 0 < (π s).mass a → ∀ s', 0 < (M.P s a).mass s' → s' ∈ W) :
    ∀ n, ∀ s ∈ W, M'.Vpol π n s = M.Vpol π n s := by
  intro n
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    rw [Vpol_succ, Vpol_succ]
    apply Finset.sum_congr rfl
    intro a _
    rcases ((π s).nonneg a).lt_or_eq with hpos | hzero
    · congr 1
      unfold Qof
      rw [hK s hs a hpos, hR, hγ]
      apply Finset.sum_congr rfl
      intro s' _
      rcases ((M.P s a).nonneg s').lt_or_eq with hpos' | hzero'
      · rw [ih s' (hW s hs a hpos s' hpos')]
      · rw [← hzero']; ring
    · rw [← hzero]; ring

/-- The action value along `π` agrees between two such MDPs at any `(s, a)` where the kernels
agree and every successor lies in `W`.
Source: [[lit-mdp-corrigible-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem Qpol_eq_of_agree (M' : FinMDP S A) (hR : M'.R = M.R) (hγ : M'.γ = M.γ) (π : Pol S A)
    (W : Set S) (hK : ∀ s ∈ W, ∀ a, 0 < (π s).mass a → M'.P s a = M.P s a)
    (hW : ∀ s ∈ W, ∀ a, 0 < (π s).mass a → ∀ s', 0 < (M.P s a).mass s' → s' ∈ W)
    (n : ℕ) (s : S) (a : A) (hsa : M'.P s a = M.P s a)
    (hsucc : ∀ s', 0 < (M.P s a).mass s' → s' ∈ W) :
    M'.Qpol π n s a = M.Qpol π n s a := by
  unfold Qpol Qof
  rw [hsa, hR, hγ]
  apply Finset.sum_congr rfl
  intro s' _
  rcases ((M.P s a).nonneg s').lt_or_eq with hpos' | hzero'
  · rw [M.Vpol_eq_of_agree M' hR hγ π W hK hW n s' (hsucc s' hpos')]
  · rw [← hzero']; ring

/-- Pathwise agreement with `W = univ`: kernels agreeing on the policy's support everywhere give
equal values everywhere.
Source: [[lit-mdp-corrigible-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem Vpol_eq_of_agree_univ (M' : FinMDP S A) (hR : M'.R = M.R) (hγ : M'.γ = M.γ) (π : Pol S A)
    (hK : ∀ s a, 0 < (π s).mass a → M'.P s a = M.P s a) (n : ℕ) (s : S) :
    M'.Vpol π n s = M.Vpol π n s :=
  M.Vpol_eq_of_agree M' hR hγ π Set.univ (fun s _ a ha => hK s a ha) (fun _ _ _ _ _ _ => Set.mem_univ _)
    n s (Set.mem_univ s)

/-! ## Myopic closed forms -/

/-- With `γ = 0` the backup ignores the value function: `Q[V](s, a) = ∑ s' P(s'|s,a) R(s,a,s')`.
Source: [[hudson-2025-corrigibility-transformation]] l. 99 (myopic)
Kind: L
Fidelity: exact -/
lemma Qof_of_disc_zero (hγ : M.γ = 0) (V : S → ℝ) (s : S) (a : A) :
    M.Qof V s a = ∑ s', (M.P s a).mass s' * M.R s a s' := by
  simp [Qof, hγ]

/-- With `γ = 0` and an `s'`-independent reward the backup is the reward itself, under *every*
kernel: `Q[V](s, a) = R(s, a, s₀)` for any `s₀`.
Source: [[hudson-2025-corrigibility-transformation]] l. 99 (non-consequentialist); App. A l. 455
Kind: L
Fidelity: exact -/
lemma Qof_of_indep (hγ : M.γ = 0) (hR : ∀ s a s' s'', M.R s a s' = M.R s a s'') (V : S → ℝ)
    (s : S) (a : A) (s₀ : S) : M.Qof V s a = M.R s a s₀ := by
  rw [M.Qof_of_disc_zero hγ]
  calc ∑ s', (M.P s a).mass s' * M.R s a s'
      = ∑ s', (M.P s a).mass s' * M.R s a s₀ := Finset.sum_congr rfl fun s' _ => by rw [hR s a s' s₀]
    _ = M.R s a s₀ := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]

/-- **Reading A at the MDP level.** For a myopic goal with `s'`-independent reward, the optimal
action set at every state and horizon is the same under every kernel: the kernel never enters the
action value. This is the whole content of "every non-consequentialist goal is corrigible and
interruptible" (T2(a)) — a `T`, and the ledger says so.
Source: [[hudson-2025-corrigibility-transformation]] App. A l. 455; [[corr-wf13-2-inventory]] 030 (C14.1)
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem optSet_Qopt_kernel_free [Nonempty A] (M' : FinMDP S A) (hR : M'.R = M.R) (hγ : M.γ = 0)
    (hγ' : M'.γ = 0) (hind : ∀ s a s' s'', M.R s a s' = M.R s a s'') (n : ℕ) (s : S) :
    optSet (M'.Qopt n) s = optSet (M.Qopt n) s := by
  apply optSet_congr
  intro a
  unfold Qopt
  rw [M'.Qof_of_indep hγ' (by rw [hR]; exact hind) _ s a s, M.Qof_of_indep hγ hind _ s a s, hR]

/-! ## Deterministic policies -/

/-- The deterministic policy playing `f s` at `s`, as a `Distr.delta`.
Source: [[lit-mdp-corrigible-mandate]] rule 1
Kind: D
Fidelity: exact -/
noncomputable def detPol [DecidableEq A] (f : S → A) : Pol S A := fun s => Distr.delta (f s)

/-- The value of a deterministic policy: one action per state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Vpol_detPol_succ [DecidableEq A] (f : S → A) (n : ℕ) (s : S) :
    M.Vpol (detPol f) (n + 1) s = M.Qof (M.Vpol (detPol f) n) s (f s) := by
  rw [Vpol_succ]
  simp [detPol, Distr.delta_mass]

end FinMDP

end Cleanroom.Lit.LitMdpCorrigible
