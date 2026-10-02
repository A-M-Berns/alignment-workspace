import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi

/-!
# The finite sequential self-game: definitions of record

The finite shadow of Cole Wyeth's rOSI self-trust theorem ([[sequential-self-game]] §1, executable
spec `sequential_self_game.py`, class `Analysis`): a finite-horizon decision tree, a finite class of
non-self hypotheses (fixed action and percept kernels), a self-hypothesis "I am `π`" of prior
`1 - δ`, and the mixture `ξ` built from a policy `π`. Fixed points of the plain and floored agents
stand in for reflective oracles. Conventions of record: rewards on arrival, absolute discounting
`γ ^ (t-1)`, continuous extension at `ξ`-null nodes (`ξ(a|h) := π(a|h)`, `w_h := 1`), the
prior-weighted fallback for the percept kernel where the non-self mixture has no mass, and one fixed
selection `π⋆(h)` of an optimal action.

Histories of depth `n` are `Fin n → A × E`; the non-terminal histories (depth `< T` and alive) form
a `Fintype` (`Model.NT`), which is what `kakutani_pi_stdSimplex` is indexed by in `Existence.lean`.
Values are defined by structural recursion on a fuel `T - n`.

Package: `Cleanroom.Uea.UeaColeShadow` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

/-- Histories of depth `n`: sequences of `n` action–percept pairs.
Source: [[sequential-self-game]] §1 ("Tree")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Hist (A E : Type*) (n : ℕ) := Fin n → A × E

variable {A E ι : Type*}

/-- Extend a history by one action–percept pair (`h ↦ hae`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ext {n : ℕ} (h : Hist A E n) (a : A) (e : E) : Hist A E (n + 1) := Fin.snoc h (a, e)

@[simp] theorem init_ext {n : ℕ} (h : Hist A E n) (a : A) (e : E) : Fin.init (ext h a e) = h := by
  simp [ext]

@[simp] theorem ext_last {n : ℕ} (h : Hist A E n) (a : A) (e : E) :
    ext h a e (Fin.last n) = (a, e) := by
  simp [ext]

@[simp] theorem ext_castSucc {n : ℕ} (h : Hist A E n) (a : A) (e : E) (i : Fin n) :
    ext h a e (Fin.castSucc i) = h i := by
  simp [ext]

@[simp] theorem ext_zero_zero (h : Hist A E 0) (a : A) (e : E) : ext h a e 0 = (a, e) := rfl
@[simp] theorem ext_one_zero (h : Hist A E 1) (a : A) (e : E) : ext h a e 0 = h 0 := rfl
@[simp] theorem ext_one_one (h : Hist A E 1) (a : A) (e : E) : ext h a e 1 = (a, e) := rfl
@[simp] theorem ext_two_zero (h : Hist A E 2) (a : A) (e : E) : ext h a e 0 = h 0 := rfl
@[simp] theorem ext_two_one (h : Hist A E 2) (a : A) (e : E) : ext h a e 1 = h 1 := rfl
@[simp] theorem ext_two_two (h : Hist A E 2) (a : A) (e : E) : ext h a e 2 = (a, e) := rfl
@[simp] theorem ext_three_zero (h : Hist A E 3) (a : A) (e : E) : ext h a e 0 = h 0 := rfl
@[simp] theorem ext_three_one (h : Hist A E 3) (a : A) (e : E) : ext h a e 1 = h 1 := rfl
@[simp] theorem ext_three_two (h : Hist A E 3) (a : A) (e : E) : ext h a e 2 = h 2 := rfl
@[simp] theorem ext_three_three (h : Hist A E 3) (a : A) (e : E) : ext h a e 3 = (a, e) := rfl

/-- Every history of positive depth is the extension of its initial segment by its last pair.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ext_init_last {n : ℕ} (h : Hist A E (n + 1)) :
    ext (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2 = h := by
  unfold ext
  exact Fin.snoc_init_self h

/-- The discounted return accumulated on arrival at the nodes of a history: `∑_{i ≤ n} γ^(i-1) r(h_{1:i})`
(reward `r n h` is received on arrival at the depth-`(n+1)` history `h`, discounted by `γ ^ n`).
Source: [[sequential-self-game]] §1 ("Normalisation": every path return)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pathReturnOf (γ : ℝ) (r : (n : ℕ) → Hist A E (n + 1) → ℝ) : (n : ℕ) → Hist A E n → ℝ
  | 0, _ => 0
  | n + 1, h => pathReturnOf γ r n (Fin.init h) + γ ^ n * r n h

@[simp] theorem pathReturnOf_zero (γ : ℝ) (r : (n : ℕ) → Hist A E (n + 1) → ℝ) (h : Hist A E 0) :
    pathReturnOf γ r 0 h = 0 := rfl

@[simp] theorem pathReturnOf_ext (γ : ℝ) (r : (n : ℕ) → Hist A E (n + 1) → ℝ) {n : ℕ}
    (h : Hist A E n) (a : A) (e : E) :
    pathReturnOf γ r (n + 1) (ext h a e) = pathReturnOf γ r n h + γ ^ n * r n (ext h a e) := by
  simp [pathReturnOf]

/-- Policies: an action distribution at every history (only the values at decision nodes matter).
Source: [[sequential-self-game]] §1 ("Policies")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Policy (A E : Type*) := (n : ℕ) → Hist A E n → A → ℝ

/-- Percept kernels. -/
abbrev PerKernel (A E : Type*) := (n : ℕ) → Hist A E n → A → E → ℝ

/-- The support of `π(·|h)`: the actions of positive probability.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def supp [Fintype A] (π : Policy A E) (n : ℕ) (h : Hist A E n) : Finset A :=
  univ.filter (fun a => 0 < π n h a)

/-- **The finite model** ([[sequential-self-game]] §1; `sequential_self_game.py` `Tree`/`Hyp`/`Analysis`):
horizon `T`; an `alive` predicate closed under prefixes (a history of depth `< T` that is alive is a
decision node; "episode ends" are dead nodes); rewards `r n h ≥ 0` on arrival at the depth-`(n+1)`
history `h`, discounted by `γ ^ n` with `γ ∈ (0, 1]`; the normalisation "every path return lies in
`[0, 1]`" (stated for all histories of depth `≤ T`; rewards below dead nodes are unreachable and may
be set to `0`); `ι` non-self hypotheses `ν i` given by fixed action kernels `νa i n h ∈ Δ(A)` and
percept kernels `νe i n h a ∈ Δ(E)`, prior weights `w i ≥ 0` with `∑ w i = δ`, `0 < δ < 1` (the
self-hypothesis has prior `1 - δ`). Scope: finite shadow of rOSI — finite horizon and hypothesis
class, fixed points for oracles, continuous extension at `ξ`-null nodes ([[sequential-self-game]]
§7); `δ = 0` is excluded (the fallback percept kernel divides by `δ`).
Source: [[sequential-self-game]] §1; `sequential_self_game.py` lines 30–100, 103–125
Kind: D
Fidelity: exact (the "tree assigns no actions" terminal rule is the `alive` predicate; action sets
are a single finite `A` at every node, as in the Python where each node's action list is read off a
global alphabet)
Hyps: n/a -/
structure Model (A E ι : Type*) [Fintype A] [Fintype E] [Fintype ι] where
  /-- horizon -/
  T : ℕ
  /-- decision nodes of depth `< T` are the alive histories -/
  alive : (n : ℕ) → Hist A E n → Bool
  alive_init : ∀ (n : ℕ) (h : Hist A E (n + 1)), alive (n + 1) h = true → alive n (Fin.init h) = true
  /-- reward received on arrival at a history of depth `n + 1` -/
  r : (n : ℕ) → Hist A E (n + 1) → ℝ
  r_nonneg : ∀ n h, 0 ≤ r n h
  /-- discount base -/
  γ : ℝ
  γ_pos : 0 < γ
  γ_le_one : γ ≤ 1
  /-- normalisation: every path return lies in `[0, 1]` -/
  norm : ∀ n, n ≤ T → ∀ h : Hist A E n, pathReturnOf γ r n h ≤ 1
  /-- action kernel of the non-self hypothesis `i` -/
  νa : ι → (n : ℕ) → Hist A E n → A → ℝ
  /-- percept kernel of the non-self hypothesis `i` -/
  νe : ι → (n : ℕ) → Hist A E n → A → E → ℝ
  νa_mem : ∀ i n h, νa i n h ∈ stdSimplex ℝ A
  νe_mem : ∀ i n h a, νe i n h a ∈ stdSimplex ℝ E
  /-- prior weights of the non-self hypotheses -/
  w : ι → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  /-- total non-self prior -/
  δ : ℝ
  w_sum : ∑ i, w i = δ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1

namespace Model

variable [Fintype A] [Fintype E] [Fintype ι] (M : Model A E ι)

/-- A history is a decision node (non-terminal) iff its depth is `< T` and it is alive.
Source: [[sequential-self-game]] §1 ("terminal if `t = T` or the tree assigns it no actions")
Kind: D
Fidelity: exact
Hyps: n/a -/
def nonterminal (n : ℕ) (h : Hist A E n) : Prop := n < M.T ∧ M.alive n h = true

instance (n : ℕ) (h : Hist A E n) : Decidable (M.nonterminal n h) :=
  inferInstanceAs (Decidable (n < M.T ∧ M.alive n h = true))

theorem nonterminal.lt {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) : n < M.T := hnt.1

theorem nonterminal.alive {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.alive n h = true := hnt.2

/-- The initial segment of a decision node is a decision node (the tree is prefix-closed).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem nonterminal_init {n : ℕ} {h : Hist A E (n + 1)} (hnt : M.nonterminal (n + 1) h) :
    M.nonterminal n (Fin.init h) :=
  ⟨by have := hnt.1; omega, M.alive_init n h hnt.2⟩

theorem nonterminal_of_ext {n : ℕ} {h : Hist A E n} {a : A} {e : E}
    (hnt : M.nonterminal (n + 1) (ext h a e)) : M.nonterminal n h := by
  have := M.nonterminal_init hnt
  simpa using this

theorem not_nonterminal_of_le {n : ℕ} (hn : M.T ≤ n) (h : Hist A E n) : ¬ M.nonterminal n h :=
  fun hnt => by have := hnt.1; omega

/-- The finite type of decision nodes (non-terminal histories of depth `≤ T`), the index type of the
product of simplices in `Existence.lean`.
Source: [[sequential-self-game]] §4.5 (the product `∏_h Δ(A)` over non-terminal `h`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def NT : Type _ := {p : Σ n : Fin (M.T + 1), Hist A E n // M.nonterminal p.1 p.2}

noncomputable instance instFintypeNT [DecidableEq A] [DecidableEq E] : Fintype M.NT := by
  unfold NT
  infer_instance

/-- The depth of a decision node. -/
def NT.depth (p : M.NT) : ℕ := p.1.1

/-- The history of a decision node. -/
def NT.hist (p : M.NT) : Hist A E p.depth := p.1.2

theorem NT.nonterminal (p : M.NT) : M.nonterminal p.depth p.hist := p.2

/-- `π` is a policy of the model: `π(·|h) ∈ Δ(A)` at every decision node.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsPolicy (π : Policy A E) : Prop := ∀ n h, M.nonterminal n h → π n h ∈ stdSimplex ℝ A

/-- `σ` is sub-stochastic at every decision node: nonnegative with total mass `≤ 1` (the non-self
action conditional `π̄` is sub-stochastic: it has mass `1` where the non-self mixture has mass and
mass `0` elsewhere).
Source: none: infrastructure (Lemma A′ needs the comparison `V^{π̄} ≤ V^*` for a sub-stochastic `π̄`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def IsSubPolicy (σ : Policy A E) : Prop :=
  ∀ n h, M.nonterminal n h → (∀ a, 0 ≤ σ n h a) ∧ ∑ a, σ n h a ≤ 1

theorem IsPolicy.isSubPolicy {π : Policy A E} (hπ : M.IsPolicy π) : M.IsSubPolicy π :=
  fun n h hnt => ⟨(hπ n h hnt).1, (hπ n h hnt).2.le⟩

/-! ### The non-self mixture -/

/-- Joint probability `ν_i(h)` of a history under the non-self hypothesis `i`
(`∏_j ν_i(a_j|h_{<j}) ν_i(e_j|h_{<j}a_j)`).
Source: [[sequential-self-game]] §1 ("Hypotheses"); `sequential_self_game.py` `joint_prob`
Kind: D
Fidelity: exact
Hyps: n/a -/
def nuJoint (i : ι) : (n : ℕ) → Hist A E n → ℝ
  | 0, _ => 1
  | n + 1, h =>
    nuJoint i n (Fin.init h) * M.νa i n (Fin.init h) (h (Fin.last n)).1 *
      M.νe i n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2

@[simp] theorem nuJoint_zero (i : ι) (h : Hist A E 0) : M.nuJoint i 0 h = 1 := rfl

@[simp] theorem nuJoint_ext (i : ι) {n : ℕ} (h : Hist A E n) (a : A) (e : E) :
    M.nuJoint i (n + 1) (ext h a e) = M.nuJoint i n h * M.νa i n h a * M.νe i n h a e := by
  simp [nuJoint]

/-- The unnormalised non-self mixture `ξ_{-S}(h) := ∑_i w_i ν_i(h)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
def xins (n : ℕ) (h : Hist A E n) : ℝ := ∑ i, M.w i * M.nuJoint i n h

/-- The non-self mass after `(h, a)`: `ξ_{-S}(ha) := ∑_i w_i ν_i(h) ν_i(a|h)` (equals `∑_e ξ_{-S}(hae)`).
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
def xinsA (n : ℕ) (h : Hist A E n) (a : A) : ℝ := ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a

/-- The non-self action conditional `π̄(a|h) := ξ_{-S}(ha) / ξ_{-S}(h)`. Junk value `0` where
`ξ_{-S}(h) = 0` (Lean's `x / 0 = 0`); every use is guarded by a factor `1 - w_h` that vanishes there
or by a positivity hypothesis.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact where `ξ_{-S}(h) > 0`; junk `0` elsewhere (disclosed)
Hyps: n/a -/
noncomputable def pibar (n : ℕ) (h : Hist A E n) (a : A) : ℝ := M.xinsA n h a / M.xins n h

/-- The percept kernel of the mixture, `ξ(e|ha)`: the non-self mixture's percept conditional where
`ξ_{-S}(ha) > 0`, and the prior-weighted non-self percept mixture `∑_i w_i ν_i(e|ha) / δ` otherwise
(the fallback of [[sequential-self-game]] §1). It does not mention the policy (audit fact F1).
Source: [[sequential-self-game]] §1 ("The self-hypothesis"); `sequential_self_game.py` `envS`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def xie (n : ℕ) (h : Hist A E n) (a : A) (e : E) : ℝ :=
  if M.xinsA n h a = 0 then (∑ i, M.w i * M.νe i n h a e) / M.δ
  else (∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.νe i n h a e) / M.xinsA n h a

/-! ### The self-hypothesis and the mixture built from a policy -/

/-- The self-hypothesis's joint `ξ_S(h) := ∏_j π(a_j|h_{<j}) ξ(e_j|h_{<j}a_j)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def xiS (π : Policy A E) : (n : ℕ) → Hist A E n → ℝ
  | 0, _ => 1
  | n + 1, h =>
    xiS π n (Fin.init h) * π n (Fin.init h) (h (Fin.last n)).1 *
      M.xie n (Fin.init h) (h (Fin.last n)).1 (h (Fin.last n)).2

@[simp] theorem xiS_zero (π : Policy A E) (h : Hist A E 0) : M.xiS π 0 h = 1 := rfl

@[simp] theorem xiS_ext (π : Policy A E) {n : ℕ} (h : Hist A E n) (a : A) (e : E) :
    M.xiS π (n + 1) (ext h a e) = M.xiS π n h * π n h a * M.xie n h a e := by
  simp [xiS]

/-- The mixture `ξ(h) := (1 - δ) ξ_S(h) + ξ_{-S}(h)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def xi (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  (1 - M.δ) * M.xiS π n h + M.xins n h

/-- The mixture mass after `(h, a)`: `ξ(ha) := ∑_e ξ(hae)`.
Source: [[sequential-self-game]] §1; `sequential_self_game.py` `xi_act`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def xiA (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  ∑ e, M.xi π (n + 1) (ext h a e)

/-- The self-posterior `w_h := (1 - δ) ξ_S(h) / ξ(h)`, with the convention `w_h := 1` when `ξ(h) = 0`
(the continuous extension; note Lean's `x / 0 = 0` would give the opposite value, hence the explicit
case split).
Source: [[sequential-self-game]] §1 ("Zero-probability actions")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def wS (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  if M.xi π n h = 0 then 1 else (1 - M.δ) * M.xiS π n h / M.xi π n h

/-- The self-posterior after an action, `w_{ha} := (1 - δ) ξ_S(h) π(a|h) / ξ(ha)`, `:= 1` when `ξ(ha) = 0`.
Source: [[sequential-self-game]] §1 (F1: `w_{hae} = w_{ha}`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def wA (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  if M.xiA π n h a = 0 then 1 else (1 - M.δ) * M.xiS π n h * π n h a / M.xiA π n h a

/-- The mixture's action conditional `ξ(a|h) := ξ(ha) / ξ(h)`, with the continuous extension
`ξ(a|h) := π(a|h)` when `ξ(h) = 0`.
Source: [[sequential-self-game]] §1 ("Zero-probability actions — continuous extension")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def xia (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  if M.xi π n h = 0 then π n h a else M.xiA π n h a / M.xi π n h


/-! ### Values by backward induction -/

/-- An aggregator turns the action-indexed continuation values at a node into the node's value:
`aggPol σ` averages under `σ(·|h)`, `aggMax` takes the maximum.
Source: none: infrastructure (one recursion for `V^π`, `V^*`, `V_ξ`, `V^{ν_i}`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Agg (A E : Type*) := (n : ℕ) → Hist A E n → (A → ℝ) → ℝ

/-- Average under a policy: `q ↦ ∑_a σ(a|h) q a`. -/
noncomputable def aggPol (σ : Policy A E) : Agg A E := fun n h q => ∑ a, σ n h a * q a

/-- Maximum over actions (`A` nonempty). -/
noncomputable def aggMax [Nonempty A] : Agg A E := fun _ _ q => univ.sup' univ_nonempty q

/-- Value recursion with fuel `k` (structural): `valF agg κ (k+1) n h = agg (Q-values from the
children with fuel `k`)` at decision nodes and `0` elsewhere; `valF _ _ 0 = 0`.
Source: [[sequential-self-game]] §1 ("Values"); `sequential_self_game.py` `_values`
Kind: D
Fidelity: exact (the fuel is `T - n`, see `val`)
Hyps: n/a -/
noncomputable def valF (agg : Agg A E) (κ : PerKernel A E) : ℕ → (n : ℕ) → Hist A E n → ℝ
  | 0, _, _ => 0
  | k + 1, n, h =>
    if M.nonterminal n h then
      agg n h (fun a => ∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + valF agg κ k (n + 1) (ext h a e)))
    else 0

/-- The value at a history: `valF` with fuel `T - n` (values at depth `≥ T` are `0`).
Source: [[sequential-self-game]] §1 ("Values")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def val (agg : Agg A E) (κ : PerKernel A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  M.valF agg κ (M.T - n) n h

/-- The action value at `(h, a)`: `∑_e κ(e|ha) (γ^n r(hae) + val(hae))`.
Source: [[sequential-self-game]] §1 ("Values")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def qval (agg : Agg A E) (κ : PerKernel A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  ∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + M.val agg κ (n + 1) (ext h a e))

theorem val_eq_zero_of_not_nonterminal (agg : Agg A E) (κ : PerKernel A E) {n : ℕ} {h : Hist A E n}
    (hnt : ¬ M.nonterminal n h) : M.val agg κ n h = 0 := by
  unfold val
  cases hk : M.T - n with
  | zero => simp [valF]
  | succ k => simp [valF, hnt]

/-- Unfolding at a decision node: `val = agg (qval)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem val_eq_of_nonterminal (agg : Agg A E) (κ : PerKernel A E) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) : M.val agg κ n h = agg n h (M.qval agg κ n h) := by
  have hlt : n < M.T := hnt.1
  have hk : M.T - n = (M.T - (n + 1)) + 1 := by omega
  unfold val
  rw [hk]
  simp only [valF, hnt, if_true]
  rfl

/-- Induction on the remaining depth: a property that holds at terminal histories and propagates
from the children of a decision node to the node holds everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem depth_induction (P : (n : ℕ) → Hist A E n → Prop)
    (hterm : ∀ n h, ¬ M.nonterminal n h → P n h)
    (hstep : ∀ n h, M.nonterminal n h → (∀ a e, P (n + 1) (ext h a e)) → P n h) :
    ∀ n h, P n h := by
  have key : ∀ k n (h : Hist A E n), M.T - n ≤ k → P n h := by
    intro k
    induction k with
    | zero =>
      intro n h hk
      exact hterm n h (M.not_nonterminal_of_le (by omega) h)
    | succ k ih =>
      intro n h hk
      by_cases hnt : M.nonterminal n h
      · exact hstep n h hnt (fun a e => ih (n + 1) (ext h a e) (by omega))
      · exact hterm n h hnt
  intro n h
  exact key (M.T - n) n h le_rfl

/-! ### The named values -/

/-- Policy value `V^π_ξ(h)`: actions from `π`, percepts from `ξ(e|·)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Vpi (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ := M.val (aggPol π) M.xie n h

/-- `Q^π_ξ(h, a)`. -/
noncomputable def Qpi (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  M.qval (aggPol π) M.xie n h a

/-- Optimal value `V^*_ξ(h)`: percepts from `ξ(e|·)`, the agent controlling all future actions. It does
not depend on any policy (the percept kernel is policy-independent).
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Vstar [Nonempty A] (n : ℕ) (h : Hist A E n) : ℝ := M.val aggMax M.xie n h

/-- `Q^*_ξ(h, a)`. -/
noncomputable def Qstar [Nonempty A] (n : ℕ) (h : Hist A E n) (a : A) : ℝ := M.qval aggMax M.xie n h a

/-- EDT value `V_ξ(h) = ∑_a ξ(a|h) Q_ξ(h,a)`: actions from `ξ`'s own action conditionals (continuous
extension at `ξ`-null nodes), percepts from `ξ(e|·)`. This recursive definition **is** the definition
of record; `Facts.lean` shows it equals the mixture's conditional expectation where `ξ(ha) > 0`.
Source: [[sequential-self-game]] §1 ("EDT values")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Vxi (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  M.val (aggPol (M.xia π)) M.xie n h

/-- `Q_ξ(h, a)`. -/
noncomputable def Qxi (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  M.qval (aggPol (M.xia π)) M.xie n h a

/-- Hypothesis-internal value `V^{ν_i}(h)`: actions and percepts from `ν_i`'s own kernels.
Source: [[sequential-self-game]] §1 (Lemma A, `Q^ν`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Vnu (i : ι) (n : ℕ) (h : Hist A E n) : ℝ := M.val (aggPol (M.νa i)) (M.νe i) n h

/-- `Q^{ν_i}(h, a)`. -/
noncomputable def Qnu (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  M.qval (aggPol (M.νa i)) (M.νe i) n h a

/-- The value of the non-self action conditional `π̄` as a policy against the percept kernel `ξ(e|·)`
(Lemma A′'s `Q^{π̄}_ξ`).
Source: [[sequential-self-game]] §1 (Lemma A′)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Vbar (n : ℕ) (h : Hist A E n) : ℝ := M.val (aggPol M.pibar) M.xie n h

/-- `Q^{π̄}_ξ(h, a)`. -/
noncomputable def Qbar (n : ℕ) (h : Hist A E n) (a : A) : ℝ := M.qval (aggPol M.pibar) M.xie n h a

/-- The non-self continuation `Q̄(h,a) := ∑_i w_i ν_i(ha) Q^{ν_i}(h,a) / ξ_{-S}(ha)` of Lemma A. Junk
`0` where `ξ_{-S}(ha) = 0`.
Source: [[sequential-self-game]] §1 (Lemma A)
Kind: D
Fidelity: exact where `ξ_{-S}(ha) > 0`; junk `0` elsewhere (disclosed)
Hyps: n/a -/
noncomputable def Qmix (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  (∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a) / M.xinsA n h a

section Star
variable [Nonempty A]

/-- The canonical optimal action `π⋆(h)`: one fixed selection of an action attaining
`max_a Q^*_ξ(h,a)` (the note takes the first such action in an enumeration of `A`; the model carries no
enumeration, so the selection is a `Classical.choice`, fixed once and for all and independent of any
policy — [[sequential-self-game]] §7 item 6 says any fixed selection works). At a node where the
optimal action is unique it is that action (`piStar_eq_of_unique`).
Source: [[sequential-self-game]] §1 ("`π^*_ξ(h)` is fixed once and for all as the first action attaining")
Kind: D
Fidelity: variant: a fixed choice instead of the first action of an enumeration (disclosed)
Hyps: n/a -/
noncomputable def piStar (n : ℕ) (h : Hist A E n) : A :=
  Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (M.Qstar n h))

theorem Qstar_piStar (n : ℕ) (h : Hist A E n) :
    M.Qstar n h (M.piStar n h) = univ.sup' univ_nonempty (M.Qstar n h) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (M.Qstar n h))).2.symm

/-- `M(h) := max_a Q_ξ(h, a)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Mx (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  univ.sup' univ_nonempty (M.Qxi π n h)

/-- The argmax set `𝒜_h := {a | Q_ξ(h,a) = M(h)}`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def argmaxSet (π : Policy A E) (n : ℕ) (h : Hist A E n) : Finset A :=
  univ.filter (fun a => M.Qxi π n h a = M.Mx π n h)

/-- The trust bound at `h`: `(TB_h) : M(h) ≥ w_h V^*_ξ(h)`.
Source: [[sequential-self-game]] §1 ("Trust bound at `h`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def TB (π : Policy A E) (n : ℕ) (h : Hist A E n) : Prop :=
  M.wS π n h * M.Vstar n h ≤ M.Mx π n h

/-- The floor residual `r_h := M(h) - w_h V^*_ξ(h)` whose sign classifies a node for the floored agent.
Source: [[oracle-side-gaps-reaudit]] Q5; `sequential_self_game.py` `floor_sign`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def resid (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  M.Mx π n h - M.wS π n h * M.Vstar n h

/-- The loss `ε(h) := V^*_ξ(h) - V^π_ξ(h)`.
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def gap (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ := M.Vstar n h - M.Vpi π n h

end Star

/-- The odds against the self-hypothesis `O_h := (1 - w_h) / w_h` (junk `0` at `w_h = 0`, which is why
Theorems B and C carry `0 < w_h`).
Source: [[sequential-self-game]] §1
Kind: D
Fidelity: exact for `w_h > 0`
Hyps: n/a -/
noncomputable def odds (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  (1 - M.wS π n h) / M.wS π n h

/-- The odds against the self after an action, `O_{ha} := (1 - w_{ha}) / w_{ha}`. -/
noncomputable def oddsA (π : Policy A E) (n : ℕ) (h : Hist A E n) (a : A) : ℝ :=
  (1 - M.wA π n h a) / M.wA π n h a

/-- The non-self mixture's mass on the agent's supported actions, `p̄_h := ∑_{a ∈ supp π(·|h)} π̄(a|h)`.
Source: [[sequential-self-game]] §3 (Theorem B)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def pbar (π : Policy A E) (n : ℕ) (h : Hist A E n) : ℝ :=
  ∑ a ∈ supp π n h, M.pibar n h a

/-- **Pure policy**: mass `1` on one action at every decision node (the note's "pure fixed point" is a pure
policy that is a fixed point). Moved here from `Open.lean` in repair round 2 so that the open statements' module
is a leaf (round-2 adversarial audit, item 2).
Source: [[sequential-self-game]] §4.5 ("Pure fixed points")
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsPure (π : Policy A E) : Prop := ∀ n h, M.nonterminal n h → ∃ a, π n h a = 1

section FixedPoints
variable [Nonempty A]

/-- **Plain fixed point**: `π` is a policy and `supp π(·|h) ⊆ 𝒜_h` at every decision node `h`, including
`ξ`-null ones (the finite analogue of an oracle consistent about `π_S` on every input). Scope: finite
shadow of rOSI ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §1 ("Fixed point (plain agent)"); `sequential_self_game.py`
`is_fixed_point`
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsPlainFP (π : Policy A E) : Prop :=
  M.IsPolicy π ∧ ∀ n h, M.nonterminal n h → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h

/-- **Floored fixed point** (fixed point of the current-node floor `π†`), by the sign of
`r_h = M(h) - w_h V^*_ξ(h)`: `r_h < 0 ⇒ supp π(·|h) = {π⋆(h)}`; `r_h > 0 ⇒ supp ⊆ 𝒜_h`;
`r_h = 0 ⇒ supp ⊆ 𝒜_h ∪ {π⋆(h)}` — `is_floored_fixed_point` verbatim (the note's `λ_h` is
`π(π⋆(h)|h)`). Scope: finite shadow of rOSI ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §1 ("Floored agent `π†`"); `sequential_self_game.py`
`is_floored_fixed_point`
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsFlooredFP (π : Policy A E) : Prop :=
  M.IsPolicy π ∧ ∀ n h, M.nonterminal n h →
    (M.resid π n h < 0 → ∀ a, 0 < π n h a → a = M.piStar n h) ∧
    (0 < M.resid π n h → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h) ∧
    (M.resid π n h = 0 → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h ∨ a = M.piStar n h)

end FixedPoints

end Model

end Cleanroom.Uea.UeaColeShadow
