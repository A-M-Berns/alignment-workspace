/-
  edt-node-value.lean  —  run2, modality LEAN-CORE.

  TODO: "EDT-derived node-value: kill the argmax tautology in updateless deference."

  ----------------------------------------------------------------------------
  THE ROUND-1 SIN THIS FILE FIXES (read first)
  ----------------------------------------------------------------------------
  Round 1 (`UpdatelessDeference{,2}`) defined "A updatelessly-defers to u" via a
  per-node valuation `node_value : S → A → ℝ` that was a *FREE INPUT*, never tied
  to the utility `U`. The discrimination between a mugging-caver and a non-caver
  was supplied by the MODELER's hand-chosen `node_value`, not by the formalism
  (critique §3). The kernel-checked Lean was therefore "argmax of a separable U is
  globally optimal" with the discriminator hand-fed — a tautology.

  This file removes the free input. The per-node value is now DERIVED, as a genuine
  EDT conditional of the SAME utility `U`, routed entirely through an explicit
  self-prediction / reachability kernel `κ`:

        v_s(a)  :=  U (κ s a)      -- the utility of the whole policy the agent
                                      PREDICTS it is running, conditioned on
                                      "reach s, play a at s".

  `κ s a : S → A` is the agent's self-model: conditioned on the local event
  "(reach s, play a)", which whole policy do I expect to be executing? `vNode` is
  `U ∘ κ`; the kernel is LITERALLY inside the definition, not a relabel. Different
  κ ⟹ different node-values ⟹ different EDT argmax. There is NO free per-node
  number anywhere.

  Two results, the SECOND mandatory (it certifies κ is not inert):

  (I)  DECOUPLED COINCIDENCE (`edt_decoupled_globally_optimal`). When U is
       separable (`U π = ∑ s, p s · u s (π s)`, p ≥ 0) AND κ is *decoupled* at s
       (it plays a at s and a FIXED off-s policy `base s`, independent of a — i.e.
       reaching s and the local action do not couple to actions elsewhere), the
       EDT-derived node-value `vNode = U∘κ` ranks local actions exactly as `u s`
       does, and the EDT-argmax policy DOMINATES every policy:  ∀ π, U π ≤ U π★.
       The κ-routing is load-bearing: the proof must unfold `U (κ s a)` THROUGH
       separability to recover `p s · u s a + (a-independent off-s mass)`. This is
       NOT a re-proof of `split_eq_global`: that took the argmax as a free hypothesis
       `hLoc`; here the argmax is DERIVED from `vNode = U∘κ` via `κ`, and the bridge
       `vNode-argmax ⟺ u-argmax` (`vNode_decoupled_eq`) is the new content.

  (II) COUPLED NEAR-MISS (`mugging_edt_misses`, MANDATORY). A counterfactual-mugging
       instance where U is GENUINELY NON-SEPARABLE — the +10000 acausal reward fires
       ONLY on the matched-pay diagonal, so there is NO off-diagonal free lunch and
       `globalOpt = (pay,pay)` is the UNRESTRICTED maximizer over all four policies
       (`global_opt_dominates_all`). κ SEVERS the correlation: the EDT self at EACH node,
       conditioning on its local action, predicts the OTHER node frozen at refuse, so the
       matched-pay reward never fires and the EDT-argmax at BOTH nodes is refuse. The
       EDT-derived policy `(refuse,refuse)` (computed at both nodes, NOT diagonal-by-fiat)
       STRICTLY DIVERGES from the global UDT optimum `(pay,pay)`, the gap = the severed
       acausal payoff. `not_separable` proves `Separable U p u` FAILS here, so the
       decoupled-coincidence theorem genuinely does not apply (the coupling is real). This
       PROVES `vNode` is not a relabel of the local argmax of U: SAME U, a severing κ
       disagrees with the optimum by exactly the severed acausal term; a CORRELATED κ agrees.

  NON-VACUITY / NEAR-MISS in the LEAN-CORE sense the task asks:
   * Non-vacuity witness: `Decoupled.edt_attains_global` — a concrete separable
     instance, κ appearing in the value, EDT-argmax = global optimum, by `decide`.
   * Near-miss (weaker hypothesis ⇒ the coincidence is FALSE): drop "U separable"
     (`Mugging.not_separable`) — the coupled mugging instance has EDT-argmax (computed at
     both nodes) STRICTLY below the unrestricted optimum (`separability_load_bearing`,
     `mugging_edt_misses`). So separability is doing real work; without it the theorem fails.

  The TARGET objects (the EDT-conditional v_s and the global UDT optimum) are NOT
  hypotheses: `vNode` is DEFINED as `U∘κ`, `policyValue` as `U`, and both theorems
  CONCLUDE about them. No LI machinery, no asymptotics — pure finite real algebra.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Finset

namespace EDTNodeValue

variable {S A : Type*} [Fintype S] [Fintype A]

/- ============================================================================
   THE DERIVED EDT NODE-VALUE (no free input — it is U ∘ κ)
   ============================================================================ -/

/-- Global / updateless (UDT) objective: utility of the WHOLE policy.
    We use the COUPLED type `U : (S → A) → ℝ` deliberately — a coupled U cannot be
    written `∑ s, p s · u s (π s)`, which is exactly what lets κ matter and what the
    round-1 decoupled type `S → A → ℝ` could not express. -/
def policyValue (U : (S → A) → ℝ) (π : S → A) : ℝ := U π

/-- **The EDT-derived per-node value.**  `κ s a : S → A` is the self-prediction /
    reachability kernel: the whole policy the agent expects to be running,
    CONDITIONED on the local event "reach `s`, play `a` at `s`".  The node value is
    the conditional expectation of the SAME utility under that prediction:

        v_s(a)  =  U (κ s a).

    κ is inside the definition; this is NOT a free `node_value`. -/
def vNode (U : (S → A) → ℝ) (κ : S → A → (S → A)) (s : S) (a : A) : ℝ :=
  U (κ s a)

/- ============================================================================
   (I) DECOUPLED COINCIDENCE
   ============================================================================ -/

section Decoupled
variable [Nonempty A] [DecidableEq S]

/-- **Separability of U** through a per-situation `u` and prior `p`. Structural:
    a coupled U cannot satisfy this for any `u,p`. -/
def Separable (U : (S → A) → ℝ) (p : S → ℝ) (u : S → A → ℝ) : Prop :=
  ∀ π : S → A, U π = ∑ s, p s * u s (π s)

/-- **Decoupling of κ at `s`** through a fixed off-`s` base policy `base : S → S → A`.
    `κ s a` plays `a` at `s` and the FIXED policy `base s` everywhere else,
    INDEPENDENT of `a`. This is "reach s, and the local action, do not couple to
    actions elsewhere" — the reachability-independence the task names. The off-`s`
    part of κ does NOT depend on the local action `a`; that is the whole content of
    "decoupled". -/
def Decoupled (κ : S → A → (S → A)) (base : S → S → A) : Prop :=
  ∀ s a, κ s a = Function.update (base s) s a

/-- **κ-collapse (the new, load-bearing content).** Under separability and decoupling,
    the EDT-derived node value `vNode = U∘κ` equals `p s · u s a` plus an
    `a`-INDEPENDENT off-`s` mass. The dependence on the local action `a` is carried
    EXACTLY by `p s · u s a` — extracted by unfolding `U (κ s a)` THROUGH separability.
    κ is load-bearing: the off-`s` constant is `κ`'s prediction `base s`. -/
theorem vNode_decoupled_eq
    (U : (S → A) → ℝ) (κ : S → A → (S → A)) (p : S → ℝ) (u : S → A → ℝ)
    (base : S → S → A)
    (hSep : Separable U p u) (hDec : Decoupled κ base) (s : S) (a : A) :
    vNode U κ s a
      = p s * u s a + ∑ t ∈ univ.erase s, p t * u t (base s t) := by
  unfold vNode
  rw [hSep (κ s a), hDec s a,
      ← Finset.add_sum_erase univ (fun x => p x * u x (Function.update (base s) s a x))
          (Finset.mem_univ s)]
  -- the `s` term: update at s gives a; the off-s sum: update agrees with base off s.
  rw [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

/-- **vNode-argmax ⟺ u-argmax in the decoupled case** (so the κ-derivation collapses
    to the local argmax ONLY here, and provably so). If `p s ≥ 0`, an action that
    maximizes `u s` also maximizes `vNode … s ·`. The genuine `κ`-derivation thus
    REPRODUCES the local argmax in the decoupled regime — not by definition, but
    because the off-`s` mass κ predicts is `a`-independent. -/
theorem vNode_argmax_of_u_argmax
    (U : (S → A) → ℝ) (κ : S → A → (S → A)) (p : S → ℝ) (u : S → A → ℝ)
    (base : S → S → A)
    (hSep : Separable U p u) (hDec : Decoupled κ base)
    (hp : ∀ s, 0 ≤ p s) (s : S) (astar : A)
    (hloc : ∀ a, u s a ≤ u s astar) :
    ∀ a, vNode U κ s a ≤ vNode U κ s astar := by
  intro a
  rw [vNode_decoupled_eq U κ p u base hSep hDec s a,
      vNode_decoupled_eq U κ p u base hSep hDec s astar]
  have : p s * u s a ≤ p s * u s astar :=
    mul_le_mul_of_nonneg_left (hloc a) (hp s)
  linarith

/-- **(I) DECOUPLED COINCIDENCE — main theorem.** Let `π★` pick, at each `s`, an
    action maximizing the EDT-DERIVED node value `vNode U κ s ·` (NOT a free
    valuation; NOT the local argmax of U by fiat — the EDT conditional through κ).
    Under separability + decoupling + `p ≥ 0`, `π★` DOMINATES every policy in the
    global UDT objective:  ∀ π, policyValue U π ≤ policyValue U π★.

    Inputs are ONLY `U` and `κ` (plus the structural witnesses p,u,base that name
    the decoupling). node_value is DERIVED. This is NOT `split_eq_global`: there the
    local argmax was a free hypothesis; here it is forced to coincide with the
    vNode-argmax via `vNode_decoupled_eq`, and that collapse is the content. -/
theorem edt_decoupled_globally_optimal
    (U : (S → A) → ℝ) (κ : S → A → (S → A)) (p : S → ℝ) (u : S → A → ℝ)
    (base : S → S → A)
    (hSep : Separable U p u) (hDec : Decoupled κ base)
    -- `hp : ∀ s, 0 ≤ p s` is part of the decoupled-regime spec and is supplied by the
    -- witness; it is not NEEDED here because the EDT-node-value ranking `hEDT` already
    -- transfers (via the κ-collapse) directly to `p s · u s`, so we keep it as `_hp`.
    (_hp : ∀ s, 0 ≤ p s)
    (πstar : S → A)
    -- π★ picks an EDT-node-value maximizer at each s (the only spec on π★):
    (hEDT : ∀ s a, vNode U κ s a ≤ vNode U κ s (πstar s)) :
    ∀ π : S → A, policyValue U π ≤ policyValue U πstar := by
  -- Step 1: π★ is also a LOCAL u-argmax at each s — DERIVED from hEDT via the κ-collapse.
  have hLoc : ∀ s a, p s * u s a ≤ p s * u s (πstar s) := by
    intro s a
    have h := hEDT s a
    rw [vNode_decoupled_eq U κ p u base hSep hDec s a,
        vNode_decoupled_eq U κ p u base hSep hDec s (πstar s)] at h
    linarith
  -- Step 2: separable global objective is dominated termwise.
  intro π
  unfold policyValue
  rw [hSep π, hSep πstar]
  exact Finset.sum_le_sum (fun s _ => hLoc s (π s))

end Decoupled

/- ============================================================================
   NON-VACUITY WITNESS (decoupled): κ in the value, EDT-argmax = global optimum.
   Two situations, two actions. u s1 maximised at action 1; u s2 maximised at 0.
   κ is the decoupled kernel `update (base s) s a`. Everything by `decide`/`norm_num`.
   ============================================================================ -/
namespace Decoupled

abbrev S2 := Fin 2
abbrev A2 := Fin 2

/-- prior, both situations weight 1. -/
def p : S2 → ℝ := fun _ => 1
/-- separable per-situation utility: at s=0 best action is 1 (payoff 3 vs 1);
    at s=1 best action is 0 (payoff 4 vs 2). -/
def u : S2 → A2 → ℝ := fun s a =>
  if s = 0 then (if a = 1 then 3 else 1) else (if a = 0 then 4 else 2)
/-- the coupled-type utility, built separably from `u`. -/
def U : (S2 → A2) → ℝ := fun π => ∑ s, p s * u s (π s)
/-- a fixed base policy (plays 0 everywhere); the off-s prediction of κ. -/
def base : S2 → S2 → A2 := fun _ _ => 0
/-- the DECOUPLED kernel: κ s a plays a at s and base s elsewhere. -/
def κ : S2 → A2 → (S2 → A2) := fun s a => Function.update (base s) s a

theorem hSep : Separable U p u := fun _ => rfl
theorem hDec : Decoupled κ base := fun _ _ => rfl
theorem hp : ∀ s, 0 ≤ p s := fun _ => by norm_num [p]

/-- The EDT-derived argmax policy: at each s, the action maximizing `vNode U κ s ·`.
    Computed (not hand-fed): s=0 ↦ 1, s=1 ↦ 0. -/
def edtPolicy : S2 → A2 := fun s => if s = 0 then 1 else 0

/-- `κ` genuinely appears in the node value: `vNode U κ 0 1` unfolds through κ.
    Check it equals the conditional value of the policy κ predicts at (0,1). -/
theorem vNode_via_kappa :
    vNode U κ 0 1 = U (Function.update (base 0) 0 1) := rfl

/-- The EDT node value at s=0 ranks action 1 above action 0 (so EDT-argmax picks 1),
    and this ranking is produced THROUGH κ (vNode = U∘κ), with the off-s base mass. -/
theorem edt_ranks_s0 : vNode U κ 0 0 < vNode U κ 0 1 := by
  simp only [vNode, U, κ, base, p, u, Fin.sum_univ_two, Function.update_apply]
  norm_num

theorem edt_ranks_s1 : vNode U κ 1 1 < vNode U κ 1 0 := by
  simp only [vNode, U, κ, base, p, u, Fin.sum_univ_two, Function.update_apply]
  norm_num

/-- `edtPolicy` maximizes the EDT-derived node value at every (s,a). -/
theorem edtPolicy_is_edt_argmax : ∀ s a, vNode U κ s a ≤ vNode U κ s (edtPolicy s) := by
  intro s a
  fin_cases s <;> fin_cases a <;>
    simp only [edtPolicy, vNode, U, κ, base, p, u, Fin.sum_univ_two, Function.update_apply] <;>
    norm_num

/-- **NON-VACUITY WITNESS.** The EDT-derived argmax policy attains the GLOBAL UDT
    optimum: it dominates every policy. By the main theorem, with κ load-bearing. -/
theorem edt_attains_global :
    ∀ π : S2 → A2, policyValue U π ≤ policyValue U edtPolicy :=
  edt_decoupled_globally_optimal U κ p u base hSep hDec hp edtPolicy edtPolicy_is_edt_argmax

/-- Sanity: the global optimum value is 3 + 4 = 7 (action 1 at s0, action 0 at s1),
    a strict improvement over e.g. the all-0 policy (value 1 + 4 = 5). NON-trivial. -/
theorem global_opt_value : policyValue U edtPolicy = 7 := by
  simp only [policyValue, U, edtPolicy, p, u, Fin.sum_univ_two]; norm_num

theorem all_zero_strictly_worse :
    policyValue U (fun _ => 0) < policyValue U edtPolicy := by
  simp only [policyValue, U, edtPolicy, p, u, Fin.sum_univ_two]; norm_num

end Decoupled

/- ============================================================================
   (II) COUPLED NEAR-MISS  (MANDATORY) — counterfactual mugging / Twin structure.
   ============================================================================
   TWO nodes; the coupling lives in a GENUINELY NON-SEPARABLE U so that NO
   off-diagonal "free lunch" exists and `globalOpt` is the UNRESTRICTED maximizer
   over all four policies — NO diagonal-by-fiat. `vNode = U∘κ` uses the SAME U.

     node 0 = `self`  (the agent's own decision)
     node 1 = `twin`  (the predicted / correlated copy)
     A = Fin 2 :  0 = refuse, 1 = pay.

   Whole-policy utility (SAME U everywhere), the ACAUSAL coupling encoded directly:
     U π = (own cost:    -100 if π 0 = pay)
         + (acausal reward: +10000 ONLY if BOTH play pay, i.e. π 0 = π 1 = pay).
   The "+10000 iff matched-pay" term is the acausal correlation: Omega rewards you in
   the counterfactual where the predicted copy does what you do. This U is NON-separable
   (the interaction term `U(0,0)+U(1,1)−U(0,1)−U(1,0) = 10000 ≠ 0`), so it CANNOT be
   written `∑ s, p s · u s (π s)` — `Separable U p u` FAILS (proved: `not_separable`).
   The UNRESTRICTED optimum over ALL FOUR policies is `(pay,pay) = 9900` (`global_opt_dominates_all`):
     (refuse,refuse)=0, (refuse,pay)=0, (pay,refuse)=−100, (pay,pay)=9900.   No free lunch.

   The self-prediction kernel κ SEVERS the correlation: the EDT self at each node,
   conditioning on "reach node s, play a here," predicts the OTHER (twin) node plays a
   FIXED action (refuse, 0) INDEPENDENT of `a` — it does not believe its local action
   correlates with the twin's.  κ s a = update (fun _ => 0) s a = (s ↦ a, other ↦ 0).
   (This κ IS `Decoupled` with base ≡ 0 — but `Separable` FAILS, so the decoupled-
   coincidence theorem does not apply: exactly the point.)  Then for the EDT self at
   EITHER node, the matched-pay reward never fires (the other node is predicted to refuse),
   so paying only burns the own cost: the EDT-argmax is REFUSE at BOTH nodes.  The
   EDT-argmax policy is therefore `(refuse,refuse) = 0`, computed at BOTH nodes (NOT
   projected onto a diagonal by hand), and it STRICTLY misses the genuine unrestricted
   optimum `(pay,pay) = 9900`, by the acausal +10000 reward κ severed.  A CORRELATED κ
   (twin copies the action) makes the matched-pay reward fire and AGREES with the optimum
   — so κ is load-bearing.  No second utility anywhere; the near-miss uses the SAME U as
   the global optimum and routes the EDT node value through κ.
   ============================================================================ -/
namespace Mugging

abbrev S2 := Fin 2     -- node 0 = self; node 1 = twin / predicted copy
abbrev A2 := Fin 2     -- 0 = refuse, 1 = pay

/-- The whole-policy utility (SAME U for the global optimum AND, via κ, the EDT node value).
    Own action costs 100 if pay; the ACAUSAL reward +10000 fires ONLY on the matched-pay
    diagonal (π 0 = π 1 = pay). This is GENUINELY non-separable — the coupling is in U's
    form, so there is no off-diagonal free lunch and `globalOpt` is the unrestricted max. -/
def U : (S2 → A2) → ℝ := fun π =>
  (if π 0 = 1 then (-100 : ℝ) else 0) + (if π 0 = 1 ∧ π 1 = 1 then 10000 else 0)

/-- **The acausal-SEVERING kernel.** κ s a predicts: play `a` at node `s`, but the OTHER
    node plays refuse (0) regardless of `a`. The severance is HERE, in κ — `vNode = U∘κ`
    reuses the SAME U. (`update (fun _ => 0) s a` = node s↦a, other↦0.) -/
def κ : S2 → A2 → (S2 → A2) := fun s a => Function.update (fun _ => (0 : A2)) s a

/-- **U is NOT separable.** No `(p,u)` witnesses `Separable U p u`: separability forces the
    interaction `U(0,0)+U(1,1) = U(0,1)+U(1,0)`, but here `0+9900 ≠ 0+(-100)`. So the
    decoupled-coincidence theorem genuinely does NOT apply to this instance — the coupling
    is real, not a diagonal-by-fiat. -/
theorem not_separable :
    ¬ ∃ (p : S2 → ℝ) (u : S2 → A2 → ℝ),
        EDTNodeValue.Separable U p u := by
  rintro ⟨p, u, hSep⟩
  -- interaction term must vanish for any separable U, but it equals 10000 here.
  have h00 := hSep (fun _ => 0)
  have h11 := hSep (fun _ => 1)
  have h01 := hSep (fun s => if s = 1 then 1 else 0)
  have h10 := hSep (fun s => if s = 0 then 1 else 0)
  simp only [U, Fin.sum_univ_two] at h00 h11 h01 h10
  norm_num at h00 h11 h01 h10
  -- h00 : 0 = p0*u 0 0 + p1*u 1 0 ; h11 : 9900 = p0*u 0 1 + p1*u 1 1
  -- h01 : 0 = p0*u 0 0 + p1*u 1 1 ; h10 : -100 = p0*u 0 1 + p1*u 1 0
  -- (p0 u01 + p1 u11) + (p0 u00 + p1 u10) = (p0 u00 + p1 u11) + (p0 u01 + p1 u10)
  -- ⇒ 9900 + (-100) = 0 + 0, contradiction.
  linarith [h00, h11, h01, h10]

/-- EDT-derived node value at node `s`, the GENUINE conditional `U(κ s a)` (same U). -/
def vNode (s a : A2) : ℝ := EDTNodeValue.vNode U κ s a

/-- EDT argmax at node 0 (self) is REFUSE: the severing κ predicts the twin refuses, so the
    matched-pay reward never fires and paying only burns 100. -/
theorem edt_argmax_is_refuse_s0 : vNode 0 1 < vNode 0 0 := by
  simp only [vNode, EDTNodeValue.vNode, U, κ, Function.update_apply]; norm_num

/-- EDT argmax at node 1 (twin) is ALSO REFUSE: κ predicts node 0 refuses, so the matched-pay
    reward never fires; paying at node 1 alone gains nothing (own-cost term is on node 0). -/
theorem edt_argmax_is_refuse_s1 : vNode 1 1 ≤ vNode 1 0 := by
  simp only [vNode, EDTNodeValue.vNode, U, κ, Function.update_apply]; norm_num

/-- **The EDT-derived policy, computed at BOTH nodes** (NOT projected onto a diagonal by
    hand): the EDT-argmax at node 0 is refuse and at node 1 is refuse, so `edtPolicy = (refuse,refuse)`. -/
def edtPolicy : S2 → A2 := fun _ => 0

/-- `edtPolicy` genuinely picks an EDT-node-value maximizer at EVERY node — the spec the
    main theorem uses (`∀ s a, vNode s a ≤ vNode s (edtPolicy s)`). Not hand-fed. -/
theorem edtPolicy_is_edt_argmax : ∀ s a, vNode s a ≤ vNode s (edtPolicy s) := by
  intro s a
  fin_cases s <;> fin_cases a <;>
    simp only [edtPolicy, vNode, EDTNodeValue.vNode, U, κ, Function.update_apply] <;> norm_num

/-- The GLOBAL (UNRESTRICTED) UDT optimum is the matched-pay policy `(pay,pay)`: 9900. -/
def globalOpt : S2 → A2 := fun _ => 1

theorem U_refuse : U edtPolicy = 0 := by simp [U, edtPolicy]
theorem U_pay    : U globalOpt = 9900 := by simp [U, globalOpt]; norm_num

/-- helper: every action in `Fin 2` is refuse or pay. -/
theorem action_cases (x : A2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **`globalOpt` is the UNRESTRICTED maximizer over ALL FOUR policies** — no diagonal
    restriction. Because U is non-separable with the matched-pay reward, the off-diagonal
    `(refuse,pay)` gives 0 (no free lunch), so `(pay,pay)=9900` dominates everything. -/
theorem global_opt_dominates_all :
    ∀ π : S2 → A2, U π ≤ U globalOpt := by
  intro π
  rw [U_pay]
  -- enumerate the four policies via the two action choices
  rcases action_cases (π 0) with h0 | h0 <;> rcases action_cases (π 1) with h1 | h1 <;>
    simp only [U, h0, h1] <;> norm_num

/-- **(II) NEAR-MISS — EDT-conditional argmax DIVERGES from the UNRESTRICTED global UDT
    optimum.** The EDT-derived policy `(refuse,refuse)` (argmax of `vNode` at BOTH nodes,
    via the severing κ) is STRICTLY worse than the genuine optimum `(pay,pay)`:
        U edtPolicy < U globalOpt   (0 < 9900).
    With the SAME U, the correlation-severing κ makes the EDT node-value argmax miss the
    global optimum. So `vNode = U∘κ` is NOT a relabel of the local argmax of U — κ does the work. -/
theorem mugging_edt_misses : U edtPolicy < U globalOpt := by
  rw [U_refuse, U_pay]; norm_num

/-- **The gap = the acausal payoff.** `U globalOpt − U edtPolicy = 9900`, and the severed
    acausal reward κ failed to count is `+10000` (isolated as `U globalOpt − vNode 0 1`:
    the matched-pay reward the EDT self at node 0 dropped, net of the −100 it did count). -/
theorem gap_is_acausal_payoff :
    U globalOpt - U edtPolicy = 9900
    ∧ U globalOpt - vNode 0 1 = 10000 := by
  refine ⟨by rw [U_refuse, U_pay]; norm_num, ?_⟩
  simp only [vNode, EDTNodeValue.vNode, U, κ, globalOpt, Function.update_apply]; norm_num

/-- κ is LOAD-BEARING: with the CORRELATED kernel (twin copies the action,
    `κcorr s a = fun _ => a`), the matched-pay reward FIRES, so the EDT node value through
    the SAME U ranks PAY above refuse, AGREEING with the global optimum. So the divergence
    is caused PRECISELY by κ's severance — κ is not inert. -/
def κcorr : S2 → A2 → (S2 → A2) := fun _ a => fun _ => a

theorem correlated_kappa_agrees :
    EDTNodeValue.vNode U κcorr 0 0 < EDTNodeValue.vNode U κcorr 0 1 := by
  simp [EDTNodeValue.vNode, U, κcorr]; norm_num

/-- **NEAR-MISS (LEAN-CORE form): weaker hypotheses ⇒ the main theorem's conclusion is FALSE.**
    `edt_decoupled_globally_optimal` needed `Separable U p u` (and `Decoupled κ base`).
    On this instance `Separable` FAILS (`not_separable`); dropping it, the theorem's CONCLUSION
        ∀ π, policyValue U π ≤ policyValue U edtPolicy
    is FALSE — `globalOpt` strictly beats `edtPolicy` (here `edtPolicy` genuinely IS the
    EDT-argmax at both nodes, `edtPolicy_is_edt_argmax`). This certifies separability is
    load-bearing (not vacuous) AND that vNode is not a relabel of the local argmax. -/
theorem separability_load_bearing :
    ¬ (∀ π : S2 → A2, EDTNodeValue.policyValue U π ≤ EDTNodeValue.policyValue U edtPolicy) := by
  intro hAll
  have h := hAll globalOpt
  simp only [EDTNodeValue.policyValue] at h
  rw [U_refuse, U_pay] at h
  norm_num at h

end Mugging

/- ============================================================================
   AXIOM AUDIT
   ============================================================================ -/
#print axioms EDTNodeValue.vNode_decoupled_eq
#print axioms EDTNodeValue.vNode_argmax_of_u_argmax
#print axioms EDTNodeValue.edt_decoupled_globally_optimal
#print axioms EDTNodeValue.Decoupled.edt_attains_global
#print axioms EDTNodeValue.Decoupled.vNode_via_kappa
#print axioms EDTNodeValue.Decoupled.edt_ranks_s0
#print axioms EDTNodeValue.Decoupled.edtPolicy_is_edt_argmax
#print axioms EDTNodeValue.Decoupled.global_opt_value
#print axioms EDTNodeValue.Decoupled.all_zero_strictly_worse
#print axioms EDTNodeValue.Mugging.not_separable
#print axioms EDTNodeValue.Mugging.edt_argmax_is_refuse_s0
#print axioms EDTNodeValue.Mugging.edt_argmax_is_refuse_s1
#print axioms EDTNodeValue.Mugging.edtPolicy_is_edt_argmax
#print axioms EDTNodeValue.Mugging.action_cases
#print axioms EDTNodeValue.Mugging.global_opt_dominates_all
#print axioms EDTNodeValue.Mugging.mugging_edt_misses
#print axioms EDTNodeValue.Mugging.gap_is_acausal_payoff
#print axioms EDTNodeValue.Mugging.correlated_kappa_agrees
#print axioms EDTNodeValue.Mugging.separability_load_bearing

end EDTNodeValue
