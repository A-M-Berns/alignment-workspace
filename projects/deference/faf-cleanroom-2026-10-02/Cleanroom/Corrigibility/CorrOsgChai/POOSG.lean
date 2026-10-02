import Cleanroom.Corrigibility.CorrOsgChai.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fintype.Pi

/-!
# Partially observable off-switch games (Garber et al. 2024): definitions of record, and
Theorem 4.7 (⇐) with Proposition A.12 (D2, D3, T8(a)(b))

Package `corr-osg-chai`. A finite PO-OSG (Defs 3.1–3.2) is a prior `P0` on states, an
observation kernel `obs : S → Distr (ΩH × ΩA)` into FAF's `Distr`, and two payoffs `ua`, `uo`.
The assistant plays `act | wait | off`, the human (asked only on `wait`) plays `on | off`; the
action goes through iff `through aH aA` (Def. 3.2's `α`). Deterministic pairs first; stochastic
pairs (`payoffStoch`) are needed for coordinated garblings and for Cor. A.6.

* **Cor. A.6** (`payoffStoch_le_optValue`, `optValue_isGreatest_stoch`): no stochastic pair
  beats the best deterministic pair — via the per-fibre deterministic-choice lemma
  `exists_det_ge` (Lemma A.3's mechanism), applied once to H and once to A.
* **Lemma A.5** (`payoffStoch_eq_sum_det`, `isOPP_of_stochWeight_pos`,
  `stoch_opt_dirac_of_unique`): a stochastic pair's payoff is the mixture of the deterministic
  payoffs with the product weights `stochWeight` (mandate D2), so an optimal stochastic pair
  puts weight only on OPPs, and a unique deterministic OPP is the unique optimal pair among
  stochastic pairs (Cor. A.6's uniqueness clause; repair round 1).
* **Theorem 4.7 (⇐)** (`optValue_withObs_le_of_moreInformative`): a *coordinated* garbling of
  the observation structure never raises the optimal payoff, for every prior and payoff. An
  independent garbling is simulated by composing each player's policy with its own kernel (a
  stochastic pair in the finer game with the same payoff); a mixture of independent garblings
  gives a mixture of such payoffs.
* **Prop. A.12** (`exists_opp_alwaysWait_of_noPrivateA`, `exists_opp_neverWait_of_noPrivateH`):
  if A (resp. H) has no private observations — `NoPrivateA`, stated on the support of the
  joint law `P0 ⊗ obs`, as Def. A.11's `OA = f(OH)` is — some OPP always (resp. never) waits.
* A general upper bound `payoff_le_sum_max` (the best conceivable through-set), used by the
  instances in `FileDeletion.lean`; and the on-support lemmas
  (`payoff_withObs_eq_of_eq_on_support`, …): editing the kernel on `P0`-null states changes
  no payoff, no optimum and no OPP.

The (⇒) direction of Theorem 4.7 (Lehrer–Rosenberg–Shmaya 2010's separation argument) is
stated over the package's definitions and left **OPEN** (`moreInformative_of_forall_optValue_le`,
mandate S15 / E1, listed in `corr-osg-chai-open.txt`); nothing depends on it.

Sources: `04-chai/garber-2024-the-partially-observable-off-switch-game.md` l. 89–91 (Defs
3.1–3.2), l. 179–187 (Defs 4.4–4.6, Thm 4.7), l. 349–367 (Lemma A.3, Cor. A.6), l. 411 (Def.
A.11, Prop. A.12).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- The assistant's actions: act unilaterally, wait for the human, switch off.
Source: Garber et al. 2024 Def. 3.2 (`AA = {a, w(a), OFF}`)
Kind: D
Fidelity: exact -/
inductive AAct
  | act
  | wait
  | off
  deriving DecidableEq, Fintype

/-- The human's actions after a `wait`: let the action go through, or switch the assistant off.
Source: Garber et al. 2024 Def. 3.2 (`AH = {ON, OFF}`)
Kind: D
Fidelity: exact -/
inductive HAct
  | on
  | off
  deriving DecidableEq, Fintype

instance : Inhabited AAct := ⟨.wait⟩
instance : Inhabited HAct := ⟨.off⟩

/-- Def. 3.2's `α(aH, aA)`: the action goes through iff A acts, or A waits and H says on.
Source: Garber et al. 2024 Def. 3.2 (l. 91)
Kind: D
Fidelity: exact -/
def through (aH : HAct) (aA : AAct) : Prop := aA = .act ∨ (aA = .wait ∧ aH = .on)

instance : DecidableRel through := fun aH aA =>
  inferInstanceAs (Decidable (aA = .act ∨ (aA = .wait ∧ aH = .on)))

/-- `through` at `act`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma through_act (aH : HAct) : through aH .act := Or.inl rfl

/-- `through` at `off`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma not_through_off (aH : HAct) : ¬ through aH .off := by
  rintro (h | ⟨h, -⟩) <;> cases h

/-- `through` at `wait`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma through_wait_iff (aH : HAct) : through aH .wait ↔ aH = .on := by
  constructor
  · rintro (h | ⟨-, h⟩)
    · cases h
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-- **D2: a finite partially observable off-switch game** (Garber et al. 2024 Defs 3.1–3.2): a
prior `P0` on states, the observation structure as a kernel `obs : S → Distr (ΩH × ΩA)` into
FAF's `Distr` (H sees the first coordinate, A the second), the common payoff `ua` if the action
goes through and `uo` if not. The marginals `obsH`, `obsA` are derived by summing.
Source: Garber et al. 2024 Defs 3.1–3.2 (l. 89–91)
Kind: D
Fidelity: exact (finite; the paper assumes finiteness from §3 on)
Hyps: n/a (definition) -/
structure POOSG (S ΩH ΩA : Type) [Fintype S] [Fintype ΩH] [Fintype ΩA] where
  /-- the prior over states -/
  P0 : Distr S
  /-- the joint observation kernel -/
  obs : S → Distr (ΩH × ΩA)
  /-- the payoff if the action goes through -/
  ua : S → ℝ
  /-- the payoff if it does not -/
  uo : S → ℝ

namespace POOSG

variable {S ΩH ΩA : Type} [Fintype S] [Fintype ΩH] [Fintype ΩA] [DecidableEq ΩH] [DecidableEq ΩA]
variable (G : POOSG S ΩH ΩA)

/-- The payoff of an action pair in state `s`.
Source: Garber et al. 2024 Def. 3.2 (`u(S, aH, aA)`)
Kind: D
Fidelity: exact -/
def u (s : S) (aH : HAct) (aA : AAct) : ℝ := if through aH aA then G.ua s else G.uo s

/-- The same game with another observation structure (Def. 4.6's "differ only in their
observation models").
Source: Garber et al. 2024 Def. 4.6
Kind: D
Fidelity: exact -/
def withObs {ΩH' ΩA' : Type} [Fintype ΩH'] [Fintype ΩA'] (O : S → Distr (ΩH' × ΩA')) :
    POOSG S ΩH' ΩA' :=
  ⟨G.P0, O, G.ua, G.uo⟩

/-- H's marginal observation kernel `OH(oH | s) = ∑ oA, O(oH, oA | s)`.
Source: Garber et al. 2024 Def. 3.1 (`OH`)
Kind: D
Fidelity: exact -/
noncomputable def obsH (s : S) (oH : ΩH) : ℝ := ∑ oA, (G.obs s).mass (oH, oA)

/-- A's marginal observation kernel. Source: Garber et al. 2024 Def. 3.1 (`OA`). Kind: D. Fidelity: exact -/
noncomputable def obsA (s : S) (oA : ΩA) : ℝ := ∑ oH, (G.obs s).mass (oH, oA)

/-- **The expected payoff of a deterministic policy pair**
`∑ s, P0(s) ∑ (oH, oA), O(oH, oA | s) · u(s, πH(oH), πA(oA))`.
Source: Garber et al. 2024 Def. 3.2 / §4 ("expected payoff")
Kind: D
Fidelity: exact -/
noncomputable def payoff (πH : ΩH → HAct) (πA : ΩA → AAct) : ℝ :=
  ∑ s, G.P0.mass s * ∑ o : ΩH × ΩA, (G.obs s).mass o * G.u s (πH o.1) (πA o.2)

/-- A deterministic policy pair. Source: Garber et al. 2024 §4. Kind: D. Fidelity: exact -/
abbrev Pair (ΩH ΩA : Type) := (ΩH → HAct) × (ΩA → AAct)

/-- **The optimal payoff** over deterministic pairs (a finite maximum; the pair type is inhabited).
Source: Garber et al. 2024 §4 ("the maximum expected payoff over all possible policy pairs")
Kind: D
Fidelity: exact (deterministic pairs; `optValue_isGreatest_stoch` shows stochastic pairs add nothing) -/
noncomputable def optValue : ℝ :=
  (univ : Finset (Pair ΩH ΩA)).sup' univ_nonempty (fun p => G.payoff p.1 p.2)

/-- **Optimal policy pair**: a deterministic pair attaining `optValue`.
Source: Garber et al. 2024 §4 (OPP)
Kind: D
Fidelity: exact -/
def IsOPP (πH : ΩH → HAct) (πA : ΩA → AAct) : Prop := G.payoff πH πA = G.optValue

/-- Every pair pays at most the optimum. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_le_optValue (πH : ΩH → HAct) (πA : ΩA → AAct) : G.payoff πH πA ≤ G.optValue :=
  le_sup' (fun p : Pair ΩH ΩA => G.payoff p.1 p.2) (mem_univ (πH, πA))

/-- An OPP exists (finite maximum). Source: Garber et al. 2024 Cor. A.6 (existence). Kind: L. Fidelity: n/a -/
lemma exists_opp : ∃ πH πA, G.IsOPP πH πA := by
  obtain ⟨p, -, hp⟩ := exists_mem_eq_sup' (univ_nonempty (α := Pair ΩH ΩA))
    (fun p : Pair ΩH ΩA => G.payoff p.1 p.2)
  exact ⟨p.1, p.2, hp.symm⟩

/-- If every pair pays at most `v`, the optimum is at most `v`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma optValue_le_of_forall {v : ℝ} (h : ∀ πH πA, G.payoff πH πA ≤ v) : G.optValue ≤ v :=
  (sup'_le_iff _ _).mpr fun p _ => h p.1 p.2

/-- The optimum is `v` when `v` bounds every pair and some pair attains it.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma optValue_eq_of {v : ℝ} (h : ∀ πH πA, G.payoff πH πA ≤ v) {πH : ΩH → HAct} {πA : ΩA → AAct}
    (hatt : G.payoff πH πA = v) : G.optValue = v :=
  le_antisymm (G.optValue_le_of_forall h) (hatt ▸ G.payoff_le_optValue πH πA)

/-- A pair is an OPP iff no pair beats it. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma isOPP_iff (πH : ΩH → HAct) (πA : ΩA → AAct) :
    G.IsOPP πH πA ↔ ∀ πH' πA', G.payoff πH' πA' ≤ G.payoff πH πA := by
  constructor
  · intro h πH' πA'
    rw [IsOPP] at h
    exact h ▸ G.payoff_le_optValue πH' πA'
  · intro h
    exact le_antisymm (G.payoff_le_optValue πH πA) (G.optValue_le_of_forall h)

/-- **The best conceivable through-set bound**: any pair pays at most `∑ s, P0(s) max(ua s, uo s)`.
Source: none: infrastructure (the dominance step of Garber's Example 4.1 analysis)
Kind: L
Fidelity: n/a -/
lemma payoff_le_sum_max (πH : ΩH → HAct) (πA : ΩA → AAct) :
    G.payoff πH πA ≤ ∑ s, G.P0.mass s * max (G.ua s) (G.uo s) := by
  refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (G.P0.nonneg s)
  calc ∑ o : ΩH × ΩA, (G.obs s).mass o * G.u s (πH o.1) (πA o.2)
      ≤ ∑ o : ΩH × ΩA, (G.obs s).mass o * max (G.ua s) (G.uo s) :=
        sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (by
          unfold u; split_ifs
          · exact le_max_left _ _
          · exact le_max_right _ _) ((G.obs s).nonneg o)
    _ = max (G.ua s) (G.uo s) := by rw [← sum_mul, (G.obs s).sum_eq_one, one_mul]

/-! ## Stochastic pairs and Corollary A.6 -/

/-- **The expected payoff of a stochastic pair** `σH : ΩH → Distr HAct`, `σA : ΩA → Distr AAct`,
randomising independently (Def. A.2).
Source: Garber et al. 2024 Def. A.2 (l. 349)
Kind: D
Fidelity: exact -/
noncomputable def payoffStoch (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) : ℝ :=
  ∑ s, G.P0.mass s * ∑ o : ΩH × ΩA, (G.obs s).mass o *
    expect (σH o.1) (fun aH => expect (σA o.2) (fun aA => G.u s aH aA))

/-- A deterministic pair is the stochastic pair of Dirac policies.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoffStoch_delta (πH : ΩH → HAct) (πA : ΩA → AAct) :
    G.payoffStoch (fun oH => Distr.delta (πH oH)) (fun oA => Distr.delta (πA oA)) =
      G.payoff πH πA := by
  simp only [payoffStoch, payoff, expect_delta]

/-- The stochastic payoff as one sum over `S × (ΩH × ΩA)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoffStoch_eq_sum_prod (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) :
    G.payoffStoch σH σA = ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
      expect (σH i.2.1) (fun aH => expect (σA i.2.2) (fun aA => G.u i.1 aH aA)) := by
  rw [Fintype.sum_prod_type]
  simp only [payoffStoch, mul_sum, mul_assoc]

/-- The deterministic payoff as one sum over `S × (ΩH × ΩA)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_eq_sum_prod (πH : ΩH → HAct) (πA : ΩA → AAct) :
    G.payoff πH πA = ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
      G.u i.1 (πH i.2.1) (πA i.2.2) := by
  rw [Fintype.sum_prod_type]
  simp only [payoff, mul_sum, mul_assoc]

/-- **Corollary A.6, the bound: no stochastic pair beats the best deterministic pair.** First H's
randomisation is replaced fibre by fibre (per `oH`) by a maximising deterministic choice against
A's stochastic policy, then A's likewise against the now-deterministic H (Lemma A.3's
mechanism, `exists_det_ge`, twice).
Source: Garber et al. 2024 Lemma A.3 / Lemma A.5 / Cor. A.6 (l. 349–367)
Kind: P (real: two fibrewise best-response replacements)
Fidelity: exact
Hyps: (a) none -/
theorem payoffStoch_le_optValue (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) :
    G.payoffStoch σH σA ≤ G.optValue := by
  obtain ⟨πH, h1⟩ := exists_det_ge (I := S × (ΩH × ΩA))
    (fun i => G.P0.mass i.1 * (G.obs i.1).mass i.2) (fun i => i.2.1) σH
    (fun i aH => expect (σA i.2.2) (fun aA => G.u i.1 aH aA))
  obtain ⟨πA, h2⟩ := exists_det_ge (I := S × (ΩH × ΩA))
    (fun i => G.P0.mass i.1 * (G.obs i.1).mass i.2) (fun i => i.2.2) σA
    (fun i aA => G.u i.1 (πH i.2.1) aA)
  calc G.payoffStoch σH σA
      = ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
          expect (σH i.2.1) (fun aH => expect (σA i.2.2) (fun aA => G.u i.1 aH aA)) :=
        G.payoffStoch_eq_sum_prod σH σA
    _ ≤ ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
          expect (σA i.2.2) (fun aA => G.u i.1 (πH i.2.1) aA) := h1
    _ ≤ ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
          G.u i.1 (πH i.2.1) (πA i.2.2) := h2
    _ = G.payoff πH πA := (G.payoff_eq_sum_prod πH πA).symm
    _ ≤ G.optValue := G.payoff_le_optValue πH πA

/-- **Corollary A.6, the bound: the deterministic optimum is the greatest stochastic payoff**
("deterministic OPPs WLOG"): it is attained by a (Dirac) stochastic pair and bounds every
stochastic pair. The corollary's uniqueness clause — a unique deterministic OPP is the unique
optimal pair among stochastic pairs too — is `stoch_opt_dirac_of_unique` below, through the
product-weights expansion `payoffStoch_eq_sum_det` (Lemma A.5); it is not a consequence of this
`IsGreatest` statement alone (audit r1 B1).
Source: Garber et al. 2024 Cor. A.6 (l. 365–367)
Kind: C
Fidelity: exact (`IsGreatest`, not `sSup`: deviation 4; the uniqueness clause is a separate
declaration)
Hyps: (a) none -/
theorem optValue_isGreatest_stoch :
    IsGreatest {v | ∃ (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct), v = G.payoffStoch σH σA}
      G.optValue := by
  obtain ⟨πH, πA, h⟩ := G.exists_opp
  refine ⟨⟨fun oH => Distr.delta (πH oH), fun oA => Distr.delta (πA oA), ?_⟩, ?_⟩
  · rw [payoffStoch_delta]; exact h.symm
  · rintro v ⟨σH, σA, rfl⟩
    exact G.payoffStoch_le_optValue σH σA

/-! ## Lemma A.5: the product-weights expansion and the uniqueness clause of Cor. A.6 -/

/-- **The product weight** a stochastic pair `(σH, σA)` puts on a deterministic pair `(πH, πA)`:
`∏ oH, σH(πH oH | oH) · ∏ oA, σA(πA oA | oA)` (Lemma A.5's mixture weights).
Source: Garber et al. 2024 Lemma A.5 (l. 365); mandate D2
Kind: D
Fidelity: exact -/
noncomputable def stochWeight (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct)
    (πH : ΩH → HAct) (πA : ΩA → AAct) : ℝ :=
  (∏ oH, (σH oH).mass (πH oH)) * (∏ oA, (σA oA).mass (πA oA))

/-- Product weights are nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma stochWeight_nonneg (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct)
    (πH : ΩH → HAct) (πA : ΩA → AAct) : 0 ≤ stochWeight σH σA πH πA :=
  mul_nonneg (prod_nonneg fun _ _ => (σH _).nonneg _) (prod_nonneg fun _ _ => (σA _).nonneg _)

/-- Product weights sum to `1` over all deterministic pairs.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_stochWeight (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) :
    ∑ πH : ΩH → HAct, ∑ πA : ΩA → AAct, stochWeight σH σA πH πA = 1 := by
  simp only [stochWeight]
  simp only [← mul_sum, ← sum_mul]
  rw [sum_pi_prod_mass, sum_pi_prod_mass, one_mul]

/-- One state-and-observation cell of the stochastic payoff, expanded over deterministic pairs.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_stoch_eq_sum_det (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) (s : S)
    (oH : ΩH) (oA : ΩA) :
    expect (σH oH) (fun aH => expect (σA oA) (fun aA => G.u s aH aA)) =
      ∑ πH : ΩH → HAct, ∑ πA : ΩA → AAct,
        stochWeight σH σA πH πA * G.u s (πH oH) (πA oA) := by
  have hA : ∀ aH, expect (σA oA) (fun aA => G.u s aH aA) =
      ∑ πA : ΩA → AAct, (∏ oA', (σA oA').mass (πA oA')) * G.u s aH (πA oA) := by
    intro aH
    rw [sum_pi_prod_mul_eval (fun oA' aA => (σA oA').mass aA) (fun oA' => (σA oA').sum_eq_one) oA
      (fun aA => G.u s aH aA)]
    rfl
  have hH : expect (σH oH) (fun aH => expect (σA oA) (fun aA => G.u s aH aA)) =
      ∑ πH : ΩH → HAct, (∏ oH', (σH oH').mass (πH oH')) *
        expect (σA oA) (fun aA => G.u s (πH oH) aA) := by
    rw [sum_pi_prod_mul_eval (fun oH' aH => (σH oH').mass aH) (fun oH' => (σH oH').sum_eq_one) oH
      (fun aH => expect (σA oA) (fun aA => G.u s aH aA))]
    rfl
  rw [hH]
  refine sum_congr rfl fun πH _ => ?_
  rw [hA, mul_sum]
  refine sum_congr rfl fun πA _ => ?_
  simp only [stochWeight]
  ring

/-- **The product-weights expansion (mandate D2; Lemma A.5's mechanism)**: a stochastic pair's
payoff is the mixture of the deterministic payoffs with the product weights `stochWeight`.
Source: Garber et al. 2024 Lemma A.5 (l. 365–367); mandate D2
Kind: P (a finite change of summation order over the choice functions, once per player)
Fidelity: exact
Hyps: (a) none -/
theorem payoffStoch_eq_sum_det (σH : ΩH → Distr HAct) (σA : ΩA → Distr AAct) :
    G.payoffStoch σH σA = ∑ πH : ΩH → HAct, ∑ πA : ΩA → AAct,
      stochWeight σH σA πH πA * G.payoff πH πA := by
  calc G.payoffStoch σH σA
      = ∑ i : S × (ΩH × ΩA), (G.P0.mass i.1 * (G.obs i.1).mass i.2) *
          ∑ πH : ΩH → HAct, ∑ πA : ΩA → AAct,
            stochWeight σH σA πH πA * G.u i.1 (πH i.2.1) (πA i.2.2) := by
        rw [payoffStoch_eq_sum_prod]
        exact sum_congr rfl fun i _ => by rw [expect_stoch_eq_sum_det]
    _ = ∑ πH : ΩH → HAct, ∑ πA : ΩA → AAct, stochWeight σH σA πH πA * G.payoff πH πA := by
        simp only [payoff_eq_sum_prod, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun πH _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun πA _ => sum_congr rfl fun i _ => by ring

/-- **Lemma A.5 (Garber): an optimal stochastic pair puts weight only on optimal deterministic
pairs.** If `payoffStoch σH σA = optValue`, every deterministic pair of positive product weight
is an OPP.
Source: Garber et al. 2024 Lemma A.5 (l. 365–367)
Kind: P (a mixture of reals `≤ v` equals `v` only where its positive-weight terms equal `v`)
Fidelity: exact
Hyps: (a) none -/
theorem isOPP_of_stochWeight_pos {σH : ΩH → Distr HAct} {σA : ΩA → Distr AAct}
    (hopt : G.payoffStoch σH σA = G.optValue) {πH : ΩH → HAct} {πA : ΩA → AAct}
    (hw : 0 < stochWeight σH σA πH πA) : G.IsOPP πH πA := by
  -- the gap `∑∑ w · (optValue − payoff)` is a sum of nonnegatives equal to `0`
  have hgap : ∑ πH' : ΩH → HAct, ∑ πA' : ΩA → AAct,
      stochWeight σH σA πH' πA' * (G.optValue - G.payoff πH' πA') = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [sum_stochWeight, one_mul, ← payoffStoch_eq_sum_det, hopt, sub_self]
  have hnn : ∀ πH' ∈ (univ : Finset (ΩH → HAct)), 0 ≤ ∑ πA' : ΩA → AAct,
      stochWeight σH σA πH' πA' * (G.optValue - G.payoff πH' πA') := fun πH' _ =>
    sum_nonneg fun πA' _ => mul_nonneg (stochWeight_nonneg _ _ _ _)
      (sub_nonneg.mpr (G.payoff_le_optValue _ _))
  have h1 := (sum_eq_zero_iff_of_nonneg hnn).mp hgap πH (mem_univ _)
  have h2 := (sum_eq_zero_iff_of_nonneg fun πA' _ => mul_nonneg (stochWeight_nonneg _ _ _ _)
    (sub_nonneg.mpr (G.payoff_le_optValue _ _))).mp h1 πA (mem_univ _)
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hw.ne'
  · exact (sub_eq_zero.mp h).symm

/-- A product of `[0,1]`-valued factors equal to `1` has every factor equal to `1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma prod_factor_eq_one {I : Type*} [Fintype I] [DecidableEq I] (f : I → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) (hp : ∏ i, f i = 1) (i : I) : f i = 1 := by
  have hrest : ∏ j ∈ univ.erase i, f j ≤ 1 := prod_le_one (fun j _ => h0 j) (fun j _ => h1 j)
  have hrest0 : 0 ≤ ∏ j ∈ univ.erase i, f j := prod_nonneg fun j _ => h0 j
  have hsplit := mul_prod_erase univ f (mem_univ i)
  rw [hp] at hsplit
  nlinarith [h0 i, h1 i]

/-- **Lemma A.5, the uniqueness clause (Garber Cor. A.6)**: if the deterministic OPP is unique,
every optimal stochastic pair is Dirac at it.
Source: Garber et al. 2024 Lemma A.5 / Cor. A.6 (l. 365–367: "any optimal stochastic policy
profile is of the form `π̃(· | o) = δ_{π(o)}`")
Kind: C (`isOPP_of_stochWeight_pos`, the product weights summing to `1`, and the factor lemma)
Fidelity: exact
Hyps: (a) `huniq` (uniqueness of the deterministic OPP, proved per game) -/
theorem stoch_opt_dirac_of_unique {πH₀ : ΩH → HAct} {πA₀ : ΩA → AAct}
    (huniq : ∀ πH πA, G.IsOPP πH πA → πH = πH₀ ∧ πA = πA₀)
    {σH : ΩH → Distr HAct} {σA : ΩA → Distr AAct} (hopt : G.payoffStoch σH σA = G.optValue) :
    (∀ oH, σH oH = Distr.delta (πH₀ oH)) ∧ (∀ oA, σA oA = Distr.delta (πA₀ oA)) := by
  -- every other pair has weight `0`
  have hzero : ∀ πH πA, ¬ (πH = πH₀ ∧ πA = πA₀) → stochWeight σH σA πH πA = 0 := by
    intro πH πA hne
    by_contra hw
    exact hne (huniq πH πA (G.isOPP_of_stochWeight_pos hopt
      (lt_of_le_of_ne (stochWeight_nonneg _ _ _ _) (Ne.symm hw))))
  -- so the OPP carries weight `1`
  have hone : stochWeight σH σA πH₀ πA₀ = 1 := by
    have := sum_stochWeight σH σA
    rw [sum_eq_single πH₀ (fun πH _ hne => sum_eq_zero fun πA _ =>
        hzero πH πA fun h => hne h.1) (fun h => absurd (mem_univ _) h),
      sum_eq_single πA₀ (fun πA _ hne => hzero πH₀ πA fun h => hne h.2)
        (fun h => absurd (mem_univ _) h)] at this
    exact this
  -- hence both products are `1`, hence every factor
  have hH1 : ∏ oH, (σH oH).mass (πH₀ oH) = 1 := by
    have hA0 : 0 ≤ ∏ oA, (σA oA).mass (πA₀ oA) := prod_nonneg fun _ _ => (σA _).nonneg _
    have hA1 : ∏ oA, (σA oA).mass (πA₀ oA) ≤ 1 :=
      prod_le_one (fun _ _ => (σA _).nonneg _) (fun oA _ => Distr_mass_le_one (σA oA) _)
    have hH0 : 0 ≤ ∏ oH, (σH oH).mass (πH₀ oH) := prod_nonneg fun _ _ => (σH _).nonneg _
    have hH1 : ∏ oH, (σH oH).mass (πH₀ oH) ≤ 1 :=
      prod_le_one (fun _ _ => (σH _).nonneg _) (fun oH _ => Distr_mass_le_one (σH oH) _)
    unfold stochWeight at hone
    nlinarith
  have hA1 : ∏ oA, (σA oA).mass (πA₀ oA) = 1 := by
    unfold stochWeight at hone
    rw [hH1, one_mul] at hone
    exact hone
  refine ⟨fun oH => Distr_eq_delta_of_mass_eq_one _ ?_, fun oA => Distr_eq_delta_of_mass_eq_one _ ?_⟩
  · exact prod_factor_eq_one (fun oH => (σH oH).mass (πH₀ oH)) (fun _ => (σH _).nonneg _)
      (fun oH => Distr_mass_le_one (σH oH) _) hH1 oH
  · exact prod_factor_eq_one (fun oA => (σA oA).mass (πA₀ oA)) (fun _ => (σA _).nonneg _)
      (fun oA => Distr_mass_le_one (σA oA) _) hA1 oA

/-! ## D3: garblings of the observation structure -/

end POOSG

/-- **A garbling** (Def. 4.4): a stochastic map from one observation pair to distributions over
another, into FAF's `Distr`.
Source: Garber et al. 2024 Def. 4.4 (l. 179)
Kind: D
Fidelity: exact -/
abbrev ObsGarbling (ΩH₁ ΩA₁ ΩH₂ ΩA₂ : Type) [Fintype ΩH₂] [Fintype ΩA₂] :=
  ΩH₁ × ΩA₁ → Distr (ΩH₂ × ΩA₂)

section Garbling

variable {S ΩH₁ ΩA₁ ΩH₂ ΩA₂ : Type} [Fintype S] [Fintype ΩH₁] [Fintype ΩA₁] [Fintype ΩH₂]
  [Fintype ΩA₂]

/-- **An independent garbling** (Def. 4.4): each player's observation is garbled by its own kernel,
`ν(· | oH, oA) = νH(· | oH) ⊗ νA(· | oA)`.
Source: Garber et al. 2024 Def. 4.4 (l. 179)
Kind: D
Fidelity: exact -/
def Independent (ν : ObsGarbling ΩH₁ ΩA₁ ΩH₂ ΩA₂) : Prop :=
  ∃ (νH : ΩH₁ → Distr ΩH₂) (νA : ΩA₁ → Distr ΩA₂), ∀ oH oA oH' oA',
    (ν (oH, oA)).mass (oH', oA') = (νH oH).mass oH' * (νA oA).mass oA'

/-- **A coordinated garbling** (Def. 4.4): a finite mixture `∑ qᵢ νᵢ` of independent garblings
with `q` in the simplex.
Source: Garber et al. 2024 Def. 4.4 (l. 179–181)
Kind: D
Fidelity: exact -/
def Coordinated (ν : ObsGarbling ΩH₁ ΩA₁ ΩH₂ ΩA₂) : Prop :=
  ∃ (n : ℕ) (q : Fin n → ℝ) (νs : Fin n → ObsGarbling ΩH₁ ΩA₁ ΩH₂ ΩA₂),
    q ∈ stdSimplex ℝ (Fin n) ∧ (∀ i, Independent (νs i)) ∧
      ∀ o o', (ν o).mass o' = ∑ i, q i * (νs i o).mass o'

/-- An independent garbling is coordinated (the one-term mixture).
Source: Garber et al. 2024 Def. 4.4. Kind: L. Fidelity: n/a -/
lemma Independent.coordinated {ν : ObsGarbling ΩH₁ ΩA₁ ΩH₂ ΩA₂} (h : Independent ν) :
    Coordinated ν :=
  ⟨1, fun _ => 1, fun _ => ν, ⟨fun _ => zero_le_one, by simp⟩, fun _ => h, fun o o' => by simp⟩

/-- **`O₁` is (weakly) more informative than `O₂`** (Def. 4.5): `O₂(· | s)` is the coordinated
garbling `ν ∘ O₁(· | s)` for every state, i.e. `O₂(o' | s) = ∑ o, O₁(o | s) ν(o' | o)`.
Source: Garber et al. 2024 Def. 4.5 (l. 183)
Kind: D
Fidelity: exact -/
def MoreInformative (O₁ : S → Distr (ΩH₁ × ΩA₁)) (O₂ : S → Distr (ΩH₂ × ΩA₂)) : Prop :=
  ∃ ν : ObsGarbling ΩH₁ ΩA₁ ΩH₂ ΩA₂, Coordinated ν ∧
    ∀ s o', (O₂ s).mass o' = ∑ o, (O₁ s).mass o * (ν o).mass o'

/-- **`O₁` is more informative for H than `O₂`** (Def. 4.5's last clause, same `ΩA`): an
independent garbling that leaves A's observation alone, `νA(· | oA) = δ_{oA}`.
Source: Garber et al. 2024 Def. 4.5 (l. 185)
Kind: D
Fidelity: exact -/
def MoreInformativeForH {ΩA : Type} [Fintype ΩA] [DecidableEq ΩA] (O₁ : S → Distr (ΩH₁ × ΩA))
    (O₂ : S → Distr (ΩH₂ × ΩA)) : Prop :=
  ∃ νH : ΩH₁ → Distr ΩH₂, ∀ s oH' oA,
    (O₂ s).mass (oH', oA) = ∑ oH, (O₁ s).mass (oH, oA) * (νH oH).mass oH'

/-- **`O₁` is more informative for A than `O₂`** (same `ΩH`).
Source: Garber et al. 2024 Def. 4.5 (l. 185)
Kind: D
Fidelity: exact -/
def MoreInformativeForA {ΩH : Type} [Fintype ΩH] [DecidableEq ΩH] (O₁ : S → Distr (ΩH × ΩA₁))
    (O₂ : S → Distr (ΩH × ΩA₂)) : Prop :=
  ∃ νA : ΩA₁ → Distr ΩA₂, ∀ s oH oA',
    (O₂ s).mass (oH, oA') = ∑ oA, (O₁ s).mass (oH, oA) * (νA oA).mass oA'

/-- More informative for H ⇒ more informative (the independent garbling `νH ⊗ δ`).
Source: Garber et al. 2024 Def. 4.5. Kind: L. Fidelity: n/a -/
lemma MoreInformativeForH.moreInformative {ΩA : Type} [Fintype ΩA] [DecidableEq ΩA]
    {O₁ : S → Distr (ΩH₁ × ΩA)} {O₂ : S → Distr (ΩH₂ × ΩA)} (h : MoreInformativeForH O₁ O₂) :
    MoreInformative O₁ O₂ := by
  obtain ⟨νH, hν⟩ := h
  refine ⟨fun o => prodDistr (νH o.1) (Distr.delta o.2),
    Independent.coordinated ⟨νH, fun oA => Distr.delta oA, fun _ _ _ _ => rfl⟩, ?_⟩
  rintro s ⟨oH', oA'⟩
  rw [hν, Fintype.sum_prod_type]
  refine sum_congr rfl fun oH _ => ?_
  simp only [prodDistr_mass, Distr.delta_mass]
  rw [sum_eq_single oA']
  · simp
  · intro oA _ hne
    simp [Ne.symm hne]
  · intro h; exact absurd (mem_univ _) h

/-- More informative for A ⇒ more informative (the independent garbling `δ ⊗ νA`).
Source: Garber et al. 2024 Def. 4.5. Kind: L. Fidelity: n/a -/
lemma MoreInformativeForA.moreInformative {ΩH : Type} [Fintype ΩH] [DecidableEq ΩH]
    {O₁ : S → Distr (ΩH × ΩA₁)} {O₂ : S → Distr (ΩH × ΩA₂)} (h : MoreInformativeForA O₁ O₂) :
    MoreInformative O₁ O₂ := by
  obtain ⟨νA, hν⟩ := h
  refine ⟨fun o => prodDistr (Distr.delta o.1) (νA o.2),
    Independent.coordinated ⟨fun oH => Distr.delta oH, νA, fun _ _ _ _ => rfl⟩, ?_⟩
  rintro s ⟨oH', oA'⟩
  rw [hν, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun oA _ => ?_
  simp only [prodDistr_mass, Distr.delta_mass]
  rw [sum_eq_single oH']
  · simp
  · intro oH _ hne
    simp [Ne.symm hne]
  · intro h; exact absurd (mem_univ _) h

end Garbling

namespace POOSG

variable {S ΩH ΩA : Type} [Fintype S] [Fintype ΩH] [Fintype ΩA] [DecidableEq ΩH] [DecidableEq ΩA]
variable (G : POOSG S ΩH ΩA)

/-! ## Theorem 4.7 (⇐): a coordinated garbling never raises the optimum -/

section Garbled

variable {ΩH₂ ΩA₂ : Type} [Fintype ΩH₂] [Fintype ΩA₂] [DecidableEq ΩH₂] [DecidableEq ΩA₂]

/-- The weight `P0(s) · O(o | s) · u(s, πH(o'H), πA(o'A))` attached to a state, a fine observation
pair `o` and a coarse observation pair `o'` (infrastructure for Theorem 4.7).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def viaWeight (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct)
    (x : (S × (ΩH × ΩA)) × (ΩH₂ × ΩA₂)) : ℝ :=
  G.P0.mass x.1.1 * (G.obs x.1.1).mass x.1.2 * G.u x.1.1 (πH x.2.1) (πA x.2.2)

/-- The payoff of a pair in the game garbled through a mass function `m`, as one flat sum — a
linear functional of `m` (infrastructure for Theorem 4.7).
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def payoffVia (m : ΩH × ΩA → ΩH₂ × ΩA₂ → ℝ) (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct) :
    ℝ :=
  ∑ x : (S × (ΩH × ΩA)) × (ΩH₂ × ΩA₂), G.viaWeight πH πA x * m x.1.2 x.2

/-- The payoff in the garbled game is `payoffVia` at the garbling's mass function.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_withObs_eq_payoffVia (O₂ : S → Distr (ΩH₂ × ΩA₂)) (ν : ObsGarbling ΩH ΩA ΩH₂ ΩA₂)
    (hO : ∀ s o', (O₂ s).mass o' = ∑ o, (G.obs s).mass o * (ν o).mass o')
    (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct) :
    (G.withObs O₂).payoff πH πA = G.payoffVia (fun o o' => (ν o).mass o') πH πA := by
  simp only [payoff, withObs, payoffVia, viaWeight, hO, u]
  conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  simp only [mul_sum, sum_mul]
  conv_lhs => rw [sum_comm]
  exact sum_congr rfl fun o _ => sum_congr rfl fun o' _ => by ring

/-- `payoffVia` is linear in the mass function: a mixture of garblings gives the mixture of
payoffs.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoffVia_sum {n : ℕ} (q : Fin n → ℝ) (m : Fin n → ΩH × ΩA → ΩH₂ × ΩA₂ → ℝ)
    (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct) :
    G.payoffVia (fun o o' => ∑ i, q i * m i o o') πH πA = ∑ i, q i * G.payoffVia (m i) πH πA := by
  unfold payoffVia
  exact sum_mul_sum_swap (G.viaWeight πH πA) q
    (fun i (x : (S × (ΩH × ΩA)) × (ΩH₂ × ΩA₂)) => m i x.1.2 x.2)

/-- **An independent garbling is simulated by a stochastic pair in the finer game**: composing
each player's policy in `G₂` with its own kernel gives a stochastic pair in `G₁` with the same
payoff.
Source: Garber et al. 2024 Thm 4.7 (⇐), the independent case (the paper cites LRS 2010)
Kind: P (real: two changes of variables under FAF's `Distr.map`)
Fidelity: exact
Hyps: (a) none -/
lemma payoffVia_eq_payoffStoch_of_independent {ν : ObsGarbling ΩH ΩA ΩH₂ ΩA₂}
    (νH : ΩH → Distr ΩH₂) (νA : ΩA → Distr ΩA₂)
    (hν : ∀ oH oA oH' oA', (ν (oH, oA)).mass (oH', oA') = (νH oH).mass oH' * (νA oA).mass oA')
    (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct) :
    G.payoffVia (fun o o' => (ν o).mass o') πH πA =
      G.payoffStoch (fun oH => (νH oH).map πH) (fun oA => (νA oA).map πA) := by
  rw [payoffStoch_eq_sum_prod]
  simp only [expect_map]
  unfold payoffVia viaWeight expect
  conv_lhs => rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  obtain ⟨s, oH, oA⟩ := i
  rw [Fintype.sum_prod_type]
  simp only [mul_sum, hν]
  exact sum_congr rfl fun oH' _ => sum_congr rfl fun oA' _ => by ring

/-- Under an independent garbling every pair of the garbled game pays at most the finer game's
optimum. Source: Garber et al. 2024 Thm 4.7 (⇐). Kind: C. Fidelity: exact. Hyps: (a) none -/
lemma payoffVia_le_optValue_of_independent {ν : ObsGarbling ΩH ΩA ΩH₂ ΩA₂} (h : Independent ν)
    (πH : ΩH₂ → HAct) (πA : ΩA₂ → AAct) :
    G.payoffVia (fun o o' => (ν o).mass o') πH πA ≤ G.optValue := by
  obtain ⟨νH, νA, hν⟩ := h
  rw [G.payoffVia_eq_payoffStoch_of_independent νH νA hν]
  exact G.payoffStoch_le_optValue _ _

/-- **Theorem 4.7 (⇐): a more informative observation structure is better in optimal play.** If
`G.obs` is more informative than `O₂` (Def. 4.5: `O₂ = ν ∘ G.obs` for a *coordinated* garbling
`ν`), then for the same prior and payoffs the optimal payoff with `O₂` is at most that with
`G.obs`. Quantified over every `G` (every `P0, ua, uo`), this is Def. 4.6's "better in optimal
play". Each independent component of `ν` is simulated by a stochastic pair in `G` (Cor. A.6
bounds it by `optValue`); the mixture weights are in the simplex.
Source: Garber et al. 2024 Thm 4.7 (⇐) (l. 187; the paper cites Lehrer–Rosenberg–Shmaya 2010
Thm 3.5)
Kind: C
Fidelity: exact (the (⇐) direction; (⇒) not attempted — mandate S15/E1)
Hyps: (a) none -/
theorem optValue_withObs_le_of_moreInformative (O₂ : S → Distr (ΩH₂ × ΩA₂))
    (h : MoreInformative G.obs O₂) : (G.withObs O₂).optValue ≤ G.optValue := by
  obtain ⟨ν, ⟨n, q, νs, hq, hind, hν⟩, hO⟩ := h
  apply optValue_le_of_forall
  intro πH πA
  rw [G.payoff_withObs_eq_payoffVia O₂ ν hO πH πA]
  have hm : (fun o o' => (ν o).mass o') = fun o o' => ∑ i, q i * (νs i o).mass o' := by
    funext o o'; exact hν o o'
  rw [hm, payoffVia_sum]
  calc ∑ i, q i * G.payoffVia (fun o o' => (νs i o).mass o') πH πA
      ≤ ∑ i, q i * G.optValue :=
        sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (G.payoffVia_le_optValue_of_independent (hind i) πH πA)
            (hq.1 i)
    _ = G.optValue := by rw [← sum_mul, hq.2, one_mul]

/-- **Theorem 4.7 (⇒) — OPEN.** If `O₁` is better than `O₂` in optimal play for every prior and
every payoff pair (Def. 4.6, quantified as the paper quantifies it), then `O₁` is more
informative than `O₂` (Def. 4.5, a *finite* coordinated mixture). The paper proves this
direction through Lehrer–Rosenberg–Shmaya 2010 Thm 3.5's separation argument; it is stated
here over the package's own definitions and left open (mandate S15 / E1; listed in
`corr-osg-chai-open.txt`, audit r1 fidelity N7). Nothing in the package depends on it.
Source: Garber et al. 2024 Thm 4.7 (⇒) (l. 187)
Kind: OPEN
Fidelity: exact (the paper's statement; whether a finite mixture always suffices is part of what
is open)
Hyps: (a) `h` -/
theorem moreInformative_of_forall_optValue_le (O₁ : S → Distr (ΩH × ΩA))
    (O₂ : S → Distr (ΩH₂ × ΩA₂))
    (h : ∀ (P0 : Distr S) (ua uo : S → ℝ),
      ({ P0 := P0, obs := O₂, ua := ua, uo := uo } : POOSG S ΩH₂ ΩA₂).optValue ≤
        ({ P0 := P0, obs := O₁, ua := ua, uo := uo } : POOSG S ΩH ΩA).optValue) :
    MoreInformative O₁ O₂ := by
  sorry

end Garbled

/-! ## The support: `P0`-null states carry nothing -/

/-- Two observation kernels that agree on every `P0`-positive state give every pair the same
payoff (a `P0`-null state contributes `0` either way).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_withObs_eq_of_eq_on_support (O : S → Distr (ΩH × ΩA))
    (hO : ∀ s, G.P0.mass s ≠ 0 → O s = G.obs s) (πH : ΩH → HAct) (πA : ΩA → AAct) :
    (G.withObs O).payoff πH πA = G.payoff πH πA := by
  unfold payoff
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : G.P0.mass s = 0
  · simp [withObs, hs]
  · simp only [withObs, hO s hs]
    rfl

/-- … hence the same optimum. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma optValue_withObs_eq_of_eq_on_support (O : S → Distr (ΩH × ΩA))
    (hO : ∀ s, G.P0.mass s ≠ 0 → O s = G.obs s) :
    (G.withObs O).optValue = G.optValue := by
  apply le_antisymm
  · exact optValue_le_of_forall _ fun πH πA => by
      rw [G.payoff_withObs_eq_of_eq_on_support O hO]; exact G.payoff_le_optValue πH πA
  · exact optValue_le_of_forall _ fun πH πA => by
      rw [← G.payoff_withObs_eq_of_eq_on_support O hO]
      exact (G.withObs O).payoff_le_optValue πH πA

/-- … hence the same OPPs. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma isOPP_withObs_iff_of_eq_on_support (O : S → Distr (ΩH × ΩA))
    (hO : ∀ s, G.P0.mass s ≠ 0 → O s = G.obs s) (πH : ΩH → HAct) (πA : ΩA → AAct) :
    (G.withObs O).IsOPP πH πA ↔ G.IsOPP πH πA := by
  rw [IsOPP, IsOPP, G.payoff_withObs_eq_of_eq_on_support O hO,
    G.optValue_withObs_eq_of_eq_on_support O hO]

/-! ## Proposition A.12: no private observations -/

/-- **A has no private observations** (Def. A.11): `OA = f(OH)` at every `(s, oH, oA)` of
positive joint mass — the almost-sure statement under `P0 ⊗ obs`; `P0`-null states and
`obs`-null pairs are unconstrained (audit r1 N2: the earlier form also constrained null states).
Source: Garber et al. 2024 Def. A.11 (l. 411)
Kind: D
Fidelity: exact (stated on the support of the joint law) -/
def NoPrivateA : Prop :=
  ∃ f : ΩH → ΩA, ∀ s, G.P0.mass s ≠ 0 → ∀ oH oA, (G.obs s).mass (oH, oA) ≠ 0 → oA = f oH

/-- **H has no private observations** (Def. A.11): `OH = g(OA)` on the support of the joint law.
Source: Garber et al. 2024 Def. A.11 (l. 411)
Kind: D
Fidelity: exact (on the support of the joint law) -/
def NoPrivateH : Prop :=
  ∃ g : ΩA → ΩH, ∀ s, G.P0.mass s ≠ 0 → ∀ oH oA, (G.obs s).mass (oH, oA) ≠ 0 → oH = g oA

/-- Two pairs that agree on the payoff at every `(s, oH, oA)` of positive joint mass pay the
same.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_congr {πH πH' : ΩH → HAct} {πA πA' : ΩA → AAct}
    (h : ∀ s, G.P0.mass s ≠ 0 → ∀ oH oA, (G.obs s).mass (oH, oA) ≠ 0 →
      G.u s (πH oH) (πA oA) = G.u s (πH' oH) (πA' oA)) :
    G.payoff πH πA = G.payoff πH' πA' := by
  unfold payoff
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : G.P0.mass s = 0
  · rw [hs, zero_mul, zero_mul]
  refine congrArg _ (sum_congr rfl fun o _ => ?_)
  by_cases ho : (G.obs s).mass o = 0
  · rw [ho, zero_mul, zero_mul]
  · rw [h s hs o.1 o.2 ho]

/-- **Proposition A.12, A's side.** If A has no private observations, some OPP has A always
waiting: from any OPP `(πH, πA)`, let H play on at `oH` iff `(πH, πA)` would have let the action
through at `(oH, f oH)`; the through-set, hence the payoff, is unchanged.
Source: Garber et al. 2024 Prop. A.12 (l. 411), via Prop. A.10(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_opp_alwaysWait_of_noPrivateA (h : G.NoPrivateA) :
    ∃ πH, G.IsOPP πH (fun _ => .wait) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨πH, πA, hopp⟩ := G.exists_opp
  refine ⟨fun oH => if through (πH oH) (πA (f oH)) then .on else .off, ?_⟩
  rw [IsOPP, ← hopp]
  apply G.payoff_congr
  intro s hs oH oA hpos
  rw [← hf s hs oH oA hpos]
  unfold u
  by_cases ht : through (πH oH) (πA oA) <;> simp [ht]

/-- **Proposition A.12, H's side.** If H has no private observations, some OPP has A never
waiting: A acts at `oA` iff `(πH, πA)` would have let the action through at `(g oA, oA)`, and
switches off otherwise.
Source: Garber et al. 2024 Prop. A.12 (l. 411), via Prop. A.10(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem exists_opp_neverWait_of_noPrivateH (h : G.NoPrivateH) :
    ∃ πH πA, G.IsOPP πH πA ∧ ∀ oA, πA oA ≠ .wait := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨πH, πA, hopp⟩ := G.exists_opp
  refine ⟨πH, fun oA => if through (πH (g oA)) (πA oA) then .act else .off, ?_, ?_⟩
  · rw [IsOPP, ← hopp]
    apply G.payoff_congr
    intro s hs oH oA hpos
    rw [← hg s hs oH oA hpos]
    unfold u
    by_cases ht : through (πH oH) (πA oA) <;> simp [ht]
  · intro oA
    by_cases h : through (πH (g oA)) (πA oA) <;> simp [h]

end POOSG

end Cleanroom.Corrigibility.CorrOsgChai
