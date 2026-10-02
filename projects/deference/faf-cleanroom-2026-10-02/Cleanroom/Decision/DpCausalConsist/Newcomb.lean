import Cleanroom.Found.DpCoreTree.Seed
import Cleanroom.Found.DpCoreTree.SeedMax
import Cleanroom.Decision.DpCausalConsist.PR

/-!
# `dp-causal-consist`: Definitions 6/6′ on opaque Newcomb — marginals agree, joints differ; the
verdict rows (T7(a), T7(b)); the shared seed breaks Lemma 3's conclusion (T4(c))

On `opaqueNewcomb p L S` (a predictor `d`-node samples `C(d)`, the box is filled per the sample
with probability `p`, then the live `d`-node is queried; worlds `(fill, act)`) with
`C(d) = (q, 1 − q)`:

* **T7(a)** — `ν(fill) = ν'(fill)` and `V_B(C) = V'_B(C)` for every label (`opaque_fill_marginal`,
  `opaque_value_eq`: the fill marginal reads only the label under both semantics), while the joints
  differ: `ν(fill ∧ two) = (1−q)(qp + (1−q)(1−p))` and `ν'(fill ∧ two) = (1−q)(1−p)`, unequal for
  `p ≠ ½`, `q ∉ {0, 1}` (`opaque_joint_ne`).
* **T4(c)** — under 6 the fill is independent of the live act (`opaque_six_indep`); under 6′ it is
  not: `ν'(fill ∧ two) · ν'(⊤) ≠ ν'(fill) · ν'(two)` for `p ≠ ½`, `q ∉ {0, 1}`
  (`opaque_seed_not_indep`) — the failure of Lemma 3's conclusion under the shared seed.
* **T7(b)** — under 6 at the strictly calibrated state `calibratedState C B ⊤`,
  `V(two) − V(one) = S` (`opaque_six_V_gap`: the fill is independent of the act, so the act
  conditionals differ by the two-box bonus); under 6′ at the calibrated-under-6′ state,
  `V'(one) − V'(two) = (2p − 1)L − S` (`opaque_seed_V_gap`), so the evidential renderings one-box
  iff `(2p − 1)L > S`.

The 6′ objects are `dp-core-tree`'s `nu'`, `value'`, `leafLaw'`; `paySum'` and `condExp'` are the
6′ twins of `dp-calibration`'s `paySum`/`condExp`, defined here (the calibrated-under-6′ state at
`O = ⊤` is the state with `P = ν'`, `V = condExp'`; only its two components are needed, so the
`State` structure is not rebuilt). Every 6′ quantity is reduced to a mixture of deterministic
procedures by `nu'_deviate_sum`/`value'_deviate_sum` and `nu'_ofFun`/`value'_ofFun`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

section seedTwins

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- `paySum'`: the 6′ payoff mass of an event, `∑_{λ(ℓ) ⊨ X} μ'(ℓ) r(ℓ)`.
Source: [[decision-problems-v2]] Definition 8 clause 2 with `μ'` (Definition 6′) in place of `μ`
Kind: D -/
def paySum' (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) : ℚ :=
  ∑ ℓ ∈ worldEv B X, leafLaw' C B ℓ * payoff B ℓ

/-- `condExp'`: `𝔼_{μ'}[r | λ ⊨ X] = paySum'(X) / ν'(X)` — the desirability the calibrated-under-6′
state at `O = ⊤` assigns to `X` (junk `0` at `ν'(X) = 0`, as `condExp`).
Source: [[decision-problems-v2]] Definition 8 clause 2 under Definition 6′; mandate T7(b)
("the calibrated-under-6′ state")
Kind: D -/
def condExp' (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) : ℚ :=
  paySum' C B X / nu' C B X

end seedTwins

section newcomb

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-- `C[d ↦ a]` on a one-point `Act2` tree is the deterministic procedure playing `a`.
Source: none: infrastructure
Kind: L -/
theorem deviatePure_unit_act2_eq_ofFun (C : Proc Unit (fun _ => Act2) ℚ) (act : Act2) :
    C.deviatePure () act = Proc.ofFun (fun _ => act) := by
  funext d; cases d; simp [Proc.deviatePure, Proc.deviate, Proc.ofFun]

/-- `ν'` on a one-point `Act2` tree is the label-mixture of the deterministic laws.
Source: `dp-core-tree` SE-1 (`nu'_deviate_sum`, `nu'_ofFun`)
Kind: L -/
theorem nu'_unit_act2 (C : Proc Unit (fun _ => Act2) ℚ) (B : Tree OpaqueW Unit (fun _ => Act2) ℚ)
    (X : Finset OpaqueW) :
    nu' C B X = ∑ s : Act2, (C ()).w s * nu (Proc.ofFun (fun _ => s)) B X := by
  rw [nu'_deviate_sum C B () X]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [deviatePure_unit_act2_eq_ofFun, nu'_ofFun]

/-- `V'` on a one-point `Act2` tree is the label-mixture of the deterministic values.
Source: `dp-core-tree` SE-1 (`value'_deviate_sum`, `value'_ofFun`)
Kind: L -/
theorem value'_unit_act2 (C : Proc Unit (fun _ => Act2) ℚ)
    (B : Tree OpaqueW Unit (fun _ => Act2) ℚ) :
    value' C B = ∑ s : Act2, (C ()).w s * value (Proc.ofFun (fun _ => s)) B := by
  rw [value'_deviate_sum C B ()]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [deviatePure_unit_act2_eq_ofFun, value'_ofFun]

/-- `paySum'` on a one-point `Act2` tree is the label-mixture of the deterministic `paySum`s.
Source: `dp-core-tree` SE-1 (`leafLaw'_deviate_sum`, `leafLaw'_ofFun`)
Kind: L -/
theorem paySum'_unit_act2 (C : Proc Unit (fun _ => Act2) ℚ)
    (B : Tree OpaqueW Unit (fun _ => Act2) ℚ) (X : Finset OpaqueW) :
    paySum' C B X = ∑ s : Act2, (C ()).w s * paySum (Proc.ofFun (fun _ => s)) B X := by
  unfold paySum' paySum
  have hℓ : ∀ ℓ, leafLaw' C B ℓ = ∑ s : Act2, (C ()).w s * leafLaw (Proc.ofFun (fun _ => s)) B ℓ := by
    intro ℓ
    rw [leafLaw'_deviate_sum C B () ℓ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [deviatePure_unit_act2_eq_ofFun, leafLaw'_ofFun]
  simp_rw [hℓ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  ring

/-- `paySum` on opaque Newcomb as an eight-term sum. Source: none: infrastructure. Kind: L -/
theorem opaqueNewcomb_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset OpaqueW) :
    paySum C (opaqueNewcomb p h0 h1 L S) X =
      ∑ s : Act2, ∑ i : Fin 2, ∑ l : Act2,
        if (opaqueFill s i, l) ∈ X then
          (C ()).w s * ((FinDistr.coin p h0 h1).w i * (C ()).w l)
            * opaquePay L S (opaqueFill s i, l) else 0 := by
  rw [paySum_eq_sum_ite]
  unfold opaqueNewcomb
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf, mul_one]
  rfl

/-- The two-box event `{act = two}`. Source: mandate T7. Kind: D -/
def twoEv : Finset OpaqueW := opaqueActEv () Act2.b

/-- The one-box event `{act = one}`. Source: mandate T7. Kind: D -/
def oneEv : Finset OpaqueW := opaqueActEv () Act2.a

variable (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-! ### T7(a): the fill marginal and the value agree; the joints differ -/

/-- **The fill marginal is the same under 6 and 6′**: `ν(fill) = ν'(fill) = qp + (1−q)(1−p)`.
Source: dp-core-2-022 ("for a single coordinate read from one node's draw, its marginal under 6′
equals its marginal under 6"); mandate T7(a)
Kind: N+
Fidelity: exact (closed form in `p, q`) -/
theorem opaque_fill_marginal :
    nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) fillEv = q * p + (1 - q) * (1 - p) ∧
    nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) fillEv = q * p + (1 - q) * (1 - p) := by
  constructor
  · rw [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, fillEv, opaqueFill, FinDistr.coin, procQ]
    all_goals ring
  · rw [nu'_unit_act2]
    simp only [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, fillEv, opaqueFill, FinDistr.coin, procQ, Proc.ofFun]
    all_goals ring

/-- **`V_B(C) = V'_B(C)` on opaque Newcomb** for every label: `qpL + (1−q)(1−p)L + (1−q)S`.
Source: dp-core-2-022; mandate T7(a) ("`value C B = value' C B`")
Kind: N+
Fidelity: exact -/
theorem opaque_value_eq :
    value (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S)
      = q * p * L + (1 - q) * (1 - p) * L + (1 - q) * S ∧
    value' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S)
      = q * p * L + (1 - q) * (1 - p) * L + (1 - q) * S := by
  constructor
  · rw [opaqueNewcomb_value]
    simp [Act2.sum_univ, Fin.sum_univ_two, opaqueFill, opaquePay, FinDistr.coin, procQ]
    all_goals ring
  · rw [value'_unit_act2]
    simp only [opaqueNewcomb_value]
    simp [Act2.sum_univ, Fin.sum_univ_two, opaqueFill, opaquePay, FinDistr.coin, procQ, Proc.ofFun]
    all_goals ring

/-- The joints: `ν(fill ∧ two) = (1−q)(qp + (1−q)(1−p))`, `ν'(fill ∧ two) = (1−q)(1−p)`.
Source: mandate T7(a) ("`nu (fill ∩ two) ≠ nu' (fill ∩ two)` … exact polynomials in `p, q`")
Kind: N+ -/
theorem opaque_joint :
    nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv)
      = (1 - q) * (q * p + (1 - q) * (1 - p)) ∧
    nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv) = (1 - q) * (1 - p) := by
  constructor
  · rw [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, fillEv, twoEv, opaqueActEv, opaqueFill, FinDistr.coin,
      procQ]
    all_goals ring
  · rw [nu'_unit_act2]
    simp only [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, fillEv, twoEv, opaqueActEv, opaqueFill, FinDistr.coin,
      procQ, Proc.ofFun]
    all_goals ring

/-- **The joints differ** for `p ≠ ½` and a mixed label: `ν(fill ∧ two) − ν'(fill ∧ two)
= q(1−q)(2p − 1) ≠ 0`.
Source: dp-core-2-022 ("marginals agree, joints differ"); mandate T7(a)
Kind: N+
Hyps: (a) `p ≠ 1/2`; (a) `0 < q < 1` -/
theorem opaque_joint_ne (hp : p ≠ 1/2) (hq0 : 0 < q) (hq1 : q < 1) :
    nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv)
      ≠ nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv) := by
  rw [(opaque_joint p h0 h1 L S q q0 q1).1, (opaque_joint p h0 h1 L S q q0 q1).2]
  intro h
  have hq : q ≠ 0 := hq0.ne'
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have h2 : (2 * p - 1) ≠ 0 := by
    intro h2; apply hp; linarith
  have : (1 - q) * q * (2 * p - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hq' h4
    · exact hq h4
  · exact h2 h3

/-! ### T4(c): the shared seed breaks Lemma 3's conclusion -/

/-- **Under Definition 6 the fill is independent of the live act** at every label:
`ν(fill ∧ two) · ν(⊤) = ν(fill) · ν(two)`.
Source: mandate T4(c) ("while under 6 (`nu`) it is")
Kind: N+ -/
theorem opaque_six_indep :
    nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv)
        * nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) Finset.univ
      = nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) fillEv
        * nu (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) twoEv := by
  rw [(opaque_joint p h0 h1 L S q q0 q1).1, (opaque_fill_marginal p h0 h1 L S q q0 q1).1, nu_univ,
    opaqueNewcomb_nu]
  simp [Act2.sum_univ, Fin.sum_univ_two, twoEv, opaqueActEv, opaqueFill, FinDistr.coin, procQ]
  ring

/-- `ν'(two) = 1 − q` and `ν'(⊤) = 1`. Source: none: infrastructure. Kind: L -/
theorem opaque_seed_two_univ :
    nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) twoEv = 1 - q ∧
    nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) Finset.univ = 1 := by
  constructor <;>
  · rw [nu'_unit_act2]
    simp only [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, twoEv, opaqueActEv, opaqueFill, FinDistr.coin, procQ,
      Proc.ofFun]
    all_goals ring

/-- **Under Definition 6′ the fill is not independent of the live act** (the shared seed):
`ν'(fill ∧ two) · ν'(⊤) − ν'(fill) · ν'(two) = q(1−q)(1 − 2p) ≠ 0` for `p ≠ ½`, `0 < q < 1` —
Lemma 3's conclusion (`m ⊥ ⟨V₀⟩`) fails under 6′ although the tree and label are unchanged.
Source: [[learning-cdt-renderings]] Corollary 3.1(c) ("under 6′ … the Newcomb correlation");
mandate T4(c) ("`nu' (fill ∩ two) · nu' univ ≠ nu' fill · nu' two` for `p ≠ ½`")
Kind: N+
Fidelity: exact (stated at the calibrated-under-6′ law `ν'` at `O = ⊤`; the tree is not
Definition-7 recorded, finding F3, so this is the independence *claim* failing, not Lemma 3's
hypotheses holding)
Hyps: (a) `p ≠ 1/2`; (a) `0 < q < 1` -/
theorem opaque_seed_not_indep (hp : p ≠ 1/2) (hq0 : 0 < q) (hq1 : q < 1) :
    nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ twoEv)
        * nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) Finset.univ
      ≠ nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) fillEv
        * nu' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) twoEv := by
  rw [(opaque_joint p h0 h1 L S q q0 q1).2, (opaque_fill_marginal p h0 h1 L S q q0 q1).2,
    (opaque_seed_two_univ p h0 h1 L S q q0 q1).1, (opaque_seed_two_univ p h0 h1 L S q q0 q1).2]
  intro h
  have hq : q ≠ 0 := hq0.ne'
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have h2 : (1 - 2 * p) ≠ 0 := by
    intro h2; apply hp; linarith
  have : (1 - q) * q * (1 - 2 * p) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hq' h4
    · exact hq h4
  · exact h2 h3

/-! ### T7(b): the verdict rows -/

/-- The strictly calibrated state of opaque Newcomb at label `q` and `O = ⊤` (Definition 6).
Source: [[decision-problems-v2]] Definition 8; mandate T7(b)
Kind: D -/
def opaqueState : State OpaqueW ℚ :=
  calibratedState (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) Finset.univ (nu_univ_pos _ _)

/-- **Under Definition 6, `V(two) − V(one) = S`** at the strictly calibrated state, for every `p`
and every mixed label: the fill is independent of the act, so the act-conditionals differ by the
two-box bonus alone (the S9/S25 duplicate of `sl-workflow`).
Source: [[learning-cdt-renderings]] Corollary 3.1(c) context; `sl-workflow` S9/S25; mandate T7(b)
Kind: P
Fidelity: exact (at a mixed label; at `q ∈ {0, 1}` one conditional is junk)
Hyps: (a) `0 < q < 1` -/
theorem opaque_six_V_gap (hq0 : 0 < q) (hq1 : q < 1) :
    (opaqueState p h0 h1 L S q q0 q1).V twoEv - (opaqueState p h0 h1 L S q q0 q1).V oneEv = S := by
  have hq : q ≠ 0 := hq0.ne'
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  simp only [opaqueState, calibratedState_V, Finset.inter_univ]
  rw [opaqueNewcomb_paySum, opaqueNewcomb_paySum, opaqueNewcomb_nu, opaqueNewcomb_nu]
  simp [Act2.sum_univ, Fin.sum_univ_two, twoEv, oneEv, opaqueActEv, opaqueFill, opaquePay,
    FinDistr.coin, procQ]
  field_simp
  ring

/-- **Under Definition 6′, `V'(one) − V'(two) = (2p − 1)L − S`** on the calibrated-under-6′
components `ν'`, `condExp' = paySum'/ν'` (no `State` structure is rebuilt for 6′):
the shared seed makes the fill track the live act, so the evidential renderings one-box iff
`(2p − 1)L > S`.
Source: [[learning-cdt-renderings]] Corollary 3.1(c) context; mandate T7(b) ("`V'(one) − V'(two)
= (2p−1)L − S`")
Kind: P
Fidelity: variant: stated on the two components `ν'`, `condExp'` at `O = ⊤` rather than on a
`State` (audit r2 fid N9a / adv N8); at a mixed label
Hyps: (a) `0 < q < 1` -/
theorem opaque_seed_V_gap (hq0 : 0 < q) (hq1 : q < 1) :
    condExp' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) oneEv
      - condExp' (procQ q q0 q1) (opaqueNewcomb p h0 h1 L S) twoEv = (2 * p - 1) * L - S := by
  have hq : q ≠ 0 := hq0.ne'
  have hq' : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  unfold condExp'
  rw [paySum'_unit_act2, paySum'_unit_act2, nu'_unit_act2, nu'_unit_act2]
  simp only [opaqueNewcomb_paySum, opaqueNewcomb_nu]
  simp [Act2.sum_univ, Fin.sum_univ_two, twoEv, oneEv, opaqueActEv, opaqueFill, opaquePay,
    FinDistr.coin, procQ, Proc.ofFun]
  field_simp
  ring

end newcomb

end Cleanroom.Decision.DpCausalConsist
