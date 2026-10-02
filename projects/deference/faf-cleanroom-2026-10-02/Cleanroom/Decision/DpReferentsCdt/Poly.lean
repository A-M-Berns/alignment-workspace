import Cleanroom.Decision.DpReferentsCdt.Structure
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-!
# Tremble polynomials for forcing, reach and the off-`d` weight; the limit-quotient lemma

`dp-calibration` renders `ν_{C^ε}(X)` and `∑_{λ⊨X} μ_{C^ε} r` as polynomials in `ε` (`nuPoly`,
`payPoly`) and takes the tremble limit algebraically (`limitVal`: lowest-order coefficients). The
referent identities of this package factor those polynomials as `trembleW C d a * Q`, so that the
limit is `Q'(0)/Q(0)` — the **limit-quotient lemma** `limitVal_eq_of_factor`. The factors are:

* `leafLawPolyForced C B q a ℓ` — the tremble-polynomial law of `ℓ` under the node policy tied to
  `C^ε` with the single node `q` forced to `a` (`eval_leafLawPolyForced`); `forcedPoly C B q a` and
  `reachPoly C B q` are its sums; `edgePoly`/`edgePayPoly` are the mass and payoff mass of the leaves
  taking the `a`-edge at `q`, and `edgePoly_eq`/`edgePayPoly_eq` are `mass_edge` and
  `condDraw_eq_forced` lifted to polynomial identities (two polynomials agreeing on `[0, 1]` are
  equal: `poly_eq_of_eval_Icc`);
* `offPoly C d B ℓ` — the tremble version of `dp-calibration`'s `offWeight` (the chance weight times
  the draw weights at points other than `d`), and `thetaPoly`/`thetaPayPoly` — CA-12′'s `Θ_{C^ε}`.

Then **Lemma C2-L3** (`refR3_eq_refR2Real_of_structural`, T5(i)): under F3′ structural, Definition
3's disjointness and `ν_C(O_d) > 0`, `refR3 a = refR2Real a` for **every** `a ∈ A_d`, nulled acts
included; and **FA-20′(ii)** (`refR3_eq_refR1State_of_recordsForAll`, T5(ii)): under Definition 7
recording for every procedure, `refR3 a = refR1State a` wherever the latter is defined.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset Polynomial

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Polynomial extension and the limit-quotient lemma -/

section limitQuotient

/-- Two polynomials over a linearly ordered field agreeing on `[0, 1]` are equal.
Source: none: infrastructure
Kind: L -/
theorem poly_eq_of_eval_Icc {p q : Polynomial K}
    (h : ∀ ε : K, 0 ≤ ε → ε ≤ 1 → p.eval ε = q.eval ε) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Icc_infinite (zero_lt_one : (0 : K) < 1))
  intro ε hε
  exact h ε hε.1 hε.2

/-- The coefficient of `w · Q` at the order of `w` is `trailingCoeff w · Q(0)`.
Source: none: infrastructure
Kind: L -/
theorem coeff_mul_natTrailingDegree_left (w Q : Polynomial K) :
    (w * Q).coeff w.natTrailingDegree = w.trailingCoeff * Q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (w.natTrailingDegree, 0)]
  · rfl
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have hi : i < w.natTrailingDegree := by
      rcases Nat.lt_or_ge i w.natTrailingDegree with h | h
      · exact h
      · exfalso; apply hne
        have hi' : i = w.natTrailingDegree := by omega
        have hj : j = 0 := by omega
        rw [hi', hj]
    rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- **The limit-quotient lemma**: if `nuPoly Y = w · Q` and `payPoly Y = w · Q'` with `w ≠ 0` and
`Q(0) > 0`, then the algebraic tremble limit `limitVal Y` is `Q'(0) / Q(0)`.
Source: [[decision-problems-v2]] Lemma 2 proof ("ratios of polynomials in `ε`"); mandate T3
(C2-L3: "the quotient of polynomials in `ε` has positive denominator at `0`")
Kind: P
Fidelity: exact -/
theorem limitVal_eq_of_factor (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω)
    (w Q Q' : Polynomial K) (hN : nuPoly C B Y = w * Q) (hP : payPoly C B Y = w * Q')
    (hw : w ≠ 0) (hQ : 0 < Q.coeff 0) :
    limitVal C B Y = Q'.coeff 0 / Q.coeff 0 := by
  unfold limitVal
  have hQne : Q ≠ 0 := by rintro rfl; simp at hQ
  have hQord : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero hQ.ne')
  have hord : (nuPoly C B Y).natTrailingDegree = w.natTrailingDegree := by
    rw [hN, Polynomial.natTrailingDegree_mul hw hQne, hQord, add_zero]
  rw [hord, hN, hP, coeff_mul_natTrailingDegree_left, coeff_mul_natTrailingDegree_left]
  have hwc : w.trailingCoeff ≠ 0 := mt Polynomial.trailingCoeff_eq_zero.mp hw
  rw [mul_div_mul_left _ _ hwc]

end limitQuotient

/-! ## The forced-law polynomial -/

section forced

variable (C : Proc ι acts K)

/-- The tremble-polynomial law of a leaf under the node policy tied to `C^ε` with the single
node `q` forced to `a`: chance weights are constants, draws at nodes other than `q` are `trembleW`,
the draw at `q` is `δ_a` (no tremble).
Source: [[decision-problems-v2]] §8 (`G_q(C, a)`: "forcing the single instance, all other nodes …
still drawing from `C`"), under Definition 10's trembles; mandate T3 (C2-L3)
Kind: D -/
noncomputable def leafLawPolyForced :
    (B : Tree Ω ι acts K) → (q : B.DecNode) → acts (pt B q) → B.Leaves → Polynomial K
  | .leaf _ _, q, _, _ => q.elim
  | .chance _ β child, ⟨i, q⟩, a, ⟨j, ℓ⟩ =>
      Polynomial.C (β.w j) *
        (if h : j = i then leafLawPolyForced (child i) q a (h ▸ ℓ) else leafLawPoly C (child j) ℓ)
  | .decision _ child, none, a, ⟨b, ℓ⟩ =>
      Polynomial.C ((FinDistr.pure a).w b) * leafLawPoly C (child b) ℓ
  | .decision d child, some ⟨c, q⟩, a, ⟨b, ℓ⟩ =>
      trembleW C d b *
        (if h : b = c then leafLawPolyForced (child c) q a (h ▸ ℓ) else leafLawPoly C (child b) ℓ)

/-- **`eval ε (leafLawPolyForced C B q a ℓ)` is the law of `ℓ` under `(ofProc C^ε)[q ↦ δ_a]`** for
`ε ∈ [0, 1]`.
Source: mandate T3 (C2-L3)
Kind: P
Fidelity: exact -/
theorem eval_leafLawPolyForced (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (a : acts (pt B q)) (ℓ : B.Leaves),
      (leafLawPolyForced C B q a ℓ).eval ε =
        leafLawNode B ((NodePolicy.ofProc (tremble C ε h0 h1) B).update q (FinDistr.pure a)) ℓ
  | .leaf _ _, q, _, _ => q.elim
  | .chance n β child, ⟨i, q⟩, a, ⟨j, ℓ⟩ => by
      simp only [leafLawPolyForced, Polynomial.eval_mul, Polynomial.eval_C, leafLawNode_chance]
      by_cases hij : j = i
      · subst hij
        rw [dif_pos rfl, NodePolicy.update_restrictChance_same, NodePolicy.ofProc_restrictChance]
        exact congrArg _ (eval_leafLawPolyForced ε h0 h1 (child j) q a ℓ)
      · rw [dif_neg hij, NodePolicy.update_restrictChance_ne _ hij, NodePolicy.ofProc_restrictChance,
          leafLawNode_ofProc, eval_leafLawPoly C ε h0 h1]
  | .decision d child, none, a, ⟨b, ℓ⟩ => by
      simp only [leafLawPolyForced, Polynomial.eval_mul, Polynomial.eval_C, leafLawNode_decision,
        NodePolicy.update_self, NodePolicy.update_none_restrictDecision,
        NodePolicy.ofProc_restrictDecision, leafLawNode_ofProc, eval_leafLawPoly C ε h0 h1]
  | .decision d child, some ⟨c, q⟩, a, ⟨b, ℓ⟩ => by
      simp only [leafLawPolyForced, Polynomial.eval_mul, leafLawNode_decision,
        NodePolicy.update_some_none, NodePolicy.ofProc_none, eval_trembleW C d b ε h0 h1]
      by_cases hbc : b = c
      · subst hbc
        rw [dif_pos rfl, NodePolicy.update_some_restrictDecision_same,
          NodePolicy.ofProc_restrictDecision]
        exact congrArg _ (eval_leafLawPolyForced ε h0 h1 (child b) q a ℓ)
      · rw [dif_neg hbc, NodePolicy.update_some_restrictDecision_ne _ hbc,
          NodePolicy.ofProc_restrictDecision, leafLawNode_ofProc, eval_leafLawPoly C ε h0 h1]

variable (B : Tree Ω ι acts K)

/-- `forcedBelow` under the trembles as a polynomial in `ε`.
Source: mandate T3 (C2-L3)
Kind: D -/
noncomputable def forcedPoly (q : B.DecNode) (a : acts (pt B q)) : Polynomial K :=
  ∑ ℓ ∈ leavesBelow B q, leafLawPolyForced C B q a ℓ * Polynomial.C (payoff B ℓ)

/-- `eval ε (forcedPoly C B q a) = forcedBelow B (ofProc C^ε) q a`. Source: mandate T3. Kind: L -/
theorem eval_forcedPoly (q : B.DecNode) (a : acts (pt B q)) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (forcedPoly C B q a).eval ε = forcedBelow B (NodePolicy.ofProc (tremble C ε h0 h1) B) q a := by
  unfold forcedPoly forcedBelow
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_leafLawPolyForced C ε h0 h1]

/-- `R_q` under the trembles as a polynomial in `ε`. Source: mandate T3. Kind: D -/
noncomputable def reachPoly (q : B.DecNode) : Polynomial K :=
  ∑ ℓ ∈ leavesBelow B q, leafLawPoly C B ℓ

/-- `eval ε (reachPoly C B q) = R_q(C^ε)`. Source: mandate T3. Kind: L -/
theorem eval_reachPoly (q : B.DecNode) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (reachPoly C B q).eval ε = reach (tremble C ε h0 h1) B q := by
  unfold reachPoly
  rw [Polynomial.eval_finsetSum, reach_eq_mass_leavesBelow]
  unfold mass
  exact Finset.sum_congr rfl fun ℓ _ => eval_leafLawPoly C ε h0 h1 B ℓ

/-- The tremble-polynomial mass of the leaves taking the `a`-edge at `q`.
Source: [[decision-problems-v2]] Definition 6 (`dp-core-tree`'s `mass_edge`); mandate T3
Kind: D -/
noncomputable def edgePoly (q : B.DecNode) (a : acts (pt B q)) : Polynomial K :=
  ∑ ℓ, if edgeOf B q ℓ = some a then leafLawPoly C B ℓ else 0

/-- The tremble-polynomial payoff mass of the leaves taking the `a`-edge at `q`.
Source: mandate T3
Kind: D -/
noncomputable def edgePayPoly (q : B.DecNode) (a : acts (pt B q)) : Polynomial K :=
  ∑ ℓ, if edgeOf B q ℓ = some a then leafLawPoly C B ℓ * Polynomial.C (payoff B ℓ) else 0

/-- `eval ε (edgePoly)`. Source: none: infrastructure. Kind: L -/
theorem eval_edgePoly (q : B.DecNode) (a : acts (pt B q)) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (edgePoly C B q a).eval ε =
      ∑ ℓ, if edgeOf B q ℓ = some a then leafLaw (tremble C ε h0 h1) B ℓ else 0 := by
  unfold edgePoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : edgeOf B q ℓ = some a
  · rw [if_pos h, if_pos h, eval_leafLawPoly C ε h0 h1]
  · rw [if_neg h, if_neg h, Polynomial.eval_zero]

/-- `eval ε (edgePayPoly)`. Source: none: infrastructure. Kind: L -/
theorem eval_edgePayPoly (q : B.DecNode) (a : acts (pt B q)) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (edgePayPoly C B q a).eval ε =
      ∑ ℓ, if edgeOf B q ℓ = some a then leafLaw (tremble C ε h0 h1) B ℓ * payoff B ℓ else 0 := by
  unfold edgePayPoly
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases h : edgeOf B q ℓ = some a
  · rw [if_pos h, if_pos h, Polynomial.eval_mul, Polynomial.eval_C, eval_leafLawPoly C ε h0 h1]
  · rw [if_neg h, if_neg h, Polynomial.eval_zero]

/-- **`mass_edge` as a polynomial identity**: `edgePoly q a = trembleW (d_q) a · reachPoly q`.
Source: [[decision-problems-v2]] Definition 6 ("draw `a ∼ C(d_q)` afresh and independently")
Kind: P
Fidelity: exact -/
theorem edgePoly_eq (q : B.DecNode) (a : acts (pt B q)) :
    edgePoly C B q a = trembleW C (pt B q) a * reachPoly C B q := by
  apply poly_eq_of_eval_Icc
  intro ε h0 h1
  rw [eval_edgePoly C B q a ε h0 h1, Polynomial.eval_mul, eval_trembleW C _ a ε h0 h1,
    eval_reachPoly C B q ε h0 h1,
    mass_edge (tremble C ε h0 h1) B q a, sum_ite_isSome_eq_reach]

/-- **`condDraw_eq_forced` as a polynomial identity**: `edgePayPoly q a = trembleW (d_q) a ·
forcedPoly q a`.
Source: [[decision-problems-v2]] Appendix B (`dp-local-opt`'s `condDraw_eq_forced`)
Kind: P
Fidelity: exact -/
theorem edgePayPoly_eq (q : B.DecNode) (a : acts (pt B q)) :
    edgePayPoly C B q a = trembleW C (pt B q) a * forcedPoly C B q a := by
  apply poly_eq_of_eval_Icc
  intro ε h0 h1
  rw [eval_edgePayPoly C B q a ε h0 h1, Polynomial.eval_mul, eval_trembleW C _ a ε h0 h1,
    eval_forcedPoly C B q a ε h0 h1, condDraw_eq_forced (tremble C ε h0 h1) B q a]

end forced

/-! ## Lemma C2-L3: `refR3 = refR2Real` at F3′-structural points -/

section c2l3

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The pointwise structural identity for the tremble polynomials (every chance-positive leaf is
positive under the uniform procedure, so F3′ structural decides which `if` fires).
Source: `C2.md` Lemma C2-L3
Kind: P -/
theorem ite_actEv_obs_poly_eq_sum_realFiber {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) (ℓ : B.Leaves) (g : Polynomial K) :
    (if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLawPoly C B ℓ * g else 0) =
      ∑ q ∈ realFiber actEv B d,
        if edgeS B q ℓ = some ⟨d, a⟩ then leafLawPoly C B ℓ * g else 0 := by
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hpos | hzero
  · have hU : 0 < leafLaw (uniformProc (K := K)) B ℓ := leafLaw_uniformProc_pos B ℓ hpos
    have hrec := hS _ uniformProc_fullSupport
    exact ite_eq_sum_of_unique (realFiber actEv B d)
      (fun q => edgeS B q ℓ = some ⟨d, a⟩) (world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d)
      (leafLawPoly C B ℓ * g)
      (fun hc => exists_realFiber_edgeS obs actEv (uniformProc (K := K)) B hrec hdisj hU hc.1 hc.2)
      (fun q hq he => actEv_obs_of_edgeS obs actEv (uniformProc (K := K)) B hrec hq he)
      (fun q₁ h₁ q₂ h₂ e₁ e₂ => realFiber_unique obs actEv (uniformProc (K := K)) B hrec hU h₁ h₂
        (isSome_of_edgeS B q₁ ℓ e₁) (isSome_of_edgeS B q₂ ℓ e₂))
  · have : leafLawPoly C B ℓ = 0 := by
      by_contra hne
      exact absurd ((leafLawPoly_ne_zero_iff C B ℓ).mp hne) (by rw [← hzero]; exact lt_irrefl 0)
    rw [this]; simp

/-- **`nuPoly (a ∧ O_d) = trembleW C d a · ∑_{q ∈ realFiber} reachPoly q`** under F3′ structural
and disjointness.
Source: `C2.md` Lemma C2-L3
Kind: P
Fidelity: exact
Hyps: (a) `ActRecordingStructural`, (a) `ActEvDisjoint` -/
theorem nuPoly_actEv_inter_obs_eq {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) :
    nuPoly C B (actEv d a ∩ obs d) =
      trembleW C d a * ∑ q ∈ realFiber actEv B d, reachPoly C B q := by
  have hL : nuPoly C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d then leafLawPoly C B ℓ * 1 else 0 := by
    unfold nuPoly worldEv
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ite_actEv_obs_poly_eq_sum_realFiber obs actEv C B hS hdisj a ℓ 1),
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpt, -⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  simp only [mul_one, edgeS_eq_some_iff]
  rw [← edgePoly_eq]
  rfl

/-- **`payPoly (a ∧ O_d) = trembleW C d a · ∑_{q ∈ realFiber} forcedPoly q a`** under F3′ structural
and disjointness.
Source: `C2.md` Lemma C2-L3
Kind: P
Fidelity: exact
Hyps: (a) `ActRecordingStructural`, (a) `ActEvDisjoint` -/
theorem payPoly_actEv_inter_obs_eq {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (a : acts d) :
    payPoly C B (actEv d a ∩ obs d) =
      trembleW C d a * ∑ q ∈ realFiber actEv B d,
        if h : pt B q = d then forcedPoly C B q (h ▸ a) else 0 := by
  have hL : payPoly C B (actEv d a ∩ obs d) =
      ∑ ℓ, if world B ℓ ∈ actEv d a ∧ world B ℓ ∈ obs d
        then leafLawPoly C B ℓ * Polynomial.C (payoff B ℓ) else 0 := by
    unfold payPoly worldEv
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp [Finset.mem_inter]
  rw [hL, Finset.sum_congr rfl
      (fun ℓ _ => ite_actEv_obs_poly_eq_sum_realFiber obs actEv C B hS hdisj a ℓ _),
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpt, -⟩ := (mem_realFiber actEv B d q).mp hq
  subst hpt
  simp only [edgeS_eq_some_iff, dif_pos]
  rw [← edgePayPoly_eq]
  rfl

/-- **Lemma C2-L3 / FA-20′(i): `refR3 a = refR2Real a` for every `a ∈ A_d`** at an F3′-structural
point with Definition 3's disjointness and `ν_C(O_d) > 0` — nulled acts included: the tremble's
positive weight at `a` cancels coefficientwise. The denominator `∑_{q ∈ realFiber} R_q(C)` is
positive because it equals `ν_C(O_d)` (`nu_obs_eq_realReach`).
Source: `C2.md` line 48 (Lemma C2-L3); `faithful.md` FA-20′(i) (R2-real = R3 "on every
`a ∈ A_d`"); dp-sl-055; dp-cf-109; mandate T3, T5(i)
Kind: P
Fidelity: exact (the limit taken algebraically, `refR3`'s variant); the positivity hypothesis is
`0 < ν_C(O_d)`, not the mandate's `nuPoly C B (obs d) ≠ 0` — at Told-You-So's `d₁₀` under `C₀`
the latter holds, `refR2Real` is junk `0`, and the identity is false (findings F2)
Hyps: (a) `ActRecordingStructural obs actEv B d`, (a) `ActEvDisjoint actEv d`, (a) `0 < ν_C(O_d)` -/
theorem refR3_eq_refR2Real_of_structural {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (a : acts d) :
    refR3 obs actEv C B d a = refR2Real actEv C B d a := by
  unfold refR3 refR2Real
  have hrec : ActRecording obs actEv C B d := hS.actRecording C
  have hQ0 : (∑ q ∈ realFiber actEv B d, reachPoly C B q).coeff 0 = realReach actEv C B d := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_finsetSum, realReach]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eval_reachPoly C B q 0 le_rfl zero_le_one, tremble_zero]
  have hQ'0 : (∑ q ∈ realFiber actEv B d,
      if h : pt B q = d then forcedPoly C B q (h ▸ a) else 0).coeff 0 =
      realForced actEv C B d a := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_finsetSum, realForced]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rw [eval_forcedPoly C B q _ 0 le_rfl zero_le_one, tremble_zero]
    · simp
  rw [limitVal_eq_of_factor C B _ _ _ _ (nuPoly_actEv_inter_obs_eq obs actEv C B hS hdisj a)
    (payPoly_actEv_inter_obs_eq obs actEv C B hS hdisj a) (trembleW_ne_zero C d a)
    (by rw [hQ0, ← nu_obs_eq_realReach obs actEv C B hrec]; exact hpos), hQ0, hQ'0]

end c2l3

/-! ## The off-`d` weight polynomial and FA-20′(ii): `refR3 = refR1State` under recording for all -/

section theta

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- The tremble-polynomial off-`d` weight: the chance weight times the `trembleW` of every draw at
a point other than `d` (`dp-calibration`'s `offWeight` under `C^ε`).
Source: `calibration.md` CA-12′; mandate T5(ii)
Kind: D -/
noncomputable def offPoly (d : ι) (ℓ : B.Leaves) : Polynomial K :=
  Polynomial.C (chanceWeight B ℓ) *
    (((draws B ℓ).filter fun x => x.1 ≠ d).map fun x => trembleW C x.1 x.2).prod

/-- `eval ε (offPoly C B d ℓ) = offWeight (C^ε) d B ℓ`. Source: mandate T5(ii). Kind: L -/
theorem eval_offPoly (d : ι) (ℓ : B.Leaves) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (offPoly C B d ℓ).eval ε = offWeight (tremble C ε h0 h1) d B ℓ := by
  unfold offPoly offWeight
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_list_prod, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  exact eval_trembleW C x.1 x.2 ε h0 h1

/-- CA-12′'s `Θ_{C^ε}(a, X)` as a polynomial in `ε`. Source: `calibration.md` CA-12′. Kind: D -/
noncomputable def thetaPoly (d : ι) (a : acts d) (X : Finset Ω) : Polynomial K :=
  ∑ q ∈ svFiber obs B d,
    ∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X then offPoly C B d ℓ else 0

/-- CA-12′'s `Θ^r_{C^ε}(a, X)` as a polynomial in `ε`. Source: `calibration.md` CA-12′. Kind: D -/
noncomputable def thetaPayPoly (d : ι) (a : acts d) (X : Finset Ω) : Polynomial K :=
  ∑ q ∈ svFiber obs B d,
    ∑ ℓ, if edgeS B q ℓ = some ⟨d, a⟩ ∧ world B ℓ ∈ X
      then offPoly C B d ℓ * Polynomial.C (payoff B ℓ) else 0

/-- `eval ε (thetaPoly) = theta obs B (C^ε) d a X`. Source: mandate T5(ii). Kind: L -/
theorem eval_thetaPoly (d : ι) (a : acts d) (X : Finset Ω) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (thetaPoly obs C B d a X).eval ε = theta obs B (tremble C ε h0 h1) d a X := by
  unfold thetaPoly theta
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp [eval_offPoly C B d ℓ ε h0 h1]

/-- `eval ε (thetaPayPoly) = thetaPay obs B (C^ε) d a X`. Source: mandate T5(ii). Kind: L -/
theorem eval_thetaPayPoly (d : ι) (a : acts d) (X : Finset Ω) (ε : K) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    (thetaPayPoly obs C B d a X).eval ε = thetaPay obs B (tremble C ε h0 h1) d a X := by
  unfold thetaPayPoly thetaPay
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp [eval_offPoly C B d ℓ ε h0 h1]

/-- **CA-12′ for the trembles, as a polynomial identity**: under recording for every procedure,
`nuPoly (X ∧ a ∧ O_d) = trembleW C d a · thetaPoly a X`.
Source: `calibration.md` CA-12′ (`dp-calibration`'s `nu_factor_of_recordsForAll`), applied to `C^ε`
Kind: P
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d` -/
theorem nuPoly_factor_of_recordsForAll {d : ι} (hall : RecordsForAll obs actEv B d) (a : acts d)
    (X : Finset Ω) :
    nuPoly C B (X ∩ actEv d a ∩ obs d) = trembleW C d a * thetaPoly obs C B d a X := by
  apply poly_eq_of_eval_Icc
  intro ε h0 h1
  rw [eval_nuPoly C B _ ε h0 h1, Polynomial.eval_mul, eval_trembleW C d a ε h0 h1,
    eval_thetaPoly obs C B d a X ε h0 h1]
  exact nu_factor_of_recordsForAll obs actEv B hall _ a X

/-- **CA-12′ for the trembles, payoff side**: `payPoly (X ∧ a ∧ O_d) = trembleW C d a ·
thetaPayPoly a X`.
Source: `calibration.md` CA-12′ (`paySum_factor_of_recordsForAll`), applied to `C^ε`
Kind: P
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d` -/
theorem payPoly_factor_of_recordsForAll {d : ι} (hall : RecordsForAll obs actEv B d)
    (a : acts d) (X : Finset Ω) :
    payPoly C B (X ∩ actEv d a ∩ obs d) = trembleW C d a * thetaPayPoly obs C B d a X := by
  apply poly_eq_of_eval_Icc
  intro ε h0 h1
  rw [eval_payPoly C B _ ε h0 h1, Polynomial.eval_mul, eval_trembleW C d a ε h0 h1,
    eval_thetaPayPoly obs C B d a X ε h0 h1]
  exact paySum_factor_of_recordsForAll obs actEv B hall _ a X

/-- Deviating twice at `d` is deviating once (`dp-local-opt` proves the same fact in a file this
package does not import). Source: none: infrastructure. Kind: L -/
theorem deviate_deviate' (C : Proc ι acts K) (d : ι) (m m' : FinDistr K (acts d)) :
    (C.deviate d m).deviate d m' = C.deviate d m' := by
  unfold Proc.deviate; simp

/-- Under recording for every procedure, `ν_{C[d↦a]}(O_d) = Θ_C(a, ⊤)` and
`paySum_{C[d↦a]}(O_d) = Θ^r_C(a, ⊤)`: the deviation conditioned on `O_d` is CA-12′'s factor at
the label `δ_a`.
Source: `calibration.md` CA-12′; `faithful.md` FA-20′(ii)
Kind: C -/
theorem deviatePure_obs_eq_theta {d : ι} (hall : RecordsForAll obs actEv B d) (a : acts d) :
    nu (C.deviatePure d a) B (obs d) = theta obs B C d a Finset.univ ∧
      paySum (C.deviatePure d a) B (obs d) = thetaPay obs B C d a Finset.univ := by
  have hrec := hall (C.deviatePure d a)
  have ha : 0 < ((C.deviatePure d a) d).w a := by
    simp [Proc.deviatePure]
  have hoff : ∀ d', d' ≠ d → C.deviatePure d a d' = C d' := fun d' hd' => Proc.deviate_ne C _ hd'
  have hw : ((C.deviatePure d a) d).w a = 1 := by simp [Proc.deviatePure]
  constructor
  · have := nu_deviatePure_obs_mul obs actEv (C.deviatePure d a) B hrec ha
    rw [Proc.deviatePure, deviate_deviate' C d, hw, mul_one] at this
    rw [this, ← Finset.univ_inter (actEv d a ∩ obs d), ← Finset.inter_assoc,
      nu_factor_of_recordsForAll obs actEv B hall _ a Finset.univ, hw, one_mul,
      theta_congr_off obs B d hoff a Finset.univ]
  · have := paySum_deviatePure_obs_mul obs actEv (C.deviatePure d a) B hrec ha
    rw [Proc.deviatePure, deviate_deviate' C d, hw, mul_one] at this
    rw [this, ← Finset.univ_inter (actEv d a ∩ obs d), ← Finset.inter_assoc,
      paySum_factor_of_recordsForAll obs actEv B hall _ a Finset.univ, hw, one_mul,
      thetaPay_congr_off obs B d hoff a Finset.univ]

/-- **FA-20′(ii): `refR3 a = refR1State a` under Definition 7 recording for every procedure**,
wherever the deviation's observation is realized (`0 < ν_{C[d↦a]}(O_d)`): deviating all instances
changes nothing on `O_d`-runs but the draw at the unique `d`-node, and the tremble limit of
`Θ^r_{C^ε}(a)/Θ_{C^ε}(a)` is `Θ^r_C(a)/Θ_C(a)` because `Θ_C(a, ⊤) = ν_{C[d↦a]}(O_d) > 0`.
Source: `faithful.md` FA-20′(ii) (R1-state = R3 "on every act"); dp-cf-109; dp-sl-2-061; mandate T5(ii)
Kind: P
Fidelity: exact (the limit taken algebraically)
Hyps: (a) `RecordsForAll obs actEv B d`, (a) `0 < ν_{C[d↦a]}(O_d)` -/
theorem refR3_eq_refR1State_of_recordsForAll {d : ι} (hall : RecordsForAll obs actEv B d)
    (a : acts d) (hpos : 0 < nu (C.deviatePure d a) B (obs d)) :
    refR3 obs actEv C B d a = refR1State obs C B d a := by
  obtain ⟨hν, hp⟩ := deviatePure_obs_eq_theta obs actEv C B hall a
  unfold refR3 refR1State condExp
  rw [hν, hp]
  have hQ0 : (thetaPoly obs C B d a Finset.univ).coeff 0 = theta obs B C d a Finset.univ := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_thetaPoly obs C B d a _ 0 le_rfl zero_le_one,
      tremble_zero]
  have hQ'0 : (thetaPayPoly obs C B d a Finset.univ).coeff 0 =
      thetaPay obs B C d a Finset.univ := by
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_thetaPayPoly obs C B d a _ 0 le_rfl zero_le_one,
      tremble_zero]
  have hN := nuPoly_factor_of_recordsForAll obs actEv C B hall a Finset.univ
  have hP := payPoly_factor_of_recordsForAll obs actEv C B hall a Finset.univ
  rw [Finset.univ_inter] at hN hP
  rw [limitVal_eq_of_factor C B _ _ _ _ hN hP (trembleW_ne_zero C d a)
    (by rw [hQ0, ← hν]; exact hpos), hQ0, hQ'0]

end theta

end Cleanroom.Decision.DpReferentsCdt
