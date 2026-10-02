import Cleanroom.Decision.DpSmokingLesion.Prop13

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T5, T6: Corollary 12′'s consequence, Rosa's population, Proposition 12 and its vacuity

[[dp-smoking-lesion-mandate]] T5 and T6, on `dp-core-tree`'s tickle tree (`tickle`, points
`Bool` = the lesion value, `O_{d_ℓ} = {ℓ}`, label `q_ℓ = C(d_ℓ)(smoke)`).

* **T5(a) the sign law** (`tickle_sign_law`): with `γ₁ > γ₀` and `ρ ∈ (0,1)`, the
  cross-multiplied population correlation is positive iff `q₁ > q₀` (from `tickle_identity`);
  `q₁ = q₀ ⇒ 0` is `dp-core-tree`'s `tickle_identity_of_eq` (cited).
* **T5(b) calibrated EDT populations** (`tickle_smokes_by_alpha`, `tickle_no_interior_approved`,
  `tickle_edtProc_smoke_smoke`): at a strictly calibrated state at `d_ℓ` with both acts possible,
  `V(smoke) − V(refrain) = α` — so no interior label is `T_EDT`-approved at a positive-mass point,
  and Definition 17's `EDT` procedure read off strict states with both acts possible is
  `(δ_smoke, δ_smoke)`, whose population correlation is `0`. **Rosa** (`tickleTyped`,
  `rosa_edtProc_split`): with lesion-dependent desirabilities `α₁ > 0 > α₀`, the `EDT` procedure
  is `(δ_smoke, δ_refrain)`, `q₁ − q₀ = 1`, and the correlation is `(γ₁ − γ₀)ρ(1 − ρ) > 0` — the
  population correlation is the procedure's type-difference.
* **T6(a) flat act-conditionals at each tickle point** (`tickle_flat_at_point`,
  `tickle_not_S2_strict`): for every procedure, `ν(k ∧ m ∧ O_ℓ)·ν(m' ∧ O_ℓ) = ν(k ∧ m' ∧ O_ℓ)·ν(m ∧ O_ℓ)`,
  hence (S2) fails at every strict (and masked, limit, SSC) state of either point, while the
  population correlation can be positive (E1-tickle numbers, `tickle_e1_instance`: population
  `7/12 > ¼`, `P_{s_{d₁}}(k ∣ m) = ¾`, `P_{s_{d₀}}(k ∣ m) = ¼`).
* **T6(b) the vacuity finding** (`tickle_recordsFor`, `tickle_refrain_refrain_approved`,
  `tickle_strict_not_masked`): the tickle tree records at both points for every procedure, so at
  the strict grade `T_EDT` approves **every** deterministic procedure, refrain–refrain included
  (`A_d^+ = {C(d)}`); the non-vacuous "smokes by `α`" is (a) at an interior label or at an
  interior self-model (masked, `tickle_masked_smokes_by_alpha`); rider (i): a deterministic
  procedure's strictly calibrated self-certain state is *not* masked-calibrated (LF), so
  Proposition 12's "masked-calibrated instantiations exist for any `C`" is true with the state
  at an interior self-model — a different state.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section tickle

variable (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁) (g11 : γ₁ ≤ 1)
  (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α β : ℚ)

local notation "T" => tickle ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β

/-- Membership in `tickleObs`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_tickleObs (ℓ : Bool) (w : TickleW) : w ∈ tickleObs ℓ ↔ w.1 = ℓ := by
  simp [tickleObs]

/-- Membership in `tickleActEv`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_tickleActEv (d m : Bool) (w : TickleW) : w ∈ tickleActEv d m ↔ w.2.1 = m := by
  simp [tickleActEv]

/-- `tickleActEv d m = evM m`. Source: none: infrastructure. Kind: L -/
theorem tickleActEv_eq (d m : Bool) : tickleActEv d m = evM m := by
  ext w; simp [evM]

/-- A sum over the leaves of the tickle tree. Source: none: infrastructure. Kind: L -/
theorem tickle_sum (f : (T).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) := by
  simp only [tickleLeaf]
  unfold tickle at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The world at a tickle leaf. Source: none: infrastructure. Kind: L -/
theorem tickle_world (i : Fin 2) (m : Bool) (j : Fin 2) :
    world T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) = (decide (i = 0), m, decide (j = 0)) :=
  rfl

/-- `paySum` on the tickle tree as an explicit eight-term sum, for any procedure.
Source: none: infrastructure. Kind: L -/
theorem tickle_paySum (C : Proc Bool (fun _ => Bool) ℚ) (X : Finset TickleW) :
    paySum C T X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then
          leafLaw C T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) *
            ticklePay α β (decide (i = 0), m, decide (j = 0)) else 0 := by
  rw [paySum_eq_sum_ite, tickle_sum]
  rfl

/-- The eight leaf masses of the tickle tree under any procedure:
`μ(ℓ, m, k) = P(ℓ) · C(d_ℓ)(m) · P(k ∣ ℓ)` (`dp-core-tree`'s `tickle_leafLaw` for `procTickle`,
restated for an arbitrary procedure on the points `Bool`).
Source: dp-sl-013; Definition 6
Kind: L -/
theorem tickle_leafLaw' (C : Proc Bool (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) =
      (if i = 0 then ρ else 1 - ρ) * (C (decide (i = 0))).w m *
        (if i = 0 then (if j = 0 then γ₁ else 1 - γ₁) else (if j = 0 then γ₀ else 1 - γ₀)) := by
  unfold tickleLeaf tickle
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.coin, tickleGamma]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- `ν` on the tickle tree for any procedure. Source: none: infrastructure. Kind: L -/
theorem tickle_nu' (C : Proc Bool (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C T X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then
          leafLaw C T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) else 0 := by
  rw [nu_eq_sum, tickle_sum]
  rfl

variable (C : Proc Bool (fun _ => Bool) ℚ)

/-- The lesion rate at point `ℓ`: `ρ` at `d₁`, `1 − ρ` at `d₀`. Source: none: infrastructure. Kind: D -/
def lesionRate (ℓ : Bool) : ℚ := if ℓ then ρ else 1 - ρ

/-- **The point-local masses on the tickle tree** for any procedure: `ν(O_ℓ) = ρ_ℓ`,
`ν(m ∧ O_ℓ) = ρ_ℓ · C(d_ℓ)(m)`, `ν(k ∧ m ∧ O_ℓ) = ρ_ℓ · C(d_ℓ)(m) · γ_ℓ`, and the payoff mass
`paySum(m ∧ O_ℓ) = ρ_ℓ · C(d_ℓ)(m) · (α·[m] − β γ_ℓ)`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("Lemma 3 within the observation");
mandate T6(a)
Kind: L -/
theorem tickle_point_masses (ℓ : Bool) :
    nu C T (tickleObs ℓ) = lesionRate ρ ℓ ∧
    (∀ m, nu C T (evM m ∩ tickleObs ℓ) = lesionRate ρ ℓ * (C ℓ).w m) ∧
    (∀ m, nu C T (evK ∩ evM m ∩ tickleObs ℓ) = lesionRate ρ ℓ * (C ℓ).w m * tickleGamma γ₁ γ₀ ℓ) ∧
    (∀ m, paySum C T (evM m ∩ tickleObs ℓ) =
      lesionRate ρ ℓ * (C ℓ).w m * ((if m then α else 0) - β * tickleGamma γ₁ γ₀ ℓ)) := by
  have hw : ∀ d : Bool, (C d).w false = 1 - (C d).w true := by
    intro d
    have := (C d).sum_one
    rw [Fintype.sum_bool] at this
    linarith
  refine ⟨?_, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · rw [tickle_nu']
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw', mem_tickleObs, lesionRate]
    cases ℓ <;> simp [hw] <;> ring
  · rw [tickle_nu']
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw', Finset.mem_inter, mem_tickleObs,
      mem_evM, lesionRate]
    cases ℓ <;> cases m <;> simp <;> try ring
  · rw [tickle_nu']
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw', Finset.mem_inter, mem_tickleObs,
      mem_evM, mem_evK, lesionRate, tickleGamma]
    cases ℓ <;> cases m <;> simp <;> ring
  · rw [tickle_paySum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickle_leafLaw', Finset.mem_inter, mem_tickleObs,
      mem_evM, lesionRate, tickleGamma, ticklePay]
    cases ℓ <;> cases m <;> simp <;> ring

/-! ### T6(a): flat act-conditionals at each point -/

/-- **Proposition 12's flatness clause**: at each tickle point, for every procedure,
`ν(k ∧ m ∧ O_ℓ) · ν(m' ∧ O_ℓ) = ν(k ∧ m' ∧ O_ℓ) · ν(m ∧ O_ℓ)` — the post-query `k`-clause
(the lesion-only clause within the observation), not `screening_recorded`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("each queried state satisfies
`P_s(k ∣ m=1) = P_s(k ∣ m=0)` (Lemma 3 within the observation)"); mandate T6(a)
Kind: P
Fidelity: exact (cross-multiplied)
Hyps: none -/
theorem tickle_flat_at_point (ℓ m m' : Bool) :
    nu C T (evK ∩ evM m ∩ tickleObs ℓ) * nu C T (evM m' ∩ tickleObs ℓ) =
      nu C T (evK ∩ evM m' ∩ tickleObs ℓ) * nu C T (evM m ∩ tickleObs ℓ) := by
  obtain ⟨-, h2, h3, -⟩ := tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ
  rw [h2, h2, h3, h3]; ring

/-- **(S2) fails at every strictly calibrated tickle state**: at point `ℓ` with `ν(O_ℓ) > 0`,
clause 1 pins `P_{s_ℓ}` to `ν(· ∣ O_ℓ)`, whose act-conditionals of cancer are flat.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("(S2) fails at every decision-point");
mandate T6(a)
Kind: C
Fidelity: exact
Hyps: (a) `StrictOCAt` at `ℓ`; (a) `0 < ν(O_ℓ)` -/
theorem tickle_not_S2_strict (ℓ : Bool) (s : Bool → State TickleW ℚ)
    (hpos : 0 < nu C T (tickleObs ℓ)) (hs : StrictOCAt s tickleObs C T ℓ) : ¬ S2 (s ℓ) := by
  rintro ⟨-, -, hlt⟩
  have h1 := (hs hpos).1
  have hP : ∀ X, (s ℓ).pr X = nu C T (X ∩ tickleObs ℓ) / nu C T (tickleObs ℓ) := by
    intro X; rw [eq_div_iff hpos.ne']; exact h1 X
  rw [hP, hP, hP, hP, div_mul_div_comm, div_mul_div_comm,
    tickle_flat_at_point ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ false true] at hlt
  exact lt_irrefl _ hlt

/-- **(S2) fails at every masked tickle state** (LF/vacuity, any self-model): the strict clauses
under the self-model `C[d_ℓ ↦ m]` give flat conditionals, whatever `m`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("in every such [masked] instantiation");
mandate T6(a)
Kind: C
Fidelity: exact (masked = first disjunct; the vacuity disjunct cannot fire when `ν_C(O_ℓ) > 0`
is not assumed — stated for the first disjunct through `MaskedOCAt` with the positivity of
the self-model's `ν(O_ℓ)` inside the definition)
Hyps: (a) `MaskedOCAt` at `ℓ` (first disjunct) -/
theorem tickle_not_S2_masked (ℓ : Bool) (s : Bool → State TickleW ℚ)
    (hs : MaskedOCAt s tickleObs C T ℓ) (hnv : ∃ C', Admissible .LF C ℓ C' ∧ 0 < nu C' T (tickleObs ℓ)) :
    ¬ S2 (s ℓ) := by
  rcases hs with ⟨C', -, hpos, hcl⟩ | ⟨-, hnull⟩
  · exact tickle_not_S2_strict ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C' ℓ s hpos (fun _ => hcl)
  · exfalso
    obtain ⟨C', hadm, hpos⟩ := hnv
    have := hnull C' hadm
    rw [this] at hpos
    exact lt_irrefl 0 hpos

/-- **E1-tickle numbers**: `ρ = ½`, `γ = (¾, ¼)`, `C = (δ_smoke, ½)`: the population correlation
is `ν(k ∣ m=1) = 7/12 > ¼ = ν(k ∣ m=0)` while the point-local conditionals are flat,
`P_{s_{d₁}}(k ∣ m) = ¾` and `P_{s_{d₀}}(k ∣ m) = ¼` (as `ν(k ∧ m ∧ O_ℓ)/ν(m ∧ O_ℓ)`).
Source: `sl-defensible-claims.md` S5 ("E1-tickle at `C = (smoke, ½)` has population `7/12` vs
`¼` while `P_{s_{d₁}}(k ∣ m) = ¾`, `P_{s_{d₀}}(k ∣ m) = ¼`"); mandate T6(a)
Kind: N+ -/
theorem tickle_e1_instance :
    let Cq := procTickle 1 (by norm_num) (by norm_num) (1/2) (by norm_num) (by norm_num)
    let B := tickle (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num) (by norm_num)
      (1/4) (by norm_num) (by norm_num) 1 3
    nu Cq B (evK ∩ evM true) / nu Cq B (evM true) = 7/12 ∧
    nu Cq B (evK ∩ evM false) / nu Cq B (evM false) = 1/4 ∧
    nu Cq B (evK ∩ evM true ∩ tickleObs true) / nu Cq B (evM true ∩ tickleObs true) = 3/4 ∧
    nu Cq B (evK ∩ evM true ∩ tickleObs false) / nu Cq B (evM true ∩ tickleObs false) = 1/4 ∧
    nu Cq B (evK ∩ evM false ∩ tickleObs false) / nu Cq B (evM false ∩ tickleObs false) = 1/4 := by
  intro Cq B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [tickle_nu_k_m1, tickle_nu_m1]; norm_num
  · rw [tickle_nu_k_m0, tickle_nu_m0]; norm_num
  · obtain ⟨-, h2, h3, -⟩ := tickle_point_masses (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num)
      (by norm_num) (1/4) (by norm_num) (by norm_num) 1 3 Cq true
    rw [h2, h3]; simp [Cq, procTickle, lesionRate, tickleGamma]; norm_num
  · obtain ⟨-, h2, h3, -⟩ := tickle_point_masses (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num)
      (by norm_num) (1/4) (by norm_num) (by norm_num) 1 3 Cq false
    rw [h2, h3]; simp [Cq, procTickle, lesionRate, tickleGamma]; norm_num
  · obtain ⟨-, h2, h3, -⟩ := tickle_point_masses (1/2) (by norm_num) (by norm_num) (3/4) (by norm_num)
      (by norm_num) (1/4) (by norm_num) (by norm_num) 1 3 Cq false
    rw [h2, h3]; simp [Cq, procTickle, lesionRate, tickleGamma]; norm_num

/-! ### T5(a): the sign law -/

/-- **Corollary 12′'s sign law**: with `γ₁ > γ₀` and `ρ ∈ (0, 1)`, the cross-multiplied
population correlation `ν(k ∧ m=1)·ν(m=0) − ν(k ∧ m=0)·ν(m=1)` is positive iff `q₁ > q₀`
(from `dp-core-tree`'s `tickle_identity`; `q₁ = q₀ ⇒ 0` is `tickle_identity_of_eq`, cited).
Source: dp-sl-013 ("sign `= sign(q₁ − q₀)` when `γ₁ > γ₀`"); `sl-defensible-claims.md` S5;
mandate T5(a)
Kind: C
Fidelity: exact (cross-multiplied)
Hyps: (a) `γ₀ < γ₁`; (a) `0 < ρ < 1` -/
theorem tickle_sign_law (hγ : γ₀ < γ₁) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (q₁ : ℚ) (a0 : 0 ≤ q₁) (a1 : q₁ ≤ 1) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1) :
    0 < nu (procTickle q₁ a0 a1 q₀ b0 b1) T (evK ∩ evM true) *
          nu (procTickle q₁ a0 a1 q₀ b0 b1) T (evM false) -
        nu (procTickle q₁ a0 a1 q₀ b0 b1) T (evK ∩ evM false) *
          nu (procTickle q₁ a0 a1 q₀ b0 b1) T (evM true) ↔ q₀ < q₁ := by
  rw [tickle_identity]
  have hc : 0 < (γ₁ - γ₀) * (ρ * (1 - ρ)) := mul_pos (sub_pos.mpr hγ) (mul_pos hρ0 (sub_pos.mpr hρ1))
  have e : (γ₁ - γ₀) * (q₁ - q₀) * ρ * (1 - ρ) = ((γ₁ - γ₀) * (ρ * (1 - ρ))) * (q₁ - q₀) := by ring
  rw [e]
  constructor
  · intro h
    by_contra hle
    have hle' : q₁ - q₀ ≤ 0 := by linarith [not_lt.mp hle]
    have := mul_nonpos_of_nonneg_of_nonpos hc.le hle'
    linarith
  · intro h
    exact mul_pos hc (sub_pos.mpr h)

/-! ### T6(b): recording, the vacuity finding, the masked rider -/

/-- Every run of the tickle tree meets `d_ℓ` once on the `ℓ`-branch and never on the other.
Source: none: infrastructure. Kind: L -/
theorem tickle_count (i : Fin 2) (m : Bool) (j : Fin 2) (ℓ : Bool) :
    count ℓ T (tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j) =
      if decide (i = 0) = ℓ then 1 else 0 := by
  unfold tickleLeaf tickle
  simp only [count_chance, count_decision, count_leaf, add_zero]

/-- Every leaf of the tickle tree is a `tickleLeaf`. Source: none: infrastructure. Kind: L -/
theorem tickle_leaves (ℓ : (T).Leaves) :
    ∃ (i : Fin 2) (m : Bool) (j : Fin 2), ℓ = tickleLeaf ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β i m j := by
  unfold tickle at ℓ
  rcases ℓ with ⟨i, m, j, ⟨⟩⟩
  exact ⟨i, m, j, rfl⟩

/-- **The tickle tree records at both points for every procedure**: the `ℓ`-branch's `d_ℓ`-node
is the unique `d_ℓ`-node on the `O_ℓ`-runs, subtree-veridical (every leaf below it has lesion
`ℓ`), the leaf's `m` is the draw.
Source: [[decision-problems-v2]] Definition 7 on Proposition 12's instantiation; mandate T6(b)
("prove `tickle_recordsFor`")
Kind: N+ -/
theorem tickle_recordsFor (ℓ : Bool) : RecordsFor tickleObs tickleActEv C T ℓ := by
  intro lf _ hobs
  obtain ⟨i, m, j, rfl⟩ := tickle_leaves ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β lf
  have hi : decide (i = 0) = ℓ := by
    rw [tickle_world] at hobs; simpa using hobs
  refine ⟨by rw [tickle_count, if_pos hi], ?_⟩
  unfold tickleLeaf tickle
  rintro ⟨i', (_ | ⟨m', ⟨j', e⟩⟩)⟩ hq a ha
  · by_cases hii : i = i'
    · subst hii
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨i'', m'', j'', _⟩ hb
        rw [mem_leavesBelow] at hb
        by_cases hi'' : i'' = i
        · subst hi''
          simp only [pt_chance, pt_decision_none]
          simp [hi]
        · simp [edgeOf_chance, hi''] at hb
      · simp
      · intro a' ha'; simp at ha'; exact ha'.symm
    · simp [edgeOf_chance, hii] at ha
  · exact e.elim

/-- `H*` holds on the tickle tree at both points for every procedure: every positive run
through a `d_ℓ`-node has lesion `ℓ`.
Source: mandate T6(b), `sl-defensible-claims.md` S1 ("their observations are `⊤` or the lesion
branch")
Kind: L -/
theorem tickle_hStar (ℓ : Bool) : HStar tickleObs tickleActEv C T ℓ := by
  refine ⟨tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ, fun lf _ hc => ?_⟩
  obtain ⟨i, m, j, rfl⟩ := tickle_leaves ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β lf
  rw [tickle_count] at hc
  rw [tickle_world]
  by_cases h : decide (i = 0) = ℓ
  · simpa using h
  · rw [if_neg h] at hc; exact absurd hc (lt_irrefl 0)

/-- **The vacuity finding**: for the deterministic refrain–refrain procedure, `T_EDT` approves
both tickle points at their strictly calibrated states (`A_{d_ℓ}^+ = {refrain}`): Proposition
12's "conditional-value maximization at a calibrated state … smokes" is vacuous at the strict
grade for deterministic procedures.
Source: dp-sl-014 ("`T_EDT` approves every deterministic procedure on the tickle instantiation,
refrain–refrain included"); `sl-defensible-claims.md` S5 rider (ii); mandate T6(b)
Kind: N−
Fidelity: exact (the refuted claim is "smokes" as a non-vacuous verdict at the strict grade)
Hyps: (a) `0 < ρ < 1` (both points realized) -/
theorem tickle_refrain_refrain_approved (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    let C₀ := procTickle 0 le_rfl zero_le_one 0 le_rfl zero_le_one
    let s₀ : Bool → State TickleW ℚ := fun ℓ =>
      calibratedState C₀ T (tickleObs ℓ) (by
        rw [(tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C₀ ℓ).1]
        unfold lesionRate; cases ℓ <;> simp <;> linarith)
    ∀ ℓ, APlus s₀ tickleActEv ℓ = {false} ∧ TEdtAt s₀ tickleActEv C₀ ℓ := by
  intro C₀ s₀ ℓ
  have hpos : 0 < nu C₀ T (tickleObs ℓ) := by
    rw [(tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C₀ ℓ).1]
    unfold lesionRate; cases ℓ <;> simp <;> linarith
  have hC : C₀ ℓ = FinDistr.pure false := by
    apply FinDistr.ext'; intro a; cases a <;> cases ℓ <;> simp [C₀, procTickle]
  exact tEdtAt_of_deterministic_recorded s₀ tickleActEv tickleObs C₀ T false hC
    (tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C₀ ℓ) hpos
    (strictOCAt_calibratedState tickleObs C₀ T s₀ ℓ hpos rfl)

/-- **Smokes by `α` at a calibrated tickle state**: at a state strictly calibrated at `d_ℓ`
(`ν(O_ℓ) > 0`) with both acts subjectively possible, `V(smoke) − V(refrain) = α`.
Source: [[decision-problems-v2]] §7.3 Proposition 12 ("computes a difference of `α > 0` and
smokes"); mandate T5(b)
Kind: P
Fidelity: exact
Hyps: (a) `StrictOCAt` at `ℓ`, `0 < ν(O_ℓ)`; (a) both acts in `A_{d_ℓ}^+` -/
theorem tickle_smokes_by_alpha (ℓ : Bool) (s : Bool → State TickleW ℚ)
    (hpos : 0 < nu C T (tickleObs ℓ)) (hs : StrictOCAt s tickleObs C T ℓ)
    (ht : true ∈ APlus s tickleActEv ℓ) (hf : false ∈ APlus s tickleActEv ℓ) :
    (s ℓ).V (tickleActEv ℓ true) - (s ℓ).V (tickleActEv ℓ false) = α := by
  obtain ⟨-, h2, -, h4⟩ := tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ
  have hcl := hs hpos
  have et := V_mul_nu_eq_paySum tickleObs tickleActEv C T ℓ s hpos hcl true ht
  have ef := V_mul_nu_eq_paySum tickleObs tickleActEv C T ℓ s hpos hcl false hf
  have hνt := (mem_aPlus_iff tickleObs tickleActEv C T ℓ s hpos hcl.1 true).mp ht
  have hνf := (mem_aPlus_iff tickleObs tickleActEv C T ℓ s hpos hcl.1 false).mp hf
  simp only [tickleActEv_eq] at et ef hνt hνf ⊢
  rw [h2, h4] at et ef
  rw [h2] at hνt hνf
  simp only [if_true, Bool.false_eq_true, if_false] at et ef
  have ht' : (s ℓ).V (evM true) = α - β * tickleGamma γ₁ γ₀ ℓ :=
    mul_right_cancel₀ hνt.ne' (by rw [et]; ring)
  have hf' : (s ℓ).V (evM false) = 0 - β * tickleGamma γ₁ γ₀ ℓ :=
    mul_right_cancel₀ hνf.ne' (by rw [ef]; ring)
  rw [ht', hf']; ring

/-- **No interior label is `T_EDT`-approved at a realized tickle point** (with `α > 0`): under
an interior `C(d_ℓ)` both acts are subjectively possible at the strict state (self-transparency),
`V(smoke) > V(refrain)`, and refrain is in the support — so the label is rejected.
Source: `sl-defensible-claims.md` S5 ("a `T_EDT`-approved interior label does not exist");
mandate T5(b)
Kind: C
Fidelity: exact
Hyps: (a) `0 < α`; (a) `0 < ν(O_ℓ)`; (a) `0 < C(d_ℓ)(smoke) < 1`; (a) `StrictOCAt` at `ℓ` -/
theorem tickle_no_interior_approved (hα : 0 < α) (ℓ : Bool) (s : Bool → State TickleW ℚ)
    (hpos : 0 < nu C T (tickleObs ℓ)) (hs : StrictOCAt s tickleObs C T ℓ)
    (hq0 : 0 < (C ℓ).w true) (hq1 : (C ℓ).w true < 1) : ¬ TEdtAt s tickleActEv C ℓ := by
  intro happ
  have hst := selfTransparent_of_recordsFor_strict tickleObs tickleActEv C T s
    (tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ) hpos hs
  have hwf : (C ℓ).w false = 1 - (C ℓ).w true := by
    have := (C ℓ).sum_one; rw [Fintype.sum_bool] at this; linarith
  have ht : true ∈ APlus s tickleActEv ℓ := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, hst true]; exact hq0
  have hf : false ∈ APlus s tickleActEv ℓ := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, hst false, hwf]; linarith
  have hgap := tickle_smokes_by_alpha ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ s hpos hs ht hf
  have hmem := happ ⟨true, ht⟩ false (by rw [hwf]; linarith)
  rw [mem_argmaxPlus] at hmem
  have := hmem.2 true ht
  linarith

/-- **Definition 17's `EDT` procedure on the tickle tree is `(δ_smoke, δ_smoke)`** whenever its
states are strictly calibrated at both points with both acts possible (e.g. read off an interior
label); its population correlation is then `0` (`tickle_identity_of_eq`, cited). A population
of calibrated `EDT` agents with equal desirabilities carries no lesion–smoking correlation.
Source: `sl-defensible-claims.md` S5 ("Corollary 12′: … with equal desirabilities calibrated
EDT and every referent smoke at both points and the correlation is zero"); dp-core-114; mandate
T5(b)
Kind: C
Fidelity: exact
Hyps: (a) `0 < α`; (a) both points realized, strictly calibrated, both acts possible -/
theorem tickle_edtProc_smoke_smoke (hα : 0 < α) (s : Bool → State TickleW ℚ)
    (hpos : ∀ ℓ, 0 < nu C T (tickleObs ℓ)) (hs : ∀ ℓ, StrictOCAt s tickleObs C T ℓ)
    (ht : ∀ ℓ, true ∈ APlus s tickleActEv ℓ) (hf : ∀ ℓ, false ∈ APlus s tickleActEv ℓ) :
    (∀ ℓ, argmaxPlus s tickleActEv ℓ = {true}) ∧
    (∀ ℓ, edtProc s tickleActEv ℓ = FinDistr.pure true) := by
  have hmax : ∀ ℓ, argmaxPlus s tickleActEv ℓ = {true} := by
    intro ℓ
    have hgap := tickle_smokes_by_alpha ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C ℓ s (hpos ℓ) (hs ℓ)
      (ht ℓ) (hf ℓ)
    ext a
    rw [mem_argmaxPlus, Finset.mem_singleton]
    cases a
    · constructor
      · rintro ⟨-, h⟩
        have := h true (ht ℓ)
        linarith
      · intro h; exact absurd h (by decide)
    · constructor
      · intro _; rfl
      · intro _
        refine ⟨ht ℓ, fun b _ => ?_⟩
        cases b
        · linarith
        · exact le_rfl
  refine ⟨hmax, fun ℓ => ?_⟩
  unfold edtProc
  rw [dif_pos (by rw [hmax]; exact Finset.singleton_nonempty _)]
  apply FinDistr.ext'
  intro a
  rw [uniformOn_w, hmax, FinDistr.pure_w]
  cases a <;> simp

/-- **Smokes by `α` at the masked grade, for every procedure**: the state calibrated to an
interior self-model `C[d_ℓ ↦ m]` at a realized point is a masked witness for `C` at `d_ℓ` with
both acts possible and `V(smoke) − V(refrain) = α` — Proposition 12's "masked-calibrated
instantiations exist for any `C` … and smokes", non-vacuously, with the state at the
self-model (rider (i)).
Source: [[decision-problems-v2]] §7.3 Proposition 12; `sl-defensible-claims.md` S5 rider (i);
mandate T6(b)
Kind: C
Fidelity: exact (masked = first disjunct at the self-model `m`)
Hyps: (a) `m` full-support; (a) `0 < ν(O_ℓ)` -/
theorem tickle_masked_smokes_by_alpha (ℓ : Bool) (m : FinDistr ℚ Bool) (hm : ∀ a, 0 < m.w a)
    (hpos : 0 < nu (C.deviate ℓ m) T (tickleObs ℓ)) :
    let s₀ : Bool → State TickleW ℚ := fun _ => calibratedState (C.deviate ℓ m) T (tickleObs ℓ) hpos
    MaskedOCAt s₀ tickleObs C T ℓ ∧ true ∈ APlus s₀ tickleActEv ℓ ∧ false ∈ APlus s₀ tickleActEv ℓ ∧
      (s₀ ℓ).V (tickleActEv ℓ true) - (s₀ ℓ).V (tickleActEv ℓ false) = α := by
  intro s₀
  have hstrict : StrictOCAt s₀ tickleObs (C.deviate ℓ m) T ℓ :=
    strictOCAt_calibratedState tickleObs _ _ s₀ ℓ hpos rfl
  have hst := selfTransparent_of_recordsFor_strict tickleObs tickleActEv (C.deviate ℓ m) T s₀
    (tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β _ ℓ) hpos hstrict
  have ht : true ∈ APlus s₀ tickleActEv ℓ := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, hst true, Proc.deviate_same]
    exact hm true
  have hf : false ∈ APlus s₀ tickleActEv ℓ := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, hst false, Proc.deviate_same]
    exact hm false
  exact ⟨maskedOCAt_calibratedState tickleObs C T s₀ ℓ m hm hpos rfl, ht, hf,
    tickle_smokes_by_alpha ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β _ ℓ s₀ hpos hstrict ht hf⟩

/-- **Rider (i): a deterministic procedure's strictly calibrated self-certain tickle state is
not masked-calibrated (LF)**: at `d₁` under `(δ_smoke, ·)` the strict state has `P(smoke) = 1`,
while every full-support self-model gives `P(smoke) = m(smoke) < 1`. So Definition 9's official
form reports *violated* for the deterministic procedure's own strict state; Proposition 12's
"masked-calibrated instantiations exist for any `C`" is true with the state at an interior
self-model (`tickle_masked_smokes_by_alpha`), a different state.
Source: `sl-defensible-claims.md` S5 rider (i) ("Definition 9's official full-support form
reports `violated` for a deterministic procedure's strictly calibrated state"); mandate T6(b)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < ρ` -/
theorem tickle_strict_not_masked (hρ0 : 0 < ρ) (q₀ : ℚ) (b0 : 0 ≤ q₀) (b1 : q₀ ≤ 1) :
    let C₁ := procTickle 1 zero_le_one le_rfl q₀ b0 b1
    ∀ hpos : 0 < nu C₁ T (tickleObs true),
    let s₀ : Bool → State TickleW ℚ := fun _ => calibratedState C₁ T (tickleObs true) hpos
    StrictOCAt s₀ tickleObs C₁ T true ∧ ¬ MaskedOCAt s₀ tickleObs C₁ T true := by
  intro C₁ hpos s₀
  refine ⟨strictOCAt_calibratedState tickleObs C₁ T s₀ true hpos rfl, ?_⟩
  have hst := selfTransparent_of_recordsFor_strict tickleObs tickleActEv C₁ T s₀
    (tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β C₁ true) hpos
    (strictOCAt_calibratedState tickleObs C₁ T s₀ true hpos rfl)
  have h1 : (s₀ true).pr (tickleActEv true true) = 1 := by rw [hst true]; simp [C₁, procTickle]
  rintro (⟨C', ⟨m, hm, rfl⟩, hpos', hcl⟩ | ⟨-, hnull⟩)
  · have h2 := hcl.1 (tickleActEv true true)
    rw [h1, one_mul, nu_actEv_inter_obs_of_recordsFor tickleObs tickleActEv _ T
      (tickle_recordsFor ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β _ true), Proc.deviate_same] at h2
    have hb := hm false
    have hsum := m.sum_one
    rw [Fintype.sum_bool] at hsum
    have h3 : (1 - m.w true) * nu (C₁.deviate true m) T (tickleObs true) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hpos'.ne'
  · have := hnull (C₁.deviate true (FinDistr.bool (1/2) (by norm_num) (by norm_num)))
      ⟨FinDistr.bool (1/2) (by norm_num) (by norm_num),
        fun a => by cases a <;> norm_num [FinDistr.bool_true, FinDistr.bool_false], rfl⟩
    rw [(tickle_point_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α β _ true).1] at this
    unfold lesionRate at this
    simp at this
    linarith

end tickle

/-! ## Rosa's population: lesion-dependent desirabilities -/

section rosa

variable (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ₁ : ℚ) (g10 : 0 ≤ γ₁) (g11 : γ₁ ≤ 1)
  (γ₀ : ℚ) (g00 : 0 ≤ γ₀) (g01 : γ₀ ≤ 1) (α₁ α₀ β : ℚ)

/-- The typed tickle payoff `α_ℓ · m − β · k`: the lesion also changes the desirability of
smoking.
Source: dp-core-114 ("the lesion causes love of smoking" as a desirability); mandate T5(b) (Rosa)
Kind: D -/
def tickleTypedPay (w : TickleW) : ℚ :=
  (if w.2.1 then (if w.1 then α₁ else α₀) else 0) - (if w.2.2 then β else 0)

/-- **The typed tickle tree** (Rosa's population): the tickle tree with payoff `α_ℓ m − β k`.
Source: dp-core-114; `sl-defensible-claims.md` S5 ("only if `α₁ > 0 > α₀`"); mandate T5(b)
Kind: D -/
def tickleTyped : Tree TickleW Bool (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin ρ r0 r1) fun i =>
    .decision (decide (i = 0)) fun m =>
      .chance 2 (FinDistr.coin (tickleGamma γ₁ γ₀ (decide (i = 0)))
          (by unfold tickleGamma; split_ifs <;> assumption)
          (by unfold tickleGamma; split_ifs <;> assumption)) fun j =>
        .leaf (decide (i = 0), m, decide (j = 0))
          (tickleTypedPay α₁ α₀ β (decide (i = 0), m, decide (j = 0)))

local notation "TT" => tickleTyped ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α₁ α₀ β

/-- A sum over the leaves of the typed tickle tree. Source: none: infrastructure. Kind: L -/
theorem tickleTyped_sum (f : (TT).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f ⟨i, m, j, ()⟩ := by
  unfold tickleTyped at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf masses of the typed tickle tree (the same as the tickle tree's).
Source: Definition 6. Kind: L -/
theorem tickleTyped_leafLaw (C : Proc Bool (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C TT ⟨i, m, j, ()⟩ =
      (if i = 0 then ρ else 1 - ρ) * (C (decide (i = 0))).w m *
        (if i = 0 then (if j = 0 then γ₁ else 1 - γ₁) else (if j = 0 then γ₀ else 1 - γ₀)) := by
  unfold tickleTyped
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.coin, tickleGamma]
  fin_cases i <;> fin_cases j <;> simp <;> ring

variable (C : Proc Bool (fun _ => Bool) ℚ)

/-- The point-local masses on the typed tickle tree: `ν(O_ℓ) = ρ_ℓ`, `ν(m ∧ O_ℓ) = ρ_ℓ C(d_ℓ)(m)`,
`paySum(m ∧ O_ℓ) = ρ_ℓ C(d_ℓ)(m)(α_ℓ [m] − β γ_ℓ)`; and the population masses `ν(m)`,
`ν(k ∧ m)` as on the tickle tree.
Source: dp-core-114; mandate T5(b)
Kind: L -/
theorem tickleTyped_masses (ℓ : Bool) :
    nu C TT (tickleObs ℓ) = lesionRate ρ ℓ ∧
    (∀ m, nu C TT (evM m ∩ tickleObs ℓ) = lesionRate ρ ℓ * (C ℓ).w m) ∧
    (∀ m, paySum C TT (evM m ∩ tickleObs ℓ) =
      lesionRate ρ ℓ * (C ℓ).w m * ((if m then (if ℓ then α₁ else α₀) else 0) - β * tickleGamma γ₁ γ₀ ℓ)) ∧
    nu C TT (evM true) = ρ * (C true).w true + (1 - ρ) * (C false).w true ∧
    nu C TT (evM false) = ρ * (C true).w false + (1 - ρ) * (C false).w false ∧
    nu C TT (evK ∩ evM true) = ρ * (C true).w true * γ₁ + (1 - ρ) * (C false).w true * γ₀ ∧
    nu C TT (evK ∩ evM false) = ρ * (C true).w false * γ₁ + (1 - ρ) * (C false).w false * γ₀ := by
  have hw : ∀ d : Bool, (C d).w false = 1 - (C d).w true := by
    intro d
    have := (C d).sum_one
    rw [Fintype.sum_bool] at this
    linarith
  have hnu : ∀ X, nu C TT X = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C TT ⟨i, m, j, ()⟩ else 0 := by
    intro X; rw [nu_eq_sum, tickleTyped_sum]; rfl
  have hpay : ∀ X, paySum C TT X = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then
        leafLaw C TT ⟨i, m, j, ()⟩ * tickleTypedPay α₁ α₀ β (decide (i = 0), m, decide (j = 0))
      else 0 := by
    intro X; rw [paySum_eq_sum_ite, tickleTyped_sum]; rfl
  refine ⟨?_, fun m => ?_, fun m => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, mem_tickleObs, lesionRate]
    cases ℓ <;> simp [hw] <;> ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, Finset.mem_inter,
      mem_tickleObs, mem_evM, lesionRate]
    cases ℓ <;> cases m <;> simp <;> ring
  · rw [hpay]
    simp only [Fin.sum_univ_two, Fintype.sum_bool]
    simp only [tickleTyped_leafLaw]
    simp only [Finset.mem_inter, mem_tickleObs, mem_evM, lesionRate, tickleGamma, tickleTypedPay]
    cases ℓ <;> cases m <;> simp <;> ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, mem_evM]
    simp; ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, mem_evM]
    simp; ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, Finset.mem_inter, mem_evM,
      mem_evK]
    simp
    try ring
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, tickleTyped_leafLaw, Finset.mem_inter, mem_evM,
      mem_evK]
    simp
    try ring

/-- The typed tickle tree records at both points for every procedure (the tickle tree's proof).
Source: mandate T5(b)
Kind: L -/
theorem tickleTyped_recordsFor (ℓ : Bool) : RecordsFor tickleObs tickleActEv C TT ℓ := by
  intro lf _ hobs
  unfold tickleTyped at lf hobs ⊢
  rcases lf with ⟨i, m, j, ⟨⟩⟩
  have hi : decide (i = 0) = ℓ := by simpa using hobs
  refine ⟨by simp [count_chance, count_decision, hi], ?_⟩
  rintro ⟨i', (_ | ⟨m', ⟨j', e⟩⟩)⟩ hq a ha
  · by_cases hii : i = i'
    · subst hii
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨i'', m'', j'', _⟩ hb
        rw [mem_leavesBelow] at hb
        by_cases hi'' : i'' = i
        · subst hi''
          simp only [pt_chance, pt_decision_none]
          simp [hi]
        · simp [edgeOf_chance, hi''] at hb
      · simp
      · intro a' ha'; simp at ha'; exact ha'.symm
    · simp [edgeOf_chance, hii] at ha
  · exact e.elim

/-- **Rosa's population**: with `α₁ > 0 > α₀` (`β` arbitrary), at states strictly calibrated at
both points with both acts possible, `V(smoke) − V(refrain) = α_ℓ`, so Definition 17's `EDT`
procedure is `(δ_smoke, δ_refrain)`: `q₁ − q₀ = 1`, and the population correlation (as on the
tickle tree, `tickle_identity`'s form) is `(γ₁ − γ₀) ρ (1 − ρ)`, positive when `γ₁ > γ₀` and
`ρ ∈ (0, 1)`. The population correlation is the procedure's type-difference.
Source: dp-core-114 ("Rosa's mixed population — the population correlation is the procedure's
type-difference"); `sl-defensible-claims.md` S5 (Corollary 12′: "only if `α₁ > 0 > α₀`");
mandate T5(b)
Kind: C
Fidelity: exact
Hyps: (a) `α₁ > 0 > α₀`; (a) both points realized, strictly calibrated, both acts possible -/
theorem rosa_edtProc_split (hα₁ : 0 < α₁) (hα₀ : α₀ < 0) (s : Bool → State TickleW ℚ)
    (hpos : ∀ ℓ, 0 < nu C TT (tickleObs ℓ)) (hs : ∀ ℓ, StrictOCAt s tickleObs C TT ℓ)
    (ht : ∀ ℓ, true ∈ APlus s tickleActEv ℓ) (hf : ∀ ℓ, false ∈ APlus s tickleActEv ℓ) :
    (∀ ℓ, (s ℓ).V (tickleActEv ℓ true) - (s ℓ).V (tickleActEv ℓ false) = if ℓ then α₁ else α₀) ∧
    edtProc s tickleActEv true = FinDistr.pure true ∧
    edtProc s tickleActEv false = FinDistr.pure false ∧
    (let E := edtProc s tickleActEv
     nu E TT (evK ∩ evM true) * nu E TT (evM false) - nu E TT (evK ∩ evM false) * nu E TT (evM true)
       = (γ₁ - γ₀) * ρ * (1 - ρ)) := by
  have hgap : ∀ ℓ, (s ℓ).V (tickleActEv ℓ true) - (s ℓ).V (tickleActEv ℓ false) =
      if ℓ then α₁ else α₀ := by
    intro ℓ
    obtain ⟨-, h2, h3, -⟩ := tickleTyped_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α₁ α₀ β C ℓ
    have hcl := hs ℓ (hpos ℓ)
    have et := V_mul_nu_eq_paySum tickleObs tickleActEv C TT ℓ s (hpos ℓ) hcl true (ht ℓ)
    have ef := V_mul_nu_eq_paySum tickleObs tickleActEv C TT ℓ s (hpos ℓ) hcl false (hf ℓ)
    have hνt := (mem_aPlus_iff tickleObs tickleActEv C TT ℓ s (hpos ℓ) hcl.1 true).mp (ht ℓ)
    have hνf := (mem_aPlus_iff tickleObs tickleActEv C TT ℓ s (hpos ℓ) hcl.1 false).mp (hf ℓ)
    simp only [tickleActEv_eq] at et ef hνt hνf ⊢
    rw [h2, h3] at et ef
    rw [h2] at hνt hνf
    simp only [if_true, Bool.false_eq_true, if_false] at et ef
    have ht' : (s ℓ).V (evM true) = (if ℓ then α₁ else α₀) - β * tickleGamma γ₁ γ₀ ℓ :=
      mul_right_cancel₀ hνt.ne' (by rw [et]; ring)
    have hf' : (s ℓ).V (evM false) = 0 - β * tickleGamma γ₁ γ₀ ℓ :=
      mul_right_cancel₀ hνf.ne' (by rw [ef]; ring)
    rw [ht', hf']; ring
  have hmax1 : argmaxPlus s tickleActEv true = {true} := by
    have hg := hgap true
    simp only [if_true] at hg
    ext a
    rw [mem_argmaxPlus, Finset.mem_singleton]
    cases a
    · constructor
      · rintro ⟨-, h⟩
        have := h true (ht true)
        linarith
      · intro h; exact absurd h (by decide)
    · constructor
      · intro _; rfl
      · intro _
        refine ⟨ht true, fun b _ => ?_⟩
        cases b
        · linarith
        · exact le_rfl
  have hmax0 : argmaxPlus s tickleActEv false = {false} := by
    have hg := hgap false
    simp only [Bool.false_eq_true, if_false] at hg
    ext a
    rw [mem_argmaxPlus, Finset.mem_singleton]
    cases a
    · constructor
      · intro _; rfl
      · intro _
        refine ⟨hf false, fun b _ => ?_⟩
        cases b
        · exact le_rfl
        · linarith
    · constructor
      · rintro ⟨-, h⟩
        have := h false (hf false)
        linarith
      · intro h; exact absurd h (by decide)
  have hE1 : edtProc s tickleActEv true = FinDistr.pure true := by
    unfold edtProc
    rw [dif_pos (by rw [hmax1]; exact Finset.singleton_nonempty _)]
    apply FinDistr.ext'; intro a
    rw [uniformOn_w, hmax1, FinDistr.pure_w]; cases a <;> simp
  have hE0 : edtProc s tickleActEv false = FinDistr.pure false := by
    unfold edtProc
    rw [dif_pos (by rw [hmax0]; exact Finset.singleton_nonempty _)]
    apply FinDistr.ext'; intro a
    rw [uniformOn_w, hmax0, FinDistr.pure_w]; cases a <;> simp
  refine ⟨hgap, hE1, hE0, ?_⟩
  intro E
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := tickleTyped_masses ρ r0 r1 γ₁ g10 g11 γ₀ g00 g01 α₁ α₀ β E true
  rw [h4, h5, h6, h7]
  simp only [E, hE1, hE0, FinDistr.pure_w]
  simp; ring

end rosa

end Cleanroom.Decision.DpSmokingLesion
