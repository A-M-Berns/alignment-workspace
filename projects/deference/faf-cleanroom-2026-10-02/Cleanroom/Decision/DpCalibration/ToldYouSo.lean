import Cleanroom.Decision.DpCalibration.MiniDevices

/-!
# Told-You-So Five-and-Ten: Proposition 8, E5/E9, Lemma 2's separation (T2(c)(i)(ii), T3(b))

Points `d₅ = five`, `d₁₀ = ten`; states `s_k` certain of the world `(k, k)` with `V ≡ k`.
Three procedures: `procFiveTen` (`C₀`: five at `d₅`, ten at `d₁₀` — **the** zero-respecting
procedure for these states), `procTake10` (`C*`: ten at both), `procTake5` (five at both — *not*
zero-respecting; Lemma 2's separation).

* **Proposition 8 for `C₀`**: strictly calibrated (`tys_fiveTen_strictOC`), limit-calibrated
  (`tys_fiveTen_limitOC`), masked-calibrated under the vacuity reading and **not** under the
  letter (`tys_fiveTen_maskedOC`, `tys_fiveTen_not_masked_letter`: `d₁₀` is unreachable under
  every `C₀[d₁₀ ↦ m]`) — E9.
* **E5, Proposition 8 for `C*`**: strictly and limit-calibrated, **not** LF-masked-calibrated at
  `d₁₀` under either reading (every full-support self-model gives
  `ν(· | O₁₀) = m(10)δ_{(10,10)} + m(5)δ_{(10,5)} ≠ δ_{(10,10)}`; `tys_take10_not_masked_LF`), and
  LP-masked-calibrated (`m = δ₁₀`; `tys_take10_masked_LP`) — the surviving neighbour.
* **Lemma 2's separation (T3(b))**: `procTake5` with `s₁₀` certain of `(10,10)` is strictly
  calibrated at `d₁₀` (vacuously) and not limit-calibrated there (`limitCond {(10,5)} O₁₀ = 1`);
  the state certain of `(10,5)` *is* limit-calibrated there (the pitfall of dp-core-2-052).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## Procedures, states, statistics -/

/-- `C₀`: five at `d₅`, ten at `d₁₀` — the zero-respecting procedure for the stipulated states.
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("`C₀` any zero-respecting procedure")
Kind: D -/
def procFiveTen : Proc Five10 (fun _ => Five10) ℚ := Proc.ofFun fun k => k

/-- `C*`: ten at both points. Source: [[decision-problems-v2]] Proposition 8. Kind: D -/
def procTake10 : Proc Five10 (fun _ => Five10) ℚ := Proc.ofFun fun _ => .ten

/-- Five at both points (Lemma 2's separation; not zero-respecting).
Source: [[decision-problems-v2]] Lemma 2 proof ("`C` takes five at *both* points")
Kind: D -/
def procTake5 : Proc Five10 (fun _ => Five10) ℚ := Proc.ofFun fun _ => .five

/-- The stipulated states: `s_k` certain of `(k, k)`, desirability `k`.
Source: [[decision-problems-v2]] §7.1 ("`P_{s_k}` certain of the world `(k, k)` and `V_{s_k}` its
conditional value")
Kind: D -/
def tysState : Five10 → State TysW ℚ := fun k => State.dirac (k, k) k.val

/-- A sum over the leaves of `toldYouSo` as three terms. Source: none: infrastructure. Kind: L -/
theorem tys_sum {M : Type} [AddCommMonoid M] (f : toldYouSo.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.five, ()⟩ + f ⟨.ten, .ten, ()⟩ + f ⟨.ten, .five, ()⟩ := by
  unfold toldYouSo at f ⊢
  rw [sum_leaves_decision, Five10.sum_univ, sum_leaves_decision, Five10.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  rw [add_assoc, add_comm (f ⟨Five10.ten, Five10.five, ()⟩) (f ⟨Five10.ten, Five10.ten, ()⟩)]

/-- `ν` on `toldYouSo`. Source: none: infrastructure. Kind: L -/
theorem tys_nu (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    nu C toldYouSo X =
      (if (Five10.five, Five10.five) ∈ X then (C .five).w .five else 0) +
      (if (Five10.ten, Five10.ten) ∈ X then (C .five).w .ten * (C .ten).w .ten else 0) +
      (if (Five10.ten, Five10.five) ∈ X then (C .five).w .ten * (C .ten).w .five else 0) := by
  rw [nu_eq_sum, tys_sum]
  simp [toldYouSo, leafLaw_decision, world_decision]

/-- `𝔼[r 1_X]` on `toldYouSo`. Source: none: infrastructure. Kind: L -/
theorem tys_paySum (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    paySum C toldYouSo X =
      (if (Five10.five, Five10.five) ∈ X then (C .five).w .five * 5 else 0) +
      (if (Five10.ten, Five10.ten) ∈ X then (C .five).w .ten * (C .ten).w .ten * 10 else 0) +
      (if (Five10.ten, Five10.five) ∈ X then (C .five).w .ten * (C .ten).w .five * 5 else 0) := by
  rw [paySum_eq_sum_ite, tys_sum]
  simp [toldYouSo, leafLaw_decision, world_decision, payoff_decision]

/-- Both points are queried. Source: none: infrastructure. Kind: L -/
theorem tys_queried (k : Five10) : k ∈ queried toldYouSo := by
  unfold toldYouSo
  cases k
  · simp [queried_decision]
  · simp only [queried_decision, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨.ten, by simp [queried_decision]⟩

/-- `O_k` membership. Source: none: infrastructure. Kind: L -/
theorem tys_mem_obs (k : Five10) (w : TysW) : w ∈ tysObs k ↔ w.1 = k := by simp [tysObs]

/-- **`C₀` is zero-respecting** for the stipulated states, and `procTake5` is not.
Source: [[decision-problems-v2]] Proposition 8 ("`C₀` any zero-respecting procedure",
"`P_{s_5}({m=10}) = 0`, so `C₀(d_5) = {m=5}`")
Kind: L -/
theorem tys_zeroRespecting :
    ZeroRespecting tysState tysActEv procFiveTen ∧ ¬ ZeroRespecting tysState tysActEv procTake5 := by
  constructor
  · intro d _ a ha
    simp only [procFiveTen, Proc.ofFun_w] at ha
    have : a = d := by by_contra h; simp [h] at ha
    subst this
    simp [APlus, tysState, State.dirac_pr, tysActEv]
  · intro h
    have := h .ten ⟨.ten, by simp [APlus, tysState, State.dirac_pr, tysActEv]⟩ .five
      (by simp [procTake5])
    simp [APlus, tysState, State.dirac_pr, tysActEv] at this

/-! ## Proposition 8 for `C₀ = (five, ten)` -/

/-- `C₀` is strictly calibrated: `ν = δ_{(5,5)}`, so `O₅` is certain and `O₁₀` null.
Source: [[decision-problems-v2]] Proposition 8 ("`ν_{C₀} = δ_{(5,5)}`: at `O_5`,
`ν(· ∣ O_5) = δ_{(5,5)} = P_{s_5}`; `ν(O_{10}) = 0` vacuous")
Kind: P -/
theorem tys_fiveTen_strictOC : StrictOC tysState tysObs procFiveTen toldYouSo := by
  intro d _ hpos
  cases d
  · refine ⟨fun X => ?_, fun X _ _ => ?_⟩
    · rw [tys_nu, tys_nu]; simp [tysObs, tysState, State.dirac_pr, procFiveTen]
    · rw [tys_nu, tys_paySum]; simp [tysObs, tysState, procFiveTen, Five10.val]
  · rw [tys_nu] at hpos; simp [tysObs, procFiveTen] at hpos

/-- **`C₀` is masked-calibrated (vacuity reading)**: at `d₅` via any full-support self-model (the
conditional on `O₅` is `δ_{(5,5)}` whatever `m`), at `d₁₀` vacuously (unreachable under every
`C₀[d₁₀ ↦ m]`, since the root plays five).
Source: [[decision-problems-v2]] Proposition 8 ("masked-calibrated for both"), read with A5
Kind: P
Fidelity: variant: null case read as vacuity (A5); v2's letter is refuted below -/
theorem tys_fiveTen_maskedOC : MaskedOC tysState tysObs procFiveTen toldYouSo := by
  intro d _
  cases d
  · refine Or.inl ⟨procFiveTen.deviate .five (FinDistr.uniform), ⟨_, fun a => FinDistr.uniform_w_pos a, rfl⟩,
      ?_, fun X => ?_, fun X _ _ => ?_⟩
    · rw [tys_nu]; simp [tysObs, Proc.deviate, procFiveTen, Fintype.card_pos]
    · rw [tys_nu, tys_nu]
      simp [tysObs, tysState, State.dirac_pr, Proc.deviate, procFiveTen]
    · rw [tys_nu, tys_paySum]
      simp [tysObs, tysState, Proc.deviate, procFiveTen, Five10.val] <;> split_ifs <;> ring
  · refine Or.inr ⟨rfl, fun C' hC' => ?_⟩
    obtain ⟨m, -, rfl⟩ := hC'
    rw [tys_nu]; simp [tysObs, Proc.deviate, procFiveTen, Function.update_of_ne]

/-- **E9: under the letter reading `C₀` is not masked-calibrated** — `d₁₀` has no admissible
self-model.
Source: `v2-amendments.md` E9 ("Proposition 8 (for `C₀` at `d_{10}`) … treat[s] such points as
vacuous"); E5 ("for `C₀` at `d_{10}` no self-model realizes `O_{10}`, so the claim needs the
vacuity reading")
Kind: N+
Fidelity: exact (v2's letter is `MaskedOCV … .LF .letter`) -/
theorem tys_fiveTen_not_masked_letter :
    ¬ MaskedOCV tysState tysObs procFiveTen toldYouSo .LF .letter := by
  intro h
  rcases h .ten (tys_queried _) with ⟨C', ⟨m, -, rfl⟩, hpos, -⟩ | ⟨h, -⟩
  · rw [tys_nu] at hpos
    simp [tysObs, Proc.deviate, procFiveTen, Function.update_of_ne] at hpos
  · cases h

/-! ## E5: Proposition 8 for `C* = (ten, ten)` -/

/-- `C*` is strictly calibrated: `ν = δ_{(10,10)}`.
Source: [[decision-problems-v2]] Proposition 8 ("For `C*` symmetrically with `δ_{(10,10)}`")
Kind: P -/
theorem tys_take10_strictOC : StrictOC tysState tysObs procTake10 toldYouSo := by
  intro d _ hpos
  cases d
  · rw [tys_nu] at hpos; simp [tysObs, procTake10] at hpos
  · refine ⟨fun X => ?_, fun X _ _ => ?_⟩
    · rw [tys_nu, tys_nu]; simp [tysObs, tysState, State.dirac_pr, procTake10]
    · rw [tys_nu, tys_paySum]; simp [tysObs, tysState, procTake10, Five10.val]

/-- **E5: `C*` is not LF-masked-calibrated at `d₁₀` under either reading**: every full-support
self-model `m` puts mass `m(5) > 0` on `(10,5)`, which the state denies; and `O₁₀` is realized
(`ν' = 1`), so the vacuity clause is unavailable.
Source: `v2-amendments.md` E5 ("For `C*` at `d_{10}` every full-support self-model gives
`ν(·∣O_{10}) = m(10)δ_{(10,10)} + m(5)δ_{(10,5)} ≠ δ_{(10,10)}`, so the official … Definition 9
fails"); [[decision-problems-v2]] Proposition 8 ("masked-calibrated for both"), refuted for `C*`
Kind: N+
Fidelity: exact -/
theorem tys_take10_not_masked_LF (r : NullReading) :
    ¬ MaskedOCAtV tysState tysObs procTake10 toldYouSo .LF r .ten := by
  rintro (⟨C', ⟨m, hm, rfl⟩, hpos, hcl, -⟩ | ⟨-, hnull⟩)
  · have := hcl {(.ten, .five)}
    simp only [tysState] at this
    rw [State.dirac_pr, tys_nu, tys_nu] at this
    simp [tysObs, Proc.deviate, procTake10, Function.update_of_ne] at this
    linarith [hm .five]
  · have := hnull (procTake10.deviate .ten FinDistr.uniform)
      ⟨_, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [tys_nu] at this
    simp [tysObs, Proc.deviate, procTake10, Function.update_of_ne] at this

/-- Hence **Proposition 8's "masked-calibrated for both" is false as stated** (under the official
LF variant, either reading) for `C*`.
Source: [[decision-problems-v2]] §7.1 Proposition 8 (line 227), refuted; `v2-amendments.md` E5
Kind: N+ -/
theorem tys_take10_not_maskedOCV (r : NullReading) :
    ¬ MaskedOCV tysState tysObs procTake10 toldYouSo .LF r :=
  fun h => tys_take10_not_masked_LF r (h .ten (tys_queried _))

/-- **The surviving neighbour: `C*` is LP-masked-calibrated** (plain self-models; `m = δ₁₀` at
`d₁₀`, `m = δ₅` at `d₅`).
Source: `v2-amendments.md` E5 ("only Appendix B's plain variant holds")
Kind: N+
Fidelity: exact -/
theorem tys_take10_masked_LP : MaskedOCV tysState tysObs procTake10 toldYouSo .LP .vacuity := by
  intro d _
  cases d
  · refine Or.inl ⟨procTake10.deviate .five (FinDistr.pure .five), ⟨_, rfl⟩, ?_, fun X => ?_,
      fun X _ _ => ?_⟩
    · rw [tys_nu]; simp [tysObs, Proc.deviate, procTake10]
    · rw [tys_nu, tys_nu]
      simp [tysObs, tysState, State.dirac_pr, Proc.deviate, procTake10]
    · rw [tys_nu, tys_paySum]
      simp [tysObs, tysState, Proc.deviate, procTake10, Five10.val]
  · refine Or.inl ⟨procTake10.deviate .ten (FinDistr.pure .ten), ⟨_, rfl⟩, ?_, fun X => ?_,
      fun X _ _ => ?_⟩
    · rw [tys_nu]; simp [tysObs, Proc.deviate, procTake10]
    · rw [tys_nu, tys_nu]
      simp [tysObs, tysState, State.dirac_pr, Proc.deviate, procTake10]
    · rw [tys_nu, tys_paySum]
      simp [tysObs, tysState, Proc.deviate, procTake10, Five10.val]

/-! ## The tremble polynomials on `toldYouSo` -/

/-- `nuPoly` on `toldYouSo` in terms of the tremble weights. Source: none: infrastructure. Kind: L -/
theorem tys_nuPoly (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    nuPoly C toldYouSo X =
      (if (Five10.five, Five10.five) ∈ X then trembleW C .five .five else 0) +
      (if (Five10.ten, Five10.ten) ∈ X then trembleW C .five .ten * trembleW C .ten .ten else 0) +
      (if (Five10.ten, Five10.five) ∈ X then trembleW C .five .ten * trembleW C .ten .five else 0) := by
  rw [nuPoly_eq_sum, tys_sum]
  simp [toldYouSo, leafLawPoly, world_decision]

/-- `payPoly` on `toldYouSo`. Source: none: infrastructure. Kind: L -/
theorem tys_payPoly (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    payPoly C toldYouSo X =
      (if (Five10.five, Five10.five) ∈ X then trembleW C .five .five * Polynomial.C 5 else 0) +
      (if (Five10.ten, Five10.ten) ∈ X then
        trembleW C .five .ten * trembleW C .ten .ten * Polynomial.C 10 else 0) +
      (if (Five10.ten, Five10.five) ∈ X then
        trembleW C .five .ten * trembleW C .ten .five * Polynomial.C 5 else 0) := by
  rw [payPoly_eq_sum, tys_sum]
  simp [toldYouSo, leafLawPoly, world_decision, payoff_decision]

/-- `|A_d| = 2` on `toldYouSo`. Source: none: infrastructure. Kind: L -/
theorem five10_card : (Fintype.card Five10 : ℚ) = 2 := by
  have : (Finset.univ : Finset Five10) = {.five, .ten} := by ext x; cases x <;> simp
  rw [Fintype.card, this, Finset.card_pair (by decide)]; norm_num

/-- The tremble weight of a deterministic procedure, played act: `1 + ε(½ − 1) = C 1 + C (−½) X`.
Source: none: infrastructure. Kind: L -/
theorem trembleW_ofFun_eq (π : (d : Five10) → Five10) (d : Five10) :
    trembleW (Proc.ofFun π : Proc Five10 (fun _ => Five10) ℚ) d (π d) =
      Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X := by
  simp only [trembleW, Proc.ofFun_w, five10_card, if_true]
  congr 2; norm_num

/-- The tremble weight of a deterministic procedure, unplayed act: `0 + ε/2 = C ½ * X`.
Source: none: infrastructure. Kind: L -/
theorem trembleW_ofFun_ne (π : (d : Five10) → Five10) (d a : Five10) (h : a ≠ π d) :
    trembleW (Proc.ofFun π : Proc Five10 (fun _ => Five10) ℚ) d a =
      Polynomial.C (1 / 2) * Polynomial.X := by
  simp only [trembleW, Proc.ofFun_w, five10_card, h, if_false, map_zero, zero_add, sub_zero]
  congr 2; norm_num

/-- Coefficients of `(C u X)(C v X)`. Source: none: infrastructure. Kind: L -/
theorem coeff_lin_lin (u v : ℚ) :
    ((Polynomial.C u * Polynomial.X) * (Polynomial.C v * Polynomial.X)).coeff 0 = 0 ∧
    ((Polynomial.C u * Polynomial.X) * (Polynomial.C v * Polynomial.X)).coeff 1 = 0 := by
  have e : (Polynomial.C u * Polynomial.X) * (Polynomial.C v * Polynomial.X) =
      Polynomial.C (u * v) * Polynomial.X ^ 2 := by rw [map_mul]; ring
  rw [e]
  constructor <;> simp only [Polynomial.coeff_C_mul_X_pow] <;> simp

/-- Coefficients of `(C u X)(C c + C d X)`. Source: none: infrastructure. Kind: L -/
theorem coeff_lin_affine (u c d : ℚ) :
    ((Polynomial.C u * Polynomial.X) * (Polynomial.C c + Polynomial.C d * Polynomial.X)).coeff 0 = 0 ∧
    ((Polynomial.C u * Polynomial.X) * (Polynomial.C c + Polynomial.C d * Polynomial.X)).coeff 1 =
      u * c := by
  have e : (Polynomial.C u * Polynomial.X) * (Polynomial.C c + Polynomial.C d * Polynomial.X) =
      Polynomial.C (u * c) * Polynomial.X + Polynomial.C (u * d) * Polynomial.X ^ 2 := by
    rw [map_mul, map_mul]; ring
  rw [e]
  constructor <;> simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow] <;> simp

/-- Coefficients of `C c + C d X`. Source: none: infrastructure. Kind: L -/
theorem coeff_aff (c d : ℚ) :
    (Polynomial.C c + Polynomial.C d * Polynomial.X).coeff 0 = c ∧
    (Polynomial.C c + Polynomial.C d * Polynomial.X).coeff 1 = d := by
  constructor <;> simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X] <;>
    simp

/-! ## Lemma 2's separation: `procTake5` with the state certain of `(10,10)` -/

/-- Under `procTake5^ε`, `nuPoly O₁₀` has order `1` with coefficient `½`;
`nuPoly (X ∩ O₁₀)` has constant coefficient `0` and coefficient `½·[(10,5) ∈ X]` at order `1`;
`payPoly (X ∩ O₁₀)` has coefficient `(5/2)·[(10,5) ∈ X]` at order `1`: the limiting conditional
given `O₁₀` is `δ_{(10,5)}`.
Source: [[decision-problems-v2]] Lemma 2 proof ("`ν_{B,C^ε}(· ∣ O_{10}) → δ_{(10,5)}`")
Kind: L -/
theorem tys_take5_coeffs :
    (nuPoly procTake5 toldYouSo (tysObs .ten)).coeff 0 = 0 ∧
    (nuPoly procTake5 toldYouSo (tysObs .ten)).coeff 1 = 1 / 2 ∧
    (∀ X : Finset TysW, (nuPoly procTake5 toldYouSo (X ∩ tysObs .ten)).coeff 0 = 0) ∧
    (∀ X : Finset TysW, (nuPoly procTake5 toldYouSo (X ∩ tysObs .ten)).coeff 1 =
      if (Five10.ten, Five10.five) ∈ X then 1 / 2 else 0) ∧
    (∀ X : Finset TysW, (payPoly procTake5 toldYouSo (X ∩ tysObs .ten)).coeff 1 =
      if (Five10.ten, Five10.five) ∈ X then 5 / 2 else 0) := by
  have hff : trembleW procTake5 .five .five = Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun _ => .five) .five
  have htf : trembleW procTake5 .ten .five = Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun _ => .five) .ten
  have hft : trembleW procTake5 .five .ten = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun _ => .five) .five .ten (by decide)
  have htt : trembleW procTake5 .ten .ten = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun _ => .five) .ten .ten (by decide)
  have hmemO : ((Five10.five, Five10.five) ∈ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ tysObs .ten ↔ True) ∧
      ((Five10.ten, Five10.five) ∈ tysObs .ten ↔ True) := by simp [tysObs]
  have hmem : ∀ X : Finset TysW, ((Five10.five, Five10.five) ∈ X ∩ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.ten) ∈ X) ∧
      ((Five10.ten, Five10.five) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.five) ∈ X) := by
    intro X; simp [tysObs]
  refine ⟨?_, ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO.1, hmemO.2.1, hmemO.2.2, if_false, if_true, zero_add]
    rw [Polynomial.coeff_add, (coeff_lin_lin _ _).1, (coeff_lin_affine _ _ _).1, add_zero]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO.1, hmemO.2.1, hmemO.2.2, if_false, if_true, zero_add]
    rw [Polynomial.coeff_add, (coeff_lin_lin _ _).2, (coeff_lin_affine _ _ _).2]
    norm_num
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [(coeff_lin_lin _ _).1, (coeff_lin_affine _ _ _).1,
      Polynomial.coeff_zero, add_zero]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [(coeff_lin_lin _ _).2, (coeff_lin_affine _ _ _).2,
      Polynomial.coeff_zero, add_zero, zero_add] <;> norm_num
  · rw [tys_payPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [Polynomial.coeff_mul_C, (coeff_lin_lin _ _).2,
      (coeff_lin_affine _ _ _).2, Polynomial.coeff_zero, add_zero, zero_add, zero_mul] <;> norm_num

/-- `nuPoly O₁₀` under `procTake5` has order `1`. Source: none: infrastructure. Kind: L -/
theorem tys_take5_deg_obs : (nuPoly procTake5 toldYouSo (tysObs .ten)).natTrailingDegree = 1 := by
  obtain ⟨h0, h1, -⟩ := tys_take5_coeffs
  exact natTrailingDegree_eq_of_coeff _ 1
    (fun j hj => by
      have : j = 0 := by omega
      subst this; exact h0)
    (by rw [h1]; norm_num)

/-- **Lemma 2's separation (T3(b))**: `procTake5` with the state certain of `(10,10)` at `d₁₀` is
strictly calibrated at `d₁₀` (vacuously: `ν(O₁₀) = 0`) and **not** limit-calibrated there:
`limitCond {(10,5)} O₁₀ = 1 ≠ 0 = P_{s₁₀}({(10,5)})` — the promised off-path behaviour is not
what near-tremble scrutiny reveals.
Source: [[decision-problems-v2]] §3.1 Lemma 2 ("the converse fails"); dp-core-2-052
Kind: N+
Fidelity: exact -/
theorem tys_take5_strict_not_limit :
    StrictOCAt tysState tysObs procTake5 toldYouSo .ten ∧
    ¬ LimitOCAt tysState tysObs procTake5 toldYouSo .ten := by
  constructor
  · intro hpos
    rw [tys_nu] at hpos; simp [tysObs, procTake5] at hpos
  · intro h
    obtain ⟨h0, h1, -, h4, -⟩ := tys_take5_coeffs
    have hne : nuPoly procTake5 toldYouSo (tysObs .ten) ≠ 0 := by
      intro hz; rw [hz, Polynomial.coeff_zero] at h1; norm_num at h1
    have := (h hne).1 {(.ten, .five)}
    rw [limitCond, tys_take5_deg_obs, h1, h4] at this
    simp only [tysState] at this
    rw [State.dirac_pr] at this
    simp at this

/-- **The non-witness (dp-core-2-052's pitfall)**: the state certain of `(10,5)` (with `V ≡ 5`)
*is* limit-calibrated at `d₁₀` for `procTake5` — so it cannot separate strict from limit
calibration.
Source: dp-core-2-052 ("A first attempt with `s'_{10}` certain of `(10,5)` fails as a witness
because that state *is* limit-calibrated")
Kind: N− (a check that the witness above is not an artifact: the natural alternative state fails
to separate) -/
theorem tys_take5_limitOC_at_ten_of_certain_105 :
    LimitOCAt (fun _ => State.dirac ((Five10.ten, Five10.five) : TysW) 5) tysObs procTake5 toldYouSo
      .ten := by
  intro _
  obtain ⟨h0, h1, h3, h4, h5⟩ := tys_take5_coeffs
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [limitCond, tys_take5_deg_obs, h1, h4, State.dirac_pr]
    split_ifs <;> norm_num
  · rw [limitCond, tys_take5_deg_obs, h1, h4] at hX
    have hmem : (Five10.ten, Five10.five) ∈ X := by
      by_contra hc; simp [hc] at hX
    have hdeg : (nuPoly procTake5 toldYouSo (X ∩ tysObs .ten)).natTrailingDegree = 1 :=
      natTrailingDegree_eq_of_coeff _ 1
        (fun j hj => by
          have : j = 0 := by omega
          subst this; exact h3 X)
        (by rw [h4 X, if_pos hmem]; norm_num)
    rw [hdeg, h4 X, h5 X, if_pos hmem, if_pos hmem, State.dirac_V]
    norm_num

/-! ## Proposition 8's limit clause for `C₀ = (five, ten)` -/

/-- Under `C₀^ε`: at `d₁₀`, `nuPoly O₁₀` has order `1` with coefficient `½`, `nuPoly (X ∩ O₁₀)`
constant coefficient `0` and coefficient `½·[(10,10) ∈ X]` at order `1`, `payPoly (X ∩ O₁₀)`
coefficient `5·[(10,10) ∈ X]` there — the limiting conditional is `δ_{(10,10)}`; at `d₅`,
`nuPoly (X ∩ O₅)` has constant coefficient `[(5,5) ∈ X]` and `payPoly` constant coefficient
`5·[(5,5) ∈ X]`.
Source: [[decision-problems-v2]] Proposition 8 ("`ν_ε(· ∣ O_{10}) → δ_{(10,10)}`")
Kind: L -/
theorem tys_fiveTen_coeffs :
    (nuPoly procFiveTen toldYouSo (tysObs .ten)).coeff 0 = 0 ∧
    (nuPoly procFiveTen toldYouSo (tysObs .ten)).coeff 1 = 1 / 2 ∧
    (∀ X : Finset TysW, (nuPoly procFiveTen toldYouSo (X ∩ tysObs .ten)).coeff 0 = 0) ∧
    (∀ X : Finset TysW, (nuPoly procFiveTen toldYouSo (X ∩ tysObs .ten)).coeff 1 =
      if (Five10.ten, Five10.ten) ∈ X then 1 / 2 else 0) ∧
    (∀ X : Finset TysW, (payPoly procFiveTen toldYouSo (X ∩ tysObs .ten)).coeff 1 =
      if (Five10.ten, Five10.ten) ∈ X then 5 else 0) ∧
    (∀ X : Finset TysW, (nuPoly procFiveTen toldYouSo (X ∩ tysObs .five)).coeff 0 =
      if (Five10.five, Five10.five) ∈ X then 1 else 0) ∧
    (∀ X : Finset TysW, (payPoly procFiveTen toldYouSo (X ∩ tysObs .five)).coeff 0 =
      if (Five10.five, Five10.five) ∈ X then 5 else 0) := by
  have hff : trembleW procFiveTen .five .five =
      Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun k => k) .five
  have htt : trembleW procFiveTen .ten .ten =
      Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun k => k) .ten
  have hft : trembleW procFiveTen .five .ten = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun k => k) .five .ten (by decide)
  have htf : trembleW procFiveTen .ten .five = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun k => k) .ten .five (by decide)
  have hmemO : ((Five10.five, Five10.five) ∈ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ tysObs .ten ↔ True) ∧
      ((Five10.ten, Five10.five) ∈ tysObs .ten ↔ True) := by simp [tysObs]
  have hmem : ∀ X : Finset TysW, ((Five10.five, Five10.five) ∈ X ∩ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.ten) ∈ X) ∧
      ((Five10.ten, Five10.five) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.five) ∈ X) := by
    intro X; simp [tysObs]
  have hmem5 : ∀ X : Finset TysW, ((Five10.five, Five10.five) ∈ X ∩ tysObs .five ↔
      (Five10.five, Five10.five) ∈ X) ∧
      ((Five10.ten, Five10.ten) ∈ X ∩ tysObs .five ↔ False) ∧
      ((Five10.ten, Five10.five) ∈ X ∩ tysObs .five ↔ False) := by
    intro X; simp [tysObs]
  refine ⟨?_, ?_, fun X => ?_, fun X => ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO.1, hmemO.2.1, hmemO.2.2, if_false, if_true, zero_add]
    rw [Polynomial.coeff_add, (coeff_lin_affine _ _ _).1, (coeff_lin_lin _ _).1, add_zero]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO.1, hmemO.2.1, hmemO.2.2, if_false, if_true, zero_add]
    rw [Polynomial.coeff_add, (coeff_lin_affine _ _ _).2, (coeff_lin_lin _ _).2]
    norm_num
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [(coeff_lin_lin _ _).1, (coeff_lin_affine _ _ _).1,
      Polynomial.coeff_zero, add_zero]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [(coeff_lin_lin _ _).2, (coeff_lin_affine _ _ _).2,
      Polynomial.coeff_zero, add_zero] <;> norm_num
  · rw [tys_payPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [Polynomial.coeff_mul_C, (coeff_lin_lin _ _).2,
      (coeff_lin_affine _ _ _).2, Polynomial.coeff_zero, add_zero, zero_mul] <;> norm_num
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem5 X
    simp only [h1, h2, h3, if_false, add_zero]
    split_ifs <;> simp only [(coeff_aff _ _).1, Polynomial.coeff_zero]
  · rw [tys_payPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem5 X
    simp only [h1, h2, h3, if_false, add_zero]
    split_ifs <;> simp only [Polynomial.coeff_mul_C, (coeff_aff _ _).1, Polynomial.coeff_zero] <;>
      norm_num

/-- **Proposition 8's limit clause for `C₀`**: `(five, ten)` is limit-calibrated with the
stipulated states (at `d₁₀` the limiting conditional is `δ_{(10,10)}`; at `d₅` the strict one).
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("Limit calibration: … `ν_ε(· ∣ O_{10}) →
δ_{(10,10)}`, matching `P_{s_{10}}`")
Kind: P
Fidelity: exact -/
theorem tys_fiveTen_limitOC : LimitOC tysState tysObs procFiveTen toldYouSo := by
  obtain ⟨h0, h1, h3, h4, h5, h6, h7⟩ := tys_fiveTen_coeffs
  intro d _ hne
  cases d
  · -- `d₅`: order 0, the strict conditional
    have hc : (nuPoly procFiveTen toldYouSo (tysObs .five)).coeff 0 = 1 := by
      have := h6 Finset.univ
      rw [Finset.univ_inter] at this
      rw [this]; simp
    have hdeg : (nuPoly procFiveTen toldYouSo (tysObs .five)).natTrailingDegree = 0 :=
      natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
        (by rw [hc]; exact one_ne_zero)
    refine ⟨fun X => ?_, fun X hX => ?_⟩
    · rw [limitCond, hdeg, hc, h6]
      simp only [tysState]
      rw [State.dirac_pr]; simp
    · rw [limitCond, hdeg, hc, h6] at hX
      have hmem : (Five10.five, Five10.five) ∈ X := by by_contra hc'; simp [hc'] at hX
      have hdeg' : (nuPoly procFiveTen toldYouSo (X ∩ tysObs .five)).natTrailingDegree = 0 :=
        natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
          (by rw [h6, if_pos hmem]; exact one_ne_zero)
      rw [hdeg', h6, h7, if_pos hmem, if_pos hmem]
      simp only [tysState, State.dirac_V, Five10.val]
      norm_num
  · -- `d₁₀`: order 1, the limiting conditional `δ_{(10,10)}`
    have hdeg : (nuPoly procFiveTen toldYouSo (tysObs .ten)).natTrailingDegree = 1 :=
      natTrailingDegree_eq_of_coeff _ 1
        (fun j hj => by
          have : j = 0 := by omega
          subst this; exact h0)
        (by rw [h1]; norm_num)
    refine ⟨fun X => ?_, fun X hX => ?_⟩
    · rw [limitCond, hdeg, h1, h4]
      simp only [tysState]
      rw [State.dirac_pr]
      split_ifs <;> norm_num
    · rw [limitCond, hdeg, h1, h4] at hX
      have hmem : (Five10.ten, Five10.ten) ∈ X := by by_contra hc; simp [hc] at hX
      have hdeg' : (nuPoly procFiveTen toldYouSo (X ∩ tysObs .ten)).natTrailingDegree = 1 :=
        natTrailingDegree_eq_of_coeff _ 1
          (fun j hj => by
            have : j = 0 := by omega
            subst this; exact h3 X)
          (by rw [h4 X, if_pos hmem]; norm_num)
      rw [hdeg', h4 X, h5 X, if_pos hmem, if_pos hmem]
      simp only [tysState, State.dirac_V, Five10.val]
      norm_num

/-! ## Proposition 8's limit clause for `C* = (ten, ten)` (repair round 1, audit N2) -/

/-- Coefficients of `(C c + C d X)(C c' + C d' X)`. Source: none: infrastructure. Kind: L -/
theorem coeff_aff_aff (c d c' d' : ℚ) :
    ((Polynomial.C c + Polynomial.C d * Polynomial.X) *
      (Polynomial.C c' + Polynomial.C d' * Polynomial.X)).coeff 0 = c * c' ∧
    ((Polynomial.C c + Polynomial.C d * Polynomial.X) *
      (Polynomial.C c' + Polynomial.C d' * Polynomial.X)).coeff 1 = c * d' + d * c' := by
  have e : (Polynomial.C c + Polynomial.C d * Polynomial.X) *
      (Polynomial.C c' + Polynomial.C d' * Polynomial.X) =
      Polynomial.C (c * c') + Polynomial.C (c * d' + d * c') * Polynomial.X +
        Polynomial.C (d * d') * Polynomial.X ^ 2 := by
    simp only [map_mul, map_add]; ring
  rw [e]
  constructor <;> simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow] <;> simp

/-- Coefficients of `(C c + C d X)(C u X)`. Source: none: infrastructure. Kind: L -/
theorem coeff_affine_lin (c d u : ℚ) :
    ((Polynomial.C c + Polynomial.C d * Polynomial.X) * (Polynomial.C u * Polynomial.X)).coeff 0
      = 0 ∧
    ((Polynomial.C c + Polynomial.C d * Polynomial.X) * (Polynomial.C u * Polynomial.X)).coeff 1
      = u * c := by
  rw [mul_comm]; exact coeff_lin_affine u c d

/-- Under `C*^ε`: at `d₁₀`, `nuPoly O₁₀` has constant coefficient `1`, `nuPoly (X ∩ O₁₀)` constant
coefficient `[(10,10) ∈ X]`, `payPoly (X ∩ O₁₀)` constant coefficient `10·[(10,10) ∈ X]` (order
`0`: the strict conditional); at `d₅`, `nuPoly O₅ = ε/2` (order `1`, coefficient `½`),
`nuPoly (X ∩ O₅)` has constant coefficient `0` and coefficient `½·[(5,5) ∈ X]` at order `1`,
`payPoly (X ∩ O₅)` coefficient `(5/2)·[(5,5) ∈ X]` there — the limiting conditional given `O₅`
is `δ_{(5,5)}`.
Source: [[decision-problems-v2]] Proposition 8 (limit clause for `C*`)
Kind: L -/
theorem tys_take10_coeffs :
    (nuPoly procTake10 toldYouSo (tysObs .ten)).coeff 0 = 1 ∧
    (∀ X : Finset TysW, (nuPoly procTake10 toldYouSo (X ∩ tysObs .ten)).coeff 0 =
      if (Five10.ten, Five10.ten) ∈ X then 1 else 0) ∧
    (∀ X : Finset TysW, (payPoly procTake10 toldYouSo (X ∩ tysObs .ten)).coeff 0 =
      if (Five10.ten, Five10.ten) ∈ X then 10 else 0) ∧
    (nuPoly procTake10 toldYouSo (tysObs .five)).coeff 0 = 0 ∧
    (nuPoly procTake10 toldYouSo (tysObs .five)).coeff 1 = 1 / 2 ∧
    (∀ X : Finset TysW, (nuPoly procTake10 toldYouSo (X ∩ tysObs .five)).coeff 0 = 0) ∧
    (∀ X : Finset TysW, (nuPoly procTake10 toldYouSo (X ∩ tysObs .five)).coeff 1 =
      if (Five10.five, Five10.five) ∈ X then 1 / 2 else 0) ∧
    (∀ X : Finset TysW, (payPoly procTake10 toldYouSo (X ∩ tysObs .five)).coeff 1 =
      if (Five10.five, Five10.five) ∈ X then 5 / 2 else 0) := by
  have hff : trembleW procTake10 .five .five = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun _ => .ten) .five .five (by decide)
  have hft : trembleW procTake10 .five .ten =
      Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun _ => .ten) .five
  have htt : trembleW procTake10 .ten .ten =
      Polynomial.C 1 + Polynomial.C (-1 / 2) * Polynomial.X :=
    trembleW_ofFun_eq (fun _ => .ten) .ten
  have htf : trembleW procTake10 .ten .five = Polynomial.C (1 / 2) * Polynomial.X :=
    trembleW_ofFun_ne (fun _ => .ten) .ten .five (by decide)
  have hmemO : ((Five10.five, Five10.five) ∈ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ tysObs .ten ↔ True) ∧
      ((Five10.ten, Five10.five) ∈ tysObs .ten ↔ True) := by simp [tysObs]
  have hmemO5 : ((Five10.five, Five10.five) ∈ tysObs .five ↔ True) ∧
      ((Five10.ten, Five10.ten) ∈ tysObs .five ↔ False) ∧
      ((Five10.ten, Five10.five) ∈ tysObs .five ↔ False) := by simp [tysObs]
  have hmem : ∀ X : Finset TysW, ((Five10.five, Five10.five) ∈ X ∩ tysObs .ten ↔ False) ∧
      ((Five10.ten, Five10.ten) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.ten) ∈ X) ∧
      ((Five10.ten, Five10.five) ∈ X ∩ tysObs .ten ↔ (Five10.ten, Five10.five) ∈ X) := by
    intro X; simp [tysObs]
  have hmem5 : ∀ X : Finset TysW, ((Five10.five, Five10.five) ∈ X ∩ tysObs .five ↔
      (Five10.five, Five10.five) ∈ X) ∧
      ((Five10.ten, Five10.ten) ∈ X ∩ tysObs .five ↔ False) ∧
      ((Five10.ten, Five10.five) ∈ X ∩ tysObs .five ↔ False) := by
    intro X; simp [tysObs]
  refine ⟨?_, fun X => ?_, fun X => ?_, ?_, ?_, fun X => ?_, fun X => ?_, fun X => ?_⟩
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO.1, hmemO.2.1, hmemO.2.2, if_false, if_true, zero_add]
    rw [Polynomial.coeff_add, (coeff_aff_aff _ _ _ _).1, (coeff_affine_lin _ _ _).1]
    norm_num
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [(coeff_aff_aff _ _ _ _).1, (coeff_affine_lin _ _ _).1,
      Polynomial.coeff_zero, add_zero, zero_add] <;> norm_num
  · rw [tys_payPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem X
    simp only [h1, h2, h3, if_false, zero_add]
    rw [Polynomial.coeff_add]
    split_ifs <;> simp only [Polynomial.coeff_mul_C, (coeff_aff_aff _ _ _ _).1,
      (coeff_affine_lin _ _ _).1, Polynomial.coeff_zero, add_zero, zero_add, zero_mul] <;>
      norm_num
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO5.1, hmemO5.2.1, hmemO5.2.2, if_false, if_true, add_zero]
    simp [Polynomial.coeff_C_mul_X]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    simp only [hmemO5.1, hmemO5.2.1, hmemO5.2.2, if_false, if_true, add_zero]
    simp [Polynomial.coeff_C_mul_X]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem5 X
    simp only [h1, h2, h3, if_false, add_zero]
    split_ifs <;> simp [Polynomial.coeff_C_mul_X]
  · rw [tys_nuPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem5 X
    simp only [h1, h2, h3, if_false, add_zero]
    split_ifs <;> simp [Polynomial.coeff_C_mul_X]
  · rw [tys_payPoly, hff, hft, htt, htf]
    obtain ⟨h1, h2, h3⟩ := hmem5 X
    simp only [h1, h2, h3, if_false, add_zero]
    split_ifs <;> simp [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul_X] <;> norm_num

/-- **Proposition 8's limit clause for `C*`**: `(ten, ten)` is limit-calibrated with the
stipulated states (at `d₅` — null for `C*` — the limiting conditional is `δ_{(5,5)}`, order `1`;
at `d₁₀` the strict one, order `0`). Completes the surviving neighbour of the E5 refutation row.
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("strictly, masked-, and limit-calibrated
for both")
Kind: P
Fidelity: exact -/
theorem tys_take10_limitOC : LimitOC tysState tysObs procTake10 toldYouSo := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := tys_take10_coeffs
  intro d _ _
  cases d
  · -- `d₅`: order 1, the limiting conditional `δ_{(5,5)}`
    have hdeg : (nuPoly procTake10 toldYouSo (tysObs .five)).natTrailingDegree = 1 :=
      natTrailingDegree_eq_of_coeff _ 1
        (fun j hj => by
          have : j = 0 := by omega
          subst this; exact h3)
        (by rw [h4]; norm_num)
    refine ⟨fun X => ?_, fun X hX => ?_⟩
    · rw [limitCond, hdeg, h4, h6]
      simp only [tysState]
      rw [State.dirac_pr]
      split_ifs <;> norm_num
    · rw [limitCond, hdeg, h4, h6] at hX
      have hmem : (Five10.five, Five10.five) ∈ X := by by_contra hc; simp [hc] at hX
      have hdeg' : (nuPoly procTake10 toldYouSo (X ∩ tysObs .five)).natTrailingDegree = 1 :=
        natTrailingDegree_eq_of_coeff _ 1
          (fun j hj => by
            have : j = 0 := by omega
            subst this; exact h5 X)
          (by rw [h6 X, if_pos hmem]; norm_num)
      rw [hdeg', h6 X, h7 X, if_pos hmem, if_pos hmem]
      simp only [tysState, State.dirac_V, Five10.val]
      norm_num
  · -- `d₁₀`: order 0, the strict conditional `δ_{(10,10)}`
    have hdeg : (nuPoly procTake10 toldYouSo (tysObs .ten)).natTrailingDegree = 0 :=
      natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
        (by rw [h0]; exact one_ne_zero)
    refine ⟨fun X => ?_, fun X hX => ?_⟩
    · rw [limitCond, hdeg, h0, h1]
      simp only [tysState]
      rw [State.dirac_pr]
      simp
    · rw [limitCond, hdeg, h0, h1] at hX
      have hmem : (Five10.ten, Five10.ten) ∈ X := by by_contra hc; simp [hc] at hX
      have hdeg' : (nuPoly procTake10 toldYouSo (X ∩ tysObs .ten)).natTrailingDegree = 0 :=
        natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
          (by rw [h1 X, if_pos hmem]; exact one_ne_zero)
      rw [hdeg', h1 X, h2 X, if_pos hmem, if_pos hmem]
      simp only [tysState, State.dirac_V, Five10.val]
      norm_num

end Cleanroom.Decision.DpCalibration
