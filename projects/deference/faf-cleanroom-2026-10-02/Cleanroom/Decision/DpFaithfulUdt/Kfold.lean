import Cleanroom.Decision.DpFaithfulUdt.Faithful
import Cleanroom.Decision.DpLocalOpt.Trees

/-!
# Faithful events under nesting (T7) and FP-8′'s interdefinability identities with their
provisos (T10), on the `k`-fold mugging

T7 and T10 of [[dp-faithful-udt-mandate]].

* **T10, general** (`firstperson.md` FP-8′): when every run meets `d` at most once (`#_d ≤ 1`),
  the per-run law of `C` is the `C(d)`-mixture of the per-run deviation laws —
  `μ_C(S ∧ occ(d)) = ∑_a C(d)(a) · μ_{C[d↦a]}(S ∧ occ(d))` (`mass_inter_occ_eq_sum_deviatePure`),
  likewise for the payoff masses (`paySum_occ_eq_sum_deviatePure`); conditioning on the recorded
  draw is the deviation (`mass_inter_drew_div`, FA-4 in conditional form, cited) and the draw's
  per-run probability is `C(d)(a)` (`mass_drew_div_occ`).
* **T10, provisos** (FP-9): on the 2-fold *concave* mugging under Definition 6 the mixture
  identity fails for the transfer event — `½ q₀ (2 − q₀) ≠ ½ q₀` for `q₀ ∈ (0,1)`
  (`kfold2_concave_mixture_fails`) — while on the 2-fold *linear* coupling it holds
  (`kfold2_linear_mixture`): `#_d ≤ 1` is sufficient, not necessary.
* **T7** (`faithful.md` FA-8): on the 2-fold concave mugging (worlds `Unit`, so leaf-sets are
  the events; the algebra compared is that of `(coin, r)`), with the full-support self-model
  `procQ q'`, **no leaf-set is law-faithful for refuse** (`kfold2_concave_no_refuse_faithful`):
  the deviation `δ_refuse` splits `½ : ½` between the `T`-refuse leaf and the `H`-leaf below two
  refusals, whose `C'`-masses are `(1−q')/2` and `(1−q')²/2`. The impossibility is not an artefact
  of the predicate: a leaf-set *is* faithful for pay (`kfold2_concave_pay_faithful`), and under
  the linear coupling faithful sets exist for both acts (`kfold2_linear_pay_faithful`,
  `kfold2_linear_refuse_faithful`).

The tree is `dp-local-opt`'s `kfold 2 x y b hb` (ten leaves: two on the `T` branch, eight on the
`H` branch — each of the four draw pairs ends in a chance node with a transfer leaf and a
no-transfer leaf; a chance leaf of weight `0` is still a leaf, and is handled as such).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### T10, general: FP-8′'s identities when `#_d ≤ 1` -/

section interdef

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The per-run mixture identity, weighted form**: when `#_d ≤ 1` on every run, for every
weight `f` on leaves, `∑_{ℓ ∈ S ∧ occ(d)} μ_C(ℓ) f(ℓ) = ∑_a C(d)(a) ∑_{ℓ ∈ S ∧ occ(d)} μ_{C[d↦a]}(ℓ) f(ℓ)`
— on an `occ(d)`-leaf, `μ_C(ℓ) = C(d)(a_ℓ) · μ_{C[d↦a_ℓ]}(ℓ)` for its unique draw `a_ℓ` and
`μ_{C[d↦b]}(ℓ) = 0` for `b ≠ a_ℓ`.
Source: `firstperson.md` FP-8′ ("on an `occ(d)`-leaf `μ_C(ℓ) = w(ℓ) m(a_ℓ)` … `μ_{C[d↦a]}(ℓ) =
w(ℓ) 1[a_ℓ = a]` … condition and sum")
Kind: P
Fidelity: exact
Hyps: (a) `∀ ℓ, count d B ℓ ≤ 1` (FP-8′'s hypothesis (a)) -/
theorem sum_occ_eq_sum_deviatePure (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves)
    (f : B.Leaves → K) :
    ∑ ℓ ∈ S ∩ occ d B, leafLaw C B ℓ * f ℓ =
      ∑ a, (C d).w a * ∑ ℓ ∈ S ∩ occ d B, leafLaw (C.deviatePure d a) B ℓ * f ℓ := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_inter, mem_occ] at hℓ
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, (⟨d, a₀⟩ : Σ d, acts d) ∈ draws B ℓ := by
    by_cases h : (⟨d, Classical.arbitrary (acts d)⟩ : Σ d, acts d) ∈ draws B ℓ
    · exact ⟨_, h⟩
    · obtain ⟨b, -, hb⟩ := exists_other_draw_of_not_drew B d _ ℓ hℓ.2 h
      exact ⟨b, hb⟩
  rw [Finset.sum_eq_single a₀]
  · rw [leafLaw_eq_mul_deviatePure_of_drew C B d a₀ ℓ ha₀ (hfair ℓ)]; ring
  · intro b _ hb
    rw [leafLaw_deviatePure_eq_zero_of_other C B d b a₀ (Ne.symm hb) ℓ ha₀]; ring
  · intro h; exact absurd (Finset.mem_univ a₀) h

/-- **FP-8′(2) — the per-run law is the `C(d)`-mixture of the per-run deviation laws**:
`μ_C(S ∧ occ(d)) = ∑_a C(d)(a) · μ_{C[d↦a]}(S ∧ occ(d))` when `#_d ≤ 1` on every run.
Source: `firstperson.md` FP-8′ ("(2) `∑_a m(a) λ_*μ_{C[d↦a]}(· ∣ occ(d)) = P^{sl}_{s_d}`"), FP-9
("the mixture identity (2)"); dp-cf-112
Kind: P
Fidelity: exact (multiplicative form; dividing by `μ(occ(d))`, deviation-invariant, gives the
conditional form)
Hyps: (a) `∀ ℓ, count d B ℓ ≤ 1` -/
theorem mass_inter_occ_eq_sum_deviatePure (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves) :
    mass C B (S ∩ occ d B) = ∑ a, (C d).w a * mass (C.deviatePure d a) B (S ∩ occ d B) := by
  have := sum_occ_eq_sum_deviatePure C B d hfair S fun _ => 1
  simpa [mass] using this

/-- **FP-8′(3), payoff form**: the payoff mass on `S ∧ occ(d)` is the `C(d)`-mixture of the
deviations' payoff masses when `#_d ≤ 1`.
Source: `firstperson.md` FP-8′ ("(3) `V^a(X) = V^{sl}_{s_d}(X ∧ ρ_d(a))`", summed)
Kind: P
Fidelity: exact
Hyps: (a) `∀ ℓ, count d B ℓ ≤ 1` -/
theorem paySum_occ_eq_sum_deviatePure (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves) :
    ∑ ℓ ∈ S ∩ occ d B, leafLaw C B ℓ * payoff B ℓ =
      ∑ a, (C d).w a * ∑ ℓ ∈ S ∩ occ d B, leafLaw (C.deviatePure d a) B ℓ * payoff B ℓ :=
  sum_occ_eq_sum_deviatePure C B d hfair S (payoff B)

/-- **FP-8′(1) — conditioning the per-run law on the recorded draw is the per-run deviation**:
`μ_C(S ∣ drew d a) = μ_{C[d↦a]}(S ∣ occ(d))` when `#_d ≤ 1` — `dp-core-tree`'s
`disposition_faithful` (FA-4) in conditional form.
Source: `firstperson.md` FP-8′ ("(1) `P^{sl}_{s_d}(· ∣ ρ_d(a)) = λ_*μ_{C[d↦a]}(· ∣ occ(d))`");
`dp-core-tree` `disposition_faithful`
Kind: L
Fidelity: exact
Hyps: (a) `∀ ℓ, count d B ℓ ≤ 1`; (a) both conditioning events positive -/
theorem mass_inter_drew_div (a : acts d) (hfair : ∀ ℓ, count d B ℓ ≤ 1) (S : Finset B.Leaves)
    (hdrew : 0 < mass C B (drew d a B)) (hocc : 0 < mass (C.deviatePure d a) B (occ d B)) :
    mass C B (S ∩ drew d a B) / mass C B (drew d a B) =
      mass (C.deviatePure d a) B (S ∩ occ d B) / mass (C.deviatePure d a) B (occ d B) := by
  rw [div_eq_div_iff hdrew.ne' hocc.ne']
  exact disposition_faithful C B d a hfair S

/-- **FP-8′, `m = P^{sl}_{s_d}(ρ_d(·))`**: the per-run probability of the recorded draw `a` is
`C(d)(a)` when `#_d ≤ 1`.
Source: `firstperson.md` FP-8′ ("`m = P^{sl}_{s_d}(ρ_d(·))`")
Kind: L
Fidelity: exact
Hyps: (a) `∀ ℓ, count d B ℓ ≤ 1`; (a) `0 < μ_C(occ(d))` -/
theorem mass_drew_div_occ (a : acts d) (hfair : ∀ ℓ, count d B ℓ ≤ 1)
    (hocc : 0 < mass C B (occ d B)) :
    mass C B (drew d a B) / mass C B (occ d B) = (C d).w a := by
  rw [div_eq_iff hocc.ne']
  have h1 := mass_inter_drew C B d a hfair Finset.univ
  have h2 := mass_deviatePure_inter_occ C B d a hfair Finset.univ
  simp only [Finset.univ_inter] at h1 h2
  rw [h1, ← h2, Proc.deviatePure, occurrence_constancy]

end interdef

/-! ### The 2-fold mugging: its ten leaves -/

section kfold2

variable (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)

/-- The `T`-branch leaf of the 2-fold mugging below the real draw `act`.
Source: `repair/seeds.md` SE-13 (the `T` branch)
Kind: D -/
def tLeaf : Act2 → (kfold 2 x y b hb).Leaves
  | .a => ⟨0, .a, ()⟩
  | .b => ⟨0, .b, ()⟩

/-- The `H`-branch leaf of the 2-fold mugging below the simulated draws `a₁, a₂` and the chance
index `i` (`0` = transfer `y`, `1` = no transfer).
Source: `repair/seeds.md` SE-13 (the `H` branch)
Kind: D -/
def hLeaf : Act2 → Act2 → Fin 2 → (kfold 2 x y b hb).Leaves
  | .a, .a, 0 => ⟨1, .a, .a, 0, ()⟩
  | .a, .a, 1 => ⟨1, .a, .a, 1, ()⟩
  | .a, .b, 0 => ⟨1, .a, .b, 0, ()⟩
  | .a, .b, 1 => ⟨1, .a, .b, 1, ()⟩
  | .b, .a, 0 => ⟨1, .b, .a, 0, ()⟩
  | .b, .a, 1 => ⟨1, .b, .a, 1, ()⟩
  | .b, .b, 0 => ⟨1, .b, .b, 0, ()⟩
  | .b, .b, 1 => ⟨1, .b, .b, 1, ()⟩

/-- The coin of a run of the 2-fold mugging (`0` = `T`, `1` = `H`).
Source: `faithful.md` FA-8 (the `(T/H, ·)` atoms)
Kind: D -/
def coinOf : (kfold 2 x y b hb).Leaves → Fin 2
  | ⟨i, _⟩ => i

/-- **The labelling `(coin, r)` of the 2-fold mugging's runs**: the algebra `σ(coin, r)` on which
FA-8's faithfulness is assessed (the world type is `Unit`, so `(λ, r)` would see only `r`; the
coin is the coordinate FA-8's atoms carry).
Source: `faithful.md` FA-8 ("the only `(H,⊥,0)` leaf"); mandate T7 ("`(coin, r)` for the `k`-fold
muggings whose world type is `Unit`")
Kind: D -/
def kfLab (ℓ : (kfold 2 x y b hb).Leaves) : Fin 2 × ℚ := (coinOf x y b hb ℓ, payoff _ ℓ)

/-- The number of paying draws contributed by one simulated draw. Source: none: infrastructure.
Kind: D -/
def payCount : Act2 → ℕ
  | .a => 1
  | .b => 0

/-- Summing over the leaves of the 2-fold mugging. Source: none: infrastructure. Kind: L -/
theorem kfold2_sum (f : (kfold 2 x y b hb).Leaves → ℚ) :
    ∑ ℓ, f ℓ = (f (tLeaf x y b hb .a) + f (tLeaf x y b hb .b)) +
      ∑ a₁ : Act2, ∑ a₂ : Act2, ∑ i : Fin 2, f (hLeaf x y b hb a₁ a₂ i) := by
  refine (sum_leaves_chance f).trans ?_
  rw [Fin.sum_univ_two]
  congr 1
  · refine (sum_leaves_decision _).trans ?_
    rw [Act2.sum_univ]
    exact congrArg₂ (· + ·) (Tree.sum_leaves_leaf _ _ _) (Tree.sum_leaves_leaf _ _ _)
  · refine (sum_leaves_decision _).trans ?_
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    cases a₁ <;> refine (sum_leaves_decision _).trans ?_ <;>
      refine Finset.sum_congr rfl fun a₂ _ => ?_ <;>
      cases a₂ <;> refine (sum_leaves_chance _).trans ?_ <;>
      rw [Fin.sum_univ_two, Fin.sum_univ_two] <;>
      exact congrArg₂ (· + ·) (Tree.sum_leaves_leaf _ _ _) (Tree.sum_leaves_leaf _ _ _)

/-- Every run of the 2-fold mugging meets `d`: `occ(d) = ⊤`. Source: none: infrastructure.
Kind: L -/
theorem kfold2_occ : occ () (kfold 2 x y b hb) = Finset.univ := by
  refine Finset.eq_univ_of_forall fun ℓ => ?_
  rw [mem_occ]
  rcases ℓ with ⟨⟨_ | _ | n, hi⟩, ℓ⟩
  · rcases ℓ with ⟨a, ℓ⟩
    cases a <;> cases ℓ <;> simp [kfold]
  · rcases ℓ with ⟨a₁, ℓ⟩
    cases a₁ <;> rcases ℓ with ⟨a₂, ℓ⟩ <;> cases a₂ <;> rcases ℓ with ⟨⟨_ | _ | m, hm⟩, ℓ⟩ <;>
      first | omega | (cases ℓ; simp [kfold, kfoldH])
  · omega

/-- The 2-fold mugging is nested: its `H`-runs meet `d` twice. Source: `faithful.md` FA-8
("nested fibers"). Kind: L -/
theorem kfold2_count_two : count () (kfold 2 x y b hb) (hLeaf x y b hb .a .a 0) = 2 := rfl

/-- The draws of a `T` leaf. Source: none: infrastructure. Kind: L -/
theorem draws_tLeaf (act : Act2) :
    draws (kfold 2 x y b hb) (tLeaf x y b hb act) = [⟨(), act⟩] := by
  cases act <;> rfl

/-- The draws of an `H` leaf. Source: none: infrastructure. Kind: L -/
theorem draws_hLeaf (a₁ a₂ : Act2) (i : Fin 2) :
    draws (kfold 2 x y b hb) (hLeaf x y b hb a₁ a₂ i) = [⟨(), a₁⟩, ⟨(), a₂⟩] := by
  revert i
  rw [Fin.forall_fin_two]
  cases a₁ <;> cases a₂ <;> exact ⟨rfl, rfl⟩

/-- The law of a `T` leaf: `½ C(d)(act)`. Source: none: infrastructure. Kind: L -/
theorem tLeaf_leafLaw (C : Proc Unit (fun _ => Act2) ℚ) (act : Act2) :
    leafLaw C (kfold 2 x y b hb) (tLeaf x y b hb act) = 1 / 2 * (C ()).w act := by
  cases act <;> simp [tLeaf, kfold, FinDistr.fair, FinDistr.coin]

/-- The law of an `H` leaf: `½ C(d)(a₁) C(d)(a₂) · (b_j or 1 − b_j)`, `j` the number of paying
draws. Source: none: infrastructure. Kind: L -/
theorem hLeaf_leafLaw (C : Proc Unit (fun _ => Act2) ℚ) (a₁ a₂ : Act2) (i : Fin 2) :
    leafLaw C (kfold 2 x y b hb) (hLeaf x y b hb a₁ a₂ i) =
      1 / 2 * (C ()).w a₁ * (C ()).w a₂ *
        (if i = 0 then b (payCount a₁ + payCount a₂) else 1 - b (payCount a₁ + payCount a₂)) := by
  revert i
  rw [Fin.forall_fin_two]
  cases a₁ <;> cases a₂ <;> constructor <;>
    simp [hLeaf, kfold, kfoldH, payCount, FinDistr.fair, FinDistr.coin] <;> try ring

/-- The label of a `T` leaf. Source: none: infrastructure. Kind: L -/
theorem kfLab_tLeaf (act : Act2) :
    kfLab x y b hb (tLeaf x y b hb act) = (0, if act = .a then -x else 0) := by
  cases act <;> rfl

/-- The label of an `H` leaf. Source: none: infrastructure. Kind: L -/
theorem kfLab_hLeaf (a₁ a₂ : Act2) (i : Fin 2) :
    kfLab x y b hb (hLeaf x y b hb a₁ a₂ i) = (1, if i = 0 then y else 0) := by
  revert i
  rw [Fin.forall_fin_two]
  cases a₁ <;> cases a₂ <;> exact ⟨rfl, rfl⟩

/-- `μ_C(S ∩ T)` as a sum of indicators over all leaves. Source: none: infrastructure. Kind: L -/
theorem mass_inter_eq_sum_ite (C : Proc ι acts K) (B : Tree Ω ι acts K) (S T : Finset B.Leaves) :
    mass C B (S ∩ T) = ∑ ℓ, if ℓ ∈ S ∧ ℓ ∈ T then leafLaw C B ℓ else 0 := by
  unfold mass
  rw [← Finset.sum_filter]
  congr 1
  ext ℓ
  simp

/-- **The mass of a leaf-set `E` on the 2-fold mugging**, as a closed form over the ten leaves.
Source: none: infrastructure
Kind: L -/
theorem kfold2_mass (C : Proc Unit (fun _ => Act2) ℚ) (E : Finset (kfold 2 x y b hb).Leaves) :
    mass C (kfold 2 x y b hb) E =
      ((if tLeaf x y b hb .a ∈ E then 1 / 2 * (C ()).w .a else 0) +
        (if tLeaf x y b hb .b ∈ E then 1 / 2 * (C ()).w .b else 0)) +
      ∑ a₁ : Act2, ∑ a₂ : Act2,
        ((if hLeaf x y b hb a₁ a₂ 0 ∈ E then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * b (payCount a₁ + payCount a₂) else 0) +
          (if hLeaf x y b hb a₁ a₂ 1 ∈ E then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * (1 - b (payCount a₁ + payCount a₂)) else 0)) := by
  rw [← Finset.univ_inter E, mass_inter_eq_sum_ite, kfold2_sum]
  simp only [Finset.mem_univ, true_and, tLeaf_leafLaw, hLeaf_leafLaw, Fin.sum_univ_two]
  simp

/-- **The mass of `(coin, r) ∈ X` within a leaf-set `E` on the 2-fold mugging**, as a closed form
over the ten leaves.
Source: none: infrastructure
Kind: L -/
theorem kfold2_mass_labEv_inter (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset (Fin 2 × ℚ))
    (E : Finset (kfold 2 x y b hb).Leaves) :
    mass C (kfold 2 x y b hb) (labEv _ (kfLab x y b hb) X ∩ E) =
      ((if ((0 : Fin 2), -x) ∈ X ∧ tLeaf x y b hb .a ∈ E then 1 / 2 * (C ()).w .a else 0) +
        (if ((0 : Fin 2), (0 : ℚ)) ∈ X ∧ tLeaf x y b hb .b ∈ E then 1 / 2 * (C ()).w .b else 0)) +
      ∑ a₁ : Act2, ∑ a₂ : Act2,
        ((if ((1 : Fin 2), y) ∈ X ∧ hLeaf x y b hb a₁ a₂ 0 ∈ E then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * b (payCount a₁ + payCount a₂) else 0) +
          (if ((1 : Fin 2), (0 : ℚ)) ∈ X ∧ hLeaf x y b hb a₁ a₂ 1 ∈ E then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * (1 - b (payCount a₁ + payCount a₂)) else 0)) := by
  rw [mass_inter_eq_sum_ite, kfold2_sum]
  simp only [mem_labEv, kfLab_tLeaf, kfLab_hLeaf, tLeaf_leafLaw, hLeaf_leafLaw, Fin.sum_univ_two]
  simp

/-- The mass of `(coin, r) ∈ X` on the 2-fold mugging. Source: none: infrastructure. Kind: L -/
theorem kfold2_mass_labEv (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset (Fin 2 × ℚ)) :
    mass C (kfold 2 x y b hb) (labEv _ (kfLab x y b hb) X) =
      ((if ((0 : Fin 2), -x) ∈ X then 1 / 2 * (C ()).w .a else 0) +
        (if ((0 : Fin 2), (0 : ℚ)) ∈ X then 1 / 2 * (C ()).w .b else 0)) +
      ∑ a₁ : Act2, ∑ a₂ : Act2,
        ((if ((1 : Fin 2), y) ∈ X then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * b (payCount a₁ + payCount a₂) else 0) +
          (if ((1 : Fin 2), (0 : ℚ)) ∈ X then
            1 / 2 * (C ()).w a₁ * (C ()).w a₂ * (1 - b (payCount a₁ + payCount a₂)) else 0)) := by
  rw [← Finset.inter_univ (labEv _ (kfLab x y b hb) X), kfold2_mass_labEv_inter]
  simp only [Finset.mem_univ, and_true]

/-- The transfer event `{r = y}` of the 2-fold mugging (the four transfer leaves, for `y ≠ 0`),
FP-9's `transfer = 1`.
Source: `firstperson.md` FP-9 ("`P^{sl}(transfer = 1)`")
Kind: D -/
def transferE : Finset (kfold 2 x y b hb).Leaves :=
  labEv _ (kfLab x y b hb) {((1 : Fin 2), y)}

/-- The `(1 : Fin 2) ≠ 0` and `(0 : Fin 2) ≠ 1` facts simp needs. Source: none: infrastructure.
Kind: L -/
theorem fin2_facts : ((1 : Fin 2) ≠ 0) ∧ ((0 : Fin 2) ≠ 1) := by decide

/-- The transfer event is in `occ(d)` already. Source: none: infrastructure. Kind: L -/
theorem transferE_inter_occ :
    transferE x y b hb ∩ occ () (kfold 2 x y b hb) = transferE x y b hb := by
  rw [kfold2_occ, Finset.inter_univ]

end kfold2

/-! ### The concave coupling: `b_j = 1[j ≥ 1]` -/

section concave

variable (x y : ℚ) (q' : ℚ) (h0 : 0 < q') (h1 : q' < 1)

/-- The 2-fold concave mugging. Source: `faithful.md` FA-8 ("`k=2` concave mugging
(`b_j = 1[j≥1]`)"). Kind: D -/
abbrev kf2c : Tree Unit Unit (fun _ => Act2) ℚ := kfold 2 x y concaveB concaveB_bounds

/-- The concave coupling's three values. Source: none: infrastructure. Kind: L -/
theorem concaveB_vals : concaveB 0 = 0 ∧ concaveB 1 = 1 ∧ concaveB 2 = 1 := by
  simp [concaveB]

/-- **T7(a) — FA-8: no leaf-set is law-faithful for refuse on the 2-fold concave mugging** under
Definition 6, for every full-support self-model `q' ∈ (0,1)` (algebra `σ(coin, r)`; `x, y > 0`
so that the payoff classes `−x`, `0`, `y` are distinct). The deviation `δ_refuse` puts `½` on
`(T, refuse)` and `½` on the no-transfer leaf below two refusals; a faithful `E` would need both
in `E` with `C'`-masses in the ratio `1 : 1`, but they are `(1−q')/2` and `(1−q')²/2`.
Source: `faithful.md` FA-8 ("exhaustive search over `2^6` leaf-sets finds faithful sets for pay
and **none for refuse** — the only `(H,⊥,0)` leaf has mass `(1−q')²/2` against `(1−q')/2`, equal
only at `q' ∈ {0,1}`"); dp-cf-2-006
Kind: P
Fidelity: exact (Definition 6; the per-run form of `LeafLawFaithfulWrt` is the unconditioned one
here since `occ(d) = ⊤`)
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1` -/
theorem kfold2_concave_no_refuse_faithful (hx : 0 < x) (hy : 0 < y)
    (E : Finset (kf2c x y).Leaves) :
    ¬ LeafLawFaithfulWrt (kf2c x y) (kfLab x y concaveB concaveB_bounds) (procQ q' h0.le h1.le)
      () .b E := by
  rintro ⟨hpos, hX⟩
  have hocc := kfold2_occ x y concaveB concaveB_bounds
  have hA := hX {((0 : Fin 2), (0 : ℚ))}
  have hB := hX {((1 : Fin 2), (0 : ℚ))}
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter,
    kfold2_mass_labEv] at hA hB
  obtain ⟨c0, c1, c2⟩ := concaveB_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  simp only [Act2.sum_univ, payCount, c0, c1, c2, procQ, FinDistr.act2_a, FinDistr.act2_b,
    Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w] at hA hB
  simp [hx.ne, hx.ne', hy.ne, hy.ne', f10, f01] at hA hB
  by_cases hT : tLeaf x y concaveB concaveB_bounds .b ∈ E
  · by_cases hH : hLeaf x y concaveB concaveB_bounds .b .b 1 ∈ E
    · simp [hT, hH] at hA hB
      nlinarith [mul_pos h0 (sub_pos.mpr h1)]
    · simp [hT, hH] at hA hB
      linarith
  · simp [hT] at hA
    linarith

/-- The pay-faithful set on the 2-fold concave mugging: the `T`-pay leaf and the transfer leaves
whose draws are not `(refuse, pay)`. (Not all transfer leaves: under the concave coupling
`(refuse, pay)` also transfers, and including it would give the `H` side `C'`-mass
`½ q'(2 − q')` against the `T` side's `½ q'`; excluding `(pay, refuse)` instead works equally —
the faithful set is *not* unique here, unlike on `B₁`.)
Source: `faithful.md` FA-8 ("finds faithful sets for pay")
Kind: D -/
def concavePayE : Finset (kf2c x y).Leaves :=
  (labEv _ (kfLab x y concaveB concaveB_bounds) {((0 : Fin 2), -x), ((1 : Fin 2), y)}).filter
    fun ℓ => draws _ ℓ ≠ [⟨(), Act2.b⟩, ⟨(), Act2.a⟩]

/-- **T7(b) — a leaf-set law-faithful for pay exists on the 2-fold concave mugging** (the
non-vacuity check of T7(a): the predicate is inhabited for the other act).
Source: `faithful.md` FA-8 ("finds faithful sets for pay")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1` -/
theorem kfold2_concave_pay_faithful (hx : 0 < x) (hy : 0 < y) :
    LeafLawFaithfulWrt (kf2c x y) (kfLab x y concaveB concaveB_bounds) (procQ q' h0.le h1.le)
      () .a (concavePayE x y) := by
  have hocc := kfold2_occ x y concaveB concaveB_bounds
  obtain ⟨c0, c1, c2⟩ := concaveB_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kf2c x y) (concavePayE x y) = q' := by
    rw [kfold2_mass]
    simp [concavePayE, kfLab_tLeaf, kfLab_hLeaf, draws_tLeaf, draws_hLeaf, Act2.sum_univ,
      payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; exact h0, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [concavePayE, kfLab_tLeaf, kfLab_hLeaf, draws_tLeaf, draws_hLeaf, Act2.sum_univ,
    payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure,
    FinDistr.pure_w]
  split_ifs <;> ring

/-- **T10, the proviso is needed (FP-9)**: on the 2-fold concave mugging under Definition 6, with
the self-model `q₀ ∈ (0,1)`, the mixture identity fails for the transfer event:
`μ_C(transfer) = ½ q₀ (2 − q₀)` while `∑_a C(d)(a) μ_{C[d↦a]}(transfer) = ½ q₀`.
Source: `firstperson.md` FP-9 ("2-fold *concave* mugging under Def 6: `P^{sl}(transfer=1) =
½ q₀(2−q₀) ≠ ½ q₀` (mixture identity (2) fails)"); dp-cf-112
Kind: N−
Fidelity: exact (the hypothesis `#_d ≤ 1` of `mass_inter_occ_eq_sum_deviatePure` fails here:
`kfold2_count_two`)
Hyps: (a) `0 < y` (so the transfer event is the payoff class `y`); (a) `0 < q₀ < 1` -/
theorem kfold2_concave_mixture_fails (hy : 0 < y) :
    mass (procQ q' h0.le h1.le) (kf2c x y) (transferE x y concaveB concaveB_bounds ∩ occ () _) =
        1 / 2 * q' * (2 - q') ∧
      (∑ a, (procQ q' h0.le h1.le ()).w a *
        mass ((procQ q' h0.le h1.le).deviatePure () a) (kf2c x y)
          (transferE x y concaveB concaveB_bounds ∩ occ () _)) = 1 / 2 * q' ∧
      mass (procQ q' h0.le h1.le) (kf2c x y) (transferE x y concaveB concaveB_bounds ∩ occ () _) ≠
        ∑ a, (procQ q' h0.le h1.le ()).w a *
          mass ((procQ q' h0.le h1.le).deviatePure () a) (kf2c x y)
            (transferE x y concaveB concaveB_bounds ∩ occ () _) := by
  obtain ⟨c0, c1, c2⟩ := concaveB_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have key : ∀ C : Proc Unit (fun _ => Act2) ℚ,
      mass C (kf2c x y) (transferE x y concaveB concaveB_bounds ∩ occ () _) =
        1 / 2 * (C ()).w .a * (C ()).w .a + 1 / 2 * (C ()).w .a * (C ()).w .b +
          1 / 2 * (C ()).w .b * (C ()).w .a := by
    intro C
    rw [transferE_inter_occ, transferE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, c0, c1, c2, f10, f01, hy.ne, hy.ne'] <;> ring
  have hL : mass (procQ q' h0.le h1.le) (kf2c x y)
      (transferE x y concaveB concaveB_bounds ∩ occ () _) = 1 / 2 * q' * (2 - q') := by
    rw [key]; simp [procQ]; ring
  have hR : (∑ a, (procQ q' h0.le h1.le ()).w a *
      mass ((procQ q' h0.le h1.le).deviatePure () a) (kf2c x y)
        (transferE x y concaveB concaveB_bounds ∩ occ () _)) = 1 / 2 * q' := by
    rw [Act2.sum_univ, key, key]
    simp [procQ, Proc.deviatePure, FinDistr.pure_w] <;> ring
  refine ⟨hL, hR, ?_⟩
  rw [hL, hR]
  intro h
  nlinarith [mul_pos h0 (sub_pos.mpr h1)]

end concave

/-! ### The linear coupling `b_j = j/2` -/

section linear

variable (x y : ℚ) (q' : ℚ) (h0 : 0 < q') (h1 : q' < 1)

/-- The 2-fold linear mugging. Source: `faithful.md` FA-8 ("`k=2` linear coupling"). Kind: D -/
abbrev kf2l : Tree Unit Unit (fun _ => Act2) ℚ := kfold 2 x y (linearB 2) (linearB_bounds 2)

/-- The linear coupling's three values at `k = 2`. Source: none: infrastructure. Kind: L -/
theorem linearB2_vals : linearB 2 0 = 0 ∧ linearB 2 1 = 1 / 2 ∧ linearB 2 2 = 1 := by
  simp [linearB] <;> norm_num

/-- **T10, the proviso is not necessary (FP-9)**: on the 2-fold *linear* mugging the mixture
identity holds for the transfer event under every self-model, although the tree is nested —
its world law is affine in the pay rate.
Source: `firstperson.md` FP-9 ("the 2-fold *linear* coupling passes even under Def 6 because its
world-law is affine in `m` (so (a)/(b) are not necessary)")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < y` -/
theorem kfold2_linear_mixture (hy : 0 < y) (C : Proc Unit (fun _ => Act2) ℚ) :
    mass C (kf2l x y) (transferE x y (linearB 2) (linearB_bounds 2) ∩ occ () _) =
      ∑ a, (C ()).w a * mass (C.deviatePure () a) (kf2l x y)
        (transferE x y (linearB 2) (linearB_bounds 2) ∩ occ () _) := by
  obtain ⟨c0, c1, c2⟩ := linearB2_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have key : ∀ C : Proc Unit (fun _ => Act2) ℚ,
      mass C (kf2l x y) (transferE x y (linearB 2) (linearB_bounds 2) ∩ occ () _) =
        1 / 2 * (C ()).w .a * (C ()).w .a + 1 / 2 * (C ()).w .a * (C ()).w .b * (1 / 2) +
          1 / 2 * (C ()).w .b * (C ()).w .a * (1 / 2) := by
    intro C
    rw [transferE_inter_occ, transferE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, c0, c1, c2, f10, f01, hy.ne, hy.ne'] <;> ring
  rw [Act2.sum_univ, key, key, key]
  have hsum := (C ()).sum_one
  rw [Act2.sum_univ] at hsum
  simp [Proc.deviatePure, FinDistr.pure_w]
  linear_combination (1 / 2 * (C ()).w Act2.a) * hsum

/-- The pay-faithful set on the 2-fold linear mugging: the `T`-pay leaf and the transfer leaves —
the payoff classes `{−x, y}`. Source: `faithful.md` FA-8. Kind: D -/
def linearPayE : Finset (kf2l x y).Leaves :=
  labEv _ (kfLab x y (linearB 2) (linearB_bounds 2)) {((0 : Fin 2), -x), ((1 : Fin 2), y)}

/-- The refuse-faithful set on the 2-fold linear mugging: the `T`-refuse leaf and the no-transfer
leaves — the payoff class `{0}`. Source: `faithful.md` FA-8. Kind: D -/
def linearRefuseE : Finset (kf2l x y).Leaves :=
  labEv _ (kfLab x y (linearB 2) (linearB_bounds 2)) {((0 : Fin 2), (0 : ℚ)), ((1 : Fin 2), (0 : ℚ))}

/-- **T7(c), pay — a law-faithful leaf-set for pay exists on the 2-fold linear mugging.**
Source: `faithful.md` FA-8 ("`k=2` linear coupling: faithful sets exist under Definition 6")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1` -/
theorem kfold2_linear_pay_faithful (hx : 0 < x) (hy : 0 < y) :
    LeafLawFaithfulWrt (kf2l x y) (kfLab x y (linearB 2) (linearB_bounds 2)) (procQ q' h0.le h1.le)
      () .a (linearPayE x y) := by
  have hocc := kfold2_occ x y (linearB 2) (linearB_bounds 2)
  obtain ⟨c0, c1, c2⟩ := linearB2_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kf2l x y) (linearPayE x y) = q' := by
    rw [linearPayE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; exact h0, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [linearPayE, kfLab_tLeaf, kfLab_hLeaf, Act2.sum_univ, payCount, c0, c1, c2, procQ,
    hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure, FinDistr.pure_w]
  split_ifs <;> ring

/-- **T7(c), refuse — a law-faithful leaf-set for refuse exists on the 2-fold linear mugging**,
in contrast with the concave coupling (`kfold2_concave_no_refuse_faithful`).
Source: `faithful.md` FA-8 ("`k=2` linear coupling: faithful sets exist under Definition 6")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1` -/
theorem kfold2_linear_refuse_faithful (hx : 0 < x) (hy : 0 < y) :
    LeafLawFaithfulWrt (kf2l x y) (kfLab x y (linearB 2) (linearB_bounds 2)) (procQ q' h0.le h1.le)
      () .b (linearRefuseE x y) := by
  have hocc := kfold2_occ x y (linearB 2) (linearB_bounds 2)
  obtain ⟨c0, c1, c2⟩ := linearB2_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kf2l x y) (linearRefuseE x y) = 1 - q' := by
    rw [linearRefuseE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; linarith, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [linearRefuseE, kfLab_tLeaf, kfLab_hLeaf, Act2.sum_univ, payCount, c0, c1, c2, procQ,
    hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure, FinDistr.pure_w]
  split_ifs <;> ring

end linear

end Cleanroom.Decision.DpFaithfulUdt
