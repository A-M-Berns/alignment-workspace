import Cleanroom.Decision.DpFairnessReloc.LawSets
import Cleanroom.Decision.DpFairnessReloc.Witnesses

/-!
# The top repair's act values (SP-3), the mugging's act values, TN-V2's numbers (repair round 2)

Package `dp-fairness-reloc`, file 18. Three of the mandate's core witness items that repair
round 1 left `flagged: not done`:

* **T6(d), SP-3**: when every queried point is relocated (`U ⊇ queried B`, the top repair),
  the relocated root's act value at the joint tuple `σ` is the input's pure value `V_B(σ)`
  (`value_deviate_root`: the resolved branch has no decision node left, so its value is
  procedure-independent and equals the lifted pure value by FR-7(a)); hence on almost-fair
  inputs the root's best act attains `max_π V_B(π) = max_C V_B(C)`
  (`AlmostFair.topRepair_best_act`, through `exists_pure_max_value'` and
  `AlmostFair.value_eq_value'`). Witness: the mugging relocated — act values `(y − x)/2` for pay
  and `0` for refuse (`mug1_act_value_pay`, `mug1_act_value_refuse`), and the value-preservation
  identity `q(y − x)/2` at every `q` (`mug1_value`, `mug1_reloc_value`).
* **T1**: Newcomb's V1 and V2 are not almost fair — the hypothetical `d_F` sits above the real
  one (`tnV1_not_almostFair`, `tnV2_not_almostFair`, count level, every `p`), and for `0 < p`
  V2 is positively nested at both points (`tnV2_nested_F`, `tnV2_nested_E`).
* **T4(f), the TN-V2 numbers** (SE-6): at `p = 1`, `L = 4`, `S = 1`, `d_E` fixed to `large` and
  `d_F` playing `large` with probability `m`: `V = m(5 − m)` (Definition 6: the real `d_F`
  redraws), `V′ = 4m` (Definition 6′), and the relocated value is `4m` (`tnV2_value`,
  `tnV2_value'`, `tnV2_reloc_value`, bundled as `tnV2_numbers`). The symbolic gap
  `S·m_E m_F (m_E − m_F)(2p − 1)` is stretch and not stated.
-/

namespace Cleanroom.Decision.DpFairnessReloc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-! ### SP-3: the top repair's act values are the pure values -/

section sp3

variable [DecidableEq ι] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [∀ d, Nonempty (acts d)] (U : Finset ι) (B : Tree Ω ι acts K)

/-- A tuple on `U` extended to a full assignment (arbitrary off `U`).
Source: none: infrastructure
Kind: D -/
noncomputable def extendTuple (σ : (d : ↥U) → acts d) : (d : ι) → acts d :=
  fun d => if h : d ∈ U then σ ⟨d, h⟩ else Classical.arbitrary _

/-- When every queried point is relocated, the output queries only its root.
Source: `spectrum.md` SP-D1 ("top repair (full normal form)")
Kind: L -/
theorem queried_relocRoot_subset (hU : queried B ⊆ U) :
    queried (relocRoot U B) ⊆ {Sum.inr ()} := by
  intro p hp
  cases p with
  | inl d =>
      exact absurd (hU (mem_queried_of_mem_queried_relocRoot U B hp))
        (not_mem_U_of_mem_queried_relocRoot U B hp)
  | inr u => cases u; simp

/-- **SP-3, the act values of the top repair**: when `U ⊇ queried B`, the relocated root's act
value at the joint tuple `σ` — under any procedure `C'` on the output — is the input's pure
value at (any extension of) `σ`. The resolved branch has no decision node left, so its value
does not depend on `C'`, and the lifted deterministic procedure gives the input's pure law
(FR-7(a), `lawOfW_reloc_ofFun`).
Source: `spectrum.md` SP-3 ("the top repair `U = queried B` has act values `V_B(π)` at each
joint policy `π`"); mandate T6(d)
Kind: P
Fidelity: exact (root site; `U ⊇ queried B`, which includes the top repair `U = queried B`)
Hyps: none -/
theorem value_deviate_root (hU : queried B ⊆ U) (C' : Proc (ι ⊕ Unit) (actsR acts U) K)
    (σ : (d : ↥U) → acts d) :
    value (C'.deviatePure (.inr ()) σ) (relocRoot U B) =
      value (Proc.ofFun (extendTuple U σ)) B := by
  have h1 : value (C'.deviatePure (.inr ()) σ) (relocRoot U B) =
      value (Proc.ofFun (liftFun U (extendTuple U σ))) (relocRoot U B) := by
    apply value_congr_queried
    intro p hp
    have hp' := queried_relocRoot_subset U B hU hp
    rw [Finset.mem_singleton] at hp'
    subst hp'
    apply FinDistr.ext'
    intro τ
    simp only [Proc.deviatePure, Proc.deviate, Function.update_self, Proc.ofFun, liftFun]
    have hσ : (fun d : ↥U => extendTuple U σ d) = σ := by
      funext d
      simp [extendTuple, d.2]
    rw [hσ]
  rw [h1, value_eq_valInt Prod.fst, lawOfW_reloc_ofFun, ← value_eq_valInt id]

/-- **SP-3 on almost-fair inputs: the top repair's best act attains the input's optimum.** For
almost-fair `B` there is a joint tuple `σ*` on `queried B` such that, under every procedure `C'`
on the output, the relocated root's act value at `σ*` is at least `V_B(C)` for every `C` (and at
least `V_B(π)` for every pure `π`): `max_σ Q_{d̂}(σ) = max_π V_B(π) = max_C V_B(C)`.
Source: `spectrum.md` SP-3 ("its best act attains `max_π V_B(π) = max_C V_B(C)` on almost-fair
trees"); mandate T6(d)
Kind: C
Fidelity: exact (the maximiser exhibited as a tuple on `queried B`; on almost-fair `B` the
optimum over all procedures is a pure value, `exists_pure_max_value'` +
`AlmostFair.value_eq_value'`)
Hyps: none -/
theorem AlmostFair.topRepair_best_act {B : Tree Ω ι acts K} (h : AlmostFair B) :
    ∃ σ : (d : ↥(queried B)) → acts d,
      (∀ (C : Proc ι acts K) (C' : Proc (ι ⊕ Unit) (actsR acts (queried B)) K),
        value C B ≤ value (C'.deviatePure (.inr ()) σ) (relocRoot (queried B) B)) ∧
      (∀ (π : (d : ι) → acts d) (C' : Proc (ι ⊕ Unit) (actsR acts (queried B)) K),
        value (Proc.ofFun π) B ≤
          value (C'.deviatePure (.inr ()) σ) (relocRoot (queried B) B)) := by
  obtain ⟨π, hC, hπ, -⟩ := exists_pure_max_value' B
  have hext : value (Proc.ofFun (extendTuple (queried B) fun d => π d)) B =
      value (Proc.ofFun π) B := by
    apply value_congr_queried
    intro d hd
    simp [Proc.ofFun, extendTuple, hd]
  refine ⟨fun d => π d, fun C C' => ?_, fun π' C' => ?_⟩
  · rw [value_deviate_root _ _ (Finset.Subset.refl _), hext, h.value_eq_value' C]
    exact hC C
  · rw [value_deviate_root _ _ (Finset.Subset.refl _), hext]
    exact hπ π'

end sp3

/-! ### The mugging's act values (FR-2) -/

/-- `V_{mug1}(q) = q(y − x)/2` where `q` is the probability of paying.
Source: `fair-repair.md` FR-2 ("`V = q(y−x)/2`"); mandate T6(d)
Kind: N+ -/
theorem mug1_value (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (procQ q h0 h1) (mug1 x y) = q * (y - x) / 2 := by
  unfold value mug1
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [mugWorld1, mugPay, FinDistr.fair, FinDistr.coin, procQ, FinDistr.act2_a, FinDistr.act2_b]
  ring

/-- The pure value of paying: `(y − x)/2`.
Source: `fair-repair.md` FR-2
Kind: L -/
theorem mug1_value_pay (x y : ℚ) : value (Proc.ofFun fun _ => Act2.a) (mug1 x y) = (y - x) / 2 := by
  unfold value mug1
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  ring

/-- The pure value of refusing: `0`.
Source: `fair-repair.md` FR-2
Kind: L -/
theorem mug1_value_refuse (x y : ℚ) : value (Proc.ofFun fun _ => Act2.b) (mug1 x y) = 0 := by
  unfold value mug1
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, Act2.sum_univ,
    sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf,
    Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]

/-- The mugging queries its one point only (trivially, `ι = Unit`).
Source: none: infrastructure
Kind: L -/
theorem mug1_queried_subset (x y : ℚ) : queried (mug1 x y) ⊆ {()} := fun p _ => by simp

/-- **The relocated mugging's act value at `pol = pay` is `(y − x)/2`**, under every procedure
on the output (`d̂` is the only queried point of the output).
Source: `fair-repair.md` FR-2 ("`V_ŝ(pol = pay) = (y − x)/2`"); mandate T6(d)
Kind: N+ -/
theorem mug1_act_value_pay (x y : ℚ)
    (C' : Proc (Unit ⊕ Unit) (actsR (fun _ => Act2) {()}) ℚ) :
    value (C'.deviatePure (.inr ()) fun _ => Act2.a) (relocRoot {()} (mug1 x y)) =
      (y - x) / 2 := by
  rw [value_deviate_root _ _ (mug1_queried_subset x y)]
  have : extendTuple ({()} : Finset Unit) (fun _ => Act2.a) = fun _ => Act2.a := by
    funext d; simp [extendTuple]
  rw [this, mug1_value_pay]

/-- **The relocated mugging's act value at `pol = refuse` is `0`.**
Source: `fair-repair.md` FR-2; mandate T6(d)
Kind: N+ -/
theorem mug1_act_value_refuse (x y : ℚ)
    (C' : Proc (Unit ⊕ Unit) (actsR (fun _ => Act2) {()}) ℚ) :
    value (C'.deviatePure (.inr ()) fun _ => Act2.b) (relocRoot {()} (mug1 x y)) = 0 := by
  rw [value_deviate_root _ _ (mug1_queried_subset x y)]
  have : extendTuple ({()} : Finset Unit) (fun _ => Act2.b) = fun _ => Act2.b := by
    funext d; simp [extendTuple]
  rw [this, mug1_value_refuse]

/-- **Value preservation on the mugging at every `q`**: `V_{Rel}(lift (procQ q)) = q(y − x)/2`.
Source: `fair-repair.md` FR-2, FR-6; mandate T6(d) ("the value-preservation identity
`q(y−x)/2` at every `q`")
Kind: N+ -/
theorem mug1_reloc_value (x y q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    value (lift {()} (procQ q h0 h1)) (relocRoot {()} (mug1 x y)) = q * (y - x) / 2 := by
  rw [AlmostFair.value_reloc (mug1_almostFair x y), mug1_value]

/-! ### Compositional value equations (infrastructure) -/

section valueEqs

variable [DecidableEq ι] [∀ d, Fintype (acts d)] (C : Proc ι acts K)

/-- The value of a leaf is its payoff. Source: none: infrastructure. Kind: L -/
theorem value_leaf (ω : Ω) (r : K) : value C (.leaf ω r) = r := by
  unfold value
  show ∑ ℓ : Unit, leafLaw C (Tree.leaf ω r) ℓ * payoff (Tree.leaf ω r) ℓ = r
  simp

/-- The value of a chance node is the chance-weighted sum of the children's values.
Source: none: infrastructure
Kind: L -/
theorem value_chance {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) :
    value C (.chance n β child) = ∑ i, β.w i * value C (child i) := by
  unfold value
  rw [sum_leaves_chance]
  simp only [leafLaw_chance, payoff_chance, Finset.mul_sum, mul_assoc]

/-- The value of a decision node is the `C(d)`-weighted sum of the children's values
(Definition 6 redraws at every node).
Source: none: infrastructure
Kind: L -/
theorem value_decision (d : ι) (child : acts d → Tree Ω ι acts K) :
    value C (.decision d child) = ∑ a, (C d).w a * value C (child a) := by
  unfold value
  rw [sum_leaves_decision]
  simp only [leafLaw_decision, payoff_decision, Finset.mul_sum, mul_assoc]

end valueEqs

/-! ### Newcomb V1/V2 are not almost fair (T1) -/

/-- **V1 is not almost fair**: the hypothetical `d_F` sits above the real one (count `2` on the
full-branch leaves), for every `p`, `L`, `S`.
Source: `fair-repair.md` FR-5 ("hypothetical-above-real nesting"); mandate T1
Kind: N+ -/
theorem tnV1_not_almostFair (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    ¬ AlmostFair (tnV1 p h0 h1 L S) := by
  intro h
  have := h .F ⟨.large, ⟨0, ⟨.large, ()⟩⟩⟩
  change 1 + (1 + 0) ≤ 1 at this
  omega

/-- **V2 is not almost fair**: the hypothetical `d_F` sits above the real one, for every `p`,
`L`, `S`.
Source: `fair-repair.md` FR-5; mandate T1 ("`tnV2` not almost fair")
Kind: N+ -/
theorem tnV2_not_almostFair (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    ¬ AlmostFair (tnV2 p h0 h1 L S) := by
  intro h
  have := h .F ⟨.large, ⟨.large, ⟨0, ⟨.large, ()⟩⟩⟩⟩
  change 1 + (0 + (1 + 0)) ≤ 1 at this
  omega

/-- V2 is positively nested at `d_F` when `0 < p` (the `(large, large)` answers reach the full
branch with weight `p`).
Source: `seeds.md` SE-2; mandate T1
Kind: N+ -/
theorem tnV2_nested_F (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : 0 < p) (L S : ℚ) :
    Nested (tnV2 p h0 h1 L S) .F := by
  refine ⟨by decide, ⟨.large, ⟨.large, ⟨0, ⟨.large, ()⟩⟩⟩⟩, ?_, ?_⟩
  · show 0 < (FinDistr.coin (if Box.large = Box.large ∧ Box.large = Box.large then p else 1 - p)
      _ _).w 0 * 1
    rw [coin_w_zero]
    simpa using hp
  · change 2 ≤ 1 + (0 + (1 + 0))
    omega

/-- V2 is positively nested at `d_E` when `0 < p` (the `(both, large)` answers reach the empty
branch with weight `p`).
Source: `seeds.md` SE-2; mandate T1
Kind: N+ -/
theorem tnV2_nested_E (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : 0 < p) (L S : ℚ) :
    Nested (tnV2 p h0 h1 L S) .E := by
  refine ⟨by decide, ⟨.both, ⟨.large, ⟨1, ⟨.large, ()⟩⟩⟩⟩, ?_, ?_⟩
  · show 0 < (FinDistr.coin (if Box.both = Box.large ∧ Box.large = Box.large then p else 1 - p)
      _ _).w 1 * 1
    rw [coin_w_one]
    simpa using hp
  · change 2 ≤ 0 + (1 + (1 + 0))
    omega

/-! ### The TN-V2 numbers (SE-6, T4(f)) -/

/-- `univ = {large, both}`. Source: none: infrastructure. Kind: L -/
theorem Box.univ_eq : (Finset.univ : Finset Box) = {.large, .both} := by
  ext x; cases x <;> simp

/-- Sums over `Box`. Source: none: infrastructure. Kind: L -/
theorem Box.sum_univ {M : Type} [AddCommMonoid M] (f : Box → M) :
    ∑ x, f x = f .large + f .both := by
  rw [Box.univ_eq, Finset.sum_pair (by decide)]

/-- The mixed action on `Box`: `large` with probability `m`.
Source: none: infrastructure
Kind: D -/
def FinDistr.box (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) : FinDistr ℚ Box where
  w b := if b = .large then m else 1 - m
  nonneg b := by split_ifs <;> linarith
  sum_one := by rw [Box.sum_univ]; simp

/-- SE-6's procedure: `d_F` plays `large` with probability `m`, `d_E` is fixed to `large`.
Source: `seeds.md` SE-6 ("`d_E` fixed to `large`"); mandate T4(f)
Kind: D -/
def tnProc (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) : Proc TnPt (fun _ => Box) ℚ
  | .F => FinDistr.box m h0 h1
  | .E => FinDistr.pure .large

/-- The pure Newcomb assignment `d_F ↦ x`, `d_E ↦ y`.
Source: none: infrastructure
Kind: D -/
def tnPure (x y : Box) : (d : TnPt) → Box
  | .F => x
  | .E => y

/-- Deviating SE-6's procedure to pure answers at both points is the pure assignment.
Source: none: infrastructure
Kind: L -/
theorem tnProc_deviate_eq (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) (x y : Box)
    (B : Tree TnW TnPt (fun _ => Box) ℚ) :
    ∀ d ∈ queried B, ((tnProc m h0 h1).deviatePure .F x).deviatePure .E y d =
      Proc.ofFun (tnPure x y) d := by
  intro d _
  cases d <;> simp [Proc.deviatePure, Proc.deviate, Proc.ofFun, tnPure, Function.update_apply]

/-- **TN-V2 under Definition 6 at `p = 1`, `L = 4`, `S = 1`: `V = m(5 − m)`.** The real `d_F`
redraws: with probability `m` the run reaches the full branch, where one-boxing (`m`) pays `4`
and two-boxing (`1 − m`) pays `5`; the `both` answer at the hypothetical `d_F` sends the run
to the empty branch, worth `0` with `d_E` fixed to `large`.
Source: `seeds.md` SE-6 ("`V = m(5−m)`"); mandate T4(f)
Kind: N+ -/
theorem tnV2_value (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    value (tnProc m h0 h1) (tnV2 1 (by norm_num) (by norm_num) 4 1) = m * (5 - m) := by
  unfold tnV2
  simp only [value_decision, value_chance, value_leaf, Box.sum_univ, Fin.sum_univ_two, tnReal,
    coin_w_zero, coin_w_one]
  simp [tnProc, FinDistr.box, tnPay, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  ring

/-- **TN-V2 under Definition 6′: `V′ = 4m`.** The seed for `d_F` is drawn once: `large` (`m`)
goes to the full branch and one-boxes for `4`; `both` goes to the empty branch and gets `0`.
Proof: SE-1(b)'s multiaffinity peels the two points off (`value'_deviate_sum`), leaving pure
values.
Source: `seeds.md` SE-6 ("`V′ = 4m`"); mandate T4(f)
Kind: N+ -/
theorem tnV2_value' (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    value' (tnProc m h0 h1) (tnV2 1 (by norm_num) (by norm_num) 4 1) = 4 * m := by
  rw [value'_deviate_sum _ _ .F, Box.sum_univ,
    value'_deviate_sum ((tnProc m h0 h1).deviatePure .F .large) _ .E, Box.sum_univ,
    value'_deviate_sum ((tnProc m h0 h1).deviatePure .F .both) _ .E, Box.sum_univ,
    value'_congr_queried _ (tnProc_deviate_eq m h0 h1 .large .large _),
    value'_congr_queried _ (tnProc_deviate_eq m h0 h1 .large .both _),
    value'_congr_queried _ (tnProc_deviate_eq m h0 h1 .both .large _),
    value'_congr_queried _ (tnProc_deviate_eq m h0 h1 .both .both _),
    value'_ofFun, value'_ofFun, value'_ofFun, value'_ofFun]
  unfold tnV2
  simp only [value_decision, value_chance, value_leaf, Box.sum_univ, Fin.sum_univ_two, tnReal,
    coin_w_zero, coin_w_one]
  simp [tnProc, FinDistr.box, tnPay, tnPure, Proc.deviatePure, Proc.deviate, Function.update_apply]
  ring

/-- **TN-V2 relocated (both points, the top repair): `4m`.** Both points are nested for `p = 1`,
so SE-7′ needs `U = {F, E}`; the relocated Definition-6 value is the input's Definition-6′ value.
Source: `seeds.md` SE-6 ("relocated `4m`"), SE-7′; mandate T4(f)
Kind: N+ -/
theorem tnV2_reloc_value (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    value (lift Finset.univ (tnProc m h0 h1))
        (relocRoot Finset.univ (tnV2 1 (by norm_num) (by norm_num) 4 1)) = 4 * m := by
  rw [value_relocRoot _ _ _ (fun _ _ => Finset.mem_univ _), tnV2_value']

/-- **SE-6's numbers on one statement**: `V = m(5 − m)`, `V′ = 4m`, relocated `4m`, and V2 is
nested at both points.
Source: `seeds.md` SE-6; mandate T4(f)
Kind: N+ -/
theorem tnV2_numbers (m : ℚ) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    value (tnProc m h0 h1) (tnV2 1 (by norm_num) (by norm_num) 4 1) = m * (5 - m) ∧
    value' (tnProc m h0 h1) (tnV2 1 (by norm_num) (by norm_num) 4 1) = 4 * m ∧
    value (lift Finset.univ (tnProc m h0 h1))
        (relocRoot Finset.univ (tnV2 1 (by norm_num) (by norm_num) 4 1)) = 4 * m ∧
    Nested (tnV2 1 (by norm_num) (by norm_num) 4 1) .F ∧
    Nested (tnV2 1 (by norm_num) (by norm_num) 4 1) .E :=
  ⟨tnV2_value m h0 h1, tnV2_value' m h0 h1, tnV2_reloc_value m h0 h1,
    tnV2_nested_F 1 (by norm_num) (by norm_num) (by norm_num) 4 1,
    tnV2_nested_E 1 (by norm_num) (by norm_num) (by norm_num) 4 1⟩

end Cleanroom.Decision.DpFairnessReloc
