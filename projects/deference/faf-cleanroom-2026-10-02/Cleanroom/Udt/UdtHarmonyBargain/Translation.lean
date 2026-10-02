import Cleanroom.Udt.UdtHarmonyBargain.PropS
import Cleanroom.Found.DpCoreTree.SeedMax
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `udt-harmony-bargain` — the translation `DP(B)` (T9)

For a `dp-core-tree` tree `B`: players are the queried points `↥(queried B)`, actions `acts d`,
outcomes the pure profiles on the queried points (extended to a `Proc` by `Proc.ofFun` of an
arbitrary extension off `queried B`; the value does not depend on the extension by
`value_congr_queried`).

* `ChanceProfile B`: one draw at **every** chance node (full chance profiles; the harmony ledger's
  lazy ones draw only along the realised path — same pushforward on leaves; `variant` disclosed in
  the docstrings), with the product law `chanceLaw` and the leaf `leafOf π e` reached by the pure
  profile `π` and the chance profile `e`.
* `homogeneousPoint B`: the SC decision-point with world-model `(ChanceProfile B, chanceLaw)` and
  utility `r ∘ leafOf` — the same for every queried point (`X_d = β`).
* **`U_homogeneous_eq_value`**: `U (homogeneousPoint B) O = V_B(O)` on pure profiles, by tree
  induction with the unused branches marginalised (HA-1′, "exact at the pure grade", derived).
* `homogeneousGame B = commonGame V_B` (HA-1′); `pointSpecificGame B U` (HA-2′(i)).
* **Shared-seed grade** (HA-3′): the action game's expected payoff at the product mixture of a
  procedure `C` is `V'_B(C)` (Definition 6′), from `dp-core-tree`'s `value'_eq_product_mixture`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [DecidableEq ι]
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Marginalisation over a product -/

/-- A sum of products over a product type is a product of sums.
Source: none: infrastructure
Kind: L -/
theorem sum_pi_prod {J : Type} [Fintype J] [DecidableEq J] {X : J → Type} [∀ j, Fintype (X j)]
    (w : ∀ j, X j → K) : ∑ f : ∀ j, X j, ∏ j, w j (f j) = ∏ j, ∑ x, w j x := by
  have := Finset.prod_univ_sum (fun j : J => (univ : Finset (X j))) w
  rw [Fintype.piFinset_univ] at this
  exact this.symm

/-- **Marginalisation**: against product weights summing to one, a function of one coordinate
integrates to its one-dimensional expectation.
Source: none: infrastructure (the "telescoping" of the mandate's T9(ii))
Kind: P -/
theorem sum_pi_marginal {J : Type} [Fintype J] [DecidableEq J] {X : J → Type} [∀ j, Fintype (X j)]
    (w : ∀ j, X j → K) (hw : ∀ j, ∑ x, w j x = 1) (j₀ : J) (g : X j₀ → K) :
    ∑ f : ∀ j, X j, (∏ j, w j (f j)) * g (f j₀) = ∑ x, w j₀ x * g x := by
  set w' : ∀ j, X j → K := Function.update w j₀ (fun x => w j₀ x * g x) with hw'
  have key : ∀ f : ∀ j, X j, (∏ j, w j (f j)) * g (f j₀) = ∏ j, w' j (f j) := by
    intro f
    rw [← mul_prod_erase univ (fun j => w j (f j)) (mem_univ j₀),
      ← mul_prod_erase univ (fun j => w' j (f j)) (mem_univ j₀)]
    have h1 : w' j₀ (f j₀) = w j₀ (f j₀) * g (f j₀) := by
      rw [hw', Function.update_self]
    have h2 : ∏ j ∈ univ.erase j₀, w' j (f j) = ∏ j ∈ univ.erase j₀, w j (f j) :=
      prod_congr rfl fun j hj => by rw [hw', Function.update_of_ne (ne_of_mem_erase hj)]
    rw [h1, h2]
    ring
  simp_rw [key]
  rw [sum_pi_prod, ← mul_prod_erase univ (fun j => ∑ x, w' j x) (mem_univ j₀)]
  have h3 : ∏ j ∈ univ.erase j₀, ∑ x, w' j x = 1 := by
    refine prod_eq_one fun j hj => ?_
    rw [sum_congr rfl fun x _ => by rw [hw', Function.update_of_ne (ne_of_mem_erase hj)]]
    exact hw j
  rw [h3, mul_one]
  refine sum_congr rfl fun x _ => ?_
  rw [hw', Function.update_self]

/-! ### Chance profiles -/

/-- **Chance profiles**: one draw at every chance node of the tree (`leaf ↦ Unit`,
`chance n β child ↦ Fin n × ∀ j, ChanceProfile (child j)`, `decision d child ↦ ∀ a, ChanceProfile
(child a)`).
Source: `repair/harmony.md` "Definitions carried" (`E` = chance profiles); mandate T9(i)
Kind: D
Fidelity: variant: full chance profiles (a draw at every chance node, in every branch) in place of
the ledger's lazy ones (a draw only along the realised path); the same pushforward on leaves. -/
def ChanceProfile : Tree Ω ι acts K → Type
  | .leaf _ _ => Unit
  | .chance n _ child => Fin n × ∀ j, ChanceProfile (child j)
  | .decision _ child => ∀ a, ChanceProfile (child a)

/-- Finiteness of the chance profiles, by recursion.
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeChanceProfile : (B : Tree Ω ι acts K) → Fintype (ChanceProfile B)
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .chance n _ child =>
      haveI : ∀ j, Fintype (ChanceProfile (child j)) := fun j => fintypeChanceProfile (child j)
      inferInstanceAs (Fintype (Fin n × ∀ j, ChanceProfile (child j)))
  | .decision d child =>
      haveI : ∀ a, Fintype (ChanceProfile (child a)) := fun a => fintypeChanceProfile (child a)
      inferInstanceAs (Fintype (∀ a, ChanceProfile (child a)))

instance (B : Tree Ω ι acts K) : Fintype (ChanceProfile B) := fintypeChanceProfile B

/-- **The chance law** `β = ⊗ₙ βₙ`: the product of the chance weights of all draws.
Source: `repair/harmony.md` "Definitions carried" (`β := ⊗ₙ βₙ`); mandate T9(i)
Kind: D -/
def chanceLaw : (B : Tree Ω ι acts K) → ChanceProfile B → K
  | .leaf _ _, _ => 1
  | .chance _ β child, (i, f) => β.w i * ∏ j, chanceLaw (child j) (f j)
  | .decision _ child, f => ∏ a, chanceLaw (child a) (f a)

/-- **The realised leaf** `leaf(O, e)` of a pure profile `π` and a chance profile `e`.
Source: `repair/harmony.md` "Definitions carried" (`leaf(O, e)`); mandate T9(i)
Kind: D -/
def leafOf (π : (d : ι) → acts d) : (B : Tree Ω ι acts K) → ChanceProfile B → B.Leaves
  | .leaf _ _, _ => ()
  | .chance _ _ child, (i, f) => ⟨i, leafOf π (child i) (f i)⟩
  | .decision d child, f => ⟨π d, leafOf π (child (π d)) (f (π d))⟩

/-- The chance law is a probability.
Source: none: infrastructure
Kind: P -/
theorem sum_chanceLaw : (B : Tree Ω ι acts K) → ∑ e, chanceLaw B e = 1
  | .leaf _ _ => by
      show ∑ _e : Unit, (1 : K) = 1
      simp
  | .chance n β child => by
      have ih : ∀ j, ∑ e, chanceLaw (child j) e = 1 := fun j => sum_chanceLaw (child j)
      show ∑ e : Fin n × ∀ j, ChanceProfile (child j),
        β.w e.1 * ∏ j, chanceLaw (child j) (e.2 j) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← mul_sum]
      rw [sum_congr rfl fun i _ => by rw [sum_pi_prod, prod_eq_one fun j _ => ih j]]
      simp [β.sum_one]
  | .decision d child => by
      have ih : ∀ a, ∑ e, chanceLaw (child a) e = 1 := fun a => sum_chanceLaw (child a)
      show ∑ e : ∀ a, ChanceProfile (child a), ∏ a, chanceLaw (child a) (e a) = 1
      rw [sum_pi_prod]
      exact prod_eq_one fun a _ => ih a

/-- The chance law is non-negative.
Source: none: infrastructure
Kind: L -/
theorem chanceLaw_nonneg : (B : Tree Ω ι acts K) → ∀ e, 0 ≤ chanceLaw B e
  | .leaf _ _, _ => zero_le_one
  | .chance n β child, (i, f) => by
      show 0 ≤ β.w i * ∏ j, chanceLaw (child j) (f j)
      exact mul_nonneg (β.nonneg i) (prod_nonneg fun j _ => chanceLaw_nonneg (child j) (f j))
  | .decision d child, f => by
      show 0 ≤ ∏ a, chanceLaw (child a) (f a)
      exact prod_nonneg fun a _ => chanceLaw_nonneg (child a) (f a)

/-- The value of a leaf tree is its payoff.
Source: none: infrastructure
Kind: L -/
theorem value_leaf' (C : Proc ι acts K) (ω : Ω) (r : K) : value C (.leaf ω r) = r := by
  unfold value
  show ∑ _ℓ : Unit, (1 : K) * r = r
  simp

/-- The value at a chance node is the chance-weighted sum of the children's values.
Source: none: infrastructure
Kind: L -/
theorem value_chance' (C : Proc ι acts K) (n : ℕ) (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    value C (.chance n β child) = ∑ i, β.w i * value C (child i) := by
  unfold value
  rw [sum_leaves_chance]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_chance, payoff_chance]
  ring

/-- The value at a decision node is the `C(d)`-weighted sum of the children's values.
Source: none: infrastructure
Kind: L -/
theorem value_decision' (C : Proc ι acts K) (d : ι) (child : acts d → Tree Ω ι acts K) :
    value C (.decision d child) = ∑ a, (C d).w a * value C (child a) := by
  unfold value
  rw [sum_leaves_decision]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_decision, payoff_decision]
  ring

/-- **The homogeneous translation is exact at the pure grade**: the chance-law expectation of the
payoff at the realised leaf equals `V_B` of the deterministic procedure playing `π`.
Source: `repair/harmony.md` HA-1′ ("`U_d(O) = V_B(O)` on pure profiles"); mandate T9(ii)
Kind: P
Fidelity: exact (pure profiles; the marginalisation over the unused branches is `sum_pi_marginal`)
Hyps: (a) all -/
theorem sum_chanceLaw_payoff (π : (d : ι) → acts d) :
    (B : Tree Ω ι acts K) → ∑ e, chanceLaw B e * payoff B (leafOf π B e) = value (Proc.ofFun π) B
  | .leaf ω r => by
      show ∑ _e : Unit, (1 : K) * r = value (Proc.ofFun π) (.leaf ω r)
      unfold value
      show ∑ _e : Unit, (1 : K) * r = ∑ _ℓ : Unit, (1 : K) * r
      rfl
  | .chance n β child => by
      have ih : ∀ i, ∑ e, chanceLaw (child i) e * payoff (child i) (leafOf π (child i) e) =
          value (Proc.ofFun π) (child i) := fun i => sum_chanceLaw_payoff π (child i)
      show ∑ e : Fin n × ∀ j, ChanceProfile (child j),
          (β.w e.1 * ∏ j, chanceLaw (child j) (e.2 j)) * payoff (child e.1) (leafOf π (child e.1) (e.2 e.1))
        = value (Proc.ofFun π) (.chance n β child)
      rw [Fintype.sum_prod_type]
      have h1 : ∀ i : Fin n, ∑ f : ∀ j, ChanceProfile (child j),
          (β.w i * ∏ j, chanceLaw (child j) (f j)) * payoff (child i) (leafOf π (child i) (f i)) =
          β.w i * value (Proc.ofFun π) (child i) := by
        intro i
        rw [← ih i]
        have := sum_pi_marginal (fun j => chanceLaw (child j)) (fun j => sum_chanceLaw (child j)) i
          (fun x => payoff (child i) (leafOf π (child i) x))
        rw [← this, mul_sum]
        refine sum_congr rfl fun f _ => ?_
        ring
      simp_rw [h1]
      rw [value_chance']
  | .decision d child => by
      have ih : ∀ a, ∑ e, chanceLaw (child a) e * payoff (child a) (leafOf π (child a) e) =
          value (Proc.ofFun π) (child a) := fun a => sum_chanceLaw_payoff π (child a)
      show ∑ f : ∀ a, ChanceProfile (child a),
          (∏ a, chanceLaw (child a) (f a)) * payoff (child (π d)) (leafOf π (child (π d)) (f (π d)))
        = value (Proc.ofFun π) (.decision d child)
      rw [sum_pi_marginal (fun a => chanceLaw (child a)) (fun a => sum_chanceLaw (child a)) (π d)
        (fun x => payoff (child (π d)) (leafOf π (child (π d)) x)), ih, value_decision']
      simp only [Proc.ofFun_w, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]

/-! ### The homogeneous decision-point and games (over `ℚ`, cast to `ℝ`) -/

section Games

variable [∀ d, Nonempty (acts d)]

/-- Extension of a pure profile on the queried points to all of `ι` (arbitrary off `queried B`;
the value does not depend on it, `value_congr_queried`).
Source: none: infrastructure
Kind: D -/
noncomputable def extendQ (B : Tree Ω ι acts K) (O : (d : ↥(queried B)) → acts d) :
    (d : ι) → acts d :=
  fun d => if h : d ∈ queried B then O ⟨d, h⟩ else Classical.arbitrary _

theorem extendQ_of_mem (B : Tree Ω ι acts K) (O : (d : ↥(queried B)) → acts d) {d : ι}
    (h : d ∈ queried B) : extendQ B O d = O ⟨d, h⟩ := by
  simp [extendQ, h]

/-- **The homogeneous decision-point** of a tree `B` (the same for every queried point): world-model
`(ChanceProfile B, chanceLaw B)`, utility `r ∘ leaf(O, ·)`.
Source: `repair/harmony.md` HA-1′ (homogeneous translation); [[superconditioning-mismatched-ontologies]]
§13.1 (the common-prior collection); mandate T9(ii)
Kind: D
Fidelity: variant: full chance profiles (see `ChanceProfile`); values cast from `ℚ` -/
noncomputable def homogeneousPoint (B : Tree Ω ι acts ℚ) :
    DecisionPoint (fun d : ↥(queried B) => acts d) where
  X := ChanceProfile B
  μ := { w := fun e => Rat.cast (chanceLaw B e)
         nonneg := fun e => by exact_mod_cast chanceLaw_nonneg B e
         sum_one := by rw [← Rat.cast_sum, sum_chanceLaw]; simp }
  u O e := Rat.cast (payoff B (leafOf (extendQ B O) B e))

/-- The value of a pure profile on the queried points, as a real.
Source: none: infrastructure
Kind: D -/
noncomputable def treeValue (B : Tree Ω ι acts ℚ) (O : (d : ↥(queried B)) → acts d) : ℝ :=
  Rat.cast (value (Proc.ofFun (extendQ B O)) B)

/-- **`U_d(O) = V_B(O)` for the homogeneous decision-point** — HA-1′'s "exact at the pure grade"
as a theorem; `X_d = β` is derived from the tree, not stipulated.
Source: `repair/harmony.md` HA-1′; mandate T9(ii) (`U_homogeneous_eq_value`)
Kind: P
Fidelity: exact (pure profiles)
Hyps: (a) all -/
theorem U_homogeneous_eq_value (B : Tree Ω ι acts ℚ) (O : (d : ↥(queried B)) → acts d) :
    U (homogeneousPoint B) O = treeValue B O := by
  unfold U homogeneousPoint treeValue
  simp only
  rw [← sum_chanceLaw_payoff (extendQ B O) B, Rat.cast_sum]
  simp

/-- **The homogeneous game** `𝒢(B)`: every queried point is the homogeneous decision-point.
Source: `repair/harmony.md` HA-1′, HA-12′ (`𝒢(B)`); mandate T9(iii)
Kind: D -/
noncomputable def homogeneousGame (B : Tree Ω ι acts ℚ) :
    Game ↥(queried B) (fun d : ↥(queried B) => acts d) :=
  collectionGame fun _ => homogeneousPoint B

/-- The homogeneous game is the common-payoff game of `V_B` on pure profiles.
Source: `repair/harmony.md` HA-1′; mandate T9(iii)
Kind: C -/
theorem homogeneousGame_eq_commonGame (B : Tree Ω ι acts ℚ) :
    homogeneousGame B = commonGame (treeValue B) := by
  unfold homogeneousGame collectionGame commonGame utilGame
  congr 1
  funext O i
  exact U_homogeneous_eq_value B O

/-- **The point-specific-utility game**: any `U : queried points → outcomes → ℝ` is an SC
collection (Def. 9.1 types `uᵢ` per point); this is the translation the updated (event-conditioned)
values enter through (HA-2′(i)).
Source: `repair/harmony.md` HA-2′(i) ("point-specific-utility translation"); mandate T9(iii)
Kind: D -/
def pointSpecificGame (B : Tree Ω ι acts K)
    (U : ↥(queried B) → ((d : ↥(queried B)) → acts d) → ℝ) :
    Game ↥(queried B) (fun d : ↥(queried B) => acts d) :=
  utilGame U

/-! ### The shared-seed grade (HA-3′) -/

/-- **The action game** of `B`: strategies the actions at each queried point, payoff `V_B` of the
pure profile (the strategic form of the homogeneous game).
Source: `repair/harmony.md` HA-3′; mandate T9(iv)
Kind: D -/
noncomputable abbrev actionGame (B : Tree Ω ι acts ℚ) : StrategicGame ↥(queried B) ℝ :=
  (commonGame (treeValue B)).toStrategic

/-- The product mixture of a procedure `C`, as a mixed profile of the action game.
Source: `repair/harmony.md` HA-3′ ("mixed strategies are distributions over pure profiles");
mandate T9(iv)
Kind: D -/
noncomputable def mixOf (B : Tree Ω ι acts ℚ) (C : Proc ι acts ℚ) : MixedProfile (actionGame B) :=
  fun d => ⟨fun s => Rat.cast ((C d).w s.val), by
    refine ⟨fun s => ?_, ?_⟩
    · show (0 : ℝ) ≤ Rat.cast ((C d).w s.val)
      exact_mod_cast (C d).nonneg s.val
    · show ∑ s : ↥(univ : Finset (acts d)), Rat.cast ((C d).w s.val) = 1
      rw [Finset.sum_coe_sort (univ : Finset (acts d)) (fun a => Rat.cast ((C d).w a)),
        ← Rat.cast_sum, (C d).sum_one]
      simp⟩

/-- Pure profiles of the queried points as profiles of the action game.
Source: none: infrastructure
Kind: D -/
def toActionProfile (B : Tree Ω ι acts ℚ) (π : (d : ↥(queried B)) → acts d) :
    (actionGame B).Profile :=
  fun d => ⟨π d, mem_univ _⟩

/-- The equivalence between action-game profiles and pure profiles of the queried points.
Source: none: infrastructure
Kind: D -/
def actionProfileEquiv (B : Tree Ω ι acts ℚ) :
    (actionGame B).Profile ≃ ((d : ↥(queried B)) → acts d) :=
  Equiv.piCongrRight fun d => Equiv.subtypeUnivEquiv fun _ => mem_univ _

/-- `Proc.pureOn C (queried B) π` and `Proc.ofFun (extendQ B π)` have the same value.
Source: none: infrastructure (`value_congr_queried`)
Kind: L -/
theorem value_pureOn_eq_value_extendQ (B : Tree Ω ι acts ℚ) (C : Proc ι acts ℚ)
    (π : (d : ↥(queried B)) → acts d) :
    value (Proc.pureOn C (queried B) π) B = value (Proc.ofFun (extendQ B π)) B := by
  refine value_congr_queried B fun d hd => ?_
  rw [Proc.pureOn_of_mem C (queried B) π hd]
  show FinDistr.pure (π ⟨d, hd⟩) = FinDistr.pure (extendQ B π d)
  rw [extendQ_of_mem B π hd]

/-- **Shared-seed grade (HA-3′)**: the action game's expected payoff at the product mixture of `C`
is `V'_B(C)` (Definition 6′), for every queried point. Definition 6's independent-redraw value
`V_B(C)` can exceed it on nested trees (`amd_value` vs `amd_value'`, `miniature_value` vs
`miniature_value'` in `dp-core-tree`), so every harmony ↔ optimality statement of this package is
at the pure / shared-seed grade only.
Source: `repair/harmony.md` HA-3′; `seeds.md` SE-1(a) via `value'_eq_product_mixture`; mandate T9(iv)
Kind: C
Fidelity: exact (the identification of mixed profiles with product mixtures is the content)
Hyps: (a) all -/
theorem expectedPayoff_actionGame_mixOf (B : Tree Ω ι acts ℚ) (C : Proc ι acts ℚ)
    (d : ↥(queried B)) : expectedPayoff (actionGame B) (mixOf B C) d = Rat.cast (value' C B) := by
  rw [value'_eq_product_mixture, Rat.cast_sum]
  unfold expectedPayoff
  rw [← (actionProfileEquiv B).symm.sum_comp]
  refine sum_congr rfl fun π _ => ?_
  rw [value_pureOn_eq_value_extendQ, Rat.cast_mul, Rat.cast_prod]
  rfl

end Games

end Cleanroom.Udt.UdtHarmonyBargain
