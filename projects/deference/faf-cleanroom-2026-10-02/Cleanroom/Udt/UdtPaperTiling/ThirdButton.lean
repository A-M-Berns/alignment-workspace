import Cleanroom.Udt.UdtPolicyCalc.Games
import EconCSLib.GameTheory.StrategicGame.MixedStrategy

/-!
# `udt-paper-tiling` · ThirdButton: the 5/10/20 game, its equilibria, and the resolutions (T10(a)–(c))

The working notes' counterexample (l10 §Counterexample, bli-paper-076(c)): two copies of the
agent, in a red and a green room, each press one of three buttons; both press "5" pays 5 to
everyone, both press "10" pays 10, one "10" and one "20" pays 20, anything else 0. If each copy
trusts the other to obey "press 10", each defects to "20" and both get 0 — "trust in other selves
is self-defeating". The game is `udt-policy-calc`'s `instanceGame U` (FAF's
`SafeParetoImprovements.Game`) for the common payoff `U` below, with `S = Fin 2` (rooms) and
`A = Fin 3` (`0 = "5"`, `1 = "10"`, `2 = "20"`); pure Nash is EconCSLib's `IsNashEquilibrium`,
which `isNashEquilibrium_instanceGame_iff` identifies with `IsLocalOptimum`.

* (a) `(10, 10)` is **not** a Nash equilibrium (each copy's best response to 10 is 20); `(10, 20)`,
  `(20, 10)` and `(5, 5)` are strict Nash equilibria; `(20, 20)` is not one.
* (b) Over `{10, 20}` the symmetric mixed profile `(1 − q, q)` is a mixed Nash equilibrium
  (EconCSLib's `IsMixedNashEq` on the direct form of the instance game) **iff `q = 1/3`**, with
  value `40/3`; pure "5" is not a best response to it, and pure "10" and "20" are *both* best
  responses — it is only weakly stable.
* (c) Resolutions (bli-paper-077): the asymmetric joint message `(10, 20)` is a strict equilibrium,
  stable under any strict stability notion (b′); the mixed resolution (a′) fails strict stability
  — "mixed strategies" resolve the problem only for a weaker stability notion.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Udt.UdtPolicyCalc StrategicGame Finset

namespace ThirdButton

noncomputable section

/-- **The Third Button payoff**: both "5" ↦ 5, both "10" ↦ 10, one "10" and one "20" ↦ 20,
else 0 (buttons `0 = "5"`, `1 = "10"`, `2 = "20"`).
Source: [[udt-tiling-working-notes-2025-06-30]] l10 §Counterexample (bli-paper-076(c))
Kind: D
Fidelity: exact -/
def U : Policy (Fin 2) (Fin 3) → ℝ := fun π =>
  if π 0 = 0 ∧ π 1 = 0 then 5
  else if π 0 = 1 ∧ π 1 = 1 then 10
  else if (π 0 = 1 ∧ π 1 = 2) ∨ (π 0 = 2 ∧ π 1 = 1) then 20
  else 0

/-- `Function.update` at room `0` on a two-room profile.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma update_zero (π : Fin 2 → Fin 3) (a : Fin 3) : Function.update π 0 a = ![a, π 1] := by
  funext i
  fin_cases i <;> simp

/-- `Function.update` at room `1` on a two-room profile.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma update_one (π : Fin 2 → Fin 3) (a : Fin 3) : Function.update π 1 a = ![π 0, a] := by
  funext i
  fin_cases i <;> simp

/-- The payoff on an explicit profile.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma U_vec (a b : Fin 3) :
    U ![a, b] = if a = 0 ∧ b = 0 then 5 else if a = 1 ∧ b = 1 then 10
      else if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then 20 else 0 := by
  simp [U]

/-- **A strict local optimum** (strict pure Nash equilibrium of the instance game): every
unilateral deviation strictly lowers the payoff.
Source: bli-paper-077 (strict stability); bli-paper-087
Kind: D
Fidelity: exact -/
def IsStrictLocalOptimum (U : Policy (Fin 2) (Fin 3) → ℝ) (π : Policy (Fin 2) (Fin 3)) : Prop :=
  ∀ s a, a ≠ π s → U (Function.update π s a) < U π

/-- A strict local optimum is a local optimum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsStrictLocalOptimum.isLocalOptimum {U : Policy (Fin 2) (Fin 3) → ℝ}
    {π : Policy (Fin 2) (Fin 3)} (h : IsStrictLocalOptimum U π) : IsLocalOptimum U π := by
  rw [isLocalOptimum_iff]
  intro s a
  by_cases ha : a = π s
  · rw [ha, Function.update_eq_self]
  · exact le_of_lt (h s a ha)

/-- **`(10, 10)` is not a Nash equilibrium**: each copy's best response to "10" is "20"
(`20 > 10`). "Trust in other selves is self-defeating."
Source: l10 §Counterexample (bli-paper-076(c))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_localOptimum_ten_ten : ¬ IsLocalOptimum U ![1, 1] := by
  intro h
  have := h 0 2
  rw [update_zero, update_zero] at this
  simp [U_vec] at this
  norm_num at this

/-- **`(10, 20)` is a strict Nash equilibrium.**
Source: bli-paper-077(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem strict_ten_twenty : IsStrictLocalOptimum U ![1, 2] := by
  unfold IsStrictLocalOptimum
  rw [Fin.forall_fin_two]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [update_zero]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num
  · rw [update_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num

/-- **`(20, 10)` is a strict Nash equilibrium.**
Source: bli-paper-077(b)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem strict_twenty_ten : IsStrictLocalOptimum U ![2, 1] := by
  unfold IsStrictLocalOptimum
  rw [Fin.forall_fin_two]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [update_zero]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num
  · rw [update_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num

/-- **`(5, 5)` is a strict Nash equilibrium.**
Source: l10 §Counterexample (bli-paper-076(c))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem strict_five_five : IsStrictLocalOptimum U ![0, 0] := by
  unfold IsStrictLocalOptimum
  rw [Fin.forall_fin_two]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [update_zero]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num
  · rw [update_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at ha ⊢
    fin_cases a <;> simp_all [U_vec] <;> norm_num

/-- **`(20, 20)` is not a Nash equilibrium** (deviating to "10" earns 20 instead of 0).
Source: l10 §Counterexample (bli-paper-076(c))
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_localOptimum_twenty_twenty : ¬ IsLocalOptimum U ![2, 2] := by
  intro h
  have := h 0 1
  rw [update_zero, update_zero] at this
  simp [U_vec] at this
  norm_num at this

/-- **The pure equilibrium facts over FAF's instance game** (EconCSLib's `IsNashEquilibrium` on
`(instanceGame U).toStrategic`): `(10, 10)` and `(20, 20)` are not Nash equilibria; `(10, 20)`,
`(20, 10)`, `(5, 5)` are.
Source: l10 §Counterexample (bli-paper-076(c), 077); `udt-policy-calc` `Games.lean`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem nash_facts :
    ¬ IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile ![1, 1] (mem_profiles_instanceGame U _)) ∧
    ¬ IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile ![2, 2] (mem_profiles_instanceGame U _)) ∧
    IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile ![1, 2] (mem_profiles_instanceGame U _)) ∧
    IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile ![2, 1] (mem_profiles_instanceGame U _)) ∧
    IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile ![0, 0] (mem_profiles_instanceGame U _)) := by
  simp only [isNashEquilibrium_instanceGame_iff]
  exact ⟨not_localOptimum_ten_ten, not_localOptimum_twenty_twenty,
    strict_ten_twenty.isLocalOptimum, strict_twenty_ten.isLocalOptimum,
    strict_five_five.isLocalOptimum⟩

/-! ## The mixed equilibrium over `{10, 20}` -/

/-- A sum over the nine two-room profiles, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_profiles {M : Type} [AddCommMonoid M] (g : (Fin 2 → Fin 3) → M) :
    ∑ π, g π = ∑ a : Fin 3, ∑ b : Fin 3, g ![a, b] := by
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp g, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_eq]

/-- **The expected payoff of a mixed profile in closed form**: `∑_{a,b} p₀(a) p₁(b) U(a, b)`.
Source: none: infrastructure (EconCSLib's `expectedPayoff` on the direct instance game)
Kind: L
Fidelity: n/a -/
lemma expectedPayoff_eq (p : MixedProfile (directGame U)) (who : Fin 2) :
    expectedPayoff (directGame U) p who =
      ∑ a : Fin 3, ∑ b : Fin 3, (p 0).val a * (p 1).val b * U ![a, b] := by
  unfold expectedPayoff
  rw [sum_profiles]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The mixed strategy `(0, 1 − q, q)` on `("5", "10", "20")`.
Source: bli-paper-077(a)
Kind: D
Fidelity: exact -/
def mix (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (i : Fin 2) : MixedStrategy (directGame U) i :=
  ⟨fun a => if a = 1 then 1 - q else if a = 2 then q else 0,
    ⟨fun a => by
      show 0 ≤ (if a = 1 then 1 - q else if a = 2 then q else 0)
      split_ifs <;> linarith,
    by
      show ∑ a : Fin 3, (if a = 1 then 1 - q else if a = 2 then q else 0) = 1
      simp [Fin.sum_univ_three]⟩⟩

/-- The symmetric mixed profile: both copies play `mix q`.
Source: bli-paper-077(a)
Kind: D
Fidelity: exact -/
def symMixed (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : MixedProfile (directGame U) :=
  fun i => mix q h0 h1 i

/-- The weight of a pure action under `mix q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mix_val (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (i : Fin 2) (a : Fin 3) :
    (mix q h0 h1 i).val a = if a = 1 then 1 - q else if a = 2 then q else 0 := rfl

/-- The weight of a pure action under the point mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma pureToMixed_val {i : Fin 2} (s a : Fin 3) :
    (pureToMixed (G := directGame U) (i := i) s).val a = if a = s then 1 else 0 := rfl

/-- **The expected payoff of the symmetric profile** (either player): the other copy plays "10"
with probability `1 − q` and "20" with probability `q`.
Source: bli-paper-077(a) (the inventory's computation)
Kind: L
Fidelity: n/a -/
lemma expectedPayoff_symMixed (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (who : Fin 2) :
    expectedPayoff (directGame U) (symMixed q h0 h1) who =
      (1 - q) * ((1 - q) * 10 + q * 20) + q * ((1 - q) * 20) := by
  rw [expectedPayoff_eq]
  simp [symMixed, mix_val, Fin.sum_univ_three, U_vec]
  ring

/-- The payoff of a pure action against `mix q`: "5" earns `0`, "10" earns `10(1 − q) + 20q`,
"20" earns `20(1 − q)`.
Source: bli-paper-077(a)
Kind: D
Fidelity: exact -/
def pureVal (q : ℝ) : Fin 3 → ℝ
  | 0 => 0
  | 1 => (1 - q) * 10 + q * 20
  | 2 => (1 - q) * 20

/-- **The expected payoff after a pure deviation of player `who`** to `s'`, the other copy still
playing `mix q`, is `pureVal q s'`.
Source: bli-paper-077(a)
Kind: L
Fidelity: n/a -/
lemma expectedPayoff_deviate (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (who : Fin 2) (s' : Fin 3) :
    expectedPayoff (directGame U) (deviateMixed (directGame U) (symMixed q h0 h1) who s') who =
      pureVal q s' := by
  rw [expectedPayoff_eq]
  match who with
  | 0 =>
    simp only [deviateMixed, Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), symMixed, pureToMixed_val, mix_val,
      Fin.sum_univ_three, U_vec]
    match s' with
    | 0 => simp [pureVal]
    | 1 => simp [pureVal] <;> ring
    | 2 => simp [pureVal] <;> ring
  | 1 =>
    simp only [deviateMixed, Function.update_self,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), symMixed, pureToMixed_val, mix_val,
      Fin.sum_univ_three, U_vec]
    match s' with
    | 0 => simp [pureVal]
    | 1 => simp [pureVal] <;> ring
    | 2 => simp [pureVal] <;> ring

/-- **The symmetric mixed profile over `{10, 20}` is a mixed Nash equilibrium iff `q = 1/3`**
(for `0 < q < 1`): at a full-support mixture the two pure actions must be indifferent,
`10(1 − q) + 20q = 20(1 − q)`, which forces `q = 1/3`; conversely at `q = 1/3` every pure
deviation earns at most the equilibrium value `40/3`.
Source: bli-paper-077(a) (the inventory's computation `q(20) = 1/3`, value `40/3`)
Kind: P
Fidelity: exact (EconCSLib's `IsMixedNashEq` on the direct form of FAF's instance game)
Hyps: (a) `0 < q < 1` -/
theorem isMixedNashEq_symMixed_iff (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    IsMixedNashEq (directGame U) (symMixed q h0 h1) ↔ q = 1 / 3 := by
  unfold IsMixedNashEq
  simp only [expectedPayoff_deviate, expectedPayoff_symMixed]
  constructor
  · intro h
    have hA : pureVal q 1 ≤ (1 - q) * ((1 - q) * 10 + q * 20) + q * ((1 - q) * 20) := h 0 1
    have hB : pureVal q 2 ≤ (1 - q) * ((1 - q) * 10 + q * 20) + q * ((1 - q) * 20) := h 0 2
    simp only [pureVal] at hA hB
    -- `A ≤ (1-q) A + q B` gives `0 ≤ q (B - A)`; `B ≤ (1-q) A + q B` gives `0 ≤ (1-q)(A - B)`.
    have h2 : 0 ≤ q * ((1 - q) * 20 - ((1 - q) * 10 + q * 20)) := by linarith
    have h3 : 0 ≤ (1 - q) * (((1 - q) * 10 + q * 20) - (1 - q) * 20) := by linarith
    have h4 : 0 ≤ (1 - q) * 20 - ((1 - q) * 10 + q * 20) := nonneg_of_mul_nonneg_right h2 hq0
    have h5 : 0 ≤ ((1 - q) * 10 + q * 20) - (1 - q) * 20 :=
      nonneg_of_mul_nonneg_right h3 (by linarith)
    linarith
  · intro hq
    subst hq
    intro who s'
    match s' with
    | 0 => simp only [pureVal]; norm_num
    | 1 => simp only [pureVal]; norm_num
    | 2 => simp only [pureVal]; norm_num

/-- **At `q = 1/3`: the value is `40/3`, pure "5" is not a best response, and pure "10" and "20"
are both best responses** — the equilibrium is only weakly stable (every pure deviation of a
player onto the support ties).
Source: bli-paper-077(a) (the strict/weak distinction, the inventory's computation)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem third_facts :
    expectedPayoff (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) 0 = 40 / 3 ∧
    expectedPayoff (directGame U)
        (deviateMixed (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) 0 0) 0 <
      40 / 3 ∧
    expectedPayoff (directGame U)
        (deviateMixed (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) 0 1) 0 =
      40 / 3 ∧
    expectedPayoff (directGame U)
        (deviateMixed (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) 0 2) 0 =
      40 / 3 := by
  simp only [expectedPayoff_deviate, expectedPayoff_symMixed, pureVal]
  norm_num

/-- **The mixed resolution is not strictly stable**: a strict mixed equilibrium would need every
pure deviation to lose strictly, but at `q = 1/3` the deviation to pure "10" ties. The asymmetric
joint message `(10, 20)` is strictly stable (`strict_ten_twenty`). So "mixed strategies" resolve
the Third Button only for a weaker stability notion (bli-paper-077(a) against 087's strict
Stability). Kind L (repair round 2, adversarial N4): this is an instance of a general fact — a
pure action in the support of a mixed profile earns exactly the mixed value, so no properly
mixed profile of any game is "strict" in this sense; the Third Button contributes only the
support `{10, 20}`.
Source: bli-paper-077(a), 087
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mixed_not_strict :
    ¬ (∀ (who : Fin 2) (s' : Fin 3),
        expectedPayoff (directGame U)
          (deviateMixed (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) who s') who <
        expectedPayoff (directGame U) (symMixed (1 / 3) (by norm_num) (by norm_num)) who) := by
  intro h
  have := h 0 1
  simp only [expectedPayoff_deviate, expectedPayoff_symMixed, pureVal] at this
  norm_num at this

end

end ThirdButton

end Cleanroom.Udt.UdtPaperTiling
