import Cleanroom.Bli.UdtBliCore.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `udt-bli-core` · MaterialConditional: the `o → a` policy point is EDT under uniform action
probabilities, and the news-management artifact (T8, load-bearing 3; U13)

Over any finite probability `μ` with an observation event `o`, an action coordinate `act` and
a utility `U`:

* `condExp_imp` — the exact formula
  `𝔼[U | o → a] = (μ(¬o) 𝔼[U | ¬o] + μ(o ∧ a) 𝔼[U | o ∧ a]) / (μ(¬o) + μ(o ∧ a))`;
* `condProb_o_imp_le` — conditioning on `o → a` only **lowers** the home branch's weight:
  `μ(o | o → a) ≤ μ(o)`, with equality iff `μ(o ∧ ¬a) = 0 ∨ μ(¬o) = 0`;
* `argmax_imp_iff_argmax_and` — **the `o → a` rule is EDT when the action probabilities given
  `o` are uniform**: the maximizers of `a ↦ 𝔼[U | o → a]` are the maximizers of
  `a ↦ 𝔼[U | o ∧ a]`;
* `newsMap_lt_iff` — the artifact: `x ↦ (p c + x v) / (p + x)` is strictly decreasing in
  `x = μ(o ∧ a)` iff `c > v`, increasing iff `c < v`; `newsPrior` is an explicit prior where the
  `o → a` rule prefers the action with the **worse** home value because it is improbable;
* `foundPrior` — the foundational witness: the universal implication has probability `1`,
  `P` holds with certainty on the state, the state is improbable, and yet the conditional on
  `o → a` puts probability `1/19` on high utility (the Aug-16 chain is a valid *implication* that
  is not the *conditional*).
-/

namespace Cleanroom.Bli.UdtBliCore

open Finset

namespace MatCond

variable {Ω : Type} [Fintype Ω]

/-- `IsArgmax f x`: `x` maximizes `f` (ties allowed), over `ℚ`.
Source: `udt-policy-calc`'s convention (`IsArgmax`), restated over `ℚ`
Kind: D
Fidelity: exact -/
def IsArgmax {X : Type} (f : X → ℚ) (x : X) : Prop := ∀ y, f y ≤ f x

/-- The mass of a disjoint union of two events is the sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_or (μ : Ω → ℚ) (E F : Ω → Prop) [DecidablePred E] [DecidablePred F]
    (hdisj : ∀ ω, E ω → F ω → False) :
    massOf μ (fun ω => E ω ∨ F ω) = massOf μ E + massOf μ F := by
  unfold massOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω
  · exact absurd hF (hdisj ω hE)
  · simp [hE, hF]
  · simp [hE, hF]
  · simp [hE, hF]

/-- The integral over a disjoint union of two events is the sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_or (μ f : Ω → ℚ) (E F : Ω → Prop) [DecidablePred E] [DecidablePred F]
    (hdisj : ∀ ω, E ω → F ω → False) :
    integralOf μ f (fun ω => E ω ∨ F ω) = integralOf μ f E + integralOf μ f F := by
  unfold integralOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω
  · exact absurd hF (hdisj ω hE)
  · simp [hE, hF]
  · simp [hE, hF]
  · simp [hE, hF]

variable {A : Type} (μ U : Ω → ℚ) (o : Ω → Prop) [DecidablePred o] (act : Ω → A)
  [DecidableEq A]

/-- The event `o → act = a` is the disjoint union of `¬o` and `o ∧ act = a`.
Source: bli-soto-b-2-001 (`{o → a} = ¬o ∪̇ (o ∧ a)`)
Kind: L
Fidelity: n/a -/
lemma imp_iff (a : A) (ω : Ω) : (o ω → act ω = a) ↔ (¬ o ω ∨ (o ω ∧ act ω = a)) := by
  by_cases h : o ω <;> simp [h]

/-- **The exact formula for the material-conditional policy point**:
`𝔼[U | o → a] = (μ(¬o) 𝔼[U | ¬o] + μ(o ∧ a) 𝔼[U | o ∧ a]) / (μ(¬o) + μ(o ∧ a))`
(with the junk conventions; the `¬o` term does not depend on `a`).
Source: bli-soto-b-2-001 (the formula); bli-soto-a-074 (ii); email Sep 14 4:06 PM
Kind: P
Fidelity: exact
Hyps: (a) `μ ≥ 0` -/
theorem condExp_imp (hμ : ∀ ω, 0 ≤ μ ω) (a : A) :
    condExp μ U (fun ω => o ω → act ω = a) =
      (massOf μ (fun ω => ¬ o ω) * condExp μ U (fun ω => ¬ o ω) +
        massOf μ (fun ω => o ω ∧ act ω = a) * condExp μ U (fun ω => o ω ∧ act ω = a)) /
      (massOf μ (fun ω => ¬ o ω) + massOf μ (fun ω => o ω ∧ act ω = a)) := by
  rw [mul_comm (massOf μ _) (condExp μ U _), mul_comm (massOf μ _) (condExp μ U _),
    condExp_mul_massOf μ U hμ, condExp_mul_massOf μ U hμ]
  unfold condExp
  rw [massOf_congr μ (imp_iff o act a), integralOf_congr μ U (imp_iff o act a),
    massOf_or μ _ _ (fun ω h1 h2 => h1 h2.1), integralOf_or μ U _ _ (fun ω h1 h2 => h1 h2.1)]

/-- The total mass splits as `μ(¬o) + μ(o ∧ a) + μ(o ∧ ¬a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_split (a : A) :
    massOf μ (fun _ => True) =
      massOf μ (fun ω => ¬ o ω) + massOf μ (fun ω => o ω ∧ act ω = a) +
        massOf μ (fun ω => o ω ∧ act ω ≠ a) := by
  unfold massOf
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ho : o ω <;> by_cases ha : act ω = a <;> simp [ho, ha]

/-- `μ(o) = μ(o ∧ a) + μ(o ∧ ¬a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_o_split (a : A) :
    massOf μ o = massOf μ (fun ω => o ω ∧ act ω = a) + massOf μ (fun ω => o ω ∧ act ω ≠ a) := by
  unfold massOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ho : o ω <;> by_cases ha : act ω = a <;> simp [ho, ha]

/-- **Conditioning on `o → a` only lowers the home branch's weight**:
`μ(o | o → a) = μ(o ∧ a) / (μ(¬o) + μ(o ∧ a)) ≤ μ(o)`, with equality iff
`μ(o ∧ ¬a) = 0 ∨ μ(¬o) = 0`.
Source: bli-soto-b-2-001 (ii); journal l. 268 ("only changes the relative weight of the home
branch compared to others, and also only reduces that weight")
Kind: P
Fidelity: exact
Hyps: (a) `μ ≥ 0`, `∑ μ = 1`, `0 < μ(¬o) + μ(o ∧ a)` -/
theorem condProb_o_imp_le (hμ : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (a : A)
    (hpos : 0 < massOf μ (fun ω => ¬ o ω) + massOf μ (fun ω => o ω ∧ act ω = a)) :
    massOf μ (fun ω => o ω ∧ act ω = a) /
        (massOf μ (fun ω => ¬ o ω) + massOf μ (fun ω => o ω ∧ act ω = a)) ≤ massOf μ o ∧
      (massOf μ (fun ω => o ω ∧ act ω = a) /
        (massOf μ (fun ω => ¬ o ω) + massOf μ (fun ω => o ω ∧ act ω = a)) = massOf μ o ↔
        massOf μ (fun ω => o ω ∧ act ω ≠ a) = 0 ∨ massOf μ (fun ω => ¬ o ω) = 0) := by
  have htot : massOf μ (fun _ => True) = 1 := by unfold massOf; simpa using h1
  have hsplit := mass_split μ o act a
  rw [htot] at hsplit
  have hosplit := massOf_o_split μ o act a
  set p := massOf μ (fun ω => ¬ o ω) with hp
  set x := massOf μ (fun ω => o ω ∧ act ω = a) with hx
  set y := massOf μ (fun ω => o ω ∧ act ω ≠ a) with hy
  have hpnn : 0 ≤ p := massOf_nonneg μ hμ _
  have hxnn : 0 ≤ x := massOf_nonneg μ hμ _
  have hynn : 0 ≤ y := massOf_nonneg μ hμ _
  rw [hosplit]
  constructor
  · rw [div_le_iff₀ hpos]
    nlinarith [hsplit, hpnn, hxnn, hynn]
  · rw [div_eq_iff (ne_of_gt hpos)]
    constructor
    · intro heq
      have : y * p = 0 := by nlinarith [hsplit, heq]
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · rw [h] at hsplit ⊢; nlinarith [hsplit]
      · rw [h] at hsplit ⊢; nlinarith [hsplit]

/-- **The `o → a` rule is EDT under uniform action probabilities** (load-bearing 3): if
`μ(o ∧ act = a)` is the same positive number for every action, then the maximizers of
`a ↦ 𝔼[U | o → a]` are exactly the maximizers of `a ↦ 𝔼[U | o ∧ a]`.
Source: bli-soto-a-074 (ii) ("Abram's theorem", email Sep 14 4:06 PM: "if the action
probability `P(a | o)` for each action is identical … precisely equivalent to EDT");
bli-soto-b-049
Kind: P
Fidelity: exact (finite; uniformity as the hypothesis `μ(o ∧ a) = μ(o ∧ b)`, positive)
Hyps: (a) `μ ≥ 0`, uniform positive action masses on `o` -/
theorem argmax_imp_iff_argmax_and (hμ : ∀ ω, 0 ≤ μ ω) (c : ℚ) (hc : 0 < c)
    (huni : ∀ a, massOf μ (fun ω => o ω ∧ act ω = a) = c) (a : A) :
    IsArgmax (fun b => condExp μ U (fun ω => o ω → act ω = b)) a ↔
      IsArgmax (fun b => condExp μ U (fun ω => o ω ∧ act ω = b)) a := by
  have hform : ∀ b, condExp μ U (fun ω => o ω → act ω = b) =
      (massOf μ (fun ω => ¬ o ω) * condExp μ U (fun ω => ¬ o ω) +
        c * condExp μ U (fun ω => o ω ∧ act ω = b)) / (massOf μ (fun ω => ¬ o ω) + c) := by
    intro b
    rw [condExp_imp μ U o act hμ b, huni b]
  have hden : 0 < massOf μ (fun ω => ¬ o ω) + c :=
    add_pos_of_nonneg_of_pos (massOf_nonneg μ hμ _) hc
  unfold IsArgmax
  apply forall_congr'
  intro b
  simp only [hform]
  rw [div_le_div_iff_of_pos_right hden, add_le_add_iff_left, mul_le_mul_iff_of_pos_left hc]

/-! ## The news-management artifact -/

/-- The value of the `o → a` rule as a function of the action's mass `x = μ(o ∧ a)`, with
`p = μ(¬o)`, `c = 𝔼[U | ¬o]`, `v = 𝔼[U | o ∧ a]`.
Source: bli-soto-a-2-010
Kind: D
Fidelity: exact -/
def newsMap (p c v x : ℚ) : ℚ := (p * c + x * v) / (p + x)

/-- **The artifact**: for `0 < p` and `0 < x₁ < x₂`, `newsMap` at `x₂` is strictly below its value
at `x₁` iff `v < c` (the other branch is better), and strictly above iff `c < v`. So two actions
with the same home value are ranked by their probability alone, the *less* probable winning when
the other branch is better.
Source: bli-soto-a-2-010 (Soto, Sep 14 7:02 PM: "the fluctuating ratio between `P(o&a)` and
`P(¬o)` can indeed change `E(U)`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < p`, `0 < x₁ < x₂` -/
theorem newsMap_lt_iff (p c v x₁ x₂ : ℚ) (hp : 0 < p) (h1 : 0 < x₁) (h12 : x₁ < x₂) :
    (newsMap p c v x₂ < newsMap p c v x₁ ↔ v < c) ∧
      (newsMap p c v x₁ < newsMap p c v x₂ ↔ c < v) := by
  have hd1 : 0 < p + x₁ := by linarith
  have hd2 : 0 < p + x₂ := by linarith
  have hpx : 0 < p * (x₂ - x₁) := mul_pos hp (sub_pos.mpr h12)
  have key : (p * c + x₂ * v) * (p + x₁) - (p * c + x₁ * v) * (p + x₂) =
      p * (x₂ - x₁) * (v - c) := by ring
  unfold newsMap
  constructor
  · rw [div_lt_iff₀ hd2, div_mul_eq_mul_div, lt_div_iff₀ hd1]
    constructor
    · intro h; nlinarith [key, hpx, h]
    · intro h; nlinarith [key, hpx, h]
  · rw [div_lt_iff₀ hd1, div_mul_eq_mul_div, lt_div_iff₀ hd2]
    constructor
    · intro h; nlinarith [key, hpx, h]
    · intro h; nlinarith [key, hpx, h]

/-- The masses of the artifact witness: `¬o` with mass `1/2`, `o ∧ a₁` with mass `2/5`,
`o ∧ a₂` with mass `1/10`.
Source: bli-soto-a-2-010 (corollary)
Kind: D
Fidelity: exact -/
def newsMass : Fin 3 → ℚ
  | 0 => 1 / 2
  | 1 => 2 / 5
  | 2 => 1 / 10

/-- The utilities of the artifact witness: `10` on `¬o`, `2` on `o ∧ a₁`, `1` on `o ∧ a₂`.
Source: bli-soto-a-2-010 (corollary)
Kind: D
Fidelity: exact -/
def newsU : Fin 3 → ℚ
  | 0 => 10
  | 1 => 2
  | 2 => 1

/-- The observation `o` (as a Boolean): holds off world `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def newsOb : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => true

/-- `newsOb 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsOb_zero : newsOb 0 = false := rfl
/-- `newsOb 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsOb_one : newsOb 1 = true := rfl
/-- `newsOb 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsOb_two : newsOb 2 = true := rfl

/-- The observation `o` holds off world `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev newsO (i : Fin 3) : Prop := newsOb i = true

/-- The action: `true = a₁` at world `1`, `false = a₂` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def newsAct : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => false

/-- `newsAct 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsAct_zero : newsAct 0 = false := rfl
/-- `newsAct 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsAct_one : newsAct 1 = true := rfl
/-- `newsAct 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsAct_two : newsAct 2 = false := rfl

/-- `newsMass` values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsMass_zero : newsMass 0 = 1 / 2 := rfl
/-- `newsMass 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsMass_one : newsMass 1 = 2 / 5 := rfl
/-- `newsMass 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsMass_two : newsMass 2 = 1 / 10 := rfl
/-- `newsU 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsU_zero : newsU 0 = 10 := rfl
/-- `newsU 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsU_one : newsU 1 = 2 := rfl
/-- `newsU 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma newsU_two : newsU 2 = 1 := rfl

/-- **The artifact, witnessed**: the home values are `𝔼[U | o ∧ a₁] = 2 > 1 = 𝔼[U | o ∧ a₂]`, yet
the `o → a` rule prefers `a₂`: `𝔼[U | o → a₂] = 17/2 > 58/9 = 𝔼[U | o → a₁]` — because `a₂` is
improbable and the other branch (`10`) is better than either home value.
Source: bli-soto-a-2-010 (corollary: "for any `v₁ > v₂` there are action probabilities making
the `o → a` rule prefer the action with value `v₂`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem newsPrior_artifact :
    condExp newsMass newsU (fun i => newsO i ∧ newsAct i = true) = 2 ∧
      condExp newsMass newsU (fun i => newsO i ∧ newsAct i = false) = 1 ∧
      condExp newsMass newsU (fun i => newsO i → newsAct i = true) = 58 / 9 ∧
      condExp newsMass newsU (fun i => newsO i → newsAct i = false) = 17 / 2 ∧
      ∑ i, newsMass i = 1 := by
  have hsum : ∑ i, newsMass i = 1 := by rw [Fin.sum_univ_three]; norm_num
  refine ⟨?_, ?_, ?_, ?_, hsum⟩ <;>
  · simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three]
    norm_num

/-! ## The foundational witness -/

/-- The masses of the foundational witness: world `0` is `¬Q` (mass `9/10`), world `1` is
`Q ∧ P ∧ A = a ∧ ↑U` (mass `1/20`), world `2` is `Q ∧ P ∧ A = b ∧ ¬↑U` (mass `1/20`).
Source: bli-soto-b-019 (Soto's PDF 16); bli-soto-a-074 (i)
Kind: D
Fidelity: exact -/
def foundMass : Fin 3 → ℚ
  | 0 => 9 / 10
  | 1 => 1 / 20
  | 2 => 1 / 20

/-- `Q_m = Q` (Boolean): holds off world `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def foundQb : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => true

/-- The action is `a` (Boolean): off world `2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def foundAb : Fin 3 → Bool
  | 0 => true
  | 1 => true
  | 2 => false

/-- High utility (Boolean): only at world `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def foundHiUb : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => false

/-- `foundQb 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundQb_zero : foundQb 0 = false := rfl
/-- `foundQb 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundQb_one : foundQb 1 = true := rfl
/-- `foundQb 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundQb_two : foundQb 2 = true := rfl
/-- `foundAb 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundAb_zero : foundAb 0 = true := rfl
/-- `foundAb 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundAb_one : foundAb 1 = true := rfl
/-- `foundAb 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundAb_two : foundAb 2 = false := rfl
/-- `foundHiUb 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundHiUb_zero : foundHiUb 0 = false := rfl
/-- `foundHiUb 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundHiUb_one : foundHiUb 1 = true := rfl
/-- `foundHiUb 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundHiUb_two : foundHiUb 2 = false := rfl
/-- `foundMass 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundMass_zero : foundMass 0 = 9 / 10 := rfl
/-- `foundMass 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundMass_one : foundMass 1 = 1 / 20 := rfl
/-- `foundMass 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma foundMass_two : foundMass 2 = 1 / 20 := rfl

/-- `Q_m = Q` holds off world `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev foundQ (i : Fin 3) : Prop := foundQb i = true

/-- The property `P(Q)` holds off world `0` (so `Q` knows it). **Identified with `Q_m = Q`**
(`foundP` and `foundQ` are the same event): `P(Q)` is false on every `¬(Q_m = Q)` world by
construction, the extreme instance of the source's "in the former worlds this might not be the
case" (PDF 16 p. 1), disclosed.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev foundP (i : Fin 3) : Prop := foundQb i = true

/-- The action is `a` off world `2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev foundA (i : Fin 3) : Prop := foundAb i = true

/-- High utility holds only at world `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev foundHiU (i : Fin 3) : Prop := foundHiUb i = true

/-- **The foundational witness**: the universal's instance `P(Q) ∧ (Q_m = Q → A = a) → ↑U` has
probability `1`, `P(Q)` is certain given `Q_m = Q`, `Q_m = Q` is improbable (`1/10`), yet
`μ(↑U | Q_m = Q → A = a) = 1/19` — while `μ(↑U | Q_m = Q ∧ A = a) = 1` (full updatefulness) and
the Aug-16 chain's implication `Q_m = Q → (A = a → ↑U)` also has probability `1`: the chain is a
valid implication that is not the conditional.
Source: bli-soto-b-019 (Soto's PDF 16, "Implication" and "Desire"); bli-soto-b-050 (the
retraction); bli-soto-a-091 (the Aug-16 chain)
Kind: N+
Fidelity: exact, with one disclosed degeneracy: `P(Q)` is identified with `Q_m = Q`
(`foundP := foundQb`), so clause 2 (`μ(P(Q) | Q_m = Q) = 1`) holds by definition; the
Implication/Desire gap (`1` vs `1/19`) is the content and does not depend on it
Hyps: (a) none -/
theorem foundPrior_witness :
    massOf foundMass (fun i => foundP i ∧ (foundQ i → foundA i) → foundHiU i) = 1 ∧
      condExp foundMass (fun i => ind (decide (foundP i))) foundQ = 1 ∧
      massOf foundMass foundQ = 1 / 10 ∧
      condExp foundMass (fun i => ind (decide (foundHiU i))) (fun i => foundQ i → foundA i) =
        1 / 19 ∧
      condExp foundMass (fun i => ind (decide (foundHiU i))) (fun i => foundQ i ∧ foundA i) = 1 ∧
      massOf foundMass (fun i => foundQ i → (foundA i → foundHiU i)) = 1 ∧
      ∑ i, foundMass i = 1 := by
  have hsum : ∑ i, foundMass i = 1 := by rw [Fin.sum_univ_three]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hsum⟩ <;>
  · simp only [condExp, massOf, integralOf, foundQ, foundP, foundA, foundHiU, Fin.sum_univ_three]
    norm_num [ind]

/-! ## An N+ inhabitant of the uniformity hypothesis (repair round 1) -/

/-- Masses `¬o ↦ 1/2`, `o ∧ a₁ ↦ 1/4`, `o ∧ a₂ ↦ 1/4`: uniform action masses on `o`, with the
artifact's `newsU`, `newsO`, `newsAct`.
Source: bli-soto-a-074 (ii) (the uniformity hypothesis, inhabited)
Kind: D
Fidelity: n/a -/
def uMass : Fin 3 → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 4
  | 2 => 1 / 4

/-- `uMass 0 = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma uMass_zero : uMass 0 = 1 / 2 := rfl

/-- `uMass 1 = 1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma uMass_one : uMass 1 = 1 / 4 := rfl

/-- `uMass 2 = 1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma uMass_two : uMass 2 = 1 / 4 := rfl

/-- `uMass` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uMass_nonneg (i : Fin 3) : 0 ≤ uMass i := by
  match i with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num

/-- The action masses on `o` are uniform: `μ(o ∧ act = a) = 1/4` for both `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma uMass_uniform (a : Bool) : massOf uMass (fun i => newsO i ∧ newsAct i = a) = 1 / 4 := by
  cases a <;> simp only [massOf, newsO, Fin.sum_univ_three] <;> norm_num

/-- **The uniformity hypothesis of `argmax_imp_iff_argmax_and`, inhabited non-degenerately**:
under uniform action masses the `o → a` rule and EDT agree, and the instance has a unique
maximizer (`𝔼[U | o ∧ a₁] = 2 > 1`, `𝔼[U | o → a₁] = 22/3 > 7`), so the theorem transfers a
strict preference, not a tie. The N+ for load-bearing 3 (the artifact `newsPrior_artifact` is its
N−, where uniformity fails).
Source: bli-soto-a-074 (ii) (email Sep 14 4:06 PM); audit r1 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem uniform_witness :
    condExp uMass newsU (fun i => newsO i ∧ newsAct i = true) = 2 ∧
      condExp uMass newsU (fun i => newsO i ∧ newsAct i = false) = 1 ∧
      condExp uMass newsU (fun i => newsO i → newsAct i = true) = 22 / 3 ∧
      condExp uMass newsU (fun i => newsO i → newsAct i = false) = 7 ∧
      IsArgmax (fun b => condExp uMass newsU (fun i => newsO i → newsAct i = b)) true ∧
      ¬ IsArgmax (fun b => condExp uMass newsU (fun i => newsO i → newsAct i = b)) false := by
  have hEDT : IsArgmax (fun b => condExp uMass newsU (fun i => newsO i ∧ newsAct i = b)) true := by
    intro b; cases b <;> simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three] <;>
      norm_num
  have hiff := argmax_imp_iff_argmax_and uMass newsU newsO newsAct uMass_nonneg (1 / 4)
    (by norm_num) uMass_uniform
  refine ⟨?_, ?_, ?_, ?_, (hiff true).mpr hEDT, fun h => ?_⟩
  · simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three]; norm_num
  · simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three]; norm_num
  · simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three]; norm_num
  · simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three]; norm_num
  · have := h true
    simp only [condExp, massOf, integralOf, newsO, Fin.sum_univ_three] at this
    norm_num at this

end MatCond

end Cleanroom.Bli.UdtBliCore
