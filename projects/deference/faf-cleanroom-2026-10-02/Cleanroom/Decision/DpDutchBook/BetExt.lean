import Cleanroom.Decision.DpDutchBook.Defs
import Cleanroom.Found.DpCoreTree.Occurrence
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# T1: the bet extension `B'` and the leaf-wise book identity

**The definition of record** (P12.md line 7, the 2020 ordering "buy before, sell during"): given
a base tree `B`, the address `q₀` of the real `d`-node (`d = pt B q₀`), the booked act `a`, the
supposed value `ca = c(a)`, the sign `s`, and the fee `δ`, the extension `attachBet` inserts a
bet point `d_B` (point `inr ()`, acts `Bool`: `true` = buy) **immediately above `q₀` only**,
replaces every `d`-node's action set by `acts d × Side` (`Side = keep | sell`; the side
coordinate is **ignored** at every node other than `q₀` — routed identically, payoff-irrelevant —
so `betActs` is non-dependent in the point's identity; disclosed), routes every decision node on
the base component, and pays
`r' = r − 2δ·[buy] + [buy ∧ base = a ∧ keep]·(ca − r)·s + [buy ∧ sell]·δ` (`betPay`) on the
leaves below `q₀`, `r` elsewhere. Worlds are `Ω × Bool × Side` (world, bought, side at `q₀`;
`(ω, false, keep)` off the path through `q₀`).

`attachBetRegardless` is the same construction with P09's reverse bet `R` offered at `d'`
regardless of the choice at `d_B` (`betPayR`: receive `δ`, owe `(ca − r)·s` on base-`a` runs) —
a second payoff function passed to the one constructor `ext`, never a flag inside a definition.

* `booked` — the booked act as an assignment `π : (e : ι) → acts e` (only `π d` is read; this
  avoids transporting `a : acts (pt B q)` along the recursion; disclosed).
* `liftProc C σ₀ bet` — the extended procedure: base per `C` at every `inl e`, side `σ₀`
  deterministically, bet law `bet` at `d_B`. `liftProc_base_marginal` is **label honesty**
  (T1(d)): the base marginal at every `inl e` is `C e`.
* `ext_sum` — **the master identity**: every leaf-sum over `B'` under `liftProc` equals a
  leaf-sum over `B` in which a leaf below `q₀` taking edge `x` carries the bet law's average of
  the extended payoff `betPay bt (x = a) σ₀ r`, and every other leaf its base payoff.
* `value_attachBet_book`, `value_attachBet_dec`, `betPay_book_sub_dec` — **T1(e), the leaf-wise
  book identity**: `V_{B'}(C_book) = V_{B'}(C_dec) − δ · R_{q₀}(C)`, from the leaf-wise
  `r'(buy, sell) − r'(decline, keep) = −δ` on every leaf below `q₀`. The `−δ` of P12-1 is the
  `R_{q₀} = 1` case (every run reaches the bet point).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

/-- The side coordinate at the real node: keep the bet or sell it back.
Source: P12.md line 7 (`A_d × {keep, sell}`)
Kind: D -/
inductive Side : Type
  | keep
  | sell
  deriving DecidableEq, Fintype

instance : Nonempty Side := ⟨.keep⟩

/-- Sums over `Side`. Source: none: infrastructure. Kind: L -/
theorem Side.sum_univ {M : Type} [AddCommMonoid M] (f : Side → M) : ∑ x, f x = f .keep + f .sell := by
  have : (Finset.univ : Finset Side) = {.keep, .sell} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- The extended action sets: `acts e × Side` at every base point, `Bool` (buy/decline) at the
bet point.
Source: P12.md line 7
Kind: D
Fidelity: variant: the side coordinate is carried at every base point and ignored off `q₀` -/
def betActs (acts : ι → Type) : ι ⊕ Unit → Type
  | .inl e => acts e × Side
  | .inr _ => Bool

instance instFintypeBetActs : ∀ e : ι ⊕ Unit, Fintype (betActs acts e)
  | .inl e => inferInstanceAs (Fintype (acts e × Side))
  | .inr _ => inferInstanceAs (Fintype Bool)

instance instDecidableEqBetActs : ∀ e : ι ⊕ Unit, DecidableEq (betActs acts e)
  | .inl e => inferInstanceAs (DecidableEq (acts e × Side))
  | .inr _ => inferInstanceAs (DecidableEq Bool)

instance instNonemptyBetActs [∀ d, Nonempty (acts d)] : ∀ e : ι ⊕ Unit, Nonempty (betActs acts e)
  | .inl e => inferInstanceAs (Nonempty (acts e × Side))
  | .inr _ => inferInstanceAs (Nonempty Bool)

/-- The extended worlds: `(base world, bought, side at q₀)`.
Source: P12.md line 7
Kind: D -/
abbrev BetW (Ω : Type) : Type := Ω × Bool × Side

/-- **P12's extended payoff** on a leaf below `q₀`:
`r − 2δ·[buy] + [buy ∧ base = a ∧ keep]·(ca − r)·s + [buy ∧ sell]·δ`.
Source: P12.md line 7 (`r' = r − 2δ[buy] + [buy ∧ base=a ∧ keep](c − r)s + [buy ∧ sell]δ`)
Kind: D
Fidelity: exact -/
def betPay (δ ca s : K) (b isA : Bool) (σ : Side) (r : K) : K :=
  r - (if b then 2 * δ else 0) + (if b ∧ isA ∧ σ = .keep then (ca - r) * s else 0) +
    (if b ∧ σ = .sell then δ else 0)

/-- **P09's "regardless" payoff**: the reverse bet `R` (receive `δ`, owe `(ca − r)·s` on base-`a`
runs) is taken at `d'` by choosing `sell`, whether or not the bet was bought:
`r − 2δ·[buy] + [buy ∧ base = a]·(ca − r)·s + [sell]·(δ − [base = a]·(ca − r)·s)`.
Source: P12.md line 7 ("Reverse bet `R` (P09's device …) offered at `d'` regardless"); P09.md
lines 5–7
Kind: D
Fidelity: exact -/
def betPayR (δ ca s : K) (b isA : Bool) (σ : Side) (r : K) : K :=
  r - (if b then 2 * δ else 0) + (if b ∧ isA then (ca - r) * s else 0) +
    (if σ = .sell then δ - (if isA then (ca - r) * s else 0) else 0)

/-- Leaf-wise: buying then selling loses exactly `δ` against declining and keeping (P12's book).
Source: P12-1 ("`r'(ℓ^buy) − r'(ℓ^dec) = −2δ + δ = −δ` on every leaf pair")
Kind: L -/
theorem betPay_book_sub_dec (δ ca s : K) (isA : Bool) (r : K) :
    betPay δ ca s true isA .sell r - betPay δ ca s false isA .keep r = -δ := by
  simp [betPay]; ring

/-- Leaf-wise, with the reverse bet offered regardless: buying then selling still loses exactly
`δ` against declining and keeping.
Source: P09-1 ("`−(k − k′)` on every reached leaf"); P12-3 ("the pair loses `δ` in every world")
Kind: L -/
theorem betPayR_book_sub_dec (δ ca s : K) (isA : Bool) (r : K) :
    betPayR δ ca s true isA .sell r - betPayR δ ca s false isA .keep r = -δ := by
  cases isA <;> simp [betPayR] <;> ring

/-- The product of a distribution with a point mass on the second coordinate.
Source: none: infrastructure
Kind: D -/
def FinDistr.prodPure {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (m : FinDistr K α)
    (σ : β) : FinDistr K (α × β) where
  w xy := m.w xy.1 * (if xy.2 = σ then 1 else 0)
  nonneg xy := mul_nonneg (m.nonneg _) (by split_ifs <;> norm_num)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact m.sum_one

/-- **The extended procedure**: base per `C` at every base point, side `σ₀` deterministically,
bet law `bet` at the bet point.
Source: P12.md lines 7–9 (`C_book`, `C_dec`; the myopic/sophisticated `d_B` states)
Kind: D -/
def liftProc (C : Proc ι acts K) (σ₀ : Side) (bet : FinDistr K Bool) : Proc (ι ⊕ Unit) (betActs acts) K
  | .inl e => FinDistr.prodPure (C e) σ₀
  | .inr _ => bet

/-- Weights of the extended procedure at a base point. Source: none: infrastructure. Kind: L -/
@[simp] theorem liftProc_inl_w (C : Proc ι acts K) (σ₀ : Side) (bet : FinDistr K Bool) (e : ι)
    (x : acts e) (τ : Side) :
    (liftProc C σ₀ bet (.inl e)).w (x, τ) = (C e).w x * (if τ = σ₀ then 1 else 0) := rfl

/-- Weights of the extended procedure at the bet point. Source: none: infrastructure. Kind: L -/
@[simp] theorem liftProc_inr_w (C : Proc ι acts K) (σ₀ : Side) (bet : FinDistr K Bool) (b : Bool) :
    (liftProc C σ₀ bet (.inr ())).w b = bet.w b := rfl

/-- **Label honesty (T1(d), P12's A2)**: the base marginal of the extended procedure at every base
point is `C e` — `C'(d')(x-keep) + C'(d')(x-sell) = C(d)(x)`.
Source: P12.md line 7 ("Label honesty (the post's A2)"); mandate T1(d)
Kind: L
Fidelity: exact -/
theorem liftProc_base_marginal (C : Proc ι acts K) (σ₀ : Side) (bet : FinDistr K Bool) (e : ι)
    (x : acts e) : ∑ τ, (liftProc C σ₀ bet (.inl e)).w (x, τ) = (C e).w x := by
  simp only [liftProc_inl_w, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

variable [DecidableEq ι]

/-- **The one constructor** behind both extensions: walk the tree towards the target node
(`some q`), inserting the bet point above it; below it (`none`) carry the state
`(bought, base = a, side)` to the leaves and apply `pay`. Every decision node routes on the base
component; the side coordinate is ignored except at the target node.
Source: P12.md line 7; mandate T1(a)–(b)
Kind: D
Fidelity: exact (the booked act is read off an assignment `π` at the target's point) -/
def ext (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e) :
    Bool → Bool → Side → (T : Tree Ω ι acts K) → Option T.DecNode →
      Tree (BetW Ω) (ι ⊕ Unit) (betActs acts) K
  | b, isA, σ, .leaf ω r, _ => .leaf (ω, b, σ) (pay b isA σ r)
  | b, isA, σ, .chance n β child, none => .chance n β fun j => ext pay π b isA σ (child j) none
  | b, isA, σ, .chance n β child, some ⟨i, q⟩ =>
      .chance n β fun j => ext pay π b isA σ (child j) (if h : j = i then some (h ▸ q) else none)
  | b, isA, σ, .decision e child, none =>
      .decision (.inl e) fun xτ => ext pay π b isA σ (child xτ.1) none
  | _, _, _, .decision e child, some none =>
      .decision (.inr ()) fun bt =>
        .decision (.inl e) fun xτ => ext pay π bt (decide (xτ.1 = π e)) xτ.2 (child xτ.1) none
  | b, isA, σ, .decision e child, some (some ⟨y, q⟩) =>
      .decision (.inl e) fun xτ =>
        ext pay π b isA σ (child xτ.1) (if h : xτ.1 = y then some (h ▸ q) else none)

/-- **`attachBet` (the definition of record, P12's 2020 ordering)**: the bet point inserted above
`q₀`, P12's payoff.
Source: P12.md line 7; mandate T1(a)
Kind: D
Fidelity: exact (see the module docstring for the two disclosed conventions) -/
def attachBet (δ ca s : K) (π : (e : ι) → acts e) (B : Tree Ω ι acts K) (q₀ : B.DecNode) :
    Tree (BetW Ω) (ι ⊕ Unit) (betActs acts) K :=
  ext (betPay δ ca s) π false false .keep B (some q₀)

/-- **`attachBetRegardless`** (P09's device): the same extension with the reverse bet offered at
`d'` regardless.
Source: P12.md line 7 (Reverse bet `R`); P09.md lines 5–7; mandate T1(b)
Kind: D
Fidelity: exact -/
def attachBetRegardless (δ ca s : K) (π : (e : ι) → acts e) (B : Tree Ω ι acts K)
    (q₀ : B.DecNode) : Tree (BetW Ω) (ι ⊕ Unit) (betActs acts) K :=
  ext (betPayR δ ca s) π false false .keep B (some q₀)

/-- Sums over the single leaf of a leaf tree, any field. Source: none: infrastructure. Kind: L -/
theorem sum_leaves_leaf' {M : Type} [AddCommMonoid M] (ω : Ω) (r : K)
    (f : (Tree.leaf ω r : Tree Ω ι acts K).Leaves → M) : ∑ ℓ, f ℓ = f () := by
  show ∑ ℓ : Unit, f ℓ = f ()
  simp

/-- The right-hand side of the master identity: the base-leaf weight of a leaf-sum over `B'`.
Source: none: infrastructure
Kind: D -/
def extG (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e) (g : BetW Ω → K → K)
    (bet : FinDistr K Bool) (σ₀ : Side) (b isA : Bool) (σ : Side) (T : Tree Ω ι acts K)
    (o : Option T.DecNode) (ℓ : T.Leaves) : K :=
  match o with
  | none => g (world T ℓ, b, σ) (pay b isA σ (payoff T ℓ))
  | some q =>
      match edgeOf T q ℓ with
      | some x => ∑ bt : Bool, bet.w bt *
          g (world T ℓ, bt, σ₀) (pay bt (decide (x = π (pt T q))) σ₀ (payoff T ℓ))
      | none => g (world T ℓ, b, σ) (pay b isA σ (payoff T ℓ))

/-- `extG` below the target. Source: none: infrastructure. Kind: L -/
@[simp] theorem extG_none (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e)
    (g : BetW Ω → K → K) (bet : FinDistr K Bool) (σ₀ : Side) (b isA : Bool) (σ : Side)
    (T : Tree Ω ι acts K) (ℓ : T.Leaves) :
    extG pay π g bet σ₀ b isA σ T none ℓ = g (world T ℓ, b, σ) (pay b isA σ (payoff T ℓ)) := rfl

/-- `extG` below the target passes through a chance node. Source: none: infrastructure. Kind: L -/
theorem extG_chance_none (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e)
    (g : BetW Ω → K → K) (bet : FinDistr K Bool) (σ₀ : Side) (b isA : Bool) (σ : Side) {n : ℕ}
    (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) (j : Fin n) (ℓ : (child j).Leaves) :
    extG pay π g bet σ₀ b isA σ (.chance n β child) none ⟨j, ℓ⟩ =
      extG pay π g bet σ₀ b isA σ (child j) none ℓ := rfl

/-- `extG` below the target passes through a decision node. Source: none: infrastructure. Kind: L -/
theorem extG_decision_none (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e)
    (g : BetW Ω → K → K) (bet : FinDistr K Bool) (σ₀ : Side) (b isA : Bool) (σ : Side) (e : ι)
    (child : acts e → Tree Ω ι acts K) (x : acts e) (ℓ : (child x).Leaves) :
    extG pay π g bet σ₀ b isA σ (.decision e child) none ⟨x, ℓ⟩ =
      extG pay π g bet σ₀ b isA σ (child x) none ℓ := rfl

/-- `extG` at a target, by the edge taken. Source: none: infrastructure. Kind: L -/
theorem extG_some (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e)
    (g : BetW Ω → K → K) (bet : FinDistr K Bool) (σ₀ : Side) (b isA : Bool) (σ : Side)
    (T : Tree Ω ι acts K) (q : T.DecNode) (ℓ : T.Leaves) :
    extG pay π g bet σ₀ b isA σ T (some q) ℓ =
      match edgeOf T q ℓ with
      | some x => ∑ bt : Bool, bet.w bt *
          g (world T ℓ, bt, σ₀) (pay bt (decide (x = π (pt T q))) σ₀ (payoff T ℓ))
      | none => g (world T ℓ, b, σ) (pay b isA σ (payoff T ℓ)) := rfl

section master

variable (pay : Bool → Bool → Side → K → K) (π : (e : ι) → acts e) (g : BetW Ω → K → K)
  (C : Proc ι acts K) (bet : FinDistr K Bool) (σ₀ : Side)

/-- The side sum with a deterministic side: only `σ₀` contributes.
Source: none: infrastructure. Kind: L -/
theorem sum_side_prodPure (F : Side → K) :
    ∑ τ : Side, (if τ = σ₀ then 1 else 0) * F τ = F σ₀ := by
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Sums over the extended actions at a base point split into base act and side.
Source: none: infrastructure. Kind: L -/
theorem sum_betActs_inl {M : Type} [AddCommMonoid M] (e : ι) (f : betActs acts (.inl e) → M) :
    ∑ xτ, f xτ = ∑ x : acts e, ∑ τ : Side, f (x, τ) :=
  Fintype.sum_prod_type f

/-- Sums over the extended actions at the bet point are sums over `Bool`.
Source: none: infrastructure. Kind: L -/
theorem sum_betActs_inr {M : Type} [AddCommMonoid M] (f : betActs acts (.inr ()) → M) :
    ∑ b, f b = ∑ b : Bool, f b := rfl

/-- A leaf-sum over an extended tree under the extended procedure (the left-hand side of the
master identity, packaged so that the tree can be rewritten).
Source: none: infrastructure
Kind: D -/
def extSum (T' : Tree (BetW Ω) (ι ⊕ Unit) (betActs acts) K) : K :=
  ∑ ℓ', leafLaw (liftProc C σ₀ bet) T' ℓ' * g (world T' ℓ') (payoff T' ℓ')

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem ext_leaf (b isA : Bool) (σ : Side) (ω : Ω) (r : K) (o : Option (Tree.leaf ω r : Tree Ω ι acts K).DecNode) :
    ext pay π b isA σ (.leaf ω r) o = .leaf (ω, b, σ) (pay b isA σ r) := by
  cases o with
  | none => rfl
  | some q => exact q.elim

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem ext_chance_none (b isA : Bool) (σ : Side) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    ext pay π b isA σ (.chance n β child) none =
      .chance n β fun j => ext pay π b isA σ (child j) none := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem ext_chance_some (b isA : Bool) (σ : Side) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (q : (child i).DecNode) :
    ext pay π b isA σ (.chance n β child) (some ⟨i, q⟩) =
      .chance n β fun j => ext pay π b isA σ (child j) (if h : j = i then some (h ▸ q) else none) :=
  rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem ext_decision_none (b isA : Bool) (σ : Side) (e : ι) (child : acts e → Tree Ω ι acts K) :
    ext pay π b isA σ (.decision e child) none =
      .decision (.inl e) fun xτ => ext pay π b isA σ (child xτ.1) none := rfl

/-- Equation lemma (the real node). Source: none: infrastructure. Kind: L -/
theorem ext_decision_real (b isA : Bool) (σ : Side) (e : ι) (child : acts e → Tree Ω ι acts K) :
    ext pay π b isA σ (.decision e child) (some none) =
      .decision (.inr ()) fun bt =>
        .decision (.inl e) fun xτ =>
          ext pay π bt (decide (xτ.1 = π e)) xτ.2 (child xτ.1) none := rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
theorem ext_decision_some (b isA : Bool) (σ : Side) (e : ι) (child : acts e → Tree Ω ι acts K)
    (y : acts e) (q : (child y).DecNode) :
    ext pay π b isA σ (.decision e child) (some (some ⟨y, q⟩)) =
      .decision (.inl e) fun xτ =>
        ext pay π b isA σ (child xτ.1) (if h : xτ.1 = y then some (h ▸ q) else none) := rfl

/-- **The master identity** (the leaf bijection of P12-1, as a sum identity): a leaf-sum over the
extended tree under `liftProc C σ₀ bet` is the base leaf-sum weighted by `extG`.
Source: P12-1 ("a leaf bijection with `leafLaw` equal and `payoff` differing by `−δ`"); mandate
T1(e)
Kind: P
Fidelity: exact -/
theorem ext_sum : (T : Tree Ω ι acts K) → ∀ (o : Option T.DecNode) (b isA : Bool) (σ : Side),
    extSum g C bet σ₀ (ext pay π b isA σ T o) =
      ∑ ℓ, leafLaw C T ℓ * extG pay π g bet σ₀ b isA σ T o ℓ
  | .leaf ω r, o, b, isA, σ => by
      rw [ext_leaf]
      unfold extSum
      rw [sum_leaves_leaf', sum_leaves_leaf']
      cases o with
      | none => simp [extG]
      | some q => exact q.elim
  | .chance n β child, none, b, isA, σ => by
      rw [ext_chance_none]
      unfold extSum
      rw [sum_leaves_chance, sum_leaves_chance]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [leafLaw_chance, world_chance, payoff_chance, mul_assoc, ← Finset.mul_sum]
      have ih := ext_sum (child j) none b isA σ
      unfold extSum at ih
      simp only [extG_chance_none]
      rw [ih]
  | .chance n β child, some ⟨i, q⟩, b, isA, σ => by
      rw [ext_chance_some]
      unfold extSum
      rw [sum_leaves_chance, sum_leaves_chance]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [leafLaw_chance, world_chance, payoff_chance, mul_assoc, ← Finset.mul_sum]
      have ih := ext_sum (child j) (if h : j = i then some (h ▸ q) else none) b isA σ
      unfold extSum at ih
      rw [ih]
      congr 1
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      congr 1
      by_cases hj : j = i
      · subst hj
        simp only [extG_some, edgeOf_chance, dite_eq_ite, if_true, pt_chance]
        generalize (child j).edgeOf q ℓ = o'
        cases o' <;> rfl
      · simp [extG_some, edgeOf_chance, hj]
  | .decision e child, none, b, isA, σ => by
      rw [ext_decision_none]
      unfold extSum
      rw [sum_leaves_decision, sum_leaves_decision, sum_betActs_inl]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [leafLaw_decision, liftProc_inl_w, world_decision, payoff_decision, mul_assoc,
        ← Finset.mul_sum]
      rw [sum_side_prodPure σ₀]
      have ih := ext_sum (child x) none b isA σ
      unfold extSum at ih
      simp only [extG_decision_none]
      rw [ih]
  | .decision e child, some none, b, isA, σ => by
      rw [ext_decision_real]
      unfold extSum
      conv_rhs => rw [sum_leaves_decision]
      rw [sum_leaves_decision, sum_betActs_inr]
      simp only [leafLaw_decision, liftProc_inr_w, world_decision, payoff_decision]
      -- inner: the real node's action sum, per bet choice
      have inner : ∀ bt : Bool,
          (∑ ℓ' : (Tree.decision (.inl e) fun xτ : betActs acts (.inl e) =>
              ext pay π bt (decide (xτ.1 = π e)) xτ.2 (child xτ.1) none).Leaves,
            bet.w bt * leafLaw (liftProc C σ₀ bet) _ ℓ' * g (world _ ℓ') (payoff _ ℓ')) =
          bet.w bt * ∑ x, (C e).w x * ∑ ℓ, leafLaw C (child x) ℓ *
            g (world (child x) ℓ, bt, σ₀) (pay bt (decide (x = π e)) σ₀ (payoff (child x) ℓ)) := by
        intro bt
        rw [sum_leaves_decision, sum_betActs_inl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [leafLaw_decision, liftProc_inl_w, world_decision, payoff_decision, mul_assoc,
          ← Finset.mul_sum]
        rw [sum_side_prodPure σ₀]
        have ih := ext_sum (child x) none bt (decide (x = π e)) σ₀
        unfold extSum at ih
        rw [ih]
        simp only [extG_none]
      simp only [inner]
      -- the right-hand side: the bet sum sits innermost; move it outside
      simp only [extG_some, edgeOf_decision_none, pt_decision_none, world_decision,
        payoff_decision, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun bt _ => ?_
      -- the two sides differ in association and in a `Decidable` instance written through
      -- `pt (decision e child) none` (invisible to `ring`); restate with the standard instance
      simp only [mul_assoc]
      show bet.w bt * ((C e).w x * (leafLaw C (child x) ℓ *
          g ((child x).world ℓ, bt, σ₀) (pay bt (decide (x = π e)) σ₀ ((child x).payoff ℓ)))) =
        (C e).w x * (leafLaw C (child x) ℓ * (bet.w bt *
          g ((child x).world ℓ, bt, σ₀) (pay bt (decide (x = π e)) σ₀ ((child x).payoff ℓ))))
      ring
  | .decision e child, some (some ⟨y, q⟩), b, isA, σ => by
      rw [ext_decision_some]
      unfold extSum
      rw [sum_leaves_decision, sum_leaves_decision, sum_betActs_inl]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [leafLaw_decision, liftProc_inl_w, world_decision, payoff_decision, mul_assoc,
        ← Finset.mul_sum]
      rw [sum_side_prodPure σ₀]
      have ih := ext_sum (child x) (if h : x = y then some (h ▸ q) else none) b isA σ
      unfold extSum at ih
      rw [ih]
      congr 1
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      congr 1
      by_cases hx : x = y
      · subst hx
        simp only [extG_some, edgeOf_decision_some, dite_eq_ite, if_true, pt_decision_some]
        generalize (child x).edgeOf q ℓ = o'
        cases o' <;> rfl
      · simp [extG_some, edgeOf_decision_some, hx]

end master

/-! ## Consequences: values, masses and the leaf-wise book identity -/

section consequences

variable (δ ca s : K) (π : (e : ι) → acts e) (C : Proc ι acts K) (B : Tree Ω ι acts K)
  (q₀ : B.DecNode) (σ₀ : Side) (bet : FinDistr K Bool)

/-- `betPay` with the bet declined is the base payoff. Source: none: infrastructure. Kind: L -/
@[simp] theorem betPay_false (isA : Bool) (σ : Side) (r : K) : betPay δ ca s false isA σ r = r := by
  simp [betPay]

/-- `betPayR` declined and kept is the base payoff. Source: none: infrastructure. Kind: L -/
@[simp] theorem betPayR_false_keep (isA : Bool) (r : K) : betPayR δ ca s false isA .keep r = r := by
  simp [betPayR]

/-- The value of the extended tree, for any payoff function `pay` with `pay false _ keep r = r`.
Source: mandate T1(e)
Kind: L -/
theorem value_ext (pay : Bool → Bool → Side → K → K) (hpay : ∀ isA r, pay false isA .keep r = r) :
    value (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) =
      ∑ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * pay bt (decide (x = π (pt B q₀))) σ₀ (payoff B ℓ)
        | none => payoff B ℓ) := by
  have h := ext_sum pay π (fun _ r => r) C bet σ₀ B (some q₀) false false .keep
  unfold extSum at h
  unfold value
  rw [h]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [extG_some]
  cases edgeOf B q₀ ℓ with
  | none => simp [hpay]
  | some x => rfl

/-- `ν` on the extended tree. Source: mandate T2. Kind: L -/
theorem nu_ext [DecidableEq Ω] (pay : Bool → Bool → Side → K → K) (X : Finset (BetW Ω)) :
    nu (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) X =
      ∑ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some _ => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, σ₀) ∈ X then 1 else 0)
        | none => if (world B ℓ, false, .keep) ∈ X then 1 else 0) := by
  have h := ext_sum pay π (fun w _ => if w ∈ X then 1 else 0) C bet σ₀ B (some q₀) false false .keep
  unfold extSum at h
  rw [nu_eq_sum]
  have e : ∀ ℓ', (if world _ ℓ' ∈ X then leafLaw (liftProc C σ₀ bet)
      (ext pay π false false Side.keep B (some q₀)) ℓ' else 0) =
      leafLaw (liftProc C σ₀ bet) (ext pay π false false Side.keep B (some q₀)) ℓ' *
        (if world _ ℓ' ∈ X then 1 else 0) := fun ℓ' => by split_ifs <;> simp
  simp only [e]
  rw [h]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [extG_some]

/-- `paySum` on the extended tree. Source: mandate T2. Kind: L -/
theorem paySum_ext [DecidableEq Ω] [Fintype Ω] (pay : Bool → Bool → Side → K → K)
    (hpay : ∀ isA r, pay false isA .keep r = r) (X : Finset (BetW Ω)) :
    paySum (liftProc C σ₀ bet) (ext pay π false false .keep B (some q₀)) X =
      ∑ ℓ, leafLaw C B ℓ * (match edgeOf B q₀ ℓ with
        | some x => ∑ bt : Bool, bet.w bt * (if (world B ℓ, bt, σ₀) ∈ X
            then pay bt (decide (x = π (pt B q₀))) σ₀ (payoff B ℓ) else 0)
        | none => if (world B ℓ, false, .keep) ∈ X then payoff B ℓ else 0) := by
  have h := ext_sum pay π (fun w r => if w ∈ X then r else 0) C bet σ₀ B (some q₀) false false .keep
  unfold extSum at h
  rw [paySum_eq_sum_ite]
  have e : ∀ ℓ', (if world _ ℓ' ∈ X then leafLaw (liftProc C σ₀ bet)
      (ext pay π false false Side.keep B (some q₀)) ℓ' * payoff _ ℓ' else 0) =
      leafLaw (liftProc C σ₀ bet) (ext pay π false false Side.keep B (some q₀)) ℓ' *
        (if world _ ℓ' ∈ X then payoff _ ℓ' else 0) := fun ℓ' => by split_ifs <;> simp
  simp only [e]
  rw [h]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [extG_some]
  cases edgeOf B q₀ ℓ with
  | none => simp [hpay]
  | some x => rfl

/-- **T1(e), the book identity on `attachBet`**: buying at `d_B` and selling at `d'`
(`liftProc C sell δ_buy`) is worth `V_B(C) − δ · R_{q₀}(C)`: exactly `δ` less on every run through
the bet point than declining and keeping (`value_attachBet_dec`). P12-1's `−δ` is the case
`R_{q₀} = 1`.
Source: P12-1 ("`V_{B'}(C^book) = V_{B'}(C^dec) − δ` for every base tree …"); C2-14; mandate T1(e)
Kind: L (the plan pre-labels the identity `L`)
Fidelity: stronger: the reach factor `R_{q₀}(C)` made explicit (P12-1 assumes every run reaches
the bet point) -/
theorem value_attachBet_book :
    value (liftProc C .sell (FinDistr.pure true)) (attachBet δ ca s π B q₀) =
      value C B - δ * reach C B q₀ := by
  unfold attachBet
  rw [value_ext π C B q₀ .sell _ _ (fun isA r => betPay_false δ ca s isA .keep r)]
  rw [reach_eq_mass_leavesBelow, mass, leavesBelow, Finset.sum_filter, value, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases edgeOf B q₀ ℓ with
  | none => simp
  | some x =>
      simp only [Option.isSome_some, if_true, Fintype.sum_bool, FinDistr.pure, betPay]
      simp; ring

/-- Declining and keeping is worth the base value. Source: P12-1. Kind: L -/
theorem value_attachBet_dec :
    value (liftProc C .keep (FinDistr.pure false)) (attachBet δ ca s π B q₀) = value C B := by
  unfold attachBet
  rw [value_ext π C B q₀ .keep _ _ (fun isA r => betPay_false δ ca s isA .keep r), value]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases edgeOf B q₀ ℓ with
  | none => rfl
  | some x =>
      simp only [Fintype.sum_bool, FinDistr.pure, betPay]
      simp

/-- **T1(e) on `attachBetRegardless`**: the same identity with the reverse bet offered regardless.
Source: P09-1; P12-3; mandate T1(b)(e)
Kind: L
Fidelity: stronger: the reach factor explicit -/
theorem value_attachBetRegardless_book :
    value (liftProc C .sell (FinDistr.pure true)) (attachBetRegardless δ ca s π B q₀) =
      value C B - δ * reach C B q₀ := by
  unfold attachBetRegardless
  rw [value_ext π C B q₀ .sell _ _ (fun isA r => betPayR_false_keep δ ca s isA r)]
  rw [reach_eq_mass_leavesBelow, mass, leavesBelow, Finset.sum_filter, value, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases edgeOf B q₀ ℓ with
  | none => simp
  | some x =>
      simp only [Option.isSome_some, if_true, Fintype.sum_bool, FinDistr.pure, betPayR]
      cases decide (x = π (pt B q₀)) <;> simp <;> ring

/-- Declining and keeping on `attachBetRegardless` is worth the base value.
Source: P09-1. Kind: L -/
theorem value_attachBetRegardless_dec :
    value (liftProc C .keep (FinDistr.pure false)) (attachBetRegardless δ ca s π B q₀) =
      value C B := by
  unfold attachBetRegardless
  rw [value_ext π C B q₀ .keep _ _ (fun isA r => betPayR_false_keep δ ca s isA r), value]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  cases edgeOf B q₀ ℓ with
  | none => rfl
  | some x =>
      simp only [Fintype.sum_bool, FinDistr.pure, betPayR]
      simp

end consequences

end Cleanroom.Decision.DpDutchBook
