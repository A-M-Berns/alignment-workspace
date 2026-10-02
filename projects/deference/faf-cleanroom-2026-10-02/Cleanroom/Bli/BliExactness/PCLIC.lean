import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Bounds.Basic

/-!
# `bli-exactness` — X5: Soto's PC-LIC has no inhabitant; the repaired accounting `A′`

**FAF-free and finite** (Mathlib only). Soto's "Definitions" (PDF 05, 2023-08-03) Defs 1–5
formalized verbatim over a day-indexed family of finite world sets `W n` with restriction maps
`π n : W (n+1) → W n` (each day-`(n+1)` world extends a day-`n` one; Soto: "worlds only get more
fine-grained with time"). A "sentence" is a predicate `W n → Bool`, priced by its world bundle
(Def 1: "a share of `φ` is actually just the bundle with a share of each `Wₙ` with `Wₙ ⊨ φ`").
An `n`-strategy is a rational combination of sentences; over a finite `W n` every predicate type is
finite, so no finite-support clause is needed. **Disclosed variant**: strategies are fixed
rational vectors, not price-dependent expressible features as in the LI paper's (and Soto's "as
always") trading strategies — see `Strategy`'s docstring; the refutation and the identities at a
fixed `T_n` are unaffected, the criteria `PCLIC`/`PCLIC'` are narrower than Soto's.

* **Def 2 verbatim** (`A`): `A(T_{≤n}, P_{≤n}, n) = ∑_{i ≤ n} ( P_i(T_i[c]) + ∑_φ T_{i−1}[φ]·P_i(φ) )`,
  with the cash `T_i[c] = −∑_φ T_i[φ]·P_i(φ)` and `T_{−1} := 0` (the recursion's base case).
* **The refutation** (`A_topShorter`, `topShorter_pcExploits`, `pclic_empty`): the trader that
  sells `n+1` tautology shares on Lean day `n` (round `n+1`) has `A = n + 1` against **every**
  PC-market — only `price P ⊤ = 1` is used — so it PC-exploits every market (Def 4) and Def 5 as
  printed has no inhabitant, for every class `EC` of "efficiently computable" traders containing
  it. Diagnosis (bli-soto-a-2-001): Def 2 credits the round-`n` cash but values the round-`n`
  position only inside `A(n+1)`; the current position is never marked to market.
* **The repair** `A′ T P n := A T P n + ∑_φ T_n[φ]·P_n(φ)` (mark the open round-`n` position to
  the current prices): `A′ ≡ 0` for the `⊤`-shorter, `A′` telescopes to
  `∑_{j<n} ⟨T_j, P_{j+1}∘π − P_j⟩` (the "no predictable price movement" reading), and the round
  increment is linear in the next price vector, so "no profit whatever `P_{n+1}` is" is Soto's
  `B(W) ≤ 0` at every vertex (`noProfit_iff_benefit_nonpos`, PDF 05 Thm 2's `B(W)`).

"Efficiently computable" for world traders has no FAF object (bli-soto-a-040's flag): `PCLIC` is
parametric in a class predicate `EC`, and the refutation quantifies over every `EC` containing the
`⊤`-shorter — the one disclosed `(c)` clause of X5. Conjectures 1–2 and Theorem 1 of PDF 05 over
the literal `A` are vacuous (every market is exploited) and are **not** formalized (findings).
-/

namespace Cleanroom.Bli.BliExactness.WorldMarket

open Finset

/-! ## Def 1: PC-valuations, bundle prices, strategies -/

/-- **A PC-valuation on a finite world set** (Def 1): a probability vector on `W`.
Source: Soto PDF 05 Def 1 ([[bli-soto-a-inventory]] 037); mandate § Definitions (PC-LIC objects)
Kind: D
Fidelity: exact -/
structure PCValuation (W : Type) [Fintype W] where
  /-- The probability of each world. -/
  P : W → ℚ
  /-- Nonnegativity. -/
  nonneg : ∀ w, 0 ≤ P w
  /-- Total mass one. -/
  sum_one : ∑ w, P w = 1

/-- **A PC-market**: one PC-valuation per day.
Source: Soto PDF 05 Def 1 ("`P̄`")
Kind: D
Fidelity: exact -/
def PCMarket (W : ℕ → Type) [∀ n, Fintype (W n)] : Type := ∀ n, PCValuation (W n)

/-- **The bundle price of a sentence** (Def 1: `Pₙ(φ) := ∑_{Wₙ ⊨ φ} Pₙ(Wₙ)`).
Source: Soto PDF 05 Def 1
Kind: D
Fidelity: exact -/
def price {W : Type} [Fintype W] (P : PCValuation W) (φ : W → Bool) : ℚ :=
  ∑ w, if φ w then P.P w else 0

/-- An `n`-strategy: a rational combination of sentences on the day-`n` worlds (finite type, so
every combination is finitely supported). **Variant** (audit r1 N2): Soto's "defined as always"
is the LI paper's trading strategy, whose coefficients are expressible features of the day's
prices (`T_n(P)[W]` in Thm 2); here a strategy is a **fixed rational vector**, independent of the
prices (the mandate's specification). Harmless for the refutation (`topShorter` is constant, and a
constant trader is in every class) and for the identities at a fixed `T_n`, but a narrowing of
`A`, `PCExploits`, `PCLIC`, `PCLIC'` and of the OPEN X5 (v): "no price-independent trader
exploits" is weaker than Soto's criterion.
Source: Soto PDF 05 Def 1 ("an `n`-trading strategy is defined as always")
Kind: D
Fidelity: variant: fixed rational vectors in place of price-dependent (expressible-feature)
strategies; finite support automatic -/
abbrev Strategy (W : Type) : Type := (W → Bool) → ℚ

/-- The tautology `⊤` on a world set (true in every world).
Source: bli-soto-a-2-001 ("a tautology `φ ∨ ¬φ`")
Kind: D
Fidelity: exact -/
def top (W : Type) : W → Bool := fun _ => true

/-- Only fact about `⊤` the refutation uses: its bundle price is `1` under every PC-valuation.
Source: bli-soto-a-2-001 ("a share of `⊤` is the bundle of all worlds, whose prices sum to `1`")
Kind: L
Fidelity: exact -/
@[simp] lemma price_top {W : Type} [Fintype W] (P : PCValuation W) : price P (top W) = 1 := by
  unfold price top
  simp [P.sum_one]

/-- **The cash term** `Tₙ[c] = −∑_φ Tₙ[φ]·Pₙ(φ)` (Def 2: "`Pᵢ(Tᵢ[c])` is calculated by just
introducing the `Pᵢ` prices into the expression for `Tᵢ[c]`").
Source: Soto PDF 05 Def 2
Kind: D
Fidelity: exact -/
def cash {W : Type} [Fintype W] [DecidableEq W] (Tn : Strategy W) (P : PCValuation W) : ℚ :=
  -∑ φ, Tn φ * price P φ

/-- The portfolio's value `∑_φ Tₙ[φ]·Pₙ(φ)` at a valuation (so `cash = −value`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def value {W : Type} [Fintype W] [DecidableEq W] (Tn : Strategy W) (P : PCValuation W) : ℚ :=
  ∑ φ, Tn φ * price P φ

/-- `cash = −value`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cash_eq_neg_value {W : Type} [Fintype W] [DecidableEq W] (Tn : Strategy W)
    (P : PCValuation W) : cash Tn P = -value Tn P := rfl

section Market

variable {W : ℕ → Type} [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)] (π : ∀ n, W (n + 1) → W n)

/-- **The carry**: the previous round's holdings valued at the current prices,
`∑_φ T_{i−1}[φ]·Pᵢ(φ)`, a day-`(n)` sentence read on day `n+1` through the restriction `π n`.
Source: Soto PDF 05 Def 2 (second summand)
Kind: D
Fidelity: exact (the restriction map makes "`Pᵢ(φ)` for a round-`(i−1)` sentence" typecheck) -/
def carry (n : ℕ) (Tprev : Strategy (W n)) (P : PCValuation (W (n + 1))) : ℚ :=
  ∑ φ, Tprev φ * price P (φ ∘ π n)

/-- **Soto's accumulated wealth, Def 2 verbatim**: `A(T_{≤n}, P_{≤n}, n) = ∑_{i≤n} (Pᵢ(Tᵢ[c]) +
∑_φ T_{i−1}[φ]·Pᵢ(φ))` with `T_{−1} := 0`, as a recursion on the Lean day (`n` = round `n+1`).
Source: Soto PDF 05 Def 2 ([[bli-soto-a-inventory]] 038, 040; [[bli-soto-a-2-inventory]] 001)
Kind: D
Fidelity: exact -/
def A (T : ∀ n, Strategy (W n)) (P : PCMarket W) : ℕ → ℚ
  | 0 => cash (T 0) (P 0)
  | n + 1 => A T P n + cash (T (n + 1)) (P (n + 1)) + carry π n (T n) (P (n + 1))

/-- **PC-exploitation** (Def 4): the accumulated wealth is bounded below but not above.
Source: Soto PDF 05 Def 4 ([[bli-soto-a-inventory]] 040)
Kind: D
Fidelity: exact -/
def PCExploits (T : ∀ n, Strategy (W n)) (P : PCMarket W) : Prop :=
  BddBelow (Set.range (A π T P)) ∧ ¬ BddAbove (Set.range (A π T P))

/-- **Respecting a deductive process** (Def 3): every sentence of `Dₙ` is priced `1` on day `n`.
Source: Soto PDF 05 Def 3 ([[bli-soto-a-inventory]] 039)
Kind: D
Fidelity: exact -/
def Respects (D : ∀ n, Set (W n → Bool)) (P : PCMarket W) : Prop :=
  ∀ n φ, φ ∈ D n → price (P n) φ = 1

/-- **PC-LIC as printed** (Def 5): `P̄` respects `D̄` and no trader of the class `EC` PC-exploits
it. `EC` is a parameter: "efficiently computable" for world traders has no FAF object
(bli-soto-a-040's flag) — the one disclosed `(c)` of X5.
Source: Soto PDF 05 Def 5 ([[bli-soto-a-inventory]] 040)
Kind: D
Fidelity: variant: parametric in the trader class `EC` (c) -/
def PCLIC (EC : (∀ n, Strategy (W n)) → Prop) (D : ∀ n, Set (W n → Bool)) (P : PCMarket W) :
    Prop :=
  Respects D P ∧ ∀ T, EC T → ¬ PCExploits π T P

/-! ## The `⊤`-shorter and the refutation -/

variable (W) in
/-- **The `⊤`-shorter**: on Lean day `n` (round `n+1`) sell `n+1` shares of the tautology, nothing
else. Trivially a fixed finite computation per day.
Source: [[bli-soto-a-2-inventory]] 001 ("`Tₙ := −n·⊤`", round-indexed)
Kind: D
Fidelity: exact (round `n+1` on Lean day `n`) -/
def topShorter (n : ℕ) : Strategy (W n) :=
  fun φ => if φ = top (W n) then -((n : ℚ) + 1) else 0

/-- The `⊤`-shorter's cash on day `n` is `n + 1` against every valuation.
Source: bli-soto-a-2-001 ("cash term `Tₙ[c] = n·Pₙ(⊤) = n`")
Kind: L
Fidelity: exact -/
lemma cash_topShorter (n : ℕ) (P : PCValuation (W n)) :
    cash (topShorter W n) P = (n : ℚ) + 1 := by
  unfold cash topShorter
  simp [Finset.sum_ite_eq', price_top]

/-- The `⊤`-shorter's carry into day `n+1` is `−(n + 1)` against every valuation (the pulled-back
tautology is the tautology).
Source: bli-soto-a-2-001
Kind: L
Fidelity: exact -/
lemma carry_topShorter (n : ℕ) (P : PCValuation (W (n + 1))) :
    carry π n (topShorter W n) P = -((n : ℚ) + 1) := by
  unfold carry topShorter
  have htop : top (W n) ∘ π n = top (W (n + 1)) := rfl
  simp [Finset.sum_ite_eq', htop, price_top]

/-- **`A` of the `⊤`-shorter is `n + 1` against every PC-market** (only `price P ⊤ = 1` is used):
the day-`n` cash `n+1` is credited, the round-`n` position is valued only on day `n+1` at
`−(n+1)`, and it is never marked to market on day `n`.
Source: [[bli-soto-a-2-inventory]] 001 (refutation computation); mandate X5 (i)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem A_topShorter (P : PCMarket W) (n : ℕ) : A π (topShorter W) P n = (n : ℚ) + 1 := by
  induction n with
  | zero => simp [A, cash_topShorter]
  | succ n ih =>
    rw [A, ih, cash_topShorter, carry_topShorter]
    push_cast
    ring

/-- **The `⊤`-shorter PC-exploits every PC-market** (Def 4): `A = n + 1` is bounded below by `1`
and unbounded above.
Source: [[bli-soto-a-2-inventory]] 001; mandate X5 (i)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem topShorter_pcExploits (P : PCMarket W) : PCExploits π (topShorter W) P := by
  constructor
  · refine ⟨1, ?_⟩
    rintro x ⟨n, rfl⟩
    rw [A_topShorter]
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := exists_nat_gt b
    have := hb ⟨n, rfl⟩
    rw [A_topShorter] at this
    linarith

/-- **Def 5 as printed is empty**: for every class `EC` containing the `⊤`-shorter, every deductive
process `D` and every PC-market `P`, `¬ PCLIC EC D P`. Soto's Conjectures 1–2 and Theorem 1 over
this `A` are therefore vacuous or false as stated (findings, severity: blocking PDF 05's
conclusion).
Source: [[bli-soto-a-2-inventory]] 001; mandate X5 (i) (refutation row)
Kind: P
Fidelity: exact
Hyps: (c) `hEC`: the class contains the `⊤`-shorter (no FAF object for e.c. world traders) -/
theorem pclic_empty (EC : (∀ n, Strategy (W n)) → Prop) (hEC : EC (topShorter W))
    (D : ∀ n, Set (W n → Bool)) (P : PCMarket W) : ¬ PCLIC π EC D P :=
  fun h => h.2 _ hEC (topShorter_pcExploits π P)

/-! ## The repair `A′`: mark the current position to market -/

/-- **The repaired accumulated wealth** `A′(n) := A(n) + ∑_φ Tₙ[φ]·Pₙ(φ)` — the round-`n` position
marked to the current prices. Soto's prose ("every round the trader sells all their shares,
receiving their new prices as payment … each trader is trying to predict the next market state")
describes a trader that is always flat, which is this accounting (ATTRIBUTION-UNVETTED that `A′`
rather than `A` is the intended definition).
Source: [[bli-soto-a-2-inventory]] 001 (repair); mandate X5 (ii)
Kind: D
Fidelity: variant: repaired accounting -/
def A' (T : ∀ n, Strategy (W n)) (P : PCMarket W) (n : ℕ) : ℚ :=
  A π T P n + value (T n) (P n)

/-- `A′` of the `⊤`-shorter is identically `0`: the repaired accounting sees a flat trader.
Source: [[bli-soto-a-2-inventory]] 001; mandate X5 (ii)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem A'_topShorter (P : PCMarket W) (n : ℕ) : A' π (topShorter W) P n = 0 := by
  unfold A'
  rw [A_topShorter]
  unfold value topShorter
  simp [Finset.sum_ite_eq', price_top]

/-- `A′` starts at `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma A'_zero (T : ∀ n, Strategy (W n)) (P : PCMarket W) : A' π T P 0 = 0 := by
  unfold A' A
  rw [cash_eq_neg_value]
  ring

/-- **The round increment** of the repaired wealth from day `n` to `n+1`:
`⟨Tₙ, P_{n+1}∘π − Pₙ⟩ = ∑_φ Tₙ[φ]·(P_{n+1}(φ∘π) − Pₙ(φ))`, the gain of the day-`n` position when
the market moves.
Source: [[bli-soto-a-2-inventory]] 002 (i)
Kind: D
Fidelity: exact -/
def increment (n : ℕ) (Tn : Strategy (W n)) (Pn : PCValuation (W n))
    (Pn1 : PCValuation (W (n + 1))) : ℚ :=
  ∑ φ, Tn φ * (price Pn1 (φ ∘ π n) - price Pn φ)

/-- `A′(n+1) = A′(n) + ⟨Tₙ, P_{n+1}∘π − Pₙ⟩`.
Source: [[bli-soto-a-2-inventory]] 001 ("`A′(n) = ∑_{j<n} ⟨T_j, P_{j+1} − P_j⟩`")
Kind: L
Fidelity: exact -/
lemma A'_succ (T : ∀ n, Strategy (W n)) (P : PCMarket W) (n : ℕ) :
    A' π T P (n + 1) = A' π T P n + increment π n (T n) (P n) (P (n + 1)) := by
  unfold A' increment
  rw [A, cash_eq_neg_value]
  unfold value carry
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **`A′` telescopes**: `A′(n) = ∑_{j<n} ⟨T_j, P_{j+1}∘π − P_j⟩` — the repaired criterion is
"no e.c. trader profits unboundedly from predictable price movements" (bli-soto-a-2-002 (i)).
Source: [[bli-soto-a-2-inventory]] 001, 002 (i); mandate X5 (iii)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem A'_telescopes (T : ∀ n, Strategy (W n)) (P : PCMarket W) (n : ℕ) :
    A' π T P n = ∑ j ∈ range n, increment π j (T j) (P j) (P (j + 1)) := by
  induction n with
  | zero => simp [A'_zero]
  | succ n ih => rw [A'_succ, ih, Finset.sum_range_succ]

/-- **Repaired PC-exploitation** (Def 4 with `A′`).
Source: [[bli-soto-a-2-inventory]] 001 (repair)
Kind: D
Fidelity: variant: repaired accounting -/
def PCExploits' (T : ∀ n, Strategy (W n)) (P : PCMarket W) : Prop :=
  BddBelow (Set.range (A' π T P)) ∧ ¬ BddAbove (Set.range (A' π T P))

/-- **Repaired PC-LIC**: `P̄` respects `D̄` and no trader of the class `EC` PC-exploits it in the
repaired accounting. The `⊤`-shorter no longer witnesses anything (`A′ ≡ 0`).
Source: [[bli-soto-a-2-inventory]] 001 (the definition of record proposed there)
Kind: D
Fidelity: variant: repaired accounting; parametric in `EC` (c) -/
def PCLIC' (EC : (∀ n, Strategy (W n)) → Prop) (D : ∀ n, Set (W n → Bool)) (P : PCMarket W) :
    Prop :=
  Respects D P ∧ ∀ T, EC T → ¬ PCExploits' π T P

/-- The `⊤`-shorter does not PC-exploit any market in the repaired accounting (`A′ ≡ 0` is
bounded above): the refutation of Def 5 does not transfer to `PCLIC'`.
Source: [[bli-soto-a-2-inventory]] 001
Kind: L
Fidelity: exact -/
theorem topShorter_not_pcExploits' (P : PCMarket W) : ¬ PCExploits' π (topShorter W) P := by
  rintro ⟨-, hnb⟩
  refine hnb ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  rw [A'_topShorter]

/-! ## X5 (iv): the increment is linear in the next price vector; Soto's `B(W)` -/

/-- **Soto's benefit `B(W)`** of the day-`n` position in the next-day world `w`: the position's
payout if `w` is the realized world, net of its cost at today's prices
(`B(W) = Tₙ[W]·1 − ∑_{W'} Tₙ[W']·P(W')`, PDF 05 Thm 2, read through the bundle).
Source: Soto PDF 05 Theorem 2 (`B(W)`); [[bli-soto-a-2-inventory]] 002 (i)
Kind: D
Fidelity: exact (through the bundle pricing) -/
def benefit (n : ℕ) (Tn : Strategy (W n)) (Pn : PCValuation (W n)) (w : W (n + 1)) : ℚ :=
  ∑ φ, Tn φ * ((if φ (π n w) then 1 else 0) - price Pn φ)

/-- **The round increment is the `P_{n+1}`-expectation of the benefit**: linear in the next price
vector.
Source: [[bli-soto-a-2-inventory]] 002 (i)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem increment_eq_sum_benefit (n : ℕ) (Tn : Strategy (W n)) (Pn : PCValuation (W n))
    (Pn1 : PCValuation (W (n + 1))) :
    increment π n Tn Pn Pn1 = ∑ w, Pn1.P w * benefit π n Tn Pn w := by
  have key : ∀ φ : W n → Bool, Tn φ * (price Pn1 (φ ∘ π n) - price Pn φ) =
      ∑ w, Pn1.P w * (Tn φ * ((if φ (π n w) then 1 else 0) - price Pn φ)) := by
    intro φ
    have hp : price Pn1 (φ ∘ π n) = ∑ w, Pn1.P w * (if φ (π n w) then 1 else 0) := by
      unfold price
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Function.comp]
      split_ifs <;> ring
    have h1 : ∑ w, Pn1.P w * (Tn φ * ((if φ (π n w) then 1 else 0) - price Pn φ)) =
        Tn φ * ∑ w, Pn1.P w * (if φ (π n w) then 1 else 0) -
          Tn φ * price Pn φ * ∑ w, Pn1.P w := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    rw [h1, Pn1.sum_one, hp]; ring
  unfold increment benefit
  rw [Finset.sum_congr rfl fun φ _ => key φ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]

/-- The Dirac valuation at a world.
Source: Soto PDF 05 Theorem 2 ("for any `P_{n+1}`" — the vertices of the simplex)
Kind: D
Fidelity: exact -/
def dirac {V : Type} [Fintype V] [DecidableEq V] (w : V) : PCValuation V where
  P := fun v => if v = w then 1 else 0
  nonneg := fun v => by split_ifs <;> norm_num
  sum_one := by simp

/-- The increment at a vertex is the benefit there.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma increment_dirac (n : ℕ) (Tn : Strategy (W n)) (Pn : PCValuation (W n)) (w : W (n + 1)) :
    increment π n Tn Pn (dirac w) = benefit π n Tn Pn w := by
  rw [increment_eq_sum_benefit]
  simp [dirac]

/-- **"No profit whatever `P_{n+1}` is" is `B(W) ≤ 0` at every vertex** (Soto PDF 05 Thm 2:
"We want all of the `B(W)` to be `≤ 0`. Indeed, this is necessary and sufficient to ensure that
no market state in the next round would yield a benefit to the trader in accumulated wealth"),
in the repaired accounting.
Source: Soto PDF 05 Theorem 2; [[bli-soto-a-2-inventory]] 002 (i); mandate X5 (iv)
Kind: P
Fidelity: exact (repaired accounting: the literal `A` has no such reading, `A_topShorter`)
Hyps: (a) -/
theorem noProfit_iff_benefit_nonpos (n : ℕ) (Tn : Strategy (W n)) (Pn : PCValuation (W n)) :
    (∀ Pn1 : PCValuation (W (n + 1)), increment π n Tn Pn Pn1 ≤ 0) ↔
      ∀ w, benefit π n Tn Pn w ≤ 0 := by
  constructor
  · intro h w
    rw [← increment_dirac]
    exact h _
  · intro h Pn1
    rw [increment_eq_sum_benefit]
    exact Finset.sum_nonpos fun w _ => mul_nonpos_of_nonneg_of_nonpos (Pn1.nonneg w) (h w)

/-! ## Non-vacuity of the repaired accounting -/

/-- **N−**: against a market whose prices never move (every day-`n` sentence keeps its price on
day `n+1`), every trader's `A′` is identically `0`. Degenerate, as the mandate says; an N+
(a moving market and a trader with nonzero bounded `A′`) is `exists_A'_ne_zero`.
Source: mandate X5 ("a constant market has every increment `0` (N−)")
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem A'_eq_zero_of_constant (T : ∀ n, Strategy (W n)) (P : PCMarket W)
    (hconst : ∀ n (φ : W n → Bool), price (P (n + 1)) (φ ∘ π n) = price (P n) φ) (n : ℕ) :
    A' π T P n = 0 := by
  rw [A'_telescopes]
  refine Finset.sum_eq_zero fun j _ => ?_
  unfold increment
  simp [hconst]

end Market

/-! ### N+ for `A′`: a moving two-world market and a one-shot trader -/

/-- The constant two-world family `Bool` with the identity restriction.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev boolWorlds : ℕ → Type := fun _ => Bool

/-- A two-world valuation with mass `a` on `true`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def boolVal (a : ℚ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : PCValuation Bool where
  P := fun b => if b then a else 1 - a
  nonneg := fun b => by cases b <;> simp <;> linarith
  sum_one := by simp

/-- A market moving from `½` on day `0` to `1` from day `1` on.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def movingMarket : PCMarket boolWorlds :=
  fun n => if n = 0 then boolVal (1 / 2) (by norm_num) (by norm_num) else boolVal 1 (by norm_num) le_rfl

/-- A one-shot trader: one share of the event `{true}` on day `0`, nothing afterwards.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oneShot : ∀ n, Strategy (boolWorlds n) :=
  fun n φ => if n = 0 ∧ φ = (fun b => b) then 1 else 0

/-- **N+ for `A′`**: `A′` is not identically `0` — the one-shot trader against the moving market
has `A′ 1 = ½` (bought at `½`, marked at `1`) — yet it is bounded (`A′ n = ½` for all `n ≥ 1`), so
the repaired accounting is neither trivial nor exploited by this trader.
Source: mandate X5 ("an N+ is `stretch`")
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem exists_A'_ne_zero :
    A' (fun _ => id) oneShot movingMarket 1 = 1 / 2 ∧
      ∀ n, 1 ≤ n → A' (fun _ => id) oneShot movingMarket n = 1 / 2 := by
  have h1 : A' (fun _ => id) oneShot movingMarket 1 = 1 / 2 := by
    rw [A'_succ, A'_zero, zero_add]
    unfold increment oneShot movingMarket boolVal price
    simp [Finset.sum_ite_eq']
    norm_num
  refine ⟨h1, fun n hn => ?_⟩
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact h1
    · rw [A'_succ, ih hpos]
      have hinc : increment (fun _ => id) n (oneShot n) (movingMarket n) (movingMarket (n + 1)) = 0 := by
        unfold increment oneShot
        simp [Nat.pos_iff_ne_zero.1 hpos]
      rw [hinc, add_zero]

end Cleanroom.Bli.BliExactness.WorldMarket
