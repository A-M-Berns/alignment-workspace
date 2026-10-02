import Cleanroom.Bli.UdtBliSist.Sist
import Cleanroom.Bli.UdtBliCore.Mugging
import Mathlib.Data.Fintype.Option

/-!
# `udt-bli-sist` · Homework: the homework mugging and the two readings of the policy point (T3, U6)

**The index** `hwIndex`: day 0 has the coin `p`; day 1 adds ten digit sentences `digit d`. **The
tables**: `Ask⁽ᵈ⁾` (coin `1`, digit `d` priced `1`, the others `0`), `Rec⁽ᵈ⁾` (coin `0`, digit `d`
priced `1`), and a residual `Other` (all `0`): twenty-one `0/1` tables indexed by
`Option (Bool × Fin 10)`. **Masses** `w` on each `Ask⁽ᵈ⁾`/`Rec⁽ᵈ⁾` and `1 − 20w` on `Other`.
**Actions** `Option (Fin 10)`: `none` = refuse, `some d'` = pay and state `d'`. **Independent uniform
points** (`prodLaw`, `1/11` each). **Utility**: at `Ask⁽ᵈ⁾`, `−c` iff the policy at `Ask⁽ᵈ⁾` is
`some d` (Omega accepts only the right digit; a wrong digit is a refusal); at `Rec⁽ᵈ⁾`, `V` iff the
policy at `Ask⁽ᵈ⁾` is `some d`; `0` at `Other`.

* **The written-out reading** (`writtenOut_pay_digit`): at the asked table `Ask⁽ᵈ⁾`,
  `EU Ask⁽ᵈ⁾ a − EU Ask⁽ᵈ⁾ b = w·(V − c)·([a = some d] − [b = some d])`, so `(pay, d)` is the unique
  one-step choice (strictly above every other action) whenever `w > 0` and `c < V` — although the
  prior's marginal over the digit is uniform (`digit_marginal`: each digit sentence is true with
  mass `2w`).
* **The term reading** (`term_flat`): `exAnteValue (const (some d'))` is `w·(V − c)` for every digit
  `d'` and `0` for `none` — a flat argmax over the digits (bli-soto-a-089's "one tenth" reading
  made exact: no digit is selected), exceeding refusal.

The two theorems are bli-soto-a-090's pair: the semantics of `A(·) = a` decides the verdict.
ATTRIBUTION-UNVETTED that the term reading is Soto's intended one (mandate §3.3).

Sources: bli-soto-a-028 (the definition), bli-soto-a-089 (Soto's claim), bli-soto-a-090 (Abram's
rebuttal), bli-soto-b-2-014, mandate T3.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore LogicalInduction LO.Propositional Finset

namespace Homework

/-! ## The index and the tables -/

/-- The coin sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev coinS : Sentence := Formula.atom 0

/-- The digit sentences `digit d := atom (d + 1)`.
Source: bli-soto-a-028 ("stating the correct digit of π")
Kind: D
Fidelity: n/a -/
def digitS (d : Fin 10) : Sentence := Formula.atom (d.val + 1)

/-- `digitS` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitS_injective : Function.Injective digitS := by
  intro d d' h
  unfold digitS at h
  have := Formula.atom.inj h
  exact Fin.ext (Nat.succ_injective this)

/-- A digit sentence is not the coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitS_ne_coinS (d : Fin 10) : digitS d ≠ coinS := by
  intro h
  unfold digitS coinS at h
  have := Formula.atom.inj h
  omega

/-- The day-1 sentences: the coin and the ten digits.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def day1 : Finset Sentence := {coinS} ∪ univ.image digitS

/-- **The homework index**: `S 0 = {coin}`, `S (m+1) = day1`.
Source: bli-soto-a-028; mandate T3
Kind: D
Fidelity: exact -/
def hwIndex : SmallIndex where
  S := fun m => if m = 0 then {coinS} else day1
  mono := by
    intro m
    by_cases h : m = 0
    · subst h
      simp only [if_true, Nat.zero_add, one_ne_zero, if_false]
      intro x hx
      unfold day1
      exact Finset.mem_union_left _ hx
    · simp only [h, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
      exact Finset.Subset.refl _

/-- The coin is small on day 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coinS_mem : coinS ∈ hwIndex.S 1 := by
  simp [hwIndex, day1]

/-- Every digit is small on day 1.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma digitS_mem (d : Fin 10) : digitS d ∈ hwIndex.S 1 := by
  simp only [hwIndex, one_ne_zero, if_false, day1, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨d, Finset.mem_univ _, rfl⟩

/-- The coin as a day-1 small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev coin1 : ↥(hwIndex.S 1) := ⟨coinS, coinS_mem⟩

/-- A digit as a day-1 small sentence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev digit1 (d : Fin 10) : ↥(hwIndex.S 1) := ⟨digitS d, digitS_mem d⟩

/-- The state indices: `some (true, d)` = `Ask⁽ᵈ⁾`, `some (false, d)` = `Rec⁽ᵈ⁾`, `none` = `Other`.
Source: mandate T3
Kind: D
Fidelity: n/a -/
abbrev Idx : Type := Option (Bool × Fin 10)

/-- **The homework tables**: `Ask⁽ᵈ⁾` prices the coin `1` and digit `d` `1`; `Rec⁽ᵈ⁾` prices the coin
`0` and digit `d` `1`; `Other` prices everything `0`.
Source: bli-soto-a-028; bli-soto-b-2-014 ("states `Q^{(d)}_Ask`, `Q^{(d)}_Rec`"); mandate T3
Kind: D
Fidelity: exact -/
def hwTable : Idx → Table hwIndex 1
  | none => fun _ => 0
  | some (b, d) => fun φ => if φ.1 = coinS then (if b then 1 else 0)
      else if φ.1 = digitS d then 1 else 0

/-- `hwTable (some (b, d))` at the coin.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hwTable_some_coin (b : Bool) (d : Fin 10) :
    hwTable (some (b, d)) coin1 = if b then 1 else 0 := by simp [hwTable]

/-- `hwTable (some (b, d))` at a digit.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hwTable_some_digit (b : Bool) (d d' : Fin 10) :
    hwTable (some (b, d)) (digit1 d') = if d' = d then 1 else 0 := by
  have hc := digitS_ne_coinS d'
  by_cases h : d' = d
  · subst h; simp [hwTable, hc]
  · have hne : digitS d' ≠ digitS d := fun e => h (digitS_injective e)
    simp [hwTable, hc, hne, h]

/-- `hwTable none` is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma hwTable_none (φ : ↥(hwIndex.S 1)) : hwTable none φ = 0 := rfl

/-- The tables are `0/1`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwTable_zeroOne (s : Idx) (φ : ↥(hwIndex.S 1)) : hwTable s φ = 0 ∨ hwTable s φ = 1 := by
  rcases s with _ | ⟨b, d⟩
  · exact Or.inl rfl
  · simp only [hwTable]
    split_ifs <;> simp

/-- `hwTable` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwTable_injective : Function.Injective hwTable := by
  intro s s' h
  rcases s with _ | ⟨b, d⟩ <;> rcases s' with _ | ⟨b', d'⟩
  · rfl
  · have := congrFun h (digit1 d'); simp at this
  · have := congrFun h (digit1 d); simp at this
  · have hc := congrFun h coin1
    have hd := congrFun h (digit1 d)
    simp only [hwTable_some_coin, hwTable_some_digit, if_true] at hc hd
    have hb : b = b' := by cases b <;> cases b' <;> simp at hc <;> rfl
    have hdd : d = d' := by
      by_contra hne
      rw [if_neg hne] at hd
      norm_num at hd
    rw [hb, hdd]

/-- **The carrier**: the twenty-one homework tables.
Source: mandate T3
Kind: D
Fidelity: exact -/
def hwTables : Finset (Table hwIndex 1) := univ.image hwTable

/-- The state of an index.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def st (s : Idx) : ↥hwTables := ⟨hwTable s, Finset.mem_image_of_mem _ (Finset.mem_univ s)⟩

/-- `st` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma st_injective : Function.Injective st := fun s s' h =>
  hwTable_injective (congrArg Subtype.val h)

/-- Every carrier table is some `st s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma st_surjective : Function.Surjective st := by
  intro T
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp T.2
  exact ⟨s, Subtype.ext hs⟩

/-- All carrier tables are `0/1`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwTables_zeroOne : ∀ (T : ↥hwTables) (φ : ↥(hwIndex.S 1)), T.1 φ = 0 ∨ T.1 φ = 1 := by
  intro T φ
  obtain ⟨s, rfl⟩ := st_surjective T
  exact hwTable_zeroOne s φ

/-! ## The prior -/

/-- The actions: `none` = refuse, `some d` = pay and state `d`.
Source: bli-soto-b-2-014 ("actions `{refuse} ∪ {(Pay, d')}`")
Kind: D
Fidelity: exact -/
abbrev Act : Type := Option (Fin 10)

/-- The uniform coordinate weights `1/11`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def hwHalf : ↥hwTables → Act → ℚ := fun _ _ => 1 / 11

/-- The coordinate weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwHalf_sum : ∀ T, ∑ a, hwHalf T a = 1 := by
  intro T
  simp only [hwHalf, Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- The masses: `w` on each `Ask⁽ᵈ⁾`/`Rec⁽ᵈ⁾`, `1 − 20w` on `Other`.
Source: mandate T3 ("masses `w` each (`20·w < 1`)")
Kind: D
Fidelity: exact -/
def hwW (w : ℚ) : Idx → ℚ
  | none => 1 - 20 * w
  | some _ => w

/-- The reference table: `Ask⁽ᵈ⁾` for both `Ask⁽ᵈ⁾` and `Rec⁽ᵈ⁾`, `Other` for itself.
Source: bli-soto-b-2-014 ("Omega paying `100` in `Q^{(d)}_Rec` iff `A(Q^{(d)}_Ask) = (Pay, d)`")
Kind: D
Fidelity: exact -/
def hwRef : Idx → ↥hwTables
  | none => st none
  | some (_, d) => st (some (true, d))

/-- The payoff read at the reference point: `−c·[b = some d]` at `Ask⁽ᵈ⁾`, `V·[b = some d]` at
`Rec⁽ᵈ⁾`, `0` at `Other`.
Source: bli-soto-b-2-014; mandate T3 (a wrong digit is a refusal)
Kind: D
Fidelity: exact -/
def hwPay (c V : ℚ) : Idx → Act → ℚ
  | none => fun _ => 0
  | some (true, d) => fun b => -c * (if b = some d then 1 else 0)
  | some (false, d) => fun b => V * (if b = some d then 1 else 0)

variable (w : ℚ) (hw : 0 ≤ w) (hw20 : 20 * w ≤ 1) (c V : ℚ)

/-- `hwW ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwW_nonneg (hw : 0 ≤ w) (hw20 : 20 * w ≤ 1) (s : Idx) : 0 ≤ hwW w s := by
  rcases s with _ | _ <;> simp [hwW] <;> linarith

/-- `∑ hwW = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwW_sum : ∑ s, hwW w s = 1 := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [hwW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The homework data**: masses `hwW`, `0/1` faith, independent uniform points, the reference-point
utility.
Source: bli-soto-a-028; bli-soto-b-2-014; mandate T3
Kind: D
Fidelity: exact -/
def hwData : IndepData hwIndex 1 hwTables Act where
  Ω₀ := Idx
  μ₀ := hwW w
  μ₀_nonneg := hwW_nonneg w hw hw20
  μ₀_sum_one := hwW_sum w
  state₀ := st
  small₀ := fun s φ => decide ((st s).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ hwTables_zeroOne
  ν := prodLaw hwHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [hwHalf])
  ν_sum_one := sum_prodLaw hwHalf_sum
  U₀ := fun s π => hwPay c V s (π (hwRef s))

/-- **The homework prior** (definition of record, T3).
Source: bli-soto-a-028; mandate T3
Kind: D
Fidelity: exact -/
def hwPrior : FiniteBLIPrior hwIndex 1 hwTables Act := (hwData w hw hw20 c V).toPrior

/-- The points are independent (product law).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma independentPoints : (hwPrior w hw hw20 c V).IndependentPoints :=
  (hwData w hw hw20 c V).independentPoints_toPrior_of_prodLaw hwHalf hwHalf_sum rfl

/-- Every point has mass `1/11`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥hwTables) (a : Act) : (hwPrior w hw hw20 c V).ppMass T a = 1 / 11 := by
  unfold hwPrior
  rw [IndepData.ppMass_toPrior]
  change massOf (prodLaw hwHalf) (fun π => π T = a) = 1 / 11
  rw [IndepData.massOf_prodLaw_point hwHalf hwHalf_sum]
  rfl

/-- `condPoint` at an independent pair is the point's own mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condPoint_ne (T Q : ↥hwTables) (hne : T ≠ Q) (b a : Act) :
    condPoint (hwPrior w hw hw20 c V) T Q b a = 1 / 11 := by
  unfold condPoint
  rw [independentPoints w hw hw20 c V T Q b a hne, ppMass_eq, ppMass_eq]
  norm_num

/-- The inner sum of `EU_ref` at a base index, for the point at `Ask⁽ᵈ⁾`: the payoff at `a` if the
index reads `Ask⁽ᵈ⁾`, the average payoff otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma inner_eq (d : Fin 10) (s : Idx) (a : Act) :
    (∑ b, condPoint (hwPrior w hw hw20 c V) (hwRef s) (st (some (true, d))) b a * hwPay c V s b) =
      if hwRef s = st (some (true, d)) then hwPay c V s a
      else ∑ b, 1 / 11 * hwPay c V s b := by
  split_ifs with h
  · rw [h]
    have hcs : ∀ b, condPoint (hwPrior w hw hw20 c V) (st (some (true, d))) (st (some (true, d))) b a =
        if b = a then 1 else 0 :=
      fun b => condPoint_self _ _ b a (by rw [ppMass_eq]; norm_num)
    simp only [hcs]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · apply Finset.sum_congr rfl
    intro b _
    rw [condPoint_ne w hw hw20 c V _ _ h]

/-- The reference of `s` is `Ask⁽ᵈ⁾` iff `s` is `Ask⁽ᵈ⁾` or `Rec⁽ᵈ⁾`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hwRef_eq_iff (d : Fin 10) (s : Idx) :
    hwRef s = st (some (true, d)) ↔ s = some (true, d) ∨ s = some (false, d) := by
  rcases s with _ | ⟨b, d'⟩
  · simp only [hwRef]
    constructor
    · intro h; exact absurd (st_injective h) (by simp)
    · intro h; simp at h
  · simp only [hwRef]
    constructor
    · intro h
      have := st_injective h
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      rw [this.2]
      cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (h | h) <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> rw [h.2]

/-- **The written-out reading**: at the asked table `Ask⁽ᵈ⁾`,
`EU Ask⁽ᵈ⁾ a − EU Ask⁽ᵈ⁾ b = w·(V − c)·([a = some d] − [b = some d])`.
Source: bli-soto-a-090 ("`A(Q̂) = 4` is a `−10` decision at `Ask` and `+100` at `Rec` … no other
branch class has significant opinions"); bli-soto-b-2-014; mandate T3(a)
Kind: P (`EU_ref` twice; only the two tables reading `Ask⁽ᵈ⁾` survive the difference)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_diff (d : Fin 10) (a b : Act) :
    (hwPrior w hw hw20 c V).EU (st (some (true, d))) a -
        (hwPrior w hw hw20 c V).EU (st (some (true, d))) b =
      w * (V - c) * ((if a = some d then 1 else 0) - (if b = some d then 1 else 0)) := by
  unfold hwPrior
  rw [EU_ref _ hwRef (hwPay c V) (fun _ _ => rfl), EU_ref _ hwRef (hwPay c V) (fun _ _ => rfl)]
  change (∑ s : Idx, hwW w s * ∑ b', condPoint (hwPrior w hw hw20 c V) (hwRef s)
      (st (some (true, d))) b' a * hwPay c V s b') -
    (∑ s : Idx, hwW w s * ∑ b', condPoint (hwPrior w hw hw20 c V) (hwRef s)
      (st (some (true, d))) b' b * hwPay c V s b') = _
  simp only [inner_eq, hwRef_eq_iff]
  rw [← Finset.sum_sub_distrib]
  have e : ∀ s : Idx, (hwW w s * (if s = some (true, d) ∨ s = some (false, d) then hwPay c V s a
      else ∑ b', 1 / 11 * hwPay c V s b') -
      hwW w s * (if s = some (true, d) ∨ s = some (false, d) then hwPay c V s b
      else ∑ b', 1 / 11 * hwPay c V s b')) =
      if s = some (true, d) then w * (-c) * ((if a = some d then 1 else 0) - (if b = some d then 1 else 0))
      else if s = some (false, d) then w * V * ((if a = some d then 1 else 0) - (if b = some d then 1 else 0))
      else 0 := by
    intro s
    by_cases h1 : s = some (true, d)
    · subst h1
      simp [hwW, hwPay]
      split_ifs <;> ring
    · by_cases h2 : s = some (false, d)
      · subst h2
        simp [hwW, hwPay]
        split_ifs <;> ring
      · simp [h1, h2]
  simp only [e]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, if_false,
    true_and, Bool.true_eq_false, Bool.false_eq_true, false_and]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

/-- **The written-out reading, the verdict**: `(pay, d)` is the one-step choice at `Ask⁽ᵈ⁾` and
strictly above every other action, whenever `0 < w` and `c < V`.
Source: bli-soto-a-090; bli-soto-b-2-014 ("show `argmax` over policy points indexed by the actual
asked state is `(Pay, d)` with `d` that state's digit"); mandate T3(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < w`, `c < V`; does not use faith -/
theorem writtenOut_pay_digit (hwpos : 0 < w) (hV : c < V) (d : Fin 10) :
    (hwPrior w hw hw20 c V).IsOneStepChoice (st (some (true, d))) (some d) ∧
      ∀ b, b ≠ some d → (hwPrior w hw hw20 c V).EU (st (some (true, d))) b <
        (hwPrior w hw hw20 c V).EU (st (some (true, d))) (some d) := by
  have hpos : 0 < w * (V - c) := mul_pos hwpos (by linarith)
  constructor
  · intro b
    have := EU_diff w hw hw20 c V d (some d) b
    simp only [if_true] at this
    have hb : (if b = some d then (1 : ℚ) else 0) ≤ 1 := by split_ifs <;> norm_num
    nlinarith
  · intro b hb
    have := EU_diff w hw hw20 c V d (some d) b
    simp only [if_true, if_neg hb] at this
    linarith

/-- Base masses are class masses (general action type; `Sist.lean`'s version is for `Bool`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma baseMass_eq_classMass' (p : ↥hwTables → Prop) [DecidablePred p] :
    (∑ s : Idx, if p (st s) then hwW w s else 0) =
      classMass (hwPrior w hw hw20 c V) (univ.filter p) := by
  unfold hwPrior classMass
  simp only [IndepData.stateMass_toPrior, Finset.sum_filter]
  change (∑ s : Idx, if p (st s) then hwW w s else 0) =
    ∑ T, if p T then massOf (hwW w) (fun s => st s = T) else 0
  unfold massOf
  have e : ∀ T : ↥hwTables, (if p T then (∑ s : Idx, if st s = T then hwW w s else 0) else 0) =
      ∑ s : Idx, if p T ∧ st s = T then hwW w s else 0 := by
    intro T
    split_ifs with hT
    · apply Finset.sum_congr rfl
      intro s _
      by_cases h : st s = T
      · simp [h, hT]
      · simp [h]
    · simp [hT]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hA : p (st s)
  · rw [if_pos hA, Finset.sum_eq_single (st s)]
    · simp [hA]
    · intro T _ hT
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hT h2.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hA]
    symm
    apply Finset.sum_eq_zero
    intro T _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hA (h2 ▸ h1)

/-- **The prior's marginal over the digit is uniform**: each digit sentence is true (priced `1`)
on tables of total mass `2w` — `Ask⁽ᵈ⁾` and `Rec⁽ᵈ⁾` — for every `d`.
Source: bli-soto-b-2-014 ("while `P`'s marginal over `d` is uniform"); mandate T3(a)
Kind: N+
Fidelity: exact (the prior does not know the digit: every digit has the same mass)
Hyps: (a) none -/
theorem digit_marginal (d : Fin 10) :
    classMass (hwPrior w hw hw20 c V) (univ.filter (fun T : ↥hwTables => T.1 (digit1 d) = 1)) =
      2 * w := by
  rw [← baseMass_eq_classMass' w hw hw20 c V (fun T : ↥hwTables => T.1 (digit1 d) = 1)]
  change (∑ s : Idx, if (hwTable s) (digit1 d) = 1 then hwW w s else 0) = 2 * w
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [hwTable_none, hwTable_some_digit, Fintype.sum_bool, hwW]
  norm_num
  ring

/-- **The term reading**: the ex-ante value of the constant policy `some d'` is `w·(V − c)` for every
digit `d'`, and that of `none` is `0` — a flat argmax over the digits, above refusal when `c < V`.
Source: bli-soto-a-089 ("all of them will have a mediocre payoff, corresponding to one tenth
probability of guessing it correctly"), made exact; bli-soto-a-090 ("under Soto's reading … the
argmax is flat"); mandate T3(a), §3.3
Kind: P
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem term_flat (a : Act) :
    (hwPrior w hw hw20 c V).exAnteValue (constPolicy a) = if a = none then 0 else w * (V - c) := by
  unfold hwPrior FiniteBLIPrior.exAnteValue condExp
  change (hwData w hw hw20 c V).toPrior.policyUtil (constPolicy a) /
    (hwData w hw hw20 c V).toPrior.policyMass (constPolicy a) = _
  rw [IndepData.policyUtil_toPrior, IndepData.policyMass_toPrior]
  have hν : 0 < (hwData w hw hw20 c V).ν (constPolicy a) :=
    prodLaw_pos (fun _ _ => by simp [hwHalf]) _
  rw [mul_div_cancel_left₀ _ (ne_of_gt hν)]
  change (∑ s : Idx, hwW w s * hwPay c V s a) = _
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hwW, hwPay]
  rcases a with _ | d
  · simp
  · simp only [Option.some.injEq, reduceCtorEq, if_false, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

/-- **The term reading, the verdict**: every `(pay, d')` is a term choice and they all tie (no digit
is selected), and `refuse` is not a term choice, whenever `0 < w` and `c < V`.
Source: bli-soto-a-089/090; mandate T3(a) ("flat argmax … exceeds `exAnteValue (const none)`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < w`, `c < V`; does not use faith -/
theorem term_verdict (hwpos : 0 < w) (hV : c < V) :
    (∀ d : Fin 10, IsTermChoice (hwPrior w hw hw20 c V) (some d)) ∧
      (∀ d d' : Fin 10, (hwPrior w hw hw20 c V).exAnteValue (constPolicy (some d)) =
        (hwPrior w hw hw20 c V).exAnteValue (constPolicy (some d'))) ∧
      ¬ IsTermChoice (hwPrior w hw hw20 c V) none := by
  have hpos : 0 < w * (V - c) := mul_pos hwpos (by linarith)
  refine ⟨fun d b => ?_, fun d d' => ?_, fun h => ?_⟩
  · rw [term_flat, term_flat]
    simp only [reduceCtorEq, if_false]
    split_ifs <;> linarith
  · rw [term_flat, term_flat]
    simp
  · have := h (some 0)
    rw [term_flat, term_flat] at this
    simp at this
    linarith

end Homework

end Cleanroom.Bli.UdtBliSist
