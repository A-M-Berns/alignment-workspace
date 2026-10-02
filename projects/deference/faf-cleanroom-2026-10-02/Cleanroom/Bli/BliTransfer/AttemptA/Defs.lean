import Cleanroom.Bli.BliFound.Size
import LogicalInduction.Framework.Criterion

/-!
# `bli-transfer` (attempt A) · Defs: the definitions of record

The expressible-overlay transfer theorem ([[bli-program]] §3.1) is about one logical inductor `Q`
and a market `overlay Q ov` computed from it: `Q`'s price on every day-`k` small sentence, a
rational re-pricing `ov k ψ` on the large ones. Nothing reads the overlay back into `Q` (one-way;
plan §0.4 rule 1 does not apply).

* `overlay Q ov` — **the** definition of record. `ov` is rational so that `ComputableMarket` can be
  inherited. **Tier B trap** (mandate T1 trap (iv)): `ExprMap.silent` below is the program's "an
  un-fired large sentence keeps the base's own value"; an `ov` that sets an un-fired large sentence
  to `1/2` violates it, and the transfer theorem is *false* for such an `ov` — a trader reading
  that leaf is not rewritten.
* `EF.freeBound` / `EF.Closed` — de Bruijn closedness. The splice puts every body under an
  administrative `letE` (mandate Known issue 8); a closed body reads no shifted variable, which is
  `EF.Closed.denoteWith_env_irrelevant`, the environment half of the program's
  `denote_eq_of_agree_on_leaves` (the leaf half is `Splice.spliceOn_denoteWith`).
* `ExprMap Q ov` — the program's hypotheses (i)–(ii) on the expression map, restated so that
  `expr` may fire on small sentences too (it must then reproduce `Q`'s price) and so that a body
  may read an earlier day (`p.1 ≤ k`; rank is preserved). The program's guard `¬ SmallOn k ψ`
  (mandate Known issue 6) is dropped at no loss and restated as `ExprMap.ofLargeOnly`.
  `ov_range` is a field: it does not follow from `fires`/`silent` (a body's denotation is
  unconstrained, and `expr` may be `none` on a small sentence).
* `RestrictedEC` — L4's restricted trader class (every leaf reads a price small on the day read),
  a disclosed `(c)`: strictly smaller than `EfficientlyComputable` (`Witnesses.lean` separates).
* `epsK`, `epsE`, `clampE`, `clamp`, `E1c` — L5's clamped re-pricing: `ε_k = 2^{-2^k}`, the
  expression computing `max (min x (1 − ε_k)) ε_k` in `var 0`, the clamped market on **every**
  sentence, and the constraint-1 variant `E1c` mirroring `Cleanroom.Bli.BliFound.E1x`.

Sources: [[bli-program]] §2.1, §3.1, §3.2(d); mandate § Definitions of record.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The overlay -/

/-- **The overlay market**: `Q`'s price on day-`k` small sentences, the rational re-pricing `ov`
on the large ones. One-way: nothing reads it back into `Q`. Tier B (mandate trap (iv)): an `ov`
that changes an un-fired large sentence breaks `ExprMap.silent`, and the transfer theorem is false
for it (a trader reading that leaf is not rewritten).
Source: [[bli-program]] §3.1; mandate § Definitions of record
Kind: D
Fidelity: exact -/
noncomputable def overlay (Q : History) (ov : ℕ → Sentence → ℚ) : History :=
  fun k ψ => if SmallOn k ψ then Q k ψ else (ov k ψ : ℝ)

/-- On a small sentence the overlay is `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma overlay_small {Q : History} {ov : ℕ → Sentence → ℚ} {k : ℕ} {ψ : Sentence}
    (h : SmallOn k ψ) : overlay Q ov k ψ = Q k ψ := by
  simp [overlay, h]

/-- On a large sentence the overlay is `ov`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma overlay_large {Q : History} {ov : ℕ → Sentence → ℚ} {k : ℕ} {ψ : Sentence}
    (h : ¬ SmallOn k ψ) : overlay Q ov k ψ = (ov k ψ : ℝ) := by
  simp [overlay, h]

/-! ## Closed expressions -/

/-- The least `m` such that every free `var i` of the expression has `i < m` (`0` for a closed
expression); `letE` binds `var 0` of its body.
Source: mandate § Definitions of record (`EF.freeBound`)
Kind: D
Fidelity: exact -/
def EF.freeBound : EF → ℕ
  | .price _ _ => 0
  | .const _ => 0
  | .add a b => Nat.max (EF.freeBound a) (EF.freeBound b)
  | .mul a b => Nat.max (EF.freeBound a) (EF.freeBound b)
  | .max a b => Nat.max (EF.freeBound a) (EF.freeBound b)
  | .safeRecip a => EF.freeBound a
  | .var i => i + 1
  | .letE x b => Nat.max (EF.freeBound x) (EF.freeBound b - 1)

/-- A closed expression: no free `var`.
Source: mandate § Definitions of record (`EF.Closed`)
Kind: D
Fidelity: exact -/
def EF.Closed (e : EF) : Prop := EF.freeBound e = 0

/-- The denotation depends on the environment only below `freeBound`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.denoteWith_congr_env (e : EF) (V : History) :
    ∀ (ρ ρ' : List ℝ), (∀ i < EF.freeBound e, ρ.getD i 0 = ρ'.getD i 0) →
      e.denoteWith ρ V = e.denoteWith ρ' V := by
  induction e with
  | price φ n => intro ρ ρ' _; rfl
  | const q => intro ρ ρ' _; rfl
  | add a b iha ihb =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | mul a b iha ihb =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | max a b iha ihb =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | safeRecip a iha =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      rw [iha ρ ρ' h]
  | var i =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      exact h i (by simp [EF.freeBound])
  | letE x b ihx ihb =>
      intro ρ ρ' h
      simp only [EF.denoteWith]
      rw [ihx ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _)))]
      apply ihb
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
          simp only [List.getD_cons_succ]
          apply h j
          simp only [EF.freeBound]
          exact lt_of_lt_of_le (by omega : j < EF.freeBound b - 1) (Nat.le_max_right _ _)

/-- **Environment irrelevance for closed expressions**: the environment half of the program's
`denote_eq_of_agree_on_leaves`. A closed body spliced under the administrative `letE` reads no
shifted variable.
Source: [[bli-program]] §3.1 (proof sketch, `denote_eq_of_agree_on_leaves`); mandate Known issue 8
Kind: L
Fidelity: exact -/
lemma EF.Closed.denoteWith_env_irrelevant {e : EF} (he : EF.Closed e) (V : History)
    (ρ ρ' : List ℝ) : e.denoteWith ρ V = e.denoteWith ρ' V :=
  EF.denoteWith_congr_env e V ρ ρ' (fun i hi => absurd hi (by unfold EF.Closed at he; omega))

/-- A closed expression denotes its closed-environment value in every environment.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.Closed.denoteWith_eq_denote {e : EF} (he : EF.Closed e) (V : History) (ρ : List ℝ) :
    e.denoteWith ρ V = e.denote V :=
  EF.Closed.denoteWith_env_irrelevant he V ρ []

/-- The rank of an expression is bounded by a bound on the days of its price queries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.rank_le_of_priceQueries (e : EF) (k : ℕ)
    (h : ∀ p ∈ e.priceQueries, p.1 ≤ k) : e.rank ≤ k := by
  induction e with
  | price φ n => exact h (n, φ) (by simp [EF.priceQueries])
  | const q => simp [EF.rank]
  | add a b iha ihb =>
      simp only [EF.rank, EF.priceQueries] at h ⊢
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (List.mem_append_left _ hp)),
        ihb (fun p hp => h p (List.mem_append_right _ hp))⟩
  | mul a b iha ihb =>
      simp only [EF.rank, EF.priceQueries] at h ⊢
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (List.mem_append_left _ hp)),
        ihb (fun p hp => h p (List.mem_append_right _ hp))⟩
  | max a b iha ihb =>
      simp only [EF.rank, EF.priceQueries] at h ⊢
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (List.mem_append_left _ hp)),
        ihb (fun p hp => h p (List.mem_append_right _ hp))⟩
  | safeRecip a iha =>
      simp only [EF.rank, EF.priceQueries] at h ⊢
      exact iha h
  | var i => simp [EF.rank]
  | letE x b ihx ihb =>
      simp only [EF.rank, EF.priceQueries] at h ⊢
      exact Nat.max_le.mpr ⟨ihx (fun p hp => h p (List.mem_append_left _ hp)),
        ihb (fun p hp => h p (List.mem_append_right _ hp))⟩

/-! ## The expression map -/

/-- **An expression map for the overlay** — the program's hypotheses (i)–(ii) restated
(mandate § Definitions of record). `expr k ψ = some e` means: the day-`k` overlay price of `ψ`
is the value of the closed expression `e` (`fires`), which reads only prices of sentences small on
the day read, at days `≤ k` (`leaves`); `expr k ψ = none` means the overlay does not touch `ψ`
on day `k` (`silent`: either `ov` agrees with `Q` there, or `ψ` is small and the overlay is `Q`
by definition). The guard "`expr` fires only on large sentences" is deliberately absent (Known
issue 6): a map may fire on a small sentence provided it reproduces `Q`'s price; nothing
downstream needs the guard (`ExprMap.ofLargeOnly` states the guarded form). `ov_range` keeps the
overlay a `[0,1]`-market; it is not derivable from the other fields.
Source: [[bli-program]] §3.1 (i)–(ii); mandate § Definitions of record; Known issue 6
Kind: D
Fidelity: variant: guard dropped (fires anywhere the value is reproduced), leaves may read earlier days -/
structure ExprMap (Q : History) (ov : ℕ → Sentence → ℚ) where
  /-- The expression map. -/
  expr : ℕ → Sentence → Option EF
  /-- Every body is closed. -/
  closed : ∀ k ψ e, expr k ψ = some e → EF.Closed e
  /-- Every leaf of a body reads a day-`≤ k` price of a sentence small on the day read. -/
  leaves : ∀ k ψ e, expr k ψ = some e → ∀ p ∈ e.priceQueries, p.1 ≤ k ∧ SmallOn p.1 p.2
  /-- A body computes the overlay price. -/
  fires : ∀ k ψ e, expr k ψ = some e → e.denote Q = overlay Q ov k ψ
  /-- An un-fired sentence is priced as by `Q` (Tier B), or is small. -/
  silent : ∀ k ψ, expr k ψ = none → (ov k ψ : ℝ) = Q k ψ ∨ SmallOn k ψ
  /-- The re-pricing stays in `[0,1]`. -/
  ov_range : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1

/-- The days read by any body are bounded by the firing day: the rank discipline the splice's
rank law needs.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ExprMap.rank_le {Q : History} {ov : ℕ → Sentence → ℚ} (E : ExprMap Q ov)
    (k : ℕ) (ψ : Sentence) (e : EF) (h : E.expr k ψ = some e) : e.rank ≤ k :=
  EF.rank_le_of_priceQueries e k (fun p hp => (E.leaves k ψ e h p hp).1)

/-- **The program's guarded form as a corollary**: an expression map that fires only on large
sentences (`hguard`), computes `ov` there (`hfires`), and whose un-fired large sentences keep
`Q`'s value (`hsilent`) is an `ExprMap` — so [[bli-program]] §3.1's statement is literally an
instance of the definition of record.
Source: [[bli-program]] §3.1 (i)–(ii) with the guard `¬ SmallOn k ψ`; mandate Known issue 6
Kind: D
Fidelity: exact (the program's guarded form) -/
def ExprMap.ofLargeOnly (Q : History) (ov : ℕ → Sentence → ℚ)
    (expr : ℕ → Sentence → Option EF)
    (hguard : ∀ k ψ e, expr k ψ = some e → ¬ SmallOn k ψ)
    (hclosed : ∀ k ψ e, expr k ψ = some e → EF.Closed e)
    (hleaves : ∀ k ψ e, expr k ψ = some e → ∀ p ∈ e.priceQueries, p.1 ≤ k ∧ SmallOn p.1 p.2)
    (hfires : ∀ k ψ e, expr k ψ = some e → e.denote Q = (ov k ψ : ℝ))
    (hsilent : ∀ k ψ, expr k ψ = none → ¬ SmallOn k ψ → (ov k ψ : ℝ) = Q k ψ)
    (hrange : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) : ExprMap Q ov where
  expr := expr
  closed := hclosed
  leaves := hleaves
  fires := fun k ψ e h => by rw [hfires k ψ e h, overlay_large (hguard k ψ e h)]
  silent := fun k ψ h => by
    by_cases hs : SmallOn k ψ
    · exact Or.inr hs
    · exact Or.inl (hsilent k ψ h hs)
  ov_range := hrange

/-! ## The restricted class (L4) -/

/-- **L4's restricted trader class**: efficiently computable, and every price leaf of every
coefficient, on every day, reads a sentence small on the day read. A disclosed `(c)`: strictly
smaller than `EfficientlyComputable` (`Witnesses.restrictedEC_separation`), so a theorem
quantified over it is *not* the criterion.
Source: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`; mandate T2
Kind: D
Fidelity: variant: (c) a proper subclass of the criterion's class -/
def RestrictedEC (Tr : Trader) : Prop :=
  EfficientlyComputable Tr ∧
    ∀ n, ∀ p ∈ (Tr.strat n).trades, ∀ q ∈ p.1.priceQueries, SmallOn q.1 q.2

/-! ## The clamp (L5) -/

/-- `ε_k = 2^{-2^k}`.
Source: [[bli-program]] §3.2(d); mandate § Definitions of record (`epsK`)
Kind: D
Fidelity: exact -/
def epsK (k : ℕ) : ℚ := (1 / 2 : ℚ) ^ (2 ^ k)

/-- `ε_{k+1} = ε_k²`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsK_succ (k : ℕ) : epsK (k + 1) = epsK k * epsK k := by
  unfold epsK
  rw [pow_succ, pow_mul, sq]

/-- `ε_k > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsK_pos (k : ℕ) : 0 < epsK k := by
  unfold epsK
  positivity

/-- `ε_k ≤ 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsK_le_half (k : ℕ) : epsK k ≤ 1 / 2 := by
  unfold epsK
  calc (1 / 2 : ℚ) ^ (2 ^ k) ≤ (1 / 2 : ℚ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_two_pow)
    _ = 1 / 2 := pow_one _

/-- `ε_k` as a closed, price-free expression: `k` nested `letE`-squarings of `const (1/2)`.
Source: mandate § Definitions of record (`clampE`)
Kind: D
Fidelity: exact -/
def epsE : ℕ → EF
  | 0 => .const (1 / 2)
  | k + 1 => .letE (epsE k) (.mul (.var 0) (.var 0))

/-- `epsE k` denotes `ε_k` in every environment.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsE_denoteWith (k : ℕ) (ρ : List ℝ) (V : History) :
    (epsE k).denoteWith ρ V = (epsK k : ℝ) := by
  induction k generalizing ρ with
  | zero => simp [epsE, epsK]
  | succ k ih =>
      simp only [epsE, EF.denoteWith, ih, List.getD_cons_zero, epsK_succ, Rat.cast_mul]

/-- `epsE k` is closed.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsE_closed (k : ℕ) : EF.Closed (epsE k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold EF.Closed at ih ⊢
      simp [epsE, EF.freeBound, ih]

/-- `epsE k` has no price leaves.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsE_priceQueries (k : ℕ) : (epsE k).priceQueries = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [epsE, EF.priceQueries, ih]

/-- `(epsE k).cost = 4k + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma epsE_cost (k : ℕ) : (epsE k).cost = 4 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [epsE, EF.cost, ih]; omega

/-- Negation as an expression: `mul (const (−1)) a`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def negE (a : EF) : EF := .mul (.const (-1)) a

/-- **The clamp body in `var 0`**: `max (min x (1 − ε_k)) ε_k` for `x = var 0`, with
`min a b = −max (−a) (−b)`; `ε_k` is bound once by an outer `letE` (so inside it the price is
`var 1` and `ε_k` is `var 0`). Not closed: `var 0` is free (it is the price the rewrite binds).
Source: [[bli-program]] §3.2(d); mandate § Definitions of record (`clampE`)
Kind: D
Fidelity: exact -/
def clampE (k : ℕ) : EF :=
  .letE (epsE k)
    (.max (negE (.max (negE (.var 1)) (negE (.add (.const 1) (negE (.var 0)))))) (.var 0))

/-- `clampE k` reads the price as `var 0` and computes the clamp.
Source: mandate § Definitions of record (`clampE_denote`)
Kind: L
Fidelity: exact -/
lemma clampE_denoteWith (k : ℕ) (x : ℝ) (ρ : List ℝ) (V : History) :
    (clampE k).denoteWith (x :: ρ) V = Max.max (Min.min x (1 - (epsK k : ℝ))) (epsK k : ℝ) := by
  simp only [clampE, negE, EF.denoteWith, epsE_denoteWith, List.getD_cons_zero,
    List.getD_cons_succ, Rat.cast_neg, Rat.cast_one]
  have h1 : (-1 : ℝ) * (Max.max ((-1) * x) ((-1) * (1 + (-1) * (epsK k : ℝ))))
      = Min.min x (1 - (epsK k : ℝ)) := by
    rw [show (-1 : ℝ) * x = -x by ring, show (-1 : ℝ) * (1 + (-1) * (epsK k : ℝ)) = -(1 - (epsK k : ℝ)) by ring,
      max_neg_neg, neg_mul, one_mul, neg_neg]
  rw [h1]

/-- `(clampE k).cost ≤ 4k + 18`.
Source: mandate § Definitions of record (`clampE_cost_le`)
Kind: L
Fidelity: exact -/
lemma clampE_cost_le (k : ℕ) : (clampE k).cost ≤ 4 * k + 18 := by
  simp only [clampE, negE, EF.cost, epsE_cost]
  omega

/-- `clampE k` has exactly one free variable, `var 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clampE_freeBound (k : ℕ) : EF.freeBound (clampE k) = 1 := by
  have h := epsE_closed k
  unfold EF.Closed at h
  simp [clampE, negE, EF.freeBound, h]

/-- `clampE k` has no price leaves.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clampE_priceQueries (k : ℕ) : (clampE k).priceQueries = [] := by
  simp [clampE, negE, EF.priceQueries, epsE_priceQueries]

/-- **The clamped market** (L5): every sentence's day-`k` price pulled into `[ε_k, 1 − ε_k]`.
Applied to **every** sentence, not only small ones — the clamp is a perturbation of `Q`, not an
overlay.
Source: [[bli-program]] §3.2(d); mandate § Definitions of record (`clamp`)
Kind: D
Fidelity: exact -/
noncomputable def clamp (Q : History) : History :=
  fun k ψ => Max.max (Min.min (Q k ψ) (1 - (epsK k : ℝ))) (epsK k : ℝ)

/-- **E1c — clamped small agreement**: `P_n φ = clamp Q n φ` for every day-`n` small `φ`; the
constraint-1 variant for `bli-assemble`, mirroring `Cleanroom.Bli.BliFound.E1x`.
Source: [[bli-program]] §3.2(d); mandate § Definitions of record (`E1c`)
Kind: D
Fidelity: exact -/
def E1c (Q P : History) : Prop := ∀ n φ, φ ∈ smallSet n → P n φ = clamp Q n φ

/-- The clamp lands in `[ε_k, 1 − ε_k]` (non-dogmatism everywhere).
Source: mandate T3 (`clamp_mem_Ioo`)
Kind: L
Fidelity: exact -/
lemma clamp_mem_Icc (Q : History) (k : ℕ) (φ : Sentence) :
    (epsK k : ℝ) ≤ clamp Q k φ ∧ clamp Q k φ ≤ 1 - (epsK k : ℝ) := by
  have hhalf : (epsK k : ℝ) ≤ 1 / 2 := by
    have h' : ((epsK k : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr (epsK_le_half k)
    simpa using h'
  unfold clamp
  constructor
  · exact le_max_right _ _
  · apply max_le
    · exact min_le_right _ _
    · linarith

/-- The clamp stays within `ε_k` of `Q` when `Q` prices in `[0,1]`.
Source: mandate T3 (the settlement term)
Kind: L
Fidelity: exact -/
lemma abs_clamp_sub_le (Q : History) (k : ℕ) (φ : Sentence)
    (h : 0 ≤ Q k φ ∧ Q k φ ≤ 1) : |clamp Q k φ - Q k φ| ≤ (epsK k : ℝ) := by
  have hhalf : (epsK k : ℝ) ≤ 1 / 2 := by
    have h' : ((epsK k : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr (epsK_le_half k)
    simpa using h'
  have hpos : (0 : ℝ) < epsK k := by exact_mod_cast epsK_pos k
  unfold clamp
  rw [abs_le]
  rcases h with ⟨h0, h1⟩
  constructor
  · -- lower: clamp ≥ Q − ε
    have : Min.min (Q k φ) (1 - (epsK k : ℝ)) ≥ Q k φ - (epsK k : ℝ) := by
      apply le_min <;> linarith
    have := le_max_left (Min.min (Q k φ) (1 - (epsK k : ℝ))) (epsK k : ℝ)
    linarith
  · -- upper: clamp ≤ Q + ε
    rw [sub_le_iff_le_add]
    apply max_le
    · have := min_le_left (Q k φ) (1 - (epsK k : ℝ))
      linarith
    · linarith

end Cleanroom.Bli.BliTransfer.AttemptA
