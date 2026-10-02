import Cleanroom.Bli.BliFound.Size
import LogicalInduction.Framework.Criterion

/-!
# `bli-transfer` · attempt B · Defs: the definitions of record

The objects every target of the package is stated over, copied from the mandate
(`run/wp/bli-transfer/bli-transfer-mandate.md` § Definitions of record) so that the two
attempts can be diffed:

* `overlay Q ov` — the market that copies the logical inductor `Q` on day-small sentences and
  re-prices the large ones by `ov` (rational, so `ComputableMarket` can be inherited);
* `EF.freeBound` / `EF.Closed` — the de Bruijn free-variable bound of an expressible feature,
  and closedness (`freeBound = 0`); the environment-irrelevance lemma
  `Closed.denoteWith_env_irrelevant`;
* `ExprMap Q ov` — an *expression map*: for each `(k, ψ)` optionally a closed body whose price
  leaves are small on their (earlier or same) day and whose denotation against `Q` is the
  overlay's price; where it is silent the overlay agrees with `Q`;
* `RestrictedEC` — the disclosed `(c)` class of T2: e.c. traders whose every price leaf reads a
  price small on the day read;
* `epsK`, `epsE`, `clampE`, `clamp`, `E1c` — T3's clamp: `ε_k = 2^{-2^k}`, the closed
  expression computing `ε_k`, the clamp body in `var 0`, the clamped market, and the
  constraint-1 variant for `bli-assemble`.

Nothing here is `Sminus`-scoped or state-atom-specific (mandate: the transfer theorem is about
an arbitrary expression map).

**Tier B (trap (iv)).** `ExprMap.silent` is the program's "Tier B is the base's own value": on
a large sentence where the map does not fire, `ov` must equal `Q`. An `ov` that sets un-fired
large sentences to `1/2` is *not* an `ExprMap`, and the transfer theorem is false for it (a
trader reading such a leaf is not rewritten).

Sources: [[bli-program]] §2.1, §3.1, §3.2(d); mandate § Definitions of record.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The overlay -/

/-- **The overlay market** (the definition of record): copy `Q` on day-small sentences, price
the large ones by `ov`. `ov` is rational so `ComputableMarket` can be inherited from `Q`'s
certificate. Tier B: where an expression map is silent on a large sentence, `ov` must agree
with `Q` (`ExprMap.silent`); the theorem is false for an `ov` that re-prices un-fired large
sentences arbitrarily.
Source: [[bli-program]] §2.1, §3.1; bli-paper-031; mandate § Definitions
Kind: D
Fidelity: exact -/
noncomputable def overlay (Q : History) (ov : ℕ → Sentence → ℚ) : History :=
  fun k ψ => if SmallOn k ψ then Q k ψ else (ov k ψ : ℝ)

/-- On a day-small sentence the overlay is `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma overlay_small {Q : History} {ov : ℕ → Sentence → ℚ} {k : ℕ} {ψ : Sentence}
    (h : SmallOn k ψ) : overlay Q ov k ψ = Q k ψ := by
  simp [overlay, h]

/-- On a day-large sentence the overlay is `ov`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma overlay_large {Q : History} {ov : ℕ → Sentence → ℚ} {k : ℕ} {ψ : Sentence}
    (h : ¬ SmallOn k ψ) : overlay Q ov k ψ = (ov k ψ : ℝ) := by
  simp [overlay, h]

/-- The overlay's prices lie in `[0, 1]` when `Q`'s and `ov`'s do.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlay_mem_Icc {Q : History} {ov : ℕ → Sentence → ℚ}
    (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1)
    (k : ℕ) (ψ : Sentence) : 0 ≤ overlay Q ov k ψ ∧ overlay Q ov k ψ ≤ 1 := by
  unfold overlay
  split_ifs
  · exact hQ k ψ
  · obtain ⟨h0, h1⟩ := hov k ψ
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

/-! ## Closed expressions -/

namespace EF

/-- The de Bruijn free-variable bound of an expressible feature: every free `var i` has
`i < freeBound`. `var i ↦ i + 1`; a `letE` binds one variable in its body.
Source: [[bli-program]] §7.15; mandate § Definitions (Known issue 8)
Kind: D
Fidelity: exact -/
def freeBound : LogicalInduction.EF → ℕ
  | .price _ _ => 0
  | .const _ => 0
  | .add a b => Nat.max (freeBound a) (freeBound b)
  | .mul a b => Nat.max (freeBound a) (freeBound b)
  | .max a b => Nat.max (freeBound a) (freeBound b)
  | .safeRecip a => freeBound a
  | .var i => i + 1
  | .letE x b => Nat.max (freeBound x) (freeBound b - 1)

/-- A feature is **closed** when it has no free variable: its `freeBound` is `0`. A body spliced
under the administrative `letE` of the rewrite then reads no shifted variable.
Source: mandate § Definitions (Known issue 8)
Kind: D
Fidelity: exact -/
def Closed (e : LogicalInduction.EF) : Prop := freeBound e = 0

/-- **Environment agreement below the free bound is all that matters.** Two environments that
agree on every index below `freeBound e` give `e` the same denotation. This is the
"environment" half of the program's `denote_eq_of_agree_on_leaves`.
Source: mandate § Definitions; [[bli-program]] §3.1
Kind: P
Fidelity: exact -/
lemma denoteWith_eq_of_agree (e : LogicalInduction.EF) (V : History) :
    ∀ (ρ ρ' : List ℝ), (∀ i, i < freeBound e → ρ.getD i 0 = ρ'.getD i 0) →
      e.denoteWith ρ V = e.denoteWith ρ' V := by
  induction e with
  | price φ n => intro ρ ρ' _; rfl
  | const q => intro ρ ρ' _; rfl
  | add a b iha ihb =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_add]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | mul a b iha ihb =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_mul]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | max a b iha ihb =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_max]
      rw [iha ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _))),
        ihb ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_right _ _)))]
  | safeRecip a iha =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_safeRecip]
      rw [iha ρ ρ' h]
  | var i =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_var]
      exact h i (Nat.lt_succ_self i)
  | letE x b ihx ihb =>
      intro ρ ρ' h
      simp only [freeBound] at h
      simp only [LogicalInduction.EF.denoteWith_letE]
      have hx : x.denoteWith ρ V = x.denoteWith ρ' V :=
        ihx ρ ρ' (fun i hi => h i (lt_of_lt_of_le hi (Nat.le_max_left _ _)))
      rw [hx]
      apply ihb
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [List.getD_cons_succ]
          exact h j (lt_of_lt_of_le (by omega) (Nat.le_max_right _ _))

/-- **A closed feature ignores its environment.**
Source: mandate § Definitions (`Closed.denoteWith_env_irrelevant`)
Kind: L
Fidelity: exact -/
lemma Closed.denoteWith_env_irrelevant {e : LogicalInduction.EF} (he : Closed e) (V : History)
    (ρ ρ' : List ℝ) : e.denoteWith ρ V = e.denoteWith ρ' V :=
  denoteWith_eq_of_agree e V ρ ρ' (fun i hi => by unfold Closed at he; omega)

/-- A closed feature's denotation in any environment is its closed denotation `denote`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Closed.denoteWith_eq_denote {e : LogicalInduction.EF} (he : Closed e) (V : History)
    (ρ : List ℝ) : e.denoteWith ρ V = e.denote V :=
  he.denoteWith_env_irrelevant V ρ []

/-- The rank of a feature is bounded by any bound on the days of its price queries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rank_le_of_priceQueries (e : LogicalInduction.EF) (k : ℕ)
    (h : ∀ p ∈ e.priceQueries, p.1 ≤ k) : e.rank ≤ k := by
  induction e with
  | price φ n => exact h (n, φ) (by simp [LogicalInduction.EF.priceQueries])
  | const q => simp
  | add a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.rank_add]
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))⟩
  | mul a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.rank_mul]
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))⟩
  | max a b iha ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.rank_max]
      exact Nat.max_le.mpr ⟨iha (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))⟩
  | safeRecip a iha =>
      simp only [LogicalInduction.EF.priceQueries] at h
      simpa using iha h
  | var i => simp
  | letE x b ihx ihb =>
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.rank_letE]
      exact Nat.max_le.mpr ⟨ihx (fun p hp => h p (Or.inl hp)), ihb (fun p hp => h p (Or.inr hp))⟩

end EF

/-! ## Expression maps -/

/-- **An expression map** for the overlay `overlay Q ov`: the program's §3.1 hypotheses
(i)–(ii), restated so that `expr` may also fire on small sentences (then it must reproduce
`Q`'s price) and so that a body's leaf may read an *earlier* day (`p.1 ≤ k`; rank is
preserved). The guard "`¬ SmallOn k ψ`" of the program is dropped because it would force the
certificate to decide smallness from a raw spelling in polynomial time (Known issue 6);
`ExprMap.ofLargeOnly` states the guarded form as a corollary.

* `closed`: every body is closed (it reads no variable of the surrounding feature);
* `leaves`: every price leaf of a body reads a day `≤ k` and a sentence small on that day;
* `fires`: where the map fires, the body's closed denotation against `Q` is the overlay's price;
* `silent`: where it does not, the overlay agrees with `Q` (Tier B) — either `ov = Q` there or
  the sentence is small (where the overlay is `Q` by definition);
* `ov_range`: `ov` prices in `[0, 1]` (needed for the day-`< N` magnitude bound; not derivable
  from `fires`/`silent` alone since `ov` is unconstrained on small sentences where `expr` is
  `none`).
Source: [[bli-program]] §3.1 (i)–(ii), corrected per mandate Known issue 6
Kind: D
Fidelity: variant: no smallness guard on `expr`; leaves may read days `≤ k` -/
structure ExprMap (Q : History) (ov : ℕ → Sentence → ℚ) where
  /-- The body for `(k, ψ)`, if any. -/
  expr : ℕ → Sentence → Option LogicalInduction.EF
  /-- Bodies are closed. -/
  closed : ∀ k ψ e, expr k ψ = some e → EF.Closed e
  /-- Bodies read only small prices of days `≤ k`. -/
  leaves : ∀ k ψ e, expr k ψ = some e →
    ∀ p ∈ e.priceQueries, p.1 ≤ k ∧ SmallOn p.1 p.2
  /-- A fired body denotes the overlay's price. -/
  fires : ∀ k ψ e, expr k ψ = some e → e.denote Q = overlay Q ov k ψ
  /-- Where silent, the overlay is `Q` (Tier B). -/
  silent : ∀ k ψ, expr k ψ = none → (ov k ψ : ℝ) = Q k ψ ∨ SmallOn k ψ
  /-- `ov` prices in `[0, 1]`. -/
  ov_range : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1

namespace ExprMap

variable {Q : History} {ov : ℕ → Sentence → ℚ}

/-- Every body has rank `≤` its day (from `leaves`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rank_le (E : ExprMap Q ov) : ∀ k ψ e, E.expr k ψ = some e → e.rank ≤ k :=
  fun k ψ e he => EF.rank_le_of_priceQueries e k (fun p hp => (E.leaves k ψ e he p hp).1)

/-- Where the map is silent, the overlay agrees with `Q` outright.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma overlay_eq_of_silent (E : ExprMap Q ov) {k : ℕ} {ψ : Sentence}
    (h : E.expr k ψ = none) : overlay Q ov k ψ = Q k ψ := by
  rcases E.silent k ψ h with hov | hsmall
  · by_cases hs : SmallOn k ψ
    · simp [hs]
    · simp [hs, hov]
  · simp [hsmall]

/-- **The program's guarded form as a corollary.** Data that fires exactly on the day-large
sentences — with closed bodies reading small prices of days `≤ k` and denoting `ov` there — is
an expression map in the sense of record.
Source: [[bli-program]] §3.1 (i)–(ii) literally; mandate Known issue 6
Kind: D
Fidelity: exact (the guarded statement) -/
def ofLargeOnly (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hfire : ∀ k ψ, ¬ SmallOn k ψ → ∃ e, expr k ψ = some e)
    (hguard : ∀ k ψ, SmallOn k ψ → expr k ψ = none)
    (hclosed : ∀ k ψ e, expr k ψ = some e → EF.Closed e)
    (hleaves : ∀ k ψ e, expr k ψ = some e → ∀ p ∈ e.priceQueries, p.1 ≤ k ∧ SmallOn p.1 p.2)
    (hval : ∀ k ψ e, expr k ψ = some e → e.denote Q = (ov k ψ : ℝ))
    (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1) : ExprMap Q ov where
  expr := expr
  closed := hclosed
  leaves := hleaves
  fires := fun k ψ e he => by
    have hlarge : ¬ SmallOn k ψ := fun hs => by rw [hguard k ψ hs] at he; exact absurd he (by simp)
    rw [hval k ψ e he, overlay_large hlarge]
  silent := fun k ψ hnone => by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, he⟩ := hfire k ψ hcon.2
    rw [hnone] at he
    exact absurd he (by simp)
  ov_range := hov

end ExprMap

/-! ## The restricted class (T2) -/

/-- **The restricted class** of T2: efficiently computable traders whose every price leaf, on
every day (including `0`), reads a price of a sentence small **on the day read**. A `(c)`:
strictly smaller than `EfficientlyComputable` (`Witnesses.lean` ships the separation) — not
the criterion's class.
Source: bli-slides-002 (reading "traders never read large prices"); [[bli-program]] `C:I4`; mandate T2
Kind: D
Fidelity: exact -/
def RestrictedEC (Tr : Trader) : Prop :=
  EfficientlyComputable Tr ∧
    ∀ n, ∀ p ∈ (Tr.strat n).trades, ∀ q ∈ p.1.priceQueries, SmallOn q.1 q.2

/-! ## The clamp (T3) -/

/-- `ε_k = 2^{-2^k}` as a rational: `(1/2)^(2^k)`.
Source: [[bli-program]] §3.2(d); mandate T3
Kind: D
Fidelity: exact -/
def epsK (k : ℕ) : ℚ := (1 / 2 : ℚ) ^ (2 ^ k)

/-- `ε_k = (1/2)^(2^k)` (the defining equation, named as the mandate asks).
Source: mandate § Definitions
Kind: L
Fidelity: n/a -/
lemma ε_def (k : ℕ) : epsK k = (1 / 2 : ℚ) ^ (2 ^ k) := rfl

/-- The closed expression computing `ε_k` by `k` nested `letE`-squarings of `const (1/2)`:
`epsE 0 = const (1/2)`, `epsE (j+1) = letE (epsE j) (mul (var 0) (var 0))`. Because the
squaring is nested *inside* the bound value rather than around the clamp body, `epsE k` is
closed and its denotation is independent of the environment; the clamp body's `var 0` therefore
still names the bound price (no de Bruijn shifting to track).
Source: mandate § Definitions (`clampE`)
Kind: D
Fidelity: exact -/
def epsE : ℕ → LogicalInduction.EF
  | 0 => .const (1 / 2)
  | j + 1 => .letE (epsE j) (.mul (.var 0) (.var 0))

/-- `min a b` as an expressible feature: `−max(−a, −b)`, with negation by `mul (const (−1))`.
Source: mandate § Definitions (`clampE`)
Kind: D
Fidelity: exact -/
def minE (a b : LogicalInduction.EF) : LogicalInduction.EF :=
  .mul (.const (-1)) (.max (.mul (.const (-1)) a) (.mul (.const (-1)) b))

/-- **The clamp body**: the expression in `var 0` computing `max (min (var 0) (1 − ε_k)) ε_k`.
Spliced under the administrative binding `letE (price φ k) (clampE k)`, `var 0` is the day-`k`
price of `φ`.
Source: [[bli-program]] §3.2(d); mandate § Definitions (`clampE`)
Kind: D
Fidelity: exact -/
def clampE (k : ℕ) : LogicalInduction.EF :=
  .max (minE (.var 0) (.add (.const 1) (.mul (.const (-1)) (epsE k)))) (epsE k)

/-- **The clamped market**: every sentence's price is clamped into `[ε_k, 1 − ε_k]` on day `k`.
A perturbation of `Q` on **all** sentences, not an overlay.
Source: [[bli-program]] §3.2(d); mandate T3
Kind: D
Fidelity: exact -/
noncomputable def clamp (Q : History) : History :=
  fun k ψ => Max.max (Min.min (Q k ψ) (1 - (epsK k : ℝ))) (epsK k : ℝ)

/-- **Constraint 1, clamped variant** (`E1c`), for `bli-assemble`: on day-`n` small sentences
`P` is the clamp of `Q`. Mirrors `Cleanroom.Bli.BliFound.E1x`.
Source: [[bli-program]] §3.2(d); mandate § Definitions
Kind: D
Fidelity: exact -/
def E1c (Q P : History) : Prop := ∀ n φ, φ ∈ smallSet n → P n φ = clamp Q n φ

end Cleanroom.Bli.BliTransfer.AttemptB
