import Cleanroom.Li.LiSpliceCondition.Defs

/-!
# `li-splice-condition` · Translate: the translated trader over FAF's `Trader` (T3.3)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 4 of the layout.
E7's proof rewrites a trader `T` against the perturbed market (`reprice`, `zeroOut`) into a
trader `T̃` against the original market `P`:

* **Features.** `EF.repriceOn ψ Φ r` replaces every price leaf `price (φ ⋏ ψ) k` (`φ ∈ Φ`) by
  `const (r φ k) * price ψ k`; `EF.zeroOn ψ Φ N` replaces every leaf `price ψ k`, `price (φ ⋏ ψ) k`
  with `k ≥ N` by `const 0`. Both are structural recursions on `EF` in the shape of FAF's
  `EF.conditionPrices` and li-projection's `EF.projectOn`, with exact denotation lemmas
  (`repriceOn_denote`: the rewritten feature at `P` *is* the feature at `reprice P ψ Φ r`; likewise
  `zeroOn_denote`) and rank preservation.
* **Legs.** `repriceLeg` sends a leg `(e, φ ⋏ ψ)` to `(const (r φ n) * e', ψ)` and every other leg
  to `(e', χ)`; `zeroLeg` (on days `≥ N`) sends a leg on `ψ` or `φ ⋏ ψ` to the zero leg
  `(const 0, χ)` and every other to `(e', χ)`. A zero-coefficient leg stands in for a dropped one so
  that the two trade lists stay aligned (value and magnitude are unchanged by it).
* **Net worth.** `repriceTranslate_netWorth_eq_of_refuted` / `zeroTranslate_netWorth_eq_of_refuted`:
  in every world refuting `ψ`, the translated trader's net worth against `P` equals the original's
  against the perturbed market, every day. `repriceTranslate_netWorth_sub_le` /
  `zeroTranslate_netWorth_sub_le`: in general the difference is bounded by the **explicit finite
  sum** `Σ_{m ≤ n} Σ_{re-priced legs} |e(ℙ^r)| · (1 + r φ m)` (resp. `Σ |e(ℙ⁰)|` over the dropped
  legs), not an existential constant. The source checked these on 200 random traders; here they are
  theorems over FAF's `Trader.netWorth`. Hypotheses (a).

The efficiency certificate of the translated traders is **not** here: it is the one OPEN
`Complexity.FP` fact `translateStreamRewriter` of `Open.lean` (a frame pass with a membership test
on the sentence block plus a leaf rewrite; li-projection F1's kind of obligation), consumed by
`Transfer.lean`.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional

/-! ## List plumbing -/

/-- A difference of mapped sums is the sum of the differences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- The absolute value of a mapped sum is at most the sum of the absolute values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma list_abs_sum_le {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map fun x => |f x|).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact le_trans (abs_add_le _ _) (by linarith)

/-- Pointwise domination of mapped sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      have := h a (List.mem_cons_self ..)
      have := ih fun x hx => h x (List.mem_cons_of_mem a hx)
      linarith

/-! ## Feature rewrites -/

/-- **The re-pricing feature rewrite**: every price leaf `price (φ ⋏ ψ) k` with `φ ∈ Φ` becomes
`const (r φ k) * price ψ k`; every other constructor is homomorphic.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii), "replace every price leaf `ℙ^r_k(φ∧ψ)` … by the feature `r(φ,k)·ℙ_k(ψ)`"); FAF `EF.conditionPrices` (the shape)
Kind: D
Fidelity: exact -/
def EF.repriceOn (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) : EF → EF
  | .price χ k => match condLeg ψ Φ χ with
      | some φ => .mul (.const (r φ k)) (.price ψ k)
      | none => .price χ k
  | .const c => .const c
  | .add a b => .add (EF.repriceOn ψ Φ r a) (EF.repriceOn ψ Φ r b)
  | .mul a b => .mul (EF.repriceOn ψ Φ r a) (EF.repriceOn ψ Φ r b)
  | .max a b => .max (EF.repriceOn ψ Φ r a) (EF.repriceOn ψ Φ r b)
  | .safeRecip a => .safeRecip (EF.repriceOn ψ Φ r a)
  | .var i => .var i
  | .letE x body => .letE (EF.repriceOn ψ Φ r x) (EF.repriceOn ψ Φ r body)

/-- The re-pricing rewrite preserves rank.
Source: none: infrastructure (mandate T3.3, `_rank_le`)
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.repriceOn_rank (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (e : EF) : (EF.repriceOn ψ Φ r e).rank = e.rank := by
  induction e with
  | price χ k => cases h : condLeg ψ Φ χ <;> simp [EF.repriceOn, h]
  | const c => simp [EF.repriceOn]
  | add a b iha ihb => simp [EF.repriceOn, iha, ihb]
  | mul a b iha ihb => simp [EF.repriceOn, iha, ihb]
  | max a b iha ihb => simp [EF.repriceOn, iha, ihb]
  | safeRecip a iha => simp [EF.repriceOn, iha]
  | var i => simp [EF.repriceOn]
  | letE x body ihx ihb => simp [EF.repriceOn, ihx, ihb]

/-- The re-pricing rewrite at `P` denotes the original at `reprice P ψ Φ r`, in every environment.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii))
Kind: P
Fidelity: exact -/
lemma EF.repriceOn_denoteWith (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (e : EF) :
    ∀ ρ : List ℝ, (EF.repriceOn ψ Φ r e).denoteWith ρ P = e.denoteWith ρ (reprice P ψ Φ r) := by
  induction e with
  | price χ k =>
      intro ρ
      cases h : condLeg ψ Φ χ
      · simp [EF.repriceOn, h, reprice]
      · simp [EF.repriceOn, h, reprice]
  | const c => intro ρ; simp [EF.repriceOn]
  | add a b iha ihb => intro ρ; simp [EF.repriceOn, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [EF.repriceOn, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [EF.repriceOn, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [EF.repriceOn, iha ρ]
  | var i => intro ρ; simp [EF.repriceOn]
  | letE x body ihx ihb =>
      intro ρ
      simp only [EF.repriceOn, EF.denoteWith_letE, ihx ρ]
      exact ihb _

/-- `(EF.repriceOn ψ Φ r e).denote P = e.denote (reprice P ψ Φ r)`.
Source: [[corr-legit-neg-inventory]] 061
Kind: P
Fidelity: exact -/
lemma EF.repriceOn_denote (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (e : EF) :
    (EF.repriceOn ψ Φ r e).denote P = e.denote (reprice P ψ Φ r) :=
  EF.repriceOn_denoteWith ψ Φ r P e []

/-- **The zeroing feature rewrite**: every price leaf `price χ k` with `k ≥ N` and `χ = ψ` or
`χ = φ ⋏ ψ` (`φ ∈ Φ`) becomes `const 0`; every other constructor is homomorphic.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i), "replaces the leaves `ℙ⁰_k(ψ)`, `ℙ⁰_k(φ∧ψ)` (`k ≥ N`) by the constant `0`")
Kind: D
Fidelity: exact -/
def EF.zeroOn (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) : EF → EF
  | .price χ k => if N ≤ k ∧ (χ = ψ ∨ (condLeg ψ Φ χ).isSome) then .const 0 else .price χ k
  | .const c => .const c
  | .add a b => .add (EF.zeroOn ψ Φ N a) (EF.zeroOn ψ Φ N b)
  | .mul a b => .mul (EF.zeroOn ψ Φ N a) (EF.zeroOn ψ Φ N b)
  | .max a b => .max (EF.zeroOn ψ Φ N a) (EF.zeroOn ψ Φ N b)
  | .safeRecip a => .safeRecip (EF.zeroOn ψ Φ N a)
  | .var i => .var i
  | .letE x body => .letE (EF.zeroOn ψ Φ N x) (EF.zeroOn ψ Φ N body)

/-- The zeroing rewrite does not raise the rank.
Source: none: infrastructure (mandate T3.3, `_rank_le`)
Kind: L
Fidelity: n/a -/
lemma EF.zeroOn_rank_le (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (e : EF) :
    (EF.zeroOn ψ Φ N e).rank ≤ e.rank := by
  induction e with
  | price χ k => unfold EF.zeroOn; split_ifs <;> simp
  | const c => simp [EF.zeroOn]
  | add a b iha ihb => simp only [EF.zeroOn, EF.rank_add]; exact max_le_max iha ihb
  | mul a b iha ihb => simp only [EF.zeroOn, EF.rank_mul]; exact max_le_max iha ihb
  | max a b iha ihb => simp only [EF.zeroOn, EF.rank_max]; exact max_le_max iha ihb
  | safeRecip a iha => simpa [EF.zeroOn] using iha
  | var i => simp [EF.zeroOn]
  | letE x body ihx ihb => simp only [EF.zeroOn, EF.rank_letE]; exact max_le_max ihx ihb

/-- The zeroing rewrite at `P` denotes the original at `zeroOut P ψ Φ N`, in every environment.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i))
Kind: P
Fidelity: exact -/
lemma EF.zeroOn_denoteWith (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (e : EF) :
    ∀ ρ : List ℝ, (EF.zeroOn ψ Φ N e).denoteWith ρ P = e.denoteWith ρ (zeroOut P ψ Φ N) := by
  induction e with
  | price χ k =>
      intro ρ
      by_cases h : N ≤ k ∧ (χ = ψ ∨ (condLeg ψ Φ χ).isSome)
      · simp [EF.zeroOn, h, zeroOut]
      · simp [EF.zeroOn, h, zeroOut]
  | const c => intro ρ; simp [EF.zeroOn]
  | add a b iha ihb => intro ρ; simp [EF.zeroOn, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [EF.zeroOn, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [EF.zeroOn, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [EF.zeroOn, iha ρ]
  | var i => intro ρ; simp [EF.zeroOn]
  | letE x body ihx ihb =>
      intro ρ
      simp only [EF.zeroOn, EF.denoteWith_letE, ihx ρ]
      exact ihb _

/-- `(EF.zeroOn ψ Φ N e).denote P = e.denote (zeroOut P ψ Φ N)`.
Source: [[corr-legit-neg-inventory]] 060
Kind: P
Fidelity: exact -/
lemma EF.zeroOn_denote (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (e : EF) :
    (EF.zeroOn ψ Φ N e).denote P = e.denote (zeroOut P ψ Φ N) :=
  EF.zeroOn_denoteWith ψ Φ N P e []

/-! ## The translated strategies and traders -/

/-- The re-priced leg: `(e, φ ⋏ ψ)` with `φ ∈ Φ` becomes `(const (r φ n) * e', ψ)`, any other
`(e, χ)` becomes `(e', χ)`, where `e' := EF.repriceOn ψ Φ r e`.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii), "delete `T`'s `φ∧ψ` leg (quantity `q_m`), and add `r(φ,m)·q_m` to its `ψ` leg")
Kind: D
Fidelity: exact (the re-priced legs are moved to `ψ` one by one rather than merged into one `ψ` leg; `Strategy.value` is additive, so the value is the same) -/
def repriceLeg (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ) (n : ℕ)
    (p : EF × Sentence) : EF × Sentence :=
  match condLeg ψ Φ p.2 with
  | some φ => (.mul (.const (r φ n)) (EF.repriceOn ψ Φ r p.1), ψ)
  | none => (EF.repriceOn ψ Φ r p.1, p.2)

/-- The re-priced day-`n` strategy.
Source: [[corr-legit-neg-inventory]] 061
Kind: D
Fidelity: exact -/
def Strategy.repriceTranslate {n : ℕ} (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (T : Strategy n) : Strategy n where
  trades := T.trades.map (repriceLeg ψ Φ r n)
  rank_le := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have h := T.rank_le p hp
    unfold repriceLeg
    cases condLeg ψ Φ p.2
    · simpa [EF.repriceOn_rank] using h
    · simpa [EF.repriceOn_rank] using h

/-- The re-priced trader `T̃` of E7 (ii).
Source: [[corr-legit-neg-inventory]] 061
Kind: D
Fidelity: exact -/
def Trader.repriceTranslate (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (T : Trader) : Trader where
  strat n := Strategy.repriceTranslate ψ Φ r (T.strat n)

/-- Whether a leg on sentence `χ` is dropped on day `n` by the zeroing translation.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def zeroDropped (ψ : Sentence) (Φ : Finset Sentence) (N n : ℕ) (χ : Sentence) : Prop :=
  N ≤ n ∧ (χ = ψ ∨ (condLeg ψ Φ χ).isSome)

instance (ψ : Sentence) (Φ : Finset Sentence) (N n : ℕ) (χ : Sentence) :
    Decidable (zeroDropped ψ Φ N n χ) := by unfold zeroDropped; infer_instance

/-- The zeroed leg: on days `≥ N` a leg on `ψ` or `φ ⋏ ψ` becomes the zero leg `(const 0, χ)`; any
other leg `(e, χ)` becomes `(EF.zeroOn ψ Φ N e, χ)`.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i), "`T̃` … drops the `ψ` and `φ∧ψ` legs")
Kind: D
Fidelity: exact (a dropped leg is kept with coefficient `0`, which has the same value and magnitude as dropping it) -/
def zeroLeg (ψ : Sentence) (Φ : Finset Sentence) (N n : ℕ) (p : EF × Sentence) : EF × Sentence :=
  if zeroDropped ψ Φ N n p.2 then (.const 0, p.2) else (EF.zeroOn ψ Φ N p.1, p.2)

/-- The zeroed day-`n` strategy.
Source: [[corr-legit-neg-inventory]] 060
Kind: D
Fidelity: exact -/
def Strategy.zeroTranslate {n : ℕ} (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ)
    (T : Strategy n) : Strategy n where
  trades := T.trades.map (zeroLeg ψ Φ N n)
  rank_le := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    have h := T.rank_le p hp
    unfold zeroLeg
    split_ifs
    · simp
    · exact le_trans (EF.zeroOn_rank_le ψ Φ N p.1) h

/-- The zeroed trader `T̃` of E7 (i).
Source: [[corr-legit-neg-inventory]] 060
Kind: D
Fidelity: exact -/
def Trader.zeroTranslate (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (T : Trader) : Trader where
  strat n := Strategy.zeroTranslate ψ Φ N (T.strat n)

/-! ## Per-leg discrepancies -/

/-- The per-leg discrepancy of the re-pricing translation on day `n` under payouts `w`:
`e(ℙ^r) · (w (φ ⋏ ψ) − r φ n · w ψ)` on a re-priced leg, `0` elsewhere.
Source: [[corr-legit-neg-inventory]] 061 (E7's display `Σ_{m≤n} q_m (W(φ∧ψ) − r(φ,m) W(ψ))`)
Kind: D
Fidelity: exact -/
noncomputable def repriceLegDiff (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (n : ℕ) (w : Sentence → ℝ) (p : EF × Sentence) : ℝ :=
  match condLeg ψ Φ p.2 with
  | some φ => p.1.denote (reprice P ψ Φ r) * (w p.2 - (r φ n : ℝ) * w ψ)
  | none => 0

/-- The original value against `ℙ^r` minus the translated value against `ℙ` is the sum of the
per-leg discrepancies.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii), "the cash legs agree exactly")
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma repriceTranslate_value_sub {n : ℕ} (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (P : History) (w : Sentence → ℝ) (T : Strategy n) :
    T.value (reprice P ψ Φ r) w - (Strategy.repriceTranslate ψ Φ r T).value P w =
      (T.trades.map (repriceLegDiff ψ Φ r P n w)).sum := by
  simp only [Strategy.value, Strategy.repriceTranslate, List.map_map]
  rw [list_sum_map_sub]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp]
  unfold repriceLeg repriceLegDiff
  cases h : condLeg ψ Φ p.2 with
  | none =>
      simp only [EF.repriceOn_denote, reprice_of_none P ψ Φ r n h]
      ring
  | some φ =>
      obtain ⟨hp2, hφ⟩ := condLeg_eq_some_iff.mp h
      simp only [EF.denote_mul, EF.denote_const, Pi.mul_apply, EF.repriceOn_denote, hp2,
        reprice_and P ψ Φ r n hφ]
      ring

/-- The per-leg discrepancy vanishes in a world refuting `ψ`.
Source: [[corr-legit-neg-inventory]] 061 ("for `n ≥ N` every `W ∈ PC(D_n)` has `W(ψ) = W(φ∧ψ) = 0`")
Kind: L
Fidelity: exact -/
lemma repriceLegDiff_eq_zero_of_refuted (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (P : History) (n : ℕ) (v : PCWorld) (hv : ¬ v.Holds ψ)
    (p : EF × Sentence) : repriceLegDiff ψ Φ r P n v.payout p = 0 := by
  unfold repriceLegDiff
  cases h : condLeg ψ Φ p.2 with
  | none => rfl
  | some φ =>
      obtain ⟨hp2, -⟩ := condLeg_eq_some_iff.mp h
      have h1 : v.payout ψ = 0 := by simp [PCWorld.payout, hv]
      have h2 : v.payout p.2 = 0 := by
        rw [hp2]
        simp [PCWorld.payout, PCWorld.holds_and, hv]
      rw [h1, h2]
      ring

/-- The per-leg bound of the re-pricing translation: `|e(ℙ^r)| · (1 + r φ n)` on a re-priced leg,
`0` elsewhere.
Source: [[corr-legit-neg-inventory]] 061 ("bounded by `Σ_{m<N} |q_m| (1 + r(φ,m))`")
Kind: D
Fidelity: exact -/
noncomputable def repriceLegBound (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (n : ℕ) (p : EF × Sentence) : ℝ :=
  match condLeg ψ Φ p.2 with
  | some φ => |p.1.denote (reprice P ψ Φ r)| * (1 + (r φ n : ℝ))
  | none => 0

/-- The per-leg discrepancy is bounded by the per-leg bound, for `[0,1]` payouts and `r ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
lemma abs_repriceLegDiff_le (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (n : ℕ) (w : Sentence → ℝ) (hw : ∀ χ, 0 ≤ w χ ∧ w χ ≤ 1)
    (hr : ∀ φ ∈ Φ, 0 ≤ r φ n) (p : EF × Sentence) :
    |repriceLegDiff ψ Φ r P n w p| ≤ repriceLegBound ψ Φ r P n p := by
  unfold repriceLegDiff repriceLegBound
  cases h : condLeg ψ Φ p.2 with
  | none => simp
  | some φ =>
      obtain ⟨-, hφ⟩ := condLeg_eq_some_iff.mp h
      have hr' : (0 : ℝ) ≤ r φ n := by exact_mod_cast hr φ hφ
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_le]
      have := hw p.2
      have := hw ψ
      constructor <;> nlinarith

/-- The per-leg discrepancy of the zeroing translation on day `n` under payouts `w`:
`e(ℙ⁰) · w χ` on a dropped leg, `0` elsewhere.
Source: [[corr-legit-neg-inventory]] 060
Kind: D
Fidelity: exact -/
noncomputable def zeroLegDiff (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (n : ℕ)
    (w : Sentence → ℝ) (p : EF × Sentence) : ℝ :=
  if zeroDropped ψ Φ N n p.2 then p.1.denote (zeroOut P ψ Φ N) * w p.2 else 0

/-- The original value against `ℙ⁰` minus the translated value against `ℙ` is the sum of the
per-leg discrepancies.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i))
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma zeroTranslate_value_sub {n : ℕ} (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History)
    (w : Sentence → ℝ) (T : Strategy n) :
    T.value (zeroOut P ψ Φ N) w - (Strategy.zeroTranslate ψ Φ N T).value P w =
      (T.trades.map (zeroLegDiff ψ Φ N P n w)).sum := by
  simp only [Strategy.value, Strategy.zeroTranslate, List.map_map]
  rw [list_sum_map_sub]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp]
  unfold zeroLeg zeroLegDiff
  by_cases h : zeroDropped ψ Φ N n p.2
  · rw [if_pos h, if_pos h]
    have hz : zeroOut P ψ Φ N n p.2 = 0 := by
      unfold zeroOut; exact if_pos h
    simp only [EF.denote_const, hz, Rat.cast_zero]
    ring
  · rw [if_neg h, if_neg h]
    have hz : zeroOut P ψ Φ N n p.2 = P n p.2 := by
      unfold zeroOut; exact if_neg h
    simp only [EF.zeroOn_denote, hz]
    ring

/-- The zeroing discrepancy vanishes in a world refuting `ψ`.
Source: [[corr-legit-neg-inventory]] 060 ("those legs are … worth `0` in every `W ∈ PC(D_n)`, `n ≥ N`")
Kind: L
Fidelity: exact -/
lemma zeroLegDiff_eq_zero_of_refuted (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History)
    (n : ℕ) (v : PCWorld) (hv : ¬ v.Holds ψ) (p : EF × Sentence) :
    zeroLegDiff ψ Φ N P n v.payout p = 0 := by
  unfold zeroLegDiff
  split_ifs with h
  · obtain ⟨-, h2⟩ := h
    have : v.payout p.2 = 0 := by
      rcases h2 with h2 | h2
      · rw [h2]; simp [PCWorld.payout, hv]
      · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h2
        obtain ⟨hp2, -⟩ := condLeg_eq_some_iff.mp hφ
        rw [hp2]; simp [PCWorld.payout, PCWorld.holds_and, hv]
    rw [this]; ring
  · rfl

/-- The per-leg bound of the zeroing translation: `|e(ℙ⁰)|` on a dropped leg, `0` elsewhere.
Source: [[corr-legit-neg-inventory]] 060
Kind: D
Fidelity: exact -/
noncomputable def zeroLegBound (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (n : ℕ)
    (p : EF × Sentence) : ℝ :=
  if zeroDropped ψ Φ N n p.2 then |p.1.denote (zeroOut P ψ Φ N)| else 0

/-- The zeroing discrepancy is bounded by the per-leg bound, for `[0,1]` payouts.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
lemma abs_zeroLegDiff_le (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (n : ℕ)
    (w : Sentence → ℝ) (hw : ∀ χ, 0 ≤ w χ ∧ w χ ≤ 1) (p : EF × Sentence) :
    |zeroLegDiff ψ Φ N P n w p| ≤ zeroLegBound ψ Φ N P n p := by
  unfold zeroLegDiff zeroLegBound
  split_ifs
  · rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_le]
    have := hw p.2
    constructor <;> linarith
  · simp

/-! ## T3.3 Net worth: exact on refuted worlds, bounded elsewhere -/

/-- The explicit bound `Σ_{m ≤ n} Σ_{re-priced legs of day m} |e(ℙ^r)| · (1 + r φ m)`.
Source: [[corr-legit-neg-inventory]] 061 (E7, "bounded by `Σ_{m<N} |q_m| (1 + r(φ,m))`")
Kind: D
Fidelity: exact -/
noncomputable def repriceBound (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (P : History) (T : Trader) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ((T.strat m).trades.map (repriceLegBound ψ Φ r P m)).sum

/-- **T3.3 (reprice, exact part).** In every world refuting `ψ`, the re-priced trader's net worth
against `P` equals the original's against `reprice P ψ Φ r`, on every day.
Source: [[corr-legit-neg-2-inventory]] 022, 008 (E7's fixture: "the translated trader's net worth equals the original's in every refuted world"); [[corr-legit-neg-inventory]] 061
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem repriceTranslate_netWorth_eq_of_refuted (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (P : History) (T : Trader) (v : PCWorld) (hv : ¬ v.Holds ψ) (n : ℕ) :
    (Trader.repriceTranslate ψ Φ r T).netWorth P v n = T.netWorth (reprice P ψ Φ r) v n := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := repriceTranslate_value_sub ψ Φ r P v.payout (T.strat m)
  rw [List.map_congr_left (fun p _ => repriceLegDiff_eq_zero_of_refuted ψ Φ r P m v hv p),
    List.map_const', List.sum_replicate, smul_zero] at h
  show (Strategy.repriceTranslate ψ Φ r (T.strat m)).value P v.payout =
    (T.strat m).value (reprice P ψ Φ r) v.payout
  linarith

/-- **T3.3 (reprice, bounded part).** In every world with `{0,1}` payouts and for `r ≥ 0` on `Φ`,
the difference of the two net worths is bounded by the explicit finite sum `repriceBound`.
Source: [[corr-legit-neg-2-inventory]] 022, 008 ("within `Σ|q|(1+r)` elsewhere"); [[corr-legit-neg-inventory]] 061
Kind: P
Fidelity: exact (an explicit finite sum, not an existential constant)
Hyps: (a) -/
theorem repriceTranslate_netWorth_sub_le (ψ : Sentence) (Φ : Finset Sentence)
    (r : Sentence → ℕ → ℚ) (hr : ∀ φ ∈ Φ, ∀ m, 0 ≤ r φ m) (P : History) (T : Trader) (v : PCWorld)
    (n : ℕ) :
    |T.netWorth (reprice P ψ Φ r) v n - (Trader.repriceTranslate ψ Φ r T).netWorth P v n| ≤
      repriceBound ψ Φ r P T n := by
  unfold Trader.netWorth repriceBound
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m _ => ?_)
  rw [show (T.strat m).value (reprice P ψ Φ r) v.payout -
      ((Trader.repriceTranslate ψ Φ r T).strat m).value P v.payout =
      ((T.strat m).trades.map (repriceLegDiff ψ Φ r P m v.payout)).sum from
    repriceTranslate_value_sub ψ Φ r P v.payout (T.strat m)]
  refine le_trans (list_abs_sum_le _ _) (list_sum_map_le _ _ _ fun p _ => ?_)
  exact abs_repriceLegDiff_le ψ Φ r P m v.payout (fun χ => payout_mem_Icc v χ)
    (fun φ hφ => hr φ hφ m) p

/-- The explicit bound `Σ_{m ≤ n} Σ_{dropped legs of day m} |e(ℙ⁰)|`.
Source: [[corr-legit-neg-inventory]] 060
Kind: D
Fidelity: exact -/
noncomputable def zeroBound (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History) (T : Trader)
    (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ((T.strat m).trades.map (zeroLegBound ψ Φ N P m)).sum

/-- **T3.3 (zeroOut, exact part).** In every world refuting `ψ`, the zeroed trader's net worth
against `P` equals the original's against `zeroOut P ψ Φ N`, on every day.
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i), "the net worths agree exactly")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem zeroTranslate_netWorth_eq_of_refuted (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ)
    (P : History) (T : Trader) (v : PCWorld) (hv : ¬ v.Holds ψ) (n : ℕ) :
    (Trader.zeroTranslate ψ Φ N T).netWorth P v n = T.netWorth (zeroOut P ψ Φ N) v n := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := zeroTranslate_value_sub ψ Φ N P v.payout (T.strat m)
  rw [List.map_congr_left (fun p _ => zeroLegDiff_eq_zero_of_refuted ψ Φ N P m v hv p),
    List.map_const', List.sum_replicate, smul_zero] at h
  show (Strategy.zeroTranslate ψ Φ N (T.strat m)).value P v.payout =
    (T.strat m).value (zeroOut P ψ Φ N) v.payout
  linarith

/-- **T3.3 (zeroOut, bounded part).** In every world the difference of the two net worths is
bounded by the explicit finite sum `zeroBound`.
Source: [[corr-legit-neg-inventory]] 060
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem zeroTranslate_netWorth_sub_le (ψ : Sentence) (Φ : Finset Sentence) (N : ℕ) (P : History)
    (T : Trader) (v : PCWorld) (n : ℕ) :
    |T.netWorth (zeroOut P ψ Φ N) v n - (Trader.zeroTranslate ψ Φ N T).netWorth P v n| ≤
      zeroBound ψ Φ N P T n := by
  unfold Trader.netWorth zeroBound
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m _ => ?_)
  rw [show (T.strat m).value (zeroOut P ψ Φ N) v.payout -
      ((Trader.zeroTranslate ψ Φ N T).strat m).value P v.payout =
      ((T.strat m).trades.map (zeroLegDiff ψ Φ N P m v.payout)).sum from
    zeroTranslate_value_sub ψ Φ N P v.payout (T.strat m)]
  refine le_trans (list_abs_sum_le _ _) (list_sum_map_le _ _ _ fun p _ => ?_)
  exact abs_zeroLegDiff_le ψ Φ N P m v.payout (fun χ => payout_mem_Icc v χ) p

/-- **The zeroing translation is exact on every plausible world from stage `N` on, and exact
before `N` on every world**: on days `< N` nothing is dropped, and on days `≥ N` every world
consistent with `DP.D n ⊇ DP.D N` refutes `ψ`. So against the plausible assessments the two
net-worth streams coincide — the bound `C` of `Exploits.of_boundedDifference` is `0` (sharper than
E7's "pre-`N` difference is a fixed finite sum", because the translation here is day-dependent).
Source: [[corr-legit-neg-inventory]] 060 (E7 proof of (i)); mandate T3.4 (the accounting)
Kind: P
Fidelity: stronger: exact on plausible worlds, every day
Hyps: (a) -/
theorem zeroTranslate_netWorth_eq_of_plausible (DP : DeductiveProcess) (ψ : Sentence)
    (Φ : Finset Sentence) (N : ℕ) (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ)
    (P : History) (T : Trader) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (Trader.zeroTranslate ψ Φ N T).netWorth P v n = T.netWorth (zeroOut P ψ Φ N) v n := by
  by_cases hN : N ≤ n
  · exact zeroTranslate_netWorth_eq_of_refuted ψ Φ N P T v
      (href v fun φ hφ => hv φ (DP.mono_le hN hφ)) n
  · unfold Trader.netWorth
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : ¬ N ≤ m := by rw [Finset.mem_range] at hm; omega
    have h := zeroTranslate_value_sub ψ Φ N P v.payout (T.strat m)
    have hzero : ∀ p ∈ (T.strat m).trades, zeroLegDiff ψ Φ N P m v.payout p = 0 := by
      intro p _
      unfold zeroLegDiff
      rw [if_neg (fun h' => hmN h'.1)]
    rw [List.map_congr_left hzero, List.map_const', List.sum_replicate, smul_zero] at h
    show (Strategy.zeroTranslate ψ Φ N (T.strat m)).value P v.payout =
      (T.strat m).value (zeroOut P ψ Φ N) v.payout
    linarith

/-- **The re-pricing translation against plausible worlds**: exact from stage `N` on, and bounded
by `repriceBound … (N − 1)` before (the days `< N` contribute at most their own per-leg bounds; the
days `≥ N` contribute `0` in every plausible world). Stated with the explicit bound at `n = N`
(which dominates every `n < N`'s), so that one constant serves `Exploits.of_boundedDifference`.
Source: [[corr-legit-neg-inventory]] 061 (E7 proof of (ii), the two cases `n ≥ N` / `n < N`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem repriceTranslate_netWorth_sub_le_of_plausible (DP : DeductiveProcess) (ψ : Sentence)
    (Φ : Finset Sentence) (N : ℕ) (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ)
    (r : Sentence → ℕ → ℚ) (hr : ∀ φ ∈ Φ, ∀ m, 0 ≤ r φ m) (P : History) (T : Trader) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    |T.netWorth (reprice P ψ Φ r) v n - (Trader.repriceTranslate ψ Φ r T).netWorth P v n| ≤
      repriceBound ψ Φ r P T N := by
  by_cases hN : N ≤ n
  · rw [repriceTranslate_netWorth_eq_of_refuted ψ Φ r P T v
      (href v fun φ hφ => hv φ (DP.mono_le hN hφ)) n, sub_self, abs_zero]
    unfold repriceBound
    refine Finset.sum_nonneg fun m _ => List.sum_nonneg fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    unfold repriceLegBound
    cases h : condLeg ψ Φ p.2 with
    | none => exact le_rfl
    | some φ =>
        obtain ⟨-, hφ⟩ := condLeg_eq_some_iff.mp h
        have : (0 : ℝ) ≤ r φ m := by exact_mod_cast hr φ hφ m
        positivity
  · refine le_trans (repriceTranslate_netWorth_sub_le ψ Φ r hr P T v n) ?_
    unfold repriceBound
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun m _ _ => List.sum_nonneg fun x hx => ?_
    rw [List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx
    unfold repriceLegBound
    cases h : condLeg ψ Φ p.2 with
    | none => exact le_rfl
    | some φ =>
        obtain ⟨-, hφ⟩ := condLeg_eq_some_iff.mp h
        have : (0 : ℝ) ≤ r φ m := by exact_mod_cast hr φ hφ m
        positivity

/-- **T3.3, the headline in one statement**: for both translations, exactness on worlds refuting
`ψ` and the explicit bounds in general.
Source: [[corr-legit-neg-2-inventory]] 022, 008; [[corr-legit-neg-inventory]] 060–061; mandate T3.3
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem translated_trader_netWorth (ψ : Sentence) (Φ : Finset Sentence) (r : Sentence → ℕ → ℚ)
    (hr : ∀ φ ∈ Φ, ∀ m, 0 ≤ r φ m) (N : ℕ) (P : History) (T : Trader) :
    (∀ (v : PCWorld), ¬ v.Holds ψ → ∀ n,
      (Trader.repriceTranslate ψ Φ r T).netWorth P v n = T.netWorth (reprice P ψ Φ r) v n ∧
      (Trader.zeroTranslate ψ Φ N T).netWorth P v n = T.netWorth (zeroOut P ψ Φ N) v n) ∧
    (∀ (v : PCWorld) (n : ℕ),
      |T.netWorth (reprice P ψ Φ r) v n - (Trader.repriceTranslate ψ Φ r T).netWorth P v n| ≤
        repriceBound ψ Φ r P T n ∧
      |T.netWorth (zeroOut P ψ Φ N) v n - (Trader.zeroTranslate ψ Φ N T).netWorth P v n| ≤
        zeroBound ψ Φ N P T n) :=
  ⟨fun v hv n => ⟨repriceTranslate_netWorth_eq_of_refuted ψ Φ r P T v hv n,
      zeroTranslate_netWorth_eq_of_refuted ψ Φ N P T v hv n⟩,
   fun v n => ⟨repriceTranslate_netWorth_sub_le ψ Φ r hr P T v n,
      zeroTranslate_netWorth_sub_le ψ Φ N P T v n⟩⟩

end Cleanroom.Li.LiSpliceCondition
