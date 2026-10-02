import Cleanroom.Bli.BliTransfer.AttemptB.Defs

/-!
# `bli-transfer` · attempt B · Splice: the rewrite and its laws (T1.1)

`EF.spliceOn expr` replaces every price leaf `price ψ k` by the administrative binding
`letE (price ψ k) e` when `expr k ψ = some e`, and leaves it alone when `none`, recursing
through the other constructors (model: FAF's `EF.freezeOn`,
`Framework/Emission/FreezeTransducer.lean`). The dead original leaf is kept exactly as FAF's
freeze keeps it — parser transparency and rank preservation for arbitrary clocked programs
(Known issue 8); a closed body makes the shift harmless.

The laws are stated for an arbitrary `expr : ℕ → Sentence → Option EF` with the leaf semantics
as a hypothesis (`spliceOn_denoteWith_of_leaf`: leaf-wise agreement lifts to every feature —
the "leaf" half of the program's `denote_eq_of_agree_on_leaves`), and then instantiated for an
`ExprMap` (`ExprMap.spliceOn_denoteWith`: the spliced feature against `Q` denotes what the
original denotes against the overlay). T3's clamp reuses the general form with a *non-closed*
body (`clampE k` reads `var 0`), which is why the general form is the one of record.

Sources: [[bli-program]] §3.1 (proof sketch, step "rewrite"); mandate T1.1.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

namespace EF

/-- The rewritten leaf: `letE (price φ k) e` when `expr k φ = some e`, else the leaf itself.
Source: mandate T1.1
Kind: D
Fidelity: exact -/
def spliceLeaf (expr : ℕ → Sentence → Option LogicalInduction.EF) (k : ℕ) (φ : Sentence) :
    LogicalInduction.EF :=
  match expr k φ with
  | some e => .letE (.price φ k) e
  | none => .price φ k

/-- The rewritten leaf where the map fires.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceLeaf_some {expr : ℕ → Sentence → Option LogicalInduction.EF} {k : ℕ}
    {φ : Sentence} {e : LogicalInduction.EF} (h : expr k φ = some e) :
    spliceLeaf expr k φ = .letE (.price φ k) e := by
  simp [spliceLeaf, h]

/-- The rewritten leaf where the map is silent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceLeaf_none {expr : ℕ → Sentence → Option LogicalInduction.EF} {k : ℕ}
    {φ : Sentence} (h : expr k φ = none) : spliceLeaf expr k φ = .price φ k := by
  simp [spliceLeaf, h]

/-- **The splice.** Replace every price leaf by its `spliceLeaf`; fix `const`/`var`; recurse
through `add`/`mul`/`max`/`safeRecip`/`letE`. Model: `EF.freezeOn`.
Source: [[bli-program]] §3.1; mandate T1.1
Kind: D
Fidelity: exact -/
def spliceOn (expr : ℕ → Sentence → Option LogicalInduction.EF) :
    LogicalInduction.EF → LogicalInduction.EF
  | .price φ k => spliceLeaf expr k φ
  | .const q => .const q
  | .add a b => .add (spliceOn expr a) (spliceOn expr b)
  | .mul a b => .mul (spliceOn expr a) (spliceOn expr b)
  | .max a b => .max (spliceOn expr a) (spliceOn expr b)
  | .safeRecip a => .safeRecip (spliceOn expr a)
  | .var i => .var i
  | .letE x b => .letE (spliceOn expr x) (spliceOn expr b)

variable {expr : ℕ → Sentence → Option LogicalInduction.EF}

/-- `spliceOn` at a price leaf.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_price (φ : Sentence) (k : ℕ) :
    spliceOn expr (.price φ k) = spliceLeaf expr k φ := rfl
/-- `spliceOn` at a constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_const (q : ℚ) : spliceOn expr (.const q) = .const q := rfl
/-- `spliceOn` at `add`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_add (a b : LogicalInduction.EF) :
    spliceOn expr (.add a b) = .add (spliceOn expr a) (spliceOn expr b) := rfl
/-- `spliceOn` at `mul`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_mul (a b : LogicalInduction.EF) :
    spliceOn expr (.mul a b) = .mul (spliceOn expr a) (spliceOn expr b) := rfl
/-- `spliceOn` at `max`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_max (a b : LogicalInduction.EF) :
    spliceOn expr (.max a b) = .max (spliceOn expr a) (spliceOn expr b) := rfl
/-- `spliceOn` at `safeRecip`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_safeRecip (a : LogicalInduction.EF) :
    spliceOn expr (.safeRecip a) = .safeRecip (spliceOn expr a) := rfl
/-- `spliceOn` at a variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_var (i : ℕ) : spliceOn expr (.var i) = .var i := rfl
/-- `spliceOn` at `letE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_letE (x b : LogicalInduction.EF) :
    spliceOn expr (.letE x b) = .letE (spliceOn expr x) (spliceOn expr b) := rfl

/-- A price-free feature is untouched by the splice.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceOn_of_priceFree : ∀ e : LogicalInduction.EF, e.priceFree → spliceOn expr e = e := by
  intro e
  induction e with
  | price φ n => intro h; exact absurd h not_false
  | const q => intro _; rfl
  | add a b iha ihb => intro h; simp [iha h.1, ihb h.2]
  | mul a b iha ihb => intro h; simp [iha h.1, ihb h.2]
  | max a b iha ihb => intro h; simp [iha h.1, ihb h.2]
  | safeRecip a iha => intro h; simp [iha h]
  | var i => intro _; rfl
  | letE x b ihx ihb => intro h; simp [ihx h.1, ihb h.2]

/-- **Rank law.** When every body has rank `≤` its day, the splice preserves rank exactly (the
dead original leaf keeps the day; the body adds nothing above it).
Source: mandate T1.1 (`spliceOn_rank_le`)
Kind: L
Fidelity: stronger: equality -/
lemma spliceOn_rank (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) :
    ∀ e : LogicalInduction.EF, (spliceOn expr e).rank = e.rank := by
  intro e
  induction e with
  | price φ n =>
      simp only [spliceOn_price, LogicalInduction.EF.rank_price]
      cases h : expr n φ with
      | none => simp [h]
      | some e' =>
          simp only [spliceLeaf_some h, LogicalInduction.EF.rank_letE,
            LogicalInduction.EF.rank_price]
          exact Nat.max_eq_left (hr n φ e' h)
  | const q => rfl
  | add a b iha ihb => simp [iha, ihb]
  | mul a b iha ihb => simp [iha, ihb]
  | max a b iha ihb => simp [iha, ihb]
  | safeRecip a iha => simp [iha]
  | var i => rfl
  | letE x b ihx ihb => simp [ihx, ihb]

/-- The rank law in the mandate's `≤` form.
Source: mandate T1.1 (`spliceOn_rank_le`)
Kind: L
Fidelity: exact -/
lemma spliceOn_rank_le (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    (e : LogicalInduction.EF) : (spliceOn expr e).rank ≤ e.rank :=
  (spliceOn_rank hr e).le

/-- **Size law.** With every body of cost `≤ B`, the splice is at most `(B + 2)` times larger.
Source: mandate T1.1 (`spliceOn_cost_le`)
Kind: L
Fidelity: exact -/
lemma spliceOn_cost_le {B : ℕ} (hB : ∀ k ψ e, expr k ψ = some e → e.cost ≤ B) :
    ∀ e : LogicalInduction.EF, (spliceOn expr e).cost ≤ (B + 2) * e.cost := by
  intro e
  induction e with
  | price φ n =>
      simp only [spliceOn_price]
      cases h : expr n φ with
      | none => simp [h, LogicalInduction.EF.cost]
      | some e' =>
          simp only [spliceLeaf_some h, LogicalInduction.EF.cost]
          have := hB n φ e' h
          omega
  | const q => simp [LogicalInduction.EF.cost]
  | add a b iha ihb => simp only [spliceOn_add, LogicalInduction.EF.cost]; nlinarith
  | mul a b iha ihb => simp only [spliceOn_mul, LogicalInduction.EF.cost]; nlinarith
  | max a b iha ihb => simp only [spliceOn_max, LogicalInduction.EF.cost]; nlinarith
  | safeRecip a iha => simp only [spliceOn_safeRecip, LogicalInduction.EF.cost]; nlinarith
  | var i => simp [LogicalInduction.EF.cost]
  | letE x b ihx ihb => simp only [spliceOn_letE, LogicalInduction.EF.cost]; nlinarith

/-- **Leaf-wise agreement lifts to every feature** (the "leaf" half of the program's
`denote_eq_of_agree_on_leaves`): if every rewritten leaf against `Q` denotes the `P`-price of
the original leaf, in every environment, then the spliced feature against `Q` denotes the
original against `P`, in every environment.
Source: [[bli-program]] §3.1; mandate T1.1 (`spliceOn_denoteWith`, general form)
Kind: P
Fidelity: exact -/
lemma spliceOn_denoteWith_of_leaf {Q P : History}
    (hleaf : ∀ k φ (ρ : List ℝ), (spliceLeaf expr k φ).denoteWith ρ Q = P k φ) :
    ∀ (e : LogicalInduction.EF) (ρ : List ℝ),
      (spliceOn expr e).denoteWith ρ Q = e.denoteWith ρ P := by
  intro e
  induction e with
  | price φ n => intro ρ; simpa using hleaf n φ ρ
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [iha ρ]
  | var i => intro ρ; rfl
  | letE x b ihx ihb =>
      intro ρ
      simp only [spliceOn_letE, LogicalInduction.EF.denoteWith_letE]
      rw [ihx ρ, ihb]

/-- **Two markets agreeing on a feature's price queries give it the same denotation.**
Source: [[bli-program]] §3.1 (`denote_eq_of_agree_on_leaves`); mandate T2
Kind: P
Fidelity: exact -/
lemma denoteWith_eq_of_leaves_agree {P Q : History} :
    ∀ (e : LogicalInduction.EF), (∀ q ∈ e.priceQueries, P q.1 q.2 = Q q.1 q.2) →
      ∀ ρ : List ℝ, e.denoteWith ρ P = e.denoteWith ρ Q := by
  intro e
  induction e with
  | price φ n => intro h ρ; simpa using h (n, φ) (by simp [LogicalInduction.EF.priceQueries])
  | const q => intro _ ρ; rfl
  | add a b iha ihb =>
      intro h ρ
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [iha (fun q hq => h q (Or.inl hq)) ρ, ihb (fun q hq => h q (Or.inr hq)) ρ]
  | mul a b iha ihb =>
      intro h ρ
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [iha (fun q hq => h q (Or.inl hq)) ρ, ihb (fun q hq => h q (Or.inr hq)) ρ]
  | max a b iha ihb =>
      intro h ρ
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp [iha (fun q hq => h q (Or.inl hq)) ρ, ihb (fun q hq => h q (Or.inr hq)) ρ]
  | safeRecip a iha =>
      intro h ρ
      simp only [LogicalInduction.EF.priceQueries] at h
      simp [iha h ρ]
  | var i => intro _ ρ; rfl
  | letE x b ihx ihb =>
      intro h ρ
      simp only [LogicalInduction.EF.priceQueries, List.mem_append] at h
      simp only [LogicalInduction.EF.denoteWith_letE]
      rw [ihx (fun q hq => h q (Or.inl hq)) ρ, ihb (fun q hq => h q (Or.inr hq))]

end EF

/-! ## The expression-map instance -/

namespace ExprMap

variable {Q : History} {ov : ℕ → Sentence → ℚ}

/-- **The rewritten leaf reads the overlay's price.** Fired: the closed body ignores the
administrative binding and denotes the overlay (`fires`). Silent: the leaf reads `Q`, which is
the overlay there (`silent`).
Source: [[bli-program]] §3.1; mandate T1.1
Kind: C
Fidelity: exact -/
lemma spliceLeaf_denoteWith (E : ExprMap Q ov) (k : ℕ) (φ : Sentence) (ρ : List ℝ) :
    (EF.spliceLeaf E.expr k φ).denoteWith ρ Q = overlay Q ov k φ := by
  cases h : E.expr k φ with
  | none =>
      simp only [EF.spliceLeaf_none h, LogicalInduction.EF.denoteWith_price]
      exact (E.overlay_eq_of_silent h).symm
  | some e =>
      simp only [EF.spliceLeaf_some h, LogicalInduction.EF.denoteWith_letE]
      rw [(E.closed k φ e h).denoteWith_eq_denote]
      exact E.fires k φ e h

/-- **Exact denotational transport** (the mandate's `spliceOn_denoteWith`): the spliced
feature against `Q` denotes the original against `overlay Q ov`, in every environment.
Source: [[bli-program]] §3.1; mandate T1.1
Kind: C
Fidelity: exact -/
lemma spliceOn_denoteWith (E : ExprMap Q ov) (e : LogicalInduction.EF) (ρ : List ℝ) :
    (EF.spliceOn E.expr e).denoteWith ρ Q = e.denoteWith ρ (overlay Q ov) :=
  EF.spliceOn_denoteWith_of_leaf (fun k φ ρ => E.spliceLeaf_denoteWith k φ ρ) e ρ

/-- Closed-environment form of `spliceOn_denoteWith`.
Source: mandate T1.1
Kind: L
Fidelity: exact -/
lemma spliceOn_denote (E : ExprMap Q ov) (e : LogicalInduction.EF) :
    (EF.spliceOn E.expr e).denote Q = e.denote (overlay Q ov) :=
  E.spliceOn_denoteWith e []

end ExprMap

/-! ## Strategies and traders -/

namespace Strategy

/-- **Splice a strategy**, coefficient-wise; the traded sentences are unchanged. The rank
certificate is transported by `EF.spliceOn_rank_le`, which needs every body's rank `≤` its
day (`hr`; for an `ExprMap` this is `ExprMap.rank_le`).
Source: mandate T1.1
Kind: D
Fidelity: exact -/
def spliceOn (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) {n : ℕ} (T : LogicalInduction.Strategy n) :
    LogicalInduction.Strategy n where
  trades := T.trades.map fun p => (EF.spliceOn expr p.1, p.2)
  rank_le := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (EF.spliceOn_rank_le hr q.1).trans (T.rank_le q hq)

/-- The trade list of a spliced strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_trades (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) {n : ℕ} (T : LogicalInduction.Strategy n) :
    (spliceOn expr hr T).trades = T.trades.map fun p => (EF.spliceOn expr p.1, p.2) := rfl

/-- **Exact value transport at strategy level.** Under leaf-wise agreement (the coefficients
transport exactly) and settlement agreement on every traded sentence (`P n p.2 = Q n p.2`),
the spliced strategy's value against `Q` is the original's against `P`. This is what FAF's
`Strategy.freezeOn_value` cannot have in general ("the settlement term is the obstruction"):
the bridge lemma supplies the settlement agreement from some day on.
Source: [[bli-program]] §3.1; mandate T1.2(a)
Kind: C
Fidelity: exact -/
lemma spliceOn_value {expr : ℕ → Sentence → Option LogicalInduction.EF}
    {hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k} {Q P : History}
    (hleaf : ∀ k φ (ρ : List ℝ), (EF.spliceLeaf expr k φ).denoteWith ρ Q = P k φ)
    {n : ℕ} (T : LogicalInduction.Strategy n) (w : Sentence → ℝ)
    (hsettle : ∀ p ∈ T.trades, P n p.2 = Q n p.2) :
    (spliceOn expr hr T).value Q w = T.value P w := by
  simp only [LogicalInduction.Strategy.value, spliceOn_trades, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, LogicalInduction.EF.denote]
  rw [EF.spliceOn_denoteWith_of_leaf hleaf p.1 [], hsettle p hp]

/-- **Magnitude transport.** The spliced strategy's magnitude against `Q` is the original's
against `P` (coefficients transport exactly; magnitude has no settlement term).
Source: mandate T1.2(b)
Kind: L
Fidelity: exact -/
lemma spliceOn_magnitude {expr : ℕ → Sentence → Option LogicalInduction.EF}
    {hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k} {Q P : History}
    (hleaf : ∀ k φ (ρ : List ℝ), (EF.spliceLeaf expr k φ).denoteWith ρ Q = P k φ)
    {n : ℕ} (T : LogicalInduction.Strategy n) :
    (spliceOn expr hr T).magnitude Q = T.magnitude P := by
  simp only [LogicalInduction.Strategy.magnitude, spliceOn_trades, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, LogicalInduction.EF.denote]
  rw [EF.spliceOn_denoteWith_of_leaf hleaf p.1 []]

end Strategy

namespace Trader

/-- **Splice a trader**, day-wise.
Source: mandate T1.1
Kind: D
Fidelity: exact -/
def spliceOn (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (Tr : LogicalInduction.Trader) :
    LogicalInduction.Trader where
  strat n := Strategy.spliceOn expr hr (Tr.strat n)

/-- The day-`n` strategy of a spliced trader.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma spliceOn_strat (expr : ℕ → Sentence → Option LogicalInduction.EF)
    (hr : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (Tr : LogicalInduction.Trader) (n : ℕ) :
    (spliceOn expr hr Tr).strat n = Strategy.spliceOn expr hr (Tr.strat n) := rfl

end Trader

/-- The mandate's `Tr.spliceOn E.expr`: the trader spliced along an expression map.
Source: mandate T1.1
Kind: D
Fidelity: exact -/
def ExprMap.spliceTrader {Q : History} {ov : ℕ → Sentence → ℚ} (E : ExprMap Q ov)
    (Tr : LogicalInduction.Trader) : LogicalInduction.Trader :=
  Trader.spliceOn E.expr E.rank_le Tr

end Cleanroom.Bli.BliTransfer.AttemptB
