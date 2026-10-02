import Cleanroom.Bli.BliTransfer.AttemptA.Defs

/-!
# `bli-transfer` (attempt A) · Splice: the syntactic rewrite and its laws (T1.1)

`EF.spliceOn expr` replaces each price leaf `price ψ k` with `expr k ψ = some e` by the
administrative binding `letE (price ψ k) e`, exactly as FAF's price freeze `EF.freezeOn`
(`Framework/Emission/FreezeTransducer.lean:69`) keeps the dead original leaf: the flat-token
rewrite stays parser-transparent and the feature's rank is preserved for arbitrary clocked
programs (mandate Known issue 8: do not splice `e` in place of the leaf). Leaves with
`expr k ψ = none` are left alone.

The laws are stated once over a **splice specification** `SpliceSpec expr Q P`: every body has at
most `var 0` free, denotes `P k ψ` when `var 0` is bound to `Q k ψ`, and an un-fired leaf has
`Q k ψ = P k ψ`. Two instances: an `ExprMap` (closed bodies, target `overlay Q ov`;
`ExprMap.spliceSpec`) and the clamp (`clampE k` reads the bound price as `var 0`, target
`clamp Q`; `Clamp.lean`). The laws: rank preservation (`EF.spliceOn_rank`, given the bodies' rank
discipline), the size law (`EF.spliceOn_cost_le`), exact denotational transport
(`EF.spliceOn_denoteWith`: the rewritten feature against `Q` denotes what the original denotes
against `P`), the coefficient-wise and day-wise lifts `Strategy.spliceOn` / `Trader.spliceOn`,
and the strategy-value law `Strategy.spliceOn_value` on a day whose traded sentences settle at the
same price on both markets — exactly where FAF's `Strategy.freezeOn_value` cannot have it ("the
settlement term is the obstruction"), and what the bridge lemma supplies from some day on.

Sources: [[bli-program]] §3.1 (proof sketch); mandate T1.1; FAF `FreezeTransducer.lean:69–150`,
`FinitePerturbations.lean:116–180`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The rewrite -/

/-- **The splice**: replace each price leaf that the expression map fires on by the
administrative binding `letE (price ψ k) e`; leave the others. Model: FAF's `EF.freezeOn`.
Source: [[bli-program]] §3.1; mandate T1.1
Kind: D
Fidelity: exact -/
def EF.spliceOn (expr : ℕ → Sentence → Option EF) : EF → EF
  | .price ψ k =>
      match expr k ψ with
      | some e => .letE (.price ψ k) e
      | none => .price ψ k
  | .const q => .const q
  | .add a b => .add (EF.spliceOn expr a) (EF.spliceOn expr b)
  | .mul a b => .mul (EF.spliceOn expr a) (EF.spliceOn expr b)
  | .max a b => .max (EF.spliceOn expr a) (EF.spliceOn expr b)
  | .safeRecip a => .safeRecip (EF.spliceOn expr a)
  | .var i => .var i
  | .letE x b => .letE (EF.spliceOn expr x) (EF.spliceOn expr b)

/-- Defining equation at a fired price leaf.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_price_some (expr : ℕ → Sentence → Option EF) {k : ℕ} {ψ : Sentence}
    {e : EF} (h : expr k ψ = some e) :
    EF.spliceOn expr (.price ψ k) = .letE (.price ψ k) e := by
  simp [EF.spliceOn, h]

/-- Defining equation at an un-fired price leaf.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_price_none (expr : ℕ → Sentence → Option EF) {k : ℕ} {ψ : Sentence}
    (h : expr k ψ = none) : EF.spliceOn expr (.price ψ k) = .price ψ k := by
  simp [EF.spliceOn, h]

/-- Defining equation at a constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_const (expr : ℕ → Sentence → Option EF) (q : ℚ) :
    EF.spliceOn expr (.const q) = .const q := rfl

/-- Defining equation at `add`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_add (expr : ℕ → Sentence → Option EF) (a b : EF) :
    EF.spliceOn expr (.add a b) = .add (EF.spliceOn expr a) (EF.spliceOn expr b) := rfl

/-- Defining equation at `mul`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_mul (expr : ℕ → Sentence → Option EF) (a b : EF) :
    EF.spliceOn expr (.mul a b) = .mul (EF.spliceOn expr a) (EF.spliceOn expr b) := rfl

/-- Defining equation at `max`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_max (expr : ℕ → Sentence → Option EF) (a b : EF) :
    EF.spliceOn expr (.max a b) = .max (EF.spliceOn expr a) (EF.spliceOn expr b) := rfl

/-- Defining equation at `safeRecip`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_safeRecip (expr : ℕ → Sentence → Option EF) (a : EF) :
    EF.spliceOn expr (.safeRecip a) = .safeRecip (EF.spliceOn expr a) := rfl

/-- Defining equation at a variable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_var (expr : ℕ → Sentence → Option EF) (i : ℕ) :
    EF.spliceOn expr (.var i) = .var i := rfl

/-- Defining equation at `letE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.spliceOn_letE (expr : ℕ → Sentence → Option EF) (x b : EF) :
    EF.spliceOn expr (.letE x b) = .letE (EF.spliceOn expr x) (EF.spliceOn expr b) := rfl

/-! ## Rank and size -/

/-- The dead leaf keeps the rank from below: splicing never lowers the rank.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.rank_le_spliceOn (expr : ℕ → Sentence → Option EF) (e : EF) :
    e.rank ≤ (EF.spliceOn expr e).rank := by
  induction e with
  | price ψ k =>
      cases h : expr k ψ with
      | none => simp [EF.spliceOn, h]
      | some b => simp [EF.spliceOn, h, EF.rank]
  | const q => simp [EF.spliceOn]
  | add a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | mul a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | max a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | safeRecip a iha => simpa [EF.spliceOn, EF.rank] using iha
  | var i => simp [EF.spliceOn]
  | letE x b ihx ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max ihx ihb

/-- **Rank law** (`spliceOn_rank_le`): under the rank discipline on bodies (every body fired on
day `k` has rank `≤ k`, which `ExprMap.leaves`' `p.1 ≤ k` gives), splicing never raises the rank.
Source: mandate T1.1 (`spliceOn_rank_le`); FAF `freezeOn_rank_le`
Kind: L
Fidelity: exact -/
lemma EF.spliceOn_rank_le (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (e : EF) :
    (EF.spliceOn expr e).rank ≤ e.rank := by
  induction e with
  | price ψ k =>
      cases h : expr k ψ with
      | none => simp [EF.spliceOn, h]
      | some b =>
          simp only [EF.spliceOn, h, EF.rank]
          exact Nat.max_le.mpr ⟨le_rfl, hrank k ψ b h⟩
  | const q => simp [EF.spliceOn]
  | add a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | mul a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | max a b iha ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max iha ihb
  | safeRecip a iha => simpa [EF.spliceOn, EF.rank] using iha
  | var i => simp [EF.spliceOn]
  | letE x b ihx ihb => simp only [EF.spliceOn, EF.rank]; exact max_le_max ihx ihb

/-- Rank is preserved exactly under the rank discipline.
Source: mandate T1.1; FAF `freezeOn_rank`
Kind: L
Fidelity: exact -/
lemma EF.spliceOn_rank (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (e : EF) :
    (EF.spliceOn expr e).rank = e.rank :=
  le_antisymm (EF.spliceOn_rank_le expr hrank e) (EF.rank_le_spliceOn expr e)

/-- **Size law** (`spliceOn_cost_le`): with every body of cost `≤ B`, the splice is at most a
`(B + 2)`-fold blow-up — the administrative binding costs the leaf plus the body plus one.
Source: mandate T1.1 (`spliceOn_cost_le`); FAF `freezeOn_cost_le`
Kind: L
Fidelity: exact -/
lemma EF.spliceOn_cost_le (expr : ℕ → Sentence → Option EF) (B : ℕ)
    (hcost : ∀ k ψ e, expr k ψ = some e → e.cost ≤ B) (e : EF) :
    (EF.spliceOn expr e).cost ≤ (B + 2) * e.cost := by
  induction e with
  | price ψ k =>
      cases h : expr k ψ with
      | none => simp [EF.spliceOn, h, EF.cost]
      | some b =>
          simp only [EF.spliceOn, h, EF.cost]
          have := hcost k ψ b h
          omega
  | const q => simp [EF.spliceOn, EF.cost]
  | add a b iha ihb => simp only [EF.spliceOn, EF.cost] at iha ihb ⊢; nlinarith
  | mul a b iha ihb => simp only [EF.spliceOn, EF.cost] at iha ihb ⊢; nlinarith
  | max a b iha ihb => simp only [EF.spliceOn, EF.cost] at iha ihb ⊢; nlinarith
  | safeRecip a iha => simp only [EF.spliceOn, EF.cost] at iha ⊢; nlinarith
  | var i => simp [EF.spliceOn, EF.cost]
  | letE x b ihx ihb => simp only [EF.spliceOn, EF.cost] at ihx ihb ⊢; nlinarith

/-! ## Denotational transport -/

/-- **A splice specification**: what the rewrite needs of its bodies to transport denotations
from the target market `P` to the base `Q`. Every body has at most `var 0` free; bound to the
base price `Q k ψ`, it denotes the target price `P k ψ`; and an un-fired leaf has the same price
on both markets. Instances: `ExprMap.spliceSpec` (closed bodies, `P = overlay Q ov`) and the clamp
(`Clamp.clampSpec`, `P = clamp Q`).
Source: none: infrastructure (the common form of T1.1 and T3's rewrite laws)
Kind: D
Fidelity: n/a -/
structure SpliceSpec (expr : ℕ → Sentence → Option EF) (Q P : History) : Prop where
  /-- Bodies read at most the bound price. -/
  bound : ∀ k ψ e, expr k ψ = some e → EF.freeBound e ≤ 1
  /-- A body, with the base price bound, denotes the target price. -/
  fires : ∀ k ψ e, expr k ψ = some e → e.denoteWith [Q k ψ] Q = P k ψ
  /-- An un-fired leaf reads the same price on both markets. -/
  silent : ∀ k ψ, expr k ψ = none → Q k ψ = P k ψ

/-- An expression map is a splice specification with target `overlay Q ov`: closed bodies read
nothing from the environment, `fires` is `ExprMap.fires`, and `silent` follows from
`ExprMap.silent` and `overlay_small`.
Source: [[bli-program]] §3.1; mandate T1.1
Kind: L
Fidelity: exact -/
lemma ExprMap.spliceSpec {Q : History} {ov : ℕ → Sentence → ℚ} (E : ExprMap Q ov) :
    SpliceSpec E.expr Q (overlay Q ov) where
  bound := fun k ψ e h => by
    have := E.closed k ψ e h
    unfold EF.Closed at this
    omega
  fires := fun k ψ e h => by
    rw [(E.closed k ψ e h).denoteWith_eq_denote, E.fires k ψ e h]
  silent := fun k ψ h => by
    rcases E.silent k ψ h with hov | hs
    · by_cases hs : SmallOn k ψ
      · rw [overlay_small hs]
      · rw [overlay_large hs, hov]
    · rw [overlay_small hs]

/-- **Exact denotational transport** (`spliceOn_denoteWith`): in every environment, the spliced
feature against the base `Q` denotes what the original denotes against the target `P` — no error
term. The leaf half of the program's `denote_eq_of_agree_on_leaves`; the environment half is
`EF.denoteWith_congr_env` (a body with only `var 0` free sees the bound price and nothing else of
the shifted environment).
Source: [[bli-program]] §3.1 (proof sketch); mandate T1.1; FAF `freezeOn_denoteWith`
Kind: L
Fidelity: exact -/
lemma EF.spliceOn_denoteWith {expr : ℕ → Sentence → Option EF} {Q P : History}
    (S : SpliceSpec expr Q P) (e : EF) :
    ∀ ρ : List ℝ, (EF.spliceOn expr e).denoteWith ρ Q = e.denoteWith ρ P := by
  induction e with
  | price ψ k =>
      intro ρ
      cases h : expr k ψ with
      | none =>
          simp only [EF.spliceOn, h, EF.denoteWith]
          exact S.silent k ψ h
      | some b =>
          simp only [EF.spliceOn, h, EF.denoteWith]
          rw [← S.fires k ψ b h]
          apply EF.denoteWith_congr_env
          intro i hi
          have hb := S.bound k ψ b h
          have hi0 : i = 0 := by omega
          subst hi0
          rfl
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [EF.spliceOn, EF.denoteWith, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [EF.spliceOn, EF.denoteWith, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [EF.spliceOn, EF.denoteWith, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [EF.spliceOn, EF.denoteWith, iha ρ]
  | var i => intro ρ; rfl
  | letE x b ihx ihb =>
      intro ρ
      simp only [EF.spliceOn, EF.denoteWith]
      rw [ihx ρ, ihb]

/-- The closed-environment form of `EF.spliceOn_denoteWith`.
Source: mandate T1.1
Kind: L
Fidelity: exact -/
lemma EF.spliceOn_denote {expr : ℕ → Sentence → Option EF} {Q P : History}
    (S : SpliceSpec expr Q P) (e : EF) :
    (EF.spliceOn expr e).denote Q = e.denote P :=
  EF.spliceOn_denoteWith S e []

/-! ## Strategies and traders -/

/-- Apply the splice to every coefficient of a strategy (rank certificate from the bodies' rank
discipline).
Source: mandate T1.1 (`Strategy.spliceOn`); FAF `Strategy.freezeOn`
Kind: D
Fidelity: exact -/
def Strategy.spliceOn (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) {n : ℕ} (T : Strategy n) : Strategy n where
  trades := T.trades.map fun p => (EF.spliceOn expr p.1, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (EF.spliceOn_rank_le expr hrank q.1).trans (T.rank_le q hq)

/-- The trades of a spliced strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma Strategy.spliceOn_trades (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) {n : ℕ} (T : Strategy n) :
    (Strategy.spliceOn expr hrank T).trades = T.trades.map fun p => (EF.spliceOn expr p.1, p.2) :=
  rfl

/-- Apply the splice to every day's strategy.
Source: mandate T1.1 (`Trader.spliceOn`); FAF `Trader.freezeOn`
Kind: D
Fidelity: exact -/
def Trader.spliceOn (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (Tr : Trader) : Trader where
  strat n := Strategy.spliceOn expr hrank (Tr.strat n)

/-- The day strategy of a spliced trader.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma Trader.spliceOn_strat (expr : ℕ → Sentence → Option EF)
    (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k) (Tr : Trader) (n : ℕ) :
    (Trader.spliceOn expr hrank Tr).strat n = Strategy.spliceOn expr hrank (Tr.strat n) := rfl

/-- **Strategy-value law** (`spliceOn_value`): on a day every one of whose traded sentences settles
at the same price on both markets, the spliced strategy against `Q` has exactly the value of the
original against `P` — the settlement term `− V n φ` is not a leaf and cannot be rewritten, so
this is where the bridge lemma's "every traded sentence is eventually small" enters (FAF's
`Strategy.freezeOn_value` needs the whole day fibre unselected for the same reason).
Source: [[bli-program]] §3.1 (proof sketch); mandate T1.2(a); FAF `Strategy.freezeOn_value`
Kind: L
Fidelity: exact -/
lemma Strategy.spliceOn_value {expr : ℕ → Sentence → Option EF} {Q P : History}
    (S : SpliceSpec expr Q P) (hrank : ∀ k ψ e, expr k ψ = some e → e.rank ≤ k)
    {n : ℕ} (T : Strategy n) (w : Sentence → ℝ)
    (hsettle : ∀ p ∈ T.trades, Q n p.2 = P n p.2) :
    (Strategy.spliceOn expr hrank T).value Q w = T.value P w := by
  simp only [Strategy.value, Strategy.spliceOn_trades, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [EF.spliceOn_denote S p.1, hsettle p hp]

end Cleanroom.Bli.BliTransfer.AttemptA
