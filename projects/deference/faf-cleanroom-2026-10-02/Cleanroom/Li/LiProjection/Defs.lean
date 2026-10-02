import Cleanroom.Li.LiProjection.Subst
import LogicalInduction.Framework.Affine

/-!
# `li-projection` · Defs: definitions of record

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 2 of the layout. The
projected market `project P u q` (the dose-response note's extended market
`𝕡_n(φ) := q_n 𝕡̄_n(α_φ) + (1 − q_n) 𝕡̄_n(β_φ)`), the finite patch `patch P S t` (T3), the
feature transform `EF.projectOn u q` (every price leaf `φ^{*m}` becomes the projected price,
written out as a feature of the base prices), the mirror traders `Trader.mirror u q b T`
(the note's `T^⊤`, `T^⊥`) and the affine combination `Trader.affineCombo λ T₁ T₂`
(FAF's `Strategy.scaleBy`/`Strategy.join`).

**Naming (disclosed).** The mandate's table spells `PCWorld.set`, `EF.projectOn`, `Trader.mirror`,
`Trader.affineCombo`. Dot-notation on FAF's types cannot reach declarations of this namespace, so
`PCWorld.set` is `setAtom` (`Subst.lean`) and the other three keep their dotted names but are
called in prefix form (`EF.projectOn u q e`, `Trader.mirror u q b T`).

**Family-4 payload convention of record** (for `li-splice-condition`): a projection atom is
`freshAtom 4 (Nat.pair 0 (Nat.pair 0 k))` — day `0`, then sub-family `0`, then the index `k`
(`projAtom`, `Subst.lean`); `li-splice-condition` takes sub-family `1`.

Scope: one-way wherever two inductors appear (from `Underdetermination.lean` on). The base
inductor's own prices on `u`-sentences are *discarded* by `project`, not assumed anything about.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The projected market -/

/-- **The projected (extended) market.** Day `n`, sentence `φ`:
`q n * P n (φ⟦u := ⊤⟧) + (1 − q n) * P n (φ⟦u := ⊥⟧)`. The weight `q : ℕ → ℚ` is rational so that
it can sit inside `EF.const` (mandate trap (4)). On `u`-free sentences this is `P` itself
(`project_restrict`, `Marginal.lean`).
Source: [[dose-response]] §6.1 Lemma A (the displayed `𝕡_n(φ)`); [[self-referential-settlement-target]] §5.4
Kind: D
Fidelity: exact -/
noncomputable def project (P : History) (u : ℕ) (q : ℕ → ℚ) : History :=
  fun n φ => (q n : ℝ) * P n (φ⟦substAtom u true⟧) + (1 - (q n : ℝ)) * P n (φ⟦substAtom u false⟧)

/-- `project_apply`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma project_apply (P : History) (u : ℕ) (q : ℕ → ℚ) (n : ℕ) (φ : Sentence) :
    project P u q n φ =
      (q n : ℝ) * P n (φ⟦substAtom u true⟧) + (1 - (q n : ℝ)) * P n (φ⟦substAtom u false⟧) := rfl

/-- **The finite patch** (T3): `P` with its prices on the finite coordinate set `S` overwritten by
the table `t`. FAF's `FreezeOracle.pointHistory`/`twoPointHistory` are its one-point and two-point instances.
Source: [[dose-response]] §4 Lemma 4.3 (finite-support reading); mandate T3.1
Kind: D
Fidelity: variant: finite support, not a whole-day prefix (the whole-day form is refuted, T3.2) -/
noncomputable def patch (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ) :
    History :=
  fun n φ => if (n, φ) ∈ S then (t n φ : ℝ) else P n φ

/-- The whole-day overwrite `overwriteBefore P N t`: every price on days `< N` replaced by the
table. This is the shape of Lemma 4.3's *proof* ("overwrite days `< N*`"); T3.2 shows the closure
claim for it is false.
Source: [[dose-response]] §4 Lemma 4.3 (the proof's overwrite)
Kind: D
Fidelity: exact -/
noncomputable def overwriteBefore (P : History) (N : ℕ) (t : ℕ → Sentence → ℚ) : History :=
  fun n φ => if n < N then (t n φ : ℝ) else P n φ

/-- The prescription is exact on `S`.
Source: mandate T3.1 (`patch_mem`)
Kind: L
Fidelity: exact -/
lemma patch_mem (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ) {n : ℕ}
    {φ : Sentence} (h : (n, φ) ∈ S) : patch P S t n φ = (t n φ : ℝ) := by
  simp [patch, h]

/-- Off `S` the patch is `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma patch_notMem (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ) {n : ℕ}
    {φ : Sentence} (h : (n, φ) ∉ S) : patch P S t n φ = P n φ := by
  simp [patch, h]

/-! ## The feature transform -/

/-- **The projected feature.** Every price leaf `price φ m` becomes
`add (mul (const (q m)) (price (φ⟦u:=⊤⟧) m)) (mul (const (1 − q m)) (price (φ⟦u:=⊥⟧) m))`;
every other constructor is homomorphic. Modelled on FAF's `EF.freezeOn`. Its denotation against
the base market is the original's against the projected market (`projectOn_denote`, `Mirror.lean`).
Source: [[dose-response]] §6.1 Lemma A ("extended prices are affine in base prices with day-constants `q_n`")
Kind: D
Fidelity: exact -/
def EF.projectOn (u : ℕ) (q : ℕ → ℚ) : EF → EF
  | .price φ m =>
      .add (.mul (.const (q m)) (.price (φ⟦substAtom u true⟧) m))
        (.mul (.const (1 - q m)) (.price (φ⟦substAtom u false⟧) m))
  | .const c => .const c
  | .add a b => .add (EF.projectOn u q a) (EF.projectOn u q b)
  | .mul a b => .mul (EF.projectOn u q a) (EF.projectOn u q b)
  | .max a b => .max (EF.projectOn u q a) (EF.projectOn u q b)
  | .safeRecip a => .safeRecip (EF.projectOn u q a)
  | .var i => .var i
  | .letE x body => .letE (EF.projectOn u q x) (EF.projectOn u q body)

/-- The projected feature has the rank of the original.
Source: none: infrastructure (mandate `projectOn_rank_le`)
Kind: L
Fidelity: n/a -/
@[simp] lemma EF.projectOn_rank (u : ℕ) (q : ℕ → ℚ) (e : EF) :
    (EF.projectOn u q e).rank = e.rank := by
  induction e with
  | price φ m => simp [EF.projectOn]
  | const c => simp [EF.projectOn]
  | add a b iha ihb => simp [EF.projectOn, iha, ihb]
  | mul a b iha ihb => simp [EF.projectOn, iha, ihb]
  | max a b iha ihb => simp [EF.projectOn, iha, ihb]
  | safeRecip a iha => simp [EF.projectOn, iha]
  | var i => simp [EF.projectOn]
  | letE x body ihx ihb => simp [EF.projectOn, ihx, ihb]

/-- `EF.projectOn_rank_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EF.projectOn_rank_le (u : ℕ) (q : ℕ → ℚ) (e : EF) :
    (EF.projectOn u q e).rank ≤ e.rank := by
  rw [EF.projectOn_rank]

/-! ## Mirror traders and affine combinations -/

/-- The mirror of a day-`n` strategy: each trade `(e, φ)` becomes
`(EF.projectOn u q e, φ⟦substAtom u b⟧)` — the note's `T^⊤` (`b = true`) / `T^⊥` (`b = false`)
executed at base prices.
Source: [[dose-response]] §6.1 Lemma A ("mirror `T`, executing `t_{n,φ}` shares of `α_φ` (resp. `β_φ`) at base prices")
Kind: D
Fidelity: exact -/
def Strategy.mirror {n : ℕ} (u : ℕ) (q : ℕ → ℚ) (b : Bool) (T : Strategy n) : Strategy n where
  trades := T.trades.map fun p => (EF.projectOn u q p.1, p.2⟦substAtom u b⟧)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    exact (EF.projectOn_rank_le u q r.1).trans (T.rank_le r hr)

/-- The mirror trader `T^b`: `Strategy.mirror` day by day.
Source: [[dose-response]] §6.1 Lemma A
Kind: D
Fidelity: exact -/
def Trader.mirror (u : ℕ) (q : ℕ → ℚ) (b : Bool) (T : Trader) : Trader where
  strat n := Strategy.mirror u q b (T.strat n)

/-- The affine combination `λ T₁ + (1 − λ) T₂` of two traders, day by day: `T₁`'s trades scaled by
`const λ` joined with `T₂`'s scaled by `const (1 − λ)` (FAF's `Strategy.scaleBy` and `Strategy.join`).
Source: [[dose-response]] §6.1 Lemma A (`S := λ T^⊤ + (1 − λ) T^⊥`; [LI 3.4.4] closure under affine combinations)
Kind: D
Fidelity: exact -/
def Trader.affineCombo (lam : ℚ) (T₁ T₂ : Trader) : Trader where
  strat n := Strategy.join
    [Strategy.scaleBy (EF.const lam) (Nat.zero_le n) (T₁.strat n),
     Strategy.scaleBy (EF.const (1 - lam)) (Nat.zero_le n) (T₂.strat n)]

/-- The day-`m` **exposure** of `T` to the atom, at the projected market:
`D_m := Σ_{(e,φ) ∈ T.strat m} e(𝕡) · (P m (φ⟦u:=⊤⟧) − P m (φ⟦u:=⊥⟧))`. World-independent.
Source: [[dose-response]] §6.1 Lemma A (`D_n`)
Kind: D
Fidelity: exact -/
noncomputable def exposure (T : Trader) (P : History) (u : ℕ) (q : ℕ → ℚ) (m : ℕ) : ℝ :=
  ((T.strat m).trades.map fun p =>
    p.1.denote (project P u q) * (P m (p.2⟦substAtom u true⟧) - P m (p.2⟦substAtom u false⟧))).sum

end Cleanroom.Li.LiProjection
