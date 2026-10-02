import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Countable probability frames: definitions of record and Value ⟹ Total Trust (T3, T4)

Package `lit-weatherson-frames` (faf-cleanroom run, 2026-09-30). A *countable frame* on a
carrier `W` (in this package `ℕ` or `ℤ × Bool`) is a row-stochastic kernel `P : W → W → ℝ` with
`HasSum (P w) 1`; a prior `π` is a distribution `IsDist π`. Expectation is
`Eℕ ρ X = ∑' w, ρ w * X w`.

**The junk value this file fences**: Lean's `tsum` of a non-summable function is `0`. Every
definition of record therefore carries the summability its statement needs as a hypothesis on
the random variable — `Bdd X` (bounded: then `ρ w * X w` is summable for every distribution `ρ`)
or `IntegrableW π X` (`π`-integrable) together with `RowsIntegrable F X` (each expert row
integrates `X`) — never silently. Menus are indexed families `o : ι → W → ℝ`; a strategy is
`S : W → ι` with the DDB cell constraint; `stratValueC π o S = ∑' w, π w * o (S w) w` is summable
under a uniformly bounded menu (`BddFam`) or a finite menu of integrable options, and `ValueInt`
(any menu, integrable options — the predicate Coin refutes) guards it explicitly.

`ValueBdd` quantifies over **uniformly** bounded menus (`BddFam o := ∃ M, ∀ i w, |o i w| ≤ M`),
not per-option bounded ones: with per-option bounds the predicate is false on Coin, whose options
`O i` are each bounded (by `2^i`) but not uniformly — finding F-T8 in the report; the mandate's
`Bdd` per option is corrected here.

Total Trust is the product form of `lit-ddb-frames` with the same convention: on a `π`-null
threshold event every summand is `0`, so only positive-mass events constrain.
-/

namespace Cleanroom.Lit.LitWeathersonFrames

noncomputable section

variable {W : Type}

/-! ## Frames, priors, expectation -/

/-- A countable probability frame: at each world `w` a distribution `P w` on `W` (nonnegative,
summing to one).
Source: [[Deference and Infinite Frames]] §3 l. 174 ("a probability frame is an ordered pair
`⟨W, P⟩`"), for infinite `W`
Kind: D
Fidelity: exact -/
structure CFrame (W : Type) where
  /-- the expert's probabilities at each world -/
  P : W → W → ℝ
  /-- rows are nonnegative -/
  P_nonneg : ∀ w v, 0 ≤ P w v
  /-- rows sum to one -/
  P_hasSum : ∀ w, HasSum (P w) 1

/-- A distribution on `W`: nonnegative, summing to one.
Source: [[Deference and Infinite Frames]] §3 l. 180 (`π`, Novice's probability function)
Kind: D
Fidelity: exact -/
def IsDist (π : W → ℝ) : Prop := (∀ w, 0 ≤ π w) ∧ HasSum π 1

/-- Expectation `E_ρ(X) = ∑' w, ρ w * X w` on a countable carrier. Junk (`0`) when the series is
not summable; every consumer carries a summability hypothesis.
Source: [[Deference and Infinite Frames]] §2 (`Exp(X, Pr)`), §3 l. 180
Kind: D
Fidelity: exact (under summability) -/
def Eℕ (ρ X : W → ℝ) : ℝ := ∑' w, ρ w * X w

/-- A bounded random variable.
Source: [[Deference and Infinite Frames]] §3 l. 194 ("the value function … was unbounded")
Kind: D
Fidelity: exact -/
def Bdd (X : W → ℝ) : Prop := ∃ M, ∀ w, |X w| ≤ M

/-- A **uniformly** bounded menu of options: one bound for all options. This, not per-option
boundedness, is "bounded utilities" (Coin's options are each bounded, not uniformly).
Source: [[Deference and Infinite Frames]] §3 l. 194; abstract l. 29 ("when utilities are
unbounded")
Kind: D
Fidelity: exact (see the module docstring) -/
def BddFam {ι : Type} (o : ι → W → ℝ) : Prop := ∃ M, ∀ i w, |o i w| ≤ M

/-- `X` is `π`-integrable: `∑' w, π w * |X w|` converges.
Source: none: infrastructure (the summability class Coin's unbounded options belong to)
Kind: D
Fidelity: n/a -/
def IntegrableW (π X : W → ℝ) : Prop := Summable (fun w => π w * |X w|)

/-- Every expert row of the frame integrates `X`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def RowsIntegrable (F : CFrame W) (X : W → ℝ) : Prop := ∀ w, Summable (fun v => F.P w v * |X v|)

/-! ## Total Trust (product form) -/

/-- **Total Trust on a countable frame, bounded variables** (product form):
`∀ X bounded, ∀ t, 0 ≤ ∑' w, π w · (X w − t) · 𝟙[t ≤ E_{P_w}(X)]`. On a `π`-null threshold event
every summand is `0` (DDB's convention, as in `lit-ddb-frames`' `TotalTrust`); the summand is
summable for every bounded `X` (`totalTrust_summand_summable`).
Source: [[Deference and Infinite Frames]] §3 l. 176 (Total Trust); [[Deference Done Better]] §2
Kind: D
Fidelity: exact (product form; bounded `X`) -/
def TotalTrustC (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ X, Bdd X → ∀ t, 0 ≤ ∑' w, π w * (X w - t) * (if t ≤ Eℕ (F.P w) X then 1 else 0)

/-- **Total Trust on a countable frame, integrable variables**: the same inequality for every
`π`-integrable `X` that every expert row integrates (so that every `E_{P_w}(X)` is a genuine
expectation).
Source: [[Deference and Infinite Frames]] §3 l. 176 (Total Trust, "any random variable `X`")
Kind: D
Fidelity: exact (product form; integrable `X`) -/
def TotalTrustInt (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ X, IntegrableW π X → RowsIntegrable F X → ∀ t,
    0 ≤ ∑' w, π w * (X w - t) * (if t ≤ Eℕ (F.P w) X then 1 else 0)

/-! ## Menus, strategies, Value -/

/-- A strategy `S : W → ι` on the frame satisfies the **cell constraint**: it chooses by the
expert's probabilities (`P w = P v → S w = S v`), as in DDB and `lit-ddb-frames`.
Source: [[Deference Done Better]] §1 l. 117; `lit-ddb-frames` `Frame.IsStrategy`
Kind: D
Fidelity: exact -/
def CFrame.IsStrategyC (F : CFrame W) {ι : Type} (S : W → ι) : Prop :=
  ∀ w v, F.P w = F.P v → S w = S v

/-- A strategy is **recommended** for the menu `o` when it is a strategy and at every world its
choice maximises expected utility under the expert's probabilities there.
Source: [[Deference and Infinite Frames]] §3 l. 178 ("`s` is a recommended strategy for `O`");
[[Deference Done Better]] §1 l. 117
Kind: D
Fidelity: exact -/
def RecommendedC (F : CFrame W) {ι : Type} (o : ι → W → ℝ) (S : W → ι) : Prop :=
  F.IsStrategyC S ∧ ∀ w i, Eℕ (F.P w) (o i) ≤ Eℕ (F.P w) (o (S w))

/-- The expected return `E_π(S) = ∑' w, π w · o (S w) w` of following a strategy.
Source: [[Deference and Infinite Frames]] §3 l. 178 (`Exp(s, π)`)
Kind: D
Fidelity: exact (under summability) -/
def stratValueC (π : W → ℝ) {ι : Type} (o : ι → W → ℝ) (S : W → ι) : ℝ :=
  ∑' w, π w * o (S w) w

/-- **Value, uniformly bounded menus**: for every menu (any index type) of uniformly bounded
options and every recommended strategy, the strategy's return is at least every option's
expectation.
Source: [[Deference and Infinite Frames]] §3 l. 178 (Value)
Kind: D
Fidelity: exact (uniformly bounded options; see the module docstring) -/
def ValueBdd (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) (o : ι → W → ℝ), BddFam o →
    ∀ S, RecommendedC F o S → ∀ i, Eℕ π (o i) ≤ stratValueC π o S

/-- **Value, finite menus of integrable options**: for every finite menu of `π`-integrable,
row-integrable options and every recommended strategy, the return dominates every option.
Source: [[Deference and Infinite Frames]] §3 l. 178 (Value), l. 194 ("`O` … finite")
Kind: D
Fidelity: exact (finite menus; integrable options) -/
def ValueFinInt (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) [Fintype ι] (o : ι → W → ℝ), (∀ i, IntegrableW π (o i)) →
    (∀ i, RowsIntegrable F (o i)) →
    ∀ S, RecommendedC F o S → ∀ i, Eℕ π (o i) ≤ stratValueC π o S

/-- **Value, any menu of integrable options** — the predicate Coin refutes. The strategy's return
must be summable for the clause to apply (otherwise `stratValueC` would be junk), so a
refutation must exhibit a recommended strategy with summable return below some option.
Source: [[Deference and Infinite Frames]] §3 l. 178 (Value), l. 188 (Coin)
Kind: D
Fidelity: exact (guarded by summability of the return) -/
def ValueInt (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) (o : ι → W → ℝ), (∀ i, IntegrableW π (o i)) → (∀ i, RowsIntegrable F (o i)) →
    ∀ S, RecommendedC F o S → Summable (fun w => π w * o (S w) w) →
      ∀ i, Eℕ π (o i) ≤ stratValueC π o S

/-- **Weak Value, integrable options**: for every nonempty menu of integrable options *some*
recommended strategy with summable return dominates every option.
Source: [[Deference Done Better]] App. B l. 472; inventory 032
Kind: D
Fidelity: exact -/
def WeakValueInt (π : W → ℝ) (F : CFrame W) : Prop :=
  ∀ (ι : Type) [Nonempty ι] (o : ι → W → ℝ), (∀ i, IntegrableW π (o i)) →
    (∀ i, RowsIntegrable F (o i)) →
    ∃ S, RecommendedC F o S ∧ Summable (fun w => π w * o (S w) w) ∧
      ∀ i, Eℕ π (o i) ≤ stratValueC π o S

/-! ## Plumbing -/

/-- A distribution is summable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsDist.summable {π : W → ℝ} (hπ : IsDist π) : Summable π := hπ.2.summable

/-- `∑' w, π w = 1` for a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsDist.tsum_eq {π : W → ℝ} (hπ : IsDist π) : ∑' w, π w = 1 := hπ.2.tsum_eq

/-- Each row of a countable frame is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CFrame.isDist (F : CFrame W) (w : W) : IsDist (F.P w) := ⟨F.P_nonneg w, F.P_hasSum w⟩

/-- A bounded variable is integrable against every distribution.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Bdd.integrableW {X : W → ℝ} (hX : Bdd X) {ρ : W → ℝ} (hρ : IsDist ρ) :
    IntegrableW ρ X := by
  obtain ⟨M, hM⟩ := hX
  refine Summable.of_nonneg_of_le (fun w => mul_nonneg (hρ.1 w) (abs_nonneg _))
    (fun w => mul_le_mul_of_nonneg_left (hM w) (hρ.1 w)) (hρ.summable.mul_right M)

/-- A bounded variable is integrated by every row of every frame.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Bdd.rowsIntegrable {X : W → ℝ} (hX : Bdd X) (F : CFrame W) : RowsIntegrable F X :=
  fun w => hX.integrableW (F.isDist w)

/-- `ρ w * X w` is summable when `X` is `ρ`-integrable and `ρ ≥ 0`.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem IntegrableW.summable_mul {ρ X : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (hX : IntegrableW ρ X) :
    Summable (fun w => ρ w * X w) := by
  refine Summable.of_norm_bounded hX fun w => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ w)]

/-- `ρ w * X w` is summable for bounded `X` and any distribution `ρ` (mandate T3).
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Bdd.summable_mul {X : W → ℝ} (hX : Bdd X) {ρ : W → ℝ} (hρ : IsDist ρ) :
    Summable (fun w => ρ w * X w) :=
  (hX.integrableW hρ).summable_mul hρ.1

/-- A constant has expectation itself under a distribution.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Eℕ_const {ρ : W → ℝ} (hρ : IsDist ρ) (t : ℝ) : Eℕ ρ (fun _ => t) = t := by
  unfold Eℕ
  rw [tsum_mul_right, hρ.tsum_eq, one_mul]

/-- Linearity of `Eℕ` in the variable (under summability).
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Eℕ_sub {ρ X Y : W → ℝ} (hX : Summable (fun w => ρ w * X w))
    (hY : Summable (fun w => ρ w * Y w)) : Eℕ ρ (X - Y) = Eℕ ρ X - Eℕ ρ Y := by
  unfold Eℕ
  rw [← hX.tsum_sub hY]
  exact tsum_congr fun w => by simp [mul_sub]

/-- Linearity of `Eℕ` in the variable (under summability).
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Eℕ_add {ρ X Y : W → ℝ} (hX : Summable (fun w => ρ w * X w))
    (hY : Summable (fun w => ρ w * Y w)) : Eℕ ρ (X + Y) = Eℕ ρ X + Eℕ ρ Y := by
  unfold Eℕ
  rw [← hX.tsum_add hY]
  exact tsum_congr fun w => by simp [mul_add]

/-- Monotonicity of `Eℕ` (under summability, `ρ ≥ 0`).
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem Eℕ_le_Eℕ {ρ X Y : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) (hX : Summable (fun w => ρ w * X w))
    (hY : Summable (fun w => ρ w * Y w)) (h : ∀ w, X w ≤ Y w) : Eℕ ρ X ≤ Eℕ ρ Y :=
  hX.tsum_le_tsum (fun w => mul_le_mul_of_nonneg_left (h w) (hρ w)) hY

/-- The Total Trust summand `π w · (X w − t) · 𝟙[…]` is summable for integrable `X`.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem totalTrust_summand_summable {π X : W → ℝ} (hπ : IsDist π) (hX : IntegrableW π X)
    (t : ℝ) (c : W → Prop) [DecidablePred c] :
    Summable (fun w => π w * (X w - t) * (if c w then 1 else 0)) := by
  refine Summable.of_norm_bounded (g := fun w => π w * |X w| + π w * |t|)
    (hX.add (hπ.summable.mul_right _)) fun w => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hπ.1 w)]
  have h1 : |(if c w then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  calc π w * |X w - t| * |(if c w then (1:ℝ) else 0)|
      ≤ π w * |X w - t| * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (hπ.1 w) (abs_nonneg _))
    _ = π w * |X w - t| := mul_one _
    _ ≤ π w * (|X w| + |t|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (hπ.1 w)
    _ = π w * |X w| + π w * |t| := mul_add _ _ _

/-- The return of a strategy for a uniformly bounded menu is summable.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem stratValue_summable_of_bddFam {π : W → ℝ} (hπ : IsDist π) {ι : Type} {o : ι → W → ℝ}
    (ho : BddFam o) (S : W → ι) : Summable (fun w => π w * o (S w) w) := by
  obtain ⟨M, hM⟩ := ho
  refine Summable.of_norm_bounded (g := fun w => π w * M) (hπ.summable.mul_right M) fun w => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 w)]
  exact mul_le_mul_of_nonneg_left (hM _ _) (hπ.1 w)

/-- The return of a strategy for a finite menu of integrable options is summable.
Source: none: infrastructure (T3 plumbing)
Kind: L
Fidelity: n/a -/
theorem stratValue_summable_of_fintype {π : W → ℝ} (hπ : IsDist π) {ι : Type} [Fintype ι]
    {o : ι → W → ℝ} (ho : ∀ i, IntegrableW π (o i)) (S : W → ι) :
    Summable (fun w => π w * o (S w) w) := by
  refine Summable.of_norm_bounded (g := fun w => ∑ i, π w * |o i w|)
    (summable_sum fun i _ => ho i) fun w => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 w)]
  exact Finset.single_le_sum (f := fun i => π w * |o i w|)
    (fun i _ => mul_nonneg (hπ.1 w) (abs_nonneg _)) (Finset.mem_univ (S w))

/-- `Eℕ π (o i)` is bounded by `M` for a uniformly bounded menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem BddFam.bdd {ι : Type} {o : ι → W → ℝ} (ho : BddFam o) (i : ι) : Bdd (o i) :=
  ho.elim fun M hM => ⟨M, hM i⟩

/-! ## T4. Value ⟹ Total Trust on every countable frame -/

/-- The two-option menu `{X, const t}` indexed by `Bool` (`true ↦ X`).
Source: [[Deference Done Better]] App. B Lemma 7.1 (the two-option witness)
Kind: D
Fidelity: exact -/
def twoMenu (X : W → ℝ) (t : ℝ) : Bool → W → ℝ := fun b => if b then X else fun _ => t

/-- The two-option strategy: take `X` exactly where the expert's estimate of `X` is at least `t`.
It depends on `w` only through `F.P w`, hence satisfies the cell constraint.
Source: [[Deference Done Better]] App. B Lemma 7.1; `lit-ddb-frames` `Frame.twoOption`
Kind: D
Fidelity: exact -/
def twoStrat (F : CFrame W) (X : W → ℝ) (t : ℝ) : W → Bool :=
  fun w => decide (t ≤ Eℕ (F.P w) X)

/-- The two-option strategy is recommended (no hypothesis on `X`: the comparison is between the
row's value of `Eℕ … X`, whatever it is, and the constant `t`; consumers supply integrability so
that the value is a genuine expectation).
Source: [[Deference Done Better]] App. B Lemma 7.1
Kind: L
Fidelity: n/a -/
theorem twoStrat_recommended (F : CFrame W) (X : W → ℝ) (t : ℝ) :
    RecommendedC F (twoMenu X t) (twoStrat F X t) := by
  refine ⟨fun w v h => by simp [twoStrat, h], fun w b => ?_⟩
  have hc : Eℕ (F.P w) (fun _ => t) = t := Eℕ_const (F.isDist w) t
  by_cases ht : t ≤ Eℕ (F.P w) X
  · simp only [twoStrat, ht, decide_true]
    cases b
    · simp only [twoMenu, Bool.false_eq_true, ↓reduceIte]
      rw [hc]; exact ht
    · exact le_rfl
  · simp only [twoStrat, ht, decide_false]
    cases b
    · exact le_rfl
    · simp only [twoMenu, ↓reduceIte, Bool.false_eq_true]
      rw [hc]; exact le_of_lt (not_le.mp ht)

/-- The product-form Total Trust sum is the two-option return minus `t`.
Source: `lit-ddb-frames` `stratValue_twoOption`, countable form
Kind: L
Fidelity: n/a -/
theorem totalTrust_sum_eq_twoStrat {π : W → ℝ} (hπ : IsDist π) (F : CFrame W) {X : W → ℝ}
    (hX : IntegrableW π X) (t : ℝ) :
    ∑' w, π w * (X w - t) * (if t ≤ Eℕ (F.P w) X then 1 else 0) =
      stratValueC π (twoMenu X t) (twoStrat F X t) - t := by
  have hs : Summable (fun w => π w * twoMenu X t (twoStrat F X t w) w) := by
    refine Summable.of_norm_bounded (g := fun w => π w * |X w| + π w * |t|)
      (hX.add (hπ.summable.mul_right _)) fun w => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ.1 w)]
    simp only [twoMenu, twoStrat]
    split_ifs
    · linarith [mul_nonneg (hπ.1 w) (abs_nonneg t)]
    · linarith [mul_nonneg (hπ.1 w) (abs_nonneg (X w))]
  have ht : ∑' w, π w * t = t := by rw [tsum_mul_right, hπ.tsum_eq, one_mul]
  have key : ∑' w, (π w * twoMenu X t (twoStrat F X t w) w - π w * t) =
      stratValueC π (twoMenu X t) (twoStrat F X t) - t := by
    rw [hs.tsum_sub (hπ.summable.mul_right t), ht]; rfl
  rw [← key]
  refine tsum_congr fun w => ?_
  simp only [twoMenu, twoStrat]
  by_cases h : t ≤ Eℕ (F.P w) X <;> simp [h] ; ring

/-- **T4 (load-bearing 2). Value ⟹ Total Trust on every countable frame** (bounded
variables). DDB's Lemma 7.1 two-option witness needs no finiteness: for `X` bounded and any
`t`, the menu `{X, const t}` with the strategy "take `X` where the expert expects at least `t`"
is recommended, and Value's inequality against the constant option is exactly the product-form
Total Trust inequality. Not a squeeze: `ValueBdd` quantifies over all menus and strategies, the
instance used is one two-option menu. Consequence: the Value ⟹ Total Trust direction of DDB's
Theorem 2.2 cannot fail on any countable frame under the positive-mass convention — the
abstract's "breaks down in both directions" is false in this direction (finding F-T4; Bentham's
"failure" conditions on a null event, `Bentham.lean`).
Source: [[Deference and Infinite Frames]] abstract l. 29, §3 l. 186; [[Deference Done Better]]
App. B Lemma 7.1; mandate T4
Kind: P
Fidelity: exact (product form, positive-mass convention)
Hyps: (a) `hπ : IsDist π` only -/
theorem value_imp_totalTrust {π : W → ℝ} (hπ : IsDist π) {F : CFrame W} (hV : ValueBdd π F) :
    TotalTrustC π F := by
  intro X hX t
  have hbdd : BddFam (twoMenu X t) := by
    obtain ⟨M, hM⟩ := hX
    refine ⟨max M |t|, fun b w => ?_⟩
    cases b
    · simp [twoMenu]
    · simp only [twoMenu, ↓reduceIte]; exact le_trans (hM w) (le_max_left _ _)
  have := hV Bool (twoMenu X t) hbdd (twoStrat F X t)
    (twoStrat_recommended F X t) false
  rw [totalTrust_sum_eq_twoStrat hπ F (hX.integrableW hπ) t]
  have hc : Eℕ π (twoMenu X t false) = t := Eℕ_const hπ t
  rw [hc] at this
  linarith

/-- **T4, integrable form.** Value on finite menus of integrable options implies Total Trust for
every `π`-integrable, row-integrable variable (the two-option menu is finite).
Source: [[Deference Done Better]] App. B Lemma 7.1; mandate T4
Kind: P
Fidelity: exact (product form, positive-mass convention)
Hyps: (a) `hπ : IsDist π` only -/
theorem valueFinInt_imp_totalTrustInt {π : W → ℝ} (hπ : IsDist π) {F : CFrame W}
    (hV : ValueFinInt π F) : TotalTrustInt π F := by
  intro X hX hrows t
  have hint : ∀ b, IntegrableW π (twoMenu X t b) := by
    intro b; cases b
    · simpa [twoMenu] using (Bdd.integrableW ⟨|t|, fun _ => le_rfl⟩ hπ : IntegrableW π fun _ => t)
    · simpa [twoMenu] using hX
  have hrow : ∀ b, RowsIntegrable F (twoMenu X t b) := by
    intro b; cases b
    · simpa [twoMenu] using (Bdd.rowsIntegrable ⟨|t|, fun _ => le_rfl⟩ F : RowsIntegrable F fun _ => t)
    · simpa [twoMenu] using hrows
  have := hV Bool (twoMenu X t) hint hrow (twoStrat F X t) (twoStrat_recommended F X t) false
  rw [totalTrust_sum_eq_twoStrat hπ F hX t]
  have hc : Eℕ π (twoMenu X t false) = t := Eℕ_const hπ t
  rw [hc] at this
  linarith

/-- Total Trust for integrable variables implies Total Trust for bounded ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TotalTrustInt.totalTrustC {π : W → ℝ} (hπ : IsDist π) {F : CFrame W}
    (h : TotalTrustInt π F) : TotalTrustC π F :=
  fun X hX t => h X (hX.integrableW hπ) (hX.rowsIntegrable F) t

/-- `tsum` of a nonnegative family is nonnegative (specialized helper).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tsum_nonneg' {f : W → ℝ} (h : ∀ w, 0 ≤ f w) : 0 ≤ ∑' w, f w := tsum_nonneg h

end

end Cleanroom.Lit.LitWeathersonFrames
