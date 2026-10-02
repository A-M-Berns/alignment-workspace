import Cleanroom.Fa.FaForcingTrader.Defs

/-!
# `fa-adaptive-joint` · Defs: the softened one-position machine as an `EF` feature

Definitions of record for [[fa-adaptive-joint-mandate]] (T1's objects, T2's real-sequence
interface). The package decides v3's (A4) over FAF's feature language `EF`
(`Framework/Criterion.lean`): the state machine *flat / holding until `f n`; when flat on a day
with `w_n ≥ θ` (softly) open a position of fraction `fire_n`; at `f n` close* is rendered in the
**additive** soft form (mandate § T1):

* `r n = ctsInd (θ/2) (w n) (θ/2)` — the ramp, `0` at `w_n ≤ θ/2`, `1` at `w_n ≥ θ`;
* `open n = ∑_{m < n, n < f m} fire m` — the pieces still held on day `n`;
* `fire n = (1 − open n) · r n`.

Day `n`'s feature is a straight-line program: `letE fire_0 (letE fire_1 (… (letE fire_{n−1} fire_n)))`,
where the day-`k` binding `fireExpr k` refers to the earlier bindings through de Bruijn indices
(`var (k − 1 − m)` is `fire m`) and the membership `n < f m` is a *fixed natural-number fact*
decided at emission time by `f.graph_fp` (through the ruler `openCount`), never a feature
(mandate trap (ε)). The product softening `flat_n = Π (1 − fire_m)` (FAF's `armChain` shape) is
**not** used: it over-fires (mandate trap (α), findings F2, `Counting.lean`).

This file holds the syntax, the denotation laws and the real-valued recursion; the emission
certificate (T1, `adaptFire_pgenerable`) is in `Expressibility.lean`, the counting argument (T2)
in `Counting.lean`.
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-! ## A. The emission-time open test `n < f m`, as a unary ruler -/

/-- The number of `i ≤ j` with `f m = i`, read at the paired index `⟨j, m⟩`: FAF's prefix scan of
the graph decider `f.graphFlag` over `i < j + 1`. It is `0` iff `j < f m`, i.e. iff a piece
opened on day `m` is still open on day `j` (`openCount_eq_zero_iff`); a machine computes it in
polynomial time on the unary pair (`openCount_ruler`), which is how `f.graph_fp` enters the
emission and why the firing set is never a `ℕ → ℚ` table (mandate trap (ε), root-fa-2-003 (β)).
Source: [[fa-adaptive-joint-mandate]] § T1 ("the index set `{m < n : n < f m}` is computed from `f.graph_fp` at emission time"); FAF `unaryRuler_scheduledValue`
Kind: D
Fidelity: n/a
Hyps: n/a -/
def openCount (f : DeferralFunction) (z : ℕ) : ℕ :=
  segPrefix f.graphFlag z.unpair.2 (z.unpair.1 + 1)

/-- The scan is `0` iff no `i < r` has `f m = i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem segPrefix_graphFlag_eq_zero_iff (f : DeferralFunction) (m : ℕ) :
    ∀ r, segPrefix f.graphFlag m r = 0 ↔ ∀ i < r, f.f m ≠ i
  | 0 => by simp
  | r + 1 => by
      rw [segPrefix_succ, Nat.add_eq_zero_iff, segPrefix_graphFlag_eq_zero_iff f m r]
      simp only [DeferralFunction.graphFlag, Nat.unpair_pair]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · intro h
          simp [h] at h2
      · intro h
        refine ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), ?_⟩
        have := h r (Nat.lt_succ_self r)
        simp [this]

/-- `openCount f ⟨j, m⟩ = 0 ↔ j < f m`: the piece opened on day `m` is still open on day `j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openCount_eq_zero_iff (f : DeferralFunction) (j m : ℕ) :
    openCount f (Nat.pair j m) = 0 ↔ j < f.f m := by
  simp only [openCount, Nat.unpair_pair]
  rw [segPrefix_graphFlag_eq_zero_iff]
  constructor
  · intro h
    by_contra hle
    exact h (f.f m) (Nat.lt_succ_of_le (not_lt.1 hle)) rfl
  · intro hj i hi hfi
    omega

/-- The open test is machine-metered on the unary pair: FAF's `UnaryRuler.segPrefix` of the graph
decider, composed with `⟨j, m⟩ ↦ ⟨m, j + 1⟩` (FAF's `unaryRuler_scheduledValue` pattern).
Source: [[fa-adaptive-joint-mandate]] § T1; FAF `DeferralFunction.graphFlag_ruler`, `UnaryRuler.segPrefix`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openCount_ruler (f : DeferralFunction) : UnaryRuler (openCount f) :=
  ((UnaryRuler.segPrefix f.graphFlag_ruler).comp
    (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst.succ)).of_eq (fun z => by simp [openCount])

/-! ## B. The day-`k` binding and the `letE` chain -/

/-- The price-free constant `1` if the piece of day `z.2` is still open on day `z.1`, else `0`,
written through the decidable count so that it is emitted by `ifZero` on the ruler.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: D
Fidelity: exact
Hyps: n/a -/
def openInd (f : DeferralFunction) (z : ℕ) : EF :=
  EF.const (if openCount f z = 0 then 1 else 0)

/-- One summand of the open position on day `j = z.1` from the piece of day `m = z.2`:
`openInd · var (j − 1 − m)`, the de Bruijn reference to the binding `fire m` inside the chain
(`fire (j−1)` is `var 0`, `fire (j−2)` is `var 1`, …).
Source: [[fa-adaptive-joint-mandate]] § T1 ("`open n := Σ_{m < n, n < f m} fire m`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def pieceTerm (f : DeferralFunction) (z : ℕ) : EF :=
  EF.mul (openInd f z) (EF.var (z.unpair.1 - 1 - z.unpair.2))

/-- The open position on day `j` summed over the first `m` pieces, as a left-nested sum of
`pieceTerm`s starting from `const 0` (FAF's `armChain` shape, additive).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: D
Fidelity: exact
Hyps: n/a -/
def openExprAux (f : DeferralFunction) (j : ℕ) : ℕ → EF
  | 0 => EF.const 0
  | m + 1 => EF.add (openExprAux f j m) (pieceTerm f (Nat.pair j m))

/-- `open j = ∑_{m < j, j < f m} fire m` as a feature with de Bruijn references.
Source: [[fa-adaptive-joint-mandate]] § T1 (`adaptOpen`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def openExpr (f : DeferralFunction) (j : ℕ) : EF := openExprAux f j j

/-- The ramp `r_n = ctsInd (θ/2) (w n) (θ/2)` of width `θ/2` on the feature family `w`: `0` at
`w_n ≤ θ/2`, `1` at `w_n ≥ θ` (FAF's `ctsIndFeature` against the constant threshold `θ/2`; the
width `θ/2` is v3's "say", fixed here — mandate trap (δ)).
Source: [[fa-positive-results-corrected-v3]] §4 ("a ramp of width `θ/2`, say"); mandate K4
Kind: D
Fidelity: exact
Hyps: n/a -/
def ramp (θ : ℚ) (w : ℕ → EF) : ℕ → EF :=
  ctsIndFeature (fun _ => θ / 2) w (fun _ => EF.const (θ / 2))

/-- The day-`j` binding of the chain: `fire j = (1 − open j) · r j`, with `open j` referring to the
earlier bindings by de Bruijn index.
Source: [[fa-adaptive-joint-mandate]] § T1 ("`fire n := flat n · r n`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def fireExpr (w : ℕ → EF) (f : DeferralFunction) (θ : ℚ) (j : ℕ) : EF :=
  EF.mul (oneMinus (openExpr f j)) (ramp θ w j)

/-- A straight-line program: `chainList [x₀, …, x_{k−1}] b = letE x₀ (letE x₁ (… (letE x_{k−1} b)))`.
Inside `b`, `x_{k−1}` is `var 0`, `x_{k−2}` is `var 1`, …; inside `x_i`, `x_{i−1}` is `var 0`.
Source: none: infrastructure (FAF `EF.letE`, licensed by the LI paper's footnote tex:788)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chainList : List EF → EF → EF
  | [], b => b
  | a :: xs, b => EF.letE a (chainList xs b)

/-- **The firing feature of v3's `T_θ` (definition of record).** Day `n`'s expression binds
`fire 0, …, fire (n−1)` once each (`letE`) and returns `fire n = (1 − open n) · r n`. Rank `≤ n`,
closed, and emitted in polynomial time: `adaptFire_pgenerable` (T1, `Expressibility.lean`).
Denotes `adaptFireR w f θ P n` in every environment (`adaptFire_denoteWith`).
Source: [[fa-positive-results-corrected-v3]] §4 "(A4)"; root-fa-020; lean-deference-043; [[fa-adaptive-joint-mandate]] § T1
Kind: D
Fidelity: variant: the additive softening (`open` as a sum, mandate trap (α)) of v3's "flat / holding" machine, lookahead a general `DeferralFunction` (K3), width `θ/2`; the weighting is the soft firing *indicator* `flat · r` (so `fire n = 1` on a flat day with `w_n = θ`), not v3's `λ w_n`-sized position `u_n ≤ w_n` — the position size belongs to T4's trader (audit r1 N4)
Hyps: n/a -/
def adaptFire (w : ℕ → EF) (f : DeferralFunction) (θ : ℚ) (n : ℕ) : EF :=
  chainList ((List.range n).map (fireExpr w f θ)) (fireExpr w f θ n)

/-! ## C. Denotation laws of the pieces -/

/-- `openInd` denotes `1[j < f m]` at the paired index `⟨j, m⟩`, in every environment.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openInd_denoteWith (f : DeferralFunction) (j m : ℕ) (ρ : List ℝ) (V : History) :
    (openInd f (Nat.pair j m)).denoteWith ρ V = if j < f.f m then 1 else 0 := by
  by_cases h : j < f.f m
  · simp [openInd, openCount_eq_zero_iff, h]
  · simp [openInd, openCount_eq_zero_iff, h]

/-- A summand denotes `1[j < f m] · ρ[j − 1 − m]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pieceTerm_denoteWith (f : DeferralFunction) (j m : ℕ) (ρ : List ℝ) (V : History) :
    (pieceTerm f (Nat.pair j m)).denoteWith ρ V =
      (if j < f.f m then 1 else 0) * ρ.getD (j - 1 - m) 0 := by
  simp only [pieceTerm, EF.denoteWith_mul, EF.denoteWith_var, Nat.unpair_pair, openInd_denoteWith]

/-- The partial open sum denotes `∑_{i < m} 1[j < f i] · ρ[j − 1 − i]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openExprAux_denoteWith (f : DeferralFunction) (j : ℕ) (ρ : List ℝ) (V : History) :
    ∀ m, (openExprAux f j m).denoteWith ρ V =
      ∑ i ∈ Finset.range m, (if j < f.f i then 1 else 0) * ρ.getD (j - 1 - i) 0
  | 0 => by simp [openExprAux]
  | m + 1 => by
      rw [openExprAux, EF.denoteWith_add, openExprAux_denoteWith f j ρ V m, pieceTerm_denoteWith,
        Finset.sum_range_succ]

/-- The ramp is environment-independent when `w` is closed (as every `PGenerableWeighting` is).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ramp_denoteWith {w : ℕ → EF} (hw : PGenerableWeighting w) (θ : ℚ) (n : ℕ) (ρ : List ℝ)
    (V : History) : (ramp θ w n).denoteWith ρ V = (ramp θ w n).denote V := by
  simp [ramp, ctsIndFeature, clip01, efMin, EF.denoteWith, hw.closed n ρ V]

/-- The ramp denotes `ctsInd (θ/2) (w n) (θ/2)` (K4: `ctsInd δ x y = clip01 ((x − y)/δ)`).
Source: [[fa-adaptive-joint-mandate]] K4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ramp_denote (w : ℕ → EF) {θ : ℚ} (hθ : 0 < θ) (n : ℕ) (V : History) :
    (ramp θ w n).denote V = ctsInd (θ / 2) ((w n).denote V) ((θ / 2 : ℚ) : ℝ) := by
  rw [ramp, ctsIndFeature_denote _ _ _ (fun _ => half_pos hθ)]
  simp

/-! ## D. Evaluating the chain: the environment of earlier firings -/

/-- Sequential evaluation of a list of bindings on top of an environment: the environment the
body of `chainList xs b` is evaluated in.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def evalEnv (V : History) : List EF → List ℝ → List ℝ
  | [], ρ => ρ
  | a :: xs, ρ => evalEnv V xs (a.denoteWith ρ V :: ρ)

/-- `chainList xs b` denotes `b` in the sequentially extended environment.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem chainList_denoteWith (V : History) : ∀ (xs : List EF) (b : EF) (ρ : List ℝ),
    (chainList xs b).denoteWith ρ V = b.denoteWith (evalEnv V xs ρ) V
  | [], _, _ => rfl
  | a :: xs, b, ρ => by
      rw [chainList, EF.denoteWith_letE, chainList_denoteWith V xs b]
      rfl

/-- Appending one binding evaluates it last, on top of the others' environment.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem evalEnv_append_singleton (V : History) (xs : List EF) (a : EF) :
    ∀ ρ : List ℝ, evalEnv V (xs ++ [a]) ρ = a.denoteWith (evalEnv V xs ρ) V :: evalEnv V xs ρ := by
  induction xs with
  | nil => intro ρ; rfl
  | cons x xs ih => intro ρ; exact ih _

/-- A feature depends only on the first `k` entries of its environment.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def DependsBelow (e : EF) (k : ℕ) : Prop :=
  ∀ (ρ ρ' : List ℝ) (V : History), (∀ i < k, ρ.getD i 0 = ρ'.getD i 0) →
    e.denoteWith ρ V = e.denoteWith ρ' V

/-- The day-`j` binding refers only to `var i` with `i < j` (the earlier firings) and to the closed
feature `w j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem fireExpr_dependsBelow {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) (j : ℕ) : DependsBelow (fireExpr w f θ j) j := by
  intro ρ ρ' V hρ
  have hsum : (openExpr f j).denoteWith ρ V = (openExpr f j).denoteWith ρ' V := by
    rw [openExpr, openExprAux_denoteWith, openExprAux_denoteWith]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [hρ (j - 1 - i) (by have := Finset.mem_range.1 hi; omega)]
  simp only [fireExpr, oneMinus, EF.denoteWith_mul, EF.denoteWith_add, EF.denoteWith_const, hsum,
    ramp_denoteWith hw]

/-- The environment of the first `n` firings of a binding family `x`: `[v_{n−1}, …, v_0]`, each
`v_k` the value of `x k` in the environment of the earlier ones.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def adaptEnv (x : ℕ → EF) (V : History) : ℕ → List ℝ
  | 0 => []
  | n + 1 => (x n).denoteWith (adaptEnv x V n) V :: adaptEnv x V n

/-- The value of the day-`n` binding in the environment of the earlier ones.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def envVal (x : ℕ → EF) (V : History) (n : ℕ) : ℝ :=
  (x n).denoteWith (adaptEnv x V n) V

/-- `adaptEnv x V n` has length `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem adaptEnv_length (x : ℕ → EF) (V : History) : ∀ n, (adaptEnv x V n).length = n
  | 0 => rfl
  | n + 1 => by rw [adaptEnv, List.length_cons, adaptEnv_length x V n]

/-- Entry `n − 1 − i` of `adaptEnv x V n` is the day-`i` value, for `i < n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem adaptEnv_getD (x : ℕ → EF) (V : History) :
    ∀ n i, i < n → (adaptEnv x V n).getD (n - 1 - i) 0 = envVal x V i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
      · have hidx : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
        rw [hidx, adaptEnv, List.getD_cons_succ]
        exact adaptEnv_getD x V n i h
      · have hidx : i + 1 - 1 - i = 0 := by omega
        rw [hidx, adaptEnv, List.getD_cons_zero]
        rfl

/-- Evaluating the first `n` bindings on top of `ρ` gives `adaptEnv x V n ++ ρ`, provided each
binding reads only the earlier ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem evalEnv_range (x : ℕ → EF) (hx : ∀ k, DependsBelow (x k) k) (V : History) (ρ : List ℝ) :
    ∀ n, evalEnv V ((List.range n).map x) ρ = adaptEnv x V n ++ ρ
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.map_singleton, evalEnv_append_singleton,
        evalEnv_range x hx V ρ n, adaptEnv, List.cons_append]
      congr 1
      refine hx n _ _ V (fun i hi => ?_)
      rw [List.getD_append _ _ _ _ (by rw [adaptEnv_length]; exact hi)]

/-- **The chain evaluates to the day-`n` value, in every environment.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem chainList_range_denoteWith (x : ℕ → EF) (hx : ∀ k, DependsBelow (x k) k) (V : History)
    (n : ℕ) (ρ : List ℝ) :
    (chainList ((List.range n).map x) (x n)).denoteWith ρ V = envVal x V n := by
  rw [chainList_denoteWith, evalEnv_range x hx V ρ n, envVal]
  refine hx n _ _ V (fun i hi => ?_)
  rw [List.getD_append _ _ _ _ (by rw [adaptEnv_length]; exact hi)]

/-! ## E. The real-valued firing sequence and its recursion law -/

/-- The open position of a real weighting on day `n` under lookahead `f`:
`openMass f u n = ∑_{m < n, n < f m} u m`.
Source: [[fa-adaptive-joint-mandate]] § Definitions (`OnePosition`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def openMass (f : ℕ → ℕ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, if n < f m then u m else 0

/-- **One-position structure** of a real weighting: nonnegative, and the pieces open on any day
sum to at most `1`. (Not the hard "at most one `u m ≠ 0` per window" — mandate T4 trap.)
Source: [[fa-adaptive-joint-mandate]] § Definitions; vq-wiki-057 Theorem 5.2 ("one position at a time")
Kind: D
Fidelity: exact
Hyps: n/a -/
def OnePosition (f : DeferralFunction) (u : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ u n ∧ openMass f.f u n ≤ 1

/-- **The recursion law of the softened machine** on real sequences: `u` is the firing sequence of
`w` under lookahead `f` and threshold `θ` iff `u n = (1 − openMass f u n) · ctsInd (θ/2) (w n) (θ/2)`
for every `n`. The T2 interface: everything in `Counting.lean` is stated over it, and
`adaptFireR` satisfies it (`adaptFireR_fireRec`).
Source: [[fa-adaptive-joint-mandate]] § T1 (the denotation laws), § T2
Kind: D
Fidelity: exact
Hyps: n/a -/
def FireRec (f : ℕ → ℕ) (θ : ℚ) (w u : ℕ → ℝ) : Prop :=
  ∀ n, u n = (1 - openMass f u n) * ctsInd (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)

/-- The real value of the day-`n` firing on the market `V`: `adaptFire w f θ n` denotes it
(`adaptFire_denote`).
Source: [[fa-adaptive-joint-mandate]] § Definitions (`adaptFireR`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def adaptFireR (w : ℕ → EF) (f : DeferralFunction) (θ : ℚ) (V : History) :
    ℕ → ℝ :=
  envVal (fireExpr w f θ) V

/-- **`adaptFire` denotes the firing value in every environment** (hence it is closed).
Source: [[fa-adaptive-joint-mandate]] § T1 (`adaptFire_denote_eq`)
Kind: L
Fidelity: exact
Hyps: (a) `hw` -/
theorem adaptFire_denoteWith {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) (n : ℕ) (ρ : List ℝ) (V : History) :
    (adaptFire w f θ n).denoteWith ρ V = adaptFireR w f θ V n :=
  chainList_range_denoteWith _ (fireExpr_dependsBelow hw f θ) V n ρ

/-- `adaptFire` denotes the firing value.
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw` -/
theorem adaptFire_denote {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    (θ : ℚ) (n : ℕ) (V : History) :
    (adaptFire w f θ n).denote V = adaptFireR w f θ V n :=
  adaptFire_denoteWith hw f θ n [] V

/-- **The recursion law** `fire n = (1 − ∑_{m < n, n < f m} fire m) · ctsInd (θ/2) (w n) (θ/2)` holds
for the denoted firing sequence (mandate `adaptFire_denote_eq`).
Source: [[fa-adaptive-joint-mandate]] § T1 ("the denotation laws"); [[fa-positive-results-corrected-v3]] §4
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFireR_rec {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) (n : ℕ) :
    adaptFireR w f θ V n =
      (1 - openMass f.f (adaptFireR w f θ V) n) * ctsInd (θ / 2) ((w n).denote V) ((θ / 2 : ℚ) : ℝ) := by
  have hsum : (openExpr f n).denoteWith (adaptEnv (fireExpr w f θ) V n) V =
      openMass f.f (adaptFireR w f θ V) n := by
    rw [openExpr, openExprAux_denoteWith, openMass]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [adaptEnv_getD _ _ n i (Finset.mem_range.1 hi), boole_mul]
    rfl
  show (fireExpr w f θ n).denoteWith (adaptEnv (fireExpr w f θ) V n) V = _
  rw [fireExpr, EF.denoteWith_mul, oneMinus, EF.denoteWith_add, EF.denoteWith_mul,
    EF.denoteWith_const, EF.denoteWith_const, hsum, ramp_denoteWith hw, ramp_denote w hθ]
  push_cast
  ring

/-- `adaptFireR w f θ V` is the firing sequence of the real weighting `n ↦ (w n).denote V`.
Source: [[fa-adaptive-joint-mandate]] § T1, § T2
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFireR_fireRec {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) :
    FireRec f.f θ (fun n => (w n).denote V) (adaptFireR w f θ V) :=
  fun n => adaptFireR_rec hw f hθ V n

end Cleanroom.Fa.FaAdaptiveJoint
