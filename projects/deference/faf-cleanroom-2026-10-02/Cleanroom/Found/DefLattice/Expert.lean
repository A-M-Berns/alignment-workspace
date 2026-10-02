import LogicalInduction.Properties.SelfTrust

/-!
# The deference lattice over FAF — the expert, reflection, the quote packages

Package `def-lattice` (faf-cleanroom run, 2026-09-29), file 1 of the *definitions module*
(with `Notions.lean`, `Menu.lean`, `BetClass.lean`). Everything a dependent needs to *state* a
deference notion over FAF's objects is defined here:

* `Expert DP` — the expert is a history `A` plus a deferral function `f` (design decision 1 of
  the mandate); its estimate of the day-`n` bet `X n` is the real `(X n).expect A (f n)`. The
  self-instance `Expert.self P DP f` has `A = P`.
* `Reflects DP E X Y` — "`Y` is the corner-quote LUV `⌜E*(X)⌝`": every completed-theory world
  values `Y n` at the expert's estimate (the `reflected` field of FAF's
  `ExpectedFutureExpectationQuote`, so the self-instance is a projection).
* `WeightQuote DP E X wt W XW` — a weight LUV `W` reflecting `wt (E*(X n))` exactly and a
  product LUV `XW` reflecting `x · wt (E*(X n))` within FAF's vanishing `dd:mesh` slack
  (design decisions 3–4); `CondQuote` — the same for a P-generable weight sequence (`ccee`
  shape, FAF's `ConditionalExpectationQuote` minus its `affine` certificate).
* The weight functions of record (`rampAbove`, `rampBelow`, `hardAbove`, `hardBelow`,
  `bandWt`, `hardBand`) and the literal-threshold indicator LUV `literalIndicator φ`, whose
  day-`m` expectation is *exactly* the price `P m φ` — the source for which FAF's `thm:st`
  package projects to a `WeightQuote` with `slack ≡ 0`.

Conventions (binding, from the mandate): FAF's `LUV` is `[0,1]`-valued and threshold-presented;
thresholds and widths are rationals; nothing here assumes a quote *exists* (that is
`li-quote-lane`'s and FAF's `Construction/Quotation`'s job) — every notion in `Notions.lean`
quantifies universally over the quote LUVs satisfying the reflection clauses.

FAF pin `159ec3f`; imports are the narrow `Properties.SelfTrust` (which brings `Expectations`,
`Asymptotics`, `ThresholdMachine`, `ctsInd`, the quote structures).
-/

namespace Cleanroom.Found.DefLattice

open LogicalInduction Filter Topology

noncomputable section

/-! ## The expert -/

/-- **The expert of record.** A history `A` (the expert's prices) with a deferral function
`f` and the `[0,1]` price range that `PCWorld.ValuesAt` demands of every reflected value. The
expert's estimate of the day-`n` bet `X n` is `(X n).expect A (f n)` (`Expert.estimate`): the
deferred-day expectation, read by the novice at day `n`. `DP` is a phantom index recording the
deductive process the expert's quotes are reflected against (`Reflects`, `WeightQuote`).
No `IsLogicalInductor` is demanded of a general expert (dependents add it when they need it;
`Expert.self` supplies the range from the novice's own certificate). Without `range`, the
reflection clause `v.ValuesAt (Y n) (E.estimate X n)` (which forces `0 ≤ · ≤ 1`) would be
unsatisfiable and every notion in `Notions.lean` vacuously true.
Source: [[deference-notions]] §Setting; [[expert-conditions]] §The three conditions;
[[deference-in-logical-induction-v6]] §0.4 (the two canonical instances)
Kind: D
Fidelity: variant: the corpus's same-day publication `e(n) = n` is not representable
(`DeferralFunction.lt` forces `f n > n`); the AI instance reads the deferred-day estimate
(finding F1 of `def-lattice-findings`). -/
structure Expert (DP : DeductiveProcess) where
  /-- the expert's history (its day-by-day prices) -/
  A : History
  /-- the deferral: the expert's day-`f n` estimate is what the novice reads at day `n` -/
  f : DeferralFunction
  /-- the expert prices in `[0,1]` (free for an inductor, `IsLogicalInductor.price_mem_Icc`) -/
  range : ∀ n s, 0 ≤ A n s ∧ A n s ≤ 1

namespace Expert

variable {DP : DeductiveProcess}

/-- The expert's estimate of the day-`n` bet: `E*(X n) := (X n).expect E.A (E.f n)` — the
corpus's `E^*(X_n)`, the number the quote LUV `⌜E^*(X_n)⌝` names.
Source: [[deference-notions]] §Setting; [[setting-and-notation]] §Corner quotes
Kind: D
Fidelity: exact (over FAF's grid expectation `LUV.expect`, precision `f n + 1`) -/
abbrev estimate (E : Expert DP) (X : ℕ → LUV) (n : ℕ) : ℝ := (X n).expect E.A (E.f n)

/-- The expert's estimate lies in `[0,1]` (from `range` through `LUV.expect_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma estimate_mem_Icc (E : Expert DP) (X : ℕ → LUV) (n : ℕ) :
    0 ≤ E.estimate X n ∧ E.estimate X n ≤ 1 :=
  LUV.expect_mem_Icc E.A (E.f n) (X n) (E.range (E.f n))

/-- **The self-instance.** The novice's own future self `E^H_{f(n)}`: the expert whose history
is the novice's market `P`, with range from the inductor certificate.
Source: [[deference-notions]] §Setting (the future self `E* = E^H_{f(n)}`); v6 §0.4 instance 1
Kind: D
Fidelity: exact -/
def self (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (f : DeferralFunction) : Expert DP :=
  ⟨P, f, fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s⟩

/-- The self-expert's history is the novice's market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma self_A (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (f : DeferralFunction) : (self P DP f).A = P := rfl

/-- The self-expert's deferral is the given one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma self_f (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (f : DeferralFunction) : (self P DP f).f = f := rfl

/-- The self-expert's estimate is the market's own deferred-day expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma self_estimate (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (f : DeferralFunction) (X : ℕ → LUV) (n : ℕ) :
    (self P DP f).estimate X n = (X n).expect P (f n) := rfl

end Expert

/-! ## Reflection: quotes are data, reflected in every consistent world -/

/-- **The reflection clause.** `Y` is the corner-quote LUV sequence `⌜E*(X_n)⌝`: every world
consistent with the completed theory values `Y n` at the expert's estimate `E.estimate X n`.
This is exactly the `reflected` field of FAF's `ExpectedFutureExpectationQuote` (the
self-instance is `Reflects.of_expectedFutureExpectationQuote`). It asserts nothing about
*existence* of such a `Y` — the notions quantify over it universally.
Source: [[deference-notions]] §Mart ("`⌜E*(X_n)⌝`"); [[setting-and-notation]] §Observable
(the quote ledger: decided threshold atoms); FAF `Properties/SelfTrust.lean`
`ExpectedFutureExpectationQuote.reflected`
Kind: D
Fidelity: exact -/
def Reflects (DP : DeductiveProcess) (E : Expert DP) (X Y : ℕ → LUV) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Y n) (E.estimate X n)

/-- **Self-instance projection (T1).** FAF's `thm:cee` quote package reflects, in the sense of
`Reflects`, for the self-expert: it is the field `reflected` up to unfolding.
Source: FAF `ExpectedFutureExpectationQuote` (`Properties/SelfTrust.lean`); mandate T1
Kind: L
Fidelity: exact
Hyps: (a) the FAF package -/
theorem Reflects.of_expectedFutureExpectationQuote {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {f : DeferralFunction} {X Y : ℕ → LUV}
    (q : ExpectedFutureExpectationQuote P DP f X Y) :
    Reflects DP (Expert.self P DP f) X Y :=
  fun n v hv => q.reflected n v hv

/-- Every completed-theory world values every member of `X` (FAF's `source_valued` /
`hval` premise, `lem:conluvapprox`: "Θ represents computations, so every consistent world
assigns each LUV its true value"). Over FAF's threshold-only `LUV` this is a hypothesis, not
a fact: a family with inconsistent thresholds (all `⊤`, or non-monotone) is valued by no
world. The corpus's "e.d. LUV" (a formula `Γ` proves names a unique real) is
`LUV.MachineThresholdCodeSeq X ∧ Valued DP X`.
Source: [[setting-and-notation]] §LUV; FAF `ConditionalExpectationQuote.source_valued`
Kind: D
Fidelity: exact -/
def Valued (DP : DeductiveProcess) (X : ℕ → LUV) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x

/-! ## Weight functions of record -/

/-- The above-threshold ramp `q ↦ ctsind_δ(q > s)` = `min 1 (max 0 ((q − s)/δ))` (FAF
`ctsInd`, v6 §1.6's `Ind_δ(y > t)`: `0` for `y ≤ t`, linear on `(t, t+δ]`, `1` beyond).
`δ = 0` gives the zero weight (Lean: `x / 0 = 0`): a `WeightQuote` at `rampAbove 0 s` has its
quote LUVs valued `0`, so the threshold inequality at width `0` is content-free (true on any
inductor novice by `thm:expprovind`, though not syntactically `0 ≳ₙ 0` for an arbitrary
history). Hence every predicate at a fixed width takes `0 < δ`.
Source: [[deference-notions]] §Total Trust (`w_{t,δ}`); v6 §1.6 lines 236–244
Kind: D
Fidelity: exact (`ctsInd δ y t` is v6's `Ind_δ(y > t)` clause for clause) -/
abbrev rampAbove (δ s : ℚ) : ℝ → ℝ := fun q => ctsInd δ q s

/-- The below-threshold ramp `q ↦ ctsind_δ(s > q)` = v6's `Ind_δ(y < t) := Ind_δ(t − y)`.
Source: v6 §1.6 line 240 (`Ind_δ(y<t)`); [[centered-bet-squeeze]] §0 (`w^<`)
Kind: D
Fidelity: exact -/
abbrev rampBelow (δ s : ℚ) : ℝ → ℝ := fun q => ctsInd δ s q

/-- The hard above-threshold indicator `1[s ≤ q]` — DDB's cut, **not a generable weight**
(discontinuous; `Notions.lean`'s `HardTotalTrust*` are comparison objects, never hypotheses).
Source: [[Deference Done Better]] l. 175 (`E_π(X | E(X) ≥ t) ≥ t`)
Kind: D
Fidelity: exact -/
abbrev hardAbove (s : ℚ) : ℝ → ℝ := fun q => if (s : ℝ) ≤ q then 1 else 0

/-- The hard below-threshold indicator `1[q ≤ s]` (DDB's symmetric form, l. 180).
Source: [[Deference Done Better]] l. 180
Kind: D
Fidelity: exact -/
abbrev hardBelow (s : ℚ) : ℝ → ℝ := fun q => if q ≤ (s : ℝ) then 1 else 0

/-- The band weight `Ind_δ(q > s − ε) · Ind_δ(q < s + ε)` of [[reflection-in-li]] — one weight
function, the product of two ramps of the *same* quote (the mandate's T5 trap).
Source: [[reflection-in-li]] §The value form is a theorem (the display `b_n`)
Kind: D
Fidelity: exact -/
abbrev bandWt (δ s ε : ℚ) : ℝ → ℝ :=
  fun q => ctsInd δ q (s - ε) * ctsInd δ (s + ε) q

/-- The sharp band `1[q = s]` — the exact value-form Reflection's weight, a **refuted object**
(LI 4.12.4's discussion; [[reflection-in-li]] §What is genuinely unreachable).
Source: [[reflection-in-li]] §Exactness
Kind: D
Fidelity: exact -/
abbrev hardBand (s : ℚ) : ℝ → ℝ := fun q => if q = (s : ℝ) then 1 else 0

/-! ## The weight-quote package (design decision 4) -/

/-- **The weighted-product quote package.** For a source `X`, a weight function `wt` of the
expert's estimate, a weight LUV `W` and a product LUV `XW`:
`W n` is valued at `wt (E*(X n))` in every completed-theory world (exactly), and `XW n` is
valued within `slack n` of `x · wt (E*(X n))` whenever `X n` is valued at `x`, with
`slack → 0` — FAF's `dd:mesh` (`ConditionalExpectationQuote.left_reflected`): an exact
product of an arbitrary threshold-only source cannot be emitted ([[faf-map-li]] §5 gap 7),
and `slack ≡ 0` is the exact instance (inhabited for indicator sources:
`WeightQuote.of_selfTrustQuote`). Both quote LUVs are e.c. (`MachineThresholdCodeSeq`), and
the source is world-valued (`source_valued`, as FAF's `ccee` package demands; without it
`product_reflected` is vacuous for a junk source and the threshold inequalities of
`Notions.lean` would be refutable by an unvalued `X`). The FAF `affine` portfolio certificate
is deliberately absent: it is most of the theorem, not part of the hypothesis.
Instances: `rampAbove`/`rampBelow` (soft Total Trust), `hardAbove`/`hardBelow` (the hard
comparison object), `bandWt` (band Reflection).
Source: [[deference-notions]] §Total Trust (`X_n · w_{t,δ}`, `w_{t,δ}`); FAF
`ConditionalExpectationQuote`, `SelfTrustQuote` (`Properties/SelfTrust.lean`); mandate
design decisions 3–4
Kind: D
Fidelity: variant: product reflected within FAF's vanishing slack, not exactly (disclosed;
the corpus's exact product is the `slack ≡ 0` instance) -/
structure WeightQuote (DP : DeductiveProcess) (E : Expert DP) (X : ℕ → LUV) (wt : ℝ → ℝ)
    (W XW : ℕ → LUV) where
  /-- the weight LUV is efficiently describable -/
  weight_codes : LUV.MachineThresholdCodeSeq W
  /-- the product LUV is efficiently describable -/
  product_codes : LUV.MachineThresholdCodeSeq XW
  /-- the per-day reflection slack of the product (FAF's `dd:mesh`) -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- every completed-theory world values the source -/
  source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  /-- the weight LUV is valued at `wt` of the expert's estimate, exactly -/
  weight_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (W n) (wt (E.estimate X n))
  /-- the product LUV is valued within `slack n` of `x · wt (E*(X n))` when `X n` is valued
  at `x` -/
  product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (X n) x → ∃ z, v.ValuesAt (XW n) z ∧ |z - x * wt (E.estimate X n)| ≤ slack n

/-- **The conditional-tower quote package** (`ccee` shape): for a P-generable weight sequence
`w` (evaluated, as in FAF and LI 4.12.3, at the *deferred* day `w (E.f n)` — the wiki's `w_n`
is finding F2 of `def-lattice-findings`), `Z n` reflects `x · w (f n)` within `slack n` and
`Z' n` reflects `E*(X n) · w (f n)` exactly. This is FAF's `ConditionalExpectationQuote`
**minus** its `affine` field (the trader-portfolio certificate that *is* the theorem) and
minus the weight's membership/generability and the source codes, which `CondTower` carries in
its quantifier.
Source: [[deference-notions]] §The conditional tower; FAF `ConditionalExpectationQuote`
Kind: D
Fidelity: variant: left product within FAF's slack (as FAF; disclosed) -/
structure CondQuote (DP : DeductiveProcess) (E : Expert DP) (X : ℕ → LUV) (w : ℕ → ℚ)
    (Z Z' : ℕ → LUV) where
  /-- the left product `⌜X_n · w_{f(n)}⌝` is efficiently describable -/
  left_codes : LUV.MachineThresholdCodeSeq Z
  /-- the right product `⌜E*(X_n) · w_{f(n)}⌝` is efficiently describable -/
  right_codes : LUV.MachineThresholdCodeSeq Z'
  /-- the per-day reflection slack of the left product -/
  slack : ℕ → ℝ
  /-- the slack vanishes -/
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  /-- every completed-theory world values the source -/
  source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  /-- the left product is valued within `slack n` of `x · w (f n)` -/
  left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (X n) x → ∃ z, v.ValuesAt (Z n) z ∧ |z - x * (w (E.f n) : ℝ)| ≤ slack n
  /-- the right product is valued at `E*(X n) · w (f n)`, exactly -/
  right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Z' n) (E.estimate X n * (w (E.f n) : ℝ))

/-- **Self-instance projection (T2).** FAF's `thm:ccee` package is a `CondQuote` for the
self-expert, field by field.
Source: FAF `ConditionalExpectationQuote`; mandate T2
Kind: L
Fidelity: exact
Hyps: (a) the FAF package -/
def CondQuote.of_conditionalExpectationQuote {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {f : DeferralFunction} {X Z Z' : ℕ → LUV} {w : ℕ → ℚ}
    (q : ConditionalExpectationQuote P DP f X Z Z' w) :
    CondQuote DP (Expert.self P DP f) X w Z Z' where
  left_codes := q.left_codes
  right_codes := q.right_codes
  slack := q.slack
  slack_tendsto := q.slack_tendsto
  source_valued := q.source_valued
  left_reflected := q.left_reflected
  right_reflected := q.right_reflected

/-! ## The literal-threshold indicator: the source on which `thm:st` projects exactly -/

/-- The indicator LUV of `φ` with the threshold sentence `φ` *itself* on `[0,1)` (`⊤` below
`0`, `⊥` from `1`). Its day-`m` expectation is exactly the price `P m φ`
(`literalIndicator_expect`), which is what makes FAF's self-trust package — whose ramp is
taken at the future *price* `P (f n) (φ n)` — a `WeightQuote` for this source with `slack ≡ 0`
(`WeightQuote.of_selfTrustQuote`). FAF's own `LUV.indicatorOf φ` uses the syntactically
distinct `φ ⋏ ∼∼φ` so that `thm:ei` is not an identity; for *that* source the ramp arguments
differ (`P (f n) (φ n)` vs `P (f n) (φ n ⋏ ∼∼φ n)`) and the projection is only asymptotic
(finding F4 of `def-lattice-findings`).
Source: FAF `LUV.indicatorOf` (`Framework/Expectations.lean`) and its anti-triviality remark;
mandate T1
Kind: D
Fidelity: exact (the paper's `1(φ)` as a threshold family) -/
def literalIndicator (φ : Sentence) : LUV where
  gt r := if r < 0 then (⊤ : Sentence) else if r < 1 then φ else (⊥ : Sentence)

/-- `literalIndicator φ` is an indicator family for `φ` in FAF's sense, in every world.
Source: none: infrastructure (mirrors FAF `LUV.indicatorOf_isIndicator`)
Kind: L
Fidelity: n/a -/
lemma literalIndicator_isIndicator (φ : Sentence) (DP : DeductiveProcess) :
    (literalIndicator φ).IsIndicator φ DP := by
  intro v _ r
  have hr0 : ((r : ℝ) < 0) ↔ r < 0 := by exact_mod_cast Iff.rfl
  have hr1 : ((r : ℝ) < 1) ↔ r < 1 := by exact_mod_cast Iff.rfl
  refine ⟨fun h => ?_, fun hlo hhi => ?_, fun h => ?_⟩
  · simpa [literalIndicator, hr0.mp h] using PCWorld.holds_top v
  · have hlo' : ¬ r < 0 := fun hc => (not_lt.mpr hlo) (hr0.mpr hc)
    simp [literalIndicator, hlo', hr1.mp hhi]
  · have hlo' : ¬ r < 0 := fun hc => (not_lt.mpr (zero_le_one.trans h)) (hr0.mpr hc)
    have hhi' : ¬ r < 1 := fun hc => (not_lt.mpr h) (hr1.mpr hc)
    simp only [literalIndicator, if_neg hlo', if_neg hhi']
    simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- Every world values `literalIndicator φ` at its payout on `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma literalIndicator_valuesAt (φ : Sentence) (DP : DeductiveProcess) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) :
    v.ValuesAt (literalIndicator φ) (v.payout φ) :=
  (literalIndicator_isIndicator φ DP).valuesAt hv

/-- **The literal indicator's expectation is the price, exactly:** every grid threshold
`i/(m+1)`, `i ≤ m`, lies in `[0,1)`, so all `m+1` summands of `expectApprox` are `P m φ`.
Source: none: infrastructure (FAF `def:e`)
Kind: L
Fidelity: n/a -/
lemma literalIndicator_expect (P : History) (m : ℕ) (φ : Sentence) :
    (literalIndicator φ).expect P m = P m φ := by
  unfold LUV.expect LUV.expectApprox
  have h : ∀ i ∈ Finset.range (m + 1),
      P m ((literalIndicator φ).gt ((i : ℚ) / ((m + 1 : ℕ) : ℚ))) = P m φ := by
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    have h0 : ¬ ((i : ℚ) / ((m + 1 : ℕ) : ℚ) < 0) := by
      rw [not_lt]; positivity
    have h1 : (i : ℚ) / ((m + 1 : ℕ) : ℚ) < 1 := by
      rw [div_lt_one (by positivity)]
      exact_mod_cast hi'
    simp only [literalIndicator, if_neg h0, if_pos h1]
  rw [Finset.sum_congr rfl h]
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [inv_mul_cancel_left₀ hm]

/-- **The literal indicator family is machine-metered** from the sentence codes alone (the
adaptation of FAF's `LUV.indicatorOf_machineThresholdCodeSeq` with the `[0,1)` branch the
bare sentence instead of `φ ⋏ ∼∼φ`).
Source: none: infrastructure (FAF `Framework/Machine/ThresholdMachine.lean`)
Kind: L
Fidelity: n/a -/
lemma literalIndicator_machineThresholdCodeSeq {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    LUV.MachineThresholdCodeSeq (fun n => literalIndicator (φ n)) := by
  have hk : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairSnd
  have hi : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairSnd
  have ht : UnaryRuler (fun m : ℕ =>
      (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1) * m.unpair.2.unpair.1) :=
    (hi.succ.sub hk).mul hk
  have hbase : MachineSentenceCodes (fun m : ℕ => φ m.unpair.1) :=
    hφ.comp UnaryRuler.unpairFst
  show MachineSentenceCodes (fun m => (literalIndicator (φ m.unpair.1)).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  refine MachineSentenceCodes.of_eq
    (MachineSentenceCodes.ifZero hbase (MachineSentenceCodes.const (⊥ : Sentence)) ht)
    (fun m => ?_)
  have hnn : ¬ ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 0) :=
    not_lt.mpr (div_nonneg (by positivity) (by positivity))
  have hkey : ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 1) ↔
      (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1) * m.unpair.2.unpair.1 = 0 := by
    rcases Nat.eq_zero_or_pos m.unpair.2.unpair.1 with hk0 | hk0
    · simp [hk0]
    · rw [div_lt_one (by exact_mod_cast hk0)]
      constructor
      · intro h
        have hlt : m.unpair.2.unpair.2 < m.unpair.2.unpair.1 := by exact_mod_cast h
        simp [Nat.sub_eq_zero_of_le hlt]
      · intro h
        have hz : m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 = 0 := by
          rcases Nat.mul_eq_zero.mp h with h' | h'
          · exact h'
          · omega
        have hlt : m.unpair.2.unpair.2 < m.unpair.2.unpair.1 := by omega
        exact_mod_cast hlt
  by_cases hlt : (m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 1
  · rw [if_pos (hkey.mp hlt)]
    simp [literalIndicator, hnn, hlt]
  · rw [if_neg (fun hc => hlt (hkey.mpr hc))]
    simp [literalIndicator, hnn, hlt]

/-- **Self-instance projection (T1, the ramp instance, `slack ≡ 0`).** FAF's `thm:st` package
at constant width `δ` and constant threshold `s`, for the sentence source
`X n := literalIndicator (φ n)`, is a `WeightQuote` for the self-expert with the above-ramp
weight `rampAbove δ s`, weight LUV `B` and product LUV `A`, with no slack: the confidence
quote is valued at `ctsInd δ (P (f n) (φ n)) s = rampAbove δ s (E*(X n))` because
`(literalIndicator (φ n)).expect P (f n) = P (f n) (φ n)` exactly, and the product quote is
valued at `payout (φ n) · ctsInd …`, which is `x · rampAbove δ s (E*(X n))` for the unique
world value `x = payout (φ n)` of the source.
Source: FAF `SelfTrustQuote` (`Properties/SelfTrust.lean`); mandate T1
Kind: L
Fidelity: exact (for the literal indicator source; finding F4 for `LUV.indicatorOf`)
Hyps: (a) the FAF package -/
def WeightQuote.of_selfTrustQuote {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {f : DeferralFunction} {φ : ℕ → Sentence} {δ s : ℚ}
    {A B : ℕ → LUV} (q : SelfTrustQuote P DP f φ (fun _ => δ) (fun _ => s) A B) :
    WeightQuote DP (Expert.self P DP f) (fun n => literalIndicator (φ n)) (rampAbove δ s)
      B A where
  weight_codes := q.confidence_codes
  product_codes := q.product_codes
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  source_valued := fun n v hv => ⟨_, literalIndicator_valuesAt (φ n) DP hv⟩
  weight_reflected := fun n v hv => by
    simpa [Expert.estimate, literalIndicator_expect] using q.confidence_reflected n v hv
  product_reflected := fun n v hv x hx => by
    have hx' : x = v.payout (φ n) := hx.eq (literalIndicator_valuesAt (φ n) DP hv)
    refine ⟨v.payout (φ n) * ctsInd δ (P (f n) (φ n)) s, ?_, ?_⟩
    · simpa using q.product_reflected n v hv
    · simp [hx', Expert.estimate, literalIndicator_expect]

end

end Cleanroom.Found.DefLattice
