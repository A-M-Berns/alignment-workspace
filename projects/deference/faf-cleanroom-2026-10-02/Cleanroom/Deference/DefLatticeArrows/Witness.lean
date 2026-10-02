import Cleanroom.Deference.DefLatticeArrows.Transfer
import Cleanroom.Deference.DefLatticeArrows.TowerToTrust
import Cleanroom.Deference.DefLatticeArrows.OneWay
import Cleanroom.Found.DefLattice.Witness

/-!
# Witnesses over the paper's inductor

Package `def-lattice-arrows`, file 15 — the only file importing
`Cleanroom.Found.DefLattice.Witness` (hence `Construction/Paper/Market`).

Over `P := liaHistory (paperDP T)` with the self-expert `Expert.self P (paperDP T) f`:

* **T6, all hypotheses (a), grade N−** (`transfer_witness`, `expert_bound_transfer_witness`):
  source `X n := literalIndicator (ψ (f n))` for the provable family
  `ψ m := ∼(⌜a_m⌝ ⋏ ∼⌜a_m⌝)` read at the deferred day (day-varying, e.c. when the deferral is a
  ruler); the ramp package from FAF's `thm:st` package at threshold `1 − ε` and width `ε/2`
  (`rampWitness`, slack `≡ 0`); the TT instance from `lic_self_trust` (`tt_witness`); and the
  expert's lower bound `hA : P_{f(n)}(ψ(f n)) ≳ₙ 1` from provability induction on `ψ`
  (`lic_provind_true`) along the deferred days. Conclusion: `E^H_n(X_n) ≳ₙ 1`, i.e. the
  novice's day-`n` price of the day-`f(n)` tautology tends to `1` — through the arrow.
  **Why N− (audit r1 fidelity B2):** the source is valued `1` in every consistent world, so
  the product `XW` and the weight `W` have the same world value, the TT instance reduces to
  the nonnegativity of `E^H_n(W_n)`, `hA` is provability induction on a theorem family, and
  the conclusion is `lic_provind_true` on `ψ ∘ f` directly — each hypothesis and the
  conclusion is separately trivial, and the transfer does no work. What the witness
  establishes is that the *full package* of `transfer_instance`/`expert_bound_transfer` is
  inhabited over the paper's inductor by FAF's closed conclusions, with a day-varying,
  machine-metered source and a genuinely late saturation day — and that this is the best
  available: FAF supplies no eventual expert lower bound `E*(X_n) ≳ₙ v` for a world-varying
  family (F11 (5)). The mandate prescribed this family and called it N+; STANDARDS §3's
  grade is N−.
* **T4, FAF-closed instance modulo the fold, grade N−** (`softAbove_witness_of_fold`): the
  Tower instance at `XW` from `lic_expected_future_expectations_closed` on the closed `cee`
  package (`paperDeferredExpectationQuoteCode`), the ramp package as above; `ExpertFoldAt`
  remains the one hypothesis. The conclusion is what `lic_self_trust` already gives, so this
  instantiates every other hypothesis of `softAbove_instance` on FAF's closed packages.
* **`TowerValued` for the self-expert, grade N+, no hypothesis** (`towerValued_self`; audit
  r1 adversarial N1): FAF's closed `cee` gives the Tower instance at FAF's own quote of any
  e.c. valued `X`, and `expect_reflects_congr` (T0) moves it to every reflecting `Y`. So the
  deference hypothesis of every predicate-level arrow *out of* the tower is (a) for the
  self-expert over `paperDP T`, and with `OneWay`'s existence clauses only the fold /
  self-endorsement clause remains (`softTotalTrustAbove_self_of_folds`,
  `softTotalTrustBelow_self_of_folds`, `condTower_self_of_folds`, `value_self_of_selfEndorses`).

Never a constant expert or an all-`⊤` source *syntactically* (def-lattice audit N3/N5); the T6
source's values are provable, hence `1` in every world — semantically all-`⊤`, which is why
its grade is N−: a family whose expert estimates are eventually `≥ v` without being provable
would need a fact FAF does not supply.
-/

namespace Cleanroom.Deference.DefLatticeArrows.Witness

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.DefLattice.Witness Cleanroom.Deference.DefLatticeArrows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The provable family `ψ m := ∼(⌜a_m⌝ ⋏ ∼⌜a_m⌝)` (a tautology at every day, day-varying).
Source: mandate Witnesses ("a provable family `φ`")
Kind: D
Fidelity: n/a -/
def tautFamily : ℕ → Sentence :=
  fun m => ∼((Formula.atom m : Sentence) ⋏ ∼(Formula.atom m : Sentence))

/-- The tautology family is machine-metered (from the atom family by `and` and `neg`).
Source: FAF `MachineSentenceCodes.and`, `.neg`, `machineSentenceCodes_atom`
Kind: L
Fidelity: n/a -/
theorem tautFamily_codes : MachineSentenceCodes tautFamily :=
  (machineSentenceCodes_atom.and machineSentenceCodes_atom.neg).neg

/-- Every world holds every member of the tautology family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tautFamily_holds (v : PCWorld) (m : ℕ) : v.Holds (tautFamily m) := by
  simp [tautFamily, PCWorld.holds_neg, PCWorld.holds_and]

/-- The deferred source family `φ n := ψ (f n)`; machine-metered when the deferral is a ruler.
Source: mandate Witnesses
Kind: L
Fidelity: n/a -/
theorem deferredTaut_codes (f : DeferralFunction) (hf : UnaryRuler f.f) :
    MachineSentenceCodes (fun n => tautFamily (f n)) :=
  tautFamily_codes.comp hf

variable (f : DeferralFunction) (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (δ s : ℚ)

/-- FAF's confidence-quote code of the paper market at the deferred day, for the family `φ`.
Source: FAF `paperConfidenceQuoteCode`; def-lattice `Witness.confidenceCode` generalised
Kind: D
Fidelity: n/a -/
def confCode :=
  paperConfidenceQuoteCode T f φ hφ (fun _ => δ) (fun _ => s)
    (MachineRatCodes.const δ).computable (sGenerable T s)

/-- The weight LUV `W n = ⌜ctsind_δ(P_{f(n)}(φ_n) > s)⌝`.
Source: FAF `RationalQuoteCode.luv`
Kind: D
Fidelity: n/a -/
def wW (n : ℕ) : LUV := (confCode T f φ hφ δ s).luv n

/-- The product LUV `XW n = ⌜1(φ_n) · ctsind_δ(…)⌝`.
Source: FAF `indicatorProductLUV`
Kind: D
Fidelity: n/a -/
def wXW (n : ℕ) : LUV := indicatorProductLUV (confCode T f φ hφ δ s) φ n

omit [Entailment.Consistent T] in
/-- The weight quote reflects the ramp of the deferred price.
Source: FAF `RationalQuoteCode.reflected`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
theorem wW_reflected (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (wW T f φ hφ δ s n)
      (ctsInd ((fun _ => δ) n) (liaHistory (paperDP T) (f n) (φ n)) (((fun _ => s) n : ℚ) : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (confCode T f φ hφ δ s)
    n v hv
  rwa [← paperConfidence_value_cast T f φ (fun _ => δ) (fun _ => s) n] at h

omit [Entailment.Consistent T] in
/-- The product quote reflects `payout(φ_n) · ramp`.
Source: FAF `indicatorProductLUV_valuesAt`, `paperConfidence_value_cast`
Kind: L
Fidelity: n/a -/
theorem wXW_reflected (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (wXW T f φ hφ δ s n)
      (v.payout (φ n) *
        ctsInd ((fun _ => δ) n) (liaHistory (paperDP T) (f n) (φ n)) (((fun _ => s) n : ℚ) : ℝ)) := by
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T) (confCode T f φ hφ δ s)
    φ n v hv
  rwa [← paperConfidence_value_cast T f φ (fun _ => δ) (fun _ => s) n] at h

/-- FAF's complete `thm:st` package over the paper's inductor for the family `φ`, at constant
width `δ > 0` and threshold `s ∈ [0,1]`.
Source: FAF `selfTrustQuoteOfRepresentation`; def-lattice `selfTrustQuoteWitness` generalised
Kind: N+
Fidelity: n/a -/
def stWitness (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    SelfTrustQuote (liaHistory (paperDP T)) (paperDP T) f φ (fun _ => δ) (fun _ => s)
      (wXW T f φ hφ δ s) (wW T f φ hφ δ s) :=
  selfTrustQuoteOfRepresentation f φ (fun _ => δ) (fun _ => s) (wXW T f φ hφ δ s)
    (wW T f φ hφ δ s) (fun _ => hδ) (fun _ => hs) hφ (MachineRatCodes.const (1 / δ))
    (sGenerable T s).choose (sGenerable T s).choose_spec
    (indicatorProductLUV_machineThresholdCodeSeq _ hφ) (confCode T f φ hφ δ s).poly
    (wW_reflected T f φ hφ δ s) (wXW_reflected T f φ hφ δ s) (paperDP_hworld T)

/-- **The ramp `WeightQuote` for the self-expert on the literal-indicator source of `φ`** —
FAF's `st` package projected, slack `≡ 0`.
Source: def-lattice `WeightQuote.of_selfTrustQuote`; mandate Witnesses
Kind: N+
Fidelity: n/a -/
def rampWitness (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) (rampAbove δ s) (wW T f φ hφ δ s) (wXW T f φ hφ δ s) :=
  WeightQuote.of_selfTrustQuote (stWitness T f φ hφ δ s hδ hs)

/-- **The soft Total-Trust instance on the witness package**: `lic_self_trust` in product form.
Source: FAF `lic_self_trust`; def-lattice `witness_selfTrust_productForm` generalised
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem tt_witness (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1) :
    (fun n => (wXW T f φ hφ δ s n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (wW T f φ hφ δ s n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  have h := lic_self_trust (liaHistory (paperDP T)) (paperDP T) f φ (fun _ => δ) (fun _ => s)
    (wXW T f φ hφ δ s) (wW T f φ hφ δ s) (paperDP_hworld T) (stWitness T f φ hφ δ s hδ hs)
  exact (soft_above_iff_unnormalized (liaHistory (paperDP T)) s _ _).mpr h

/-! ### T6: the fully-(a) witness -/

/-- **The expert's lower bound on the deferred tautology family** (a): provability induction
on `ψ` (`lic_provind_true`) along the deferred days, read through `literalIndicator_expect`.
Source: FAF `lic_provind_true`; mandate Witnesses ("`hA` from provability induction on the
future prices")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem hA_witness :
    (fun n => (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate
      (fun n => literalIndicator (tautFamily (f n))) n) ≳ₙ (fun _ => ((1 : ℚ) : ℝ)) := by
  have h := lic_provind_true (liaHistory (paperDP T)) (paperDP T) tautFamily tautFamily_codes
    (fun m v _ => tautFamily_holds v m) (paperDP_hworld T)
  have h' := asympEq_comp_deferral h f
  have heq : (fun n => (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate
      (fun n => literalIndicator (tautFamily (f n))) n) =
      fun n => liaHistory (paperDP T) (f n) (tautFamily (f n)) := by
    funext n
    simp [Expert.estimate, literalIndicator_expect]
  rw [heq]
  push_cast
  exact h'.asympGE

/-- **T6's per-instance transfer over the paper's inductor, every hypothesis (a), N−**: for a
ruler deferral `f` and `0 < ε ≤ 1`, the ramp package at threshold `1 − ε`, width `ε/2`, its TT
instance (`lic_self_trust`) and `hA` (provability induction) give
`E^H_n(literalIndicator (ψ (f n))) ≳ₙ 1 − ε`. N− because the source is valued `1` in every
consistent world: the TT instance, `hA` and the conclusion are each independently trivial
(the conclusion is `lic_provind_true` on `ψ ∘ f`), so the arrow's content is not exercised;
the package is inhabited by FAF's closed conclusions over the real inductor, and FAF has no
non-provable eventual lower bound to do better with (audit r1 fidelity B2; module docstring).
Source: mandate Witnesses (the prescribed provable-family witness of T6; the mandate's "N+"
conflicts with STANDARDS §3, which wins)
Kind: N−
Fidelity: exact
Hyps: (a) — `hf : UnaryRuler f.f` (the deferral is a ruler, e.g. `succDeferral`) -/
theorem transfer_witness (hf : UnaryRuler f.f) {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (fun n => (literalIndicator (tautFamily (f n))).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => ((1 - ε : ℚ) : ℝ)) :=
  transfer_instance (v := 1) (ε := ε) (δ := ε / 2) (by positivity) (by linarith)
    (literalIndicator_machineThresholdCodeSeq (deferredTaut_codes f hf))
    (rampWitness T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε) (by positivity)
      ⟨by linarith, by linarith⟩)
    (tt_witness T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε) (by positivity)
      ⟨by linarith, by linarith⟩)
    (hA_witness T f) (paperDP_hworld T)

/-- **T6's headline over the paper's inductor, every hypothesis (a), N−**:
`E^H_n(literalIndicator (ψ (f n))) ≳ₙ 1` — the novice's day-`n` price of the day-`f(n)`
tautology tends to `1`, through bounds transfer (packages at every `ε ≤ 1`). N− for the
reason `transfer_witness` gives: the source is world-constant, so the conclusion is also
`lic_provind_true` directly; the instance shows the full hypothesis package is jointly
inhabited over the real inductor, not that the arrow is needed.
Source: mandate Witnesses (the prescribed provable-family witness of T6)
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem expert_bound_transfer_witness (hf : UnaryRuler f.f) :
    (fun n => (literalIndicator (tautFamily (f n))).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => ((1 : ℚ) : ℝ)) :=
  expert_bound_transfer (v := 1) (literalIndicator_machineThresholdCodeSeq (deferredTaut_codes f hf))
    one_pos
    (fun ε hε hε1 => ⟨ε / 2, by positivity, by linarith, wW T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε),
      wXW T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε),
      rampWitness T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε) (by positivity)
        ⟨by linarith, by linarith⟩,
      tt_witness T f _ (deferredTaut_codes f hf) (ε / 2) (1 - ε) (by positivity)
        ⟨by linarith, by linarith⟩⟩)
    (hA_witness T f) (paperDP_hworld T)

/-- The successor deferral is a ruler.
Source: FAF `succDeferral`; `UnaryRuler.succ`
Kind: L
Fidelity: n/a -/
theorem succDeferral_ruler : UnaryRuler succDeferral.f := UnaryRuler.id.succ

/-- The T6 witness instantiated at the successor deferral: no hypothesis at all (N−, as its
parent: world-constant source).
Source: mandate Witnesses
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem expert_bound_transfer_witness_succ :
    (fun n => (literalIndicator (tautFamily (succDeferral n))).expect (liaHistory (paperDP T)) n)
      ≳ₙ (fun _ => ((1 : ℚ) : ℝ)) :=
  expert_bound_transfer_witness T succDeferral succDeferral_ruler

/-! ### T4: the FAF-closed instance modulo the fold -/

omit [Entailment.Consistent T] in
/-- The product LUV of the witness is e.c.
Source: FAF `indicatorProductLUV_machineThresholdCodeSeq`
Kind: L
Fidelity: n/a -/
theorem wXW_codes : LUV.MachineThresholdCodeSeq (wXW T f φ hφ δ s) :=
  indicatorProductLUV_machineThresholdCodeSeq _ hφ

omit [Entailment.Consistent T] in
/-- The product LUV of the witness is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem wXW_valued : Valued (paperDP T) (wXW T f φ hφ δ s) :=
  fun n v hv => ⟨_, wXW_reflected T f φ hφ δ s n v hv⟩

omit [Entailment.Consistent T] in
/-- **FAF's closed `cee` quote of the product reflects the self-expert's estimate**: the
`Reflects` clause for `paperDeferredExpectationQuoteCode` on `XW`.
Source: FAF `paperDeferredExpectationQuoteCode`, `RationalQuoteCode.reflected`,
`MarketComputation.expectQuoteAt_cast`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem ceeQuote_reflects :
    Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) (wXW T f φ hφ δ s)
      ((paperDeferredExpectationQuoteCode T f (wXW T f φ hφ δ s) (wXW_codes T f φ hφ δ s)).luv) := by
  intro n v hv
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperDeferredExpectationQuoteCode T f (wXW T f φ hφ δ s) (wXW_codes T f φ hφ δ s)) n v hv
  rwa [← (paperMarketComputation T).expectQuoteAt_cast (wXW T f φ hφ δ s) n (f.f n)] at h

/-- **T4's above half on FAF's closed packages, modulo the fold (N−)**: the Tower instance at
`XW` is `lic_expected_future_expectations_closed` (closed `cee`), the ramp package is FAF's
closed `st` package, and `ExpertFoldAt` is the one remaining hypothesis (the self-expert's fold
at the deferred day, a pull-back FAF does not provide). The conclusion coincides with
`tt_witness`, which `lic_self_trust` proves without the fold: this row instantiates every
*other* hypothesis of `softAbove_instance` on FAF's closed packages and no more.
Source: mandate Witnesses ("attempt one FAF-closed instance of T4's above half")
Kind: N−
Fidelity: exact
Hyps: (b) `hfold` (`ExpertFoldAt` for the self-expert, not discharged); (a) otherwise -/
theorem softAbove_witness_of_fold (hδ : 0 < δ) (hs : 0 ≤ s ∧ s ≤ 1)
    (hfold : ExpertFoldAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (fun n => literalIndicator (φ n)) (rampAbove δ s) (wXW T f φ hφ δ s)) :
    (fun n => (wXW T f φ hφ δ s n).expect (liaHistory (paperDP T)) n -
        (s : ℝ) * (wW T f φ hφ δ s n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) :=
  softAbove_instance hδ (rampWitness T f φ hφ δ s hδ hs)
    (paperDeferredExpectationQuoteCode T f (wXW T f φ hφ δ s) (wXW_codes T f φ hφ δ s)).poly
    (ceeQuote_reflects T f φ hφ δ s)
    (lic_expected_future_expectations_closed T f (wXW T f φ hφ δ s) (wXW_codes T f φ hφ δ s)
      (wXW_valued T f φ hφ δ s))
    hfold (paperDP_hworld T)

/-! ### T13: the self-expert's quotes -/

omit [Entailment.Consistent T] in
/-- **The self-expert's quotes exist** (a): the paper market is a computable market
(`paperMarketComputation T`), so `OneWay.quotesAvailable_of_marketComputation` applies.
Source: FAF `paperMarketComputation` (`Construction/Paper/Market.lean`); mandate T13
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quotesAvailable_self :
    QuotesAvailable (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  quotesAvailable_of_marketComputation T _ (paperMarketComputation T)

/-! ### `TowerValued` for the self-expert is a theorem (audit r1 adversarial N1) -/

omit [Entailment.Consistent T] in
/-- **FAF's closed `cee` quote of any e.c. `X` reflects the self-expert's estimate**: the
`Reflects` clause of `paperDeferredExpectationQuoteCode T f X hX`, `X` general
(`ceeQuote_reflects` is the case `X = wXW`).
Source: FAF `paperDeferredExpectationQuoteCode`, `RationalQuoteCode.reflected`,
`MarketComputation.expectQuoteAt_cast`; audit r1 adversarial N1 (probe `TowerValuedSelf.lean`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem closedQuote_reflects (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) :
    Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
      ((paperDeferredExpectationQuoteCode T f X hX).luv) := by
  intro n v hv
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperDeferredExpectationQuoteCode T f X hX) n v hv
  rwa [← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

/-- **`TowerValued` holds for the self-expert over the paper's inductor, at every deferral,
with no hypothesis**: FAF's closed `cee` (`lic_expected_future_expectations_closed`) gives the
Tower instance at FAF's own quote of `X`, and `expect_reflects_congr` (T0) moves it to any e.c.
`Y` reflecting the same estimates. No fold, no pull-back. (The package's design decision 1
said the tower "has no known inhabitant over an inductor": true of FAF's *open* `cee`, which
consumes an `affine` certificate, false of the closed one, which builds it — for
`TowerValued`; def-lattice's `Tower` also ranges over unvalued sources, which the closed `cee`
does not cover.)
Source: FAF `lic_expected_future_expectations_closed`; audit r1 adversarial N1 (probe
`TowerValuedSelf.lean`)
Kind: N+
Fidelity: exact (`TowerValued`; `Tower` proper not claimed)
Hyps: (a) none -/
theorem towerValued_self :
    TowerValued (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) := by
  intro X Y hX hY hval hR
  have h1 := lic_expected_future_expectations_closed T f X hX hval
  have h2 := expect_reflects_congr (P := liaHistory (paperDP T)) (DP := paperDP T)
    (paperDeferredExpectationQuoteCode T f X hX).poly hY (closedQuote_reflects T f X hX) hR
    (paperDP_hworld T)
  exact h1.trans h2

/-- **T4 above half for the self-expert over the paper's inductor**: every hypothesis but the
fold is (a) — `TowerValued` by `towerValued_self`, the product quotes by `OneWay`.
Source: [[tower-implies-total-trust]]; audit r1 adversarial N1
Kind: L
Fidelity: exact
Hyps: (b) `ExpertFoldsAt` (the self-expert's folds at the deferred day, F8); (a) otherwise -/
theorem softTotalTrustAbove_self_of_folds {s δ : ℚ} (hδ : 0 < δ)
    (hf : ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (rampAbove δ s)) :
    SoftTotalTrustAbove (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ :=
  softTotalTrustAbove_of_towerValued (towerValued_self T f) hδ
    (productQuotesAvailable_of_marketComputation T _ (paperMarketComputation T) _) hf
    (paperDP_hworld T)

/-- **T4 below half for the self-expert**, likewise.
Source: [[tower-implies-total-trust]]; audit r1 adversarial N1
Kind: L
Fidelity: exact
Hyps: (b) `ExpertFoldsAt`; (a) otherwise -/
theorem softTotalTrustBelow_self_of_folds {s δ : ℚ} (hδ : 0 < δ)
    (hf : ExpertFoldsAt (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
      (rampBelow δ s)) :
    SoftTotalTrustBelow (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) s δ :=
  softTotalTrustBelow_of_towerValued (towerValued_self T f) hδ
    (productQuotesAvailable_of_marketComputation T _ (paperMarketComputation T) _) hf
    (paperDP_hworld T)

/-- **T3 for the self-expert**: `CondTower` from the folds alone.
Source: v6 §1.5; audit r1 adversarial N1
Kind: L
Fidelity: exact
Hyps: (b) `ExpertFoldsCond`; (a) otherwise -/
theorem condTower_self_of_folds
    (hf : ExpertFoldsCond (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) :
    CondTower (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  condTower_of_towerValued (towerValued_self T f)
    (condQuotesReflected_of_marketComputation T _ (paperMarketComputation T)) hf
    (paperDP_hworld T)

/-- **T2 for the self-expert**: `Value` from `SelfEndorses` alone (the H3-laden clause).
Source: v6 §1.1; audit r1 adversarial N1
Kind: L
Fidelity: exact
Hyps: (c) `SelfEndorses` (H3-laden; `def-argmax-value`); (a) otherwise -/
theorem value_self_of_selfEndorses
    (hSE : SelfEndorses (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) :
    Value (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  value_of_towerValued_of_selfEndorse (towerValued_self T f)
    (quotesAvailable_self T f) hSE (paperDP_hworld T)

end

end Cleanroom.Deference.DefLatticeArrows.Witness
