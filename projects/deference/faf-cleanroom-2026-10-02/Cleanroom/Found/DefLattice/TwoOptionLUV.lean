import Cleanroom.Found.DefLattice.Notions
import Cleanroom.Found.DefLattice.Menu
import LogicalInduction.Construction.LUV.Endpoints

/-!
# The two-option identity at the LUV level (T6c) and the bridge from `Value` (T6d)

Package `def-lattice`.

* **T6c (definitional).** `twoOptionComb s XW W n := s + XW_n − s·W_n` is the δ-hedged
  followed strategy `X·w + s·(1 − w)` of the menu `{X, const s}` as a `LUVCombination`; its
  day-`n` expectation is `E^H_n(XW_n) + s − s·E^H_n(W_n)` *by definition* of
  `LUVCombination.expect` (linear in the prices), so "Value against the constant on the hedged
  menu" — `E^H_n(twoOptionComb) ≳ₙ s` — **is** the product form
  `E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` of `ThresholdIneqAbove`, per `(X, s, δ)`. The corpus's
  `hLoe` hypothesis is dissolved, not discharged (finding F6). The content of "this combination
  is the followed strategy" is `WeightQuote`'s reflection clause.
* **T6d (composition, all hypotheses (a) except a disclosed FAF API gap).** On the two-option
  menu `{X, C}` with `C` valued `s` in every consistent world, `Value` gives the hard
  above-threshold inequality **at the expert's own quote of the constant** `q_n := E*(C_n)`:
  `E^H_n(X·1[q_n ≤ E*(X_n)]) − s·E^H_n(1[q_n ≤ E*(X_n)]) ≳ₙ 0`, and the below-threshold
  companion. Over FAF's grid expectation `q_n ≠ s` in general (finding F3), so the fixed-`s`
  form `HardTotalTrustAbove` is reached only under the surrogate reading `E*(C_n) = s`,
  disclosed as `(c)` in `value_twoOption_hardAbove_of_weightQuote`.
-/

namespace Cleanroom.Found.DefLattice

open LogicalInduction Filter Topology

noncomputable section

/-! ## T6c — the LUV combination form -/

/-- **The two-option (δ-hedged) followed strategy as a LUV combination:**
`s + 1·XW_n + (−s)·W_n` = "`X·w + s·(1 − w)`", with `XW` the product quote and `W` the weight
quote of `WeightQuote`. Constants enter through `LUVCombination.const` (FAF has no constant
LUV).
Source: [[two-option-value-iff-total-trust]] §Soft/LI form
(`Ŝ_{X,s,δ} := X·w_{s,δ} + s(1 − w_{s,δ})`); mandate T6c
Kind: D
Fidelity: exact -/
def twoOptionComb (s : ℚ) (XW W : ℕ → LUV) (n : ℕ) : LUVCombination :=
  ⟨EF.const s, [(EF.const 1, XW n), (EF.const (-s), W n)]⟩

/-- The day-`n` expectation of the hedged strategy is `E^H_n(XW_n) + s − s·E^H_n(W_n)` — by
definition of `LUVCombination.expect` (linear in the prices).
Source: mandate T6c; FAF `LUVCombination.expect`
Kind: L
Fidelity: exact -/
theorem twoOptionComb_expect (P : History) (s : ℚ) (XW W : ℕ → LUV) (n : ℕ) :
    (twoOptionComb s XW W n).expect P n =
      (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n := by
  simp [twoOptionComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]
  ring

/-- The world value of the hedged strategy under a LUV valuation `ν`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twoOptionComb_value (P : History) (s : ℚ) (XW W : ℕ → LUV) (n : ℕ) (ν : LUV → ℝ) :
    (twoOptionComb s XW W n).value P ν = ν (XW n) + (s : ℝ) - (s : ℝ) * ν (W n) := by
  simp [twoOptionComb, LUVCombination.value]
  ring

/-- **Value against the constant on the hedged menu *is* the product form** (T6c):
`E^H_n(twoOptionComb s XW W n) ≳ₙ s` ⟺ `E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0` — the conclusion of
`ThresholdIneqAbove` at this `(X, W, XW)`. Definitional: the content of "this combination is
the followed strategy" is `WeightQuote`'s reflection clause; no `loe` is needed (finding F6).
Source: [[two-option-value-iff-total-trust]] §Soft/LI form; mandate T6c
Kind: L
Fidelity: exact -/
theorem twoOptionComb_value_iff_productForm (P : History) (s : ℚ) (XW W : ℕ → LUV) :
    (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ)) ↔
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  simp only [twoOptionComb_expect]
  unfold AsympGE AsympLE
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    linarith

/-- Soft Total Trust above threshold at `(s, δ)` gives Value against the constant on every
hedged two-option menu at that `(s, δ)`, per `(X, W, XW)`.
Source: [[two-option-value-iff-total-trust]] §Soft/LI form
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem twoOptionComb_value_of_softTotalTrustAbove (P : History) (DP : DeductiveProcess)
    {E : Expert DP} {s δ : ℚ} (h : SoftTotalTrustAbove P DP E s δ) {X W XW : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (q : WeightQuote DP E X (rampAbove δ s) W XW) :
    (fun n => (twoOptionComb s XW W n).expect P n) ≳ₙ (fun _ => (s : ℝ)) :=
  (twoOptionComb_value_iff_productForm P s XW W).mpr (h X W XW hX q)

/-! ## World values: a canonical valuation for `WorldValued` -/

/-- The value a world assigns to a LUV, when it assigns one (junk `0` otherwise); the
canonical `ν : LUV → ℝ` that discharges `LUVCombination.WorldValued`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldValue (v : PCWorld) (L : LUV) : ℝ := by
  classical
  exact if h : ∃ x, v.ValuesAt L x then Classical.choose h else 0

/-- `worldValue` is the (unique) value whenever one exists.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldValue_eq {v : PCWorld} {L : LUV} {x : ℝ} (hx : v.ValuesAt L x) :
    worldValue v L = x := by
  have h : ∃ x, v.ValuesAt L x := ⟨x, hx⟩
  unfold worldValue
  simp only [dif_pos h]
  exact (Classical.choose_spec h).eq hx

/-- `worldValue` is a value whenever one exists.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma valuesAt_worldValue {v : PCWorld} {L : LUV} {x : ℝ} (hx : v.ValuesAt L x) :
    v.ValuesAt L (worldValue v L) := by
  rw [worldValue_eq hx]
  exact hx

/-! ## T6d — the bridge from `Value` to the hard threshold inequalities -/

/-- The two-option menu `{X, C}` (`O 0 = X`, `O 1 = C`).
Source: [[two-option-value-iff-total-trust]] §Statement; v6 §1.2
Kind: D
Fidelity: exact -/
def twoOptionMenu (X C : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hC : LUV.MachineThresholdCodeSeq C) : Menu 1 where
  O := fun j => if j = 0 then X else C
  codes := fun j => by
    by_cases h : j = 0
    · simpa [h] using hX
    · simpa [h] using hC

/-- Option `0` of the two-option menu is `X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma twoOptionMenu_O_zero (X C : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hC : LUV.MachineThresholdCodeSeq C) : (twoOptionMenu X C hX hC).O 0 = X := rfl

/-- Option `1` of the two-option menu is `C`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma twoOptionMenu_O_one (X C : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hC : LUV.MachineThresholdCodeSeq C) : (twoOptionMenu X C hX hC).O 1 = C := rfl

/-- The hard-selection identity combination `−s + S_n − XW_n + s·W_n`, valued `0` in every
consistent world when `S` follows the expert on `{X, C}` and `(W, XW)` are the hard
weight/product at the expert's quote of `C`.
Source: mandate T6d
Kind: D
Fidelity: exact -/
def hardSelectionComb (s : ℚ) (S XW W : ℕ → LUV) (n : ℕ) : LUVCombination :=
  ⟨EF.const (-s), [(EF.const 1, S n), (EF.const (-1), XW n), (EF.const s, W n)]⟩

/-- The single-LUV combination `0 + 1·C_n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def singleComb (C : ℕ → LUV) (n : ℕ) : LUVCombination :=
  ⟨EF.const 0, [(EF.const 1, C n)]⟩

/-- The expectation of the identity combination, by definition of `LUVCombination.expect`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hardSelectionComb_expect (P : History) (s : ℚ) (S XW W : ℕ → LUV) (n : ℕ) :
    (hardSelectionComb s S XW W n).expect P n =
      -(s : ℝ) + (S n).expect P n - (XW n).expect P n + (s : ℝ) * (W n).expect P n := by
  simp [hardSelectionComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]
  ring

/-- The world value of the identity combination under a LUV valuation `ν`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hardSelectionComb_value (P : History) (s : ℚ) (S XW W : ℕ → LUV) (n : ℕ)
    (ν : LUV → ℝ) :
    (hardSelectionComb s S XW W n).value P ν =
      -(s : ℝ) + ν (S n) - ν (XW n) + (s : ℝ) * ν (W n) := by
  simp [hardSelectionComb, LUVCombination.value]
  ring

/-- The expectation of the single-LUV combination is the LUV's expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma singleComb_expect (P : History) (C : ℕ → LUV) (n : ℕ) :
    (singleComb C n).expect P n = (C n).expect P n := by
  simp [singleComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]

/-- The world value of the single-LUV combination is `ν` of the LUV.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma singleComb_value (P : History) (C : ℕ → LUV) (n : ℕ) (ν : LUV → ℝ) :
    (singleComb C n).value P ν = ν (C n) := by
  simp [singleComb, LUVCombination.value]

/-! ## `BoundedSequence` certificates for the two T6d combinations (repair round 1)

FAF's `thm:expprovind` endpoints take `LUVCombination.BoundedSequence`, whose `poly` field is
discharged from a compact `LUVCombinationSyntax` (`LUVCombinationSyntax.polySequence`) and whose
`bounded` field is an `l1Norm` bound. FAF has no such syntax for a constant-coefficient
combination of `MachineThresholdCodeSeq` LUVs (its `PaperLUVCombination.toSyntax` covers
paper-LUV sources, `ordinaryLUVCombinationSyntax` one quotation-atom term), so the two this
package needs are built here: three constant coefficients over `S, XW, W`, dispatching on the
paired index by two `ifZero`s, and one over `C`. The `l1Norm` is the numeral `2|s| + 2`, resp.
`1`. Audit round 1 (fidelity item 1, adversarial N5) asked for exactly this: `hbdd`/`hbddC`
are no longer hypotheses of any T6d theorem, and every T6d hypothesis is (a).
-/

/-- The coefficient stream of `hardSelectionComb`: `1, −1, s` at paired-index positions
`0, 1, 2` (and `s` beyond, unused by `terms_eq`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def hardSelectionCoeff (s : ℚ) (z : ℕ) : EF :=
  if z.unpair.2 = 0 then EF.const 1
  else if z.unpair.2 - 1 = 0 then EF.const (-1) else EF.const s

/-- The LUV stream of `hardSelectionComb`: `S, XW, W` at paired-index positions `0, 1, 2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def hardSelectionLuv (S XW W : ℕ → LUV) (z : ℕ) : LUV :=
  if z.unpair.2 = 0 then S z.unpair.1
  else if z.unpair.2 - 1 = 0 then XW z.unpair.1 else W z.unpair.1

/-- The `S, XW, W` stream is machine-metered from the three code certificates (FAF's
`LUV.MachineThresholdCodeSeq.reindex` along `unpair.1`, then two-way dispatch on the paired
index, twice).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hardSelectionLuv_machineThresholdCodeSeq {S XW W : ℕ → LUV}
    (hS : LUV.MachineThresholdCodeSeq S) (hXW : LUV.MachineThresholdCodeSeq XW)
    (hW : LUV.MachineThresholdCodeSeq W) :
    LUV.MachineThresholdCodeSeq (hardSelectionLuv S XW W) := by
  have hj : UnaryRuler (fun m : ℕ => m.unpair.1.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst
  have hj1 : UnaryRuler (fun m : ℕ => m.unpair.1.unpair.2 - 1) := hj.sub (UnaryRuler.const 1)
  have hS' := hS.reindex UnaryRuler.unpairFst
  have hXW' := hXW.reindex UnaryRuler.unpairFst
  have hW' := hW.reindex UnaryRuler.unpairFst
  unfold LUV.MachineThresholdCodeSeq at hS' hXW' hW' ⊢
  refine (MachineSentenceCodes.ifZero hS' (MachineSentenceCodes.ifZero hXW' hW' hj1) hj).of_eq
    (fun m => ?_)
  simp only [hardSelectionLuv]
  split_ifs <;> rfl

/-- The coefficient stream `1, −1, s` is machine-metered (two-way dispatch on the paired
index, twice, over `serialize_const`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hardSelectionCoeff_spliceStream (s : ℚ) :
    MachineSpliceStream (fun z => (hardSelectionCoeff s z).serialize) := by
  have hj : UnaryRuler (fun z : ℕ => z.unpair.2) := UnaryRuler.unpairSnd
  have hj1 : UnaryRuler (fun z : ℕ => z.unpair.2 - 1) := hj.sub (UnaryRuler.const 1)
  refine (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 1)
    (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const (-1))
      (MachineSpliceStream.serialize_const s) hj1) hj).of_eq (fun z => ?_)
  simp only [hardSelectionCoeff]
  split_ifs <;> rfl

/-- **Compact syntax for the identity combination** `−s + S_n − XW_n + s·W_n`: three terms,
constant coefficients, threshold codes from the three certificates.
Source: none: infrastructure (FAF API request: a constant-coefficient `LUVCombinationSyntax`
constructor over `MachineThresholdCodeSeq` sources)
Kind: D
Fidelity: n/a -/
def hardSelectionSyntax (s : ℚ) {S XW W : ℕ → LUV}
    (hS : LUV.MachineThresholdCodeSeq S) (hXW : LUV.MachineThresholdCodeSeq XW)
    (hW : LUV.MachineThresholdCodeSeq W) :
    LUVCombinationSyntax (fun n => hardSelectionComb s S XW W n) where
  termCount _ := 3
  coefficient := hardSelectionCoeff s
  luv := hardSelectionLuv S XW W
  termCount_poly := UnaryRuler.const 3
  const_poly := MachineSpliceStream.serialize_const (-s)
  coefficient_poly := hardSelectionCoeff_spliceStream s
  threshold_poly := hardSelectionLuv_machineThresholdCodeSeq hS hXW hW
  terms_eq n := by
    have h3 : List.range 3 = [0, 1, 2] := rfl
    rw [h3]
    simp [hardSelectionComb, hardSelectionCoeff, hardSelectionLuv]
  const_rank n := by simp [hardSelectionComb]
  coefficient_rank n j _ := by
    unfold hardSelectionCoeff
    split_ifs <;> simp
  const_closed n ρ V := by simp [hardSelectionComb]
  coefficient_closed z ρ V := by
    unfold hardSelectionCoeff
    split_ifs <;> simp

/-- The `L¹` norm of the identity combination is the numeral `2|s| + 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hardSelectionComb_l1Norm (P : History) (s : ℚ) (S XW W : ℕ → LUV) (n : ℕ) :
    (hardSelectionComb s S XW W n).l1Norm P = 2 * |(s : ℝ)| + 2 := by
  simp [LUVCombination.l1Norm, LUVCombination.shareNorm, hardSelectionComb]
  ring

/-- **`BoundedSequence` for the identity combination, from the three code certificates** —
the side condition `hbdd` of audit round 1, discharged.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def hardSelectionComb_boundedSequence (P : History) (s : ℚ) {S XW W : ℕ → LUV}
    (hS : LUV.MachineThresholdCodeSeq S) (hXW : LUV.MachineThresholdCodeSeq XW)
    (hW : LUV.MachineThresholdCodeSeq W) :
    LUVCombination.BoundedSequence (fun n => hardSelectionComb s S XW W n) P where
  poly := (hardSelectionSyntax s hS hXW hW).polySequence
  bounded := ⟨2 * |(s : ℝ)| + 2, fun n => (hardSelectionComb_l1Norm P s S XW W n).le⟩

/-- **Compact syntax for the single-LUV combination** `0 + 1·C_n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def singleCombSyntax {C : ℕ → LUV} (hC : LUV.MachineThresholdCodeSeq C) :
    LUVCombinationSyntax (fun n => singleComb C n) where
  termCount _ := 1
  coefficient _ := EF.const 1
  luv z := C z.unpair.1
  termCount_poly := UnaryRuler.const 1
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly := MachineSpliceStream.serialize_const 1
  threshold_poly := hC.reindex UnaryRuler.unpairFst
  terms_eq n := by simp [singleComb]
  const_rank n := Nat.zero_le n
  coefficient_rank n j _ := Nat.zero_le n
  const_closed n ρ V := by simp [singleComb]
  coefficient_closed z ρ V := by simp

/-- The `L¹` norm of the single-LUV combination is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma singleComb_l1Norm (P : History) (C : ℕ → LUV) (n : ℕ) :
    (singleComb C n).l1Norm P = 1 := by
  simp [LUVCombination.l1Norm, LUVCombination.shareNorm, singleComb]

/-- **`BoundedSequence` for the single-LUV combination, from its code certificate** — the side
condition `hbddC` of audit round 1, discharged.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def singleComb_boundedSequence (P : History) {C : ℕ → LUV}
    (hC : LUV.MachineThresholdCodeSeq C) :
    LUVCombination.BoundedSequence (fun n => singleComb C n) P where
  poly := (singleCombSyntax hC).polySequence
  bounded := ⟨1, fun n => (singleComb_l1Norm P C n).le⟩

/-- The hypothesis package of T6d, bundled: the menu `{X, C}` with `C` valued `s`, the
followed `S`, and the hard weight/product quotes `(W, XW)` at the expert's quote of `C`
(exact, `slack ≡ 0`). Every clause is a reflection clause or a code certificate. The code
certificates for `W` and `XW` (added in repair round 1; they are `WeightQuote`'s
`weight_codes`/`product_codes`) are what discharge the `BoundedSequence` side conditions.
Source: mandate T6d
Kind: D
Fidelity: exact -/
structure HardTwoOptionData (DP : DeductiveProcess) (E : Expert DP) (X C S W XW : ℕ → LUV)
    (s : ℚ) where
  /-- the bet is efficiently describable -/
  codes_X : LUV.MachineThresholdCodeSeq X
  /-- the constant option is efficiently describable -/
  codes_C : LUV.MachineThresholdCodeSeq C
  /-- the followed strategy is efficiently describable -/
  codes_S : LUV.MachineThresholdCodeSeq S
  /-- the hard weight LUV is efficiently describable -/
  codes_W : LUV.MachineThresholdCodeSeq W
  /-- the hard product LUV is efficiently describable -/
  codes_XW : LUV.MachineThresholdCodeSeq XW
  /-- every consistent world values the bet -/
  valued_X : Valued DP X
  /-- the constant option is valued `s` in every consistent world -/
  const_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (C n) s
  /-- the hard weight `1[E*(C_n) ≤ E*(X_n)]` -/
  weight_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (W n) (if E.estimate C n ≤ E.estimate X n then 1 else 0)
  /-- the hard product `x · 1[E*(C_n) ≤ E*(X_n)]` -/
  product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x,
    v.ValuesAt (X n) x → v.ValuesAt (XW n) (x * if E.estimate C n ≤ E.estimate X n then 1 else 0)
  /-- `S` follows the expert's least-index argmax on `{X, C}` -/
  follows : Follows DP E (twoOptionMenu X C codes_X codes_C) S

namespace HardTwoOptionData

variable {DP : DeductiveProcess} {E : Expert DP} {X C S W XW : ℕ → LUV} {s : ℚ}

/-- The menu `{X, C}` is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma menu_valued (d : HardTwoOptionData DP E X C S W XW s) :
    (twoOptionMenu X C d.codes_X d.codes_C).Valued DP := by
  intro j
  by_cases h : j = 0
  · subst h
    simpa using d.valued_X
  · have h1 : j = 1 := by
      revert h
      generalize j = a
      intro h
      fin_cases a
      · exact absurd rfl h
      · rfl
    subst h1
    intro n v hv
    exact ⟨_, d.const_reflected n v hv⟩

/-- **The followed strategy's world value:** `S n` is valued `x` where `E*(C_n) ≤ E*(X_n)`
(the expert takes `X`, ties toward `X`) and `s` otherwise, whenever `X n` is valued `x`.
Source: [[two-option-value-iff-total-trust]] §Statement (`Ŝ_{X,s}`)
Kind: L
Fidelity: exact -/
lemma followed_valuesAt (d : HardTwoOptionData DP E X C S W XW s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) (x : ℝ) (hx : v.ValuesAt (X n) x) :
    v.ValuesAt (S n) (if E.estimate C n ≤ E.estimate X n then x else s) := by
  have hargmax := (twoOptionMenu X C d.codes_X d.codes_C).argmax_two E n
  simp only [Menu.quote, twoOptionMenu_O_zero, twoOptionMenu_O_one] at hargmax
  by_cases h : E.estimate C n ≤ E.estimate X n
  · rw [if_pos h]
    rw [if_pos h] at hargmax
    have := d.follows n v hv x
    rw [hargmax, twoOptionMenu_O_zero] at this
    exact this hx
  · rw [if_neg h]
    rw [if_neg h] at hargmax
    have := d.follows n v hv s
    rw [hargmax, twoOptionMenu_O_one] at this
    exact this (d.const_reflected n v hv)

/-- The identity combination is world-valued (representation premise, derived from the
reflection clauses — no `(b)`, no `(c)`).
Source: mandate T6d
Kind: L
Fidelity: exact -/
lemma worldValued (d : HardTwoOptionData DP E X C S W XW s) :
    LUVCombination.WorldValued (fun n => hardSelectionComb s S XW W n) DP := by
  intro n v hv
  obtain ⟨x, hx⟩ := d.valued_X n v hv
  refine ⟨worldValue v, ?_⟩
  intro p hp
  simp only [hardSelectionComb, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact valuesAt_worldValue (d.followed_valuesAt n v hv x hx)
  · exact valuesAt_worldValue (d.product_reflected n v hv x hx)
  · exact valuesAt_worldValue (d.weight_reflected n v hv)

/-- The identity combination is valued `0` in every consistent world: pointwise
`S_n − XW_n − s + s·W_n = 0` for `S_n = if q ≤ q_X then x else s`, `XW_n = x·1[q ≤ q_X]`,
`W_n = 1[q ≤ q_X]`.
Source: [[two-option-value-iff-total-trust]] §Proof ("Pointwise, on every world")
Kind: L
Fidelity: exact -/
lemma value_eq_zero (d : HardTwoOptionData DP E X C S W XW s) (P : History) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) (ν : LUV → ℝ)
    (hν : (hardSelectionComb s S XW W n).ValuesAt v ν) :
    (hardSelectionComb s S XW W n).value P ν = 0 := by
  obtain ⟨x, hx⟩ := d.valued_X n v hv
  have hS : ν (S n) = if E.estimate C n ≤ E.estimate X n then x else s :=
    (hν (EF.const 1, S n) (by simp [hardSelectionComb])).eq (d.followed_valuesAt n v hv x hx)
  have hXW : ν (XW n) = x * if E.estimate C n ≤ E.estimate X n then 1 else 0 :=
    (hν (EF.const (-1), XW n) (by simp [hardSelectionComb])).eq
      (d.product_reflected n v hv x hx)
  have hW : ν (W n) = if E.estimate C n ≤ E.estimate X n then 1 else 0 :=
    (hν (EF.const s, W n) (by simp [hardSelectionComb])).eq (d.weight_reflected n v hv)
  rw [hardSelectionComb_value, hS, hXW, hW]
  by_cases h : E.estimate C n ≤ E.estimate X n
  · simp [h]
  · simp [h]

/-- The single combination on `C` is world-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma singleComb_worldValued (d : HardTwoOptionData DP E X C S W XW s) :
    LUVCombination.WorldValued (fun n => singleComb C n) DP := by
  intro n v hv
  refine ⟨worldValue v, ?_⟩
  intro p hp
  simp only [singleComb, List.mem_singleton] at hp
  subst hp
  exact valuesAt_worldValue (d.const_reflected n v hv)

/-- **The linearity step of T6d:** `E^H_n(S_n) ≈ₙ E^H_n(XW_n) + s − s·E^H_n(W_n)`, from
`lic_expect_combination_provind_eq` at `c = 0` on the identity combination, whose
`BoundedSequence` certificate is built from the package's code certificates
(`hardSelectionComb_boundedSequence`).
Source: mandate T6d; FAF `thm:expprovind`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_followed_asympEq (d : HardTwoOptionData DP E X C S W XW s) (P : History)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (S n).expect P n) ≈ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) := by
  have h := lic_expect_combination_provind_eq
    (hardSelectionComb_boundedSequence P s d.codes_S d.codes_XW d.codes_W) d.worldValued 0
    (fun n v hv ν hν => d.value_eq_zero P n v hv ν hν) hworld
  simp only [hardSelectionComb_expect] at h
  unfold AsympEq at h ⊢
  refine (tendsto_congr (fun n => ?_)).mp h
  ring

/-- The novice's expectation of the constant option tends to `s` (`thm:expprovind` on the
single-LUV combination, whose `BoundedSequence` is `singleComb_boundedSequence`).
Source: mandate T6d; FAF `thm:expprovind`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_const_asympEq (d : HardTwoOptionData DP E X C S W XW s) (P : History)
    [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (C n).expect P n) ≈ₙ (fun _ => (s : ℝ)) := by
  have h := lic_expect_combination_provind_eq (singleComb_boundedSequence P d.codes_C)
    d.singleComb_worldValued s
    (fun n v hv ν hν => by
      rw [singleComb_value]
      exact (hν (EF.const 1, C n) (by simp [singleComb])).eq (d.const_reflected n v hv))
    hworld
  simpa only [singleComb_expect] using h

end HardTwoOptionData

/-- **T6d, above-threshold face (menu-local):** Value against the constant option on the
two-option menu `{X, C}` — the single instance `E^H_n(S_n) ≳ₙ E^H_n(C_n)`, hypothesis `hval` —
gives the hard above-threshold product inequality **at the expert's quote of the constant**:
`E^H_n(X_n·1[E*(C_n) ≤ E*(X_n)]) − s·E^H_n(1[E*(C_n) ≤ E*(X_n)]) ≳ₙ 0`.
The hypothesis is the *per-menu* Value instance, not the unconditional predicate
`Value P DP E`: the corpus holds unconditional argmax Value to be false for inductor-experts
([[deference-notions]] §Value ⚠ 2026-07-25, `def-argmax-value`'s refutation), so a theorem
hypothesised on it would be vacuous on every instance the run cares about (audit round 1, B1).
`value_twoOption_hardAbove_of_value` is the one-line corollary from the global predicate.
Composition: the local Value instance, the linearity identity (`expect_followed_asympEq`,
`thm:expprovind` at `c = 0`) and `E^H_n(C_n) ≈ₙ s` (`expect_const_asympEq`). `WorldValued` and
the determined value are *derived* from the reflection clauses. The cut is at `q_n := E*(C_n)`,
not at `s`: over FAF's grid expectation the expert's estimate of a LUV valued `s` is not `s`
(finding F3); see `value_twoOption_hardAbove_of_weightQuote` for the fixed-`s` form under the
surrogate reading.
Source: [[two-option-value-iff-total-trust]] §Statement (Value against the constant ⟹ the
upper cut); mandate T6d
Kind: C
Fidelity: variant: threshold at the expert's quote of the constant (see F3); hypothesis is the
menu-local Value instance (stronger theorem than the mandate's `Value → …` shape)
Hyps: (a) — `hval` (the per-menu Value instance), the reflection clauses and code certificates
of `d`, `hworld` (caller obligation, [[faf-map-li]] §5 gap 12); the `BoundedSequence` side
conditions of round 1 (`hbdd`/`hbddC`) are discharged from `d`'s code certificates -/
theorem value_twoOption_hardAbove (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s)
    (hval : (fun n => (S n).expect P n) ≳ₙ (fun n => (C n).expect P n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hlin := d.expect_followed_asympEq P hworld
  have hconst := d.expect_const_asympEq P hworld
  -- `s ≲ₙ E(C) ≲ₙ E(S) ≈ₙ E(XW) + s − s·E(W)`
  have h1 : (fun _ => (s : ℝ)) ≲ₙ (fun n => (S n).expect P n) :=
    AsympEq.trans_asympLE hconst.symm hval
  have h2 : (fun _ => (s : ℝ)) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) :=
    AsympLE.trans_asympEq h1 hlin
  unfold AsympGE AsympLE at h2 ⊢
  intro ε hε
  filter_upwards [h2 ε hε] with n hn
  linarith

/-- The above face from the unconditional predicate `Value P DP E`, by instantiating it once at
the menu `{X, C}` and index `1` (the mandate's literal `Value → …` shape). Vacuous wherever
unconditional Value fails — which the corpus says is every inductor-expert — so dependents
should consume `value_twoOption_hardAbove` and supply the per-menu instance.
Source: mandate T6d
Kind: L
Fidelity: exact (instance of `value_twoOption_hardAbove`)
Hyps: as `value_twoOption_hardAbove`, with `Value P DP E` in place of `hval` -/
theorem value_twoOption_hardAbove_of_value (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP} (hV : Value P DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hval := hV 1 (twoOptionMenu X C d.codes_X d.codes_C) d.menu_valued S d.codes_S
    d.follows 1
  rw [twoOptionMenu_O_one] at hval
  exact value_twoOption_hardAbove P DP hworld d hval

/-- **T6d, below-threshold face (menu-local):** Value against the fixed option `X` on `{X, C}` —
the single instance `E^H_n(S_n) ≳ₙ E^H_n(X_n)`, hypothesis `hval` — gives
`s·(1 − E^H_n(W_n)) − (E^H_n(X_n) − E^H_n(XW_n)) ≳ₙ 0`: the below-threshold product form
`E^H_n((s − X_n)·1[E*(X_n) < E*(C_n)]) ≳ₙ 0` with the complementary weight `1 − W_n` and
product `X_n − XW_n`. Menu-local hypothesis for the reason given at
`value_twoOption_hardAbove`; `value_twoOption_hardBelow_of_value` is the global corollary.
Source: [[two-option-value-iff-total-trust]] §Statement (Value against `X` ⟹ the lower cut)
Kind: C
Fidelity: variant: threshold at the expert's quote of the constant (see F3); menu-local
hypothesis
Hyps: as `value_twoOption_hardAbove` (`hval` is the per-menu instance against `X`) -/
theorem value_twoOption_hardBelow (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s)
    (hval : (fun n => (S n).expect P n) ≳ₙ (fun n => (X n).expect P n)) :
    (fun n => (s : ℝ) * (1 - (W n).expect P n) - ((X n).expect P n - (XW n).expect P n)) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  have hlin := d.expect_followed_asympEq P hworld
  have h2 : (fun n => (X n).expect P n) ≲ₙ
      (fun n => (XW n).expect P n + (s : ℝ) - (s : ℝ) * (W n).expect P n) :=
    AsympLE.trans_asympEq hval hlin
  unfold AsympGE AsympLE at h2 ⊢
  intro ε hε
  filter_upwards [h2 ε hε] with n hn
  linarith

/-- The below face from the unconditional predicate `Value P DP E` (instantiated at `{X, C}`,
index `0`). Same caveat as `value_twoOption_hardAbove_of_value`.
Source: mandate T6d
Kind: L
Fidelity: exact (instance of `value_twoOption_hardBelow`)
Hyps: as `value_twoOption_hardBelow`, with `Value P DP E` in place of `hval` -/
theorem value_twoOption_hardBelow_of_value (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP} (hV : Value P DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ} (d : HardTwoOptionData DP E X C S W XW s) :
    (fun n => (s : ℝ) * (1 - (W n).expect P n) - ((X n).expect P n - (XW n).expect P n)) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  have hval := hV 1 (twoOptionMenu X C d.codes_X d.codes_C) d.menu_valued S d.codes_S
    d.follows 0
  rw [twoOptionMenu_O_zero] at hval
  exact value_twoOption_hardBelow P DP hworld d hval

/-- **T6d under the surrogate reading (the mandate's literal claim, `(c)` disclosed):** if the
expert quotes the constant option *exactly* at `s` — `E*(C_n) = s` for all `n` — then a hard
`WeightQuote` at `hardAbove s` with `slack ≡ 0` is the data of `HardTwoOptionData`, and the
per-menu Value instance `E^H_n(S_n) ≳ₙ E^H_n(C_n)` gives `ThresholdIneqAbove`'s conclusion at
`(X, W, XW)` for threshold `s`. The surrogate hypothesis `hsur` is the corpus's exact coherence
`E*(const s) = s`; over FAF's grid expectation it fails for inductor experts in general
(finding F3), so this is a `(c)`-graded corollary, kept because it is the shape the corpus
states. Menu-local hypothesis as in `value_twoOption_hardAbove` (instantiate `Value P DP E`
at `twoOptionMenu X C hX hC`, index `1`, to recover the global form).
Source: [[two-option-value-iff-total-trust]] §Setting ("Coherence is used only through
`E*(const s) = s`"); mandate T6d
Kind: C
Fidelity: exact under `hsur`
Hyps: (c) `hsur` (surrogate coherence); (a) otherwise -/
theorem value_twoOption_hardAbove_of_weightQuote (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] {E : Expert DP}
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X C S W XW : ℕ → LUV} {s : ℚ}
    (hX : LUV.MachineThresholdCodeSeq X) (hC : LUV.MachineThresholdCodeSeq C)
    (hS : LUV.MachineThresholdCodeSeq S)
    (hCval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (C n) s)
    (hsur : ∀ n, E.estimate C n = s)
    (q : WeightQuote DP E X (hardAbove s) W XW) (hq0 : ∀ n, q.slack n = 0)
    (hF : Follows DP E (twoOptionMenu X C hX hC) S)
    (hval : (fun n => (S n).expect P n) ≳ₙ (fun n => (C n).expect P n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  refine value_twoOption_hardAbove P DP hworld
    (X := X) (C := C) (S := S) (W := W) (XW := XW) (s := s) ⟨hX, hC, hS, q.weight_codes,
      q.product_codes, q.source_valued, hCval, ?_, ?_, hF⟩ hval
  · intro n v hv
    have h := q.weight_reflected n v hv
    simpa [hardAbove, hsur n] using h
  · intro n v hv x hx
    obtain ⟨z, hz, hzx⟩ := q.product_reflected n v hv x hx
    rw [hq0 n] at hzx
    have hzx' : z = x * hardAbove s (E.estimate X n) := by
      have := abs_nonpos_iff.mp hzx
      linarith
    rw [hzx'] at hz
    simpa [hardAbove, hsur n] using hz

end

end Cleanroom.Found.DefLattice
