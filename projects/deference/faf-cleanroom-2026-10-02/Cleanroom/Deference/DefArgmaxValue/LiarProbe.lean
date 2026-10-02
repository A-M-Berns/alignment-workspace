import Cleanroom.Deference.DefArgmaxValue.AtomCode
import Cleanroom.Deference.DefArgmaxValue.CondStable
import Cleanroom.Deference.DefArgmaxValue.Pin
import Cleanroom.Deference.DefSqueezeDiamond.GapIndicator
import Cleanroom.Found.DefLattice.TwoOptionLUV
import Cleanroom.Li.LiDiagonal.Deferred

/-!
# `def-argmax-value` · LiarProbe: the `K = 2` liar probe (target 1, the construction)

Abram's constant-probe menu ([[loop-direction]] §The liar probe; [[total-trust-implies-value]]
§Necessity, last paragraph): one option `O^0_n := 1[χ_n]` whose sentence `χ_n` is the
**deferred liar at the menu's own comparison** — `χ_n` holds in every `paperDP T`-world iff the
self-expert's argmax on `{O^0, const s}` is `1`, i.e. iff `P_{f n}(χ_n) < s_{f n}` where
`s_{f n} := E_{f n}(const s)` is the mesh value of the constant option (`probeThreshold`) — and
one constant option `O^1_n := const s`.

**Route (ii) of the mandate** (recorded): `def-squeeze-diamond`'s `deferredLiarOfDiagonal` has
the clause `P_{f n}(χ_n) < s` at the *fixed* rational `s`, while `Menu.argmax` compares against
the constant option's *mesh* expectation `s_{f n} = ⌈s(f n+1)⌉/(f n+1) · P_{f n}(⊤) + …`, which
is neither `s` nor eventually `s`; the days on which the two clauses disagree are not known to
be finite. So the liar is built at the comparison itself: `Selector.lean`'s Kleene selector with
`quotes c n := [P_{f n}(a_{n,1}), s_{f n}]` and `rel := (· = ·)`, so that
`v.Holds χ_n ↔ argmax = 1` is the reflection clause (`liarSentence_holds_iff`,
`probeMenu_argmax_iff`), and the pin `P_{f n}(χ_n) → s` is `Pin.lean`'s deferred engine
against the convergent threshold (`liarPrice_tendsto_s`); the present-day pin `P_n(χ_n) → s` is
`cee` (`selfTower_valued`) at FAF's closed quote. This is target 3's construction at `k = 1`
with one constant option.

Objects: `probeMenu`, the honest follower `probeFollower` (`selectLUV` by `χ_n` between the two
options; `probeFollower_follows`), its world value `s · 1[χ_n]`, the selection package
`probePackage` (indicators `1[∼χ_n]`, `1[χ_n]`; products `0`, `S`), and the five real-number
limits the refutations consume (`Refuted.lean`).

Construction-facing; single market (self); `0 < s < 1`, `f` strictly increasing.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open Cleanroom.Li.LiDiagonal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- The self-expert over the paper market at deferral `f` (an abbreviation of `def-lattice`'s
`Expert.self` at FAF's constructed inductor).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev selfExpert (T : ArithmeticTheory) [T.Δ₁] (f : DeferralFunction) : Expert (paperDP T) :=
  Expert.self (liaHistory (paperDP T)) (paperDP T) f

/-- The self-expert's history is FAF's inductor (the instance, found through the abbreviation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance selfExpert_isLogicalInductor (T : ArithmeticTheory) [T.Δ₁] (f : DeferralFunction) :
    IsLogicalInductor (selfExpert T f).A (paperDP T) :=
  inferInstanceAs (IsLogicalInductor (liaHistory (paperDP T)) (paperDP T))

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

/-! ## The comparison threshold: the constant option's mesh value at the deferred day -/

/-- **The menu's own comparison value** `s_{f n} := expectQuoteAt (const s) n (f n)`, the exact
rational mesh expectation of the constant option at day `f n` (not `s`: FAF's grid average of
the prices of `⊤`/`⊥`).
Source: mandate target 1a ("the comparison `m^0 < m^1` is `P(fn)(χ_n) < s_n` with `s_n → s`")
Kind: D
Fidelity: exact -/
def probeThreshold (n : ℕ) : ℚ :=
  (paperMarketComputation T).expectQuoteAt (fun _ => constLUV s) n (f.f n)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The threshold is computable (FAF `expectQuoteAt_computable` on `constLUV_codes`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeThreshold_computable (hs : 0 ≤ s) : Computable (probeThreshold T f s) :=
  (((paperMarketComputation T).expectQuoteAt_computable (constLUV_codes hs)).comp
    (Computable.id.pair f.computable) : _)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The threshold is the self-expert's quote of the constant option.
Source: none: infrastructure (FAF `expectQuoteAt_cast`)
Kind: L
Fidelity: n/a -/
theorem probeThreshold_cast (n : ℕ) :
    ((probeThreshold T f s n : ℚ) : ℝ) = (constLUV s).expect (liaHistory (paperDP T)) (f n) :=
  ((paperMarketComputation T).expectQuoteAt_cast (fun _ => constLUV s) n (f.f n)).symm

/-- The threshold converges to `s` (the constant option's expectation at the deferred day).
Source: none: infrastructure (`expect_constLUV_asympEq` along `f`)
Kind: L
Fidelity: n/a -/
theorem probeThreshold_tendsto (hs : 0 ≤ s ∧ s ≤ 1) :
    Tendsto (fun n => ((probeThreshold T f s n : ℚ) : ℝ)) atTop (𝓝 (s : ℝ)) := by
  have h := asympEq_comp_deferral (expect_constLUV_asympEq (P := liaHistory (paperDP T))
    (DP := paperDP T) hs (paperDP_hworld T)) f
  have h' := tendsto_of_asympEq_const h
  refine (tendsto_congr (fun n => ?_)).mp h'
  exact (probeThreshold_cast T f s n).symm

/-! ## The liar as the menu's own selection atom -/

/-- The selector's quotes: `[P_{f n}(a_{n,1}), s_{f n}]` for the candidate code `c`.
Source: mandate target 1a, route (ii)
Kind: D
Fidelity: exact -/
def probeQuotes (c : Nat.Partrec.Code) (n : ℕ) : List ℚ :=
  [(paperMarketComputation T).quote (f.f n)
      (Encodable.encode (quoteAtom (Nat.pair (Encodable.encode c) (Nat.pair n 1)))),
    probeThreshold T f s n]

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The quotes are computable in `(c, n)`.
Source: none: infrastructure (`quote_of_atom_computable`, `probeThreshold_computable`)
Kind: L
Fidelity: n/a -/
theorem probeQuotes_computable (hs : 0 ≤ s) : Computable₂ (probeQuotes T f s) := by
  have h1 : Computable fun z : Nat.Partrec.Code × ℕ => (paperMarketComputation T).quote (f.f z.2)
      (Encodable.encode (quoteAtom (Nat.pair (Encodable.encode z.1) (Nat.pair z.2 1)))) :=
    quote_of_atom_computable (paperMarketComputation T) (f.computable.comp Computable.snd)
      (atomPayload_primrec 1)
  have h2 : Computable fun z : Nat.Partrec.Code × ℕ => probeThreshold T f s z.2 :=
    (probeThreshold_computable T f s hs).comp Computable.snd
  exact Computable.list_cons.comp h1 (Computable.list_cons.comp h2 (Computable.const []))

/-- The selection relation of the probe: "the argmax is `j`".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def eqRel : ℕ → ℕ → Bool := fun a j => decide (a = j)

/-- `eqRel` is primitive recursive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eqRel_primrec : Primrec₂ eqRel := Primrec.eq.decide

/-- **The liar sentence** `χ_n := a_{n,1}`: the selector's atom for option `1` — holds iff the
self-expert's argmax on the probe menu is `1`, iff `P_{f n}(χ_n) < s_{f n}`.
Source: mandate target 1a, route (ii); [[loop-direction]] §The liar probe
Kind: D
Fidelity: exact -/
def liarSentence (hs : 0 ≤ s) (n : ℕ) : Sentence :=
  selectorAtom (probeQuotes T f s) eqRel T (probeQuotes_computable T f s hs) eqRel_primrec n 1

omit [Entailment.Consistent T] in
/-- The liar family is e.c.
Source: none: infrastructure (`selectorAtom_codes`)
Kind: L
Fidelity: n/a -/
theorem liarSentence_codes (hs : 0 ≤ s) : MachineSentenceCodes (liarSentence T f s hs) :=
  selectorAtom_codes (probeQuotes T f s) eqRel T (probeQuotes_computable T f s hs) eqRel_primrec 1

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `argmaxList [p, q] = 1` iff `p < q`, for nonnegative `p q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxList_pair_eq_one_iff {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    argmaxList [p, q] = 1 ↔ p < q := by
  unfold argmaxList
  have hm : List.foldl max 0 [p, q] = max p q := by
    simp only [List.foldl_cons, List.foldl_nil]
    rw [max_eq_right hp]
  rw [hm]
  simp only [List.findIdx_cons, List.findIdx_nil]
  constructor
  · intro h
    by_contra hnlt
    push Not at hnlt
    rw [max_eq_left hnlt] at h
    simp at h
  · intro hlt
    rw [max_eq_right hlt.le]
    simp [not_le.2 hlt]

omit [Entailment.Consistent T] in
/-- **The liar clause at the menu's own comparison**: a `paperDP T`-world holds `χ_n` iff
`P_{f n}(χ_n) < s_{f n}`.
Source: mandate target 1a (the selection identity, route (ii)); `def-squeeze-diamond`
`DeferredLiar.reflected` (the fixed-threshold form)
Kind: L
Fidelity: exact -/
theorem liarSentence_holds_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (liarSentence T f s hs n) ↔
      (liaHistory (paperDP T)) (f n) (liarSentence T f s hs n) <
        ((probeThreshold T f s n : ℚ) : ℝ) := by
  have hq : 0 ≤ probeThreshold T f s n :=
    ((paperMarketComputation T).expectQuoteAt_mem_Icc _ _ _).1
  have hp : 0 ≤ (paperMarketComputation T).quote (f.f n)
      (Encodable.encode (liarSentence T f s hs n)) :=
    ((paperMarketComputation T).quote_mem_Icc _ _).1
  have hqe := (paperMarketComputation T).quote_exact (f.f n) (liarSentence T f s hs n)
  change (liaHistory (paperDP T)) (f n) (liarSentence T f s hs n) =
    (((paperMarketComputation T).quote (f.f n) (Encodable.encode (liarSentence T f s hs n)) : ℚ) : ℝ)
    at hqe
  have key : v.Holds (liarSentence T f s hs n) ↔
      argmaxList (probeQuotes T f s (selectorCode (probeQuotes T f s) eqRel
        (probeQuotes_computable T f s hs) eqRel_primrec) n) = 1 := by
    rw [liarSentence, selectorAtom_holds_iff (hv := hv)]
    simp [eqRel]
  rw [key]
  change argmaxList [(paperMarketComputation T).quote (f.f n)
    (Encodable.encode (liarSentence T f s hs n)), probeThreshold T f s n] = 1 ↔ _
  rw [argmaxList_pair_eq_one_iff hp hq, hqe]
  exact (Rat.cast_lt).symm

/-! ## The probe menu -/

/-- **The probe menu** `{1[χ_n], const s}`.
Source: [[loop-direction]] §The liar probe; mandate target 1a
Kind: D
Fidelity: exact -/
def probeMenu (hs : 0 ≤ s) : Menu 1 :=
  twoOptionMenu (fun n => literalIndicator (liarSentence T f s hs n)) (fun _ => constLUV s)
    (literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs)) (constLUV_codes hs)

omit [Entailment.Consistent T] in
/-- Option `0` is the liar's indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem probeMenu_O_zero (hs : 0 ≤ s) :
    (probeMenu T f s hs).O 0 = fun n => literalIndicator (liarSentence T f s hs n) := rfl

omit [Entailment.Consistent T] in
/-- Option `1` is the constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem probeMenu_O_one (hs : 0 ≤ s) :
    (probeMenu T f s hs).O 1 = fun _ => constLUV s := rfl

omit [Entailment.Consistent T] in
/-- The probe menu is world-valued for `s ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeMenu_valued (hs : 0 ≤ s ∧ s ≤ 1) : (probeMenu T f s hs.1).Valued (paperDP T) := by
  intro j
  fin_cases j
  · exact fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩
  · exact constLUV_valued hs (paperDP T)

omit [Entailment.Consistent T] in
/-- The quote of option `0` is the deferred price of the liar, exactly.
Source: none: infrastructure (`literalIndicator_expect`)
Kind: L
Fidelity: n/a -/
theorem probeMenu_quote_zero (hs : 0 ≤ s) (n : ℕ) :
    (probeMenu T f s hs).quote (selfExpert T f) 0 n =
      (liaHistory (paperDP T)) (f n) (liarSentence T f s hs n) := by
  simp [Menu.quote, probeMenu, twoOptionMenu, literalIndicator_expect]

omit [Entailment.Consistent T] in
/-- The quote of option `1` is the threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeMenu_quote_one (hs : 0 ≤ s) (n : ℕ) :
    (probeMenu T f s hs).quote (selfExpert T f) 1 n = ((probeThreshold T f s n : ℚ) : ℝ) := by
  simp [Menu.quote, probeMenu, twoOptionMenu, probeThreshold_cast]

omit [Entailment.Consistent T] in
/-- **The selection identity (the keystone)**: in every `paperDP T`-world, `χ_n` holds iff the
self-expert's least-index argmax on the probe menu is `1` (`Menu.argmax_two`: option `1` wins
iff `m^0_n < m^1_n`).
Source: mandate target 1a ("`sel_n = 1 ↔ m^0_n < m^1_n`, and with `L.reflected` …
`v.Holds (χ_n) ↔ sel_n = 1`")
Kind: L
Fidelity: exact (definitional, by route (ii))
Hyps: (a) none -/
theorem probeMenu_argmax_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (probeMenu T f s hs).argmax (selfExpert T f) n = 1 ↔ v.Holds (liarSentence T f s hs n) := by
  rw [liarSentence_holds_iff T f s hs n v hv, Menu.argmax_two, probeMenu_quote_zero,
    probeMenu_quote_one]
  by_cases hc : ((probeThreshold T f s n : ℚ) : ℝ) ≤
      (liaHistory (paperDP T)) (f n) (liarSentence T f s hs n)
  · rw [if_pos hc]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_lt.2 hc)⟩
  · rw [if_neg hc]
    exact ⟨fun _ => not_le.1 hc, fun _ => rfl⟩

omit [Entailment.Consistent T] in
/-- The argmax is `0` iff the liar fails.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probeMenu_argmax_zero_iff (hs : 0 ≤ s) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    (probeMenu T f s hs).argmax (selfExpert T f) n = 0 ↔ ¬ v.Holds (liarSentence T f s hs n) := by
  rw [← probeMenu_argmax_iff T f s hs n v hv]
  generalize (probeMenu T f s hs).argmax (selfExpert T f) n = a
  fin_cases a <;> simp

/-! ## The honest follower -/

/-- **The probe follower**: the select by `χ_n` between the constant (when `χ_n`, i.e. when
option `1` is chosen) and the liar's indicator (otherwise) — valued `s · 1[χ_n]`.
Source: mandate target 1c ("the honest follower … valued `s · 1[χ_n]`")
Kind: D
Fidelity: exact -/
def probeFollower (hs : 0 ≤ s) : ℕ → LUV :=
  selectLUV (liarSentence T f s hs) (fun _ => constLUV s)
    (fun n => literalIndicator (liarSentence T f s hs n))

omit [Entailment.Consistent T] in
/-- The follower is e.c.
Source: none: infrastructure (`selectLUV_codes`)
Kind: L
Fidelity: n/a -/
theorem probeFollower_codes (hs : 0 ≤ s) : LUV.MachineThresholdCodeSeq (probeFollower T f s hs) :=
  selectLUV_codes (liarSentence_codes T f s hs) (constLUV_codes hs)
    (literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs))

omit [Entailment.Consistent T] in
/-- **The follower's world value** is `s · 1[χ_n]`.
Source: mandate target 1c
Kind: L
Fidelity: exact -/
theorem probeFollower_valuesAt (hs : 0 ≤ s ∧ s ≤ 1) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt (probeFollower T f s hs.1 n) ((s : ℝ) * v.payout (liarSentence T f s hs.1 n)) := by
  have h := selectLUV_valuesAt (liarSentence T f s hs.1) (fun _ => constLUV s)
    (fun n => literalIndicator (liarSentence T f s hs.1 n)) n v (constLUV_valuesAt hs v)
    (literalIndicator_valuesAt _ (paperDP T) hv)
  unfold PCWorld.payout probeFollower
  by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
  · simpa [hχ, PCWorld.payout] using h
  · simpa [hχ, PCWorld.payout] using h

omit [Entailment.Consistent T] in
/-- **The follower follows the self-expert's argmax** on the probe menu: when `χ_n` holds the
argmax is `1` and the select is valued as `const s`; otherwise the argmax is `0` and the select
is valued as `1[χ_n]`.
Source: mandate target 1c ("its `Follows` proof: in every world the selected option is `O 1`
valued `s` when `χ_n` holds and `O 0` valued `0` otherwise")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem probeFollower_follows (hs : 0 ≤ s ∧ s ≤ 1) :
    Follows (paperDP T) (selfExpert T f) (probeMenu T f s hs.1) (probeFollower T f s hs.1) := by
  intro n v hv x hx
  have hsel := selectLUV_valuesAt (liarSentence T f s hs.1) (fun _ => constLUV s)
    (fun n => literalIndicator (liarSentence T f s hs.1 n)) n v (constLUV_valuesAt hs v)
    (literalIndicator_valuesAt _ (paperDP T) hv)
  show v.ValuesAt (selectLUV _ _ _ n) x
  by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
  · have ha := (probeMenu_argmax_iff T f s hs.1 n v hv).2 hχ
    rw [ha, probeMenu_O_one] at hx
    rw [hx.eq (constLUV_valuesAt hs v)]
    simpa [hχ] using hsel
  · have ha := (probeMenu_argmax_zero_iff T f s hs.1 n v hv).2 hχ
    rw [ha, probeMenu_O_zero] at hx
    rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
    simpa [hχ] using hsel

/-- The constant `0` option has vanishing deferred-day expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem constZero_estimate_tendsto (hf : StrictlyIncreasingDeferral f) :
    Tendsto (fun n => (constLUV 0).expect (liaHistory (paperDP T)) (f n)) atTop (𝓝 (0 : ℝ)) := by
  have h := expect_deferred_const (P := liaHistory (paperDP T)) (DP := paperDP T) f hf 0
    (Y := fun _ => constLUV 0) (constLUV_codes le_rfl) (fun _ => 0) tendsto_const_nhds
    (fun n v hv => ⟨0, by simpa using constLUV_valuesAt (s := 0) ⟨le_rfl, zero_le_one⟩ v, by simp⟩)
    (paperDP_hworld T)
  simpa using tendsto_of_asympEq_const h

/-! ## The pins -/

/-- **The deferred pin**: `P_{f n}(χ_n) → s` (target 1b), by the deferred engine against the
convergent threshold `s_{f n} → s`.
Source: mandate target 1b; [[loop-direction]] §The liar probe ("the expert's quote … is driven
to a liar fixed point at `s`")
Kind: C
Fidelity: exact (asymptotic)
Hyps: (a); `hf` -/
theorem liarPrice_tendsto_s (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) (f n) (liarSentence T f s hs0.le n)) atTop
      (𝓝 (s : ℝ)) :=
  liarPrice_tendsto T f hf (liarSentence_codes T f s hs0.le)
    (fun n => ((probeThreshold T f s n : ℚ) : ℝ)) s hs0 hs1
    (probeThreshold_tendsto T f s ⟨hs0.le, hs1.le⟩) (liarSentence_holds_iff T f s hs0.le)

/-- **The present pin**: `P_n(χ_n) → s` (target 1b), by `cee` (`selfTower_valued` at FAF's closed
quote of the indicator) and the deferred pin.
Source: mandate target 1b ("`P n (χ_n) ≈ₙ s` … the present-price pin"); li-diagonal T5c
Kind: C
Fidelity: exact (asymptotic)
Hyps: (a); `hf` -/
theorem liarPresentPrice_tendsto_s (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    Tendsto (fun n => (liaHistory (paperDP T)) n (liarSentence T f s hs0.le n)) atTop
      (𝓝 (s : ℝ)) := by
  set X : ℕ → LUV := fun n => literalIndicator (liarSentence T f s hs0.le n) with hX
  have hXc : LUV.MachineThresholdCodeSeq X :=
    literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs0.le)
  set Y : ℕ → LUV := (paperDeferredExpectationQuoteCode T f X hXc).luv with hY
  have hYc : LUV.MachineThresholdCodeSeq Y := (paperDeferredExpectationQuoteCode T f X hXc).poly
  have hR := Cleanroom.Deference.DefLatticeArrows.Witness.closedQuote_reflects T f X hXc
  have hval : Valued (paperDP T) X := fun n v hv => ⟨_, literalIndicator_valuesAt _ (paperDP T) hv⟩
  have h1 := selfTower_valued T f X Y hXc hYc hval hR
  have h2 : (fun n => (Y n).expect (liaHistory (paperDP T)) n) ≈ₙ fun _ => (s : ℝ) :=
    expect_asympEq_of_determinedVia_tendsto (liaHistory (paperDP T)) (paperDP T) Y hYc
      (fun n => (liaHistory (paperDP T)) (f n) (liarSentence T f s hs0.le n))
      (fun n v hv => by
        have := hR n v hv
        simpa [Expert.self_estimate, hX, literalIndicator_expect] using this)
      s (liarPrice_tendsto_s T f s hf hs0 hs1) (paperDP_hworld T)
  have h3 := tendsto_of_asympEq_const (h1.trans h2)
  refine (tendsto_congr (fun n => ?_)).mp h3
  simp [hX, literalIndicator_expect]

/-! ## The selection package of the probe -/

/-- The selection indicators of the probe: `1[∼χ_n]` for option `0`, `1[χ_n]` for option `1`.
Source: mandate target 4c (N−)
Kind: D
Fidelity: exact -/
def probeI (hs : 0 ≤ s) : Fin 2 → ℕ → LUV :=
  ![fun n => literalIndicator (∼ liarSentence T f s hs n),
    fun n => literalIndicator (liarSentence T f s hs n)]

/-- The products of the probe: `0` for option `0` (`1[χ_n]·1[sel=0] = 1[χ_n]·1[∼χ_n] = 0`), the
follower for option `1` (`s · 1[χ_n]`).
Source: mandate target 4c (N−)
Kind: D
Fidelity: exact -/
def probeQ (hs : 0 ≤ s) : Fin 2 → ℕ → LUV :=
  ![fun _ => constLUV 0, probeFollower T f s hs]

omit [Entailment.Consistent T] in
/-- **The probe's selection package** (exact, slack `0`).
Source: mandate target 4c
Kind: D
Fidelity: exact -/
def probePackage (hs : 0 ≤ s ∧ s ≤ 1) :
    SelectionPackage (paperDP T) (selfExpert T f) (probeMenu T f s hs.1) (probeI T f s hs.1)
      (probeQ T f s hs.1) where
  codes_I := fun j => by
    fin_cases j
    · exact literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs.1).neg
    · exact literalIndicator_machineThresholdCodeSeq (liarSentence_codes T f s hs.1)
  codes_Q := fun j => by
    fin_cases j
    · exact constLUV_codes le_rfl
    · exact probeFollower_codes T f s hs.1
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected_I := by
    rw [Fin.forall_fin_two]
    refine ⟨fun n v hv => ?_, fun n v hv => ?_⟩
    · have h := literalIndicator_valuesAt (∼ liarSentence T f s hs.1 n) (paperDP T) hv
      have e : v.payout (∼ liarSentence T f s hs.1 n) =
          (if (probeMenu T f s hs.1).argmax (selfExpert T f) n = 0 then 1 else 0) := by
        unfold PCWorld.payout
        rw [PCWorld.holds_neg]
        by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
        · rw [if_neg (fun h => h hχ), if_neg]
          rw [probeMenu_argmax_zero_iff T f s hs.1 n v hv]; exact fun h => h hχ
        · rw [if_pos hχ, if_pos ((probeMenu_argmax_zero_iff T f s hs.1 n v hv).2 hχ)]
      simpa [probeI, e] using h
    · have h := literalIndicator_valuesAt (liarSentence T f s hs.1 n) (paperDP T) hv
      have e : v.payout (liarSentence T f s hs.1 n) =
          (if (probeMenu T f s hs.1).argmax (selfExpert T f) n = 1 then 1 else 0) := by
        unfold PCWorld.payout
        by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
        · rw [if_pos hχ, if_pos ((probeMenu_argmax_iff T f s hs.1 n v hv).2 hχ)]
        · rw [if_neg hχ, if_neg]
          rw [probeMenu_argmax_iff T f s hs.1 n v hv]; exact hχ
      simpa [probeI, e] using h
  reflected_Q := by
    rw [Fin.forall_fin_two]
    refine ⟨fun n v hv x hx => ?_, fun n v hv x hx => ?_⟩
    · refine ⟨0, by simpa [probeQ] using constLUV_valuesAt (s := 0) ⟨le_rfl, zero_le_one⟩ v, ?_⟩
      simp only [probeMenu_O_zero] at hx
      rw [hx.eq (literalIndicator_valuesAt _ (paperDP T) hv)]
      by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
      · rw [if_neg]
        · simp
        · rw [probeMenu_argmax_zero_iff T f s hs.1 n v hv]; exact fun h => h hχ
      · simp [PCWorld.payout, hχ]
    · refine ⟨(s : ℝ) * v.payout (liarSentence T f s hs.1 n), ?_, ?_⟩
      · simpa [probeQ] using probeFollower_valuesAt T f s hs n v hv
      · simp only [probeMenu_O_one] at hx
        rw [hx.eq (constLUV_valuesAt hs v)]
        unfold PCWorld.payout
        by_cases hχ : v.Holds (liarSentence T f s hs.1 n)
        · rw [if_pos hχ, if_pos ((probeMenu_argmax_iff T f s hs.1 n v hv).2 hχ)]; simp
        · rw [if_neg hχ, if_neg]
          · simp
          · rw [probeMenu_argmax_iff T f s hs.1 n v hv]; exact hχ

end

end Cleanroom.Deference.DefArgmaxValue
