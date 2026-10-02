import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Found.DefLattice.TwoOptionLUV

/-!
# `def-frozen-sibling` · Value: T4, two-option Value on `G'` and the above-threshold form

[[frozen-deliberation-deference-v6]] T4 (anson-021; root-deference-042): "Let `Ŝ_n` be the option
`A` would pick. On `G`, `E^{H⁺}_n(Ŝ_n) ≳ₙ E^{H⁺}_n(O^i_n)`." At the two-option menu
`{P^{(n)}, const s}` the option `A` picks is read off the **ledger literal** `q n := ⌜a_n > s⌝`
(`(ledgerLuv 0 n).gt s`, decided in `Hplus`'s process at the published quote — hard selection by a
settled literal, no continuity needed; the `LedgerDecided` selector of `li-coupled-pair` at a
one-threshold menu). The followed strategy is the LUV combination
`Ŝ_n = 𝟙(P^{(n)} ∧ q_n) + s·𝟙(∼q_n)` (`followed`).

* **T4a** (`valueTwoOption_onG`): along every e.c. sub-fragment `G'`, `𝔼^{H}_n(Ŝ_n) ≳ 𝔼^{H}_n(𝟙 P^{(n)})`
  and `𝔼^{H}_n(Ŝ_n) ≳ s`. Route: on `G'` eventually `a_n > s ⟹ truthAt = 1` and `a_n ≤ s ⟹
  truthAt = 0` (`engineA_truth`, costing T1's `hz`), so in every completed-theory world of
  `Hplus`'s process the payouts satisfy `𝟙(P ∧ q) + s·𝟙(∼q) − 𝟙(P) ≥ 0` and `… − s ≥ 0`; FAF's
  one-sided provability induction on the gated three-sentence combination (`gated_three_ge`)
  carries each to the prices, and FAF's `thm:ei` (`lic_expectation_indicator_unconditional`) moves
  from sentence prices to the indicator expectations.
* **T4b** (`thresholdAbove_onG`, `valueConst_onG`): the on-`G'` **above-threshold inequality**
  `𝔼^{H}_n(𝟙(P ∧ q)) − s·𝔼^{H}_n(𝟙 q) ≳ 0`, the same engine; and Value against the constant on
  `def-lattice`'s own hedged menu object `twoOptionComb s XW W` (`XW = 𝟙(P ∧ q)`, `W = 𝟙 q`),
  through `twoOptionComb_expect` — the witness identity `𝔼_n(Ŝ_wit) − s = 𝔼_n(XW) − s·𝔼_n(W)` is
  `def-lattice`'s, cited, not re-proved. The converse of the mandate ("this preference already
  forces the conditional tower") is `def-lattice`'s `twoOptionComb_value_iff_productForm`
  (global form); along `G'` it is `valueConst_onG ↔ thresholdAbove_onG` by the same identity.

Trap avoided: nothing here is named `Value` — `def-lattice`'s `Value` quantifies over all menus;
this is the fixed two-option menu (`valueTwoOption_onG`). The `k+1`-option form (T4c, stretch)
is not built.
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin Cleanroom.Found.DefLattice
open Filter Topology

/-! ## A. The ledger literal and the followed strategy -/

/-- The ledger literal "`a_n > s`": the quote item's threshold atom at `s`, decided in the advised
reasoner's process at the published quote (strict polarity, disclosure (β)).
Source: mandate T4 (`q n := (ledgerLuv 0 n).gt s`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def followLiteral (s : ℚ) (n : ℕ) : Sentence := (ledgerLuv 0 n).gt s

/-- `followLiteral_codes`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem followLiteral_codes (s : ℚ) : MachineSentenceCodes (followLiteral s) :=
  ledgerLuv_gt_sentenceCodes 0 s

/-- In a completed-theory world of the advised reasoner's process, the ledger literal holds iff
`s < a_n`.
Source: none: infrastructure (`def-tracking-pin` `ledgerLuv_gt_holds_iff`)
Kind: L
Fidelity: n/a -/
theorem holds_followLiteral_iff (S : FrozenSystem) (s : ℚ) (n : ℕ) (w : PCWorld)
    (hw : w.ConsistentWithTheory S.processH) : w.Holds (followLiteral s n) ↔ s < S.a n := by
  rw [followLiteral,
    ledgerLuv_gt_holds_iff S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY) 0 n s w hw]
  rfl

/-- **The followed strategy** on the menu `{P^{(n)}, const s}`: take `P^{(n)}` when the ledger says
`a_n > s`, the constant `s` otherwise — `𝟙(P^{(n)} ∧ q_n) + s·𝟙(∼q_n)` as a LUV combination.
Source: [[frozen-deliberation-deference-v6]] T4 (`Ŝ_n := O^{j*(n)}_n`); mandate T4
Kind: D
Fidelity: variant: hard selection by the settled ledger literal (no continuity), two-option menu
Hyps: n/a -/
def followed (S : FrozenSystem) (s : ℚ) (n : ℕ) : LUVCombination :=
  ⟨EF.const 0, [(EF.const 1, LUV.indicatorOf (S.contract n ⋏ followLiteral s n)),
    (EF.const s, LUV.indicatorOf (∼followLiteral s n))]⟩

/-- `followed_expect`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem followed_expect (S : FrozenSystem) (s : ℚ) (P : History) (n : ℕ) :
    (followed S s n).expect P n =
      (LUV.indicatorOf (S.contract n ⋏ followLiteral s n)).expect P n +
        (s : ℝ) * (LUV.indicatorOf (∼followLiteral s n)).expect P n := by
  simp [followed, LUVCombination.expect, LUVCombination.expectAt, LUV.expect]

/-! ## B. The polarity pattern on `G'`, from `engineA_truth` -/

/-- Eventually on `G'`, the quote is on the right side of the threshold: `truthAt = 1 ⟹ s < a_n`
and `truthAt = 0 ⟹ a_n < s` (from `engineA_truth` at tolerance `min s (1 − s) / 2`).
Source: mandate T4a ("on `G'` eventually `a_n > s ⟹ truthAt = 1` and `a_n ≤ s ⟹ truthAt = 0`")
Kind: L
Fidelity: n/a
Hyps: (c) `hz` through T1; all else (a) -/
theorem polarity_onG (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) (s : ℚ) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ∀ᶠ n in atTop, t n = 0 → (truthAt S n = 1 → s < S.a n) ∧ (truthAt S n = 0 → S.a n < s) := by
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
  have hδ : (0 : ℝ) < min (s : ℝ) (1 - s) / 2 := by
    apply half_pos
    exact lt_min hs0' (by linarith)
  filter_upwards [engineA_truth S ε hε hG zhat hz hlim _ hδ] with n hn h0
  have h := abs_le.1 (hn h0)
  have hm1 : min (s : ℝ) (1 - s) / 2 ≤ s / 2 := by
    have := min_le_left (s : ℝ) (1 - s); linarith
  have hm2 : min (s : ℝ) (1 - s) / 2 ≤ (1 - s) / 2 := by
    have := min_le_right (s : ℝ) (1 - s); linarith
  constructor
  · intro h1
    rw [h1] at h
    push_cast at h
    have : (s : ℝ) < S.a n := by linarith
    exact_mod_cast this
  · intro h1
    rw [h1] at h
    push_cast at h
    have : (S.a n : ℝ) < s := by linarith
    exact_mod_cast this

/-! ## C. T4a: Value on `G'`, two-option -/

/-- **T4a — two-option Value on `G'`** (headline). Along every e.c. sub-fragment `G'`, the advised
reasoner's expectation of the followed strategy dominates its expectation of the option `P^{(n)}`
and the constant `s`: for every `δ > 0`, eventually on `G'`,
`𝔼^{H}_n(Ŝ_n) ≥ 𝔼^{H}_n(𝟙 P^{(n)}) − δ` and `𝔼^{H}_n(Ŝ_n) ≥ s − δ`.
Route: the polarity pattern on `G'` (`polarity_onG`, from T1 through `engineA_truth`) makes the
world payouts satisfy `𝟙(P ∧ q) + s·𝟙(∼q) ≥ 𝟙(P)` and `≥ s` in every completed-theory world of
`Hplus`'s process; `gated_three_ge` carries each inequality to the day-`n` prices along `G'`;
FAF's `thm:ei` identifies each indicator expectation with the sentence price. The four-liner of
the source (two tower steps, two carries) is here one gated provability-induction step per
inequality, because at a two-option menu the selected option is a settled literal. Roles:
`Hplus` the advised reasoner, `A` the predictor (through T1). **Two-way** through T1:
`partial: over timely_cofinite_const` (the on-`G` pair of record, repair round 2) and `hz` at
that pair.
Source: [[frozen-deliberation-deference-v6]] T4 (lines 106–116; anson-021); [[deference-in-logical-induction-v6]] §5.5 T4 (root-deference-042); [[AUDIT]] §3.3 (`value_on_G`, "bottoms out in named antecedents" — here it bottoms out in settlement)
Kind: C
Fidelity: variant: two-option menu with hard selection by the ledger literal; along e.c. sub-fragments; plain trader class
Hyps: (c) `hz` through T1 (checklist row 6); all else (a) -/
theorem valueTwoOption_onG (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) (s : ℚ) (hs0 : 0 < s)
    (hs1 : s < 1) :
    (∀ δ > 0, ∀ᶠ n in atTop, t n = 0 →
      (LUV.indicatorOf (S.contract n)).expect S.Hplus n - δ ≤ (followed S s n).expect S.Hplus n) ∧
    (∀ δ > 0, ∀ᶠ n in atTop, t n = 0 → (s : ℝ) - δ ≤ (followed S s n).expect S.Hplus n) := by
  haveI := S.Hplus_inductor
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
  -- codes
  have hPq : MachineSentenceCodes (fun n => S.contract n ⋏ followLiteral s n) :=
    S.contract_codes.and (followLiteral_codes s)
  have hnq : MachineSentenceCodes (fun n => ∼followLiteral s n) := (followLiteral_codes s).neg
  -- `thm:ei` for the three indicator families
  have hei1 := lic_expectation_indicator_unconditional S.Hplus S.processH _ hPq S.hworldH
  have hei2 := lic_expectation_indicator_unconditional S.Hplus S.processH _ hnq S.hworldH
  have hei3 := lic_expectation_indicator_unconditional S.Hplus S.processH _ S.contract_codes
    S.hworldH
  -- the world payouts on `G'`
  have hpay : ∀ᶠ n in atTop, t n = 0 → ∀ w : PCWorld, w.ConsistentWithTheory S.processH →
      (w.payout (S.contract n ⋏ followLiteral s n) + (s : ℝ) * w.payout (∼followLiteral s n) -
          w.payout (S.contract n) ≥ 0) ∧
        (w.payout (S.contract n ⋏ followLiteral s n) + (s : ℝ) * w.payout (∼followLiteral s n) -
          (s : ℝ) * w.payout (⊤ : Sentence) ≥ 0) := by
    filter_upwards [polarity_onG S ε hε hG zhat hz hlim s hs0 hs1] with n hn h0 w hw
    have hb := S.consistentWithTheory_base_of_subset S.base_subset_processH hw
    have hq := holds_followLiteral_iff S s n w hw
    have hP := truthAt_holds (hG n h0).1 hb
    rw [payout_top]
    rcases truthAt_eq_zero_or_one S n with hz0 | ho
    · -- truth `0`: `a_n < s`, so `q` fails, `P` fails
      have hqf : ¬ w.Holds (followLiteral s n) := fun hh => by
        have := hq.1 hh; have := (hn h0).2 hz0; linarith
      have hPf : ¬ w.Holds (S.contract n) := fun hh => by
        have := hP.1 hh; rw [hz0] at this; norm_num at this
      simp only [PCWorld.payout, PCWorld.holds_and, PCWorld.holds_neg, hqf, hPf, and_false,
        if_false, not_false_eq_true, if_true]
      constructor <;> linarith
    · -- truth `1`: `s < a_n`, so `q` holds, `P` holds
      have hqt : w.Holds (followLiteral s n) := hq.2 ((hn h0).1 ho)
      have hPt : w.Holds (S.contract n) := hP.2 ho
      simp only [PCWorld.payout, PCWorld.holds_and, PCWorld.holds_neg, hqt, hPt, and_self,
        if_true, not_true_eq_false, if_false]
      constructor <;> linarith
  -- the two price inequalities along `G'`
  have hge1 := gated_three_ge S.Hplus S.processH S.hworldH ht hPq hnq S.contract_codes s 1
    hs0.le (by linarith) (by
      filter_upwards [hpay] with n hn h0 w hw
      have := (hn h0 w hw).1
      push_cast
      linarith)
  have hge2 := gated_three_ge S.Hplus S.processH S.hworldH ht hPq hnq
    (MachineSentenceCodes.const ⊤) s s hs0.le (by linarith) (by
      filter_upwards [hpay] with n hn h0 w hw
      exact (hn h0 w hw).2)
  constructor
  · intro δ hδ
    filter_upwards [hge1 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 hei1 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 hei2 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 hei3 (δ / 4) (by positivity)] with n h1 h2 h3 h4 h0
    have h1' := h1 h0
    obtain ⟨a1, a2⟩ := abs_le.1 h2
    obtain ⟨b1, b2⟩ := abs_le.1 h3
    obtain ⟨c1, c2⟩ := abs_le.1 h4
    rw [followed_expect]
    push_cast at h1'
    nlinarith [hs0', hs1']
  · intro δ hδ
    -- the price of `⊤` tends to `1` (provability induction at a constant family)
    have htop := lic_provind_true S.Hplus S.processH (fun _ => (⊤ : Sentence))
      (MachineSentenceCodes.const ⊤) (fun _ v _ => PCWorld.holds_top v) S.hworldH
    filter_upwards [hge2 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 hei1 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 hei2 (δ / 4) (by positivity),
      asympEq_iff_eventuallyWithin.1 htop (δ / 4) (by positivity)] with n h1 h2 h3 h4 h0
    have h1' := h1 h0
    obtain ⟨a1, a2⟩ := abs_le.1 h2
    obtain ⟨b1, b2⟩ := abs_le.1 h3
    obtain ⟨c1, c2⟩ := abs_le.1 h4
    have hsT : (s : ℝ) - δ / 4 ≤ (s : ℝ) * S.Hplus n (⊤ : Sentence) := by
      nlinarith [hs0', hs1', hδ]
    have hsB : (s : ℝ) * S.Hplus n (∼followLiteral s n) - δ / 4 ≤
        (s : ℝ) * (LUV.indicatorOf (∼followLiteral s n)).expect S.Hplus n := by
      nlinarith [hs0', hs1', hδ]
    rw [followed_expect]
    linarith

/-! ## D. T4b: the above-threshold inequality and Value against the constant -/

/-- **T4b, the on-`G'` above-threshold inequality**: along `G'`,
`𝔼^{H}_n(𝟙(P^{(n)} ∧ q_n)) − s·𝔼^{H}_n(𝟙 q_n) ≥ −δ` eventually, for every `δ > 0` — the
conclusion of a threshold inequality above `s` at the ledger literal, by the same engine
(`gated_three_ge` at `φ₁ = P ∧ q`, `c₂ = 0`, `φ₃ = q`, `c₃ = s`) and `thm:ei`. T4a restated at
the witness menu.
Source: [[frozen-deliberation-deference-v6]] T4 converse ("`E_n((X − s)·𝟙[A(X) ≥ s])`"); mandate T4b; [[two-option-value-iff-total-trust]] (via `def-lattice`)
Kind: C
Fidelity: variant: along e.c. sub-fragments; the weight is the settled ledger literal
Hyps: (c) `hz` through T1; all else (a) -/
theorem thresholdAbove_onG (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) (s : ℚ) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ∀ δ > 0, ∀ᶠ n in atTop, t n = 0 →
      -δ ≤ (LUV.indicatorOf (S.contract n ⋏ followLiteral s n)).expect S.Hplus n -
        (s : ℝ) * (LUV.indicatorOf (followLiteral s n)).expect S.Hplus n := by
  haveI := S.Hplus_inductor
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
  have hPq : MachineSentenceCodes (fun n => S.contract n ⋏ followLiteral s n) :=
    S.contract_codes.and (followLiteral_codes s)
  have hei1 := lic_expectation_indicator_unconditional S.Hplus S.processH _ hPq S.hworldH
  have hei2 := lic_expectation_indicator_unconditional S.Hplus S.processH _
    (followLiteral_codes s) S.hworldH
  have hge := gated_three_ge S.Hplus S.processH S.hworldH ht hPq
    (MachineSentenceCodes.const ⊤) (followLiteral_codes s) 0 s le_rfl (by linarith) (by
      filter_upwards [polarity_onG S ε hε hG zhat hz hlim s hs0 hs1] with n hn h0 w hw
      have hb := S.consistentWithTheory_base_of_subset S.base_subset_processH hw
      have hq := holds_followLiteral_iff S s n w hw
      have hP := truthAt_holds (hG n h0).1 hb
      rcases truthAt_eq_zero_or_one S n with hz0 | ho
      · have hqf : ¬ w.Holds (followLiteral s n) := fun hh => by
          have := hq.1 hh; have := (hn h0).2 hz0; linarith
        have hPf : ¬ w.Holds (S.contract n) := fun hh => by
          have := hP.1 hh; rw [hz0] at this; norm_num at this
        simp only [PCWorld.payout, PCWorld.holds_and, hqf, hPf, and_false, if_false]
        push_cast
        linarith
      · have hqt : w.Holds (followLiteral s n) := hq.2 ((hn h0).1 ho)
        have hPt : w.Holds (S.contract n) := hP.2 ho
        simp only [PCWorld.payout, PCWorld.holds_and, hqt, hPt, and_self, if_true]
        push_cast
        linarith)
  intro δ hδ
  filter_upwards [hge (δ / 3) (by positivity),
    asympEq_iff_eventuallyWithin.1 hei1 (δ / 3) (by positivity),
    asympEq_iff_eventuallyWithin.1 hei2 (δ / 3) (by positivity)] with n h1 h2 h3 h0
  have h1' := h1 h0
  obtain ⟨a1, a2⟩ := abs_le.1 h2
  obtain ⟨b1, b2⟩ := abs_le.1 h3
  push_cast at h1'
  nlinarith [hs0', hs1']

/-- **T4b, Value against the constant on `def-lattice`'s hedged menu object**: along `G'`, the
advised reasoner's expectation of `def-lattice`'s `twoOptionComb s XW W` (the strategy
`XW + s(1 − W)`, at `XW = 𝟙(P ∧ q)`, `W = 𝟙 q`) is at least `s − δ` eventually. By
`def-lattice`'s witness identity `twoOptionComb_expect` (`𝔼_n(Ŝ_wit) = 𝔼_n(XW) + s − s·𝔼_n(W)`,
cited, not re-proved) from `thresholdAbove_onG`; the global biconditional is `def-lattice`'s
`twoOptionComb_value_iff_productForm`, which this instantiates along `G'`.
Source: [[frozen-deliberation-deference-v6]] T4 converse; mandate T4b ("cite"); `def-lattice` T6c
Kind: L
Fidelity: variant: along e.c. sub-fragments
Hyps: (c) `hz` through T1; all else (a) -/
theorem valueConst_onG (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) (s : ℚ) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ∀ δ > 0, ∀ᶠ n in atTop, t n = 0 → (s : ℝ) - δ ≤
      (twoOptionComb s (fun n => LUV.indicatorOf (S.contract n ⋏ followLiteral s n))
        (fun n => LUV.indicatorOf (followLiteral s n)) n).expect S.Hplus n := by
  intro δ hδ
  filter_upwards [thresholdAbove_onG S ε hε ht hG zhat hz hlim s hs0 hs1 δ hδ] with n hn h0
  rw [twoOptionComb_expect]
  linarith [hn h0]

end Cleanroom.Deference.DefFrozenSibling
