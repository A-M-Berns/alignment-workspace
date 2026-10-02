import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# T4 — Tower ⟹ soft Total Trust (both halves) and the band limit-equality

Package `def-lattice-arrows`, file 3. [[tower-implies-total-trust]] in the true LI setting
over `def-lattice`'s objects: one Tower instance at the weighted bet `XW`, the expert's
asymptotic fold (`ExpertFoldAt`), and ramp arithmetic give each threshold inequality.

The chain, per instance (§Proof of the page):
`E^H_n(XW_n) ≈ₙ E^H_n(⌜E*(XW_n)⌝)` (Tower at `XW`) — then `⌜E*(XW_n)⌝ − s·W_n` is valued at
`E*(XW_n) − s·wt(E*(X_n))`, which is within the fold's `o(1)` of
`(E*(X_n) − s)·wt(E*(X_n)) ≥ 0` because the weight is positive only where the estimate exceeds
`s` (fact (c), `ctsInd_pos_iff`); T0 at `0` and `loe`-by-definition finish.

* `thresholdAbove_instance_of_tower` / `thresholdBelow_instance_of_tower`: the generic form,
  for any nonnegative weight positive only above (below) the threshold — the page's
  observation that "any `[0,1]`-valued weight vanishing wherever the quote is at most `v`
  would satisfy it" (the slope is never used).
* `softAbove_instance`, `softBelow_instance` (ramps), `bandAbove_instance`,
  `bandBelow_instance` (the band pinch, vq-wiki-005): instances.
* Predicate level: `softTotalTrustAbove_of_tower`, `softTotalTrustBelow_of_tower`,
  `totalTrust_of_tower`, `bandReflection_of_tower`, with the existence of the product quotes
  (`ProductQuotesAvailable`) and the fold (`ExpertFoldsAt`) as named clauses.

The below half is derived directly, not as the `−V` instance of the above half: `[0,1]`-LUVs
have no negation (the page's "Lipschitz wrinkle" does not arise).
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **Ramp arithmetic, above** (fact (c)): a nonnegative weight positive only above `s` makes
`(x − s) · wt x ≥ 0`.
Source: [[tower-implies-total-trust]] §Three facts (c)
Kind: L
Fidelity: exact -/
theorem sub_mul_wt_nonneg {wt : ℝ → ℝ} {s : ℝ} (hwt : ∀ x, 0 ≤ wt x)
    (hsupp : ∀ x, 0 < wt x → s < x) (x : ℝ) : 0 ≤ (x - s) * wt x := by
  rcases (hwt x).lt_or_eq with h | h
  · exact mul_nonneg (by linarith [hsupp x h]) (hwt x)
  · rw [← h, mul_zero]

/-- **Ramp arithmetic, below**: a nonnegative weight positive only below `s` makes
`(x − s) · wt x ≤ 0`.
Source: [[tower-implies-total-trust]] §The other direction (the low side)
Kind: L
Fidelity: exact -/
theorem sub_mul_wt_nonpos {wt : ℝ → ℝ} {s : ℝ} (hwt : ∀ x, 0 ≤ wt x)
    (hsupp : ∀ x, 0 < wt x → x < s) (x : ℝ) : (x - s) * wt x ≤ 0 := by
  rcases (hwt x).lt_or_eq with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hsupp x h]) (hwt x)
  · rw [← h, mul_zero]

/-- The key expectation: `E^H_n(⌜E*(XW_n)⌝) − s·E^H_n(W_n)` is the expectation of the
combination `Y_n − s·W_n`, valued at `E*(XW_n) − s·wt(E*(X_n))` in every consistent world.
Source: [[tower-implies-total-trust]] §Proof, third step, move 1 (the difference bet `D_n`)
Kind: L
Fidelity: exact -/
theorem quoteComb_expect (s : ℚ) (Y W : ℕ → LUV) (n : ℕ) :
    (listComb (fun _ => 0) [(1, Y), (-s, W)] n).expect P n =
      (Y n).expect P n - (s : ℝ) * (W n).expect P n := by
  simp [listComb_expect, sub_eq_add_neg]

/-- **The above-threshold inequality from one Tower instance, generic weight** (T4, the
content): for a nonnegative weight `wt` positive only above `s`, a `WeightQuote` `(W, XW)` of
`X` at `wt`, an e.c. quote `Y` reflecting `E*(XW)`, the Tower instance
`E^H_n(XW_n) ≈ₙ E^H_n(Y_n)` and the expert's fold `E*(XW_n) ≈ₙ wt(E*(X_n))·E*(X_n)`:
`E^H_n(XW_n) − s·E^H_n(W_n) ≳ₙ 0`.
Source: [[tower-implies-total-trust]] §Proof (the three-step chain); v6 §1.6 first display
(root-deference-005); vq-wiki-004
Kind: C
Fidelity: exact (unnormalized product form)
Hyps: (a) the Tower instance `hT` and the package `q` (data; the self-instance of `hT` is
FAF's `thm:cee` on `XW`); (b)/(c) `hfold` — `ExpertFoldAt`, the expert's own `loe` at the
deferred day: `(b)` for the self-expert (FAF `thm:loe`/`thm:er`, day-`f n` pull-back not in
FAF), `(c)` for a general expert; `hworld` -/
theorem thresholdAbove_instance_of_tower [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW Y : ℕ → LUV} {wt : ℝ → ℝ} {s : ℚ} (hwt : ∀ x, 0 ≤ wt x)
    (hsupp : ∀ x, 0 < wt x → (s : ℝ) < x) (q : WeightQuote DP E X wt W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X wt XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have h := expect_listComb_ge_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, Y), (-s, W)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hY
      · exact q.weight_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hYr n v hv⟩
      · exact fun n v hv => ⟨_, q.weight_reflected n v hv⟩))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [asympEq_eventually_abs_le hfold hε] with n hn v hv ν hν
      have hYv := listComb_valuesAt_mem hν (p := (1, Y)) (by simp)
      have hWv := listComb_valuesAt_mem hν (p := (-s, W)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hYv.eq (hYr n v hv), hWv.eq (q.weight_reflected n v hv)]
      have hramp := sub_mul_wt_nonneg hwt hsupp (E.estimate X n)
      rw [abs_le] at hn
      push_cast
      nlinarith [hn.1, hramp]) hworld
  have h0 : (fun _ => (0 : ℝ)) ≲ₙ (fun n => (Y n).expect P n - (s : ℝ) * (W n).expect P n) := by
    refine fun ε hε => ?_
    filter_upwards [h ε hε] with n hn
    rwa [quoteComb_expect] at hn
  have hEq : (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≈ₙ
      (fun n => (Y n).expect P n - (s : ℝ) * (W n).expect P n) :=
    hT.sub (AsympEq.refl _)
  exact h0.trans_asympEq hEq.symm

/-- **The below-threshold inequality from one Tower instance, generic weight**: the mirror of
`thresholdAbove_instance_of_tower` for a weight positive only below `s`, derived directly
(not as a `−V` instance: `[0,1]`-LUVs have no negation).
Source: [[tower-implies-total-trust]] §The other direction (the low side)
Kind: C
Fidelity: exact
Hyps: as `thresholdAbove_instance_of_tower` -/
theorem thresholdBelow_instance_of_tower [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW Y : ℕ → LUV} {wt : ℝ → ℝ} {s : ℚ} (hwt : ∀ x, 0 ≤ wt x)
    (hsupp : ∀ x, 0 < wt x → x < (s : ℝ)) (q : WeightQuote DP E X wt W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X wt XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) := by
  have h := expect_listComb_le_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, Y), (-s, W)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hY
      · exact q.weight_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun n v hv => ⟨_, hYr n v hv⟩
      · exact fun n v hv => ⟨_, q.weight_reflected n v hv⟩))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [asympEq_eventually_abs_le hfold hε] with n hn v hv ν hν
      have hYv := listComb_valuesAt_mem hν (p := (1, Y)) (by simp)
      have hWv := listComb_valuesAt_mem hν (p := (-s, W)) (by simp)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hYv.eq (hYr n v hv), hWv.eq (q.weight_reflected n v hv)]
      have hramp := sub_mul_wt_nonpos hwt hsupp (E.estimate X n)
      rw [abs_le] at hn
      push_cast
      nlinarith [hn.2, hramp]) hworld
  have h0 : (fun n => (Y n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) := by
    refine fun ε hε => ?_
    filter_upwards [h ε hε] with n hn
    rwa [quoteComb_expect] at hn
  have hEq : (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≈ₙ
      (fun n => (Y n).expect P n - (s : ℝ) * (W n).expect P n) :=
    hT.sub (AsympEq.refl _)
  exact hEq.trans_asympLE h0

/-! ### The ramp instances: soft Total Trust, both halves -/

/-- **Tower ⟹ soft Total Trust, above half, per instance** (T4): at the ramp `rampAbove δ s`,
`0 < δ`, with the Tower instance at `XW` and the expert's fold.
Source: [[tower-implies-total-trust]] §Proof; v6 §1.6 (root-deference-005); vq-wiki-004
Kind: C
Fidelity: exact
Hyps: as `thresholdAbove_instance_of_tower` -/
theorem softAbove_instance [IsLogicalInductor P DP] {E : Expert DP} {X W XW Y : ℕ → LUV}
    {s δ : ℚ} (hδ : 0 < δ) (q : WeightQuote DP E X (rampAbove δ s) W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X (rampAbove δ s) XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) :=
  thresholdAbove_instance_of_tower (fun x => ctsInd_nonneg δ x s)
    (fun x h => (ctsInd_pos_iff hδ x s).mp h) q hY hYr hT hfold hworld

/-- **Tower ⟹ soft Total Trust, below half, per instance** (T4): at the down-ramp
`rampBelow δ s`, positive only where the estimate is below `s`.
Source: [[tower-implies-total-trust]] §The other direction (the low side); vq-wiki-004
Kind: C
Fidelity: exact
Hyps: as `thresholdAbove_instance_of_tower` -/
theorem softBelow_instance [IsLogicalInductor P DP] {E : Expert DP} {X W XW Y : ℕ → LUV}
    {s δ : ℚ} (hδ : 0 < δ) (q : WeightQuote DP E X (rampBelow δ s) W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X (rampBelow δ s) XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ)) :=
  thresholdBelow_instance_of_tower (fun x => ctsInd_nonneg δ s x)
    (fun x h => (ctsInd_pos_iff hδ s x).mp h) q hY hYr hT hfold hworld

/-! ### The band instances: the limit-equality (soft value-Reflection) -/

/-- **The support of the band weight** (`0 < δ`): `bandWt δ s ε q > 0` iff
`s − ε < q < s + ε`. Not symmetric in the ramp width: the up-ramp is positive strictly above
`s − ε`, the down-ramp strictly below `s + ε`, both climbing over a `δ`-strip inside the band.
Source: [[tower-implies-total-trust]] §The limit-equality ("positive only where the quote
lies strictly between `s − ε` and `s + ε`"); mandate T4
Kind: L
Fidelity: exact -/
theorem bandWt_pos_iff {δ : ℚ} (hδ : 0 < δ) (s ε : ℚ) (q : ℝ) :
    0 < bandWt δ s ε q ↔ ((s : ℝ) - ε < q ∧ q < (s : ℝ) + ε) := by
  simp only [bandWt]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · have := (ctsInd_pos_iff hδ _ _).mp h1
      have := (ctsInd_pos_iff hδ _ _).mp h2
      constructor <;> linarith
    · exact absurd h1 (not_lt.mpr (ctsInd_nonneg _ _ _))
  · rintro ⟨h1, h2⟩
    refine mul_pos ((ctsInd_pos_iff hδ _ _).mpr ?_) ((ctsInd_pos_iff hδ _ _).mpr ?_) <;>
      linarith

/-- The band weight is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bandWt_nonneg (δ s ε : ℚ) (q : ℝ) : 0 ≤ bandWt δ s ε q :=
  mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)

/-- **Band pinch, lower face, per instance** (vq-wiki-005): at the band weight `bandWt δ s ε`
(`0 < δ`), the above-threshold inequality at `s − ε`, from the Tower instance at the band
product and the fold. No relation between `ε` and `δ` is needed for the pinch itself (the
page's `ε > δ` is not used).
Source: [[tower-implies-total-trust]] §The limit-equality; [[reflection-in-li]] §The value
form is a theorem
Kind: C
Fidelity: exact
Hyps: as `thresholdAbove_instance_of_tower` -/
theorem bandAbove_instance [IsLogicalInductor P DP] {E : Expert DP} {X W XW Y : ℕ → LUV}
    {s ε δ : ℚ} (hδ : 0 < δ) (q : WeightQuote DP E X (bandWt δ s ε) W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X (bandWt δ s ε) XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - ((s - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
      (fun _ => (0 : ℝ)) :=
  thresholdAbove_instance_of_tower (bandWt_nonneg δ s ε)
    (fun x h => by push_cast; exact ((bandWt_pos_iff hδ s ε x).mp h).1) q hY hYr hT hfold hworld

/-- **Band pinch, upper face, per instance** (vq-wiki-005): the below-threshold inequality at
`s + ε` on the same band weight.
Source: [[tower-implies-total-trust]] §The limit-equality
Kind: C
Fidelity: exact
Hyps: as `thresholdAbove_instance_of_tower` -/
theorem bandBelow_instance [IsLogicalInductor P DP] {E : Expert DP} {X W XW Y : ℕ → LUV}
    {s ε δ : ℚ} (hδ : 0 < δ) (q : WeightQuote DP E X (bandWt δ s ε) W XW)
    (hY : LUV.MachineThresholdCodeSeq Y) (hYr : Reflects DP E XW Y)
    (hT : (fun n => (XW n).expect P n) ≈ₙ (fun n => (Y n).expect P n))
    (hfold : ExpertFoldAt DP E X (bandWt δ s ε) XW)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - ((s + ε : ℚ) : ℝ) * (W n).expect P n) ≲ₙ
      (fun _ => (0 : ℝ)) :=
  thresholdBelow_instance_of_tower (bandWt_nonneg δ s ε)
    (fun x h => by push_cast; exact ((bandWt_pos_iff hδ s ε x).mp h).2) q hY hYr hT hfold hworld

/-! ### Predicate level -/

/-- **Existence of the product quote** `⌜E*(XW)⌝` for every weight quote at `wt`: the channel
clause of [[tower-implies-total-trust]] ("the ramp's argument is a published quote, so
`V_n · w_n` is an e.d. LUV" whose expert estimate the ledger prices). `(c)` for a general
expert (`li-quote-lane`); for the self-expert FAF's `Construction/Quotation` builds it
(`Witness.lean`).
Source: [[tower-implies-total-trust]] §Hypotheses (T); mandate T4
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def ProductQuotesAvailable (DP : DeductiveProcess) (E : Expert DP) (wt : ℝ → ℝ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
    ∃ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y ∧ Reflects DP E XW Y

/-- **The expert folds every weight quote at `wt`**: `ExpertFoldAt` for every `WeightQuote` of
every e.c. source at the weight function `wt` — the expert-side hypothesis of the arrow,
asymptotic ((b) for the self-expert, (c) in general; see `ExpertFoldAt`).
Source: [[tower-implies-total-trust]] §Hypotheses ("Expert side: its own `loe`, nothing more")
Kind: D
Fidelity: variant: asymptotic -/
def ExpertFoldsAt (DP : DeductiveProcess) (E : Expert DP) (wt : ℝ → ℝ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → WeightQuote DP E X wt W XW →
    ExpertFoldAt DP E X wt XW

/-- A weight quote's product LUV is world-valued (from `source_valued` and
`product_reflected`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weightQuote_product_valued {E : Expert DP} {X W XW : ℕ → LUV} {wt : ℝ → ℝ}
    (q : WeightQuote DP E X wt W XW) : Valued DP XW := by
  intro n v hv
  obtain ⟨x, hx⟩ := q.source_valued n v hv
  obtain ⟨z, hz, -⟩ := q.product_reflected n v hv x hx
  exact ⟨z, hz⟩

/-- **Tower on valued sources ⟹ soft Total Trust, above half** (predicate level): the
product quotes are valued (`source_valued`), so `TowerValued` suffices.
Source: [[tower-implies-total-trust]]; vq-wiki-004
Kind: L
Fidelity: exact
Hyps: (c) `ProductQuotesAvailable` (existence of the product quotes), `ExpertFoldsAt`
((b) self / (c) general); `TowerValued` is the deference hypothesis; `hworld` -/
theorem softTotalTrustAbove_of_towerValued [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) {s δ : ℚ} (hδ : 0 < δ)
    (hq : ProductQuotesAvailable DP E (rampAbove δ s)) (hf : ExpertFoldsAt DP E (rampAbove δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustAbove P DP E s δ := by
  intro X W XW hX q
  obtain ⟨Y, hY, hYr⟩ := hq X W XW hX q
  exact softAbove_instance hδ q hY hYr (hT XW Y q.product_codes hY (weightQuote_product_valued q) hYr)
    (hf X W XW hX q) hworld

/-- **Tower on valued sources ⟹ soft Total Trust, below half** (predicate level).
Source: [[tower-implies-total-trust]] §The other direction
Kind: L
Fidelity: exact
Hyps: as `softTotalTrustAbove_of_towerValued` -/
theorem softTotalTrustBelow_of_towerValued [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E) {s δ : ℚ} (hδ : 0 < δ)
    (hq : ProductQuotesAvailable DP E (rampBelow δ s)) (hf : ExpertFoldsAt DP E (rampBelow δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustBelow P DP E s δ := by
  intro X W XW hX q
  obtain ⟨Y, hY, hYr⟩ := hq X W XW hX q
  exact softBelow_instance hδ q hY hYr (hT XW Y q.product_codes hY (weightQuote_product_valued q) hYr)
    (hf X W XW hX q) hworld

/-- **Tower on valued sources ⟹ Total Trust** (predicate level): both halves at every
rational threshold and positive width, given product quotes and folds at every ramp.
Source: [[tower-implies-total-trust]] §Place in the circuit ("the loop closes")
Kind: L
Fidelity: exact
Hyps: (c) product quotes at every ramp; the folds ((b) self / (c) general); `TowerValued`;
`hworld` -/
theorem totalTrust_of_towerValued [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E)
    (hq : ∀ s δ : ℚ, 0 < δ → ProductQuotesAvailable DP E (rampAbove δ s) ∧
      ProductQuotesAvailable DP E (rampBelow δ s))
    (hf : ∀ s δ : ℚ, 0 < δ → ExpertFoldsAt DP E (rampAbove δ s) ∧
      ExpertFoldsAt DP E (rampBelow δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TotalTrust P DP E :=
  fun s δ hδ => ⟨softTotalTrustAbove_of_towerValued hT hδ (hq s δ hδ).1 (hf s δ hδ).1 hworld,
    softTotalTrustBelow_of_towerValued hT hδ (hq s δ hδ).2 (hf s δ hδ).2 hworld⟩

/-- **Tower on valued sources ⟹ band Reflection** (predicate level, vq-wiki-005): the
two-sided pinch at every band, given product quotes and folds at every band weight.
Source: [[tower-implies-total-trust]] §The limit-equality; [[reflection-in-li]] §The value
form is a theorem
Kind: L
Fidelity: exact (unnormalized; the normalized reading divides by the band mass and is a
remark)
Hyps: (c) product quotes at every band; the folds ((b) self / (c) general); `TowerValued`;
`hworld` -/
theorem bandReflection_of_towerValued [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TowerValued P DP E)
    (hq : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ProductQuotesAvailable DP E (bandWt δ s ε))
    (hf : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ExpertFoldsAt DP E (bandWt δ s ε))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BandReflection P DP E := by
  intro s ε δ hε hδ
  constructor
  · intro X W XW hX q
    obtain ⟨Y, hY, hYr⟩ := hq s ε δ hε hδ X W XW hX q
    exact bandAbove_instance hδ q hY hYr (hT XW Y q.product_codes hY (weightQuote_product_valued q) hYr)
      (hf s ε δ hε hδ X W XW hX q) hworld
  · intro X W XW hX q
    obtain ⟨Y, hY, hYr⟩ := hq s ε δ hε hδ X W XW hX q
    exact bandBelow_instance hδ q hY hYr (hT XW Y q.product_codes hY (weightQuote_product_valued q) hYr)
      (hf s ε δ hε hδ X W XW hX q) hworld

/-- **Tower ⟹ soft Total Trust, above half** (from def-lattice's `Tower`; one line over
`softTotalTrustAbove_of_towerValued`).
Source: [[tower-implies-total-trust]]; vq-wiki-004
Kind: L
Fidelity: exact
Hyps: as `softTotalTrustAbove_of_towerValued` with `Tower` in place of `TowerValued` -/
theorem softTotalTrustAbove_of_tower [IsLogicalInductor P DP] {E : Expert DP}
    (hT : Tower P DP E) {s δ : ℚ} (hδ : 0 < δ)
    (hq : ProductQuotesAvailable DP E (rampAbove δ s)) (hf : ExpertFoldsAt DP E (rampAbove δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustAbove P DP E s δ :=
  softTotalTrustAbove_of_towerValued (towerValued_of_tower hT) hδ hq hf hworld

/-- **Tower ⟹ soft Total Trust, below half** (from `Tower`).
Source: [[tower-implies-total-trust]] §The other direction
Kind: L
Fidelity: exact
Hyps: as `softTotalTrustBelow_of_towerValued` with `Tower` -/
theorem softTotalTrustBelow_of_tower [IsLogicalInductor P DP] {E : Expert DP}
    (hT : Tower P DP E) {s δ : ℚ} (hδ : 0 < δ)
    (hq : ProductQuotesAvailable DP E (rampBelow δ s)) (hf : ExpertFoldsAt DP E (rampBelow δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    SoftTotalTrustBelow P DP E s δ :=
  softTotalTrustBelow_of_towerValued (towerValued_of_tower hT) hδ hq hf hworld

/-- **Tower ⟹ Total Trust** (from `Tower`).
Source: [[tower-implies-total-trust]] §Place in the circuit
Kind: L
Fidelity: exact
Hyps: as `totalTrust_of_towerValued` with `Tower` -/
theorem totalTrust_of_tower [IsLogicalInductor P DP] {E : Expert DP} (hT : Tower P DP E)
    (hq : ∀ s δ : ℚ, 0 < δ → ProductQuotesAvailable DP E (rampAbove δ s) ∧
      ProductQuotesAvailable DP E (rampBelow δ s))
    (hf : ∀ s δ : ℚ, 0 < δ → ExpertFoldsAt DP E (rampAbove δ s) ∧
      ExpertFoldsAt DP E (rampBelow δ s))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TotalTrust P DP E :=
  totalTrust_of_towerValued (towerValued_of_tower hT) hq hf hworld

/-- **Tower ⟹ band Reflection** (from `Tower`).
Source: [[tower-implies-total-trust]] §The limit-equality
Kind: L
Fidelity: exact
Hyps: as `bandReflection_of_towerValued` with `Tower` -/
theorem bandReflection_of_tower [IsLogicalInductor P DP] {E : Expert DP} (hT : Tower P DP E)
    (hq : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ProductQuotesAvailable DP E (bandWt δ s ε))
    (hf : ∀ s ε δ : ℚ, 0 < ε → 0 < δ → ExpertFoldsAt DP E (bandWt δ s ε))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BandReflection P DP E :=
  bandReflection_of_towerValued (towerValued_of_tower hT) hq hf hworld

end

end Cleanroom.Deference.DefLatticeArrows
