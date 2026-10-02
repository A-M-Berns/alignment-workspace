import Cleanroom.Deference.DefArgmaxValue.Theorem
import Cleanroom.Deference.DefArgmaxValue.Punishing

/-!
# `def-argmax-value` · Hedged: soft self-endorsement and δ-hedged Value (target 9)

[[soft-self-endorsement]]: the soft strategy `T_δ := Σ_j θ_j O^j` with the ramp blend
`θ_j := φ_j / Σ_i φ_i`, `φ_j := Ind_δ(m^j > M − 2δ)` (`def-lattice`'s `rampBlend`), needs
neither a tie-break nor H3:

* **9a** the blend weights are generable features of the expert's day-`f n` prices: ramps of the
  expectation features against their `max` (FAF's `EF.max`, closure `PGenerableWeighting.max'`),
  normalized by `EF.safeRecip` of their sum, which is `≥ 1` (`one_le_rampPhi_sum`) so the safe
  reciprocal is exact — `blendFeature_pgenerable` for the self-expert, with the rational value
  `blendWeight` (`blendWeight_at_cast`).
* **9b** `softSelfEndorse`: for an inductor-expert whose blend weights are generable at rank `f n`
  and a `BlendQuote` for `rampBlend δ` (the blended LUV, data: its existence for the self-expert
  is a sum of `k+1` mesh products — the same two-dimensional construction as the composite,
  findings F13), `E*(T_δ) ≳ₙ M_n − 2δ`. **No fold is needed**: the weights are coefficients of
  the expert's own provind (vq-wiki-018 by lookup, findings F3). `softSelfEndorse_self` discharges
  the generability.
* **9c** `hedgedValue_of_totalTrust` (δ-hedged Value, the explicit `−2δ` — `def-lattice`'s
  `BlendValue` has no `−2δ` and is not claimed): Total Trust + ramp quotes on the composite
  `½(T_δ − O^i + 1)` + 9b ⟹ `E^P_n(T_δ) ≳ₙ E^P_n(O^i_n) − 2δ`. Survives the punishing menus:
  nothing mentions the selection.
* **9d** `rampBlend_eq_of_decisive`: with a decisive margin `η > 2δ`, the blend is the hard
  selection (`θ_{j*} = 1`, others `0`), so a `BlendQuote` is a follower within slack; the margins
  corollary `selfEndorseGE_instance_of_margin`: decisive margin ⟹ `E*(S) ≳ₙ M_n` for any follower
  — Lemma 2 with H3 swapped for a margin condition.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## Generability closure under `max` and `safeRecip` -/

/-- Generable weightings are closed under `EF.max` (FAF's `serialize_max`; the `mul` lemma's shape).
Source: none: infrastructure (FAF `PGenerableWeighting.mul`)
Kind: L
Fidelity: n/a -/
theorem PGenerableWeighting.max' {A B : ℕ → EF} (hA : PGenerableWeighting A)
    (hB : PGenerableWeighting B) : PGenerableWeighting (fun n => EF.max (A n) (B n)) where
  polySeg := MachineSpliceStream.serialize_max hA.polySeg hB.polySeg
  rank_le := by
    intro n
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨hA.rank_le n, hB.rank_le n⟩
  closed := by
    intro n ρ V
    simp only [EF.denoteWith_max]
    rw [hA.closed n ρ V, hB.closed n ρ V]
    rfl

/-- Generable weightings are closed under `EF.safeRecip`.
Source: none: infrastructure (FAF `serialize_safeRecip`)
Kind: L
Fidelity: n/a -/
theorem PGenerableWeighting.safeRecip' {A : ℕ → EF} (hA : PGenerableWeighting A) :
    PGenerableWeighting (fun n => EF.safeRecip (A n)) where
  polySeg := MachineSpliceStream.serialize_safeRecip hA.polySeg
  rank_le := by
    intro n
    simp only [EF.rank]
    exact hA.rank_le n
  closed := by
    intro n ρ V
    simp only [EF.denoteWith]
    rw [hA.closed n ρ V]
    rfl

/-- A finite `max`-fold of generable weightings is generable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pgenerable_foldr_max : ∀ (l : List (ℕ → EF)), (∀ A ∈ l, PGenerableWeighting A) →
    PGenerableWeighting (fun n => l.foldr (fun A acc => EF.max (A n) acc) (EF.const 0))
  | [], _ => by simpa using constWeighting 0
  | A :: l, h => by
    have hA := h A (List.mem_cons_self ..)
    have hl := pgenerable_foldr_max l (fun B hB => h B (List.mem_cons_of_mem _ hB))
    simpa [List.foldr_cons] using PGenerableWeighting.max' hA hl

/-- A finite `add`-fold of generable weightings is generable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pgenerable_foldr_add : ∀ (l : List (ℕ → EF)), (∀ A ∈ l, PGenerableWeighting A) →
    PGenerableWeighting (fun n => l.foldr (fun A acc => EF.add (A n) acc) (EF.const 0))
  | [], _ => by simpa using constWeighting 0
  | A :: l, h => by
    have hA := h A (List.mem_cons_self ..)
    have hl := pgenerable_foldr_add l (fun B hB => h B (List.mem_cons_of_mem _ hB))
    simpa [List.foldr_cons] using PGenerableWeighting.add hA hl

/-- The denotation of a `max`-fold is the `max`-fold of the denotations (seeded at `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem denote_foldr_max (V : History) : ∀ (l : List (ℕ → EF)) (n : ℕ),
    (l.foldr (fun A acc => EF.max (A n) acc) (EF.const 0)).denote V =
      (l.map (fun A => (A n).denote V)).foldr max 0
  | [], _ => by simp [EF.denote_const]
  | A :: l, n => by
    simp only [List.foldr_cons, List.map_cons, EF.denote_max]
    rw [denote_foldr_max V l n]

/-- The denotation of an `add`-fold is the sum of the denotations.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem denote_foldr_add (V : History) : ∀ (l : List (ℕ → EF)) (n : ℕ),
    (l.foldr (fun A acc => EF.add (A n) acc) (EF.const 0)).denote V =
      (l.map (fun A => (A n).denote V)).sum
  | [], _ => by simp [EF.denote_const]
  | A :: l, n => by
    simp only [List.foldr_cons, List.map_cons, EF.denote_add, Pi.add_apply, List.sum_cons]
    rw [denote_foldr_add V l n]

/-- `foldr max 0` over a nonnegative finite family is its `Finset.sup'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem foldr_max_ofFn_eq_sup' {k : ℕ} (m : Fin (k + 1) → ℝ) (hm : ∀ i, 0 ≤ m i) :
    (List.ofFn m).foldr max 0 = Finset.univ.sup' Finset.univ_nonempty m := by
  apply le_antisymm
  · have h : ∀ (l : List ℝ) (b : ℝ), (∀ x ∈ l, x ≤ b) → 0 ≤ b → l.foldr max 0 ≤ b := by
      intro l
      induction l with
      | nil => intro b _ hb; simpa using hb
      | cons x l ih =>
        intro b hl hb
        simp only [List.foldr_cons]
        exact max_le (hl x (List.mem_cons_self ..)) (ih b (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hb)
    refine h _ _ (fun x hx => ?_) ?_
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact Finset.le_sup' m (Finset.mem_univ i)
    · exact le_trans (hm 0) (Finset.le_sup' m (Finset.mem_univ 0))
  · rw [Finset.sup'_le_iff]
    intro i _
    have h : ∀ (l : List ℝ) (x : ℝ), x ∈ l → x ≤ l.foldr max 0 := by
      intro l
      induction l with
      | nil => intro x hx; simp at hx
      | cons y l ih =>
        intro x hx
        simp only [List.foldr_cons]
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_max_left _ _
        · exact le_trans (ih x hx) (le_max_right _ _)
    exact h _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)

/-! ## 9a — the blend weights of the self-expert as generable features -/

section Blend

variable {P : History} (market : MarketComputation P) (f : DeferralFunction) {k : ℕ}
  (M : Menu k) (δ : ℚ)

/-- The reindexed expectation feature of option `i`.
Source: mandate target 9a
Kind: D
Fidelity: n/a -/
def optFeature (i : Fin (k + 1)) (m : ℕ) : EF :=
  expectFeature (fun m => M.O i (deferralPreimage f m)) m

/-- The `max` of the option features.
Source: mandate target 9a ("`max` over `k+1` mesh sums")
Kind: D
Fidelity: n/a -/
def maxFeature (m : ℕ) : EF :=
  (List.ofFn (fun i => optFeature f M i)).foldr (fun A acc => EF.max (A m) acc) (EF.const 0)

/-- The ramp feature `φ_j = Ind_δ(e_j > max − 2δ)`.
Source: [[soft-self-endorsement]] §The soft strategy
Kind: D
Fidelity: exact -/
def phiFeature (j : Fin (k + 1)) (m : ℕ) : EF :=
  ctsIndFeature (fun _ => δ) (optFeature f M j)
    (fun m => EF.add (maxFeature f M m) (EF.const (-(2 * δ)))) m

/-- The sum of the ramp features.
Source: mandate target 9a
Kind: D
Fidelity: n/a -/
def phiSumFeature (m : ℕ) : EF :=
  (List.ofFn (fun j => phiFeature f M δ j)).foldr (fun A acc => EF.add (A m) acc) (EF.const 0)

/-- **The blend feature** `θ_j = φ_j · safeRecip(Σ_i φ_i)`, gated by the image flag.
Source: mandate target 9a ("`EF.safeRecip` applies exactly")
Kind: D
Fidelity: exact -/
def blendFeature (j : Fin (k + 1)) (m : ℕ) : EF :=
  if deferralImageFlag f m = 0 then EF.const 0 else
    EF.mul (phiFeature f M δ j m) (EF.safeRecip (phiSumFeature f M δ m))

/-- The option feature is generable.
Source: none: infrastructure (`expectFeature_pgenerable`)
Kind: L
Fidelity: n/a -/
theorem optFeature_pgenerable (i : Fin (k + 1)) : PGenerableWeighting (optFeature f M i) :=
  expectFeature_pgenerable ((M.codes i).reindex (unaryRuler_deferralPreimage f))

/-- The ungated blend feature is generable.
Source: mandate target 9a
Kind: L
Fidelity: n/a -/
theorem blendCore_pgenerable (hδ : 0 < δ) (j : Fin (k + 1)) :
    PGenerableWeighting (fun m =>
      EF.mul (phiFeature f M δ j m) (EF.safeRecip (phiSumFeature f M δ m))) := by
  have hmax : PGenerableWeighting (maxFeature f M) :=
    pgenerable_foldr_max _ (fun A hA => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      exact optFeature_pgenerable f M i)
  have hphi : ∀ j, PGenerableWeighting (phiFeature f M δ j) := fun j =>
    ctsIndFeature_generated (fun _ => δ) _ _ (MachineRatCodes.const (1 / δ))
      (optFeature_pgenerable f M j) (PGenerableWeighting.add hmax (constWeighting _))
  have hsum : PGenerableWeighting (phiSumFeature f M δ) :=
    pgenerable_foldr_add _ (fun A hA => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      exact hphi i)
  exact PGenerableWeighting.mul (hphi j) (PGenerableWeighting.safeRecip' hsum)

include market in
/-- The blend feature denotes the ramp blend of the day-`m` expectations of the reindexed options.
Source: mandate target 9a
Kind: L
Fidelity: exact
Hyps: (a); `hδ` -/
theorem blendCore_denote (hδ : 0 < δ) (j : Fin (k + 1)) (m : ℕ) :
    (EF.mul (phiFeature f M δ j m) (EF.safeRecip (phiSumFeature f M δ m))).denote P =
      rampBlend δ (fun i => (M.O i (deferralPreimage f m)).expect P m) j := by
  have hopt : ∀ i, (optFeature f M i m).denote P = (M.O i (deferralPreimage f m)).expect P m :=
    fun i => expectFeature_denote _ P m
  have hmax : (maxFeature f M m).denote P =
      Finset.univ.sup' Finset.univ_nonempty (fun i => (M.O i (deferralPreimage f m)).expect P m) := by
    unfold maxFeature
    rw [denote_foldr_max, List.map_ofFn]
    simp only [Function.comp_def, hopt]
    exact foldr_max_ofFn_eq_sup' _ (fun i => (LUV.expect_mem_Icc P m _ (market.price_mem_Icc m)).1)
  have hphi : ∀ j, (phiFeature f M δ j m).denote P =
      rampPhi δ (fun i => (M.O i (deferralPreimage f m)).expect P m) j := by
    intro j
    unfold phiFeature rampPhi
    rw [ctsIndFeature_denote (fun _ => δ) _ _ (fun _ => hδ) P m, hopt, EF.denote_add, Pi.add_apply,
      hmax, EF.denote_const]
    push_cast
    ring_nf
  have hsum : (phiSumFeature f M δ m).denote P =
      ∑ i, rampPhi δ (fun i => (M.O i (deferralPreimage f m)).expect P m) i := by
    unfold phiSumFeature
    rw [denote_foldr_add, List.map_ofFn]
    simp only [Function.comp_def, hphi, List.sum_ofFn]
  have hrecip : (EF.safeRecip (phiSumFeature f M δ m)).denote P =
      (max 1 ((phiSumFeature f M δ m).denote P))⁻¹ := rfl
  rw [EF.denote_mul, Pi.mul_apply, hphi j, hrecip, hsum, max_eq_right (one_le_rampPhi_sum δ hδ _)]
  unfold rampBlend
  rw [div_eq_mul_inv]

/-- The rational expectation of option `i` at day `m` of the reindexed member.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ratE (i : Fin (k + 1)) (m : ℕ) : ℚ := market.expectQuoteAt (M.O i) (deferralPreimage f m) m

/-- The rational ramp `φ_j`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def ratPhi (j : Fin (k + 1)) (m : ℕ) : ℚ :=
  ratCtsInd δ (ratE market f M j m) ((List.ofFn (fun i => ratE market f M i m)).foldr max 0 - 2 * δ)

/-- **The rational blend weight** `θ_j` at day `m` (`0` off the image of `f`).
Source: mandate target 9a
Kind: D
Fidelity: exact -/
def blendWeight (j : Fin (k + 1)) (m : ℕ) : ℚ :=
  if deferralImageFlag f m = 1 then ratPhi market f M δ j m / ∑ i, ratPhi market f M δ i m else 0

/-- Casting a `max`-fold of rationals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cast_foldr_max : ∀ (l : List ℚ),
    ((l.foldr max 0 : ℚ) : ℝ) = (l.map (fun q : ℚ => (q : ℝ))).foldr max 0
  | [] => by simp
  | q :: l => by
    simp only [List.foldr_cons, List.map_cons, Rat.cast_max]
    rw [cast_foldr_max l]

/-- The rational ramp casts to `rampPhi`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ratPhi_cast (j : Fin (k + 1)) (m : ℕ) :
    ((ratPhi market f M δ j m : ℚ) : ℝ) =
      rampPhi δ (fun i => (M.O i (deferralPreimage f m)).expect P m) j := by
  unfold ratPhi rampPhi
  rw [← ratCtsInd_cast]
  congr 1
  · unfold ratE; exact (market.expectQuoteAt_cast _ _ _).symm
  · push_cast
    rw [cast_foldr_max, List.map_ofFn]
    simp only [Function.comp_def]
    have : (fun i => ((ratE market f M i m : ℚ) : ℝ)) =
        fun i => (M.O i (deferralPreimage f m)).expect P m := by
      funext i; unfold ratE; exact (market.expectQuoteAt_cast _ _ _).symm
    rw [this, foldr_max_ofFn_eq_sup' _
      (fun i => (LUV.expect_mem_Icc P m _ (market.price_mem_Icc m)).1)]

/-- The blend weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem blendWeight_mem (hδ : 0 < δ) (j : Fin (k + 1)) (m : ℕ) :
    0 ≤ blendWeight market f M δ j m ∧ blendWeight market f M δ j m ≤ 1 := by
  unfold blendWeight
  split_ifs
  · have hpos : ∀ i, 0 ≤ ratPhi market f M δ i m := fun i => (ratCtsInd_mem_Icc _ _ _).1
    have hsum1 : 1 ≤ ∑ i, ratPhi market f M δ i m := by
      have := one_le_rampPhi_sum δ hδ (fun i => (M.O i (deferralPreimage f m)).expect P m)
      have hc : ((∑ i, ratPhi market f M δ i m : ℚ) : ℝ) =
          ∑ i, rampPhi δ (fun i => (M.O i (deferralPreimage f m)).expect P m) i := by
        push_cast; simp [ratPhi_cast]
      have : (1 : ℝ) ≤ ((∑ i, ratPhi market f M δ i m : ℚ) : ℝ) := by rw [hc]; exact this
      exact_mod_cast this
    constructor
    · exact div_nonneg (hpos j) (by linarith [hsum1])
    · rw [div_le_one (by linarith)]
      exact Finset.single_le_sum (fun i _ => hpos i) (Finset.mem_univ j) |>.trans (le_refl _)
  · exact ⟨le_rfl, zero_le_one⟩

/-- **The blend weight is P-generable** (9a): the gated `blendFeature`.
Source: mandate target 9a ("so `θ_j` is `PGenerableRat A` at rank `f n`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem blendWeight_pgenerable (hδ : 0 < δ) (j : Fin (k + 1)) :
    PGenerableRat P (blendWeight market f M δ j) := by
  have hcore := blendCore_pgenerable f M δ hδ j
  refine ⟨blendFeature f M δ j,
    { rank_le := fun m => ?_
      polyTok := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
        hcore.polySeg (unaryRuler_deferralImageFlag f)).of_eq (fun m => by
          unfold blendFeature; split_ifs <;> rfl)
      closed := fun m ρ V => ?_
      denote := fun m => ?_ }⟩
  · unfold blendFeature; split_ifs
    · simp
    · exact hcore.rank_le m
  · unfold blendFeature; split_ifs
    · simp
    · exact hcore.closed m ρ V
  · unfold blendFeature blendWeight
    rcases deferralImageFlag_zero_or_one f m with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega), if_pos h1, blendCore_denote market f M δ hδ j m]
      unfold rampBlend
      push_cast
      simp only [ratPhi_cast]

/-- At the deferred day the blend weight is the ramp blend of the self-expert's quotes.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a); `hinj` -/
theorem blendWeight_at_cast (hinj : Function.Injective f.f) (j : Fin (k + 1)) (n : ℕ) :
    ((blendWeight market f M δ j (f n) : ℚ) : ℝ) =
      rampBlend δ (fun i => (M.O i n).expect P (f n)) j := by
  unfold blendWeight rampBlend
  rw [if_pos (deferralImageFlag_at f n)]
  push_cast
  simp only [ratPhi_cast, deferralPreimage_at f hinj]

end Blend

/-! ## The real-number step: the blend dot the quotes is at least `M − 2δ` -/

/-- `Σ_j θ_j m_j ≥ max m − 2δ`: every positive ramp weight has `m_j > max − 2δ`, and the weights
sum to `1`.
Source: [[soft-self-endorsement]] §Soft self-endorsement; mandate target 9b
Kind: P
Fidelity: exact
Hyps: (a); `hδ` -/
theorem rampBlend_dot_ge (δ : ℚ) (hδ : 0 < δ) {k : ℕ} (m : Fin (k + 1) → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty m - 2 * (δ : ℝ) ≤ ∑ j, rampBlend δ m j * m j := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hsum := rampBlend_sum δ hδ m
  have hpos : 0 < ∑ i, rampPhi δ m i := lt_of_lt_of_le one_pos (one_le_rampPhi_sum δ hδ m)
  have hterm : ∀ j, rampBlend δ m j * (Finset.univ.sup' Finset.univ_nonempty m - 2 * (δ : ℝ)) ≤
      rampBlend δ m j * m j := by
    intro j
    by_cases h : m j ≤ Finset.univ.sup' Finset.univ_nonempty m - 2 * (δ : ℝ)
    · have : rampBlend δ m j = 0 := by
        unfold rampBlend rampPhi
        rw [ctsInd_eq_zero_of_le hδ h, _root_.zero_div]
      rw [this, zero_mul, zero_mul]
    · push Not at h
      exact mul_le_mul_of_nonneg_left h.le (div_nonneg (ctsInd_mem_Icc _ _ _).1 hpos.le)
  calc Finset.univ.sup' Finset.univ_nonempty m - 2 * (δ : ℝ)
      = ∑ j, rampBlend δ m j * (Finset.univ.sup' Finset.univ_nonempty m - 2 * (δ : ℝ)) := by
        rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ j, rampBlend δ m j * m j := Finset.sum_le_sum (fun j _ => hterm j)

/-! ## 9b — soft self-endorsement -/

section Soft

variable {DP : DeductiveProcess} {E : Expert DP} [IsLogicalInductor E.A DP]

/-- **The expert's estimate of a blended strategy is the blend of its quotes**: for a `BlendQuote`
at `rampBlend δ` whose weights `θ_j` are generable features of the expert's market at rank
`f n`, `E*(T_δ) ≈ₙ Σ_j θ_j m^j` — deferred provind with the weights as coefficients. No fold.
Source: [[soft-self-endorsement]] §Soft self-endorsement; vq-wiki-018 (closed by lookup, F3)
Kind: C
Fidelity: exact (within the quote's slack)
Hyps: (a); `hf`; `(c)` the quote (data) and the generability `hθ` ((a) for the self-expert,
`blendWeight_pgenerable`) -/
theorem blend_estimate (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    (hM : M.Valued DP) (δ : ℚ) {Tδ : ℕ → LUV} (q : BlendQuote DP E M (rampBlend δ) Tδ)
    (θ : Fin (k + 1) → ℕ → ℚ) (hθ : ∀ j, PGenerableRat E.A (θ j))
    (hθmem : ∀ j m, 0 ≤ θ j m ∧ θ j m ≤ 1)
    (hθcast : ∀ j n, ((θ j (E.f n) : ℚ) : ℝ) = rampBlend δ (fun i => M.quote E i n) j)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate Tδ n) ≈ₙ
      (fun n => ∑ j, rampBlend δ (fun i => M.quote E i n) j * M.quote E j n) := by
  choose C hC using hθ
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    ((fun _ => EF.const 1), Tδ) ::
      List.ofFn (fun j : Fin (k + 1) => ((fun m => EF.mul (EF.const (-1)) (C j m)), M.O j))
    with hterms
  have hmem : ∀ p ∈ terms, p = ((fun _ => EF.const 1), Tδ) ∨
      ∃ j, p = ((fun m => EF.mul (EF.const (-1)) (C j m)), M.O j) := fun p hp => by
    simp only [hterms, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
      exact Or.inr ⟨j, hj.symm⟩
  have hTv : Valued DP Tδ := fun n v hv => by
    choose x hx using fun j => hM j n v hv
    obtain ⟨z, hz, -⟩ := q.reflected n v hv x hx
    exact ⟨z, hz⟩
  have hCden : ∀ j m, (EF.mul (EF.const (-1)) (C j m)).denote E.A = -((θ j m : ℚ) : ℝ) := by
    intro j m
    simp [EF.denote_mul, Pi.mul_apply, EF.denote_const, (hC j).denote m]
  have h := expect_deferred_asympEq_zero_of_slack (P := E.A) (DP := DP) E.f hf
    (c₀ := fun _ => EF.const 0) (constWeighting 0) (terms := terms)
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact constWeighting 1
      · exact (constWeighting (-1)).mul (hC j).toWeighting)
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact q.codes
      · exact M.codes j)
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact hTv
      · exact hM j)
    (B := (k : ℝ) + 2) (by positivity)
    (fun m => by
      simp only [hterms, List.map_cons, List.map_ofFn, Function.comp_def, EF.denote_const,
        List.sum_cons, List.sum_ofFn, hCden]
      push_cast
      have hb : ∀ j, |((θ j m : ℚ) : ℝ)| ≤ 1 := fun j => by
        rw [abs_of_nonneg (by exact_mod_cast (hθmem j m).1)]
        exact_mod_cast (hθmem j m).2
      have hsum : ∑ j, |((θ j m : ℚ) : ℝ)| ≤ ∑ _j : Fin (k + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hb j)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        at hsum
      push_cast at hsum
      simp
      linarith)
    q.slack q.slack_tendsto
    (fun n v hv ν hν => by
      choose x hx using fun j => hM j n v hv
      obtain ⟨z, hz, hb⟩ := q.reflected n v hv x hx
      have hνT : ν (Tδ n) = z := (hν _ (List.mem_cons_self ..)).eq hz
      have hνO : ∀ j, ν (M.O j n) = x j := fun j =>
        (hν _ (List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨j, rfl⟩))).eq (hx j)
      simp only [hterms, List.map_cons, List.map_ofFn, Function.comp_def, EF.denote_const,
        List.sum_cons, List.sum_ofFn, hνT, hνO, hCden, hθcast]
      push_cast
      have e : (0 : ℝ) + (1 * z + ∑ j, -rampBlend δ (fun i => M.quote E i n) j * x j) =
          z - ∑ j, rampBlend δ (fun i => M.quote E i n) j * x j := by
        simp only [neg_mul, Finset.sum_neg_distrib]
        ring
      rw [e]
      exact hb) hworld
  have hE : deferredExpect E.A E.f (fun _ => EF.const 0) terms =
      fun n => E.estimate Tδ n - ∑ j, rampBlend δ (fun i => M.quote E i n) j * M.quote E j n := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_ofFn, Function.comp_def,
      EF.denote_const, List.sum_cons, List.sum_ofFn, hCden, hθcast, Menu.quote]
    push_cast
    simp [Finset.sum_neg_distrib, Expert.estimate]
    try ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Soft self-endorsement** (9b): `E*(T_δ) ≳ₙ M_n − 2δ` for a blended strategy whose weights
are generable at rank `f n`. No tie-break, no H3; survives the punishing menus.
Source: [[soft-self-endorsement]] §Soft self-endorsement; vq-wiki-021; mandate target 9b
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `(c)` the quote (data) and `hθ` ((a) self) -/
theorem softSelfEndorse (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    (hM : M.Valued DP) (δ : ℚ) (hδ : 0 < δ) {Tδ : ℕ → LUV}
    (q : BlendQuote DP E M (rampBlend δ) Tδ) (θ : Fin (k + 1) → ℕ → ℚ)
    (hθ : ∀ j, PGenerableRat E.A (θ j)) (hθmem : ∀ j m, 0 ≤ θ j m ∧ θ j m ≤ 1)
    (hθcast : ∀ j n, ((θ j (E.f n) : ℚ) : ℝ) = rampBlend δ (fun i => M.quote E i n) j)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate Tδ n) ≳ₙ (fun n => M.maxQuote E n - 2 * (δ : ℝ)) := by
  have h1 := blend_estimate hf hM δ q θ hθ hθmem hθcast hworld
  have h2 : (fun n => ∑ j, rampBlend δ (fun i => M.quote E i n) j * M.quote E j n) ≳ₙ
      (fun n => M.maxQuote E n - 2 * (δ : ℝ)) :=
    asympGE_of_forall_le (fun n => rampBlend_dot_ge δ hδ (fun i => M.quote E i n))
  exact asympGE_iff.2 ((asympGE_iff.1 h2).trans_asympEq h1.symm)

end Soft

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **Soft self-endorsement for the self-expert** (9b, (a)): the generability of the blend weights
is `blendWeight_pgenerable`; the quote `T_δ` remains data (findings F13).
Source: mandate target 9b ("(a) self")
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `(c)` the quote (data) -/
theorem softSelfEndorse_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {k : ℕ} (M : Menu k) (hM : M.Valued (paperDP T)) (δ : ℚ) (hδ : 0 < δ) {Tδ : ℕ → LUV}
    (q : BlendQuote (paperDP T) (selfExpert T f) M (rampBlend δ) Tδ) :
    (fun n => (selfExpert T f).estimate Tδ n) ≳ₙ
      (fun n => M.maxQuote (selfExpert T f) n - 2 * (δ : ℝ)) :=
  softSelfEndorse (E := selfExpert T f) hf hM δ hδ q
    (blendWeight (paperMarketComputation T) f M δ)
    (fun j => blendWeight_pgenerable (paperMarketComputation T) f M δ hδ j)
    (fun j m => blendWeight_mem (paperMarketComputation T) f M δ hδ j m)
    (fun j n => blendWeight_at_cast (paperMarketComputation T) f M δ hf.injective j n)
    (paperDP_hworld T)

/-! ## 9c — δ-hedged Value -/

/-- From `E(D) ≳ₙ ½ − δ` and `E(D) ≈ₙ ½E(T) − ½E(O) + ½`, `E(T) ≳ₙ E(O) − 2δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_of_composite_offset {d t o : ℕ → ℝ} {δ : ℝ}
    (hd : d ≳ₙ (fun _ => (1 / 2 : ℝ) - δ))
    (he : d ≈ₙ (fun n => (1 / 2 : ℝ) * t n - (1 / 2 : ℝ) * o n + 1 / 2)) :
    t ≳ₙ (fun n => o n - 2 * δ) := by
  intro ε hε
  have h1 := hd (ε / 4) (by linarith)
  have h2 := asympEq_eventually_abs_le he (show (0 : ℝ) < ε / 4 by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [abs_le] at hn2
  linarith [hn2.1, hn2.2]

/-- **δ-hedged Value** (9c): Total Trust and ramp quotes on the composite `½(T_δ − O^i + 1)`, with
soft self-endorsement, give `E^P_n(T_δ) ≳ₙ E^P_n(O^i_n) − 2δ` — the explicit `−2δ` (`def-lattice`'s
`BlendValue` has none and is not claimed). Two processes as `scoped_value`. Nothing mentions the
selection: survives the punishing menus.
Source: [[soft-self-endorsement]] §δ-hedged Value; vq-wiki-021; mandate target 9c
Kind: C
Fidelity: exact (the explicit `−2δ`)
Hyps: (a) the transfer and provind steps; `hf`, `hext`; `(c)` `hTT` (deference), `hramp`, `comp`,
the quote `q` and the generability `hθ` ((a) self) -/
theorem hedgedValue_of_totalTrust {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    (δ : ℚ) (hδ : 0 < δ) {Tδ : ℕ → LUV} (q : BlendQuote DPE E M (rampBlend δ) Tδ)
    (θ : Fin (k + 1) → ℕ → ℚ) (hθ : ∀ j, PGenerableRat E.A (θ j))
    (hθmem : ∀ j m, 0 ≤ θ j m ∧ θ j m ≤ 1)
    (hθcast : ∀ j n, ((θ j (E.f n) : ℚ) : ℝ) = rampBlend δ (fun i => M.quote E i n) j)
    (i : Fin (k + 1)) (comp : Composite DPE Tδ (M.O i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    (hramp : RampQuotesAvailable DPH (E.recast DPH) comp.D)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (Tδ n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n - 2 * (δ : ℝ)) := by
  have hTv : Valued DPE Tδ := fun n v hv => by
    choose x hx using fun j => hM j n v hv
    obtain ⟨z, hz, -⟩ := q.reflected n v hv x hx
    exact ⟨z, hz⟩
  have hsoft := softSelfEndorse hf hM δ hδ q θ hθ hθmem hθcast hworldE
  have hD := composite_estimate hf q.codes (M.codes i) hTv (hM i) comp hworldE
  have hA : (fun n => (E.recast DPH).estimate comp.D n) ≳ₙ
      (fun _ => (((1 / 2 - δ : ℚ)) : ℝ)) := by
    simp only [Expert.recast_estimate]
    have h1 : (fun n => (1 / 2 : ℝ) * E.estimate Tδ n - (1 / 2 : ℝ) * E.estimate (M.O i) n + 1 / 2)
        ≳ₙ (fun _ => (((1 / 2 - δ : ℚ)) : ℝ)) := by
      intro ε hε
      filter_upwards [hsoft (2 * ε) (by linarith)] with n hn
      have := M.quote_le_maxQuote E i n
      push_cast
      simp only [Menu.quote] at this
      linarith
    exact asympGE_iff.2 ((asympGE_iff.1 h1).trans_asympEq hD.symm)
  have hH := expert_bound_transfer_of_totalTrust hTT comp.codes hramp hA hworldH
  have hN := composite_expect (P := P) hext q.codes (M.codes i) hTv (hM i) comp hworldH
  push_cast at hH
  exact asympGE_of_composite_offset hH hN

/-! ## 9d — decisive margins -/

/-- **The ramp blend is the hard selection on a decisive day**: if `m_{j*}` exceeds every other
quote by `η > 2δ`, then `θ_{j*} = 1` and `θ_i = 0` for `i ≠ j*`.
Source: 2-018; [[soft-self-endorsement]] (the margins remark); mandate target 9d
Kind: P
Fidelity: exact
Hyps: (a); `hδ` -/
theorem rampBlend_eq_of_decisive (δ : ℚ) (hδ : 0 < δ) {k : ℕ} (m : Fin (k + 1) → ℝ)
    (j₀ : Fin (k + 1)) {η : ℝ} (hη : 2 * (δ : ℝ) < η)
    (hdec : ∀ i, i ≠ j₀ → m i + η ≤ m j₀) :
    rampBlend δ m j₀ = 1 ∧ ∀ i, i ≠ j₀ → rampBlend δ m i = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hsup : Finset.univ.sup' Finset.univ_nonempty m = m j₀ := by
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro i _
      by_cases h : i = j₀
      · rw [h]
      · linarith [hdec i h]
    · exact Finset.le_sup' m (Finset.mem_univ j₀)
  have hphi0 : ∀ i, i ≠ j₀ → rampPhi δ m i = 0 := fun i hi => by
    unfold rampPhi
    rw [hsup]
    exact ctsInd_eq_zero_of_le hδ (by linarith [hdec i hi])
  have hphi1 : rampPhi δ m j₀ = 1 := by
    unfold rampPhi
    rw [hsup]
    exact ctsInd_eq_one_of_le_sub _ _ _ hδ (by linarith)
  have hsum : ∑ i, rampPhi δ m i = 1 := by
    rw [Finset.sum_eq_single j₀ (fun i _ hi => hphi0 i hi) (fun h => absurd (Finset.mem_univ _) h),
      hphi1]
  refine ⟨?_, fun i hi => ?_⟩
  · unfold rampBlend; rw [hphi1, hsum, _root_.div_one]
  · unfold rampBlend; rw [hphi0 i hi, _root_.zero_div]

/-- **The margins corollary** (9d; vq-wiki-021): on a menu with an eventual decisive margin
`η`, every follower of the argmax has `E*(S_n) ≳ₙ M_n` — Lemma 2 with H3 swapped for a margin
condition — provided a blended quote is available at every small width (data, `(c)`): on
decisive days the blend is the hard selection, so `S` and `T_δ` are valued equal within slack
and soft self-endorsement at every `δ < η/2` gives the instance.
Source: vq-wiki-021 (the margins corollary); 2-018; mandate target 9d
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `(c)` the quotes at every small width and their generable weights ((a) self) -/
theorem selfEndorseGE_instance_of_margin {DP : DeductiveProcess} {E : Expert DP}
    [IsLogicalInductor E.A DP] (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    (hM : M.Valued DP) {η : ℝ} (hη : 0 < η)
    (hdec : ∀ᶠ n in atTop, ∀ i, i ≠ M.argmax E n → M.quote E i n + η ≤ M.quote E (M.argmax E n) n)
    (hquotes : ∀ δ : ℚ, 0 < δ → 2 * (δ : ℝ) < η → ∃ (Tδ : ℕ → LUV)
      (_q : BlendQuote DP E M (rampBlend δ) Tδ) (θ : Fin (k + 1) → ℕ → ℚ),
        (∀ j, PGenerableRat E.A (θ j)) ∧ (∀ j m, 0 ≤ θ j m ∧ θ j m ≤ 1) ∧
        (∀ j n, ((θ j (E.f n) : ℚ) : ℝ) = rampBlend δ (fun i => M.quote E i n) j))
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n) := by
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn (show (0 : ℝ) < min (ε / 4) (η / 4) by positivity)
  have hδ : 0 < δ := by exact_mod_cast hδ0
  have hδε' : (δ : ℝ) < ε / 4 := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδη : 2 * (δ : ℝ) < η := by
    have := lt_of_lt_of_le hδε (min_le_right _ _); linarith
  obtain ⟨Tδ, q, θ, hθ, hθmem, hθcast⟩ := hquotes δ hδ hδη
  have hsoft := softSelfEndorse hf hM δ hδ q θ hθ hθmem hθcast hworld
  -- S and Tδ agree within slack on decisive days
  have hagree : (fun n => E.estimate S n) ≈ₙ (fun n => E.estimate Tδ n) := by
    have hSv : Valued DP S := follows_valued hM hfol
    have hTv : Valued DP Tδ := fun n v hv => by
      choose x hx using fun j => hM j n v hv
      obtain ⟨z, hz, -⟩ := q.reflected n v hv x hx
      exact ⟨z, hz⟩
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := E.A) (DP := DP) E.f hf
      (c₀ := fun _ => EF.const 0) (constWeighting 0)
      (terms := [((fun _ => EF.const 1), S), ((fun _ => EF.const (-1)), Tδ)])
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact constWeighting _)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hS
        · exact q.codes)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hSv
        · exact hTv)
      (B := 2) (by norm_num) (fun m => by simp [EF.denote_const]; try norm_num)
      (fun ε' hε' => by
        filter_upwards [hdec, (tendsto_order.1 q.slack_tendsto).2 ε' hε'] with n hn hs v hv ν hν
        choose x hx using fun j => hM j n v hv
        obtain ⟨z, hz, hb⟩ := q.reflected n v hv x hx
        have e1 : ν (S n) = x (M.argmax E n) :=
          (hν ((fun _ => EF.const 1), S) (by simp)).eq (hfol n v hv _ (hx _))
        have e2 : ν (Tδ n) = z := (hν ((fun _ => EF.const (-1)), Tδ) (by simp)).eq hz
        obtain ⟨h1, h0⟩ := rampBlend_eq_of_decisive δ hδ (fun i => M.quote E i n) (M.argmax E n)
          hδη hn
        have hblend : ∑ j, rampBlend δ (fun i => M.quote E i n) j * x j = x (M.argmax E n) := by
          rw [Finset.sum_eq_single (M.argmax E n) (fun j _ hj => by rw [h0 j hj, zero_mul])
            (fun h => absurd (Finset.mem_univ _) h), h1, one_mul]
        rw [hblend] at hb
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const,
          e1, e2]
        push_cast
        have : (0 : ℝ) + (1 * x (M.argmax E n) + (-1 * z + 0)) = -(z - x (M.argmax E n)) := by ring
        rw [this, abs_neg]
        exact hb.trans hs.le) hworld
    have hE : deferredExpect E.A E.f (fun _ => EF.const 0)
        [((fun _ => EF.const 1), S), ((fun _ => EF.const (-1)), Tδ)] =
        fun n => E.estimate S n - E.estimate Tδ n := by
      funext n
      simp only [deferredExpect, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        EF.denote_const]
      push_cast
      ring
    rw [hE] at h
    unfold AsympEq at h ⊢
    simpa using h
  have h1 := hsoft (ε / 4) (by linarith)
  have h2 := asympEq_eventually_abs_le hagree (show (0 : ℝ) < ε / 4 by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [abs_le] at hn2
  linarith [hn2.1, hn2.2]

end

end Cleanroom.Deference.DefArgmaxValue
