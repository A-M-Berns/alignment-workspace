import LogicalInduction.Construction.Quotation.MarketQuoteCodes
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `def-self-trust` — design decision 3: the weights of `ccee`, as generable features

FAF's `thm:ccee` takes a P-generable `[0,1]` weight `w : ℕ → ℚ` (`PGenerableRat P w`) and
evaluates it at the **deferred** day `w (f n)` (LI 4.12.3; `def-lattice` F2). Everything this
package feeds into `ccee` is built here as a `GeneratedRatFeature`:

* **the pull-back along `f`** (`pullbackWeight`): a day-`n` weight `u n` becomes the weight
  `w m := u (f⁻¹ m)` on the image of `f` and `0` off it, so that `w (f n) = u n` — FAF's
  bounded-scan inverse `deferralPreimage` with its `deferralImageFlag`, which needs
  `Function.Injective f.f` (FAF's `DeferralFunction` does not carry it; the mandate takes it as
  a hypothesis, discharged for `succDeferral` and every strictly increasing deferral);
* **the ramp of the deferred expectation** (`rampWeight`, `rampWeightBelow`): the weight of
  `est` (target 2), `w m := ctsind_δ(E_m(X_{f⁻¹ m}) > s)` on the image and `0` off it — its
  feature is FAF's `ctsIndFeature` of the reified price feature of the expectation mesh
  (`LUV.expectAffineSeq`, rank `m`) against the constant `s`, gated by the image flag. This is
  the certificate vq-wiki-061 calls "the ramp of a future expectation quote as a generable
  feature at rank `f(n)`" and the one genuinely new piece of Lean in the package;
* closure lemmas: products, `1 − w`, and the ramp of a day-`n` generable rational
  (`pgenerableRat_mul`, `pgenerableRat_one_sub`, `pgenerableRat_ratCtsInd_left/right`) for
  targets 4 and 5.

The rational value of the ramp is stated against a certified market program
(`MarketComputation P`, FAF's `expectQuoteAt`), as FAF's own `deferredWeightQuoteCode` is; the
paper market instantiates it with `paperMarketComputation T`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology

noncomputable section

/-! ## Generable-weight closure lemmas -/

/-- The product of two P-generable rational sequences is P-generable (`EF.mul` of the features).
Source: none: infrastructure (FAF `PGenerableWeighting.mul`; mandate target 4a)
Kind: L
Fidelity: n/a -/
theorem pgenerableRat_mul {P : History} {u w : ℕ → ℚ} (hu : PGenerableRat P u)
    (hw : PGenerableRat P w) : PGenerableRat P (fun n => u n * w n) := by
  obtain ⟨U, hU⟩ := hu
  obtain ⟨W, hW⟩ := hw
  refine ⟨fun n => EF.mul (U n) (W n), (hU.toWeighting.mul hW.toWeighting).toGeneratedRatFeature
    (fun n => ?_)⟩
  simp [EF.denote_mul, hU.denote n, hW.denote n]

/-- `1 − w` is P-generable when `w` is.
Source: none: infrastructure (mandate target 4b)
Kind: L
Fidelity: n/a -/
theorem pgenerableRat_one_sub {P : History} {w : ℕ → ℚ} (hw : PGenerableRat P w) :
    PGenerableRat P (fun n => 1 - w n) := by
  obtain ⟨W, hW⟩ := hw
  have hconst : PGenerableWeighting (fun _ : ℕ => EF.const (1 : ℚ)) :=
    { polySeg := MachineSpliceStream.serialize_const 1
      rank_le := fun n => by simp
      closed := fun n ρ V => by simp }
  have hneg : PGenerableWeighting (fun _ : ℕ => EF.const (-1 : ℚ)) :=
    { polySeg := MachineSpliceStream.serialize_const (-1)
      rank_le := fun n => by simp
      closed := fun n ρ V => by simp }
  refine ⟨fun n => EF.add (EF.const 1) (EF.mul (EF.const (-1)) (W n)),
    (hconst.add (hneg.mul hW.toWeighting)).toGeneratedRatFeature (fun n => ?_)⟩
  simp [EF.denote_add, EF.denote_mul, hW.denote n]
  ring

/-- The constant feature `s` is a generable weighting.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem constWeighting (s : ℚ) : PGenerableWeighting (fun _ : ℕ => EF.const s) where
  polySeg := MachineSpliceStream.serialize_const s
  rank_le n := by simp
  closed n ρ V := by simp

/-- The up-ramp `ctsind_δ(c n > t)` of a P-generable rational sequence `c` (read at day `n`)
against a constant threshold is P-generable, with the rational value `ratCtsInd δ (c n) t`.
Source: vq-wiki-062 (Prop 3.1: "`ctsInd` of a generable rational is generable"); FAF
`ctsIndFeature_generated`
Kind: L
Fidelity: n/a -/
theorem pgenerableRat_ratCtsInd_left {P : History} {c : ℕ → ℚ} (hc : PGenerableRat P c)
    {δ : ℚ} (hδ : 0 < δ) (t : ℚ) :
    PGenerableRat P (fun n => ratCtsInd δ (c n) t) := by
  obtain ⟨C, hC⟩ := hc
  refine ⟨ctsIndFeature (fun _ => δ) C (fun _ => EF.const t),
    (ctsIndFeature_generated (fun _ => δ) C (fun _ => EF.const t)
      (MachineRatCodes.const (1 / δ)) hC.toWeighting (constWeighting t)).toGeneratedRatFeature
      (fun n => ?_)⟩
  rw [ctsIndFeature_denote (fun _ => δ) C (fun _ => EF.const t) (fun _ => hδ) P n, hC.denote n,
    EF.denote_const, ratCtsInd_cast]

/-- The down-ramp `ctsind_δ(c n < t)` of a P-generable rational sequence is P-generable.
Source: vq-wiki-062; FAF `ctsIndFeature_generated`
Kind: L
Fidelity: n/a -/
theorem pgenerableRat_ratCtsInd_right {P : History} {c : ℕ → ℚ} (hc : PGenerableRat P c)
    {δ : ℚ} (hδ : 0 < δ) (t : ℚ) :
    PGenerableRat P (fun n => ratCtsInd δ t (c n)) := by
  obtain ⟨C, hC⟩ := hc
  refine ⟨ctsIndFeature (fun _ => δ) (fun _ => EF.const t) C,
    (ctsIndFeature_generated (fun _ => δ) (fun _ => EF.const t) C
      (MachineRatCodes.const (1 / δ)) (constWeighting t) hC.toWeighting).toGeneratedRatFeature
      (fun n => ?_)⟩
  rw [ctsIndFeature_denote (fun _ => δ) (fun _ => EF.const t) C (fun _ => hδ) P n, hC.denote n,
    EF.denote_const, ratCtsInd_cast]

/-! ## The pull-back of a day-`n` weight along the deferral -/

/-- **The pull-back along `f`:** `u (f⁻¹ m)` on the image of `f`, `0` off it (FAF's bounded-scan
`deferralPreimage`/`deferralImageFlag`).
Source: mandate design decision 3; vq-wiki-053 ("supply `w_m := u_{f^{-1}(m)}` on `im f`")
Kind: D
Fidelity: exact -/
def pullbackWeight (f : DeferralFunction) (u : ℕ → ℚ) (m : ℕ) : ℚ :=
  if deferralImageFlag f m = 1 then u (deferralPreimage f m) else 0

/-- On the image, the pull-back reads the day-`n` weight: `pullbackWeight f u (f n) = u n`,
given that `f` is injective.
Source: mandate design decision 3; FAF `deferralPreimage_at`, `deferralImageFlag_at`
Kind: L
Fidelity: exact
Hyps: (a); injectivity of `f` is a hypothesis FAF's `DeferralFunction` does not carry
(finding F2 of this package) -/
theorem pullbackWeight_at (f : DeferralFunction) (hinj : Function.Injective f.f) (u : ℕ → ℚ)
    (n : ℕ) : pullbackWeight f u (f n) = u n := by
  simp [pullbackWeight, deferralImageFlag_at, deferralPreimage_at f hinj]

/-- The pull-back stays in `[0,1]` when `u` does.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pullbackWeight_mem (f : DeferralFunction) {u : ℕ → ℚ} (hu : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    (m : ℕ) : 0 ≤ pullbackWeight f u m ∧ pullbackWeight f u m ≤ 1 := by
  unfold pullbackWeight
  split_ifs
  · exact hu _
  · exact ⟨le_rfl, zero_le_one⟩

/-- **The pull-back of a P-generable weight is P-generable**: the feature is the day-`n`
feature reindexed along the bounded-scan preimage and gated by the image flag (both unary
rulers); rank `≤ f⁻¹ m < m` on the image, which is where injectivity enters (off the image the
scan's default is not bounded by `m` without it).
Source: mandate design decision 3; vq-wiki-053's "(F-INV)" legality remark, made exact
Kind: L
Fidelity: exact
Hyps: (a); `hinj` as in `pullbackWeight_at` -/
theorem pullbackWeight_pgenerable {P : History} (f : DeferralFunction)
    (hinj : Function.Injective f.f) {u : ℕ → ℚ}
    (hu : PGenerableRat P u) : PGenerableRat P (pullbackWeight f u) := by
  obtain ⟨U, hU⟩ := hu
  refine ⟨fun m => if deferralImageFlag f m = 0 then EF.const 0 else U (deferralPreimage f m),
    { rank_le := fun m => ?_
      polyTok := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
        (hU.polyTok.comp (unaryRuler_deferralPreimage f)) (unaryRuler_deferralImageFlag f)).of_eq
        (fun m => by split_ifs <;> rfl)
      closed := fun m ρ V => ?_
      denote := fun m => ?_ }⟩
  · split_ifs with h
    · simp
    · rcases deferralImageFlag_zero_or_one f m with h0 | h1
      · exact absurd h0 h
      · exact (hU.rank_le _).trans (deferralPreimage_spec f hinj h1).1.le
  · split_ifs
    · simp
    · exact hU.closed _ ρ V
  · unfold pullbackWeight
    rcases deferralImageFlag_zero_or_one f m with h0 | h1
    · simp [h0]
    · simp [h1, hU.denote]

/-! ## The ramp of the deferred expectation (the weight of `est`) -/

/-- The reified day-`m` expectation feature of a LUV sequence: the price feature of FAF's
expectation mesh `LUV.expectAffineSeq X m` on day `m`, denoting `(X m).expect V m`.
Source: mandate design decision 3 ("`priceFeature (expectAffineSeq …) m`")
Kind: D
Fidelity: exact -/
def expectFeature (X : ℕ → LUV) (m : ℕ) : EF :=
  (LUV.expectAffineSeq X m).priceFeature m

/-- The expectation feature denotes the day-`m` expectation of `X m`.
Source: FAF `AffineCombination.priceFeature_denote`, `LUV.expectAffineSeq_price`
Kind: L
Fidelity: n/a -/
theorem expectFeature_denote (X : ℕ → LUV) (V : History) (m : ℕ) :
    (expectFeature X m).denote V = (X m).expect V m := by
  rw [expectFeature, AffineCombination.priceFeature_denote, LUV.expectAffineSeq_price]

/-- **The expectation feature of an e.c. LUV sequence is a generable weighting**: emitted by
FAF's `PolySequence.priceFeature_polySeg` on the mesh's polynomial sequence, rank `≤ m`
(constant coefficients), closed.
Source: mandate design decision 3; FAF `LUV.expectAffineSeq_polySequence`,
`AffineCombination.PolySequence.priceFeature_polySeg`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem expectFeature_pgenerable {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) :
    PGenerableWeighting (expectFeature X) where
  polySeg := ((LUV.expectAffineSeq_polySequence X hX).priceFeature_polySeg.comp
    (UnaryRuler.id.pair UnaryRuler.id)).of_eq (fun m => by simp [expectFeature, Nat.unpair_pair])
  rank_le m := by
    refine AffineCombination.priceFeature_rank _ (k := 0) (Nat.zero_le m) ?_ ?_
    · simp [LUV.expectAffineSeq, LUV.expectAffine]
    · intro p hp
      simp only [LUV.expectAffineSeq, LUV.expectAffine, List.mem_map, List.mem_range] at hp
      obtain ⟨i, -, rfl⟩ := hp
      simp
  closed m ρ V :=
    (LUV.expectAffineSeq_polySequence X hX).priceFeature_closed m m ρ V

variable {P : History} (market : MarketComputation P)

/-- **The `est` weight, above face:** on the image of `f`, the ramp of the market's own day-`m`
expectation of the source member `X (f⁻¹ m)` against `s`; `0` off the image. At `m = f n` this
is `ctsind_δ(E_{f n}(X n) > s)` (`rampWeight_at`).
Source: vq-wiki-061 ("`v̄` pulled back along `f` is generable in `[0,1]` (rank `m`)");
mandate design decision 3
Kind: D
Fidelity: exact -/
def rampWeight (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) : ℚ :=
  if deferralImageFlag f m = 1 then
    ratCtsInd δ (market.expectQuoteAt X (deferralPreimage f m) m) s else 0

/-- **The `est` weight, below face:** the down-ramp `ctsind_δ(E_m(X_{f⁻¹ m}) < s)` on the image.
Source: vq-wiki-061 (dual face); trust-lab-2-020
Kind: D
Fidelity: exact -/
def rampWeightBelow (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) : ℚ :=
  if deferralImageFlag f m = 1 then
    ratCtsInd δ s (market.expectQuoteAt X (deferralPreimage f m) m) else 0

/-- At the deferred day the weight is the ramp of the deferred expectation of the day-`n`
member (needs injectivity of `f`).
Source: mandate design decision 3
Kind: L
Fidelity: exact
Hyps: (a); `hinj` -/
theorem rampWeight_at (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (δ s : ℚ) (n : ℕ) :
    rampWeight market f X δ s (f n) = ratCtsInd δ (market.expectQuoteAt X n (f n)) s := by
  simp [rampWeight, deferralImageFlag_at, deferralPreimage_at f hinj]

/-- Below-face version of `rampWeight_at`.
Source: mandate design decision 3
Kind: L
Fidelity: exact
Hyps: (a); `hinj` -/
theorem rampWeightBelow_at (f : DeferralFunction) (hinj : Function.Injective f.f) (X : ℕ → LUV)
    (δ s : ℚ) (n : ℕ) :
    rampWeightBelow market f X δ s (f n) = ratCtsInd δ s (market.expectQuoteAt X n (f n)) := by
  simp [rampWeightBelow, deferralImageFlag_at, deferralPreimage_at f hinj]

/-- The ramp weight lies in `[0,1]`.
Source: none: infrastructure (FAF `ratCtsInd_mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem rampWeight_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) :
    0 ≤ rampWeight market f X δ s m ∧ rampWeight market f X δ s m ≤ 1 := by
  unfold rampWeight
  split_ifs
  · exact ratCtsInd_mem_Icc _ _ _
  · exact ⟨le_rfl, zero_le_one⟩

/-- The below-face ramp weight lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rampWeightBelow_mem (f : DeferralFunction) (X : ℕ → LUV) (δ s : ℚ) (m : ℕ) :
    0 ≤ rampWeightBelow market f X δ s m ∧ rampWeightBelow market f X δ s m ≤ 1 := by
  unfold rampWeightBelow
  split_ifs
  · exact ratCtsInd_mem_Icc _ _ _
  · exact ⟨le_rfl, zero_le_one⟩

/-- **The `est` weight is P-generable** (the load-bearing certificate of the package): its
feature is FAF's `ctsIndFeature` of the expectation feature of the reindexed source
`X ∘ deferralPreimage f` (rank `m`) against the constant `s`, gated by the image flag; the
denotation is `ctsInd δ (E_m(X_{f⁻¹ m})) s = ratCtsInd δ (expectQuoteAt X (f⁻¹ m) m) s` by the
market certificate's `expectQuoteAt_cast`.
Source: vq-wiki-061; mandate design decision 3 ("this certificate is the one genuinely new
piece of Lean in the package")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem rampWeight_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    PGenerableRat P (rampWeight market f X δ s) := by
  have hX' : LUV.MachineThresholdCodeSeq (fun m => X (deferralPreimage f m)) :=
    hX.reindex (unaryRuler_deferralPreimage f)
  have hcts : PGenerableWeighting (ctsIndFeature (fun _ => δ)
      (expectFeature (fun m => X (deferralPreimage f m))) (fun _ => EF.const s)) :=
    ctsIndFeature_generated (fun _ => δ) _ _ (MachineRatCodes.const (1 / δ))
      (expectFeature_pgenerable hX') (constWeighting s)
  refine ⟨fun m => if deferralImageFlag f m = 0 then EF.const 0 else
      ctsIndFeature (fun _ => δ) (expectFeature (fun m => X (deferralPreimage f m)))
        (fun _ => EF.const s) m,
    { rank_le := fun m => ?_
      polyTok := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
        hcts.polySeg (unaryRuler_deferralImageFlag f)).of_eq (fun m => by split_ifs <;> rfl)
      closed := fun m ρ V => ?_
      denote := fun m => ?_ }⟩
  · split_ifs
    · simp
    · exact hcts.rank_le m
  · split_ifs
    · simp
    · exact hcts.closed m ρ V
  · unfold rampWeight
    rcases deferralImageFlag_zero_or_one f m with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega), if_pos h1,
        ctsIndFeature_denote (fun _ => δ) _ _ (fun _ => hδ) P m, expectFeature_denote,
        EF.denote_const, market.expectQuoteAt_cast, ratCtsInd_cast]

/-- **The below-face `est` weight is P-generable** (mirror of `rampWeight_pgenerable`).
Source: vq-wiki-061 (dual face); mandate design decision 3
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem rampWeightBelow_pgenerable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    PGenerableRat P (rampWeightBelow market f X δ s) := by
  have hX' : LUV.MachineThresholdCodeSeq (fun m => X (deferralPreimage f m)) :=
    hX.reindex (unaryRuler_deferralPreimage f)
  have hcts : PGenerableWeighting (ctsIndFeature (fun _ => δ) (fun _ => EF.const s)
      (expectFeature (fun m => X (deferralPreimage f m)))) :=
    ctsIndFeature_generated (fun _ => δ) _ _ (MachineRatCodes.const (1 / δ))
      (constWeighting s) (expectFeature_pgenerable hX')
  refine ⟨fun m => if deferralImageFlag f m = 0 then EF.const 0 else
      ctsIndFeature (fun _ => δ) (fun _ => EF.const s)
        (expectFeature (fun m => X (deferralPreimage f m))) m,
    { rank_le := fun m => ?_
      polyTok := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
        hcts.polySeg (unaryRuler_deferralImageFlag f)).of_eq (fun m => by split_ifs <;> rfl)
      closed := fun m ρ V => ?_
      denote := fun m => ?_ }⟩
  · split_ifs
    · simp
    · exact hcts.rank_le m
  · split_ifs
    · simp
    · exact hcts.closed m ρ V
  · unfold rampWeightBelow
    rcases deferralImageFlag_zero_or_one f m with h0 | h1
    · simp [h0]
    · rw [if_neg (by omega), if_pos h1,
        ctsIndFeature_denote (fun _ => δ) _ _ (fun _ => hδ) P m, expectFeature_denote,
        EF.denote_const, market.expectQuoteAt_cast, ratCtsInd_cast]

end

end Cleanroom.Deference.DefSelfTrust
