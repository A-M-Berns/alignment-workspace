import Cleanroom.Found.LiQuoteLane.Defs
import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Properties.Calibration

/-!
# `li-quote-lane` · PullBack: day-`n` gates are legal `ccee` weights (T5)

`thm:ccee` (FAF's `ConditionalExpectationQuote`) gates at `w (f n)`, the `f n`-th term of a
generable weight sequence. [[route-transitivity]] §2 observes that this *includes* every day-`n`
gate: pull `u` back along `f`, setting `w m := u k` when `m = f k` and `w m := 0` otherwise. The
content is the emission certificate: deciding `m ∈ im f` and recovering `f⁻¹ m` in time
polynomial in `m` from `f.graph_fp` alone (no poly-time computability of `f` is assumed — a proof
that used it would be a (b)). FAF's padding device is `scheduledMatch` / `segPrefix`
(`Properties/SelfTrust.lean`, `Framework/Machine/Ruler.lean`): the preimage count
`∑_{k ≤ m} [f k = m]` and the preimage index `∑_{k ≤ m} k · [f k = m]` are unary rulers, and
`pullBack` dispatches on the count.

Single market, no ledger. Finding (severity: imprecision): [[unbiasedness-theorem-families]] §4.1
applies `ccee` "at weight `w := u`" without this reindexing; its conclusion is rescued by
`pullBack_apply`.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional

/-! ## The preimage count and index -/

/-- `∑_{k ≤ m} [f k = m]`: the number of preimages of `m` under `f` below `m + 1` (at most one
when `f` is injective).
Source: none: infrastructure (FAF `scheduledMatch`, `segPrefix`)
Kind: D
Fidelity: n/a -/
def preimageCount (f : DeferralFunction) (m : ℕ) : ℕ := segPrefix (scheduledMatch f) m (m + 1)

/-- `∑_{k ≤ m} k · [f k = m]`: the preimage of `m` under `f` when there is one, `0` otherwise.
Source: none: infrastructure (FAF `scheduledValue`'s device)
Kind: D
Fidelity: n/a -/
def preimageIndex (f : DeferralFunction) (m : ℕ) : ℕ :=
  segPrefix (fun w => w.unpair.2 * scheduledMatch f w) m (m + 1)

/-- `segPrefix` as a `Finset.sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma segPrefix_eq_sum (lenFn : ℕ → ℕ) (n : ℕ) : ∀ k : ℕ,
    segPrefix lenFn n k = ∑ i ∈ Finset.range k, lenFn (Nat.pair n i)
  | 0 => by simp
  | k + 1 => by rw [segPrefix_succ, Finset.sum_range_succ, segPrefix_eq_sum lenFn n k]

/-- `preimageCount_eq_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma preimageCount_eq_sum (f : DeferralFunction) (m : ℕ) :
    preimageCount f m = ∑ i ∈ Finset.range (m + 1), if f.f i = m then 1 else 0 := by
  unfold preimageCount
  rw [segPrefix_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [scheduledMatch]

/-- `preimageIndex_eq_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma preimageIndex_eq_sum (f : DeferralFunction) (m : ℕ) :
    preimageIndex f m = ∑ i ∈ Finset.range (m + 1), i * (if f.f i = m then 1 else 0) := by
  unfold preimageIndex
  rw [segPrefix_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [scheduledMatch]

/-- For injective `f`, the preimage count is the indicator of `m ∈ im f`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma preimageCount_eq (f : DeferralFunction) (hinj : Function.Injective f.f) (m : ℕ) :
    preimageCount f m = if ∃ k, k < m + 1 ∧ f.f k = m then 1 else 0 := by
  rw [preimageCount_eq_sum]
  split_ifs with h
  · obtain ⟨k₀, hk₀, hfk₀⟩ := h
    rw [Finset.sum_eq_single k₀]
    · simp [hfk₀]
    · intro i _ hi
      have : f.f i ≠ m := fun hfi => hi (hinj (hfi.trans hfk₀.symm))
      simp [this]
    · intro hk
      exact absurd (Finset.mem_range.mpr hk₀) hk
  · refine Finset.sum_eq_zero fun i hi => ?_
    have : f.f i ≠ m := fun hfi => h ⟨i, Finset.mem_range.mp hi, hfi⟩
    simp [this]

/-- For injective `f`, the preimage index is the preimage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma preimageIndex_eq (f : DeferralFunction) (hinj : Function.Injective f.f) {m : ℕ}
    (h : ∃ k, k < m + 1 ∧ f.f k = m) : preimageIndex f m = Nat.find h := by
  rw [preimageIndex_eq_sum]
  have hspec := Nat.find_spec h
  rw [Finset.sum_eq_single (Nat.find h)]
  · rw [if_pos hspec.2, mul_one]
  · intro i _ hi
    have : f.f i ≠ m := fun hfi => hi (hinj (hfi.trans hspec.2.symm))
    simp [this]
  · intro hk
    exact absurd (Finset.mem_range.mpr hspec.1) hk

/-- The preimage count is a unary ruler (FAF's `segPrefix` ruler on the `scheduledMatch` flag).
Source: none: infrastructure (FAF `unaryRuler_scheduledValue`'s device)
Kind: L
Fidelity: n/a -/
lemma unaryRuler_preimageCount (f : DeferralFunction) : UnaryRuler (preimageCount f) :=
  ((UnaryRuler.segPrefix (unaryRuler_scheduledMatch f)).comp
    (UnaryRuler.id.pair UnaryRuler.id.succ)).of_eq (fun m => by simp [preimageCount])

/-- The preimage index is a unary ruler.
Source: none: infrastructure (FAF `unaryRuler_scheduledValue`'s device)
Kind: L
Fidelity: n/a -/
lemma unaryRuler_preimageIndex (f : DeferralFunction) : UnaryRuler (preimageIndex f) :=
  ((UnaryRuler.segPrefix (UnaryRuler.unpairSnd.mul (unaryRuler_scheduledMatch f))).comp
    (UnaryRuler.id.pair UnaryRuler.id.succ)).of_eq (fun m => by simp [preimageIndex])

/-- `pullBack` dispatches on the preimage count (injective `f`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pullBack_eq (f : DeferralFunction) (hinj : Function.Injective f.f) (u : ℕ → EF) (m : ℕ) :
    pullBack f u m = if preimageCount f m = 0 then EF.const 0 else u (preimageIndex f m) := by
  unfold pullBack
  split_ifs with h h2 h2
  · rw [preimageCount_eq f hinj, if_pos h] at h2
    exact absurd h2 one_ne_zero
  · rw [preimageIndex_eq f hinj h]
  · rfl
  · rw [preimageCount_eq f hinj, if_neg h] at h2
    exact absurd rfl h2

/-! ## T5.1: the pull-back is generable and restricts to `u` on the image -/

/-- **T5.1 (headline). Pull-back preserves generability**: for a strictly increasing deferral
function `f` (FAF's `StrictlyIncreasingDeferral`, the `thm:wubaff` schedule condition) and a
`PGenerableWeighting u`, `pullBack f u` is a `PGenerableWeighting`. The certificate: the emitted
serialization dispatches on the unary ruler `preimageCount` and reindexes `u`'s stream by the
unary ruler `preimageIndex` (`MachineSpliceStream.ifZero`, `.comp`); the rank bound is
`rank (u k) ≤ k ≤ f k = m`; closure is inherited. Only `f.graph_fp` is used, through FAF's
`scheduledMatch` ruler — no poly-time computability of `f`.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005)
Kind: P
Fidelity: exact
Hyps: (a) none (strict monotonicity is the source's "strictly increasing", FAF's `StrictlyIncreasingDeferral`) -/
theorem pullBack_pgenerable (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {u : ℕ → EF} (hu : PGenerableWeighting u) : PGenerableWeighting (pullBack f u) := by
  have hinj : Function.Injective f.f := hf.injective
  refine { polySeg := ?_, rank_le := ?_, closed := ?_ }
  · refine (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
      (hu.polySeg.comp (unaryRuler_preimageIndex f)) (unaryRuler_preimageCount f)).of_eq
      fun m => ?_
    rw [pullBack_eq f hinj u m]
    split_ifs <;> rfl
  · intro m
    unfold pullBack
    split_ifs with h
    · exact (hu.rank_le _).trans (Nat.lt_succ_iff.mp (Nat.find_spec h).1)
    · simp
  · intro m ρ V
    unfold pullBack
    split_ifs with h
    · exact hu.closed _ ρ V
    · simp [EF.denote]

/-- **T5.1, the restriction:** on the image of an injective `f`, the pull-back is `u`:
`pullBack f u (f n) = u n`.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pullBack_apply (f : DeferralFunction) (hinj : Function.Injective f.f) (u : ℕ → EF)
    (n : ℕ) : pullBack f u (f.f n) = u n := by
  have h : ∃ k, k < f.f n + 1 ∧ f.f k = f.f n := ⟨n, Nat.lt_succ_of_lt (f.lt n), rfl⟩
  unfold pullBack
  rw [dif_pos h]
  congr 1
  rw [Nat.find_eq_iff]
  exact ⟨⟨Nat.lt_succ_of_lt (f.lt n), rfl⟩, fun k hk hfk => absurd (hinj hfk.2) hk.ne⟩

/-- **Bonus (L):** the pull-back is supported on the image of `f` — FAF's
`WeightingSupportedOnDeferralImage`, the `thm:wubaff` support premise — by construction.
Source: mandate T5.1 (bonus row); FAF `WeightingSupportedOnDeferralImage`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pullBack_supported (f : DeferralFunction) (u : ℕ → EF) (P : History) :
    WeightingSupportedOnDeferralImage (pullBack f u) P f := by
  intro m hm
  unfold pullBack at hm
  split_ifs at hm with h
  · exact ⟨Nat.find h, (Nat.find_spec h).2⟩
  · exact absurd (by simp) hm

/-! ## T5.2: a day-`n` generable gate is a legal `ccee` weight -/

/-- **T5.2. The rational twin: pull-back preserves `PGenerableRat`.** A `ConditionalExpectationQuote`
(`thm:ccee`) takes `w : ℕ → ℚ` with `weight_generable : PGenerableRat P w` and gates at `w (f n)`;
for a day-`n` generable rational gate `q`, `pullBackRat f q` is a legal such `w`
(`pullBackRat_mem`, `pullBackRat_pgenerableRat`) with `w (f n) = q n` (`pullBackRat_apply`).
`ccee` itself is not re-proved.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005); FAF `ConditionalExpectationQuote`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem pullBackRat_pgenerableRat (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {P : History} {q : ℕ → ℚ} (hq : PGenerableRat P q) : PGenerableRat P (pullBackRat f q) := by
  obtain ⟨feat, hfeat⟩ := hq
  refine ⟨pullBack f feat,
    (pullBack_pgenerable f hf hfeat.toWeighting).toGeneratedRatFeature fun m => ?_⟩
  unfold pullBack pullBackRat
  split_ifs with h
  · exact hfeat.denote _
  · simp

/-- `pullBackRat f q (f n) = q n` for injective `f`.
Source: [[route-transitivity]] §2 line 68 (vq-wiki-2-005)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem pullBackRat_apply (f : DeferralFunction) (hinj : Function.Injective f.f) (q : ℕ → ℚ)
    (n : ℕ) : pullBackRat f q (f.f n) = q n := by
  have h : ∃ k, k < f.f n + 1 ∧ f.f k = f.f n := ⟨n, Nat.lt_succ_of_lt (f.lt n), rfl⟩
  unfold pullBackRat
  rw [dif_pos h]
  congr 1
  rw [Nat.find_eq_iff]
  exact ⟨⟨Nat.lt_succ_of_lt (f.lt n), rfl⟩, fun k hk hfk => absurd (hinj hfk.2) hk.ne⟩

/-- The pull-back of a `[0,1]`-valued rational sequence is `[0,1]`-valued (`weight_mem`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pullBackRat_mem (f : DeferralFunction) (q : ℕ → ℚ) (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (m : ℕ) : 0 ≤ pullBackRat f q m ∧ pullBackRat f q m ≤ 1 := by
  unfold pullBackRat
  split_ifs
  · exact hq _
  · norm_num

/-! ## T5.1's hypothesis is inhabited by FAF's deferral functions

FAF ships `succDeferral` (`f n = n + 1`) and `doublingDeferral` (`f n = 2 ^ n`) as
`DeferralFunction`s but states `StrictlyIncreasingDeferral` for neither (audit r1 adversarial
3); both are proved here, with the pull-back along `succDeferral` evaluated on and off the image.
-/

/-- `succDeferral` is strictly increasing.
Source: none: infrastructure (T5.1 witness; FAF `succDeferral`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem succDeferral_strict : StrictlyIncreasingDeferral succDeferral := by
  intro a b h
  show a + 1 < b + 1
  omega

/-- `doublingDeferral` is strictly increasing.
Source: none: infrastructure (T5.1 witness; FAF `doublingDeferral`)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem doublingDeferral_strict : StrictlyIncreasingDeferral doublingDeferral := by
  intro a b h
  show 2 ^ a < 2 ^ b
  exact Nat.pow_lt_pow_right (by norm_num) h

/-- T5.1 at `succDeferral`: the pull-back of any generable weighting along `n ↦ n + 1` is
generable, and on the image it is `u` (`pullBack succDeferral u (n + 1) = u n`).
Source: none: infrastructure (T5.1 witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem pullBack_succ {u : ℕ → EF} (hu : PGenerableWeighting u) :
    PGenerableWeighting (pullBack succDeferral u) ∧
      ∀ n, pullBack succDeferral u (n + 1) = u n :=
  ⟨pullBack_pgenerable succDeferral succDeferral_strict hu,
    fun n => pullBack_apply succDeferral succDeferral_strict.injective u n⟩

/-- Off the image of `succDeferral` (`0`), the pull-back is the zero constant — the default
value `EF.const 0` of `pullBack`, exhibited.
Source: none: infrastructure (T5.1 witness)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem pullBack_succ_zero (u : ℕ → EF) : pullBack succDeferral u 0 = EF.const 0 := by
  unfold pullBack
  rw [dif_neg]
  rintro ⟨k, -, hk⟩
  exact Nat.succ_ne_zero k hk

end Cleanroom.Found.LiQuoteLane
