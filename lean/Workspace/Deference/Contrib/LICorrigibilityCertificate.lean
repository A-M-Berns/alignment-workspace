/-
# The generability certificate for the compiled corrigibility constraint

Round `projects/deference/rounds/2026-09-15-li-corrigibility/`, landing pass.

`LICorrigibility.li_bypass_le` takes the pinned library's operational package
(`BoundedSequence`, `MeshSoftmaxOperationalWitness`, threshold codes) as named
hypotheses.  The pinned `Construction/Witnesses/LUVSyntax.lean` derives that whole package
from one syntactic certificate, `LUVCombinationSyntax`: a compact presentation naming the
constants, coefficients, LUVs and threshold sentences of the sequence, with each stream
polynomially emitted.  This file **constructs that certificate** for the compiled
constraint `B_n = U_raw − U_corr − λ·G_δ − G_ρ − G_M`.

**1. Emission of the concrete threshold families.**  `rpnSentenceCodes_imp` is the
implication twin of the pinned `RpnSentenceCodes.and` (parser tag `2`).  `gate`,
`indicator` and `constLUV` families are emitted from the emission of their inputs:
`gate_thresholdCodeSeq` (a gated family from its gate sentences and base thresholds),
`indicator_thresholdCodeSeq` (an indicator family from its sentences),
`constLUV_thresholdCodeSeq_pos` / `constLUV_thresholdCodeSeq_zero` (constants).  Each
threshold test on the paired index is a poly-fueled natural-number computation.

**2. The certificate.**  `MediatedPair.syntaxOf` packages a `MediatedPair` sequence into
`LUVCombinationSyntax (fun n => (p n).B)` from: an e.c. code of `−λ_n`, and threshold
emission of the five component families.  `MediatedPair.boundedSequence` adds the `ℓ¹`
bound `4 + Λ`.

**3. The endpoints.**  `li_bypass_le_ofSyntax` — the corollary of
`expcoh_ofSyntax` with the certificate as data; `li_bypass_le_generated` — the same with
the certificate *constructed* from the five component emissions;
`li_bypass_le_compiled` — the same for pairs *compiled* from activation sentence families
and base evaluation families by `MediatedPair.compile`, whose hypotheses are exactly the
realization's inputs: emission of the two activation sentence families, emission of the
four base evaluation families, an e.c. `λ_n` with a uniform bound, validity in every
completed-theory world, and a consistent world at every stage.  `Witness.li_instance`
discharges every one of them but the last on a constant family over two atoms: the
theorem's hypotheses are inhabited.

**What this does not establish.**  The finite-menu (T3′) weighting's certificate: the
near-argmax weights are expressible features folded over a growing menu, and their
serialization needs a variable-width fold the pinned splice suite exposes only for token
concatenation, not for `max`/reciprocal chains; that is the residual named in the round's
`LUV_COMPILATION.md`.  Names are provisional (`AGENTS.md` standard 6).
-/
import LogicalInduction.Construction.Witnesses.LUVSyntax
import Workspace.Deference.Contrib.LICorrigibility

namespace Workspace.Deference.Contrib.LICorrigibility

open LogicalInduction
open Filter Topology
open scoped Classical

/-! ## 1. Emission of the concrete threshold families -/

section Emission

/-- Implication of two sentence-block streams: the fixed `🡒` tag (`2`) in front of the two
blocks, mirroring the pinned `RpnSentenceCodes.and`. -/
lemma rpnSentenceCodes_imp {φ ψ : ℕ → Sentence}
    (hφ : RpnSentenceCodes φ) (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes (fun z => (φ z).imp (ψ z)) := by
  obtain ⟨a, ha, hpa⟩ := hφ
  obtain ⟨b, hb, hpb⟩ := hψ
  have h2 : PolySegStream (fun _ : ℕ => [2]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 2)
  refine ⟨fun z => 2 :: (a z ++ b z), ((h2.append ha).append hb).of_eq (fun z => by simp),
    fun z => ?_⟩
  have hlen : (2 :: (a z ++ b z)).length = (a z).length + (b z).length + 1 := by
    simp
  rw [hlen, parseRpn_cons]
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  rw [parseRpn_block_head (hpa z) (b z) (by omega)]
  simp only [Option.bind_some]
  rw [parseRpn_mono (b z) (show (b z).length ≤ (a z).length + (b z).length by omega)
    (hpb z)]
  rfl

/-- Negation of a sentence-block stream. -/
lemma rpnSentenceCodes_neg {ψ : ℕ → Sentence} (hψ : RpnSentenceCodes ψ) :
    RpnSentenceCodes (fun z => neg (ψ z)) :=
  rpnSentenceCodes_imp hψ (RpnSentenceCodes.const LO.Propositional.Formula.falsum)

/-- The threshold ratio of the paired index is never negative. -/
lemma threshold_nonneg (m : ℕ) :
    ¬ ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 0) :=
  not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- **A gated family is emitted** from its gate sentences and its base thresholds. -/
lemma gate_thresholdCodeSeq {φ : ℕ → Sentence} {X : ℕ → LUV}
    (hφ : RpnSentenceCodes φ) (hX : LUV.RpnThresholdCodeSeq X) :
    LUV.RpnThresholdCodeSeq (fun n => gate (φ n) (X n)) := by
  unfold LUV.RpnThresholdCodeSeq at hX ⊢
  refine (RpnSentenceCodes.and (hφ.comp PolyFueled.left) hX).of_eq (fun m => ?_)
  simp only [gate, if_neg (threshold_nonneg m)]
  rfl

/-- The poly-fueled projections of the paired threshold index. -/
lemma index_i_poly : ∃ c, PolyFueled c (fun m : ℕ => m.unpair.2.unpair.2) :=
  ⟨_, PolyFueled.right.comp PolyFueled.right⟩

lemma index_k_poly : ∃ c, PolyFueled c (fun m : ℕ => m.unpair.2.unpair.1) :=
  ⟨_, PolyFueled.left.comp PolyFueled.right⟩

/-- **An indicator family is emitted** from its sentences.  The test `(i + 1 − k)·k = 0`
decides `i/k < 1` on the paired index. -/
lemma indicator_thresholdCodeSeq {ψ : ℕ → Sentence} (hψ : RpnSentenceCodes ψ) :
    LUV.RpnThresholdCodeSeq (fun n => indicator (ψ n)) := by
  unfold LUV.RpnThresholdCodeSeq
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨ci, hi⟩ := index_i_poly
  obtain ⟨ck, hk⟩ := index_k_poly
  have ht : PolyFueled _ (fun m : ℕ =>
      (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1) * m.unpair.2.unpair.1) :=
    (hmul.comp ((subc_polyFueled.comp (hi.succ_comp.pair hk)).pair
      hk)).of_eq (fun m => by simp)
  refine (RpnSentenceCodes.ifZero (hψ.comp PolyFueled.left)
    (RpnSentenceCodes.const bot) ht).of_eq (fun m => ?_)
  simp only [indicator, if_neg (threshold_nonneg m)]
  set i := m.unpair.2.unpair.2
  set k := m.unpair.2.unpair.1
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [hk]
  · have hkq : (0 : ℚ) < k := by exact_mod_cast hk
    have hiff : (i : ℚ) / (k : ℚ) < 1 ↔ i < k := by
      rw [div_lt_one hkq]; exact_mod_cast Iff.rfl
    by_cases hik : i < k
    · have h0 : (i + 1 - k) * k = 0 := by
        rw [Nat.sub_eq_zero_of_le (by omega), zero_mul]
      simp [h0, hiff.mpr hik]
    · have h0 : (i + 1 - k) * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      simp [h0, hiff, hik]

/-- **A positive constant family is emitted.**  For `q = a/b` with `a, b > 0` the test
`(b·i + 1 − a·k)·k = 0` decides `i/k < a/b` on the paired index. -/
lemma constLUV_thresholdCodeSeq_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    LUV.RpnThresholdCodeSeq (fun _ => constLUV ((a : ℚ) / (b : ℚ))) := by
  unfold LUV.RpnThresholdCodeSeq
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  obtain ⟨ci, hi⟩ := index_i_poly
  obtain ⟨ck, hk⟩ := index_k_poly
  have hbi : PolyFueled _ (fun m : ℕ => b * m.unpair.2.unpair.2) :=
    (hmul.comp ((PolyFueled.const b).pair hi)).of_eq (fun m => by simp)
  have hak : PolyFueled _ (fun m : ℕ => a * m.unpair.2.unpair.1) :=
    (hmul.comp ((PolyFueled.const a).pair hk)).of_eq (fun m => by simp)
  have ht : PolyFueled _ (fun m : ℕ =>
      (b * m.unpair.2.unpair.2 + 1 - a * m.unpair.2.unpair.1) * m.unpair.2.unpair.1) :=
    (hmul.comp ((subc_polyFueled.comp (hbi.succ_comp.pair hak)).pair
      hk)).of_eq (fun m => by simp)
  refine (RpnSentenceCodes.ifZero (RpnSentenceCodes.const top)
    (RpnSentenceCodes.const bot) ht).of_eq (fun m => ?_)
  simp only [constLUV]
  set i := m.unpair.2.unpair.2
  set k := m.unpair.2.unpair.1
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hq : (0 : ℚ) < (a : ℚ) / (b : ℚ) := div_pos (by exact_mod_cast ha) hbq
    simp [hk, hq]
  · have hkq : (0 : ℚ) < k := by exact_mod_cast hk
    have hiff : (i : ℚ) / (k : ℚ) < (a : ℚ) / (b : ℚ) ↔ b * i < a * k := by
      rw [lt_div_iff₀ hbq, div_mul_eq_mul_div, div_lt_iff₀ hkq]
      constructor
      · intro h; exact_mod_cast (by linarith : (b : ℚ) * i < a * k)
      · intro h; have : (b : ℚ) * i < a * k := by exact_mod_cast h
        linarith
    by_cases hlt : b * i < a * k
    · have h0 : (b * i + 1 - a * k) * k = 0 := by
        rw [Nat.sub_eq_zero_of_le (by omega), zero_mul]
      simp [h0, hiff.mpr hlt]
    · have h0 : (b * i + 1 - a * k) * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      simp [h0, hiff, hlt]

/-- **The zero constant family is emitted**: every threshold at `r ≥ 0` is `⊥`. -/
lemma constLUV_thresholdCodeSeq_zero :
    LUV.RpnThresholdCodeSeq (fun _ => constLUV 0) := by
  unfold LUV.RpnThresholdCodeSeq
  refine (RpnSentenceCodes.const bot).of_eq (fun m => ?_)
  simp only [constLUV, if_neg (threshold_nonneg m)]

end Emission

/-! ## 2. The certificate -/

section Certificate

/-- The `j`-th variable of a pair. -/
def luvOf (p : MediatedPair) : ℕ → LUV
  | 0 => p.Uraw
  | 1 => p.Ucorr
  | 2 => p.Gδ
  | 3 => p.Gρ
  | _ => p.GM

/-- The `j`-th coefficient of a pair. -/
def coefOf (p : MediatedPair) : ℕ → EF
  | 0 => EF.const 1
  | 1 => EF.const (-1)
  | 2 => EF.const (-p.lam)
  | _ => EF.const (-1)

lemma B_terms_eq (p : MediatedPair) :
    (p.B).terms = (List.range 5).map (fun j => (coefOf p j, luvOf p j)) := by
  simp [MediatedPair.B, List.range_succ, coefOf, luvOf]

/-- The paired-index map dropping the term number: `⟨⟨n,j⟩,t⟩ ↦ ⟨n,t⟩`. -/
lemma dropTerm_poly :
    ∃ c, PolyFueled c (fun m : ℕ => Nat.pair m.unpair.1.unpair.1 m.unpair.2) :=
  ⟨_, (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right⟩

/-- The term number of a paired threshold index. -/
lemma termIndex_poly : ∃ c, PolyFueled c (fun m : ℕ => m.unpair.1.unpair.2) :=
  ⟨_, PolyFueled.right.comp PolyFueled.left⟩

/-- A reindexed component family: its threshold emission at the flattened index. -/
lemma component_reindexed {X : ℕ → LUV} (hX : LUV.RpnThresholdCodeSeq X) :
    RpnSentenceCodes (fun m => (X m.unpair.1.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) := by
  unfold LUV.RpnThresholdCodeSeq at hX
  obtain ⟨cd, hd⟩ := dropTerm_poly
  exact (hX.comp hd).of_eq (fun m => by simp)

/-- The test `j − c` on the term number. -/
lemma termTest_poly (c : ℕ) : ∃ cc, PolyFueled cc (fun m : ℕ => m.unpair.1.unpair.2 - c) := by
  obtain ⟨ct, ht⟩ := termIndex_poly
  exact ⟨_, (subc_polyFueled.comp (ht.pair (PolyFueled.const c))).of_eq (fun m => by simp)⟩

/-- **Threshold emission of the five-way dispatch.** -/
lemma luvOf_thresholdCodeSeq (p : ℕ → MediatedPair)
    (hU : LUV.RpnThresholdCodeSeq (fun n => (p n).Uraw))
    (hC : LUV.RpnThresholdCodeSeq (fun n => (p n).Ucorr))
    (hδ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gδ))
    (hρ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gρ))
    (hM : LUV.RpnThresholdCodeSeq (fun n => (p n).GM)) :
    LUV.RpnThresholdCodeSeq (fun z => luvOf (p z.unpair.1) z.unpair.2) := by
  unfold LUV.RpnThresholdCodeSeq
  obtain ⟨c0, h0⟩ := termTest_poly 0
  obtain ⟨c1, h1⟩ := termTest_poly 1
  obtain ⟨c2, h2⟩ := termTest_poly 2
  obtain ⟨c3, h3⟩ := termTest_poly 3
  refine (RpnSentenceCodes.ifZero (component_reindexed hU)
    (RpnSentenceCodes.ifZero (component_reindexed hC)
      (RpnSentenceCodes.ifZero (component_reindexed hδ)
        (RpnSentenceCodes.ifZero (component_reindexed hρ) (component_reindexed hM) h3)
        h2)
      h1)
    h0).of_eq (fun m => ?_)
  rcases hj : m.unpair.1.unpair.2 with _ | _ | _ | _ | j <;> simp [luvOf, hj]

/-- The coefficient stream is emitted: three constants and the e.c. code of `−λ_n`. -/
lemma coefOf_spliceStream (p : ℕ → MediatedPair)
    (hlam : ∃ c, PolyFueled c (fun n => Encodable.encode (-(p n).lam))) :
    RpnSpliceStream (fun z => (coefOf (p z.unpair.1) z.unpair.2).serialize) := by
  have hlam' : ∃ c, PolyFueled c (fun z : ℕ => Encodable.encode (-(p z.unpair.1).lam)) := by
    obtain ⟨c, hc⟩ := hlam
    exact ⟨_, hc.comp PolyFueled.left⟩
  have htest : ∀ c, PolyFueled _ (fun z : ℕ => z.unpair.2 - c) := fun c =>
    (subc_polyFueled.comp (PolyFueled.right.pair (PolyFueled.const c))).of_eq
      (fun z => by simp)
  refine (RpnSpliceStream.ifZero (RpnSpliceStream.serialize_const 1)
    (RpnSpliceStream.ifZero (RpnSpliceStream.serialize_const (-1))
      (RpnSpliceStream.ifZero (RpnSpliceStream.serialize_const_comp hlam')
        (RpnSpliceStream.serialize_const (-1)) (htest 2))
      (htest 1))
    (htest 0)).of_eq (fun z => ?_)
  rcases hj : z.unpair.2 with _ | _ | _ | j <;> simp [coefOf]

/-- **The generability certificate** of the compiled constraint sequence. -/
noncomputable def MediatedPair.syntaxOf (p : ℕ → MediatedPair)
    (hlam : ∃ c, PolyFueled c (fun n => Encodable.encode (-(p n).lam)))
    (hU : LUV.RpnThresholdCodeSeq (fun n => (p n).Uraw))
    (hC : LUV.RpnThresholdCodeSeq (fun n => (p n).Ucorr))
    (hδ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gδ))
    (hρ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gρ))
    (hM : LUV.RpnThresholdCodeSeq (fun n => (p n).GM)) :
    LUVCombinationSyntax (fun n => (p n).B) where
  termCount := fun _ => 5
  coefficient := fun z => coefOf (p z.unpair.1) z.unpair.2
  luv := fun z => luvOf (p z.unpair.1) z.unpair.2
  termCount_poly := ⟨_, PolyFueled.const 5⟩
  const_poly := by
    simpa [MediatedPair.B] using RpnSpliceStream.serialize_const (0 : ℚ)
  coefficient_poly := coefOf_spliceStream p hlam
  threshold_poly := luvOf_thresholdCodeSeq p hU hC hδ hρ hM
  terms_eq := fun n => by
    rw [B_terms_eq]
    simp [Nat.unpair_pair]
  const_rank := fun n => by simp [MediatedPair.B]
  coefficient_rank := fun n j _ => by
    simp only [Nat.unpair_pair]
    rcases j with _ | _ | _ | j <;> simp [coefOf]
  const_closed := fun n ρ V => by simp [MediatedPair.B, EF.denote]
  coefficient_closed := fun z ρ V => by
    rcases hj : z.unpair.2 with _ | _ | _ | j <;> simp [coefOf, EF.denote]

/-- The `ℓ¹` norm of the compiled constraint is `4 + |λ_n|`. -/
lemma B_l1Norm (p : MediatedPair) (P : History) :
    (p.B).l1Norm P = 4 + |((p.lam : ℚ) : ℝ)| := by
  simp only [LUVCombination.l1Norm, LUVCombination.shareNorm, MediatedPair.B, EF.denote,
    EF.denoteWith_const, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  simp only [abs_zero, abs_one, abs_neg]
  ring

/-- **The bounded combination sequence** (`def:blcp`) from the certificate and a uniform
bound on `λ_n`. -/
noncomputable def MediatedPair.boundedSequence (p : ℕ → MediatedPair) (P : History)
    (S : LUVCombinationSyntax (fun n => (p n).B))
    (Λ : ℝ) (hΛ : ∀ n, |((p n).lam : ℝ)| ≤ Λ) :
    LUVCombination.BoundedSequence (fun n => (p n).B) P where
  poly := S.polySequence
  bounded := ⟨4 + Λ, fun n => by rw [B_l1Norm]; linarith [hΛ n]⟩

end Certificate

/-! ## 3. The endpoints -/

section Endpoints

/-- The passage from the `expcoh` chain to `𝔼ₙ(B_n) ≲ₙ 0`, factored out of
`li_constraint_le`. -/
theorem constraint_le_of_chain {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Λ : ℝ) (hΛ : ∀ n, |((p n).lam : ℝ)| ≤ Λ)
    (hchain : limsup (fun n => ((p n).B).expect P n) atTop ≤
        limsup (fun n => ((p n).B).expectInf P) atTop ∧
      limsup (fun n => ((p n).B).expectInf P) atTop ≤
        limsup (LUVCombination.completedHigh (fun n => (p n).B) P DP) atTop) :
    (fun n => ((p n).B).expect P n) ≲ₙ fun _ => 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨b, hbΛ⟩ := exists_rat_gt (max (4 + Λ) 0)
  have hshare : ∀ n, ((p n).B).shareNorm P ≤ (b : ℝ) := fun n => by
    have h1 : ((p n).B).shareNorm P ≤ ((p n).B).l1Norm P :=
      le_add_of_nonneg_left (abs_nonneg _)
    rw [B_l1Norm] at h1
    linarith [hΛ n, (le_max_left (4 + Λ) 0).trans hbΛ.le]
  have hhigh : limsup (LUVCombination.completedHigh (fun n => (p n).B) P DP) atTop ≤ 0 := by
    apply limsup_le_of_le
    · exact (isBoundedUnder_of ⟨-(3 + (b : ℝ)),
        fun n => completedHigh_ge p hvalid hworld b hshare n⟩).isCoboundedUnder_flip
    · exact Eventually.of_forall (completedHigh_le_zero p hvalid)
  have hlim : limsup (fun n => ((p n).B).expect P n) atTop ≤ 0 :=
    (hchain.1.trans hchain.2).trans hhigh
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun n => ((p n).B).expect P n) := by
    refine isBoundedUnder_of ⟨4 + Λ, fun n => ?_⟩
    have := ((p n).B).abs_expectAt_le_l1Norm P (n + 1) n (hP n)
    rw [B_l1Norm] at this
    have := abs_le.mp this
    show ((p n).B).expectAt P (n + 1) n ≤ 4 + Λ
    linarith [hΛ n]
  intro ε hε
  filter_upwards [eventually_lt_of_limsup_lt (show limsup (fun n => ((p n).B).expect P n)
    atTop < ε by linarith) hup] with n hn
  linarith

/-- **The corollary of `expcoh_ofSyntax`**: with the certificate as data, the inductor's
expectations respect the inequality. -/
theorem li_bypass_le_ofSyntax {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Λ : ℝ) (hΛ : ∀ n, |((p n).lam : ℝ)| ≤ Λ)
    (S : LUVCombinationSyntax (fun n => (p n).B)) :
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun n => ((p n).lam : ℝ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
        + (p n).GM.expect P n := by
  have hcoh := LUVCombination.BoundedSequence.expcoh_ofSyntax
    (MediatedPair.boundedSequence p P S Λ hΛ) S (worldValued_of_valid p hvalid) hworld
  have hc := constraint_le_of_chain p hvalid hworld Λ hΛ ⟨hcoh.2.1, hcoh.2.2⟩
  intro ε hε
  filter_upwards [hc ε hε] with n hn
  rw [MediatedPair.expect_eq] at hn
  linarith

/-- **T3 with the certificate constructed**: the hypotheses are the e.c. code of `λ_n`,
its uniform bound, threshold emission of the five component families, validity in every
completed-theory world, and a consistent world at every stage. -/
theorem li_bypass_le_generated {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → MediatedPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ValidAt (p n) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Λ : ℝ) (hΛ : ∀ n, |((p n).lam : ℝ)| ≤ Λ)
    (hlam : ∃ c, PolyFueled c (fun n => Encodable.encode (-(p n).lam)))
    (hU : LUV.RpnThresholdCodeSeq (fun n => (p n).Uraw))
    (hC : LUV.RpnThresholdCodeSeq (fun n => (p n).Ucorr))
    (hδ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gδ))
    (hρ : LUV.RpnThresholdCodeSeq (fun n => (p n).Gρ))
    (hM : LUV.RpnThresholdCodeSeq (fun n => (p n).GM)) :
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun n => ((p n).lam : ℝ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
        + (p n).GM.expect P n :=
  li_bypass_le_ofSyntax p hvalid hworld Λ hΛ (MediatedPair.syntaxOf p hlam hU hC hδ hρ hM)

/-- **The compiler.**  A mediated pair from two activation sentences, four base
evaluation variables and the stability coefficient: the raw and corrigibilized
securities gated on their own activations, the discrepancy and regret gated on the common
branch, and the indicator of the directional mismatch. -/
def MediatedPair.compile (φraw φcorr : Sentence) (Xr Xa Xδ Xρ : LUV) (lam : ℚ) :
    MediatedPair where
  Uraw := gate φraw Xr
  Ucorr := gate φcorr Xa
  Gδ := gate (LO.Propositional.Formula.and φraw φcorr) Xδ
  Gρ := gate (LO.Propositional.Formula.and φraw φcorr) Xρ
  GM := indicator (LO.Propositional.Formula.and φraw (neg φcorr))
  φraw := φraw
  φcorr := φcorr
  lam := lam

/-- The compiled pair's validity package from the base values. -/
def MediatedPair.compile_validAt (φraw φcorr : Sentence) (Xr Xa Xδ Xρ : LUV) (lam : ℚ)
    (v : PCWorld) (wr wapp wa δ ρ : ℝ)
    (hwr : 0 ≤ wr ∧ wr ≤ 1) (hwa : 0 ≤ wa ∧ wa ≤ 1) (hδ : 0 ≤ δ ∧ δ ≤ 1) (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hxr : v.ValuesAt Xr wr) (hxa : v.ValuesAt Xa wa) (hxδ : v.ValuesAt Xδ δ)
    (hxρ : v.ValuesAt Xρ ρ)
    (lip : v.Holds φraw → v.Holds φcorr → |wr - wapp| ≤ (lam : ℝ) * δ)
    (regret : v.Holds φraw → v.Holds φcorr → wapp - wa ≤ ρ) :
    ValidAt (MediatedPair.compile φraw φcorr Xr Xa Xδ Xρ lam) v :=
  ValidAt.ofGated (p := MediatedPair.compile φraw φcorr Xr Xa Xδ Xρ lam)
    (Xr := Xr) (Xa := Xa) (Xδ := Xδ) (Xρ := Xρ) wr wapp wa δ ρ hwr hwa hδ hρ
    (gate_gatedAt v _ _) hxr (gate_gatedAt v _ _) hxa (gate_gatedAt v _ _) hxδ
    (gate_gatedAt v _ _) hxρ (indicator_indicatorAt v _) lip regret

/-- **T3 for compiled pairs.**  The hypotheses are exactly the realization's inputs:
emission of the activation sentence families, emission of the base evaluation families,
an e.c. bounded `λ_n`, validity in every completed-theory world, a consistent world at
every stage. -/
theorem li_bypass_le_compiled {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φraw φcorr : ℕ → Sentence) (Xr Xa Xδ Xρ : ℕ → LUV) (lam : ℕ → ℚ)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φraw n) (φcorr n) (Xr n) (Xa n) (Xδ n) (Xρ n) (lam n)) v)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Λ : ℝ) (hΛ : ∀ n, |((lam n : ℚ) : ℝ)| ≤ Λ)
    (hlam : ∃ c, PolyFueled c (fun n => Encodable.encode (-(lam n))))
    (hφraw : RpnSentenceCodes φraw) (hφcorr : RpnSentenceCodes φcorr)
    (hXr : LUV.RpnThresholdCodeSeq Xr) (hXa : LUV.RpnThresholdCodeSeq Xa)
    (hXδ : LUV.RpnThresholdCodeSeq Xδ) (hXρ : LUV.RpnThresholdCodeSeq Xρ) :
    let p := fun n => MediatedPair.compile (φraw n) (φcorr n) (Xr n) (Xa n) (Xδ n) (Xρ n) (lam n)
    (fun n => (p n).Uraw.expect P n - (p n).Ucorr.expect P n) ≲ₙ
      fun n => ((p n).lam : ℝ) * (p n).Gδ.expect P n + (p n).Gρ.expect P n
        + (p n).GM.expect P n := by
  intro p
  have hboth : RpnSentenceCodes (fun n => LO.Propositional.Formula.and (φraw n) (φcorr n)) :=
    RpnSentenceCodes.and hφraw hφcorr
  have hmis : RpnSentenceCodes (fun n => LO.Propositional.Formula.and (φraw n) (neg (φcorr n))) :=
    RpnSentenceCodes.and hφraw (rpnSentenceCodes_neg hφcorr)
  exact li_bypass_le_generated p hvalid hworld Λ hΛ hlam
    (gate_thresholdCodeSeq hφraw hXr) (gate_thresholdCodeSeq hφcorr hXa)
    (gate_thresholdCodeSeq hboth hXδ) (gate_thresholdCodeSeq hboth hXρ)
    (indicator_thresholdCodeSeq hmis)

end Endpoints

/-! ## 4. Witness: every hypothesis of the compiled theorem is inhabited -/

namespace Witness

open LO.Propositional (Formula)

/-- The constant family of `LICorrigibility.Witness.pair`, as a compiled pair. -/
theorem pair_eq_compile :
    pair = MediatedPair.compile (Formula.atom 0) (Formula.atom 1)
      (constLUV 1) (constLUV (1/2)) (constLUV 0) (constLUV (1/2)) 1 := rfl

/-- **The compiled theorem, fully instantiated** on the constant two-atom family: every
hypothesis but the consistency of the deductive process is discharged. -/
theorem li_instance {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => pair.Uraw.expect P n - pair.Ucorr.expect P n) ≲ₙ
      fun n => ((pair.lam : ℚ) : ℝ) * pair.Gδ.expect P n + pair.Gρ.expect P n
        + pair.GM.expect P n := by
  have h := li_bypass_le_compiled (P := P) (DP := DP)
    (fun _ => Formula.atom 0) (fun _ => Formula.atom 1)
    (fun _ => constLUV 1) (fun _ => constLUV (1/2)) (fun _ => constLUV 0)
    (fun _ => constLUV (1/2)) (fun _ => 1)
    (fun _ v _ => valid v) hworld 1 (fun _ => by norm_num)
    ⟨_, PolyFueled.const (Encodable.encode (-(1 : ℚ)))⟩
    (RpnSentenceCodes.const _) (RpnSentenceCodes.const _)
    (by simpa using constLUV_thresholdCodeSeq_pos 1 1 one_pos one_pos)
    (by simpa using constLUV_thresholdCodeSeq_pos 1 2 one_pos two_pos)
    constLUV_thresholdCodeSeq_zero
    (by simpa using constLUV_thresholdCodeSeq_pos 1 2 one_pos two_pos)
  simpa [pair_eq_compile] using h

end Witness

end Workspace.Deference.Contrib.LICorrigibility

#print axioms Workspace.Deference.Contrib.LICorrigibility.rpnSentenceCodes_imp
#print axioms Workspace.Deference.Contrib.LICorrigibility.gate_thresholdCodeSeq
#print axioms Workspace.Deference.Contrib.LICorrigibility.indicator_thresholdCodeSeq
#print axioms Workspace.Deference.Contrib.LICorrigibility.constLUV_thresholdCodeSeq_pos
#print axioms Workspace.Deference.Contrib.LICorrigibility.constLUV_thresholdCodeSeq_zero
#print axioms Workspace.Deference.Contrib.LICorrigibility.luvOf_thresholdCodeSeq
#print axioms Workspace.Deference.Contrib.LICorrigibility.coefOf_spliceStream
#print axioms Workspace.Deference.Contrib.LICorrigibility.MediatedPair.syntaxOf
#print axioms Workspace.Deference.Contrib.LICorrigibility.MediatedPair.boundedSequence
#print axioms Workspace.Deference.Contrib.LICorrigibility.constraint_le_of_chain
#print axioms Workspace.Deference.Contrib.LICorrigibility.li_bypass_le_ofSyntax
#print axioms Workspace.Deference.Contrib.LICorrigibility.li_bypass_le_generated
#print axioms Workspace.Deference.Contrib.LICorrigibility.MediatedPair.compile_validAt
#print axioms Workspace.Deference.Contrib.LICorrigibility.li_bypass_le_compiled
#print axioms Workspace.Deference.Contrib.LICorrigibility.Witness.li_instance
