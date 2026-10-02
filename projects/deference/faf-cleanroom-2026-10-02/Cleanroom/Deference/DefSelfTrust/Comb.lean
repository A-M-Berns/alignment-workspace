import Cleanroom.Found.DefLattice.TwoOptionLUV

/-!
# `def-self-trust` — combination infrastructure for the transfer lemma and the bets

Two pieces of plumbing that every `thm:expprovind` step of this package rests on:

* **`constComb`**: the constant-coefficient LUV combination `c₀ + Σᵢ cᵢ · Xᵢ(n)` over a list
  of e.c. LUV sequences, with its compact `LUVCombinationSyntax` (`constCombSyntax`) and
  `BoundedSequence` (`constComb_boundedSequence`). FAF has no such constructor for
  `MachineThresholdCodeSeq` sources (`def-lattice` F18 built the two three-term and one-term instances
  it needed by hand); this is the general list version, so the two-term transfer bet (target 1c),
  the two-term `est` bet (target 2), the three-term Lemma B bet (target 5) and the five-term
  Lemma C bet (target 6) are all one constructor.
* **`zeroPrefix`** and the *eventual* forms of `lic_expect_combination_provind_{le,ge}`
  (`expect_asympLE_of_eventually`, `expect_asympGE_of_eventually`,
  `expect_asympEq_zero_of_eventually_abs_le`): FAF's endpoints demand the world-value bound at
  **every** day; a bound that holds only eventually (a vanishing slack `s n → 0` makes the
  bound `≤ ε` only from some `N` on) is transported by zeroing the coefficients of the first
  `N` members — a finitely patched sequence with the same syntax, the same LUVs and value `0`
  on the patched prefix. This is the "tail trick" of the mandate's target 1c.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice

noncomputable section

/-! ## The constant-coefficient combination -/

/-- The constant-coefficient LUV combination `c₀ + Σ p.1 · p.2 n` over a list of
(coefficient, LUV-sequence) pairs, read at day `n`. Constants enter through
`LUVCombination.const` (FAF has no constant LUV).
Source: none: infrastructure (FAF `LUVCombination`, `def:luv`)
Kind: D
Fidelity: n/a -/
def constComb (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV))) (n : ℕ) : LUVCombination :=
  ⟨EF.const c₀, terms.map (fun p => (EF.const p.1, p.2 n))⟩

/-- The diagonal expectation of a constant-coefficient combination is the constant plus the
coefficient-weighted sum of the members' expectations.
Source: none: infrastructure (FAF `LUVCombination.expect`)
Kind: L
Fidelity: n/a -/
lemma constComb_expect (P : History) (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV))) (n : ℕ) :
    (constComb c₀ terms n).expect P n =
      (c₀ : ℝ) + (terms.map (fun p => (p.1 : ℝ) * (p.2 n).expect P n)).sum := by
  simp [constComb, LUVCombination.expect, LUVCombination.expectAt, LUV.expect, List.map_map,
    Function.comp_def]

/-- The world value of a constant-coefficient combination under a LUV valuation `ν`.
Source: none: infrastructure (FAF `LUVCombination.value`)
Kind: L
Fidelity: n/a -/
lemma constComb_value (P : History) (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV))) (n : ℕ)
    (ν : LUV → ℝ) :
    (constComb c₀ terms n).value P ν =
      (c₀ : ℝ) + (terms.map (fun p => (p.1 : ℝ) * ν (p.2 n))).sum := by
  simp [constComb, LUVCombination.value, List.map_map, Function.comp_def]

/-- The `L¹` norm of a constant-coefficient combination is `|c₀| + Σ |cᵢ|`, independent of the
day.
Source: none: infrastructure (FAF `LUVCombination.l1Norm`, `def:blcp`)
Kind: L
Fidelity: n/a -/
lemma constComb_l1Norm (P : History) (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV))) (n : ℕ) :
    (constComb c₀ terms n).l1Norm P =
      |(c₀ : ℝ)| + (terms.map (fun p => |(p.1 : ℝ)|)).sum := by
  simp [constComb, LUVCombination.l1Norm, LUVCombination.shareNorm, List.map_map,
    Function.comp_def]

/-- A term of `constComb` is a coefficient paired with a member LUV read at day `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_constComb_terms {c₀ : ℚ} {terms : List (ℚ × (ℕ → LUV))} {n : ℕ}
    {p : EF × LUV} (hp : p ∈ (constComb c₀ terms n).terms) :
    ∃ q ∈ terms, p.2 = q.2 n := by
  simp only [constComb, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q, hq, rfl⟩

/-- The default LUV of the dispatch streams below (never read by `terms_eq`): the literal
indicator of `⊤`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev defaultLuvSeq : ℕ → LUV := fun _ => literalIndicator ⊤

/-- The default LUV sequence is machine-metered (a constant sentence family).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma defaultLuvSeq_machineThresholdCodeSeq : LUV.MachineThresholdCodeSeq defaultLuvSeq :=
  literalIndicator_machineThresholdCodeSeq (MachineSentenceCodes.const ⊤)

/-- The LUV stream of `constComb`: member `j` of the list at day `n`, read at the paired index
`⟨n, j⟩` (`List.getD` with the default beyond the list).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def luvDispatch (Xs : List (ℕ → LUV)) (z : ℕ) : LUV :=
  (Xs.getD z.unpair.2 defaultLuvSeq) z.unpair.1

/-- The coefficient stream of `constComb`: the `j`-th rational at the paired index `⟨n, j⟩`
(`0` beyond the list).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def coeffDispatch (cs : List ℚ) (z : ℕ) : EF :=
  EF.const (cs.getD z.unpair.2 0)

/-- The reindexer `⟨n, j+1⟩ ↦ ⟨n, j⟩` that peels one member off the dispatch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unaryRuler_peel : UnaryRuler (fun z : ℕ => Nat.pair z.unpair.1 (z.unpair.2 - 1)) :=
  UnaryRuler.unpairFst.pair (UnaryRuler.unpairSnd.sub (UnaryRuler.const 1))

/-- The LUV stream is machine-metered from the members' certificates (list induction, a
two-way dispatch on the paired index per member — FAF's `MachineSentenceCodes.ifZero`).
Source: none: infrastructure (FAF `LUV.MachineThresholdCodeSeq.reindex`,
`MachineSentenceCodes.ifZero`; the pattern of `def-lattice`'s
`hardSelectionLuv_machineThresholdCodeSeq`)
Kind: L
Fidelity: n/a -/
lemma luvDispatch_machineThresholdCodeSeq (Xs : List (ℕ → LUV))
    (hXs : ∀ X ∈ Xs, LUV.MachineThresholdCodeSeq X) :
    LUV.MachineThresholdCodeSeq (luvDispatch Xs) := by
  induction Xs with
  | nil =>
      have h := defaultLuvSeq_machineThresholdCodeSeq.reindex UnaryRuler.unpairFst
      unfold LUV.MachineThresholdCodeSeq at h ⊢
      exact h.of_eq (fun m => by simp [luvDispatch])
  | cons X Xs ih =>
      have hX : LUV.MachineThresholdCodeSeq X := hXs X (by simp)
      have ih' := ih (fun Y hY => hXs Y (by simp [hY]))
      have hj : UnaryRuler (fun m : ℕ => m.unpair.1.unpair.2) :=
        UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst
      have hX' := hX.reindex UnaryRuler.unpairFst
      have hrest := ih'.reindex unaryRuler_peel
      unfold LUV.MachineThresholdCodeSeq at hX' hrest ⊢
      refine (MachineSentenceCodes.ifZero hX' hrest hj).of_eq (fun m => ?_)
      simp only [luvDispatch, Nat.unpair_pair]
      split_ifs with hz
      · rw [hz, List.getD_cons_zero]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [hk, List.getD_cons_succ, Nat.succ_sub_one]

/-- The coefficient stream is machine-metered (list induction over `serialize_const`).
Source: none: infrastructure (FAF `MachineSpliceStream.ifZero`, `serialize_const`)
Kind: L
Fidelity: n/a -/
lemma coeffDispatch_spliceStream (cs : List ℚ) :
    MachineSpliceStream (fun z => (coeffDispatch cs z).serialize) := by
  induction cs with
  | nil => exact (MachineSpliceStream.serialize_const 0).of_eq (fun z => by simp [coeffDispatch])
  | cons c cs ih =>
      have hrest := ih.comp unaryRuler_peel
      refine (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const c) hrest
        UnaryRuler.unpairSnd).of_eq (fun z => ?_)
      simp only [coeffDispatch, Nat.unpair_pair]
      split_ifs with hz
      · rw [hz, List.getD_cons_zero]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        rw [hk, List.getD_cons_succ, Nat.succ_sub_one]

/-- The term list of `constComb` is the dispatch streams reassembled along `List.range`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constComb_terms_eq (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV))) (n : ℕ) :
    (constComb c₀ terms n).terms = (List.range terms.length).map (fun j =>
      (coeffDispatch (terms.map Prod.fst) (Nat.pair n j),
        luvDispatch (terms.map Prod.snd) (Nat.pair n j))) := by
  induction terms with
  | nil => simp [constComb]
  | cons p ps ih =>
      simp only [constComb, List.map_cons, List.length_cons, List.range_succ_eq_map,
        List.map_map, Function.comp_def, coeffDispatch, luvDispatch, Nat.unpair_pair,
        List.getD_cons_zero, List.getD_cons_succ]
      simp only [constComb] at ih
      rw [ih]
      simp only [coeffDispatch, luvDispatch, Nat.unpair_pair]

/-- **Compact syntax for the constant-coefficient combination** over machine-metered members.
Source: none: infrastructure (FAF API request: a constant-coefficient `LUVCombinationSyntax`
constructor over `MachineThresholdCodeSeq` sources — `def-lattice` F18, general list form)
Kind: D
Fidelity: n/a -/
def constCombSyntax (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV)))
    (hterms : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombinationSyntax (constComb c₀ terms) where
  termCount _ := terms.length
  coefficient := coeffDispatch (terms.map Prod.fst)
  luv := luvDispatch (terms.map Prod.snd)
  termCount_poly := UnaryRuler.const terms.length
  const_poly := MachineSpliceStream.serialize_const c₀
  coefficient_poly := coeffDispatch_spliceStream _
  threshold_poly := luvDispatch_machineThresholdCodeSeq _ (fun X hX => by
    simp only [List.mem_map] at hX
    obtain ⟨p, hp, rfl⟩ := hX
    exact hterms p hp)
  terms_eq n := constComb_terms_eq c₀ terms n
  const_rank n := by simp [constComb]
  coefficient_rank n j _ := by simp [coeffDispatch]
  const_closed n ρ V := by simp [constComb]
  coefficient_closed z ρ V := by simp [coeffDispatch]

/-- **`BoundedSequence` for the constant-coefficient combination**, from the members'
certificates; the `L¹` bound is the day-independent `|c₀| + Σ |cᵢ|`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def constComb_boundedSequence (P : History) (c₀ : ℚ) (terms : List (ℚ × (ℕ → LUV)))
    (hterms : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2) :
    LUVCombination.BoundedSequence (constComb c₀ terms) P where
  poly := (constCombSyntax c₀ terms hterms).polySequence
  bounded := ⟨|(c₀ : ℝ)| + (terms.map (fun p => |(p.1 : ℝ)|)).sum,
    fun n => (constComb_l1Norm P c₀ terms n).le⟩

/-! ## The zero-prefix patch (the tail trick) -/

/-- The combination with every coefficient and the constant replaced by `0` (same LUVs).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def zeroed (A : LUVCombination) : LUVCombination :=
  ⟨EF.const 0, A.terms.map (fun p => (EF.const 0, p.2))⟩

/-- The sequence zeroed on its first `N` members.
Source: none: infrastructure (mandate target 1c, "the tail trick")
Kind: D
Fidelity: n/a -/
def zeroPrefix (N : ℕ) (As : ℕ → LUVCombination) (n : ℕ) : LUVCombination :=
  if n < N then zeroed (As n) else As n

/-- The zeroed combination has world value `0` under every valuation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroed_value (A : LUVCombination) (P : History) (ν : LUV → ℝ) :
    (zeroed A).value P ν = 0 := by
  simp [zeroed, LUVCombination.value, List.map_map, Function.comp_def]

/-- The zeroed combination has `L¹` norm `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroed_l1Norm (A : LUVCombination) (P : History) : (zeroed A).l1Norm P = 0 := by
  simp [zeroed, LUVCombination.l1Norm, LUVCombination.shareNorm, List.map_map,
    Function.comp_def]

/-- A valuation coherent for `A` is coherent for `zeroed A` (same LUVs).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroed_valuesAt {A : LUVCombination} {v : PCWorld} {ν : LUV → ℝ}
    (h : A.ValuesAt v ν) : (zeroed A).ValuesAt v ν := by
  intro p hp
  simp only [zeroed, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact h q hq

/-- Beyond the prefix the patched sequence is the original.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zeroPrefix_of_le (N : ℕ) (As : ℕ → LUVCombination) {n : ℕ} (hn : N ≤ n) :
    zeroPrefix N As n = As n := by
  simp [zeroPrefix, not_lt.2 hn]

/-- The test ruler `n ↦ (n + 1) − N`, which vanishes exactly on `n < N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unaryRuler_prefixTest (N : ℕ) : UnaryRuler (fun n : ℕ => n + 1 - N) :=
  UnaryRuler.id.succ.sub (UnaryRuler.const N)

/-- The test on the paired index's first component.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unaryRuler_prefixTest_fst (N : ℕ) : UnaryRuler (fun z : ℕ => z.unpair.1 + 1 - N) :=
  UnaryRuler.unpairFst.succ.sub (UnaryRuler.const N)

/-- **The patched sequence has compact syntax** whenever the original does: same term count and
LUV stream, coefficients (and constants) zeroed on the prefix by a two-way dispatch on the
prefix test.
Source: none: infrastructure (mandate target 1c)
Kind: D
Fidelity: n/a -/
def zeroPrefixSyntax {As : ℕ → LUVCombination} (S : LUVCombinationSyntax As)
    (N : ℕ) : LUVCombinationSyntax (zeroPrefix N As) where
  termCount := S.termCount
  coefficient z := if z.unpair.1 < N then EF.const 0 else S.coefficient z
  luv := S.luv
  termCount_poly := S.termCount_poly
  const_poly := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
    S.const_poly (unaryRuler_prefixTest N)).of_eq (fun n => by
      simp only [DefSelfTrust.zeroPrefix]
      split_ifs with h1 h2 h2 <;> first | rfl | omega)
  coefficient_poly := (MachineSpliceStream.ifZero (MachineSpliceStream.serialize_const 0)
    S.coefficient_poly (unaryRuler_prefixTest_fst N)).of_eq (fun z => by
      split_ifs with h1 h2 h2 <;> first | rfl | omega)
  threshold_poly := S.threshold_poly
  terms_eq n := by
    by_cases hn : n < N
    · simp [DefSelfTrust.zeroPrefix, zeroed, hn, S.terms_eq n, List.map_map, Function.comp_def,
        Nat.unpair_pair]
    · simp [DefSelfTrust.zeroPrefix, hn, S.terms_eq n, Nat.unpair_pair]
  const_rank n := by
    simp only [DefSelfTrust.zeroPrefix]
    split_ifs
    · simp [zeroed]
    · exact S.const_rank n
  coefficient_rank n j hj := by
    simp only [Nat.unpair_pair]
    split_ifs
    · simp
    · exact S.coefficient_rank n j hj
  const_closed n ρ V := by
    simp only [DefSelfTrust.zeroPrefix]
    split_ifs
    · simp [zeroed]
    · exact S.const_closed n ρ V
  coefficient_closed z ρ V := by
    split_ifs
    · simp
    · exact S.coefficient_closed z ρ V

/-! ## Expectation provability induction with an eventual world bound -/

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-- **`thm:expprovind` (`≤` face) from an *eventual* world bound**, for a nonnegative bound
`c`: if from some day on every completed-theory world values the combination at most `c`, the
diagonal expectation is `≲ₙ c`. Proof: zero the prefix (value `0 ≤ c` there) and apply FAF's
`lic_expect_combination_provind_le` to the patched sequence, whose syntax is
`zeroPrefixSyntax`.
Source: none: infrastructure (mandate target 1c, the tail trick); FAF
`lic_expect_combination_provind_le` (`Construction/LUV/Endpoints.lean`)
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem expect_asympLE_of_eventually {As : ℕ → LUVCombination} (S : LUVCombinationSyntax As)
    {B : ℝ} (hbdd : ∀ n, (As n).l1Norm P ≤ B)
    (hwv : LUVCombination.WorldValued As DP) {c : ℝ} (hc : 0 ≤ c)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → (As n).value P ν ≤ c)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => c) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hval
  have hbs : LUVCombination.BoundedSequence (zeroPrefix N As) P :=
    ⟨(zeroPrefixSyntax S N).polySequence, ⟨B, fun n => by
      unfold zeroPrefix
      split_ifs with hn
      · rw [zeroed_l1Norm]
        exact ((As 0).l1Norm_nonneg P).trans (hbdd 0)
      · exact hbdd n⟩⟩
  have hwv' : LUVCombination.WorldValued (zeroPrefix N As) DP := fun n v hv => by
    obtain ⟨ν, hν⟩ := hwv n v hv
    refine ⟨ν, ?_⟩
    unfold zeroPrefix
    split_ifs
    · exact zeroed_valuesAt hν
    · exact hν
  have hval' : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (zeroPrefix N As n).ValuesAt v ν → (zeroPrefix N As n).value P ν ≤ c := by
    intro n v hv ν hν
    unfold zeroPrefix at hν ⊢
    split_ifs at hν ⊢ with hn
    · rw [zeroed_value]; exact hc
    · exact hN n (not_lt.1 hn) v hv ν hν
  have h := lic_expect_combination_provind_le hbs hwv' c hval' hworld
  intro ε hε
  filter_upwards [h ε hε, Filter.eventually_ge_atTop N] with n hn hnN
  rwa [zeroPrefix_of_le N As hnN] at hn

/-- **`thm:expprovind` (`≥` face) from an *eventual* world bound**, for a nonpositive bound `c`.
Source: none: infrastructure (mandate target 1c); FAF `lic_expect_combination_provind_ge`
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem expect_asympGE_of_eventually {As : ℕ → LUVCombination} (S : LUVCombinationSyntax As)
    {B : ℝ} (hbdd : ∀ n, (As n).l1Norm P ≤ B)
    (hwv : LUVCombination.WorldValued As DP) {c : ℝ} (hc : c ≤ 0)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → c ≤ (As n).value P ν)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => c) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hval
  have hbs : LUVCombination.BoundedSequence (zeroPrefix N As) P :=
    ⟨(zeroPrefixSyntax S N).polySequence, ⟨B, fun n => by
      unfold zeroPrefix
      split_ifs with hn
      · rw [zeroed_l1Norm]
        exact ((As 0).l1Norm_nonneg P).trans (hbdd 0)
      · exact hbdd n⟩⟩
  have hwv' : LUVCombination.WorldValued (zeroPrefix N As) DP := fun n v hv => by
    obtain ⟨ν, hν⟩ := hwv n v hv
    refine ⟨ν, ?_⟩
    unfold zeroPrefix
    split_ifs
    · exact zeroed_valuesAt hν
    · exact hν
  have hval' : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (zeroPrefix N As n).ValuesAt v ν → c ≤ (zeroPrefix N As n).value P ν := by
    intro n v hv ν hν
    unfold zeroPrefix at hν ⊢
    split_ifs at hν ⊢ with hn
    · rw [zeroed_value]; exact hc
    · exact hN n (not_lt.1 hn) v hv ν hν
  have h := lic_expect_combination_provind_ge hbs hwv' c hval' hworld
  intro ε hε
  filter_upwards [h ε hε, Filter.eventually_ge_atTop N] with n hn hnN
  rwa [zeroPrefix_of_le N As hnN] at hn

/-- **A combination whose world value is eventually within every `ε` of `0` has diagonal
expectation `≈ₙ 0`.** Both faces of the eventual `thm:expprovind` at `±ε/2`.
Source: none: infrastructure (mandate target 1c)
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem expect_asympEq_zero_of_eventually_abs_le {As : ℕ → LUVCombination}
    (S : LUVCombinationSyntax As) {B : ℝ} (hbdd : ∀ n, (As n).l1Norm P ≤ B)
    (hwv : LUVCombination.WorldValued As DP)
    (hval : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (As n).ValuesAt v ν → |(As n).value P ν| ≤ ε)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
  rw [asympEq_iff_asympLE_asympGE]
  constructor
  · intro ε hε
    have hle := expect_asympLE_of_eventually S hbdd hwv (c := ε / 2) (by positivity)
      (by
        filter_upwards [hval (ε / 2) (by positivity)] with n hn v hv ν hν
        exact (abs_le.1 (hn v hv ν hν)).2) hworld
    filter_upwards [hle (ε / 2) (by positivity)] with n hn
    linarith
  · intro ε hε
    have hge := expect_asympGE_of_eventually S hbdd hwv (c := -(ε / 2)) (by linarith)
      (by
        filter_upwards [hval (ε / 2) (by positivity)] with n hn v hv ν hν
        exact (abs_le.1 (hn v hv ν hν)).1) hworld
    filter_upwards [hge (ε / 2) (by positivity)] with n hn
    linarith

end

end Cleanroom.Deference.DefSelfTrust
