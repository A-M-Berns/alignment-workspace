import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert

/-!
# `def-squeeze-diamond` · GapMesh: the gap quote of an arbitrary e.c. valued source (target 4b's
general gap LUV; repair round 1)

The arrows' `GapQuote DP E Z Y a G` asks for an e.c. LUV `G` valued within a vanishing slack of
the rescaled signed gap `(a (z − E*(Z_n)) + 1)/2` whenever `Z n` is valued at `z`. `GapIndicator`
built it exactly for literal-indicator sources (`z ∈ {0,1}` is decided by a sentence, so the gap
is a two-way select between quoted rationals). For a **general** `[0,1]`-source the exact gap
would carry the threshold `⌜Z_n > 2r − 1 + E*(Z_n)⌝`, whose shift names the non-polynomial value
`E*(Z_n)` and is not emittable (FAF's own remark at `meshProductLUV`: "exact reflection is
unreachable"). The device here is a **mesh select over the source's own threshold sentences**:

* `meshSelectLUV B q n`, with threshold `⋁_{k < n+2} (B n k ⋏ ⌜u(n,k) > r⌝)` where the `B n k`
  are "bin" sentences and `u(n,k)` are quoted computable rationals (`RationalQuoteCode` at the
  paired index `⟨n, k⟩`). In a world that affirms at least one bin, it is valued at the
  **maximum** of the affirmed branch values (`meshSelectLUV_valuesAt`): FAF's `ValuesAt` leaves
  the threshold *at* the value undetermined, so a disjunction of `r < u_k` over the affirmed `k`
  is exactly `r < max u_k`. Its codes are FAF's `MachineSentenceCodes.bigOr` over the bin and
  quote streams (`meshSelectLUV_codes`), at the block interface, exactly as `meshProductLUV`'s.
* The branch value is the gap at the **grid point** `k/(n+1)` in place of `z`:
  `u(n,k) := (a (min(k, n+1)/(n+1) − e_n) + 1)/2` with `e_n := E*(Z_n)` as FAF's computable
  rational `expectQuoteAt` (`meshGapVal`, `meshGapCode`).
* **Positive sign** (`binPlus`): bin `0` is `⊤`, bin `k ≥ 1` is `⌜Z_n > k/(n+1)⌝`. The affirmed
  bins are `0` and the `k ≥ 1` with `k/(n+1) ≤ z` (and all with `k/(n+1) < z`), the branch value
  increases with `k`, so the max is the gap at the largest grid point below `z`:
  within `1/(n+1)` of the gap at `z` (`meshGapPlus_reflected`).
* **Negative sign** (`binMinus`): bin `n+1` is `⊤`, bin `k ≤ n` is `∼⌜Z_n > k/(n+1)⌝`. The
  affirmed bins are `n+1` and the `k` with `z ≤ k/(n+1)` (and all with `z < k/(n+1)`), the
  branch value decreases with `k`, so the max is the gap at the smallest grid point above `z`
  (`meshGapMinus_reflected`). This is the construction `1 − Z` cannot be made as a single
  threshold shift: a threshold presentation of `Z` gives `⌜Z > s⌝` and `∼⌜Z > s⌝`, so the
  complement enters only through the mesh of decided bins.

Consequences: `gapQuote_meshPlus`/`gapQuote_meshMinus` (the `GapQuote` of **every** e.c. valued
source for the self-expert, both signs, (a), slack `1/(n+1)`), which `SelfInstance.lean` turns
into `PinnedGapPackages` for the self-expert and `PinnedGapPackagesBase` for the paper expert
read by any extending novice. Construction-facing; single market (self) / one-way.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional

noncomputable section

/-! ## The mesh select -/

section MeshSelect

variable {T : ArithmeticTheory} {value : ℕ → ℚ}

/-- **The mesh select**: threshold `⋁_{k < n+2} (B n k ⋏ ⌜u(n,k) > r⌝)` between the quoted
rationals `u(n,k) := value ⟨n, k⟩` by the bin sentences `B n k`.
Source: mandate target 4b ("a mesh over the quoted expectation"); FAF `meshProductLUV` (the shape)
Kind: D
Fidelity: exact -/
def meshSelectLUV (B : ℕ → ℕ → Sentence) (q : RationalQuoteCode T value) (n : ℕ) : LUV where
  gt r := sentenceDisjunction ((List.range (n + 2)).map fun k =>
    B n k ⋏ (q.luv (Nat.pair n k)).gt r)

/-- A world holds the select's threshold iff some bin `k < n+2` holds together with the quoted
threshold of its branch.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem meshSelectLUV_holds_iff (B : ℕ → ℕ → Sentence) (q : RationalQuoteCode T value) (n : ℕ)
    (r : ℚ) (v : PCWorld) :
    v.Holds ((meshSelectLUV B q n).gt r) ↔
      ∃ k, k < n + 2 ∧ v.Holds (B n k) ∧ v.Holds ((q.luv (Nat.pair n k)).gt r) := by
  simp only [meshSelectLUV, holds_sentenceDisjunction, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨φ, ⟨k, hk, rfl⟩, h⟩
    exact ⟨k, hk, h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨_, ⟨k, hk, rfl⟩, h⟩

open Classical in
/-- **The mesh select is valued at the maximum of the affirmed branch values**: in a
completed-theory world that affirms some bin, the select is valued at `g := max {u(n,k) : B n k
holds}` — every affirmed branch value is `≤ g` and `g` is one of them.
Source: none: infrastructure (FAF `RationalQuoteCode.reflected`; `ValuesAt` leaves the
threshold at the value undetermined)
Kind: L
Fidelity: n/a -/
theorem meshSelectLUV_valuesAt {DP : DeductiveProcess} (Q : QuotationTheoryPresentation DP T)
    (B : ℕ → ℕ → Sentence) (q : RationalQuoteCode T value) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) (hne : ∃ k, k < n + 2 ∧ v.Holds (B n k)) :
    ∃ g : ℝ, v.ValuesAt (meshSelectLUV B q n) g ∧
      (∀ k, k < n + 2 → v.Holds (B n k) → ((value (Nat.pair n k) : ℚ) : ℝ) ≤ g) ∧
      (∃ k, k < n + 2 ∧ v.Holds (B n k) ∧ g = ((value (Nat.pair n k) : ℚ) : ℝ)) := by
  set S : Finset ℕ := (Finset.range (n + 2)).filter (fun k => v.Holds (B n k)) with hS
  have hmem : ∀ k, k ∈ S ↔ k < n + 2 ∧ v.Holds (B n k) := by
    intro k
    simp [hS, Finset.mem_filter, Finset.mem_range]
  have hSne : S.Nonempty := by
    obtain ⟨k, hk, hB⟩ := hne
    exact ⟨k, (hmem k).2 ⟨hk, hB⟩⟩
  set u : ℕ → ℝ := fun k => ((value (Nat.pair n k) : ℚ) : ℝ) with hu
  obtain ⟨k₀, hk₀, hsup⟩ := Finset.exists_mem_eq_sup' hSne u
  refine ⟨S.sup' hSne u, ⟨?_, ?_, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩, ?_, ?_⟩
  · rw [hsup]
    show (0 : ℝ) ≤ ((value (Nat.pair n k₀) : ℚ) : ℝ)
    exact_mod_cast (q.value_mem _).1
  · rw [Finset.sup'_le_iff]
    intro k _
    show ((value (Nat.pair n k) : ℚ) : ℝ) ≤ 1
    exact_mod_cast (q.value_mem _).2
  · rw [Finset.lt_sup'_iff] at hr
    obtain ⟨k, hk, hrk⟩ := hr
    rw [hmem] at hk
    rw [meshSelectLUV_holds_iff]
    exact ⟨k, hk.1, hk.2, ((RationalQuoteCode.reflected Q q (Nat.pair n k) v hv).2.2 r).1 hrk⟩
  · intro hcon
    rw [meshSelectLUV_holds_iff] at hcon
    obtain ⟨k, hk, hB, hq⟩ := hcon
    have hle : u k ≤ S.sup' hSne u := Finset.le_sup' u ((hmem k).2 ⟨hk, hB⟩)
    exact ((RationalQuoteCode.reflected Q q (Nat.pair n k) v hv).2.2 r).2
      (lt_of_le_of_lt hle hr) hq
  · intro k hk hB
    exact Finset.le_sup' u ((hmem k).2 ⟨hk, hB⟩)
  · exact ⟨k₀, ((hmem k₀).1 hk₀).1, ((hmem k₀).1 hk₀).2, hsup⟩

/-- **The mesh select is e.c.** when the bin family is (as a family of the paired index
`⟨⟨n, ⟨k', i'⟩⟩, k⟩`) — FAF's `MachineSentenceCodes.bigOr` over the `⋏`-shell of the bin stream
and the quote's own threshold stream, with the variable width `n + 2` as a ruler.
Source: none: infrastructure (FAF `meshProductLUV_machineThresholdCodeSeq`, the same shape)
Kind: L
Fidelity: n/a -/
theorem meshSelectLUV_codes {B : ℕ → ℕ → Sentence}
    (hB : MachineSentenceCodes (fun z : ℕ => B z.unpair.1.unpair.1 z.unpair.2))
    (q : RationalQuoteCode T value) : LUV.MachineThresholdCodeSeq (meshSelectLUV B q) := by
  have hn : UnaryRuler (fun z : ℕ => z.unpair.1.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairFst
  have hk : UnaryRuler (fun z : ℕ => z.unpair.1.unpair.2.unpair.1) :=
    UnaryRuler.unpairFst.comp (UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst)
  have hi : UnaryRuler (fun z : ℕ => z.unpair.1.unpair.2.unpair.2) :=
    UnaryRuler.unpairSnd.comp (UnaryRuler.unpairSnd.comp UnaryRuler.unpairFst)
  have hj : UnaryRuler (fun z : ℕ => z.unpair.2) := UnaryRuler.unpairSnd
  have hquote : MachineSentenceCodes (fun z : ℕ =>
      (q.luv (Nat.pair z.unpair.1.unpair.1 z.unpair.2)).gt
        ((z.unpair.1.unpair.2.unpair.2 : ℚ) / (z.unpair.1.unpair.2.unpair.1 : ℚ))) :=
    (MachineSentenceCodes.comp q.poly ((hn.pair hj).pair (hk.pair hi))).of_eq
      (fun z => by simp)
  have hcnt : UnaryRuler (fun m : ℕ => m.unpair.1 + 2) :=
    UnaryRuler.unpairFst.add (UnaryRuler.const 2)
  unfold LUV.MachineThresholdCodeSeq
  exact (MachineSentenceCodes.bigOr (D := fun m j =>
      B m.unpair.1 j ⋏ (q.luv (Nat.pair m.unpair.1 j)).gt
        ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
    (MachineSentenceCodes.and hB hquote) hcnt).of_eq (fun m => rfl)

end MeshSelect

/-! ## The branch values: the gap at a grid point, with FAF's computable deferred expectation -/

section Branches

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The self-expert's deferred-day expectation `E*(Z_n) = E_{f n}(Z_n)` as FAF's exact
computable rational `expectQuoteAt Z n (f n)`.
Source: none: infrastructure (FAF `MarketComputation.expectQuoteAt`)
Kind: D
Fidelity: exact -/
def deferredExpectSeq (f : DeferralFunction) (Z : ℕ → LUV) (n : ℕ) : ℚ :=
  (paperMarketComputation T).expectQuoteAt Z n (f.f n)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The deferred expectation sequence of an e.c. family is computable.
Source: none: infrastructure (FAF `expectQuoteAt_computable`, `DeferralFunction.computable`)
Kind: L
Fidelity: n/a -/
theorem deferredExpectSeq_computable (f : DeferralFunction) {Z : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) : Computable (deferredExpectSeq T f Z) :=
  -- the `( … : _)` ascription is load-bearing (FAF `paperDeferredExpectationQuoteCode`)
  have hcomp : Computable fun n =>
      (paperMarketComputation T).expectQuoteAt Z n (f.f n) :=
    (((paperMarketComputation T).expectQuoteAt_computable hZ).comp
      (Computable.id.pair f.computable) : _)
  hcomp

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The deferred expectation sequence lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem deferredExpectSeq_mem (f : DeferralFunction) (Z : ℕ → LUV) (n : ℕ) :
    0 ≤ deferredExpectSeq T f Z n ∧ deferredExpectSeq T f Z n ≤ 1 :=
  (paperMarketComputation T).expectQuoteAt_mem_Icc Z n (f.f n)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- As a real, the deferred expectation sequence is the self-expert's estimate.
Source: none: infrastructure (FAF `expectQuoteAt_cast`)
Kind: L
Fidelity: n/a -/
theorem deferredExpectSeq_cast (f : DeferralFunction) (Z : ℕ → LUV) (n : ℕ) :
    ((deferredExpectSeq T f Z n : ℚ) : ℝ) =
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n := by
  rw [Expert.self_estimate]
  exact ((paperMarketComputation T).expectQuoteAt_cast Z n (f.f n)).symm

end Branches

/-- The grid point `min(k, n+1)/(n+1)` at the paired index `⟨n, k⟩` (clipped at `1` so that the
value is in `[0,1]` at every index).
Source: mandate target 4b (the mesh)
Kind: D
Fidelity: exact -/
def gridPoint (m : ℕ) : ℚ :=
  min (m.unpair.2 : ℚ) ((m.unpair.1 + 1 : ℕ) : ℚ) / ((m.unpair.1 + 1 : ℕ) : ℚ)

/-- The grid point is computable.
Source: none: infrastructure (FAF `ratNatCast_prim`, `ratMin_prim`, `ratDiv_prim`)
Kind: L
Fidelity: n/a -/
theorem gridPoint_computable : Computable gridPoint := by
  have hk : Computable fun m : ℕ => (m.unpair.2 : ℚ) :=
    (ratNatCast_prim.comp (Primrec.snd.comp Primrec.unpair)).to_comp
  have hN : Computable fun m : ℕ => ((m.unpair.1 + 1 : ℕ) : ℚ) :=
    (ratNatCast_prim.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))).to_comp
  have hmin : Computable fun m : ℕ => min (m.unpair.2 : ℚ) ((m.unpair.1 + 1 : ℕ) : ℚ) :=
    (ratMin_prim.to_comp.comp hk hN : _)
  exact (ratDiv_prim.to_comp.comp hmin hN : _)

/-- The grid point lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gridPoint_mem (m : ℕ) : 0 ≤ gridPoint m ∧ gridPoint m ≤ 1 := by
  unfold gridPoint
  have hN : (0 : ℚ) < ((m.unpair.1 + 1 : ℕ) : ℚ) := by positivity
  constructor
  · exact div_nonneg (le_min (Nat.cast_nonneg _) hN.le) hN.le
  · rw [div_le_one hN]
    exact min_le_right _ _

/-- **The branch value**: the rescaled signed gap at the grid point in place of the source's
value, `(a (min(k, n+1)/(n+1) − e_n) + 1)/2`, at the paired index `⟨n, k⟩`.
Source: mandate target 4b (the gap LUV); `def-lattice-arrows` `gapValue`
Kind: D
Fidelity: exact -/
def meshGapVal (a : ℚ) (e : ℕ → ℚ) (m : ℕ) : ℚ := (a * (gridPoint m - e m.unpair.1) + 1) / 2

/-- The branch value is computable when `e` is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem meshGapVal_computable (a : ℚ) {e : ℕ → ℚ} (he : Computable e) :
    Computable (meshGapVal a e) := by
  have he' : Computable fun m : ℕ => e m.unpair.1 :=
    he.comp (Primrec.fst.comp Primrec.unpair).to_comp
  have h1 : Computable fun m : ℕ => gridPoint m - e m.unpair.1 :=
    (ratSub_prim.to_comp.comp gridPoint_computable he' : _)
  have h2 : Computable fun m : ℕ => a * (gridPoint m - e m.unpair.1) :=
    (ratMul_prim.to_comp.comp (Computable.const a) h1 : _)
  have h3 : Computable fun m : ℕ => a * (gridPoint m - e m.unpair.1) + 1 :=
    (ratAdd_prim.to_comp.comp h2 (Computable.const 1) : _)
  exact (ratDiv_prim.to_comp.comp h3 (Computable.const 2) : _)

/-- For `a = ±1` and `e ∈ [0,1]`, the branch value lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem meshGapVal_mem {a : ℚ} (ha : a = 1 ∨ a = -1) {e : ℕ → ℚ}
    (he : ∀ n, 0 ≤ e n ∧ e n ≤ 1) (m : ℕ) : 0 ≤ meshGapVal a e m ∧ meshGapVal a e m ≤ 1 := by
  have h1 := he m.unpair.1
  have h2 := gridPoint_mem m
  unfold meshGapVal
  rcases ha with rfl | rfl <;> constructor <;> linarith

/-- The branch value at `⟨n, k⟩`, as a real.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem meshGapVal_pair_cast (a : ℚ) (e : ℕ → ℚ) (n k : ℕ) :
    ((meshGapVal a e (Nat.pair n k) : ℚ) : ℝ) =
      ((a : ℝ) * (min (k : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) - (e n : ℝ)) + 1) / 2 := by
  simp only [meshGapVal, gridPoint, Nat.unpair_pair]
  push_cast
  ring

/-! ## The bins -/

/-- **The positive bins**: bin `0` is `⊤`, bin `k ≥ 1` is `⌜Z_n > k/(n+1)⌝`.
Source: mandate target 4b (the mesh)
Kind: D
Fidelity: exact -/
def binPlus (Z : ℕ → LUV) (n k : ℕ) : Sentence :=
  if k = 0 then ⊤ else (Z n).gt ((k : ℚ) / ((n + 1 : ℕ) : ℚ))

/-- **The negative bins**: bin `n+1` is `⊤`, bin `k ≤ n` is `∼⌜Z_n > k/(n+1)⌝`.
Source: mandate target 4b (the mesh; "its mirror with the negated atoms")
Kind: D
Fidelity: exact -/
def binMinus (Z : ℕ → LUV) (n k : ℕ) : Sentence :=
  if (n + 1) - k = 0 then ⊤ else ∼((Z n).gt ((k : ℚ) / ((n + 1 : ℕ) : ℚ)))

/-- The positive bins are e.c. as a family of the paired index (`ifZero` on the branch index,
the source's threshold stream read at `⟨n, ⟨n+1, k⟩⟩`).
Source: none: infrastructure (FAF `MachineSentenceCodes.ifZero`/`.comp`)
Kind: L
Fidelity: n/a -/
theorem binPlus_codes {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) :
    MachineSentenceCodes (fun z : ℕ => binPlus Z z.unpair.1.unpair.1 z.unpair.2) := by
  have hn : UnaryRuler (fun z : ℕ => z.unpair.1.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairFst
  have hj : UnaryRuler (fun z : ℕ => z.unpair.2) := UnaryRuler.unpairSnd
  have hgt : MachineSentenceCodes (fun z : ℕ => (Z z.unpair.1.unpair.1).gt
      ((z.unpair.2 : ℚ) / ((z.unpair.1.unpair.1 + 1 : ℕ) : ℚ))) :=
    (MachineSentenceCodes.comp hZ (hn.pair (hn.succ.pair hj))).of_eq (fun z => by simp)
  exact (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (⊤ : Sentence)) hgt hj).of_eq
    (fun z => rfl)

/-- The negative bins are e.c. as a family of the paired index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem binMinus_codes {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) :
    MachineSentenceCodes (fun z : ℕ => binMinus Z z.unpair.1.unpair.1 z.unpair.2) := by
  have hn : UnaryRuler (fun z : ℕ => z.unpair.1.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairFst
  have hj : UnaryRuler (fun z : ℕ => z.unpair.2) := UnaryRuler.unpairSnd
  have hgt : MachineSentenceCodes (fun z : ℕ => (Z z.unpair.1.unpair.1).gt
      ((z.unpair.2 : ℚ) / ((z.unpair.1.unpair.1 + 1 : ℕ) : ℚ))) :=
    (MachineSentenceCodes.comp hZ (hn.pair (hn.succ.pair hj))).of_eq (fun z => by simp)
  exact (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (⊤ : Sentence)) hgt.neg
    (hn.succ.sub hj)).of_eq (fun z => rfl)

/-! ## The two grid lemmas (pure real arithmetic) -/

/-- Below every `z ∈ [0,1]` there is a grid point of the positive mesh within `1/(n+1)`: `k = 0`
(the `⊤` bin) when `z ≤ 1/(n+1)`, else `k = ⌈z(n+1)⌉ − 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_grid_below (n : ℕ) {z : ℝ} (hz1 : z ≤ 1) :
    ∃ k, k < n + 2 ∧ (k = 0 ∨ (k : ℝ) / ((n : ℝ) + 1) < z) ∧
      z - 1 / ((n : ℝ) + 1) ≤ min (k : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases h : z * ((n : ℝ) + 1) ≤ 1
  · refine ⟨0, by omega, Or.inl rfl, ?_⟩
    rw [Nat.cast_zero, min_eq_left hNpos.le, _root_.zero_div, sub_nonpos, le_div_iff₀ hNpos]
    exact h
  · push Not at h
    set c : ℕ := ⌈z * ((n : ℝ) + 1)⌉₊ with hc
    have h1c : 1 < c := Nat.lt_ceil.mpr (by push_cast; exact h)
    have hcle : c ≤ n + 1 := Nat.ceil_le.mpr (by
      push_cast
      nlinarith)
    have hclt : ((c - 1 : ℕ) : ℝ) < z * ((n : ℝ) + 1) :=
      Nat.lt_ceil.mp (Nat.sub_lt (by omega) one_pos)
    have hcge : z * ((n : ℝ) + 1) ≤ (c : ℝ) := Nat.le_ceil _
    have hcast : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    refine ⟨c - 1, by omega, Or.inr ?_, ?_⟩
    · rw [div_lt_iff₀ hNpos]
      exact hclt
    · have hle : ((c - 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        rw [hcast]
        have : (c : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcle
        linarith
      rw [min_eq_left hle, hcast, le_div_iff₀ hNpos]
      have : z * ((n : ℝ) + 1) - 1 ≤ (c : ℝ) - 1 := by linarith
      calc (z - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = z * ((n : ℝ) + 1) - 1 := by
            field_simp
        _ ≤ (c : ℝ) - 1 := this

/-- Above every `z ∈ [0,1]` there is a grid point of the negative mesh within `1/(n+1)`:
`k = n+1` (the `⊤` bin) when `z ≥ n/(n+1)`, else `k = ⌊z(n+1)⌋ + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_grid_above (n : ℕ) {z : ℝ} (hz0 : 0 ≤ z) :
    ∃ k, k < n + 2 ∧ (k = n + 1 ∨ z < (k : ℝ) / ((n : ℝ) + 1)) ∧
      min (k : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) ≤ z + 1 / ((n : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  by_cases h : (n : ℝ) ≤ z * ((n : ℝ) + 1)
  · refine ⟨n + 1, by omega, Or.inl rfl, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, min_self, div_self hNpos.ne', ← sub_le_iff_le_add]
    have key : 1 - 1 / ((n : ℝ) + 1) = (n : ℝ) / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [key, div_le_iff₀ hNpos]
    exact h
  · push Not at h
    set c : ℕ := ⌊z * ((n : ℝ) + 1)⌋₊ with hc
    have hz0' : 0 ≤ z * ((n : ℝ) + 1) := by positivity
    have hcn : c < n := (Nat.floor_lt hz0').mpr h
    have hlt : z * ((n : ℝ) + 1) < (c : ℝ) + 1 := Nat.lt_floor_add_one _
    have hle : (c : ℝ) ≤ z * ((n : ℝ) + 1) := Nat.floor_le hz0'
    refine ⟨c + 1, by omega, Or.inr ?_, ?_⟩
    · rw [lt_div_iff₀ hNpos]
      push_cast
      exact hlt
    · have hle' : ((c + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        have : ((c + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcn
        linarith
      rw [min_eq_left hle', div_le_iff₀ hNpos]
      push_cast
      calc (c : ℝ) + 1 ≤ z * ((n : ℝ) + 1) + 1 := by linarith
        _ = (z + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by field_simp

/-! ## The mesh gap LUVs and their gap quotes, for the self-expert -/

section Gap

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- FAF's quote code of the branch values `(a (min(k, n+1)/(n+1) − E*(Z_n)) + 1)/2` at the
paired index `⟨n, k⟩`, along the deferral `f`.
Source: mandate target 4b; FAF `RationalQuoteCode.ofComputable`
Kind: D
Fidelity: exact -/
def meshGapCode (f : DeferralFunction) {a : ℚ} (ha : a = 1 ∨ a = -1) {Z : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) :
    RationalQuoteCode T (meshGapVal a (deferredExpectSeq T f Z)) :=
  RationalQuoteCode.ofComputable T (meshGapVal_computable a (deferredExpectSeq_computable T f hZ))
    (meshGapVal_mem ha (deferredExpectSeq_mem T f Z))

/-- **The positive mesh gap LUV** of an e.c. source: the mesh select over the positive bins.
Source: mandate target 4b (the gap LUV `(Z − ⌜E*(Z)⌝ + 1)/2`, within slack)
Kind: D
Fidelity: variant: within `1/(n+1)` (the mesh) -/
def meshGapPlus (f : DeferralFunction) {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) :
    ℕ → LUV :=
  meshSelectLUV (binPlus Z) (meshGapCode T f (Or.inl rfl) hZ)

/-- **The negative mesh gap LUV** of an e.c. source: the mesh select over the negative bins.
Source: mandate target 4b (the gap LUV `(⌜E*(Z)⌝ − Z + 1)/2`, within slack)
Kind: D
Fidelity: variant: within `1/(n+1)` (the mesh) -/
def meshGapMinus (f : DeferralFunction) {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) :
    ℕ → LUV :=
  meshSelectLUV (binMinus Z) (meshGapCode T f (Or.inr rfl) hZ)

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The threshold `k/(n+1)` of a bin, as a real.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bin_threshold_cast (n k : ℕ) :
    (((k : ℚ) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) = (k : ℝ) / ((n : ℝ) + 1) := by
  push_cast
  ring

omit [Entailment.Consistent T] in
/-- **The positive mesh gap is valued within `1/(n+1)` of the gap** in every completed-theory
world where the source is valued: the affirmed bins are `0` and the `k ≥ 1` with
`k/(n+1) ≤ z`, every branch value is at most the gap at `z`, and the grid point below `z`
(`exists_grid_below`) gives a branch value within `1/(n+1)` of it.
Source: mandate target 4b; [[total-trust-implies-mart]] §Proof (the gap bet `D_n`)
Kind: C
Fidelity: variant: within `1/(n+1)`
Hyps: (a) -/
theorem meshGapPlus_reflected (f : DeferralFunction) {Z : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) {z : ℝ} (hz : v.ValuesAt (Z n) z) :
    ∃ g, v.ValuesAt (meshGapPlus T f hZ n) g ∧
      |g - gapValue 1 z ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n)| ≤
        1 / ((n : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2.1
  have hecast : ((deferredExpectSeq T f Z n : ℚ) : ℝ) =
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n :=
    deferredExpectSeq_cast T f Z n
  set e : ℝ := (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n with he
  have hval : ∀ k, ((meshGapVal 1 (deferredExpectSeq T f Z) (Nat.pair n k) : ℚ) : ℝ) =
      (min (k : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) - e + 1) / 2 := by
    intro k
    rw [meshGapVal_pair_cast, hecast]
    push_cast
    ring
  have hbin0 : v.Holds (binPlus Z n 0) := by
    simp [binPlus, PCWorld.holds_top]
  have hbin_le : ∀ k, k ≠ 0 → v.Holds (binPlus Z n k) → (k : ℝ) / ((n : ℝ) + 1) ≤ z := by
    intro k hk hB
    simp only [binPlus, if_neg hk] at hB
    by_contra hcon
    push Not at hcon
    exact (hz.2.2 _).2 (by rw [bin_threshold_cast]; exact hcon) hB
  have hbin_of : ∀ k : ℕ, (k : ℝ) / ((n : ℝ) + 1) < z → v.Holds (binPlus Z n k) := by
    intro k hlt
    by_cases hk : k = 0
    · subst hk
      exact hbin0
    · simp only [binPlus, if_neg hk]
      exact (hz.2.2 _).1 (by rw [bin_threshold_cast]; exact hlt)
  obtain ⟨g, hg, hupper, k₀, hk₀, hB₀, hg₀⟩ :=
    meshSelectLUV_valuesAt (paperQuotationPresentation T) (binPlus Z)
      (meshGapCode T f (Or.inl rfl) hZ) n v hv ⟨0, by omega, hbin0⟩
  refine ⟨g, hg, abs_le.mpr ⟨?_, ?_⟩⟩
  · -- the lower bound: the grid point below `z`
    obtain ⟨k, hk, hkB, hkge⟩ := exists_grid_below n hz1
    have hB : v.Holds (binPlus Z n k) := by
      rcases hkB with rfl | hlt
      · exact hbin0
      · exact hbin_of k hlt
    have h1 := hupper k hk hB
    rw [hval k] at h1
    have h1N : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [gapValue, Rat.cast_one, one_mul]
    linarith
  · -- the upper bound: every affirmed branch value is at most the gap at `z`
    rw [hg₀, hval k₀]
    simp only [gapValue, Rat.cast_one, one_mul]
    have h1N : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_cases hk : k₀ = 0
    · subst hk
      rw [Nat.cast_zero, min_eq_left hNpos.le, _root_.zero_div]
      linarith
    · have hle := hbin_le k₀ hk hB₀
      have hmin : min (k₀ : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) ≤ (k₀ : ℝ) / ((n : ℝ) + 1) :=
        (div_le_div_iff_of_pos_right hNpos).mpr (min_le_left _ _)
      linarith

omit [Entailment.Consistent T] in
/-- **The negative mesh gap is valued within `1/(n+1)` of the gap** in every completed-theory
world where the source is valued: the affirmed bins are `n+1` and the `k ≤ n` with
`z ≤ k/(n+1)`, every branch value is at most the gap at `z`, and the grid point above `z`
(`exists_grid_above`) gives a branch value within `1/(n+1)` of it.
Source: mandate target 4b; [[total-trust-implies-mart]] §Proof (the gap bet `D_n`, negative sign)
Kind: C
Fidelity: variant: within `1/(n+1)`
Hyps: (a) -/
theorem meshGapMinus_reflected (f : DeferralFunction) {Z : ℕ → LUV}
    (hZ : LUV.MachineThresholdCodeSeq Z) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) {z : ℝ} (hz : v.ValuesAt (Z n) z) :
    ∃ g, v.ValuesAt (meshGapMinus T f hZ n) g ∧
      |g - gapValue (-1) z ((Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n)| ≤
        1 / ((n : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2.1
  have hecast : ((deferredExpectSeq T f Z n : ℚ) : ℝ) =
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n :=
    deferredExpectSeq_cast T f Z n
  set e : ℝ := (Expert.self (liaHistory (paperDP T)) (paperDP T) f).estimate Z n with he
  have hval : ∀ k, ((meshGapVal (-1) (deferredExpectSeq T f Z) (Nat.pair n k) : ℚ) : ℝ) =
      (e - min (k : ℝ) ((n : ℝ) + 1) / ((n : ℝ) + 1) + 1) / 2 := by
    intro k
    rw [meshGapVal_pair_cast, hecast]
    push_cast
    ring
  have hbin_top : v.Holds (binMinus Z n (n + 1)) := by
    simp [binMinus, PCWorld.holds_top]
  have hbin_ge : ∀ k, (n + 1) - k ≠ 0 → v.Holds (binMinus Z n k) →
      z ≤ (k : ℝ) / ((n : ℝ) + 1) := by
    intro k hk hB
    simp only [binMinus, if_neg hk, PCWorld.holds_neg] at hB
    by_contra hcon
    push Not at hcon
    exact hB ((hz.2.2 _).1 (by rw [bin_threshold_cast]; exact hcon))
  have hbin_of : ∀ k : ℕ, z < (k : ℝ) / ((n : ℝ) + 1) → v.Holds (binMinus Z n k) := by
    intro k hlt
    by_cases hk : (n + 1) - k = 0
    · simp only [binMinus, if_pos hk]
      exact PCWorld.holds_top v
    · simp only [binMinus, if_neg hk, PCWorld.holds_neg]
      exact (hz.2.2 _).2 (by rw [bin_threshold_cast]; exact hlt)
  obtain ⟨g, hg, hupper, k₀, hk₀, hB₀, hg₀⟩ :=
    meshSelectLUV_valuesAt (paperQuotationPresentation T) (binMinus Z)
      (meshGapCode T f (Or.inr rfl) hZ) n v hv ⟨n + 1, by omega, hbin_top⟩
  refine ⟨g, hg, abs_le.mpr ⟨?_, ?_⟩⟩
  · -- the lower bound: the grid point above `z`
    obtain ⟨k, hk, hkB, hkle⟩ := exists_grid_above n hz0
    have hB : v.Holds (binMinus Z n k) := by
      rcases hkB with rfl | hlt
      · exact hbin_top
      · exact hbin_of k hlt
    have h1 := hupper k hk hB
    rw [hval k] at h1
    have h1N : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [gapValue, Rat.cast_neg, Rat.cast_one, neg_one_mul]
    linarith
  · -- the upper bound: every affirmed branch value is at most the gap at `z`
    rw [hg₀, hval k₀]
    simp only [gapValue, Rat.cast_neg, Rat.cast_one, neg_one_mul]
    have h1N : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_cases hk : (n + 1) - k₀ = 0
    · have hk' : (n : ℝ) + 1 ≤ (k₀ : ℝ) := by
        have : n + 1 ≤ k₀ := by omega
        exact_mod_cast this
      rw [min_eq_right hk', div_self hNpos.ne']
      linarith
    · have hge := hbin_ge k₀ hk hB₀
      have hk' : (k₀ : ℝ) ≤ (n : ℝ) + 1 := by
        have : k₀ ≤ n + 1 := by omega
        exact_mod_cast this
      rw [min_eq_left hk']
      linarith

/-- **The gap quote of every e.c. valued source, for the self-expert, positive sign** (target
4b's gap package on the whole e.c. class, (a)): `meshGapPlus` is e.c. (`meshSelectLUV_codes`),
valued within `1/(n+1)` of `gapValue 1 z (E*(Z_n))` in every completed-theory world
(`meshGapPlus_reflected`), with FAF's closed quote as `Y`.
Source: mandate target 4b ("the gap LUV … build it; this is the one new construction");
[[total-trust-implies-mart]] §Proof (the gap bet `D_n`)
Kind: C
Fidelity: variant: within `1/(n+1)` (`slack n = 1/(n+1)`, the general class)
Hyps: (a); `hZv : Valued (paperDP T) Z` (the package's own premise) -/
def gapQuote_meshPlus (f : DeferralFunction) {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z)
    (hZv : Valued (paperDP T) Z) :
    GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z
      ((paperDeferredExpectationQuoteCode T f Z hZ).luv) 1 (meshGapPlus T f hZ) where
  codes := meshSelectLUV_codes (binPlus_codes hZ) _
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  source_valued := hZv
  reflects := closedQuote_reflects T f Z hZ
  gap_reflected := fun n v hv _ hz => meshGapPlus_reflected T f hZ n v hv hz

/-- **The gap quote of every e.c. valued source, for the self-expert, negative sign** (a).
Source: mandate target 4b; [[total-trust-implies-mart]] §Proof
Kind: C
Fidelity: variant: within `1/(n+1)` (the general class)
Hyps: (a); `hZv` -/
def gapQuote_meshMinus (f : DeferralFunction) {Z : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z)
    (hZv : Valued (paperDP T) Z) :
    GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z
      ((paperDeferredExpectationQuoteCode T f Z hZ).luv) (-1) (meshGapMinus T f hZ) where
  codes := meshSelectLUV_codes (binMinus_codes hZ) _
  slack := fun n => 1 / ((n : ℝ) + 1)
  slack_tendsto := tendsto_one_div_add_atTop_nhds_zero_nat
  source_valued := hZv
  reflects := closedQuote_reflects T f Z hZ
  gap_reflected := fun n v hv _ hz => meshGapMinus_reflected T f hZ n v hv hz

end Gap

end

end Cleanroom.Deference.DefSqueezeDiamond
