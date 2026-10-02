import Cleanroom.Deference.DefTrackingPin.Witnesses

/-!
# Audit round 3 (adversarial) probe: `pinning_unpair`'s conclusion needs no `hz`

The T1 ledger row grades `pinning_unpair` N+ "for the statement as written" because its target
`1/(unpair₂ n + 1)` has no limit, "so `hz` is load-bearing — `pinning_ofTendsto` does not apply".
This probe proves the same conclusion with **no generability hypothesis**, through the package's
own one-sided T3 forms `pinning_asympLE` / `pinning_asympGE` and the padding trick of
`deferred_diagonal_subsequence`: the oscillating target is constant on each e.c. piece
`{n | unpair₂ n = c}`, and on the tail `{n | C ≤ unpair₂ n}` it is at most `1/(C+1)`, so for every
`ε` finitely many padded families (one per piece `c < C`, one for the tail) give the two-sided
bound. So on this witness `hz` is idle in exactly the sense the package used to grade
`deferred_tracking_constLookahead` N− (its `_hzFree` twin): the T1 route is the only *shipped*
route to the witness's conclusion, not the only route. Not imported by the library.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- Pad item `j`'s ledger family with FAF's indicator `𝟙(ψ)` off the piece `{n | t n = 0}`. -/
def piecePad (j : ℕ) (t : ℕ → ℕ) (ψ : Sentence) (n : ℕ) : LUV :=
  if t n = 0 then ledgerLuv j n else LUV.indicatorOf ψ

/-- The padded family is e.c. when the piece test is a ruler (`MachineSentenceCodes.ifZero` on the
paired index, exactly as `columnPad_thresholdCodes`). -/
theorem piecePad_thresholdCodes (j : ℕ) {t : ℕ → ℕ} (ht : UnaryRuler t) (ψ : Sentence) :
    LUV.MachineThresholdCodeSeq (piecePad j t ψ) := by
  have ht' : UnaryRuler (fun m : ℕ => t m.unpair.1) := ht.comp UnaryRuler.unpairFst
  have hA : MachineSentenceCodes (fun m : ℕ => (ledgerLuv j m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    ledgerLuv_thresholdCodes j
  have hB : MachineSentenceCodes (fun m : ℕ => (LUV.indicatorOf ψ).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    LUV.indicatorOf_machineThresholdCodeSeq (MachineSentenceCodes.const ψ)
  show MachineSentenceCodes (fun m => (piecePad j t ψ m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  refine (MachineSentenceCodes.ifZero hA hB ht').of_eq (fun m => ?_)
  by_cases h : t m.unpair.1 = 0
  · simp [piecePad, h]
  · simp [piecePad, h]

/-- The padded family over the oscillating ledger is settled: at the table on the piece, at the
indicator's value `y` off it. -/
theorem piecePad_determined (j : ℕ) (t : ℕ → ℕ) (ψ : Sentence) (y : ℝ)
    (hψ : ∀ w : PCWorld, w.ConsistentWithTheory unpairProcess →
      w.ValuesAt (LUV.indicatorOf ψ) y) (n : ℕ) :
    LUV.DeterminedVia (piecePad j t ψ n) unpairProcess
      (if t n = 0 then (unpairTable j n : ℝ) else y) := by
  intro w hw
  by_cases h : t n = 0
  · simp only [piecePad, if_pos h]
    exact ledgerLuv_determinedVia (paperDP 𝗜𝚺₁) unpairTable (fun _ => PublicationSchedule.succ)
      unpairTable_mem j n w hw
  · simp only [piecePad, if_neg h]
    exact hψ w hw

/-- The piece test `unpair₂ n = c`, as a ruler vanishing exactly on the piece. -/
def pieceEq (c n : ℕ) : ℕ := (n.unpair.2 - c) + (c - n.unpair.2)

theorem pieceEq_ruler (c : ℕ) : UnaryRuler (pieceEq c) :=
  ((UnaryRuler.unpairSnd.sub (UnaryRuler.const c)).add
    ((UnaryRuler.const c).sub UnaryRuler.unpairSnd)).of_eq fun _ => rfl

theorem pieceEq_eq_zero {c n : ℕ} : pieceEq c n = 0 ↔ n.unpair.2 = c := by
  unfold pieceEq; omega

/-- The tail test `C ≤ unpair₂ n`, as a ruler vanishing exactly on the tail. -/
def pieceGE (C n : ℕ) : ℕ := C - n.unpair.2

theorem pieceGE_ruler (C : ℕ) : UnaryRuler (pieceGE C) :=
  ((UnaryRuler.const C).sub UnaryRuler.unpairSnd).of_eq fun _ => rfl

theorem pieceGE_eq_zero {C n : ℕ} : pieceGE C n = 0 ↔ C ≤ n.unpair.2 := by
  unfold pieceGE; omega

theorem unpairTable_piece (j : ℕ) {c n : ℕ} (h : n.unpair.2 = c) :
    (unpairTable j n : ℝ) = 1 / ((c : ℝ) + 1) := by
  simp [unpairTable, h]

theorem unpairTable_tail (j : ℕ) {C n : ℕ} (h : C ≤ n.unpair.2) :
    (unpairTable j n : ℝ) ≤ 1 / ((C : ℝ) + 1) := by
  have h' : (C : ℝ) + 1 ≤ (n.unpair.2 : ℝ) + 1 := by
    have : (C : ℝ) ≤ n.unpair.2 := by exact_mod_cast h
    linarith
  rw [unpairTable]
  push_cast
  exact one_div_le_one_div_of_le (by positivity) h'

/-- **`pinning_unpair` with no `hz`**: FAF's LIA over the oscillating ledger tracks the table
`1/(unpair₂ n + 1)` through the one-sided T3 forms alone. -/
theorem pinning_unpair_hzFree (j : ℕ) :
    (fun n => (ledgerLuv j n).expect (liaHistory unpairProcess) n) ≈ₙ
      (fun n => (unpairTable j n : ℝ)) := by
  haveI := unpair_inductor
  set P := liaHistory unpairProcess with hPdef
  have hworld := ledgerProcess_paperDP_hworld 𝗜𝚺₁ unpairTable (fun _ => PublicationSchedule.succ)
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 := fun n s =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := unpairProcess) n s
  have hexp : ∀ n, 0 ≤ (ledgerLuv j n).expect P n := fun n =>
    ((ledgerLuv j n).expect_mem_Icc P n (hP n)).1
  have hv0 : ∀ n, 0 ≤ (unpairTable j n : ℝ) := fun n => by
    exact_mod_cast (unpairTable_mem j n).1
  have hzero : ∀ w : PCWorld, w.ConsistentWithTheory unpairProcess →
      w.ValuesAt (LUV.indicatorOf (∼(⊤ : Sentence))) 0 := fun w hw =>
    indicatorOf_valuesAt_zero hw fun h => ((PCWorld.holds_neg w _).1 h) (PCWorld.holds_top w)
  have hone : ∀ w : PCWorld, w.ConsistentWithTheory unpairProcess →
      w.ValuesAt (LUV.indicatorOf (⊤ : Sentence)) 1 := fun w hw =>
    indicatorOf_valuesAt_one hw (PCWorld.holds_top w)
  -- the piece bounds, both sides, for every `c`
  have hpieceLE : ∀ c : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, n.unpair.2 = c →
      (ledgerLuv j n).expect P n ≤ (unpairTable j n : ℝ) + ε := by
    intro c ε hε
    have hc0 : (0 : ℝ) ≤ 1 / ((c : ℝ) + 1) := by positivity
    have h := pinning_asympLE (P := P) (piecePad_thresholdCodes j (pieceEq_ruler c) _) hworld
      (piecePad_determined j (pieceEq c) (∼(⊤ : Sentence)) 0 hzero) (L := 1 / ((c : ℝ) + 1))
      (fun ε' hε' => Filter.Eventually.of_forall fun n => by
        by_cases h0 : pieceEq c n = 0
        · rw [if_pos h0, unpairTable_piece j (pieceEq_eq_zero.1 h0)]; linarith
        · rw [if_neg h0]; linarith)
    filter_upwards [h ε hε] with n hn hnc
    have h0 : pieceEq c n = 0 := pieceEq_eq_zero.2 hnc
    simp only [piecePad, if_pos h0] at hn
    rw [unpairTable_piece j hnc]
    exact hn
  have hpieceGE : ∀ c : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, n.unpair.2 = c →
      (unpairTable j n : ℝ) ≤ (ledgerLuv j n).expect P n + ε := by
    intro c ε hε
    have hc1 : 1 / ((c : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
    have h := pinning_asympGE (P := P) (piecePad_thresholdCodes j (pieceEq_ruler c) _) hworld
      (piecePad_determined j (pieceEq c) (⊤ : Sentence) 1 hone) (L := 1 / ((c : ℝ) + 1))
      (fun ε' hε' => Filter.Eventually.of_forall fun n => by
        by_cases h0 : pieceEq c n = 0
        · rw [if_pos h0, unpairTable_piece j (pieceEq_eq_zero.1 h0)]; linarith
        · rw [if_neg h0]; linarith)
    filter_upwards [h ε hε] with n hn hnc
    have h0 : pieceEq c n = 0 := pieceEq_eq_zero.2 hnc
    simp only [piecePad, if_pos h0] at hn
    rw [unpairTable_piece j hnc]
    exact hn
  -- the tail bound, upper side only (the lower side is `0 ≤ expect`)
  have htailLE : ∀ C : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, C ≤ n.unpair.2 →
      (ledgerLuv j n).expect P n ≤ 1 / ((C : ℝ) + 1) + ε := by
    intro C ε hε
    have hC0 : (0 : ℝ) ≤ 1 / ((C : ℝ) + 1) := by positivity
    have h := pinning_asympLE (P := P) (piecePad_thresholdCodes j (pieceGE_ruler C) _) hworld
      (piecePad_determined j (pieceGE C) (∼(⊤ : Sentence)) 0 hzero) (L := 1 / ((C : ℝ) + 1))
      (fun ε' hε' => Filter.Eventually.of_forall fun n => by
        by_cases h0 : pieceGE C n = 0
        · rw [if_pos h0]; linarith [unpairTable_tail j (pieceGE_eq_zero.1 h0)]
        · rw [if_neg h0]; linarith)
    filter_upwards [h ε hε] with n hn hnC
    have h0 : pieceGE C n = 0 := pieceGE_eq_zero.2 hnC
    simp only [piecePad, if_pos h0] at hn
    exact hn
  refine asympEq_iff_asympLE_asympGE.2 ⟨?_, ?_⟩
  · -- `≲ₙ`
    intro ε hε
    obtain ⟨C, hC⟩ := exists_nat_one_div_lt (half_pos hε)
    have hall : ∀ᶠ n in atTop, ∀ c ∈ Finset.range C, n.unpair.2 = c →
        (ledgerLuv j n).expect P n ≤ (unpairTable j n : ℝ) + ε :=
      (Filter.eventually_all_finset (Finset.range C)).2 fun c _ => hpieceLE c ε hε
    filter_upwards [hall, htailLE C (ε / 2) (half_pos hε)] with n h1 h2
    by_cases hn : C ≤ n.unpair.2
    · have := h2 hn
      have := hv0 n
      linarith
    · exact h1 n.unpair.2 (Finset.mem_range.2 (not_le.1 hn)) rfl
  · -- `≳ₙ`
    intro ε hε
    obtain ⟨C, hC⟩ := exists_nat_one_div_lt hε
    have hall : ∀ᶠ n in atTop, ∀ c ∈ Finset.range C, n.unpair.2 = c →
        (unpairTable j n : ℝ) ≤ (ledgerLuv j n).expect P n + ε :=
      (Filter.eventually_all_finset (Finset.range C)).2 fun c _ => hpieceGE c ε hε
    filter_upwards [hall] with n h1
    by_cases hn : C ≤ n.unpair.2
    · have := unpairTable_tail j hn
      have := hexp n
      linarith
    · exact h1 n.unpair.2 (Finset.mem_range.2 (not_le.1 hn)) rfl

end Cleanroom.Deference.DefTrackingPin
