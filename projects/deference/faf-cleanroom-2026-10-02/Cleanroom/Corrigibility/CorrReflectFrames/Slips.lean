import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-!
# corr-reflect-frames — T17: Managing Misalignment's worked-example slips

Herrmann 2025 (MM) §4.1 Table 2 (12 equiprobable states; Bob's decisions and the outcome for
Alice) transcribed as magnitudes, signs and acceptances, scored under the two gain conventions
the paper uses: the **all-correct** convention of Appendix A/B ("a gain if Bob opens on a
positive value or correctly avoids opening on a negative value") and the **printed-formula**
convention of §4.3 (`G = ∫_{D ∩ I_ω} |g_ω| dμ`, gains only on accepted positives). Under Table
2's own convention the gains sum to `43/12` and `S(D_B) = −22/12`, not the printed `32/12` and
`−11/12`; under the printed formula, `33/12` and `−1`. For §4.2, the main text's
`(−150/12, −700/12)` is the all-correct convention; Appendix B's `(750/12, −400/12)` matches
neither. The delegation verdicts are unchanged under either convention. Local errors in the
literature; no thesis claim depends on them. No frame is involved, so this file imports only
Mathlib.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Slips

open Finset

noncomputable section

/-- Expected loss: probability-weighted magnitudes of the wrong decisions (accept a negative or
reject a positive).
Source: [[herrmann-2025]] §4.1 Table 2 caption (Appendix A) l. 199
Kind: D
Fidelity: exact -/
def lossOf {n : ℕ} (p mag : Fin n → ℝ) (pos acc : Fin n → Bool) : ℝ :=
  ∑ i, p i * mag i * (if acc i ≠ pos i then 1 else 0)

/-- Expected gain, all-correct convention (Appendix A/B): magnitudes of the correct decisions.
Source: [[herrmann-2025]] Appendix A l. 199 ("a gain if Bob opens on a positive value or
correctly avoids opening on a negative value")
Kind: D
Fidelity: exact -/
def gainAll {n : ℕ} (p mag : Fin n → ℝ) (pos acc : Fin n → Bool) : ℝ :=
  ∑ i, p i * mag i * (if acc i = pos i then 1 else 0)

/-- Expected gain, printed-formula convention (§4.3, `G = ∫_{D ∩ I_ω} |g_ω| dμ`): magnitudes of
the accepted positives only.
Source: [[herrmann-2025]] §4.3 (the displayed formula); [[mm]] item 13(a) l. 283
Kind: D
Fidelity: exact -/
def gainPrinted {n : ℕ} (p mag : Fin n → ℝ) (pos acc : Fin n → Bool) : ℝ :=
  ∑ i, p i * mag i * (if acc i = true ∧ pos i = true then 1 else 0)

/-- Table 2 (§4.1), Bob's twelve states: outcome magnitudes for Alice.
Source: [[herrmann-2025]] Table 2 l. 201 (rows as `mm-scratch/check_i12_i13.py` `bob41`)
Kind: D
Fidelity: exact (transcription) -/
def table2Mag : Fin 12 → ℝ := ![5, 5, 5, 5, 3, 3, 3, 3, 8, 8, 8, 8]

/-- Table 2: whether the true value is positive.
Source: [[herrmann-2025]] Table 2 l. 201
Kind: D
Fidelity: exact (transcription) -/
def table2Pos : Fin 12 → Bool :=
  ![false, false, false, false, true, true, true, true, true, true, true, true]

/-- Table 2: whether Bob opens.
Source: [[herrmann-2025]] Table 2 l. 201
Kind: D
Fidelity: exact (transcription) -/
def table2Acc : Fin 12 → Bool :=
  ![true, false, true, false, true, true, true, false, true, true, true, false]

/-- The uniform weights on twelve states.
Source: [[herrmann-2025]] Appendix A l. 199
Kind: D
Fidelity: exact -/
def unif12 : Fin 12 → ℝ := fun _ => 1 / 12

/-- **Table 2 recomputed (all-correct convention).** `L(D_B) = 21/12`, `G(D_B) = 43/12`, so
`S(D_B) = L − G = −22/12` — not the printed `G = 32/12`, `S = −11/12`.
Source: [[herrmann-2025]] §4.1 l. 137 (printed values), Table 2 l. 201; [[mm]] item 13(b)
l. 283
Kind: N+
Fidelity: exact (the paper's own table under the paper's own stated convention)
Hyps: (a) none -/
theorem table2_allCorrect :
    lossOf unif12 table2Mag table2Pos table2Acc = 21 / 12 ∧
      gainAll unif12 table2Mag table2Pos table2Acc = 43 / 12 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [lossOf, gainAll, Fin.sum_univ_succ, unif12, table2Mag, table2Pos, table2Acc]

/-- **Table 2 recomputed (printed-formula convention).** Gains only on accepted positives:
`G(D_B) = 33/12`, so `S(D_B) = −12/12`. Neither convention yields the printed `32/12`.
Source: [[herrmann-2025]] §4.1 l. 137, §4.3 (formula); [[mm]] item 13(a)(b) l. 283
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem table2_printed : gainPrinted unif12 table2Mag table2Pos table2Acc = 33 / 12 := by
  norm_num [gainPrinted, Fin.sum_univ_succ, unif12, table2Mag, table2Pos, table2Acc]

/-- §4.2 (misaligned expert), Bob's twelve states: Alice's effective post-fee magnitudes.
Source: [[herrmann-2025]] §4.2 l. 137, Table 4 (rows as `check_i12_i13.py` `bob42`)
Kind: D
Fidelity: exact (transcription) -/
def table4Mag : Fin 12 → ℝ := ![450, 450, 450, 25, 25, 25, 50, 50, 50, 175, 175, 175]

/-- §4.2: sign of Alice's effective payoff, **post-fee**: the `ω = 25` rows (4–6) are transcribed
as negative, the convention that reproduces the main text's `−700/12`, `−150/12`. The paper's
own row labels disagree with each other here (Appendix B calls rows 5–6 "fails to open on a
positive value" while row 4's outcome is "−25 (Loss)"), and Appendix B's sums count rows 5–6 as
losses of `25` and the avoided `−400` as a pre-fee gain of `400`, mixing the two conventions
within one table (findings F12).
Source: [[herrmann-2025]] §4.2 l. 137, Appendix B l. 353
Kind: D
Fidelity: exact (transcription, post-fee sign) -/
def table4Pos : Fin 12 → Bool :=
  ![false, false, false, false, false, false, true, true, true, true, true, true]

/-- §4.2: whether Bob opens.
Source: [[herrmann-2025]] §4.2 l. 137
Kind: D
Fidelity: exact (transcription) -/
def table4Acc : Fin 12 → Bool :=
  ![true, false, false, true, false, false, true, true, false, true, true, false]

/-- **§4.2 recomputed for Bob.** All-correct: `L = 700/12`, `G = 1400/12`, `S = −700/12`
(the main text's value). Printed formula: `G = 450/12`, `S = 250/12`. Appendix B's `−400/12`
matches neither.
Source: [[herrmann-2025]] §4.2 l. 137, Appendix B l. 361; [[mm]] item 13(c) l. 283
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem table4_bob :
    lossOf unif12 table4Mag table4Pos table4Acc = 700 / 12 ∧
      gainAll unif12 table4Mag table4Pos table4Acc = 1400 / 12 ∧
      gainPrinted unif12 table4Mag table4Pos table4Acc = 450 / 12 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [lossOf, gainAll, gainPrinted, Fin.sum_univ_succ, unif12, table4Mag, table4Pos,
      table4Acc]

/-- §4.2, Alice never opening: four equiprobable values `(−400, 25, 100, 225)`, all rejected.
Source: [[herrmann-2025]] §4.2 l. 137
Kind: D
Fidelity: exact (transcription) -/
def aliceMag : Fin 4 → ℝ := ![400, 25, 100, 225]

/-- §4.2, Alice: signs.
Source: [[herrmann-2025]] §4.2 l. 137
Kind: D
Fidelity: exact (transcription) -/
def alicePos : Fin 4 → Bool := ![false, true, true, true]

/-- §4.2, Alice never opens.
Source: [[herrmann-2025]] §4.2 l. 137
Kind: D
Fidelity: exact (transcription) -/
def aliceAcc : Fin 4 → Bool := ![false, false, false, false]

/-- **§4.2 recomputed for Alice.** All-correct: `L = 1050/12`, `G = 1200/12`, `S = −150/12`
(the main text's value); printed formula: `G = 0`, `S = 1050/12`. Appendix B's `750/12`
matches neither. Under either convention `S(D_B) < S(D_π)`: the delegation verdict is unchanged.
Source: [[herrmann-2025]] §4.2 l. 137, Appendix B l. 361; [[mm]] item 13(c) l. 283
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem table4_alice :
    lossOf (fun _ => 1 / 4) aliceMag alicePos aliceAcc = 1050 / 12 ∧
      gainAll (fun _ => 1 / 4) aliceMag alicePos aliceAcc = 1200 / 12 ∧
      gainPrinted (fun _ => 1 / 4) aliceMag alicePos aliceAcc = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [lossOf, gainAll, gainPrinted, Fin.sum_univ_succ, aliceMag, alicePos, aliceAcc]

/-- §4.1, Alice always opens: every one of Table 2's twelve states accepted.
Source: [[herrmann-2025]] §4.1 l. 137 ("Alice … always opens")
Kind: D
Fidelity: exact (transcription) -/
def table2AccAlice : Fin 12 → Bool := fun _ => true

/-- **§4.1 recomputed for Alice always opening.** `L = 20/12` (the four `−5` states accepted),
`G = 44/12` under both conventions (the eight positives are all accepted), so `S = −24/12`.
Source: [[herrmann-2025]] §4.1 l. 137; [[mm]] item 13 l. 283
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem table2_aliceOpens :
    lossOf unif12 table2Mag table2Pos table2AccAlice = 20 / 12 ∧
      gainAll unif12 table2Mag table2Pos table2AccAlice = 44 / 12 ∧
      gainPrinted unif12 table2Mag table2Pos table2AccAlice = 44 / 12 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [lossOf, gainAll, gainPrinted, Fin.sum_univ_succ, unif12, table2Mag, table2Pos,
      table2AccAlice]

/-- **Delegation verdicts are convention-independent**, stated through the transcribed tables
(`S = L − G` for each decision-maker under each convention; the paper delegates when the
delegate's `S` is lower): in §4.2 Bob's `−700/12` is below Alice's `−150/12` (all-correct) and
his `250/12` below her `1050/12` (printed formula) — delegate; in §4.1 Alice always opening
scores `−24/12` under both conventions while Bob scores `−22/12` (all-correct) and `−12/12`
(printed), both higher — do not delegate. The verdicts the paper prints, under either
convention. Round 0 stated this on bare numerals; the `20/12`, `44/12` are now computed from
`table2AccAlice` (audit r1, N3).
Source: [[mm]] item 13 l. 283 ("Every delegation verdict is unchanged under either convention")
Kind: L
Fidelity: exact (every number is computed from the transcribed tables; nothing hand-entered)
Hyps: (a) none -/
theorem verdicts_unchanged :
    (lossOf unif12 table4Mag table4Pos table4Acc - gainAll unif12 table4Mag table4Pos table4Acc <
      lossOf (fun _ => 1 / 4) aliceMag alicePos aliceAcc -
        gainAll (fun _ => 1 / 4) aliceMag alicePos aliceAcc) ∧
    (lossOf unif12 table4Mag table4Pos table4Acc - gainPrinted unif12 table4Mag table4Pos table4Acc <
      lossOf (fun _ => 1 / 4) aliceMag alicePos aliceAcc -
        gainPrinted (fun _ => 1 / 4) aliceMag alicePos aliceAcc) ∧
    (lossOf unif12 table2Mag table2Pos table2AccAlice -
        gainAll unif12 table2Mag table2Pos table2AccAlice <
      lossOf unif12 table2Mag table2Pos table2Acc - gainAll unif12 table2Mag table2Pos table2Acc) ∧
    (lossOf unif12 table2Mag table2Pos table2AccAlice -
        gainPrinted unif12 table2Mag table2Pos table2AccAlice <
      lossOf unif12 table2Mag table2Pos table2Acc -
        gainPrinted unif12 table2Mag table2Pos table2Acc) := by
  obtain ⟨b1, b2, b3⟩ := table4_bob
  obtain ⟨a1, a2, a3⟩ := table4_alice
  obtain ⟨c1, c2⟩ := table2_allCorrect
  have c3 := table2_printed
  obtain ⟨d1, d2, d3⟩ := table2_aliceOpens
  rw [b1, b2, b3, a1, a2, a3, c1, c2, c3, d1, d2, d3]
  norm_num

end

end Cleanroom.Corrigibility.CorrReflectFrames.Slips
