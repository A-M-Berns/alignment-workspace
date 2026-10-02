import Cleanroom.Decision.DpDutchBook.Yankees

/-!
Audit round 2, adversarial lens — probe 2: does `yankees_no_msrAtD4` have *joint* content?

The headline says no procedure is D4-approved at **both** points of Arntzenius's tree. An
adversarial reading: perhaps `MsrAtD4 · .lose` (or `· .win`) is unsatisfiable on its own, so the
conjunction fails for a one-point reason and the "two tie curves never meet" story is decoration.
This probe exhibits, from the package's own closed forms (`yankees_msrAtD4_win_iff`,
`yankees_msrAtD4_lose_iff`), one procedure D4-approved at `d_win` (`p = 2/9`, `q = 0`: the
win-point tie) and another D4-approved at `d_lose` (`p = 1/2`, `q = 9/11`: the lose-point tie,
with `R_lose > 0` so the standing hypothesis holds there). Each point's condition is satisfiable;
only the conjunction is not — the headline's content is genuinely joint. (The win-point witness
is also what `yankees_hStand_win` + Kakutani would give; note `msrAtD4_exists` is over `ℝ` and
`yankees` is over `ℚ`, so the win-point existence is shown here directly, not through Kakutani.)
Not imported by the library.
-/

namespace Cleanroom.Decision.DpDutchBook.AuditR2Adv

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDutchBook

/-- A label on `Act2` over `ℚ` with weight `q` on `.b` (= BY). -/
def act2Q (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr ℚ Act2 where
  w := fun | .a => 1 - q | .b => q
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Act2.sum_univ]; simp

/-- `p = C(d_win)(BY) = 2/9`, `q = C(d_lose)(BY) = 0`: the win-point tie `Q_win = 0`. -/
def yCwin : Proc YPt (fun _ => Act2) ℚ := fun d =>
  match d with
  | .win => act2Q (2 / 9) (by norm_num) (by norm_num)
  | .lose => act2Q 0 (by norm_num) (by norm_num)

/-- `p = 1/2`, `q = 9/11`: the lose-point tie `Q_lose = 0`. -/
def yClose : Proc YPt (fun _ => Act2) ℚ := fun d =>
  match d with
  | .win => act2Q (1 / 2) (by norm_num) (by norm_num)
  | .lose => act2Q (9 / 11) (by norm_num) (by norm_num)

/-- D4 at `d_win` alone is satisfiable. -/
theorem win_alone : MsrAtD4 yObs yActEv yCwin yankees .win := by
  rw [yankees_msrAtD4_win_iff]
  norm_num [yCwin, act2Q, yQwin]

/-- D4 at `d_lose` alone is satisfiable, with the standing hypothesis holding there. -/
theorem lose_alone :
    0 < yRlose ((yClose .win).w .b) ((yClose .lose).w .b) ∧
      MsrAtD4 yObs yActEv yClose yankees .lose := by
  have hR : 0 < yRlose ((yClose .win).w .b) ((yClose .lose).w .b) := by
    simp [yClose, act2Q, yRlose]; norm_num
  refine ⟨hR, ?_⟩
  rw [yankees_msrAtD4_lose_iff yClose hR]
  norm_num [yClose, act2Q, yQlose]

/-- …and the headline still kills both (sanity). -/
example : ¬ (MsrAtD4 yObs yActEv yCwin yankees .win ∧ MsrAtD4 yObs yActEv yCwin yankees .lose) :=
  yankees_no_msrAtD4 yCwin

example : ¬ (MsrAtD4 yObs yActEv yClose yankees .win ∧ MsrAtD4 yObs yActEv yClose yankees .lose) :=
  yankees_no_msrAtD4 yClose

end Cleanroom.Decision.DpDutchBook.AuditR2Adv
