import Cleanroom.Udt.UdtPaperTiling.Vingean
import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-paper-tiling` · VingeanWitness: the N+ witness of Theorems 3/4 and the N− content check

**The N+ witness** (`VinWit`): observations `o = T1`, `ō = T2` (`udt-bli-core`'s `twoTables`);
actions `x = 0`, `y = 1`, `m = 2` with `𝒜_o = {x, y, m}`, `𝒜_ō = {x, y}`, `𝒜^m = {m}`, `m̂ = x`,
`mod m = {(ō, x)}`; twelve worlds of mass `1/12` — the state (`Fin 2`), the chosen point at `o`
(`Fin 3`) and at `ō` (`Bool`: `false = x`, `true = y`); utility `U(x,x) = 6` in state `0` and
`2` in state `1` (cell average `4`), `U(x,y) = 4`, `U(y,x) = 0`, `U(y,y) = 2`, `U(m,·) = 4`; the
argmax variables `αM o' := pp · o'`, `αJ := pp · ō`, `αC := pp · ō`. Then Fine-Grained Fairness
holds (`EU o m = 4 = cellEU (x, x)`), Faith in Joint Argmax at `({x,y}, o, ō)` holds (the cells
`4, 4, 0, 2` are all `≤ 4 = EU o x`), Faith in Argmax at `φ = (pp·ō = x)` holds (`4, 0, 4 ≤ 4`),
Action Coordination / Naive Action Coordination / KDP hold with probability one, and Theorems 3
and 4 give `EU o m = 4 ≤ 4 = EU o x`.

**Why this is N+, and what it is not** (repair round 1, adversarial B1). Round 1's witness had
`U ≤ 4` everywhere with `EU o x = 4`, so the conclusion followed from a global bound and none of
FGF/FJA/AC/KDP did any work. Here `sup U = 6 > 4 = EU o x` (`U_xx0`), so no global bound closes
the conclusion and FJA must be proved from the cell values (`cell_le`); the chain is needed.
`αM ō` is non-constant, `m` has mass `1/3`, and `EU ō x = 8/3 < 10/3 = EU ō y` — `pp · ō` is
random and sometimes suboptimal. What this does **not** show: the argmax variables are the policy
coordinate by `rfl`, so AC and KDP hold identically rather than as constraints — and inside
Theorem 3's package that is forced (`Vingean.lean`, `fja_pinned`: AC + KDP pin `αJ` to `pp · ō`
a.s. for any `V`), so no witness can exercise the (c) model beyond a.s.-equality there. The
hypothesis the witness exercises is `FaithInJointArgmaxPrior` on the prior; the content check
that it is not a tautology is `VinSep.not_fja`.

**The N− content check** (`VinSep`): the same structure and variables with the separable utility
`U = 2 · [pp·ō = x]`: Faith in Joint Argmax **fails** (`cellEU (x, x) = 2 > 1 = jointEU b` for
every `b`), so the model's FJA is not a tautology.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

namespace VinWit

/-- `(0 : Fin 3) ≠ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f01 : (0 : Fin 3) ≠ 1 := by decide
/-- `(0 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f02 : (0 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma f12 : (1 : Fin 3) ≠ 2 := by decide
/-- `Rec ≠ Ask` (the form `T2 = T1` takes after `simp`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm
/-- `(1 : Fin 2) ≠ 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma s10 : (1 : Fin 2) ≠ 0 := by decide
/-- The three actions. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide

/-- **The witness structure**: `𝒜_o = {x, y, m}`, `𝒜_ō = {x, y}`, `𝒜^m = {m}`, `m̂ = x`,
`mod m = {(ō, x)}`.
Source: mandate T5 (suggested witness)
Kind: D
Fidelity: n/a -/
def S : PaperStructure twoTables (Fin 3) where
  Aof := fun T => if T = T1 then {0, 1, 2} else {0, 1}
  selfMod := {2}
  twin := fun a => if a = 2 then 0 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    by_cases hT : T = T1
    · simp only [hT, if_true] at ha ⊢
      fin_cases a <;> decide
    · simp only [hT, if_false] at ha ⊢
      fin_cases a <;> simp_all
  twin_id := by
    intro a ha
    fin_cases a <;> simp_all
  mod := fun a T => if a = 2 ∧ T = T2 then some 0 else none
  mod_nonMod_none := by
    intro a ha T
    fin_cases a <;> simp_all

/-- **Limited Self-Modification** on `S`: `ob m = ō`, `ac m = x`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def L : LimitedSelfMod S where
  ob := fun _ => T2
  ac := fun _ => 0
  mod_eq := by
    intro a ha T
    have : a = 2 := by simpa [S] using ha
    subst this
    simp [S]
  ac_nonMod := by intro a _; decide
  not_self := by
    intro a ha
    have : a = 2 := by simpa [S] using ha
    subst this
    simp [S, mRec_ne_mAsk]

/-- The chosen policy of the world `(state, point at o, point at ō)`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def pp₀ (ω : Fin 2 × Fin 3 × Bool) : Policy twoTables (Fin 3) :=
  fun T => if T = T1 then ω.2.1 else if ω.2.2 then 1 else 0

/-- The utility table, by state `s`, point `a` at `o` and point `b` at `ō`: `U(y,x) = 0`,
`U(y,y) = 2`, `U(x,x) = 6` in state `0` and `2` in state `1` (so the cell `(x,x)` averages `4`
but `sup U = 6 > EU o x`), `U(x,y) = 4`, `U(m,·) = 4`.
Source: mandate T5, with the audit r1 (adversarial B1) change on the `(x,x)` cell
Kind: D
Fidelity: n/a -/
def tbl (s : Fin 2) (a : Fin 3) (b : Bool) : ℚ :=
  if a = 1 then (if b then 2 else 0) else if a = 0 then (if b then 4 else if s = 0 then 6 else 2) else 4

/-- The utility of a world. Source: mandate T5. Kind: D. Fidelity: n/a -/
def U₀ (ω : Fin 2 × Fin 3 × Bool) : ℚ := tbl ω.1 ω.2.1 ω.2.2

/-- **The N+ prior**: twelve worlds of mass `1/12`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables (Fin 3) :=
  handPrior (Fin 2 × Fin 3 × Bool) (fun _ => 1 / 12) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => twoState ω.1) two_zeroOne pp₀ U₀

/-- **The argmax variables**: `αM o' := pp · o'`, `αJ := pp · ō`, `αC := pp · ō`.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def V : ArgmaxVars prior where
  αM := fun T ω => pp₀ ω T
  αJ := fun _ _ _ ω => pp₀ ω T2
  αC := fun _ _ _ ω => pp₀ ω T2

/-- `U = 6` on the world `(0, x, x)`: the utility exceeds `EU o x = 4`, so no global bound closes
Theorem 3's conclusion on this witness. Source: audit r1 adversarial B1. Kind: L. Fidelity: n/a -/
lemma U_xx0 : prior.U (0, 0, false) = 6 := by
  show tbl 0 0 false = 6
  simp [tbl]

/-- `EU o x = 4`. Source: mandate T5. Kind: L. Fidelity: n/a -/
lemma EU_x : prior.EU T1 0 = 4 := by
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `EU o y = 1`. Source: mandate T5. Kind: L. Fidelity: n/a -/
lemma EU_y : prior.EU T1 1 = 1 := by
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `EU o m = 4`. Source: mandate T5. Kind: L. Fidelity: n/a -/
lemma EU_m : prior.EU T1 2 = 4 := by
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `EU ō x = 8/3`. Source: mandate T5 (the N+ point). Kind: L. Fidelity: n/a -/
lemma EU_bar_x : prior.EU T2 0 = 8 / 3 := by
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `EU ō y = 10/3`. Source: mandate T5 (the N+ point). Kind: L. Fidelity: n/a -/
lemma EU_bar_y : prior.EU T2 1 = 10 / 3 := by
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `μ(pp·o = m) = 1/3`. Source: mandate T5. Kind: L. Fidelity: n/a -/
lemma ppMass_m : prior.ppMass T1 2 = 1 / 3 := by
  unfold FiniteBLIPrior.ppMass prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- `μ(pp·o = x) = 1/3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma ppMass_x : prior.ppMass T1 0 = 1 / 3 := by
  unfold FiniteBLIPrior.ppMass prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- The fairness cell `(x, x)` has mass `1/6`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_xx_mass : prior.pairMass T1 T2 0 0 = 1 / 6 := by
  unfold FiniteBLIPrior.pairMass prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- The fairness cell `(x, x)` has value `4` (the average of `6` and `2`).
Source: mandate T5. Kind: L. Fidelity: n/a -/
lemma cell_xx_EU : cellEU prior T1 T2 0 0 = 4 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The cell `(x, y)` has value `4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_xy_EU : cellEU prior T1 T2 0 1 = 4 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The cell `(y, x)` has value `0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_yx_EU : cellEU prior T1 T2 1 0 = 0 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The cell `(y, y)` has value `2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_yy_EU : cellEU prior T1 T2 1 1 = 2 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The cell `(m, x)` has value `4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_mx_EU : cellEU prior T1 T2 2 0 = 4 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The cell `(m, y)` has value `4`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_my_EU : cellEU prior T1 T2 2 1 = 4 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, tbl, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm, s10]

/-- The point `pp·ō = m` is null, so every cell `(a, m)` is. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pairMass_T2_m (a : Fin 3) : prior.pairMass T1 T2 a 2 = 0 := by
  unfold FiniteBLIPrior.pairMass prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- **Every positive concrete cell at `(o, ō)` has value at most `4 = EU o x`**: the cells are
`(x,x) = 4`, `(x,y) = 4`, `(y,x) = 0`, `(y,y) = 2`, `(m,x) = 4`, `(m,y) = 4`, and the cells
`(·, m)` are null. This is `FaithInJointArgmaxPrior` on the witness, proved from the cell values
(no global bound on `U` is available: `U_xx0`).
Source: audit r1 adversarial B1 ("re-prove `fja` from the cells")
Kind: L
Fidelity: n/a -/
lemma cell_le (a a' : Fin 3) (hpos : 0 < prior.pairMass T1 T2 a a') :
    cellEU prior T1 T2 a a' ≤ 4 := by
  rcases fin3_cases a' with rfl | rfl | rfl
  · rcases fin3_cases a with rfl | rfl | rfl
    · exact le_of_eq cell_xx_EU
    · rw [cell_yx_EU]; norm_num
    · exact le_of_eq cell_mx_EU
  · rcases fin3_cases a with rfl | rfl | rfl
    · exact le_of_eq cell_xy_EU
    · rw [cell_yy_EU]; norm_num
    · exact le_of_eq cell_my_EU
  · rw [pairMass_T2_m] at hpos
    exact absurd hpos (lt_irrefl _)

/-- The `αJ`-cell of `b` is the point `pp·o = b` (the second conjunct is `pp·ō = pp·ō`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointMass_eq (A' : Finset (Fin 3)) (b : Fin 3) :
    jointMass V A' T1 T2 b = prior.ppMass T1 b := by
  unfold jointMass FiniteBLIPrior.ppMass
  apply massOf_congr
  intro ω
  simp [V, prior, handPrior]

/-- The `αJ`-cell of `b` has the value `EU o b`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointEU_eq (A' : Finset (Fin 3)) (b : Fin 3) : jointEU V A' T1 T2 b = prior.EU T1 b := by
  unfold jointEU FiniteBLIPrior.EU
  apply condExp_congr
  intro ω
  simp [V, prior, handPrior]

/-- The `αC`-cell of `x` is the point `pp·o = x` (mass). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condMass_eq :
    massOf prior.μ (fun ω => prior.pp ω T1 = 0 ∧ prior.pp ω T2 = V.αC T1 0 T2 ω) =
      prior.ppMass T1 0 := by
  unfold FiniteBLIPrior.ppMass
  apply massOf_congr
  intro ω
  simp [V, prior, handPrior]

/-- The `αC`-cell of `x` has the value `EU o x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condEU_eq :
    condExp prior.μ prior.U (fun ω => prior.pp ω T1 = 0 ∧ prior.pp ω T2 = V.αC T1 0 T2 ω) =
      prior.EU T1 0 := by
  unfold FiniteBLIPrior.EU
  apply condExp_congr
  intro ω
  simp [V, prior, handPrior]

/-- **Fine-Grained Fairness holds**: `EU o m = 4 = cellEU (x, x)`.
Source: mandate T5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fgf : FineGrainedFairness prior S L := by
  intro o aₘ ha hm _ _
  have h2 : aₘ = 2 := by simpa [S] using hm
  subst h2
  rcases eq_T1_or_T2 o with rfl | rfl
  · have ht : S.twin 2 = 0 := by simp [S]
    show prior.EU T1 2 = cellEU prior T1 T2 (S.twin 2) 0
    rw [ht, EU_m, cell_xx_EU]
  · exfalso
    simp [S, mRec_ne_mAsk] at ha

/-- **Faith in Joint Argmax at `({x, y}, o, ō)` holds**: every positive concrete cell has value
at most `4 = jointEU x`, proved from the cell values (`cell_le`), not from a bound on `U`.
Source: mandate T5; audit r1 adversarial B1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fja : FaithInJointArgmaxAt V (S.nonModAt T1) T1 T2 := by
  intro a' a _ hpos
  refine ⟨0, by simp [S], ?_, ?_⟩
  · rw [jointMass_eq, ppMass_x]; norm_num
  · rw [jointEU_eq, EU_x]
    exact cell_le a a' hpos

/-- **Action Coordination holds** (with probability one, `αJ = αM ō`: both are `pp · ō`).
Source: mandate T5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem ac : ActionCoordination V (S.nonModAt T1) T1 T2 := by
  unfold ActionCoordination
  rw [← prior.massOf_true]
  apply massOf_congr
  intro ω
  simp [V]

/-- **Knowledge of Decision Procedure holds at `ō`** (and at `o`): `pp · o' = αM o'` everywhere.
Source: mandate T5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem kdp (o : ↥twoTables) : KnowledgeOfDecisionProcedure V o := by
  unfold KnowledgeOfDecisionProcedure
  rw [← prior.massOf_true]
  apply massOf_congr
  intro ω
  simp [V, prior, handPrior]

/-- **Faith in Argmax at `(ō, o, x)` holds** (`φ = (pp·o = x)`): the positive cells `(x,x) = 4`
and `(x,y) = 4` of the row `pp·o = x` are `≤ 4 = EU o x`, from the cell values.
Source: mandate T5; audit r1 adversarial B1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fa : FaithInArgmax V T2 T1 0 := by
  intro a hpos
  refine ⟨?_, ?_⟩
  · rw [condMass_eq, ppMass_x]; norm_num
  · rw [condEU_eq, EU_x]
    exact cell_le 0 a hpos

/-- **Naive Action Coordination holds** at `(ō, o, x)`.
Source: mandate T5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem nac : NaiveActionCoordination S V T2 T1 0 := by
  intro _
  rw [← prior.massOf_true]
  apply massOf_congr
  intro ω
  simp [V]

/-- **Theorem 3 instantiated on the witness**: an available non-modifying action of positive
mass at least as good as `m` exists — and the numbers: `EU o m = 4 = EU o x`, `EU o y = 1`.
Source: mandate T5 (load-bearing 2)
Kind: N+
Fidelity: n/a
Hyps: (a) none (every hypothesis of `thm3_vingean_tiling` is discharged above) -/
theorem thm3_on_witness :
    (∃ a ∈ S.Aof T1, a ∉ S.selfMod ∧ 0 < prior.ppMass T1 a ∧ prior.EU T1 2 ≤ prior.EU T1 a) ∧
    prior.EU T1 2 = 4 ∧ prior.EU T1 0 = 4 ∧ prior.EU T1 1 = 1 := by
  refine ⟨thm3_vingean_tiling S L V fgf T1 2 (by simp [S]) (by simp [S]) ?_ ?_ fja ac (kdp T2),
    EU_m, EU_x, EU_y⟩
  · rw [ppMass_m]; norm_num
  · show 0 < prior.pairMass T1 T2 0 0
    rw [cell_xx_mass]; norm_num

/-- **Theorem 4 instantiated on the witness**: `EU o m ≤ EU o m̂ = EU o x` with the twin's point
positive.
Source: mandate T5; bli-slides-045
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem thm4_on_witness : 0 < prior.ppMass T1 (S.twin 2) ∧ prior.EU T1 2 ≤ prior.EU T1 (S.twin 2) :=
  thm4_appendixA_tiling S L V fgf T1 2 (by simp [S]) (by simp [S])
    (by rw [ppMass_m]; norm_num) (by show 0 < prior.pairMass T1 T2 0 0; rw [cell_xx_mass]; norm_num)
    fa nac (kdp T2)

/-- **Why the witness is N+**: the self-modifying action has mass `1/3`; the argmax variable at
`ō` (which is `pp · ō`) is non-constant; the meta-level maximizer at `ō` is `y`
(`EU ō x = 8/3 < 10/3 = EU ō y`) while `αM ō` takes the non-maximizer `x` with probability
`1/2` — `pp · ō` is random and sometimes suboptimal; **and** the utility reaches `6` on a world of
the `(x,x)` cell while `EU o x = 4`, so Theorem 3's conclusion is not a consequence of a global
bound and the chain (FGF, FJA from the cells, AC, KDP) is needed. Not claimed: that the model
expresses something the prior cannot — inside Theorem 3's package it cannot (`fja_pinned`).
Source: mandate T5 ("record this as the witness's point"); audit r1 adversarial B1
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem grade_Nplus :
    prior.ppMass T1 2 = 1 / 3 ∧ (∃ ω ω', V.αM T2 ω ≠ V.αM T2 ω') ∧
    prior.EU T2 0 = 8 / 3 ∧ prior.EU T2 1 = 10 / 3 ∧
    massOf prior.μ (fun ω => V.αM T2 ω = 0) = 1 / 2 ∧
    prior.EU T1 0 < prior.U (0, 0, false) := by
  refine ⟨ppMass_m, ⟨(0, 0, false), (0, 0, true), by simp [V, pp₀, mRec_ne_mAsk]⟩, EU_bar_x,
    EU_bar_y, ?_, by rw [EU_x, U_xx0]; norm_num⟩
  unfold prior
  rw [handPrior_massOf]
  simp only [V, handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

end VinWit

/-! ## The N− content check: a model where Faith in Joint Argmax fails -/

namespace VinSep

open VinWit

/-- The separable utility `U = 2 · [pp·ō = x]`. Source: mandate T5. Kind: D. Fidelity: n/a -/
def U₀ (ω : Fin 2 × Fin 3 × Bool) : ℚ := if ω.2.2 then 0 else 2

/-- **The separable prior**: the same worlds, utility `U = 2 · [pp·ō = x]`.
Source: mandate T5 (content check)
Kind: D
Fidelity: n/a -/
def prior : FiniteBLIPrior witIndex 1 twoTables (Fin 3) :=
  handPrior (Fin 2 × Fin 3 × Bool) (fun _ => 1 / 12) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool])
    (fun ω => twoState ω.1) two_zeroOne pp₀ U₀

/-- The same argmax variables over the separable prior.
Source: mandate T5
Kind: D
Fidelity: n/a -/
def V : ArgmaxVars prior where
  αM := fun T ω => pp₀ ω T
  αJ := fun _ _ _ ω => pp₀ ω T2
  αC := fun _ _ _ ω => pp₀ ω T2

/-- The cell `(x, x)` has mass `1/6`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_xx_mass : prior.pairMass T1 T2 0 0 = 1 / 6 := by
  unfold FiniteBLIPrior.pairMass prior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, pp₀, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- The cell `(x, x)` has value `2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cell_xx_EU : cellEU prior T1 T2 0 0 = 2 := by
  unfold cellEU prior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- Every `αJ`-cell has value `1` (the average of `g`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma jointEU_eq (A' : Finset (Fin 3)) (b : Fin 3) : jointEU V A' T1 T2 b = 1 := by
  have h : jointEU V A' T1 T2 b = prior.EU T1 b := by
    unfold jointEU FiniteBLIPrior.EU
    apply condExp_congr
    intro ω
    simp [V, prior, handPrior]
  rw [h]
  unfold FiniteBLIPrior.EU prior
  rw [handPrior_condExp]
  match b with
  | 0 =>
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]
  | 1 =>
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]
  | 2 =>
    simp only [handPrior, condExp, massOf, integralOf, pp₀, U₀, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three, Fintype.sum_bool]
    norm_num [mRec_ne_mAsk, f01, f02, f12, f01.symm, f02.symm, f12.symm]

/-- **Faith in Joint Argmax fails on the separable prior**: the concrete cell `(x, x)` has value
`2`, every `αJ`-cell has value `1`. So FJA in the computation-output model is not a tautology.
Source: mandate T5 (content check, N−)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem not_fja : ¬ FaithInJointArgmaxAt V (S.nonModAt T1) T1 T2 := by
  intro h
  obtain ⟨b, _, _, hle⟩ := h 0 0 (by simp [S]) (by rw [cell_xx_mass]; norm_num)
  rw [cell_xx_EU, jointEU_eq] at hle
  norm_num at hle

end VinSep

end Cleanroom.Udt.UdtPaperTiling
