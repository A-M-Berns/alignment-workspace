/-
# The robust reading of a warrant, on the eight-world model

Round `projects/normativity/rounds/2026-11-07-score-side-binding/`.

**The model** (§2), stated here with exact rationals: a binary quantity `q` with a uniform
prior, a signal `s` of accuracy `3/4` and a challenge `ch` of accuracy `2/3`, independent given
the quantity — eight worlds `(q, s, ch)`.  The dispatch cited `ThinLegitimacy` for it; that
file's §11 mentions an eight-world fixture in prose and exposes no world type or measure for
it, so the model is local.

**What fails** (§3).  Read "the signal is a reason for the quantity, strength `3/4`" as the
strength row `3/4 · P(A) ≤ P(A ∧ Y)` at the posterior of whatever record the warrant is
undefeated at.  At the record with the signal alone the row holds with equality
(`valid_at_signal`: `Pr(Y | A) = 3/4`).  At the record with a contrary challenge the posterior
is `3/5` and the row fails (`invalid_at_contrary`).  Neither mechanism the rows have removes it
there: embedded in a three-coordinate fragment, the settlement that records the challenge pins
neither the antecedent nor the consequent, so `settleOutcome` keeps the form and `settleForm`
contributes the specialized row, and the quiet docket undercuts nothing
(`kept_under_challenge`, `not_undercut`), and the repository's grounded survivor rule applied
to the warrant's grounds at that record keeps it (`survives_challenge`); the contributed row is
violated by her posterior (`contributed_row_invalid`).  Registering the challenge as an opposing warrant at `2/3` makes
the two rows jointly infeasible (`naiveCert`, `naive_conflict`), although the answer `3/5` is
determinate.

**What holds** (§1, §4).  **The robust reading** (provisional name `Robust`): a warrant is a
constraint on her model over the undefeated extensions `U` of its anchor,
`Pr(Y | A ∧ E) ≥ c` for every `E ∈ U`.  Its one-line soundness lemma: the strength row is then
valid at every undefeated record (`robust_sound`).  The **robust strength** is the least
conditional over the undefeated extensions (`robustStrength`, `robust_iff_le_robustStrength`):
`3/5` over the three extensions of the fixture (`robustStrength_all`), `3/4` with the contrary
challenge declared a defeater (`robustStrength_defeated`; both together `robustStrength_both`,
the statement of record).  The extension sets `Uall` and `Udef` are declared, not derived from
any defeat mechanism.  The opposing warrant's robust
strength is `2/5` (`against_robust_iff`), and the two robust rows meet at the single point
`3/5` (`robust_meet`).  No general defeat semantics is built; the definition and the fixture
are the deliverable.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantEntitlement

namespace Workspace.Normativity.Contrib.RobustWarrant

open Finset
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement

/-! ## 1. The robust reading -/

section General

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The mass of an event under a rational measure on a finite world type. -/
def mass (μ : W → ℚ) (E : Finset W) : ℚ := ∑ w ∈ E, μ w

/-- **The robust reading of a warrant** (provisional name).  "`A` is a reason for `Y` at strength
`c`" constrains her model over the undefeated extensions `U` of the anchor: `Pr(Y | A ∧ E) ≥ c`
for every `E ∈ U` at which `A ∧ E` is possible — not the posterior at whichever record the
warrant happens to be undefeated at. -/
def Robust (μ : W → ℚ) (A Y : Finset W) (c : ℚ) (U : Finset (Finset W)) : Prop :=
  ∀ E ∈ U, 0 < mass μ (A ∩ E) → c * mass μ (A ∩ E) ≤ mass μ (A ∩ Y ∩ E)

/-- Her posterior at the record `E`: `p_E(S) = μ(S ∩ E) / μ(E)`. -/
def post (μ : W → ℚ) (E S : Finset W) : ℚ := mass μ (S ∩ E) / mass μ E

/-- **The strength row is valid at a record** when her posterior there satisfies
`c · p(A) ≤ p(A ∧ Y)`. -/
def RowValid (μ : W → ℚ) (A Y : Finset W) (c : ℚ) (E : Finset W) : Prop :=
  c * post μ E A ≤ post μ E (A ∩ Y)

omit [Fintype W] in
/-- **Soundness of the robust reading**, one line: a robust warrant's strength row is valid at
every undefeated record of positive mass at which the anchor is possible. -/
theorem robust_sound {μ : W → ℚ} {A Y : Finset W} {c : ℚ} {U : Finset (Finset W)}
    (h : Robust μ A Y c U) {E : Finset W} (hE : E ∈ U) (hpos : 0 < mass μ E)
    (hA : 0 < mass μ (A ∩ E)) : RowValid μ A Y c E := by
  unfold RowValid post
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hpos]
  exact h E hE hA

/-- **The robust strength**: the least conditional `Pr(Y | A ∧ E)` over the undefeated
extensions at which the anchor is possible. -/
noncomputable def robustStrength (μ : W → ℚ) (A Y : Finset W) (U : Finset (Finset W))
    (hU : (U.filter fun E => 0 < mass μ (A ∩ E)).Nonempty) : ℚ :=
  (U.filter fun E => 0 < mass μ (A ∩ E)).inf' hU fun E => mass μ (A ∩ Y ∩ E) / mass μ (A ∩ E)

omit [Fintype W] in
/-- A warrant is robust at strength `c` iff `c` is at most the robust strength. -/
theorem robust_iff_le_robustStrength (μ : W → ℚ) (A Y : Finset W) (c : ℚ)
    (U : Finset (Finset W)) (hU : (U.filter fun E => 0 < mass μ (A ∩ E)).Nonempty) :
    Robust μ A Y c U ↔ c ≤ robustStrength μ A Y U hU := by
  unfold Robust robustStrength
  rw [Finset.le_inf'_iff]
  constructor
  · intro h E hE
    rw [mem_filter] at hE
    rw [le_div_iff₀ hE.2]
    exact h E hE.1 hE.2
  · intro h E hE hpos
    have := h E (mem_filter.2 ⟨hE, hpos⟩)
    rwa [le_div_iff₀ hpos] at this

end General

/-! ## 2. The eight-world model -/

/-- A world: the quantity, the signal's reading, the challenge's reading. -/
abbrev World := Bool × Bool × Bool

/-- The measure: a uniform prior on the quantity; the signal right with probability `3/4`, the
challenge right with probability `2/3`, independently given the quantity. -/
def μ : World → ℚ := fun w =>
  (1/2) * (if w.2.1 = w.1 then 3/4 else 1/4) * (if w.2.2 = w.1 then 2/3 else 1/3)

/-- The quantity is true. -/
def Yev : Finset World := univ.filter fun w => w.1 = true
/-- The signal reads true: the warrant's anchor. -/
def Aev : Finset World := univ.filter fun w => w.2.1 = true
/-- The challenge reads false: contrary to the signal. -/
def Cev : Finset World := univ.filter fun w => w.2.2 = false
/-- The challenge reads true: concurring. -/
def Ccev : Finset World := univ.filter fun w => w.2.2 = true

/-- A mass as a sum over all worlds of an indicator. -/
lemma mass_eq_sum_ite (E : Finset World) : mass μ E = ∑ w, if w ∈ E then μ w else 0 := by
  unfold mass
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The measure sums to one. -/
theorem mass_univ : mass μ univ = 1 := by
  rw [mass_eq_sum_ite]
  norm_num [μ, Fintype.sum_prod_type, Fintype.sum_bool]

lemma mass_A : mass μ Aev = 1/2 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_AY : mass μ (Aev ∩ Yev) = 3/8 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Yev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_AC : mass μ (Aev ∩ Cev) = 5/24 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Cev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_AYC : mass μ (Aev ∩ Yev ∩ Cev) = 1/8 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Yev, Cev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_ACc : mass μ (Aev ∩ Ccev) = 7/24 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Ccev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_AYCc : mass μ (Aev ∩ Yev ∩ Ccev) = 1/4 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Aev, Yev, Ccev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_C : mass μ Cev = 1/2 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Cev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_Aunion : mass μ (Aev ∩ univ) = 1/2 := by rw [inter_univ, mass_A]
lemma mass_AYunion : mass μ (Aev ∩ Yev ∩ univ) = 3/8 := by rw [inter_univ, mass_AY]

/-! ## 3. What fails: the row at the posterior, and the mechanisms that do not fire -/

/-- `Pr(Y | A) = 3/4`: at the record with the signal alone the warrant's strength is exact. -/
theorem posterior_signal : post μ Aev Yev = 3/4 := by
  unfold post; rw [inter_comm, mass_AY, mass_A]; norm_num

/-- `Pr(Y | A ∧ C) = 3/5`: after a contrary challenge. -/
theorem posterior_contrary : post μ (Aev ∩ Cev) Yev = 3/5 := by
  unfold post
  rw [show Yev ∩ (Aev ∩ Cev) = Aev ∩ Yev ∩ Cev by ext; simp only [mem_inter]; tauto,
    mass_AYC, mass_AC]
  norm_num

/-- `Pr(Y | A ∧ ¬C) = 6/7`: after a concurring challenge. -/
theorem posterior_concurring : post μ (Aev ∩ Ccev) Yev = 6/7 := by
  unfold post
  rw [show Yev ∩ (Aev ∩ Ccev) = Aev ∩ Yev ∩ Ccev by ext; simp only [mem_inter]; tauto,
    mass_AYCc, mass_ACc]
  norm_num

/-- **Valid at the record with the signal alone**: `3/4 · P(A) ≤ P(A ∧ Y)` holds at her prior
(the record `⊤`), with equality. -/
theorem valid_at_signal : RowValid μ Aev Yev (3/4) univ := by
  unfold RowValid post
  rw [inter_univ, inter_univ, mass_univ, mass_A, mass_AY]
  norm_num

/-- **Invalid at the record with the contrary challenge**: `3/4 · P(A | C) = 5/16 > 1/4 =
P(A ∧ Y | C)`. -/
theorem invalid_at_contrary : ¬ RowValid μ Aev Yev (3/4) Cev := by
  unfold RowValid post
  rw [mass_AC, mass_AYC, mass_C]
  norm_num

/-- The fragment: coordinates `A`, `A ∧ Y`, and the contrary challenge `C`. -/
abbrev a : Fin 3 := 0
abbrev ay : Fin 3 := 1
abbrev cc : Fin 3 := 2

/-- The warrant occurrence: the strength form `P(A ∧ Y) ≥ 3/4 · P(A)`. -/
def occ : Occurrence 3 := ⟨1, Form.strength a ay (3/4), .none, .party 1, ∅⟩

/-- The settlement after the contrary challenge is observed: `C` pinned true, the antecedent
and the consequent untouched. -/
def Fch : Settlement 3 := ⟨![none, none, some true]⟩

/-- Her posterior at the record `C`, as a price vector on the fragment:
`(P(A | C), P(A ∧ Y | C), P(C | C)) = (5/12, 1/4, 1)`. -/
def postC : Fin 3 → ℚ := ![5/12, 1/4, 1]

lemma postC_eq : postC = ![post μ Cev Aev, post μ Cev (Aev ∩ Yev), post μ Cev Cev] := by
  unfold post
  rw [mass_AC, mass_AYC, inter_self, mass_C]
  funext i; fin_cases i <;> simp [postC] <;> norm_num

/-- **Rebuttal by settlement does not fire**: the challenge pins neither `A` nor `A ∧ Y`, so
the form is kept and `settleForm` contributes its specialized row. -/
theorem kept_under_challenge :
    settleOutcome Fch occ.form = .kept ∧ settleForm Fch occ = some [specialize Fch occ.form.row] := by
  refine ⟨by decide, ?_⟩
  unfold settleForm
  rw [if_pos (by decide)]

/-- **Undercut does not fire**: the docket is quiet. -/
theorem not_undercut : ¬ undercut DocketState.quiet occ := by
  simp [undercut, occ, DocketState.quiet]

/-- The grounds of the embedding: the warrant alone. -/
def groundsCh : Grounds 3 := [occ]

/-- **The grounded survivor rule keeps the warrant.**  `Grounds.survivors` — the repository's
rule composing undercut, rebuttal by settlement and grounded citation — applied to the grounds
`[occ]` at the contrary-challenge record on the quiet docket returns `[occ]`: neither
mechanism removes it, and its specialized row is contributed there. -/
theorem survives_challenge : groundsCh.survivors DocketState.quiet Fch = [occ] := by
  have hk : settleOutcome Fch (Form.strength a ay (3/4)) = .kept := kept_under_challenge.1
  have hu := not_undercut
  unfold Grounds.survivors
  simp only [groundsCh, occ] at hu ⊢
  simp [liveGiven, hk, hu, citesIn]

/-- The contributed row holds at her posterior at the record `⊤`. -/
theorem contributed_row_valid_at_signal : occ.form.row.Sat ![1/2, 3/8, 1/2] := by
  simp [occ, Form.row, Row.Sat, Fin.sum_univ_three, a, ay]
  norm_num

/-- **The contributed row is violated by her posterior at the record `C`**: the row the kept,
un-undercut warrant contributes demands `3/4 · 5/12 ≤ 1/4`. -/
theorem contributed_row_invalid : ¬ (specialize Fch occ.form.row).Sat postC := by
  simp [specialize, settledTerm, Fch, occ, Form.row, Row.Sat, postC, Fin.sum_univ_three, truth,
    a, ay]
  norm_num

/-- **Registering the challenge as an opposing warrant conflicts.**  At the record `A ∧ C`, on
the single coordinate `P(Y)`: for `Y` at `3/4` and for `¬Y` at `2/3` are `3/4 ≤ y` and
`y ≤ 1/3`; the certificate sums them to `0 ≤ −5/12`. -/
def naiveCert : FarkasCert 1 2 where
  mult := ![1, 1]
  row := ![⟨![-1], -3/4⟩, ⟨![1], 1/3⟩]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by fin_cases j; simp [Fin.sum_univ_two]
  const_sum := by simp [Fin.sum_univ_two]; norm_num

theorem naive_conflict : ¬ ∃ y : Fin 1 → ℚ, ∀ i, (naiveCert.row i).Sat y :=
  fun ⟨y, hy⟩ => farkas_sound naiveCert y hy

/-! ## 4. What holds: the robust strengths -/

/-- The undefeated extensions of the anchor: nothing more, the contrary challenge, the
concurring challenge. -/
def Uall : Finset (Finset World) := {univ, Cev, Ccev}

/-- The extensions with the contrary challenge declared a defeater. -/
def Udef : Finset (Finset World) := {univ, Ccev}

lemma Cev_ne_univ : Cev ≠ univ := by
  intro h
  have : (true, true, true) ∈ Cev := h ▸ mem_univ _
  simp [Cev] at this
lemma Ccev_ne_univ : Ccev ≠ univ := by
  intro h
  have : (true, true, false) ∈ Ccev := h ▸ mem_univ _
  simp [Ccev] at this
lemma Cev_ne_Ccev : Cev ≠ Ccev := by
  intro h
  have : (true, true, false) ∈ Ccev := h ▸ (by simp [Cev])
  simp [Ccev] at this

/-- **Robust over all three extensions iff `c ≤ 3/5`.** -/
theorem robust_all_iff (c : ℚ) : Robust μ Aev Yev c Uall ↔ c ≤ 3/5 := by
  unfold Robust Uall
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, mass_Aunion, mass_AYunion,
    mass_AC, mass_AYC, mass_ACc, mass_AYCc]
  constructor
  · rintro ⟨-, h, -⟩
    have := h (by norm_num)
    linarith
  · intro h
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> linarith

/-- **Robust with the contrary challenge a defeater iff `c ≤ 3/4`.** -/
theorem robust_defeated_iff (c : ℚ) : Robust μ Aev Yev c Udef ↔ c ≤ 3/4 := by
  unfold Robust Udef
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, mass_Aunion, mass_AYunion,
    mass_ACc, mass_AYCc]
  constructor
  · rintro ⟨h, -⟩
    have := h (by norm_num)
    linarith
  · intro h
    refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> linarith

lemma Uall_filter : Uall.filter (fun E => 0 < mass μ (Aev ∩ E)) = Uall := by
  unfold Uall
  rw [filter_eq_self]
  intro E hE
  simp only [mem_insert, mem_singleton] at hE
  rcases hE with rfl | rfl | rfl
  · rw [mass_Aunion]; norm_num
  · rw [mass_AC]; norm_num
  · rw [mass_ACc]; norm_num

lemma Udef_filter : Udef.filter (fun E => 0 < mass μ (Aev ∩ E)) = Udef := by
  unfold Udef
  rw [filter_eq_self]
  intro E hE
  simp only [mem_insert, mem_singleton] at hE
  rcases hE with rfl | rfl
  · rw [mass_Aunion]; norm_num
  · rw [mass_ACc]; norm_num

lemma Uall_nonempty : (Uall.filter fun E => 0 < mass μ (Aev ∩ E)).Nonempty := by
  rw [Uall_filter]; exact ⟨univ, by simp [Uall]⟩
lemma Udef_nonempty : (Udef.filter fun E => 0 < mass μ (Aev ∩ E)).Nonempty := by
  rw [Udef_filter]; exact ⟨univ, by simp [Udef]⟩

/-- **The robust strength over the three extensions is `3/5`.** -/
theorem robustStrength_all : robustStrength μ Aev Yev Uall Uall_nonempty = 3/5 := by
  apply le_antisymm
  · unfold robustStrength
    refine (Finset.inf'_le _ (show Cev ∈ _ by rw [Uall_filter]; simp [Uall])).trans ?_
    rw [mass_AYC, mass_AC]; norm_num
  · rw [← robust_iff_le_robustStrength, robust_all_iff]

/-- **With the contrary challenge a defeater, the robust strength is `3/4`.** -/
theorem robustStrength_defeated : robustStrength μ Aev Yev Udef Udef_nonempty = 3/4 := by
  apply le_antisymm
  · unfold robustStrength
    refine (Finset.inf'_le _ (show (univ : Finset World) ∈ _ by rw [Udef_filter]; simp [Udef])).trans ?_
    rw [mass_AYunion, mass_Aunion]; norm_num
  · rw [← robust_iff_le_robustStrength, robust_defeated_iff]

/-- **Both robust strengths**: `3/5` over the three extensions and `3/4` with the contrary
challenge declared a defeater.  The statement of record for `robust.eight-world-strengths`. -/
theorem robustStrength_both :
    robustStrength μ Aev Yev Uall Uall_nonempty = 3/5 ∧
      robustStrength μ Aev Yev Udef Udef_nonempty = 3/4 :=
  ⟨robustStrength_all, robustStrength_defeated⟩

/-- The opposing warrant's extensions: nothing more, the signal, no signal. -/
def Uagainst : Finset (Finset World) := {univ, Aev, univ \ Aev}

lemma mass_C_notY : mass μ (Cev ∩ (univ \ Yev)) = 1/3 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Cev, Yev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_C_A : mass μ (Cev ∩ Aev) = 5/24 := by rw [inter_comm, mass_AC]
lemma mass_C_notY_A : mass μ (Cev ∩ (univ \ Yev) ∩ Aev) = 1/12 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Cev, Yev, Aev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_C_notA : mass μ (Cev ∩ (univ \ Aev)) = 7/24 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Cev, Aev, Fintype.sum_prod_type, Fintype.sum_bool]
lemma mass_C_notY_notA : mass μ (Cev ∩ (univ \ Yev) ∩ (univ \ Aev)) = 1/4 := by
  rw [mass_eq_sum_ite]; norm_num [μ, Cev, Yev, Aev, Fintype.sum_prod_type, Fintype.sum_bool]

/-- **The opposing warrant — the contrary challenge is a reason against `Y` — is robust iff
`c ≤ 2/5`**: `Pr(¬Y | C) = 2/3`, `Pr(¬Y | C ∧ A) = 2/5`, `Pr(¬Y | C ∧ ¬A) = 6/7`. -/
theorem against_robust_iff (c : ℚ) : Robust μ Cev (univ \ Yev) c Uagainst ↔ c ≤ 2/5 := by
  unfold Robust Uagainst
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, inter_univ, mass_C,
    mass_C_notY, mass_C_A, mass_C_notY_A, mass_C_notA, mass_C_notY_notA]
  constructor
  · rintro ⟨-, h, -⟩
    have := h (by norm_num)
    linarith
  · intro h
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> linarith

/-- **The robust rows meet at `3/5`.**  At the record `A ∧ C`, the robust row for `Y` is
`3/5 ≤ y` and the robust row for `¬Y` is `2/5 ≤ 1 − y`; together they fix `y = 3/5`, the
determinate posterior. -/
theorem robust_meet (y : ℚ) : (3/5 ≤ y ∧ 2/5 ≤ 1 - y) ↔ y = 3/5 := by
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · rintro rfl; norm_num

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.RobustWarrant.mass
#print axioms Workspace.Normativity.Contrib.RobustWarrant.Robust
#print axioms Workspace.Normativity.Contrib.RobustWarrant.post
#print axioms Workspace.Normativity.Contrib.RobustWarrant.RowValid
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robust_sound
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robustStrength
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robust_iff_le_robustStrength
#print axioms Workspace.Normativity.Contrib.RobustWarrant.μ
#print axioms Workspace.Normativity.Contrib.RobustWarrant.mass_eq_sum_ite
#print axioms Workspace.Normativity.Contrib.RobustWarrant.mass_univ
#print axioms Workspace.Normativity.Contrib.RobustWarrant.posterior_signal
#print axioms Workspace.Normativity.Contrib.RobustWarrant.posterior_contrary
#print axioms Workspace.Normativity.Contrib.RobustWarrant.posterior_concurring
#print axioms Workspace.Normativity.Contrib.RobustWarrant.valid_at_signal
#print axioms Workspace.Normativity.Contrib.RobustWarrant.invalid_at_contrary
#print axioms Workspace.Normativity.Contrib.RobustWarrant.occ
#print axioms Workspace.Normativity.Contrib.RobustWarrant.Fch
#print axioms Workspace.Normativity.Contrib.RobustWarrant.postC
#print axioms Workspace.Normativity.Contrib.RobustWarrant.postC_eq
#print axioms Workspace.Normativity.Contrib.RobustWarrant.kept_under_challenge
#print axioms Workspace.Normativity.Contrib.RobustWarrant.not_undercut
#print axioms Workspace.Normativity.Contrib.RobustWarrant.groundsCh
#print axioms Workspace.Normativity.Contrib.RobustWarrant.survives_challenge
#print axioms Workspace.Normativity.Contrib.RobustWarrant.contributed_row_valid_at_signal
#print axioms Workspace.Normativity.Contrib.RobustWarrant.contributed_row_invalid
#print axioms Workspace.Normativity.Contrib.RobustWarrant.naiveCert
#print axioms Workspace.Normativity.Contrib.RobustWarrant.naive_conflict
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robust_all_iff
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robust_defeated_iff
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robustStrength_all
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robustStrength_defeated
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robustStrength_both
#print axioms Workspace.Normativity.Contrib.RobustWarrant.against_robust_iff
#print axioms Workspace.Normativity.Contrib.RobustWarrant.robust_meet

end Workspace.Normativity.Contrib.RobustWarrant
