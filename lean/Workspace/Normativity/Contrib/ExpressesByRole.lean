/-
# `Expresses` by incompatibility role, against the robust reading of a warrant

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, matter 2, second half.

`WarrantInductor.Entitlement` takes a declared `Expresses : Req → Form d → Prop`.  Here the
anchored requirement is a defeasible warrant (`Requirement`: antecedent event, consequent
event, strength, undefeated extensions) and it **denotes its models**: the nonnegative measures
satisfying `RobustWarrant.Robust` (`Requirement.Models`).  A form is read as a **content** — the
rows it contributes at each record (`Content`) — under one of two rules: `plain`, its
specialized row at every record, and `settled`, its specialized row where the rebuttal rule
`settleOutcome` keeps it (`settled_eq_settleForm`).  An interpretation `ι` sends coordinates to
events; a record is the event its settlement records (`recEvent`) and a model prices the
fragment by its posterior there (`prices`).

**The two strengths** (§2).  A list of rows is *incompatible with the requirement at a record*
when no model's posterior there satisfies it (`ReqIncompatible`).  The content **demands no
more** than the requirement when every list incompatible with the content at a record is
incompatible with the requirement there (`DemandsNoMore`), and has the **same role**, relative
to a declared background, when the two incompatibility relations agree (`SameRole`).  By
completeness of conflicts, demanding no more is exactly: every model of the requirement
satisfies the content's rows at every record of positive mass (`demandsNoMore_iff`).

**General results** (§3).  A model of a requirement of positive strength gives the antecedent
mass zero on any undefeated extension on which the consequent is false
(`models_null_at_rebuttal`).  The row the rebuttal rule keeps demands no more than a
requirement of at least its strength whose undefeated extensions include every record the rule
keeps it at (`settled_demandsNoMore`).  The plain row demands more wherever a model gives the
antecedent positive posterior at a record that settles the consequent false
(`plain_demandsMore`): there it contraposes (`WarrantEntitlement.strength_contraposes`).

**The fixture** (§4), on the eight-world model of `RobustWarrant` with the fragment
`(A, A∧Y, C)`.  `entitlementW` inhabits `Entitlement` under `ExpressesNoMore ι settled` for the
strength row at `3/5` against the requirement at `3/5` over the kept extensions, with admission
by standing and a live account.  The relation discriminates: the plain row is not expressed
(`plain_not_expresses`, with the conflict `contraCert` in `contraposition_as_expression`), so no
entitlement exists under the plain rule (`no_entitlement_plain`); the row at `3/4` is expressed
under neither anchored requirement, so the grounds of `RobustWarrant` have no entitlement
(`no_entitlement_at_three_quarters`) — against the requirement at `3/4` with the contrary
challenge a declared defeater the kept row demands more at the challenge record
(`defeater_not_expressed`); the three together are `entitlement_discriminates`.  The row at
`1/2` demands no more and does not have the same role
(`weaker_noMore_not_same`).  That the row at `3/5` has the same role is not proved.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.IncompatibilitySemantics
import Workspace.Normativity.Contrib.RobustWarrant
import Workspace.Normativity.Contrib.AdmissionByStanding

namespace Workspace.Normativity.Contrib.ExpressesByRole

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.RowAlternative
open Workspace.Normativity.Contrib.IncompatibilitySemantics
open Workspace.Normativity.Contrib.RobustWarrant
open Workspace.Normativity.Contrib.OccurrenceIntegrity
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Normativity.Contrib.WarrantInductor
open Workspace.Normativity.Contrib.AdmissionByStanding (withStanding J₀ issuer)
open Finset

/-! ## 1. Contents, records, posterior prices -/

section General

variable {W : Type*} [Fintype W] [DecidableEq W] {d : ℕ}

/-- A **content**: the rows demanded at each record. -/
abbrev Content (d : ℕ) := Settlement d → List (Row d)

/-- The plain reading of a form: its specialized row at every record. -/
def plain (f : Form d) : Content d := fun F => [specialize F f.row]

/-- The reading under the rebuttal rule: the specialized row where `settleOutcome` keeps the
form, nothing otherwise. -/
def settled (f : Form d) : Content d :=
  fun F => if settleOutcome F f = .kept then [specialize F f.row] else []

theorem settled_eq_settleForm (F : Settlement d) (o : Occurrence d) :
    settled o.form F = (settleForm F o).getD [] := by
  unfold settled settleForm
  split_ifs <;> rfl

omit [Fintype W] [DecidableEq W] in
theorem mass_empty (μ : W → ℚ) : mass μ ∅ = 0 := by simp [mass]

omit [Fintype W] [DecidableEq W] in
theorem mass_nonneg {μ : W → ℚ} (hμ : ∀ w, 0 ≤ μ w) (E : Finset W) : 0 ≤ mass μ E :=
  Finset.sum_nonneg fun w _ => hμ w

omit [Fintype W] [DecidableEq W] in
theorem mass_mono {μ : W → ℚ} (hμ : ∀ w, 0 ≤ μ w) {E E' : Finset W} (h : E ⊆ E') :
    mass μ E ≤ mass μ E' :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun w _ _ => hμ w

/-- **The event a settlement records**, under an interpretation of the coordinates as events:
the worlds in every coordinate settled true and outside every coordinate settled false. -/
def recEvent (ι : Fin d → Finset W) (F : Settlement d) : Finset W :=
  univ.filter fun w => ∀ i, (F.val i = some true → w ∈ ι i) ∧ (F.val i = some false → w ∉ ι i)

/-- **Posterior prices** of the fragment at a record. -/
def prices (μ : W → ℚ) (ι : Fin d → Finset W) (E : Finset W) : Fin d → ℚ :=
  fun i => post μ E (ι i)

omit [Fintype W] in
theorem prices_inCube {μ : W → ℚ} (hμ : ∀ w, 0 ≤ μ w) (ι : Fin d → Finset W) {E : Finset W}
    (hE : 0 < mass μ E) : InCube (prices μ ι E) := by
  intro i
  unfold prices post
  exact ⟨div_nonneg (mass_nonneg hμ _) hE.le,
    (div_le_one hE).2 (mass_mono hμ Finset.inter_subset_right)⟩

/-- The posterior at a record agrees with the record's settlement. -/
theorem prices_pinned {μ : W → ℚ} (ι : Fin d → Finset W) (F : Settlement d)
    (hE : 0 < mass μ (recEvent ι F)) : F.Pinned (prices μ ι (recEvent ι F)) := by
  intro i b hi
  unfold prices post
  cases b with
  | true =>
    have h : ι i ∩ recEvent ι F = recEvent ι F := by
      rw [Finset.inter_eq_right]
      intro w hw
      exact ((Finset.mem_filter.1 hw).2 i).1 hi
    rw [h, div_self hE.ne']
    simp [truth]
  | false =>
    have h : ι i ∩ recEvent ι F = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter] at hw
      exact ((Finset.mem_filter.1 hw.2).2 i).2 hi hw.1
    rw [h, mass_empty, zero_div]
    simp [truth]

/-- The rows fixing a point: `x i ≤ p i` and `−x i ≤ −p i` for each coordinate. -/
def pointRows (p : Fin d → ℚ) : List (Row d) :=
  (List.finRange d).flatMap fun i => [boundRow i 1 (p i), boundRow i (-1) (-(p i))]

theorem pointRows_sat_iff (p x : Fin d → ℚ) : SatAll (pointRows p) x ↔ x = p := by
  unfold SatAll pointRows
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · intro h
    funext i
    have h1 := h _ ⟨i, Or.inl rfl⟩
    have h2 := h _ ⟨i, Or.inr rfl⟩
    rw [boundRow_sat] at h1 h2
    linarith
  · rintro rfl r ⟨i, rfl | rfl⟩ <;> rw [boundRow_sat] <;> linarith

/-! ## 2. The requirement and the two strengths -/

/-- **A defeasible warrant as an anchored requirement**: `A` is a reason for `Y` at strength
`c`, over the undefeated extensions `U`. -/
structure Requirement (W : Type*) where
  A : Finset W
  Y : Finset W
  c : ℚ
  U : Finset (Finset W)

/-- **The denotation of the requirement**: the nonnegative measures at which the warrant is
robust. -/
def Requirement.Models (w : Requirement W) (μ : W → ℚ) : Prop :=
  (∀ v, 0 ≤ μ v) ∧ Robust μ w.A w.Y w.c w.U

/-- A list of rows is **incompatible with the requirement at a record**: no model's posterior
at the record satisfies it. -/
def ReqIncompatible (w : Requirement W) (ι : Fin d → Finset W) (F : Settlement d)
    (X : List (Row d)) : Prop :=
  ¬ ∃ μ, w.Models μ ∧ 0 < mass μ (recEvent ι F) ∧ SatAll X (prices μ ι (recEvent ι F))

/-- **Demands no more**: every list incompatible with the content at a record is incompatible
with the requirement there. -/
def DemandsNoMore (ι : Fin d → Finset W) (w : Requirement W) (ρ : Content d) : Prop :=
  ∀ F X, Incompatible (ρ F ++ X) → ReqIncompatible w ι F X

/-- **Same role**, relative to a background content: at every record the lists incompatible
with the content and the background are exactly the lists incompatible with the requirement. -/
def SameRole (ι : Fin d → Finset W) (w : Requirement W) (β ρ : Content d) : Prop :=
  ∀ F X, Incompatible (ρ F ++ β F ++ X) ↔ ReqIncompatible w ι F X

/-- A model satisfies a content: its posterior at every record of positive mass satisfies the
rows the content contributes there. -/
def Holds (μ : W → ℚ) (ι : Fin d → Finset W) (ρ : Content d) : Prop :=
  ∀ F, 0 < mass μ (recEvent ι F) → SatAll (ρ F) (prices μ ι (recEvent ι F))

/-- **Demanding no more is model inclusion**: the content demands no more than the requirement
iff every model of the requirement satisfies the content. -/
theorem demandsNoMore_iff (ι : Fin d → Finset W) (w : Requirement W) (ρ : Content d) :
    DemandsNoMore ι w ρ ↔ ∀ μ, w.Models μ → Holds μ ι ρ := by
  constructor
  · intro h μ hmod F hpos r hr
    by_contra hsat
    have hinc : Incompatible (ρ F ++ pointRows (prices μ ι (recEvent ι F))) := by
      rw [incompatible_iff_not_feasible]
      rintro ⟨x, -, hx⟩
      rw [satAll_append, pointRows_sat_iff] at hx
      obtain ⟨hρ, hxp⟩ := hx
      rw [hxp] at hρ
      exact hsat (hρ r hr)
    exact h F _ hinc ⟨μ, hmod, hpos, (pointRows_sat_iff _ _).2 rfl⟩
  · rintro h F X hinc ⟨μ, hmod, hpos, hX⟩
    rw [incompatible_iff_not_feasible] at hinc
    exact hinc ⟨_, prices_inCube hmod.1 ι hpos, (satAll_append _ _ _).2 ⟨h μ hmod F hpos, hX⟩⟩

omit [Fintype W] [DecidableEq W] in
theorem incompatible_mono {L L' : List (Row d)} (h : ∀ r ∈ L, r ∈ L') (hL : Incompatible L) :
    Incompatible L' := by
  obtain ⟨m, c, hall⟩ := hL
  exact ⟨m, c, fun i => (hall i).mono h⟩

/-- The same role implies demanding no more. -/
theorem SameRole.demandsNoMore {ι : Fin d → Finset W} {w : Requirement W} {β ρ : Content d}
    (h : SameRole ι w β ρ) : DemandsNoMore ι w ρ := by
  intro F X hinc
  refine (h F X).1 (incompatible_mono (fun r hr => ?_) hinc)
  simp only [List.mem_append] at hr ⊢
  tauto

/-- **`Expresses`, the weaker strength**: under a contribution rule, the form's content demands
no more than the requirement. -/
def ExpressesNoMore (ι : Fin d → Finset W) (rule : Form d → Content d) (w : Requirement W)
    (f : Form d) : Prop :=
  DemandsNoMore ι w (rule f)

/-- **`Expresses`, the stronger strength**: the form's content has the same role as the
requirement, relative to a background. -/
def ExpressesSame (ι : Fin d → Finset W) (β : Content d) (rule : Form d → Content d)
    (w : Requirement W) (f : Form d) : Prop :=
  SameRole ι w β (rule f)

/-! ## 3. General results -/

omit [Fintype W] in
/-- **A robust warrant of positive strength gives the antecedent no mass on an undefeated
extension that rebuts it.** -/
theorem models_null_at_rebuttal {w : Requirement W} {μ : W → ℚ} (hmod : w.Models μ)
    (hc : 0 < w.c) {E : Finset W} (hE : E ∈ w.U) (hreb : w.A ∩ w.Y ∩ E = ∅) :
    mass μ (w.A ∩ E) = 0 := by
  by_contra hne
  have hpos : 0 < mass μ (w.A ∩ E) := lt_of_le_of_ne (mass_nonneg hmod.1 _) (Ne.symm hne)
  have := hmod.2 E hE hpos
  rw [hreb, mass_empty] at this
  nlinarith

/-- **The records at which the rebuttal rule keeps a form**, as events. -/
def keptExtensions (ι : Fin d → Finset W) (f : Form d) : Finset (Finset W) :=
  ((univ : Finset (Fin d → Option Bool)).filter fun v => settleOutcome ⟨v⟩ f = .kept).image
    fun v => recEvent ι ⟨v⟩

theorem mem_keptExtensions {ι : Fin d → Finset W} {f : Form d} {F : Settlement d}
    (h : settleOutcome F f = .kept) : recEvent ι F ∈ keptExtensions ι f :=
  Finset.mem_image.2 ⟨F.val, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- **The row the rebuttal rule keeps demands no more** than a requirement of at least its
strength whose undefeated extensions include every record the rule keeps it at. -/
theorem settled_demandsNoMore (ι : Fin d → Finset W) (w : Requirement W) (XA XAY : Fin d)
    (c : ℚ) (hc : c ≤ w.c) (hA : ι XA = w.A) (hAY : ι XAY = w.A ∩ w.Y)
    (hU : ∀ F : Settlement d, settleOutcome F (.strength XA XAY c) = .kept → recEvent ι F ∈ w.U) :
    DemandsNoMore ι w (settled (.strength XA XAY c)) := by
  rw [demandsNoMore_iff]
  intro μ hmod F hpos r hr
  unfold settled at hr
  split_ifs at hr with hk
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [specialize_sat_iff F _ (prices_pinned ι F hpos), Form.strength_sat_iff]
    show c * post μ (recEvent ι F) (ι XA) ≤ post μ (recEvent ι F) (ι XAY)
    rw [hA, hAY]
    have hpA : 0 ≤ post μ (recEvent ι F) w.A := div_nonneg (mass_nonneg hmod.1 _) hpos.le
    rcases (mass_nonneg hmod.1 (w.A ∩ recEvent ι F)).lt_or_eq with hApos | hA0
    · have hrow : RowValid μ w.A w.Y w.c (recEvent ι F) :=
        robust_sound hmod.2 (hU F hk) hpos hApos
      exact (mul_le_mul_of_nonneg_right hc hpA).trans hrow
    · have h0 : post μ (recEvent ι F) w.A = 0 := by unfold post; rw [← hA0, zero_div]
      rw [h0, mul_zero]
      exact div_nonneg (mass_nonneg hmod.1 _) hpos.le
  · simp at hr

/-- **The plain row demands more** wherever a model gives the antecedent positive posterior at
a record that settles the consequent false: there the row contraposes. -/
theorem plain_demandsMore (ι : Fin d → Finset W) (w : Requirement W) (XA XAY : Fin d) (c : ℚ)
    (hc : 0 < c) (μ : W → ℚ) (hmod : w.Models μ) (F : Settlement d)
    (hpin : F.val XAY = some false) (hpos : 0 < mass μ (recEvent ι F))
    (hA : 0 < mass μ (ι XA ∩ recEvent ι F)) :
    ¬ DemandsNoMore ι w (plain (.strength XA XAY c)) := by
  rw [demandsNoMore_iff]
  intro h
  have hsat := h μ hmod F hpos _ (List.mem_singleton_self _)
  have hle := strength_contraposes F XA XAY c hc hpin _ (prices_pinned ι F hpos) hsat
  have hp : 0 < prices μ ι (recEvent ι F) XA := div_pos hA hpos
  linarith

end General

/-! ## 4. The fixture: the eight-world model, the fragment `(A, A∧Y, C)` -/

/-- The interpretation of the fragment: the signal, the signal with the quantity, the contrary
challenge. -/
def ι : Fin 3 → Finset World := ![Aev, Aev ∩ Yev, Cev]

theorem μ_nonneg : ∀ w, 0 ≤ μ w := by
  intro w
  unfold μ
  split_ifs <;> norm_num

/-- The requirement over the extensions the rebuttal rule keeps the strength form at. -/
def reqKept (c : ℚ) : Requirement World := ⟨Aev, Yev, c, keptExtensions ι (.strength a ay c)⟩

/-- The requirement at `3/4` with the contrary challenge a declared defeater. -/
def reqDef : Requirement World := ⟨Aev, Yev, 3/4, Udef⟩

/-- At every record the rule keeps the form at, `Pr(Y | A ∧ E) ≥ 3/5` on the eight-world
measure. -/
theorem robust_at_kept : ∀ v : Fin 3 → Option Bool,
    settleOutcome ⟨v⟩ (Form.strength a ay (3/5)) = .kept →
      0 < mass μ (Aev ∩ recEvent ι ⟨v⟩) →
        3/5 * mass μ (Aev ∩ recEvent ι ⟨v⟩) ≤ mass μ (Aev ∩ Yev ∩ recEvent ι ⟨v⟩) := by
  decide +kernel

/-- **The eight-world measure is a model of the requirement at `3/5`** over the kept
extensions. -/
theorem μ_models_kept : (reqKept (3/5)).Models μ := by
  refine ⟨μ_nonneg, fun E hE => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hE
  exact robust_at_kept v (Finset.mem_filter.1 hv).2

/-- The eight-world measure is a model of the requirement at `3/4` with the contrary challenge
a defeater. -/
theorem μ_models_def : reqDef.Models μ := ⟨μ_nonneg, (robust_defeated_iff (3/4)).2 le_rfl⟩

/-- **(iii) The row the rebuttal rule keeps is expressed**: the strength row at `3/5` demands
no more than the requirement at `3/5` over the kept extensions. -/
theorem settled_expresses :
    ExpressesNoMore ι settled (reqKept (3/5)) (Form.strength a ay (3/5)) :=
  settled_demandsNoMore ι _ a ay (3/5) le_rfl rfl rfl fun _ h => mem_keptExtensions h

/-- The record at which the consequent `A ∧ Y` is settled false. -/
def Frb : Settlement 3 := ⟨![none, some false, none]⟩

theorem mass_rec_Frb : mass μ (recEvent ι Frb) = 5/8 := by decide +kernel
theorem mass_A_rec_Frb : mass μ (ι a ∩ recEvent ι Frb) = 1/8 := by decide +kernel

/-- **(ii) The plain row is not expressed**: against the same requirement it demands more,
because at the record settling the consequent false it forces the antecedent to zero while the
eight-world measure, a model of the requirement, prices it at `1/5`. -/
theorem plain_not_expresses :
    ¬ ExpressesNoMore ι plain (reqKept (3/5)) (Form.strength a ay (3/5)) :=
  plain_demandsMore ι _ a ay (3/5) (by norm_num) μ μ_models_kept Frb rfl
    (by rw [mass_rec_Frb]; norm_num) (by rw [mass_A_rec_Frb]; norm_num)

/-- The conflict: `5/3` of the plain row at the rebutting record, `3/5 · P(A) ≤ 0`, and the
row `P(A) ≥ 1/5`. -/
def contraCert : FarkasCert 3 2 where
  mult := ![5/3, 1]
  row := ![specialize Frb (Form.strength a ay (3/5)).row, (Form.premise a (1/5)).row]
  mult_nonneg := fun i => by fin_cases i <;> norm_num
  coeff_sum := fun j => by
    fin_cases j <;>
      simp [Fin.sum_univ_two, specialize, Frb, Form.row, a, ay] <;> norm_num
  const_sum := by
    simp [Fin.sum_univ_two, specialize, settledTerm, Frb, Form.row, Fin.sum_univ_three, truth,
      a, ay]

/-- **Contraposition as a statement about expression**: `P(A) ≥ 1/5` is incompatible with the
plain row at the rebutting record, by `contraCert`, and compatible with the requirement there. -/
theorem contraposition_as_expression :
    Incompatible (plain (Form.strength a ay (3/5)) Frb ++ [(Form.premise a (1/5)).row]) ∧
      ¬ ReqIncompatible (reqKept (3/5)) ι Frb [(Form.premise a (1/5)).row] := by
  refine ⟨⟨2, contraCert, fun i => Or.inl ?_⟩, fun h => h ⟨μ, μ_models_kept, ?_, ?_⟩⟩
  · fin_cases i <;> simp [contraCert, plain]
  · rw [mass_rec_Frb]; norm_num
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [Form.premise_sat_iff]
    show 1/5 ≤ mass μ (ι a ∩ recEvent ι Frb) / mass μ (recEvent ι Frb)
    rw [mass_rec_Frb, mass_A_rec_Frb]
    norm_num

theorem recEvent_Fch : recEvent ι Fch = Cev := by decide +kernel

theorem prices_Fch : prices μ ι Cev = postC := by
  rw [postC_eq]
  funext i
  fin_cases i <;> rfl

/-- At the contrary-challenge record the rule keeps the row at `3/4` and the eight-world
measure violates it: the row is expressed under no requirement the measure is a model of. -/
theorem kept_row_violated (w : Requirement World) (hmod : w.Models μ) :
    ¬ DemandsNoMore ι w (settled occ.form) := by
  rw [demandsNoMore_iff]
  intro h
  have hpos : 0 < mass μ (recEvent ι Fch) := by rw [recEvent_Fch, mass_C]; norm_num
  have hsat := h μ hmod Fch hpos (specialize Fch occ.form.row) (by
    unfold settled
    rw [if_pos kept_under_challenge.1]
    exact List.mem_singleton_self _)
  rw [recEvent_Fch, prices_Fch] at hsat
  exact contributed_row_invalid hsat

/-- The row at `3/4` is not expressed against the requirement at `3/5`. -/
theorem stronger_not_expresses : ¬ ExpressesNoMore ι settled (reqKept (3/5)) occ.form :=
  kept_row_violated _ μ_models_kept

/-- **The kept row demands more than the warrant with a declared defeater**: against the
requirement at `3/4` whose undefeated extensions exclude the contrary challenge, the row the
rebuttal rule keeps at the challenge record is not expressed. -/
theorem defeater_not_expressed : ¬ ExpressesNoMore ι settled reqDef occ.form :=
  kept_row_violated _ μ_models_def

/-! ### (i) The entitlement -/

/-- The occurrence carrying the strength row at `3/5`. -/
def occ35 : Occurrence 3 := ⟨1, Form.strength a ay (3/5), .none, .party 1, ∅⟩

/-- The anchors: the first obligation's requirement is the warrant at `3/5` over the kept
extensions, the second's the warrant at `3/4` with the contrary challenge a defeater. -/
def anchorW : Fin 2 → Requirement World := ![reqKept (3/5), reqDef]

/-- The protocol over requirements, everything else authenticated. -/
def protocolW : Protocol.{0, 0, 0} (Fin 2) (Requirement World) where
  Resolution _ := Unit
  Settlement := Unit
  Warrant := Unit
  Admitted _ _ _ := True
  Live _ _ _ := True
  Authorized _ _ := True
  AnswerOK _ _ _ := True
  SetView _ _ := True
  Closes _ _ _ _ := True
  answer_resolves _ _ _ _ := ()
  closure_resolves _ _ _ _ _ _ := ()

/-- The protocol with admission by standing under the allocation `J₀`. -/
def protocolWS : Protocol.{0, 0, 0} (Fin 2) (Requirement World) :=
  withStanding protocolW (fun _ => J₀) id issuer

/-- Both obligations exposed on their own ports, each demanding its anchor. -/
def startW : Boundary (Fin 2) (Requirement World) := ⟨[0], Finset.univ, 2, anchorW⟩

def initialW : Initial protocolWS anchorW startW where
  admitted _ _ := rfl
  port o _ := o
  anchored _ _ := rfl
  credential _ _ := trivial

/-- The accounted state. -/
def stateW : ObligationState protocolWS anchorW := initialW.state

theorem account_liveW (e : Fin 2) (h : e ∈ stateW.boundary.exposed) :
    OccurrenceIntegrity.Fate.live ∈ (stateW.account e h).fates := by
  simp [stateW, Initial.state, Initial.accounted, initialW, Program.fates]

/-- **(i) The entitlement, with `Expresses` carrying content**: the occurrence at `3/5` traces
to the first obligation — exposed, admitted by the allocation, its account live — and its form
under the rebuttal rule demands no more than that obligation's anchored requirement. -/
def entitlementW : Entitlement stateW [occ35] (ExpressesNoMore ι settled) where
  origin _ := 0
  origin_exposed _ _ := by simp [stateW, Initial.state, startW]
  admitted _ _ := rfl
  live _ _ := account_liveW _ _
  faithful o ho := by
    have h : o = occ35 := by simpa using ho
    subst h
    exact settled_expresses

/-- **Under the plain rule there is no entitlement** of the same grounds over the same state:
the plain row demands more than either anchored requirement. -/
theorem no_entitlement_plain (E : Entitlement stateW [occ35] (ExpressesNoMore ι plain)) :
    False := by
  have hf := E.faithful occ35 (by simp)
  have hno : ∀ e : Fin 2, ¬ ExpressesNoMore ι plain (anchorW e) occ35.form := by
    intro e
    fin_cases e
    · exact plain_not_expresses
    · exact plain_demandsMore ι _ a ay (3/5) (by norm_num) μ μ_models_def Frb rfl
        (by rw [mass_rec_Frb]; norm_num) (by rw [mass_A_rec_Frb]; norm_num)
  exact hno _ hf

/-- **The warrant at `3/4` has no entitlement** over this state under the rebuttal rule: its
kept row is expressed under neither anchored requirement. -/
theorem no_entitlement_at_three_quarters
    (E : Entitlement stateW groundsCh (ExpressesNoMore ι settled)) : False := by
  have hf := E.faithful occ (by simp [groundsCh])
  have hno : ∀ e : Fin 2, ¬ ExpressesNoMore ι settled (anchorW e) occ.form := by
    intro e
    fin_cases e
    · exact stronger_not_expresses
    · exact defeater_not_expressed
  exact hno _ hf

/-- **Entitlement discriminates by expression**: over one accounted state, with both
obligations exposed, admitted by the allocation and live, the row at `3/5` under the rebuttal
rule has an entitlement, the same row under the plain rule has none, and the row at `3/4` under
the rebuttal rule has none. -/
theorem entitlement_discriminates :
    Nonempty (Entitlement stateW [occ35] (ExpressesNoMore ι settled)) ∧
      IsEmpty (Entitlement stateW [occ35] (ExpressesNoMore ι plain)) ∧
      IsEmpty (Entitlement stateW groundsCh (ExpressesNoMore ι settled)) :=
  ⟨⟨entitlementW⟩, ⟨no_entitlement_plain⟩, ⟨no_entitlement_at_three_quarters⟩⟩

/-! ### The two strengths differ -/

/-- The background at a record: its pins and the coherence row `P(A∧Y) ≤ P(A)`. -/
def bg : Content 3 := fun F => F.pinRows ++ [⟨![-1, 1, 0], 0⟩]

theorem recEvent_empty : recEvent ι (Settlement.empty 3) = univ := by decide +kernel

/-- **A weaker row demands no more and does not have the same role**: the strength row at
`1/2` against the requirement at `3/5`.  The list `P(A) ≥ 1`, `P(A∧Y) ≤ 1/2` is incompatible
with the requirement at the bare record and compatible with the row and the background. -/
theorem weaker_noMore_not_same :
    DemandsNoMore ι (reqKept (3/5)) (settled (Form.strength a ay (1/2))) ∧
      ¬ SameRole ι (reqKept (3/5)) bg (settled (Form.strength a ay (1/2))) := by
  refine ⟨settled_demandsNoMore ι _ a ay (1/2) (by norm_num [reqKept]) rfl rfl
    (fun F h => mem_keptExtensions (by simpa [settleOutcome] using h)), fun h => ?_⟩
  have hreq : ReqIncompatible (reqKept (3/5)) ι (Settlement.empty 3)
      [(Form.premise a 1).row, boundRow ay 1 (1/2)] := by
    rintro ⟨μ', hmod, hpos, hX⟩
    rw [recEvent_empty] at hpos hX
    have h1 := hX (Form.premise a 1).row (by simp)
    have h2 := hX (boundRow ay 1 (1/2)) (by simp)
    rw [Form.premise_sat_iff] at h1
    rw [boundRow_sat] at h2
    have h1' : mass μ' univ ≤ mass μ' (Aev ∩ univ) := by
      have : (1 : ℚ) ≤ mass μ' (Aev ∩ univ) / mass μ' univ := h1
      rwa [le_div_iff₀ hpos, one_mul] at this
    have h2' : mass μ' (Aev ∩ Yev ∩ univ) ≤ 1/2 * mass μ' univ := by
      have : 1 * (mass μ' (Aev ∩ Yev ∩ univ) / mass μ' univ) ≤ 1/2 := h2
      rwa [one_mul, div_le_iff₀ hpos] at this
    have hU : (univ : Finset World) ∈ (reqKept (3/5)).U := by
      rw [← recEvent_empty]
      exact mem_keptExtensions (by decide)
    have hrob := hmod.2 univ hU (lt_of_lt_of_le hpos h1')
    have hrob' : 3/5 * mass μ' (Aev ∩ univ) ≤ mass μ' (Aev ∩ Yev ∩ univ) := hrob
    linarith
  have hinc := (h (Settlement.empty 3) _).2 hreq
  rw [incompatible_iff_not_feasible] at hinc
  exact hinc ⟨![1, 1/2, 0], by decide +kernel, by decide +kernel⟩

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.ExpressesByRole.plain
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.settled
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.settled_eq_settleForm
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mass_empty
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mass_nonneg
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mass_mono
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.recEvent
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.prices
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.prices_inCube
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.prices_pinned
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.pointRows
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.pointRows_sat_iff
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.Requirement
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.Requirement.Models
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.ReqIncompatible
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.DemandsNoMore
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.SameRole
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.Holds
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.demandsNoMore_iff
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.incompatible_mono
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.SameRole.demandsNoMore
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.ExpressesNoMore
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.ExpressesSame
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.models_null_at_rebuttal
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.keptExtensions
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mem_keptExtensions
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.settled_demandsNoMore
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.plain_demandsMore
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.ι
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.μ_nonneg
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.reqKept
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.reqDef
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.robust_at_kept
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.μ_models_kept
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.μ_models_def
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.settled_expresses
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.Frb
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mass_rec_Frb
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.mass_A_rec_Frb
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.plain_not_expresses
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.contraCert
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.contraposition_as_expression
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.recEvent_Fch
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.prices_Fch
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.kept_row_violated
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.stronger_not_expresses
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.defeater_not_expressed
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.occ35
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.anchorW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.protocolW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.protocolWS
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.startW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.initialW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.stateW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.account_liveW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.entitlementW
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.no_entitlement_plain
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.no_entitlement_at_three_quarters
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.entitlement_discriminates
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.bg
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.recEvent_empty
#print axioms Workspace.Normativity.Contrib.ExpressesByRole.weaker_noMore_not_same

end Workspace.Normativity.Contrib.ExpressesByRole
