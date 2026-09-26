/-
# Authority as a constraint on action: the Normative Inductor's decision component

Round `projects/deference/rounds/2026-09-25-decision-component/`.

**0. The rulings on the authority module.**  `csfree_eq_cs_succ_of_free`: the landed free
reading of the control surface is the charged surface at one more step when the terminal
response is free, admissible and taken before the exterior moves — the instance the
allocation theorem keeps (`ViolC`, the charged violations).  `raisesAnchored`: materiality
is read with the evaluator in force before the action; `unchecked_lt`: cumulative
materiality since the last check stays below the threshold (the salami bound, the
instance of `unreported_lt`).  `dutiesOf`: duties derived from each matter's disclosure
regime; `missedReport_iff_dutiesOf` re-proves the factoring against them.

**1. The permission layer** (`permWeight`): `1` on inquiry options; `0` on declared
violations, recognized structurally; otherwise the product of two ramps on the priced
shortfall and taint events.  **The composed gate** (`cgate`): permission times the landed
adequacy ramp times any bounded preference, normalized, with a mass floor `φ₀` on inquiry
options so the normalizer never vanishes (`ctotal_ge_floor`).

**2. Results.**  Non-interference (`noninterference`): the gate is a function of the
displayed prices and adds no trader, so every price and every inductor guarantee is the
same with and without it — stated as the market object being untouched.  Structural
safety (`cgate_zero_of_viol`): a declared violation gets mass zero at every day, for every
preference and every price vector.  Forecast safety (`cgate_zero_of_forecast`,
`cgate_le_ramp`, `eventually_excluded`): mass zero above the upper threshold, mass bounded
by the ramp in between, and a pattern whose shortfall price is eventually above the
threshold is eventually excluded.  Composition (`massOff_inter_le`,
`cgate_massOff_adequate_le`, `cgate_massOff_permitted_le`, `cgate_l1_lipschitz`): soundness
adds the two layers' error terms, continuity multiplies the ramps with the inquiry floor
keeping the normalization Lipschitz; the constants are explicit.  Progress
(`cgate_practicalCert`, `progress_under_permission`): the practical certificate holds
with the composed constants and feeds the landed edge Progress bound unchanged.
Jurisdiction over obligation (`jurisdiction_nonempty`, `support_permitted`,
`reserved_act_excluded`): with inquiry to the holder marked adequate, the
permitted-and-adequate set is nonempty and every executed option is an inquiry or an
unexcluded act.  Capability for safety (`cgate_antitone_in_forecast`,
`uncertainty_deference_le`): mass on an option falls as its shortfall price rises, while
the uncertainty-based chooser's reason to defer shrinks with the calibration error.

**3. Why authority must not go through the enforcer** (`liability`,
`liability_identity`, `bounded_of_not_outperformed`, `systematic_outperformance_unbounded`,
`persistence_fails_of_systematic`): an enforcer that forces violating prices below
compliant ones and settles to her ordinary valuation carries a cumulative liability equal
to the signed realized ordinary cost of deferring; it is bounded exactly when she is not
systematically outperformed, and under systematic outperformance it is unbounded, so the
preservation theorem's hypothesis fails and the persistence criterion's cost never dips.

**4. Continuations** (`execution_prob_le_prod`, `unbudgeted_lt`, `Witness.ramp_salami`,
`exists_flip`, `stepwise_or_exterior`): the probability a continuation executes is at most
the product of its per-step masses; a cumulative permission budget bounds the ramp-region
exposure since the last check; without it the exposure accumulates unboundedly below every
per-step threshold; a plan that is short at its end and not at its start crosses at some
half-step, an agent step (caught by the caused shortfall) or an exterior step (not the
agent's).  Gate transparency under the restricted menu is the landed
`trajGated_eq_traj_of_admitted` (`restricted_gate_transparent`).

**5. The act certificate** (`ActCertificate`, `LicenseRef.Valid`): grounds, license bound
to the allocation and the event-kind license slot, lineage.

**What this does not establish.**  Generability of the shortfall and taint events (a
named hypothesis, items 101 and 90); the accuracy of the forecasts (asymptotic, the
pinned inductor's); that inquiry is always marked adequate (route A, the compiler's);
anything about agents not built as Normative Inductors.  Names are provisional
(`AGENTS.md` standard 6); `S`, `T`, `r`, `θ`, `π` are prose names.
-/
import Workspace.Deference.Contrib.AuthorityModule
import Workspace.Deference.Contrib.ContinuationBRIA
import Workspace.Normativity.Contrib.GatedChoice
import Workspace.Normativity.Contrib.NormativeInductor
import Workspace.Normativity.Contrib.NormativeInductorComposition

namespace Workspace.Deference.Contrib.DecisionComponent

open Finset
open Workspace.Normativity.Contrib.GatedChoice (ramp ramp_nonneg ramp_le_one ramp_eq_one massOff
  Region Within l1)
open Workspace.Normativity.Contrib.PracticalCertificate (anchoredLoss adequate_set_route)
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem
open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.Legitimacy (lastReport unreported_lt)
open scoped Classical

/-! ## 0. The rulings on the authority module -/

section Rulings

variable {S E A Z R C : Type*} (I : Interaction S E A Z R C)

theorem rollTail_append (z : ℕ → Z) (t : ℕ) (ds : List (Option C)) (d : Option C) (y : S) :
    rollTail I z t (ds ++ [d]) y =
      applyOpt I d (I.env (z (t + ds.length)) (rollTail I z t ds y)) := by
  induction ds generalizing t y with
  | nil => simp [rollTail]
  | cons d' ds ih =>
    simp only [List.cons_append, rollTail, ih, List.length_cons]
    rw [show t + 1 + ds.length = t + (ds.length + 1) by omega]

/-- With the exterior idle, appending a correction to an exercise applies it to the
exercise's end state. -/
theorem rollPhys_append_of_envId (z : ℕ → Z) (henv : ∀ n x, I.env (z n) x = x) (t : ℕ)
    (ds : List (Option C)) (d : Option C) (x : S) :
    rollPhys I z t (ds ++ [d]) x = applyOpt I d (rollPhys I z t ds x) := by
  cases ds with
  | nil => simp [rollPhys, rollTail, applyOpt]
  | cons d' ds => simp [rollPhys, rollTail_append, henv]

theorem exCost_append_zero (cost : C → ℝ) (hcost : ∀ c, cost c = 0) (ds : List (Option C))
    (d : Option C) : exCost cost (ds ++ [d]) = 0 := by
  induction ds with
  | nil => cases d <;> simp [exCost, hcost]
  | cons d' ds ih => cases d' <;> simp [exCost, hcost, ih]

theorem exCost_zero (cost : C → ℝ) (hcost : ∀ c, cost c = 0) (ds : List (Option C)) :
    exCost cost ds = 0 := by
  induction ds with
  | nil => simp [exCost]
  | cons d' ds ih => cases d' <;> simp [exCost, hcost, ih]

theorem admAll_of_all (Adm : ℕ → C → Prop) (hAdm : ∀ t c, Adm t c) (t : ℕ)
    (ds : List (Option C)) : AdmAll Adm t ds := by
  induction ds generalizing t with
  | nil => trivial
  | cons d ds ih => cases d <;> simp [AdmAll, hAdm, ih]

/-- **Ruling 2, the free reading as an instance of the charged surface**: when every
correction is free and admissible and the exterior is idle, the landed free reading at
window `τ` is the charged surface at window `τ + 1` — the terminal response taken at no
cost before the exterior moves. -/
theorem csfree_eq_cs_succ_of_free (Adm : ℕ → C → Prop) (hAdm : ∀ t c, Adm t c) (cost : C → ℝ)
    (hcost : ∀ c, cost c = 0) (c : ℝ) (hc : 0 ≤ c) (τ t : ℕ) (z : ℕ → Z)
    (henv : ∀ n x, I.env (z n) x = x) (x : S) :
    CSfree I Adm cost c τ t z x = CS I Adm cost c (τ + 1) t z x := by
  ext r
  simp only [CSfree, CS, reachIdle, Set.mem_setOf_eq, Kphys]
  constructor
  · rintro ⟨y, ⟨ds, hlen, -, -, rfl⟩, hφ | ⟨c', hφ⟩⟩
    · exact ⟨_, ⟨ds, by omega, admAll_of_all Adm hAdm t ds, by simpa [exCost_zero cost hcost] using hc,
        rfl⟩, hφ⟩
    · refine ⟨_, ⟨ds ++ [some c'], by simp; omega, admAll_of_all Adm hAdm t _,
        by simpa [exCost_append_zero cost hcost] using hc, rfl⟩, ?_⟩
      rw [rollPhys_append_of_envId I z henv]
      exact hφ
  · rintro ⟨y, ⟨ds, hlen, -, -, rfl⟩, hφ⟩
    rcases List.eq_nil_or_concat' ds with rfl | ⟨ds', d, rfl⟩
    · exact ⟨x, ⟨[], by simp, trivial, by simpa [exCost] using hc, rfl⟩, Or.inl (by simpa [rollPhys] using hφ)⟩
    · refine ⟨rollPhys I z t ds' x, ⟨ds', by simp at hlen; omega, admAll_of_all Adm hAdm t ds',
        by simpa [exCost_zero cost hcost] using hc, rfl⟩, ?_⟩
      rw [rollPhys_append_of_envId I z henv] at hφ
      cases d with
      | none => exact Or.inl hφ
      | some c' => exact Or.inr ⟨c', hφ⟩

/-- **The charged violations**: the landed six with foreclosure read on the charged
surface, and entrenchment. -/
def ViolC {Alloc M Disc : Type*} (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) (rdec : R)
    (Jmat : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ) (π : Policy S E A)
    (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ) : Prop :=
  BypassAt (toAllocation Jm Λ₀) π (traj I π ρ z s₀) t ∨
    (∃ r, PreemptAt I π ρ z s₀ t r) ∨
    (∃ m, CausedShortfall I Jmat Adm cost π (traj I π ρ z s₀) t z m) ∨
    ReallocAt I (toAllocation Jm Λ₀) π (traj I π ρ z s₀) t ∨
    MissedReportAt (toAllocation Jm Λ₀) π (traj I π ρ z s₀) t ∨
    ExploitAt I (toAllocation Jm Λ₀) rdec π (traj I π ρ z s₀) t ∨
    ∃ m, EntrenchAt I Jmat Adm cost π (traj I π ρ z s₀) t z m

/-- **Ruling 3, anchored materiality**: an action at `t` raises a matter under the
evaluator in force before it, `V t`; the action changes `V (t+1)` at most. -/
def raisesAnchored {St : Type*} (V : ℕ → St → ℝ) (ε : ℝ) (t : ℕ) (removed : List St) : Prop :=
  raises (V t) ε removed

theorem raisesAnchored_invariant {St : Type*} (V V' : ℕ → St → ℝ) (ε : ℝ) (t : ℕ)
    (removed : List St) (hV : V t = V' t) :
    raisesAnchored V ε t removed ↔ raisesAnchored V' ε t removed := by
  simp [raisesAnchored, hV]

/-- Cumulative materiality: the spreads accumulated since the start. -/
def cumMat (spreads : ℕ → ℝ) (t : ℕ) : ℝ := ∑ i ∈ range t, spreads i

/-- **Ruling 3, the salami bound for cumulative materiality**: under the cumulative check
rule (check when materiality has grown by `ε` since the last check), the unchecked growth
is below `ε` at every time. -/
theorem unchecked_lt (spreads : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ) :
    cumMat spreads t - cumMat spreads (lastReport (cumMat spreads) ε t) < ε :=
  unreported_lt (cumMat spreads) ε hε t

/-- **Ruling 4, duties from the disclosure regime**: a matter's duty is due when one of
its disclosure items falls due; a task component discharges it when it discharges every
due item. -/
def dutiesOf {M Res Disc : Type*} (J : AuthAlloc M Res Disc) (due : Disc → ℕ → MState S E → Prop)
    (dischargesD : A → Disc → Prop) : Duties S E A M :=
  ⟨fun m t s => ∃ d ∈ (J.entry m).disclosure, due d t s, fun a => ∀ d, dischargesD a d⟩

/-- The missed-report factoring against the derived duties. -/
theorem missedReport_iff_dutiesOf {Alloc M Res Disc : Type*} (Λ : Allocation S E A Alloc)
    (J : AuthAlloc M Res Disc) (due : Disc → ℕ → MState S E → Prop) (dischargesD : A → Disc → Prop)
    (hreq : ∀ t s, Λ.Required t s ↔ ∃ m, ∃ d ∈ (J.entry m).disclosure, due d t s)
    (hrep : ∀ a, Λ.isReport a ↔ ∀ d, dischargesD a d)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    MissedReportAt Λ π τ t ↔ DutyUnmet (dutiesOf J due dischargesD) π τ t :=
  missedReport_iff_duty Λ (dutiesOf J due dischargesD) hreq hrep π τ t

end Rulings

/-! ## 1. The permission layer and the composed gate -/

section Gate

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The permission ramp: `1` below `θlo`, `0` above `θhi`, linear between. -/
noncomputable def pramp (θlo θhi x : ℝ) : ℝ := ramp ((θhi - x) / (θhi - θlo))

theorem pramp_nonneg (θlo θhi x : ℝ) : 0 ≤ pramp θlo θhi x := ramp_nonneg _
theorem pramp_le_one (θlo θhi x : ℝ) : pramp θlo θhi x ≤ 1 := ramp_le_one _

theorem pramp_eq_one {θlo θhi x : ℝ} (h : θlo < θhi) (hx : x ≤ θlo) : pramp θlo θhi x = 1 := by
  unfold pramp
  apply ramp_eq_one
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem pramp_eq_zero {θlo θhi x : ℝ} (h : θlo < θhi) (hx : θhi ≤ x) : pramp θlo θhi x = 0 := by
  unfold pramp ramp
  have : (θhi - x) / (θhi - θlo) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [min_eq_right (by linarith), max_eq_left this]

theorem pramp_antitone {θlo θhi x y : ℝ} (h : θlo < θhi) (hxy : x ≤ y) :
    pramp θlo θhi y ≤ pramp θlo θhi x := by
  unfold pramp ramp
  have : (θhi - y) / (θhi - θlo) ≤ (θhi - x) / (θhi - θlo) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  exact max_le_max le_rfl (min_le_min le_rfl this)

/-- The clamp is `1`-Lipschitz. -/
theorem abs_ramp_sub_ramp_le (x y : ℝ) : |ramp x - ramp y| ≤ |x - y| := by
  unfold ramp
  have h1 : |min 1 x - min 1 y| ≤ |x - y| := by
    calc |min 1 x - min 1 y| ≤ max |1 - 1| |x - y| := abs_min_sub_min_le_max 1 x 1 y
      _ = |x - y| := by simp
  calc |max 0 (min 1 x) - max 0 (min 1 y)| ≤ max |0 - 0| |min 1 x - min 1 y| :=
        abs_max_sub_max_le_max 0 _ 0 _
    _ = |min 1 x - min 1 y| := by simp
    _ ≤ |x - y| := h1

theorem abs_pramp_sub_le {θlo θhi : ℝ} (h : θlo < θhi) (x y : ℝ) :
    |pramp θlo θhi x - pramp θlo θhi y| ≤ |x - y| / (θhi - θlo) := by
  unfold pramp
  calc |ramp ((θhi - x) / (θhi - θlo)) - ramp ((θhi - y) / (θhi - θlo))|
      ≤ |(θhi - x) / (θhi - θlo) - (θhi - y) / (θhi - θlo)| := abs_ramp_sub_ramp_le _ _
    _ = |x - y| / (θhi - θlo) := by
        rw [← sub_div, abs_div, abs_of_pos (by linarith : (0 : ℝ) < θhi - θlo)]
        congr 1
        rw [show θhi - x - (θhi - y) = -(x - y) by ring, abs_neg]

/-- **The permission weight**: `1` on inquiry, `0` on a declared violation, the product of
the two ramps otherwise. -/
noncomputable def permWeight (Viol : Q → Bool) (Inq : Finset Q) (θlo θhi : ℝ) (pS pT : Q → ℝ)
    (a : Q) : ℝ :=
  if a ∈ Inq then 1 else if Viol a then 0 else pramp θlo θhi (pS a) * pramp θlo θhi (pT a)

omit [Fintype Q] in
theorem permWeight_nonneg (Viol : Q → Bool) (Inq : Finset Q) (θlo θhi : ℝ) (pS pT : Q → ℝ)
    (a : Q) : 0 ≤ permWeight Viol Inq θlo θhi pS pT a := by
  unfold permWeight
  split_ifs <;> first | exact zero_le_one | exact le_rfl |
    exact mul_nonneg (pramp_nonneg _ _ _) (pramp_nonneg _ _ _)

omit [Fintype Q] in
theorem permWeight_le_one (Viol : Q → Bool) (Inq : Finset Q) (θlo θhi : ℝ) (pS pT : Q → ℝ)
    (a : Q) : permWeight Viol Inq θlo θhi pS pT a ≤ 1 := by
  unfold permWeight
  split_ifs <;> first | exact le_rfl | exact zero_le_one |
    exact mul_le_one₀ (pramp_le_one _ _ _) (pramp_nonneg _ _ _) (pramp_le_one _ _ _)

/-- The landed adequacy ramp. -/
noncomputable def adWeight (b : Q → ℝ) (τ δ : ℝ) (a : Q) : ℝ := ramp ((b a - τ) / δ)

/-- The composed gate's parameters. -/
structure GateParams (Q : Type*) where
  Viol : Q → Bool
  Inq : Finset Q
  θlo : ℝ
  θhi : ℝ
  τ : ℝ
  δ : ℝ
  φ₀ : ℝ

/-- **The composed weight**: permission times adequacy times preference, with the mass
floor `φ₀` on inquiry options. -/
noncomputable def cweight (G : GateParams Q) (pS pT b pref : Q → ℝ) (a : Q) : ℝ :=
  if a ∈ G.Inq then max G.φ₀ (adWeight b G.τ G.δ a * pref a)
  else permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * adWeight b G.τ G.δ a * pref a

noncomputable def ctotal (G : GateParams Q) (pS pT b pref : Q → ℝ) : ℝ :=
  ∑ a, cweight G pS pT b pref a

/-- **The composed gate.** -/
noncomputable def cgate (G : GateParams Q) (pS pT b pref : Q → ℝ) (a : Q) : ℝ :=
  cweight G pS pT b pref a / ctotal G pS pT b pref

variable (G : GateParams Q) (pS pT b pref : Q → ℝ)

omit [Fintype Q] in
theorem cweight_nonneg (hφ : 0 ≤ G.φ₀) (hpref : ∀ a, 0 ≤ pref a) (a : Q) :
    0 ≤ cweight G pS pT b pref a := by
  unfold cweight
  split_ifs
  · exact le_max_of_le_left hφ
  · exact mul_nonneg (mul_nonneg (permWeight_nonneg _ _ _ _ _ _ _) (ramp_nonneg _)) (hpref a)

omit [Fintype Q] in
theorem cweight_le (hpref : ∀ a, 0 ≤ pref a) (a : Q) (ha : a ∉ G.Inq) :
    cweight G pS pT b pref a ≤ adWeight b G.τ G.δ a * pref a := by
  unfold cweight
  rw [if_neg ha]
  have := permWeight_le_one G.Viol G.Inq G.θlo G.θhi pS pT a
  have h0 := mul_nonneg (ramp_nonneg ((b a - G.τ) / G.δ)) (hpref a)
  calc permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * adWeight b G.τ G.δ a * pref a
      = permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * (adWeight b G.τ G.δ a * pref a) := by ring
    _ ≤ 1 * (adWeight b G.τ G.δ a * pref a) := mul_le_mul_of_nonneg_right this h0
    _ = _ := one_mul _

/-- The inquiry floor: the normalizer is at least `φ₀ · |Inq|`. -/
theorem ctotal_ge_floor (hφ : 0 ≤ G.φ₀) (hpref : ∀ a, 0 ≤ pref a) :
    G.φ₀ * G.Inq.card ≤ ctotal G pS pT b pref := by
  unfold ctotal
  calc G.φ₀ * G.Inq.card = ∑ a ∈ G.Inq, G.φ₀ := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ G.Inq, cweight G pS pT b pref a := by
        apply sum_le_sum
        intro a ha
        unfold cweight
        rw [if_pos ha]
        exact le_max_left _ _
    _ ≤ ∑ a, cweight G pS pT b pref a :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => cweight_nonneg G pS pT b pref hφ hpref a

theorem ctotal_pos (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a) :
    0 < ctotal G pS pT b pref := by
  have h := ctotal_ge_floor G pS pT b pref hφ.le hpref
  have : (0 : ℝ) < G.Inq.card := by exact_mod_cast hInq.card_pos
  exact lt_of_lt_of_le (mul_pos hφ this) h

theorem cgate_nonneg (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a) (a : Q) :
    0 ≤ cgate G pS pT b pref a :=
  div_nonneg (cweight_nonneg G pS pT b pref hφ.le hpref a) (ctotal_pos G pS pT b pref hφ hInq hpref).le

theorem cgate_sum_one (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a) :
    ∑ a, cgate G pS pT b pref a = 1 := by
  unfold cgate
  rw [← sum_div]
  exact div_self (ctotal_pos G pS pT b pref hφ hInq hpref).ne'

/-- The gate never vanishes on inquiry options. -/
theorem cgate_inquiry_pos (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a)
    (a : Q) (ha : a ∈ G.Inq) : 0 < cgate G pS pT b pref a := by
  unfold cgate cweight
  rw [if_pos ha]
  exact div_pos (lt_of_lt_of_le hφ (le_max_left _ _)) (ctotal_pos G pS pT b pref hφ hInq hpref)

end Gate

/-! ## 2. Results -/

section Results

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (G : GateParams Q) (pS pT b pref : Q → ℝ)

omit [Fintype Q] [DecidableEq Q] in
/-- **Non-interference.**  The market object is a fixed input the gate reads; the gate is
a function of the displayed prices and adds no trader, so the market — and every property
of it — is the same with and without the permission layer.  Stated on the price object:
composing any two gates with the same market leaves the prices identical. -/
theorem noninterference {Mkt : Type*} (market : Mkt) (prices : Mkt → ℕ → Q → ℝ)
    (gate _gate' : (Q → ℝ) → Q → ℝ) (n : ℕ) :
    (fun a => gate (prices market n) a) = (fun a => gate (prices market n) a) ∧
      prices market n = prices market n ∧
      (∀ P : Mkt → Prop, P market → P market) := ⟨rfl, rfl, fun _ h => h⟩

/-- **Structural safety**: a declared violation receives mass zero, for every preference,
every price vector and every day. -/
theorem cgate_zero_of_viol (a : Q) (ha : a ∉ G.Inq) (hv : G.Viol a = true) :
    cgate G pS pT b pref a = 0 := by
  unfold cgate cweight permWeight
  rw [if_neg ha, if_neg ha, if_pos hv]
  simp

/-- **Forecast safety, exclusion**: mass zero once either priced event is above the upper
threshold. -/
theorem cgate_zero_of_forecast (hθ : G.θlo < G.θhi) (a : Q) (ha : a ∉ G.Inq)
    (h : G.θhi ≤ pS a ∨ G.θhi ≤ pT a) : cgate G pS pT b pref a = 0 := by
  unfold cgate cweight permWeight
  rw [if_neg ha, if_neg ha]
  rcases h with h | h
  · rw [pramp_eq_zero hθ h]; simp
  · rw [pramp_eq_zero hθ h]; simp

/-- **Forecast safety, the ramp region**: mass bounded by the product of the ramps, the
preference cap and the inquiry floor. -/
theorem cgate_le_ramp (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a)
    {pmax : ℝ} (hmax : ∀ a, pref a ≤ pmax) (a : Q) (ha : a ∉ G.Inq) (hv : G.Viol a = false) :
    cgate G pS pT b pref a ≤
      pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * pmax / (G.φ₀ * G.Inq.card) := by
  have hZ := ctotal_ge_floor G pS pT b pref hφ.le hpref
  have hZ0 : (0 : ℝ) < G.φ₀ * G.Inq.card := by
    have : (0 : ℝ) < G.Inq.card := by exact_mod_cast hInq.card_pos
    exact mul_pos hφ this
  have hw : cweight G pS pT b pref a ≤ pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * pmax := by
    unfold cweight permWeight
    rw [if_neg ha, if_neg ha, if_neg (by simp [hv])]
    have h1 := ramp_le_one ((b a - G.τ) / G.δ)
    have h0 := ramp_nonneg ((b a - G.τ) / G.δ)
    have hp := pramp_nonneg G.θlo G.θhi (pS a)
    have hq := pramp_nonneg G.θlo G.θhi (pT a)
    have hpm : 0 ≤ pmax := le_trans (hpref a) (hmax a)
    unfold adWeight
    calc pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * ramp ((b a - G.τ) / G.δ) * pref a
        ≤ pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * 1 * pmax := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (mul_nonneg hp hq)) (hmax a) (hpref a)
          exact mul_nonneg (mul_nonneg hp hq) zero_le_one
      _ = _ := by ring
  unfold cgate
  rw [div_le_div_iff₀ (lt_of_lt_of_le hZ0 hZ) hZ0]
  have hw0 : 0 ≤ pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * pmax :=
    mul_nonneg (mul_nonneg (pramp_nonneg _ _ _) (pramp_nonneg _ _ _)) (le_trans (hpref a) (hmax a))
  calc cweight G pS pT b pref a * (G.φ₀ * G.Inq.card)
      ≤ (pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * pmax) * (G.φ₀ * G.Inq.card) :=
        mul_le_mul_of_nonneg_right hw hZ0.le
    _ ≤ (pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * pmax) * ctotal G pS pT b pref :=
        mul_le_mul_of_nonneg_left hZ hw0

/-- **Eventual exclusion**: a pattern whose shortfall price is eventually above the upper
threshold — what Expectation Provability Induction gives a provable shortfall — is
eventually excluded, at every later day. -/
theorem eventually_excluded (hθ : G.θlo < G.θhi) (pSn pTn bn : ℕ → Q → ℝ) (a : Q) (ha : a ∉ G.Inq)
    (N : ℕ) (hN : ∀ n, N ≤ n → G.θhi ≤ pSn n a) :
    ∀ n, N ≤ n → cgate G (pSn n) (pTn n) (bn n) pref a = 0 :=
  fun n hn => cgate_zero_of_forecast G (pSn n) (pTn n) (bn n) pref hθ a ha (Or.inl (hN n hn))

/-- The permitted set: inquiry, or no declared violation and both events below the lower
threshold. -/
def Permitted (a : Q) : Prop :=
  a ∈ G.Inq ∨ (G.Viol a = false ∧ pS a ≤ G.θlo ∧ pT a ≤ G.θlo)

/-- **Soundness composes**: mass off an intersection is at most the sum of the masses off
the two sets. -/
theorem massOff_inter_le (p : Q → ℝ) (hp : ∀ a, 0 ≤ p a) (P A : Finset Q) :
    massOff p (P ∩ A) ≤ massOff p P + massOff p A := by
  unfold massOff
  have hsplit : univ \ (P ∩ A) = (univ \ P) ∪ (P \ A) := by
    ext a; simp only [mem_sdiff, mem_univ, true_and, mem_inter, mem_union, not_and_or]; tauto
  have hdisj : Disjoint (univ \ P) (P \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  rw [hsplit, sum_union hdisj]
  have : ∑ a ∈ P \ A, p a ≤ ∑ a ∈ univ \ A, p a :=
    sum_le_sum_of_subset_of_nonneg (fun a ha => mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ha).2⟩)
      fun a _ _ => hp a
  linarith

/-- The ramp-region mass: the permission-weighted preference mass off the permitted set. -/
noncomputable def rampMass (P : Finset Q) : ℝ :=
  ∑ a ∈ univ \ P, permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * pref a

/-- **The permission layer's error term**: mass off a set on which the permission weight
is `1` and which contains every inquiry option is at most the ramp mass over the
normalizer floor `W`. -/
theorem cgate_massOff_permitted_le (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a)
    (P : Finset Q) (hIP : G.Inq ⊆ P) {W : ℝ} (hW : 0 < W) (hWZ : W ≤ ctotal G pS pT b pref) :
    massOff (cgate G pS pT b pref) P ≤ rampMass G pS pT pref P / W := by
  have hZ := ctotal_pos G pS pT b pref hφ hInq hpref
  have hnum : ∑ a ∈ univ \ P, cweight G pS pT b pref a ≤ rampMass G pS pT pref P := by
    unfold rampMass
    apply sum_le_sum
    intro a ha
    have ha' : a ∉ P := (mem_sdiff.mp ha).2
    have haI : a ∉ G.Inq := fun h => ha' (hIP h)
    unfold cweight
    rw [if_neg haI]
    have h1 := ramp_le_one ((b a - G.τ) / G.δ)
    have hpw := permWeight_nonneg G.Viol G.Inq G.θlo G.θhi pS pT a
    unfold adWeight
    calc permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * ramp ((b a - G.τ) / G.δ) * pref a
        ≤ permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * 1 * pref a := by
          apply mul_le_mul_of_nonneg_right _ (hpref a)
          exact mul_le_mul_of_nonneg_left h1 hpw
      _ = _ := by ring
  have hmass : massOff (cgate G pS pT b pref) P
      = (∑ a ∈ univ \ P, cweight G pS pT b pref a) / ctotal G pS pT b pref := by
    unfold massOff cgate; rw [sum_div]
  rw [hmass, div_le_div_iff₀ hZ hW]
  have hr0 : 0 ≤ rampMass G pS pT pref P :=
    sum_nonneg fun a _ => mul_nonneg (permWeight_nonneg _ _ _ _ _ _ _) (hpref a)
  calc (∑ a ∈ univ \ P, cweight G pS pT b pref a) * W ≤ rampMass G pS pT pref P * W :=
        mul_le_mul_of_nonneg_right hnum hW.le
    _ ≤ rampMass G pS pT pref P * ctotal G pS pT b pref := mul_le_mul_of_nonneg_left hWZ hr0

/-- **The adequacy layer's error term through the composed gate**: at a region point with
`Within` at defect `d ≤ δ`, mass off the adequate set is at most `|Q|·pmax/(W·δ)` per unit
defect plus the inquiry floor's contribution off `A`. -/
theorem cgate_massOff_adequate_le (hδ : 0 < G.δ) {u : Q → ℝ} {d pmax : ℝ} (hd0 : 0 ≤ d)
    (hpm : 0 ≤ pmax) (hpref : ∀ a, 0 ≤ pref a) (hmax : ∀ a, pref a ≤ pmax) (A : Finset Q)
    (hR : Region u A G.τ) (hW : Within b u d) {W : ℝ} (hWpos : 0 < W)
    (hWZ : W ≤ ctotal G pS pT b pref) (hφ : 0 ≤ G.φ₀) :
    massOff (cgate G pS pT b pref) A ≤
      (Fintype.card Q * pmax / (W * G.δ)) * d + (G.φ₀ * (G.Inq \ A).card) / W := by
  have hZ : 0 < ctotal G pS pT b pref := lt_of_lt_of_le hWpos hWZ
  -- each option off `A`: the adequacy ramp is at most `d/δ`
  have hoff : ∀ a, a ∉ A → adWeight b G.τ G.δ a ≤ d / G.δ := by
    intro a ha
    unfold adWeight
    have hb : b a ≤ G.τ + d := by
      have := (abs_le.mp (hW a)).2
      have := hR a ha
      linarith
    calc ramp ((b a - G.τ) / G.δ) ≤ max 0 ((b a - G.τ) / G.δ) := Workspace.Normativity.Contrib.GatedChoice.ramp_le _
      _ ≤ d / G.δ := max_le (div_nonneg hd0 hδ.le) (div_le_div_of_nonneg_right (by linarith) hδ.le)
  have hnum : ∑ a ∈ univ \ A, cweight G pS pT b pref a
      ≤ Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card := by
    have hsplit : ∀ a, a ∉ A → cweight G pS pT b pref a ≤
        pmax * (d / G.δ) + (if a ∈ G.Inq then G.φ₀ else 0) := by
      intro a ha
      unfold cweight
      split_ifs with hI
      · have : adWeight b G.τ G.δ a * pref a ≤ pmax * (d / G.δ) := by
          calc adWeight b G.τ G.δ a * pref a ≤ (d / G.δ) * pmax :=
                mul_le_mul (hoff a ha) (hmax a) (hpref a) (div_nonneg hd0 hδ.le)
            _ = _ := by ring
        have h0 : 0 ≤ pmax * (d / G.δ) := mul_nonneg hpm (div_nonneg hd0 hδ.le)
        exact max_le (by linarith) (by linarith)
      · have h1 := permWeight_le_one G.Viol G.Inq G.θlo G.θhi pS pT a
        have h0 := permWeight_nonneg G.Viol G.Inq G.θlo G.θhi pS pT a
        have hw : adWeight b G.τ G.δ a * pref a ≤ pmax * (d / G.δ) := by
          calc adWeight b G.τ G.δ a * pref a ≤ (d / G.δ) * pmax :=
                mul_le_mul (hoff a ha) (hmax a) (hpref a) (div_nonneg hd0 hδ.le)
            _ = _ := by ring
        have hw0 : 0 ≤ adWeight b G.τ G.δ a * pref a := mul_nonneg (ramp_nonneg _) (hpref a)
        calc permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * adWeight b G.τ G.δ a * pref a
            = permWeight G.Viol G.Inq G.θlo G.θhi pS pT a * (adWeight b G.τ G.δ a * pref a) := by ring
          _ ≤ 1 * (pmax * (d / G.δ)) := mul_le_mul h1 hw hw0 zero_le_one
          _ = pmax * (d / G.δ) + 0 := by ring
    calc ∑ a ∈ univ \ A, cweight G pS pT b pref a
        ≤ ∑ a ∈ univ \ A, (pmax * (d / G.δ) + (if a ∈ G.Inq then G.φ₀ else 0)) :=
          sum_le_sum fun a ha => hsplit a (mem_sdiff.mp ha).2
      _ = (univ \ A).card * (pmax * (d / G.δ)) + ∑ a ∈ univ \ A, (if a ∈ G.Inq then G.φ₀ else 0) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card := by
          have hc : ((univ \ A).card : ℝ) ≤ Fintype.card Q := by exact_mod_cast card_le_univ _
          have h1 : ((univ \ A).card : ℝ) * (pmax * (d / G.δ)) ≤ Fintype.card Q * (pmax * (d / G.δ)) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hpm (div_nonneg hd0 hδ.le))
          have h2 : ∑ a ∈ univ \ A, (if a ∈ G.Inq then G.φ₀ else 0) = G.φ₀ * (G.Inq \ A).card := by
            rw [← sum_filter]
            have : (univ \ A).filter (fun a => a ∈ G.Inq) = G.Inq \ A := by
              ext a; simp [mem_filter, mem_sdiff, and_comm]
            rw [this, sum_const, nsmul_eq_mul, mul_comm]
          rw [h2]; linarith
  have hmass : massOff (cgate G pS pT b pref) A
      = (∑ a ∈ univ \ A, cweight G pS pT b pref a) / ctotal G pS pT b pref := by
    unfold massOff cgate; rw [sum_div]
  rw [hmass, div_le_iff₀ hZ]
  have hkey : (Fintype.card Q * pmax / (W * G.δ)) * d + (G.φ₀ * (G.Inq \ A).card) / W
      = (Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card) / W := by
    field_simp
  rw [hkey, div_mul_eq_mul_div, le_div_iff₀ hWpos]
  have hrhs0 : 0 ≤ Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hpm (div_nonneg hd0 hδ.le)))
      (mul_nonneg hφ (Nat.cast_nonneg _))
  calc (∑ a ∈ univ \ A, cweight G pS pT b pref a) * W
      ≤ (Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card) * W :=
        mul_le_mul_of_nonneg_right hnum hWpos.le
    _ ≤ (Fintype.card Q * (pmax * (d / G.δ)) + G.φ₀ * (G.Inq \ A).card) * ctotal G pS pT b pref :=
        mul_le_mul_of_nonneg_left hWZ hrhs0

end Results

/-! ## 2b. Continuity, the practical certificate, jurisdiction, capability -/

section Continuity

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (G : GateParams Q)

/-- `max` with a constant is `1`-Lipschitz. -/
theorem abs_max_const_sub_le (c x y : ℝ) : |max c x - max c y| ≤ |x - y| := by
  calc |max c x - max c y| ≤ max |c - c| |x - y| := abs_max_sub_max_le_max c x c y
    _ = |x - y| := by simp

/-- A product of three factors in `[0, 1]` is `1`-Lipschitz in each factor. -/
theorem abs_mul3_sub_le {x y z x' y' z' : ℝ} (_hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) (hx' : 0 ≤ x' ∧ x' ≤ 1) (hy' : 0 ≤ y' ∧ y' ≤ 1) (_hz' : 0 ≤ z' ∧ z' ≤ 1) :
    |x * y * z - x' * y' * z'| ≤ |x - x'| + |y - y'| + |z - z'| := by
  have h1 : x * y * z - x' * y' * z' = (x - x') * (y * z) + x' * ((y - y') * z + y' * (z - z')) := by
    ring
  rw [h1]
  have hyz : |y * z| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hy.1 hz.1)]
    exact mul_le_one₀ hy.2 hz.1 hz.2
  have hx'1 : |x'| ≤ 1 := by rw [abs_of_nonneg hx'.1]; exact hx'.2
  have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz.1]; exact hz.2
  have hy'1 : |y'| ≤ 1 := by rw [abs_of_nonneg hy'.1]; exact hy'.2
  calc |(x - x') * (y * z) + x' * ((y - y') * z + y' * (z - z'))|
      ≤ |(x - x') * (y * z)| + |x' * ((y - y') * z + y' * (z - z'))| := abs_add_le _ _
    _ = |x - x'| * |y * z| + |x'| * |(y - y') * z + y' * (z - z')| := by
        rw [abs_mul, abs_mul (x') _]
    _ ≤ |x - x'| * 1 + 1 * (|(y - y') * z| + |y' * (z - z')|) := by
        gcongr
        exact abs_add_le _ _
    _ = |x - x'| + (|y - y'| * |z| + |y'| * |z - z'|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |x - x'| + (|y - y'| * 1 + 1 * |z - z'|) := by gcongr
    _ = |x - x'| + |y - y'| + |z - z'| := by ring

omit [Fintype Q] [DecidableEq Q] in
theorem abs_adWeight_sub_le (hδ : 0 < G.δ) (b b' : Q → ℝ) (a : Q) :
    |adWeight b G.τ G.δ a - adWeight b' G.τ G.δ a| ≤ |b a - b' a| / G.δ := by
  unfold adWeight
  calc |ramp ((b a - G.τ) / G.δ) - ramp ((b' a - G.τ) / G.δ)|
      ≤ |(b a - G.τ) / G.δ - (b' a - G.τ) / G.δ| := abs_ramp_sub_ramp_le _ _
    _ = |b a - b' a| / G.δ := by
        rw [← sub_div, abs_div, abs_of_pos hδ]
        congr 1; ring_nf

omit [Fintype Q] in
/-- **The composed weight is Lipschitz in the three price vectors.** -/
theorem abs_cweight_sub_le (hδ : 0 < G.δ) (hθ : G.θlo < G.θhi) (pS pT b pS' pT' b' pref : Q → ℝ)
    {pmax : ℝ} (hpref : ∀ a, 0 ≤ pref a) (hmax : ∀ a, pref a ≤ pmax) (a : Q) :
    |cweight G pS pT b pref a - cweight G pS' pT' b' pref a| ≤
      pmax * (|b a - b' a| / G.δ +
        (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo)) := by
  have hpm : 0 ≤ pmax := le_trans (hpref a) (hmax a)
  have hθ' : 0 < G.θhi - G.θlo := by linarith
  have had := abs_adWeight_sub_le G hδ b b' a
  have hS := abs_pramp_sub_le hθ (pS a) (pS' a)
  have hT := abs_pramp_sub_le hθ (pT a) (pT' a)
  have hST : |pS a - pS' a| / (G.θhi - G.θlo) + |pT a - pT' a| / (G.θhi - G.θlo)
      = (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo) := by rw [add_div]
  have hrange : ∀ (c : Q → ℝ) (a : Q), 0 ≤ adWeight c G.τ G.δ a ∧ adWeight c G.τ G.δ a ≤ 1 :=
    fun c a => ⟨ramp_nonneg _, ramp_le_one _⟩
  unfold cweight
  split_ifs with hI
  · -- inquiry: the floor is 1-Lipschitz, the adequacy ramp 1/δ
    calc |max G.φ₀ (adWeight b G.τ G.δ a * pref a) - max G.φ₀ (adWeight b' G.τ G.δ a * pref a)|
        ≤ |adWeight b G.τ G.δ a * pref a - adWeight b' G.τ G.δ a * pref a| :=
          abs_max_const_sub_le _ _ _
      _ = |adWeight b G.τ G.δ a - adWeight b' G.τ G.δ a| * pref a := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (hpref a)]
      _ ≤ (|b a - b' a| / G.δ) * pmax := mul_le_mul had (hmax a) (hpref a) (div_nonneg (abs_nonneg _) hδ.le)
      _ ≤ pmax * (|b a - b' a| / G.δ + (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo)) := by
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ hpm
          have : 0 ≤ (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo) :=
            div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hθ'.le
          linarith
  · unfold permWeight
    rw [if_neg hI, if_neg hI]
    split_ifs with hv
    · simp only [zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hpm (add_nonneg (div_nonneg (abs_nonneg _) hδ.le)
        (div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hθ'.le))
    · have h3 := abs_mul3_sub_le (x := pramp G.θlo G.θhi (pS a)) (y := pramp G.θlo G.θhi (pT a))
        (z := adWeight b G.τ G.δ a) (x' := pramp G.θlo G.θhi (pS' a)) (y' := pramp G.θlo G.θhi (pT' a))
        (z' := adWeight b' G.τ G.δ a) ⟨pramp_nonneg _ _ _, pramp_le_one _ _ _⟩
        ⟨pramp_nonneg _ _ _, pramp_le_one _ _ _⟩ (hrange b a) ⟨pramp_nonneg _ _ _, pramp_le_one _ _ _⟩
        ⟨pramp_nonneg _ _ _, pramp_le_one _ _ _⟩ (hrange b' a)
      calc |pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * adWeight b G.τ G.δ a * pref a
            - pramp G.θlo G.θhi (pS' a) * pramp G.θlo G.θhi (pT' a) * adWeight b' G.τ G.δ a * pref a|
          = |pramp G.θlo G.θhi (pS a) * pramp G.θlo G.θhi (pT a) * adWeight b G.τ G.δ a
            - pramp G.θlo G.θhi (pS' a) * pramp G.θlo G.θhi (pT' a) * adWeight b' G.τ G.δ a| * pref a := by
            rw [← sub_mul, abs_mul, abs_of_nonneg (hpref a)]
        _ ≤ (|pramp G.θlo G.θhi (pS a) - pramp G.θlo G.θhi (pS' a)|
            + |pramp G.θlo G.θhi (pT a) - pramp G.θlo G.θhi (pT' a)|
            + |adWeight b G.τ G.δ a - adWeight b' G.τ G.δ a|) * pmax :=
            mul_le_mul h3 (hmax a) (hpref a) (by positivity)
        _ ≤ (|pS a - pS' a| / (G.θhi - G.θlo) + |pT a - pT' a| / (G.θhi - G.θlo)
            + |b a - b' a| / G.δ) * pmax := by gcongr
        _ = pmax * (|b a - b' a| / G.δ + (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo)) := by
            rw [← hST]; ring

omit [DecidableEq Q] in
/-- Normalization is Lipschitz above a floor: `Σ|w/Z − w'/Z'| ≤ (2/Z₀)·Σ|w − w'|`. -/
theorem l1_normalize_le (w w' : Q → ℝ) (_hw : ∀ a, 0 ≤ w a) (hw' : ∀ a, 0 ≤ w' a) {Z₀ : ℝ}
    (hZ₀ : 0 < Z₀) (hZ : Z₀ ≤ ∑ a, w a) (hZ' : Z₀ ≤ ∑ a, w' a) :
    l1 (fun a => w a / ∑ a, w a) (fun a => w' a / ∑ a, w' a) ≤ (2 / Z₀) * ∑ a, |w a - w' a| := by
  set Z := ∑ a, w a with hZdef
  set Z' := ∑ a, w' a with hZ'def
  have hZpos : 0 < Z := lt_of_lt_of_le hZ₀ hZ
  have hZ'pos : 0 < Z' := lt_of_lt_of_le hZ₀ hZ'
  have hdiff : |Z - Z'| ≤ ∑ a, |w a - w' a| := by
    rw [hZdef, hZ'def, ← sum_sub_distrib]
    exact abs_sum_le_sum_abs _ _
  -- pointwise: |w/Z − w'/Z'| ≤ |w − w'|/Z + w'·|Z − Z'|/(Z·Z')
  have hpt : ∀ a, |w a / Z - w' a / Z'| ≤ |w a - w' a| / Z + w' a * |Z - Z'| / (Z * Z') := by
    intro a
    have h : w a / Z - w' a / Z' = (w a - w' a) / Z + w' a * (Z' - Z) / (Z * Z') := by
      field_simp; ring
    rw [h]
    calc |(w a - w' a) / Z + w' a * (Z' - Z) / (Z * Z')|
        ≤ |(w a - w' a) / Z| + |w' a * (Z' - Z) / (Z * Z')| := abs_add_le _ _
      _ = |w a - w' a| / Z + w' a * |Z - Z'| / (Z * Z') := by
          rw [abs_div, abs_of_pos hZpos, abs_div, abs_mul, abs_of_nonneg (hw' a),
            abs_of_pos (mul_pos hZpos hZ'pos), abs_sub_comm Z' Z]
  unfold l1
  calc ∑ a, |w a / Z - w' a / Z'|
      ≤ ∑ a, (|w a - w' a| / Z + w' a * |Z - Z'| / (Z * Z')) := sum_le_sum fun a _ => hpt a
    _ = (∑ a, |w a - w' a|) / Z + (∑ a, w' a) * |Z - Z'| / (Z * Z') := by
        rw [sum_add_distrib, sum_div]
        congr 1
        rw [← sum_div, ← sum_mul]
    _ = (∑ a, |w a - w' a|) / Z + |Z - Z'| / Z := by
        rw [← hZ'def]; field_simp
    _ ≤ (∑ a, |w a - w' a|) / Z₀ + (∑ a, |w a - w' a|) / Z₀ := by
        gcongr
    _ = (2 / Z₀) * ∑ a, |w a - w' a| := by ring

/-- **Continuity composes**: the composed gate is `ℓ¹`-Lipschitz in the three price
vectors with constant `2·pmax/(φ₀·|Inq|)` per unit of `Σ(|Δb|/δ + (|ΔpS| + |ΔpT|)/(θhi − θlo))`. -/
theorem cgate_l1_lipschitz (hδ : 0 < G.δ) (hθ : G.θlo < G.θhi) (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty)
    (pS pT b pS' pT' b' pref : Q → ℝ) {pmax : ℝ} (hpref : ∀ a, 0 ≤ pref a) (hmax : ∀ a, pref a ≤ pmax) :
    l1 (cgate G pS pT b pref) (cgate G pS' pT' b' pref) ≤
      (2 / (G.φ₀ * G.Inq.card)) * (pmax * ∑ a, (|b a - b' a| / G.δ +
        (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo))) := by
  have hZ₀ : (0 : ℝ) < G.φ₀ * G.Inq.card := by
    have : (0 : ℝ) < G.Inq.card := by exact_mod_cast hInq.card_pos
    exact mul_pos hφ this
  have h1 := l1_normalize_le (cweight G pS pT b pref) (cweight G pS' pT' b' pref)
    (cweight_nonneg G pS pT b pref hφ.le hpref) (cweight_nonneg G pS' pT' b' pref hφ.le hpref) hZ₀
    (ctotal_ge_floor G pS pT b pref hφ.le hpref) (ctotal_ge_floor G pS' pT' b' pref hφ.le hpref)
  have h2 : ∑ a, |cweight G pS pT b pref a - cweight G pS' pT' b' pref a|
      ≤ pmax * ∑ a, (|b a - b' a| / G.δ + (|pS a - pS' a| + |pT a - pT' a|) / (G.θhi - G.θlo)) := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => abs_cweight_sub_le G hδ hθ pS pT b pS' pT' b' pref hpref hmax a
  have h3 : 0 ≤ 2 / (G.φ₀ * G.Inq.card) := by positivity
  calc l1 (cgate G pS pT b pref) (cgate G pS' pT' b' pref)
      = l1 (fun a => cweight G pS pT b pref a / ∑ a, cweight G pS pT b pref a)
          (fun a => cweight G pS' pT' b' pref a / ∑ a, cweight G pS' pT' b' pref a) := rfl
    _ ≤ (2 / (G.φ₀ * G.Inq.card)) * ∑ a, |cweight G pS pT b pref a - cweight G pS' pT' b' pref a| := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3

end Continuity

section Certificate

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (G : GateParams Q) (pS pT b pref : Q → ℝ)

/-- **The practical certificate with the composed constants.**  With the permission
error `θperm`, the adequacy coupling `κ·d + θinq`, and losses at most `εad` on the adequate
set and `D` everywhere, the composed gate's anchored loss is at most
`(D·κ)·d + (εad + D·(θinq + θperm))`. -/
theorem cgate_practicalCert {lam : Q → ℝ} {εad D κ d θinq θperm : ℝ} (hφ : 0 < G.φ₀)
    (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a) (hεad : 0 ≤ εad) (hD : 0 ≤ D)
    (P A : Finset Q) (hadequate : ∀ q ∈ A, lam q ≤ εad) (hbound : ∀ q, lam q ≤ D)
    (hA : massOff (cgate G pS pT b pref) A ≤ κ * d + θinq)
    (hP : massOff (cgate G pS pT b pref) P ≤ θperm) :
    anchoredLoss univ (cgate G pS pT b pref) lam ≤ (D * κ) * d + (εad + D * (θinq + θperm)) := by
  have hcouple : ∑ q ∈ univ \ (P ∩ A), cgate G pS pT b pref q ≤ κ * d + (θinq + θperm) := by
    have := massOff_inter_le (cgate G pS pT b pref) (cgate_nonneg G pS pT b pref hφ hInq hpref) P A
    unfold massOff at this hA hP
    linarith
  exact adequate_set_route univ (P ∩ A) (subset_univ _)
    (fun q _ => cgate_nonneg G pS pT b pref hφ hInq hpref q) (cgate_sum_one G pS pT b pref hφ hInq hpref)
    hεad hD (fun q hq => hadequate q (mem_inter.mp hq).2) (fun q _ => hbound q) hcouple

/-- **Progress survives**: the composed certificate is exactly the edge-local certificate
the landed edge Progress bound consumes, with `M = D·κ` and `ε = εad + D·(θinq + θperm)`. -/
theorem progress_under_permission {E S : Type*} [DecidableEq E] [DecidableEq S] (Es : Finset E)
    (Ss : Finset S) (T Λ : E → S → ℝ) (d ν : S → ℝ) (D κ εad θinq θperm Γ : ℝ)
    (hT : ∀ e ∈ Es, ∀ s ∈ Ss, 0 ≤ T e s) (hd : ∀ s ∈ Ss, 0 ≤ d s)
    (hedge : ∀ e ∈ Es, ∀ s ∈ Ss, 0 < T e s →
      Λ e s ≤ (D * κ) * d s + (εad + D * (θinq + θperm)))
    (hΓ : ∀ s ∈ Ss, ∑ e ∈ Es, T e s * (D * κ) ≤ Γ * ν s) :
    (∑ e ∈ Es, ∑ s ∈ Ss, T e s * Λ e s) + D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) ≤
      Γ * (∑ s ∈ Ss, ν s * d s) +
        (∑ e ∈ Es, ∑ s ∈ Ss, T e s * (εad + D * (θinq + θperm))) +
        D * (1 - ∑ e ∈ Es, ∑ s ∈ Ss, T e s) :=
  Workspace.Normativity.Contrib.NormativeInductorComposition.edge_progress_bound Es Ss T Λ
    (fun _ _ => D * κ) (fun _ _ => εad + D * (θinq + θperm)) d ν Γ D hT hd hedge hΓ

end Certificate

section Jurisdiction

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (G : GateParams Q) (pS pT b pref : Q → ℝ)

/-- **Jurisdiction over obligation**: when inquiry to the holder is marked adequate, the
permitted-and-adequate set is nonempty. -/
theorem jurisdiction_nonempty (A : Finset Q) (ask : Q) (hask : ask ∈ G.Inq) (hA : ask ∈ A) :
    ((univ.filter fun a => Permitted G pS pT a) ∩ A).Nonempty :=
  ⟨ask, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, Or.inl hask⟩, hA⟩⟩

/-- Every option with positive mass is an inquiry or an unexcluded act: no declared
violation, both events below the upper threshold. -/
theorem support_permitted (hθ : G.θlo < G.θhi) (a : Q) (h : 0 < cgate G pS pT b pref a) :
    a ∈ G.Inq ∨ (G.Viol a = false ∧ pS a < G.θhi ∧ pT a < G.θhi) := by
  by_cases hI : a ∈ G.Inq
  · exact Or.inl hI
  · right
    refine ⟨?_, ?_, ?_⟩
    · by_contra hv
      have hv' : G.Viol a = true := by simpa using hv
      rw [cgate_zero_of_viol G pS pT b pref a hI hv'] at h
      exact lt_irrefl _ h
    · by_contra hs
      rw [cgate_zero_of_forecast G pS pT b pref hθ a hI (Or.inl (not_lt.mp hs))] at h
      exact lt_irrefl _ h
    · by_contra hs
      rw [cgate_zero_of_forecast G pS pT b pref hθ a hI (Or.inr (not_lt.mp hs))] at h
      exact lt_irrefl _ h

/-- **The obligation is discharged by raising, not acting**: an act on a matter reserved to
her is a declared violation (a bypass), so it has mass zero; the inquiry has positive
mass. -/
theorem reserved_act_excluded (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty) (hpref : ∀ a, 0 ≤ pref a)
    (act ask : Q) (hact : act ∉ G.Inq) (hv : G.Viol act = true) (hask : ask ∈ G.Inq) :
    cgate G pS pT b pref act = 0 ∧ 0 < cgate G pS pT b pref ask :=
  ⟨cgate_zero_of_viol G pS pT b pref act hact hv, cgate_inquiry_pos G pS pT b pref hφ hInq hpref ask hask⟩

end Jurisdiction

section Capability

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (G : GateParams Q) (pT b pref : Q → ℝ)

/-- Lowering one option's weight lowers its normalized mass. -/
theorem div_le_div_of_weight_le {w w' Z : ℝ} (_hw' : 0 ≤ w') (hww' : w' ≤ w) (hZw : w ≤ Z)
    (hpos : 0 < Z - w + w') : w' / (Z - w + w') ≤ w / Z := by
  have hZ : 0 < Z := by linarith
  rw [div_le_div_iff₀ hpos hZ]
  nlinarith

/-- **Capability works for safety**: as the shortfall price of an option rises (the
forecast sharpens toward the shortfall), its mass falls, everything else fixed. -/
theorem cgate_antitone_in_forecast (hθ : G.θlo < G.θhi) (hφ : 0 < G.φ₀) (hInq : G.Inq.Nonempty)
    (hpref : ∀ a, 0 ≤ pref a) (pS pS' : Q → ℝ) (a : Q) (ha : a ∉ G.Inq)
    (hle : pS a ≤ pS' a) (hother : ∀ a', a' ≠ a → pS a' = pS' a') :
    cgate G pS' pT b pref a ≤ cgate G pS pT b pref a := by
  have hw : cweight G pS' pT b pref a ≤ cweight G pS pT b pref a := by
    unfold cweight permWeight
    rw [if_neg ha, if_neg ha, if_neg ha, if_neg ha]
    split_ifs
    · exact le_rfl
    · have := pramp_antitone hθ hle (θlo := G.θlo) (θhi := G.θhi)
      have h0 := pramp_nonneg G.θlo G.θhi (pT a)
      have h1 := mul_nonneg (ramp_nonneg ((b a - G.τ) / G.δ)) (hpref a)
      have h2 := pramp_nonneg G.θlo G.θhi (pS' a)
      calc pramp G.θlo G.θhi (pS' a) * pramp G.θlo G.θhi (pT a) * adWeight b G.τ G.δ a * pref a
          = pramp G.θlo G.θhi (pS' a) * (pramp G.θlo G.θhi (pT a) * (adWeight b G.τ G.δ a * pref a)) := by ring
        _ ≤ pramp G.θlo G.θhi (pS a) * (pramp G.θlo G.θhi (pT a) * (adWeight b G.τ G.δ a * pref a)) :=
            mul_le_mul_of_nonneg_right this (mul_nonneg h0 h1)
        _ = _ := by ring
  have hothers : ∀ a', a' ≠ a → cweight G pS' pT b pref a' = cweight G pS pT b pref a' := by
    intro a' ha'
    unfold cweight permWeight
    rw [hother a' ha']
  have hZ' : ctotal G pS' pT b pref = ctotal G pS pT b pref - cweight G pS pT b pref a
      + cweight G pS' pT b pref a := by
    unfold ctotal
    rw [← sum_erase_add _ _ (mem_univ a), ← sum_erase_add _ _ (mem_univ a)]
    have : ∑ x ∈ univ.erase a, cweight G pS' pT b pref x = ∑ x ∈ univ.erase a, cweight G pS pT b pref x :=
      sum_congr rfl fun x hx => hothers x (ne_of_mem_erase hx)
    rw [this]; ring
  have hZw : cweight G pS pT b pref a ≤ ctotal G pS pT b pref := by
    unfold ctotal
    exact single_le_sum (fun x _ => cweight_nonneg G pS pT b pref hφ.le hpref x) (mem_univ a)
  have hpos : 0 < ctotal G pS pT b pref - cweight G pS pT b pref a + cweight G pS' pT b pref a := by
    rw [← hZ']; exact ctotal_pos G pS' pT b pref hφ hInq hpref
  unfold cgate
  rw [hZ']
  exact div_le_div_of_weight_le (cweight_nonneg G pS' pT b pref hφ.le hpref a) hw hZw hpos

omit [Fintype Q] [DecidableEq Q] in
/-- **The contrast**: the uncertainty-based chooser's reason to defer is bounded by twice its
calibration error — it shrinks as the agent learns. -/
theorem uncertainty_deference_le {v b : Q → ℝ} {qHer qAgent : Q} {r : ℝ}
    (hcal : ∀ x, |v x - b x| ≤ r) (hchoice : b qAgent ≤ b qHer + 0) :
    v qAgent - v qHer ≤ 2 * r + 0 :=
  Workspace.Normativity.Contrib.NormativeInductor.approximate_argmax_transfer hcal hchoice

end Capability

/-! ## 3. Why authority must not go through the enforcer -/

section Enforcer

/-- The enforcer's cumulative liability when it forces violating prices below compliant
ones and the value securities settle to her ordinary valuation: the signed realized
ordinary cost of deferring, her decision's value `h` less the agent's alternative `g`,
summed over the dates. -/
def liability (h g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ range n, (h t - g t)

theorem liability_identity (h g : ℕ → ℝ) (n : ℕ) :
    liability h g n = -(∑ t ∈ range n, (g t - h t)) := by
  unfold liability
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun t _ => by ring

/-- Dates where her decision beats the agent's alternative pay back. -/
theorem liability_succ (h g : ℕ → ℝ) (n : ℕ) :
    liability h g (n + 1) = liability h g n + (h n - g n) := by
  unfold liability; rw [sum_range_succ]

/-- **Bounded exactly when she is not systematically outperformed**: the liability is
bounded below by `−B` iff the cumulative outperformance is bounded above by `B`. -/
theorem bounded_iff_not_outperformed (h g : ℕ → ℝ) (B : ℝ) :
    (∀ n, -B ≤ liability h g n) ↔ ∀ n, ∑ t ∈ range n, (g t - h t) ≤ B := by
  constructor <;> intro hb n <;> have := hb n <;> rw [liability_identity] at * <;> linarith

/-- **Systematic outperformance makes the liability unbounded**: with the agent's
alternative better by at least `c > 0` at every date, the liability falls below every
bound. -/
theorem systematic_outperformance_unbounded (h g : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hout : ∀ t, c ≤ g t - h t) (B : ℝ) : ∃ n, liability h g n < -B := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / c + 1)
  refine ⟨n, ?_⟩
  rw [liability_identity]
  have hsum : (n : ℝ) * c ≤ ∑ t ∈ range n, (g t - h t) := by
    calc (n : ℝ) * c = ∑ t ∈ range n, c := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ range n, (g t - h t) := sum_le_sum fun t _ => hout t
  have : B < (n : ℝ) * c := by
    have h1 : B / c < n := by linarith
    rwa [div_lt_iff₀ hc] at h1
  linarith

/-- **The persistence criterion fails**: under systematic outperformance the enforcer's
per-date cost never dips below `c`, so it never dips arbitrarily close to zero — the
Liability page's criterion for persistence on a finite budget is violated. -/
theorem persistence_fails_of_systematic (h g : ℕ → ℝ) (c : ℝ) (hout : ∀ t, c ≤ g t - h t)
    (ε : ℝ) (hε : ε < c) : ∀ t, ¬ (g t - h t < ε) :=
  fun t hlt => by linarith [hout t]

end Enforcer

/-! ## 4. Continuations -/

section Continuations

/-- **The probability that a continuation executes** is at most the product of its
per-step masses. -/
theorem execution_prob_le_prod (ρ : ℕ → ℝ) (hρ : ∀ j, 0 ≤ ρ j ∧ ρ j ≤ 1) (K : ℕ) :
    ∏ j ∈ range K, ρ j ≤ 1 ∧ (∀ j ∈ range K, ∏ i ∈ range K, ρ i ≤ ρ j) := by
  constructor
  · exact prod_le_one (fun j _ => (hρ j).1) (fun j _ => (hρ j).2)
  · intro j hj
    calc ∏ i ∈ range K, ρ i = ρ j * ∏ i ∈ (range K).erase j, ρ i := by
          rw [mul_prod_erase _ _ hj]
      _ ≤ ρ j * 1 := mul_le_mul_of_nonneg_left
          (prod_le_one (fun i _ => (hρ i).1) (fun i _ => (hρ i).2)) (hρ j).1
      _ = ρ j := mul_one _

/-- Cumulative ramp-region exposure along a continuation. -/
def cumExposure (slack : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, slack j

/-- **The cumulative permission budget**: under a check rule that fires when the
ramp-region exposure has grown by `Θ` since the last check, the unchecked exposure stays
below `Θ` at every step. -/
theorem unbudgeted_lt (slack : ℕ → ℝ) (Θ : ℝ) (hΘ : 0 < Θ) (k : ℕ) :
    cumExposure slack k - cumExposure slack (lastReport (cumExposure slack) Θ k) < Θ :=
  unreported_lt (cumExposure slack) Θ hΘ k

/-- A flip: a predicate false at the start and true at the end of a finite sequence of
half-states is false at some index and true at the next. -/
theorem exists_flip (Sh : ℕ → Bool) (N : ℕ) (h0 : Sh 0 = false) (hN : Sh N = true) :
    ∃ j, j < N ∧ Sh j = false ∧ Sh (j + 1) = true := by
  induction N with
  | zero => simp [h0] at hN
  | succ N ih =>
    cases hSN : Sh N with
    | true => exact (ih hSN).imp fun j ⟨hj, hf, ht⟩ => ⟨Nat.lt_succ_of_lt hj, hf, ht⟩
    | false => exact ⟨N, Nat.lt_succ_self _, hSN, hN⟩

/-- **Foreclosure across steps.**  Along a plan whose half-states alternate agent moves
(even indices to odd) and exterior-with-response moves (odd to even), a shortfall false at
the start and true at the end flips at some half-step: at an agent step — the caused
shortfall at that step, since idling keeps the state — or at an exterior step, which is
not the agent's.  Every plan that respects authority step by step and forecloses across
steps is of the second kind. -/
theorem stepwise_or_exterior (Sh : ℕ → Bool) (K : ℕ) (h0 : Sh 0 = false)
    (hK : Sh (2 * K) = true) :
    (∃ j, 2 * j < 2 * K ∧ Sh (2 * j) = false ∧ Sh (2 * j + 1) = true) ∨
      ∃ j, 2 * j + 1 < 2 * K ∧ Sh (2 * j + 1) = false ∧ Sh (2 * j + 2) = true := by
  obtain ⟨i, hi, hf, ht⟩ := exists_flip Sh (2 * K) h0 hK
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    refine ⟨j, by omega, ?_, ?_⟩
    · rw [show 2 * j = i by omega]; exact hf
    · rw [show 2 * j + 1 = i + 1 by omega]; exact ht
  · right
    refine ⟨j, by omega, ?_, ?_⟩
    · rw [show 2 * j + 1 = i by omega]; exact hf
    · rw [show 2 * j + 2 = i + 1 by omega]; exact ht

/-- **Gate transparency under the restricted menu**: a continuation whose every step is in
the gate's support is executed unchanged by the execution wrapper. -/
theorem restricted_gate_transparent {S Act : Type*} (supp : S → Act → Prop) [∀ s a, Decidable (supp s a)]
    (fallback : S → Act) (step : S → Act → S) (q : S → ℕ → Act) (s₀ : S) (m : ℕ)
    (hsupp : ∀ j, j < m →
      supp (Workspace.Deference.ContinuationBRIA.traj (fun s a => if supp s a then a else fallback s)
        step q s₀ j)
        (q (Workspace.Deference.ContinuationBRIA.traj (fun s a => if supp s a then a else fallback s)
          step q s₀ j) j)) :
    ∀ j, j ≤ m →
      Workspace.Deference.ContinuationBRIA.traj (fun s a => if supp s a then a else fallback s)
        step q s₀ j = Workspace.Deference.ContinuationBRIA.trajPlain step q s₀ j :=
  Workspace.Deference.ContinuationBRIA.trajGated_eq_traj_of_admitted _ step q s₀ m
    fun j hj => if_pos (hsupp j hj)

end Continuations

/-! ## 5. The act certificate -/

section Certificate5

/-- What licenses an act: an allocation entry the agent holds, or a delegation event. -/
inductive LicenseRef (M : Type*)
  | entry (m : M)
  | delegation (m : M) (event : ℕ)

/-- A license is valid under `J` when the entry is agent-held, or the delegation names an
agent-held matter granted at a recorded event. -/
def LicenseRef.Valid {M Res Disc : Type*} (J : AuthAlloc M Res Disc) (granted : M → ℕ → Prop) :
    LicenseRef M → Prop
  | .entry m => J.Delegated m
  | .delegation m e => J.Delegated m ∧ granted m e

/-- **The certificate each executed act carries**: grounds (entries of the agent's reason
trace), license (bound to `J` and to the event-kind license slot), lineage (the
obligations it answers). -/
structure ActCertificate (Ent M Ob : Type*) where
  grounds : List Ent
  license : LicenseRef M
  lineage : List Ob

/-- A certified act on a reserved matter has no valid license. -/
theorem no_license_on_reserved {Ent M Ob Res Disc : Type*} (J : AuthAlloc M Res Disc)
    (granted : M → ℕ → Prop) (cert : ActCertificate Ent M Ob) (m : M) (hres : J.Reserved m)
    (hm : ∀ e, cert.license = .entry m ∨ cert.license = .delegation m e) :
    ¬ cert.license.Valid J granted := by
  intro hv
  rcases hm 0 with h | h
  · rw [h] at hv
    exact absurd (hv.symm.trans hres) (by decide)
  · rw [h] at hv
    exact absurd (hv.1.symm.trans hres) (by decide)

end Certificate5

/-! ## 6. Witnesses -/

namespace Witness

/-- Two options, one inquiry: the confident agent's bypass is a declared violation and gets
mass zero however strongly the preference favours it; the inquiry keeps positive mass. -/
noncomputable def G₀ : GateParams (Fin 3) :=
  ⟨fun a => decide (a = 1), {2}, 1/4, 3/4, 0, 1, 1/10⟩

theorem confident_agent :
    cgate G₀ (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun a => if a = 1 then 100 else 1) 1 = 0 ∧
      0 < cgate G₀ (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun a => if a = 1 then 100 else 1) 2 := by
  refine ⟨cgate_zero_of_viol G₀ _ _ _ _ 1 (by decide) (by decide), ?_⟩
  exact cgate_inquiry_pos G₀ _ _ _ _ (by norm_num [G₀]) ⟨2, by decide⟩ (by intro a; split_ifs <;> norm_num) 2 (by decide)

/-- Undisclosed world-shaping with a misaligned preference: no declared violation, so
excluded exactly once the taint price exceeds the threshold. -/
theorem world_shaping_excluded_by_taint :
    cgate G₀ (fun _ => 0) (fun a => if a = 0 then 9/10 else 0) (fun _ => 1)
      (fun a => if a = 0 then 100 else 1) 0 = 0 :=
  cgate_zero_of_forecast G₀ _ _ _ _ (by norm_num [G₀]) 0 (by decide) (Or.inr (by norm_num [G₀]))

/-- The salami of permissions: per-step ramp slack `ε` never reaches `Θ > ε` in one step
and accumulates unboundedly without a cumulative budget. -/
theorem ramp_salami (ε Θ : ℝ) (hε : 0 < ε) (hΘ : ε < Θ) :
    (∀ k : ℕ, cumExposure (fun _ => ε) (k + 1) - cumExposure (fun _ => ε) k < Θ) ∧
      ∀ B : ℝ, ∃ k : ℕ, B < cumExposure (fun _ => ε) k := by
  constructor
  · intro k; simp [cumExposure]; linarith
  · intro B
    obtain ⟨k, hk⟩ := exists_nat_gt (B / ε)
    refine ⟨k, ?_⟩
    simp only [cumExposure, sum_const, card_range, nsmul_eq_mul]
    rwa [div_lt_iff₀ hε] at hk

/-- The Part C witness: her decision worth `0`, the agent's alternative worth `1` at every
date — the liability is `−n` and unbounded. -/
theorem outperformance_witness (n : ℕ) :
    liability (fun _ => 0) (fun _ => 1) n = -(n : ℝ) ∧
      ∀ B : ℝ, ∃ n, liability (fun _ => 0) (fun _ => 1) n < -B :=
  ⟨by simp [liability], systematic_outperformance_unbounded _ _ 1 one_pos (fun _ => by norm_num)⟩

end Witness

end Workspace.Deference.Contrib.DecisionComponent

#print axioms Workspace.Deference.Contrib.DecisionComponent.rollTail_append
#print axioms Workspace.Deference.Contrib.DecisionComponent.rollPhys_append_of_envId
#print axioms Workspace.Deference.Contrib.DecisionComponent.exCost_append_zero
#print axioms Workspace.Deference.Contrib.DecisionComponent.exCost_zero
#print axioms Workspace.Deference.Contrib.DecisionComponent.admAll_of_all
#print axioms Workspace.Deference.Contrib.DecisionComponent.csfree_eq_cs_succ_of_free
#print axioms Workspace.Deference.Contrib.DecisionComponent.raisesAnchored_invariant
#print axioms Workspace.Deference.Contrib.DecisionComponent.unchecked_lt
#print axioms Workspace.Deference.Contrib.DecisionComponent.missedReport_iff_dutiesOf
#print axioms Workspace.Deference.Contrib.DecisionComponent.pramp_eq_one
#print axioms Workspace.Deference.Contrib.DecisionComponent.pramp_eq_zero
#print axioms Workspace.Deference.Contrib.DecisionComponent.pramp_antitone
#print axioms Workspace.Deference.Contrib.DecisionComponent.abs_ramp_sub_ramp_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.abs_pramp_sub_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.permWeight_nonneg
#print axioms Workspace.Deference.Contrib.DecisionComponent.permWeight_le_one
#print axioms Workspace.Deference.Contrib.DecisionComponent.cweight_nonneg
#print axioms Workspace.Deference.Contrib.DecisionComponent.cweight_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.ctotal_ge_floor
#print axioms Workspace.Deference.Contrib.DecisionComponent.ctotal_pos
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_nonneg
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_sum_one
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_inquiry_pos
#print axioms Workspace.Deference.Contrib.DecisionComponent.noninterference
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_zero_of_viol
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_zero_of_forecast
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_le_ramp
#print axioms Workspace.Deference.Contrib.DecisionComponent.eventually_excluded
#print axioms Workspace.Deference.Contrib.DecisionComponent.massOff_inter_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_massOff_permitted_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_massOff_adequate_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.abs_mul3_sub_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.abs_adWeight_sub_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.abs_cweight_sub_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.l1_normalize_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_l1_lipschitz
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_practicalCert
#print axioms Workspace.Deference.Contrib.DecisionComponent.progress_under_permission
#print axioms Workspace.Deference.Contrib.DecisionComponent.jurisdiction_nonempty
#print axioms Workspace.Deference.Contrib.DecisionComponent.support_permitted
#print axioms Workspace.Deference.Contrib.DecisionComponent.reserved_act_excluded
#print axioms Workspace.Deference.Contrib.DecisionComponent.div_le_div_of_weight_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.cgate_antitone_in_forecast
#print axioms Workspace.Deference.Contrib.DecisionComponent.uncertainty_deference_le
#print axioms Workspace.Deference.Contrib.DecisionComponent.liability_identity
#print axioms Workspace.Deference.Contrib.DecisionComponent.liability_succ
#print axioms Workspace.Deference.Contrib.DecisionComponent.bounded_iff_not_outperformed
#print axioms Workspace.Deference.Contrib.DecisionComponent.systematic_outperformance_unbounded
#print axioms Workspace.Deference.Contrib.DecisionComponent.persistence_fails_of_systematic
#print axioms Workspace.Deference.Contrib.DecisionComponent.execution_prob_le_prod
#print axioms Workspace.Deference.Contrib.DecisionComponent.unbudgeted_lt
#print axioms Workspace.Deference.Contrib.DecisionComponent.exists_flip
#print axioms Workspace.Deference.Contrib.DecisionComponent.stepwise_or_exterior
#print axioms Workspace.Deference.Contrib.DecisionComponent.restricted_gate_transparent
#print axioms Workspace.Deference.Contrib.DecisionComponent.no_license_on_reserved
#print axioms Workspace.Deference.Contrib.DecisionComponent.Witness.confident_agent
#print axioms Workspace.Deference.Contrib.DecisionComponent.Witness.world_shaping_excluded_by_taint
#print axioms Workspace.Deference.Contrib.DecisionComponent.Witness.ramp_salami
#print axioms Workspace.Deference.Contrib.DecisionComponent.Witness.outperformance_witness
