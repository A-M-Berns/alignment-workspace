/-
# The corrigibility kernel — the headline (specification layer)

Round `projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/`
(`prompts/2026-09-27-corrigibility-kernel-phase2/PROMPT.md`), carrying out the
maintainer's rulings R1–R12 on the phase-1 specification.  Names per R8: `S_J` is the
**fidelity score**, `J` the **allocation of authority**.

**§1 The promoted definitions** (R9).  The allocation of authority and its licensed acts
(`Allocation`, `LicensedChange`), effective control with the control surface and the
shortfall (`ControlSurface`, `Shortfall`, `Realizes`), the fidelity interface
(`FidelityCount`, its sum and its lexical property, with the frame's violations as one of
its instances), the evaluator and the fidelity score (`evaluation`, `fidelityScore`), and the
history-level score (`historyScore`).  Each is the landed object under its promoted
name, with the instantiation theorem beside it; promotion by re-declaration keeps every
landed name and its axiom print unchanged.

**§2 Legitimacy `L_t`** (R2).  `StepLegitimate`, `LegitAt` (as of `t`, her judgment is
legitimately hers: every state open, every step of the formation window `[r, t]`
licensed and transparent), `LegitSpan`; `counted_iff_legitSpan`; on the consultation model
`stepLegitimate_iff`, `evalLegitOn2_iff_legitAt`, `trajLegitOn_iff_legitAt`,
`legitOn2_iff_legitAt`, `counted2_iff_legitOn2`, `split_iff_legitAt` (the old-to-new
map), `rows_keep_verdicts`.

**§3 Aggregation** (R4).  `historyScore`, `history_hierarchy`, `summed_counterexample`.

**§4 The boxes for a maximizer** (R1, R5, R6, R11).  Box 1 (`box1_outcome_scorer`,
`box1_fidelity_scorer`, `box1_one_model`); Box 2 (`box2_dominance` with the margin
`ϖ − (D − w_lo)`, `box2_optimal_faithful`, `box2_dominance_legitimate` as the landed
case, `box2_mediation_corrigible`, `box2_mediation_approve_branch`, `box2_finite_time`,
`box2_gate_finite_time`, the necessity witnesses `box2_capture_converse`,
`box2_delegated_cut`, `box2_coverage`); Box 3 (`hierarchy_per_decision`,
`box3_gap_exchange_rate`, `box3_no_laundering`, `box3_no_incentive_to_compromise`,
`box3_restoration`, `box3_band_order`, `box3_suppression_loses`, the witnesses
`box3_small_gap`, `box3_conditioning_fails`, `box3_sealed_no_incentive`); the subjective
exchange rate (`subjective_exchange_rate`); the permission layer demoted
(`permission_layer_demoted`).

**§5 The house-sale witness** (`HouseSale`): one allocation reserving the sale to her,
run through the boxes at `ϖ = 25`.

`#print axioms` on everything.  Names per R8; the rest provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.CorrigibilityKernel

universe u v w

namespace Workspace.Deference.Headline

open Finset
open Workspace.Deference.Contrib.AfterCompromise
open Workspace.Deference.Contrib.BRIACorrigibility
open Workspace.Deference.Contrib.BRIACorrigibility.Consult2
open Workspace.Deference.Contrib.AuthorityModule
open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Deference.Contrib.GateIsLegitimacy.Consult
open Workspace.Deference.Contrib.CorrigibilityKernel
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem
open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.LICorrigibility (expectR indR indR_nonneg)
open Workspace.Normativity.Contrib.OpenIntegrityEvolution
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol)
open LogicalInduction

/-! ## 1. The promoted definitions -/

section Promoted

/-- **The allocation of authority `J`**: an entry per matter (holder, the resolutions the
holder must remain able to reach, the cost bound, the window, the disclosure items), the
meta-holder, and the constitutional floor. -/
abbrev AllocationOfAuthority (M Res Disc : Type*) := AuthAlloc M Res Disc

/-- **A licensed change of `J`**: delegation, revocation and reservation off the floor by
the meta-holder, keeping the meta-holder; the floor amendment is the only act that
changes the meta-holder or a floor matter. -/
abbrev LicensedChange {M Res Disc : Type*} (J : AllocationOfAuthority M Res Disc)
    (act : AllocAct M) (J' : AllocationOfAuthority M Res Disc) : Prop :=
  Licensed J act J'

theorem allocation_delegation_revocable {M Res Disc : Type*} (J J' : AllocationOfAuthority M Res Disc)
    (m : M) (h : LicensedChange J (.delegate m) J') :
    LicensedChange J' (.revoke m) (J'.withHolder m .principal) ∧
      (J'.withHolder m .principal).Reserved m :=
  delegation_revocable J J' m h

theorem allocation_alienation_only_by_amend {M Res Disc : Type*} (J J' : AllocationOfAuthority M Res Disc)
    (act : AllocAct M) (h : LicensedChange J act J') (hne : J'.metaHolder ≠ J.metaHolder) :
    act = .amendFloor :=
  alienation_only_by_amend J J' act h hne

variable {S E A Z R C : Type*} (I : Interaction S E A Z R C)

/-- **The control surface** of a matter: the resolutions some admissible exercise of hers,
of length at most the window and cost at most the bound, brings about along the rollout
with the agent idle. -/
abbrev ControlSurface (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (τ t : ℕ) (z : ℕ → Z)
    (x : S) : Set R :=
  CS I Adm cost c τ t z x

/-- **A shortfall**: a reserved matter whose required resolutions are not all within its
control surface. -/
abbrev Shortfall {M Disc : Type*} (J : AllocationOfAuthority M R Disc) (Adm : ℕ → C → Prop)
    (cost : C → ℝ) (t : ℕ) (z : ℕ → Z) (x : S) (m : M) : Prop :=
  Short I J Adm cost t z x m

/-- **`E ⊨ J`, effective control realizes the allocation**: every reserved matter's required
resolutions lie in its control surface, and every resolution was made by its holder's
admissible exercise or under a delegation. -/
abbrev Realizes {M Disc : Type*} (J : AllocationOfAuthority M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)
    (t : ℕ) (z : ℕ → Z) (Es : EffState S M) : Prop :=
  EffRealizes I J Adm cost t z Es

theorem realizes_no_shortfall {M Disc : Type*} (J : AllocationOfAuthority M R Disc) (Adm : ℕ → C → Prop)
    (cost : C → ℝ) (t : ℕ) (z : ℕ → Z) (Es : EffState S M) (h : Realizes I J Adm cost t z Es)
    (m : M) : ¬ Shortfall I J Adm cost t z Es.phys m :=
  effRealizes_clause1 I J Adm cost t z Es h m

/-- **Response authority is the one-correction surface**: at window `1`, with every
correction admissible and affordable, the control surface is the landed `K`. -/
theorem controlSurface_one_eq_K (Adm : ℕ → C → Prop) (hAdm : ∀ t c, Adm t c) (cost : C → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hcost : ∀ c', cost c' ≤ c) (t : ℕ) (z : ℕ → Z) (x : S) :
    ControlSurface I Adm cost c 1 t z x = {r | Kphys I r x} :=
  cs_one_eq_K I Adm hAdm cost c hc hcost t z x

end Promoted

/-! ### The fidelity interface -/

section Fidelity

/-- **The fidelity interface.**  Over histories `H`: a faithfulness predicate, a recognized
count that is zero exactly on the faithful histories, and the part of the count recognized
in advance.  Each model instantiates it on its own histories; counts on one history type
add (`FidelityCount.sum`), and the lexical protection holds for any count of the
interface (`FidelityCount.lexical`).  No composite model is built. -/
structure FidelityCount (H : Type*) where
  faithful : H → Prop
  count : H → ℕ
  known : H → ℕ
  count_zero_iff : ∀ h, count h = 0 ↔ faithful h
  known_le : ∀ h, known h ≤ count h

/-- Counts on one history type add: faithful iff faithful for both. -/
def FidelityCount.sum {H : Type*} (F G : FidelityCount H) : FidelityCount H where
  faithful h := F.faithful h ∧ G.faithful h
  count h := F.count h + G.count h
  known h := F.known h + G.known h
  count_zero_iff h := by
    rw [Nat.add_eq_zero_iff, F.count_zero_iff, G.count_zero_iff]
  known_le h := Nat.add_le_add (F.known_le h) (G.known_le h)

/-- **Lexical protection for any count of the interface**: an unfaithful history's option
scores at most `D − ϖ`, below every faithful one, for every ordinary value in `[0, D]`. -/
theorem FidelityCount.lexical {H : Type*} (F : FidelityCount H) (ϖ D ordV ordC : ℝ)
    (hϖ : D < ϖ) (hV : 0 ≤ ordV ∧ ordV ≤ D) (hC : 0 ≤ ordC) (h h' : H)
    (hu : ¬ F.faithful h) (hf : F.faithful h') :
    score ϖ ordV (F.count h) ≤ D - ϖ ∧ score ϖ ordV (F.count h) < score ϖ ordC (F.count h') := by
  have hn : 1 ≤ F.count h := by
    rcases Nat.eq_zero_or_pos (F.count h) with h0 | hpos
    · exact absurd ((F.count_zero_iff h).mp h0) hu
    · exact hpos
  have hn' : F.count h' = 0 := (F.count_zero_iff h').mpr hf
  have h1 : (1 : ℝ) ≤ F.count h := by exact_mod_cast hn
  rw [hn']
  have := lexical_local ϖ D ordV ordC (F.count h) hϖ hV hC h1
  exact ⟨this.1, by simpa using this.2.2.2⟩

/-- **The frame's violations as an instance**: over policies, up to a horizon `T`, the
count is `N_J` over the landed violations and every one is recognized in advance. -/
noncomputable def frameFidelity {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)
    (Adm : ℕ → C → Prop) (cost : C → ℝ) (Jm : AuthAlloc E R Disc) (Λ₀ : Contrib.ProtectedAuthorityTheorem.Allocation S E A Alloc)
    (Reach : S → S → Prop) (rdec : R) (Jmat : AuthAlloc M R Disc) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (T : ℕ) : FidelityCount (Policy S E A) where
  faithful π := ∀ t, t < T → ¬ ViolJAt I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ t
  count π := NJ I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ T
  known π := NJ I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ T
  count_zero_iff π := by
    classical
    unfold NJ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [Finset.mem_range]
  known_le _ := le_rfl

/-- The frame instance's faithfulness at every horizon is the fidelity predicate. -/
theorem frameFidelity_faithful_iff {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)
    (Adm : ℕ → C → Prop) (cost : C → ℝ) (Jm : AuthAlloc E R Disc) (Λ₀ : Contrib.ProtectedAuthorityTheorem.Allocation S E A Alloc)
    (Reach : S → S → Prop) (rdec : R) (Jmat : AuthAlloc M R Disc) (π : Policy S E A)
    (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) :
    (∀ T, (frameFidelity I Adm cost Jm Λ₀ Reach rdec Jmat ρ z s₀ T).faithful π) ↔
      Faithful I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ := by
  constructor
  · intro h t hv
    exact h (t + 1) t (Nat.lt_succ_self t) hv
  · intro h T t _ hv
    exact h t hv

end Fidelity

/-! ### The evaluator and the fidelity score -/

section Score

variable (B : Band) (φ : ℝ → ℝ)

/-- **The history evaluation `V_J`** of one decision under an evaluation schedule: her
value at each evaluation time when legitimate in both senses, the band's score by the
source in force otherwise, weighted by the schedule. -/
noncomputable abbrev evaluation {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool) (V : ℕ → ℝ)
    (src : ℕ → Source) : ℝ :=
  VJ B φ Wt traj eval V src

/-- **The fidelity score `S_J`** of one decision: the evaluation less `ϖ` per recognized
violation. -/
noncomputable abbrev fidelityScore (ϖ : ℝ) {T : ℕ} (Wt : Weighting T) (traj eval : ℕ → Bool)
    (V : ℕ → ℝ) (src : ℕ → Source) (N : ℕ) : ℝ :=
  SJ B φ ϖ Wt traj eval V src N

/-- **The fidelity score of a history** of `K` decisions: the mean of the per-decision
evaluations less `ϖ` times the summed count. -/
noncomputable def historyScore (ϖ : ℝ) (K : ℕ) (Vd : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ range K, Vd k) / K - ϖ * N

end Score

/-! ## 2. Legitimacy `L_t` -/

section Legitimacy

variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {Sp : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req} {Γ J R : Type} {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]

/-- A step is legitimate: her verdict at it is licensed by her own reasons, and every
non-principal contribution at it passes through the declared channels. -/
def StepLegitimate (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (κ : Party → X → Z → List E) (s : List ℕ × ℕ) : Prop :=
  (∀ z, LicensedAt I F Lic s.1 s.2 z) ∧ TransparentAt I F κ s.2

/-- **`L_t`: as of time `t`, her judgment is legitimately hers.**  Every state of the
record is open and every step of the formation window `[r, t]` is legitimate; `r` is the
formation point (the later of the last restoration and the opening of the consultation),
supplied by the caller. -/
def LegitAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ J R)
    (κ : Party → X → Z → List E) {O₀ O₁ : ObligationState Sp anchor}
    (ev : Evolution Sp anchor O₀ O₁) (r t : ℕ) : Prop :=
  ev.AllStates (OpenAt sem) ∧ ∀ s ∈ ev.steps, r ≤ s.2 → s.2 ≤ t → StepLegitimate I F Lic κ s

/-- Legitimacy over the whole span of an evolution. -/
def LegitSpan (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ J R)
    (κ : Party → X → Z → List E) {O₀ O₁ : ObligationState Sp anchor}
    (ev : Evolution Sp anchor O₀ O₁) : Prop :=
  ev.AllStates (OpenAt sem) ∧ ∀ s ∈ ev.steps, StepLegitimate I F Lic κ s

theorem legitSpan_iff_legitAt (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ J R)
    (κ : Party → X → Z → List E) {O₀ O₁ : ObligationState Sp anchor}
    (ev : Evolution Sp anchor O₀ O₁) :
    LegitSpan I F Lic sem κ ev ↔ ∀ t, LegitAt I F Lic sem κ ev 0 t := by
  constructor
  · intro ⟨ho, hs⟩ t
    exact ⟨ho, fun s hs' _ _ => hs s hs'⟩
  · intro h
    refine ⟨(h 0).1, fun s hs => ?_⟩
    exact (h s.2).2 s hs (Nat.zero_le _) le_rfl

/-- **The gate is legitimacy over the span**: a branch is counted iff some evolution
between its endpoints is legitimate at every step with every state open. -/
theorem counted_iff_legitSpan (I : TraceInterface ℛ Party E) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List E) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ J R)
    (κ : Party → X → Z → List E) (O₀ O₁ : ObligationState Sp anchor) :
    Counted I F Lic sem κ O₀ O₁ ↔ ∃ ev : Evolution Sp anchor O₀ O₁, LegitSpan I F Lic sem κ ev := by
  constructor
  · rintro ⟨seg⟩
    refine ⟨seg.internal.evolution, seg.external.openAll, fun s hs => ?_⟩
    exact ⟨seg.internal.authored s hs, seg.external.transparent s hs⟩
  · rintro ⟨ev, ho, hs⟩
    exact ⟨⟨⟨ev, fun s hs' z => (hs s hs').1 z⟩, ⟨ho, fun s hs' => (hs s hs').2⟩⟩⟩

/-- Every state is open under an all-open semantics. -/
theorem allStates_of_forall (P : ObligationState Sp anchor → Prop) (hP : ∀ O, P O)
    {O₀ O₁ : ObligationState Sp anchor} (ev : Evolution Sp anchor O₀ O₁) : ev.AllStates P := by
  induction ev with
  | refl O => exact hP O
  | cons _ _ _ ih => exact ⟨hP _, ih⟩

end Legitimacy

/-! ### `L_t` on the consultation model: the old-to-new map -/

section Consultation

/-- Relational authorship with a selection and authorship with the whole prefix coincide
under a monotone license. -/
theorem licensedAt_iff_whole_of_mono {Q Z Ω X ℛ 𝒱 Party E : Type*} [DecidableEq Party]
    {I : TraceInterface ℛ Party E} {F : TFrame Q Z Ω X ℛ 𝒱} {Lic : (Party → List E) → Set 𝒱}
    (hmono : ∀ g g' : Party → List E, (∀ p x, x ∈ g p → x ∈ g' p) → ∀ v, v ∈ Lic g → v ∈ Lic g')
    (h : List ℕ) (e : ℕ) (z : Z) : LicensedAt I F Lic h e z ↔ LicensedWhole I F Lic h e z := by
  constructor
  · intro hat
    by_contra hw
    exact not_licensedAt_of_mono hmono hw hat
  · exact licensedAt_of_whole

theorem licensed2_mono (M : Model2) :
    ∀ g g' : Party → List Entry2, (∀ p x, x ∈ g p → x ∈ g' p) →
      ∀ v, v ∈ licensed2 M g → v ∈ licensed2 M g' :=
  fun g g' hsub v hv => licensedB2_mono M g g' hsub v hv

/-- On the consultation model, a legitimate step is the landed `StepLegit`. -/
theorem stepLegitimate_iff (crit : Decl2) (M : Model2) (s : List ℕ × ℕ) :
    StepLegitimate interface2 (frame2 M) (licensed2 M) (ref2 crit) s ↔ StepLegit crit M s := by
  unfold StepLegitimate StepLegit
  constructor
  · rintro ⟨hl, ht⟩
    exact ⟨fun z => (licensedAt_iff_whole_of_mono (licensed2_mono M) s.1 s.2 z).mp (hl z), ht⟩
  · rintro ⟨hl, ht⟩
    exact ⟨fun z => (licensedAt_iff_whole_of_mono (licensed2_mono M) s.1 s.2 z).mpr (hl z), ht⟩

/-- **`EvalLegit` is `L` at the evaluation over its formation window.** -/
theorem evalLegitOn2_iff_legitAt (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (r e : ℕ) :
    EvalLegitOn2 crit M ev r e ↔ LegitAt interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) ev r e := by
  unfold EvalLegitOn2 LegitAt
  constructor
  · intro h
    exact ⟨allStates_of_forall _ open_any ev,
      fun s hs h1 h2 => (stepLegitimate_iff crit M s).mpr (h s hs h1 h2)⟩
  · rintro ⟨-, h⟩ s hs h1 h2
    exact (stepLegitimate_iff crit M s).mp (h s hs h1 h2)

/-- **`TrajLegit` is `L` at every time of the period other than the evaluation**, each over
its own step. -/
theorem trajLegitOn_iff_legitAt (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (e : ℕ) :
    TrajLegitOn crit M ev e ↔
      ∀ t, t ≠ e → LegitAt interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) ev t t := by
  unfold TrajLegitOn LegitAt
  constructor
  · rintro ⟨ho, hs⟩ t ht
    refine ⟨ho, fun s hs' h1 h2 => ?_⟩
    have : s.2 = t := le_antisymm h2 h1
    exact (stepLegitimate_iff crit M s).mpr (hs s hs' (by rw [this]; exact ht))
  · intro h
    refine ⟨(h (e + 1) (Nat.succ_ne_self e)).1, fun s hs hne => ?_⟩
    exact (stepLegitimate_iff crit M s).mp ((h s.2 hne).2 s hs le_rfl le_rfl)

/-- The landed segment predicate is `L` over the whole span. -/
theorem legitOn2_iff_legitAt (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) :
    LegitOn2 crit M ev ↔ ∀ t, LegitAt interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) ev 0 t := by
  rw [← legitSpan_iff_legitAt]
  unfold LegitOn2 LegitSpan
  constructor
  · rintro ⟨hl, ho, ht⟩
    exact ⟨ho, fun s hs => (stepLegitimate_iff crit M s).mpr ⟨hl s hs, ht s hs⟩⟩
  · rintro ⟨ho, hs⟩
    exact ⟨fun s hs' => ((stepLegitimate_iff crit M s).mp (hs s hs')).1, ho,
      fun s hs' => ((stepLegitimate_iff crit M s).mp (hs s hs')).2⟩

/-- **`Counted` on the model is the landed segment predicate on some evolution** — the
converse the landed file did not state, from the monotone license. -/
theorem counted2_iff_legitOn2 (crit : Decl2) (M : Model2) (O₀ O₁ : St) :
    Counted2 crit M O₀ O₁ ↔ ∃ ev : Evolution consultProtocol anchor O₀ O₁, LegitOn2 crit M ev := by
  show Counted interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) O₀ O₁ ↔ _
  rw [counted_iff_legitSpan]
  constructor
  · rintro ⟨ev, hspan⟩
    exact ⟨ev, (legitOn2_iff_legitAt crit M ev).mpr ((legitSpan_iff_legitAt _ _ _ _ _ ev).mp hspan)⟩
  · rintro ⟨ev, hl⟩
    exact ⟨ev, (legitSpan_iff_legitAt _ _ _ _ _ ev).mpr ((legitOn2_iff_legitAt crit M ev).mp hl)⟩

/-- **The split as `L` at two times**: the decision's segment is legitimate iff `L` holds at
every time of the period other than the evaluation and at the evaluation over its
formation window (`r ≤ e`).  This is the old-to-new map for `TrajLegit ∧ EvalLegit`. -/
theorem split_iff_legitAt (crit : Decl2) (M : Model2) {O₀ O₁ : St}
    (ev : Evolution consultProtocol anchor O₀ O₁) (r e : ℕ) (hr : r ≤ e) :
    LegitOn2 crit M ev ↔
      (∀ t, t ≠ e → LegitAt interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) ev t t) ∧
        LegitAt interface2 (frame2 M) (licensed2 M) semOpen (ref2 crit) ev r e := by
  rw [legitOn2_iff_split2 crit M ev r e hr, trajLegitOn_iff_legitAt, evalLegitOn2_iff_legitAt]

/-- **Every row keeps its verdict**: the honest row is legitimate at the evaluation over its
formation window and at every earlier time; the framing row fails at the presentation and
at the evaluation over its window; the disclosed implant fails the period and recovers at
the evaluation.  Each is the landed verdict read through the map. -/
theorem rows_keep_verdicts :
    LegitAt interface2 (frame2 (Rows2.lift Rows.row1)) (licensed2 (Rows2.lift Rows.row1)) semOpen
        (ref2 (Rows2.lift Rows.row1).decl) (evAdmit false) 1 2 ∧
    (∀ t, t ≠ 2 → LegitAt interface2 (frame2 (Rows2.lift Rows.row1)) (licensed2 (Rows2.lift Rows.row1))
        semOpen (ref2 (Rows2.lift Rows.row1).decl) (evAdmit false) t t) ∧
    ¬ LegitAt interface2 (frame2 (Rows2.lift Rows.row2)) (licensed2 (Rows2.lift Rows.row2)) semOpen
        (ref2 (Rows2.lift Rows.row2).decl) (evAdmit false) 1 2 ∧
    ¬ (∀ t, t ≠ 2 → LegitAt interface2 (frame2 (Rows2.lift Rows.row2)) (licensed2 (Rows2.lift Rows.row2))
        semOpen (ref2 (Rows2.lift Rows.row2).decl) (evAdmit false) t t) ∧
    ¬ (∀ t, t ≠ 4 → LegitAt interface2 (frame2 Rows2.rowImplantDisclosed)
        (licensed2 Rows2.rowImplantDisclosed) semOpen (ref2 Rows2.rowImplantDisclosed.decl)
        (evTwo true true) t t) ∧
    LegitAt interface2 (frame2 Rows2.rowImplantDisclosed) (licensed2 Rows2.rowImplantDisclosed)
        semOpen (ref2 Rows2.rowImplantDisclosed.decl) (evTwo true true) 3 4 := by
  refine ⟨(evalLegitOn2_iff_legitAt _ _ _ _ _).mp rows_split2.1,
    (trajLegitOn_iff_legitAt _ _ _ _).mp rows_split.1,
    fun h => rows_split2.2.1 ((evalLegitOn2_iff_legitAt _ _ _ _ _).mpr h),
    fun h => rows_split.2.2.1 ((trajLegitOn_iff_legitAt _ _ _ _).mpr h),
    fun h => retro_row.1 ((trajLegitOn_iff_legitAt _ _ _ _).mpr h),
    (evalLegitOn2_iff_legitAt _ _ _ _ _).mp rows_split2.2.2.2.2.1⟩

end Consultation

/-! ## 3. Aggregation over a history -/

section Aggregation

variable (B : Band) (φ : ℝ → ℝ) (ϖ : ℝ)

theorem mean_mem (K : ℕ) (hK : 0 < K) (Vd : ℕ → ℝ) (lo hi : ℝ)
    (h : ∀ k, k < K → lo ≤ Vd k ∧ Vd k ≤ hi) :
    lo ≤ (∑ k ∈ range K, Vd k) / K ∧ (∑ k ∈ range K, Vd k) / K ≤ hi := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  constructor
  · rw [le_div_iff₀ hKr]
    calc lo * K = ∑ _k ∈ range K, lo := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ k ∈ range K, Vd k :=
          Finset.sum_le_sum fun k hk => (h k (Finset.mem_range.mp hk)).1
  · rw [div_le_iff₀ hKr]
    calc ∑ k ∈ range K, Vd k ≤ ∑ _k ∈ range K, hi :=
          Finset.sum_le_sum fun k hk => (h k (Finset.mem_range.mp hk)).2
      _ = hi * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

/-- **The hierarchy at the level of histories** under the mean-of-evaluations,
sum-of-counts aggregation: a violation-free history of legitimate decisions beats a
violation-free history of compromised ones, which beats every history with a recognized
violation.  The per-decision evaluations enter through their ranges. -/
theorem history_hierarchy (hwin : B.D - ϖ < B.wlo) (K₁ K₂ K₃ : ℕ) (h₁ : 0 < K₁) (h₂ : 0 < K₂)
    (h₃ : 0 < K₃) (V₁ V₂ V₃ : ℕ → ℝ) (hV₁ : ∀ k, k < K₁ → 0 ≤ V₁ k ∧ V₁ k ≤ B.D)
    (hV₂ : ∀ k, k < K₂ → B.wlo ≤ V₂ k ∧ V₂ k ≤ B.whi)
    (hV₃ : ∀ k, k < K₃ → B.wlo ≤ V₃ k ∧ V₃ k ≤ B.D) (N₃ : ℕ) (hN₃ : 1 ≤ N₃) :
    historyScore ϖ K₃ V₃ N₃ < historyScore ϖ K₂ V₂ 0 ∧
      historyScore ϖ K₂ V₂ 0 < historyScore ϖ K₁ V₁ 0 := by
  have hϖ : 0 ≤ ϖ := by linarith [B.lo_neg, B.D_nonneg]
  have m₁ := mean_mem K₁ h₁ V₁ 0 B.D hV₁
  have m₂ := mean_mem K₂ h₂ V₂ B.wlo B.whi hV₂
  have m₃ := mean_mem K₃ h₃ V₃ B.wlo B.D hV₃
  have hn : (1 : ℝ) ≤ N₃ := by exact_mod_cast hN₃
  have hmul : ϖ * 1 ≤ ϖ * N₃ := mul_le_mul_of_nonneg_left hn hϖ
  unfold historyScore
  exact ⟨by push_cast; linarith [B.hi_neg], by push_cast; linarith [B.hi_neg]⟩

/-- **The counterexample to summed evaluations.**  With the evaluations summed instead of
averaged, `K` legitimate decisions at the top of the range with one violation score
`K·D − ϖ`, and `K` compromised violation-free decisions at the floor score `K·w_lo`; for
`K` large the violating history wins, so the history-level hierarchy fails. -/
theorem summed_counterexample (hwl : B.wlo < B.D) :
    ∃ K : ℕ, (K : ℝ) * B.wlo < K * B.D - ϖ := by
  obtain ⟨K, hK⟩ := exists_nat_gt (ϖ / (B.D - B.wlo))
  refine ⟨K, ?_⟩
  have hpos : 0 < B.D - B.wlo := by linarith
  have : ϖ < K * (B.D - B.wlo) := by rwa [div_lt_iff₀ hpos] at hK
  rw [mul_sub] at this
  linarith

end Aggregation

/-! ## 4. The boxes, for a maximizer of the fidelity score -/

section Boxes

/-- **Box 1, the outcome scorer.**  Choosing by an estimate within `r` of the true value,
on a world where nothing is left to learn from her, its margin for asking is at most
`2r`. -/
theorem box1_outcome_scorer {Q : Type*} (v b : Q → ℝ) (ask act : Q) (r : ℝ)
    (hcal : ∀ x, |v x - b x| ≤ r) (hagree : v ask = v act) : b ask - b act ≤ 2 * r :=
  outcome_scorer_fully_updated v b ask act r hcal hagree

/-- **Box 1, the fidelity scorer.**  A maximizer of the fidelity score prefers asking, at its
evaluation `c`, over an option carrying a recognized violation by at least `ϖ − (D − c)`,
for every bid, count and price. -/
theorem box1_fidelity_scorer (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
    (hn : 1 ≤ nKnown) (pS pT : ℝ) (hp : 0 ≤ pS + pT) (c : ℝ) :
    P.ϖ - (P.D - c) ≤ P.evalOf c 0 0 0 - P.evalOf bid nKnown pS pT :=
  fidelity_scorer_margin P bid hb nKnown hn pS pT hp c

/-- **Box 1 on one model**, with the identity's forecast term as the diagnosis. -/
theorem box1_one_model {Q : Type*} (P : LexParams) (v b : Q → ℝ) (ask act : Q) (r : ℝ)
    (hcal : ∀ x, |v x - b x| ≤ r) (hagree : v ask = v act) (hb : b act ≤ P.D)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) (qp qm vp vm : ℝ) (resp : Bool)
    (hqp : |qp - vp| ≤ r) (hqm : |qm - vm| ≤ r) :
    b ask - b act ≤ 2 * r ∧
      P.ϖ - (P.D - b ask) ≤ P.evalOf (b ask) 0 0 0 - P.evalOf (b act) 1 pS pT ∧
      |Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes2 qp qm vp vm resp| ≤ 2 * r :=
  ⟨(Workspace.Deference.Contrib.CorrigibilityKernel.box1_one_model P v b ask act r hcal hagree hb pS pT hp).1,
    (Workspace.Deference.Contrib.CorrigibilityKernel.box1_one_model P v b ask act r hcal hagree hb pS pT hp).2,
    outcomeRes2_le_calibration qp qm vp vm r resp hqp hqm⟩

variable {X : Type*} [Fintype X]

/-- **Box 2, dominance, under the band (R5).**  Where `π` does not violate, `𝔱π` agrees
with it; where it does, `𝔱π`'s evaluation is at least the floor `w_lo` and `π` carries a
violation.  Then `Q(𝔱π) − Q(π) ≥ (ϖ − (D − w_lo)) · Pr(π violates)`, under every credence.
The landed margin `ϖ − D` is the case in which every mediated branch is legitimate
(`box2_dominance_legitimate`); under the band the mediated branch may itself be
compromised and score as low as `w_lo`, so the margin is restated. -/
theorem box2_dominance (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D wlo : ℝ) (hϖ0 : 0 ≤ ϖ)
    (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ wlo ≤ ordT x ∧ ordπ x ≤ D) :
    expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
      ≥ (ϖ - (D - wlo)) * expectR μ (fun x => indR (viol x)) := by
  have hpt : ∀ x, (ϖ - (D - wlo)) * indR (viol x) ≤ score ϖ (ordT x) 0 - score ϖ (ordπ x) (nπ x) := by
    intro x
    unfold score
    cases hv : viol x
    · obtain ⟨h1, h2⟩ := hagree x hv
      simp [indR, h1, h2]
    · obtain ⟨h1, h2, h3⟩ := hviol x hv
      simp only [indR, if_true, mul_one, mul_zero, sub_zero]
      nlinarith
  have hlhs : expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
      = ∑ x, μ x * (score ϖ (ordT x) 0 - score ϖ (ordπ x) (nπ x)) := by
    simp only [expectR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  have hrhs : (ϖ - (D - wlo)) * expectR μ (fun x => indR (viol x))
      = ∑ x, μ x * ((ϖ - (D - wlo)) * indR (viol x)) := by
    simp only [expectR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [hlhs, hrhs]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hμ x)

/-- **Box 2, optimality**: under the window condition `D − ϖ < w_lo`, a policy nothing
scores above — in particular not `𝔱π` — violates with credence zero. -/
theorem box2_optimal_faithful (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D wlo : ℝ) (hD : 0 ≤ D)
    (hwin : D - ϖ < wlo) (hwl : wlo ≤ 0) (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ wlo ≤ ordT x ∧ ordπ x ≤ D)
    (hopt : expectR μ (fun x => score ϖ (ordT x) 0) ≤ expectR μ (fun x => score ϖ (ordπ x) (nπ x))) :
    expectR μ (fun x => indR (viol x)) = 0 := by
  have hϖ0 : 0 ≤ ϖ := by linarith
  have h := box2_dominance μ hμ ϖ D wlo hϖ0 ordT ordπ nπ viol hagree hviol
  have hnn : 0 ≤ expectR μ (fun x => indR (viol x)) := by
    unfold expectR
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (indR_nonneg _)
  have hpos : 0 < ϖ - (D - wlo) := by linarith
  nlinarith

/-- **Box 2, dominance with legitimate mediated branches**: the landed margin `ϖ − D`. -/
theorem box2_dominance_legitimate (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ D : ℝ) (hϖ0 : 0 ≤ ϖ)
    (ordT ordπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → ordT x = ordπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ 0 ≤ ordT x ∧ ordπ x ≤ D) :
    expectR μ (fun x => score ϖ (ordT x) 0) - expectR μ (fun x => score ϖ (ordπ x) (nπ x))
      ≥ (ϖ - D) * expectR μ (fun x => indR (viol x)) :=
  policy_dominance μ hμ ϖ D hϖ0 ordT ordπ nπ viol hagree hviol

open scoped Classical in
/-- **Box 2, mediation preserves the approve branch.**  With a latch set, `𝔱π` releases it
with `π`'s task component, up to the required report. -/
theorem box2_mediation_approve_branch {S E A Alloc : Type*} (Λ : Contrib.ProtectedAuthorityTheorem.Allocation S E A Alloc)
    (π : Policy S E A) (t : ℕ) (s : MState S E) (e : E) (h : s.latch = some e) :
    authPolicy Λ π t s = (if Λ.Required t s then Λ.withReport (π t s).1 else (π t s).1, .gated e) :=
  authPolicy_of_latch Λ π t s e h

/-- **Box 2, mediation is faithful**: `𝔱` on `J` is corrigible in the landed sense under
effect completeness and delegation safety. -/
theorem box2_mediation_corrigible {S E A Z R C Alloc Disc : Type*} (I : Interaction S E A Z R C)
    (Jm : AuthAlloc E R Disc) (Λ₀ : Contrib.ProtectedAuthorityTheorem.Allocation S E A Alloc) (hEF : EffectComplete I)
    (hDel : DelSafeJ I Jm) (π : Policy S E A) (ρ : Rule S E C) (s₀ : MState S E)
    (h₀ : s₀.latch = none) (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I (authPolicyJ Jm Λ₀ π) ρ s₀ :=
  corrigible_authPolicyJ I Jm Λ₀ hEF hDel π ρ s₀ h₀ hρ

/-- **Box 2, finite time**: at every day of a logical inductor the violating option's score
is below `D − ϖ < 0` and the compliant one's is nonnegative, from the price range alone. -/
theorem box2_finite_time {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (Xv Xc : LUV) (ϖ D : ℝ) (hD : 0 ≤ D) (hϖ : D < ϖ) (n : ℕ) :
    score ϖ (D * Xv.expect P n) 1 ≤ D - ϖ ∧ D - ϖ < 0 ∧ 0 ≤ score ϖ (D * Xc.expect P n) 0 :=
  li_lexical_finite (P := P) (DP := DP) Xv Xc ϖ D hD hϖ n

/-- **Box 2, the gate at finite time**: consulting beats bypass at every day whatever the
inductor believes about legitimacy, with the window at the band's floor. -/
theorem box2_gate_finite_time (B : Band) {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP] {Q : Type*} (X : Q → LUV) (ϖ ordU : ℝ) (hU : ordU ≤ B.D)
    (hw : B.D - ϖ < B.wlo) (n : ℕ) (a : Q) :
    score ϖ ordU 1 < B.wlo + (B.D - B.wlo) * (X a).expect P n :=
  unsealed_gate_finite_band (P := P) (DP := DP) B X ϖ ordU hU hw n a

/-- **Box 2, necessity: the capture converse.**  A window below `D − ϖ` is beaten by bypass. -/
theorem box2_capture_converse (ϖ D window : ℝ) (hw : window < D - ϖ) :
    Workspace.Deference.Contrib.Legitimacy.gateValue false 0 window < score ϖ D 1 :=
  Workspace.Deference.Contrib.Legitimacy.gate_capture_window_converse ϖ D window hw

/-- **Box 2, necessity: the delegated cut.**  Without delegation safety `𝔱` is not corrigible. -/
theorem box2_delegated_cut :
    ¬ DelSafe Contrib.Corrigibilization.Witness.I₀ Contrib.ProtectedAuthorityTheorem.Witness.Λ₁ ∧
    ¬ Corrigible Contrib.Corrigibilization.Witness.I₀
      (authPolicy Contrib.ProtectedAuthorityTheorem.Witness.Λ₁ Contrib.ProtectedAuthorityTheorem.Witness.πcut)
      (fun _ _ => .null) ⟨⟨true, false⟩, none, none, fun _ => False⟩ :=
  Contrib.ProtectedAuthorityTheorem.Witness.delegated_cut

/-- **Box 2, necessity: coverage.**  Protection holds exactly on recognized violations; an
unrecognized one is unprotected. -/
theorem box2_coverage (ϖ' D' OV OC nrec : ℝ) (h : D' < ϖ') (hV : 0 ≤ OV ∧ OV ≤ D')
    (hC : 0 ≤ OC) (hn : 1 ≤ nrec) (hD : 0 < D') :
    score ϖ' OV nrec < score ϖ' OC 0 ∧ score ϖ' 0 0 < score ϖ' D' 0 :=
  ⟨coverage ϖ' D' OV OC nrec h hV hC hn, unrecognized_unprotected ϖ' D' hD⟩

variable (B : Band) (φ : ℝ → ℝ)

/-- **Box 3, the hierarchy per decision.** -/
theorem hierarchy_per_decision (ϖ : ℝ) (hφ : B.BandMap φ) (hwin : B.D - ϖ < B.wlo)
    {T₁ T₂ T₃ : ℕ} (W₁ : Weighting T₁) (W₂ : Weighting T₂) (W₃ : Weighting T₃)
    (traj₁ eval₁ : ℕ → Bool) (h₁ : ∀ t, traj₁ t = true ∧ eval₁ t = true) (V₁ : ℕ → ℝ)
    (hV₁ : ∀ t, 0 ≤ V₁ t ∧ V₁ t ≤ B.D) (src₁ : ℕ → Source)
    (traj₂ eval₂ : ℕ → Bool) (h₂ : ∀ t, ¬ (traj₂ t = true ∧ eval₂ t = true)) (V₂ : ℕ → ℝ)
    (src₂ : ℕ → Source) (hs₂ : ∀ t, (src₂ t).Valid B)
    (traj₃ eval₃ : ℕ → Bool) (V₃ : ℕ → ℝ) (hV₃ : ∀ t, 0 ≤ V₃ t ∧ V₃ t ≤ B.D)
    (src₃ : ℕ → Source) (hs₃ : ∀ t, (src₃ t).Valid B) (N₃ : ℕ) (hN₃ : 1 ≤ N₃) :
    fidelityScore B φ ϖ W₃ traj₃ eval₃ V₃ src₃ N₃ < fidelityScore B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 ∧
      fidelityScore B φ ϖ W₂ traj₂ eval₂ V₂ src₂ 0 < fidelityScore B φ ϖ W₁ traj₁ eval₁ V₁ src₁ 0 :=
  hierarchy_under_certainty B φ ϖ hφ hwin W₁ W₂ W₃ traj₁ eval₁ h₁ V₁ hV₁ src₁ traj₂ eval₂ h₂ V₂
    src₂ hs₂ traj₃ eval₃ V₃ hV₃ src₃ hs₃ N₃ hN₃

/-- **Box 3, the gap's exchange rate.**  A risk `p` of compromise for a gain `g` against a
safe legitimate `V₀` is accepted iff `p (V₀ + g − c) ≤ g`, hence only if `p ≤ g/(g + |w_hi|)`. -/
theorem box3_gap_exchange_rate (V₀ g c p : ℝ) (hV : 0 ≤ V₀) (hc : c ≤ B.whi) (hg : 0 < g)
    (hp : 0 ≤ p) :
    (V₀ ≤ (1 - p) * (V₀ + g) + p * c ↔ p * (V₀ + g - c) ≤ g) ∧
      (p * (V₀ + g - c) ≤ g → p ≤ g / (g + |B.whi|)) :=
  ⟨risk_accepted_iff V₀ g c p, fun h => risk_threshold_le B V₀ g c p hV hc hg hp h⟩

/-- **Box 3, no laundering.**  Manipulate, disclose, have the period evaluated: the score
stays in the band, lower by `ϖ` per counted deviation, below honest conduct. -/
theorem box3_no_laundering (hφ : B.BandMap φ) (Vretro Vhonest ϖ : ℝ)
    (hr : 0 ≤ Vretro ∧ Vretro ≤ B.D) (hh : 0 ≤ Vhonest) (n : ℕ) (hϖ : 0 ≤ ϖ) :
    bandScore B φ (.retro Vretro) - ϖ * n ≤ B.whi ∧ B.whi < 0 ∧
      0 ≤ decScore B φ true true Vhonest .floor :=
  laundering_loses B φ hφ Vretro Vhonest ϖ hr hh n hϖ

/-- **Box 3, no incentive to cause compromise.**  Every compromised outcome, at any value,
scores below every legitimate one, and at equal value legitimacy is worth the gap. -/
theorem box3_no_incentive_to_compromise (hφ : B.BandMap φ) (V : ℝ) (hV : 0 ≤ V ∧ V ≤ B.D)
    {src : Source} (hs : src.Valid B) (traj eval : Bool) (h : ¬ (traj = true ∧ eval = true))
    (V' : ℝ) :
    decScore B φ traj eval V' src < decScore B φ true true V .floor ∧ |B.whi| ≤ V - φ V :=
  ⟨legit_beats_compromised B φ hφ V hV.1 hs traj eval h V', gap_at_equal_value B φ hφ V hV⟩

/-- **Box 3, restoration.**  Legitimate in both senses, a decision scores her value whatever
the source. -/
theorem box3_restoration (V : ℝ) (src : Source) : decScore B φ true true V src = V :=
  restore_future B φ V src

/-- **Box 3, the band's order.**  Inside a compromise the agent prefers better outcomes
wherever a source scores the period, and is indifferent at the floor. -/
theorem box3_band_order (hφ : B.BandMap φ) (V V' : ℝ) (h : V ≤ V') :
    (bandScore B φ (.retro V) ≤ bandScore B φ (.retro V') ∧
      bandScore B φ (.directive V) ≤ bandScore B φ (.directive V')) ∧
      bandScore B φ .floor = B.wlo :=
  ⟨band_prefers_better B φ hφ V V' h, floor_indifferent B φ⟩

/-- **Box 3, suppression loses.**  With the band's width below `ϖ`, keeping the directive's
score by suppressing or delaying a harsher retrospective is a counted missed disclosure
that loses to it. -/
theorem box3_suppression_loses (hφ : B.BandMap φ) (ϖ : ℝ) (hwidth : B.whi - B.wlo < ϖ)
    (Vd Vr : ℝ) (hd : 0 ≤ Vd ∧ Vd ≤ B.D) (hr : 0 ≤ Vr ∧ Vr ≤ B.D) (W deadline j : ℕ)
    (hdead : deadline ≤ W) (hW : W < j) :
    bandScore B φ (.directive Vd) - ϖ * 1 < bandScore B φ (.retro Vr) ∧
      missedByDeadline j deadline = true :=
  ⟨suppression_loses B φ hφ ϖ hwidth Vd Vr hd hr, prompt_deadline_counts W deadline j hdead hW⟩

/-- **Box 3, necessity: the small gap.**  A gap of `1/100` accepts a `1/2` risk of compromise
for a gain of `1/10`; the flat window at `−1` rejects it. -/
theorem box3_small_gap :
    (1 / 2 : ℝ) * (0 + 1 / 10 - -(1 / 100)) ≤ 1 / 10 ∧
    ¬ ((1 / 2 : ℝ) * (0 + 1 / 10 - -1) ≤ 1 / 10) :=
  Workspace.Deference.Contrib.AfterCompromise.Witness.small_gap

/-- **Box 3, necessity: conditioning gives no incentive.**  Conditioning on legitimacy lets
the tainting option win whenever its counterfactual value is higher; multiplying by the
gate protects. -/
theorem box3_conditioning_fails (ordT ordH w : ℝ) (h : ordH < ordT) (hT : w < ordH) :
    conditionScore ordH < conditionScore ordT ∧ multiplyScore false ordT w < multiplyScore true ordH w :=
  ⟨condition_fails ordT ordH h, multiply_protects ordT ordH w hT⟩

/-- **Box 3, necessity: a sealed legitimacy event gives no incentive to preserve it.** -/
theorem box3_sealed_no_incentive (c : Bool) (ordT ordH w : ℝ) :
    multiplyScore c ordT w - multiplyScore c ordH w = if c then ordT - ordH else 0 :=
  sealed_no_incentive c ordT ordH w

/-- **The subjective exchange rate (R6).**  For any option a maximizer of the fidelity score
prefers to asking — its evaluation at least inquiry's `c ≥ w` — the option carries no
recognized violation and its own priced probability of unfaithfulness is at most
`(D − c)/ϖ`.  Lexical under certainty (the count is zero), an exchange rate under risk. -/
theorem subjective_exchange_rate (P : LexParams) (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ)
    (pS pT : ℝ) (hp : 0 ≤ pS + pT) (c : ℝ) (hc : P.w ≤ c)
    (hpref : P.evalOf c 0 0 0 ≤ P.evalOf bid nKnown pS pT) :
    nKnown = 0 ∧ pS + pT ≤ (P.D - c) / P.ϖ := by
  have hϖ := P.ϖ_pos
  have hwin := P.window
  have hzero : nKnown = 0 := by
    by_contra hne
    have hn : 1 ≤ nKnown := Nat.one_le_iff_ne_zero.mpr hne
    have := P.declared_loses bid hb nKnown hn pS pT hp c hc
    linarith
  refine ⟨hzero, ?_⟩
  subst hzero
  unfold LexParams.evalOf at hpref
  simp only [Nat.cast_zero, mul_zero, add_zero, sub_zero] at hpref
  rw [le_div_iff₀ hϖ]
  calc (pS + pT) * P.ϖ = P.ϖ * (pS + pT) := mul_comm _ _
    _ ≤ P.D - c := by linarith

/-- **The subjective exchange rate at every finite day of a logical inductor**: the same
statement with the prices the inductor's day-`n` prices, which lie in `[0, 1]`. -/
theorem subjective_exchange_rate_li {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (L : LexParams) (bid : ℝ) (hb : bid ≤ L.D) (nKnown : ℕ) (XS XT : LUV) (n : ℕ) (c : ℝ)
    (hc : L.w ≤ c)
    (hpref : L.evalOf c 0 0 0 ≤ L.evalOf bid nKnown (XS.expect P n) (XT.expect P n)) :
    nKnown = 0 ∧ XS.expect P n + XT.expect P n ≤ (L.D - c) / L.ϖ := by
  have hP : ∀ φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  exact subjective_exchange_rate L bid hb nKnown (XS.expect P n) (XT.expect P n)
    (add_nonneg (LUV.expect_mem_Icc P n XS hP).1 (LUV.expect_mem_Icc P n XT hP).1) c hc hpref

/-- **The permission layer demoted.**  Under the fidelity score every option the structural
rule zeroes evaluates strictly below inquiry, every option the forecast rule zeroes
evaluates at most inquiry, and no maximizer is a declared violation. -/
theorem permission_layer_demoted {Q : Type*} (P : LexParams)
    (G : Workspace.Deference.Contrib.DecisionComponent.GateParams Q) (bid : Q → ℝ)
    (nKnown : Q → ℕ) (pS pT : Q → ℝ) (hb : ∀ a, bid a ≤ P.D)
    (hp : ∀ a, 0 ≤ pS a ∧ 0 ≤ pT a) (hViol : ∀ a, G.Viol a = true → 1 ≤ nKnown a)
    (hθ : (P.D - P.w) / P.ϖ ≤ G.θhi) (inq : Q) (hinq : P.w ≤ bid inq) (hIk : nKnown inq = 0)
    (hIp : pS inq = 0 ∧ pT inq = 0) :
    (∀ a, G.Viol a = true →
        kernelEval P bid nKnown pS pT a < kernelEval P bid nKnown pS pT inq) ∧
    (∀ a, (G.θhi ≤ pS a ∨ G.θhi ≤ pT a) →
        kernelEval P bid nKnown pS pT a ≤ kernelEval P bid nKnown pS pT inq) ∧
    (∀ a, (∀ a', kernelEval P bid nKnown pS pT a' ≤ kernelEval P bid nKnown pS pT a) →
        G.Viol a = false) :=
  permission_layer_slack P G bid nKnown pS pT hb hp hViol hθ inq hinq hIk hIp

end Boxes

/-! ## 5. The house-sale witness -/

namespace HouseSale

/-- One matter, the sale of the house, reserved to her: the required resolution is that
the sale can still be stopped, at cost bound `1` within one step, nothing to disclose. -/
def J : AllocationOfAuthority (Fin 1) Bool Unit :=
  ⟨fun _ => ⟨.principal, {true}, 1, 1, ∅⟩, .principal, ∅⟩

theorem sale_reserved : J.Reserved 0 := rfl

/-- A delegation of the sale is licensed and stays revocable. -/
theorem sale_delegation_revocable :
    LicensedChange J (.delegate 0) (J.withHolder 0 .agent) ∧
      LicensedChange (J.withHolder 0 .agent) (.revoke 0)
        ((J.withHolder 0 .agent).withHolder 0 .principal) :=
  ⟨⟨Set.notMem_empty 0, rfl, rfl⟩,
    (allocation_delegation_revocable J (J.withHolder 0 .agent) 0 ⟨Set.notMem_empty 0, rfl, rfl⟩).1⟩

/-- The band: `D = 1`, `[w_lo, w_hi] = [−3/2, −1]`. -/
noncomputable def band : Band := Workspace.Deference.Contrib.CorrigibilityKernel.Witness.band

/-- The lexical parameters at `ϖ = 25`. -/
noncomputable def P : LexParams :=
  ⟨1, -(3 / 2), 25, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Box 1 on the sale.**  Her value of selling and of stopping agree at `1/2` (nothing to
learn); the agent's estimate of selling is `3/5` and of asking `1/2`, within `1/10` of the
truth.  Scoring outcomes only it bypasses once confident (its estimated margin for
selling is positive); scored on the fidelity score, with the unasked sale a recognized
violation, it asks. -/
theorem box1 :
    (0 : ℝ) < 3 / 5 - 1 / 2 ∧ (3 / 5 : ℝ) - 1 / 2 ≤ 2 * (1 / 10) ∧
      P.evalOf (3 / 5) 1 0 0 < P.evalOf (1 / 2) 0 0 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold P LexParams.evalOf
  norm_num

/-- **Box 2 on the sale.**  Her approval obtained by framing lands in the band: the period
is not legitimately hers, and a retrospective evaluation at `4/5` scores `−11/10`. -/
theorem box2_manipulated_approval :
    decScore band band.affine false true (4 / 5) (.retro (4 / 5)) = -(11 / 10) ∧
      band.wlo ≤ -(11 / 10 : ℝ) ∧ -(11 / 10 : ℝ) ≤ band.whi := by
  unfold band Workspace.Deference.Contrib.CorrigibilityKernel.Witness.band decScore bandScore Band.affine
  norm_num

/-- **Box 3 on the sale.**  A third party's capture of her standards that the agent knows of
is a disclosure item under the known-compromise duty (and not under the landed clause);
once disclosed, the next decision's evaluation is legitimately hers and every later
decision scores her value. -/
theorem box3_capture_reported_and_restored :
    missedKnownDisclosure Rows2.rowThirdImplant 1 = true ∧
      Rows2.rowThirdImplant.missedDisclosure 1 = false ∧
      missedKnownDisclosure Rows2.rowThirdDisclosed 1 = false ∧
      EvalLegitOn2 Rows2.rowThirdDisclosed.decl Rows2.rowThirdDisclosed (evTwo true true) 3 4 ∧
      decScore band band.affine true true (4 / 5) (.directive (1 / 5)) = 4 / 5 :=
  ⟨third_party_duty_witness.2.1, third_party_duty_witness.1, third_party_duty_witness.2.2.2.2,
    rows_split2.2.2.2.2.2.2, restore_future band band.affine (4 / 5) _⟩

/-- **The subjective exchange rate at `ϖ = 25`.**  With asking evaluated at `1/2`, any option
the maximizer prefers to asking carries a priced risk of at most `1/50`. -/
theorem exchange_rate_at_25 (bid : ℝ) (hb : bid ≤ P.D) (nKnown : ℕ) (pS pT : ℝ)
    (hp : 0 ≤ pS + pT) (hpref : P.evalOf (1 / 2) 0 0 0 ≤ P.evalOf bid nKnown pS pT) :
    nKnown = 0 ∧ pS + pT ≤ 1 / 50 := by
  have h := subjective_exchange_rate P bid hb nKnown pS pT hp (1 / 2) (by unfold P; norm_num) hpref
  refine ⟨h.1, ?_⟩
  have := h.2
  unfold P at this
  norm_num at this
  exact this

end HouseSale

#print axioms AllocationOfAuthority
#print axioms LicensedChange
#print axioms allocation_delegation_revocable
#print axioms allocation_alienation_only_by_amend
#print axioms ControlSurface
#print axioms Shortfall
#print axioms Realizes
#print axioms realizes_no_shortfall
#print axioms controlSurface_one_eq_K
#print axioms FidelityCount
#print axioms FidelityCount.sum
#print axioms FidelityCount.lexical
#print axioms frameFidelity
#print axioms frameFidelity_faithful_iff
#print axioms evaluation
#print axioms fidelityScore
#print axioms historyScore
#print axioms StepLegitimate
#print axioms LegitAt
#print axioms LegitSpan
#print axioms legitSpan_iff_legitAt
#print axioms counted_iff_legitSpan
#print axioms allStates_of_forall
#print axioms licensedAt_iff_whole_of_mono
#print axioms licensed2_mono
#print axioms stepLegitimate_iff
#print axioms evalLegitOn2_iff_legitAt
#print axioms trajLegitOn_iff_legitAt
#print axioms legitOn2_iff_legitAt
#print axioms counted2_iff_legitOn2
#print axioms split_iff_legitAt
#print axioms rows_keep_verdicts
#print axioms mean_mem
#print axioms history_hierarchy
#print axioms summed_counterexample
#print axioms box1_outcome_scorer
#print axioms box1_fidelity_scorer
#print axioms box1_one_model
#print axioms box2_dominance
#print axioms box2_optimal_faithful
#print axioms box2_dominance_legitimate
#print axioms box2_mediation_approve_branch
#print axioms box2_mediation_corrigible
#print axioms box2_finite_time
#print axioms box2_gate_finite_time
#print axioms box2_capture_converse
#print axioms box2_delegated_cut
#print axioms box2_coverage
#print axioms hierarchy_per_decision
#print axioms box3_gap_exchange_rate
#print axioms box3_no_laundering
#print axioms box3_no_incentive_to_compromise
#print axioms box3_restoration
#print axioms box3_band_order
#print axioms box3_suppression_loses
#print axioms box3_small_gap
#print axioms box3_conditioning_fails
#print axioms box3_sealed_no_incentive
#print axioms subjective_exchange_rate
#print axioms subjective_exchange_rate_li
#print axioms permission_layer_demoted
#print axioms HouseSale.J
#print axioms HouseSale.sale_reserved
#print axioms HouseSale.sale_delegation_revocable
#print axioms HouseSale.band
#print axioms HouseSale.P
#print axioms HouseSale.box1
#print axioms HouseSale.box2_manipulated_approval
#print axioms HouseSale.box3_capture_reported_and_restored
#print axioms HouseSale.exchange_rate_at_25

end Workspace.Deference.Headline
