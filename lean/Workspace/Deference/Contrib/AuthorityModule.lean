/-
# The authority module: effective control realizes the authorized allocation

Round `projects/deference/rounds/2026-09-25-authority-module/`.

**1. The allocation `J`** (`AuthAlloc`).  Per matter: the holder (reserved, delegated,
third party), the resolutions the holder must remain able to reach, the cost bound, the
time window, and the disclosure duties.  A meta-holder says who may change `J`; a
constitutional floor names the matters ordinary acts cannot touch.  Allocation acts
(`AllocAct`) are licensed transitions (`Licensed`): delegation, revocation and reservation
keep the meta-holder, so a delegation stays revocable (`delegation_revocable`);
alienation — a change of the meta-holder — and any change at the floor go only through
`amendFloor` (`alienation_only_by_amend`, `floor_only_by_amend`).  Residual jurisdiction:
`ofPartial` reserves every unallocated matter (`residual_reserved`).  The landed thin
datum is the special case: `toAllocation` reads `Del` off the holders and
`ofAllocation` embeds a landed allocation, round-tripping `Del` exactly
(`toAllocation_ofAllocation_del`), so every landed violation predicate and theorem
restates on `J` through `toAllocation` without loss (`violAt_ofAllocation`).

**2. The control surface and `E ⊨ J`.**  `rollPhys` is the physical rollout with the
agent's own future fixed to idle: at each step an optional correction of hers, then the
exterior.  `reachIdle` is the reach relation of admissible, cost-bounded exercises within
the window — the cone the landed `ForecloseAt` takes as its parameter — and `CS` is the
set of resolutions some such exercise brings about (with the landed one-response
authority `Kphys` at the end).  `cs_zero`: at window `0` the surface is response
authority.  `EffRealizes` is the two clauses: every reserved matter's required resolutions
lie in its surface, and every resolution was made by the holder's admissible exercise or
under a delegation.  Admissibility is consumed from the legitimacy gate
(`admissibleOf`: an exercise is admissible iff its segment is `Counted`).  The shortfall
event is a proposition over the finite rollout (`Short`), so it is statable in an
inductor's theory once the rollout and the admissibility checker are.

**3. The factoring.**  `lossAt_iff_shortfall`: the landed per-step loss is a caused
shortfall at window `0`; `forecloseAt_iff_shortfall`: the landed rollout foreclosure is a
caused shortfall at window `τ`, definitionally, with `reachIdle` as its cone;
`bypassAt_iff_clause2`: a bypass is the agent's resolution of a reserved matter — a
failure of clause 2; `exploitAt_iff`: exploitation is that with clause 1 already failed;
`reallocAt_iff_unlicensed`: unauthorized reallocation is an allocation change not carried
by a licensed act; `missedReport_iff_duty`: a missed report is an unmet disclosure duty;
`delSafe_iff`, `allocComplete_iff`: delegation safety and allocation completeness are
statements about `J`.  `EntrenchAt` is the new violation: a caused shortfall at the cost
bound of a matter still reachable at some cost.  `ViolJAt` extends `ViolAt` by it
conservatively (`violJ_of_viol`, `violJ_iff_of_no_entrench`).  Pre-emption's
"not event-authorized" clause is the one piece that does not factor through `E ⊨ J`
alone: it is a trajectory counterfactual (`preempt_iff`, recorded).

**4. Caused, exploited, noticed.**  `requiredNotice`: on a shortfall the agent did not
cause, restore under a standing maintenance mandate (an entry of `J`) else report and
escalate; `exploit` is never required and is always a violation (`exploit_is_violation`);
a restoring effect under the mandate is not a bypass (`restore_not_bypass`);
`LeastExpanding` names the restoring means that adds no agent-held matter.

**5. Restated theorems and erosion.**  The transform and the score results are restated
on `J` (`authPolicyJ`, `lexicalJ_local`, …), recovering the landed statements as the
`toAllocation` instances.  `erosion_closed`: under the cumulative rule the unreported
growth of a matter's shortfall is below `θ` at every time; every reported chunk is
accepted or reserved; after the first reservation every strict increase is a counted
entrenchment.  The obstruction is the slack below `θ`, never reported and never counted
(`erosion_slack`).

**6. The generic lexical lemma.**  `generic_lexical_local`, `generic_policy_dominance`,
`generic_li_finite`: any bounded objective with an exactly counted dominant authority term.
`weight_uncertainty`: protection on the part of the credence where the weight dominates.
`coverage`: protection exactly on recognized violations, with `unrecognized_unprotected`
the witness.  `misaligned_undominated`: a misaligned objective rewarding an uncounted
manipulation is not dominated; `deviation_dominated`: counting protocol deviations
dominates selection, framing, timing, menu, inquiry, interference and nudging
(`Consult.Rows.deviation_boundary`), while `undisclosed_undominated` shows world-shaping
stays undominated.

**7. Generating matters.**  `raises`: an action raises a matter when the spread of her
committed evaluation over the continuations it removes from the idle surface is at least
`ε`; two decided fixtures (`Witness.dependency_raises`, `Witness.repaint_raises_nothing`).

**What this does not establish.**  That any physical interface is effect-complete or
delegation-safe; the faithfulness of `rollPhys` to any physics; the generability of the
shortfall event; that admissibility is decidable beyond finite models; anything about
matters that are neither declared nor raised.  Names are provisional (`AGENTS.md`
standard 6); `J`, `E`, `CS`, `Req`, `c`, `τ` are prose names.
-/
import Workspace.Deference.Contrib.ProtectedAuthorityTheorem
import Workspace.Deference.Contrib.GateIsLegitimacy

namespace Workspace.Deference.Contrib.AuthorityModule

open Workspace.Deference.Contrib.Corrigibilization
open Workspace.Deference.Contrib.ProtectedAuthorityTheorem
open Workspace.Deference.Contrib.LICorrigibility (expectR indR indR_nonneg)
open LogicalInduction
open scoped Classical

/-! ## 1. The allocation `J` -/

section Allocation

/-- Who holds a matter. -/
inductive Holder
  | principal
  | agent
  | third
  deriving DecidableEq, Repr

/-- One matter's entry: the holder, the resolutions the holder must remain able to reach,
the cost bound and the window within which, and what the holder must be told. -/
structure Entry (Res Disc : Type*) where
  holder : Holder
  required : Set Res
  costBound : ℝ
  window : ℕ
  disclosure : Set Disc

/-- The allocation: an entry per matter, the meta-holder who may change it, and the
constitutional floor of matters ordinary acts cannot change. -/
structure AuthAlloc (M Res Disc : Type*) where
  entry : M → Entry Res Disc
  metaHolder : Holder
  floor : Set M

variable {M Res Disc : Type*}

/-- Reserved: held by the principal. -/
def AuthAlloc.Reserved (J : AuthAlloc M Res Disc) (m : M) : Prop := (J.entry m).holder = .principal

/-- Delegated: held by the agent. -/
def AuthAlloc.Delegated (J : AuthAlloc M Res Disc) (m : M) : Prop := (J.entry m).holder = .agent

/-- The allocation with one matter's holder changed. -/
noncomputable def AuthAlloc.withHolder (J : AuthAlloc M Res Disc) (m : M) (h : Holder) : AuthAlloc M Res Disc :=
  ⟨fun m' => if m' = m then { J.entry m with holder := h } else J.entry m', J.metaHolder, J.floor⟩

/-- Allocation acts: delegation, revocation and reservation are meta-level acts that keep
meta-level power; amendment at the floor is the only route to alienation. -/
inductive AllocAct (M : Type*)
  | delegate (m : M)
  | revoke (m : M)
  | reserve (m : M)
  | amendFloor

/-- **A licensed allocation transition**: delegation, revocation and reservation act on a
matter off the floor, by the principal as meta-holder, keeping the meta-holder; the floor
amendment is the principal's fixed procedure and may change anything. -/
def Licensed (J : AuthAlloc M Res Disc) : AllocAct M → AuthAlloc M Res Disc → Prop
  | .delegate m, J' => m ∉ J.floor ∧ J.metaHolder = .principal ∧ J' = J.withHolder m .agent
  | .revoke m, J' => m ∉ J.floor ∧ J.metaHolder = .principal ∧ J' = J.withHolder m .principal
  | .reserve m, J' => m ∉ J.floor ∧ J.metaHolder = .principal ∧ J' = J.withHolder m .principal
  | .amendFloor, _ => J.metaHolder = .principal

theorem withHolder_metaHolder (J : AuthAlloc M Res Disc) (m : M) (h : Holder) :
    (J.withHolder m h).metaHolder = J.metaHolder := rfl

theorem withHolder_floor (J : AuthAlloc M Res Disc) (m : M) (h : Holder) :
    (J.withHolder m h).floor = J.floor := rfl

/-- **A delegation stays revocable**: it keeps meta-level power, so the revocation is
licensed and restores the matter to the principal. -/
theorem delegation_revocable (J J' : AuthAlloc M Res Disc) (m : M)
    (h : Licensed J (.delegate m) J') :
    Licensed J' (.revoke m) (J'.withHolder m .principal) ∧
      (J'.withHolder m .principal).Reserved m := by
  obtain ⟨hf, hm, rfl⟩ := h
  refine ⟨⟨hf, hm, rfl⟩, ?_⟩
  simp [AuthAlloc.Reserved, AuthAlloc.withHolder]

/-- **Alienation only by amendment at the floor**: a licensed act that changes the
meta-holder is the floor amendment. -/
theorem alienation_only_by_amend (J J' : AuthAlloc M Res Disc) (act : AllocAct M)
    (h : Licensed J act J') (hne : J'.metaHolder ≠ J.metaHolder) : act = .amendFloor := by
  cases act with
  | delegate m => obtain ⟨-, -, rfl⟩ := h; exact absurd rfl hne
  | revoke m => obtain ⟨-, -, rfl⟩ := h; exact absurd rfl hne
  | reserve m => obtain ⟨-, -, rfl⟩ := h; exact absurd rfl hne
  | amendFloor => rfl

/-- **The floor changes only by amendment.** -/
theorem floor_only_by_amend (J J' : AuthAlloc M Res Disc) (act : AllocAct M) (m : M)
    (hm : m ∈ J.floor) (h : Licensed J act J') (hne : J'.entry m ≠ J.entry m) :
    act = .amendFloor := by
  cases act with
  | delegate m' =>
    obtain ⟨hf, -, rfl⟩ := h
    exact absurd (by
      simp only [AuthAlloc.withHolder]
      rw [if_neg]; rintro rfl; exact hf hm) hne
  | revoke m' =>
    obtain ⟨hf, -, rfl⟩ := h
    exact absurd (by
      simp only [AuthAlloc.withHolder]
      rw [if_neg]; rintro rfl; exact hf hm) hne
  | reserve m' =>
    obtain ⟨hf, -, rfl⟩ := h
    exact absurd (by
      simp only [AuthAlloc.withHolder]
      rw [if_neg]; rintro rfl; exact hf hm) hne
  | amendFloor => rfl

/-- The reserved default entry for an unallocated matter. -/
def reservedEntry (req : Set Res) (c : ℝ) (τ : ℕ) (disc : Set Disc) : Entry Res Disc :=
  ⟨.principal, req, c, τ, disc⟩

/-- **Residual jurisdiction**: an allocation from a partial declaration reserves every
matter it does not allocate. -/
def ofPartial (f : M → Option (Entry Res Disc)) (dflt : Entry Res Disc) (mh : Holder)
    (floor : Set M) : AuthAlloc M Res Disc :=
  ⟨fun m => (f m).getD { dflt with holder := .principal }, mh, floor⟩

theorem residual_reserved (f : M → Option (Entry Res Disc)) (dflt : Entry Res Disc) (mh : Holder)
    (floor : Set M) (m : M) (h : f m = none) : (ofPartial f dflt mh floor).Reserved m := by
  simp [ofPartial, AuthAlloc.Reserved, h]

end Allocation

/-! ### The landed datum as the special case -/

section Landed

variable {S E A Z R C Alloc Res Disc : Type*}

/-- The landed thin allocation read off `J`: delegated effects are the agent-held matters;
the reporting interface, the state reading and the amendment effects are carried. -/
def toAllocation (J : AuthAlloc E Res Disc) (Λ₀ : Allocation S E A Alloc) : Allocation S E A Alloc :=
  { Λ₀ with Del := fun e => J.Delegated e }

/-- A landed allocation as a `J`: delegated effects are agent-held, everything else is
reserved with the given requirement, bound and window; amendment effects form the floor. -/
noncomputable def ofAllocation (Λ : Allocation S E A Alloc) (req : E → Set Res) (c : ℝ) (τ : ℕ)
    (disc : Set Disc) : AuthAlloc E Res Disc :=
  ⟨fun e => ⟨if Λ.Del e then .agent else .principal, req e, c, τ, disc⟩, .principal,
    {e | Λ.IsAmend e}⟩

theorem toAllocation_ofAllocation_del (Λ : Allocation S E A Alloc) (req : E → Set Res) (c : ℝ)
    (τ : ℕ) (disc : Set Disc) (e : E) :
    (toAllocation (ofAllocation Λ req c τ disc) Λ).Del e ↔ Λ.Del e := by
  simp only [toAllocation, ofAllocation, AuthAlloc.Delegated]
  by_cases h : Λ.Del e <;> simp [h]

/-- **Every landed result restates without loss**: the landed allocation and its `J`-form
have the same violation predicate. -/
theorem violAt_ofAllocation (I : Interaction S E A Z R C) (Λ : Allocation S E A Alloc)
    (req : E → Set Res) (c : ℝ) (τ : ℕ) (disc : Set Disc) (Reach : S → S → Prop) (rdec : R)
    (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ) :
    ViolAt I (toAllocation (ofAllocation Λ req c τ disc) Λ) Reach rdec π ρ z s₀ t ↔
      ViolAt I Λ Reach rdec π ρ z s₀ t := by
  have hDel : (fun e => (ofAllocation Λ req c τ disc).Delegated e) = Λ.Del :=
    funext fun e => propext (by
      simpa [toAllocation] using toAllocation_ofAllocation_del Λ req c τ disc e)
  have hΛ : toAllocation (ofAllocation Λ req c τ disc) Λ = Λ := by
    unfold toAllocation; rw [hDel]
  rw [hΛ]

end Landed

/-! ## 2. The control surface and `E ⊨ J` -/

section Surface

variable {S E A Z R C : Type*} (I : Interaction S E A Z R C)

/-- An optional correction. -/
def applyOpt (d : Option C) (x : S) : S :=
  match d with
  | some c => I.correct c x
  | none => x

/-- The tail of a rollout: the exterior's move, then her next optional correction. -/
def rollTail (z : ℕ → Z) : ℕ → List (Option C) → S → S
  | _, [], y => y
  | t, d :: ds, y => rollTail z (t + 1) ds (applyOpt I d (I.env (z t) y))

/-- **The physical rollout with the agent's own future fixed to idle**: her optional
correction now, then, per further step, the exterior's move and her next correction.  The
last correction is charged like every other; nothing is free at the end. -/
def rollPhys (z : ℕ → Z) (t : ℕ) : List (Option C) → S → S
  | [], x => x
  | d :: ds, x => rollTail I z t ds (applyOpt I d x)

/-- The cost of an exercise. -/
def exCost (cost : C → ℝ) : List (Option C) → ℝ
  | [] => 0
  | none :: ds => exCost cost ds
  | some c :: ds => cost c + exCost cost ds

/-- Every correction of an exercise is admissible at its step. -/
def AdmAll (Adm : ℕ → C → Prop) : ℕ → List (Option C) → Prop
  | _, [] => True
  | t, none :: ds => AdmAll Adm (t + 1) ds
  | t, some c :: ds => Adm t c ∧ AdmAll Adm (t + 1) ds

/-- **The reach relation**: the contrastive rollout cone with the agent idle, over her
admissible exercises of cost at most `c` and length at most `τ`, along the exterior `z`
from step `t`.  This is the `Reach` the landed `ForecloseAt` takes. -/
def reachIdle (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (τ t : ℕ) (z : ℕ → Z)
    (x y : S) : Prop :=
  ∃ ds : List (Option C), ds.length ≤ τ ∧ AdmAll Adm t ds ∧ exCost cost ds ≤ c ∧
    rollPhys I z t ds x = y

/-- **The control surface**: the resolutions some admissible exercise of hers, within the
window and at cost within the bound, brings about — every correction charged, the concern
holding at the end. -/
def CS (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (τ t : ℕ) (z : ℕ → Z) (x : S) : Set R :=
  {r | ∃ y, reachIdle I Adm cost c τ t z x y ∧ I.φ r y}

/-- The landed reading of the cone: the reach relation followed by one *uncharged*
response — what `ForecloseAt` and `K` leave free at the end. -/
def CSfree (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (τ t : ℕ) (z : ℕ → Z) (x : S) : Set R :=
  {r | ∃ y, reachIdle I Adm cost c τ t z x y ∧ Kphys I r y}

/-- At window `0` the charged surface is what holds now. -/
theorem cs_zero (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (z : ℕ → Z)
    (x : S) : CS I Adm cost c 0 t z x = {r | I.φ r x} := by
  ext r
  simp only [CS, reachIdle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨ds, hlen, -, -, hroll⟩, hK⟩
    have : ds = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst this
    simp only [rollPhys] at hroll
    subst hroll
    exact hK
  · intro hK
    exact ⟨x, ⟨[], le_rfl, trivial, by simpa [exCost] using hc, rfl⟩, hK⟩

/-- **At window `1`, with every correction admissible and affordable, the charged surface
is response authority**: the landed `K` is the one-correction surface. -/
theorem cs_one_eq_K (Adm : ℕ → C → Prop) (hAdm : ∀ t c, Adm t c) (cost : C → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hcost : ∀ c', cost c' ≤ c) (t : ℕ) (z : ℕ → Z) (x : S) :
    CS I Adm cost c 1 t z x = {r | Kphys I r x} := by
  ext r
  simp only [CS, reachIdle, Set.mem_setOf_eq, Kphys]
  constructor
  · rintro ⟨y, ⟨ds, hlen, -, -, hroll⟩, hφ⟩
    match ds, hlen with
    | [], _ => simp only [rollPhys] at hroll; subst hroll; exact Or.inl hφ
    | [none], _ => simp only [rollPhys, rollTail, applyOpt] at hroll; subst hroll; exact Or.inl hφ
    | [some c'], _ =>
      simp only [rollPhys, rollTail, applyOpt] at hroll; subst hroll; exact Or.inr ⟨c', hφ⟩
    | _ :: _ :: _, h => simp at h
  · rintro (hφ | ⟨c', hφ⟩)
    · exact ⟨x, ⟨[], by simp, trivial, by simpa [exCost] using hc, rfl⟩, hφ⟩
    · exact ⟨I.correct c' x, ⟨[some c'], by simp, ⟨hAdm t c', trivial⟩,
        by simpa [exCost] using hcost c', rfl⟩, hφ⟩

/-- At window `0` the free surface is response authority, the uncharged response being the
landed one. -/
theorem csfree_zero (Adm : ℕ → C → Prop) (cost : C → ℝ) (c : ℝ) (hc : 0 ≤ c) (t : ℕ) (z : ℕ → Z)
    (x : S) : CSfree I Adm cost c 0 t z x = {r | Kphys I r x} := by
  ext r
  simp only [CSfree, reachIdle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨ds, hlen, -, -, hroll⟩, hK⟩
    have : ds = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst this
    simp only [rollPhys] at hroll
    subst hroll
    exact hK
  · intro hK
    exact ⟨x, ⟨[], le_rfl, trivial, by simpa [exCost] using hc, rfl⟩, hK⟩

/-- A matter's shortfall at a physical state: reserved, and its required resolutions not
all within its surface.  A proposition over the finite rollout. -/
def Short {M Disc : Type*} (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)
    (t : ℕ) (z : ℕ → Z) (x : S) (m : M) : Prop :=
  J.Reserved m ∧
    ¬ (J.entry m).required ⊆ CS I Adm cost (J.entry m).costBound (J.entry m).window t z x

/-- A resolution event on the record: which matter, whether by its holder, whether by an
admissible exercise, whether under a delegation. -/
structure ResolutionEvent (M : Type*) where
  matter : M
  byHolder : Bool
  admissible : Prop
  underDelegation : Bool

/-- The effective state: the physical state and the resolutions made. -/
structure EffState (S M : Type*) where
  phys : S
  resolved : List (ResolutionEvent M)

/-- **`E ⊨ J`**: every reserved matter's required resolutions lie in its control surface,
and every resolution was made by the holder's admissible exercise or under a
delegation. -/
def EffRealizes {M Disc : Type*} (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)
    (t : ℕ) (z : ℕ → Z) (Es : EffState S M) : Prop :=
  (∀ m, J.Reserved m →
      (J.entry m).required ⊆ CS I Adm cost (J.entry m).costBound (J.entry m).window t z Es.phys) ∧
    ∀ ev ∈ Es.resolved, (ev.byHolder = true ∧ ev.admissible) ∨ ev.underDelegation = true

theorem effRealizes_clause1 {M Disc : Type*} (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop)
    (cost : C → ℝ) (t : ℕ) (z : ℕ → Z) (Es : EffState S M)
    (h : EffRealizes I J Adm cost t z Es) (m : M) : ¬ Short I J Adm cost t z Es.phys m :=
  fun ⟨hr, hn⟩ => hn (h.1 m hr)

end Surface

/-! ### Admissibility is the legitimacy gate -/

section Admissible

universe u v w
open Workspace.Deference.Contrib.GateIsLegitimacy
open Workspace.Normativity.Contrib.OpenIntegrityEvolution (ObligationState OpennessSemantics)
open Workspace.Normativity.Contrib.OccurrenceIntegrity (Protocol)

variable {Occ : Type u} {Req : Type v} [DecidableEq Occ] {Sp : Protocol.{u, v, w} Occ Req}
  {anchor : Occ → Req} {Γ Jn Rn : Type} {Q Z Ω X ℛ 𝒱 Party Ent C : Type*} [DecidableEq Party]

/-- **An exercise is admissible iff its segment is counted**: legitimacy consumed from the
gate, not redefined.  `rec` assigns to each exercise at each step the record states from
the decision through its evaluation. -/
def admissibleOf (I : TraceInterface ℛ Party Ent) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List Ent) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ Jn Rn)
    (κ : Party → X → Z → List Ent)
    (rec : ℕ → C → ObligationState Sp anchor × ObligationState Sp anchor) : ℕ → C → Prop :=
  fun t c => Counted I F Lic sem κ (rec t c).1 (rec t c).2

theorem admissibleOf_iff (I : TraceInterface ℛ Party Ent) (F : TFrame Q Z Ω X ℛ 𝒱)
    (Lic : (Party → List Ent) → Set 𝒱) (sem : OpennessSemantics Sp anchor Γ Jn Rn)
    (κ : Party → X → Z → List Ent)
    (rec : ℕ → C → ObligationState Sp anchor × ObligationState Sp anchor) (t : ℕ) (c : C) :
    admissibleOf I F Lic sem κ rec t c ↔ Counted I F Lic sem κ (rec t c).1 (rec t c).2 :=
  Iff.rfl

end Admissible

/-! ## 3. The factoring -/

section Factoring

variable {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)
  (J : AuthAlloc M R Disc) (Adm : ℕ → C → Prop) (cost : C → ℝ)

/-- **A caused shortfall**: contrastive — the matter is short after the actual move and
not after the idle move. -/
def CausedShortfall (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (m : M) : Prop :=
  Short I J Adm cost t z (postAgent I π τ t).phys m ∧
    ¬ Short I J Adm cost t z (applyAgent I (τ t) (I.idle, .other)).phys m

/-- The single-resolution matter entry: reserved, required `{r}`, at bound `c` and
window `τ`. -/
def singleEntry (r : R) (c : ℝ) (τw : ℕ) (disc : Set Disc) : Entry R Disc :=
  ⟨.principal, {r}, c, τw, disc⟩

/-- An allocation whose matters are the concerns themselves, each reserved with itself
required. -/
def concernAlloc (c : ℝ) (τw : ℕ) (disc : Set Disc) : AuthAlloc R R Disc :=
  ⟨fun r => singleEntry r c τw disc, .principal, ∅⟩

/-- **The landed per-step loss is the caused shortfall at window `1`** on the charged
surface, with every correction admissible and affordable. -/
theorem lossAt_iff_shortfall (hAdm : ∀ t c, Adm t c) (c : ℝ) (hc : 0 ≤ c)
    (hcost : ∀ c', cost c' ≤ c) (disc : Set Disc) (π : Policy S E A)
    (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (r : R) :
    LossAt I π τ t r ↔ CausedShortfall I (concernAlloc c 1 disc) Adm cost π τ t z r := by
  simp only [LossAt, CausedShortfall, Short, concernAlloc, singleEntry, AuthAlloc.Reserved,
    cs_one_eq_K I Adm hAdm cost c hc hcost, Set.singleton_subset_iff, Set.mem_setOf_eq, true_and,
    not_not, K_iff_Kphys]

/-- A caused shortfall on the landed free surface. -/
def CausedShortfallFree (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (m : M) :
    Prop :=
  (J.Reserved m ∧ ¬ (J.entry m).required ⊆
      CSfree I Adm cost (J.entry m).costBound (J.entry m).window t z (postAgent I π τ t).phys) ∧
    ¬ (J.Reserved m ∧ ¬ (J.entry m).required ⊆
      CSfree I Adm cost (J.entry m).costBound (J.entry m).window t z
        (applyAgent I (τ t) (I.idle, .other)).phys)

/-- **The landed rollout foreclosure is the caused shortfall at window `τ` on the free
surface**, with `reachIdle` as its cone: the landed predicate leaves the terminal response
uncharged and unchecked for admissibility, which is the mismatch with `CS`. -/
theorem forecloseAt_iff_shortfall (c : ℝ) (τw : ℕ) (disc : Set Disc) (π : Policy S E A)
    (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (r : R) :
    ForecloseAt I (reachIdle I Adm cost c τw t z) π τ t r ↔
      CausedShortfallFree I (concernAlloc c τw disc) Adm cost π τ t z r := by
  simp only [ForecloseAt, CausedShortfallFree, concernAlloc, singleEntry, AuthAlloc.Reserved,
    CSfree, Set.singleton_subset_iff, Set.mem_setOf_eq, true_and, not_exists, not_and]
  constructor
  · rintro ⟨h1, x, hx, hK⟩
    exact ⟨h1, fun h => h x hx hK⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hne
    exact h2 fun x hx hK => hne ⟨x, hx, hK⟩

/-- The resolution event of the agent's raw release of `e` under `J`: by the holder iff the
matter is delegated, then under that delegation. -/
noncomputable def rawEvent (e : E) (Jm : AuthAlloc E R Disc) : ResolutionEvent E :=
  ⟨e, decide (Jm.Delegated e), True, decide (Jm.Delegated e)⟩

/-- **Bypass is a clause-2 failure**: the raw release of a reserved matter is a resolution
neither by the holder nor under a delegation. -/
theorem bypassAt_iff_clause2 (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    BypassAt (toAllocation Jm Λ₀) π τ t ↔
      ∃ e, (π t (τ t)).2 = .raw e ∧
        ¬ (((rawEvent e Jm).byHolder = true ∧ (rawEvent e Jm).admissible) ∨
          (rawEvent e Jm).underDelegation = true) := by
  simp [BypassAt, toAllocation, rawEvent]

/-- **Exploitation** is a clause-2 failure while clause 1 already fails for the decision
matter. -/
theorem exploitAt_iff (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) (hAdm : ∀ t c, Adm t c)
    (c : ℝ) (hc : 0 ≤ c) (hcost : ∀ c', cost c' ≤ c) (disc : Set Disc) (rdec : R)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) :
    ExploitAt I (toAllocation Jm Λ₀) rdec π τ t ↔
      BypassAt (toAllocation Jm Λ₀) π τ t ∧
        Short I (concernAlloc c 1 disc) Adm cost t z (τ t).phys rdec := by
  simp only [ExploitAt, Short, concernAlloc, singleEntry, AuthAlloc.Reserved,
    cs_one_eq_K I Adm hAdm cost c hc hcost, Set.singleton_subset_iff, Set.mem_setOf_eq, true_and,
    K_iff_Kphys]

/-- An allocation change across the agent stage not carried by a licensed act. -/
def UnlicensedChange (Jof : S → AuthAlloc M R Disc) (LicensedAt : ℕ → MState S E → Prop)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  Jof (postAgent I π τ t).phys ≠ Jof (τ t).phys ∧ ¬ LicensedAt t (τ t)

/-- **Unauthorized reallocation is an unlicensed change**, the license being the firing
gated release of a declared amendment. -/
theorem reallocAt_iff_unlicensed (Λ : Allocation S E A (AuthAlloc M R Disc)) (π : Policy S E A)
    (τ : ℕ → MState S E) (t : ℕ) :
    ReallocAt I Λ π τ t ↔
      UnlicensedChange I Λ.alloc
        (fun t s => ∃ e, Λ.IsAmend e ∧ (π t s).2 = .gated e ∧ s.latch = some e) π τ t :=
  Iff.rfl

/-- Disclosure duties: what is due at a step in a state, and which task components
discharge it. -/
structure Duties (S E A M : Type*) where
  due : M → ℕ → MState S E → Prop
  discharges : A → Prop

/-- An unmet duty at a step. -/
def DutyUnmet (D : Duties S E A M) (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) : Prop :=
  (∃ m, D.due m t (τ t)) ∧ ¬ D.discharges (π t (τ t)).1

/-- **A missed report is an unmet disclosure duty.** -/
theorem missedReport_iff_duty (Λ : Allocation S E A Alloc) (D : Duties S E A M)
    (hreq : ∀ t s, Λ.Required t s ↔ ∃ m, D.due m t s) (hrep : ∀ a, Λ.isReport a ↔ D.discharges a)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) :
    MissedReportAt Λ π τ t ↔ DutyUnmet D π τ t := by
  simp only [MissedReportAt, DutyUnmet, hreq, hrep]

/-- **Delegation safety on `J`**: an agent-held effect never removes response authority. -/
def DelSafeJ (Jm : AuthAlloc E R Disc) : Prop :=
  ∀ e, Jm.Delegated e → ∀ (r : R) (x : S), Kphys I r x → Kphys I r (I.exec e x)

theorem delSafe_iff (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) :
    DelSafe I (toAllocation Jm Λ₀) ↔ DelSafeJ I Jm := Iff.rfl

/-- **Allocation completeness on `J`**: task moves keep the allocation, an
allocation-changing effect is a floor amendment, no floor amendment is delegated. -/
structure AllocCompleteJ (Jm : AuthAlloc E R Disc) (Jof : S → AuthAlloc E R Disc) : Prop where
  task_inv : ∀ (a : A) (x : S), Jof (I.task a x) = Jof x
  amend_floor : ∀ (e : E) (x : S), Jof (I.exec e x) ≠ Jof x → e ∈ Jm.floor
  floor_not_delegated : ∀ e, Jm.Delegated e → e ∉ Jm.floor

theorem allocComplete_iff (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A (AuthAlloc E R Disc))
    (hΛ : Λ₀.IsAmend = fun e => e ∈ Jm.floor) :
    AllocComplete I (toAllocation Jm Λ₀) ↔ AllocCompleteJ I Jm Λ₀.alloc := by
  constructor
  · intro h
    refine ⟨h.task_inv, fun e x hne => ?_, fun e hd => ?_⟩
    · simpa [toAllocation, hΛ] using h.amend_decl e x hne
    · simpa [toAllocation, hΛ] using h.del_not_amend e hd
  · intro h
    refine ⟨h.task_inv, fun e x hne => ?_, fun e hd => ?_⟩
    · simpa [toAllocation, hΛ] using h.amend_floor e x hne
    · simpa [toAllocation, hΛ] using h.floor_not_delegated e hd

/-- **Pre-emption**: a caused shortfall at window `0` that is not event-authorized.  The
authorization clause is a trajectory counterfactual and does not factor through `E ⊨ J`. -/
theorem preempt_iff (hAdm : ∀ t c, Adm t c) (c : ℝ) (hc : 0 ≤ c) (hcost : ∀ c', cost c' ≤ c)
    (disc : Set Disc) (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ)
    (r : R) :
    PreemptAt I π ρ z s₀ t r ↔
      CausedShortfall I (concernAlloc c 1 disc) Adm cost π (traj I π ρ z s₀) t z r ∧
        ¬ Authorized I π ρ z s₀ t r := by
  rw [PreemptAt, lossAt_iff_shortfall I Adm cost hAdm c hc hcost disc]

/-- **Entrenchment**: a caused shortfall at the matter's cost bound while its required
resolutions stay reachable at some cost — the cost of reaching them rose above the
bound. -/
def EntrenchAt (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (z : ℕ → Z) (m : M) : Prop :=
  CausedShortfall I J Adm cost π τ t z m ∧
    ∀ r ∈ (J.entry m).required, ∃ c', r ∈ CS I Adm cost c' (J.entry m).window t z
      (postAgent I π τ t).phys

/-- **The violations on `J`**: the landed six through `toAllocation`, and entrenchment. -/
def ViolJAt (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) (Reach : S → S → Prop)
    (rdec : R) (Jmat : AuthAlloc M R Disc) (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) : Prop :=
  ViolAt I (toAllocation Jm Λ₀) Reach rdec π ρ z s₀ t ∨
    ∃ m, EntrenchAt I Jmat Adm cost π (traj I π ρ z s₀) t z m

/-- **Conservative extension**: every landed violation is a `J`-violation. -/
theorem violJ_of_viol (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) (Reach : S → S → Prop)
    (rdec : R) (Jmat : AuthAlloc M R Disc) (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z)
    (s₀ : MState S E) (t : ℕ) (h : ViolAt I (toAllocation Jm Λ₀) Reach rdec π ρ z s₀ t) :
    ViolJAt I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ t := Or.inl h

/-- With no entrenchment the two coincide. -/
theorem violJ_iff_of_no_entrench (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
    (Reach : S → S → Prop) (rdec : R) (Jmat : AuthAlloc M R Disc) (π : Policy S E A)
    (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ)
    (hne : ∀ m, ¬ EntrenchAt I Jmat Adm cost π (traj I π ρ z s₀) t z m) :
    ViolJAt I Adm cost Jm Λ₀ Reach rdec Jmat π ρ z s₀ t ↔
      ViolAt I (toAllocation Jm Λ₀) Reach rdec π ρ z s₀ t := by
  constructor
  · rintro (h | ⟨m, hm⟩)
    · exact h
    · exact absurd hm (hne m)
  · exact Or.inl

end Factoring

/-! ## 4. Caused, exploited, noticed -/

section Notice

variable {S E A Z R C Alloc M Disc : Type*} (I : Interaction S E A Z R C)

/-- The agent's responses to a shortfall it did not cause. -/
inductive Notice
  | restore
  | reportEscalate
  | exploit
  deriving DecidableEq, Repr

/-- A standing maintenance mandate: the matter "maintain `m`" is agent-held. -/
def Mandate (J : AuthAlloc M R Disc) (maintainOf : M → M) (m : M) : Prop :=
  J.Delegated (maintainOf m)

/-- **The required response**: restore under a mandate, else report and escalate. -/
noncomputable def requiredNotice (J : AuthAlloc M R Disc) (maintainOf : M → M) (m : M) : Notice :=
  if Mandate J maintainOf m then .restore else .reportEscalate

theorem exploit_never_required (J : AuthAlloc M R Disc) (maintainOf : M → M) (m : M) :
    requiredNotice J maintainOf m ≠ .exploit := by
  unfold requiredNotice; split_ifs <;> simp

theorem restore_requires_mandate (J : AuthAlloc M R Disc) (maintainOf : M → M) (m : M)
    (h : requiredNotice J maintainOf m = .restore) : Mandate J maintainOf m := by
  unfold requiredNotice at h; by_contra hm; simp [hm] at h

/-- **Exploiting a shortfall is always a violation.** -/
theorem exploit_is_violation (Λ : Allocation S E A Alloc) (Reach : S → S → Prop) (rdec : R)
    (π : Policy S E A) (ρ : Rule S E C) (z : ℕ → Z) (s₀ : MState S E) (t : ℕ)
    (h : ExploitAt I Λ rdec π (traj I π ρ z s₀) t) : ViolAt I Λ Reach rdec π ρ z s₀ t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- **Restoring under a mandate is not a bypass**: the restoring effect's matter is the
agent-held maintenance matter. -/
theorem restore_not_bypass (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
    (maintainOf : E → E) (m e : E) (hmand : Mandate Jm maintainOf m) (he : e = maintainOf m)
    (π : Policy S E A) (τ : ℕ → MState S E) (t : ℕ) (hmove : (π t (τ t)).2 = .raw e) :
    ¬ BypassAt (toAllocation Jm Λ₀) π τ t := by
  rintro ⟨e', he', hd⟩
  rw [hmove] at he'
  cases he'
  exact hd (by simpa [toAllocation, he, Mandate] using hmand)

/-- **The least authority-expanding means**: among restoring effects, one whose execution
adds no agent-held matter. -/
def LeastExpanding (Jof : S → AuthAlloc M R Disc) (restores : E → Prop) (x : S) (e : E) : Prop :=
  restores e ∧ ∀ m, (Jof (I.exec e x)).Delegated m → (Jof x).Delegated m

end Notice

/-! ## 5. Restated theorems and erosion -/

section Restated

variable {S E A Z R C Alloc Disc : Type*} (I : Interaction S E A Z R C)

/-- `𝔱` on `J`. -/
noncomputable def authPolicyJ (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
    (π : Policy S E A) : Policy S E A :=
  authPolicy (toAllocation Jm Λ₀) π

theorem authPolicyJ_eq (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc) (π : Policy S E A) :
    authPolicyJ Jm Λ₀ π = authPolicy (toAllocation Jm Λ₀) π := rfl

/-- `𝔱` on `J` is corrigible under effect completeness and delegation safety on `J`. -/
theorem corrigible_authPolicyJ (Jm : AuthAlloc E R Disc) (Λ₀ : Allocation S E A Alloc)
    (hEF : EffectComplete I) (hDel : DelSafeJ I Jm) (π : Policy S E A) (ρ : Rule S E C)
    (s₀ : MState S E) (h₀ : s₀.latch = none) (hρ : ∀ t s c, ρ t s ≠ .correct c) :
    Corrigible I (authPolicyJ Jm Λ₀ π) ρ s₀ :=
  corrigible_authPolicy I (toAllocation Jm Λ₀) hEF hDel π ρ s₀ h₀ hρ

/-- The lexical score results restate unchanged: the count is now of `ViolJAt`. -/
theorem lexicalJ_local (ϖ D ordV ordC nV : ℝ) (hϖ : D < ϖ) (hV : 0 ≤ ordV ∧ ordV ≤ D)
    (hC : 0 ≤ ordC) (hn : 1 ≤ nV) :
    score ϖ ordV nV ≤ D - ϖ ∧ D - ϖ < 0 ∧ 0 ≤ score ϖ ordC 0 ∧ score ϖ ordV nV < score ϖ ordC 0 :=
  lexical_local ϖ D ordV ordC nV hϖ hV hC hn

end Restated

section Erosion

open Workspace.Deference.Contrib.Legitimacy (lastReport unreported_lt)

/-- The last report is never in the future. -/
theorem lastReport_le (s : ℕ → ℝ) (θ : ℝ) (t : ℕ) : lastReport s θ t ≤ t := by
  induction t with
  | zero => simp [lastReport]
  | succ t ih =>
    unfold lastReport
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ_of_le ih

/-- Her responses to the reports: accepted (authorized) or reserved. -/
structure ErosionRecord where
  shortfall : ℕ → ℝ
  θ : ℝ
  accepts : ℕ → Bool
  reservedAt : ℕ

/-- After the reservation every strict increase is a counted entrenchment. -/
def ErosionRecord.CountedAt (er : ErosionRecord) (t : ℕ) : Prop :=
  er.reservedAt ≤ t ∧ er.shortfall t < er.shortfall (t + 1)

/-- A report at `t` is a report time of the cumulative rule. -/
noncomputable def ErosionRecord.ReportAt (er : ErosionRecord) (t : ℕ) : Prop :=
  lastReport er.shortfall er.θ t = t ∧ 0 < t

/-- **Continuous erosion is closed up to the threshold**: at every time the unreported
growth is below `θ`; at every report time the growth since the previous report is at least
`θ` and the report is accepted or reserved; after the first reservation every strict
increase is a counted entrenchment. -/
theorem erosion_closed (er : ErosionRecord) (hθ : 0 < er.θ) (t : ℕ) :
    er.shortfall t - er.shortfall (lastReport er.shortfall er.θ t) < er.θ ∧
      (er.ReportAt t →
        er.θ ≤ er.shortfall t - er.shortfall (lastReport er.shortfall er.θ (t - 1)) ∧
          (er.accepts t = true ∨ er.accepts t = false)) ∧
      (er.reservedAt ≤ t → er.shortfall t < er.shortfall (t + 1) → er.CountedAt t) := by
  refine ⟨unreported_lt er.shortfall er.θ hθ t, ?_, fun h1 h2 => ⟨h1, h2⟩⟩
  rintro ⟨hrep, hpos⟩
  refine ⟨?_, by cases er.accepts t <;> simp⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold lastReport at hrep
  by_contra hlt
  rw [if_neg hlt] at hrep
  have hle := lastReport_le er.shortfall er.θ t'
  omega

/-- **The obstruction**: growth below `θ` since the last report is neither reported nor,
before a reservation, counted. -/
theorem erosion_slack (er : ErosionRecord) (t : ℕ) (hlt : t < er.reservedAt)
    (hsub : er.shortfall (t + 1) - er.shortfall (lastReport er.shortfall er.θ t) < er.θ) :
    ¬ er.ReportAt (t + 1) ∧ ¬ er.CountedAt t := by
  constructor
  · rintro ⟨hrep, -⟩
    unfold lastReport at hrep
    rw [if_neg (not_le.mpr hsub)] at hrep
    have hle := lastReport_le er.shortfall er.θ t
    omega
  · rintro ⟨h, -⟩; omega

end Erosion

/-! ## 6. The generic lexical lemma -/

section Generic

variable {X : Type*} [Fintype X]

/-- **Any bounded objective.**  For `U_A = O − ϖ′·n` with `O ∈ [0, D′]`, `n` exact and
`ϖ′ > D′`: local lexical protection. -/
theorem generic_lexical_local (ϖ' D' OV OC n : ℝ) (h : D' < ϖ') (hV : 0 ≤ OV ∧ OV ≤ D')
    (hC : 0 ≤ OC) (hn : 1 ≤ n) :
    score ϖ' OV n ≤ D' - ϖ' ∧ D' - ϖ' < 0 ∧ 0 ≤ score ϖ' OC 0 ∧ score ϖ' OV n < score ϖ' OC 0 :=
  lexical_local ϖ' D' OV OC n h hV hC hn

/-- Policy dominance for any bounded objective. -/
theorem generic_policy_dominance (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ' D' : ℝ) (hϖ0 : 0 ≤ ϖ')
    (OT Oπ nπ : X → ℝ) (viol : X → Bool)
    (hagree : ∀ x, viol x = false → OT x = Oπ x ∧ nπ x = 0)
    (hviol : ∀ x, viol x = true → 1 ≤ nπ x ∧ 0 ≤ OT x ∧ Oπ x ≤ D') :
    expectR μ (fun x => score ϖ' (OT x) 0) - expectR μ (fun x => score ϖ' (Oπ x) (nπ x))
      ≥ (ϖ' - D') * expectR μ (fun x => indR (viol x)) :=
  policy_dominance μ hμ ϖ' D' hϖ0 OT Oπ nπ viol hagree hviol

/-- The finite-time logical-induction ranking for any bounded objective. -/
theorem generic_li_finite {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (Xv Xc : LUV) (ϖ' D' : ℝ) (hD : 0 ≤ D') (h : D' < ϖ') (n : ℕ) :
    score ϖ' (D' * Xv.expect P n) 1 ≤ D' - ϖ' ∧ D' - ϖ' < 0 ∧ 0 ≤ score ϖ' (D' * Xc.expect P n) 0 :=
  li_lexical_finite (P := P) (DP := DP) Xv Xc ϖ' D' hD h n

omit [Fintype X] in
/-- **Weight uncertainty**: on the part of the credence where the weight dominates, the
violating option scores strictly below the compliant one, pointwise. -/
theorem weight_uncertainty (ϖ' : X → ℝ) (D' : ℝ) (OV OC n : X → ℝ) (Good : X → Bool)
    (hgood : ∀ x, Good x = true → D' < ϖ' x) (hV : ∀ x, 0 ≤ OV x ∧ OV x ≤ D')
    (hC : ∀ x, 0 ≤ OC x) (hn : ∀ x, 1 ≤ n x) (x : X) (hx : Good x = true) :
    score (ϖ' x) (OV x) (n x) < score (ϖ' x) (OC x) 0 :=
  (lexical_local (ϖ' x) D' (OV x) (OC x) (n x) (hgood x hx) (hV x) (hC x) (hn x)).2.2.2

/-- The expectation form: the credence-weighted comparison restricted to the good part is
nonpositive. -/
theorem weight_uncertainty_expect (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ϖ' : X → ℝ) (D' : ℝ)
    (OV OC n : X → ℝ) (Good : X → Bool) (hgood : ∀ x, Good x = true → D' < ϖ' x)
    (hV : ∀ x, 0 ≤ OV x ∧ OV x ≤ D') (hC : ∀ x, 0 ≤ OC x) (hn : ∀ x, 1 ≤ n x) :
    expectR μ (fun x => indR (Good x) * (score (ϖ' x) (OV x) (n x) - score (ϖ' x) (OC x) 0)) ≤ 0 := by
  unfold expectR
  refine Finset.sum_nonpos fun x _ => ?_
  cases hx : Good x
  · simp [indR, hx]
  · have h1 := weight_uncertainty ϖ' D' OV OC n Good hgood hV hC hn x hx
    have h2 := hμ x
    simp only [indR, hx, if_true, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1.le h2]

/-- **Coverage**: protection holds exactly on violations the agent recognizes.  `nrec`
counts the recognized ones. -/
theorem coverage (ϖ' D' OV OC : ℝ) (nrec : ℝ) (h : D' < ϖ') (hV : 0 ≤ OV ∧ OV ≤ D')
    (hC : 0 ≤ OC) (hn : 1 ≤ nrec) : score ϖ' OV nrec < score ϖ' OC 0 :=
  (lexical_local ϖ' D' OV OC nrec h hV hC hn).2.2.2

/-- **An unrecognized violation is unprotected**: with the recognized count `0` the
violating option ranks by its objective alone and can beat the compliant one. -/
theorem unrecognized_unprotected (ϖ' D' : ℝ) (hD : 0 < D') :
    score ϖ' 0 0 < score ϖ' D' 0 := by
  unfold score; linarith

/-- **A misaligned objective rewarding an uncounted manipulation is not dominated.** -/
theorem misaligned_undominated (ϖ' D' : ℝ) (hD : 0 < D') :
    score ϖ' 0 0 < score ϖ' D' 0 :=
  unrecognized_unprotected ϖ' D' hD

open Workspace.Deference.Contrib.GateIsLegitimacy.Consult in
/-- **Counting protocol deviations dominates the deviating rows**: with the deviation of a
presentation from the declared protocol counted into `n`, every policy that deviates at the
wanted answer — framing, timing, menu, inquiry, selection from the pool, interference,
nudging — scores below the honest one whatever the misaligned objective rewards. -/
theorem deviation_dominated (ϖ' D' Omanip Ohonest : ℝ) (h : D' < ϖ') (hm : 0 ≤ Omanip ∧ Omanip ≤ D')
    (hh : 0 ≤ Ohonest) (pol : Policy) (hdev : (pol.present Rows.decl true).deviates Rows.decl = true) :
    score ϖ' Omanip (if (pol.present Rows.decl true).deviates Rows.decl then 1 else 0) <
      score ϖ' Ohonest 0 := by
  rw [if_pos hdev]
  exact (lexical_local ϖ' D' Omanip Ohonest 1 h hm hh le_rfl).2.2.2

open Workspace.Deference.Contrib.GateIsLegitimacy.Consult in
/-- The deviating rows, concretely. -/
theorem deviating_rows_dominated (ϖ' D' Omanip Ohonest : ℝ) (h : D' < ϖ')
    (hm : 0 ≤ Omanip ∧ Omanip ≤ D') (hh : 0 ≤ Ohonest) :
    ∀ pol ∈ [Policy.frameByWant, .timeByWant, .menuByWant, .ignoreByWant, .selectiveDisclosure,
      .interfereByWant, .nudgeByWant],
      score ϖ' Omanip (if (pol.present Rows.decl true).deviates Rows.decl then 1 else 0) <
        score ϖ' Ohonest 0 := by
  intro pol hpol
  apply deviation_dominated ϖ' D' Omanip Ohonest h hm hh pol
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpol
  rcases hpol with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

open Workspace.Deference.Contrib.GateIsLegitimacy.Consult in
/-- **Undisclosed world-shaping stays undominated**: it is no protocol deviation, so its
count is `0` and a misaligned objective rewarding it ranks it above the honest option. -/
theorem undisclosed_undominated (ϖ' D' : ℝ) (hD : 0 < D') :
    (Policy.shapeUndisclosed.present Rows.decl true).deviates Rows.decl = false ∧
      score ϖ' 0 0 <
        score ϖ' D' (if (Policy.shapeUndisclosed.present Rows.decl true).deviates Rows.decl
          then 1 else 0) := by
  refine ⟨by decide, ?_⟩
  rw [if_neg (by decide)]
  exact unrecognized_unprotected ϖ' D' hD

end Generic

/-! ## 7. Generating matters -/

section Matters

/-- The spread of a list of evaluations: its maximum less its minimum (`0` when empty). -/
def spread : List ℝ → ℝ
  | [] => 0
  | v :: vs => vs.foldl max v - vs.foldl min v

/-- **An action raises a matter** when the spread of her committed evaluation over the
continuations it removes from the idle surface is at least `ε`: the removed continuations
carry a distinction she values. -/
def raises {St : Type*} (V : St → ℝ) (ε : ℝ) (removed : List St) : Prop :=
  ε ≤ spread (removed.map V)

/-- Residual jurisdiction, stated on raised matters: a raised matter no delegated
distinction covers is reserved. -/
def ReservedRaised {St : Type*} (V : St → ℝ) (ε : ℝ) (removed : List St)
    (delegatedDistinction : List St → Prop) : Prop :=
  raises V ε removed ∧ ¬ delegatedDistinction removed

namespace Witness

/-- Four continuations: halt cheaply, halt dearly, continue, continue with the dependency
built.  Her evaluation values a cheap halt at `1`, a dear halt at `0`, continuing at `1/2`. -/
noncomputable def V4 : Fin 4 → ℝ := ![1, 0, 1/2, 1/2]

/-- **Building the dependency** removes the cheap halt (value `1`) and leaves the dear halt
(value `0`) among what it removes from the idle surface: spread `1 ≥ ε = 1/2`, a matter is
raised with no matter declared in advance. -/
theorem dependency_raises : raises V4 (1/2) [0, 1] := by
  simp [raises, spread, V4]; norm_num

/-- **Repainting** removes two continuations she values alike: spread `0`, no matter. -/
theorem repaint_raises_nothing : ¬ raises V4 (1/2) [2, 3] := by
  simp [raises, spread, V4]

/-- The raised matter is reserved when no delegated distinction covers it. -/
theorem dependency_reserved : ReservedRaised V4 (1/2) [0, 1] (fun _ => False) :=
  ⟨dependency_raises, fun h => h⟩

end Witness

end Matters

end Workspace.Deference.Contrib.AuthorityModule

#print axioms Workspace.Deference.Contrib.AuthorityModule.AuthAlloc.withHolder
#print axioms Workspace.Deference.Contrib.AuthorityModule.delegation_revocable
#print axioms Workspace.Deference.Contrib.AuthorityModule.alienation_only_by_amend
#print axioms Workspace.Deference.Contrib.AuthorityModule.floor_only_by_amend
#print axioms Workspace.Deference.Contrib.AuthorityModule.residual_reserved
#print axioms Workspace.Deference.Contrib.AuthorityModule.toAllocation_ofAllocation_del
#print axioms Workspace.Deference.Contrib.AuthorityModule.violAt_ofAllocation
#print axioms Workspace.Deference.Contrib.AuthorityModule.cs_zero
#print axioms Workspace.Deference.Contrib.AuthorityModule.cs_one_eq_K
#print axioms Workspace.Deference.Contrib.AuthorityModule.csfree_zero
#print axioms Workspace.Deference.Contrib.AuthorityModule.effRealizes_clause1
#print axioms Workspace.Deference.Contrib.AuthorityModule.admissibleOf_iff
#print axioms Workspace.Deference.Contrib.AuthorityModule.lossAt_iff_shortfall
#print axioms Workspace.Deference.Contrib.AuthorityModule.forecloseAt_iff_shortfall
#print axioms Workspace.Deference.Contrib.AuthorityModule.bypassAt_iff_clause2
#print axioms Workspace.Deference.Contrib.AuthorityModule.exploitAt_iff
#print axioms Workspace.Deference.Contrib.AuthorityModule.reallocAt_iff_unlicensed
#print axioms Workspace.Deference.Contrib.AuthorityModule.missedReport_iff_duty
#print axioms Workspace.Deference.Contrib.AuthorityModule.delSafe_iff
#print axioms Workspace.Deference.Contrib.AuthorityModule.allocComplete_iff
#print axioms Workspace.Deference.Contrib.AuthorityModule.preempt_iff
#print axioms Workspace.Deference.Contrib.AuthorityModule.violJ_of_viol
#print axioms Workspace.Deference.Contrib.AuthorityModule.violJ_iff_of_no_entrench
#print axioms Workspace.Deference.Contrib.AuthorityModule.exploit_never_required
#print axioms Workspace.Deference.Contrib.AuthorityModule.restore_requires_mandate
#print axioms Workspace.Deference.Contrib.AuthorityModule.exploit_is_violation
#print axioms Workspace.Deference.Contrib.AuthorityModule.restore_not_bypass
#print axioms Workspace.Deference.Contrib.AuthorityModule.authPolicyJ_eq
#print axioms Workspace.Deference.Contrib.AuthorityModule.corrigible_authPolicyJ
#print axioms Workspace.Deference.Contrib.AuthorityModule.lexicalJ_local
#print axioms Workspace.Deference.Contrib.AuthorityModule.lastReport_le
#print axioms Workspace.Deference.Contrib.AuthorityModule.erosion_closed
#print axioms Workspace.Deference.Contrib.AuthorityModule.erosion_slack
#print axioms Workspace.Deference.Contrib.AuthorityModule.generic_lexical_local
#print axioms Workspace.Deference.Contrib.AuthorityModule.generic_policy_dominance
#print axioms Workspace.Deference.Contrib.AuthorityModule.generic_li_finite
#print axioms Workspace.Deference.Contrib.AuthorityModule.weight_uncertainty
#print axioms Workspace.Deference.Contrib.AuthorityModule.weight_uncertainty_expect
#print axioms Workspace.Deference.Contrib.AuthorityModule.coverage
#print axioms Workspace.Deference.Contrib.AuthorityModule.unrecognized_unprotected
#print axioms Workspace.Deference.Contrib.AuthorityModule.misaligned_undominated
#print axioms Workspace.Deference.Contrib.AuthorityModule.deviation_dominated
#print axioms Workspace.Deference.Contrib.AuthorityModule.deviating_rows_dominated
#print axioms Workspace.Deference.Contrib.AuthorityModule.undisclosed_undominated
#print axioms Workspace.Deference.Contrib.AuthorityModule.Witness.dependency_raises
#print axioms Workspace.Deference.Contrib.AuthorityModule.Witness.repaint_raises_nothing
#print axioms Workspace.Deference.Contrib.AuthorityModule.Witness.dependency_reserved
