import Cleanroom.Decision.DpFaithfulUdt.Carrier
import Cleanroom.Decision.DpFirstpersonSc.Stamp

/-!
# The first-personal audit (D7′) and Proposition 1′ — T1 of [[dp-firstperson-sc-mandate]]

* `auditRef s₀ E h := jeffreyCond s₀ E h` — the audit's referent `ŝ = (P_{s₀}(· | E), V_{s₀}(· ∧ E))`
  (D7′), for a prior state `s₀` on a carrier `W` and an event `E` of positive prior probability.
* `pushState π t` — a state on `W` read on a coarser carrier `Ω` along `π : W → Ω`
  (`P(X) := P_t(π⁻¹X)`, `V(X) := V_t(π⁻¹X)`); `dp-calibration`'s `pushdown` is the case
  `π = world B`.
* `AuditPassAt s₀ E h π s` — **the audit verdict**: the audited state `s` (on `Ω`) agrees with
  `ŝ` read along `π`: `P_s = (π_* ŝ).P` and `V_s = (π_* ŝ).V` on events of positive `ŝ`-probability
  (the `V`-clause is guarded because `State.V` is junk off the support, mandate decision 3; D7′'s
  `ε`-version is total-variation slack, not built — stretch). With `π = id` both states live on
  one carrier (the stamped audit of a stamped state, T2(a)); with `π = Prod.fst` a base state is
  audited against the stamped prior (T1(a), T2(b)). The verdict is a function of `(s₀, E, s)`
  alone — no `μ`, `ν` or payoff is consulted — so it is an *epistemology* in Definition 19's sense
  (T1(d)); that is the form of the definition, not a theorem.
* **T1(a), Proposition 1′** (`audit_iff_perRunClausesAt`, `auditAll_iff_perRunSSC`): with the
  prior state `priorState C (stamp U B)` (or any Definition-11 prior-calibrated `s₀` on the stamped
  problem, `audit_iff_perRunClausesAt_of_priorCalibrated`) and `E := occW` (`{pol_d ≠ ⊥}`), the
  base state `s_d` passes the audit at `d` iff `dp-calibration`'s per-run SSC clauses hold at
  `d` (both clauses, `V` on positive events); hence audit-pass at every queried point iff per-run
  SSC. **Grade C, by design**: the audit's referent is *defined* as a conditioning, so the
  content is the identity `Prod.fst_* (jeffreyCond (priorState C (stamp U B)) occW) ≈ occState C B d`
  (`pushState_fst_auditRef_stamp_agree`: `leafLaw_relabel` + the `Stamp.lean` transports +
  `occState_pr/V`), and a ledger row calling the iff `P` would be a squeeze.
* **T1(b)** (`obsAudit_ref_agree_calibratedState`): the *observation*-conditioned audit
  (evidence `occW ∩ fst⁻¹ O_d`) has `calibratedState C B (obs d)` as its referent wherever `B`
  covers `d` — no bite beyond strict OC (FP-21′'s "an observation-conditioned audit has no
  bite"); on `mug1` coverage is automatic (`occ = ⊤`, `WitnessesAudit.lean`).

Scope: finite regime, Definition 6 (independent redraws); the stamped problem is `stamp U B`
with `d ∈ U`; no `AlmostFair` hypothesis is needed because `occW` reads only `{#_d > 0}`
(`Stamp.lean`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## `State.Agree` is an equivalence -/

section agree

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `Agree` is reflexive. Source: none: infrastructure. Kind: L -/
theorem _root_.Cleanroom.Decision.DpCalibration.State.Agree.refl (s : State Ω K) :
    State.Agree s s := ⟨rfl, fun _ _ => rfl⟩

/-- `Agree` is symmetric. Source: none: infrastructure. Kind: L -/
theorem _root_.Cleanroom.Decision.DpCalibration.State.Agree.symm {s t : State Ω K}
    (h : State.Agree s t) : State.Agree t s :=
  ⟨h.1.symm, fun X hX => (h.2 X (by simpa [State.pr, h.1] using hX)).symm⟩

/-- `Agree` is transitive. Source: none: infrastructure. Kind: L -/
theorem _root_.Cleanroom.Decision.DpCalibration.State.Agree.trans {s t u : State Ω K}
    (h₁ : State.Agree s t) (h₂ : State.Agree t u) : State.Agree s u :=
  ⟨h₁.1.trans h₂.1, fun X hX => (h₁.2 X hX).trans (h₂.2 X (by simpa [State.pr, ← h₁.1] using hX))⟩

/-- Jeffrey conditioning respects agreement. Source: none: infrastructure. Kind: L -/
theorem jeffreyCond_agree {s t : State Ω K} (hag : State.Agree s t) (E : Finset Ω)
    (h : 0 < s.pr E) (h' : 0 < t.pr E) :
    State.Agree (jeffreyCond s E h) (jeffreyCond t E h') := by
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    show (if ω ∈ E then s.P.w ω / s.pr E else 0) = (if ω ∈ E then t.P.w ω / t.pr E else 0)
    simp only [State.pr, hag.1]
  · rw [jeffreyCond_V, jeffreyCond_V]
    apply hag.2
    rw [jeffreyCond_pr] at hX
    by_contra hc
    rw [not_lt] at hc
    have := div_nonpos_of_nonpos_of_nonneg hc (probOf_nonneg s.P E)
    linarith

end agree

/-! ## Reading a state along a projection -/

section push

variable {W Ω : Type} [Fintype W] [DecidableEq W] [Fintype Ω] [DecidableEq Ω]

/-- The pre-image event `π⁻¹ X` as a `Finset`. Source: none: infrastructure. Kind: D -/
def preEv (π : W → Ω) (X : Finset Ω) : Finset W := Finset.univ.filter fun w => π w ∈ X

/-- Membership in a pre-image event. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_preEv (π : W → Ω) (X : Finset Ω) (w : W) : w ∈ preEv π X ↔ π w ∈ X := by
  simp [preEv]

/-- `∑_{ω ∈ X} P(π⁻¹{ω}) = P(π⁻¹X)`. Source: none: infrastructure. Kind: L -/
theorem sum_probOf_preEv_singleton (π : W → Ω) (P : FinDistr K W) (X : Finset Ω) :
    ∑ ω ∈ X, probOf P (preEv π {ω}) = probOf P (preEv π X) := by
  simp only [probOf, preEv, Finset.sum_filter, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact Finset.sum_ite_eq X (π w) (fun _ => P.w w)

/-- The pushforward `π_* P` of a distribution on `W`. Source: none: infrastructure. Kind: D -/
def pushDistrK (π : W → Ω) (P : FinDistr K W) : FinDistr K Ω where
  w ω := probOf P (preEv π {ω})
  nonneg _ := probOf_nonneg _ _
  sum_one := by
    rw [sum_probOf_preEv_singleton]
    have : preEv π (Finset.univ : Finset Ω) = Finset.univ := by ext w; simp
    rw [this, probOf_univ]

/-- `(π_* P)(X) = P(π⁻¹X)`. Source: none: infrastructure. Kind: L -/
theorem probOf_pushDistrK (π : W → Ω) (P : FinDistr K W) (X : Finset Ω) :
    probOf (pushDistrK π P) X = probOf P (preEv π X) :=
  sum_probOf_preEv_singleton π P X

/-- **A state read along a projection** `π : W → Ω`: `P(X) := P_t(π⁻¹X)`, `V(X) := V_t(π⁻¹X)`.
`dp-calibration`'s `pushdown B` is the case `π = world B`.
Source: [[decision-problems-v2]] §3.1 Proposition 2 (`λ_* P_{s'_d}`), generalized to any
projection; `firstperson.md` D5 (`λ_* μ_C(· | occ(d))`)
Kind: D -/
def pushState (π : W → Ω) (t : State W K) : State Ω K where
  P := pushDistrK π t.P
  V X := t.V (preEv π X)
  avg X Y hXY hX hY := by
    simp only [probOf_pushDistrK] at hX hY ⊢
    have hU : preEv π (X ∪ Y) = preEv π X ∪ preEv π Y := by
      ext w; simp [Finset.mem_union]
    have hdisj : Disjoint (preEv π X) (preEv π Y) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [mem_preEv] at h1 h2
      exact Finset.disjoint_left.mp hXY h1 h2
    rw [hU]
    exact t.avg _ _ hdisj hX hY

/-- `(π_* t)(X) = P_t(π⁻¹X)`. Source: none: infrastructure. Kind: L -/
theorem pushState_pr (π : W → Ω) (t : State W K) (X : Finset Ω) :
    (pushState π t).pr X = t.pr (preEv π X) :=
  probOf_pushDistrK π t.P X

/-- `V` of a pushed state. Source: none: infrastructure. Kind: L -/
theorem pushState_V (π : W → Ω) (t : State W K) (X : Finset Ω) :
    (pushState π t).V X = t.V (preEv π X) := rfl

/-- Pushing respects agreement. Source: none: infrastructure. Kind: L -/
theorem pushState_agree (π : W → Ω) {t t' : State W K} (h : State.Agree t t') :
    State.Agree (pushState π t) (pushState π t') := by
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    show probOf t.P (preEv π {ω}) = probOf t'.P (preEv π {ω})
    rw [h.1]
  · rw [pushState_V, pushState_V]
    exact h.2 _ (by rwa [pushState_pr] at hX)

/-- Reading along the identity changes nothing (modulo `V`'s junk).
Source: none: infrastructure. Kind: L -/
theorem pushState_id_agree (t : State Ω K) : State.Agree (pushState id t) t := by
  have hp : ∀ X : Finset Ω, preEv id X = X := fun X => by ext ω; simp
  refine ⟨?_, fun X _ => ?_⟩
  · apply FinDistr.ext'
    intro ω
    show probOf t.P (preEv id {ω}) = t.P.w ω
    rw [hp, probOf_singleton]
  · rw [pushState_V, hp]

end push

/-! ## The audit -/

section audit

variable {W Ω : Type} [Fintype W] [DecidableEq W] [Fintype Ω] [DecidableEq Ω]

/-- **The audit's referent `ŝ`** (D7′): the prior state Jeffrey-conditioned on the event `E`
(`occ(d)` on the stamped algebra), under the guard `0 < P_{s₀}(E)` (Definition 13's
`μ(occ(d)) > 0` at a calibrated prior).
Source: `firstperson.md` D7′ ("`ŝ := (P_{s₀}(· | occ(d)), V_{s₀}(· ∧ occ(d)))`")
Kind: D
Fidelity: exact (the `ε`-version is not built) -/
def auditRef (s₀ : State W K) (E : Finset W) (h : 0 < s₀.pr E) : State W K := jeffreyCond s₀ E h

/-- **The audit verdict at a point** (D7′, repaired): the audited state `s` on `Ω` equals the
referent `ŝ` read along `π : W → Ω` — `P_s = (π_* ŝ).P`, and `V_s = (π_* ŝ).V` on every event of
positive `ŝ`-probability (`V` is junk off the support). `π = id`: both states on one carrier;
`π = Prod.fst`: a base state against a stamped prior. The verdict reads `(s₀, E, s)` only —
Definition 19's epistemology (T1(d)); the "grade" is the choice of `s₀` (strict: `priorState C`;
masked-local: `priorState (C.deviate d m)` with `m` full-support; T13's limit grades).
Source: `firstperson.md` D7′ ("pass iff `(P_{s_d}, V_{s_d}) = ŝ`"), FP-21′(iii);
[[decision-problems-v2]] Definition 19
Kind: D
Fidelity: variant: `V`-clause on events of positive referent probability (v2's `V` is defined
only there); `ε`-slack not built -/
def AuditPassAt (s₀ : State W K) (E : Finset W) (h : 0 < s₀.pr E) (π : W → Ω) (s : State Ω K) :
    Prop :=
  s.P = (pushState π (auditRef s₀ E h)).P ∧
    ∀ X, 0 < (pushState π (auditRef s₀ E h)).pr X →
      s.V X = (pushState π (auditRef s₀ E h)).V X

/-- The verdict is agreement with the pushed referent. Source: none: infrastructure. Kind: L -/
theorem auditPassAt_iff_agree (s₀ : State W K) (E : Finset W) (h : 0 < s₀.pr E) (π : W → Ω)
    (s : State Ω K) :
    AuditPassAt s₀ E h π s ↔ State.Agree s (pushState π (auditRef s₀ E h)) := by
  unfold AuditPassAt State.Agree
  constructor
  · rintro ⟨hP, hV⟩
    exact ⟨hP, fun X hX => hV X (by simpa [State.pr, hP] using hX)⟩
  · rintro ⟨hP, hV⟩
    exact ⟨hP, fun X hX => hV X (by simpa [State.pr, hP] using hX)⟩

/-- On one carrier (`π = id`) the verdict is agreement with `ŝ` itself.
Source: none: infrastructure. Kind: L -/
theorem auditPassAt_id_iff (s₀ : State Ω K) (E : Finset Ω) (h : 0 < s₀.pr E) (s : State Ω K) :
    AuditPassAt s₀ E h id s ↔ State.Agree s (auditRef s₀ E h) := by
  rw [auditPassAt_iff_agree]
  exact ⟨fun ha => ha.trans (pushState_id_agree _),
    fun ha => ha.trans (pushState_id_agree _).symm⟩

/-- The verdict is invariant under replacing the prior by an agreeing one.
Source: none: infrastructure. Kind: L -/
theorem auditPassAt_congr_prior {s₀ t₀ : State W K} (hag : State.Agree s₀ t₀) (E : Finset W)
    (h : 0 < s₀.pr E) (h' : 0 < t₀.pr E) (π : W → Ω) (s : State Ω K) :
    AuditPassAt s₀ E h π s ↔ AuditPassAt t₀ E h' π s := by
  rw [auditPassAt_iff_agree, auditPassAt_iff_agree]
  have := pushState_agree π (jeffreyCond_agree hag E h h')
  exact ⟨fun ha => ha.trans this, fun ha => ha.trans this.symm⟩

end audit

/-! ## T1(a): the audit on the stamped problem is per-run SSC -/

section perRun

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **Agreement with the per-run state is the per-run clause pair**: where `μ(occ(d)) > 0`,
`s_d` agrees with `occState C B d` (modulo junk `V`) iff Definition 13's per-run clauses hold
at `d`.
Source: [[decision-problems-v2]] §3.1 Definition 13; `firstperson.md` D5
Kind: L
Fidelity: exact (agreement modulo `V`'s junk values; `V`-clause reading of record)
Hyps: (a) `0 < μ(occ(d))` -/
theorem agree_occState_iff_perRunClausesAt (s : ι → State Ω K) (d : ι)
    (h : 0 < mass C B (occ d B)) :
    State.Agree (s d) (occState C B d h) ↔ PerRunClausesAt s C B d := by
  have hpr : ∀ X, (occState C B d h).pr X =
      mass C B (worldEv B X ∩ occ d B) / mass C B (occ d B) := fun X => occState_pr C B d h X
  have hV : ∀ X, (occState C B d h).V X =
      (∑ ℓ ∈ worldEv B X ∩ occ d B, leafLaw C B ℓ * payoff B ℓ) /
        mass C B (worldEv B X ∩ occ d B) := fun X => occState_V C B d h X
  constructor
  · rintro ⟨hP, hVa⟩
    refine ⟨fun X => ?_, fun X hX hXm => ?_⟩
    · have := hpr X
      simp only [State.pr] at this ⊢
      rw [hP, this]
      exact div_mul_cancel₀ _ h.ne'
    · rw [hVa X hX, hV X]
      exact div_mul_cancel₀ _ hXm.ne'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun X hX => ?_⟩
    · apply FinDistr.ext'
      intro ω
      have := h1 {ω}
      have hp := hpr {ω}
      simp only [State.pr, probOf_singleton] at this hp ⊢
      rw [hp, ← this]
      exact (mul_div_cancel_right₀ _ h.ne').symm
    · have h1X := h1 X
      have hXm : 0 < mass C B (worldEv B X ∩ occ d B) := by
        rw [← h1X]; exact mul_pos hX h
      rw [hV X]
      have := h2 X hX hXm
      rw [eq_div_iff hXm.ne']
      exact this

variable (U : Finset ι) {d : ι} (hd : d ∈ U)

/-- The stamped prior's probability of `occW` is `μ(occ(d))`.
Source: none: infrastructure. Kind: L -/
theorem priorState_stamp_pr_occW :
    (priorState C (stamp U B)).pr (occW U hd) = mass C B (occ d B) := by
  rw [priorState_pr, nu_stamp_occW]

/-- `preEv Prod.fst X` on the stamped carrier is `obsW U X`. Source: none: infrastructure.
Kind: L -/
theorem preEv_fst_eq_obsW (X : Finset Ω) : preEv (Prod.fst : SW Ω acts U → Ω) X = obsW U X := rfl

/-- **The audit's referent, pushed to the base carrier, is the per-run state** (D5):
`Prod.fst_* (jeffreyCond (priorState C (stamp U B)) occW) ≈ occState C B d`. This identity is the
whole content of Proposition 1′: `P` by `leafLaw_relabel` through the `Stamp.lean` transports,
`V` likewise.
Source: `firstperson.md` D5, D7′, FP-21′ ("the audit is per-run SSC with the prior in place of
the statistics, on the enriched algebra")
Kind: C
Fidelity: exact
Hyps: (a) `0 < μ(occ(d))` (both guards, equal by `priorState_stamp_pr_occW`) -/
theorem pushState_fst_auditRef_stamp_agree
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) (h' : 0 < mass C B (occ d B)) :
    State.Agree (pushState Prod.fst (auditRef (priorState C (stamp U B)) (occW U hd) h))
      (occState C B d h') := by
  have hpr : ∀ Y, probOf (priorState C (stamp U B)).P Y = nu C (stamp U B) Y :=
    fun Y => priorState_pr C (stamp U B) Y
  refine ⟨?_, fun X _ => ?_⟩
  · apply FinDistr.ext'
    intro ω
    show probOf (jeffreyCond (priorState C (stamp U B)) (occW U hd) h).P (preEv Prod.fst {ω}) =
      mass C B (occEv B d {ω}) / mass C B (occ d B)
    have := jeffreyCond_pr (priorState C (stamp U B)) (occW U hd) h (preEv Prod.fst {ω})
    simp only [State.pr] at this
    rw [this, hpr, hpr, preEv_fst_eq_obsW, nu_stamp_obsW_inter_occW, nu_stamp_occW]
  · rw [pushState_V, auditRef, jeffreyCond_V, priorState_V, preEv_fst_eq_obsW,
      nu_stamp_obsW_inter_occW, paySum_stamp_obsW_inter_occW, occState_V]

/-- **T1(a), the audit at a point is per-run SSC at the point** (Proposition 1′, pointwise):
with the prior state of `C` on the stamped problem and evidence `occ(d) = {pol_d ≠ ⊥}`, the base
state `s_d` passes the audit iff Definition 13's per-run clauses hold at `d` (both clauses).
Grade `C`: the referent is defined as a conditioning; the content is
`pushState_fst_auditRef_stamp_agree`.
Source: `firstperson.md` FP-21′(i) ("audit-pass everywhere ⟺ per-run SSC when the prior is
calibrated"), D7′; [[decision-problems-v2]] Definition 13
Kind: C
Fidelity: exact (stamped algebra; `V`-clause on positive events; no `AlmostFair` needed)
Hyps: (a) `0 < μ(occ(d))` -/
theorem audit_iff_perRunClausesAt (s : ι → State Ω K)
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) h Prod.fst (s d) ↔
      PerRunClausesAt s C B d := by
  have h' : 0 < mass C B (occ d B) := by rwa [priorState_stamp_pr_occW] at h
  rw [auditPassAt_iff_agree, ← agree_occState_iff_perRunClausesAt C B s d h']
  exact ⟨fun ha => ha.trans (pushState_fst_auditRef_stamp_agree C B U hd h h'),
    fun ha => ha.trans (pushState_fst_auditRef_stamp_agree C B U hd h h').symm⟩

/-- A Definition-11 prior-calibrated state agrees with `priorState`.
Source: [[decision-problems-v2]] §3.1 Definition 11
Kind: L -/
theorem agree_priorState_of_priorCalibrated {s₀ : State Ω K} (hcal : PriorCalibrated C B s₀) :
    State.Agree s₀ (priorState C B) := by
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    have := hcal.1 {ω}
    simp only [State.pr, probOf_singleton] at this
    rw [this]
    show nu C B {ω} = (priorState C B).P.w ω
    have := priorState_pr C B {ω}
    simp only [State.pr, probOf_singleton] at this
    exact this.symm
  · rw [priorState_V]
    have hν : 0 < nu C B X := by rw [← hcal.1 X]; exact hX
    rw [eq_div_iff hν.ne']
    exact hcal.2 X hν

/-- **T1(a) for any prior-calibrated prior**: the audit against a Definition-11 prior-calibrated
`s₀` on the stamped problem is per-run SSC at `d`.
Source: `firstperson.md` FP-21′(i); [[decision-problems-v2]] Definition 11, Definition 13
Kind: C
Fidelity: exact
Hyps: (a) `PriorCalibrated C (stamp U B) s₀`, (a) `0 < P_{s₀}(occW)` -/
theorem audit_iff_perRunClausesAt_of_priorCalibrated (s : ι → State Ω K) {s₀ : State (SW Ω acts U) K}
    (hcal : PriorCalibrated C (stamp U B) s₀) (h : 0 < s₀.pr (occW U hd)) :
    AuditPassAt s₀ (occW U hd) h Prod.fst (s d) ↔ PerRunClausesAt s C B d := by
  have hag := agree_priorState_of_priorCalibrated C (stamp U B) hcal
  have h' : 0 < (priorState C (stamp U B)).pr (occW U hd) := by
    show 0 < probOf (priorState C (stamp U B)).P (occW U hd)
    rw [← hag.1]; exact h
  rw [auditPassAt_congr_prior hag (occW U hd) h h']
  exact audit_iff_perRunClausesAt C B U hd s h'

/-- **Proposition 1′**: a prior-calibrated `s₀` on the stamped problem (stamping every queried
point) plus audit-pass at every reachable queried point gives per-run SSC; and conversely.
"Audit-pass everywhere" quantifies over `d ∈ queried B` with `μ(occ(d)) > 0` (the guard of both
the audit and Definition 13).
Source: `firstperson.md` FP-21′(i) ("Prop 1′: prior-calibrated `s₀` + states = its
occurrence-conditionals ⇒ per-run SSC; audit-pass everywhere ⟺ per-run SSC when the prior is
calibrated")
Kind: C
Fidelity: exact
Hyps: (a) `PriorCalibrated C (stamp U B) s₀`, (a) `queried B ⊆ U` -/
theorem auditAll_iff_perRunSSC (s : ι → State Ω K) {s₀ : State (SW Ω acts U) K}
    (hcal : PriorCalibrated C (stamp U B) s₀) (hU : queried B ⊆ U) :
    (∀ d (hd : d ∈ U), d ∈ queried B → ∀ h : 0 < s₀.pr (occW U hd),
        AuditPassAt s₀ (occW U hd) h Prod.fst (s d)) ↔
      PerRunSSC s C B := by
  constructor
  · intro haud d hdq hm
    have hd : d ∈ U := hU hdq
    have h : 0 < s₀.pr (occW U hd) := by
      rw [hcal.1, nu_stamp_occW]; exact hm
    exact (audit_iff_perRunClausesAt_of_priorCalibrated C B U hd s hcal h).mp (haud d hd hdq h)
  · intro hssc d hd hdq h
    have hm : 0 < mass C B (occ d B) := by
      rw [hcal.1, nu_stamp_occW] at h; exact h
    exact (audit_iff_perRunClausesAt_of_priorCalibrated C B U hd s hcal h).mpr (hssc d hdq hm)

/-! ## T1(b): the observation-conditioned audit has no bite under coverage -/

variable (obs : ι → Finset Ω)

/-- Under coverage at `d`, `{λ ⊨ Y} ∩ occ(d)` carries the mass of `{λ ⊨ Y}` for `Y ⊆ O_d`.
Source: [[decision-problems-v2]] Definition 7 ("covers")
Kind: L -/
theorem mass_occEv_eq_nu_of_covers (hcov : Covers obs C B d) {Y : Finset Ω} (hY : Y ⊆ obs d) :
    mass C B (occEv B d Y) = nu C B Y := by
  unfold nu
  apply mass_congr_ae
  intro ℓ hpos
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    occ, and_iff_left_iff_imp]
  intro hw
  exact hcov ℓ hpos (hY hw)

/-- Under coverage the payoff masses agree likewise. Source: none: infrastructure. Kind: L -/
theorem occPay_eq_paySum_of_covers (hcov : Covers obs C B d) {Y : Finset Ω} (hY : Y ⊆ obs d) :
    occPay C B d Y = paySum C B Y := by
  unfold occPay paySum
  apply paySumLeaves_congr_ae
  intro ℓ hpos
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    occ, and_iff_left_iff_imp]
  intro hw
  exact hcov ℓ hpos (hY hw)

/-- **T1(b): the observation-conditioned audit returns the strict-OC state.** Under coverage at
`d`, the referent with evidence `occ(d) ∧ O_d` (instead of `occ(d)`), read on the base carrier, is
`calibratedState C B (obs d)` — so auditing against it is strict OC at `d` and adds nothing
(FP-21′: "an observation-conditioned audit has no bite").
Source: `firstperson.md` FP-21′ ("`λ_*P_{s₀}(· | occ ∧ O_T)` equals the strict-OC state")
Kind: P
Fidelity: exact under coverage (on `mug1` coverage is automatic: `occ = ⊤`)
Hyps: (a) `Covers obs C B d`, (a) `0 < ν(O_d)`, (a) the evidence guard -/
theorem obsAudit_ref_agree_calibratedState (hcov : Covers obs C B d) (hO : 0 < nu C B (obs d))
    (h : 0 < (priorState C (stamp U B)).pr (obsW U (obs d) ∩ occW U hd)) :
    State.Agree
      (pushState Prod.fst (auditRef (priorState C (stamp U B)) (obsW U (obs d) ∩ occW U hd) h))
      (calibratedState C B (obs d) hO) := by
  have hE : ∀ X : Finset Ω, (obsW U X : Finset (SW Ω acts U)) ∩ (obsW U (obs d) ∩ occW U hd) =
      obsW U (X ∩ obs d) ∩ occW U hd := by
    intro X; ext w; simp [mem_obsW, mem_occW]; tauto
  have hO' : (obsW U (obs d) : Finset (SW Ω acts U)) ∩ occW U hd =
      obsW U (obs d ∩ obs d) ∩ occW U hd := by
    rw [Finset.inter_self]
  have hpr : ∀ Y, probOf (priorState C (stamp U B)).P Y = nu C (stamp U B) Y :=
    fun Y => priorState_pr C (stamp U B) Y
  have hsub : ∀ X : Finset Ω, X ∩ obs d ⊆ obs d := fun X => Finset.inter_subset_right
  refine ⟨?_, fun X _ => ?_⟩
  · apply FinDistr.ext'
    intro ω
    show probOf (jeffreyCond (priorState C (stamp U B)) _ h).P (preEv Prod.fst {ω}) =
      (calibratedState C B (obs d) hO).P.w ω
    have := jeffreyCond_pr (priorState C (stamp U B)) _ h (preEv Prod.fst {ω})
    simp only [State.pr] at this
    rw [this, hpr, hpr, preEv_fst_eq_obsW, hE, hO',
      nu_stamp_obsW_inter_occW, nu_stamp_obsW_inter_occW,
      mass_occEv_eq_nu_of_covers C B obs hcov (hsub {ω}),
      mass_occEv_eq_nu_of_covers C B obs hcov (hsub (obs d)), Finset.inter_self]
    have := calibratedState_pr C B (obs d) hO {ω}
    simp only [State.pr, probOf_singleton] at this
    exact this.symm
  · rw [pushState_V, auditRef, jeffreyCond_V, priorState_V, preEv_fst_eq_obsW, hE,
      nu_stamp_obsW_inter_occW, paySum_stamp_obsW_inter_occW,
      mass_occEv_eq_nu_of_covers C B obs hcov (hsub X),
      occPay_eq_paySum_of_covers C B obs hcov (hsub X), calibratedState_V]

end perRun

/-! ## The `occ(d) = ⊤` case: the referent is the prior state -/

section occUniv

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- When every run consults `d`, the per-run state's `P` is the prior state's `P` (`ν`).
Source: none: infrastructure (the `occ(d) = ⊤` case of T1(a)). Kind: L -/
theorem occState_P_eq_priorState_P_of_occ_univ (hocc : occ d B = Finset.univ)
    (h : 0 < mass C B (occ d B)) : (occState C B d h).P = (priorState C B).P := by
  have hev : ∀ X, occEv B d X = worldEv B X := by
    intro X; unfold occEv; rw [hocc, Finset.inter_univ]
  have hm : mass C B (occ d B) = 1 := by rw [hocc, mass_univ]
  apply FinDistr.ext'
  intro ω
  have h1 := occState_pr C B d h {ω}
  have h2 := priorState_pr C B {ω}
  simp only [State.pr, probOf_singleton] at h1 h2
  simp only [h1, h2, hev, hm, div_one, nu]

/-- When every run consults `d`, the per-run state's `V` is the prior state's `V` on every event
(`occPay = paySum`, `μ(occEv X) = ν(X)`).
Source: none: infrastructure (the `occ(d) = ⊤` case of T1(a)). Kind: L -/
theorem occState_V_eq_priorState_V_of_occ_univ (hocc : occ d B = Finset.univ)
    (h : 0 < mass C B (occ d B)) (X : Finset Ω) :
    (occState C B d h).V X = (priorState C B).V X := by
  have hev : occEv B d X = worldEv B X := by
    unfold occEv; rw [hocc, Finset.inter_univ]
  rw [occState_V, priorState_V]
  unfold occPay paySum nu
  rw [hev]

/-- **The audit's referent at a point every run consults is the prior state**: at `occ(d) = ⊤`
the per-run state (= the pushed-down referent, `pushState_fst_auditRef_stamp_agree`) agrees with
`priorState C B` as a state — `P` equal, `V` equal on every event. The `B₁` cells and the
`seqStag`-at-`d₁` cells read the prior state's `V` for this reason.
Source: `firstperson.md` D7′ (the referent at `occ(d) = ⊤`); audit r1 fidelity N1/N4
Kind: L -/
theorem occState_agree_priorState_of_occ_univ (hocc : occ d B = Finset.univ)
    (h : 0 < mass C B (occ d B)) : State.Agree (occState C B d h) (priorState C B) :=
  ⟨occState_P_eq_priorState_P_of_occ_univ C B d hocc h,
    fun X _ => occState_V_eq_priorState_V_of_occ_univ C B d hocc h X⟩

/-- **At a point every run consults, the strict-grade audit is the prior-identity check**: with
`occ(d) = ⊤`, a base state passes the audit against the stamped prior with evidence `occ(d)`
(projection `fst`) iff it agrees with the base prior state. So an audit cell at such a point
(`stagePostState_fails_audit`; `mug1`'s cells; `seqStag` at `d₁`) adds nothing to the agreement
or disagreement with `priorState` — the content of those cells is the inequality, not the audit
(audit r2 adversarial N1; the probe's lemma adopted).
Source: `firstperson.md` D7′ (the referent at `occ(d) = ⊤`); audit r2 adversarial N1
Kind: L
Fidelity: exact
Hyps: (a) `occ(d) = ⊤` -/
theorem audit_iff_agree_priorState_of_occ_univ (U : Finset ι) (hd : d ∈ U)
    (hocc : occ d B = Finset.univ)
    (h : 0 < (priorState C (stamp U B)).pr (occW U hd)) (s : State Ω K) :
    AuditPassAt (priorState C (stamp U B)) (occW U hd) h Prod.fst s ↔
      State.Agree s (priorState C B) := by
  rw [auditPassAt_iff_agree]
  have h' : 0 < mass C B (occ d B) := by rwa [priorState_stamp_pr_occW] at h
  have h1 := pushState_fst_auditRef_stamp_agree C B U hd h h'
  have h2 := occState_agree_priorState_of_occ_univ C B d hocc h'
  exact ⟨fun hs => hs.trans (h1.trans h2), fun hs => hs.trans (h2.symm.trans h1.symm)⟩

end occUniv

end Cleanroom.Decision.DpFirstpersonSc
