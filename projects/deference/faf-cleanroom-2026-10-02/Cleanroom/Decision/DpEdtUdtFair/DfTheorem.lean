import Cleanroom.Decision.DpEdtUdtFair.Theorem3
import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses
import Cleanroom.Decision.DpCalibration.Devices
import Cleanroom.Decision.DpCalibration.Basic

/-!
# CA-2′, the downstream-faithful (DF) theorem on `𝔉` (T12(b))

* **Step 1 without the full-support device.** `Step1.lean` states the set identity and the act
  values for a full-support `C'`; the set identity is a fact about the tree (the procedure is only
  the device that makes every leaf positive), so it holds for every procedure once proved with
  `Proc.uniform`. `FairClass.nu_actEv_inter_obs_eq_fiberMass'`, `nu_obs_eq_fiberMass'`,
  `paySum_actEv_inter_obs_eq'` and `condExp_eq_Q'` are the device-free forms, for an arbitrary
  procedure (the act value needs only `ν_{C'}(O_d) > 0` and `C'(d)(a) > 0`).
* **CA-3′'s locality.** `strictlyBelow_of_mem_queried_child`: a point queried below a `d`-node
  is strictly below `d` (`dp-calibration`'s `StrictlyBelow`). So a DF self-model, which agrees
  with `C` strictly below `d`, has `Q_{C'}(d, ·) = Q_C(d, ·)` (`value_congr_queried`).
* **The DF act values are `Q_C`** (`FairClass.dfMasked_at`): under a DF self-model at `d`, the
  strict state's `P(a) = C'(d)(a) > 0` (so `A_d^+ = A_d`) and `V(a) = 𝔼_{C'}[r ∣ a ∧ O_d] =
  Q_{C'}(d, a) = Q_C(d, a)`. Hence `FairClass.dfMasked_tEdt_iff`: DF-`T_EDT` on `𝔉` is exactly
  "`supp C(d) ⊆ argmax Q_C(d, ·)` at every queried `d`" — no trembles, no limit.
* **`fairClass_dfMasked_isOptimal`** — **CA-2′**: `FairClass → DFMasked → TEdt → IsOptimal`,
  by Step 3 (`stronglyFair_isOptimal_of_pointwise_best`).
* Witness `dupPay_dfMasked_witness` (N+, two-member fiber): `δ_a` on `dupPay 1 0` is DF-masked
  with the uniform self-model and `T_EDT`-approved, hence optimal; `δ_b` is DF-`T_EDT`-rejected
  under every state assignment and is not optimal.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### Step 1 for an arbitrary procedure -/

section step1

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- The set identity is a fact about the tree: on `𝔉` the leaves whose world satisfies `a ∧ O_d`
are exactly the leaves drawing `⟨d, a⟩`, with no procedure in the statement (proved through the
uniform procedure).
Source: `fair-repair.md` FR-11 Step 1; dp-cf-119
Kind: L -/
theorem FairClass.worldEv_eq_drew' [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    worldEv B (actEv d a ∩ obs d) = drew d a B :=
  h.worldEv_eq_drew (C' := Proc.uniform) Proc.uniform_fullSupport hd a

/-- **`ν_{C'}(a ∧ O_d) = C'(d)(a) · fiberMass_d(C')`** on `𝔉` for every procedure `C'` (the
full-support hypothesis of `Step1.lean` was only the device for the set identity).
Source: `fair-repair.md` FR-11 Step 1–2; mandate T2(b)
Kind: P
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.nu_actEv_inter_obs_eq_fiberMass' [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : FairClass obs actEv B) (C' : Proc ι acts K) {d : ι}
    (hd : d ∈ queried B) (a : acts d) :
    nu C' B (actEv d a ∩ obs d) = (C' d).w a * fiberMass C' B d := by
  unfold nu mass
  rw [h.worldEv_eq_drew' hd a]
  unfold drew
  rw [Finset.sum_filter]
  have key := sum_drew_eq C' d a (refChildren B d) (fun _ => 1) B
    (stronglyFair_iso_ref h.stronglyFair hd) (StronglyFair.almostFair B h.stronglyFair d)
  simp only [mul_one] at key
  rw [key]
  unfold lawInt
  simp only [mul_one, sum_leafLaw]

/-- On `𝔉`, `ν_{C'}(O_d) = fiberMass_d(C')` for every procedure `C'`.
Source: `fair-repair.md` FR-11 Step 1
Kind: C -/
theorem FairClass.nu_obs_eq_fiberMass' [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C' : Proc ι acts K) {d : ι} (hd : d ∈ queried B) :
    nu C' B (obs d) = fiberMass C' B d := by
  obtain ⟨a, ha⟩ := FinDistr.exists_pos (C' d)
  have h1 := h.nu_actEv_inter_obs_eq_fiberMass' C' hd a
  rw [h.nu_actEv_inter_obs C' hd a] at h1
  exact mul_left_cancel₀ ha.ne' h1

/-- **The payoff mass of `a ∧ O_d` is `C'(d)(a) · fiberMass_d(C') · Q_{C'}(d, a)`** on `𝔉` for
every procedure `C'`.
Source: `fair-repair.md` FR-11 Step 1; mandate T2(b)
Kind: P
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.paySum_actEv_inter_obs_eq' [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C' : Proc ι acts K) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    paySum C' B (actEv d a ∩ obs d) = (C' d).w a * (fiberMass C' B d * Q C' B d a) := by
  unfold paySum
  rw [h.worldEv_eq_drew' hd a]
  unfold drew
  rw [Finset.sum_filter]
  exact sum_drew_eq C' d a (refChildren B d) Prod.snd B
    (stronglyFair_iso_ref h.stronglyFair hd) (StronglyFair.almostFair B h.stronglyFair d)

/-- **The act value is `Q` for every procedure that realizes `O_d`**: on `𝔉`, if
`ν_{C'}(O_d) > 0` and `C'(d)(a) > 0`, then `𝔼_{C'}[r ∣ a ∧ O_d] = Q_{C'}(d, a)` — Step 1 with
`ν(O_d) > 0` in place of full support (the form a DF self-model needs: it may agree with a
deterministic `C` strictly below `d`).
Source: `fair-repair.md` FR-11 Step 1; `calibration.md` CA-2′ (the DF act value "is the honest
one-step deviation value")
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) `0 < ν_{C'}(O_d)`, (a) `0 < C'(d)(a)` -/
theorem FairClass.condExp_eq_Q' [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C' : Proc ι acts K) {d : ι} (hd : d ∈ queried B)
    (hnu : 0 < nu C' B (obs d)) (a : acts d) (ha : 0 < (C' d).w a) :
    condExp C' B (actEv d a ∩ obs d) = Q C' B d a := by
  have hfm : 0 < fiberMass C' B d := by rw [← h.nu_obs_eq_fiberMass' C' hd]; exact hnu
  unfold condExp
  rw [h.paySum_actEv_inter_obs_eq' C' hd a, h.nu_actEv_inter_obs_eq_fiberMass' C' hd a,
    mul_div_mul_left _ _ ha.ne', mul_div_cancel_left₀ _ hfm.ne']

end step1

/-! ### CA-3′'s locality: points queried below a `d`-node are strictly below `d` -/

section below

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] in
/-- A point queried below a `d`-node is strictly below `d`: if `subtreeAt B q₀ = decision d c` and
`e ∈ queried (c a)`, some `e`-node has `d` among its ancestor points.
Source: `calibration.md` Definition C2 ("'`e` strictly below `d`' := some `e`-node is a proper
descendant of some `d`-node"); CA-3′
Kind: P -/
theorem strictlyBelow_of_mem_queried_child :
    (B : Tree Ω ι acts K) → ∀ (q₀ : B.DecNode) (d : ι) (c : acts d → Tree Ω ι acts K),
      subtreeAt B q₀ = .decision d c → ∀ (a : acts d) (e : ι), e ∈ queried (c a) →
      StrictlyBelow B e d
  | leaf _ _, q₀, _, _, _, _, _, _ => q₀.elim
  | chance _ β child, ⟨i, q₀⟩, d, c, hc, a, e, he => by
      obtain ⟨q, hq, hanc⟩ := strictlyBelow_of_mem_queried_child (child i) q₀ d c hc a e he
      exact ⟨⟨i, q⟩, hq, hanc⟩
  | decision d' child, none, d, c, hc, a, e, he => by
      change Tree.decision d' child = Tree.decision d c at hc
      obtain ⟨rfl, hc'⟩ := Tree.decision.inj hc
      have hcc : child = c := eq_of_heq hc'
      subst hcc
      obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried (child a) e he
      exact ⟨some ⟨a, q⟩, hq, List.mem_cons_self⟩
  | decision d' child, some ⟨b, q₀⟩, d, c, hc, a, e, he => by
      obtain ⟨q, hq, hanc⟩ := strictlyBelow_of_mem_queried_child (child b) q₀ d c hc a e he
      exact ⟨some ⟨b, q⟩, hq, List.mem_cons_of_mem d' hanc⟩

end below

/-! ### The DF act values on `𝔉` -/

section df

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **The DF act values are `Q_C`** (CA-2′'s mechanism): on `𝔉`, under a DF self-model `C'` at a
queried `d` (full support at `d`, equal to `C` strictly below `d`, `ν_{C'}(O_d) > 0`, strict
clauses for `s_d`): `P_{s_d}(a) = C'(d)(a)` for every `a` (so `A_d^+ = A_d`) and
`V_{s_d}(a) = Q_C(d, a)` — the self-model's act value is the honest one-step deviation value
under `C` itself, because every point queried below a `d`-node is strictly below `d`
(`strictlyBelow_of_mem_queried_child`) and there `C' = C`.
Source: `calibration.md` CA-2′ ("the DF self-model agrees with `C` strictly below `d`, so the
act value at `d` is `Q_C(d, a)`"); A52
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) the DF clauses at `d` -/
theorem FairClass.dfMasked_at [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K} {s : ι → State Ω K} {d : ι}
    (hd : d ∈ queried B) {C' : Proc ι acts K} (hC'd : ∀ a, 0 < (C' d).w a)
    (hbelow : ∀ e, StrictlyBelow B e d → C' e = C e) (hnu : 0 < nu C' B (obs d))
    (hs : StrictClausesAt s obs C' B d) :
    (∀ x, (s d).pr (actEv d x) = (C' d).w x) ∧ (∀ x, x ∈ APlus s actEv d) ∧
      ∀ x, (s d).V (actEv d x) = Q C B d x := by
  have hQ : ∀ x, Q C' B d x = Q C B d x := by
    intro x
    unfold Q
    apply value_congr_queried
    intro e he
    apply hbelow
    obtain ⟨q₀, hq₀⟩ := refChildren_spec hd
    exact strictlyBelow_of_mem_queried_child B q₀ d (refChildren B d) hq₀ x e he
  have hpr : ∀ x, (s d).pr (actEv d x) = (C' d).w x := by
    intro x
    have h1 := hs.1 (actEv d x)
    rw [h.nu_actEv_inter_obs C' hd x] at h1
    exact mul_right_cancel₀ hnu.ne' h1
  refine ⟨hpr, fun x => ?_, fun x => ?_⟩
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hpr]
    exact hC'd x
  · have hpos : 0 < nu C' B (actEv d x ∩ obs d) := by
      rw [h.nu_actEv_inter_obs C' hd x]; exact mul_pos (hC'd x) hnu
    have h2 := hs.2 (actEv d x) (by rw [hpr]; exact hC'd x) hpos
    rw [← hQ x, ← h.condExp_eq_Q' C' hd hnu x (hC'd x)]
    unfold condExp
    rw [eq_div_iff hpos.ne']
    exact h2

/-- **DF-`T_EDT` on `𝔉` in `Q`-form**: for a DF-masked `C`, `T_EDT` holds iff at every queried
`d` every supported action maximises `Q_C(d, ·)` — the untrembled analogue of
`FairClass.eventTremble_iff_Q` (no `ε`, no limit).
Source: `calibration.md` CA-2′; A52
Kind: C
Fidelity: exact
Hyps: (a) `FairClass`, (a) `DFMasked` -/
theorem FairClass.dfMasked_tEdt_iff [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K} (s : ι → State Ω K)
    (hDF : DFMasked s obs C B) :
    TEdt s actEv C B ↔ ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b, Q C B d b ≤ Q C B d a := by
  constructor
  · intro hT d hd a ha b
    obtain ⟨C', hC'd, -, hbelow, hnu, hs⟩ := hDF d hd
    obtain ⟨-, hAplus, hV⟩ := h.dfMasked_at hd hC'd hbelow hnu hs
    have hmem := (mem_argmaxPlus s actEv d a).mp (hT d hd ⟨a, hAplus a⟩ a ha)
    have := hmem.2 b (hAplus b)
    rwa [hV, hV] at this
  · intro hQ d hd _ a ha
    obtain ⟨C', hC'd, -, hbelow, hnu, hs⟩ := hDF d hd
    obtain ⟨-, hAplus, hV⟩ := h.dfMasked_at hd hC'd hbelow hnu hs
    rw [mem_argmaxPlus]
    refine ⟨hAplus a, fun b _ => ?_⟩
    rw [hV, hV]
    exact hQ d hd a ha b

/-- **CA-2′, the DF theorem on `𝔉`**: a DF-masked procedure approved by `T_EDT` is optimal
(`C` mixed allowed). Route: the DF act values are `Q_C` (`FairClass.dfMasked_at`), so `T_EDT`
reads "`supp C(d) ⊆ argmax Q_C(d, ·)`" (`FairClass.dfMasked_tEdt_iff`), and Step 3
(`stronglyFair_isOptimal_of_pointwise_best`) closes. No trembles and no limit are taken: this is
the untrembled counterpart of Theorem 3 (`eventTrembleEdt_isOptimal_of_fairClass`).
Source: `calibration.md` CA-2′ ("DF-masked-EDT-consistency implies optimality on `𝔉`"); A52;
dp-cf-043; mandate T12(b)
Kind: C
Fidelity: exact
Hyps: (a) `FairClass`, (a) `DFMasked` (`dp-calibration`'s Definition C2 unchanged), (a) `TEdt` -/
theorem fairClass_dfMasked_isOptimal [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K} (s : ι → State Ω K)
    (hDF : DFMasked s obs C B) (hT : TEdt s actEv C B) : IsOptimal C B := by
  have hQ := (h.dfMasked_tEdt_iff s hDF).mp hT
  apply stronglyFair_isOptimal_of_pointwise_best h.stronglyFair C
  intro d hd m
  exact sum_w_mul_le_of_support_max (C d) (Q C B d) (fun a ha b => hQ d hd a ha b) m

/-- **D2 implies DF-`T_EDT`'s `Q`-form on `𝔉`** (the first inclusion of CA-4′'s chain at the level
of the act-value condition): an event-tremble-EDT-consistent `C` is a pointwise best response in
`Q_C`, so for *every* DF state assignment `s` it is `T_EDT`-approved.
Source: `calibration.md` CA-4′ (`{D2} ⊆ {DF-EDT}`); A52
Kind: C
Fidelity: weaker: the existence of a DF state assignment is not part of the conclusion (the
chain's `{D2} ⊆ {DF-EDT}` as a statement about procedures needs CA-3′'s positivity, see the
report) -/
theorem FairClass.tEdt_of_eventTremble_of_dfMasked [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} (h : FairClass obs actEv B) {C : Proc ι acts K}
    (hD2 : EventTrembleEdtConsistent obs actEv C B) (s : ι → State Ω K)
    (hDF : DFMasked s obs C B) : TEdt s actEv C B :=
  (h.dfMasked_tEdt_iff s hDF).mpr fun _ hd a ha b => h.Q_le_Q_of_eventTremble hD2 hd a ha b

end df

/-! ### Witness: `dupPay 1 0` -/

section dupPayWitness

open Cleanroom.Found.DpCoreTree.Catalogue

/-- Nothing is strictly below the only point of `dupPay` (depth one).
Source: none: infrastructure
Kind: L -/
theorem dupPay_not_strictlyBelow (ra rb : ℚ) (e : Unit) : ¬ StrictlyBelow (dupPay ra rb) e () := by
  rintro ⟨⟨i, q⟩, -, hanc⟩
  rcases q with _ | ⟨x, q'⟩
  · simp [dupPay, dupNode] at hanc
  · exact q'.elim

/-- **T12(b)'s witness on the two-member fiber `dupPay 1 0`**: `δ_a` is DF-masked (uniform
self-model, calibrated state) and `T_EDT`-approved, hence optimal by CA-2′ (`V = 1`); `δ_b` is
`T_EDT`-rejected under every DF state assignment and is not optimal.
Source: mandate T12(b)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem dupPay_dfMasked_witness :
    (∃ s : Unit → State Act2 ℚ,
      DFMasked s dupPayObs (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) ∧
      TEdt s dupPayActEv (Proc.ofFun fun _ => Act2.a) (dupPay 1 0)) ∧
    IsOptimal (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) ∧
    value (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) = 1 ∧
    (∀ s : Unit → State Act2 ℚ, DFMasked s dupPayObs (Proc.ofFun fun _ => Act2.b) (dupPay 1 0) →
      ¬ TEdt s dupPayActEv (Proc.ofFun fun _ => Act2.b) (dupPay 1 0)) ∧
    ¬ IsOptimal (Proc.ofFun fun _ => Act2.b) (dupPay 1 0) := by
  have hF := dupPay_fairClass 1 0
  have hq : (() : Unit) ∈ queried (dupPay 1 0) := pt_mem_queried (dupPay 1 0) ⟨0, none⟩
  have hpos : 0 < nu (Proc.uniform : Proc Unit (fun _ => Act2) ℚ) (dupPay 1 0) (dupPayObs ()) :=
    nu_uniform_obs_pos hF.pruned (hF.realized () hq)
  obtain ⟨-, hopt, hval, hnot⟩ := dupPay_theorem3_witness
  have hDF : DFMasked (fun _ => calibratedState Proc.uniform (dupPay 1 0) (dupPayObs ()) hpos)
      dupPayObs (Proc.ofFun fun _ => Act2.a) (dupPay 1 0) := by
    intro d _
    cases d
    have hU : (Proc.uniform : Proc Unit (fun _ => Act2) ℚ).FullSupport := Proc.uniform_fullSupport
    refine ⟨Proc.uniform, hU (), fun e _ => hU e,
      fun e he => absurd he (dupPay_not_strictlyBelow 1 0 e), hpos, ?_⟩
    exact strictClausesAt_calibratedState dupPayObs Proc.uniform (dupPay 1 0) _ () hpos rfl
  refine ⟨⟨_, hDF, ?_⟩, hopt, hval, fun s hDFb hT => ?_, hnot⟩
  · rw [hF.dfMasked_tEdt_iff _ hDF]
    intro d _ a ha b
    cases d
    cases a <;> cases b <;> simp [(dupPay_Q 1 0 _).1, (dupPay_Q 1 0 _).2, Proc.ofFun_w] at ha ⊢
  · have := (hF.dfMasked_tEdt_iff s hDFb).mp hT () hq .b (by simp [Proc.ofFun_w]) .a
    rw [(dupPay_Q 1 0 _).1, (dupPay_Q 1 0 _).2] at this
    norm_num at this

end dupPayWitness

end Cleanroom.Decision.DpEdtUdtFair
