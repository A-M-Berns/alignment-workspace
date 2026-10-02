import Cleanroom.Udt.UdtCommTrust.Determination
import Cleanroom.Udt.UdtCommTrust.Prob
import Cleanroom.Udt.UdtCtExamples.CoordButtons
import Cleanroom.Udt.UdtCtExamples.Infra

/-!
# `Cleanroom.Udt.UdtCtExamples.Screening`: the screening extension (T7(e)) and "proper
policies" (T7(c))

Work package `udt-ct-examples`, stretch targets T7(e) (bli-paper-091, 081's extension) and T7(c)
(bli-paper-2-019), added in repair round 1 (audit r1 N9/N10 asked for the open list's prose
entries to become Lean).

* `PolicyFairCT S`: two realized dynamics encoding the same external policy have the same
  conditional expected utility. `policyFairCT_of_decisionDetermined`: decision-determination
  gives it, from `udt-comm-trust`'s `condExp_DIB_eq_policyUtility` (`C`).
* `EffScreens S`: the effective policy screens the chosen one off from the utility,
  `E[U ∣ Π† = π†, Π* = π*] = E[U ∣ Π† = π†]` on non-empty events. `screening_display`
  (bli-paper-091's display): under `EffScreens`, two chosen policies with the same conditional
  law of `Π†` have the same conditional expected utility — by total expectation over `Π†`
  (`condExpJunk_total`), `P`.
* `Proper S ω`: the chosen policy's instance policies agree across external observations. On
  `CB` the notion is **degenerate** (findings F-10): `Proper` over all three instances holds iff
  the channel state equals the room policy (`CB.proper_iff`) — a coincidence of encodings, since
  at `pre` the "action" is the channel state and at a room it is a button — so under `W5` the
  `$5`-policy pill world satisfies the rule at both rooms with an *improper* `Π*`
  (`CB.improper_udtRuleAt5`), while properness across the two rooms holds at every world by
  construction (`CB.roomProper`). The mandate's "every `UdtRuleAt`-world has proper `Π*` under
  symmetric weights" is therefore false on `CB` for a representation reason and its asymmetric
  half is true for the same reason; neither says anything about the write-up's notion, which
  needs instances of one type and room-dependent chosen policies — not on this carrier.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OI] [Fintype OE] [DecidableEq OI] [DecidableEq OE] [Fintype AI] [Fintype AE]
  [DecidableEq AI] [DecidableEq AE] [Fintype DI] [DecidableEq DI] [Fintype DE] [DecidableEq DE]
  [Fintype DB] [DecidableEq DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **Policy fairness, C&T-style**: realized dynamics `d`, `d'` encoding the same external policy
(`[[d]]_Π̈ = [[d']]_Π̈`) have the same conditional expected utility `E[U ∣ D_{I,B} = ·]`. The
identification with `udt-bli-core`'s `PolicyFair` (another carrier) is not attempted.
Source: bli-paper-081 (extension), 091; mandate T7(e)
Kind: D
Fidelity: variant: on `D_{I,B}`-atoms of this structure, not `udt-bli-core`'s `ProcLayer`
Hyps: n/a -/
noncomputable def PolicyFairCT : Prop := ∀ d d' : DI × DB, (S.evDIB d).Nonempty →
  (S.evDIB d').Nonempty → S.polOf d = S.polOf d' →
  condExpJunk S.μ.w S.U (S.evDIB d) (-1) = condExpJunk S.μ.w S.U (S.evDIB d') (-1)

/-- **Decision-determination implies policy fairness**: both sides are the policy utility of
the common external policy (`condExp_DIB_eq_policyUtility`).
Source: bli-paper-081 (extension); mandate T7(e)
Kind: C
Fidelity: exact
Hyps: (a) `condExp_DIB_eq_policyUtility` (udt-comm-trust); §3 (c) -/
theorem policyFairCT_of_decisionDetermined (h : S.DecisionDetermined) : PolicyFairCT S :=
  fun d d' hd hd' hpol => by
    rw [S.condExp_DIB_eq_policyUtility h hd, S.condExp_DIB_eq_policyUtility h hd', hpol]

/-- **The effective policy screens the chosen policy off from the utility**:
`E[U ∣ Π† = π†, Π* = π*] = E[U ∣ Π† = π†]` whenever the joint event is non-empty.
Source: bli-paper-091; mandate T7(e)
Kind: D
Fidelity: exact (on non-empty events; junk `−1` elsewhere)
Hyps: n/a -/
noncomputable def EffScreens : Prop := ∀ π π' : Policy (OI × OE) (AI × AE),
  (event fun ω => S.polD ω = π ∧ S.polS ω = π').Nonempty →
  condExpJunk S.μ.w S.U (event fun ω => S.polD ω = π ∧ S.polS ω = π') (-1) =
    condExpJunk S.μ.w S.U (event fun ω => S.polD ω = π) (-1)

/-- Supporting lemma: the `Π†`-cell of a `Π*`-event is the joint event.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem filter_polD_eq (π π' : Policy (OI × OE) (AI × AE)) :
    ((event fun ω => S.polS ω = π').filter fun ω => S.polD ω = π) =
      event fun ω => S.polD ω = π ∧ S.polS ω = π' := by
  ext ω
  simp only [Finset.mem_filter]
  tauto

/-- Supporting lemma: a `Π†`-cell of positive conditional probability is non-empty, and
`EffScreens` evaluates it.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExp_cell_of_effScreens (hS : EffScreens S) {π π' : Policy (OI × OE) (AI × AE)}
    (hπ' : (event fun ω => S.polS ω = π').Nonempty)
    (hne : condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π') 0 ≠ 0) :
    condExpJunk S.μ.w S.U ((event fun ω => S.polS ω = π').filter fun ω => S.polD ω = π) (-1) =
      condExpJunk S.μ.w S.U (event fun ω => S.polD ω = π) (-1) := by
  rw [filter_polD_eq S]
  apply hS
  rw [condProbJunk_of_nonempty S.pos hπ'] at hne
  have hmass : mass S.μ.w ((event fun ω => S.polD ω = π) ∩ event fun ω => S.polS ω = π') ≠ 0 :=
    fun h0 => hne (by rw [h0, zero_div])
  rw [Ne, mass_eq_zero_iff S.pos, ← Ne, ← Finset.nonempty_iff_ne_empty] at hmass
  obtain ⟨ω, hω⟩ := hmass
  rw [Finset.mem_inter, mem_event, mem_event] at hω
  exact ⟨ω, mem_event.2 hω⟩

/-- **bli-paper-091's display**: under `EffScreens`, two chosen policies with the same
conditional law of `Π†` (`P(Π† = · ∣ Π* = π₂) = P(Π† = · ∣ Π* = π₃)`) have the same conditional
expected utility `E[U ∣ Π* = ·]`. Proof: total expectation over `Π†` on each side
(`condExpJunk_total`); a cell of conditional probability `0` contributes `(−1) · 0` on both
sides, a cell of positive probability is evaluated by `EffScreens` to `E[U ∣ Π† = π†]` on both.
Source: bli-paper-091; mandate T7(e)
Kind: P
Fidelity: exact
Hyps: `EffScreens` is the item's own antecedent (bli-paper-091's proposed definition) — neither derived nor a published theorem, a hypothesis of the item (audit r2 adversarial N1); both `Π*`-events realized; witness `Flip.display`; §3 (c) -/
theorem screening_display (hS : EffScreens S) {π₂ π₃ : Policy (OI × OE) (AI × AE)}
    (h₂ : (event fun ω => S.polS ω = π₂).Nonempty) (h₃ : (event fun ω => S.polS ω = π₃).Nonempty)
    (hlaw : ∀ π : Policy (OI × OE) (AI × AE),
      condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π₂) 0 =
        condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π₃) 0) :
    condExpJunk S.μ.w S.U (event fun ω => S.polS ω = π₂) (-1) =
      condExpJunk S.μ.w S.U (event fun ω => S.polS ω = π₃) (-1) := by
  rw [condExpJunk_total S.pos S.U S.polD h₂ (-1), condExpJunk_total S.pos S.U S.polD h₃ (-1)]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← hlaw π]
  by_cases hp : condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π₂) 0 = 0
  · rw [hp, mul_zero, mul_zero]
  · rw [condExp_cell_of_effScreens S hS h₂ hp,
      condExp_cell_of_effScreens S hS h₃ (by rw [← hlaw π]; exact hp)]

/-- **A proper chosen policy** (the write-up's notion, bli-paper-2-019): its instance policies
agree across external observations, `(o ↦ Π*(ω)(o, e)) = (o ↦ Π*(ω)(o, e'))` for all `e, e'`.
Representable here because every instance policy has type `OI → AI × AE`; absent from the
LaTeX; ill-posed when the instances' action types differ in meaning (module docstring).
Source: [[udt-tiling-working-notes-2025-06-30]] (the write-up's "proper policies"; bli-paper-2-019); mandate T7(c)
Kind: D
Fidelity: exact for the write-up's wording on a single action type
Hyps: n/a -/
def Proper (ω : Ω) : Prop :=
  ∀ e e' : OE, (fun o => S.polS ω (o, e)) = fun o => S.polS ω (o, e')

end General

namespace CB

/-- **On `CB`, `Proper` over all three instances holds iff the channel state equals the room
policy** (`s = k`): a coincidence of the encodings of two actions of different meaning (the
pre-instance's "action" is the channel state, a room's is a button). The notion is degenerate
on this carrier (findings F-10).
Source: mandate T7(c); findings F-10
Kind: L
Fidelity: n/a (the degeneracy, made exact)
Hyps: none -/
theorem proper_iff (W : IntWeights Ω) (ω : Ω) :
    Proper (S W).toAbstractDS ω ↔ ω.1.1 = ω.1.2 := by
  show (∀ e e' : Fin 3, (fun o : Fin 2 => polOf' ω.1.1 ω.1.2 (o, e)) =
    fun o => polOf' ω.1.1 ω.1.2 (o, e')) ↔ ω.1.1 = ω.1.2
  revert ω
  decide +kernel

/-- **Properness across the two rooms holds at every world of `CB`** by construction (the room
policy presses `k` at both rooms).
Source: mandate T7(c)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem roomProper (W : IntWeights Ω) (ω : Ω) :
    (fun o => (S W).polS ω (o, 1)) = fun o => (S W).polS ω (o, 2) := by
  show (fun o : Fin 2 => polOf' ω.1.1 ω.1.2 (o, 1)) = fun o => polOf' ω.1.1 ω.1.2 (o, 2)
  revert ω
  decide +kernel

/-- **Under `W5` an improper `Π*` satisfies the rule at both room inputs**: the `$5`-policy pill
world `((1, 0), (ö, a))` has `s = 1 ≠ 0 = k`, so it is not `Proper`, and `udtRuleAt5` holds there.
This is the mandate's "with asymmetric weights an improper `Π*` satisfies the rule", true on
`CB` for the representation reason of `proper_iff`, not the write-up's (findings F-10).
Source: mandate T7(c)
Kind: L
Fidelity: weaker: holds through the encoding coincidence of `proper_iff`
Hyps: none; §3 (c) -/
theorem improper_udtRuleAt5 :
    ∃ ω : Ω, ¬ Proper (S W5).toAbstractDS ω ∧ ∀ o e, e ≠ 0 → (S W5).UdtRuleAt ω o e :=
  ⟨((1, 0), (0, 0)), fun h => by rw [proper_iff] at h; exact absurd h (by decide),
    fun o e he => udtRuleAt5 _ rfl o e he⟩

/-! ### Repair round 2: `PolicyFairCT` exercised on `CB W5` (audit r2 adversarial N3) -/

/-- **`polOf` is not injective on `CB`'s realized dynamics**: the `$5`-policy and the
`$10`-policy pill dynamics encode the same external policy `(pre ↦ pill, $10, $10)`.
Source: audit r2 (adversarial N3)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_pill_eq (W : IntWeights Ω) : (S W).polOf (1, 0) = (S W).polOf (1, 1) := by
  rw [polOf_eq, polOf_eq]
  funext e
  revert e
  decide

/-- **`CB.S W5` is policy-fair** (`PolicyFairCT`), from decision-determination.
Source: bli-paper-081 (extension); mandate T7(e); audit r2 (adversarial N3)
Kind: C
Fidelity: exact
Hyps: (a) `policyFairCT_of_decisionDetermined`, `decisionDetermined5` -/
theorem policyFairCT5 : PolicyFairCT (S W5).toAbstractDS :=
  policyFairCT_of_decisionDetermined _ decisionDetermined5

/-- **The non-trivial instance on `CB W5`**: the two pill atoms — distinct realized dynamics
with the same external policy (`polOf_pill_eq`) — have the same conditional expected utility,
`E[U ∣ pill, $5 policy] = E[U ∣ pill, $10 policy]` (both `7/12`). On a carrier whose `polOf` is
injective on realized dynamics `PolicyFairCT` holds trivially; on `CB` it does not.
Source: bli-paper-081 (extension); audit r2 (adversarial N3)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem pill_atoms_fair5 :
    condExpJunk (S W5).μ.w (S W5).U ((S W5).evDIB (1, 0)) (-1) =
      condExpJunk (S W5).μ.w (S W5).U ((S W5).evDIB (1, 1)) (-1) :=
  policyFairCT5 (1, 0) (1, 1) ⟨((1, 0), (0, 0)), mem_event.2 rfl⟩
    ⟨((1, 1), (0, 0)), mem_event.2 rfl⟩ (polOf_pill_eq W5)

end CB

/-! ### Repair round 2: a non-degenerate witness for `screening_display` (audit r2 adversarial N1)

On the package's own carriers the hypothesis package of `screening_display` is degenerate: on
`CBm` and `HF` `Π† = Π*` at every world, so equal conditional laws of `Π†` force `π₂ = π₃`; on
`CB W5` `EffScreens` fails (the pill changes `E[U ∣ k = $10]`). `Flip` (four worlds `(k, f)`:
chosen button `k`, a flip `f = 1` forces the other button, `U = 𝟙[Ä = 1]`) inhabits the full
package: `EffScreens` holds because `U` is a function of the effective action, the law of `Π†`
given either chosen policy is uniform, and the display's conclusion is about two different
policies. Lifted from the audit-r2 probe `ScreeningWitness`. -/

namespace Flip

open Cleanroom.Udt.UdtCommTrust

/-- Worlds `(k, f)`: chosen button `k`, flip flag `f`.
Source: none: infrastructure (audit r2 adversarial N1)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights on the four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The external action: `k`, flipped when `f = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def act (ω : Ω) : Fin 2 := if ω.2 = 1 then (if ω.1 = 0 then 1 else 0) else ω.1

/-- Utility numerator `𝟙[Ä = 1]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if act ω = 1 then 1 else 0

/-- **The flip structure**: one instance, trivial observations, `D_B = (k, f)`, `Ä = act`,
`Π* = press k`; `Π† ≠ Π*` on the flip worlds (half the mass).
Source: audit r2 (adversarial N1, probe `ScreeningWitness`)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : AbstractDS Ω (Fin 1) (Fin 1) (Fin 1) (Fin 2) (Fin 1) (Fin 1) (Fin 2 × Fin 2)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE _ := 0
  aI _ := 0
  aE := act
  dI _ := 0
  dE _ := 0
  dB ω := ω
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (0, ω.1)
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  B_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- The policy type of `Flip`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Pol := Policy (Fin 1 × Fin 1) (Fin 1 × Fin 2)

/-- **`Π†` on `Flip` presses the effective action `act ω`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun _ => ((0 : Fin 1), act ω) :=
  polD_eq_of S (fun ω _ => (0, act ω)) (fun _ => rfl)
    (fun ω ω' h => by have h' : ω = ω' := h; rw [h'])
    (by
      show ∀ (ω : Ω) (o : Fin 1 × Fin 1), ∃ ω' : Ω, ω' = ω ∧ ((0 : Fin 1), (0 : Fin 1)) = o
      decide +kernel) ω

/-- Supporting lemma `evS_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (π' : Pol) : (event fun ω => S.polS ω = π') =
    event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π' :=
  event_congr fun _ => Iff.rfl

/-- Supporting lemma: `EffScreens` as a count identity, for every pair of policies (trivially
true when the joint event is empty: both sides are `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key1 : ∀ π π' : Pol,
    csum weights u (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π ∧
        (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π') *
      weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π) =
    csum weights u (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π) *
      weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π ∧
        (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π') := by
  decide +kernel

/-- **`EffScreens` holds on `Flip`**: `E[U ∣ Π† = π, Π* = π'] = E[U ∣ Π† = π]` on every non-empty
joint event — `U` is a function of the effective action.
Source: bli-paper-091; audit r2 (adversarial N1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem effScreens : EffScreens S := by
  intro π π' hne
  have h1 : (event fun ω => S.polD ω = π ∧ S.polS ω = π') =
      event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π ∧
        (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π' :=
    event_congr fun ω => by rw [polD_eq]; exact Iff.rfl
  have h2 : (event fun ω => S.polD ω = π) =
      event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π :=
    event_congr fun ω => by rw [polD_eq]
  rw [h1] at hne
  rw [h1, h2]
  have hF : (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π).Nonempty :=
    hne.mono fun ω hω => mem_event.2 (mem_event.1 hω).1
  exact condExpJunk_natDiv_eq weights u (by norm_num) hne hF (key1 π π') (-1)

/-- The chosen policy "press `0`".
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev π₂ : Pol := fun _ => (0, 0)

/-- The chosen policy "press `1`".
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev π₃ : Pol := fun _ => (0, 1)

/-- Both chosen policies are realized.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem h₂ : (event fun ω => S.polS ω = π₂).Nonempty := ⟨(0, 0), mem_event.2 rfl⟩

/-- Both chosen policies are realized.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem h₃ : (event fun ω => S.polS ω = π₃).Nonempty := ⟨(1, 0), mem_event.2 rfl⟩

/-- Supporting lemma: the equal-law identity in count form.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key2 : ∀ π : Pol,
    weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π) ∩
        event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₂) *
      weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₃) =
    weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π) ∩
        event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₃) *
      weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₂) := by
  decide +kernel

/-- **Equal conditional laws of `Π†`** given `Π* = π₂` and given `Π* = π₃` (both uniform).
Source: bli-paper-091; audit r2 (adversarial N1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlaw : ∀ π : Pol,
    condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π₂) 0 =
      condProbJunk S.μ.w (event fun ω => S.polD ω = π) (event fun ω => S.polS ω = π₃) 0 := by
  intro π
  have h2 : (event fun ω => S.polD ω = π) =
      event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), act ω)) = π :=
    event_congr fun ω => by rw [polD_eq]
  rw [h2, evS_eq, evS_eq, show S.μ.w = weights.w from rfl]
  exact weights.condProbJunk_eq_of_cnt (by decide +kernel) (by decide +kernel) (key2 π)

/-- **`screening_display` instantiated on `Flip`** with every hypothesis discharged on the
witness: `E[U ∣ Π* = press 0] = E[U ∣ Π* = press 1]` (both `1/2`, `values`), for two different
chosen policies (`pol_ne`), a varying `Π†` (`polD_varies`) and `Π† ≠ Π*` on the flip worlds
(`modBeh_flip`).
Source: bli-paper-091; mandate T7(e); audit r2 (adversarial N1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem display :
    condExpJunk S.μ.w S.U (event fun ω => S.polS ω = π₂) (-1) =
      condExpJunk S.μ.w S.U (event fun ω => S.polS ω = π₃) (-1) :=
  screening_display S effScreens h₂ h₃ hlaw

/-- Non-degeneracy: the two chosen policies differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pol_ne : π₂ ≠ π₃ := by decide

/-- Non-degeneracy: `Π†` varies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_varies : S.polD (0, 0) ≠ S.polD (1, 0) := by rw [polD_eq, polD_eq]; decide

/-- Non-degeneracy: `Π† ≠ Π*` on a flip world (behavioural modification, `Modification.lean`'s
`ModBeh`, on half the mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem modBeh_flip : S.polD (0, 1) ≠ S.polS (0, 1) := by rw [polD_eq]; decide

/-- Both conditional expectations are `1/2` (count form: `csum = 1`, `cnt = 2` on each side).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem values :
    csum weights u (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₂) = 1 ∧
    weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₂) = 2 ∧
    csum weights u (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₃) = 1 ∧
    weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => ((0 : Fin 1), ω.1)) = π₃) = 2 := by
  decide +kernel

end Flip

end Cleanroom.Udt.UdtCtExamples
