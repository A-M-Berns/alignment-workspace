import Cleanroom.Udt.UdtEndorsePolicy.NodeValue

/-!
# T8: policy-respecting endorsement and "defers"

Sources: [[updateless-deference-ideate]] §1 Idea A and §7 "Most important caveat";
[[updateless-deference-model]] §1.3; trust-lab-2-014; red-team §B, §E1.

An update is encoded as the informed self's kernel `κᵤ` (the run-2 repair, red-team §E1): the
updateful policy is an EDT-argmax assembly `πᵤ` through `κᵤ` (`EdtAssembly U κᵤ πᵤ`). Definitions:

* `PolicyEndorses U κᵤ πᵤ := IsOptimal U πᵤ` — the ideate's "`πᵤ` is control-endorsed by `P`"
  (T4(a)'s form for one deterministic policy; with a single deterministic policy the conditioning
  in control endorsement is trivial, so control endorsement *is* optimality; `κᵤ` is inert in the
  definition, which is the point of T8(a)).
* `DefersAll U πᵤ := ∀ π, U π ≤ U πᵤ` — the model's (UD).
* `DefersMenu U πᵤ := ∀ a, U (fun _ => a) ≤ U πᵤ` — the ideate's "`E_P(diagonal of πᵤ) ≥ E_P(O)`
  for every option `O`" with the DDB menu of fixed options.

Results: `defersAll_iff_policyEndorses` (kind **S**: the two sides are the same predicate — the
ideate's biconditional is definitional under the all-policies reading);
`defersMenu_of_policyEndorses` (T) and `defersMenu_not_policyEndorses_witness` (N+, `refuted`:
the model's "equivalently, in DDB's menu form" is false); `policyEndorses_of_decoupled` (P, T7(b)
restated: ordinary endorsement is the special case with no cross-situation dependence is *not*
a theorem here — red-team §B — only this one-directional fact).
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {S A : Type} [Fintype S] [DecidableEq S]

/-- **Policy-respecting endorsement** of the update `κᵤ` at the assembly `πᵤ`: the prior
control-endorses the updated self's whole policy, i.e. `πᵤ` is optimal for `U`. With one
deterministic policy, the conditioning of control endorsement (T1) is on the whole support, so
"control-endorsed by `P`" is `IsOptimal`; the kernel `κᵤ` is a parameter the predicate does not
read — that inertness is T8(a).
Source: [[updateless-deference-ideate]] §1 Idea A ("`π_u` is control-endorsed by `P`") | trust-lab-2-014
Kind: D
Fidelity: exact under the deterministic-policy reading (ATTRIBUTION-UNVETTED)
Hyps: n/a -/
def PolicyEndorses (U : Policy S A → ℝ) (_κᵤ : S → A → Policy S A) (πᵤ : Policy S A) : Prop :=
  IsOptimal U πᵤ

/-- **Defers, all-policies form** (the model's (UD)): `U πᵤ ≥ U π` for every policy `π`.
Source: [[updateless-deference-model]] §1.3 (UD) | trust-lab-2-014
Kind: D
Fidelity: exact
Hyps: n/a -/
def DefersAll (U : Policy S A → ℝ) (πᵤ : Policy S A) : Prop := ∀ π, U π ≤ U πᵤ

/-- **Defers, DDB-menu form**: `U πᵤ ≥ U (const a)` for every fixed option `a` (the ideate's
"`E_P(diagonal of π_u) ≥ E_P(O)` for every option `O`", menu = constant policies).
Source: [[updateless-deference-ideate]] §1 Idea A (the "Hardness" paragraph); [[updateless-deference-model]] §1.3 ("Equivalently, in DDB's menu form")
Kind: D
Fidelity: exact
Hyps: n/a -/
def DefersMenu (U : Policy S A → ℝ) (πᵤ : Policy S A) : Prop := ∀ a, U (fun _ => a) ≤ U πᵤ

omit [Fintype S] [DecidableEq S] in
/-- **T8(a): "UDT defers to `u` iff `P` policy-endorses `u`" is definitional** — `DefersAll U πᵤ`
and `PolicyEndorses U κᵤ πᵤ` are the same predicate (`IsOptimal U πᵤ`) under the all-policies
reading of "defers". Kind **S**: this is the ideate's biconditional, and it has no content beyond
the definitions; the red-team's §A–§B diagnosis stands.
Source: [[updateless-deference-ideate]] §1 Idea A ("Claim: UDT defers to `u` iff `P` policy-endorses `u`") | trust-lab-2-014
Kind: S
Fidelity: exact (both sides are `IsOptimal U πᵤ`)
Hyps: none -/
theorem defersAll_iff_policyEndorses (U : Policy S A → ℝ) (κᵤ : S → A → Policy S A)
    (πᵤ : Policy S A) : DefersAll U πᵤ ↔ PolicyEndorses U κᵤ πᵤ :=
  Iff.rfl

omit [Fintype S] [DecidableEq S] in
/-- **Policy endorsement implies menu deference** (T): constant policies are policies.
Source: [[updateless-deference-model]] §1.3
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem defersMenu_of_policyEndorses {U : Policy S A → ℝ} {κᵤ : S → A → Policy S A}
    {πᵤ : Policy S A} (h : PolicyEndorses U κᵤ πᵤ) : DefersMenu U πᵤ :=
  fun a => h (fun _ => a)

/-- The utility `U id = 1`, `U swap = 3/4`, `U (const 0) = 1/2`, `U (const 1) = 0` on
`Fin 2 → Fin 2` (`tbl v00 v01 v10 v11` with `id = ![0, 1]`, `swap = ![1, 0]`).
Source: mandate T8(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def menuU : Policy (Fin 2) (Fin 2) → ℝ := tbl (1 / 2) 1 (3 / 4) 0

/-- **T8(b): menu deference does not imply policy endorsement** (N+, `refuted`): `swap` beats
every constant policy (`3/4 > 1/2, 0`) but is not optimal (`id` scores `1`). `swap` is a
legitimate "updated self's diagonal" under the mandate's framing: it is an EDT assembly through
its own decoupled kernel (a local optimum of `menuU`; third conjunct, added in repair round 1,
audit r1 N5). (i) The refuted sentence: [[updateless-deference-model]] §1.3, "Equivalently, in
DDB's menu form: for the menu of all constant ('fixed-option') policies `O` … `E_p(diagonal) ≥
E_p(O)` for every `O`"; (ii) reading: `DefersMenu` versus `DefersAll` with the menu of constant
policies; (iii) survivor: `defersMenu_of_policyEndorses` (one direction) — the menu form is
strictly weaker than (UD).
Source: [[updateless-deference-model]] §1.3 | trust-lab-2-014
Kind: N+
Fidelity: n/a (non-constant `πᵤ`, all four policies distinct in value; `πᵤ` is an EDT assembly through a decoupled kernel)
Hyps: none -/
theorem defersMenu_not_policyEndorses_witness :
    DefersMenu menuU ![1, 0] ∧ (∀ κᵤ, ¬ PolicyEndorses menuU κᵤ ![1, 0]) ∧
      EdtAssembly menuU (selfKernel ![1, 0]) ![1, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    fin_cases a
    · show menuU ![0, 0] ≤ menuU ![1, 0]
      simp [menuU]; norm_num
    · show menuU ![1, 1] ≤ menuU ![1, 0]
      simp [menuU]; norm_num
  · intro κᵤ h
    have := h ![0, 1]
    simp [menuU] at this
    norm_num at this
  · rw [edtAssembly_selfKernel_iff]
    intro s a
    fin_cases s <;> fin_cases a <;>
    · show menuU (Function.update ![1, 0] _ _) ≤ menuU (Function.update ![1, 0] _ _)
      simp [menuU] <;> norm_num

/-- **T8(c): the decoupled special case** (P, T7(b) restated in T8's vocabulary): for separable
`U` and a decoupled `κᵤ`, every EDT-argmax assembly is policy-endorsed. This is the one-way,
one-object fact behind the ideate's "ordinary (van Fraassen) endorsement is the special case with
no cross-situation dependence"; that sentence itself is a gloss (red-team §B) and no theorem is
named after it.
Source: [[updateless-deference-ideate]] §1 Idea A | red-team §B | trust-lab-2-014
Kind: C
Fidelity: exact (the one direction that holds)
Hyps: (a) all -/
theorem policyEndorses_of_decoupled {U : Policy S A → ℝ} {p : S → ℝ} {u : S → A → ℝ}
    (hU : SeparableW U p u) {κᵤ : S → A → Policy S A} {base : S → Policy S A}
    (hκ : Decoupled κᵤ base) {πᵤ : Policy S A} (hEDT : EdtAssembly U κᵤ πᵤ) :
    PolicyEndorses U κᵤ πᵤ :=
  edt_decoupled_globally_optimal hU hκ hEDT

end

end Cleanroom.Udt.UdtEndorsePolicy
