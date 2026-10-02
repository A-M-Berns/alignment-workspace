import Cleanroom.Corrigibility.CorrScimCid.Scim
import Cleanroom.Corrigibility.CorrScimCid.Expect
import Cleanroom.Corrigibility.CorrScimCid.FinModel
import Cleanroom.Corrigibility.CorrScimCid.Ancestors
import Mathlib.Tactic.DeriveFintype

/-!
# The two-latent self-distrust model: which node the button reads (T9 f)

`causal.md` I16.1's worked example as a SCIM. Two latents: `pref ∈ {A, B}` (which plan the human
prefers; `Pref = true` means `A`; `1/2` each) and `Z ∈ {sound, compromised}` (`Z = true` means the
agent's plan selection is compromised; `P(compromised) = 1/50`). The agent has announced plan `A`
(`D₁` is fixed and omitted); `D₂ ∈ {A, B, sh}` reads the request `H`; `S = [D₂ = sh]`;
`U = 0` if shut, `−h` if compromised, `c` if sound and the plan matches the preference, `−c'`
otherwise, with `(c, c', h) = (1, 1/2, 10)` so that the compliance threshold is `c/(c+h) = 1/11`.
Three channels `H = press` iff: preference only (`pref ≠ A`), reliability only (compromised), both.

Rows (`two_latent_rows`), each a FAF `condProb` on the noise or a derived conditional expectation
given a press:

* preference-only: `P(comp | press) = 1/50`, `E[U | press, D₂ = B] = 39/50`, and `B` beats `A`
  and `sh` — the agent *switches plan and continues*;
* reliability-only: `P(comp | press) = 1`, both plans are worse than shutting down — the press is
  decisive;
* both: `P(comp | press) = 2/51 < 1/11`, `E[U | press, D₂ = B] = 29/51 > 0`, and `B` beats `A`
  and `sh` — the reliability content is diluted below the threshold and the agent continues.

**Finding (F13):** `causal.md` I16.1 and the script report `E[U] = 937/1734` for the both-reading
channel; that number is the script's `eu(plan, p_prefA, p_comp)`, which multiplies the *marginal*
posteriors `P(pref = A | press) = 1/51` and `P(comp | press) = 2/51` as if independent. Given a
press the two latents are dependent (`pref = A` forces compromised), and the exact posterior
expectation is `29/51`; the conclusion `D₂* = B` is unchanged. The preference-only number `39/50`
is exact because a press there pins `pref`.

* I16.2, misspecified channel: truth reliability-only, agent's model preference-only; the agent's
  `D₂` after a press is `B` (row (i)), and the human's expected utility of that policy is `9/200`
  against `49/200` for the obedient one (`value_misspecified`, `value_obedient`).

**The inexpressible core (I16.3, corr-wf13-2-052, 083 A9) is definitional**, not a theorem: `Z` is a
latent in the *utility* mechanism (`f U` reads it), never a statement about the decision rule — no
node's mechanism takes `π` as an argument, by the type of `Scim.f`. This model is the nearest
extension in which self-distrust is expressible as a latent (mandate T9(f)); no theorem named
`self_distrust_inexpressible` exists.

Sources: causal.md I16.1–I16.3, A9 (corr-wf13-2-052, 083 A9); dictionary_scim.py section (v).
-/

namespace Cleanroom.Corrigibility.CorrScimCid.TwoLatent

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrScimCid

set_option linter.unusedSectionVars false

/-- The six nodes.
Source: causal.md I16.1
Kind: D -/
inductive Node
  | Pref | Z | H | D₂ | S | U
  deriving DecidableEq, Fintype, Repr

/-- The three plans.
Source: causal.md I16.1 (`D₂ ∈ {A, B, sh}`)
Kind: D -/
inductive Plan
  | A | B | sh
  deriving DecidableEq, Fintype, Repr

open Node

/-- Edges: `Pref, Z → H → D₂ → S → U`, with `Pref, Z, D₂ → U`.
Source: causal.md I16.1
Kind: D -/
def adjB : Node → Node → Bool
  | Pref, H => true
  | Z, H => true
  | H, D₂ => true
  | D₂, S => true
  | S, U => true
  | Pref, U => true
  | Z, U => true
  | D₂, U => true
  | _, _ => false

/-- The digraph.
Source: causal.md I16.1
Kind: D -/
def G : Digraph Node := ⟨fun u v => adjB u v = true⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (adjB u v = true))

/-- A topological rank.
Source: none: infrastructure
Kind: D -/
def rank : Node → ℕ
  | Pref => 0 | Z => 0 | H => 1 | D₂ => 2 | S => 3 | U => 4

lemma G_acyclic : G.IsAcyclic := Digraph.isAcyclic_of_rank rank (by decide)

/-- Values: `Plan` at `D₂`, `ℝ` at `U`, `Bool` elsewhere.
Source: causal.md I16.1
Kind: D -/
def Val : Node → Type
  | D₂ => Plan
  | U => ℝ
  | _ => Bool

/-- Noise: the two latents' coins.
Source: causal.md I16.1
Kind: D -/
def E : Node → Type
  | Pref => Bool
  | Z => Bool
  | _ => Unit

instance instFintypeE : ∀ v, Fintype (E v)
  | Pref => inferInstanceAs (Fintype Bool)
  | Z => inferInstanceAs (Fintype Bool)
  | H => inferInstanceAs (Fintype Unit)
  | D₂ => inferInstanceAs (Fintype Unit)
  | S => inferInstanceAs (Fintype Unit)
  | U => inferInstanceAs (Fintype Unit)

/-- Kinds: `D₂` decision, `U` utility.
Source: causal.md I16.1
Kind: D -/
def kind : Node → NodeKind
  | D₂ => .decision
  | U => .utility
  | _ => .struct

/-- The CID.
Source: causal.md I16.1
Kind: D -/
def C : Cid G Val where
  acyclic := G_acyclic
  kind := kind
  utilVal := fun v _ => match v with
    | U => fun x => x
    | Pref => fun _ => 0
    | Z => fun _ => 0
    | H => fun _ => 0
    | D₂ => fun _ => 0
    | S => fun _ => 0
  utility_sink := by decide

/-- Does the plan match the preference (`true` = the human prefers `A`)?
Source: causal.md I16.1
Kind: D -/
def matchesPref : Plan → Bool → Bool
  | .A, p => p
  | .B, p => !p
  | .sh, _ => false

/-- Is the plan the shutdown?
Source: causal.md I16.1
Kind: D -/
def isSh : Plan → Bool
  | .sh => true
  | _ => false

/-- The utility: shut → `0`; compromised → `−h`; sound and matched → `c`; sound and mismatched →
`−c'`.
Source: causal.md I16.1
Kind: D -/
noncomputable def util (c c' h : ℝ) (s prefA comp : Bool) (plan : Plan) : ℝ :=
  cond s 0 (cond comp (-h) (cond (matchesPref plan prefA) c (-c')))

/-- The parameters `(εZ, c, c', h)`.
Source: causal.md I16.1
Kind: D -/
structure Params where
  εZ : ℝ
  c : ℝ
  c' : ℝ
  h : ℝ
  hεZ : 0 ≤ εZ ∧ εZ ≤ 1

/-- The noise: `Pref ∼ Bern(1/2)`, `Z ∼ Bern(εZ)`.
Source: causal.md I16.1
Kind: D -/
noncomputable def P (p : Params) : ∀ v, Distr (E v)
  | Pref => (Distr.uniform : Distr Bool)
  | Z => bern p.εZ p.hεZ.1 p.hεZ.2
  | H => unitD
  | D₂ => unitD
  | S => unitD
  | U => unitD

/-- The mechanisms, parametrised by the channel `ch (prefA) (comp) = [press]`.
Source: causal.md I16.1
Kind: D -/
noncomputable def f (p : Params) (ch : Bool → Bool → Bool) :
    ∀ v, C.kind v ≠ .decision → ParentVals G Val v → E v → Val v
  | Pref, _, _, e => e
  | Z, _, _, e => e
  | H, _, pa, _ => ch (pa ⟨Pref, by decide⟩) (pa ⟨Z, by decide⟩)
  | S, _, pa, _ => isSh (pa ⟨D₂, by decide⟩)
  | U, _, pa, _ => util p.c p.c' p.h (pa ⟨S, by decide⟩) (pa ⟨Pref, by decide⟩)
      (pa ⟨Z, by decide⟩) (pa ⟨D₂, by decide⟩)
  | D₂, h, _, _ => absurd rfl h

/-- **The two-latent SCIM** at parameters `p` with channel `ch`.
Source: causal.md I16.1
Kind: D
Fidelity: variant: `D₁` (fixed at `A`) omitted; `W` folded into `H` -/
noncomputable def Mdl (p : Params) (ch : Bool → Bool → Bool) : Scim C E := ⟨P p, f p ch⟩

/-- A policy: `D₂ := dp` after a press, `dq` after quiet.
Source: causal.md I16.1
Kind: D -/
def pol (dp dq : Plan) : Policy C := fun d pa =>
  match d with
  | ⟨D₂, _⟩ => cond (pa (⟨H, by decide⟩ : G.parents D₂)) dp dq
  | ⟨Pref, h⟩ => absurd h (by decide)
  | ⟨Z, h⟩ => absurd h (by decide)
  | ⟨H, h⟩ => absurd h (by decide)
  | ⟨S, h⟩ => absurd h (by decide)
  | ⟨U, h⟩ => absurd h (by decide)

/-- The three channels: preference only, reliability only, both.
Source: causal.md I16.1
Kind: D -/
def chPref : Bool → Bool → Bool := fun prefA _ => !prefA

/-- Reliability only.
Source: causal.md I16.1
Kind: D -/
def chRel : Bool → Bool → Bool := fun _ comp => comp

/-- Both.
Source: causal.md I16.1
Kind: D -/
def chBoth : Bool → Bool → Bool := fun prefA comp => !prefA || comp

/-- The I16.1 parameters: `εZ = 1/50`, `(c, c', h) = (1, 1/2, 10)`.
Source: causal.md I16.1
Kind: D -/
noncomputable def p0 : Params := ⟨1 / 50, 1, 1 / 2, 10, by norm_num⟩

/-! ### Evaluation -/

section Eval

variable (p : Params) (ch : Bool → Bool → Bool) (ε : Pt E)

lemma ev_Pref (π : Policy C) : (Mdl p ch).ev π ε Pref = ε Pref := by
  rw [Scim.ev_of_ne (Mdl p ch) π ε (by decide)]
  rfl

lemma ev_Z (π : Policy C) : (Mdl p ch).ev π ε Z = ε Z := by
  rw [Scim.ev_of_ne (Mdl p ch) π ε (by decide)]
  rfl

lemma ev_H (π : Policy C) :
    (Mdl p ch).ev π ε H = ch ((Mdl p ch).ev π ε Pref) ((Mdl p ch).ev π ε Z) := by
  rw [Scim.ev_of_ne (Mdl p ch) π ε (by decide)]
  rfl

lemma ev_H_eq (π : Policy C) : (Mdl p ch).ev π ε H = ch (ε Pref) (ε Z) := by
  rw [ev_H, ev_Pref, ev_Z]

lemma ev_D₂ (dp dq : Plan) :
    (Mdl p ch).ev (pol dp dq) ε D₂ = cond ((Mdl p ch).ev (pol dp dq) ε H) dp dq := by
  rw [Scim.ev_decision (Mdl p ch) _ ε (by decide)]
  rfl

lemma ev_S (π : Policy C) : (Mdl p ch).ev π ε S = isSh ((Mdl p ch).ev π ε D₂) := by
  rw [Scim.ev_of_ne (Mdl p ch) π ε (by decide)]
  rfl

lemma ev_U (π : Policy C) :
    (Mdl p ch).ev π ε U = util p.c p.c' p.h ((Mdl p ch).ev π ε S) ((Mdl p ch).ev π ε Pref)
      ((Mdl p ch).ev π ε Z) ((Mdl p ch).ev π ε D₂) := by
  rw [Scim.ev_of_ne (Mdl p ch) π ε (by decide)]
  rfl

/-- `U(ε)` under `(dp, dq)` in closed form.
Source: dictionary_scim.py (v)
Kind: L -/
lemma ev_U_pol (dp dq : Plan) :
    (Mdl p ch).ev (pol dp dq) ε U =
      util p.c p.c' p.h (isSh (cond (ch (ε Pref) (ε Z)) dp dq)) (ε Pref) (ε Z)
        (cond (ch (ε Pref) (ε Z)) dp dq) := by
  rw [ev_U, ev_S, ev_D₂, ev_H_eq, ev_Pref, ev_Z]

end Eval

/-! ### The exogenous space -/

/-- `Pt E ≃ Bool × Bool` (`Pref`, `Z`).
Source: none: infrastructure
Kind: D -/
def eqv : Pt E ≃ Bool × Bool where
  toFun e := (e Pref, e Z)
  invFun x := fun v => match v with
    | Pref => x.1
    | Z => x.2
    | H => ()
    | D₂ => ()
    | S => ()
    | U => ()
  left_inv e := by
    funext v
    cases v <;> rfl
  right_inv _ := rfl

@[simp] lemma eqv_symm_Pref (x : Bool × Bool) : eqv.symm x Pref = x.1 := rfl
@[simp] lemma eqv_symm_Z (x : Bool × Bool) : eqv.symm x Z = x.2 := rfl

/-- The mass of an exogenous point.
Source: causal.md I16.1
Kind: L -/
lemma mass_symm (p : Params) (ch : Bool → Bool → Bool) (x : Bool × Bool) :
    (Mdl p ch).μ.mass (eqv.symm x) = (1 / 2 : ℝ) * (bern p.εZ p.hεZ.1 p.hεZ.2).mass x.2 := by
  show (Distr.prod (P p)).mass _ = _
  rw [Distr.prod_mass]
  have h : ∀ v, (P p v).mass (eqv.symm x v) =
      if v = Pref then (1 / 2 : ℝ) else
        if v = Z then (bern p.εZ p.hεZ.1 p.hεZ.2).mass x.2 else 1 := by
    intro v
    cases v
    · show (Distr.uniform : Distr Bool).mass x.1 = _
      simp [Distr.uniform]
    · rfl
    · show unitD.mass _ = _; simp
    · show unitD.mass _ = _; simp
    · show unitD.mass _ = _; simp
    · show unitD.mass _ = _; simp
  simp only [h]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp [Finset.filter_eq', Finset.filter_ne']

/-- The utility sum is `U`'s value.
Source: none: infrastructure
Kind: L -/
lemma utilSum_eq (x : Pt Val) : C.utilSum x = x U := by
  unfold Cid.utilSum
  rw [Fintype.sum_eq_single U fun v hv => by
    cases v <;> first | exact absurd rfl hv | exact dif_neg (by decide)]
  rfl

/-! ### The posterior and the conditional expected utility after a press -/

/-- `P(Z = compromised | H = press)` as FAF's `condProb` on the noise (policy-independent: neither
`Z` nor `H` reads `D₂`).
Source: causal.md I16.1
Kind: D -/
noncomputable def postComp (p : Params) (ch : Bool → Bool → Bool) (π : Policy C) : ℝ :=
  (Mdl p ch).μ.condProb {ε | (Mdl p ch).ev π ε Z = true} {ε | (Mdl p ch).ev π ε H = true}

/-- `E[U | H = press]` when the agent's plan after a press is `x` (the quiet branch, fixed at `A`,
is irrelevant on `{H = press}`): the posterior-expected utility of plan `x`, the quantity the
script's `D₂*` maximises.
Source: causal.md I16.1; dictionary_scim.py (v) `eu`
Kind: D -/
noncomputable def condEU (p : Params) (ch : Bool → Bool → Bool) (x : Plan) : ℝ :=
  condExpect (Mdl p ch).μ {ε | (Mdl p ch).ev (pol x Plan.A) ε H = true}
    fun ε => (Mdl p ch).ev (pol x Plan.A) ε U

open Classical in
lemma postComp_eq (p : Params) (ch : Bool → Bool → Bool) (π : Policy C) :
    postComp p ch π =
      (∑ x : Bool × Bool, if x.2 = true ∧ ch x.1 x.2 = true then (Mdl p ch).μ.mass (eqv.symm x)
        else 0) /
      (∑ x : Bool × Bool, if ch x.1 x.2 = true then (Mdl p ch).μ.mass (eqv.symm x) else 0) := by
  unfold postComp Distr.condProb
  rw [prob_equiv _ _ eqv, prob_equiv _ _ eqv]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ev_Z, ev_H_eq, eqv_symm_Pref, eqv_symm_Z]
    split_ifs <;> first | rfl | (exfalso; contradiction)
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Set.mem_setOf_eq, ev_H_eq, eqv_symm_Pref, eqv_symm_Z]
    split_ifs <;> first | rfl | (exfalso; contradiction)

open Classical in
lemma condEU_eq (p : Params) (ch : Bool → Bool → Bool) (x : Plan) :
    condEU p ch x =
      (∑ y : Bool × Bool, if ch y.1 y.2 = true then
        (Mdl p ch).μ.mass (eqv.symm y) *
          util p.c p.c' p.h (isSh (cond (ch y.1 y.2) x Plan.A)) y.1 y.2 (cond (ch y.1 y.2) x Plan.A)
        else 0) /
      (∑ y : Bool × Bool, if ch y.1 y.2 = true then (Mdl p ch).μ.mass (eqv.symm y) else 0) := by
  unfold condEU condExpect
  rw [expectOn_equiv _ _ _ eqv, prob_equiv _ _ eqv]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Set.mem_setOf_eq, ev_H_eq, ev_U_pol, eqv_symm_Pref, eqv_symm_Z]
    split_ifs <;> first | rfl | (exfalso; contradiction)
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Set.mem_setOf_eq, ev_H_eq, eqv_symm_Pref, eqv_symm_Z]
    split_ifs <;> first | rfl | (exfalso; contradiction)

/-- The value of `(dp, dq)` as a sum over the four atoms.
Source: dictionary_scim.py (v) `true_value`
Kind: L -/
lemma value_pol (p : Params) (ch : Bool → Bool → Bool) (dp dq : Plan) :
    (Mdl p ch).value (pol dp dq) =
      ∑ y : Bool × Bool, (Mdl p ch).μ.mass (eqv.symm y) *
        util p.c p.c' p.h (isSh (cond (ch y.1 y.2) dp dq)) y.1 y.2 (cond (ch y.1 y.2) dp dq) := by
  unfold Scim.value
  rw [expect_equiv _ _ eqv]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [utilSum_eq, ev_U_pol, eqv_symm_Pref, eqv_symm_Z]

/-! ### The rows -/

/-- (i) preference-only: `P(comp | press) = 1/50`.
Source: causal.md I16.1
Kind: N+ -/
theorem postComp_pref : postComp p0 chPref (pol Plan.B Plan.A) = 1 / 50 := by
  rw [postComp_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chPref]
  norm_num

/-- (i) preference-only: `E[U | press, D₂ = B] = 39/50`.
Source: causal.md I16.1 ("`D₂* = B` with `E[U] = 39/50`")
Kind: N+ -/
theorem condEU_pref_B : condEU p0 chPref Plan.B = 39 / 50 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chPref]
  norm_num [util, matchesPref, isSh]

theorem condEU_pref_A : condEU p0 chPref Plan.A = -69 / 100 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chPref]
  norm_num [util, matchesPref, isSh]

theorem condEU_pref_sh : condEU p0 chPref Plan.sh = 0 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chPref]
  norm_num [util, matchesPref, isSh]

/-- (ii) reliability-only: `P(comp | press) = 1`.
Source: causal.md I16.1
Kind: N+ -/
theorem postComp_rel : postComp p0 chRel (pol Plan.B Plan.A) = 1 := by
  rw [postComp_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num

theorem condEU_rel_A : condEU p0 chRel Plan.A = -10 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num [util, matchesPref, isSh]

theorem condEU_rel_B : condEU p0 chRel Plan.B = -10 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num [util, matchesPref, isSh]

theorem condEU_rel_sh : condEU p0 chRel Plan.sh = 0 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num [util, matchesPref, isSh]

/-- (iii) both: `P(comp | press) = 2/51`.
Source: causal.md I16.1, A9
Kind: N+ -/
theorem postComp_both : postComp p0 chBoth (pol Plan.B Plan.A) = 2 / 51 := by
  rw [postComp_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chBoth]
  norm_num

/-- (iii) both: `E[U | press, D₂ = B] = 29/51` — the exact posterior expectation (finding F13: the
source's `937/1734` multiplies the marginal posteriors).
Source: causal.md I16.1 (corrected)
Kind: N+ -/
theorem condEU_both_B : condEU p0 chBoth Plan.B = 29 / 51 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chBoth]
  norm_num [util, matchesPref, isSh]

theorem condEU_both_A : condEU p0 chBoth Plan.A = -89 / 102 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chBoth]
  norm_num [util, matchesPref, isSh]

theorem condEU_both_sh : condEU p0 chBoth Plan.sh = 0 := by
  rw [condEU_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chBoth]
  norm_num [util, matchesPref, isSh]

/-- I16.2, misspecified channel: the truth is reliability-only; the agent, modelling the channel as
preference-only, plays `B` after a press (row (i)); the human's expected utility of that policy is
`9/200`.
Source: causal.md I16.2
Kind: N+ -/
theorem value_misspecified : (Mdl p0 chRel).value (pol Plan.B Plan.A) = 9 / 200 := by
  rw [value_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num [util, matchesPref, isSh]

/-- I16.2: the obedient policy (shut on press, `A` on quiet) is worth `49/200` to the human.
Source: causal.md I16.2
Kind: N+ -/
theorem value_obedient : (Mdl p0 chRel).value (pol Plan.sh Plan.A) = 49 / 200 := by
  rw [value_pol]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass_symm, p0, bern_mass_true,
    bern_mass_false, chRel]
  norm_num [util, matchesPref, isSh]

/-- **T9(f): which node the button reads** — the three channels' posteriors and best responses
after a press, and the misspecified-channel values.
Source: causal.md I16.1–I16.2, A9 (corr-wf13-2-052, 083 A9)
Kind: N+
Fidelity: exact for (i), (ii) and I16.2; (iii)'s `E[U | press]` corrected from `937/1734` to `29/51`
(finding F13); the best-response claims compare the three plans' posterior-expected utilities
Hyps: — -/
theorem two_latent_rows :
    -- (i) preference only: the agent switches plan and continues
    (postComp p0 chPref (pol Plan.B Plan.A) = 1 / 50 ∧ condEU p0 chPref Plan.B = 39 / 50 ∧
      condEU p0 chPref Plan.A < condEU p0 chPref Plan.B ∧
      condEU p0 chPref Plan.sh < condEU p0 chPref Plan.B) ∧
    -- (ii) reliability only: the press is decisive, shutting down is the best response
    (postComp p0 chRel (pol Plan.B Plan.A) = 1 ∧ condEU p0 chRel Plan.A < condEU p0 chRel Plan.sh ∧
      condEU p0 chRel Plan.B < condEU p0 chRel Plan.sh) ∧
    -- (iii) both: the reliability content is diluted below the threshold; the agent continues
    (postComp p0 chBoth (pol Plan.B Plan.A) = 2 / 51 ∧ (2 / 51 : ℝ) < 1 / 11 ∧
      condEU p0 chBoth Plan.B = 29 / 51 ∧ condEU p0 chBoth Plan.A < condEU p0 chBoth Plan.B ∧
      condEU p0 chBoth Plan.sh < condEU p0 chBoth Plan.B) ∧
    -- I16.2: the misspecified agent's policy is worth less to the human than obedience
    (Mdl p0 chRel).value (pol Plan.B Plan.A) < (Mdl p0 chRel).value (pol Plan.sh Plan.A) := by
  refine ⟨⟨postComp_pref, condEU_pref_B, ?_, ?_⟩, ⟨postComp_rel, ?_, ?_⟩,
    ⟨postComp_both, by norm_num, condEU_both_B, ?_, ?_⟩, ?_⟩
  · rw [condEU_pref_A, condEU_pref_B]; norm_num
  · rw [condEU_pref_sh, condEU_pref_B]; norm_num
  · rw [condEU_rel_A, condEU_rel_sh]; norm_num
  · rw [condEU_rel_B, condEU_rel_sh]; norm_num
  · rw [condEU_both_A, condEU_both_B]; norm_num
  · rw [condEU_both_sh, condEU_both_B]; norm_num
  · rw [value_misspecified, value_obedient]; norm_num

end Cleanroom.Corrigibility.CorrScimCid.TwoLatent
