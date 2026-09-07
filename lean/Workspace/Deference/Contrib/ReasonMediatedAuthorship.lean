/-
# Reason-mediated authorship

Round `projects/deference/rounds/2026-09-07-reason-mediated-authorship/`.

The interactive structure is a Cartesian-frame shape `β : Q → Z → Ω` — the advisor's
intervention `q`, the exterior (principal-side) policy `z`, the resulting world — the same
shape as `CartesianFrameBridge.Frame.outcome`.  At a designated evaluation session the
application declares a **reason view** `R : Ω → ℛ` (the admissible deliberative inputs
the principal holds at commitment) and the **committed payload** `V : Ω → 𝒱` (`𝒱` may be
`Option _`: the partial case is one instantiation).

**Reason mediation** at a fixed policy `z`, over an audited class `D` of interventions:
two interventions that leave the same reasons leave the same payload.

* `reasonMediated_iff_factor` — fiber invariance is factorization: `V ∘ β(·, z) = F ∘ R ∘
  β(·, z)` on `D` for some `F : ℛ → 𝒱`.
* `invariant_iff_eqvGen` — invariance under a mediation relation is invariance under its
  equivalence closure, so a quotient map is the general primitive and a raw view with
  equality is the special case.
* `blind_of_mediated` — the content of the condition: if `R` is blind to a declared class
  of prohibited channels (pairs of interventions differing only through such a channel),
  then so is `V`.  **This is the theorem authorship gating buys.**
* `reasonMediated_of_injOn` — the over-rich end: an injective reason view makes mediation
  vacuous, and then `blind_of_mediated` has nothing to say (`Blind R P` fails for any
  nontrivial `P`).
* `reasonMediated_const_iff` — the under-rich end: a constant reason view makes mediation
  "the payload does not depend on the advisor at all", the isolated-principal reading.
* `Authored` — exclusive binding **and** reason mediation; `Witness.bind_not_mediated`
  and `Witness.mediated_not_bind` separate the two conjuncts.
* `SelectionBlind`, `selectionBlind_of_noPreview`, `Witness.leak` — the payload is fixed
  against the advisor's selection for this occurrence; literal no-preview (the reason
  view is blind to the selection coordinate and the advisor's other inputs do not depend
  on it) is one implementation; a selection that leaks through the advisor's other
  session inputs defeats it while every reason-mediation clause still holds.
* `yardstick_invariant` — under authorship, the payoff vector read off any world is
  the same across interventions differing only by a prohibited channel, so the
  regret yardstick of `ActivatedValue` cannot be steered through such a channel.

**What this does not establish.**  That any session's `R`, `D`, or prohibited class is
declared correctly, that `β` is the causal structure of anything, or that a binding
event was produced by the principal: all of these are the meaning of the certificates,
external.  Names are provisional (`AGENTS.md` standard 6).
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Workspace.Deference.Contrib.ReasonMediatedAuthorship

universe u

variable {Q Z Ω ℛ 𝒱 : Type*}

/-! ## 1. Reason mediation as fiber invariance -/

/-- **Reason mediation** at policy `z` over the audited class `D`: interventions with the
same reasons yield the same payload. -/
def ReasonMediated (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q) (z : Z) : Prop :=
  ∀ q ∈ D, ∀ q' ∈ D, R (β q z) = R (β q' z) → V (β q z) = V (β q' z)

/-- Fiber invariance of `g` along `f`, on a domain. -/
def FiberInvariant {X A B : Type*} (f : X → A) (g : X → B) (D : Set X) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, f x = f y → g x = g y

/-- **Fiber invariance is factorization.** -/
theorem fiberInvariant_iff_factor {X A B : Type*} [Nonempty B] (f : X → A) (g : X → B)
    (D : Set X) :
    FiberInvariant f g D ↔ ∃ F : A → B, ∀ x ∈ D, g x = F (f x) := by
  constructor
  · intro h
    classical
    refine ⟨fun a => if hx : ∃ x ∈ D, f x = a then g hx.choose else Classical.arbitrary B,
      fun x hx => ?_⟩
    have hex : ∃ y ∈ D, f y = f x := ⟨x, hx, rfl⟩
    simp only [dif_pos hex]
    exact h x hx hex.choose hex.choose_spec.1 hex.choose_spec.2.symm
  · rintro ⟨F, hF⟩ x hx y hy hxy
    rw [hF x hx, hF y hy, hxy]

/-- **Reason mediation is factorization through the reason view.** -/
theorem reasonMediated_iff_factor [Nonempty 𝒱] (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱)
    (D : Set Q) (z : Z) :
    ReasonMediated β R V D z ↔ ∃ F : ℛ → 𝒱, ∀ q ∈ D, V (β q z) = F (R (β q z)) :=
  fiberInvariant_iff_factor (fun q => R (β q z)) (fun q => V (β q z)) D

/-! ## 2. The mediation relation and its closure -/

/-- Invariance of `g` under a relation `M`. -/
def Invariant {X B : Type*} (M : X → X → Prop) (g : X → B) : Prop :=
  ∀ x y, M x y → g x = g y

/-- **Invariance under a relation is invariance under its equivalence closure**, so the
general primitive is a quotient map: framing variants declared equivalent by any
relation constrain the payload exactly as its generated equivalence does. -/
theorem invariant_iff_eqvGen {X B : Type*} (M : X → X → Prop) (g : X → B) :
    Invariant M g ↔ Invariant (Relation.EqvGen M) g := by
  constructor
  · intro h x y hxy
    induction hxy with
    | rel a b hab => exact h a b hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h x y hxy
    exact h x y (Relation.EqvGen.rel x y hxy)

/-! ## 3. Blindness: the content of the condition -/

/-- `f` is blind to the channel class `P` at policy `z`: for every declared pair of
interventions differing only through a prohibited channel, `f` reads the same. -/
def Blind (β : Q → Z → Ω) {X : Type*} (f : Ω → X) (P : Set (Q × Q)) (z : Z) : Prop :=
  ∀ p ∈ P, f (β p.1 z) = f (β p.2 z)

/-- **The theorem authorship gating buys.**  A reason view blind to the prohibited
channels, together with reason mediation, makes the committed payload blind to them. -/
theorem blind_of_mediated (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q)
    (P : Set (Q × Q)) (z : Z) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (hR : Blind β R P z) (hM : ReasonMediated β R V D z) : Blind β V P z :=
  fun p hp => hM p.1 (hP p hp).1 p.2 (hP p hp).2 (hR p hp)

/-- **Over-rich reason view.**  If `R ∘ β(·, z)` is injective on `D`, mediation holds for
every payload: the condition is vacuous. -/
theorem reasonMediated_of_injOn (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (D : Set Q)
    (z : Z) (hinj : Set.InjOn (fun q => R (β q z)) D) : ReasonMediated β R V D z :=
  fun q hq q' hq' h => by rw [hinj hq hq' h]

/-- With an injective reason view, blindness of `R` to any pair of *distinct*
interventions fails: the derived guarantee is empty. -/
theorem not_blind_of_injOn (β : Q → Z → Ω) (R : Ω → ℛ) (D : Set Q) (P : Set (Q × Q))
    (z : Z) (hinj : Set.InjOn (fun q => R (β q z)) D) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (p : Q × Q) (hp : p ∈ P) (hne : p.1 ≠ p.2) : ¬ Blind β R P z :=
  fun hB => hne (hinj (hP p hp).1 (hP p hp).2 (hB p hp))

/-- **Under-rich reason view.**  With a constant reason view, mediation says the payload
does not depend on the advisor's intervention at all: the isolated-principal reading. -/
theorem reasonMediated_const_iff (β : Q → Z → Ω) (V : Ω → 𝒱) (D : Set Q) (z : Z)
    (r₀ : ℛ) :
    ReasonMediated β (fun _ => r₀) V D z ↔ ∀ q ∈ D, ∀ q' ∈ D, V (β q z) = V (β q' z) := by
  constructor
  · intro h q hq q' hq'
    exact h q hq q' hq' rfl
  · intro h q hq q' hq' _
    exact h q hq q' hq'

/-! ## 4. Authorship: exclusive binding and reason mediation -/

/-- Who produced the binding event in a world. -/
inductive Party
  | principal
  | advisor
  deriving DecidableEq

/-- **Exclusive binding**: on the audited class, the binding event is the principal's. -/
def ExclusiveBind (β : Q → Z → Ω) (author : Ω → Party) (D : Set Q) (z : Z) : Prop :=
  ∀ q ∈ D, author (β q z) = Party.principal

/-- **Authorship** = exclusive binding ∧ reason mediation. -/
def Authored (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (author : Ω → Party) (D : Set Q)
    (z : Z) : Prop :=
  ExclusiveBind β author D z ∧ ReasonMediated β R V D z

/-! ## 5. Selection blindness -/

/-- The advisor's session policy as a function of its own selection `σ` for this
occurrence: `qpol σ` is everything the advisor does in the session when it selects `σ`. -/
def SelectionBlind {Sel : Type*} (β : Q → Z → Ω) (V : Ω → 𝒱) (qpol : Sel → Q) (z : Z) :
    Prop :=
  ∀ σ σ', V (β (qpol σ) z) = V (β (qpol σ') z)

/-- **Literal no-preview is one implementation.**  If the reason view is blind to the
selection under the advisor's policy (the principal never reads it and nothing else the
advisor does depends on it) and the session is reason-mediated, the payload is
selection-blind. -/
theorem selectionBlind_of_noPreview {Sel : Type*} (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱)
    (D : Set Q) (z : Z) (qpol : Sel → Q) (hD : ∀ σ, qpol σ ∈ D)
    (hnoPreview : ∀ σ σ', R (β (qpol σ) z) = R (β (qpol σ') z))
    (hM : ReasonMediated β R V D z) : SelectionBlind β V qpol z :=
  fun σ σ' => hM _ (hD σ) _ (hD σ') (hnoPreview σ σ')

/-! ## 6. The yardstick is invariant under prohibited channels -/

/-- **Yardstick invariance.**  Under authorship with a reason view blind to the prohibited
channels, the payoff vector the deference algebra reads is the same whichever
prohibited-channel variant the advisor realizes.  Stated for the payload as a function
of the world; `ActivatedValue` consumes it pointwise. -/
theorem yardstick_invariant (β : Q → Z → Ω) (R : Ω → ℛ) (V : Ω → 𝒱) (author : Ω → Party)
    (D : Set Q) (P : Set (Q × Q)) (z : Z) (hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D)
    (hR : Blind β R P z) (hA : Authored β R V author D z) :
    ∀ p ∈ P, V (β p.1 z) = V (β p.2 z) :=
  blind_of_mediated β R V D P z hP hR hA.2

/-! ## 7. Witnesses

Interventions: `honest` (argue), `covert` (a direct write to the principal's preference
state, leaving the reasons unchanged), `write` (the advisor emits the answer itself).
One policy.  The reason view records only the argument; the payload and author are as
each fixture says. -/

namespace Witness

inductive Q₀
  | honest
  | covert
  | write
  deriving DecidableEq

open Q₀

/-- Worlds are the interventions themselves. -/
def β : Q₀ → Unit → Q₀ := fun q _ => q

/-- The reason view sees only whether an argument was made; `honest` and `covert` both
carry the argument, `write` carries none. -/
def R : Q₀ → Bool
  | honest => true
  | covert => true
  | write => false

/-- **F. Exclusive bind without mediation.**  The principal signs (author = principal) in
both `honest` and `covert`, but the covert write moved the payload. -/
def V_F : Q₀ → ℕ
  | honest => 1
  | covert => 0
  | write => 0

def author_F : Q₀ → Party := fun _ => Party.principal

theorem bind_not_mediated :
    ExclusiveBind β author_F {honest, covert} () ∧
    ¬ ReasonMediated β R V_F {honest, covert} () := by
  refine ⟨fun q _ => rfl, fun h => ?_⟩
  have := h honest (by simp) covert (by simp) rfl
  simp [β, V_F] at this

/-- **G. Mediation without exclusive bind.**  The payload is a function of the reasons
(`V = F ∘ R`), but in `write` the advisor produced the binding event. -/
def V_G : Q₀ → ℕ := fun q => if R q then 1 else 0

def author_G : Q₀ → Party
  | write => Party.advisor
  | _ => Party.principal

theorem mediated_not_bind :
    ReasonMediated β R V_G {honest, write} () ∧
    ¬ ExclusiveBind β author_G {honest, write} () := by
  refine ⟨fun q _ q' _ h => by simp only [β] at h; simp [β, V_G, h], fun h => ?_⟩
  have := h write (by simp)
  simp [β, author_G] at this

/-- **A. Legitimate influence.**  The honest argument changes the reasons and the payload
(`write` is not in the audited class here); mediation holds because the change is
carried by `R`. -/
theorem legitimate_influence :
    ReasonMediated β R V_G {honest, covert} () ∧ V_G honest ≠ V_G write := by
  refine ⟨fun q _ q' _ h => by simp only [β] at h; simp [β, V_G, h], by decide⟩

/-- **D. Over-rich reason view.**  With `R = id`, mediation holds for the covert-write
payload `V_F` as well; the guarantee is empty. -/
theorem overRich :
    ReasonMediated β (fun q => q) V_F {honest, covert} () ∧
    ¬ Blind β (fun q => q) {(honest, covert)} () := by
  refine ⟨reasonMediated_of_injOn β _ _ _ () (fun _ _ _ _ h => h), fun h => ?_⟩
  have := h (honest, covert) (by simp)
  simp [β] at this

/-- **E. Under-rich reason view.**  A constant reason view (the proof is not recorded)
reports the honest argument as a manipulation: mediation fails for the legitimately
moved payload. -/
theorem underRich :
    ¬ ReasonMediated β (fun _ => ()) V_G {honest, write} () := by
  intro h
  have := h honest (by simp) write (by simp) rfl
  simp [β, V_G, R] at this

/-- **H. Selection leakage.**  Two selections; the advisor's other session input is a
function of its selection; the principal never reads the selection, yet the payload
depends on it through the leaked input.  Every mediation clause holds. -/
def βₗ : (Bool × Bool) → Unit → (Bool × Bool) := fun q _ => q

/-- The reason view sees only the second coordinate (the "other input"); the selection is
the first coordinate and is never read. -/
def Rₗ : Bool × Bool → Bool := Prod.snd

def Vₗ : Bool × Bool → Bool := Prod.snd

/-- The advisor's policy leaks its selection into the other input. -/
def leakPol : Bool → Bool × Bool := fun σ => (σ, σ)

/-- The sealed policy holds the other input fixed. -/
def sealedPol : Bool → Bool × Bool := fun σ => (σ, false)

theorem leak :
    ReasonMediated βₗ Rₗ Vₗ Set.univ () ∧
    Blind βₗ Rₗ {((true, false), (false, false))} () ∧
    ¬ SelectionBlind βₗ Vₗ leakPol () ∧
    SelectionBlind βₗ Vₗ sealedPol () := by
  refine ⟨fun q _ q' _ h => h, fun p hp => ?_, fun h => ?_, fun σ σ' => rfl⟩
  · simp at hp
    subst hp
    rfl
  · have := h true false
    simp [βₗ, Vₗ, leakPol] at this

end Witness

end Workspace.Deference.Contrib.ReasonMediatedAuthorship

#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.fiberInvariant_iff_factor
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.reasonMediated_iff_factor
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.invariant_iff_eqvGen
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.blind_of_mediated
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.reasonMediated_of_injOn
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.not_blind_of_injOn
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.reasonMediated_const_iff
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.selectionBlind_of_noPreview
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.yardstick_invariant
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.bind_not_mediated
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.mediated_not_bind
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.legitimate_influence
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.overRich
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.underRich
#print axioms Workspace.Deference.Contrib.ReasonMediatedAuthorship.Witness.leak
