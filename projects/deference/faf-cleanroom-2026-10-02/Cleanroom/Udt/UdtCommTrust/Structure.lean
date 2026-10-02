import Cleanroom.Udt.UdtCommTrust.Factor
import Cleanroom.Udt.UdtCommTrust.Prob

/-!
# `Cleanroom.Udt.UdtCommTrust.Structure`: the abstract decision structure

Work package `udt-comm-trust`, targets T3 (the structure and the determination lemmas) and
T4(a) (the policy types and the UDT rule as a predicate). Sources: [[communication-trust-translated]]
lines 276–392; the original `references/communication&trust.md` lines 318–361 (dynamics, `Π*` as
an assumption at line ~345).

## Representation of record (mandate §3)

* One finite `Ω` with `μ : FinDist Ω` and **`Ω` the support** (`pos`). This is the package-wide
  modelling substitution `(c)`: restricting a finite space to its support loses nothing the paper
  states (every conditioning event is empty or of positive mass), and it makes "exists `ω`" and
  "positive probability" the same thing (udt-rep-009).
* Random variables are functions; value types are parameters. ASCII names, because the paper's
  diacritics are not Lean identifier characters: `oI` = `Ȯ` (internal observation), `oE` = `Ö`
  (external observation), `aI` = `Ȧ`, `aE` = `Ä`, `dI dE dB` = `D_I D_E D_B`, `oH` = `Ô` (semantic
  observation), `oC` = `Ǒ` (side channel), `polS` = `Π*` (chosen), `polE` = `Π̈` (external), `polD` =
  `Π†` (effective).
* The paper's compound variables are **defined as products**: `I := (Ȧ, D_I)`, `E := (Ä, D_E)`,
  `O := (Ȯ, Ö)`, `A := (Ȧ, Ä)`, `B := (O, D_B)`, `D_{I,B} := (D_I, D_B)`. Clause 1 of "factors as"
  (`X = (Y, Z)` as random variables) is then definitional for the four dynamics assumptions; the
  one place it is not — `(I, B)` factors as `(Ö, D_{I,B})` — carries the field `IB_det` for it.
* `Π*` is a field: the paper's assumption ("I assume that a subvariable representing the chosen
  policy exists", original line ~345). `Π†` and `Π̈` are derived, never fields.
* Every restriction map is a named `def` with an explicit off-range junk value.
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

variable {Ω : Type}

/-- The projection of `Y` along `X`, made explicit: on `v = X ω` it returns `Y ω`; off the range of
`X` it returns `Y ω₀` (the junk value). `projOf_spec` is its only property.
Source: [[communication-trust-translated]] lines 210–213 (the projection `[[·]]_Y`)
Kind: D
Fidelity: exact on `Set.range X`; junk `Y ω₀` off it
Hyps: n/a -/
noncomputable def projOf {V W : Type} (X : Ω → V) (Y : Ω → W) (ω₀ : Ω) (v : V) : W :=
  open Classical in if h : ∃ ω, X ω = v then Y h.choose else Y ω₀

/-- Supporting lemma `projOf_spec`: on the range the projection recovers `Y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOf_spec {V W : Type} {X : Ω → V} {Y : Ω → W} (h : IsSubvariable X Y) (ω₀ ω : Ω) :
    projOf X Y ω₀ (X ω) = Y ω := by
  have hex : ∃ ω', X ω' = X ω := ⟨ω, rfl⟩
  unfold projOf
  rw [dif_pos hex]
  exact h _ _ hex.choose_spec

variable (Ω : Type) (OI OE AI AE DI DE DB OH OC : Type)

/-- **The abstract decision structure** (the paper's fourteen variables and its assumptions), over
a finite support. Fields: the measure `μ` with full support `pos`; the nine primitive variables
`oI oE aI aE dI dE dB oH oC`; the chosen policy `polS` (a field: the paper's assumption); the
utility `U : Ω → [0,1]`; the subvariable clauses (`Ȯ ⊑ I`, `Ö ⊑ E`, `Ȧ ⊑ B`, `Ä ⊑ B`, `Ô ⊑ Ȯ`,
`Ǒ ⊑ Ȯ`; `Ȯ, Ö ⊑ B`, `Ȧ ⊑ I`, `Ä ⊑ E` are definitional); the two common-information equations as
fields (udt-rep-012: "field, not theorem"); the six factorization assumptions (internal,
environment, boundary, agent-dynamic, `O`, `A`), with `IB_det` carrying clause 1 of the
agent-dynamic constraint (`(I, B)` is a function of `(Ö, D_{I,B})`; the converse is definitional).
Source: [[communication-trust-translated]] lines 276–380 (udt-rep-012, 2-001); original lines 318–361
Kind: D
Fidelity: variant: `Ω` taken to be the support (mandate §3 (c)); compound variables defined as products; `Π*` a field
Hyps: n/a -/
structure AbstractDS [Fintype Ω] where
  /-- The agent's subjective prior. -/
  μ : FinDist Ω
  /-- `Ω` is the support. -/
  pos : ∀ ω, 0 < μ.w ω
  /-- `Ȯ`, the internal observation. -/
  oI : Ω → OI
  /-- `Ö`, the external observation. -/
  oE : Ω → OE
  /-- `Ȧ`, the internal action. -/
  aI : Ω → AI
  /-- `Ä`, the external action. -/
  aE : Ω → AE
  /-- `D_I`, the internal dynamic. -/
  dI : Ω → DI
  /-- `D_E`, the environment dynamic. -/
  dE : Ω → DE
  /-- `D_B`, the boundary dynamic. -/
  dB : Ω → DB
  /-- `Ô`, the semantic observation. -/
  oH : Ω → OH
  /-- `Ǒ`, the side channel. -/
  oC : Ω → OC
  /-- `Π*`, the chosen policy (the paper's assumption, original line ~345). -/
  polS : Ω → Policy (OI × OE) (AI × AE)
  /-- The utility. -/
  U : Ω → ℝ
  /-- `U` takes values in `[0, 1]`. -/
  U_mem : ∀ ω, U ω ∈ Set.Icc (0 : ℝ) 1
  /-- `Ȯ ⊑ I = (Ȧ, D_I)`. -/
  oI_I : IsSubvariable (fun ω => (aI ω, dI ω)) oI
  /-- `Ö ⊑ E = (Ä, D_E)`. -/
  oE_E : IsSubvariable (fun ω => (aE ω, dE ω)) oE
  /-- `Ȧ ⊑ B = ((Ȯ, Ö), D_B)`. -/
  aI_B : IsSubvariable (fun ω => ((oI ω, oE ω), dB ω)) aI
  /-- `Ä ⊑ B`. -/
  aE_B : IsSubvariable (fun ω => ((oI ω, oE ω), dB ω)) aE
  /-- `Ô ⊑ Ȯ`. -/
  oH_oI : IsSubvariable oI oH
  /-- `Ǒ ⊑ Ȯ`. -/
  oC_oI : IsSubvariable oI oC
  /-- `I ∨ B = (Ȯ, Ȧ)`. -/
  IB_common : CommonInfo (fun ω => (aI ω, dI ω)) (fun ω => ((oI ω, oE ω), dB ω))
    (fun ω => (oI ω, aI ω))
  /-- `B ∨ E = (Ö, Ä)`. -/
  BE_common : CommonInfo (fun ω => ((oI ω, oE ω), dB ω)) (fun ω => (aE ω, dE ω))
    (fun ω => (oE ω, aE ω))
  /-- Internal dynamic: `I` factors as `(Ȧ, D_I)`. -/
  I_fac : FactorsAs aI dI
  /-- Environment dynamic: `E` factors as `(Ä, D_E)`. -/
  E_fac : FactorsAs aE dE
  /-- Boundary dynamic: `B` factors as `(O, D_B)`. -/
  B_fac : FactorsAs (fun ω => (oI ω, oE ω)) dB
  /-- Agent dynamic constraint, clause 2: `Ö` and `D_{I,B}` are independent in support. -/
  IB_fac : FactorsAs oE (fun ω => (dI ω, dB ω))
  /-- Agent dynamic constraint, clause 1: `(I, B)` is a function of `(Ö, D_{I,B})`. -/
  IB_det : IsSubvariable (fun ω => (oE ω, (dI ω, dB ω)))
    (fun ω => ((aI ω, dI ω), ((oI ω, oE ω), dB ω)))
  /-- `O` factors as `(Ȯ, Ö)`. -/
  O_fac : FactorsAs oI oE
  /-- `A` factors as `(Ȧ, Ä)`. -/
  A_fac : FactorsAs aI aE

namespace AbstractDS

variable {Ω OI OE AI AE DI DE DB OH OC}
variable [Fintype Ω]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- `I = (Ȧ, D_I)`, the interior.
Source: [[communication-trust-translated]] line 343 (internal dynamic)
Kind: D
Fidelity: exact (definitional product)
Hyps: n/a -/
def I (ω : Ω) : AI × DI := (S.aI ω, S.dI ω)

/-- `O = (Ȯ, Ö)`, the full observation.
Source: [[communication-trust-translated]] line 306
Kind: D
Fidelity: exact
Hyps: n/a -/
def O (ω : Ω) : OI × OE := (S.oI ω, S.oE ω)

/-- `A = (Ȧ, Ä)`, the full action.
Source: [[communication-trust-translated]] line 307
Kind: D
Fidelity: exact
Hyps: n/a -/
def A (ω : Ω) : AI × AE := (S.aI ω, S.aE ω)

/-- `B = (O, D_B)`, the boundary.
Source: [[communication-trust-translated]] line 355 (boundary dynamic)
Kind: D
Fidelity: exact
Hyps: n/a -/
def B (ω : Ω) : (OI × OE) × DB := (S.O ω, S.dB ω)

/-- `E = (Ä, D_E)`, the external environment.
Source: [[communication-trust-translated]] line 349 (environment dynamic)
Kind: D
Fidelity: exact
Hyps: n/a -/
def E (ω : Ω) : AE × DE := (S.aE ω, S.dE ω)

/-- `D_{I,B} = (D_I, D_B)`.
Source: [[communication-trust-translated]] line 361
Kind: D
Fidelity: exact
Hyps: n/a -/
def DIB (ω : Ω) : DI × DB := (S.dI ω, S.dB ω)

/-- `(I, B)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def IB (ω : Ω) : (AI × DI) × ((OI × OE) × DB) := (S.I ω, S.B ω)

include S in
/-- Supporting lemma `nonempty`: the support is non-empty (the weights sum to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem nonempty : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := S.μ.sum_one
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

/-- A fixed world, the junk value of every projection.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def w₀ : Ω := S.nonempty.some

/-- Supporting lemma `U_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_nonneg (ω : Ω) : 0 ≤ S.U ω := (S.U_mem ω).1

/-- `[[·]]_Ä` from `B`. Junk off `Set.range B`: `Ä w₀`.
Source: [[communication-trust-translated]] line 376 (`[[ρ(ö)]]_Ä`)
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def projAE : (OI × OE) × DB → AE := projOf S.B S.aE S.w₀

/-- `[[·]]_Ȧ` from `B`.
Source: [[communication-trust-translated]] line 368 (`[[β]]_A`)
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def projAI : (OI × OE) × DB → AI := projOf S.B S.aI S.w₀

/-- `[[·]]_Ö` from `E`.
Source: none: infrastructure (T5(b))
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def projOE : AE × DE → OE := projOf S.E S.oE S.w₀

/-- **The restriction map `ρ_{d_{I,B}} : Ö → (I, B)`** of the agent dynamic constraint. Off the
range of `(Ö, D_{I,B})` it returns `(I, B)` at `w₀`; `rho_spec` is the only property used.
Source: [[communication-trust-translated]] line 363
Kind: D
Fidelity: exact on the range
Hyps: n/a -/
noncomputable def rho (d : DI × DB) (e : OE) : (AI × DI) × ((OI × OE) × DB) :=
  projOf (fun ω => (S.oE ω, S.DIB ω)) S.IB S.w₀ (e, d)

/-- Supporting lemma `rho_spec`: `ρ_{D_{I,B}(ω)}(Ö(ω)) = (I, B)(ω)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rho_spec (ω : Ω) : S.rho (S.DIB ω) (S.oE ω) = S.IB ω :=
  projOf_spec S.IB_det S.w₀ ω

/-- **`[[d]]_Π̈`**: the external policy encoded by a value of `D_{I,B}`:
`ö ↦ [[ρ_d(ö)]]_Ä`.
Source: [[communication-trust-translated]] line 376
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def polOf (d : DI × DB) : OE → AE := fun e => S.projAE (S.rho d e).2

/-- **`Π̈`, the external policy** as a random variable: `Π̈(ω) = [[D_{I,B}(ω)]]_Π̈`. Derived, not
a field (T4(a)).
Source: [[communication-trust-translated]] lines 374–378
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def polE (ω : Ω) : OE → AE := S.polOf (S.DIB ω)

/-- `[[·]]_A` from `B`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def projA (b : (OI × OE) × DB) : AI × AE := (S.projAI b, S.projAE b)

/-- **`Π†`, the effective policy**: `Π†(ω) = [[β_{D_B(ω)}]]_A = o ↦ [[(o, D_B(ω))]]_A`. Derived,
not a field (T4(a)); `β_{d_B}(o) = (o, d_B)` is definitional.
Source: [[communication-trust-translated]] lines 366–368
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def polD (ω : Ω) : Policy (OI × OE) (AI × AE) := fun o => S.projA (o, S.dB ω)

/-- Supporting lemma `projAE_B`: `[[B(ω)]]_Ä = Ä(ω)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projAE_B (ω : Ω) : S.projAE (S.B ω) = S.aE ω := projOf_spec S.aE_B S.w₀ ω

/-- Supporting lemma `projAI_B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projAI_B (ω : Ω) : S.projAI (S.B ω) = S.aI ω := projOf_spec S.aI_B S.w₀ ω

/-- Supporting lemma `projOE_E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOE_E (ω : Ω) : S.projOE (S.E ω) = S.oE ω := projOf_spec S.oE_E S.w₀ ω

/-- **`Π̈` realizes `Ä` at the realized observation**: `Π̈(ω)(Ö(ω)) = Ä(ω)`.
Source: [[communication-trust-translated]] line 376
Kind: L
Fidelity: exact
Hyps: none -/
theorem polE_apply_oE (ω : Ω) : S.polE ω (S.oE ω) = S.aE ω := by
  unfold polE polOf
  rw [rho_spec]
  exact S.projAE_B ω

/-- **`Π†` realizes `A` at the realized observation**: `Π†(ω)(O(ω)) = A(ω)`.
Source: [[communication-trust-translated]] line 368
Kind: L
Fidelity: exact
Hyps: none -/
theorem polD_apply_O (ω : Ω) : S.polD ω (S.O ω) = S.A ω := by
  unfold polD projA
  show (S.projAI (S.B ω), S.projAE (S.B ω)) = S.A ω
  rw [projAI_B, projAE_B]
  rfl

/-- **Determination lemma (T3): `Π̈` is a function of `D_{I,B}`** — udt-rep-2-001's "one true
sentence" ([[ct-diffractor-comparison]] line 69). By construction.
Source: [[communication-trust-translated]] line 378; [[ct-diffractor-comparison]] line 69
Kind: L
Fidelity: exact
Hyps: none -/
theorem polE_sub : IsSubvariable S.DIB S.polE := IsSubvariable.of_comp S.DIB S.polOf

/-- **Determination lemma (T3): `Π†` is a function of `D_B`.** By construction.
Source: [[communication-trust-translated]] line 370
Kind: L
Fidelity: exact
Hyps: none -/
theorem polD_sub : IsSubvariable S.dB S.polD :=
  IsSubvariable.of_comp S.dB fun d => fun o => S.projA (o, d)

/-- **Determination lemma (T3): `Ȯ` is a function of `(Ö, D_{I,B})`** — from the agent-dynamic
constraint (`IB_det`) and `Ȯ ⊑ B`.
Source: [[communication-trust-translated]] line 363
Kind: L
Fidelity: exact
Hyps: none -/
theorem oI_sub_oE_DIB : IsSubvariable (fun ω => (S.oE ω, S.DIB ω)) S.oI :=
  S.IB_det.comp fun ib => ib.2.1.1

/-- Supporting lemma `polE_eq_polOf_DIB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = S.polOf (S.DIB ω) := rfl

/-- **`Π̈` read off another world with the same dynamics**: if `D_{I,B}(ω) = D_{I,B}(ω')` then
`Π̈(ω)(Ö(ω')) = Ä(ω')`. This is how `Π̈` is computed on witnesses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_apply_of_DIB_eq {ω ω' : Ω} (h : S.DIB ω = S.DIB ω') : S.polE ω (S.oE ω') = S.aE ω' := by
  rw [polE_eq, h, ← polE_eq]
  exact S.polE_apply_oE ω'

/-- **A computable description of `Π̈`**: if `f` agrees with `Ä` at each world's own observation,
depends on the world only through `D_{I,B}`, and every observation is realized alongside every
value of `D_{I,B}`, then `Π̈ = f`. All three hypotheses are decidable on finite carriers; this is
the witnesses' route past the `Classical.choose` in `rho`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq_of (f : Ω → OE → AE) (hf : ∀ ω, f ω (S.oE ω) = S.aE ω)
    (hD : ∀ ω ω', S.DIB ω = S.DIB ω' → f ω = f ω')
    (hs : ∀ ω e, ∃ ω', S.DIB ω' = S.DIB ω ∧ S.oE ω' = e) (ω : Ω) : S.polE ω = f ω := by
  funext e
  obtain ⟨ω', h1, h2⟩ := hs ω e
  rw [← h2, S.polE_apply_of_DIB_eq h1.symm, ← hf ω', hD ω ω' h1.symm]

/-! ### The UDT rule (T4(a)) -/

variable [DecidableEq AI] [DecidableEq AE]

/-- **The event `{Π*(ȯ, ö) = a}`**: the worlds whose chosen policy outputs `a` at input `(ȯ, ö)`.
Source: [[communication-trust-translated]] lines 430–432; original line ~350 ("equations denote the set of worlds")
Kind: D
Fidelity: exact
Hyps: n/a -/
def evS (o : OI) (e : OE) (a : AI × AE) : Finset Ω := event fun ω => S.polS ω (o, e) = a

/-- Supporting lemma `mem_evS`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evS {o : OI} {e : OE} {a : AI × AE} {ω : Ω} :
    ω ∈ S.evS o e a ↔ S.polS ω (o, e) = a := by
  simp [evS]

/-- **The UDT score of an action at an input**: `E[U ∣ Π*(ȯ, ö) = a]` with the paper's junk `−1`
on the empty event.
Source: [[communication-trust-translated]] lines 430–432
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def score (o : OI) (e : OE) (a : AI × AE) : ℝ :=
  condExpJunk S.μ.w S.U (S.evS o e a) (-1)

/-- **The UDT rule at one world and input**: the chosen policy's output is an argmax of the score
(over all actions; an unattained action scores `−1` and can never be an argmax, so this equals
the paper's argmax over `range A_ö`).
Source: [[communication-trust-translated]] lines 430–432
Kind: D
Fidelity: exact (pointwise reading, ATTRIBUTION-UNVETTED: the paper's display treats `Π*(ȯ_ö, ö)` as *the* argmax while `Π*` is a random variable; read as "every chosen policy in the support is an argmax at every input under the prior over chosen policies", udt-rep-090's fixed-point equation)
Hyps: n/a -/
def UdtRuleAt (ω : Ω) (o : OI) (e : OE) : Prop := IsArgmax (S.score o e) (S.polS ω (o, e))

/-- **The UDT rule** (a predicate, never a function): `UdtRuleAt` at every world and input.
Source: [[communication-trust-translated]] lines 430–432 (udt-rep-013)
Kind: D
Fidelity: exact (pointwise reading, ATTRIBUTION-UNVETTED, see `UdtRuleAt`)
Hyps: n/a -/
def UdtRule : Prop := ∀ ω o e, S.UdtRuleAt ω o e

/-- Supporting lemma `evS_self_nonempty`: the event of the action actually chosen at `(ȯ, ö)` in
`ω` contains `ω`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_self_nonempty (ω : Ω) (o : OI) (e : OE) : (S.evS o e (S.polS ω (o, e))).Nonempty :=
  ⟨ω, by simp⟩

/-- **An unattained action never wins**: if `{Π*(ȯ, ö) = a} = ∅` then `score a = −1` is strictly
below the score of any attained action.
Source: mandate §3 (`junk_lt_of_nonempty`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem score_lt_of_empty {o : OI} {e : OE} {a a' : AI × AE} (ha : S.evS o e a = ∅)
    (ha' : (S.evS o e a').Nonempty) : S.score o e a < S.score o e a' := by
  unfold score
  rw [ha, condExpJunk_of_empty]
  exact junk_lt_of_nonempty S.pos S.U_nonneg ha'

/-- **An argmax is attained**: under any structure, an `IsArgmax` of the score at `(ȯ, ö)` has a
non-empty event.
Source: mandate T11(b) (the events `{Π*(ȯ,ö) = a}` cover `Ω`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem evS_nonempty_of_isArgmax {o : OI} {e : OE} {a : AI × AE}
    (h : IsArgmax (S.score o e) a) : (S.evS o e a).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have := h (S.polS S.w₀ (o, e))
  exact absurd this (not_le.2 (S.score_lt_of_empty hne (S.evS_self_nonempty S.w₀ o e)))

end AbstractDS

end Cleanroom.Udt.UdtCommTrust
