import Cleanroom.Udt.UdtPaperTiling.Structure
import Cleanroom.Bli.UdtBliCore.Basic
import Cleanroom.Bli.UdtBliCore.Bridges

/-!
# `udt-paper-tiling` · Rules: the paper layer, the chosen-point value, UDT 1.0 / 1.1 (T2)

**The reading of record.** The paper's `π*` is the *chosen* policy and `eff(π*)` is what the world
sees. Over `udt-bli-core`'s prior, `pp` is the *effective* policy (the world's policy points); the
chosen policy is a further coordinate `chosen : Ω → Policy 𝒟 Act` with `pp = eff ∘ chosen`
(`PaperLayer`). A paper layer is a `ProcLayer` whose procedures are the policies themselves
(`PaperLayer.toProcLayer`), so the run's one fairness predicate `PolicyFair` applies to it
unchanged. The paper's `E_p(u | π* = ⌜π⌝)` is `procEU π` of that layer and its
`E_p(u | π*(o) = a)` is `chosenEU o a := 𝔼_μ[U | chosen · o = a]`. On the trivial layer
(`chosen = pp`, `eff = id`) `chosenEU` is `udt-bli-core`'s `EU` (`chosenEU_trivial`).

**The circularity of `π*`** (`main.tex:127`, footnote "quines") is resolved by taking `πstar` as a
distinguished policy — the agent's actual choice — and `chosen` as the prior's *uncertainty*
about it, tied to `πstar` only by the assumptions that say so (Knowledge of Decision Procedure,
`Vingean.lean`). `IsUDT10` is the fixed-point condition on `πstar` (each `πstar o` maximizes the
chosen-point value over the available actions of positive point mass); `IsUDT11` is prior
optimality among well-typed policies of positive mass. Argmax is a predicate, never a function.

**Junk.** `condExp` has the junk value `0` at a null event (inherited from `udt-bli-core`); every
headline names the positivity it needs. The null-event lemmas `condExp_congr_null`
(replace a conditioning event by an a.s.-equal one) and `condExp_and_eq_of_ae` (drop a
probability-one conjunct) are the only tools that move conditioning events; nothing divides.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-! ## Null-event lemmas (generic finite probability) -/

section NullEvents

variable {Ω : Type} [Fintype Ω]

/-- A null complement means every world of positive weight satisfies `G`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_not_eq_zero_iff (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (G : Ω → Prop) [DecidablePred G] :
    massOf μ (fun ω => ¬ G ω) = 0 ↔ ∀ ω, 0 < μ ω → G ω := by
  rw [massOf_eq_zero_iff μ hμ]
  constructor
  · intro h ω hpos
    by_contra hG
    exact absurd (h ω hG) (ne_of_gt hpos)
  · intro h ω hG
    by_contra hne
    exact hG (h ω (lt_of_le_of_ne (hμ ω) (Ne.symm hne)))

/-- `μ(E) + μ(¬E)` is the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_add_massOf_not (μ : Ω → ℚ) (E : Ω → Prop) [DecidablePred E] :
    massOf μ E + massOf μ (fun ω => ¬ E ω) = ∑ ω, μ ω := by
  unfold massOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

/-- Under a probability (total mass one), `μ(E) = 1 ↔ μ(¬E) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_eq_one_iff (μ : Ω → ℚ) (h1 : ∑ ω, μ ω = 1) (E : Ω → Prop) [DecidablePred E] :
    massOf μ E = 1 ↔ massOf μ (fun ω => ¬ E ω) = 0 := by
  have := massOf_add_massOf_not μ E
  rw [h1] at this
  constructor <;> intro h <;> linarith

/-- **Masses of a.s.-equal events agree**: if `¬(E ↔ F)` is null then `μ(E) = μ(F)`.
Source: none: infrastructure (mandate §3, the null-event lemmas)
Kind: L
Fidelity: n/a -/
lemma massOf_congr_null (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : massOf μ (fun ω => ¬ (E ω ↔ F ω)) = 0) : massOf μ E = massOf μ F := by
  rw [massOf_not_eq_zero_iff μ hμ] at h
  unfold massOf
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hpos : 0 < μ ω
  · have := h ω hpos
    by_cases hE : E ω
    · simp [hE, this.mp hE]
    · have hF : ¬ F ω := fun hF => hE (this.mpr hF)
      simp [hE, hF]
  · have hz : μ ω = 0 := le_antisymm (not_lt.mp hpos) (hμ ω)
    simp [hz]

/-- **Integrals over a.s.-equal events agree.**
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma integralOf_congr_null (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : massOf μ (fun ω => ¬ (E ω ↔ F ω)) = 0) :
    integralOf μ f E = integralOf μ f F := by
  rw [massOf_not_eq_zero_iff μ hμ] at h
  unfold integralOf
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hpos : 0 < μ ω
  · have := h ω hpos
    by_cases hE : E ω
    · simp [hE, this.mp hE]
    · have hF : ¬ F ω := fun hF => hE (this.mpr hF)
      simp [hE, hF]
  · have hz : μ ω = 0 := le_antisymm (not_lt.mp hpos) (hμ ω)
    simp [hz]

/-- **Conditional expectations on a.s.-equal events agree** — exact, with no positivity: both the
numerator and the denominator agree (Theorem 3's "replace an a.s.-equal event inside a
conditional").
Source: none: infrastructure (mandate §3)
Kind: L
Fidelity: n/a -/
theorem condExp_congr_null (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : massOf μ (fun ω => ¬ (E ω ↔ F ω)) = 0) :
    condExp μ f E = condExp μ f F := by
  unfold condExp
  rw [massOf_congr_null μ hμ h, integralOf_congr_null μ f hμ h]

/-- A probability-one conjunct can be dropped from an event (a.s.-equality of `E ∧ G` and `E`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_not_iff_and_eq_zero (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E G : Ω → Prop)
    [DecidablePred E] [DecidablePred G] (h : massOf μ (fun ω => ¬ G ω) = 0) :
    massOf μ (fun ω => ¬ ((E ω ∧ G ω) ↔ E ω)) = 0 := by
  rw [massOf_not_eq_zero_iff μ hμ] at h ⊢
  intro ω hpos
  have := h ω hpos
  constructor
  · exact And.left
  · exact fun hE => ⟨hE, this⟩

/-- **Dropping a probability-one conjunct from a mass**: `μ(¬G) = 0 → μ(E ∧ G) = μ(E)`.
Source: none: infrastructure (mandate §3)
Kind: L
Fidelity: n/a -/
theorem massOf_and_eq_of_ae (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E G : Ω → Prop) [DecidablePred E]
    [DecidablePred G] (h : massOf μ (fun ω => ¬ G ω) = 0) :
    massOf μ (fun ω => E ω ∧ G ω) = massOf μ E :=
  massOf_congr_null μ hμ (massOf_not_iff_and_eq_zero μ hμ E G h)

/-- **Dropping a probability-one conjunct from a conditional expectation** (Theorem 3's
"by Knowledge of Decision Procedure the argmax condition can be dropped").
Source: none: infrastructure (mandate §3)
Kind: L
Fidelity: n/a -/
theorem condExp_and_eq_of_ae (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E G : Ω → Prop) [DecidablePred E]
    [DecidablePred G] (h : massOf μ (fun ω => ¬ G ω) = 0) :
    condExp μ f (fun ω => E ω ∧ G ω) = condExp μ f E :=
  condExp_congr_null μ f hμ (massOf_not_iff_and_eq_zero μ hμ E G h)

/-- Monotonicity of mass under inclusion of events.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_mono (μ : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : ∀ ω, E ω → F ω) : massOf μ E ≤ massOf μ F := by
  unfold massOf
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · simp [hE, h ω hE]
  · simp only [hE, if_false]
    split_ifs
    · exact hμ ω
    · exact le_rfl

/-- The conditional expectation on an event where `f` is bounded by `c` is at most `c`
(positive event, nonnegative weights).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_le_of_le (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (hpos : 0 < massOf μ E) {c : ℚ} (hc : ∀ ω, E ω → f ω ≤ c) : condExp μ f E ≤ c := by
  unfold condExp
  rw [div_le_iff₀ hpos]
  have := integralOf_le_integralOf μ f (fun _ => c) hμ E hc
  rw [integralOf_const] at this
  linarith

/-- The conditional expectation on an event where `f` is at least `c` is at least `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_condExp_of_le (μ f : Ω → ℚ) (hμ : ∀ ω, 0 ≤ μ ω) (E : Ω → Prop) [DecidablePred E]
    (hpos : 0 < massOf μ E) {c : ℚ} (hc : ∀ ω, E ω → c ≤ f ω) : c ≤ condExp μ f E := by
  unfold condExp
  rw [le_div_iff₀ hpos]
  have := integralOf_le_integralOf μ (fun _ => c) f hμ E hc
  rw [integralOf_const] at this
  linarith

end NullEvents

/-! ## The paper layer -/

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act]

/-- **A paper layer** over a prior: the chosen-policy coordinate `chosen` (the paper's `π*` as the
prior's uncertainty about the agent's choice) and the effective-policy map `eff`, with the
world's policy points `pp` the effective behaviour of the chosen policy. A paper layer is the
`ProcLayer` whose procedures are policies (`toProcLayer`), so `udt-bli-core`'s `PolicyFair` is
the paper's Policy Fairness on it (`Theorem1.lean`, `paperPolicyFair_iff`).
Source: `main.tex` 95–107, 145–147 (bli-paper-001, 004); mandate §3 ("chosen versus effective")
Kind: D
Fidelity: exact (the chosen policy is a coordinate; `eff` is any map, its properties are
hypotheses of the theorems that need them) -/
structure PaperLayer (P : FiniteBLIPrior 𝒮 m 𝒟 Act) where
  /-- The chosen policy in each world. -/
  chosen : P.Ω → Policy 𝒟 Act
  /-- The effective-policy map. -/
  eff : Policy 𝒟 Act → Policy 𝒟 Act
  /-- The world's policy points are the effective behaviour of the chosen policy. -/
  pp_eff : ∀ ω, P.pp ω = eff (chosen ω)

namespace PaperLayer

variable {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (Λ : PaperLayer P)

/-- The procedure layer of a paper layer: procedures are policies.
Source: mandate §3
Kind: D
Fidelity: exact -/
def toProcLayer : P.ProcLayer where
  Proc := Policy 𝒟 Act
  proc := Λ.chosen
  eff := Λ.eff
  pp_eff := Λ.pp_eff

/-- `μ(chosen = π)`: the paper's `p(π* = ⌜π⌝)`.
Source: `main.tex` 145–147
Kind: D
Fidelity: exact -/
abbrev procMass (π : Policy 𝒟 Act) : ℚ := Λ.toProcLayer.procMass π

/-- `𝔼_μ[U | chosen = π]`: the paper's `E_p(u | π* = ⌜π⌝)` (junk `0` at a null policy).
Source: `main.tex` 145–147 (bli-paper-003, 004)
Kind: D
Fidelity: exact -/
abbrev procEU (π : Policy 𝒟 Act) : ℚ := Λ.toProcLayer.procEU π

/-- `μ(chosen · o = a)`: the mass of the chosen point `π*(o) = a`.
Source: `main.tex` 103–107
Kind: D
Fidelity: exact -/
def pointMass (o : ↥𝒟) (a : Act) : ℚ := massOf P.μ (fun ω => Λ.chosen ω o = a)

/-- **The chosen-point value** `chosenEU o a := 𝔼_μ[U | chosen · o = a]`: the paper's
`E_p(u | π*(o) = a)` with `π*` the chosen policy. Junk `0` at a null point.
Source: `main.tex` 103–107, 127 (bli-paper-002); mandate §3
Kind: D
Fidelity: exact -/
def chosenEU (o : ↥𝒟) (a : Act) : ℚ := condExp P.μ P.U (fun ω => Λ.chosen ω o = a)

/-- `procMass` unfolds to the mass of the chosen-policy event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma procMass_eq (π : Policy 𝒟 Act) : Λ.procMass π = massOf P.μ (fun ω => Λ.chosen ω = π) := rfl

/-- `procEU` unfolds to the conditional expectation on the chosen-policy event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma procEU_eq (π : Policy 𝒟 Act) :
    Λ.procEU π = condExp P.μ P.U (fun ω => Λ.chosen ω = π) := rfl

/-- A positive policy has positive points.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointMass_pos_of_procMass_pos {π : Policy 𝒟 Act} (h : 0 < Λ.procMass π) (o : ↥𝒟) :
    0 < Λ.pointMass o (π o) :=
  lt_of_lt_of_le h (massOf_mono P.μ P.μ_nonneg (fun ω hω => by
    have hω' : Λ.chosen ω = π := hω
    rw [hω']))

/-- **The trivial paper layer**: the chosen policy is the world's policy, `eff = id`.
Source: mandate §3 (Theorems 3/4 live here: `pp` is the chosen policy)
Kind: D
Fidelity: exact -/
def trivial (P : FiniteBLIPrior 𝒮 m 𝒟 Act) : PaperLayer P where
  chosen := P.pp
  eff := id
  pp_eff := fun _ => rfl

omit [Fintype Act] in
/-- On the trivial layer the chosen-point value is `udt-bli-core`'s one-step value `EU`.
Source: mandate T2
Kind: L
Fidelity: exact -/
theorem chosenEU_trivial (P : FiniteBLIPrior 𝒮 m 𝒟 Act) (o : ↥𝒟) (a : Act) :
    (trivial P).chosenEU o a = P.EU o a := rfl

/-- The trivial paper layer's procedure layer is `udt-bli-core`'s `trivialLayer`.
Source: mandate T2
Kind: L
Fidelity: exact -/
theorem toProcLayer_trivial (P : FiniteBLIPrior 𝒮 m 𝒟 Act) :
    (trivial P).toProcLayer = FiniteBLIPrior.trivialLayer P := rfl

end PaperLayer

/-! ## The two rules as predicates -/

variable (S : PaperStructure 𝒟 Act) {P : FiniteBLIPrior 𝒮 m 𝒟 Act} (Λ : PaperLayer P)

/-- **UDT 1.0 as a fixed-point condition on the distinguished policy `πstar`**: at every
observation, `πstar o` is available and its chosen-point value is at least that of every
available action of positive point mass (ties allowed; argmax as a predicate). The circular
`π*(o) := argmax_a E_p(u | π*(o) = ⌜a⌝)` of `main.tex:127` is read with `πstar` the agent's
actual choice and `chosen` the prior's uncertainty about it (module docstring).
**Read under a positive `πstar`** (audit r1): the competitor's point is guarded but `πstar o`'s
is not, so a `πstar` with a *null* point at `o` has the junk value `chosenEU o (πstar o) = 0`
there and "is a fixed point" iff every positive available action has value `≤ 0` (probe
`JunkFixedPoint`: on `NoFair`'s worlds with `U ≡ −1`, `(x, m)` is `IsUDT10` with a null point at
`ō`). Every headline that takes this predicate also takes `0 < procMass πstar`, which makes every
point positive (`pointMass_pos_of_procMass_pos`); the predicate is meaningful only then.
Source: `main.tex` 123–127 (bli-paper-002); mandate §3
Kind: D
Fidelity: variant: a fixed-point predicate on a distinguished policy; the comparison ranges
over positive points only (no junk cells); meaningful only for positive `πstar` -/
def IsUDT10 (πstar : Policy 𝒟 Act) : Prop :=
  ∀ o, πstar o ∈ S.Aof o ∧
    ∀ a ∈ S.Aof o, 0 < Λ.pointMass o a → Λ.chosenEU o a ≤ Λ.chosenEU o (πstar o)

/-- **UDT 1.1**: `πstar` is prior-optimal among the well-typed policies of positive mass (ties
allowed). Read under a positive `πstar` (audit r1): a null `πstar` has the junk value
`procEU πstar = 0` and "is an optimum" iff every positive well-typed policy has value `≤ 0`;
every headline taking this predicate also takes `0 < procMass πstar`.
Source: `main.tex` 135–137 (bli-paper-003)
Kind: D
Fidelity: variant: positive-mass policies only; meaningful only for positive `πstar` -/
def IsUDT11 (πstar : Policy 𝒟 Act) : Prop :=
  ∀ π, S.WellTyped π → 0 < Λ.procMass π → Λ.procEU π ≤ Λ.procEU πstar

/-- On the trivial layer, when every policy is well-typed, UDT 1.1 is `udt-bli-core`'s
`IsPriorOptimalOnSupport`.
Source: mandate T2
Kind: L
Fidelity: exact -/
theorem isUDT11_trivial_iff (hall : ∀ π, S.WellTyped π) (π : Policy 𝒟 Act) :
    IsUDT11 S (PaperLayer.trivial P) π ↔ P.IsPriorOptimalOnSupport π := by
  constructor
  · intro h π' hpos
    exact h π' (hall π') hpos
  · intro h π' _ hpos
    exact h π' hpos

end Cleanroom.Udt.UdtPaperTiling
