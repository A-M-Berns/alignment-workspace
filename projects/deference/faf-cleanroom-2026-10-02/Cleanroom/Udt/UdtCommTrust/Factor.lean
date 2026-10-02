import Cleanroom.Udt.UdtPolicyCalc.Defs

/-!
# `Cleanroom.Udt.UdtCommTrust.Factor`: random variables, subvariables, "factors as", common information

Work package `udt-comm-trust` (faf-cleanroom run, 2026-09-30), target T1(a). Sources:
[[communication-trust-translated]] lines 184–247 (random variables, "is a function of",
projections, common information, "factors as", families and the restriction map); the original
`references/communication&trust.md` says the same in §2.

Representation of record (mandate §3): a random variable is a plain function `X : Ω → V` on a
finite `Ω`. `Ω` will be the *support* of the probability measure in every decision structure, so
"almost everywhere" and "everywhere" coincide; every notion here is stated everywhere on `Ω`.

The FFS bridge (T1(b),(c)) is in `FfsBridge.lean`, kept separate so that the decision structures
do not import `FiniteFactoredSets`.
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc

variable {Ω : Type}

/-! ### Subvariables -/

/-- **`Y` is a subvariable of `X`** (a function of `X`, a coarsening of `X`): `X ω = X ω'` forces
`Y ω = Y ω'` for every pair of worlds. This is the paper's "`Y = f(X)` almost everywhere"
stated on the support: `isSubvariable_iff_exists` gives back the function `f` (the projection
`[[·]]_Y`) whenever `W` is inhabited. The dependence form is the definition of record because it
is decidable on finite carriers, which is what the witnesses check.
Source: [[communication-trust-translated]] lines 200–206 (udt-rep-009)
Kind: D
Fidelity: variant: "a.e." read as "everywhere on the support" (mandate §3); otherwise exact
Hyps: n/a -/
def IsSubvariable {V W : Type} (X : Ω → V) (Y : Ω → W) : Prop :=
  ∀ ω ω', X ω = X ω' → Y ω = Y ω'

instance {V W : Type} [Fintype Ω] [DecidableEq V] [DecidableEq W] (X : Ω → V) (Y : Ω → W) :
    Decidable (IsSubvariable X Y) := by
  unfold IsSubvariable; infer_instance

/-- The paper's form of "`Y` is a function of `X`": some `f : V → W` has `Y = f ∘ X`. With `W`
inhabited this is `IsSubvariable`; the inhabitation hypothesis is what makes the empty case work.
Source: [[communication-trust-translated]] lines 200–202
Kind: L
Fidelity: exact
Hyps: none -/
theorem isSubvariable_iff_exists {V W : Type} [Nonempty W] (X : Ω → V) (Y : Ω → W) :
    IsSubvariable X Y ↔ ∃ f : V → W, ∀ ω, Y ω = f (X ω) := by
  classical
  constructor
  · intro h
    refine ⟨fun v => if hv : ∃ ω, X ω = v then Y hv.choose else Classical.arbitrary W, fun ω => ?_⟩
    have hv : ∃ ω', X ω' = X ω := ⟨ω, rfl⟩
    simp only [hv, ↓reduceDIte]
    exact h ω hv.choose hv.choose_spec.symm
  · rintro ⟨f, hf⟩ ω ω' h
    rw [hf, hf, h]

/-- Supporting lemma: from the paper's form back to the dependence form (no inhabitation needed).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.of_exists {V W : Type} {X : Ω → V} {Y : Ω → W}
    (h : ∃ f : V → W, ∀ ω, Y ω = f (X ω)) : IsSubvariable X Y := by
  obtain ⟨f, hf⟩ := h
  intro ω ω' hx
  rw [hf, hf, hx]

/-- Supporting lemma `IsSubvariable.of_comp`: `f ∘ X` is a subvariable of `X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.of_comp {V W : Type} (X : Ω → V) (f : V → W) :
    IsSubvariable X (fun ω => f (X ω)) := fun _ _ h => by simp [h]

/-- Supporting lemma `IsSubvariable.refl`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.refl {V : Type} (X : Ω → V) : IsSubvariable X X := fun _ _ h => h

/-- Supporting lemma `IsSubvariable.trans`: a subvariable of a subvariable is a subvariable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.trans {V W Z : Type} {X : Ω → V} {Y : Ω → W} {Zv : Ω → Z}
    (h₁ : IsSubvariable X Y) (h₂ : IsSubvariable Y Zv) : IsSubvariable X Zv :=
  fun ω ω' h => h₂ ω ω' (h₁ ω ω' h)

/-- Supporting lemma `IsSubvariable.comp`: post-composing a subvariable with a function keeps it a
subvariable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.comp {V W Z : Type} {X : Ω → V} {Y : Ω → W} (h : IsSubvariable X Y)
    (f : W → Z) : IsSubvariable X (fun ω => f (Y ω)) := fun ω ω' hx => by
  show f (Y ω) = f (Y ω')
  rw [h ω ω' hx]

/-- Supporting lemma `IsSubvariable.fst`: the first coordinate of a product is a subvariable of it.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.fst {V W : Type} (X : Ω → V) (Y : Ω → W) :
    IsSubvariable (fun ω => (X ω, Y ω)) X := fun _ _ h => (Prod.mk.inj h).1

/-- Supporting lemma `IsSubvariable.snd`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.snd {V W : Type} (X : Ω → V) (Y : Ω → W) :
    IsSubvariable (fun ω => (X ω, Y ω)) Y := fun _ _ h => (Prod.mk.inj h).2

/-- Supporting lemma `IsSubvariable.prod`: two subvariables of `X` make a product subvariable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.prod {V W₁ W₂ : Type} {X : Ω → V} {Y₁ : Ω → W₁} {Y₂ : Ω → W₂}
    (h₁ : IsSubvariable X Y₁) (h₂ : IsSubvariable X Y₂) :
    IsSubvariable X (fun ω => (Y₁ ω, Y₂ ω)) := fun ω ω' h => by
  show (Y₁ ω, Y₂ ω) = (Y₁ ω', Y₂ ω')
  rw [h₁ ω ω' h, h₂ ω ω' h]

/-- Supporting lemma `IsSubvariable.of_fst`: a subvariable of the first coordinate is a
subvariable of the product.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.of_fst {V W Z : Type} {X : Ω → V} {Y : Ω → W} {Zv : Ω → Z}
    (h : IsSubvariable X Zv) : IsSubvariable (fun ω => (X ω, Y ω)) Zv :=
  (IsSubvariable.fst X Y).trans h

/-- Supporting lemma `IsSubvariable.of_snd`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.of_snd {V W Z : Type} {X : Ω → V} {Y : Ω → W} {Zv : Ω → Z}
    (h : IsSubvariable Y Zv) : IsSubvariable (fun ω => (X ω, Y ω)) Zv :=
  (IsSubvariable.snd X Y).trans h

/-- **The projection `[[·]]_Y`** from `X` to a subvariable `Y`: a chosen `f : V → W` with
`Y = f ∘ X` (`IsSubvariable.proj_spec`). Zero case: on values `v ∉ Set.range X` the projection
returns `Classical.arbitrary W`; nothing in this package uses it off the range.
Source: [[communication-trust-translated]] lines 210–213 (udt-rep-009)
Kind: D
Fidelity: exact on `Set.range X`
Hyps: n/a -/
noncomputable def IsSubvariable.proj {V W : Type} [Nonempty W] {X : Ω → V} {Y : Ω → W}
    (h : IsSubvariable X Y) : V → W :=
  Classical.choose ((isSubvariable_iff_exists X Y).1 h)

/-- Supporting lemma `IsSubvariable.proj_spec`: `Y ω = [[X ω]]_Y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IsSubvariable.proj_spec {V W : Type} [Nonempty W] {X : Ω → V} {Y : Ω → W}
    (h : IsSubvariable X Y) (ω : Ω) : Y ω = h.proj (X ω) :=
  Classical.choose_spec ((isSubvariable_iff_exists X Y).1 h) ω

/-! ### "Factors as" -/

/-- **`X` factors as `(Y, Z)`** (the paper's Definition, clause 2): every realized value of `Y`
co-occurs with every realized value of `Z` — `Y` and `Z` are *independent in support*. Clause 1
("`X = (Y, Z)` as random variables") is definitional here: the product variable is
`fun ω => (Yv ω, Zv ω)` by construction, and every decision structure below *defines* the factored
variable as that product.
Source: [[communication-trust-translated]] lines 225–233 (udt-rep-009, 089)
Kind: D
Fidelity: exact (clause 1 definitional)
Hyps: n/a -/
def FactorsAs {Y Z : Type} (Yv : Ω → Y) (Zv : Ω → Z) : Prop :=
  ∀ y ∈ Set.range Yv, ∀ z ∈ Set.range Zv, ∃ ω, Yv ω = y ∧ Zv ω = z

/-- The decidable form of `FactorsAs`: for any two worlds there is a world with the first's
`Y`-value and the second's `Z`-value. Witnesses check this by `decide`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAs_iff {Y Z : Type} (Yv : Ω → Y) (Zv : Ω → Z) :
    FactorsAs Yv Zv ↔ ∀ ω₁ ω₂, ∃ ω, Yv ω = Yv ω₁ ∧ Zv ω = Zv ω₂ := by
  constructor
  · intro h ω₁ ω₂
    exact h _ ⟨ω₁, rfl⟩ _ ⟨ω₂, rfl⟩
  · rintro h y ⟨ω₁, rfl⟩ z ⟨ω₂, rfl⟩
    exact h ω₁ ω₂

/-- Supporting lemma `FactorsAs.symm`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem FactorsAs.symm {Y Z : Type} {Yv : Ω → Y} {Zv : Ω → Z} (h : FactorsAs Yv Zv) :
    FactorsAs Zv Yv := fun z hz y hy => by
  obtain ⟨ω, h₁, h₂⟩ := h y hy z hz
  exact ⟨ω, h₂, h₁⟩

/-- A constant variable factors with anything (and anything with a constant variable): the
degenerate case that the FFS bridge must exclude (`IsTrivialPartition`).
Source: none: infrastructure (T1(b) trap)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAs_of_subsingleton_range {Y Z : Type} (Yv : Ω → Y) (Zv : Ω → Z)
    (h : ∀ ω ω', Yv ω = Yv ω') : FactorsAs Yv Zv := by
  rintro y ⟨ω₁, rfl⟩ z ⟨ω₂, rfl⟩
  exact ⟨ω₂, h ω₂ ω₁, rfl⟩

/-- **`X` factors as the family `(X_i)_{i ∈ ι}`**: every choice function whose coordinates are
realized is realized jointly. The paper's restriction map `m` (choice functions → values of `X`)
is the identity on choice functions in this representation, so it needs no definition; the
family's product variable is `X` itself.
Source: [[communication-trust-translated]] lines 241–247 (udt-rep-009, 089)
Kind: D
Fidelity: exact (restriction map identity; presentation)
Hyps: n/a -/
def FactorsAsFam {ι V : Type} [Fintype ι] (X : Ω → ι → V) : Prop :=
  ∀ c : ι → V, (∀ i, c i ∈ Set.range fun ω => X ω i) → ∃ ω, X ω = c

/-- The decidable form of `FactorsAsFam`: for every assignment of a world to each coordinate there
is a world agreeing with each chosen world on that coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAsFam_iff {ι V : Type} [Fintype ι] (X : Ω → ι → V) :
    FactorsAsFam X ↔ ∀ c : ι → Ω, ∃ ω, ∀ i, X ω i = X (c i) i := by
  constructor
  · intro h c
    obtain ⟨ω, hω⟩ := h (fun i => X (c i) i) (fun i => ⟨c i, rfl⟩)
    exact ⟨ω, fun i => by rw [hω]⟩
  · intro h c hc
    choose g hg using hc
    obtain ⟨ω, hω⟩ := h g
    exact ⟨ω, funext fun i => by rw [hω i]; exact hg i⟩

/-- A two-member family factors iff the pair factors: `FactorsAsFam` over `Bool` is `FactorsAs`
of the two coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAsFam_bool_iff {V : Type} (X : Ω → Bool → V) :
    FactorsAsFam X ↔ FactorsAs (fun ω => X ω false) (fun ω => X ω true) := by
  rw [factorsAsFam_iff, factorsAs_iff]
  constructor
  · intro h ω₁ ω₂
    obtain ⟨ω, hω⟩ := h (fun b => if b then ω₂ else ω₁)
    exact ⟨ω, by simpa using hω false, by simpa using hω true⟩
  · intro h c
    obtain ⟨ω, h₁, h₂⟩ := h (c false) (c true)
    exact ⟨ω, fun b => by cases b <;> assumption⟩

/-! ### Common information -/

/-- **Common information `X ∨ Y`**: `W` is a subvariable of both `X` and `Y`, and every other
common subvariable of `X` and `Y` is a subvariable of `W` — the finest common coarsening. The
paper's "when it exists"; `commonInfo_exists` shows that on a finite carrier it always exists as a
partition (the connected components of the "same `X`-value or same `Y`-value" graph).
Source: [[communication-trust-translated]] lines 215–223 (udt-rep-012)
Kind: D
Fidelity: exact
Hyps: n/a -/
def CommonInfo {V₁ V₂ W : Type} (X : Ω → V₁) (Y : Ω → V₂) (Wv : Ω → W) : Prop :=
  IsSubvariable X Wv ∧ IsSubvariable Y Wv ∧
    ∀ (W' : Type) (Wv' : Ω → W'), IsSubvariable X Wv' → IsSubvariable Y Wv' → IsSubvariable Wv Wv'

/-- The one-step criterion: if `W` is a common subvariable and any two worlds with the same
`W`-value already agree on `X` or on `Y`, then `W` is the common information. This is what the
witnesses check by `decide`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem commonInfo_of_step {V₁ V₂ W : Type} {X : Ω → V₁} {Y : Ω → V₂} {Wv : Ω → W}
    (hX : IsSubvariable X Wv) (hY : IsSubvariable Y Wv)
    (hstep : ∀ ω ω', Wv ω = Wv ω' → X ω = X ω' ∨ Y ω = Y ω') : CommonInfo X Y Wv := by
  refine ⟨hX, hY, fun W' Wv' hX' hY' ω ω' hw => ?_⟩
  rcases hstep ω ω' hw with h | h
  · exact hX' ω ω' h
  · exact hY' ω ω' h

/-- The relation "same `X`-value or same `Y`-value"; its equivalence closure is the common
information partition.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def commonRel {V₁ V₂ : Type} (X : Ω → V₁) (Y : Ω → V₂) (ω ω' : Ω) : Prop :=
  X ω = X ω' ∨ Y ω = Y ω'

/-- **Common information always exists on a finite carrier** (as a partition): the quotient of `Ω`
by the equivalence closure of `commonRel X Y` is the finest common coarsening of `X` and `Y`. This
is the paper's remark "in our discrete setting it will exist", proved in the partition sense; the
Gács–Körner caveat (that this variable can carry less information than `I(X;Y)`) is a statement
about entropy, not about existence, and is recorded in the findings.
Source: [[communication-trust-translated]] lines 221–223 (udt-rep-012; mandate §6 item 10)
Kind: P
Fidelity: exact (partition sense)
Hyps: (a) -/
theorem commonInfo_exists {V₁ V₂ : Type} (X : Ω → V₁) (Y : Ω → V₂) :
    CommonInfo X Y (Quot.mk (commonRel X Y)) := by
  refine ⟨fun ω ω' h => Quot.sound (Or.inl h), fun ω ω' h => Quot.sound (Or.inr h),
    fun W' Wv' hX' hY' ω ω' h => ?_⟩
  have hlift : ∀ a b, commonRel X Y a b → Wv' a = Wv' b := fun a b hab => by
    rcases hab with hab | hab
    · exact hX' a b hab
    · exact hY' a b hab
  have := congrArg (Quot.lift Wv' hlift) h
  simpa using this

/-! ### Witness-side criteria (explicit mixing functions instead of enumeration) -/

/-- `FactorsAs` from an explicit mixing function `g`: `g ω₁ ω₂` carries `ω₁`'s `Y`-value and `ω₂`'s
`Z`-value. Reduces a witness check to `|Ω|²` decidable cases.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAs_of_fun {Y Z : Type} {Yv : Ω → Y} {Zv : Ω → Z} (g : Ω → Ω → Ω)
    (h : ∀ ω₁ ω₂, Yv (g ω₁ ω₂) = Yv ω₁ ∧ Zv (g ω₁ ω₂) = Zv ω₂) : FactorsAs Yv Zv :=
  (factorsAs_iff Yv Zv).2 fun ω₁ ω₂ => ⟨g ω₁ ω₂, h ω₁ ω₂⟩

/-- `FactorsAsFam` from an explicit mixing function on choice functions of worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem factorsAsFam_of_fun {ι V : Type} [Fintype ι] {X : Ω → ι → V} (g : (ι → Ω) → Ω)
    (h : ∀ c i, X (g c) i = X (c i) i) : FactorsAsFam X :=
  (factorsAsFam_iff X).2 fun c => ⟨g c, h c⟩

/-- The two-step criterion for common information: any two worlds with the same `W`-value are
joined by a chain of length two through `g ω ω'`, each step agreeing on `X` or on `Y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem commonInfo_of_chain {V₁ V₂ W : Type} {X : Ω → V₁} {Y : Ω → V₂} {Wv : Ω → W}
    (hX : IsSubvariable X Wv) (hY : IsSubvariable Y Wv) (g : Ω → Ω → Ω)
    (hstep : ∀ ω ω', Wv ω = Wv ω' →
      (X ω = X (g ω ω') ∨ Y ω = Y (g ω ω')) ∧ (X (g ω ω') = X ω' ∨ Y (g ω ω') = Y ω')) :
    CommonInfo X Y Wv := by
  refine ⟨hX, hY, fun W' Wv' hX' hY' ω ω' hw => ?_⟩
  obtain ⟨h1, h2⟩ := hstep ω ω' hw
  have e1 : Wv' ω = Wv' (g ω ω') := by
    rcases h1 with h | h
    · exact hX' _ _ h
    · exact hY' _ _ h
  have e2 : Wv' (g ω ω') = Wv' ω' := by
    rcases h2 with h | h
    · exact hX' _ _ h
    · exact hY' _ _ h
  exact e1.trans e2

end Cleanroom.Udt.UdtCommTrust
