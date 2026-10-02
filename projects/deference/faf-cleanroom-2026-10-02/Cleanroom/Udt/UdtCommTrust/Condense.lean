import Cleanroom.Udt.UdtCommTrust.Factor
import Mathlib.Tactic.FinCases

/-!
# `Cleanroom.Udt.UdtCommTrust.Condense`: the translation's condensation variable

Work package `udt-comm-trust`, target T2(a),(b). The *translation*
([[communication-trust-translated]] lines 320–329) defines a "condensation variable for
`H(X | Y)`"; the original `references/communication&trust.md` has no such definition (its
dynamics section, lines 318–361, introduces `D_I`, `D_E`, `D_B` by the factorization assumptions
alone). Every docstring here therefore says "the translation defines" (udt-rep-2-008(a)).

The entropy clause `H(V) = H(X | Y)` is replaced by its support-and-law equivalent (3′): `V` is a
function of `(X, Y)` and `V` is independent of `Y` in law. The equivalence, given clause (1), is
T2(c) (`Entropy.lean`, open); (a) and (b) do not depend on it.
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **Independence in law**, division-free: `P(V = v, Y = y) = P(V = v) · P(Y = y)` for all values.
Zero case: none (no division).
Source: none: infrastructure (mandate T2(a), clause (3′))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def IndepLaw {VV VY : Type} [DecidableEq VV] [DecidableEq VY] (μ : FinDist Ω) (V : Ω → VV)
    (Y : Ω → VY) : Prop :=
  ∀ v y, mass μ.w (event fun ω => V ω = v ∧ Y ω = y) =
    mass μ.w (event fun ω => V ω = v) * mass μ.w (event fun ω => Y ω = y)

/-- **The translation's condensation variable** for `(X, Y)`, entropy-free: (1) `X` is a function
of `(Y, V)`; (2) `Y` and `V` are independent in support (`FactorsAs`); (3′) `V` is a function of
`(X, Y)` and `V` is independent of `Y` in law. The definition is the translation's, not the
paper's (udt-rep-2-008(a)); the prefix `CT` keeps it apart from Eisenstat's condensation
(`udt-condense-dd`).
Source: [[communication-trust-translated]] lines 320–329 (the translation's definition; udt-rep-009, 010)
Kind: D
Fidelity: variant: the entropy clause `H(V) = H(X|Y)` replaced by (3′), its equivalent given (1) (T2(c), open)
Hyps: n/a -/
def CTCondensation {VX VY VV : Type} [DecidableEq VV] [DecidableEq VY] (μ : FinDist Ω)
    (X : Ω → VX) (Y : Ω → VY) (V : Ω → VV) : Prop :=
  IsSubvariable (fun ω => (Y ω, V ω)) X ∧ FactorsAs Y V ∧
    IsSubvariable (fun ω => (X ω, Y ω)) V ∧ IndepLaw μ V Y

omit [DecidableEq Ω] in
/-- **Corrected uniqueness**: two `CTCondensation` variables for the same `(X, Y)` are functions of
each other *given `Y`* — worlds with the same `Y`- and `V`-value have the same `V'`-value.
Immediate from clause (1) for `V` and clause (3′) for `V'`. This is the surviving neighbour of the
corpus's uniqueness claim (`ct_not_unique`).
Source: [[topics/dynamics-and-condensation]] line 76 (udt-rep-010); mandate T2(b)
Kind: L (audit r1: two applications of clauses (1) and (3′); regraded from P)
Fidelity: exact
Hyps: (a) -/
theorem CTCondensation.unique_given {VX VY VV VV' : Type} [DecidableEq VV] [DecidableEq VV']
    [DecidableEq VY] {μ : FinDist Ω} {X : Ω → VX} {Y : Ω → VY} {V : Ω → VV} {V' : Ω → VV'}
    (h : CTCondensation μ X Y V) (h' : CTCondensation μ X Y V') :
    ∀ ω ω', Y ω = Y ω' → V ω = V ω' → V' ω = V' ω' := by
  intro ω ω' hy hv
  have hx : X ω = X ω' := h.1 ω ω' (by show (Y ω, V ω) = (Y ω', V ω'); rw [hy, hv])
  exact h'.2.2.1 ω ω' (by show (X ω, Y ω) = (X ω', Y ω'); rw [hx, hy])

/-! ### The refutation witness: XOR on four points -/

/-- The uniform distribution on `Fin 2 × Fin 2`.
Source: none: infrastructure (T2(b) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def uniform4 : FinDist (Fin 2 × Fin 2) where
  w _ := 1 / 4
  nonneg _ := by norm_num
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    norm_num

/-- The XOR of the two coordinates.
Source: none: infrastructure (T2(b) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def xorVar (ω : Fin 2 × Fin 2) : Fin 2 := ω.1 + ω.2

/-- Supporting lemma: a mass on `Fin 2 × Fin 2` under `uniform4` is `1/4` times the count.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem uniform4_mass (P : Fin 2 × Fin 2 → Prop) [DecidablePred P] :
    mass uniform4.w (event P) = ((Finset.univ.filter P).card : ℝ) / 4 := by
  simp [mass, event, uniform4, Finset.sum_const, div_eq_mul_inv]

/-- Supporting lemma: the product law on four uniform points reduces to a count identity in `ℕ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem indep_of_card {c₁ c₂ c₃ : ℕ} (h : 4 * c₁ = c₂ * c₃) :
    (c₁ : ℝ) / 4 = (c₂ : ℝ) / 4 * ((c₃ : ℝ) / 4) := by
  have : (4 : ℝ) * c₁ = c₂ * c₃ := by exact_mod_cast h
  rw [div_mul_div_comm, div_eq_div_iff (by norm_num) (by norm_num)]
  linarith

/-- `snd` is a `CTCondensation` variable for `(xor, fst)`.
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem ct_snd : CTCondensation uniform4 xorVar Prod.fst Prod.snd := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · rw [factorsAs_iff]; decide
  · decide
  · intro v y
    rw [uniform4_mass, uniform4_mass, uniform4_mass]
    fin_cases v <;> fin_cases y <;> exact indep_of_card (by decide)

/-- `xor` itself is a `CTCondensation` variable for `(xor, fst)`.
Source: mandate T2(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem ct_xor : CTCondensation uniform4 xorVar Prod.fst xorVar := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · rw [factorsAs_iff]; decide
  · decide
  · intro v y
    rw [uniform4_mass, uniform4_mass, uniform4_mass]
    fin_cases v <;> fin_cases y <;> exact indep_of_card (by decide)

/-- **Refutation of "condensation variables are unique up to bijection"** (udt-rep-010). Quoted
claim ([[topics/dynamics-and-condensation]] line 76): "If `V` and `V′` are both condensation
variables for `H(X | Y)`, then `V` is a function of `V′` and vice versa." Reading: literal, with
"function of" everywhere on the support (ATTRIBUTION-UNVETTED: the note's author may have meant
"given `Y`", which is `CTCondensation.unique_given`). On four uniform points with `Y = fst`,
`V = snd`, `X = xor`, `V′ = X`: both are `CTCondensation` variables, and `X` is not a function of
`V` (`(0,0)` and `(1,0)` share `V = 0` and have `X`-values `0`, `1`). Surviving neighbour:
`CTCondensation.unique_given`.
Source: [[topics/dynamics-and-condensation]] line 76 (udt-rep-010); mandate T2(b)
Kind: P
Fidelity: exact (refutation of the literal reading)
Hyps: (a) -/
theorem ct_not_unique :
    CTCondensation uniform4 xorVar Prod.fst Prod.snd ∧
      CTCondensation uniform4 xorVar Prod.fst xorVar ∧
      ¬ IsSubvariable (Prod.snd : Fin 2 × Fin 2 → Fin 2) xorVar :=
  ⟨ct_snd, ct_xor, by decide⟩

omit [DecidableEq Ω] in
/-- **A condensation variable is independent of its input** (udt-rep-011's corollary) — in the
(3′) form this is clause (3′) of the definition, read off; the entropy route (`H(V) = H(X|Y)`
forces the independence) is T2(c), open.
Source: [[topics/dynamics-and-condensation]] (udt-rep-011)
Kind: L
Fidelity: exact for the (3′) definition
Hyps: none -/
theorem CTCondensation.indepLaw {VX VY VV : Type} [DecidableEq VV] [DecidableEq VY]
    {μ : FinDist Ω} {X : Ω → VX} {Y : Ω → VY} {V : Ω → VV} (h : CTCondensation μ X Y V) :
    IndepLaw μ V Y := h.2.2.2

end Cleanroom.Udt.UdtCommTrust
