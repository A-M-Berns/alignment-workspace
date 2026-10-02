import Cleanroom.Decision.DpCalibration

/-!
# `dp-calib-limits`: definitions of record

Package `dp-calib-limits` (area `decision`), the plan's split of `dp-calibration`: what
Definition 10's limit *is* (a Popper function, a lexicographic probability system, a ray
choice) and what the device family `FF ⊆ TS ⊆ MSR = DE ⊆ MSR¹⁷` is made of. This file holds
the §3 definitions of record of [[dp-calib-limits-mandate]]; every theorem file imports it.
Nothing of `dp-calibration` or `dp-core-tree` is redefined: `limitCond`, `limitVal`,
`nuPoly`, the senses and the devices are used under their frozen names.

## Modelling choices, disclosed once here (each also on the declaration)

* **Popper functions on a finite atomic algebra** (`IsPopper`): events are `Finset Ω`; the
  axiom set is P07 I2′'s reconstruction (Popper 1959 appendix *iv / van Fraassen 1976 as
  quoted by Hájek 2003 pp. 316–317; the multiplication axiom confirmed from Hájek) — a
  grade (b) definition of record (`Fidelity: variant: finite atomic algebra; (b) axiom form`).
  Additivity is required only on *normal* conditions (`¬ Abnormal p B`, where `Abnormal p B`
  means `p (· | B) ≡ 1`).
* **The `≡ 1` convention** (`popperLimit`): Definition 10's algebraic limit `limitCond` keeps
  `dp-calibration`'s junk `0` on tremble-unreachable conditions; the Popper reading sets the
  conditional to `1` there. This is the only place the convention enters
  (`Fidelity: variant: the ≡ 1 convention on tremble-unreachable conditions`).
* **Rays** (`Ray`): a problem-side object — one positively-trailing polynomial weight per
  `(d, a)`, summing to the constant `1` at each point. `IsRayOf R C` says the ray starts at
  `C` (constant coefficients). The uniform ray of Definition 10 is `uniformRay C` (weights
  `trembleW`). No `ε`-dependent payoffs exist (`dp-calibration` findings F17).
* **Nonstandard labels in polynomial coordinates**: no ordered field `ℝ(ε)` is built
  (Mathlib's `RatFunc` carries no order). "Non-negative near `0⁺`" is `NonnegNear0`: the
  polynomial is zero or its trailing coefficient is positive; `Nonstandard.lean` proves this
  equivalent to non-negativity on an interval `(0, ε₀)` (`Fidelity: variant: polynomial
  coordinates for ℝ(ε)`).
* **MSR** (`MSRAt`, `MSR`): SL-21's Definition 18′ verbatim — `supp C(d) ⊆ argmax` of the
  tremble-pinned act values `limitVal`, over the acts whose event is tremble-realizable; as
  written it demands realizability of every supported act unconditionally, which is where it
  differs from D4's escape clauses (`Family.lean` states the exact relation).
* **Abbreviations, not redefinitions** (plan §0.4 rule 10): `FF := EventTrembleEdtConsistent`
  (D2), `TS := TestSeqTrembleEdtConsistent` (DY-3), `MSR17At := TEdtAt` (Definition 17's
  advocacy at a strict state), `DE := OccEdtConsistent` (D3⁰).
* **εFP** (`EpsFP`): P05's `ε`-floored device with the act values cross-multiplied under
  positivity guards; Definition 18's escape clause included.
* **The anti-zero-respecting (chicken) rule**, **the Weak Thesis**, **per-run SSC with a
  full-support self-model**, **the grid's uniform substitution** and **the calibration
  manifold** are typed as the mandate §3.7 states them.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Popper functions on a finite atomic algebra -/

section popper

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- A condition `B` is *abnormal* for a two-place function `p` if `p (· | B) ≡ 1`.
Source: `sl-workflow/notes/repair/P07.md` I2′ (the `≡ 1` convention on unreachable
conditions); Hájek 2003 p. 316 (abnormal conditions)
Kind: D -/
def Abnormal (p : Finset Ω → Finset Ω → K) (B : Finset Ω) : Prop := ∀ A, p A B = 1

/-- **A Popper function on the finite atomic algebra of `Ω`** (axiom form reconstructed by the
SL run from Popper 1959 appendix *iv / van Fraassen 1976 as quoted by Hájek 2003 pp. 316–317):
(P0) values in `[0, 1]`; (P1) `p B B = 1`; (P2) additivity on normal conditions; (P3) the
multiplication axiom `p (A ∩ B) C = p A (B ∩ C) · p B C`; (P4) non-triviality.
Source: P07 I2′ (dp-sl-029); Hájek 2003 pp. 316–317
Kind: D
Fidelity: variant: finite atomic algebra; (b) axiom form [reconstructed by the SL run; the
multiplication axiom confirmed from Hájek] -/
structure IsPopper (p : Finset Ω → Finset Ω → K) : Prop where
  /-- (P0) `0 ≤ p A B ≤ 1`. -/
  bounds : ∀ A B, 0 ≤ p A B ∧ p A B ≤ 1
  /-- (P1) `p B B = 1`. -/
  refl : ∀ B, p B B = 1
  /-- (P2) additivity on normal conditions. -/
  add : ∀ A A' B, ¬ Abnormal p B → Disjoint A A' → p (A ∪ A') B = p A B + p A' B
  /-- (P3) the multiplication axiom. -/
  mul : ∀ A B C, p (A ∩ B) C = p A (B ∩ C) * p B C
  /-- (P4) non-triviality: some conditional probability is not `1`. -/
  nontrivial : ∃ A B, p A B ≠ 1

/-- A Popper function as a bundled object: the two-place function with the axioms.
Source: P07 I2′; Hájek 2003 pp. 316–317
Kind: D
Fidelity: variant: finite atomic algebra; (b) axiom form -/
structure PopperFn (Ω : Type) [Fintype Ω] [DecidableEq Ω] (K : Type) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  /-- The conditional probability `p (A | B)`. -/
  p : Finset Ω → Finset Ω → K
  /-- The axioms. -/
  isPopper : IsPopper p

end popper

/-! ## The Popper reading of Definition 10, and rays -/

section rays

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **The Popper reading of Definition 10**: `limitCond C B A B'` where `B'` is
tremble-realizable (`nuPoly C B B' ≠ 0`), and `1` on tremble-unreachable conditions — the
`≡ 1` convention of P07 I2′. `limitCond` itself keeps `dp-calibration`'s junk `0` there.
Source: P07 I2′ ("with the convention `P(· | B) ≡ 1` on tremble-unreachable `B`"); SL-12
Kind: D
Fidelity: variant: the ≡ 1 convention on tremble-unreachable conditions -/
noncomputable def popperLimit (C : Proc ι acts K) (B : Tree Ω ι acts K) (A B' : Finset Ω) : K :=
  if nuPoly C B B' ≠ 0 then limitCond C B A B' else 1

end rays

/-- **A ray of trembles**: a polynomial weight `w d a` in `ε` for every point and action, summing
to the constant `1` at each point, every weight positively trailing (so the order lemmas of
`dp-calibration`'s `PosTrail` apply). The uniform ray of Definition 10 is `uniformRay`; other
rays (e.g. `s = ε, t = ε²` on the two-route tree) are problem-side choices.
Source: P07 I2′ ("each ray of trembles selects one"; "the uniform ray is a choice"); SE-18′(b)
Kind: D
Fidelity: variant: rays as polynomial weight families (no ordered field `ℝ(ε)`) -/
structure Ray (ι : Type) (acts : ι → Type) [∀ d, Fintype (acts d)] (K : Type) [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The weight of `(d, a)` as a polynomial in `ε`. -/
  w : (d : ι) → acts d → Polynomial K
  /-- Weights sum to one at each point. -/
  sum_one : ∀ d, ∑ a, w d a = Polynomial.C 1
  /-- Every weight is positively trailing. -/
  posTrail : ∀ d a, PosTrail (w d a)

section rays2

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- The ray `R` *starts at* `C`: its constant coefficients are `C`'s weights.
Source: P07 I2′ (the ray of trembles of `C`); SE-18′(b)
Kind: D -/
def IsRayOf (R : Ray ι acts K) (C : Proc ι acts K) : Prop := ∀ d a, (R.w d a).coeff 0 = (C d).w a

/-- A ray is full-support if no weight is the zero polynomial (every act is trembled to).
Source: P07 I3′ (trap rays set `w d a = 0` at stipulated traps; full-support rays do not)
Kind: D -/
def Ray.FullSupport (R : Ray ι acts K) : Prop := ∀ d a, R.w d a ≠ 0

/-- **The uniform ray of Definition 10**: weights `trembleW C d a = C(d)(a) + ε(1/|A_d| − C(d)(a))`.
Source: [[decision-problems-v2]] §3.1 Definition 10; P07 I2′ ("the uniform ray")
Kind: D -/
noncomputable def uniformRay (C : Proc ι acts K) : Ray ι acts K where
  w d a := trembleW C d a
  sum_one d := by
    simp only [trembleW]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum, (C d).sum_one,
      Finset.sum_sub_distrib, (C d).sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card (acts d) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [mul_inv_cancel₀ this, sub_self, map_zero, zero_mul, add_zero]
  posTrail d a := posTrail_trembleW C d a

/-- The run law along a ray as a polynomial in `ε`: chance weights are constants, draw
weights are the ray's weights (the same recursion as `leafLawPoly`, which is the uniform ray's).
Source: [[decision-problems-v2]] Lemma 2 proof (polynomial leaf probabilities); P07 I2′
Kind: D -/
noncomputable def leafLawPolyRay (R : Ray ι acts K) :
    (B : Tree Ω ι acts K) → B.Leaves → Polynomial K
  | .leaf _ _, _ => 1
  | .chance _ β child, ⟨i, ℓ⟩ => Polynomial.C (β.w i) * leafLawPolyRay R (child i) ℓ
  | .decision d child, ⟨a, ℓ⟩ => R.w d a * leafLawPolyRay R (child a) ℓ

/-- `ν_{B,R(ε)}(X)` as a polynomial along the ray `R`.
Source: P07 I2′; SE-18′(b)
Kind: D -/
noncomputable def nuPolyRay (R : Ray ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    Polynomial K :=
  ∑ ℓ ∈ worldEv B X, leafLawPolyRay R B ℓ

/-- `∑_{λ⊨X} μ_{R(ε)}(ℓ) r(ℓ)` as a polynomial along the ray `R`.
Source: P07 I2′; SE-18′(b)
Kind: D -/
noncomputable def payPolyRay (R : Ray ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    Polynomial K :=
  ∑ ℓ ∈ worldEv B X, leafLawPolyRay R B ℓ * Polynomial.C (payoff B ℓ)

/-- The limiting conditional along the ray `R`, taken algebraically as `limitCond` is: the
quotient of the coefficients at the order of `nuPolyRay R B O`; junk `0` when that is `0`.
Source: P07 I2′ (Definition 10's limit along a ray); SE-18′(b)
Kind: D
Fidelity: variant: limit taken algebraically by lowest-order coefficients -/
noncomputable def limitCondRay (R : Ray ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) : K :=
  (nuPolyRay R B (X ∩ O)).coeff (nuPolyRay R B O).natTrailingDegree /
    (nuPolyRay R B O).coeff (nuPolyRay R B O).natTrailingDegree

/-- The limiting act value along the ray `R` (the ray form of `limitVal`).
Source: SE-18′(b) (`V(a) = 10s/(s+t)` along a ray); P07 I2′
Kind: D
Fidelity: variant: limit taken algebraically -/
noncomputable def limitValRay (R : Ray ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω) : K :=
  (payPolyRay R B Y).coeff (nuPolyRay R B Y).natTrailingDegree /
    (nuPolyRay R B Y).coeff (nuPolyRay R B Y).natTrailingDegree

/-- **Limit calibration along a ray**, mirroring `LimitOCAt` with `nuPolyRay`/`payPolyRay`.
Source: [[decision-problems-v2]] §3.1 Definition 10 read along the ray `R` (P07 I2′)
Kind: D
Fidelity: variant: limit taken algebraically; ray-relative -/
def LimitOCRayAt (R : Ray ι acts K) (s : ι → State Ω K) (obs : ι → Finset Ω)
    (B : Tree Ω ι acts K) (d : ι) : Prop :=
  nuPolyRay R B (obs d) ≠ 0 →
    (∀ X, (s d).pr X = limitCondRay R B X (obs d)) ∧
    (∀ X, 0 < limitCondRay R B X (obs d) →
      (s d).V X * (nuPolyRay R B (X ∩ obs d)).coeff (nuPolyRay R B (X ∩ obs d)).natTrailingDegree =
        (payPolyRay R B (X ∩ obs d)).coeff (nuPolyRay R B (X ∩ obs d)).natTrailingDegree)

end rays2

/-! ## Nonstandard labels in polynomial coordinates -/

/-- **"Non-negative near `0⁺`"** for a polynomial: it is zero or its trailing coefficient is
positive. `Nonstandard.lean` proves this is exactly non-negativity on some `(0, ε₀)` — the
whole content of "the sign of a rational function near `0⁺` is its order in `ℝ(ε)`".
Source: P07 I1′ ("sign of a rational function near `0⁺` = its order in `ℝ(ε)`"); mandate §3.4
Kind: D
Fidelity: variant: polynomial coordinates for ℝ(ε) -/
def NonnegNear0 (p : Polynomial K) : Prop := p = 0 ∨ 0 < p.trailingCoeff

/-! ## The device family: MSR, the abbreviations, εFP -/

section devices

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- **Definition 18′ at a point (mixed-strategy ratifiability, limit form)**:
`supp C(d) ⊆ argmax_{a} v_d(a; C)` with `v_d(a; C) := limitVal C B (a ∧ O_d)`, the
tremble-pinned act value, defined where `a ∧ O_d` is tremble-realizable. As written it demands
`nuPoly (a ∧ O_d) ≠ 0` for every supported `a` unconditionally (no escape clause), which is
exactly where it differs from D4 `AdviceEdt` (`Family.lean`).
Source: `sl-amendments.md` SL-21, Definition 18′ (line 155); dp-sl-005
Kind: D
Fidelity: exact (limit taken algebraically, as `limitVal`) -/
def MSRAt (d : ι) : Prop :=
  ∀ a, 0 < (C d).w a → nuPoly C B (actEv d a ∩ obs d) ≠ 0 ∧
    ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
      limitVal C B (actEv d b ∩ obs d) ≤ limitVal C B (actEv d a ∩ obs d)

/-- **MSR**: Definition 18′ at every queried point.
Source: SL-21 Definition 18′; dp-sl-005
Kind: D -/
def MSR : Prop := ∀ d ∈ queried B, MSRAt obs actEv C B d

/-- **FF**, the fixed-form (fixed-procedure) tremble-EDT device: the sources' name for D2.
Source: `sl-defensible-claims.md` S10; C2-9′ ("FF"); `calibration.md` D2
Kind: D -/
abbrev FF : Prop := EventTrembleEdtConsistent obs actEv C B

/-- **TS**, the test-sequence tremble-EDT device: the sources' name for DY-3.
Source: S10; C2-9′ ("TS"); `dynamic.md` DY-3
Kind: D -/
abbrev TS : Prop := TestSeqTrembleEdtConsistent obs actEv C B

/-- **MSR¹⁷ at a point**: Definition 17's advocacy `T_EDT` read at the state `s`; the
sources' `MSR¹⁷` is this at a *strictly calibrated* state (the theorems carry that hypothesis).
Source: SL-21 ("read on Definition 17's domain `A_d^+` instead"); C2-9′ (`MSR¹⁷`)
Kind: D -/
abbrev MSR17At (s : ι → State Ω K) (d : ι) : Prop := TEdtAt s actEv C d

/-- **DE**, deliberational equilibrium: the sources' name for D3⁰ (Theorem 1's forcing
evaluator at `ε = 0`). The identification of Skyrms's deliberational equilibrium with D3⁰ is
the SL run's (C2-6) and ATTRIBUTION-UNVETTED.
Source: C2-6, C2-9′ ("DE"); `calibration.md` D3⁰
Kind: D -/
abbrev DE : Prop := OccEdtConsistent C B

/-- **εFP** (P05's `ε`-floored device): every act has weight at least `ε/|A_d|`, and at every
queried point where some act event is realized, every act strictly above the floor maximizes
the strictly calibrated act values of `C` itself (cross-multiplied, with positivity guards;
Definition 18's escape clause included). The floor `ε/|A_d|` is SE-18′(a)'s `Δ_ε`, a
reparametrization of P05's "all action probabilities at least `ε`" (P05's `ε` is this `ε/|A_d|`);
it is what makes `epsFP_tremble_iff_d2At` exact. The floor clause quantifies over every point,
queried or not (unqueried points enter nowhere else); P05's floor is per queried point.
Source: P05 `:33, :38` via C2-9′; P07 I1′ rider ("SE-18′'s ε-floored simplex")
Kind: D
Fidelity: variant: floor `ε/|A_d|` (SE-18′(a)'s parametrization of P05's `ε`); floor on all
points; act values as `condExp` under the positivity guards -/
def EpsFP (ε : K) : Prop :=
  (∀ d a, ε / (Fintype.card (acts d) : K) ≤ (C d).w a) ∧
  ∀ d ∈ queried B, (∃ b, 0 < nu C B (actEv d b ∩ obs d)) →
    ∀ a, ε / (Fintype.card (acts d) : K) < (C d).w a →
      0 < nu C B (actEv d a ∩ obs d) ∧
      ∀ b, 0 < nu C B (actEv d b ∩ obs d) →
        condExp C B (actEv d b ∩ obs d) ≤ condExp C B (actEv d a ∩ obs d)

/-- **The anti-zero-respecting (p-chicken) rule at `d`**: an act the state is nearly certain
of (`P_{s_d}(a) > 1 − ε`) gets weight `0`.
Source: P10-8′; P04 Import 5 (the anti-zero-respecting rule); SL-13
Kind: D -/
def AntiZeroRespectingAt (s : ι → State Ω K) (ε : K) (d : ι) : Prop :=
  ∀ a, 1 - ε < (s d).pr (actEv d a) → (C d).w a = 0

/-- **The Weak Thesis at `d`**: every act event has state probability strictly between `0`
and `1`. The Strong Thesis ("the agent has no credence in its own acts at all") has no slot in
the type `State` — `P` is total and every act event gets a number — and is recorded as a
finding, not a theorem (L3-2′; `dp-calib-limits-findings.md`).
Source: L3-6′; `sl-defensible-claims.md` S15
Kind: D -/
def WeakThesisAt (s : ι → State Ω K) (d : ι) : Prop :=
  ∀ a, 0 < (s d).pr (actEv d a) ∧ (s d).pr (actEv d a) < 1

/-- **Per-run SSC with a full-support self-model at `d`**: some full-support `m` makes `occ(d)`
positive under `C[d ↦ m]` and `s_d` satisfies the per-run clauses under `C[d ↦ m]`.
Source: P11 §A4; P11-12′(e); `sl-synthesis.md` §5.4 item 10 (dp-sl-075)
Kind: D
Fidelity: exact (per-run `V`-clause reading as `dp-calibration`'s) -/
def PerRunSSCMaskedAt (s : ι → State Ω K) (d : ι) : Prop :=
  ∃ m : FinDistr K (acts d), (∀ a, 0 < m.w a) ∧
    0 < mass (C.deviate d m) B (occ d B) ∧ PerRunClausesAt s (C.deviate d m) B d

/-- **The SL grid's masked column**: the strict clauses at the state of `C[d ↦ Unif]` — the
`(c)` substitution the grid computed in place of Definition 9's existential (C1 Open 8).
Source: C1 Open 8 (dp-sl-2-062)
Kind: D
Fidelity: variant: a (c) substitution for Definition 9 (disclosed; `Zo1.lean` proves it
strictly stronger) -/
def MaskedUniformAt (s : ι → State Ω K) (d : ι) : Prop :=
  0 < nu (C.deviate d FinDistr.uniform) B (obs d) ∧
    StrictClausesAt s obs (C.deviate d FinDistr.uniform) B d

/-- **The calibration manifold `M_d`** (v2's Q2): the conditionals `ν_{C'}(· | O_d)` over the
local full-support self-models `C' = C[d ↦ m]` that realize `O_d`, as functions on events
(cross-multiplied: `f X · ν_{C'}(O_d) = ν_{C'}(X ∧ O_d)`).
Source: [[decision-problems-v2]] Q2 (line 297); CA-8′
Kind: D -/
def manifold (d : ι) : Set (Finset Ω → K) :=
  {f | ∃ C', Admissible .LF C d C' ∧ 0 < nu C' B (obs d) ∧
    ∀ X, f X * nu C' B (obs d) = nu C' B (X ∩ obs d)}

end devices

end Cleanroom.Decision.DpCalibLimits
