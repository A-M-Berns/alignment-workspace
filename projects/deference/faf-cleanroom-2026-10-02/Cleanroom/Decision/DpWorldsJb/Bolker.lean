import Cleanroom.Decision.DpWorldsJb.JB

/-!
# Bolker rotation (S2): the gauge argument for pair-valued `cf`

The drafting chat's second argument for pair-valued `cf` (line 2389): "rotations tilt `P` by an
affine function of `V` (`P' ∝ P·(1 + cV)`; the exact family should come from Bolker/Jeffrey
before printing), so the probability component of the supposed state isn't
preference-invariant". [[decision-problems-v2]] Remark 1.2 (line 42) states the same argument
in the vetted document ("the transformed `P` is the old one tilted by an affine function of
`V`; exact transformation family to be checked against Bolker in the literature pass … a
bare-probability counterfactual is not a preference-invariant notion"). The family used here
is the mandate writer's recollection of Jeffrey
ch. 6 — **(b), from memory, unverified against the source** (finding 5): with `V(⊤)`
normalized, the preference-preserving transformations are the fractional-linear
`V' = (aV + b)/(cV + d)`, `P' = P·(cV + d)`, with `cV(X) + d > 0` on non-null `X` and
`cV(⊤) + d = 1`.

What is proved is about the *defined* transformation, over the null-tolerant pair (`JBPairNT`,
`J = ∅`): in vector-measure coordinates `𝒥 = (P, P·V)` the transformation is the **linear map**
`(x, y) ↦ (d·x + c·y, b·x + a·y)`, so it sends vector measures to vector measures for free
(`bolkerVec`), hence null-tolerant pairs to null-tolerant pairs (`bolkerTransform`);
`bolkerTransform_P`/`_V` are the coordinate formulas; `bolker_preserves_order` says the
transformation is preference-preserving when `a·d − b·c > 0`; and
**`probability_component_not_invariant`**: `P' = P` iff `c = 0` or `V` is constant on non-null
events — the sharpened "probability-only `cf` is not gauge-invariant". Bolker's uniqueness
theorem (only these transformations preserve preference) is out of scope and not stated.

Over the v2 pair (averaging on non-null pairs only) the transformed `P'` is **not** finitely
additive in general — the null-`X` case needs `V(X ⊔ Y) = V(Y)`, which v2's axiom does not give
(the same gap as finding 3/8); this is why the transformation is defined on `JBPairNT`.
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-- The Bolker transformation in vector coordinates: `(x, y) ↦ (d·x + c·y, b·x + a·y)` applied
pointwise to a vector measure with `𝒥(N).2 = 0` on null `N`; the hypotheses are positivity of
`c·V + d` on non-null events and its normalization at `⊤`.
Source: drafting chat line 2389 (`P' ∝ P·(1 + cV)`); [[decision-problems-v2]] Remark 1.2 (line 42); Jeffrey, *The Logic of Decision* ch. 6 (from memory) | dp-core-2-050
Kind: P
Fidelity: variant: null-tolerant pair, `J = ∅`; the family is (b) from memory
Hyps: (b) the fractional-linear family, cited from memory -/
def bolkerVec (w : {w : JBVec E // ∀ X, (w.v X).1 = 0 → (w.v X).2 = 0}) (a b c d : ℝ)
    (hpos : ∀ X, 0 < (w.1.v X).1 → 0 < d * (w.1.v X).1 + c * (w.1.v X).2)
    (hnorm : d * (w.1.v ⊤).1 + c * (w.1.v ⊤).2 = 1) :
    {w : JBVec E // ∀ X, (w.v X).1 = 0 → (w.v X).2 = 0} :=
  ⟨{ v := fun X => (d * (w.1.v X).1 + c * (w.1.v X).2, b * (w.1.v X).1 + a * (w.1.v X).2)
     add := fun X Y h => by
       rw [w.1.add X Y h]
       ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
     nonneg := fun X => by
       by_cases hX : 0 < (w.1.v X).1
       · exact (hpos X hX).le
       · have h0 : (w.1.v X).1 = 0 := le_antisymm (not_lt.1 hX) (w.1.nonneg X)
         show 0 ≤ d * (w.1.v X).1 + c * (w.1.v X).2
         rw [h0, w.2 X h0]
         simp
     top := hnorm },
    fun X hX => by
      show b * (w.1.v X).1 + a * (w.1.v X).2 = 0
      by_cases h : 0 < (w.1.v X).1
      · exact absurd hX (hpos X h).ne'
      · have h0 : (w.1.v X).1 = 0 := le_antisymm (not_lt.1 h) (w.1.nonneg X)
        rw [h0, w.2 X h0]
        simp⟩

/-- The positivity and normalization hypotheses in `(P, V)` coordinates: `0 < c·V X + d` on
non-null `X` (v2's `P`-non-null events) and `c·V ⊤ + d = 1`.
Source: Jeffrey ch. 6 (from memory) | dp-core-2-050
Kind: D
Fidelity: (b) from memory
Hyps: n/a -/
def BolkerAdmissible (p : JBPairNT E) (c d : ℝ) : Prop :=
  (∀ X (h : 0 < p.P.P X), 0 < c * p.V ⟨X, h⟩ + d) ∧
    c * p.V ⟨⊤, by rw [p.P.top]; exact one_pos⟩ + d = 1

theorem BolkerAdmissible.vec_pos {p : JBPairNT E} {c d : ℝ} (hcd : BolkerAdmissible p c d) :
    ∀ X, 0 < ((jbVec_equiv.symm p).1.v X).1 →
      0 < d * ((jbVec_equiv.symm p).1.v X).1 + c * ((jbVec_equiv.symm p).1.v X).2 := by
  intro X hX
  show 0 < d * p.P.P X + c * pvFun p.P p.V X
  have hX' : 0 < p.P.P X := hX
  rw [pvFun_of_pos _ _ hX']
  have := hcd.1 X hX'
  nlinarith

theorem BolkerAdmissible.vec_norm {p : JBPairNT E} {c d : ℝ} (hcd : BolkerAdmissible p c d) :
    d * ((jbVec_equiv.symm p).1.v ⊤).1 + c * ((jbVec_equiv.symm p).1.v ⊤).2 = 1 := by
  show d * p.P.P ⊤ + c * pvFun p.P p.V ⊤ = 1
  have ht : 0 < p.P.P ⊤ := by rw [p.P.top]; exact one_pos
  rw [pvFun_of_pos _ _ ht, p.P.top]
  have := hcd.2
  linarith

/-- **The Bolker transformation** of a null-tolerant JB pair: `P' = P·(cV + d)`,
`V' = (aV + b)/(cV + d)`, obtained by transporting the linear map `bolkerVec` through
`jbVec_equiv`.
Source: drafting chat line 2389; Jeffrey ch. 6 (from memory) | dp-core-2-050
Kind: C
Fidelity: variant: null-tolerant pair, `J = ∅`; the family is (b) from memory
Hyps: (b) the fractional-linear family -/
def bolkerTransform (p : JBPairNT E) (a b c d : ℝ) (hcd : BolkerAdmissible p c d) :
    JBPairNT E :=
  jbVec_equiv (bolkerVec (jbVec_equiv.symm p) a b c d hcd.vec_pos hcd.vec_norm)

/-- `P' X = P X · (c·V X + d)` on non-null `X` (and `P' X = 0` on null `X`).
Source: Jeffrey ch. 6 (from memory) | dp-core-2-050
Kind: L
Fidelity: exact for the defined transformation
Hyps: n/a -/
theorem bolkerTransform_P (p : JBPairNT E) (a b c d : ℝ) (hcd : BolkerAdmissible p c d) (X : E) :
    (bolkerTransform p a b c d hcd).P.P X = d * p.P.P X + c * pvFun p.P p.V X := rfl

theorem bolkerTransform_P_of_pos (p : JBPairNT E) (a b c d : ℝ) (hcd : BolkerAdmissible p c d)
    (X : E) (h : 0 < p.P.P X) :
    (bolkerTransform p a b c d hcd).P.P X = p.P.P X * (c * p.V ⟨X, h⟩ + d) := by
  rw [bolkerTransform_P, pvFun_of_pos _ _ h]
  ring

/-- `V' X = (a·V X + b)/(c·V X + d)` on non-null `X`.
Source: Jeffrey ch. 6 (from memory) | dp-core-2-050
Kind: L
Fidelity: exact for the defined transformation
Hyps: n/a -/
theorem bolkerTransform_V (p : JBPairNT E) (a b c d : ℝ) (hcd : BolkerAdmissible p c d) (X : E)
    (h : 0 < p.P.P X) (h' : 0 < (bolkerTransform p a b c d hcd).P.P X) :
    (bolkerTransform p a b c d hcd).V ⟨X, h'⟩ =
      (a * p.V ⟨X, h⟩ + b) / (c * p.V ⟨X, h⟩ + d) := by
  show (b * p.P.P X + a * pvFun p.P p.V X) / (d * p.P.P X + c * pvFun p.P p.V X) = _
  rw [pvFun_of_pos _ _ h]
  have hpos := hcd.1 X h
  have hP := h
  field_simp
  ring

/-- The transformation is preference-preserving when `a·d − b·c > 0`: `V' X ≤ V' Y ↔ V X ≤ V Y`
on non-null `X`, `Y`.
Source: Jeffrey ch. 6 (from memory) | dp-core-2-050
Kind: L
Fidelity: exact for the defined transformation
Hyps: n/a -/
theorem bolker_preserves_order (p : JBPairNT E) (a b c d : ℝ) (hcd : BolkerAdmissible p c d)
    (hdet : 0 < a * d - b * c) (X Y : E) (hX : 0 < p.P.P X) (hY : 0 < p.P.P Y)
    (hX' : 0 < (bolkerTransform p a b c d hcd).P.P X)
    (hY' : 0 < (bolkerTransform p a b c d hcd).P.P Y) :
    (bolkerTransform p a b c d hcd).V ⟨X, hX'⟩ ≤ (bolkerTransform p a b c d hcd).V ⟨Y, hY'⟩ ↔
      p.V ⟨X, hX⟩ ≤ p.V ⟨Y, hY⟩ := by
  rw [bolkerTransform_V p a b c d hcd X hX hX', bolkerTransform_V p a b c d hcd Y hY hY']
  have h1 := hcd.1 X hX
  have h2 := hcd.1 Y hY
  rw [div_le_div_iff₀ h1 h2]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    nlinarith
  · intro h
    nlinarith

/-- **S2, sharpened.** The probability component is gauge-invariant (`P' = P`) iff `c = 0` or
`V` is constant on non-null events: "the probability component of the supposed state is not a
preference-invariant notion" unless the rotation is trivial or the desirability is flat.
Source: drafting chat line 2389 ("probability-only `cf` is not gauge-invariant") | dp-core-2-050
Kind: P
Fidelity: exact for the defined transformation; the family is (b) from memory
Hyps: (b) the fractional-linear family -/
theorem probability_component_not_invariant (p : JBPairNT E) (a b c d : ℝ)
    (hcd : BolkerAdmissible p c d) :
    (bolkerTransform p a b c d hcd).P = p.P ↔
      c = 0 ∨ ∀ X (h : 0 < p.P.P X), p.V ⟨X, h⟩ = p.V ⟨⊤, by rw [p.P.top]; exact one_pos⟩ := by
  have ht : 0 < p.P.P ⊤ := by rw [p.P.top]; exact one_pos
  have hnorm := hcd.2
  constructor
  · intro hP
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      intro X h
      have this : (bolkerTransform p a b c d hcd).P.P X = p.P.P X :=
        congrArg (fun Q : Prob (∅ : Designation E) => Q.P X) hP
      rw [bolkerTransform_P_of_pos p a b c d hcd X h] at this
      -- P X * (c V X + d) = P X, P X > 0 ⟹ c V X + d = 1 = c V ⊤ + d
      have h1 : c * p.V ⟨X, h⟩ + d = 1 := by
        have h2 : p.P.P X * (c * p.V ⟨X, h⟩ + d) = p.P.P X * 1 := by rw [this, mul_one]
        exact mul_left_cancel₀ h.ne' h2
      have h3 : c * (p.V ⟨X, h⟩ - p.V ⟨⊤, ht⟩) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 hc
      · linarith
  · intro hcV
    apply Prob.ext
    funext X
    rw [bolkerTransform_P]
    by_cases h : 0 < p.P.P X
    · rw [pvFun_of_pos _ _ h]
      rcases hcV with hc | hV
      · rw [hc]
        have : d = 1 := by rw [hc] at hnorm; linarith
        rw [this]
        ring
      · rw [hV X h]
        have : d * p.P.P X + c * (p.P.P X * p.V ⟨⊤, ht⟩) = p.P.P X * (c * p.V ⟨⊤, ht⟩ + d) := by
          ring
        rw [this, hnorm, mul_one]
    · have h0 : p.P.P X = 0 := le_antisymm (not_lt.1 h) (p.P.nonneg X)
      rw [pvFun_of_null _ _ h0, h0]
      ring

end

end Cleanroom.Decision.DpWorldsJb
