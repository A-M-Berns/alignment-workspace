import Cleanroom.Decision.DpWorldsJb.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Jeffrey–Bolker structures as vector measures (T4), the belief-vs-choice-rule fork (T9),
# and the Definition 2 lemmas (T2)

* **T4, the two domain conventions** `slide_vector_form_fails_at_v2_axiom`: slide 30 (AISC
  2025) says a JB structure is "equivalently a finitely-additive vector-valued measure
  `𝒥(E) = [P(E), V(E)·P(E)]`". The corpus carries two domain conventions for `V` that are not
  interchangeable. Under **v2 Definition 2's** convention (`V` on non-null events, the averaging
  axiom on non-null disjoint pairs) the equivalence **fails**: on the three-atom algebra with
  `P = δ_a` the averaging axiom is vacuous and `V(⊤) = 5`, `V({a,n}) = V({a,m}) = 1`,
  `V({a}) = 0` is a v2 pair with no additive `𝒥`. Under the **slide's own** convention ("`V(⊥)`
  is not defined" — so `V` has a value at every non-`⊥` event, null or not — with the averaging
  formula imposed wherever its denominator is positive) that pair is *not* a JB structure
  (`slide_formula_fails_on_slidePair`, `slidePair_not_null_tolerant`): the slide's formula at a
  null `N` and a non-null `A` reads `V(N ∨ A) = V(A)`, which is exactly the null-tolerant axiom
  below, and there the slide's sentence is `jbVec_equiv` (up to `V` on null events, which the
  vector form forgets, and the side condition `𝒥(N).2 = 0` it leaves unstated). So the
  counterexample is a fact about v2's convention, not an error on the slide (audit r1, B1).
* `JBVec`, `toJB`, `toJB_injective`: every vector measure gives a JB pair; the map is injective.
* **T4** `jbVec_equiv`: vector measures with `𝒥(N).2 = 0` on null `N` ≃ JB pairs with the
  **null-tolerant** averaging axiom (`JBPairNT`, null summands read as `0`).
* `jbVec_equiv_of_pos`: when `P` is strictly positive on non-`⊥` events (every corpus example)
  the v2 axiom and the null-tolerant axiom coincide, so the slide is exact as written there.
* `JBVec.mix`: mixtures are pointwise in `JBVec` (the reason the vector form exists).
* **T9** `agree_prices_coincide`, `agree_vacuous_on_null`: Abram's constraint "cf = conditional
  wherever defined" and its silence at null acts.
* **T2** `JBPairNT.pv_eq_sum_atoms`: on a finite algebra the null-tolerant pair is determined by
  its atom values; `slidePair_not_atom_determined`: the v2 pair is **not** (same example).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-! ### Vector measures -/

/-- An **`ℝ²`-valued finitely additive measure** `𝒥 : E → ℝ × ℝ` with nonnegative normalized
first component (slide 30, AISC 2025: "`𝒥` is a finitely-additive vector-valued measure with
`𝒥(A ∨ B) = 𝒥(A) + 𝒥(B)` when `A ∧ B = ⊥`").
Source: `research/references/bli/slides/AISC 2025 - 1 Understanding Trust.pdf` p. 30 | bli-slides-039
Kind: D
Fidelity: exact
Hyps: n/a -/
structure JBVec (E : Type*) [BooleanAlgebra E] where
  /-- The vector measure. -/
  v : E → ℝ × ℝ
  /-- Finite additivity. -/
  add : ∀ X Y, Disjoint X Y → v (X ⊔ Y) = v X + v Y
  /-- The first component is nonnegative. -/
  nonneg : ∀ X, 0 ≤ (v X).1
  /-- The first component is normalized. -/
  top : (v ⊤).1 = 1

namespace JBVec

@[ext] theorem ext {w₁ w₂ : JBVec E} (h : w₁.v = w₂.v) : w₁ = w₂ := by
  cases w₁; cases w₂; cases h; rfl

/-- The first component of a vector measure is a finitely additive probability.
Source: slide 30 (`𝒥(E).1 = P(E)`)
Kind: L
Fidelity: exact
Hyps: n/a -/
def toProb (w : JBVec E) : Prob (∅ : Designation E) where
  P X := (w.v X).1
  nonneg := w.nonneg
  top := w.top
  add X Y h := by
    show (w.v (X ⊔ Y)).1 = (w.v X).1 + (w.v Y).1
    rw [w.add X Y h]
    rfl
  cont _ hD := hD.elim

theorem toProb_apply (w : JBVec E) (X : E) : w.toProb.P X = (w.v X).1 := rfl

theorem mul_div_self_left {a b : ℝ} (ha : a ≠ 0) : a * (b / a) = b := by
  field_simp

/-- A vector measure yields a JB pair: `P := 𝒥.1`, `V X := 𝒥(X).2 / 𝒥(X).1` on non-null `X`;
the averaging axiom is additivity of the second component.
Source: slide 30 (`𝒥(E) = [P(E), V(E)·P(E)]`, read backwards) | bli-slides-039
Kind: P
Fidelity: exact
Hyps: (a) -/
def toJB (w : JBVec E) : JBPair (∅ : Designation E) where
  P := w.toProb
  V X := (w.v X.1).2 / (w.v X.1).1
  avg X Y hX hY h := by
    show (w.v (X ⊔ Y)).1 * ((w.v (X ⊔ Y)).2 / (w.v (X ⊔ Y)).1) =
      (w.v X).1 * ((w.v X).2 / (w.v X).1) + (w.v Y).1 * ((w.v Y).2 / (w.v Y).1)
    have hXY : (0 : ℝ) < (w.v (X ⊔ Y)).1 := w.toProb.pos_of_le_of_pos le_sup_left hX
    have hX' : (w.v X).1 ≠ 0 := hX.ne'
    have hY' : (w.v Y).1 ≠ 0 := hY.ne'
    rw [mul_div_self_left hXY.ne', mul_div_self_left hX', mul_div_self_left hY', w.add X Y h]
    rfl

theorem toJB_P (w : JBVec E) (X : E) : w.toJB.P.P X = (w.v X).1 := rfl

theorem toJB_V (w : JBVec E) (X : E) (h : 0 < (w.v X).1) :
    w.toJB.V ⟨X, h⟩ = (w.v X).2 / (w.v X).1 := rfl

end JBVec

/-- Equal JB pairs have equal desirabilities (dependent congruence).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem JBPair.V_congr {J : Designation E} {p q : JBPair J} (h : p = q) (X : E)
    (hp : 0 < p.P.P X) (hq : 0 < q.P.P X) : p.V ⟨X, hp⟩ = q.V ⟨X, hq⟩ := by
  subst h
  rfl

/-- `toJB` is injective: `𝒥` is recovered on non-null events as `(P, V·P)` and on a null event
`N` from `𝒥 N = 𝒥 ⊤ - 𝒥 Nᶜ` (with `⊤`, `Nᶜ` non-null).
Source: slide 30 | bli-slides-039
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem JBVec.toJB_injective : Function.Injective (JBVec.toJB (E := E)) := by
  intro w₁ w₂ h
  have hP : ∀ X, (w₁.v X).1 = (w₂.v X).1 :=
    fun X => congrArg (fun p : JBPair (∅ : Designation E) => p.P.P X) h
  have hpos : ∀ X, 0 < (w₁.v X).1 → (w₁.v X).2 = (w₂.v X).2 := by
    intro X hX
    have hX' : 0 < (w₂.v X).1 := hP X ▸ hX
    have := JBPair.V_congr h X hX hX'
    rw [w₁.toJB_V X hX, w₂.toJB_V X hX'] at this
    have e1 : (w₁.v X).2 = (w₁.v X).1 * ((w₁.v X).2 / (w₁.v X).1) :=
      (JBVec.mul_div_self_left hX.ne').symm
    rw [e1, this, hP X, JBVec.mul_div_self_left hX'.ne']
  apply JBVec.ext
  funext X
  apply Prod.ext (hP X)
  by_cases hX : 0 < (w₁.v X).1
  · exact hpos X hX
  · have hX0 : (w₁.v X).1 = 0 := le_antisymm (not_lt.1 hX) (w₁.nonneg X)
    have hc : 0 < (w₁.v Xᶜ).1 := by
      have := w₁.toProb.compl X
      rw [JBVec.toProb_apply, JBVec.toProb_apply, hX0] at this
      rw [this]
      norm_num
    have ht : 0 < (w₁.v ⊤).1 := by rw [w₁.top]; exact one_pos
    have e1 := w₁.add X Xᶜ disjoint_compl_right
    have e2 := w₂.add X Xᶜ disjoint_compl_right
    rw [sup_compl_eq_top] at e1 e2
    have s1 := congrArg Prod.snd e1
    have s2 := congrArg Prod.snd e2
    simp only [Prod.snd_add] at s1 s2
    have := hpos Xᶜ hc
    have := hpos ⊤ ht
    linarith

/-! ### The refutation of the slide's equivalence at the v2 axiom -/

/-- The Dirac probability at the atom `0` on the three-atom algebra `Finset (Fin 3)`.
Source: dp-worlds-jb mandate §3 T4 (the three-atom `δ_a` example)
Kind: D
Fidelity: exact
Hyps: n/a -/
def deltaA : Prob (∅ : Designation (Finset (Fin 3))) where
  P s := if (0 : Fin 3) ∈ s then 1 else 0
  nonneg s := by split_ifs <;> norm_num
  top := by simp
  add s t h := by
    by_cases hs : (0 : Fin 3) ∈ s <;> by_cases ht : (0 : Fin 3) ∈ t
    · exact absurd ht (Finset.disjoint_left.1 h hs)
    · simp [hs, ht]
    · simp [hs, ht]
    · simp [hs, ht]
  cont _ hD := hD.elim

theorem deltaA_apply (s : Finset (Fin 3)) : deltaA.P s = if (0 : Fin 3) ∈ s then 1 else 0 := rfl

theorem deltaA_pos_iff (s : Finset (Fin 3)) : 0 < deltaA.P s ↔ (0 : Fin 3) ∈ s := by
  rw [deltaA_apply]
  split_ifs with h <;> simp [h]

/-- The slide's counterexample desirability: `V {0} = 0`, `V ⊤ = 5`, `V = 1` on the other two
non-null events `{0,1}`, `{0,2}`.
Source: dp-worlds-jb mandate §3 T4
Kind: D
Fidelity: exact
Hyps: n/a -/
def slideV (X : {X : Finset (Fin 3) // 0 < deltaA.P X}) : ℝ :=
  if X.1 = {0} then 0 else if X.1 = Finset.univ then 5 else 1

/-- The three-atom pair `(δ_0, slideV)` is a JB pair in **v2's** sense: every non-null event
contains the atom `0`, so no two non-null events are disjoint and v2's averaging axiom is
vacuous. It is *not* a JB structure under the slide's own convention (`slidePair_not_null_tolerant`).
Source: [[decision-problems-v2]] §1 Definition 2; slide 30 | bli-slides-039
Kind: N−
Fidelity: exact (a v2 pair)
Hyps: (a) -/
def slidePair : JBPair (∅ : Designation (Finset (Fin 3))) where
  P := deltaA
  V := slideV
  avg X Y hX hY h := by
    exfalso
    exact Finset.disjoint_left.1 h ((deltaA_pos_iff X).1 hX) ((deltaA_pos_iff Y).1 hY)

/-- **T4, the N− row: the vector form fails under v2 Definition 2's convention.** Slide 30's
sentence "equivalently, `𝒥` is a finitely-additive vector-valued measure with
`𝒥(E) = [P(E), V(E)·P(E)]`", read with `V` on non-null events only and the averaging axiom on
non-null disjoint pairs only (**v2 Definition 2's convention**, not the slide's — the slide
excludes only `⊥`; ATTRIBUTION-UNVETTED which reading the slide intends), is false: for the v2
pair `slidePair` there is no additive `𝒥` with `𝒥.1 = P` and `𝒥.2 = V·P` on non-null events,
since additivity would force `𝒥(⊤).2 = 𝒥{0}.2 + 𝒥{1}.2 + 𝒥{2}.2 = 0 + 1 + 1 = 2 ≠ 5`. Under
the slide's own convention the sentence holds (`jbVec_equiv`, `jbVec_equiv_of_pos`) and this
pair is not a JB structure (`slidePair_not_null_tolerant`). Status in the ledger: proved (a fact
about v2's convention), not a refutation of the slide.
Source: `research/references/bli/slides/AISC 2025 - 1 Understanding Trust.pdf` p. 30, read with [[decision-problems-v2]] §1 Definition 2's domain | bli-slides-039
Kind: N−
Fidelity: variant: v2's domain convention substituted for the slide's
Hyps: (a) -/
theorem slide_vector_form_fails_at_v2_axiom :
    ¬ ∃ J : Finset (Fin 3) → ℝ × ℝ,
      (∀ X Y, Disjoint X Y → J (X ⊔ Y) = J X + J Y) ∧
      (∀ X, (J X).1 = slidePair.P.P X) ∧
      (∀ X (hX : 0 < slidePair.P.P X), (J X).2 = slidePair.V ⟨X, hX⟩ * slidePair.P.P X) := by
  rintro ⟨J, hadd, -, hV⟩
  have e01 : ({0} : Finset (Fin 3)) ⊔ {1} = {0, 1} := by decide
  have e02 : ({0} : Finset (Fin 3)) ⊔ {2} = {0, 2} := by decide
  have eu : ({0, 1} : Finset (Fin 3)) ⊔ {2} = Finset.univ := by decide
  have d01 : Disjoint ({0} : Finset (Fin 3)) {1} := by decide
  have d02 : Disjoint ({0} : Finset (Fin 3)) {2} := by decide
  have du : Disjoint ({0, 1} : Finset (Fin 3)) {2} := by decide
  have h01 := congrArg Prod.snd (hadd _ _ d01)
  have h02 := congrArg Prod.snd (hadd _ _ d02)
  have hu := congrArg Prod.snd (hadd _ _ du)
  rw [e01] at h01
  rw [e02] at h02
  rw [eu] at hu
  simp only [Prod.snd_add] at h01 h02 hu
  have p0 : 0 < slidePair.P.P {0} := (deltaA_pos_iff _).2 (by decide)
  have p01 : 0 < slidePair.P.P {0, 1} := (deltaA_pos_iff _).2 (by decide)
  have p02 : 0 < slidePair.P.P {0, 2} := (deltaA_pos_iff _).2 (by decide)
  have pu : 0 < slidePair.P.P Finset.univ := (deltaA_pos_iff _).2 (by decide)
  have v0 := hV _ p0
  have v01 := hV _ p01
  have v02 := hV _ p02
  have vu := hV _ pu
  have n0 : slidePair.V ⟨{0}, p0⟩ * slidePair.P.P {0} = 0 := by
    show slideV ⟨{0}, p0⟩ * deltaA.P {0} = 0
    simp [slideV, deltaA_apply]
  have n01 : slidePair.V ⟨{0, 1}, p01⟩ * slidePair.P.P {0, 1} = 1 := by
    show slideV ⟨{0, 1}, p01⟩ * deltaA.P {0, 1} = 1
    have h1 : ({0, 1} : Finset (Fin 3)) ≠ {0} := by decide
    have h2 : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := by decide
    simp [slideV, deltaA_apply, h1, h2]
  have n02 : slidePair.V ⟨{0, 2}, p02⟩ * slidePair.P.P {0, 2} = 1 := by
    show slideV ⟨{0, 2}, p02⟩ * deltaA.P {0, 2} = 1
    have h1 : ({0, 2} : Finset (Fin 3)) ≠ {0} := by decide
    have h2 : ({0, 2} : Finset (Fin 3)) ≠ Finset.univ := by decide
    simp [slideV, deltaA_apply, h1, h2]
  have nu : slidePair.V ⟨Finset.univ, pu⟩ * slidePair.P.P Finset.univ = 5 := by
    show slideV ⟨Finset.univ, pu⟩ * deltaA.P Finset.univ = 5
    have h1 : (Finset.univ : Finset (Fin 3)) ≠ {0} := by decide
    simp [slideV, deltaA_apply, h1]
  linarith

/-! ### The null-tolerant pair and the equivalence -/

/-- `P X · V X` with a null `X` read as `0`.
Source: dp-worlds-jb mandate §3 T4(b) ("a null summand read as `0`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def pvFun (P : Prob (∅ : Designation E)) (V : {X : E // 0 < P.P X} → ℝ) (X : E) : ℝ :=
  if h : 0 < P.P X then P.P X * V ⟨X, h⟩ else 0

theorem pvFun_of_pos (P : Prob (∅ : Designation E)) (V : {X : E // 0 < P.P X} → ℝ) {X : E}
    (h : 0 < P.P X) : pvFun P V X = P.P X * V ⟨X, h⟩ := dif_pos h

theorem pvFun_of_null (P : Prob (∅ : Designation E)) (V : {X : E // 0 < P.P X} → ℝ) {X : E}
    (h : P.P X = 0) : pvFun P V X = 0 := dif_neg (by rw [h]; exact lt_irrefl 0)

/-- A **null-tolerant JB pair**: `V` on non-null events, and the averaging axiom
`P (X ⊔ Y) · V (X ⊔ Y) = P X · V X + P Y · V Y` for **all** disjoint `X`, `Y`, with a null
summand read as `0` (the case `P (X ⊔ Y) = 0` is then automatic). Equivalently: v2's axiom plus
`V (N ⊔ A) = V A` for null `N` and non-null `A`.
Source: dp-worlds-jb mandate §3 T4(b); slide 30 | bli-slides-039
Kind: D
Fidelity: variant: null-tolerant averaging
Hyps: n/a -/
structure JBPairNT (E : Type*) [BooleanAlgebra E] where
  /-- The probability. -/
  P : Prob (∅ : Designation E)
  /-- The desirability on non-null events. -/
  V : {X : E // 0 < P.P X} → ℝ
  /-- The null-tolerant averaging axiom. -/
  avgNT : ∀ X Y, Disjoint X Y → pvFun P V (X ⊔ Y) = pvFun P V X + pvFun P V Y

theorem JBPairNT.ext' {p q : JBPairNT E} (hP : p.P = q.P)
    (hV : ∀ X (hp : 0 < p.P.P X) (hq : 0 < q.P.P X), p.V ⟨X, hp⟩ = q.V ⟨X, hq⟩) : p = q := by
  obtain ⟨P, V, avg⟩ := p
  obtain ⟨Q, W, avg'⟩ := q
  cases hP
  congr
  funext ⟨X, hX⟩
  exact hV X hX hX

/-- The second component of a vector measure with `null_zero` equals `pvFun` of its JB pair.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem JBVec.pvFun_toJB (w : JBVec E) (hnull : ∀ X, (w.v X).1 = 0 → (w.v X).2 = 0) (X : E) :
    pvFun w.toProb w.toJB.V X = (w.v X).2 := by
  by_cases h : 0 < (w.v X).1
  · rw [pvFun_of_pos _ _ h]
    show (w.v X).1 * ((w.v X).2 / (w.v X).1) = (w.v X).2
    exact JBVec.mul_div_self_left h.ne'
  · have h0 : (w.v X).1 = 0 := le_antisymm (not_lt.1 h) (w.nonneg X)
    rw [pvFun_of_null _ _ h0, hnull X h0]

/-- **T4 (made true).** Vector measures whose second component vanishes on null events are
exactly the null-tolerant JB pairs: `𝒥 ↦ (𝒥.1, 𝒥.2/𝒥.1)` and `(P, V) ↦ (P, pvFun P V)`.
Source: `AISC 2025 - 1 Understanding Trust.pdf` p. 30 ("equivalently, `𝒥` is a finitely-additive vector-valued measure") | bli-slides-039
Kind: P
Fidelity: variant: null-tolerant averaging axiom (the slide's own formula read at every non-`⊥`
event) and the side condition `𝒥(N).2 = 0` on null `N`, which the slide leaves unstated; `V` on
null events is forgotten by the vector form. Under v2 Definition 2's convention instead the
equivalence fails (`slide_vector_form_fails_at_v2_axiom`)
Hyps: (a) -/
def jbVec_equiv : {w : JBVec E // ∀ X, (w.v X).1 = 0 → (w.v X).2 = 0} ≃ JBPairNT E where
  toFun w :=
    { P := w.1.toProb
      V := w.1.toJB.V
      avgNT := fun X Y h => by
        rw [w.1.pvFun_toJB w.2, w.1.pvFun_toJB w.2, w.1.pvFun_toJB w.2, w.1.add X Y h]
        rfl }
  invFun p :=
    ⟨{ v := fun X => (p.P.P X, pvFun p.P p.V X)
       add := fun X Y h => Prod.ext (p.P.add X Y h) (p.avgNT X Y h)
       nonneg := p.P.nonneg
       top := p.P.top },
      fun X hX => pvFun_of_null _ _ hX⟩
  left_inv w := by
    apply Subtype.ext
    apply JBVec.ext
    funext X
    dsimp only
    exact Prod.ext rfl (w.1.pvFun_toJB w.2 X)
  right_inv p := by
    apply JBPairNT.ext'
    · rfl
    · intro X hp hq
      show pvFun p.P p.V X / p.P.P X = p.V ⟨X, hq⟩
      rw [pvFun_of_pos _ _ hq, mul_div_cancel_left₀ _ hq.ne']

/-- Under strict positivity on non-`⊥` events, a v2 JB pair is a null-tolerant pair (the null
cases of the axiom are `⊥` cases, where both sides vanish).
Source: dp-worlds-jb mandate §3 T4(c)
Kind: C
Fidelity: exact
Hyps: (a) -/
def JBPair.toNT (p : JBPair (∅ : Designation E)) (hpos : ∀ X, X ≠ ⊥ → 0 < p.P.P X) :
    JBPairNT E where
  P := p.P
  V := p.V
  avgNT X Y h := by
    by_cases hX : X = ⊥
    · subst hX
      rw [bot_sup_eq, pvFun_of_null _ _ p.P.bot, zero_add]
    by_cases hY : Y = ⊥
    · subst hY
      rw [sup_bot_eq, pvFun_of_null _ _ p.P.bot, add_zero]
    have hX' := hpos X hX
    have hY' := hpos Y hY
    have hXY : 0 < p.P.P (X ⊔ Y) := p.P.pos_of_le_of_pos le_sup_left hX'
    rw [pvFun_of_pos _ _ hX', pvFun_of_pos _ _ hY', pvFun_of_pos _ _ hXY]
    exact p.avg X Y hX' hY' h

/-- A null-tolerant pair is a v2 JB pair (the axiom restricted to non-null pairs).
Source: dp-worlds-jb mandate §3 T4(c)
Kind: L
Fidelity: exact
Hyps: n/a -/
def JBPairNT.toPair (p : JBPairNT E) : JBPair (∅ : Designation E) where
  P := p.P
  V := p.V
  avg X Y hX hY h := by
    have := p.avgNT X Y h
    rw [pvFun_of_pos _ _ hX, pvFun_of_pos _ _ hY,
      pvFun_of_pos _ _ (p.P.pos_of_le_of_pos le_sup_left hX)] at this
    exact this

theorem JBPair.ext' {J : Designation E} {p q : JBPair J} (hP : p.P = q.P)
    (hV : ∀ X (hp : 0 < p.P.P X) (hq : 0 < q.P.P X), p.V ⟨X, hp⟩ = q.V ⟨X, hq⟩) : p = q := by
  obtain ⟨P, V, avg⟩ := p
  obtain ⟨Q, W, avg'⟩ := q
  cases hP
  congr
  funext ⟨X, hX⟩
  exact hV X hX hX

/-- **T4(c).** When `P` is strictly positive on non-`⊥` events (every corpus example: finite
algebras with every atom charged), v2 JB pairs and null-tolerant pairs coincide, so the slide's
equivalence is exact as written on that scope.
Source: dp-worlds-jb mandate §3 T4(c); slide 30 | bli-slides-039
Kind: C
Fidelity: exact (on the strictly positive scope)
Hyps: (a) -/
def jbVec_equiv_of_pos :
    {p : JBPair (∅ : Designation E) // ∀ X, X ≠ ⊥ → 0 < p.P.P X} ≃
      {p : JBPairNT E // ∀ X, X ≠ ⊥ → 0 < p.P.P X} where
  toFun p := ⟨p.1.toNT p.2, p.2⟩
  invFun p := ⟨p.1.toPair, p.2⟩
  left_inv _ := Subtype.ext (JBPair.ext' rfl fun _ _ _ => rfl)
  right_inv _ := Subtype.ext (JBPairNT.ext' rfl fun _ _ _ => rfl)

/-! ### Mixtures -/

/-- Convex mixtures of vector measures are vector measures (pointwise): the reason the vector
form exists ("makes mixtures of JB structures linear").
Source: `Understanding Trust talk 2024-10.pdf` pp. 18–20 (multigrain mixtures) | bli-slides-029, 039
Kind: L
Fidelity: exact
Hyps: n/a -/
def JBVec.mix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w₁ w₂ : JBVec E) : JBVec E where
  v X := t • w₁.v X + (1 - t) • w₂.v X
  add X Y h := by
    rw [w₁.add X Y h, w₂.add X Y h]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      ring
  nonneg X := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    exact add_nonneg (mul_nonneg ht0 (w₁.nonneg X)) (mul_nonneg (sub_nonneg.2 ht1) (w₂.nonneg X))
  top := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, w₁.top, w₂.top]
    ring

/-- In `(P, V)` coordinates the mixture has `P = t P₁ + (1 - t) P₂` and
`V = (t P₁ V₁ + (1 - t) P₂ V₂) / (t P₁ + (1 - t) P₂)` (second components written as `𝒥.2`).
Source: bli-slides-039 ("makes mixtures of JB structures linear")
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem JBVec.mix_coords (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (w₁ w₂ : JBVec E) (X : E)
    (h : 0 < ((JBVec.mix t ht0 ht1 w₁ w₂).v X).1) :
    (JBVec.mix t ht0 ht1 w₁ w₂).toProb.P X = t * (w₁.v X).1 + (1 - t) * (w₂.v X).1 ∧
    (JBVec.mix t ht0 ht1 w₁ w₂).toJB.V ⟨X, h⟩ =
      (t * (w₁.v X).2 + (1 - t) * (w₂.v X).2) / (t * (w₁.v X).1 + (1 - t) * (w₂.v X).1) :=
  ⟨rfl, rfl⟩

/-! ### T9: the belief-vs-choice-rule fork -/

/-- The typing observation of the wiki's fork argument: inside one supposition `cf a'` is one
probability, so "one event, two probabilities" is impossible. A `T` row — a function is
single-valued.
Source: [[learning-cdt-renderings]] "The fork: belief or choice rule" (lines 59–67) | dp-core-102
Kind: T
Fidelity: exact (the argument's formal content is this typing fact)
Hyps: n/a -/
theorem JBState.cf_single_valued {J : Designation E} (s : JBState J) (a : E) (h : a ≠ ⊥) (X : E)
    {p₁ p₂ : ℝ} (h₁ : (s.cf a h).P.P X = p₁) (h₂ : (s.cf a h).P.P X = p₂) : p₁ = p₂ :=
  h₁ ▸ h₂ ▸ rfl

/-- **T9 (the non-trivial neighbour).** Under Abram's constraint (`AgreesWithConditioning`), for
a positive-probability compound act `a'` the two prices of an event coincide:
`P^{a'} fill = P_s (fill ⊓ a') / P_s a'`.
Source: [[learning-cdt-renderings]] "Abram's constraint, read" | dp-core-102
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem JBState.agree_prices_coincide {J : Designation E} (s : JBState J)
    (hs : s.AgreesWithConditioning) (a' fill : E) (h : 0 < s.s.P.P a') :
    (s.cf a' (s.s.P.ne_bot_of_pos h)).P.P fill = s.s.P.P (fill ⊓ a') / s.s.P.P a' :=
  hs a' h fill

/-- Replace the supposition at one act.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def JBState.update {J : Designation E} (s : JBState J) (a' : E) (q : JBPair J)
    (hq : q.P.P a' = 1) : JBState J where
  s := s.s
  cf b hb := if b = a' then q else s.cf b hb
  success b hb := by
    by_cases hba : b = a'
    · subst hba
      rw [if_pos rfl]
      exact hq
    · rw [if_neg hba]
      exact s.success b hb

/-- **T9, silence at null acts.** The constraint says nothing at `P_s a' = 0`: replacing
`cf a'` by any successful pair keeps `AgreesWithConditioning`. (Where the Troll-Bridge agent
lives — `dp-troll-bridge`'s business.)
Source: [[learning-cdt-renderings]] "Abram's constraint, read" ("binding on positive-probability acts and silent elsewhere") | dp-core-102
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem JBState.agree_vacuous_on_null {J : Designation E} (s : JBState J)
    (hs : s.AgreesWithConditioning) (a' : E) (ha' : s.s.P.P a' = 0) (q : JBPair J)
    (hq : q.P.P a' = 1) : (s.update a' q hq).AgreesWithConditioning := by
  intro b hb X
  have hb' : 0 < s.s.P.P b := hb
  have hba : b ≠ a' := fun h => by rw [h, ha'] at hb'; exact lt_irrefl _ hb'
  show (if b = a' then q else s.cf b _).P.P X = _
  rw [if_neg hba]
  exact hs b hb X

/-! ### T2: atom determination on a finite algebra -/

section Finite

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **T2.** On a finite atomic algebra a null-tolerant pair is determined by its atom values:
`P X · V X = ∑_{ω ∈ X} pvFun {ω}` (the sum over charged atoms of `P {ω} · V {ω}`).
Source: [[decision-problems-v2]] §1 Definition 2 (finite atomic case) | dp-core-003
Kind: L
Fidelity: variant: for the null-tolerant pair (the v2 pair is not atom-determined, see
`slidePair_not_atom_determined`)
Hyps: n/a -/
theorem JBPairNT.pv_eq_sum_atoms (p : JBPairNT (Finset Ω)) (X : Finset Ω) :
    pvFun p.P p.V X = ∑ ω ∈ X, pvFun p.P p.V {ω} := by
  induction X using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact pvFun_of_null _ _ p.P.bot
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq]
    have hd : Disjoint ({a} : Finset Ω) s := Finset.disjoint_singleton_left.2 ha
    exact p.avgNT {a} s hd

/-- The v2 pair `slidePair` is **not** determined by its atom values: `P ⊤ · V ⊤ = 5` while the
only charged atom contributes `P {0} · V {0} = 0`.
Source: [[decision-problems-v2]] §1 Definition 2; dp-worlds-jb mandate §3 T2 | dp-core-003
Kind: N−
Fidelity: n/a
Hyps: (a) -/
theorem slidePair_not_atom_determined :
    slidePair.P.P Finset.univ * slidePair.V ⟨Finset.univ, (deltaA_pos_iff _).2 (by decide)⟩ ≠
      ∑ ω ∈ (Finset.univ : Finset (Fin 3)), pvFun slidePair.P slidePair.V {ω} := by
  have h1 : (Finset.univ : Finset (Fin 3)) ≠ {0} := by decide
  have hpv : ∀ ω : Fin 3, pvFun slidePair.P slidePair.V {ω} = 0 := by
    intro ω
    by_cases hω : ω = 0
    · subst hω
      have h0 : 0 < slidePair.P.P {0} := (deltaA_pos_iff _).2 (by decide)
      rw [pvFun_of_pos slidePair.P slidePair.V h0]
      show deltaA.P {0} * slideV ⟨{0}, h0⟩ = 0
      simp [slideV, deltaA_apply]
    · apply pvFun_of_null
      show deltaA.P {ω} = 0
      rw [deltaA_apply, if_neg]
      rw [Finset.mem_singleton]
      exact fun h => hω h.symm
  rw [Finset.sum_eq_zero fun ω _ => hpv ω]
  intro h
  simp [slidePair, slideV, deltaA, h1] at h

/-! ### The counterexample is v2-specific (audit r1, B1) -/

/-- The slide's formula `V(A ∨ B) = (P(A)V(A) + P(B)V(B)) / (P(A) + P(B))`, applied under the
slide's own domain convention ("`V(⊥)` is not defined", so `V` has a value at the null event
`{1}`) at `A = {1}`, `B = {0}` with `P = δ_0`, evaluates to `V {0}` — whatever `V {1}` is — and
`slideV` (`V {0} = 0`, `V {0,1} = 1`) violates it. So `slidePair` is not a JB structure in the
slide's sense.
Source: `AISC 2025 - 1 Understanding Trust.pdf` p. 30 (the averaging formula and "`V(⊥)` is not defined") | bli-slides-039; audit r1 probes
Kind: N−
Fidelity: exact (the slide's formula, evaluated)
Hyps: (a) -/
theorem slide_formula_fails_on_slidePair (V : Finset (Fin 3) → ℝ)
    (h0 : V {0} = 0) (h01 : V {0, 1} = 1) :
    (deltaA.P {1} * V {1} + deltaA.P {0} * V {0}) / (deltaA.P {1} + deltaA.P {0}) ≠ V {0, 1} := by
  have e1 : deltaA.P {1} = 0 := by simp [deltaA_apply]
  have e0 : deltaA.P {0} = 1 := by simp [deltaA_apply]
  rw [e1, e0, h0, h01]
  norm_num

/-- The null-tolerant axiom at a (null, non-null) disjoint pair is the slide's formula there:
`P (N ⊔ A) · V (N ⊔ A) = P A · V A`, i.e. `V (N ⊔ A) = V A`.
Source: `AISC 2025 - 1 Understanding Trust.pdf` p. 30; dp-worlds-jb mandate §3 T4(b)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem JBPairNT.avgNT_of_null_left (p : JBPairNT E) {N A : E} (hd : Disjoint N A)
    (hN : p.P.P N = 0) (hA : 0 < p.P.P A) (hNA : 0 < p.P.P (N ⊔ A)) :
    p.P.P (N ⊔ A) * p.V ⟨N ⊔ A, hNA⟩ = p.P.P A * p.V ⟨A, hA⟩ := by
  have := p.avgNT N A hd
  rw [pvFun_of_null _ _ hN, zero_add, pvFun_of_pos _ _ hA, pvFun_of_pos _ _ hNA] at this
  exact this

/-- Any null-tolerant pair on the three-atom algebra with `P = δ_0` has `V {0,1} = V {0}`.
Source: none: infrastructure (audit r1 probes)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem JBPairNT.V01_eq_V0_of_deltaA (q : JBPairNT (Finset (Fin 3))) (hP : q.P = deltaA)
    (h0 : 0 < q.P.P {0}) (h01 : 0 < q.P.P {0, 1}) :
    q.V ⟨{0, 1}, h01⟩ = q.V ⟨{0}, h0⟩ := by
  have hd : Disjoint ({0} : Finset (Fin 3)) {1} := by decide
  have e : ({0} : Finset (Fin 3)) ⊔ {1} = {0, 1} := by decide
  have h1 : q.P.P {1} = 0 := by rw [hP, deltaA_apply]; exact if_neg (by decide)
  have hv0 : q.P.P {0} = 1 := by rw [hP, deltaA_apply]; exact if_pos (by decide)
  have hv01 : q.P.P {0, 1} = 1 := by rw [hP, deltaA_apply]; exact if_pos (by decide)
  have := q.avgNT {0} {1} hd
  rw [e, pvFun_of_pos _ _ h01, pvFun_of_pos _ _ h0, pvFun_of_null _ _ h1, hv0, hv01] at this
  linarith

/-- **`slidePair` is not the restriction of any null-tolerant pair**: no JB structure in the
slide's own sense (`V` at every non-`⊥` event, the formula wherever its denominator is positive)
has `slidePair`'s desirabilities on the non-null events. Hence the N− row
`slide_vector_form_fails_at_v2_axiom` lives only under v2 Definition 2's convention.
Source: `AISC 2025 - 1 Understanding Trust.pdf` p. 30 vs [[decision-problems-v2]] §1 Definition 2 | bli-slides-039; audit r1 probes
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem slidePair_not_null_tolerant :
    ¬ ∃ q : JBPairNT (Finset (Fin 3)), q.P = deltaA ∧
      ∀ X (hq : 0 < q.P.P X) (hs : 0 < slidePair.P.P X), q.V ⟨X, hq⟩ = slidePair.V ⟨X, hs⟩ := by
  rintro ⟨q, hP, hV⟩
  have h0 : 0 < q.P.P {0} := by rw [hP]; exact (deltaA_pos_iff _).2 (by decide)
  have h01 : 0 < q.P.P {0, 1} := by rw [hP]; exact (deltaA_pos_iff _).2 (by decide)
  have s0 : 0 < slidePair.P.P {0} := (deltaA_pos_iff _).2 (by decide)
  have s01 : 0 < slidePair.P.P {0, 1} := (deltaA_pos_iff _).2 (by decide)
  have key := q.V01_eq_V0_of_deltaA hP h0 h01
  rw [hV _ h01 s01, hV _ h0 s0] at key
  have n1 : ({0, 1} : Finset (Fin 3)) ≠ {0} := by decide
  have n2 : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := by decide
  simp [slidePair, slideV, n1, n2] at key

end Finite

end

end Cleanroom.Decision.DpWorldsJb
