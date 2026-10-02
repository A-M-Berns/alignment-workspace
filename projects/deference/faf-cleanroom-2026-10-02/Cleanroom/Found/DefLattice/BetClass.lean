import Cleanroom.Found.DefLattice.Notions
import Cleanroom.Found.DefLattice.Menu

/-!
# The common closure class (T7) and the domain-relative notions

Package `def-lattice`, file 4 of the definitions module. The six-arrow table (msg 68 of the
2026-07-23 arc; documented in `def-lattice-report`) says each arrow of the lattice needs a
different closure of the bet class — ramp-weighting by the expert's quotes (Tower ⟹ TT),
argmax composites and differences (TT ⟹ Value), gap-bets and constants (Value ⟹ Tower) — all
e.d. operations generating one common class, v6 §1.2's "e.d. bounded LUV-combinations of menu
options and observable expert-estimates".

A `BetClass DP E` is a set of e.d. LUV sequences. Its closure predicates are stated in
**reflection form** and **universally**: every quote/product/follower of a class member *that
carries the reflection clause and a code certificate* is in the class. This is the form the
arrows consume (a hypothesis-notion restricted to the class then applies to the quotes of its
members) and the form under which intersections are closed and a least closed class containing
a base exists (`generated`). It does **not** assert that any quote exists — that is
`li-quote-lane`'s and FAF's `Construction/Quotation`'s job; a class may be closed vacuously.
Combinations (`XW − s·W`, `Z − Y`, `S − O^i`) are formed from members; the class holds LUVs.

The domain-relative notions `TowerOn`, `ThresholdIneqAboveOn/BelowOn`, `ValueOn` restrict the
quantifiers of `Notions.lean`/`Menu.lean` to a class; on the universal class they are the
unrestricted predicates (`towerOn_univ_iff` …).

Also here (T8, vq-wiki-028's one formalizable fragment): `no_generable_hard_indicator` — a
sharp indicator of a price event is not the denotation of any expressible feature
(`EF.continuous_denote`).
-/

namespace Cleanroom.Found.DefLattice

open LogicalInduction Filter Topology

noncomputable section

/-- **A bet class:** a set of efficiently describable LUV sequences. `DP` and `E` are phantom
indices naming the process and expert the closure predicates refer to.
Source: lean-deference-072 (msg 68); v6 §1.2 ("e.d. bounded LUV-combinations of menu options
and observable expert-estimates")
Kind: D
Fidelity: variant: a class of LUV sequences (combinations are formed from members) -/
structure BetClass (DP : DeductiveProcess) (E : Expert DP) where
  /-- the member sequences -/
  carrier : Set (ℕ → LUV)
  /-- every member is efficiently describable -/
  codes : ∀ X ∈ carrier, LUV.MachineThresholdCodeSeq X

namespace BetClass

variable {DP : DeductiveProcess} {E : Expert DP}

/-- The universal class: every e.d. LUV sequence.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def univ (DP : DeductiveProcess) (E : Expert DP) : BetClass DP E :=
  ⟨{X | LUV.MachineThresholdCodeSeq X}, fun _ hX => hX⟩

/-- Membership in the universal class is the code certificate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mem_univ_iff (X : ℕ → LUV) :
    X ∈ (univ DP E).carrier ↔ LUV.MachineThresholdCodeSeq X := Iff.rfl

/-- The intersection of two classes.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def inter (C₁ C₂ : BetClass DP E) : BetClass DP E :=
  ⟨C₁.carrier ∩ C₂.carrier, fun X hX => C₁.codes X hX.1⟩

/-- The ramp weights: `rampAbove δ s` and `rampBelow δ s` at positive width.
Source: [[deference-notions]] §Total Trust
Kind: D
Fidelity: exact -/
def rampWeights : Set (ℝ → ℝ) :=
  {wt | ∃ s δ : ℚ, 0 < δ ∧ (wt = rampAbove δ s ∨ wt = rampBelow δ s)}

/-- The band weights `bandWt δ s ε` at positive width and half-width.
Source: [[reflection-in-li]] §The value form
Kind: D
Fidelity: exact -/
def bandWeights : Set (ℝ → ℝ) :=
  {wt | ∃ s ε δ : ℚ, 0 < ε ∧ 0 < δ ∧ wt = bandWt δ s ε}

/-- **Closure under weighting by the expert's quotes** at a family of weight functions: for
every member `X` and every weight quote `(W, XW)` of `X` at a weight in `wts`, both `W` and
`XW` are members. (Tower ⟹ TT needs the tower on `X · Ind_δ(E*(X) > t)`.)
Source: lean-deference-072 (msg 68: "closure under ramp-weighting by the expert's own quotes")
Kind: D
Fidelity: exact (reflection form, universal) -/
def WeightClosed (C : BetClass DP E) (wts : Set (ℝ → ℝ)) : Prop :=
  ∀ X ∈ C.carrier, ∀ wt ∈ wts, ∀ W XW : ℕ → LUV, WeightQuote DP E X wt W XW →
    W ∈ C.carrier ∧ XW ∈ C.carrier

/-- Closure under ramp-weighting (both cuts, every rational threshold, every positive width).
Source: lean-deference-072
Kind: D
Fidelity: exact -/
abbrev RampClosed (C : BetClass DP E) : Prop := C.WeightClosed rampWeights

/-- **Closure under gap-bets:** every e.d. quote `Y` reflecting `E*(Z)` of a member `Z` is a
member (so the gap-bet `Z − ⌜E*(Z)⌝` is a combination of members).
Source: lean-deference-072 (msg 68: "closure under gap-bets and constants");
[[value-implies-tower]]; [[tower-implies-total-trust]]
Kind: D
Fidelity: exact (reflection form, universal) -/
def GapClosed (C : BetClass DP E) : Prop :=
  ∀ Z ∈ C.carrier, ∀ Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Y → Reflects DP E Z Y →
    Y ∈ C.carrier

/-- **Closure under constants:** every e.d. LUV sequence valued at a fixed rational in every
consistent world is a member.
Source: lean-deference-072
Kind: D
Fidelity: exact -/
def ConstClosed (C : BetClass DP E) : Prop :=
  ∀ (s : ℚ) (K : ℕ → LUV), LUV.MachineThresholdCodeSeq K →
    (∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (K n) s) → K ∈ C.carrier

/-- **Closure under argmax composites:** every e.d. `S` following the expert on a
*world-valued* menu of members is a member (so `Ŝ − O^i` is a combination of members). The
`M.Valued DP` guard matches `Value`'s and `ValueOn`'s quantifier: without it `Follows` is
vacuous on a menu whose selected option no world values, and one unvalued member (the all-`⊤`
family) would force every e.d. sequence into the class (audit round 1, N1).
Source: lean-deference-072 (msg 68: "closure under argmax composites and differences")
Kind: D
Fidelity: exact (reflection form, universal; valued menus only) -/
def ArgmaxClosed (C : BetClass DP E) : Prop :=
  ∀ (k : ℕ) (M : Menu k), (∀ j, M.O j ∈ C.carrier) → M.Valued DP → ∀ S : ℕ → LUV,
    LUV.MachineThresholdCodeSeq S → Follows DP E M S → S ∈ C.carrier

/-- **A deference class:** closed under ramp-weighting, gap-bets, constants and argmax
composites — the common closure on which all six arrows are domain-preserving.
Source: lean-deference-072; v6 §1.2
Kind: D
Fidelity: exact -/
def IsDeferenceClass (C : BetClass DP E) : Prop :=
  C.RampClosed ∧ C.GapClosed ∧ C.ConstClosed ∧ C.ArgmaxClosed

/-- The universal class is a deference class (every closure output carries a code
certificate).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem univ_isDeferenceClass : (univ DP E).IsDeferenceClass :=
  ⟨fun _ _ _ _ _ _ q => ⟨q.weight_codes, q.product_codes⟩,
    fun _ _ _ hY _ => hY,
    fun _ _ hK _ => hK,
    fun _ _ _ _ _ hS _ => hS⟩

/-- **Intersections of deference classes are deference classes** (T7 closure lemma).
Source: lean-deference-072; mandate T7
Kind: L
Fidelity: exact -/
theorem IsDeferenceClass.inter {C₁ C₂ : BetClass DP E} (h₁ : C₁.IsDeferenceClass)
    (h₂ : C₂.IsDeferenceClass) : (C₁.inter C₂).IsDeferenceClass := by
  obtain ⟨r₁, g₁, c₁, a₁⟩ := h₁
  obtain ⟨r₂, g₂, c₂, a₂⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX wt hwt W XW q
    obtain ⟨hW₁, hXW₁⟩ := r₁ X hX.1 wt hwt W XW q
    obtain ⟨hW₂, hXW₂⟩ := r₂ X hX.2 wt hwt W XW q
    exact ⟨⟨hW₁, hW₂⟩, ⟨hXW₁, hXW₂⟩⟩
  · intro Z hZ Y hY hR
    exact ⟨g₁ Z hZ.1 Y hY hR, g₂ Z hZ.2 Y hY hR⟩
  · intro s K hK hval
    exact ⟨c₁ s K hK hval, c₂ s K hK hval⟩
  · intro k M hM hMv S hS hF
    exact ⟨a₁ k M (fun j => (hM j).1) hMv S hS hF, a₂ k M (fun j => (hM j).2) hMv S hS hF⟩

/-- **The class generated by a base set:** the e.d. sequences lying in every deference class
containing the base — the `sInf` form of "the least deference class containing `base`".
Source: lean-deference-072; mandate T7
Kind: D
Fidelity: exact -/
def generated (DP : DeductiveProcess) (E : Expert DP) (base : Set (ℕ → LUV)) :
    BetClass DP E :=
  ⟨{X | LUV.MachineThresholdCodeSeq X ∧
      ∀ C : BetClass DP E, C.IsDeferenceClass → base ⊆ C.carrier → X ∈ C.carrier},
    fun _ hX => hX.1⟩

/-- The generated class contains its (e.d.) base.
Source: mandate T7
Kind: L
Fidelity: exact -/
theorem subset_generated {base : Set (ℕ → LUV)}
    (hbase : ∀ X ∈ base, LUV.MachineThresholdCodeSeq X) :
    base ⊆ (generated DP E base).carrier :=
  fun X hX => ⟨hbase X hX, fun _ _ hb => hb hX⟩

/-- The generated class is contained in every deference class containing the base (it is the
least one).
Source: mandate T7
Kind: L
Fidelity: exact -/
theorem generated_subset {base : Set (ℕ → LUV)} {C : BetClass DP E}
    (hC : C.IsDeferenceClass) (hb : base ⊆ C.carrier) :
    (generated DP E base).carrier ⊆ C.carrier :=
  fun _ hX => hX.2 C hC hb

/-- **The generated class is a deference class** (T7 closure lemma).
Source: lean-deference-072; mandate T7
Kind: L
Fidelity: exact -/
theorem generated_isDeferenceClass (base : Set (ℕ → LUV)) :
    (generated DP E base).IsDeferenceClass := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX wt hwt W XW q
    exact ⟨⟨q.weight_codes, fun C hC hb => (hC.1 X (hX.2 C hC hb) wt hwt W XW q).1⟩,
      ⟨q.product_codes, fun C hC hb => (hC.1 X (hX.2 C hC hb) wt hwt W XW q).2⟩⟩
  · intro Z hZ Y hY hR
    exact ⟨hY, fun C hC hb => hC.2.1 Z (hZ.2 C hC hb) Y hY hR⟩
  · intro s K hK hval
    exact ⟨hK, fun C hC _ => hC.2.2.1 s K hK hval⟩
  · intro k M hM hMv S hS hF
    exact ⟨hS, fun C hC hb => hC.2.2.2 k M (fun j => (hM j).2 C hC hb) hMv S hS hF⟩

/-! ## Domain-relative notions -/

/-- `Tower` restricted to a class: sources and quotes in `C`.
Source: [[deference-notions]] §Value ("domain-relative"); v6 §5.11
Kind: D
Fidelity: exact -/
def TowerOn (C : BetClass DP E) (P : History) : Prop :=
  ∀ X ∈ C.carrier, ∀ Y ∈ C.carrier, Reflects DP E X Y →
    (fun n => (X n).expect P n) ≈ₙ (fun n => (Y n).expect P n)

/-- `ThresholdIneqAbove` restricted to a class: source, weight and product in `C`.
Source: [[deference-notions]] §Value ("domain-relative")
Kind: D
Fidelity: exact -/
def ThresholdIneqAboveOn (C : BetClass DP E) (P : History) (wt : ℝ → ℝ) (s : ℚ) : Prop :=
  ∀ X ∈ C.carrier, ∀ W ∈ C.carrier, ∀ XW ∈ C.carrier, WeightQuote DP E X wt W XW →
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ))

/-- `ThresholdIneqBelow` restricted to a class.
Source: [[deference-notions]] §Value ("domain-relative")
Kind: D
Fidelity: exact -/
def ThresholdIneqBelowOn (C : BetClass DP E) (P : History) (wt : ℝ → ℝ) (s : ℚ) : Prop :=
  ∀ X ∈ C.carrier, ∀ W ∈ C.carrier, ∀ XW ∈ C.carrier, WeightQuote DP E X wt W XW →
    (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ))

/-- `Value` restricted to a class: menus of members and followers in `C`.
Source: [[deference-notions]] §Value ("Value over menus drawn from a family `D`"); v6 §5.11
Kind: D
Fidelity: exact -/
def ValueOn (C : BetClass DP E) (P : History) : Prop :=
  ∀ (k : ℕ) (M : Menu k), (∀ j, M.O j ∈ C.carrier) → M.Valued DP → ∀ S ∈ C.carrier,
    Follows DP E M S → ∀ i, (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n)

/-- On the universal class, `TowerOn` is `Tower`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem towerOn_univ_iff (P : History) : TowerOn (univ DP E) P ↔ Tower P DP E := by
  constructor
  · intro h X Y hX hY hR
    exact h X hX Y hY hR
  · intro h X hX Y hY hR
    exact h X Y hX hY hR

/-- On the universal class, `ThresholdIneqAboveOn` is `ThresholdIneqAbove` (the codes of `W`,
`XW` are carried by the `WeightQuote`).
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem thresholdIneqAboveOn_univ_iff (P : History) (wt : ℝ → ℝ) (s : ℚ) :
    ThresholdIneqAboveOn (univ DP E) P wt s ↔ ThresholdIneqAbove P DP E wt s := by
  constructor
  · intro h X W XW hX q
    exact h X hX W q.weight_codes XW q.product_codes q
  · intro h X hX W _ XW _ q
    exact h X W XW hX q

/-- On the universal class, `ThresholdIneqBelowOn` is `ThresholdIneqBelow`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem thresholdIneqBelowOn_univ_iff (P : History) (wt : ℝ → ℝ) (s : ℚ) :
    ThresholdIneqBelowOn (univ DP E) P wt s ↔ ThresholdIneqBelow P DP E wt s := by
  constructor
  · intro h X W XW hX q
    exact h X hX W q.weight_codes XW q.product_codes q
  · intro h X hX W _ XW _ q
    exact h X W XW hX q

/-- On the universal class, `ValueOn` is `Value`.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
theorem valueOn_univ_iff (P : History) : ValueOn (univ DP E) P ↔ Value P DP E := by
  constructor
  · intro h k M hval S hS hF i
    exact h k M (fun j => M.codes j) hval S hS hF i
  · intro h k M _ hval S hS hF i
    exact h k M hval S hS hF i

/-- Domain-relative notions are antitone in the class: a smaller domain is a weaker
hypothesis.
Source: [[deference-notions]] §Value ("Value on the admissible domain does not imply
unrestricted Value")
Kind: L
Fidelity: exact -/
theorem TowerOn.mono {C₁ C₂ : BetClass DP E} (h : C₁.carrier ⊆ C₂.carrier) (P : History)
    (hT : TowerOn C₂ P) : TowerOn C₁ P :=
  fun X hX Y hY hR => hT X (h hX) Y (h hY) hR

/-- `ValueOn` is antitone in the class.
Source: [[deference-notions]] §Value
Kind: L
Fidelity: exact -/
theorem ValueOn.mono {C₁ C₂ : BetClass DP E} (h : C₁.carrier ⊆ C₂.carrier) (P : History)
    (hV : ValueOn C₂ P) : ValueOn C₁ P :=
  fun k M hM hval S hS hF i => hV k M (fun j => h (hM j)) hval S (h hS) hF i

end BetClass

/-! ## T8 — a sharp indicator of a price event is not a generable weight (N−) -/

/-- **No expressible feature denotes a hard price indicator, even on `[0,1]`-valued
histories.** For any day `n` and sentence `φ`, no `e : EF` has `e.denote P = 1[1/2 ≤ P n φ]`
for every history `P` with all prices in `[0,1]` (market histories): `EF.denote` is continuous
in the prices (`EF.continuous_denote`, product topology on `History`), and the step is not —
along the `[0,1]`-valued histories `P_k` with `P_k n φ = 1/2 − 1/(2(k+1))` and every other
price `1/2`, `P_k → P₀` (all prices `1/2`) while the indicator jumps from `0` to `1`.
**Scope:** this excludes the *same-day* trade-weight reading — one feature `e` read against
the current history, which is what [[setting-and-notation]] §Market-generable weights means by
a generable weight. It does not show that the step *sequence* `n ↦ 1[1/2 ≤ P n φ]` on a fixed
computable market fails `PGenerableRat P`: `PGenerableRat` admits constant features
(`ratCodeFeature`), so a machine-emittable step sequence read from the ledger at a later day may
well be generable — the deferred-day reading is a `PGenerableRat` question, not settled here
(audit round 1, N4). This is the definitional fact behind the corpus's "a hard indicator is
discontinuous, hence not a legal weight" and why `HardTotalTrust` is a comparison object.
Grade N−: it certifies the encoding excludes the hard weight; it exercises no inductor.
Source: vq-wiki-028 (the one formalizable fragment); [[setting-and-notation]]
§Market-generable weights; [[deference-notions]] §Total Trust
Kind: N-
Fidelity: exact (restricted to `[0,1]`-valued histories, hence stronger than the all-histories
form it replaced in repair round 1) -/
theorem no_generable_hard_indicator (n : ℕ) (φ : Sentence) :
    ¬ ∃ e : EF, ∀ P : History, (∀ m ψ, 0 ≤ P m ψ ∧ P m ψ ≤ 1) →
      e.denote P = if (1 / 2 : ℝ) ≤ P n φ then 1 else 0 := by
  classical
  rintro ⟨e, he⟩
  let P₀ : History := fun _ _ => (1 / 2 : ℝ)
  let Pk : ℕ → History := fun k m ψ =>
    if m = n ∧ ψ = φ then (1 / 2 : ℝ) - 1 / 2 * (1 / ((k : ℝ) + 1)) else (1 / 2 : ℝ)
  have hP₀ : ∀ m ψ, 0 ≤ P₀ m ψ ∧ P₀ m ψ ≤ 1 := fun _ _ => by norm_num [P₀]
  have hPk : ∀ k m ψ, 0 ≤ Pk k m ψ ∧ Pk k m ψ ≤ 1 := by
    intro k m ψ
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := k.cast_nonneg
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    simp only [Pk]
    split_ifs
    · constructor <;> linarith
    · norm_num
  have hlim : Tendsto Pk atTop (𝓝 P₀) := by
    rw [tendsto_pi_nhds]
    intro m
    rw [tendsto_pi_nhds]
    intro ψ
    by_cases h : m = n ∧ ψ = φ
    · have : (fun k => Pk k m ψ) =
          fun k : ℕ => (1 / 2 : ℝ) - 1 / 2 * (1 / ((k : ℝ) + 1)) := by
        funext k
        simp [Pk, h]
      rw [this]
      have h0 : P₀ m ψ = (1 / 2 : ℝ) - 1 / 2 * 0 := by simp [P₀]
      rw [h0]
      exact tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
    · have : (fun k => Pk k m ψ) = fun _ : ℕ => (1 / 2 : ℝ) := by
        funext k
        simp [Pk, h]
      rw [this]
      exact tendsto_const_nhds
  have hcont : Tendsto (fun k => e.denote (Pk k)) atTop (𝓝 (e.denote P₀)) :=
    (e.continuous_denote.tendsto P₀).comp hlim
  have hval0 : e.denote P₀ = 1 := by
    rw [he P₀ hP₀]
    simp [P₀]
  have hvalk : ∀ k, e.denote (Pk k) = 0 := by
    intro k
    rw [he (Pk k) (hPk k)]
    have hlt : Pk k n φ < 1 / 2 := by
      simp only [Pk, and_self, if_true]
      have : (0 : ℝ) < 1 / 2 * (1 / ((k : ℝ) + 1)) := by positivity
      linarith
    rw [if_neg (not_le.mpr hlt)]
  rw [hval0] at hcont
  have h0 : Tendsto (fun k => e.denote (Pk k)) atTop (𝓝 0) := by
    simp only [hvalk]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hcont h0)

end

end Cleanroom.Found.DefLattice
