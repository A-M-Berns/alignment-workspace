import Cleanroom.Lit.LitDdbFacts.Ladder
import Cleanroom.Lit.LitDdbFacts.Geometry
import Cleanroom.Lit.LitDdbFacts.Convexity
import Cleanroom.Lit.LitDdbFacts.DutchBook
import Cleanroom.Lit.LitDdbFacts.Hereditary
import Cleanroom.Lit.LitDdbFacts.Collected

/-!
# Witnesses on two, three and four worlds

Package `lit-ddb-facts`. The immodest frame with duplicate rows `dup3` (Targets 1, 3, 5: all six
principles hold for the uniform deferrer, none for `(3/5, 1/5, 1/5)`); `nullSelf`, the frame on
which every row totally trusts the frame yet row 0 has a null self-cell (Corollary 4.5 is false
under the guarded `Frame.ModestlyInformed`); `swap2` from the frames audit (validates NR-vac but
not Fact 4.3's hull condition, so Fact 4.3 needs NR-str); `nonHered4`, on which New Reflection is
not hereditary (fn 56's exception, no example in DDB); Figure 2's Trust failure (audit probe,
copied); Fact 2.1's fixed-option Dutch book; and the biconvex formulation on Figure 3 and Fact
2.1; after audit round 1: the lexicographic biconvex set `lexHalf` (findings F5, in `ℝ^W` and inside
the simplex), the validation witnesses for Facts 4.2/4.3 (`dup3`, Figure 2), Theorem 5.1's six
bullets on Figure 3 and Fact 2.1, a non-trivial positive-access instance, and the refutation of
each new predicate of record on a concrete frame (audit probes P1, P3, copied). Figure 5's `F₁`
and the "`F₂` is totally trusted by no `π`" claim are in `ExamplesFig5.lean`.
Every number is DDB's or the mandate's; proofs are `norm_num` on explicit rationals.
-/

namespace Cleanroom.Lit.LitDdbFacts.Examples

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbFacts

noncomputable section

/-! ## Convex-combination helpers (general carrier) -/

/-- A convex combination of two points of a set lies in its hull (any carrier).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_hull_of_comb2 {W : Type} {s : Set (W → ℝ)} {x y z : W → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hz : z = a • x + b • y) :
    z ∈ convexHull ℝ s := by
  rw [hz]
  exact (convex_convexHull ℝ s) (subset_convexHull ℝ s hx) (subset_convexHull ℝ s hy) ha hb hab

/-- A convex combination of three points of a set lies in its hull.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_hull_of_comb3 {W : Type} {s : Set (W → ℝ)} {x y z v : W → ℝ} (hx : x ∈ s)
    (hy : y ∈ s) (hz : z ∈ s) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) (hv : v = a • x + b • y + c • z) : v ∈ convexHull ℝ s := by
  rw [hv]
  rcases (add_nonneg ha hb).lt_or_eq with hab | hab
  · have h1 : (a / (a + b)) • x + (b / (a + b)) • y ∈ convexHull ℝ s :=
      (convex_convexHull ℝ s) (subset_convexHull ℝ s hx) (subset_convexHull ℝ s hy)
        (div_nonneg ha hab.le) (div_nonneg hb hab.le) (by rw [← add_div, div_self hab.ne'])
    have h2 := (convex_convexHull ℝ s) h1 (subset_convexHull ℝ s hz) hab.le hc habc
    convert h2 using 1
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hab.ne', mul_div_cancel₀ _ hab.ne']
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc1 : c = 1 := by linarith
    rw [ha0, hb0, hc1, zero_smul, zero_smul, one_smul, zero_add, zero_add]
    exact subset_convexHull ℝ s hz

/-- The uniform distribution on three worlds is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π5_mem : π5 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Target 1/5 witness: an immodest frame with duplicate rows -/

/-- Rows `(½, ½, 0)`, `(½, ½, 0)`, `(0, 0, 1)`: immodest, with a non-Dirac candidate carried by
two worlds (Remark 7.2.1 exercised).
Source: mandate Target 1 (witness)
Kind: D
Fidelity: n/a -/
def dup3 : Frame (Fin 3) :=
  mk3 ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `dup3`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_P : dup3.P 0 = ![1 / 2, 1 / 2, 0] ∧ dup3.P 1 = ![1 / 2, 1 / 2, 0] ∧
    dup3.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- The two distinct rows of `dup3` differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_ne : (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ≠ ![0, 0, 1] := by
  intro h
  have := congrFun h 0
  norm_num at this

/-- The cells of `dup3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_cell : dup3.cell ![1 / 2, 1 / 2, 0] = {0, 1} ∧ dup3.cell ![0, 0, 1] = {2} := by
  constructor
  · ext w; fin_cases w <;> simp [Frame.mem_cell, dup3_P, dup3_ne.symm]
  · ext w; fin_cases w <;> simp [Frame.mem_cell, dup3_P, dup3_ne]

/-- `dup3` is immodest.
Source: mandate Target 1 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_immodest : dup3.Immodest := by
  intro w
  obtain ⟨hc0, hc2⟩ := dup3_cell
  fin_cases w
  · show dup3.selfMass (dup3.P 0) = 1
    rw [Frame.selfMass, dup3_P.1, hc0, mass, sum_pair (by simp)]
    norm_num
  · show dup3.selfMass (dup3.P 1) = 1
    rw [Frame.selfMass, dup3_P.2.1, hc0, mass, sum_pair (by simp)]
    norm_num
  · show dup3.selfMass (dup3.P 2) = 1
    rw [Frame.selfMass, dup3_P.2.2, hc2, mass, sum_singleton]
    norm_num [vec3_two]

/-- The uniform deferrer's masses on `dup3`'s cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_mass : mass π5 {0, 1} = 2 / 3 ∧ mass π5 {2} = 1 / 3 := by
  constructor
  · rw [mass, sum_pair (by simp)]; norm_num [π5]
  · rw [mass, sum_singleton]; norm_num [π5, vec3_two]

/-- **Targets 1, 3, 5 (positive side).** The uniform deferrer reflects `dup3`.
Source: mandate Target 1 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_reflects : Reflects π5 dup3 := by
  obtain ⟨hc0, hc2⟩ := dup3_cell
  obtain ⟨hm0, hm2⟩ := dup3_mass
  intro ρ hρ w
  obtain ⟨v, _, rfl⟩ := Frame.mem_cands.1 hρ
  fin_cases v
  · show π5 w * ind (dup3.cell (dup3.P 0)) w = mass π5 (dup3.cell (dup3.P 0)) * dup3.P 0 w
    rw [dup3_P.1, hc0, hm0]
    fin_cases w <;> norm_num [ind, π5, vec3_two, Fin.ext_iff]
  · show π5 w * ind (dup3.cell (dup3.P 1)) w = mass π5 (dup3.cell (dup3.P 1)) * dup3.P 1 w
    rw [dup3_P.2.1, hc0, hm0]
    fin_cases w <;> norm_num [ind, π5, vec3_two, Fin.ext_iff]
  · show π5 w * ind (dup3.cell (dup3.P 2)) w = mass π5 (dup3.cell (dup3.P 2)) * dup3.P 2 w
    rw [dup3_P.2.2, hc2, hm2]
    fin_cases w <;> norm_num [ind, π5, vec3_two, Fin.ext_iff]

/-- **Target 5, the collapse exercised.** On `dup3` the uniform deferrer satisfies all six
principles (from Reflection through `tfae_immodestFrame`).
Source: [[Deference Done Better]] §5 l. 390; mandate Target 5 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_all : Reflects π5 dup3 ∧ NewReflects π5 dup3 ∧ SimpleTrust π5 dup3 ∧
    Trust π5 dup3 ∧ TotalTrust π5 dup3 ∧ Value π5 dup3 := by
  have t := tfae_immodestFrame π5_mem dup3_immodest
  exact ⟨dup3_reflects, (t.out 0 1).1 dup3_reflects, (t.out 0 2).1 dup3_reflects,
    (t.out 0 3).1 dup3_reflects, (t.out 0 4).1 dup3_reflects, (t.out 0 5).1 dup3_reflects⟩

/-- The deferrer `(3/5, 1/5, 1/5)` on `dup3`.
Source: mandate Target 5 (negative witness)
Kind: D
Fidelity: n/a -/
def πneg : Fin 3 → ℝ := ![3 / 5, 1 / 5, 1 / 5]

/-- `πneg` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πneg_mem : πneg ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `[P({w₁}) ≥ ½] = {w₀, w₁}` on `dup3` (the mandate's "`q = {2}`" is this world in 1-based
numbering).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_probEvent : dup3.probEvent {1} (1 / 2) = {0, 1} := by
  ext w
  fin_cases w <;> simp [Frame.probEvent, mass, dup3_P, vec3_two, Fin.ext_iff] <;> norm_num

/-- **Target 5 (negative side).** `(3/5, 1/5, 1/5)` fails Simple Trust on `dup3` at
`q = {w₁}`, `t = ½`: the event is `{w₀, w₁}` of mass `4/5`, but `πneg(w₁) = 1/5 < ½ · 4/5`.
Source: mandate Target 5 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_not_simpleTrust : ¬ SimpleTrust πneg dup3 := by
  intro h
  have hev := dup3_probEvent
  have := h {1} (1 / 2) (by rw [hev, mass, sum_pair (by simp)]; norm_num [πneg])
  have hi : ({1} : Finset (Fin 3)) ∩ {0, 1} = {1} := by ext w; fin_cases w <;> simp
  rw [hev, hi, mass, sum_pair (by simp), mass, sum_singleton] at this
  norm_num [πneg] at this

/-- On `dup3`, `(3/5, 1/5, 1/5)` satisfies none of the six principles (the collapse run
backwards from the Simple Trust failure).
Source: mandate Target 5 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_none : ¬ Reflects πneg dup3 ∧ ¬ NewReflects πneg dup3 ∧ ¬ SimpleTrust πneg dup3 ∧
    ¬ Trust πneg dup3 ∧ ¬ TotalTrust πneg dup3 ∧ ¬ Value πneg dup3 := by
  have t := tfae_immodestFrame πneg_mem dup3_immodest
  have h := dup3_not_simpleTrust
  exact ⟨fun h' => h ((t.out 0 2).1 h'), fun h' => h ((t.out 1 2).1 h'), h,
    fun h' => h ((t.out 3 2).1 h'), fun h' => h ((t.out 4 2).1 h'), fun h' => h ((t.out 5 2).1 h')⟩

/-! ## Target 12 witness: Corollary 4.5 fails under the guarded predicate -/

/-- Rows `(0, ½, ½)`, `(0, 1, 0)`, `(0, 0, 1)`: row 0 is the midpoint of the two immodest Diracs
it leaves open, and gives itself probability `0`.
Source: mandate Target 12 (finding of record)
Kind: D
Fidelity: n/a -/
def nullSelf : Frame (Fin 3) :=
  mk3 ![0, 1 / 2, 1 / 2] ![0, 1, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `nullSelf`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullSelf_P : nullSelf.P 0 = ![0, 1 / 2, 1 / 2] ∧ nullSelf.P 1 = ![0, 1, 0] ∧
    nullSelf.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- `nullSelf`'s rows are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullSelf_ne : (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) ≠ ![0, 1, 0] ∧
    (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) ≠ ![0, 0, 1] ∧ (![0, 1, 0] : Fin 3 → ℝ) ≠ ![0, 0, 1] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    · have := congrFun h 1; norm_num at this

/-- The cells of `nullSelf` are singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullSelf_cell : nullSelf.cell ![0, 1 / 2, 1 / 2] = {0} ∧ nullSelf.cell ![0, 1, 0] = {1} ∧
    nullSelf.cell ![0, 0, 1] = {2} := by
  obtain ⟨h01, h02, h12⟩ := nullSelf_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w; fin_cases w <;> simp [Frame.mem_cell, nullSelf_P, h01, h02, h12, h01.symm, h02.symm, h12.symm]

/-- Self-cell masses on `nullSelf`: `0`, `1`, `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullSelf_selfMass : nullSelf.selfMass (nullSelf.P 0) = 0 ∧
    nullSelf.selfMass (nullSelf.P 1) = 1 ∧ nullSelf.selfMass (nullSelf.P 2) = 1 := by
  obtain ⟨hc0, hc1, hc2⟩ := nullSelf_cell
  refine ⟨?_, ?_, ?_⟩
  · rw [Frame.selfMass, nullSelf_P.1, hc0, mass, sum_singleton]; norm_num
  · rw [Frame.selfMass, nullSelf_P.2.1, hc1, mass, sum_singleton]; norm_num
  · rw [Frame.selfMass, nullSelf_P.2.2, hc2, mass, sum_singleton]; norm_num [vec3_two]

/-- Row 0 of `nullSelf` is not modestly informed in the *guarded* sense (its self-cell is null).
Source: mandate Target 12 (finding of record)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem nullSelf_not_modestlyInformed : ¬ nullSelf.ModestlyInformed (nullSelf.P 0) := fun h => by
  obtain ⟨h1, _⟩ := h
  rw [nullSelf_selfMass.1] at h1
  exact lt_irrefl _ h1

/-- The candidates of `nullSelf`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullSelf_cands : nullSelf.cands (nullSelf.P 0) = {nullSelf.P 1, nullSelf.P 2} ∧
    nullSelf.cands (nullSelf.P 1) = {nullSelf.P 1} ∧
    nullSelf.cands (nullSelf.P 2) = {nullSelf.P 2} := by
  refine ⟨?_, ?_, ?_⟩
  · ext σ
    rw [Frame.mem_cands]
    constructor
    · rintro ⟨w, hw, rfl⟩
      fin_cases w
      · exfalso; norm_num [nullSelf_P] at hw
      · simp
      · simp
    · intro hσ
      simp only [mem_insert, mem_singleton] at hσ
      rcases hσ with rfl | rfl
      · exact ⟨1, by norm_num [nullSelf_P], rfl⟩
      · exact ⟨2, by norm_num [nullSelf_P, vec3_two], rfl⟩
  · ext σ
    rw [Frame.mem_cands, mem_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      fin_cases w
      · exfalso; norm_num [nullSelf_P] at hw
      · rfl
      · exfalso; norm_num [nullSelf_P, vec3_two] at hw
    · rintro rfl
      exact ⟨1, by norm_num [nullSelf_P], rfl⟩
  · ext σ
    rw [Frame.mem_cands, mem_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      fin_cases w
      · exfalso; norm_num [nullSelf_P] at hw
      · exfalso; norm_num [nullSelf_P] at hw
      · rfl
    · rintro rfl
      exact ⟨2, by norm_num [nullSelf_P, vec3_two], rfl⟩

/-- **Target 12, the finding of record.** `nullSelf` validates Total Trust (every row totally
trusts the frame, via Corollary 4.5 in its unguarded form) although row 0 is not modestly
informed in the guarded sense — so Corollary 4.5 (⇒) with `Frame.ModestlyInformed` is false.
Source: [[Deference Done Better]] §4 l. 363, fn 61; mandate Target 12
Kind: N+
Fidelity: n/a (refutes the guarded reading of Corollary 4.5)
Hyps: (a) none -/
theorem nullSelf_validates_totalTrust_not_modestlyInformed :
    nullSelf.Validates TotalTrust ∧ ¬ nullSelf.ModestlyInformed (nullSelf.P 0) := by
  refine ⟨?_, nullSelf_not_modestlyInformed⟩
  rw [validates_totalTrust_iff]
  obtain ⟨hs0, hs1, hs2⟩ := nullSelf_selfMass
  obtain ⟨hcd0, hcd1, hcd2⟩ := nullSelf_cands
  obtain ⟨h01, h02, h12⟩ := nullSelf_ne
  intro i
  fin_cases i
  · show ModestlyInformedU nullSelf (nullSelf.P 0)
    unfold ModestlyInformedU
    have hcm : nullSelf.candsMinus (nullSelf.P 0) = {nullSelf.P 1, nullSelf.P 2} := by
      rw [Frame.candsMinus, hcd0]
      apply erase_eq_of_notMem
      simp only [mem_insert, mem_singleton, nullSelf_P]
      exact fun h => h.elim h01 h02
    rw [hcm]
    exact mem_hull_of_comb2 (x := nullSelf.P 1) (y := nullSelf.P 2)
      (Set.mem_insert_of_mem _ (by simp)) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [nullSelf_P, vec3_two])
  · show ModestlyInformedU nullSelf (nullSelf.P 1)
    unfold ModestlyInformedU
    rw [(informed_eq_self_iff nullSelf (nullSelf.P_mem 1)).2 hs1]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)
  · show ModestlyInformedU nullSelf (nullSelf.P 2)
    unfold ModestlyInformedU
    rw [(informed_eq_self_iff nullSelf (nullSelf.P_mem 2)).2 hs2]
    exact subset_convexHull ℝ _ (Set.mem_insert _ _)

/-! ## Target 11 witness: Fact 4.3 needs NR-str (`swap2`, from the frames audit) -/

/-- The swapped-certainty frame `(0, 1)`, `(1, 0)` (from `lit-ddb-frames`' adversarial audit,
`audit-r1-probes/Vacuity.lean`, copied).
Source: [[lit-ddb-frames-audit-r1-adversarial]] probe 2
Kind: D
Fidelity: n/a -/
def swap2 : Frame (Fin 2) :=
  mk2 ![0, 1] ![1, 0]
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))
    (simplex2 _ _ (by norm_num) (by norm_num) (by norm_num))

/-- `swap2`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem swap2_P : swap2.P 0 = ![0, 1] ∧ swap2.P 1 = ![1, 0] := ⟨rfl, rfl⟩

/-- `swap2`'s rows differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem swap2_ne : swap2.P 0 ≠ swap2.P 1 := by
  intro h
  have := congrFun h 0
  rw [swap2_P.1, swap2_P.2] at this
  norm_num at this

/-- Both self-cells of `swap2` are null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem swap2_selfMass : swap2.selfMass (swap2.P 0) = 0 ∧ swap2.selfMass (swap2.P 1) = 0 := by
  obtain ⟨hc0, hc1⟩ := cell_of_ne swap2 swap2_ne
  constructor
  · rw [Frame.selfMass, hc0]; norm_num [mass, swap2_P.1]
  · rw [Frame.selfMass, hc1]; norm_num [mass, swap2_P.2]

/-- The candidates of `swap2`'s rows: each row's only candidate is the other row.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem swap2_cands : swap2.cands (swap2.P 0) = {swap2.P 1} ∧
    swap2.cands (swap2.P 1) = {swap2.P 0} := by
  constructor <;>
  · ext σ
    rw [Frame.mem_cands, mem_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      fin_cases w <;> simp_all [swap2_P]
    · rintro rfl
      first
        | exact ⟨1, by norm_num [swap2_P], rfl⟩
        | exact ⟨0, by norm_num [swap2_P], rfl⟩

/-- **Target 11 witness.** `swap2` validates New Reflection in the *vacuous* reading (every
candidate has a null self-cell) yet fails Fact 4.3's hull condition: `P_0 = δ_1` is not in
`convexHull {P̂_1} = {0}`. So Fact 4.3 is false for NR-vac and needs NR-str.
Source: [[Deference Done Better]] §4 l. 347 (Fact 4.3); [[lit-ddb-frames-audit-r1-adversarial]]
probe 2
Kind: N+
Fidelity: n/a (refutes the NR-vac reading of Fact 4.3)
Hyps: (a) none -/
theorem swap2_validates_newReflectsVac_not_hull :
    swap2.Validates NewReflectsVac ∧
      ¬ ∀ i, swap2.P i ∈ convexHull ℝ (↑((swap2.cands (swap2.P i)).image swap2.informed) :
        Set (Fin 2 → ℝ)) := by
  obtain ⟨hs0, hs1⟩ := swap2_selfMass
  obtain ⟨hcd0, hcd1⟩ := swap2_cands
  constructor
  · intro i ρ hρ hpos
    fin_cases i
    · change ρ ∈ swap2.cands (swap2.P 0) at hρ
      rw [hcd0, mem_singleton] at hρ
      rw [hρ, hs1] at hpos
      exact absurd hpos (lt_irrefl _)
    · change ρ ∈ swap2.cands (swap2.P 1) at hρ
      rw [hcd1, mem_singleton] at hρ
      rw [hρ, hs0] at hpos
      exact absurd hpos (lt_irrefl _)
  · intro H
    have h := H 0
    rw [hcd0, image_singleton, (informed_eq_zero_iff swap2 (swap2.P_nonneg 1)).2 hs1,
      coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at h
    have := congrFun h 1
    rw [swap2_P.1] at this
    norm_num at this

/-! ## Target 14(ii) witness: New Reflection is not hereditary -/

/-- A four-world frame from its rows.
Source: none: infrastructure (Target 14)
Kind: D
Fidelity: n/a -/
def mk4 (r₀ r₁ r₂ r₃ : Fin 4 → ℝ) (h₀ : r₀ ∈ stdSimplex ℝ (Fin 4))
    (h₁ : r₁ ∈ stdSimplex ℝ (Fin 4)) (h₂ : r₂ ∈ stdSimplex ℝ (Fin 4))
    (h₃ : r₃ ∈ stdSimplex ℝ (Fin 4)) : Frame (Fin 4) where
  P := ![r₀, r₁, r₂, r₃]
  P_mem := fun w => by fin_cases w <;> assumption

/-- Third and fourth coordinates of a four-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_two (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := rfl

/-- Fourth coordinate of a four-vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec4_three (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := rfl

/-- A nonnegative quadruple summing to one is a distribution on four worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem simplex4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 1) : (![a, b, c, d] : Fin 4 → ℝ) ∈ stdSimplex ℝ (Fin 4) :=
  ⟨fun x => by fin_cases x <;> simp [ha, hb, hc, hd],
    by simp [Fin.sum_univ_four, vec4_two, vec4_three, h]⟩

/-- Rows `P₀ = (½, 0, ½, 0)`, `P₁ = (0, ½, 0, ½)`, `P₂ = P₃ = (0, 0, ½, ½)`.
Source: mandate Target 14(ii) (witness; no example in DDB)
Kind: D
Fidelity: n/a -/
def nonHered4 : Frame (Fin 4) :=
  mk4 ![1 / 2, 0, 1 / 2, 0] ![0, 1 / 2, 0, 1 / 2] ![0, 0, 1 / 2, 1 / 2] ![0, 0, 1 / 2, 1 / 2]
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- `nonHered4`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nonHered4_P : nonHered4.P 0 = ![1 / 2, 0, 1 / 2, 0] ∧
    nonHered4.P 1 = ![0, 1 / 2, 0, 1 / 2] ∧ nonHered4.P 2 = ![0, 0, 1 / 2, 1 / 2] ∧
    nonHered4.P 3 = ![0, 0, 1 / 2, 1 / 2] := ⟨rfl, rfl, rfl, rfl⟩

/-- The three distinct rows of `nonHered4` differ pairwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nonHered4_ne : (![1 / 2, 0, 1 / 2, 0] : Fin 4 → ℝ) ≠ ![0, 1 / 2, 0, 1 / 2] ∧
    (![1 / 2, 0, 1 / 2, 0] : Fin 4 → ℝ) ≠ ![0, 0, 1 / 2, 1 / 2] ∧
    (![0, 1 / 2, 0, 1 / 2] : Fin 4 → ℝ) ≠ ![0, 0, 1 / 2, 1 / 2] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 1; norm_num at this

/-- The cells of `nonHered4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nonHered4_cell : nonHered4.cell ![1 / 2, 0, 1 / 2, 0] = {0} ∧
    nonHered4.cell ![0, 1 / 2, 0, 1 / 2] = {1} ∧
    nonHered4.cell ![0, 0, 1 / 2, 1 / 2] = {2, 3} := by
  obtain ⟨h01, h02, h12⟩ := nonHered4_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w
      fin_cases w <;>
        simp [Frame.mem_cell, nonHered4_P, h01, h02, h12, h01.symm, h02.symm, h12.symm]

/-- The deferrer `π = (½, ½, 0, 0)` on `nonHered4`.
Source: mandate Target 14(ii)
Kind: D
Fidelity: n/a -/
def π4 : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

/-- `π4` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π4_mem : π4 ∈ stdSimplex ℝ (Fin 4) :=
  simplex4 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `π4` new-reflects `nonHered4`: its candidates `P₀`, `P₁` have singleton cells with
self-mass `½`, and the identity holds at each world.
Source: mandate Target 14(ii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem nonHered4_newReflects : NewReflects π4 nonHered4 := by
  obtain ⟨hc0, hc1, _⟩ := nonHered4_cell
  intro ρ hρ
  obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hρ
  fin_cases v
  · show 0 < nonHered4.selfMass (nonHered4.P 0) ∧ ∀ w, π4 w * ind (nonHered4.cell (nonHered4.P 0)) w *
      nonHered4.selfMass (nonHered4.P 0) = mass π4 (nonHered4.cell (nonHered4.P 0)) * nonHered4.P 0 w *
      ind (nonHered4.cell (nonHered4.P 0)) w
    rw [Frame.selfMass, nonHered4_P.1, hc0, mass, sum_singleton, mass, sum_singleton]
    refine ⟨by norm_num, fun w => ?_⟩
    fin_cases w <;> norm_num [ind, π4, vec4_two, vec4_three, Fin.ext_iff]
  · show 0 < nonHered4.selfMass (nonHered4.P 1) ∧ ∀ w, π4 w * ind (nonHered4.cell (nonHered4.P 1)) w *
      nonHered4.selfMass (nonHered4.P 1) = mass π4 (nonHered4.cell (nonHered4.P 1)) * nonHered4.P 1 w *
      ind (nonHered4.cell (nonHered4.P 1)) w
    rw [Frame.selfMass, nonHered4_P.2.1, hc1, mass, sum_singleton, mass, sum_singleton]
    refine ⟨by norm_num, fun w => ?_⟩
    fin_cases w <;> norm_num [ind, π4, vec4_two, vec4_three, Fin.ext_iff]
  · exfalso; norm_num [π4, vec4_two] at hv
  · exfalso; norm_num [π4, vec4_three] at hv

/-- **Target 14(ii).** New Reflection is not hereditary: `π4` new-reflects `nonHered4`, `P₀` is a
candidate of `π4`, but `P₀` does not new-reflect the frame even in the vacuous reading — its
candidate `P₂` has cell `{w₂, w₃}` and self-mass `1`, yet `P₀(· | P = P₂) = δ_{w₂} ≠ P̂₂`
(at `w₂`: `½ · 1 ≠ ½ · ½`). Refutes both readings at once; fn 56's exception, with no example
in DDB (the inventory's guess, Figure 2's `P_a`, does new-reflect).
Source: [[Deference Done Better]] fn 56; item 071
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem nonHered4_not_hereditary : NewReflects π4 nonHered4 ∧ nonHered4.P 0 ∈ nonHered4.cands π4 ∧
    ¬ NewReflectsVac (nonHered4.P 0) nonHered4 ∧ ¬ NewReflects (nonHered4.P 0) nonHered4 := by
  obtain ⟨_, _, hc2⟩ := nonHered4_cell
  have hvac : ¬ NewReflectsVac (nonHered4.P 0) nonHered4 := by
    intro h
    have hmem : nonHered4.P 2 ∈ nonHered4.cands (nonHered4.P 0) :=
      nonHered4.P_mem_cands (by norm_num [nonHered4_P, vec4_two])
    have hpos : 0 < nonHered4.selfMass (nonHered4.P 2) := by
      rw [Frame.selfMass, nonHered4_P.2.2.1, hc2, mass, sum_pair (by simp)]
      norm_num [vec4_two, vec4_three]
    have := h _ hmem hpos 2
    rw [Frame.selfMass, nonHered4_P.2.2.1, hc2, mass, sum_pair (by simp), mass,
      sum_pair (by simp)] at this
    norm_num [ind, nonHered4_P, vec4_two, vec4_three] at this
  refine ⟨nonHered4_newReflects, nonHered4.P_mem_cands (by norm_num [π4]), hvac,
    fun h => hvac h.vac⟩

/-! ## Target 6 witness: New Reflection without Trust on Figure 2 (audit probe, copied) -/

/-- `[P({a}) ≥ 4/5] = {b}` on Figure 2.
Source: [[lit-ddb-frames-audit-r1-adversarial]] probe 3 (copied)
Kind: L
Fidelity: n/a -/
theorem fig2_probEvent : fig2.probEvent {0} (4 / 5) = {1} := by
  ext w
  fin_cases w <;> simp [Frame.probEvent, mass, fig2_P0, fig2_P1] <;> norm_num

/-- `[P({a} | W) ≥ 4/5] = {b}` on Figure 2.
Source: [[lit-ddb-frames-audit-r1-adversarial]] probe 3 (copied)
Kind: L
Fidelity: n/a -/
theorem fig2_condProbEvent : fig2.condProbEvent {0} univ (4 / 5) = {1} := by
  ext w
  fin_cases w <;>
    simp [Frame.condProbEvent, mass, Fin.sum_univ_two, fig2_P0, fig2_P1] <;> norm_num

/-- Figure 2's deferrer does not trust the frame (`q = {a}`, `p = W`, `t = 4/5`).
Source: [[lit-ddb-frames-audit-r1-adversarial]] probe 3 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig2_not_trust : ¬ Trust half fig2 := by
  intro h
  have hint : ({0} : Finset (Fin 2)) ∩ (univ ∩ {1}) = ∅ := by ext w; fin_cases w <;> simp
  have := h {0} univ (4 / 5) (by rw [fig2_condProbEvent, univ_inter]; norm_num [mass, half])
  rw [fig2_condProbEvent, hint, univ_inter] at this
  norm_num [mass, half] at this

/-- **Target 6(b), strictness.** New Reflection does not imply Trust: Figure 2.
Source: [[Deference Done Better]] §1 l. 104 (Figure 2), §2 l. 182
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig2_newReflects_not_trust : NewReflects half fig2 ∧ ¬ Trust half fig2 :=
  ⟨fig2_newReflects, fig2_not_trust⟩

/-! ## Target 9 witness: Fact 2.1's fixed-option Dutch book -/

/-- The before-option of Fact 2.1's book: `−O₁ − 1/10`.
Source: mandate Target 9 (witness)
Kind: D
Fidelity: n/a -/
def bookO : Fin 3 → ℝ := fun w => -O1 w - 1 / 10

/-- **Target 9 witness (N+).** On Fact 2.1's frame, `𝒪₁ = {0, −O₁ − 1/10}` (with `−O₁ − 1/10`
`π`-optimal: `E_π = 0.26 − 0.1 > 0`), `𝒪₂ = {0, O₁}`, the strategy "take `O₁` everywhere" is
recommended, and the combined payoff is `−1/10` at every world.
Source: [[Deference Done Better]] §2 l. 161 (Fact 2.1), fn 21; mandate Target 9
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fact21_book :
    FixedOptionBook π21 fact21 {fun _ => 0, bookO} {fun _ => 0, O1} bookO (fun _ => O1)
      SureLoss := by
  obtain ⟨h0, h1, h2⟩ := fact21_P
  obtain ⟨e0, e1, e2, eπ⟩ := fact21_E_O1
  have hEb : E π21 bookO = 4 / 25 := by
    norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, π21, bookO, O1]
  refine ⟨by simp, by simp, by simp, ?_, ⟨⟨fun w => by simp, fun _ _ _ => rfl⟩, ?_⟩, ?_⟩
  · intro o ho
    simp only [mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · rw [E_const π21_mem, hEb]; norm_num
    · exact le_rfl
  · intro w o ho
    simp only [mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl
    · rw [E_const (fact21.P_mem w)]
      change (0 : ℝ) ≤ E (fact21.P w) O1
      fin_cases w
      · change (0 : ℝ) ≤ E (fact21.P 0) O1
        rw [e0]; norm_num
      · change (0 : ℝ) ≤ E (fact21.P 1) O1
        rw [e1]; norm_num
      · change (0 : ℝ) ≤ E (fact21.P 2) O1
        rw [e2]; norm_num
    · exact le_rfl
  · intro w
    simp only [bookO]
    linarith

/-! ## Target 7 witnesses: the biconvex formulation on Figure 3 and Fact 2.1 -/

/-- The open half-plane `{ρ : ½ < ρ(a)}` is biconvex.
Source: mandate Target 7 (witness)
Kind: L
Fidelity: n/a -/
theorem biconvex_halfPlane : Biconvex {ρ : Fin 2 → ℝ | 1 / 2 < ρ 0} := by
  have hlin : IsLinearMap ℝ (fun ρ : Fin 2 → ℝ => ρ 0) := ⟨fun a b => rfl, fun c a => rfl⟩
  refine ⟨convex_halfSpace_gt hlin _, ?_⟩
  have : {ρ : Fin 2 → ℝ | 1 / 2 < ρ 0}ᶜ = {ρ : Fin 2 → ℝ | ρ 0 ≤ 1 / 2} := by
    ext ρ; simp [not_lt]
  rw [this]
  exact convex_halfSpace_le hlin _

/-- **Target 7(ii) witness (N+).** On Figure 3, conditioning on the expert lying in the
biconvex `{ρ : ½ < ρ(a)}` (which holds exactly at `a`) yields `δ_a`, which lies in the set; and
the biconvex formulation holds outright (from `totalTrust_iff_totalTrustBiconvex`).
Source: [[Deference Done Better]] §2 l. 227; mandate Target 7
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig3_totalTrustBiconvex :
    TotalTrustBiconvex half fig3 ∧ CondIn half fig3 {ρ : Fin 2 → ℝ | 1 / 2 < ρ 0} := by
  refine ⟨(totalTrust_iff_totalTrustBiconvex half_mem).1 fig3_totalTrust_value.1, ?_⟩
  have hev : memEvent fig3 {ρ : Fin 2 → ℝ | 1 / 2 < ρ 0} = {0} := by
    ext w; fin_cases w <;> simp [mem_memEvent, fig3_P0, fig3_P1] <;> norm_num
  refine ⟨![1, 0], by norm_num, fun w => ?_⟩
  rw [hev, mass, sum_singleton]
  fin_cases w <;> norm_num [ind, half]

/-- **Target 7(ii) witness (N+, negative).** On Fact 2.1, the biconvex formulation fails directly
at `B = {ρ : 0 ≤ E_ρ(O₁)}`: `[P ∈ B] = W`, so the conditional is `π` itself, and
`E_π(O₁) = −0.26 < 0`.
Source: [[Deference Done Better]] §2 l. 206, Fact 2.1; mandate Target 7
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fact21_not_totalTrustBiconvex : ¬ TotalTrustBiconvex π21 fact21 := by
  intro h
  obtain ⟨e0, e1, e2, eπ⟩ := fact21_E_O1
  have hev : memEvent fact21 {ρ : Fin 3 → ℝ | 0 ≤ E ρ O1} = univ := by
    ext w
    fin_cases w
    · simp [mem_memEvent, e0]; norm_num
    · simp [mem_memEvent, e1]; norm_num
    · show (2 : Fin 3) ∈ memEvent fact21 {ρ : Fin 3 → ℝ | 0 ≤ E ρ O1} ↔ (2 : Fin 3) ∈ univ
      simp [mem_memEvent, e2]; norm_num
  have hpos : 0 < mass π21 (memEvent fact21 {ρ : Fin 3 → ℝ | 0 ≤ E ρ O1}) := by
    rw [hev, mass_univ π21_mem]; exact one_pos
  obtain ⟨σ, hσ, hid⟩ := h _ (biconvex_halfSpace O1 0) hpos
  have hσπ : σ = π21 := by
    funext w
    have := hid w
    rw [hev, mass_univ π21_mem, one_mul] at this
    rw [← this]
    simp [ind]
  rw [hσπ, Set.mem_setOf_eq, eπ] at hσ
  norm_num at hσ

/-! ## Findings F5 witness: a biconvex set that is not a half-space -/

/-- The **lexicographic half-space** with pivot coordinates `i, j` and threshold `c`:
`{x : 0 < x i ∨ (x i = 0 ∧ c ≤ x j)}`. Biconvex for every `i, j, c`; for `i ≠ j` it is neither
a closed nor an open half-space `{ρ : t ≤ E_ρ(X)}` / `{ρ : t < E_ρ(X)}`, although its
topological boundary is the hyperplane `{x i = 0}` (as fn 34 says). So "biconvex ⟺ one side of
a cut" (§2 l. 219) is false, and Target 7(ii) (⇒) cannot go through fn 34 alone.
Source: [[Deference Done Better]] §2 l. 219, fn 34 (findings F5)
Kind: D
Fidelity: n/a -/
def lexHalf {W : Type} (i j : W) (c : ℝ) : Set (W → ℝ) :=
  {x | 0 < x i ∨ (x i = 0 ∧ c ≤ x j)}

/-- Membership in the lexicographic half-space.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_lexHalf {W : Type} {i j : W} {c : ℝ} {x : W → ℝ} :
    x ∈ lexHalf i j c ↔ 0 < x i ∨ (x i = 0 ∧ c ≤ x j) := Iff.rfl

/-- Membership in its complement.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_lexHalf_compl {W : Type} {i j : W} {c : ℝ} {x : W → ℝ} :
    x ∈ (lexHalf i j c)ᶜ ↔ x i < 0 ∨ (x i = 0 ∧ x j < c) := by
  rw [Set.mem_compl_iff, mem_lexHalf]
  constructor
  · intro h
    push Not at h
    rcases h.1.lt_or_eq with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, h.2 h0⟩
  · rintro (h | ⟨h0, h1⟩)
    · rintro (h' | ⟨h', _⟩) <;> linarith
    · rintro (h' | ⟨_, h'⟩) <;> linarith

/-- A nonnegative multiple of a point of `L` with vanishing pivot coordinate has second
coordinate at least the scaled threshold.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexHalf_aux_mem {W : Type} {i j : W} {c : ℝ} (a : ℝ) (ha : 0 ≤ a) {x : W → ℝ}
    (hx : x ∈ lexHalf i j c) (h : a * x i = 0) : a * c ≤ a * x j := by
  rcases ha.lt_or_eq with ha' | ha'
  · have hx0 : x i = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' ha'.ne'
      · exact h'
    rcases mem_lexHalf.1 hx with hx' | ⟨_, hx1⟩
    · linarith
    · exact mul_le_mul_of_nonneg_left hx1 ha
  · rw [← ha', zero_mul, zero_mul]

/-- A nonnegative multiple of a point of `Lᶜ` with vanishing pivot coordinate has second
coordinate at most the scaled threshold, strictly if the multiplier is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexHalf_aux_compl {W : Type} {i j : W} {c : ℝ} (a : ℝ) (ha : 0 ≤ a) {x : W → ℝ}
    (hx : x ∈ (lexHalf i j c)ᶜ) (h : a * x i = 0) :
    a * x j ≤ a * c ∧ (0 < a → a * x j < a * c) := by
  rcases ha.lt_or_eq with ha' | ha'
  · have hx0 : x i = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' ha'.ne'
      · exact h'
    rcases mem_lexHalf_compl.1 hx with hx' | ⟨_, hx1⟩
    · linarith
    · have : a * x j < a * c := mul_lt_mul_of_pos_left hx1 ha'
      exact ⟨this.le, fun _ => this⟩
  · rw [← ha', zero_mul, zero_mul]
    exact ⟨le_rfl, fun h' => absurd h' (lt_irrefl _)⟩

/-- `L` is convex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexHalf_convex {W : Type} (i j : W) (c : ℝ) : Convex ℝ (lexHalf i j c) := by
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x i := by rcases mem_lexHalf.1 hx with h | ⟨h, _⟩ <;> linarith
  have hy0 : 0 ≤ y i := by rcases mem_lexHalf.1 hy with h | ⟨h, _⟩ <;> linarith
  rw [mem_lexHalf]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hax := mul_nonneg ha hx0
  have hby := mul_nonneg hb hy0
  rcases (add_nonneg hax hby).lt_or_eq with h | h
  · exact Or.inl h
  · right
    refine ⟨h.symm, ?_⟩
    have e1 : a * x i = 0 := by linarith
    have e2 : b * y i = 0 := by linarith
    have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith [lexHalf_aux_mem a ha hx e1, lexHalf_aux_mem b hb hy e2]

/-- `Lᶜ` is convex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexHalf_compl_convex {W : Type} (i j : W) (c : ℝ) : Convex ℝ (lexHalf i j c)ᶜ := by
  intro x hx y hy a b ha hb hab
  have hx0 : x i ≤ 0 := by rcases mem_lexHalf_compl.1 hx with h | ⟨h, _⟩ <;> linarith
  have hy0 : y i ≤ 0 := by rcases mem_lexHalf_compl.1 hy with h | ⟨h, _⟩ <;> linarith
  rw [mem_lexHalf_compl]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hax := mul_nonpos_of_nonneg_of_nonpos ha hx0
  have hby := mul_nonpos_of_nonneg_of_nonpos hb hy0
  rcases (add_nonpos hax hby).lt_or_eq with h | h
  · exact Or.inl h
  · right
    refine ⟨h, ?_⟩
    have e1 : a * x i = 0 := by linarith
    have e2 : b * y i = 0 := by linarith
    obtain ⟨hx1, hx1'⟩ := lexHalf_aux_compl a ha hx e1
    obtain ⟨hy1, hy1'⟩ := lexHalf_aux_compl b hb hy e2
    have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · linarith [hx1' ha']
    · have hb' : 0 < b := by linarith
      linarith [hy1' hb']

/-- **The lexicographic half-space is biconvex** (any pivot coordinates, any threshold).
Source: [[Deference Done Better]] §2 l. 219, fn 34 (findings F5)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf_biconvex {W : Type} (i j : W) (c : ℝ) :
    Biconvex (lexHalf i j c) :=
  ⟨lexHalf_convex i j c, lexHalf_compl_convex i j c⟩

/-- The vector with `a` at `i`, `b` at `j` and `0` elsewhere.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def lexPt {W : Type} [DecidableEq W] (i j : W) (a b : ℝ) : W → ℝ :=
  fun w => (if w = i then a else 0) + (if w = j then b else 0)

/-- Its expectation of `X` is `a X_i + b X_j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_lexPt {W : Type} [Fintype W] [DecidableEq W] (i j : W) (a b : ℝ) (X : W → ℝ) :
    E (lexPt i j a b) X = a * X i + b * X j := by
  simp [E, lexPt, add_mul, sum_add_distrib, ite_mul]

/-- Its `i`-coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexPt_apply_i {W : Type} [DecidableEq W] {i j : W} (hij : i ≠ j) (a b : ℝ) :
    lexPt i j a b i = a := by
  simp [lexPt, hij]

/-- Its `j`-coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem lexPt_apply_j {W : Type} [DecidableEq W] {i j : W} (hij : i ≠ j) (a b : ℝ) :
    lexPt i j a b j = b := by
  simp [lexPt, hij.symm]

/-- **`L` is not a closed half-space** `{ρ : t ≤ E_ρ(X)}` for any `X, t`: the points with
`(x_i, x_j) = (0, c) ∈ L` and `(0, c − 1) ∉ L` force `X_j > 0`; but `(1, −M) ∈ L` for every
`M`, and `X_i − M X_j < t` for `M` large.
Source: [[Deference Done Better]] §2 l. 219 (refuted: a biconvex set need not be a cut)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf_ne_closedHalf {W : Type} [Fintype W] [DecidableEq W] {i j : W} (hij : i ≠ j)
    (c : ℝ) (X : W → ℝ) (t : ℝ) : lexHalf i j c ≠ {ρ | t ≤ E ρ X} := by
  intro h
  have hp : lexPt i j 0 c ∈ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij, lexPt_apply_j hij]
    exact Or.inr ⟨rfl, le_rfl⟩
  have hq : lexPt i j 0 (c - 1) ∉ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij, lexPt_apply_j hij]
    rintro (h' | ⟨_, h'⟩) <;> linarith
  rw [h, Set.mem_setOf_eq, E_lexPt] at hp hq
  have hq' := not_le.1 hq
  have hXj : 0 < X j := by linarith
  set M : ℝ := (X i - t + 1) / X j with hM
  have hr : lexPt i j 1 (-M) ∈ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij]
    exact Or.inl one_pos
  rw [h, Set.mem_setOf_eq, E_lexPt] at hr
  have hMX : M * X j = X i - t + 1 := by rw [hM]; field_simp
  linarith

/-- **`L` is not an open half-space** `{ρ : t < E_ρ(X)}` for any `X, t` (same three points,
with `M := (X_i − t)/X_j` making `E(X) = t` at a point of `L`).
Source: [[Deference Done Better]] §2 l. 219 (refuted: a biconvex set need not be a cut)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf_ne_openHalf {W : Type} [Fintype W] [DecidableEq W] {i j : W} (hij : i ≠ j)
    (c : ℝ) (X : W → ℝ) (t : ℝ) : lexHalf i j c ≠ {ρ | t < E ρ X} := by
  intro h
  have hp : lexPt i j 0 c ∈ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij, lexPt_apply_j hij]
    exact Or.inr ⟨rfl, le_rfl⟩
  have hq : lexPt i j 0 (c - 1) ∉ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij, lexPt_apply_j hij]
    rintro (h' | ⟨_, h'⟩) <;> linarith
  rw [h, Set.mem_setOf_eq, E_lexPt] at hp hq
  have hq' := not_lt.1 hq
  have hXj : 0 < X j := by linarith
  set M : ℝ := (X i - t) / X j with hM
  have hr : lexPt i j 1 (-M) ∈ lexHalf i j c := by
    rw [mem_lexHalf, lexPt_apply_i hij]
    exact Or.inl one_pos
  rw [h, Set.mem_setOf_eq, E_lexPt] at hr
  have hMX : M * X j = X i - t := by rw [hM]; field_simp
  linarith

/-- **Findings F5 in Lean (all-vectors form).** For `i ≠ j` the lexicographic half-space is
biconvex and is neither a closed nor an open half-space: a biconvex set need not be "one side
of a cut", which is what fn 34's one-line argument for Target 7(ii) (⇒) would need.
Source: [[Deference Done Better]] §2 l. 219, fn 34; findings F5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf_not_halfSpace {W : Type} [Fintype W] [DecidableEq W] {i j : W} (hij : i ≠ j)
    (c : ℝ) :
    Biconvex (lexHalf i j c) ∧ (∀ X t, lexHalf i j c ≠ {ρ | t ≤ E ρ X}) ∧
      ∀ X t, lexHalf i j c ≠ {ρ | t < E ρ X} :=
  ⟨lexHalf_biconvex i j c, fun X t => lexHalf_ne_closedHalf hij c X t,
    fun X t => lexHalf_ne_openHalf hij c X t⟩

/-- Expectation on three worlds, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_fin3 (ρ X : Fin 3 → ℝ) : E ρ X = ρ 0 * X 0 + ρ 1 * X 1 + ρ 2 * X 2 := by
  simp [E, Fin.sum_univ_three]

/-- **The in-simplex instance is non-trivial.** On three worlds with threshold `½`,
`L = {ρ(w₀) > 0} ∪ {ρ(w₀) = 0 ∧ ρ(w₁) ≥ ½}` contains the distribution `(0, ½, ½)` and misses the
distribution `(0, 0, 1)`, so it cuts *probability space* (not just `ℝ^W`) into two nonempty
convex pieces. (With threshold `0` — the example as first written in findings F5 — the set
would contain the whole simplex.)
Source: [[Deference Done Better]] §2 l. 219 ("divide probability space"); findings F5
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf3_nontrivial :
    (![0, 1 / 2, 1 / 2] : Fin 3 → ℝ) ∈ lexHalf (0 : Fin 3) 1 (1 / 2) ∩ stdSimplex ℝ (Fin 3) ∧
      (![0, 0, 1] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) \ lexHalf (0 : Fin 3) 1 (1 / 2) := by
  refine ⟨⟨?_, simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩,
    simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  · rw [mem_lexHalf]; right; simp
  · rw [mem_lexHalf]; simp

/-- For `d > 0` and any `s`, some `ε ∈ (0, 1)` has `ε s < d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_small_eps (d s : ℝ) (hd : 0 < d) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε * s < d := by
  set K : ℝ := |s| + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨d / (d + K), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · calc d / (d + K) * s ≤ d / (d + K) * K := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [le_abs_self s]
      _ < d := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith

/-- **In probability space, `L` is not a closed half-space either**: on three worlds,
`L ∩ Δ ≠ {ρ ∈ Δ : t ≤ E_ρ(X)}` for every `X, t`. From `(0, ½, ½) ∈ L` and `(0, 0, 1) ∉ L` we get
`X_2 < t`, but `(ε, 0, 1 − ε) ∈ L` for every `ε ∈ (0, 1]` and its expectation tends to `X_2`.
Source: [[Deference Done Better]] §2 l. 219 (refuted as a claim about probability space)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf3_ne_closedHalf_simplex (X : Fin 3 → ℝ) (t : ℝ) :
    lexHalf (0 : Fin 3) 1 (1 / 2) ∩ stdSimplex ℝ (Fin 3) ≠
      {ρ | t ≤ E ρ X} ∩ stdSimplex ℝ (Fin 3) := by
  intro h
  obtain ⟨hp, hq⟩ := lexHalf3_nontrivial
  have hp' := hp
  rw [h] at hp'
  obtain ⟨hp1, -⟩ := hp'
  rw [Set.mem_setOf_eq, E_fin3] at hp1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hp1
  have hq' : (![0, 0, 1] : Fin 3 → ℝ) ∉ {ρ | t ≤ E ρ X} ∩ stdSimplex ℝ (Fin 3) := by
    rw [← h]; exact fun hmem => hq.2 hmem.1
  have hq1 : E (![0, 0, 1] : Fin 3 → ℝ) X < t := by
    by_contra hc
    exact hq' ⟨not_lt.1 hc, hq.1⟩
  rw [E_fin3] at hq1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hq1
  obtain ⟨ε, hε0, hε1, hεs⟩ := exists_small_eps (t - X 2) (X 0 - X 2) (by linarith)
  have hr : (![ε, 0, 1 - ε] : Fin 3 → ℝ) ∈
      lexHalf (0 : Fin 3) 1 (1 / 2) ∩ stdSimplex ℝ (Fin 3) := by
    refine ⟨?_, simplex3 _ _ _ hε0.le le_rfl (by linarith) (by ring)⟩
    rw [mem_lexHalf]; left; simpa using hε0
  rw [h] at hr
  obtain ⟨hr1, -⟩ := hr
  rw [Set.mem_setOf_eq, E_fin3] at hr1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hr1
  nlinarith

/-- **In probability space, `L` is not an open half-space**: `L ∩ Δ ≠ {ρ ∈ Δ : t < E_ρ(X)}` for
every `X, t`. From `(0, ½, ½) ∈ L` and `(0, ¼, ¾) ∉ L` we get `X_1 > X_2` and then `X_2 < t`; the
points `(ε, 0, 1 − ε) ∈ L` again bring the expectation below `t`.
Source: [[Deference Done Better]] §2 l. 219 (refuted as a claim about probability space)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem lexHalf3_ne_openHalf_simplex (X : Fin 3 → ℝ) (t : ℝ) :
    lexHalf (0 : Fin 3) 1 (1 / 2) ∩ stdSimplex ℝ (Fin 3) ≠
      {ρ | t < E ρ X} ∩ stdSimplex ℝ (Fin 3) := by
  intro h
  obtain ⟨hp, -⟩ := lexHalf3_nontrivial
  have hp' := hp
  rw [h] at hp'
  obtain ⟨hp1, -⟩ := hp'
  rw [Set.mem_setOf_eq, E_fin3] at hp1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hp1
  have hq : (![0, 1 / 4, 3 / 4] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) \
      lexHalf (0 : Fin 3) 1 (1 / 2) := by
    refine ⟨simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
    rw [mem_lexHalf]; simp; norm_num
  have hq' : (![0, 1 / 4, 3 / 4] : Fin 3 → ℝ) ∉ {ρ | t < E ρ X} ∩ stdSimplex ℝ (Fin 3) := by
    rw [← h]; exact fun hmem => hq.2 hmem.1
  have hq1 : E (![0, 1 / 4, 3 / 4] : Fin 3 → ℝ) X ≤ t := by
    by_contra hc
    exact hq' ⟨not_le.1 hc, hq.1⟩
  rw [E_fin3] at hq1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hq1
  obtain ⟨ε, hε0, hε1, hεs⟩ := exists_small_eps (t - X 2) (X 0 - X 2) (by linarith)
  have hr : (![ε, 0, 1 - ε] : Fin 3 → ℝ) ∈
      lexHalf (0 : Fin 3) 1 (1 / 2) ∩ stdSimplex ℝ (Fin 3) := by
    refine ⟨?_, simplex3 _ _ _ hε0.le le_rfl (by linarith) (by ring)⟩
    rw [mem_lexHalf]; left; simpa using hε0
  rw [h] at hr
  obtain ⟨hr1, -⟩ := hr
  rw [Set.mem_setOf_eq, E_fin3] at hr1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, vec3_two] at hr1
  nlinarith

/-! ## Targets 10, 11: positive validation witnesses (audit r1 NB1/N1) -/

/-- **Target 10 witness (N+).** `dup3` validates Reflection: every row is immodest.
Source: [[Deference Done Better]] §4 l. 339 (Fact 4.2); mandate Target 10 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_validates_reflects : dup3.Validates Reflects :=
  (validates_reflects_iff dup3).2 fun i => Or.inl (dup3_immodest i)

/-- **Target 11 witness (N+, immodest case).** `dup3` validates New Reflection (NR-str).
Source: [[Deference Done Better]] §4 l. 347 (Fact 4.3); mandate Target 11 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_validates_newReflects : dup3.Validates NewReflects := fun i =>
  newReflects_of_reflects (dup3.P_nonneg i) (dup3_validates_reflects i)

/-- **Target 11 witness (N+, modest case).** Figure 2 validates New Reflection (NR-str): each
row's candidates are the two rows, with singleton cells and self-mass `1/5`, and the product
identities hold at both worlds. A modest frame in Fact 4.3's hull condition.
Source: [[Deference Done Better]] §4 l. 347 (Fact 4.3), §1 l. 102, fn 13; mandate Target 11
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig2_validates_newReflects : fig2.Validates NewReflects := by
  intro i ρ hρ
  obtain ⟨hc0, hc1⟩ := cell_of_ne fig2 fig2_ne
  obtain ⟨hs0, hs1⟩ := fig2_selfMass
  fin_cases i
  · rw [cands_eq_pair fig2 (by norm_num [fig2_P0]) (by norm_num [fig2_P0])] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · refine ⟨by rw [hs0]; norm_num, fun w => ?_⟩
      rw [hs0, hc0]
      fin_cases w <;> norm_num [ind, mass, fig2_P0]
    · refine ⟨by rw [hs1]; norm_num, fun w => ?_⟩
      rw [hs1, hc1]
      fin_cases w <;> norm_num [ind, mass, fig2_P0, fig2_P1]
  · rw [cands_eq_pair fig2 (by norm_num [fig2_P1]) (by norm_num [fig2_P1])] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · refine ⟨by rw [hs0]; norm_num, fun w => ?_⟩
      rw [hs0, hc0]
      fin_cases w <;> norm_num [ind, mass, fig2_P0, fig2_P1]
    · refine ⟨by rw [hs1]; norm_num, fun w => ?_⟩
      rw [hs1, hc1]
      fin_cases w <;> norm_num [ind, mass, fig2_P1]

/-! ## Target 15: Theorem 5.1's six bullets on Figure 3 and Fact 2.1 (audit r1 NB1) -/

/-- **Target 15 witness (N+, positive).** All six bullets of `tfae_thm51` hold for the uniform
deferrer on Figure 3.
Source: [[Deference Done Better]] §5 l. 375 (Theorem 5.1); §1 l. 130 (Figure 3)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fig3_thm51_all :
    Value half fig3 ∧
      (¬ ∃ (𝒪₁ 𝒪₂ : DecisionProblem (Fin 2)) (O : Fin 2 → ℝ) (S : Fin 2 → (Fin 2 → ℝ)),
        FixedOptionBook half fig3 𝒪₁ 𝒪₂ O S SureLoss) ∧
      TotalTrust half fig3 ∧ TotalTrustBiconvex half fig3 ∧
      HullAndModestlyInformed half fig3 ∧ LambdaForm half fig3 := by
  have t := tfae_thm51 half_mem fig3
  have hv := fig3_totalTrust_value.2
  exact ⟨hv, (t.out 0 1).1 hv, (t.out 0 2).1 hv, (t.out 0 3).1 hv, (t.out 0 4).1 hv,
    (t.out 0 5).1 hv⟩

/-- **Target 15 witness (N+, negative).** All six bullets of `tfae_thm51` fail for `π` on Fact
2.1's frame (the Dutch book is `fact21_book`).
Source: [[Deference Done Better]] §5 l. 375 (Theorem 5.1); §2 l. 161 (Fact 2.1)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fact21_thm51_none :
    ¬ Value π21 fact21 ∧
      (∃ (𝒪₁ 𝒪₂ : DecisionProblem (Fin 3)) (O : Fin 3 → ℝ) (S : Fin 3 → (Fin 3 → ℝ)),
        FixedOptionBook π21 fact21 𝒪₁ 𝒪₂ O S SureLoss) ∧
      ¬ TotalTrust π21 fact21 ∧ ¬ TotalTrustBiconvex π21 fact21 ∧
      ¬ HullAndModestlyInformed π21 fact21 ∧ ¬ LambdaForm π21 fact21 := by
  have t := tfae_thm51 π21_mem fact21
  exact ⟨fact21_not_value, ⟨_, _, _, _, fact21_book⟩,
    fun h => fact21_not_value ((t.out 0 2).2 h), fun h => fact21_not_value ((t.out 0 3).2 h),
    fun h => fact21_not_value ((t.out 0 4).2 h), fun h => fact21_not_value ((t.out 0 5).2 h)⟩

/-! ## Target 16: positive access has content (audit r1 N2) -/

/-- Row 0 of `dup3` simply trusts the frame (it reflects it, being immodest; the collapse).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem dup3_row0_simpleTrust : SimpleTrust (dup3.P 0) dup3 :=
  ((tfae_immodestFrame (dup3.P_mem 0) dup3_immodest).out 0 2).1
    (reflects_self_of_selfMass_eq_one dup3 (dup3.P_mem 0) (dup3_immodest 0))

/-- **Target 16 witness (N+, positive, non-trivial instance).** Row 0 of `dup3`, `(½, ½, 0)`,
has positive access, and the instance is not the trivial `q = W`: it is certain of
`q = {w₀, w₁} ≠ W`.
Source: [[Deference Done Better]] §5 l. 392; mandate Target 16 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem dup3_row0_positiveAccess :
    PositiveAccess dup3 (dup3.P 0) ∧ mass (dup3.P 0) {0, 1} = 1 ∧
      ({0, 1} : Finset (Fin 3)) ≠ univ := by
  refine ⟨positiveAccess_of_simpleTrust (dup3.P_mem 0) dup3_row0_simpleTrust, ?_, by decide⟩
  rw [dup3_P.1, mass, sum_pair (by decide)]
  norm_num

/-- The point mass on the first world of `Fin 3`.
Source: none: infrastructure (audit r1 probe P3, copied)
Kind: D
Fidelity: n/a -/
def δ0 : Fin 3 → ℝ := ![1, 0, 0]

/-- `δ0` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem δ0_mem : δ0 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Target 16 witness (N+, negative).** The point mass on `w₀` fails positive access on Fact
2.1's frame: no row is certain of `w₀`.
Source: [[Deference Done Better]] §5 l. 392; audit r1 probe P3 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_positiveAccess_δ0_fact21 : ¬ PositiveAccess fact21 δ0 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fact21_P
  have hq : mass δ0 {0} = 1 := by simp [mass, δ0]
  have := h {0} hq
  have hf : univ.filter (fun w => mass (fact21.P w) {0} = 1) = (∅ : Finset (Fin 3)) := by
    ext w
    fin_cases w <;> simp [mass, h0, h1, h2, fin3_mk_two] <;> norm_num
  rw [hf] at this
  simp [mass] at this

/-- Hence `δ0` does not simply trust Fact 2.1's frame (`positiveAccess_of_simpleTrust`).
Source: audit r1 probe P3 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_simpleTrust_δ0_fact21 : ¬ SimpleTrust δ0 fact21 := fun h =>
  not_positiveAccess_δ0_fact21 (positiveAccess_of_simpleTrust δ0_mem h)

/-! ## The new predicates of record each fail on a concrete frame (audit r1 N3, probe P1) -/

/-- On `dup3` every candidate is immodest, so NR-vac already forces NR-str; `(3/5, 1/5, 1/5)`
fails both.
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_newReflectsVac_πneg_dup3 : ¬ NewReflectsVac πneg dup3 := fun h =>
  dup3_none.2.1 fun ρ hρ =>
    have hpos : 0 < dup3.selfMass ρ := by
      rw [immodest_cands dup3_immodest πneg ρ hρ]; exact one_pos
    ⟨hpos, h ρ hρ hpos⟩

/-- `InformedReflects` (Target 2, all vectors `σ`) fails for `(3/5, 1/5, 1/5)` on `dup3`.
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_informedReflects_πneg_dup3 : ¬ InformedReflects πneg dup3 := fun h =>
  dup3_none.2.1 ((informedReflects_iff_newReflects πneg_mem.1).1 h)

/-- `InformedReflectsSimplex` (Target 2 stretch, distributions only) fails there too.
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_informedReflectsSimplex_πneg_dup3 : ¬ InformedReflectsSimplex πneg dup3 := fun h =>
  not_newReflectsVac_πneg_dup3 ((informedReflectsSimplex_iff_newReflectsVac πneg_mem.1).1 h)

/-- `CondTotalTrust` (Target 6(a)) fails on Fact 2.1 (it *is* Total Trust).
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_condTotalTrust_fact21 : ¬ CondTotalTrust π21 fact21 := fun h =>
  fact21_not_totalTrust (totalTrust_of_condTotalTrust h)

/-- `ComparativeTotalTrust` (Target 6(c)) fails on Fact 2.1.
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_comparativeTotalTrust_fact21 : ¬ ComparativeTotalTrust π21 fact21 := fun h =>
  fact21_not_totalTrust (comparativeTotalTrust_iff_totalTrust.1 h)

/-- `ReflectsConvex` (Target 7(i)) fails on Figure 3 (which does not reflect).
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_reflectsConvex_fig3 : ¬ ReflectsConvex half fig3 := fun h =>
  fig3_not_reflects ((reflects_iff_reflectsConvex half_mem).2 h)

/-- At `n = 1` the averaged event is the Simple-Trust event.
Source: none: infrastructure (audit r1 probe P1, copied)
Kind: L
Fidelity: n/a -/
theorem averagedEvent_one {W : Type} [Fintype W] [DecidableEq W] (F : Frame W) (q : Finset W)
    (t : ℝ) : averagedEvent F (![q] : Fin 1 → Finset W) t = F.probEvent q t := by
  ext w
  simp [averagedEvent, Frame.probEvent]

/-- `AveragedTotalTrust` (Target 6(d), only `⇒` is proved in the package) is not trivially
true: at `n = 1`, `q = {w₁}`, `t = ½` it is the Simple Trust failure of `(3/5, 1/5, 1/5)` on
`dup3`.
Source: audit r1 probe P1 (copied)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem not_averagedTotalTrust_πneg_dup3 : ¬ AveragedTotalTrust πneg dup3 := by
  intro h
  have := h 1 one_pos (![{1}] : Fin 1 → Finset (Fin 3)) (1 / 2)
  rw [averagedEvent_one, dup3_probEvent] at this
  simp only [Fin.sum_univ_one, Nat.cast_one, div_one, one_mul, Matrix.cons_val_zero] at this
  have hi : ({1} : Finset (Fin 3)) ∩ {0, 1} = {1} := by ext w; fin_cases w <;> simp
  rw [hi, mass, sum_pair (by simp), mass, sum_singleton] at this
  norm_num [πneg] at this

/-! ## Audit round 2 probes, copied: Q2 (biconvex headline off half-spaces), Q3 (`¬ Validates
TotalTrust`), Q4 (Fact 4.2's modest disjunct) -/

/-- The complement of a lexicographic half-space is biconvex.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2 (§2 l. 219, findings F5)
Kind: L
Fidelity: n/a -/
theorem lexHalf_compl_biconvex {W : Type} (i j : W) (c : ℝ) : Biconvex (lexHalf i j c)ᶜ :=
  ⟨lexHalf_compl_convex i j c, by rw [compl_compl]; exact lexHalf_convex i j c⟩

/-- Nor is the complement a closed half-space (else `L` would be an open one).
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2
Kind: P
Fidelity: n/a -/
theorem lexHalf_compl_ne_closedHalf {W : Type} [Fintype W] [DecidableEq W] {i j : W} (hij : i ≠ j)
    (c : ℝ) (X : W → ℝ) (t : ℝ) : (lexHalf i j c)ᶜ ≠ {ρ | t ≤ E ρ X} := by
  intro h
  apply lexHalf_ne_openHalf hij c (-X) (-t)
  rw [← compl_compl (lexHalf i j c), h]
  ext ρ
  simp [E_neg_right, not_le]

/-- Nor an open half-space.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2
Kind: P
Fidelity: n/a -/
theorem lexHalf_compl_ne_openHalf {W : Type} [Fintype W] [DecidableEq W] {i j : W} (hij : i ≠ j)
    (c : ℝ) (X : W → ℝ) (t : ℝ) : (lexHalf i j c)ᶜ ≠ {ρ | t < E ρ X} := by
  intro h
  apply lexHalf_ne_closedHalf hij c (-X) (-t)
  rw [← compl_compl (lexHalf i j c), h]
  ext ρ
  simp [E_neg_right, not_lt]

/-- On `dup3`, `B := (lexHalf 2 0 (3/4))ᶜ = {x₂ < 0} ∪ {x₂ = 0 ∧ x₀ < ¾}` holds exactly at the two
worlds with row `(½, ½, 0)`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2
Kind: L
Fidelity: n/a -/
theorem dup3_memEvent_lexHalf_compl :
    memEvent dup3 (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ = {0, 1} := by
  ext w
  rw [mem_memEvent, mem_lexHalf_compl]
  fin_cases w <;> simp [dup3_P, vec3_two, fin3_mk_two] <;> norm_num

/-- Direct verification: the conditional `π5(· | P ∈ B) = (½, ½, 0)` lies **on** the boundary
hyperplane `{x₂ = 0}`, and is in `B` only by the lexicographic clause `x₀ = ½ < ¾`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2
Kind: N+
Fidelity: n/a -/
theorem dup3_condIn_lexHalf_compl_direct :
    CondIn π5 dup3 (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ := by
  refine ⟨![1 / 2, 1 / 2, 0], ?_, fun w => ?_⟩
  · rw [mem_lexHalf_compl]; right; simp [vec3_two]; norm_num
  · rw [dup3_memEvent_lexHalf_compl, mass, sum_pair (by simp)]
    fin_cases w <;> norm_num [ind, π5, vec3_two, Fin.ext_iff]

/-- The same instance through the headline `totalTrust_iff_totalTrustBiconvex` (the uniform
deferrer totally trusts `dup3`), so the headline's (⇒) is exercised at a biconvex set that is
not a half-space of either form.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2; §2 l. 225
Kind: N+
Fidelity: n/a -/
theorem dup3_condIn_lexHalf_compl_of_headline :
    CondIn π5 dup3 (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ :=
  (totalTrust_iff_totalTrustBiconvex π5_mem).1 dup3_all.2.2.2.2.1 _
    (lexHalf_compl_biconvex 2 0 (3 / 4))
    (by rw [dup3_memEvent_lexHalf_compl, mass, sum_pair (by simp)]; norm_num [π5])

/-- Q2 collected: the set is biconvex, not a half-space of either form, and the conditional lands
in it.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q2
Kind: N+
Fidelity: n/a -/
theorem dup3_condIn_lexHalf_compl_summary :
    Biconvex (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ ∧
      (∀ X t, (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ ≠ {ρ | t ≤ E ρ X}) ∧
      (∀ X t, (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ ≠ {ρ | t < E ρ X}) ∧
      CondIn π5 dup3 (lexHalf (2 : Fin 3) 0 (3 / 4))ᶜ :=
  ⟨lexHalf_compl_biconvex 2 0 (3 / 4),
   fun X t => lexHalf_compl_ne_closedHalf (by decide) (3 / 4) X t,
   fun X t => lexHalf_compl_ne_openHalf (by decide) (3 / 4) X t,
   dup3_condIn_lexHalf_compl_direct⟩

/-- `swap2`'s row `δ₁` has a null self-cell and `C_0⁻ = {δ₀}`, so it is not unguarded-modestly
informed: `δ₁ ∉ hull {δ₀}`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q3 (Corollary 4.5, fn 61)
Kind: N+
Fidelity: n/a -/
theorem swap2_not_modestlyInformedU : ¬ ModestlyInformedU swap2 (swap2.P 0) := by
  intro h
  obtain ⟨hs0, _⟩ := swap2_selfMass
  obtain ⟨hcd0, _⟩ := swap2_cands
  rw [modestlyInformedU_iff_of_zero swap2 (swap2.P_mem 0) hs0] at h
  have hcm : swap2.candsMinus (swap2.P 0) = {swap2.P 1} := by
    rw [Frame.candsMinus, hcd0]
    exact erase_eq_of_notMem (by simp [swap2_ne])
  rw [hcm, coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at h
  exact swap2_ne h

/-- Hence `swap2` does not validate Total Trust (Corollary 4.5, unguarded, ⇒ contrapositive): a
frame that fails the right-hand side of `validates_totalTrust_iff`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q3 (§4 l. 363)
Kind: N+
Fidelity: n/a -/
theorem swap2_not_validates_totalTrust : ¬ swap2.Validates TotalTrust := fun h =>
  swap2_not_modestlyInformedU ((validates_totalTrust_iff swap2).1 h 0)

/-- `nullSelf` validates Reflection although its row 0, `(0, ½, ½)`, is modest: row 0 has a null
self-cell and lies in the hull of its other candidates `{δ₁, δ₂}` (Fact 4.2's right disjunct),
rows 1, 2 are immodest (the left one). No world gives row 0's world positive probability, which
is why a modest row is compatible with validated Reflection (DDB §4 l. 351: modest candidates
"might as well not be included").
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q4, [[lit-ddb-facts-audit-r2-fidelity]] NB3
(§4 l. 339, Fact 4.2's modest disjunct)
Kind: N+
Fidelity: n/a -/
theorem nullSelf_validates_reflects_modest :
    nullSelf.Validates Reflects ∧ nullSelf.ModestAt 0 := by
  obtain ⟨hs0, hs1, hs2⟩ := nullSelf_selfMass
  obtain ⟨hcd0, _, _⟩ := nullSelf_cands
  obtain ⟨h01, h02, _⟩ := nullSelf_ne
  refine ⟨?_, ?_⟩
  · rw [validates_reflects_iff]
    intro i
    fin_cases i
    · right
      show nullSelf.P 0 ∈ convexHull ℝ (↑(nullSelf.candsMinus (nullSelf.P 0)) : Set (Fin 3 → ℝ))
      have hcm : nullSelf.candsMinus (nullSelf.P 0) = {nullSelf.P 1, nullSelf.P 2} := by
        rw [Frame.candsMinus, hcd0]
        apply erase_eq_of_notMem
        simp only [mem_insert, mem_singleton, nullSelf_P]
        exact fun h => h.elim h01 h02
      rw [hcm]
      exact mem_hull_of_comb2 (x := nullSelf.P 1) (y := nullSelf.P 2) (by simp) (by simp)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        (by ext w; fin_cases w <;> norm_num [nullSelf_P, vec3_two])
    · left; exact hs1
    · left; exact hs2
  · show nullSelf.selfMass (nullSelf.P 0) < 1
    rw [hs0]; norm_num

/-- `nullSelf` validates all four hereditary principles (Reflection, New Reflection, Total Trust,
Value) with a modest row: Fact 4.3's hull condition with a null-self-cell row (`P_0 = ½ P̂_1 +
½ P̂_2`) and Corollary 4.4's `λ_00 = 0` branch are inhabited by a positive instance.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q4; §4 ll. 339, 347, 359
Kind: N+
Fidelity: n/a -/
theorem nullSelf_validates_all :
    nullSelf.Validates Reflects ∧ nullSelf.Validates NewReflects ∧
      nullSelf.Validates TotalTrust ∧ nullSelf.Validates Value :=
  ⟨nullSelf_validates_reflects_modest.1,
   fun i => newReflects_of_reflects (nullSelf.P_nonneg i) (nullSelf_validates_reflects_modest.1 i),
   nullSelf_validates_totalTrust_not_modestlyInformed.1,
   fun i => value_of_reflects (nullSelf.P_nonneg i) (nullSelf_validates_reflects_modest.1 i)⟩

end

end Cleanroom.Lit.LitDdbFacts.Examples
