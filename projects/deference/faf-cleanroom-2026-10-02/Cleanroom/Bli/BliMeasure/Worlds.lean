import Cleanroom.Bli.BliFinite.Coherence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `bli-measure` · Worlds: world conjunctions, extension by `false`, world measures (target 5)

The finite-world vocabulary B3 is built on, over FAF's `FiniteWorld B = Fin B → Bool` and
`PCWorld`:

* `worldConj u` — Soto's `φ_u`, the conjunction of the literals of `u`; `holds_worldConj`
  characterizes `u` (`payoutRat_worldConj`: a longer world pays `φ_u` iff it restricts to `u`).
* `extFW` / `restrFW` — extension by `false` and restriction of finite worlds; the extended world
  reads every sentence as the original (`toBoolPCWorld_extFW`).
* `WMeasure w D`, `wMarginal w φ` — Soto's PC-valuation (PDF 05 Def 1) as a weight vector on
  `FiniteWorld B` supported on `D`-consistent worlds, and its sentence marginal
  `∑ u, w u * u.payoutRat φ`. **The formulas are literally `bli-coherent-mm`'s `IsWorldMeasure`
  and `marginal`** (`Base.lean` proves the two `rfl` bridges); they are restated here because the
  theory files of this package must not import the construction-heavy `BliCoherentMm`
  modules ([[bli-measure-mandate]] §Deliverables, file discipline).
* `wMarginal_eq_sum_filter` — the bundle identity (bli-soto-a-037: a share of `φ` is the bundle
  of the worlds satisfying it); `respects_iff` — Soto's "respects `D̄`" and its "equivalently"
  (bli-soto-a-039), proved as an iff.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite

/-! ## World conjunctions -/

/-- The literal of atom `i` in the finite world `u`: `atom i` if `u i`, else `∼atom i`.
Source: bli-soto-a-041 (`φ_W`, the conjunction of literals of `W`)
Kind: D
Fidelity: exact -/
def litOf {B : ℕ} (u : FiniteWorld B) (i : Fin B) : Sentence :=
  if u i then Formula.atom i.val else ∼Formula.atom i.val

/-- **Soto's `φ_u`**: the conjunction of the literals of `u` over all `B` atoms (FAF's
`sentenceConjunction` over `List.finRange B`).
Source: bli-soto-a-041 (`φ_W`); bli-soto-a-037 (worlds as Boolean assignments)
Kind: D
Fidelity: exact -/
def worldConj {B : ℕ} (u : FiniteWorld B) : Sentence :=
  sentenceConjunction ((List.finRange B).map (litOf u))

/-- A world holds the literal of `i` in `u` iff it agrees with `u` at `i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_litOf (v : PCWorld) {B : ℕ} (u : FiniteWorld B) (i : Fin B) :
    v.Holds (litOf u i) ↔ (v i.val ↔ u i = true) := by
  unfold litOf
  cases h : u i
  · simp
  · simp

/-- **`φ_u` characterizes `u`**: a world holds `worldConj u` iff it agrees with `u` on every atom
below `B`.
Source: bli-soto-a-041 (`PCWorld.Holds` of `φ_u` characterizes `u`); mandate target 6
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem holds_worldConj (v : PCWorld) {B : ℕ} (u : FiniteWorld B) :
    v.Holds (worldConj u) ↔ ∀ i : Fin B, (v i.val ↔ u i = true) := by
  unfold worldConj
  rw [holds_sentenceConjunction]
  constructor
  · intro h i
    exact (holds_litOf v u i).mp (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h φ hφ
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hφ
    exact (holds_litOf v u i).mpr (h i)

/-- The Boolean form of `holds_worldConj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_worldConj_toPCWorld (v : BoolPCWorld) {B : ℕ} (u : FiniteWorld B) :
    (toPCWorld v).Holds (worldConj u) ↔ ∀ i : Fin B, v i.val = u i := by
  rw [holds_worldConj]
  apply forall_congr'
  intro i
  show (v i.val = true ↔ u i = true) ↔ v i.val = u i
  cases v i.val <;> cases u i <;> simp

/-- Atom bound of a literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomBound_litOf {B : ℕ} (u : FiniteWorld B) (i : Fin B) : atomBound (litOf u i) ≤ B := by
  unfold litOf
  split_ifs
  · show i.val + 1 ≤ B; exact i.isLt
  · show max (i.val + 1) 0 ≤ B; simp [i.isLt]

/-- Atom bound of a world conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomBound_worldConj {B : ℕ} (u : FiniteWorld B) : atomBound (worldConj u) ≤ B := by
  unfold worldConj
  suffices h : ∀ l : List (Fin B), atomBound (sentenceConjunction (l.map (litOf u))) ≤ B from
    h _
  intro l
  induction l with
  | nil => show max 0 0 ≤ B; simp
  | cons i l ih =>
      show max (atomBound (litOf u i)) _ ≤ B
      exact max_le (atomBound_litOf u i) ih

/-! ## Extension by `false` and restriction -/

/-- Restriction of a finite world on `B'` atoms to its first `B` atoms (`B ≤ B'`).
Source: FAF `FiniteWorld.restrict` (specialized)
Kind: D
Fidelity: exact -/
def restrFW {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') : FiniteWorld B :=
  fun i => u' ⟨i.val, lt_of_lt_of_le i.isLt hB⟩

/-- Extension of a finite world on `B` atoms to `B'` atoms by `false` (`B ≤ B'`).
Source: mandate target 0 (the extension lemma: "extended by `false` on the new atoms")
Kind: D
Fidelity: exact -/
def extFW {B B' : ℕ} (_hB : B ≤ B') (u : FiniteWorld B) : FiniteWorld B' :=
  fun i => if h : i.val < B then u ⟨i.val, h⟩ else false

/-- `restrFW` applied.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrFW_apply {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') (i : Fin B) :
    restrFW hB u' i = u' ⟨i.val, lt_of_lt_of_le i.isLt hB⟩ := rfl

/-- Restriction after extension is the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrFW_extFW {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) :
    restrFW hB (extFW hB u) = u := by
  funext i
  simp [restrFW, extFW, i.isLt]

/-- Extension by `false` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extFW_injective {B B' : ℕ} (hB : B ≤ B') : Function.Injective (extFW hB) := by
  intro u₁ u₂ h
  have := congrArg (restrFW hB) h
  rwa [restrFW_extFW, restrFW_extFW] at this

/-- Restriction to the same bound is the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma restrFW_self {B : ℕ} (u : FiniteWorld B) : restrFW le_rfl u = u := by
  funext i; rfl

/-- Restriction composes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrFW_restrFW {B B' B'' : ℕ} (h₁ : B ≤ B') (h₂ : B' ≤ B'') (u : FiniteWorld B'') :
    restrFW h₁ (restrFW h₂ u) = restrFW (h₁.trans h₂) u := by
  funext i; rfl

/-- **The extended world reads every atom as the original**: `toBoolPCWorld (extFW u) =
toBoolPCWorld u` (both read `false` beyond `B`).
Source: none: infrastructure (mandate target 0, extension lemma)
Kind: L
Fidelity: n/a -/
lemma toBoolPCWorld_extFW {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) :
    (extFW hB u).toBoolPCWorld = u.toBoolPCWorld := by
  funext a
  unfold FiniteWorld.toBoolPCWorld extFW
  by_cases ha : a < B
  · rw [dif_pos (lt_of_lt_of_le ha hB), dif_pos ha]
  · rw [dif_neg ha]
    split_ifs <;> rfl

/-- The extended world's `PCWorld` is the original's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldOf_extFW {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) :
    worldOf (extFW hB u) = worldOf u := by
  show (extFW hB u).toBoolPCWorld.toPCWorld = u.toBoolPCWorld.toPCWorld
  rw [toBoolPCWorld_extFW]

/-- The extended world pays every sentence as the original.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_extFW {B B' : ℕ} (hB : B ≤ B') (u : FiniteWorld B) (φ : Sentence) :
    (extFW hB u).payoutRat φ = u.payoutRat φ := by
  unfold FiniteWorld.payoutRat
  rw [toBoolPCWorld_extFW]

/-- The restricted world agrees with the original on atoms below `B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma toBoolPCWorld_restrFW_of_lt {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') {a : ℕ}
    (ha : a < B) : (restrFW hB u').toBoolPCWorld a = u'.toBoolPCWorld a := by
  unfold FiniteWorld.toBoolPCWorld
  rw [dif_pos ha, dif_pos (lt_of_lt_of_le ha hB)]
  rfl

/-- An atom occurring in a sentence is below its atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lt_atomBound_of_mem {φ : Sentence} {a : ℕ} (ha : a ∈ sentenceAtomCodes φ) :
    a < atomBound φ := by
  induction φ using Formula.rec' with
  | hfalsum => simp at ha
  | hatom b => simp at ha; subst ha; show a < a + 1; omega
  | himp φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_imp, Finset.mem_union] at ha
      show a < max (atomBound φ) (atomBound ψ)
      rcases ha with h | h
      · exact lt_max_of_lt_left (ihφ h)
      · exact lt_max_of_lt_right (ihψ h)
  | hand φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_and, Finset.mem_union] at ha
      show a < max (atomBound φ) (atomBound ψ)
      rcases ha with h | h
      · exact lt_max_of_lt_left (ihφ h)
      · exact lt_max_of_lt_right (ihψ h)
  | hor φ ψ ihφ ihψ =>
      rw [sentenceAtomCodes_or, Finset.mem_union] at ha
      show a < max (atomBound φ) (atomBound ψ)
      rcases ha with h | h
      · exact lt_max_of_lt_left (ihφ h)
      · exact lt_max_of_lt_right (ihψ h)

/-- The restricted world holds every sentence within the bound as the original does.
Source: FAF `eval_toBoolPCWorld_restrict` (the same fact for `restrFW`)
Kind: L
Fidelity: n/a -/
lemma holds_worldOf_restrFW {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') {φ : Sentence}
    (hφ : atomBound φ ≤ B) : (worldOf (restrFW hB u')).Holds φ ↔ (worldOf u').Holds φ := by
  apply PCWorld.holds_congr_atomCodes
  intro a ha
  show (restrFW hB u').toBoolPCWorld a = true ↔ u'.toBoolPCWorld a = true
  rw [toBoolPCWorld_restrFW_of_lt hB u' (lt_of_lt_of_le (lt_atomBound_of_mem ha) hφ)]

/-- The restricted world pays every sentence within the bound as the original.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_restrFW {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') {φ : Sentence}
    (hφ : atomBound φ ≤ B) : (restrFW hB u').payoutRat φ = u'.payoutRat φ := by
  rw [payoutRat_eq_ite, payoutRat_eq_ite]
  by_cases h : (worldOf u').Holds φ
  · rw [if_pos h, if_pos ((holds_worldOf_restrFW hB u' hφ).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((holds_worldOf_restrFW hB u' hφ).mp h'))]

/-- **A longer world pays `φ_u` iff it restricts to `u`.**
Source: bli-soto-a-041; mandate target 6 (`φ_u` characterizes `u`)
Kind: L
Fidelity: exact -/
lemma payoutRat_worldConj {B B' : ℕ} (hB : B ≤ B') (u' : FiniteWorld B') (u : FiniteWorld B) :
    u'.payoutRat (worldConj u) = if restrFW hB u' = u then 1 else 0 := by
  have key : (worldOf u').Holds (worldConj u) ↔ restrFW hB u' = u := by
    show (toPCWorld u'.toBoolPCWorld).Holds (worldConj u) ↔ _
    rw [holds_worldConj_toPCWorld]
    constructor
    · intro h; funext i
      rw [← h i]
      unfold FiniteWorld.toBoolPCWorld
      rw [dif_pos (lt_of_lt_of_le i.isLt hB)]
      rfl
    · intro h i
      rw [← h]
      unfold FiniteWorld.toBoolPCWorld
      rw [dif_pos (lt_of_lt_of_le i.isLt hB)]
      rfl
  by_cases h : restrFW hB u' = u
  · rw [if_pos h, payoutRat_of_holds (key.mpr h)]
  · rw [if_neg h, payoutRat_of_not_holds (fun h' => h (key.mp h'))]

/-- Same-bound case: a world pays `φ_u` iff it is `u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payoutRat_worldConj_self {B : ℕ} (u' u : FiniteWorld B) :
    u'.payoutRat (worldConj u) = if u' = u then 1 else 0 := by
  rw [payoutRat_worldConj le_rfl, restrFW_self]

/-! ## World measures (Soto's PC-valuation) -/

/-- **Soto's PC-valuation / `bli-coherent-mm`'s `IsWorldMeasure`**: a nonnegative weight vector
on `FiniteWorld B` of mass one, supported on `D`-consistent worlds. The formula is literally
`Cleanroom.Bli.BliCoherentMm.IsWorldMeasure` (bridge: `Base.lean`, `rfl`).
Source: bli-soto-a-037 (PDF 05 Def 1); bli-soto-a-039 (Def 3, the support clause);
[[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact (Soto's primes are the sentences of `S_n`; here the atoms are FAF's `ℕ` and
`S_n`'s sentences are compounds — the bridge is the mesh's atom bound) -/
def WMeasure {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) : Prop :=
  (∀ u, 0 ≤ w u) ∧ ∑ u, w u = 1 ∧ ∀ u, w u ≠ 0 → (worldOf u).ConsistentWith D

/-- **The sentence marginal of a weight vector**: `∑ u, w u * u.payoutRat φ` — Soto's
`P_n(φ) := ∑_{W ⊨ φ} P_n(W)` (`wMarginal_eq_sum_filter`). Literally
`Cleanroom.Bli.BliCoherentMm.marginal` (bridge: `Base.lean`, `rfl`).
Source: bli-soto-a-037 (PDF 05 Def 1); [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact -/
def wMarginal {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) : ℚ :=
  ∑ u, w u * u.payoutRat φ

open Classical in
/-- **The bundle identity** (bli-soto-a-037): the marginal of `φ` is the mass of the worlds
satisfying it — a share of `φ` is the bundle of the shares of those worlds.
Source: bli-soto-a-037 (PDF 05 Def 1, "`P_n(φ) := ∑_{W_n ⊨ φ} P_n(W_n)`"); mandate target 5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem wMarginal_eq_sum_filter {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    wMarginal w φ = ∑ u ∈ univ.filter (fun u : FiniteWorld B => (worldOf u).Holds φ), w u := by
  unfold wMarginal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  rw [payoutRat_eq_ite]
  split_ifs <;> simp

/-- The marginal of `φ_u` is the weight of `u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_worldConj {B : ℕ} (w : FiniteWorld B → ℚ) (u : FiniteWorld B) :
    wMarginal w (worldConj u) = w u := by
  unfold wMarginal
  simp only [payoutRat_worldConj_self, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ u w, if_pos (mem_univ u)]

/-- The marginal of a shorter `φ_u` is the mass of the fiber over `u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_worldConj_restr {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B' → ℚ)
    (u : FiniteWorld B) :
    wMarginal w (worldConj u) = ∑ u' ∈ univ.filter (fun u' => restrFW hB u' = u), w u' := by
  unfold wMarginal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u' _
  rw [payoutRat_worldConj hB]
  split_ifs <;> simp

/-- Marginals of a nonnegative vector are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_nonneg {B : ℕ} {w : FiniteWorld B → ℚ} (hw : ∀ u, 0 ≤ w u) (φ : Sentence) :
    0 ≤ wMarginal w φ :=
  Finset.sum_nonneg fun u _ => mul_nonneg (hw u) (payoutRat_nonneg u φ)

/-- Marginals of a probability vector are at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_le_one {B : ℕ} {w : FiniteWorld B → ℚ} (hw : ∀ u, 0 ≤ w u) (hw1 : ∑ u, w u = 1)
    (φ : Sentence) : wMarginal w φ ≤ 1 := by
  unfold wMarginal
  calc ∑ u, w u * u.payoutRat φ ≤ ∑ u, w u :=
        Finset.sum_le_sum fun u _ => mul_le_of_le_one_right (hw u) (payoutRat_le_one u φ)
    _ = 1 := hw1

/-- The marginal of `⊤` is the total mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wMarginal_top {B : ℕ} (w : FiniteWorld B → ℚ) : wMarginal w ⊤ = ∑ u, w u := by
  unfold wMarginal
  apply Finset.sum_congr rfl
  intro u _
  rw [payoutRat_of_holds (PCWorld.holds_top _), mul_one]

/-- **Pushing a vector forward along extension by `false` preserves every marginal.**
Source: none: infrastructure (mandate target 0, extension lemma)
Kind: L
Fidelity: n/a -/
lemma wMarginal_extend {B B' : ℕ} (hB : B ≤ B') (w : FiniteWorld B → ℚ) (φ : Sentence) :
    wMarginal (fun u' => if extFW hB (restrFW hB u') = u' then w (restrFW hB u') else 0) φ =
      wMarginal w φ := by
  unfold wMarginal
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have himage : (univ : Finset (FiniteWorld B')).filter (fun u' => extFW hB (restrFW hB u') = u') =
      (univ : Finset (FiniteWorld B)).image (extFW hB) := by
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨restrFW hB u', h⟩
    · rintro ⟨u, rfl⟩; rw [restrFW_extFW]
  rw [himage, Finset.sum_image (fun u₁ _ u₂ _ h => extFW_injective hB h)]
  apply Finset.sum_congr rfl
  intro u _
  rw [restrFW_extFW, payoutRat_extFW]

/-! ## Soto's "respects `D̄`" (bli-soto-a-039) -/

/-- **Soto's Def 3 and its "equivalently"**: for a probability vector on finite worlds, "every
sentence of `D` has marginal `1`" iff "every positive-weight world satisfies every sentence of
`D`" — the support clause of `WMeasure`. No atom bound is needed: consistency is read in
`worldOf u` (atoms beyond `B` read `false`).
Source: bli-soto-a-039 (PDF 05 Def 3); mandate target 5
Kind: P
Fidelity: exact
Hyps: (a) `hw0`, `hw1` (a probability vector) -/
theorem respects_iff {B : ℕ} {w : FiniteWorld B → ℚ} (hw0 : ∀ u, 0 ≤ w u)
    (hw1 : ∑ u, w u = 1) (D : Finset Sentence) :
    (∀ φ ∈ D, wMarginal w φ = 1) ↔ ∀ u, w u ≠ 0 → (worldOf u).ConsistentWith D := by
  constructor
  · intro h u hu φ hφ
    have h1 := h φ hφ
    unfold wMarginal at h1
    rw [← hw1] at h1
    have hle : ∀ u ∈ (univ : Finset (FiniteWorld B)), w u * u.payoutRat φ ≤ w u :=
      fun u _ => mul_le_of_le_one_right (hw0 u) (payoutRat_le_one u φ)
    have := (Finset.sum_eq_sum_iff_of_le hle).mp h1 u (mem_univ u)
    have hp : u.payoutRat φ = 1 := by
      rcases mul_right_eq_self₀.mp this with h' | h'
      · exact h'
      · exact absurd h' hu
    rw [payoutRat_eq_ite] at hp
    by_contra hcon
    rw [if_neg hcon] at hp
    exact zero_ne_one hp
  · intro h φ hφ
    unfold wMarginal
    rw [← hw1]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : w u = 0
    · rw [hu, zero_mul]
    · rw [payoutRat_of_holds (h u hu φ hφ), mul_one]

/-- A `WMeasure` quotes every stage sentence at `1` (one direction of `respects_iff`, in the
record's vocabulary).
Source: bli-soto-a-039; mandate target 5
Kind: L
Fidelity: exact -/
lemma WMeasure.wMarginal_of_mem {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : WMeasure w D) {φ : Sentence} (hφ : φ ∈ D) : wMarginal w φ = 1 :=
  (respects_iff hw.1 hw.2.1 D).mpr hw.2.2 φ hφ

/-- The unit-mass tautology marginal of a `WMeasure`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma WMeasure.wMarginal_top {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : WMeasure w D) : wMarginal w ⊤ = 1 := by
  rw [Cleanroom.Bli.BliMeasure.wMarginal_top, hw.2.1]

end Cleanroom.Bli.BliMeasure
