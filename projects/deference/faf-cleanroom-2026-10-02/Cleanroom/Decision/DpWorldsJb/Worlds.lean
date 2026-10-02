import Cleanroom.Decision.DpWorldsJb.Defs
import Mathlib.Order.PrimeIdeal
import Mathlib.Order.PrimeSeparator
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Data.Set.Finite.Basic

/-!
# Worlds ≃ two-valued probabilities; prime filters; existence and witness-less worlds

* **T1** `world_equiv_twoValuedProb`: v2 Definition 1 worlds are exactly the two-valued
  probabilities, for every `(E, J)` — both directions from the two definitions of record.
* The bridge `world_iff_primeFilter`: for `J = ∅`, worlds are the prime filters of `E`
  (Mathlib's `Order.PFilter.IsPrime`, whose definition includes properness) — Remark 0.1's
  "constraints 1–3 are exactly the ultrafilter axioms", stated over Mathlib's object.
* **T5(a)** `exists_world_mem`, `worlds_separate`: worlds exist in abundance at `J = ∅` (the
  prime ideal theorem, `DistribLattice.prime_ideal_of_disjoint_filter_ideal`).
* **T5(b)** `worldEmptyEquivUltrafilter`, `hyperfilter_world_not_designated`: on `Set ℕ`, the
  hyperfilter world contains `univ = ⋃ {n}` and no `{n}`, so it is a `World ∅` and not a world
  for the designation of the complemented singleton family; `principalWorld`,
  `worldJ₁_equiv_nat`: for that designation the worlds are exactly the points.
* **T5(c)** the finite–cofinite algebra `finCofinite` and its cofinite world.
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-! ### T1: worlds ≃ two-valued probabilities -/

namespace World

variable {J : Designation E}

/-- The indicator `𝟙_ω : E → ℝ` of a world.
Source: [[decision-problems-v2]] §1 ("read 2-valuedly")
Kind: D
Fidelity: exact
Hyps: n/a -/
def indicator (ω : World J) : E → ℝ := fun X => if X ∈ ω then 1 else 0

theorem indicator_of_mem (ω : World J) {X : E} (h : X ∈ ω) : ω.indicator X = 1 := by
  simp [indicator, h]

theorem indicator_of_notMem (ω : World J) {X : E} (h : X ∉ ω) : ω.indicator X = 0 := by
  simp [indicator, h]

theorem indicator_eq_one_iff (ω : World J) (X : E) : ω.indicator X = 1 ↔ X ∈ ω := by
  unfold indicator
  split_ifs with h <;> simp [h]

/-- A world's indicator is a probability on `(E, J)`: finitely additive by Remark 0.1
(finite witnessing), continuous along designated meets by constraint 4 and its free converse.
Source: [[decision-problems-v2]] §1 ("Worlds are exactly the 2-valued probabilities", ⇒)
Kind: P
Fidelity: exact
Hyps: (a) -/
def toProb (ω : World J) : Prob J where
  P := ω.indicator
  nonneg := by
    intro X
    unfold indicator
    split_ifs <;> norm_num
  top := ω.indicator_of_mem ω.top_mem
  add := by
    intro X Y h
    by_cases hX : X ∈ ω <;> by_cases hY : Y ∈ ω
    · exfalso
      have := ω.meet _ _ hX hY
      rw [disjoint_iff.1 h] at this
      exact ω.bot_notMem this
    · rw [ω.indicator_of_mem ((ω.sup_mem_iff X Y).2 (Or.inl hX)), ω.indicator_of_mem hX,
        ω.indicator_of_notMem hY]
      norm_num
    · rw [ω.indicator_of_mem ((ω.sup_mem_iff X Y).2 (Or.inr hY)), ω.indicator_of_mem hY,
        ω.indicator_of_notMem hX]
      norm_num
    · have : X ⊔ Y ∉ ω := fun h => (ω.mem_or_mem_of_sup_mem h).elim hX hY
      rw [ω.indicator_of_notMem this, ω.indicator_of_notMem hX, ω.indicator_of_notMem hY]
      norm_num
  cont := by
    intro D hD m hm
    by_cases hmω : m ∈ ω
    · have hset : {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = ω.indicator (F.inf id)} = {1} := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨F, hF, rfl⟩
          exact ω.indicator_of_mem
            (ω.finset_inf_mem F fun A hA => ω.mem_of_isGLB_mem hm hmω A (hF hA))
        · rintro rfl
          exact ⟨∅, by simp, by rw [Finset.inf_empty, ω.indicator_of_mem ω.top_mem]⟩
      rw [hset, ω.indicator_of_mem hmω]
      exact isGLB_singleton
    · have : ∃ A ∈ D, A ∉ ω := by
        by_contra hc
        push Not at hc
        exact hmω (ω.designated D hD hc m hm)
      obtain ⟨A, hA, hAω⟩ := this
      have h0 : (0 : ℝ) ∈ {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = ω.indicator (F.inf id)} :=
        ⟨{A}, by simpa using hA, by rw [Finset.inf_singleton, id, ω.indicator_of_notMem hAω]⟩
      rw [ω.indicator_of_notMem hmω]
      constructor
      · rintro r ⟨F, -, rfl⟩
        unfold indicator
        split_ifs <;> norm_num
      · intro b hb
        exact hb h0

theorem toProb_twoValued (ω : World J) : TwoValued ω.toProb.P := by
  intro X
  show ω.indicator X = 0 ∨ ω.indicator X = 1
  unfold indicator
  split_ifs <;> simp

end World

namespace Prob

variable {J : Designation E}

/-- Finite meets of probability-one events have probability one.
Source: [[decision-problems-v2]] §1
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem finset_inf_eq_one (P : Prob J) (F : Finset E) (h : ∀ A ∈ F, P.P A = 1) :
    P.P (F.inf id) = 1 := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact P.top
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun A hA => h A (Finset.mem_insert_of_mem hA)
    have := P.inf_ge (id a) (s.inf id)
    have := P.le_one (id a ⊓ s.inf id)
    simp only [id] at *
    linarith

/-- The probability-one events of a two-valued probability form a world: constraint 1 from
`P X + P Xᶜ = 1`, 2 from monotonicity, 3 from `P (X ⊓ Y) ≥ P X + P Y - 1`, 4 from continuity
along the designated meet read two-valuedly.
Source: [[decision-problems-v2]] §1 ("Worlds are exactly the 2-valued probabilities", ⇐)
Kind: P
Fidelity: exact
Hyps: (a) -/
def toWorld (P : Prob J) (hP : TwoValued P.P) : World J where
  carrier := {X | P.P X = 1}
  exactly_one := by
    intro X
    simp only [Set.mem_setOf_eq]
    rw [P.compl]
    rcases hP X with h | h <;> rw [h] <;> norm_num
  upward := by
    intro X Y hX hle
    simp only [Set.mem_setOf_eq] at *
    exact le_antisymm (P.le_one Y) (hX ▸ P.mono hle)
  meet := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have := P.inf_ge X Y
    have := P.le_one (X ⊓ Y)
    linarith
  designated := by
    intro D hD hall m hm
    simp only [Set.mem_setOf_eq] at *
    have hc := P.cont D hD m hm
    have hset : {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = P.P (F.inf id)} = {1} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨F, hF, rfl⟩
        exact P.finset_inf_eq_one F fun A hA => hall A (hF hA)
      · rintro rfl
        exact ⟨∅, by simp, by rw [Finset.inf_empty, P.top]⟩
    rw [hset] at hc
    exact hc.unique isGLB_singleton

theorem mem_toWorld (P : Prob J) (hP : TwoValued P.P) (X : E) :
    X ∈ P.toWorld hP ↔ P.P X = 1 := Iff.rfl

end Prob

/-- **T1.** Worlds of `(E, J)` are exactly the two-valued probabilities on `(E, J)`, for every
Boolean algebra `E` and designation `J`: `ω ↦ 𝟙_ω` and `P ↦ {X | P X = 1}` are mutually
inverse. Both directions are proved from Definition 1 and §1's probability condition; neither
notion is defined as the other.
Source: [[decision-problems-v2]] §1 line 28 ("Worlds are exactly the 2-valued probabilities") | dp-core-001
Kind: P
Fidelity: exact (including the designated case)
Hyps: (a) -/
def world_equiv_twoValuedProb (J : Designation E) :
    World J ≃ {P : Prob J // TwoValued P.P} where
  toFun ω := ⟨ω.toProb, ω.toProb_twoValued⟩
  invFun P := P.1.toWorld P.2
  left_inv ω := by
    ext X
    exact ω.indicator_eq_one_iff X
  right_inv P := by
    apply Subtype.ext
    apply Prob.ext
    funext X
    show (if P.1.P X = 1 then (1 : ℝ) else 0) = P.1.P X
    rcases P.2 X with h | h <;> rw [h] <;> norm_num

theorem world_equiv_twoValuedProb_apply (J : Designation E) (ω : World J) (X : E) :
    (world_equiv_twoValuedProb J ω).1.P X = if X ∈ ω then 1 else 0 := rfl

theorem world_equiv_twoValuedProb_symm_mem (J : Designation E) (P : {P : Prob J // TwoValued P.P})
    (X : E) : X ∈ (world_equiv_twoValuedProb J).symm P ↔ P.1.P X = 1 := Iff.rfl

/-! ### The prime-filter bridge (Remark 0.1) -/

/-- **Bridge.** For `J = ∅`, a set `s ⊆ E` is the carrier of a world iff it is (the carrier
of) a prime filter of `E` in Mathlib's sense (`Order.PFilter.IsPrime`: the complement is an
ideal, which includes properness). Constraints 1–3 are "exactly the ultrafilter axioms".
Source: [[decision-problems-v2]] §0 Remark 0.1 | dp-core-001
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem world_iff_primeFilter (s : Set E) :
    (∃ ω : World (∅ : Designation E), ω.carrier = s) ↔
      ∃ F : Order.PFilter E, Order.PFilter.IsPrime F ∧ (F : Set E) = s := by
  constructor
  · rintro ⟨ω, rfl⟩
    have hF : Order.IsPFilter ω.carrier := by
      refine Order.IsPFilter.of_def ⟨⊤, ω.top_mem⟩ ?_ ?_
      · intro X hX Y hY
        exact ⟨X ⊓ Y, ω.meet X Y hX hY, inf_le_left, inf_le_right⟩
      · intro X Y hle hX
        exact ω.upward X Y hX hle
    refine ⟨hF.toPFilter, ⟨?_⟩, ?_⟩
    · have hcoe : (hF.toPFilter : Set E) = ω.carrier := by
        ext X
        exact Order.Ideal.mem_toIdeal hF
      rw [hcoe]
      refine ⟨?_, ⟨⊥, ω.bot_notMem⟩, ?_⟩
      · intro X Y hle hY hX
        exact hY (ω.upward Y X hX hle)
      · intro X hX Y hY
        refine ⟨X ⊔ Y, ?_, le_sup_left, le_sup_right⟩
        intro h
        exact (ω.mem_or_mem_of_sup_mem h).elim hX hY
    · ext X
      exact Order.Ideal.mem_toIdeal hF
  · rintro ⟨F, ⟨hF⟩, rfl⟩
    refine ⟨⟨(F : Set E), ?_, ?_, ?_, ?_⟩, rfl⟩
    · intro X
      constructor
      · intro hX hXc
        have hbot : (⊥ : E) ∈ F := by
          have := Order.PFilter.inf_mem hX hXc
          rwa [inf_compl_eq_bot] at this
        obtain ⟨Y, hY⟩ := hF.Nonempty
        exact hY (Order.PFilter.mem_of_le bot_le hbot)
      · intro hXc
        by_contra hX
        obtain ⟨z, hz, hXz, hXcz⟩ := hF.Directed X hX Xᶜ hXc
        have htop : (⊤ : E) ∈ (F : Set E)ᶜ :=
          hF.IsLowerSet (by rw [← sup_compl_eq_top (x := X)]; exact sup_le hXz hXcz) hz
        exact htop Order.PFilter.top_mem
    · intro X Y hX hle
      exact Order.PFilter.mem_of_le hle hX
    · intro X Y hX hY
      exact Order.PFilter.inf_mem hX hY
    · intro D hD
      exact hD.elim

/-! ### T5(a): existence at `J = ∅` (the prime ideal theorem) -/

/-- **T5(a).** Every non-`⊥` event lies in some world for `J = ∅`: the prime ideal theorem
(`DistribLattice.prime_ideal_of_disjoint_filter_ideal`, Zorn) applied to the principal filter
at `X` and the zero ideal; the complement of the prime ideal is a world.
Source: [[decision-problems-v2]] Appendix A "Existence at `J = ∅`" (line 323) | dp-core-2-056(a)
Kind: P
Fidelity: exact ("undesignated worlds always exist in abundance")
Hyps: (a) -/
theorem exists_world_mem {X : E} (hX : X ≠ ⊥) : ∃ ω : World (∅ : Designation E), X ∈ ω := by
  have hdisj : Disjoint ((Order.PFilter.principal X : Order.PFilter E) : Set E)
      ((Order.Ideal.principal (⊥ : E) : Order.Ideal E) : Set E) := by
    rw [Set.disjoint_left]
    intro Y hYF hYI
    rw [SetLike.mem_coe, Order.PFilter.mem_principal] at hYF
    rw [SetLike.mem_coe, Order.Ideal.mem_principal] at hYI
    exact hX (le_bot_iff.1 (hYF.trans hYI))
  obtain ⟨I, hI, -, hdis⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
  haveI := hI
  refine ⟨⟨{Y | Y ∉ I}, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro Y
    simp only [Set.mem_setOf_eq, not_not]
    constructor
    · intro hY
      exact hI.mem_or_compl_mem.resolve_left hY
    · intro hYc hY
      have := Order.Ideal.sup_mem hY hYc
      rw [sup_compl_eq_top] at this
      exact hI.toIsProper.top_notMem this
  · intro Y Z hY hle hZ
    exact hY (I.lower hle hZ)
  · intro Y Z hY hZ hYZ
    exact ((Order.Ideal.isPrime_iff_mem_or_mem.1 hI) hYZ).elim hY hZ
  · intro D hD
    exact hD.elim
  · show X ∉ I
    intro hXI
    exact Set.disjoint_left.1 hdis
      (by rw [SetLike.mem_coe, Order.PFilter.mem_principal]) hXI

/-- Worlds exist for `J = ∅` on every nontrivial Boolean algebra (on the trivial algebra
`⊤ = ⊥` there are none, since `⊤ ∈ ω` and `⊥ ∉ ω`).
Source: [[decision-problems-v2]] Appendix A "Existence at `J = ∅`"
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem nonempty_world [Nontrivial E] : Nonempty (World (∅ : Designation E)) :=
  let ⟨ω, _⟩ := exists_world_mem (top_ne_bot (α := E))
  ⟨ω⟩

/-- Worlds separate events: distinct events are distinguished by some world for `J = ∅`.
Source: [[decision-problems-v2]] Appendix A "Existence at `J = ∅`" ("ultrafilters separate every Boolean algebra")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem worlds_separate {X Y : E} (h : X ≠ Y) :
    ∃ ω : World (∅ : Designation E), ¬ (X ∈ ω ↔ Y ∈ ω) := by
  have key : ∀ {X Y : E}, X \ Y ≠ ⊥ → ∃ ω : World (∅ : Designation E), X ∈ ω ∧ Y ∉ ω := by
    intro X Y hne
    obtain ⟨ω, hω⟩ := exists_world_mem hne
    refine ⟨ω, ω.upward _ _ hω sdiff_le, ?_⟩
    have : Yᶜ ∈ ω := ω.upward _ _ hω (by rw [sdiff_eq]; exact inf_le_right)
    exact (ω.compl_mem_iff Y).1 this
  by_cases h1 : X \ Y = ⊥
  · have h2 : Y \ X ≠ ⊥ := by
      intro h2
      exact h (le_antisymm (sdiff_eq_bot_iff.1 h1) (sdiff_eq_bot_iff.1 h2))
    obtain ⟨ω, hY, hX⟩ := key h2
    exact ⟨ω, fun hiff => hX (hiff.2 hY)⟩
  · obtain ⟨ω, hX, hY⟩ := key h1
    exact ⟨ω, fun hiff => hY (hiff.1 hX)⟩

/-! ### T5(b): power-set worlds are ultrafilters; the hyperfilter world -/

section PowerSet

variable {α : Type*}

/-- The filter of a `J = ∅` world on a power set.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def World.toFilter (ω : World (∅ : Designation (Set α))) : Filter α where
  sets := ω.carrier
  univ_sets := ω.top_mem
  sets_of_superset := fun h hle => ω.upward _ _ h hle
  inter_sets := fun h₁ h₂ => ω.meet _ _ h₁ h₂

theorem World.mem_toFilter (ω : World (∅ : Designation (Set α))) (s : Set α) :
    s ∈ ω.toFilter ↔ s ∈ ω := Iff.rfl

/-- The ultrafilter of a `J = ∅` world on a power set (constraint 1 is `ofComplNotMemIff`).
Source: [[decision-problems-v2]] §0 Remark 0.1
Kind: L
Fidelity: exact
Hyps: n/a -/
def World.toUltrafilter (ω : World (∅ : Designation (Set α))) : Ultrafilter α :=
  Ultrafilter.ofComplNotMemIff ω.toFilter fun s => (ω.exactly_one s).symm

theorem World.mem_toUltrafilter (ω : World (∅ : Designation (Set α))) (s : Set α) :
    s ∈ ω.toUltrafilter ↔ s ∈ ω := Iff.rfl

/-- The `J = ∅` world of an ultrafilter.
Source: [[decision-problems-v2]] §0 Remark 0.1
Kind: L
Fidelity: exact
Hyps: n/a -/
def ultrafilterToWorld (U : Ultrafilter α) : World (∅ : Designation (Set α)) where
  carrier := {s | s ∈ U}
  exactly_one := fun s => (Ultrafilter.compl_notMem_iff (f := U) (s := s)).symm
  upward := fun _ _ h hle => Filter.mem_of_superset h hle
  meet := fun _ _ h₁ h₂ => Filter.inter_mem h₁ h₂
  designated := fun _ hD => hD.elim

theorem mem_ultrafilterToWorld (U : Ultrafilter α) (s : Set α) : s ∈ ultrafilterToWorld U ↔ s ∈ U :=
  Iff.rfl

/-- **T5(b) bridge.** On a power set, `J = ∅` worlds are exactly Mathlib's ultrafilters.
Source: [[decision-problems-v2]] §0 Remark 0.1; Appendix A "Witness-less worlds" | dp-core-2-057
Kind: P
Fidelity: exact
Hyps: (a) -/
def worldEmptyEquivUltrafilter (α : Type*) : World (∅ : Designation (Set α)) ≃ Ultrafilter α where
  toFun := World.toUltrafilter
  invFun := ultrafilterToWorld
  left_inv ω := by
    ext s
    exact Iff.rfl
  right_inv U := by
    apply Ultrafilter.ext
    intro s
    exact Iff.rfl

/-- The point world `{s | x ∈ s}` on a power set: a world for **every** designation `J` on
`Set α`, because in a complete lattice an existing infimum of a family is its intersection.
Source: [[decision-problems-v2]] Appendix A "Typing the designation" (principal ultrafilters)
Kind: L
Fidelity: exact
Hyps: n/a -/
def principalWorld (J : Designation (Set α)) (x : α) : World J where
  carrier := {s | x ∈ s}
  exactly_one := fun s => by simp
  upward := fun _ _ h hle => hle h
  meet := fun _ _ h₁ h₂ => ⟨h₁, h₂⟩
  designated := by
    intro D _ hall m hm
    rw [hm.sInf_eq.symm]
    exact Set.mem_sInter.2 hall

theorem mem_principalWorld (J : Designation (Set α)) (x : α) (s : Set α) :
    s ∈ principalWorld J x ↔ x ∈ s := Iff.rfl

/-- A world containing the singleton `{x}` is the point world at `x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem World.eq_principalWorld_of_singleton_mem {J : Designation (Set α)} (ω : World J) {x : α}
    (hx : ({x} : Set α) ∈ ω) : ω = principalWorld J x := by
  ext s
  constructor
  · intro hs
    by_contra hxs
    have : s ⊆ ({x} : Set α)ᶜ := fun y hy hyx => hxs (by rw [Set.mem_singleton_iff] at hyx; rw [hyx] at hy; exact hy)
    have := ω.upward _ _ hs this
    exact (ω.compl_mem_iff _).1 this hx
  · intro hxs
    exact ω.upward _ _ hx (Set.singleton_subset_iff.2 hxs)

end PowerSet

/-! #### The hyperfilter world on `Set ℕ` -/

/-- The world of the hyperfilter (Mathlib's `Filter.hyperfilter ℕ = Ultrafilter.of cofinite`, one
ultrafilter extending the cofinite filter).
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds" (line 325) | dp-core-2-057
Kind: D
Fidelity: exact for one instance; the appendix's "any ultrafilter extending the cofinite filter"
is `free_ultrafilter_not_J₁_world` (every free ultrafilter fails `J₁`, via `worldJ₁_equiv_nat`)
Hyps: n/a -/
def hyperfilterWorld : World (∅ : Designation (Set ℕ)) :=
  (worldEmptyEquivUltrafilter ℕ).symm (Filter.hyperfilter ℕ)

theorem mem_hyperfilterWorld (s : Set ℕ) : s ∈ hyperfilterWorld ↔ s ∈ Filter.hyperfilter ℕ :=
  Iff.rfl

theorem univ_mem_hyperfilterWorld : Set.univ ∈ hyperfilterWorld := hyperfilterWorld.top_mem

theorem singleton_notMem_hyperfilterWorld (n : ℕ) : ({n} : Set ℕ) ∉ hyperfilterWorld :=
  Filter.notMem_hyperfilter_of_finite (Set.finite_singleton n)

/-- `ℕ = ⋃ₙ {n}`: `univ` is the supremum of the singleton family in `Set ℕ`.
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds"
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isLUB_singletons_univ : IsLUB (Set.range fun n : ℕ => ({n} : Set ℕ)) Set.univ := by
  constructor
  · rintro s ⟨n, rfl⟩
    exact Set.subset_univ _
  · intro b hb x _
    exact hb ⟨x, rfl⟩ (Set.mem_singleton x)

/-- The complemented singleton family has infimum `∅` in `Set ℕ`.
Source: [[decision-problems-v2]] Appendix A "Typing the designation"
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isGLB_compl_singletons_empty :
    IsGLB (Set.range fun n : ℕ => ({n}ᶜ : Set ℕ)) ∅ := by
  constructor
  · rintro s ⟨n, rfl⟩
    exact Set.empty_subset _
  · intro b hb x hx
    exact (hb ⟨x, rfl⟩ hx) (Set.mem_singleton x)

/-- The designation `J₁` of the single family `{ {n}ᶜ | n : ℕ }` (the singleton family in the
official meet language; its infimum is `∅`).
Source: [[decision-problems-v2]] Appendix A "Typing the designation" ("designating the singleton family bans exactly the free ultrafilters")
Kind: D
Fidelity: exact
Hyps: n/a -/
def J₁ : Designation (Set ℕ) :=
  ⟨{Set.range fun n : ℕ => ({n}ᶜ : Set ℕ)}, by
    rintro D hD
    rw [Set.mem_singleton_iff] at hD
    exact ⟨∅, hD ▸ isGLB_compl_singletons_empty⟩⟩

/-- **T5(b).** The hyperfilter world is a `World ∅` containing `univ = ⋃ₙ {n}` but no `{n}`
(a "witness-less" world); it is **not** a world for `J₁`, where the complemented singleton
family is designated: it contains every `{n}ᶜ` but not their designated meet `∅`. So
constraint 4 has content.
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds" (line 325) | dp-core-2-057
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem hyperfilter_world_not_designated :
    (Set.univ ∈ hyperfilterWorld ∧ ∀ n, ({n} : Set ℕ) ∉ hyperfilterWorld) ∧
      ¬ ∃ ω : World J₁, ω.carrier = hyperfilterWorld.carrier := by
  refine ⟨⟨univ_mem_hyperfilterWorld, singleton_notMem_hyperfilterWorld⟩, ?_⟩
  rintro ⟨ω, hω⟩
  have hall : ∀ A ∈ Set.range fun n : ℕ => ({n}ᶜ : Set ℕ), A ∈ ω := by
    rintro A ⟨n, rfl⟩
    show ({n}ᶜ : Set ℕ) ∈ ω.carrier
    rw [hω]
    exact (hyperfilterWorld.compl_mem_iff _).2 (singleton_notMem_hyperfilterWorld n)
  have := ω.designated _ (Set.mem_singleton _) hall ∅ isGLB_compl_singletons_empty
  exact ω.bot_notMem this

/-- The `J₁`-worlds are a proper subset of the `∅`-worlds (as carriers).
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds"
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem worldJ₁_carriers_ssubset :
    Set.range (World.carrier : World J₁ → Set (Set ℕ)) ⊂
      Set.range (World.carrier : World (∅ : Designation (Set ℕ)) → Set (Set ℕ)) := by
  constructor
  · rintro _ ⟨ω, rfl⟩
    exact ⟨ω.restrict (by simp [Designation.empty_val]), rfl⟩
  · intro h
    obtain ⟨ω, hω⟩ := h ⟨hyperfilterWorld, rfl⟩
    exact hyperfilter_world_not_designated.2 ⟨ω, hω⟩

/-- Every `J₁`-world contains some singleton, hence is a point world.
Source: [[decision-problems-v2]] Appendix A "Typing the designation"
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem World.exists_singleton_mem_J₁ (ω : World J₁) : ∃ n, ({n} : Set ℕ) ∈ ω := by
  by_contra h
  push Not at h
  have hall : ∀ A ∈ Set.range fun n : ℕ => ({n}ᶜ : Set ℕ), A ∈ ω := by
    rintro A ⟨n, rfl⟩
    exact (ω.compl_mem_iff _).2 (h n)
  exact ω.bot_notMem (ω.designated _ (Set.mem_singleton _) hall ∅ isGLB_compl_singletons_empty)

/-- **T5(b), converse.** With the singleton family designated, the worlds of `Set ℕ` are
exactly the points: `World J₁ ≃ ℕ`.
Source: [[decision-problems-v2]] Appendix A "Typing the designation" ("designating the singleton family bans exactly the free ultrafilters")
Kind: C
Fidelity: exact
Hyps: (a) -/
def worldJ₁_equiv_nat : World J₁ ≃ ℕ where
  toFun ω := Classical.choose ω.exists_singleton_mem_J₁
  invFun n := principalWorld J₁ n
  left_inv ω := (ω.eq_principalWorld_of_singleton_mem
    (Classical.choose_spec ω.exists_singleton_mem_J₁)).symm
  right_inv n := by
    have h := Classical.choose_spec (principalWorld J₁ n).exists_singleton_mem_J₁
    rw [mem_principalWorld, Set.mem_singleton_iff] at h
    exact h.symm

/-- **T5(b), the appendix's "any".** Every free ultrafilter on `ℕ` (no singleton in it) is a
`J = ∅` world that is **not** a `J₁` world: a `J₁`-world contains a singleton.
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds" ("any ultrafilter extending the cofinite filter") and "Typing the designation" | dp-core-2-057
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem free_ultrafilter_not_J₁_world (U : Ultrafilter ℕ) (hU : ∀ n, ({n} : Set ℕ) ∉ U) :
    ¬ ∃ ω : World J₁, ω.carrier = ((worldEmptyEquivUltrafilter ℕ).symm U).carrier := by
  rintro ⟨ω, hω⟩
  obtain ⟨n, hn⟩ := ω.exists_singleton_mem_J₁
  have h : ({n} : Set ℕ) ∈ ((worldEmptyEquivUltrafilter ℕ).symm U).carrier := hω ▸ hn
  exact hU n h

/-! ### T5(c): the finite–cofinite algebra -/

/-- The finite–cofinite algebra on `ℕ`, as a Boolean subalgebra of `Set ℕ`.
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds" (line 325) | dp-core-2-057
Kind: D
Fidelity: exact
Hyps: n/a -/
def finCofinite : BooleanSubalgebra (Set ℕ) where
  carrier := {s | s.Finite ∨ sᶜ.Finite}
  supClosed' := by
    intro s hs t ht
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · exact Or.inl (hs.union ht)
      · exact Or.inr (by show ((s ∪ t)ᶜ).Finite; rw [Set.compl_union]; exact ht.subset Set.inter_subset_right)
    · exact Or.inr (by show ((s ∪ t)ᶜ).Finite; rw [Set.compl_union]; exact hs.subset Set.inter_subset_left)
  infClosed' := by
    intro s hs t ht
    rcases hs with hs | hs
    · exact Or.inl (hs.subset Set.inter_subset_left)
    · rcases ht with ht | ht
      · exact Or.inl (ht.subset Set.inter_subset_right)
      · exact Or.inr (by show ((s ∩ t)ᶜ).Finite; rw [Set.compl_inter]; exact hs.union ht)
  compl_mem' := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inr (by rwa [compl_compl])
    · exact Or.inl hs
  bot_mem' := Or.inl Set.finite_empty

theorem mem_finCofinite (s : Set ℕ) : s ∈ finCofinite ↔ s.Finite ∨ sᶜ.Finite := Iff.rfl

/-- In the finite–cofinite algebra no set is both finite and cofinite.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem finCofinite_not_both (s : finCofinite) : ¬ ((s : Set ℕ).Finite ∧ (s : Set ℕ)ᶜ.Finite) :=
  fun h => Set.infinite_univ (by rw [← Set.union_compl_self (s : Set ℕ)]; exact h.1.union h.2)

/-- **T5(c).** The cofinite sets form a world of the finite–cofinite algebra for `J = ∅`: it
contains `univ`, no singleton, and `univ` is the supremum of the singletons *in* the
subalgebra — explicitly witness-less (Appendix A: "no choice principle is needed"; stated
classically here, the run does not track constructivity).
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds" (line 325) | dp-core-2-057
Kind: N+
Fidelity: exact
Hyps: (a) -/
def cofiniteWorld : World (∅ : Designation finCofinite) where
  carrier := {s | (s : Set ℕ)ᶜ.Finite}
  exactly_one := by
    intro s
    show (s : Set ℕ)ᶜ.Finite ↔ ¬ ((sᶜ : finCofinite) : Set ℕ)ᶜ.Finite
    rw [BooleanSubalgebra.val_compl, compl_compl]
    constructor
    · intro h h'
      exact finCofinite_not_both s ⟨h', h⟩
    · intro h
      exact s.2.resolve_left h
  upward := by
    intro s t hs hle
    simp only [Set.mem_setOf_eq] at *
    exact hs.subset (Set.compl_subset_compl.2 hle)
  meet := by
    intro s t hs ht
    show ((s ⊓ t : finCofinite) : Set ℕ)ᶜ.Finite
    rw [BooleanSubalgebra.val_inf]
    show (((s : Set ℕ) ∩ (t : Set ℕ))ᶜ).Finite
    rw [Set.compl_inter]
    exact hs.union ht
  designated := fun _ hD => hD.elim

theorem top_mem_cofiniteWorld : (⊤ : finCofinite) ∈ cofiniteWorld := cofiniteWorld.top_mem

theorem singleton_notMem_cofiniteWorld (n : ℕ) :
    (⟨{n}, Or.inl (Set.finite_singleton n)⟩ : finCofinite) ∉ cofiniteWorld := by
  show ¬ ({n} : Set ℕ)ᶜ.Finite
  exact (Set.finite_singleton n).infinite_compl

/-- `⊤` is the supremum of the singletons inside the finite–cofinite algebra.
Source: [[decision-problems-v2]] Appendix A "Witness-less worlds"
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isLUB_singletons_finCofinite :
    IsLUB (Set.range fun n : ℕ => (⟨{n}, Or.inl (Set.finite_singleton n)⟩ : finCofinite))
      (⊤ : finCofinite) := by
  constructor
  · rintro s ⟨n, rfl⟩
    exact le_top
  · intro b hb
    show ((⊤ : finCofinite) : Set ℕ) ≤ (b : Set ℕ)
    rw [BooleanSubalgebra.val_top]
    intro x _
    exact hb ⟨x, rfl⟩ (Set.mem_singleton x)

end

end Cleanroom.Decision.DpWorldsJb
