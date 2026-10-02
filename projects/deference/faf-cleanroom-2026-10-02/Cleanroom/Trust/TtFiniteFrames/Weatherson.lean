import Cleanroom.Trust.TtFiniteFrames.Geanakoplos
import Mathlib.Data.Fin.VecNotation

/-!
# Weatherson's three-world example, the two near-misses, and the printed typo

Package `tt-finite-frames`, Targets G4, G5, G6.

* **G4**: Weatherson's example — `W = {0,1,2}`, uniform prior, menu `{0, (3, 9, −6)}`,
  `E₁ = {{0,2}, {1}, {2}}` refining `E₂ = {W, {1,2}, {2}}`, both reflexive, transitive and nested,
  `E₂` **not** partitional. Under `E₁` the unique recommended strategy is worth `3`, under `E₂`
  it is worth `4`, and with no information `2`. So G3 fails when "`E₂` partitional" is weakened to
  "`E₂` nested": refinement loses. G2 still holds for each (`3 ≥ 2`, `4 ≥ 2`): both experiments
  have nonnegative value of information relative to none, as the source says. Second instance:
  trust-lab-042's frame, with a partitional anchor that ties.
* **G5**: the two near-misses showing transitivity and nesting are each load-bearing in G2:
  (a) reflexive + nested, not transitive: `Value` fails (return `−1/3 < 0`);
  (b) reflexive + transitive, not nested (the S4 frame of `aumann-modesty.lean`): `Value` fails
  (return `−1 < 0`).
* **G6**: the source's printed transitivity condition (`v ∈ E w → E w ⊆ E v`) fails on its own
  example, while the corrected one holds — a local error (typo), settled.

`decide` is used only for `Finset`/`Bool` facts over `Fin 3`/`Fin 4`; every real-valued fact is
`norm_num` on exact rationals. The recommended strategies in G4 and G5 are unique (strict
preferences at every world), so "every recommended strategy" and "some recommended strategy"
agree — stated explicitly.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Decidability of the correspondence predicates on finite types -/

/-- Reflexivity is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.Reflexive := inferInstanceAs (Decidable (∀ w, w ∈ K w))

/-- Transitivity is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.Transitive :=
  inferInstanceAs (Decidable (∀ w v, v ∈ K w → K v ⊆ K w))

/-- The printed transitivity is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.TransitivePrinted :=
  inferInstanceAs (Decidable (∀ w v, v ∈ K w → K w ⊆ K v))

/-- Nesting is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.Nested :=
  inferInstanceAs (Decidable (∀ w v, Disjoint (K w) (K v) ∨ K w ⊆ K v ∨ K v ⊆ K w))

/-- Partitionality is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.Partitional :=
  inferInstanceAs (Decidable (K.Reflexive ∧ ∀ w v, v ∈ K w → K w = K v))

/-- RTN is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K : Corr W) : Decidable K.RTN :=
  inferInstanceAs (Decidable (K.Reflexive ∧ K.Transitive ∧ K.Nested))

/-- Refinement is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (K₁ K₂ : Corr W) : Decidable (Corr.Refines K₁ K₂) :=
  inferInstanceAs (Decidable (∀ w, K₁ w ⊆ K₂ w))

/-- The uniform prior on `Fin 3`.
Source: [[Deference and Infinite Frames]] §2 l. 152
Kind: D
Fidelity: exact -/
def unif3 : Fin 3 → ℝ := fun _ => 1 / 3

/-- The uniform prior on `Fin 3` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unif3_pos : ∀ w, 0 < unif3 w := fun _ => by norm_num [unif3]

/-- The uniform prior on `Fin 3` is in the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unif3_mem : unif3 ∈ stdSimplex ℝ (Fin 3) :=
  ⟨fun w => (unif3_pos w).le, by simp [unif3]⟩

/-- The constant-zero option.
Source: [[Deference and Infinite Frames]] §2 l. 154 (`O₁ ≡ 0`)
Kind: D
Fidelity: exact -/
def zero3 : Fin 3 → ℝ := fun _ => 0

/-- The experts' estimates of the zero option vanish.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_zero3 (F : Frame (Fin 3)) (w : Fin 3) : E (F.P w) zero3 = 0 := by
  simp [E, zero3]

/-! ## G4: Weatherson's example -/

namespace Weatherson

/-- Weatherson's `E₁ = {{w₁,w₃}, {w₂}, {w₃}}` (worlds `0,1,2` for `w₁,w₂,w₃`).
Source: [[Deference and Infinite Frames]] §2 ll. 159–161
Kind: D
Fidelity: exact -/
def K₁ : Corr (Fin 3) := ![{0, 2}, {1}, {2}]

/-- Weatherson's `E₂ = {W, {w₂,w₃}, {w₃}}`.
Source: [[Deference and Infinite Frames]] §2 ll. 162–164
Kind: D
Fidelity: exact -/
def K₂ : Corr (Fin 3) := ![{0, 1, 2}, {1, 2}, {2}]

/-- The bet `O₂ = (3, 9, −6)`.
Source: [[Deference and Infinite Frames]] §2 ll. 155–157
Kind: D
Fidelity: exact -/
def O₂ : Fin 3 → ℝ := ![3, 9, -6]

/-- The menu `{O₁, O₂}`.
Source: [[Deference and Infinite Frames]] §2 l. 153
Kind: D
Fidelity: exact -/
def menu : DecisionProblem (Fin 3) := {zero3, O₂}

/-- Both experiments are reflexive, transitive (corrected direction) and nested; `E₁` refines
`E₂`; neither is partitional.
Source: [[Deference and Infinite Frames]] §2 l. 166 ("both experiments are reflexive, transitive,
and nested"), note 1
Kind: N+
Fidelity: exact -/
theorem structure_facts : K₁.RTN ∧ K₂.RTN ∧ Corr.Refines K₁ K₂ ∧ ¬ K₂.Partitional ∧
    ¬ K₁.Partitional := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The conditioning frame of `E₁`.
Source: [[Deference and Infinite Frames]] §2
Kind: D
Fidelity: exact -/
def F₁ : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) K₁
    (Corr.mass_pos_of_reflexive unif3_pos structure_facts.1.1)

/-- The conditioning frame of `E₂`.
Source: [[Deference and Infinite Frames]] §2
Kind: D
Fidelity: exact -/
def F₂ : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) K₂
    (Corr.mass_pos_of_reflexive unif3_pos structure_facts.2.1.1)

/-- The experts' estimates of the bet: under `E₁`: `−3/2, 9, −6`; under `E₂`: `2, 3/2, −6`.
Source: [[Deference and Infinite Frames]] §2 ll. 166–168
Kind: L
Fidelity: n/a -/
theorem E_O₂ : E (F₁.P 0) O₂ = -3 / 2 ∧ E (F₁.P 1) O₂ = 9 ∧ E (F₁.P 2) O₂ = -6 ∧
    E (F₂.P 0) O₂ = 2 ∧ E (F₂.P 1) O₂ = 3 / 2 ∧ E (F₂.P 2) O₂ = -6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | rw [F₁, Frame.ofCorr_E_eq] | rw [F₂, Frame.ofCorr_E_eq]) <;>
    (simp [K₁, K₂, mass, unif3, O₂] <;> norm_num)

/-- Membership in the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_menu {o : Fin 3 → ℝ} : o ∈ menu ↔ o = zero3 ∨ o = O₂ := by
  simp [menu]

/-- A recommended strategy for `E₁` declines at `0` and `2` and bets at `1` (strict preferences
at every world, so this is forced).
Source: [[Deference and Infinite Frames]] §2 l. 167 ("the only recommended strategy")
Kind: L
Fidelity: n/a -/
theorem rec₁_shape {S : Fin 3 → Fin 3 → ℝ} (hS : F₁.Recommended menu S) :
    S 0 = zero3 ∧ S 1 = O₂ ∧ S 2 = zero3 := by
  obtain ⟨e0, e1, e2, -, -, -⟩ := E_O₂
  refine ⟨?_, ?_, ?_⟩
  · rcases mem_menu.1 (hS.mem 0) with h | h
    · exact h
    · exfalso
      have := hS.le 0 (mem_menu.2 (Or.inl rfl))
      rw [h, E_zero3, e0] at this
      norm_num at this
  · rcases mem_menu.1 (hS.mem 1) with h | h
    · exfalso
      have := hS.le 1 (mem_menu.2 (Or.inr rfl))
      rw [h, E_zero3, e1] at this
      norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 2) with h | h
    · exact h
    · exfalso
      have := hS.le 2 (mem_menu.2 (Or.inl rfl))
      rw [h, E_zero3, e2] at this
      norm_num at this

/-- A recommended strategy for `E₂` bets at `0` and `1` and declines at `2` (forced).
Source: [[Deference and Infinite Frames]] §2 l. 167
Kind: L
Fidelity: n/a -/
theorem rec₂_shape {S : Fin 3 → Fin 3 → ℝ} (hS : F₂.Recommended menu S) :
    S 0 = O₂ ∧ S 1 = O₂ ∧ S 2 = zero3 := by
  obtain ⟨-, -, -, e0, e1, e2⟩ := E_O₂
  refine ⟨?_, ?_, ?_⟩
  · rcases mem_menu.1 (hS.mem 0) with h | h
    · exfalso
      have := hS.le 0 (mem_menu.2 (Or.inr rfl))
      rw [h, E_zero3, e0] at this
      norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 1) with h | h
    · exfalso
      have := hS.le 1 (mem_menu.2 (Or.inr rfl))
      rw [h, E_zero3, e1] at this
      norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 2) with h | h
    · exact h
    · exfalso
      have := hS.le 2 (mem_menu.2 (Or.inl rfl))
      rw [h, E_zero3, e2] at this
      norm_num at this

/-- **Every** recommended strategy for `E₁` is worth exactly `3`.
Source: [[Deference and Infinite Frames]] §2 l. 167
Kind: N+
Fidelity: exact -/
theorem stratValue₁ {S : Fin 3 → Fin 3 → ℝ} (hS : F₁.Recommended menu S) :
    stratValue unif3 S = 3 := by
  obtain ⟨h0, h1, h2⟩ := rec₁_shape hS
  simp [stratValue, Fin.sum_univ_three, h0, h1, h2, unif3, zero3, O₂]
  norm_num

/-- **Every** recommended strategy for `E₂` is worth exactly `4`.
Source: [[Deference and Infinite Frames]] §2 l. 168
Kind: N+
Fidelity: exact -/
theorem stratValue₂ {S : Fin 3 → Fin 3 → ℝ} (hS : F₂.Recommended menu S) :
    stratValue unif3 S = 4 := by
  obtain ⟨h0, h1, h2⟩ := rec₂_shape hS
  simp [stratValue, Fin.sum_univ_three, h0, h1, h2, unif3, zero3, O₂]
  norm_num

/-- Recommended strategies exist for both experiments (the dependency's informed strategy).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rec_exists : (∃ S, F₁.Recommended menu S) ∧ ∃ S, F₂.Recommended menu S :=
  ⟨⟨_, F₁.informedStrategy_recommended menu (insert_nonempty _ _)⟩,
    ⟨_, F₂.informedStrategy_recommended menu (insert_nonempty _ _)⟩⟩

/-- No information: the bet is worth `2 > 0` to the prior.
Source: [[Deference and Infinite Frames]] §2 l. 166 ("expected return of 2")
Kind: N+
Fidelity: exact -/
theorem E_prior_O₂ : E unif3 O₂ = 2 := by
  simp [E, Fin.sum_univ_three, unif3, O₂]; norm_num

/-- **G4 (Weatherson's example): refinement can lose when the coarser experiment is nested but
not partitional.** `E₁` refines `E₂`, both are RTN, `E₂` is not partitional, and some (indeed
every) `E₁`-recommended strategy is worth strictly less (`3`) than some (every) `E₂`-recommended
strategy (`4`). So G3's partition hypothesis on the coarser experiment is essential.
Source: [[Deference and Infinite Frames]] §2 ll. 150–168; trust-lab-042; fixpoint-lit-027
Kind: N+ (refutes the weakening of G3 to a nested coarser experiment)
Fidelity: exact
Hyps: (a) none -/
theorem refinement_loses : Corr.Refines K₁ K₂ ∧ K₁.RTN ∧ K₂.RTN ∧ ¬ K₂.Partitional ∧
    ∃ S₁ S₂, F₁.Recommended menu S₁ ∧ F₂.Recommended menu S₂ ∧
      stratValue unif3 S₁ < stratValue unif3 S₂ := by
  obtain ⟨h1, h2, h3, h4, -⟩ := structure_facts
  obtain ⟨⟨S₁, hS₁⟩, ⟨S₂, hS₂⟩⟩ := rec_exists
  refine ⟨h3, h1, h2, h4, S₁, S₂, hS₁, hS₂, ?_⟩
  rw [stratValue₁ hS₁, stratValue₂ hS₂]
  norm_num

/-- **G2 holds for both experiments** (they are RTN): each has nonnegative value of information
relative to no information — on this menu, `3 ≥ 2` and `4 ≥ 2`.
Source: [[Deference and Infinite Frames]] §2 l. 168 ("both experiments have positive expected
returns, relative to not doing anything")
Kind: C / N+
Fidelity: exact
Hyps: (a) none -/
theorem both_valued : Value unif3 F₁ ∧ Value unif3 F₂ ∧
    (∀ S, F₁.Recommended menu S → E unif3 O₂ ≤ stratValue unif3 S) ∧
    (∀ S, F₂.Recommended menu S → E unif3 O₂ ≤ stratValue unif3 S) := by
  refine ⟨value_ofCorr_of_rtn unif3_pos structure_facts.1,
    value_ofCorr_of_rtn unif3_pos structure_facts.2.1, fun S hS => ?_, fun S hS => ?_⟩
  · rw [stratValue₁ hS, E_prior_O₂]; norm_num
  · rw [stratValue₂ hS, E_prior_O₂]; norm_num

/-! ### G6: the printed transitivity condition -/

/-- **G6.** The source's printed transitivity (`v ∈ E w → E w ⊆ E v`) fails on both of its own
experiments (`2 ∈ E₁ 0` but `E₁ 0 ⊄ E₁ 2`; `1 ∈ E₂ 0` but `E₂ 0 ⊄ E₂ 1`), while the corrected
condition holds on both. A local error (typo) in the source, as transcriber's note 1 says.
Source: [[Deference and Infinite Frames]] §2 l. 136 and note 1 (l. 11); fixpoint-lit-028
Kind: N+ (finding)
Fidelity: exact -/
theorem printed_transitivity_fails : ¬ K₁.TransitivePrinted ∧ ¬ K₂.TransitivePrinted ∧
    K₁.Transitive ∧ K₂.Transitive := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end Weatherson

/-! ## G4, second instance: trust-lab-042's frame -/

namespace Lab042

/-- The finer experiment `{{0}, {1}, {0,2}}`.
Source: trust-lab-042 (`negative-voi.lean`)
Kind: D
Fidelity: exact -/
def K₁ : Corr (Fin 3) := ![{0}, {1}, {0, 2}]

/-- The coarser experiment `{{0}, {1}, W}`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def K₂ : Corr (Fin 3) := ![{0}, {1}, {0, 1, 2}]

/-- The partitional anchor `{{0,2}, {1}, {0,2}}`.
Source: trust-lab-042 (partitional near-miss)
Kind: D
Fidelity: exact -/
def Q : Corr (Fin 3) := ![{0, 2}, {1}, {0, 2}]

/-- Option `a = (0, 2/3, 1/3)`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def Oa : Fin 3 → ℝ := ![0, 2 / 3, 1 / 3]

/-- Option `b = (2/3, 0, 0)`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def Ob : Fin 3 → ℝ := ![2 / 3, 0, 0]

/-- The menu `{a, b}`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def menu : DecisionProblem (Fin 3) := {Oa, Ob}

/-- Structure: `K₁`, `K₂` RTN, `Q` partitional, `K₁` refines both `K₂` and `Q`, `K₂` not
partitional.
Source: trust-lab-042
Kind: N+
Fidelity: exact -/
theorem structure_facts : K₁.RTN ∧ K₂.RTN ∧ Q.Partitional ∧ Corr.Refines K₁ K₂ ∧
    Corr.Refines K₁ Q ∧ ¬ K₂.Partitional := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The conditioning frame of `K₁`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def F₁ : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) K₁
    (Corr.mass_pos_of_reflexive unif3_pos structure_facts.1.1)

/-- The conditioning frame of `K₂`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def F₂ : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) K₂
    (Corr.mass_pos_of_reflexive unif3_pos structure_facts.2.1.1)

/-- The conditioning frame of the anchor `Q`.
Source: trust-lab-042
Kind: D
Fidelity: exact -/
def FQ : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) Q
    (Corr.mass_pos_of_reflexive unif3_pos structure_facts.2.2.1.1)

/-- Membership in the menu.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_menu {o : Fin 3 → ℝ} : o ∈ menu ↔ o = Oa ∨ o = Ob := by simp [menu]

/-- The estimates: `F₁`: `(a,b)` at `0`: `(0, 2/3)`, at `1`: `(2/3, 0)`, at `2`: `(1/6, 1/3)`;
`F₂` at `2`: `(1/3, 2/9)`; `FQ` at `0` and `2`: `(1/6, 1/3)`.
Source: trust-lab-042
Kind: L
Fidelity: n/a -/
theorem estimates :
    (E (F₁.P 0) Oa = 0 ∧ E (F₁.P 0) Ob = 2 / 3) ∧ (E (F₁.P 1) Oa = 2 / 3 ∧ E (F₁.P 1) Ob = 0) ∧
    (E (F₁.P 2) Oa = 1 / 6 ∧ E (F₁.P 2) Ob = 1 / 3) ∧
    (E (F₂.P 0) Oa = 0 ∧ E (F₂.P 0) Ob = 2 / 3) ∧ (E (F₂.P 1) Oa = 2 / 3 ∧ E (F₂.P 1) Ob = 0) ∧
    (E (F₂.P 2) Oa = 1 / 3 ∧ E (F₂.P 2) Ob = 2 / 9) ∧
    (E (FQ.P 0) Oa = 1 / 6 ∧ E (FQ.P 0) Ob = 1 / 3) ∧ (E (FQ.P 1) Oa = 2 / 3 ∧ E (FQ.P 1) Ob = 0) ∧
    (E (FQ.P 2) Oa = 1 / 6 ∧ E (FQ.P 2) Ob = 1 / 3) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩ <;>
    (first | rw [F₁, Frame.ofCorr_E_eq] | rw [F₂, Frame.ofCorr_E_eq] | rw [FQ, Frame.ofCorr_E_eq]) <;>
    (simp [K₁, K₂, Q, mass, unif3, Oa, Ob] <;> norm_num)

/-- Forced choices under `K₁`: `b, a, b`.
Source: trust-lab-042
Kind: L
Fidelity: n/a -/
theorem rec₁_shape {S : Fin 3 → Fin 3 → ℝ} (hS : F₁.Recommended menu S) :
    S 0 = Ob ∧ S 1 = Oa ∧ S 2 = Ob := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, -, -, -, -, -, -⟩ := estimates
  refine ⟨?_, ?_, ?_⟩
  · rcases mem_menu.1 (hS.mem 0) with h | h
    · exfalso; have := hS.le 0 (mem_menu.2 (Or.inr rfl)); rw [h, a0, b0] at this; norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 1) with h | h
    · exact h
    · exfalso; have := hS.le 1 (mem_menu.2 (Or.inl rfl)); rw [h, a1, b1] at this; norm_num at this
  · rcases mem_menu.1 (hS.mem 2) with h | h
    · exfalso; have := hS.le 2 (mem_menu.2 (Or.inr rfl)); rw [h, a2, b2] at this; norm_num at this
    · exact h

/-- Forced choices under `K₂`: `b, a, a`.
Source: trust-lab-042
Kind: L
Fidelity: n/a -/
theorem rec₂_shape {S : Fin 3 → Fin 3 → ℝ} (hS : F₂.Recommended menu S) :
    S 0 = Ob ∧ S 1 = Oa ∧ S 2 = Oa := by
  obtain ⟨-, -, -, ⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, -, -, -⟩ := estimates
  refine ⟨?_, ?_, ?_⟩
  · rcases mem_menu.1 (hS.mem 0) with h | h
    · exfalso; have := hS.le 0 (mem_menu.2 (Or.inr rfl)); rw [h, a0, b0] at this; norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 1) with h | h
    · exact h
    · exfalso; have := hS.le 1 (mem_menu.2 (Or.inl rfl)); rw [h, a1, b1] at this; norm_num at this
  · rcases mem_menu.1 (hS.mem 2) with h | h
    · exact h
    · exfalso; have := hS.le 2 (mem_menu.2 (Or.inl rfl)); rw [h, a2, b2] at this; norm_num at this

/-- Forced choices under the anchor `Q`: `b, a, b`.
Source: trust-lab-042
Kind: L
Fidelity: n/a -/
theorem recQ_shape {S : Fin 3 → Fin 3 → ℝ} (hS : FQ.Recommended menu S) :
    S 0 = Ob ∧ S 1 = Oa ∧ S 2 = Ob := by
  obtain ⟨-, -, -, -, -, -, ⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩ := estimates
  refine ⟨?_, ?_, ?_⟩
  · rcases mem_menu.1 (hS.mem 0) with h | h
    · exfalso; have := hS.le 0 (mem_menu.2 (Or.inr rfl)); rw [h, a0, b0] at this; norm_num at this
    · exact h
  · rcases mem_menu.1 (hS.mem 1) with h | h
    · exact h
    · exfalso; have := hS.le 1 (mem_menu.2 (Or.inl rfl)); rw [h, a1, b1] at this; norm_num at this
  · rcases mem_menu.1 (hS.mem 2) with h | h
    · exfalso; have := hS.le 2 (mem_menu.2 (Or.inr rfl)); rw [h, a2, b2] at this; norm_num at this
    · exact h

/-- **G4, second instance.** Values `4/9` (finer `K₁`), `5/9` (coarser, nested, non-partitional
`K₂`) and `4/9` (partitional anchor `Q`, which `K₁` refines and ties). Refinement of a nested
non-partitional experiment loses; refinement of a partitional one does not (G3).
Source: trust-lab-042
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem values : (∀ S, F₁.Recommended menu S → stratValue unif3 S = 4 / 9) ∧
    (∀ S, F₂.Recommended menu S → stratValue unif3 S = 5 / 9) ∧
    (∀ S, FQ.Recommended menu S → stratValue unif3 S = 4 / 9) := by
  refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨h0, h1, h2⟩ := rec₁_shape hS
    simp [stratValue, Fin.sum_univ_three, h0, h1, h2, unif3, Oa, Ob]; norm_num
  · obtain ⟨h0, h1, h2⟩ := rec₂_shape hS
    simp [stratValue, Fin.sum_univ_three, h0, h1, h2, unif3, Oa, Ob]; norm_num
  · obtain ⟨h0, h1, h2⟩ := recQ_shape hS
    simp [stratValue, Fin.sum_univ_three, h0, h1, h2, unif3, Oa, Ob]; norm_num

end Lab042

/-! ## G5: the near-misses -/

namespace NearMiss

/-- (a) Reflexive + nested, **not transitive**: `E 0 = {0,1}`, `E 1 = W`, `E 2 = {2}`.
Source: mandate G5(a) (trust-lab-2-026's requested near-miss)
Kind: D
Fidelity: exact -/
def Ka : Corr (Fin 3) := ![{0, 1}, {0, 1, 2}, {2}]

/-- The bet `(−1, 2, −4)`.
Source: mandate G5(a)
Kind: D
Fidelity: exact -/
def bet3 : Fin 3 → ℝ := ![-1, 2, -4]

/-- `Ka` is reflexive and nested but not transitive.
Source: mandate G5(a)
Kind: N−
Fidelity: exact -/
theorem Ka_facts : Ka.Reflexive ∧ Ka.Nested ∧ ¬ Ka.Transitive := by
  refine ⟨by decide, by decide, by decide⟩

/-- The conditioning frame of `Ka`.
Source: mandate G5(a)
Kind: D
Fidelity: exact -/
def Fa : Frame (Fin 3) :=
  Frame.ofCorr unif3 (fun w => (unif3_pos w).le) Ka
    (Corr.mass_pos_of_reflexive unif3_pos Ka_facts.1)

/-- Estimates of the bet under `Ka`: `1/2, −1, −4`.
Source: mandate G5(a) (re-verified)
Kind: L
Fidelity: n/a -/
theorem Fa_E : E (Fa.P 0) bet3 = 1 / 2 ∧ E (Fa.P 1) bet3 = -1 ∧ E (Fa.P 2) bet3 = -4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Fa, Frame.ofCorr_E_eq] <;>
    (simp [Ka, mass, unif3, bet3] <;> norm_num)

/-- **G5(a). Transitivity is load-bearing in G2.** For the reflexive, nested, non-transitive
`Ka`, `Value` fails: on the menu `{bet, 0}` the (unique) recommended strategy takes the bet at
world `0` only and returns `−1/3 < 0 = E_π(0)`.
Source: mandate G5(a); trust-lab-2-026
Kind: N− (refuted variant: the point is that the hypothesis is sharp)
Fidelity: exact
Hyps: (a) none -/
theorem value_fails_without_transitivity : ¬ Value unif3 Fa := by
  intro hV
  obtain ⟨e0, e1, e2⟩ := Fa_E
  -- the strategy: bet at `0`, decline elsewhere
  set S : Fin 3 → Fin 3 → ℝ := ![bet3, zero3, zero3] with hS
  have hrec : Fa.Recommended {bet3, zero3} S := by
    refine ⟨⟨fun w => ?_, fun w v e => ?_⟩, fun w o ho => ?_⟩
    · fin_cases w <;> simp [hS]
    · have hinj := Frame.ofCorr_P_inj unif3 unif3_pos Ka
        (Corr.mass_pos_of_reflexive unif3_pos Ka_facts.1) w v
      rw [Fa] at e
      have hK := hinj.1 e
      fin_cases w <;> fin_cases v <;> first | rfl | (exact absurd hK (by decide))
    · simp only [mem_insert, mem_singleton] at ho
      fin_cases w <;> rcases ho with rfl | rfl <;> simp [hS, E_zero3, e0, e1, e2]
  have := hV _ (insert_nonempty _ _) S hrec zero3 (by simp)
  simp [stratValue, Fin.sum_univ_three, hS, E, unif3, bet3, zero3] at this
  norm_num at this

/-- (b) Reflexive + transitive, **not nested**: the S4 frame of `aumann-modesty.lean` on `Fin 4`:
`E 0 = {0,1,2}`, `E 1 = E 2 = {1,2}`, `E 3 = {1,2,3}`.
Source: trust-lab-041 (`aumann-modesty.lean` ll. 56–58); mandate G5(b)
Kind: D
Fidelity: exact -/
def Kb : Corr (Fin 4) := ![{0, 1, 2}, {1, 2}, {1, 2}, {1, 2, 3}]

/-- The uniform prior on `Fin 4`.
Source: trust-lab-041
Kind: D
Fidelity: exact -/
def unif4 : Fin 4 → ℝ := fun _ => 1 / 4

/-- The uniform prior on `Fin 4` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem unif4_pos : ∀ w, 0 < unif4 w := fun _ => by norm_num [unif4]

/-- The bet `(−5, 3, 3, −5)`.
Source: mandate G5(b)
Kind: D
Fidelity: exact -/
def bet4 : Fin 4 → ℝ := ![-5, 3, 3, -5]

/-- The zero option on `Fin 4`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def zero4 : Fin 4 → ℝ := fun _ => 0

/-- `Kb` is reflexive and transitive but not nested.
Source: trust-lab-041 (`E_reflexive`, `E_transitive`, `cells_overlap_not_nested`)
Kind: N−
Fidelity: exact -/
theorem Kb_facts : Kb.Reflexive ∧ Kb.Transitive ∧ ¬ Kb.Nested := by
  refine ⟨by decide, by decide, by decide⟩

/-- The conditioning frame of `Kb`.
Source: mandate G5(b)
Kind: D
Fidelity: exact -/
def Fb : Frame (Fin 4) :=
  Frame.ofCorr unif4 (fun w => (unif4_pos w).le) Kb
    (Corr.mass_pos_of_reflexive unif4_pos Kb_facts.1)

/-- Estimates of the bet under `Kb`: `1/3, 3, 3, 1/3` — all positive.
Source: mandate G5(b) (re-verified)
Kind: L
Fidelity: n/a -/
theorem Fb_E : E (Fb.P 0) bet4 = 1 / 3 ∧ E (Fb.P 1) bet4 = 3 ∧ E (Fb.P 2) bet4 = 3 ∧
    E (Fb.P 3) bet4 = 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Fb, Frame.ofCorr_E_eq] <;>
    (simp [Kb, mass, unif4, bet4] <;> norm_num)

/-- The zero option has zero estimate under any frame on `Fin 4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_zero4 (F : Frame (Fin 4)) (w : Fin 4) : E (F.P w) zero4 = 0 := by simp [E, zero4]

/-- **G5(b). Nesting is load-bearing in G2.** For the reflexive, transitive, non-nested `Kb`,
`Value` fails: every world takes the bet and the return is `−1 < 0`.
Source: mandate G5(b); trust-lab-041
Kind: N− (refuted variant)
Fidelity: exact
Hyps: (a) none -/
theorem value_fails_without_nesting : ¬ Value unif4 Fb := by
  intro hV
  obtain ⟨e0, e1, e2, e3⟩ := Fb_E
  set S : Fin 4 → Fin 4 → ℝ := fun _ => bet4 with hS
  have hrec : Fb.Recommended {bet4, zero4} S := by
    refine ⟨⟨fun w => by simp [hS], fun w v _ => rfl⟩, fun w o ho => ?_⟩
    simp only [mem_insert, mem_singleton] at ho
    fin_cases w <;> rcases ho with rfl | rfl <;> simp [hS, E_zero4, e0, e1, e2, e3]
  have := hV _ (insert_nonempty _ _) S hrec zero4 (by simp)
  simp [stratValue, Fin.sum_univ_four, hS, E, unif4, bet4, zero4] at this
  norm_num at this

end NearMiss

end

end Cleanroom.Trust.TtFiniteFrames
