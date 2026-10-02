import Cleanroom.Found.DpCoreTree.Occurrence

/-!
# SE-2: the two run semantics agree at the leaf-law level iff no point is nested

T3 of [[dp-core-tree-mandate]]. **Theorem** (`agreement_iff_not_nested`): `μ_{B,C} = μ'_{B,C}`
for every procedure `C` iff no chance-positive path meets two nodes carrying one point `d`
with `|A_d| ≥ 2`.

The proof goes through the list of draws on a path. `seedFold C env L` is the memoised walk
restricted to the decision draws `L` (so `μ'(ℓ) = chanceWeight(ℓ) · seedFold C none (draws ℓ)`,
`leafLawSeed_eq_chanceWeight_mul_seedFold`). (⇐) On a path where every point with ≥ 2 actions
occurs at most once, the fold is the plain product of draw weights
(`seedFold_eq_prod_of_simple`). (⇒) If `d` is nested, a positive path meeting two `d`-nodes can
be re-routed at the second one to a positive path whose draws at `d` disagree
(`exists_positive_inconsistent`); under the uniform procedure that leaf has positive
Definition-6 mass and zero shared-seed mass, because a non-zero fold forces the draws at each
point to agree (`seedFold_ne_zero_functional`).

This is a **leaf-law** theorem: at the `(λ, r)`-law or value level "only if" fails (SE-4′,
caveat c1 — the payoff-degenerate miniature), so it is not stated over `ν` or `V`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

namespace Tree

/-! ### The memoised walk on a list of draws -/

/-- The memoised walk of Definition 6′ restricted to a list of decision draws: the weight
contributed by the draws, given the seeds `env` already drawn.
Source: `seeds.md` Definition 6′; none: infrastructure
Kind: D -/
def seedFold (C : Proc ι acts K) : ((d : ι) → Option (acts d)) → List (Σ d : ι, acts d) → K
  | _, [] => 1
  | env, ⟨d, a⟩ :: L =>
      match env d with
      | some a' => if a' = a then seedFold C env L else 0
      | none => (C d).w a * seedFold C (Function.update env d (some a)) L

variable (C : Proc ι acts K)

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem seedFold_nil (env : (d : ι) → Option (acts d)) : seedFold C env [] = 1 := rfl

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem seedFold_cons_of_some {env : (d : ι) → Option (acts d)} {d : ι} {a' : acts d}
    (h : env d = some a') (a : acts d) (L : List (Σ d : ι, acts d)) :
    seedFold C env (⟨d, a⟩ :: L) = if a' = a then seedFold C env L else 0 := by
  simp only [seedFold, h]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem seedFold_cons_of_none {env : (d : ι) → Option (acts d)} {d : ι}
    (h : env d = none) (a : acts d) (L : List (Σ d : ι, acts d)) :
    seedFold C env (⟨d, a⟩ :: L) =
      (C d).w a * seedFold C (Function.update env d (some a)) L := by
  simp only [seedFold, h]

/-- The shared-seed law factors as chance weight times the fold over the draws.
Source: `seeds.md` Definition 6′
Kind: P -/
theorem leafLawSeed_eq_chanceWeight_mul_seedFold :
    (B : Tree Ω ι acts K) → ∀ env ℓ,
      leafLawSeed C env B ℓ = chanceWeight B ℓ * seedFold C env (draws B ℓ)
  | leaf _ _, _, _ => by simp
  | chance _ β child, env, ⟨i, ℓ⟩ => by
      simp only [leafLawSeed_chance, chanceWeight_chance, draws_chance,
        leafLawSeed_eq_chanceWeight_mul_seedFold (child i) env ℓ]
      ring
  | decision d child, env, ⟨a, ℓ⟩ => by
      simp only [chanceWeight_decision, draws_decision]
      rcases h : env d with _ | a'
      · rw [leafLawSeed_decision_of_none C h, seedFold_cons_of_none C h,
          leafLawSeed_eq_chanceWeight_mul_seedFold (child a) _ ℓ]
        ring
      · rw [leafLawSeed_decision_of_some C h, seedFold_cons_of_some C h,
          leafLawSeed_eq_chanceWeight_mul_seedFold (child a) _ ℓ]
        split_ifs <;> simp

/-- `μ'_{B,C}(ℓ) = chanceWeight(ℓ) · seedFold C none (draws ℓ)`.
Source: `seeds.md` Definition 6′
Kind: L -/
theorem leafLaw'_eq (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    leafLaw' C B ℓ = chanceWeight B ℓ * seedFold C (fun _ => none) (draws B ℓ) :=
  leafLawSeed_eq_chanceWeight_mul_seedFold C B _ ℓ

/-- A non-zero fold forces every draw at an already-seeded point to equal its seed.
Source: none: infrastructure
Kind: L -/
theorem seedFold_ne_zero_imp_seed :
    (L : List (Σ d : ι, acts d)) → ∀ env, seedFold C env L ≠ 0 →
      ∀ x ∈ L, ∀ a', env x.1 = some a' → x.2 = a'
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | ⟨d, a⟩ :: L, env, h, x, hx, a', henv => by
      rcases hd : env d with _ | b
      · rw [seedFold_cons_of_none C hd] at h
        have h' : seedFold C (Function.update env d (some a)) L ≠ 0 :=
          fun h0 => h (by rw [h0, mul_zero])
        rcases List.mem_cons.mp hx with rfl | hx'
        · simp only at henv; rw [hd] at henv; cases henv
        · obtain ⟨d'', b⟩ := x
          by_cases hdd : d'' = d
          · subst hdd
            simp only at henv; rw [hd] at henv; cases henv
          · have := seedFold_ne_zero_imp_seed L _ h' ⟨d'', b⟩ hx' a'
              (by simp only; rw [Function.update_of_ne hdd]; exact henv)
            exact this
      · rw [seedFold_cons_of_some C hd] at h
        split_ifs at h with hba
        · rcases List.mem_cons.mp hx with rfl | hx'
          · simp only at henv; rw [hd] at henv; cases henv; exact hba.symm
          · exact seedFold_ne_zero_imp_seed L env h ⟨_, _⟩ hx' a' henv
        · exact absurd rfl h

/-- A non-zero fold forces the draws to be *functional* in the point: two draws at the same
point are the same draw.
Source: `seeds.md` Definition 6′ ("the same edge at every node carrying `d_q`")
Kind: P -/
theorem seedFold_ne_zero_functional :
    (L : List (Σ d : ι, acts d)) → ∀ env, seedFold C env L ≠ 0 →
      ∀ x ∈ L, ∀ y ∈ L, x.1 = y.1 → x = y
  | [], _, _, _, hx, _, _, _ => absurd hx List.not_mem_nil
  | ⟨d, a⟩ :: L, env, h, x, hx, y, hy, hxy => by
      rcases hd : env d with _ | b
      · rw [seedFold_cons_of_none C hd] at h
        have h' : seedFold C (Function.update env d (some a)) L ≠ 0 :=
          fun h0 => h (by rw [h0, mul_zero])
        have key : ∀ z ∈ L, z.1 = d → z = ⟨d, a⟩ := by
          intro z hz hz1
          obtain ⟨d', c⟩ := z
          simp only at hz1; subst hz1
          have := seedFold_ne_zero_imp_seed C L _ h' ⟨d', c⟩ hz a (by simp)
          simp only at this; subst this; rfl
        rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact (key y hy' hxy.symm).symm
        · exact key x hx' hxy
        · exact seedFold_ne_zero_functional L _ h' x hx' y hy' hxy
      · rw [seedFold_cons_of_some C hd] at h
        split_ifs at h with hba
        · subst hba
          have key : ∀ z ∈ L, z.1 = d → z = ⟨d, b⟩ := by
            intro z hz hz1
            obtain ⟨d', c⟩ := z
            simp only at hz1; subst hz1
            have := seedFold_ne_zero_imp_seed C L env h ⟨d', c⟩ hz b hd
            simp only at this; subst this; rfl
          rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
          · rfl
          · exact (key y hy' hxy.symm).symm
          · exact key x hx' hxy
          · exact seedFold_ne_zero_functional L env h x hx' y hy' hxy
        · exact absurd rfl h

/-- A subsingleton action type gives every action weight one.
Source: none: infrastructure
Kind: L -/
theorem FinDistr.w_eq_one_of_subsingleton {α : Type} [Fintype α] [Subsingleton α]
    (p : FinDistr K α) (a : α) : p.w a = 1 := by
  have := p.sum_one
  rwa [Fintype.sum_subsingleton _ a] at this

/-- On a *simple* list — every point either unseeded and occurring exactly once, or a
subsingleton action type — the fold is the product of the draw weights.
Source: `seeds.md` SE-2 proof (⇐) ("on a positive path the stochastic points are distinct, so
the path probability factors identically under both semantics")
Kind: P -/
theorem seedFold_eq_prod_of_simple :
    (L : List (Σ d : ι, acts d)) → ∀ env,
      (∀ x ∈ L, (env x.1 = none ∧ (L.map Sigma.fst).count x.1 = 1) ∨ Subsingleton (acts x.1)) →
      seedFold C env L = (L.map fun x => (C x.1).w x.2).prod
  | [], _, _ => by simp
  | ⟨d, a⟩ :: L, env, H => by
      simp only [List.map_cons, List.prod_cons]
      rcases hd : env d with _ | b
      · rw [seedFold_cons_of_none C hd, seedFold_eq_prod_of_simple L _]
        intro x hx
        obtain ⟨d', c⟩ := x
        rcases H ⟨d', c⟩ (List.mem_cons_of_mem _ hx) with ⟨hn, hc⟩ | hs
        · by_cases hdd : d' = d
          · subst hdd
            exfalso
            simp only [List.map_cons, List.count_cons_self] at hc
            have : d' ∈ L.map Sigma.fst := List.mem_map.mpr ⟨⟨d', c⟩, hx, rfl⟩
            have := List.count_pos_iff.mpr this
            omega
          · left
            refine ⟨by simp only; rw [Function.update_of_ne hdd]; exact hn, ?_⟩
            simpa [List.count_cons, hdd, Ne.symm hdd] using hc
        · exact Or.inr hs
      · rcases H ⟨d, a⟩ List.mem_cons_self with ⟨hn, -⟩ | hs
        · simp only at hn; rw [hd] at hn; cases hn
        · have hba : b = a := Subsingleton.elim _ _
          rw [seedFold_cons_of_some C hd, if_pos hba,
            seedFold_eq_prod_of_simple L env, FinDistr.w_eq_one_of_subsingleton, one_mul]
          intro x hx
          obtain ⟨d', c⟩ := x
          rcases H ⟨d', c⟩ (List.mem_cons_of_mem _ hx) with ⟨hn, hc⟩ | hs'
          · by_cases hdd : d' = d
            · subst hdd; exact Or.inr hs
            · left
              refine ⟨hn, ?_⟩
              simpa [List.count_cons, hdd, Ne.symm hdd] using hc
          · exact Or.inr hs'

/-! ### Counting draws -/

/-- `#_d(ℓ)` is the number of draws at `d` on the path.
Source: none: infrastructure
Kind: L -/
theorem count_eq_draws_count (d : ι) :
    (B : Tree Ω ι acts K) → ∀ ℓ, count d B ℓ = ((draws B ℓ).map Sigma.fst).count d
  | leaf _ _, _ => by simp
  | chance _ β child, ⟨i, ℓ⟩ => by simp [count_eq_draws_count d (child i) ℓ]
  | decision d' child, ⟨a, ℓ⟩ => by
      simp only [count_decision, draws_decision, List.map_cons, List.count_cons,
        count_eq_draws_count d (child a) ℓ, beq_iff_eq]
      by_cases h : d' = d <;> simp [h] <;> omega

/-- A draw at `d` on the path means `d` is met on it.
Source: none: infrastructure
Kind: L -/
theorem count_pos_of_mem_draws {d : ι} {a : acts d} {B : Tree Ω ι acts K} {ℓ : B.Leaves}
    (h : (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) : 0 < count d B ℓ := by
  rw [count_eq_draws_count]
  exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨⟨d, a⟩, h, rfl⟩)

/-! ### Positive paths and the re-routing construction -/

/-- Positivity through a chance node.
Source: none: infrastructure
Kind: L -/
theorem Positive.chance_iff {n : ℕ} (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K)
    (i : Fin n) (ℓ : (child i).Leaves) :
    Positive (chance n β child) ⟨i, ℓ⟩ ↔ 0 < β.w i ∧ Positive (child i) ℓ := by
  unfold Positive
  simp only [chanceWeight_chance]
  constructor
  · intro h
    rcases (β.nonneg i).lt_or_eq with h1 | h1
    · refine ⟨h1, ?_⟩
      rcases (chanceWeight_nonneg (child i) ℓ).lt_or_eq with h2 | h2
      · exact h2
      · rw [← h2, mul_zero] at h; exact absurd h (lt_irrefl 0)
    · rw [← h1, zero_mul] at h; exact absurd h (lt_irrefl 0)
  · rintro ⟨h1, h2⟩; exact mul_pos h1 h2

/-- Positivity through a decision node.
Source: none: infrastructure
Kind: L -/
theorem Positive.decision_iff (d : ι) (child : acts d → Tree Ω ι acts K) (a : acts d)
    (ℓ : (child a).Leaves) : Positive (decision d child) ⟨a, ℓ⟩ ↔ Positive (child a) ℓ :=
  Iff.rfl

/-- A distribution has a positive weight somewhere.
Source: none: infrastructure
Kind: L -/
theorem FinDistr.exists_pos {α : Type} [Fintype α] (β : FinDistr K α) : ∃ a, 0 < β.w a := by
  by_contra h
  have h' : ∀ a, β.w a ≤ 0 := fun a => not_lt.mp fun ha => h ⟨a, ha⟩
  have : ∑ a, β.w a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (h' a) (β.nonneg a)
  rw [β.sum_one] at this
  exact one_ne_zero this

/-- Every tree has a chance-positive leaf.
Source: none: infrastructure
Kind: L -/
theorem exists_positive_leaf [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → ∃ ℓ, Positive B ℓ
  | leaf _ _ => ⟨(), by simp [Positive]⟩
  | chance _ β child => by
      obtain ⟨i, hi⟩ := FinDistr.exists_pos β
      obtain ⟨ℓ, hℓ⟩ := exists_positive_leaf (child i)
      exact ⟨⟨i, ℓ⟩, (Positive.chance_iff β child i ℓ).mpr ⟨hi, hℓ⟩⟩
  | decision d child => by
      have ⟨a⟩ := (inferInstance : Nonempty (acts d))
      obtain ⟨ℓ, hℓ⟩ := exists_positive_leaf (child a)
      exact ⟨⟨a, ℓ⟩, hℓ⟩

/-- Re-routing, one step: below a point met on a positive path, some positive path draws an
action other than `a` at `d`.
Source: `seeds.md` SE-2 proof (⇒) ("deviate to `b ≠ a` at `q₂` and follow positive chance
edges")
Kind: L -/
theorem exists_positive_with_other_draw [∀ d, Nonempty (acts d)] (d : ι) (a : acts d)
    (h2 : 2 ≤ Fintype.card (acts d)) :
    (B : Tree Ω ι acts K) → ∀ ℓ, Positive B ℓ → 1 ≤ count d B ℓ →
      ∃ ℓ', Positive B ℓ' ∧ ∃ b, b ≠ a ∧ (⟨d, b⟩ : Σ d, acts d) ∈ draws B ℓ'
  | leaf _ _, _, _, hc => by simp at hc
  | chance _ β child, ⟨i, ℓ⟩, hp, hc => by
      rw [Positive.chance_iff] at hp
      obtain ⟨ℓ', hℓ', b, hb, hmem⟩ :=
        exists_positive_with_other_draw d a h2 (child i) ℓ hp.2 (by simpa using hc)
      exact ⟨⟨i, ℓ'⟩, (Positive.chance_iff β child i ℓ').mpr ⟨hp.1, hℓ'⟩, b, hb, by simpa⟩
  | decision d' child, ⟨c, ℓ⟩, hp, hc => by
      by_cases hd : d' = d
      · subst hd
        obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
        obtain ⟨ℓ'', hℓ''⟩ := exists_positive_leaf (child b)
        exact ⟨⟨b, ℓ''⟩, hℓ'', b, hb, by simp⟩
      · rw [Positive.decision_iff] at hp
        simp only [count_decision, hd, if_false, zero_add] at hc
        obtain ⟨ℓ', hℓ', b, hb, hmem⟩ :=
          exists_positive_with_other_draw d a h2 (child c) ℓ hp hc
        exact ⟨⟨c, ℓ'⟩, hℓ', b, hb, List.mem_cons_of_mem _ hmem⟩

/-- **Re-routing**: a positive path meeting two `d`-nodes (with `|A_d| ≥ 2`) can be re-routed
at the second one into a positive path whose two draws at `d` differ.
Source: `seeds.md` SE-2 proof (⇒)
Kind: P -/
theorem exists_positive_inconsistent [∀ d, Nonempty (acts d)] (d : ι)
    (h2 : 2 ≤ Fintype.card (acts d)) :
    (B : Tree Ω ι acts K) → ∀ ℓ, Positive B ℓ → 2 ≤ count d B ℓ →
      ∃ ℓ', Positive B ℓ' ∧ ∃ a b, a ≠ b ∧
        (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ' ∧ (⟨d, b⟩ : Σ d, acts d) ∈ draws B ℓ'
  | leaf _ _, _, _, hc => by simp at hc
  | chance _ β child, ⟨i, ℓ⟩, hp, hc => by
      rw [Positive.chance_iff] at hp
      obtain ⟨ℓ', hℓ', a, b, hab, ha, hb⟩ :=
        exists_positive_inconsistent d h2 (child i) ℓ hp.2 (by simpa using hc)
      exact ⟨⟨i, ℓ'⟩, (Positive.chance_iff β child i ℓ').mpr ⟨hp.1, hℓ'⟩, a, b, hab,
        by simpa, by simpa⟩
  | decision d' child, ⟨c, ℓ⟩, hp, hc => by
      rw [Positive.decision_iff] at hp
      by_cases hd : d' = d
      · subst hd
        simp only [count_decision, if_true] at hc
        obtain ⟨ℓ', hℓ', b, hb, hmem⟩ :=
          exists_positive_with_other_draw d' c h2 (child c) ℓ hp (by omega)
        exact ⟨⟨c, ℓ'⟩, hℓ', c, b, hb.symm, List.mem_cons_self, List.mem_cons_of_mem _ hmem⟩
      · simp only [count_decision, hd, if_false, zero_add] at hc
        obtain ⟨ℓ', hℓ', a, b, hab, ha, hb⟩ := exists_positive_inconsistent d h2 (child c) ℓ hp hc
        exact ⟨⟨c, ℓ'⟩, hℓ', a, b, hab, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

/-! ### The uniform procedure -/

/-- The procedure that is uniform at every point.
Source: `seeds.md` SE-2 proof ("with `C` uniform")
Kind: D -/
def Proc.uniform [∀ d, Nonempty (acts d)] : Proc ι acts K := fun _ => FinDistr.uniform

/-- The uniform procedure has full support.
Source: none: infrastructure
Kind: L -/
theorem Proc.uniform_fullSupport [∀ d, Nonempty (acts d)] :
    Proc.FullSupport (Proc.uniform : Proc ι acts K) := fun _ a => FinDistr.uniform_w_pos a

/-- Under a full-support procedure the draw-weight product is positive.
Source: none: infrastructure
Kind: L -/
theorem drawsWeight_pos_of_fullSupport {C : Proc ι acts K} (hC : C.FullSupport)
    (B : Tree Ω ι acts K) (ℓ : B.Leaves) : 0 < drawsWeight C B ℓ := by
  unfold drawsWeight
  apply List.prod_pos
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact hC y.1 y.2

/-- Under a full-support procedure, exactly the chance-positive leaves have positive mass.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_pos_iff_of_fullSupport {C : Proc ι acts K} (hC : C.FullSupport)
    (B : Tree Ω ι acts K) (ℓ : B.Leaves) : 0 < leafLaw C B ℓ ↔ Positive B ℓ := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight]
  constructor
  · intro h; exact Positive.of_leafLaw_pos C (by rwa [leafLaw_eq_chanceWeight_mul_drawsWeight])
  · intro h; exact mul_pos h (drawsWeight_pos_of_fullSupport hC B ℓ)

/-! ### SE-2 -/

/-- **SE-2 (⇐)**: if no point is nested, the two run laws agree for every procedure.
Source: `seeds.md` SE-2 (⇐)
Kind: P
Fidelity: exact -/
theorem leafLaw_eq_leafLaw'_of_not_nested {B : Tree Ω ι acts K} (hn : ¬ ∃ d, Nested B d)
    (C : Proc ι acts K) (ℓ : B.Leaves) : leafLaw C B ℓ = leafLaw' C B ℓ := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight, leafLaw'_eq]
  rcases (chanceWeight_nonneg B ℓ).lt_or_eq with hpos | hzero
  · congr 1
    unfold drawsWeight
    symm
    apply seedFold_eq_prod_of_simple
    intro x hx
    obtain ⟨d, a⟩ := x
    simp only
    by_cases hcard : 2 ≤ Fintype.card (acts d)
    · left
      refine ⟨by simp, ?_⟩
      have hle : count d B ℓ ≤ 1 := by
        by_contra hgt
        exact hn ⟨d, hcard, ℓ, hpos, by omega⟩
      have hge := count_pos_of_mem_draws hx
      rw [count_eq_draws_count] at hle hge
      omega
    · right
      exact Fintype.card_le_one_iff_subsingleton.mp (by omega)
  · rw [← hzero, zero_mul, zero_mul]

/-- **SE-2 (⇒), for every full-support procedure**: if some point is nested, every full-support
procedure has a leaf of positive Definition-6 mass and zero shared-seed mass (the two laws
differ on some leaf).
Source: `seeds.md` SE-2 (⇒) ("under nesting they differ for every full-support procedure on
some leaf"); fidelity audit r1 §3.7
Kind: P
Fidelity: exact -/
theorem exists_leafLaw_ne_leafLaw'_of_nested_of_fullSupport [∀ d, Nonempty (acts d)]
    {B : Tree Ω ι acts K} {d : ι} (hn : Nested B d) {C : Proc ι acts K} (hC : C.FullSupport) :
    ∃ ℓ, 0 < leafLaw C B ℓ ∧ leafLaw' C B ℓ = 0 := by
  obtain ⟨h2, ℓ₀, hpos, hc⟩ := hn
  obtain ⟨ℓ, hℓ, a, b, hab, ha, hb⟩ := exists_positive_inconsistent d h2 B ℓ₀ hpos hc
  refine ⟨ℓ, (leafLaw_pos_iff_of_fullSupport hC B ℓ).mpr hℓ, ?_⟩
  rw [leafLaw'_eq]
  by_contra h
  have hfold : seedFold C (fun _ => none) (draws B ℓ) ≠ 0 :=
    fun h0 => h (by rw [h0, mul_zero])
  have := seedFold_ne_zero_functional _ _ _ hfold ⟨d, a⟩ ha ⟨d, b⟩ hb rfl
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
  exact hab this

/-- **SE-2 (⇒)**: if some point is nested, the uniform procedure has a leaf of positive
Definition-6 mass and zero shared-seed mass.
Source: `seeds.md` SE-2 (⇒)
Kind: P
Fidelity: exact -/
theorem exists_leafLaw_ne_leafLaw'_of_nested [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    {d : ι} (hn : Nested B d) :
    ∃ ℓ, 0 < leafLaw (Proc.uniform : Proc ι acts K) B ℓ ∧
      leafLaw' (Proc.uniform : Proc ι acts K) B ℓ = 0 :=
  exists_leafLaw_ne_leafLaw'_of_nested_of_fullSupport hn Proc.uniform_fullSupport

/-- **SE-2, the agreement theorem (leaf-law level)**: `μ_{B,C} = μ'_{B,C}` for every procedure
`C` iff no chance-positive path contains two decision nodes carrying one point `d` with
`|A_d| ≥ 2`.
Source: `seeds.md` SE-2; mandate T3 (dp-cf-053)
Kind: P
Fidelity: exact (leaf-law level; `Nested` carries the `|A_d| ≥ 2` and positive-path clauses)
Hyps: none (`[∀ d, Nonempty (acts d)]` is Definition 3's non-emptiness of `A_d`) -/
theorem agreement_iff_not_nested [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) :
    (∀ C : Proc ι acts K, ∀ ℓ, leafLaw C B ℓ = leafLaw' C B ℓ) ↔ ¬ ∃ d, Nested B d := by
  constructor
  · rintro h ⟨d, hn⟩
    obtain ⟨ℓ, hpos, hzero⟩ := exists_leafLaw_ne_leafLaw'_of_nested hn
    rw [h _ ℓ, hzero] at hpos
    exact lt_irrefl 0 hpos
  · intro hn C ℓ
    exact leafLaw_eq_leafLaw'_of_not_nested hn C ℓ

/-- **Corollary**: on an almost-fair tree the two semantics agree for every procedure, hence
under every point-deviation `C[d ↦ m]`, and give the same `ν` and `V`.
Source: `seeds.md` SE-2 Corollary
Kind: C -/
theorem AlmostFair.leafLaw_eq_leafLaw' {B : Tree Ω ι acts K} (h : AlmostFair B)
    (C : Proc ι acts K) (ℓ : B.Leaves) : leafLaw C B ℓ = leafLaw' C B ℓ :=
  leafLaw_eq_leafLaw'_of_not_nested (fun ⟨d, hd⟩ => h.not_nested d hd) C ℓ

/-- SE-2 corollary on almost-fair trees (an instance of `AlmostFair.leafLaw_eq_leafLaw'`).
Source: `seeds.md` SE-2 Corollary. Kind: L -/
theorem AlmostFair.leafLaw_deviate_eq_leafLaw' {B : Tree Ω ι acts K} (h : AlmostFair B)
    (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d)) (ℓ : B.Leaves) :
    leafLaw (C.deviate d m) B ℓ = leafLaw' (C.deviate d m) B ℓ :=
  h.leafLaw_eq_leafLaw' _ ℓ

/-- SE-2 corollary on almost-fair trees. Source: `seeds.md` SE-2 Corollary. Kind: C -/
theorem AlmostFair.value_eq_value' {B : Tree Ω ι acts K} (h : AlmostFair B)
    (C : Proc ι acts K) : value C B = value' C B :=
  Finset.sum_congr rfl fun ℓ _ => by rw [h.leafLaw_eq_leafLaw' C ℓ]

/-- SE-2 corollary on almost-fair trees. Source: `seeds.md` SE-2 Corollary. Kind: C -/
theorem AlmostFair.nu_eq_nu' [DecidableEq Ω] {B : Tree Ω ι acts K} (h : AlmostFair B)
    (C : Proc ι acts K) (X : Finset Ω) : nu C B X = nu' C B X :=
  Finset.sum_congr rfl fun ℓ _ => by rw [h.leafLaw_eq_leafLaw' C ℓ]

end Tree

end Cleanroom.Found.DpCoreTree
