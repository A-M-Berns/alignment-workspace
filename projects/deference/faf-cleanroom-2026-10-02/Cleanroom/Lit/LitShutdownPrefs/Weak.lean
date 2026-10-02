import Cleanroom.Lit.LitShutdownPrefs.Lottery

/-!
# Framework W: weak preference as primitive (Thornley 2023, Thorstad 2026) — Targets 1, 2, 24

A weak preference `le : Lottery T → Lottery T → Prop` is primitive; `lt`, `indiff` and `gap`
are derived. Transitivity is an axiom on `le`, and Sen's Lemma 1*a (PP-, II-, PI-, IP-
transitivity; Thornley 2023 App. A ll. 550–566) is proved once here.

The six antecedent conditions of the First Theorem are predicates on `le`:
* `IABM` (Indifference to Attempted Button Manipulation) on `Act × R`;
* `IBILsub` — the *substitution* reading of Indifference between Indifference-Shifted Lotteries
  (definition of record; ATTRIBUTION-UNVETTED that this is the intended reading of the
  sublottery schema, item corr-refs-048), with the three-way form of the paper's example and
  the **pointwise lift** (`indiff_map_of_pointwise`: if every support point is indifferent to its
  relabelling, the lottery is indifferent to its push-forward) proved as lemmas — the lift is
  exactly what Lemma 1 of the First Theorem uses;
* `BetterChances` (the iff), `StrictMonotone` (one direction, strict), and Thorstad's
  `Monotonicity` (weak, one direction);
* `Transitive`, `Complete`.

Option Set Independence and Backward Induction are absorbed by the carrier (menu-free
relation; an action *is* its mixture lottery), as the mandate directs.

The expected-utility relation `euLe u` is the N+ engine: it is transitive, complete, satisfies
Better Chances, IBIL and Monotonicity, and satisfies IABM iff `u` is label-blind (Target 24;
critique/thornley.md §2.1 item 1).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Weak

open Lottery

variable {T : Type}

/-- Strict preference derived from weak preference: `X ≻ Y := X ≽ Y ∧ ¬ Y ≽ X`.
Source: Thornley 2023 App. A (Sen 2017 conventions); [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D
Fidelity: exact -/
def lt (le : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := le X Y ∧ ¬ le Y X

/-- Indifference: `X ≽ Y ∧ Y ≽ X`.
Source: Thornley 2024 fn `x09fuv8skd` ("usual definition"); [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D
Fidelity: exact -/
def indiff (le : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := le X Y ∧ le Y X

/-- Preferential gap: `¬ X ≽ Y ∧ ¬ Y ≽ X`.
Source: Thornley 2024 fn `x09fuv8skd` ("usual definition"); [[lit-shutdown-prefs-mandate]] Carrier §
Kind: D
Fidelity: exact -/
def gap (le : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := ¬ le X Y ∧ ¬ le Y X

/-- Lack of preference: neither strict preference holds.
Source: Thornley 2023 §7 ("lacks a preference")
Kind: D
Fidelity: exact -/
def lacks (le : Lottery T → Lottery T → Prop) (X Y : Lottery T) : Prop := ¬ lt le X Y ∧ ¬ lt le Y X

/-- Transitivity of weak preference.
Source: Thornley 2023 §6 (Transitivity)
Kind: D
Fidelity: exact -/
def Transitive (le : Lottery T → Lottery T → Prop) : Prop := ∀ X Y Z, le X Y → le Y Z → le X Z

/-- Completeness of weak preference.
Source: Thornley 2023 §7 (Completeness)
Kind: D
Fidelity: exact -/
def Complete (le : Lottery T → Lottery T → Prop) : Prop := ∀ X Y, le X Y ∨ le Y X

section Sen

variable {le : Lottery T → Lottery T → Prop}

/-- **PP-transitivity** (Sen 2017 Lemma 1*a): strict, strict ⇒ strict.
Source: Thornley 2023 App. A ll. 550–566
Kind: L
Fidelity: exact -/
theorem pp_trans (hT : Transitive le) {X Y Z : Lottery T} (h₁ : lt le X Y) (h₂ : lt le Y Z) :
    lt le X Z :=
  ⟨hT _ _ _ h₁.1 h₂.1, fun h => h₁.2 (hT _ _ _ h₂.1 h)⟩

/-- **II-transitivity** (Sen 2017 Lemma 1*a): indifferent, indifferent ⇒ indifferent.
Source: Thornley 2023 App. A ll. 550–566
Kind: L
Fidelity: exact -/
theorem ii_trans (hT : Transitive le) {X Y Z : Lottery T} (h₁ : indiff le X Y)
    (h₂ : indiff le Y Z) : indiff le X Z :=
  ⟨hT _ _ _ h₁.1 h₂.1, hT _ _ _ h₂.2 h₁.2⟩

/-- **PI-transitivity** (Sen 2017 Lemma 1*a): strict, indifferent ⇒ strict.
Source: Thornley 2023 App. A ll. 550–566
Kind: L
Fidelity: exact -/
theorem pi_trans (hT : Transitive le) {X Y Z : Lottery T} (h₁ : lt le X Y)
    (h₂ : indiff le Y Z) : lt le X Z :=
  ⟨hT _ _ _ h₁.1 h₂.1, fun h => h₁.2 (hT _ _ _ h₂.1 h)⟩

/-- **IP-transitivity** (Sen 2017 Lemma 1*a): indifferent, strict ⇒ strict.
Source: Thornley 2023 App. A ll. 550–566
Kind: L
Fidelity: exact -/
theorem ip_trans (hT : Transitive le) {X Y Z : Lottery T} (h₁ : indiff le X Y)
    (h₂ : lt le Y Z) : lt le X Z :=
  ⟨hT _ _ _ h₁.1 h₂.1, fun h => h₂.2 (hT _ _ _ h h₁.1)⟩

/-- Indifference is symmetric.
Source: none: infrastructure
Kind: L -/
theorem indiff_symm {X Y : Lottery T} (h : indiff le X Y) : indiff le Y X := ⟨h.2, h.1⟩

/-- Strict preference is asymmetric.
Source: none: infrastructure
Kind: L -/
theorem lt_asymm {X Y : Lottery T} (h : lt le X Y) : ¬ lt le Y X := fun h' => h.2 h'.1

/-- Strict preference is irreflexive.
Source: none: infrastructure
Kind: L -/
theorem lt_irrefl (X : Lottery T) : ¬ lt le X X := fun h => h.2 h.1

/-- Lack of preference is indifference or a gap.
Source: Thornley 2023 §7 ("this lack of preference must be indifference")
Kind: L -/
theorem lacks_iff {X Y : Lottery T} : lacks le X Y ↔ indiff le X Y ∨ gap le X Y := by
  unfold lacks lt indiff gap
  by_cases h1 : le X Y <;> by_cases h2 : le Y X <;> simp [h1, h2]

/-- Under Completeness there are no gaps, so a lack of preference is indifference.
Source: Thornley 2023 §7 ("Completeness rules out preferential gaps")
Kind: L -/
theorem lacks_iff_indiff_of_complete (hC : Complete le) {X Y : Lottery T} :
    lacks le X Y ↔ indiff le X Y := by
  rw [lacks_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd (hC X Y) (by rintro (h' | h') <;> [exact h.1 h'; exact h.2 h'])
  · exact Or.inl

/-- Under Completeness: trichotomy `X ≻ Y ∨ Y ≻ X ∨ X ~ Y`.
Source: Thornley 2023 §8 ("By Completeness, either …")
Kind: L -/
theorem trichotomy_of_complete (hC : Complete le) (X Y : Lottery T) :
    lt le X Y ∨ lt le Y X ∨ indiff le X Y := by
  unfold lt indiff
  rcases hC X Y with h | h <;> by_cases h' : le Y X <;> by_cases h'' : le X Y <;> simp_all

end Sen

/-! ## The six conditions -/

/-- **Indifference to Attempted Button Manipulation** on `Act × R`: trajectories that differ only
in the shutdown-influencing action are indifferent.
Source: Thornley 2023 §6 (IABM); [[lit-shutdown-prefs-mandate]] Target 2
Kind: D
Fidelity: exact (the "differ only in the timestep-1 action" clause is the product carrier) -/
def IABM {Act R : Type} (le : Lottery (Act × R) → Lottery (Act × R) → Prop) : Prop :=
  ∀ (a a' : Act) (r : R), indiff le (dirac (a, r)) (dirac (a', r))

/-- **IBIL, substitution reading** (definition of record): indifferent lotteries may be swapped
inside a mixture with any third lottery. ATTRIBUTION-UNVETTED that this is the intended reading
of Thornley's sublottery schema (corr-refs-048's ill-posedness flag); the paper's three-way
example and the pointwise lift used by Lemma 1 are derived from it below.
Source: Thornley 2023 §6 (IBIL); [[lit-shutdown-prefs-mandate]] Target 2
Kind: D
Fidelity: variant: substitution form of a schema over sublotteries -/
def IBILsub (le : Lottery T → Lottery T → Prop) : Prop :=
  ∀ (X Y Z : Lottery T) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1),
    indiff le X Y → indiff le (mix p hp X Z) (mix p hp Y Z)

/-- **Better Chances** (iff form): for `q < p`, `X ≻ Y ↔ pX+(1−p)Y ≻ qX+(1−q)Y`.
Source: Thornley 2023 §6 (Better Chances)
Kind: D
Fidelity: exact -/
def BetterChances (le : Lottery T → Lottery T → Prop) : Prop :=
  ∀ (X Y : Lottery T) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1),
    q < p → (lt le X Y ↔ lt le (mix p hp X Y) (mix q hq X Y))

/-- **Strict Monotonicity** (one direction of Better Chances): `X ≻ Y → q < p →
pX+(1−p)Y ≻ qX+(1−q)Y`. This is what the First Theorem's proof uses.
Source: [[lit-shutdown-prefs-mandate]] Target 2 (the surviving neighbour of Thorstad's Monotonicity)
Kind: D
Fidelity: weaker than Better Chances (one direction) -/
def StrictMonotone (le : Lottery T → Lottery T → Prop) : Prop :=
  ∀ (X Y : Lottery T) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1),
    q < p → lt le X Y → lt le (mix p hp X Y) (mix q hq X Y)

/-- **Thorstad's Monotonicity**: `X ≽ Y → p > q → pX+(1−p)Y ≽ qX+(1−q)Y` (weak, one direction).
Source: Thorstad 2026 §4.1 l. 142
Kind: D
Fidelity: exact -/
def Monotonicity (le : Lottery T → Lottery T → Prop) : Prop :=
  ∀ (X Y : Lottery T) (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1),
    q < p → le X Y → le (mix p hp X Y) (mix q hq X Y)

/-- Better Chances implies Strict Monotonicity.
Source: [[lit-shutdown-prefs-mandate]] Target 3
Kind: L -/
theorem strictMonotone_of_betterChances {le : Lottery T → Lottery T → Prop}
    (h : BetterChances le) : StrictMonotone le :=
  fun X Y p q hp hq hpq hXY => (h X Y p q hp hq hpq).mp hXY

section IBIL

variable {le : Lottery T → Lottery T → Prop}

/-- IBIL on the paper's example: if `X ~ Y` then any two mixtures `s X + (1−s) Y` are indifferent
to `Y`, hence (with Transitivity) `c·(sX+(1−s)Y) + (1−c)Z ~ c·(s'X+(1−s')Y) + (1−c)Z` — this is
`0.1X+0.4Y+0.5Z ~ 0.3X+0.2Y+0.5Z` written with nested mixtures (`a + b = a' + b'` is the shared
outer weight `c`).
Source: Thornley 2023 §6 (the `0.1X+0.4Y+0.5Z` example)
Kind: L
Fidelity: exact -/
theorem indiff_mix_mix_of_indiff (hT : Transitive le) (hI : IBILsub le) {X Y : Lottery T}
    (hXY : indiff le X Y) (Z : Lottery T) (s s' c : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hs' : s' ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    indiff le (mix c hc (mix s hs X Y) Z) (mix c hc (mix s' hs' X Y) Z) := by
  have h1 : indiff le (mix s hs X Y) Y := by
    have := hI X Y Y s hs hXY
    rwa [mix_self] at this
  have h2 : indiff le (mix s' hs' X Y) Y := by
    have := hI X Y Y s' hs' hXY
    rwa [mix_self] at this
  exact hI _ _ Z c hc (ii_trans hT h1 (indiff_symm h2))

/-- **Pointwise lift of IBIL** (the content of Lemma 1): if every support point `t` of `X` is
indifferent to its relabelling `φ t`, then `X` is indifferent to its push-forward `X.map φ`.
Proved by induction on the support, peeling one point at a time with the two-part decomposition
and `IBILsub`; injectivity of `φ` is not needed.
Source: Thornley 2023 App. A A1 (Lemma 1: "differ only insofar as probability mass is shifted
between indifferent trajectories"); [[lit-shutdown-prefs-mandate]] Target 2
Kind: L
Fidelity: stronger (no injectivity hypothesis) -/
theorem indiff_map_of_pointwise (hT : Transitive le) (hI : IBILsub le) (φ : T → T) :
    ∀ (n : ℕ) (X : Lottery T), X.support.card = n →
      (∀ t ∈ X.support, indiff le (dirac t) (dirac (φ t))) → indiff le X (X.map φ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hcard hpt
  classical
  obtain ⟨t, ht⟩ := X.support_nonempty
  by_cases hsing : X.support = {t}
  · rw [X.eq_dirac_of_support_eq t hsing, map_dirac]
    exact hpt t ht
  · have hq : 0 < X.mass (fun s => s = t) := X.mass_pos_of_mem _ t ht rfl
    have hq' : 0 < X.mass (fun s => ¬ s = t) := by
      obtain ⟨s, hs, hst⟩ : ∃ s ∈ X.support, ¬ s = t := by
        by_contra hcon
        push_neg at hcon
        apply hsing
        ext s
        simp only [Finset.mem_singleton]
        exact ⟨hcon s, fun h => h ▸ ht⟩
      exact X.mass_pos_of_mem _ s hs hst
    have hmI : X.mass (fun s => s = t) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨X.mass_nonneg _, X.mass_le_one _⟩
    have hXeq := X.eq_mix_condOn (fun s => s = t) hq hq'
    rw [X.condOn_point t hq] at hXeq
    set Z := X.condOn (fun s => ¬ s = t) hq' with hZ
    set m := X.mass (fun s => s = t) with hm
    have hZsupp : Z.support = X.support.filter (fun s => ¬ s = t) := X.support_condOn _ hq'
    have hZpt : ∀ s ∈ Z.support, indiff le (dirac s) (dirac (φ s)) := fun s hs =>
      hpt s (Finset.mem_filter.mp (hZsupp ▸ hs)).1
    have hZcard : Z.support.card < n := by
      rw [hZsupp, ← hcard]
      exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨t, ht, fun h => h rfl⟩)
    have ihZ : indiff le Z (Z.map φ) := ih _ hZcard Z rfl hZpt
    have hm' : 1 - m ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hmI.2], by linarith [hmI.1]⟩
    have s1 : indiff le (mix m hmI (dirac t) Z) (mix m hmI (dirac (φ t)) Z) :=
      hI _ _ Z m hmI (hpt t ht)
    have s2 : indiff le (mix m hmI (dirac (φ t)) Z) (mix m hmI (dirac (φ t)) (Z.map φ)) := by
      rw [mix_comm m hmI hm' (dirac (φ t)) Z, mix_comm m hmI hm' (dirac (φ t)) (Z.map φ)]
      exact hI _ _ _ (1 - m) hm' ihZ
    rw [hXeq, map_mix, map_dirac]
    exact ii_trans hT s1 s2

end IBIL

/-! ## Expected-utility relations (the N+ engine; Target 24) -/

/-- The expected-utility weak preference for utility `u`: `X ≽ Y ↔ E_Y[u] ≤ E_X[u]`.
Source: [[lit-shutdown-prefs-mandate]] Target 1 (`IsEU u`); critique/thornley.md §2.1 item 1
Kind: D
Fidelity: exact -/
def euLe (u : T → ℝ) (X Y : Lottery T) : Prop := Y.expect u ≤ X.expect u

section EU

variable (u : T → ℝ)

/-- Strict EU preference is strict inequality of expectations.
Source: none: infrastructure
Kind: L -/
theorem euLe_lt_iff (X Y : Lottery T) : lt (euLe u) X Y ↔ Y.expect u < X.expect u := by
  unfold lt euLe; constructor
  · rintro ⟨h1, h2⟩; exact lt_of_le_not_ge h1 h2
  · intro h; exact ⟨h.le, not_le.mpr h⟩

/-- EU indifference is equality of expectations.
Source: none: infrastructure
Kind: L -/
theorem euLe_indiff_iff (X Y : Lottery T) : indiff (euLe u) X Y ↔ X.expect u = Y.expect u := by
  unfold indiff euLe; constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨h.ge, h.le⟩

/-- Every EU relation is transitive.
Source: critique/thornley.md §2.1 item 1 ("Transitivity … hold[s] for any expected-utility maximiser")
Kind: L -/
theorem euLe_transitive : Transitive (euLe u) := fun _ _ _ h1 h2 => le_trans h2 h1

/-- Every EU relation is complete.
Source: critique/thornley.md §2.1 item 1
Kind: L -/
theorem euLe_complete : Complete (euLe u) := fun X Y => by
  unfold euLe; exact le_total _ _

/-- Every EU relation satisfies Better Chances.
Source: critique/thornley.md §2.1 item 1
Kind: L -/
theorem euLe_betterChances : BetterChances (euLe u) := by
  intro X Y p q hp hq hpq
  rw [euLe_lt_iff, euLe_lt_iff, expect_mix, expect_mix]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Every EU relation satisfies Strict Monotonicity.
Source: [[lit-shutdown-prefs-mandate]] Target 3
Kind: L -/
theorem euLe_strictMonotone : StrictMonotone (euLe u) :=
  strictMonotone_of_betterChances (euLe_betterChances u)

/-- Every EU relation satisfies Thorstad's Monotonicity.
Source: Thorstad 2026 §4.1 l. 142
Kind: L -/
theorem euLe_monotonicity : Monotonicity (euLe u) := by
  intro X Y p q hp hq hpq h
  unfold euLe at *
  rw [expect_mix, expect_mix]
  nlinarith

/-- Every EU relation satisfies IBIL (substitution form).
Source: critique/thornley.md §2.1 item 1
Kind: L -/
theorem euLe_ibilSub : IBILsub (euLe u) := by
  intro X Y Z p hp h
  rw [euLe_indiff_iff] at h ⊢
  rw [expect_mix, expect_mix, h]

/-- An EU relation on `Act × R` satisfies IABM iff its utility ignores the action label.
Source: critique/thornley.md §2.1 item 1 (`[checked]`); [[lit-shutdown-prefs-mandate]] Target 1
Kind: L
Fidelity: exact -/
theorem euLe_iabm_iff {Act R : Type} (v : Act × R → ℝ) :
    IABM (euLe v) ↔ ∀ (a a' : Act) (r : R), v (a, r) = v (a', r) := by
  unfold IABM
  constructor
  · intro h a a' r
    have := (euLe_indiff_iff v _ _).mp (h a a' r)
    simpa using this
  · intro h a a' r
    rw [euLe_indiff_iff]
    simp [h a a' r]

end EU

end Weak

end Cleanroom.Lit.LitShutdownPrefs
